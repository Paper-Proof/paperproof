// A resident "shadow" document: a hidden .lean file (under the project's gitignored
// `.lake/`) mirroring the user's file with Paperproof's parser injected after the
// imports. The user's real buffer is never touched, so there's no didChange fight
// with the lean4 extension. Rebuilt only when the source changes; cursor moves
// re-query the already-elaborated shadow. Mirrors paperproof-mcp's lean_runner.

import * as fs from "fs";
import * as path from "path";
import * as vscode from "vscode";

import vscodeRequest from "../vscodeRequest";
import { buildInjection, mapPosition, Injection } from "./injection";
import { candidateParsers, findProjectRoot, ParserCandidate } from "./parserVersions";

const TREE_METHOD = "ppMcpGetProof";
const SINGLE_TACTIC_METHOD = "ppMcpGetSingleTactic";

// "no tactic-mode proof here" — a definitive answer, not an error.
const NO_PROOF_MARKS = ["noParsedTree", "no snapshot found", "zeroProofSteps"];
// [Claude comment] ...of which only this one has nothing for the user: the others carry
// snackbars in the webview (e.g. the "cursor after #exit?" hint), so they have to arrive
// there as errors instead of being flattened into an empty proof tree.
const SILENT_NO_PROOF_MARKS = ["noParsedTree"];
// method not registered: parser still elaborating, or (if it errored) unsupported.
const NOT_REGISTERED_MARKS = ["No RPC method", "-32601"];
// transient states to retry through while the shadow re-elaborates.
const TRANSIENT_MARKS = [
  ...NOT_REGISTERED_MARKS,
  "Outdated RPC session",
  "-32900",
  "contains errors",
  "uses 'sorry'",
  "_rpc_wrapped",
  "rpcTimeout",
];

const ELAB_WAIT_MS = 180_000;
const POLL_MS = 400;
// Hard cap on any single RPC: the lean4 client's sendRequest never times out, so
// a blocked `withWaitFindSnapAtPos` on the server would otherwise hang forever
// (and poison the shared `refreshing` promise). Treated as transient -> retried.
const RPC_TIMEOUT_MS = 45_000;

export interface ShadowQueryResult {
  steps: any;
  goal: any;
}

/** The parser measures tactic positions against the shadow's FileMap, so they sit
 *  `injectedLineCount` lines below where they are in the real file. Undo that, or
 *  the webview can never match the cursor to a tactic. Inverse of `mapPosition`. */
const unmapSteps = (injection: Injection, steps: any): any => {
  const firstShifted = injection.insertedAt + injection.injectedLineCount;
  const unshift = (p: any) => {
    if (p && typeof p.line === "number" && p.line >= firstShifted) {
      p.line -= injection.injectedLineCount;
    }
  };
  for (const step of Array.isArray(steps) ? steps : []) {
    unshift(step?.position?.start);
    unshift(step?.position?.stop);
  }
  return steps;
};

const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));
const hasMark = (msg: string, marks: string[]) => marks.some((m) => msg.includes(m));

const withTimeout = <T>(p: Promise<T>, ms: number, label: string): Promise<T> =>
  new Promise((resolve, reject) => {
    const t = setTimeout(() => reject(new Error(label)), ms);
    p.then(
      (v) => { clearTimeout(t); resolve(v); },
      (e) => { clearTimeout(t); reject(e); }
    );
  });

const goalIds = (steps: any): Set<string> => {
  const ids = new Set<string>();
  for (const step of Array.isArray(steps) ? steps : []) {
    const goals = [step?.goalBefore, ...(step?.goalsAfter ?? []), ...(step?.spawnedGoals ?? [])];
    goals.forEach((g) => { if (g?.id) { ids.add(g.id); } });
  }
  return ids;
};

export class ShadowDoc {
  private tempPath: string;
  private uri: vscode.Uri;
  private doc: vscode.TextDocument | null = null;
  private injection: Injection | null = null;
  private syncedVersion = -1; // source TextDocument.version last mirrored
  private workingParser: ParserCandidate | null = null;
  private refreshing: Promise<void> | null = null;
  private noSingleTactic = false; // set once a bundle proves to lack the single-tactic method
  private treeCache: { version: number; goalIds: Set<string>; steps: any } | null = null;

  private constructor(
    private readonly context: vscode.ExtensionContext,
    private readonly log: vscode.OutputChannel,
    private readonly leanClient: any,
    private readonly source: vscode.TextDocument,
    private readonly projectRoot: string
  ) {
    // `.lake/` is gitignored in every Lean project (so the shadow never shows up
    // in git), and the server still elaborates files there with the project's
    // LEAN_PATH. Unique suffix so concurrent files don't collide.
    const shadowDir = path.join(projectRoot, ".lake", "paperproof");
    try { fs.mkdirSync(shadowDir, { recursive: true }); } catch { /* best effort */ }
    const base = path.basename(source.uri.fsPath, ".lean");
    const tag = Math.random().toString(36).slice(2, 8);
    this.tempPath = path.join(shadowDir, `${base}-${tag}.lean`);
    this.uri = vscode.Uri.file(this.tempPath);
  }

  static create(
    context: vscode.ExtensionContext,
    log: vscode.OutputChannel,
    leanClient: any,
    source: vscode.TextDocument
  ): ShadowDoc | null {
    const root = findProjectRoot(source.uri.fsPath);
    if (!root) { return null; }
    return new ShadowDoc(context, log, leanClient, source, root);
  }

  /** Query the proof at `position` (in the real file's coordinates). Returns the
   *  webview-native steps, or null when there's no tactic proof there. In single-
   *  tactic mode, falls back to tree mode if the bundle lacks the method. */
  async query(position: vscode.Position, singleTactic = false): Promise<ShadowQueryResult | null> {
    await this.ensureFresh();
    if (!this.injection || !this.doc) { return null; }

    const mapped = mapPosition(this.injection, position.line, position.character, this.source.getText().split("\n"));
    const goal = await this.fetchGoal(mapped);

    if (singleTactic && !this.noSingleTactic) {
      try {
        return await this.callRpc(SINGLE_TACTIC_METHOD, mapped, goal);
      } catch (err) {
        // The parser is already registered (ensureFresh primed it), so a missing-
        // method error means this bundle has no single-tactic method.
        if (!hasMark((err as Error).message || String(err), NOT_REGISTERED_MARKS)) { throw err; }
        this.noSingleTactic = true;
        this.log.appendLine("no-install: bundle has no single-tactic method — using tree mode.");
      }
    }

    // [Claude comment] there's one command per snapshot, so every position inside a proof answers
    // with the same tree - a cursor goal that belongs to the cached tree means we're still
    // in the proof it came from, and the (expensive) reparse can be skipped.
    if (this.treeCache && this.treeCache.version === this.syncedVersion &&
        goal?.mvarId && this.treeCache.goalIds.has(goal.mvarId)) {
      return { steps: this.treeCache.steps, goal };
    }

    const result = await this.callRpc(TREE_METHOD, mapped, goal);
    if (result) {
      this.treeCache = { version: this.syncedVersion, goalIds: goalIds(result.steps), steps: result.steps };
    }
    return result;
  }

  /** Rebuild the shadow if the source changed since we last mirrored it.
   *  vscode closes documents that were opened but never shown, which makes the lean
   *  server drop the file - every later RPC against that URI then fails. Checking
   *  `isClosed` is what stops us short-circuiting onto a document nobody is serving. */
  private async ensureFresh(): Promise<void> {
    if (this.doc?.isClosed) { this.doc = null; this.syncedVersion = -1; }
    if (this.doc && this.syncedVersion === this.source.version) { return; }
    if (this.refreshing) { return this.refreshing; }
    this.refreshing = this.refresh().finally(() => { this.refreshing = null; });
    return this.refreshing;
  }

  private async refresh(): Promise<void> {
    const sourceText = this.source.getText();
    const sourceVersion = this.source.version;
    const { candidates, projectVersion } = candidateParsers(this.context, this.projectRoot);
    const ordered = this.workingParser ? [this.workingParser] : candidates;

    let lastErr: unknown = null;
    for (const cand of ordered) {
      const injection = buildInjection(sourceText, cand.source);
      await this.writeShadow(injection.shadowText);
      this.injection = injection;
      try {
        await this.waitForParser(injection);
        this.workingParser = cand;
        this.syncedVersion = sourceVersion;
        return;
      } catch (err) {
        lastErr = err;
        this.workingParser = null;
        if ((err as Error).message === "parserCompileError") { continue; }
        throw err;
      }
    }
    // [Claude comment] The cause goes to the log, not into the message - the webview
    // matches error strings exactly, so they stay bare codes.
    this.log.appendLine(
      `no-install: no bundled parser compiled against this project's Lean ` +
        `(${lastErr instanceof Error ? lastErr.message : lastErr}).`
    );
    throw Object.assign(new Error("noParserForLeanVersion"), { meta: { leanVersion: projectVersion } });
  }

  /** Wait until the injected parser registers its RPC method, telling a genuine
   *  compile failure (error diagnostics in the injected region) apart from "still
   *  elaborating". */
  private async waitForParser(injection: Injection): Promise<void> {
    const deadline = Date.now() + ELAB_WAIT_MS;
    const probe = { line: injection.insertedAt + injection.injectedLineCount, character: 0 };
    while (true) {
      if (this.hasParserErrors(injection)) { throw new Error("parserCompileError"); }
      const goal = await this.fetchGoal(probe);
      try {
        await this.callRpc(TREE_METHOD, probe, goal);
        return; // answered (even "no proof here" means it registered)
      } catch (err) {
        const msg = (err as Error).message || String(err);
        if (hasMark(msg, NO_PROOF_MARKS)) { return; }
        if (hasMark(msg, TRANSIENT_MARKS) && Date.now() < deadline) {
          await sleep(POLL_MS);
          continue;
        }
        throw err;
      }
    }
  }

  /* Still no "wait until the whole shadow is elaborated" step: the RPC is
     `withWaitFindSnapAtPos`, so it already blocks exactly as long as the cursor's
     snapshot needs. Waiting for the full file made every edit pay for elaborating
     the entire rest of the file, just to keep the server log free of
     `Task.get called from a (sync := true) task` warnings. `fetchGoal` gets
     rid of those warnings without that cost. */

  /** Core Lean's goals, asked of the shadow at the mapped position so the ids line up
   *  with the tree.
   *
   *  Doubles as the elaboration barrier for the user-method calls that follow, which is
   *  why it retries instead of giving up on the first error. `handleRpcCall` answers
   *  builtins straight off `RequestM.asTask`, but routes a user-registered method (ours)
   *  through `bindWaitFindSnap`, whose predicate reads `userRpcProcedures` out of each
   *  candidate snapshot's env. While the file is still elaborating that env is an
   *  unfinished task, and the predicate runs on the server's sync task - so every attempt
   *  makes the runtime print "`Task.get` called from a `(sync := true)` task" plus a
   *  60-line backtrace, which vscode raises as an error toast.
   *
   *  A builtin blocks on the very same snapshot, so this costs no extra waiting: with
   *  a cold shadow, time-to-first-answer measured the same with and without it, while
   *  the warnings went from ~13 per edit to none. */
  private async fetchGoal(pos: { line: number; character: number }): Promise<any> {
    const deadline = Date.now() + ELAB_WAIT_MS;
    const tdp = { textDocument: { uri: this.uri.toString() }, position: pos };
    while (Date.now() < deadline) {
      try {
        const res = await withTimeout(
          vscodeRequest(this.log, "Lean.Widget.getInteractiveGoals", this.leanClient, this.uri.toString(), tdp, tdp),
          RPC_TIMEOUT_MS,
          "rpcTimeout"
        );
        return (res && res.goals && res.goals[0]) || null;
      } catch (err) {
        // Only "not ready yet" answers are worth another round; anything else (no goals
        // at this position, say) still tells us the snapshot itself is elaborated.
        if (hasMark((err as Error).message || String(err), TRANSIENT_MARKS)) {
          await sleep(POLL_MS);
          continue;
        }
        return null;
      }
    }
    return null;
  }

  private hasParserErrors(injection: Injection): boolean {
    const lo = injection.insertedAt;
    const hi = injection.insertedAt + injection.injectedLineCount;
    return vscode.languages.getDiagnostics(this.uri).some(
      (d) => d.severity === vscode.DiagnosticSeverity.Error && d.range.start.line >= lo && d.range.start.line < hi
    );
  }

  /** One RPC round-trip against the shadow URI. Returns null for the "no proof
   *  here" answers; throws otherwise (the caller classifies). */
  private async callRpc(
    method: string,
    pos: { line: number; character: number },
    goal: any
  ): Promise<ShadowQueryResult | null> {
    const tdp = { textDocument: { uri: this.uri.toString() }, position: pos };
    try {
      const resStr = await withTimeout(
        vscodeRequest(this.log, method, this.leanClient, this.uri.toString(), tdp, { pos, includeTheorems: false }),
        RPC_TIMEOUT_MS,
        "rpcTimeout"
      );
      const data = typeof resStr === "string" ? JSON.parse(resStr) : resStr; // compressed JSON string
      const steps = data?.steps ?? [];
      if (!steps.length) { throw new Error("zeroProofSteps"); } // term-mode proof, or not in a theorem
      return { steps: unmapSteps(this.injection!, steps), goal };
    } catch (err) {
      if (hasMark((err as Error).message || String(err), SILENT_NO_PROOF_MARKS)) { return null; }
      throw err;
    }
  }

  private async writeShadow(text: string): Promise<void> {
    if (this.doc && !this.doc.isClosed) {
      const doc = this.doc;
      const fullRange = new vscode.Range(doc.positionAt(0), doc.positionAt(doc.getText().length));
      const edit = new vscode.WorkspaceEdit();
      edit.replace(this.uri, fullRange, text);
      // A closed document rejects edits silently - we'd then wait for elaboration
      // of text that was never written, and hang until the timeout.
      if (await vscode.workspace.applyEdit(edit)) { return; }
      this.doc = null;
    }
    fs.writeFileSync(this.tempPath, text, "utf-8");
    // Opening (without showing) makes vscode send didOpen to the lean server.
    this.doc = await vscode.workspace.openTextDocument(this.uri);
  }

  dispose(): void {
    try {
      if (fs.existsSync(this.tempPath)) { fs.unlinkSync(this.tempPath); }
    } catch { /* best effort */ }
    this.doc = null;
    this.injection = null;
  }
}

// One shadow per source URI, reused across cursor moves.
const registry = new Map<string, ShadowDoc>();

export const getShadowDoc = (
  context: vscode.ExtensionContext,
  log: vscode.OutputChannel,
  leanClient: any,
  source: vscode.TextDocument
): ShadowDoc | null => {
  const key = source.uri.toString();
  let shadow = registry.get(key);
  if (!shadow) {
    shadow = ShadowDoc.create(context, log, leanClient, source) ?? undefined;
    if (!shadow) { return null; }
    registry.set(key, shadow);
  }
  return shadow;
};

export const disposeShadowDoc = (uri: string): void => {
  registry.get(uri)?.dispose();
  registry.delete(uri);
};

export const disposeAllShadowDocs = (): void => {
  registry.forEach((s) => s.dispose());
  registry.clear();
};
