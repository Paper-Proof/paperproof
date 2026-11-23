import React, { useEffect, useLayoutEffect, useMemo, useState } from "react";
import { Position, Settings } from "types";
import type { PaperproofProps } from "../../../react";
import { formatProblems } from "@app/format";
import ProofTreeView, { DEFAULT_SETTINGS } from "../ProofTreeView";
import ProofTreeErrorBoundary from "../ProofTreeErrorBoundary";
import { useThemeMenu } from "./components/ThemeMenu";
import { KATEX_CSS, useKatex } from "./services/katex";
import { Parsed, View, parseProof } from "./services/parseProof";

export interface PaperproofViewProps extends Omit<PaperproofProps, "fit" | "className" | "style"> {
  error?: string;
  onLayout?: () => void;
  onState?: (state: "rendered" | "error") => void;
}

interface TreeProps {
  view: View;
  position?: Position;
  onLayout?: () => void;
}

const Tree = ({ view, position, onLayout }: TreeProps) => {
  const [collapsedBoxIds, setCollapsedBoxIds] = useState(view.collapsedBoxIds);
  const [deletedHypothesisNames, setDeletedHypothesisNames] = useState(view.deletedHypothesisNames);
  useLayoutEffect(() => onLayout?.());
  return (
    <ProofTreeErrorBoundary>
      <ProofTreeView
        proofTree={view.tree}
        highlights={view.highlights}
        settings={view.settings}
        latexSettings={view.latexSettings}
        collapsedBoxIds={collapsedBoxIds}               setCollapsedBoxIds={setCollapsedBoxIds}
        deletedHypothesisNames={deletedHypothesisNames} setDeletedHypothesisNames={setDeletedHypothesisNames}
        position={position}
      />
    </ProofTreeErrorBoundary>
  );
};

const PaperproofView = (props: PaperproofViewProps) => {
  const settings = useMemo<Settings>(() => ({
    ...DEFAULT_SETTINGS,
    fontSize: props.fontSize || DEFAULT_SETTINGS.fontSize,
    isUnlimitedWidth: !!props.unlimitedWidth,
  }), [props.fontSize, props.unlimitedWidth]);
  const parsed = useMemo<Parsed>(() => props.error === undefined ?
    parseProof(props.proof, settings) :
    { kind: "error", message: props.error }, [props.error, props.proof, settings]);
  const view = "view" in parsed ? parsed.view : null;
  const problems = "problems" in parsed ? parsed.problems : [];
  const errors = problems.filter((problem) => problem.level === "error");
  const isKatexReady = useKatex(!!view?.latexSettings.isActive);
  const { look, onContextMenu, menu } = useThemeMenu(props.theme, props.darkBars);

  useEffect(() => {
    problems.filter((problem) => problem.level === "warning").forEach((problem) => console.warn(`[paperproof] ${problem.path}: ${problem.message}`));
  }, [parsed]);

  useLayoutEffect(() => {
    if (isKatexReady) props.onState?.(view && errors.length === 0 ? "rendered" : "error");
  });

  return (
    <div className={`pp-root -theme-${look.theme} -${parsed.kind}${look.darkBars ? " -dark-bars" : ""}`} onContextMenu={onContextMenu}>
      {parsed.kind === "error" && <pre className="pp-error">Paperproof: {parsed.message}</pre>}
      {view && isKatexReady && <>
        {view.latexSettings.isActive && <link rel="stylesheet" href={KATEX_CSS}/>}
        <div className="pp-wrap">
          <Tree view={view} position={props.position} onLayout={props.onLayout}/>
        </div>
      </>}
      {errors.length > 0 && <pre className="pp-problems">{formatProblems(errors)}</pre>}
      {menu}
    </div>
  );
};

export default PaperproofView;
