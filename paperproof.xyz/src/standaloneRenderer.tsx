import React, { useState, useEffect, useRef } from "react";
import { createRoot } from 'react-dom/client';
import { NaturalProofTree } from "types";
import "@app/index.css";
import "@app/css/theorem.css";
import "./naturalRenderer.css";
import "./proofPanel.css";
import { Paperproof } from "../../embed/dist/react.js";
import JsonEditor from "./components/JsonEditor";
import { llmInstructions, fewShotExamples } from "@app/format/llmInstructions.js";
import { NaturalProofTreeSchema } from "@app/format";

import Nav from "./components/Nav";

const LS_KEY = 'paperproof-natural-json';
const MAX_ATTEMPTS = 3;

type ConvertingStatus = 'idle' | 'Reading image…' | 'Converting…';

const streamSSE = async (
  url: string,
  body: Record<string, unknown>,
  onThinking: (t: string) => void,
  onContent: (c: string) => void,
) => {
  const res = await fetch(url, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
  if (!res.ok) {
    const data = await res.json();
    throw new Error(data.error || 'Request failed');
  }
  const reader = res.body!.getReader();
  const decoder = new TextDecoder();
  let buf = '';
  while (true) {
    const { done, value } = await reader.read();
    if (done) break;
    buf += decoder.decode(value, { stream: true });
    const lines = buf.split('\n');
    buf = lines.pop() ?? '';
    for (const line of lines) {
      if (!line.startsWith('data: ')) continue;
      const payload = line.slice(6).trim();
      if (payload === '[DONE]') continue;
      try {
        const delta = JSON.parse(payload).choices?.[0]?.delta;
        if (delta?.reasoning_content) onThinking(delta.reasoning_content);
        if (delta?.content) onContent(delta.content);
      } catch {}
    }
  }
};

function tryValidateJson(jsonValue: string): string | null {
  if (!jsonValue.trim()) return 'Empty JSON';
  try {
    const result = NaturalProofTreeSchema.safeParse(JSON.parse(jsonValue));
    if (!result.success) return result.error.issues[0]?.message ?? 'Invalid JSON';
    return null;
  } catch (err) {
    return err instanceof Error ? err.message : 'Unknown error';
  }
}

const EXAMPLE_PROOFS = [
  {
    name: 's ∩ t = t ∩ s',
    text: `Theorem: for any sets s and t, s ∩ t = t ∩ s.
Proof: Immediate from the definition of intersection and commutativity of conjunction. ∎`,
    json: `{"format":"unicode","goal":"s ∩ t = t ∩ s","newHyps":[],"tactics":[{"tactic":"double inclusion","newSubgoals":[{"goal":"s ∩ t ⊆ t ∩ s","newHyps":[],"tactics":[{"tactic":"introduce x","newHyps":[{"name":"h","type":"x ∈ s ∩ t"}],"newGoal":"x ∈ t ∩ s"},{"tactic":"definition of ∩","dependsOn":["h"],"newHyps":[{"name":"h","type":"x ∈ s ∧ x ∈ t"}]},{"tactic":"definition of ∩","newGoal":"x ∈ t ∧ x ∈ s"},{"tactic":"commutativity of ∧","dependsOn":["h"],"closed":true}]},{"goal":"t ∩ s ⊆ s ∩ t","newHyps":[],"tactics":[{"tactic":"introduce x","newHyps":[{"name":"h","type":"x ∈ t ∩ s"}],"newGoal":"x ∈ s ∩ t"},{"tactic":"definition of ∩","dependsOn":["h"],"newHyps":[{"name":"h","type":"x ∈ t ∧ x ∈ s"}]},{"tactic":"definition of ∩","newGoal":"x ∈ s ∧ x ∈ t"},{"tactic":"commutativity of ∧","dependsOn":["h"],"closed":true}]}]}]}`,
  },
  {
    name: '√2 is irrational',
    text: `Theorem: √2 is irrational.
Proof: Suppose for contradiction that √2 = p/q with p, q integers and gcd(p,q) = 1.
Then 2 = p²/q², so p² = 2q². Thus 2 | p², hence 2 | p.
Write p = 2k. Then 4k² = 2q², so q² = 2k², meaning 2 | q.
But then 2 | gcd(p,q) = 1 - a contradiction. ∎`,
    json: `{"format":"unicode","goal":"√2 ∉ ℚ","newHyps":[],"tactics":[{"tactic":"assume the opposite","newGoal":"contradiction","newHyps":[{"name":"h","type":"√2 ∈ ℚ"}]},{"tactic":"write √2 = p/q in lowest terms","dependsOn":["h"],"newHyps":[{"name":"p","type":"ℤ"},{"name":"q","type":"ℤ, q ≠ 0"},{"name":"eq","type":"√2 = p/q"},{"name":"coprime","type":"gcd(p, q) = 1"}]},{"tactic":"square both sides","dependsOn":["eq"],"newHyps":[{"name":"eq","type":"p² = 2q²"}]},{"tactic":"Theorem: if p² = 2q² then 2 | p","dependsOn":["eq"],"newHyps":[{"name":"p_even","type":"2 | p"}]},{"tactic":"definition of even","dependsOn":["p_even"],"newHyps":[{"name":"k","type":"ℤ"},{"name":"p_eq","type":"p = 2k"}]},{"tactic":"p = 2k, so p² = 4k², and since p² = 2q², we get q² = 2k²","dependsOn":["p_eq"],"newHyps":[{"name":"eq","type":"q² = 2k²"}]},{"tactic":"Theorem: if 2 | q² then 2 | q","dependsOn":["eq"],"newHyps":[{"name":"q_even","type":"2 | q"}]},{"tactic":"contradiction","dependsOn":["p_even","q_even","coprime"],"closed":true}]}`,
  },
  {
    name: 'Infinitely many primes',
    text: `Theorem: the set of prime numbers is infinite.
Proof: Suppose not - suppose the set of prime numbers is finite, and list them in ascending order: 2, 3, 5, 7, 11, …, p.
Let N = (2·3·5·7·11···p) + 1. Then N > 1, so N is divisible by some prime q. Because q is prime, q must be one of 2, 3, 5, 7, 11, …, p.
Thus q divides 2·3·5·7·11···p, and so q does not divide (2·3·5·7·11···p) + 1 = N. Hence N is divisible by q and not divisible by q - a contradiction. ∎`,
    json: `{"format":"unicode","goal":"set of prime numbers is infinite","newHyps":[],"tactics":[{"tactic":"assume the opposite","newGoal":"contradiction","newHyps":[{"name":"h_finite","type":"set of prime numbers is finite"}]},{"tactic":"multiply all prime numbers, add 1","dependsOn":["h_finite"],"newHyps":[{"name":"N","type":"2 * 3 * 5 * ... * p + 1"}]},{"tactic":"because N is bigger than all prime numbers, it must be composite","dependsOn":["N"],"newHyps":[{"name":"one","type":"N > 1"},{"name":"N_is_composite","type":"N is composite"}]},{"tactic":"Theorem: every integer > 1 has a prime divisor","dependsOn":["one","N_is_composite"],"newHyps":[{"name":"q_exists","type":"∃ q, (q is prime) ∧ (q | N)"}]},{"tactic":"unfold","dependsOn":["q_exists"],"newHyps":[{"name":"q","type":"ℕ"},{"name":"q_is_prime","type":"q is prime"},{"name":"q_divides_N","type":"q | N"}]},{"tactic":"q is prime, and we multiplied all prime numbers","dependsOn":["q_is_prime"],"newHyps":[{"name":"q_is_one_of_primes","type":"q is one of 2, 3, 5, 7, ..., p"}]},{"tactic":"if q is one of [a,b,c], then q can divide a*b*c","dependsOn":["q_is_one_of_primes"],"newHyps":[{"name":"q_divides","type":"q | 2 * 3 * 5 * 7 * ... * p"}]},{"tactic":"Theorem: if q | m then q ∤ m + 1","dependsOn":["q_divides"],"newHyps":[{"name":"q_doesnt_divide_N","type":"q ∤ (2 * 3 * 5 * 7 * ... * p) + 1"}]},{"tactic":"definition of N","dependsOn":["q_doesnt_divide_N"],"newHyps":[{"name":"q_doesnt_divide_N","type":"q ∤ N"}]},{"tactic":"contradiction","dependsOn":["q_doesnt_divide_N","q_divides_N"],"closed":true}]}`,
  },
];

function StandaloneRenderer() {
  const [jsonInput, setJsonInput] = useState<string>(
    () => localStorage.getItem(LS_KEY) || ""
  );
  const [proof, setProof] = useState<NaturalProofTree | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [isEditing, setIsEditing] = useState<boolean>(false);
  const [isPrintView, setIsPrintView] = useState<boolean>(false);

  const validateAndCompile = (jsonValue: string) => {
    if (!jsonValue.trim()) {
      setProof(null);
      setError(null);
      setIsEditing(false);
      return;
    }

    try {
      const parsed = NaturalProofTreeSchema.safeParse(JSON.parse(jsonValue));
      if (!parsed.success) throw new Error(parsed.error.issues[0]?.message ?? 'Invalid JSON');

      localStorage.setItem(LS_KEY, jsonValue);
      setError(null);
      setIsEditing(false);
      setProof(parsed.data);

    } catch (err) {
      const errorMessage = err instanceof Error ? err.message : 'Unknown error occurred';
      setError('Error: ' + errorMessage);
      setIsEditing(false);
      // Keep the last valid tree visible - don't clear proof
    }
  };

  // Compile saved JSON on first mount
  useEffect(() => {
    const saved = localStorage.getItem(LS_KEY);
    if (saved) validateAndCompile(saved);
  }, []); // eslint-disable-line react-hooks/exhaustive-deps

  const handleValidationChange = (isValid: boolean, _markers: any[]) => {
    if (isValid) validateAndCompile(jsonInput);
    // When invalid, leave the last tree visible; isEditing is already set by handleJsonChange
  };

  const handleJsonChange = (newValue: string) => {
    setJsonInput(newValue);
    setIsEditing(true);
    setTimeout(() => validateAndCompile(newValue), 300);
  };

  const [nlInput, setNlInput] = useState('');
  const [droppedImage, setDroppedImage] = useState<string | null>(null); // base64 data URL
  const [isDragOver, setIsDragOver] = useState(false);
  const [status, setStatus] = useState<ConvertingStatus>('idle');
  const [nlError, setNlError] = useState<string | null>(null);
  const [isJsonOpen, setIsJsonOpen] = useState(false);
  const [isCopied, setIsCopied] = useState(false);
  const [thinkingText, setThinkingText] = useState('');
  const thinkingRef = useRef<HTMLDivElement>(null);
  const pendingThinkingRef = useRef('');
  const isMouseInThinkingRef = useRef(false);

  const onThinkingMouseEnter = () => { isMouseInThinkingRef.current = true; };
  const onThinkingMouseLeave = () => {
    isMouseInThinkingRef.current = false;
    setThinkingText(pendingThinkingRef.current);
  };

  const updateThinkingText = (text: string) => {
    pendingThinkingRef.current = text;
    if (!isMouseInThinkingRef.current) setThinkingText(text);
  };

  const resetThinkingText = () => {
    pendingThinkingRef.current = '';
    isMouseInThinkingRef.current = false;
    setThinkingText('');
  };

  const readImageFile = (file: File) => {
    if (!file.type.startsWith('image/')) return;
    const reader = new FileReader();
    reader.onload = (e) => setDroppedImage(e.target!.result as string);
    reader.readAsDataURL(file);
  };

  const handleDragOver = (e: React.DragEvent) => { e.preventDefault(); setIsDragOver(true); };
  const handleDragLeave = () => setIsDragOver(false);
  const handleDrop = (e: React.DragEvent) => {
    e.preventDefault();
    setIsDragOver(false);
    const file = e.dataTransfer.files[0];
    if (file) readImageFile(file);
  };

  useEffect(() => {
    const onPaste = (e: ClipboardEvent) => {
      for (const item of Array.from(e.clipboardData?.items ?? [])) {
        if (item.type.startsWith('image/')) {
          e.preventDefault();
          const file = item.getAsFile();
          if (file) readImageFile(file);
          return;
        }
      }
    };
    window.addEventListener('paste', onPaste);
    return () => window.removeEventListener('paste', onPaste);
  }, []);

  useEffect(() => {
    const el = thinkingRef.current;
    if (!el || isMouseInThinkingRef.current) return;
    el.scrollTop = el.scrollHeight;
  }, [thinkingText]);

  const convertNlToJson = async () => {
    if (!nlInput.trim() && !droppedImage) return;

    const preloaded = EXAMPLE_PROOFS.find(ex => ex.text === nlInput);
    if (preloaded) {
      handleJsonChange(preloaded.json);
      return;
    }

    setStatus('Converting…');
    setNlError(null);
    resetThinkingText();

    let currentJson = '';
    let currentError: string | null = null;

    // Phase 1: image → text (non-thinking, streamed for progress)
    let proofText = nlInput;
    if (droppedImage) {
      setStatus('Reading image…');
      let extracted = '';
      try {
        await streamSSE(
          '/api/image-to-text-stream',
          { imageDataUrl: droppedImage, additionalText: nlInput || undefined },
          () => {},
          (chunk) => { extracted += chunk; updateThinkingText(extracted); setNlInput(extracted); },
        );
      } catch (err) {
        setNlError(err instanceof Error ? err.message : 'Image reading failed');
        setStatus('idle');
        return;
      }
      proofText = extracted;
    }

    // Phase 2: text → JSON (thinking, with retries)
    const runAttempt = async (prev: { json: string; error: string } | null) => {
      const body: Record<string, unknown> = { proof: proofText };
      if (prev) body.previousAttempt = prev;
      resetThinkingText();
      let thinking = '';
      let content = '';
      await streamSSE(
        '/api/natural-to-proof-stream',
        body,
        (chunk) => { thinking += chunk; updateThinkingText(thinking); },
        (chunk) => { content += chunk; },
      );
      content = content.replace(/^```(?:json)?\s*/i, '').replace(/\s*```\s*$/, '').trim();
      return { json: content, error: tryValidateJson(content) };
    };

    setStatus('Converting…');
    for (let attempt = 1; attempt <= MAX_ATTEMPTS; attempt++) {
      try {
        const result = await runAttempt(
          currentError ? { json: currentJson, error: currentError } : null
        );
        currentJson = result.json;
        currentError = result.error;
        if (!currentError) break;
      } catch (err) {
        setNlError(err instanceof Error ? err.message : 'Conversion failed');
        setStatus('idle');
        return;
      }
    }

    handleJsonChange(currentJson);
    setStatus('idle');
  };

  useEffect(() => {
    const onKey = (e: KeyboardEvent) => { if (e.key === 'Escape') setIsPrintView(false); };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  }, []);

  useEffect(() => {
    document.body.classList.toggle('is-print-view', isPrintView);
  }, [isPrintView]);

  // Glass overlay: shown while the user is mid-edit or the current JSON has an error
  const showOverlay = isEditing || (!!error && !!proof);

  const proofTreeContent = proof && <Paperproof proof={proof} fit="none"/>;

  if (isPrintView) {
    return (
      <div className="natural-print-view">
        <button className="natural-print-exit" onClick={() => setIsPrintView(false)}>← back</button>
        {proofTreeContent}
      </div>
    );
  }

  return (
    <div className="natural-page">

      <Nav />

      <main className="natural-main">

        {/* LEFT: sticky input panel */}
        <div className="natural-left">
          <div className="natural-label">Playground</div>
          <h1 className="natural-heading">Any proof. One notation.</h1>
          <p className="natural-desc">
            We write <em>x² + 2x = 5</em> instead of <em>"a square and two roots equal five"</em>.<br/>
Paperproof does the same for entire proofs - a structured, unambiguous diagram that corresponds to the formal logic behind the proof, and yet remains perfectly readable.
          </p>

          <div
            className={`natural-nl-section${isDragOver ? ' -drag-over' : ''}`}
            onDragOver={handleDragOver}
            onDragLeave={handleDragLeave}
            onDrop={handleDrop}
          >
            <textarea
              className="natural-nl-textarea"
              value={nlInput}
              onChange={e => setNlInput(e.target.value)}
              onKeyDown={e => { if (e.key === 'Enter' && (e.metaKey || e.ctrlKey)) convertNlToJson(); }}
              placeholder={"Describe a mathematical proof in plain language, \nor paste an image"}
            />
            {droppedImage && (
              <div className="natural-image-preview">
                <img src={droppedImage} className="natural-image-thumb" alt="proof" />
                <button className="natural-image-remove" onClick={() => setDroppedImage(null)}>×</button>
              </div>
            )}
            <button
              className="natural-convert-btn"
              onClick={convertNlToJson}
              disabled={status !== 'idle' || (!nlInput.trim() && !droppedImage)}
            >
              {status !== 'idle' ? status : 'Convert →'}
            </button>
          </div>

          <div className="natural-examples">
            <div className="natural-examples-label">or try a famous proof:</div>
            <div className="natural-examples-chips">
              {EXAMPLE_PROOFS.map(ex => (
                <button
                  key={ex.name}
                  className={`natural-examples-chip${nlInput === ex.text ? ' -active' : ''}`}
                  onClick={() => setNlInput(ex.text)}
                >
                  {ex.name}
                </button>
              ))}
            </div>
          </div>

          {thinkingText && (
            <div className="natural-thinking">
              <div className="natural-thinking-label">
                {status !== 'idle' ? status : 'Thought process'}
              </div>
              <div
                className="natural-thinking-body"
                ref={thinkingRef}
                onMouseEnter={onThinkingMouseEnter}
                onMouseLeave={onThinkingMouseLeave}
              >
                {thinkingText}
              </div>
            </div>
          )}
        </div>

        {/* RIGHT: tree + json */}
        <div className="natural-right">
          {nlError && <div className="natural-error">{nlError}</div>}

          {proof && (
            <div className="natural-tree-wrap">
              <div className="natural-proof-body">
                {showOverlay && <div className="natural-proof-overlay" />}
                {proofTreeContent}
              </div>
              <button className="natural-print-btn" onClick={() => setIsPrintView(true)}>Print</button>
            </div>
          )}

          {(jsonInput || proof) && <div className="pp-panel natural-editor-wrap">
            <div className={`pp-panel-tabs${isJsonOpen ? '' : ' -no-border'}`}>
              <span className="pp-panel-tab -active">≡ proof.json ×</span>
              <div className="natural-tabs-right">
                {isJsonOpen && (
                  <button className={`natural-json-toggle -with-icon${isCopied ? ' -copied' : ''}`} onClick={() => {
                    navigator.clipboard.writeText(
                      [
                        llmInstructions,
                        ...fewShotExamples.flatMap(ex => [`User: ${ex.text}`, `Assistant: ${ex.json}`]),
                      ].join('\n\n')
                    );
                    setIsCopied(true);
                    setTimeout(() => setIsCopied(false), 2000);
                  }}>
                    <svg style={{ position: 'absolute', left: 10, top: '50%', transform: 'translateY(-50%)' }} width="10" height="10" viewBox="0 0 10 10" fill="none" xmlns="http://www.w3.org/2000/svg">
                      <rect x="0.6" y="2.1" width="6.3" height="7.3" rx="1.1" stroke="currentColor" strokeWidth="1.1"/>
                      <rect x="3.1" y="0.6" width="6.3" height="7.3" rx="1.1" stroke="currentColor" strokeWidth="1.1" fill="var(--panel-header)"/>
                    </svg>
                    {isCopied ? 'copied!' : 'format instructions'}
                  </button>
                )}
                <button className="natural-json-toggle" onClick={() => setIsJsonOpen(o => !o)}>
                  {isJsonOpen ? '↑ hide source' : '↓ show source'}
                </button>
              </div>
            </div>
            {isJsonOpen && (
              <JsonEditor
                value={jsonInput}
                onChange={handleJsonChange}
                onValidationChange={handleValidationChange}
                height="360px"
              />
            )}
          </div>}
        </div>

      </main>

    </div>
  );
}

const root = createRoot(document.getElementById("root")!);
root.render(<StandaloneRenderer />);
