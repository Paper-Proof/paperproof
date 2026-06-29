import React, { useState, useEffect, useLayoutEffect, useRef } from 'react';
import { createRoot } from 'react-dom/client';
import Nav from './components/Nav';
import './landingPage.css';
import './proofPanel.css';

function ProofTree() {
  return (
    <div className="proof-tree -isGreenHypothesesOFF">
      <section className="box" id="box-1">
        <header className="-row2Absent">
          <div className="title">hypotheses</div>
          <div className="row-1">
            <div>
              <div id="hypothesis-_uniq.2928.2" className="hypothesis data"><span className="name">s</span>: <span className="text">Set ℕ</span></div>
              <div id="hypothesis-_uniq.2928.3" className="hypothesis data"><span className="name">t</span>: <span className="text">Set ℕ</span></div>
            </div>
          </div>
        </header>
        <div className="box-insides">
          <div className="hypothesis-table">
            <div className="tactic -hypothesis-tactic" id="tactic-2-0">ext x</div>
            <div className="htr-hyp">
              <div id="hypothesis-_uniq.2928.24" className="hypothesis data"><span className="name">x</span>: ℕ</div>
            </div>
          </div>
          <div className="child-boxes">
            <section className="box" id="box-2">
              <div className="box-insides">
                <div className="hypothesis-table">
                  <div className="tactic -hypothesis-tactic" id="tactic-4-0">intro h1</div>
                  <div className="htr-hyp">
                    <div id="hypothesis-_uniq.2928.35" className="hypothesis"><span className="name">h1</span>: x ∈ s ∩ t</div>
                  </div>
                  <div className="tactic -hypothesis-tactic" id="tactic-5-0">rw [Set.mem_inter_iff]</div>
                  <div className="htr-hyp">
                    <div id="hypothesis-_uniq.2928.55" className="hypothesis"><span className="name">h1</span>: x ∈ s ∧ x ∈ t</div>
                  </div>
                  <div className="tactic -hypothesis-tactic" id="tactic-6-0">rw [and_comm]</div>
                  <div className="htr-hyp">
                    <div id="hypothesis-_uniq.2928.74" className="hypothesis"><span className="name">h1</span>: x ∈ t ∧ x ∈ s</div>
                  </div>
                </div>
                <div className="goals">
                  <div className="tactic -success" id="tactic-7">🎉 exact h1 🎉</div>
                  <div className="gtr-goal"><div className="goal">x ∈ t ∩ s</div></div>
                </div>
                <div className="goals">
                  <div className="tactic -hypothesis-tactic" id="tactic-4">intro h1</div>
                  <div className="gtr-goal"><div className="goal">x ∈ s ∩ t → x ∈ t ∩ s</div></div>
                </div>
              </div>
            </section>
            <section className="box" id="box-3">
              <div className="box-insides">
                <div className="hypothesis-table">
                  <div className="tactic -hypothesis-tactic" id="tactic-8-0">intro h2</div>
                  <div className="htr-hyp">
                    <div id="hypothesis-_uniq.2928.82" className="hypothesis"><span className="name">h2</span>: x ∈ t ∩ s</div>
                  </div>
                  <div className="tactic -hypothesis-tactic" id="tactic-9-0">rw [Set.mem_inter_iff]</div>
                  <div className="htr-hyp">
                    <div id="hypothesis-_uniq.2928.102" className="hypothesis"><span className="name">h2</span>: x ∈ t ∧ x ∈ s</div>
                  </div>
                  <div className="tactic -hypothesis-tactic" id="tactic-10-0">rw [and_comm]</div>
                  <div className="htr-hyp">
                    <div id="hypothesis-_uniq.2928.121" className="hypothesis"><span className="name">h2</span>: x ∈ s ∧ x ∈ t</div>
                  </div>
                </div>
                <div className="goals">
                  <div className="tactic -success" id="tactic-11">🎉 exact h2 🎉</div>
                  <div className="gtr-goal"><div className="goal">x ∈ s ∩ t</div></div>
                </div>
                <div className="goals">
                  <div className="tactic -hypothesis-tactic" id="tactic-8">intro h2</div>
                  <div className="gtr-goal"><div className="goal">x ∈ t ∩ s → x ∈ s ∩ t</div></div>
                </div>
              </div>
            </section>
          </div>
          <div className="goals">
            <div className="tactic -hypothesis-tactic" id="tactic-3">apply Iff.intro</div>
            <div className="gtr-goal"><div className="goal">x ∈ s ∩ t ↔ x ∈ t ∩ s</div></div>
          </div>
          <div className="goals">
            <div className="tactic -hypothesis-tactic" id="tactic-2">ext x</div>
            <div className="gtr-goal"><div className="goal">s ∩ t = t ∩ s</div></div>
          </div>
        </div>
        <footer><div className="title">theorem</div></footer>
      </section>
    </div>
  );
}

// Animation assignments: [elementId, direction, delaySeconds]
// null id = handled via text-content matching in useLayoutEffect
const ANIMS_BY_ID: Array<[string, 'fd' | 'sd' | 'fu' | 'su', number]> = [
  // top-down: hypotheses slide in from under tactic above; tactics fade down
  ['hypothesis-_uniq.2928.2',   'sd', 0.20],  // s: Set ℕ
  ['hypothesis-_uniq.2928.3',   'sd', 0.20],  // t: Set ℕ
  ['tactic-2-0',                'fd', 0.60],  // ext x (hyp-tactic)
  ['hypothesis-_uniq.2928.24',  'sd', 1.00],  // x: ℕ
  // h1 branch (top-down)
  ['tactic-4-0',                'fd', 1.60],  // intro h1
  ['hypothesis-_uniq.2928.35',  'sd', 1.85],  // h1: x ∈ s ∩ t
  ['tactic-5-0',                'fd', 2.10],  // rw [Set.mem_inter_iff]
  ['hypothesis-_uniq.2928.55',  'sd', 2.35],  // h1: x ∈ s ∧ x ∈ t
  ['tactic-6-0',                'fd', 2.60],  // rw [and_comm]
  ['hypothesis-_uniq.2928.74',  'sd', 2.85],  // h1: x ∈ t ∧ x ∈ s
  // h2 branch starts 1.5s after h1 (top-down)
  ['box-3',                     'fu', 1.50],  // box-3 fades in with box-2 (both goals from apply Iff.intro)
  ['tactic-8-0',                'fd', 3.10],  // intro h2
  ['hypothesis-_uniq.2928.82',  'sd', 3.35],  // h2: x ∈ t ∩ s
  ['tactic-9-0',                'fd', 3.60],  // rw [Set.mem_inter_iff]
  ['hypothesis-_uniq.2928.102', 'sd', 3.85],  // h2: x ∈ t ∧ x ∈ s
  ['tactic-10-0',               'fd', 4.10],  // rw [and_comm]
  ['hypothesis-_uniq.2928.121', 'sd', 4.35],  // h2: x ∈ s ∧ x ∈ t
  // bottom-up: goals and goal-side tactics
  ['tactic-2',  'fu', 0.65],  // ext x (goal-side)
  ['tactic-3',  'fu', 1.35],  // apply Iff.intro (goal-side)
  // h1 branch (bottom-up)
  ['box-2',     'fu', 1.50],  // box-2 fades in just before h1 content
  ['tactic-4',  'fu', 1.95],  // intro h1 (goal-side)
  ['tactic-7',  'fu', 2.80],  // exact h1 -success
  // h2 branch (bottom-up, +1.5s)
  ['tactic-8',  'fu', 3.45],  // intro h2 (goal-side)
  ['tactic-11', 'fu', 4.30],  // exact h2 -success
];

// Goals have no IDs - matched by text content
const ANIMS_BY_TEXT: Array<[string, 'fu' | 'su', number]> = [
  ['s ∩ t = t ∩ s',            'su', 0.30],
  ['x ∈ s ∩ t ↔ x ∈ t ∩ s',  'su', 1.05],
  ['x ∈ s ∩ t → x ∈ t ∩ s',  'su', 1.65],  // h1 branch goal
  ['x ∈ t ∩ s',               'su', 2.40],  // h1 goal after intro h1
  ['x ∈ s ∩ t',               'su', 3.90],  // h2 goal after intro h2  (+1.5s)
  ['x ∈ t ∩ s → x ∈ s ∩ t',  'su', 1.65],  // h2 branch goal (same time as h1, both from apply Iff.intro)
];

type Arrow = { x1: number; y1: number; x2: number; y2: number; delay: number };

function offsetRelTo(el: HTMLElement, ancestor: HTMLElement) {
  let x = 0, y = 0;
  let cur: HTMLElement | null = el;
  while (cur && cur !== ancestor) {
    x += cur.offsetLeft;
    y += cur.offsetTop;
    cur = cur.offsetParent as HTMLElement | null;
  }
  return { x, y, w: el.offsetWidth, h: el.offsetHeight };
}

function ProofFigure() {
  const containerRef = useRef<HTMLDivElement>(null);
  const [arrows, setArrows] = useState<Arrow[]>([]);

  useLayoutEffect(() => {
    const apply = (el: HTMLElement | null, dir: 'fd' | 'sd' | 'fu' | 'su', delay: number) => {
      if (!el) return;
      if (dir === 'sd') {
        el.style.animation = `ppSlideDown .35s ease both`;
        el.style.animationDelay = `${delay}s`;
      } else if (dir === 'su') {
        el.style.animation = `ppSlideUp .35s ease both`;
        el.style.animationDelay = `${delay}s`;
      } else {
        el.style.opacity = '0';
        el.style.animation = `${dir === 'fd' ? 'ppFadeDown' : 'ppFadeUp'} .45s ease both`;
        el.style.animationDelay = `${delay}s`;
      }
    };

    for (const [id, dir, delay] of ANIMS_BY_ID) {
      apply(document.getElementById(id), dir, delay);
    }

    const container = containerRef.current;
    if (container) {
      container.querySelectorAll<HTMLElement>('.goal').forEach(el => {
        const text = el.textContent?.trim() ?? '';
        const match = ANIMS_BY_TEXT.find(([t]) => t === text);
        if (match) apply(el, match[1], match[2]);
      });
    }
  }, []);

  useEffect(() => {
    const container = containerRef.current;
    if (!container) return;
    document.fonts.ready.then(() => {
      const pairs: [string, string, number][] = [
        ['hypothesis-_uniq.2928.74',  'tactic-7',  2.80],
        ['hypothesis-_uniq.2928.121', 'tactic-11', 4.30],
      ];
      const computed = pairs.flatMap(([fromId, toId, delay]) => {
        const from = document.getElementById(fromId);
        const to   = document.getElementById(toId);
        if (!from || !to) return [];
        const f = offsetRelTo(from, container);
        const t = offsetRelTo(to,   container);
        return [{ x1: f.x + f.w / 2, y1: f.y + f.h, x2: t.x + t.w / 2, y2: t.y, delay }];
      });
      setArrows(computed);
    });
  }, []);

  return (
    <figure className="lp-proof-figure">
      <div className="lp-proof-panel pp-panel">
        <div className="pp-panel-tabs">
          <span className="pp-panel-tab">≡ Lean Infoview</span>
          <span className="pp-panel-tab -active">≡ Paperproof ×</span>
        </div>
        <div ref={containerRef} className="lp-proof-container">
          <ProofTree />
          <svg>
            <defs>
              <marker id="arrowhead" markerWidth="5" markerHeight="5" refX="4" refY="2.5" orient="auto">
                <path d="M0,0 L0,5 L5,2.5 z" fill="#a0ceb0" />
              </marker>
            </defs>
            {arrows.map((a, i) => (
              <path
                key={i}
                d={`M${a.x1},${a.y1} L${a.x2},${a.y2}`}
                fill="none"
                stroke="#a0ceb0"
                strokeWidth="2"
                markerEnd="url(#arrowhead)"
                style={{ opacity: 0, animation: `ppFadeDown .45s ease both`, animationDelay: `${a.delay}s` }}
              />
            ))}
          </svg>
        </div>
      </div>
      <figcaption>commutativityOfIntersections.lean - as Paperproof draws it</figcaption>
    </figure>
  );
}

function LandingPage() {
  return (
    <div className="lp-root">

      <div className="lp-vignette" />

      <Nav />

      {/* HERO */}
      <section className="lp-section lp-hero">
        <div>
          <div className="lp-label" style={{ marginBottom: 26 }}>Lean 4 · VSCode extension</div>
          <h1>A proof tree for every<br />Lean theorem.</h1>
          <p className="lp-hero-p">
            Lean proof is a list of tactics. Lean's default interface shows available goals and hypotheses after a <i>single</i> tactic. <br/>Paperproof shows the <i>entire proof</i>, the way a mathematician would sketch it on paper.</p>
          <div className="lp-hero-actions">
            <a href="https://github.com/Paper-Proof/paperproof" target="_blank" className="lp-btn -dark">Install for VSCode →</a>
          </div>
          <div className="lp-hero-tagline">Free &amp; open-source · works inside the proof assistant and on paper</div>
        </div>

        <ProofFigure />
      </section>

      {/* THE IDEA */}
      <section id="problem" className="lp-section lp-idea">
        <div className="lp-section-divider lp-idea-grid">
          <div>
            <div className="lp-label" style={{ marginBottom: 18 }}>The idea</div>
            <h2 className="lp-h2" style={{ margin: "0 0 20px" }}>Mathematics is about hypotheses and goals.</h2>
            <p className="lp-p" style={{ margin: "0 0 16px" }}>
              A list of tactics is barely helpful in understanding the mathematical content behind the proof.
              In order to read a Lean proof, we have to inspect the proof state (hypotheses and goals) after every tactic.
            </p>
            <p className="lp-p">
              Paperproof shows how hypotheses and goals were transforming <em>throughout the proof</em>, laid out in a consistent spatial notation, so that structure and dependencies is something you simply <em>see</em>.
            </p>
          </div>
          <div className="lp-idea-compare">
            <div className="lp-card">
              <div className="lp-mono-label" style={{ marginBottom: 12 }}>The tactics you write</div>
              <pre className="lp-idea-pre">{"...\nintro h1\nrw [mem_inter_iff] at h1\nrw [add_comm] at h1\n..."}</pre>
              <div className="lp-idea-invisible-note">↑ the proof state is invisible</div>
            </div>
            <div className="lp-idea-arrow">→</div>
            <div className="lp-card lp-idea-proof-card">
              <div className="lp-mono-label" style={{ marginBottom: 14 }}>The proof you read</div>
              <div className="proof-tree -isGreenHypothesesOFF">
                <div className="box-insides">
                  <div className="hypothesis-table">
                    <div className="tactic -hypothesis-tactic">intro h1</div>
                    <div className="htr-hyp">
                      <div className="hypothesis"><span className="name">h1</span>: x ∈ s ∩ t</div>
                    </div>
                    <div className="tactic -hypothesis-tactic">rw [mem_inter_iff] at h1</div>
                    <div className="htr-hyp">
                      <div className="hypothesis"><span className="name">h1</span>: x ∈ s ∧ x ∈ t</div>
                    </div>
                    <div className="tactic -hypothesis-tactic">rw [and_comm] at h1</div>
                    <div className="htr-hyp">
                      <div className="hypothesis"><span className="name">h1</span>: x ∈ t ∧ x ∈ s</div>
                    </div>
                  </div>
                </div>
              </div>
            </div>
          </div>
        </div>
      </section>

      {/* THE NOTATION */}
      <section id="read" className="lp-section lp-notation">
        <div className="lp-section-divider">
          <div className="lp-label" style={{ marginBottom: 18 }}>The notation</div>
          <h2 className="lp-h2" style={{ margin: "0 0 8px", maxWidth: "16em" }}>Three boxes. Learn it in one glance.</h2>
          <p className="lp-p" style={{ maxWidth: "34em", margin: "0 0 40px" }}>The entire visual language is small enough to learn in a glance - colour tells you what a fact <em>is</em>, position tells you where it came from.</p>
          <div className="lp-notation-grid">
            {[
              { badge: <div className="hypothesis"><span className="name">h</span>: x ∈ s</div>, title: "Hypothesis", desc: "Everything we know: variables, assumptions, and facts derived during the proof." },
              { badge: <div className="goal">s ∩ t = t ∩ s</div>, title: "Goal", desc: "What's left to show. Close every goal and the theorem is done." },
              { badge: <div className="tactic -hypothesis-tactic">intro h</div>, title: "Tactic", desc: "A verb. Tells us what action transformed one Hypothesis/Goal into another." },
            ].map(({ badge, title, desc }) => (
              <div key={title} className="lp-card lp-notation-card">
                <div className="lp-notation-badge-wrap">{badge}</div>
                <h3>{title}</h3>
                <p>{desc}</p>
              </div>
            ))}
          </div>
        </div>
      </section>

      {/* INSTALL */}
      <section id="install" className="lp-section lp-install">
        <div className="lp-install-box">
          <img src="/paper.png" alt="" className="lp-install-paper" />
          <div>
            <div className="lp-label" style={{ marginBottom: 18 }}>Get started</div>
            <h2 className="lp-h2">See your next proof<br />in two minutes.</h2>
            <p className="lp-install-p">Install the Paperproof VSCode extension &amp; Lean library, open any <span className="lp-install-lean">.lean</span> file of yours, and see your proof render as you type.</p>
            <a href="https://github.com/Paper-Proof/paperproof#installation" target="_blank" rel="noopener noreferrer" className="lp-btn -light">Read installation instructions →</a>
          </div>
          <div className="lp-install-steps">
            {[
              { n: "01", title: "Install Paperproof VSCode extension", desc: "" },
              { n: "02", title: "Install Paperproof Lean library", desc: "" },
              { n: "03", title: "Open the panel", desc: <>Click on Paperproof icon and start proving.</> },
            ].map(({ n, title, desc }) => (
              <div key={n} className="lp-install-step">
                <span className="lp-install-step-n">{n}</span>
                <div>
                  <div className="lp-install-step-title">{title}</div>
                  <div className="lp-install-step-desc">{desc}</div>
                </div>
              </div>
            ))}
          </div>
        </div>
      </section>

      {/* FOOTER / PAPER */}
      <footer id="paper" className="lp-footer">
        <div className="lp-footer-grid">
          <div>
            <div className="lp-footer-brand">
              <img src="/paper.png" alt="" />
              <span>paperproof</span>
            </div>
            <p className="lp-footer-p">A new representation for formal proofs - readable inside the proof assistant and on paper.
            {/* Read the paper for the notation, design and examples. TODO */}

            </p>
          </div>
          <div className="lp-card lp-cite">
            <div className="lp-mono-label" style={{ marginBottom: 10 }}>Cite</div>
            <pre>{"@misc{paperproof,\n  title  = {Paperproof},\n  author = {Evgenia Karunus, Anton Kovsharov},\n  doi    = {10.5281/zenodo.10023223},\n}"}</pre>
            <div className="lp-cite-links">
              <a href="https://zenodo.org/records/19463976" target="_blank" rel="noopener noreferrer">Zenodo ↗</a>
              <a href="https://github.com/Paper-Proof/paperproof" target="_blank" rel="noopener noreferrer">GitHub ↗</a>
            </div>
          </div>
        </div>
        <div className="lp-copyright">Evgenia Karunus & Anton Kovsharov · paperproof.xyz · Lean 4 · MIT licensed</div>
      </footer>

    </div>
  );
}

export { LandingPage };
if (typeof document !== 'undefined') {
  const container = document.getElementById('root');
  if (container) createRoot(container).render(<LandingPage />);
}
