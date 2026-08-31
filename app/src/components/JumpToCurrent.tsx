import React, { useState } from "react";
import { Position } from "types";
import flashElement from "src/services/flashElement";

// The cursor's tactic is rendered everywhere it acts - once in the hypothesis table
// next to the hypothesis it produced, once down in the goals - so one can be off-screen
// above while the other is off-screen below.
const CURRENT_SELECTOR = '.tactic.-position-matches, .goal.-highlighted';

const offScreenTargets = (direction: "up" | "down") =>
  Array.from(document.querySelectorAll(CURRENT_SELECTOR))
    .map((el) => ({ el, rect: el.getBoundingClientRect() }))
    .filter(({ rect }) => direction === "up" ? rect.bottom <= 0 : rect.top >= window.innerHeight);

const isInView = (rect: DOMRect) =>
  rect.bottom > 0 && rect.top < window.innerHeight &&
  rect.right > 0 && rect.left < window.innerWidth;

const scrollToTarget = (el: Element) => {
  el.scrollIntoView({ behavior: 'smooth', block: 'center', inline: 'start' });
};

interface Props {
  // We never scroll the user around on their behalf, so we recheck what's visible
  // whenever anything could have moved
  converted: unknown;
  position: Position;
  UIVersion: number;
  isFollowingCursor: boolean;
}

const JumpToCurrent = (props: Props) => {
  const [arrows, setArrows] = useState<{ up: boolean, down: boolean }>({ up: false, down: false });

  React.useEffect(() => {
    let frame: number | null = null;
    const recompute = () => {
      frame = null;
      const up = offScreenTargets("up").length > 0;
      const down = offScreenTargets("down").length > 0;
      // Bail out when nothing changed, otherwise we'd rerender on every scroll frame
      setArrows((old) => old.up === up && old.down === down ? old : { up, down });
    };
    const schedule = () => { if (frame === null) frame = requestAnimationFrame(recompute); };
    recompute();
    addEventListener('scroll', schedule, { passive: true });
    addEventListener('resize', schedule);
    return () => {
      if (frame !== null) cancelAnimationFrame(frame);
      removeEventListener('scroll', schedule);
      removeEventListener('resize', schedule);
    };
  }, [props.converted, props.position, props.UIVersion]);

  // Moving the cursor onto a different tactic only recolors it, which is easy to miss
  const boldedTactics = React.useRef<string | null>(null);
  React.useEffect(() => {
    const els = Array.from(document.querySelectorAll('.tactic.-position-matches'));
    // [Claude comment] keyed on the cursor rather than on which tactics matched, so that
    // moving around inside one tactic flashes it again instead of staying silent.
    const key = [props.position.line, props.position.character, ...els.map((el) => el.id).sort()].join('|');
    if (key === boldedTactics.current) return;
    boldedTactics.current = key;
    els.forEach(flashElement);
  }, [props.converted, props.position, props.UIVersion]);

  // "Follow the current tactic": do the jump for the user when what they clicked on is
  // off-screen. Only when nothing current is in view, so a visible tactic never moves.
  const followedCursor = React.useRef<string | null>(null);
  React.useEffect(() => {
    if (!props.isFollowingCursor) { followedCursor.current = null; return; }

    const targets = Array.from(document.querySelectorAll(CURRENT_SELECTOR))
      .map((el) => ({ el, rect: el.getBoundingClientRect() }));
    if (targets.length === 0) return;

    const key = [props.position.line, props.position.character, ...targets.map(({ el }) => el.id).sort()].join('|');
    if (key === followedCursor.current) return;
    followedCursor.current = key;

    if (targets.some(({ rect }) => isInView(rect))) return;
    // Nearest to the viewport, so we travel the shorter distance
    const nearest = targets.reduce((a, b) => Math.abs(a.rect.top) < Math.abs(b.rect.top) ? a : b);
    scrollToTarget(nearest.el);
  }, [props.converted, props.position, props.UIVersion, props.isFollowingCursor]);

  const jumpTo = (direction: "up" | "down") => {
    const targets = offScreenTargets(direction);
    if (targets.length === 0) return;
    // Jump to the nearest one - repeated clicks then walk you through the rest
    const nearest = targets.reduce((a, b) =>
      direction === "up" ?
      (a.rect.bottom > b.rect.bottom ? a : b) :
      (a.rect.top < b.rect.top ? a : b)
    );
    scrollToTarget(nearest.el);
    flashElement(nearest.el);
  };

  if (!arrows.up && !arrows.down) return null;

  return (
    <div className="jump-to-current">
      {
        arrows.up &&
        <button type="button" title="Jump to the current tactic/goal above" onClick={() => jumpTo("up")}>
          <svg viewBox="0 0 24 24" aria-hidden="true"><path d="M12 19V6M6 12l6-6 6 6"/></svg>
        </button>
      }
      {
        arrows.down &&
        <button type="button" title="Jump to the current tactic/goal below" onClick={() => jumpTo("down")}>
          <svg viewBox="0 0 24 24" aria-hidden="true"><path d="M12 5v13M6 12l6 6 6-6"/></svg>
        </button>
      }
    </div>
  );
};

export default JumpToCurrent;
