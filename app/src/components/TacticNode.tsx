import React from "react";
import { Arrow, Tactic, AnyTheoremSignature } from "types";
import Hint from "./ProofTree/components/BoxEl/components/Hint";
import PerfectArrow from "./PerfectArrow";
import { useGlobalContext } from "src/indexBrowser";
import createArrow from "src/services/createArrow";
import prettifyTacticText from "src/services/prettifyTacticText";
import DependsOnUI from "src/services/DependsOnUI";
import FancySubstring, { SubstringMatch } from "src/services/FancySubstring";
import isCursorWithinTactic from "src/services/isCursorWithinTactic";
import Theorem from "./Theorem";
import getHypById from "src/services/getHypById";

const getTheoremShortName = (theorem: AnyTheoremSignature): string => {
  return theorem.name
    // Skip all modules
    .split('.').at(-1)!
    // Strip "@"
    .split('@').at(-1)!
};

interface TacticNodeProps {
  tactic?: Tactic;
  className?: string;
  shardId?: string;
  isActiveGoal?: boolean;
  onClick?: (e: React.MouseEvent) => void;
  circleEl?: React.ReactNode;
}
const TacticNode = (props: TacticNodeProps) => {
  const global = useGlobalContext();

  const isSorriedAndWriting = (!props.tactic || props.tactic.text.includes("sorry")) && props.isActiveGoal;
  const isFake = global.settings.isSingleTacticMode && global.proofTree.tactics.find((t) => t.text === "fake");
  // console.log(props.tactic)
  if (isSorriedAndWriting || isFake) {
    return <div className="active-tactic">
      <div className="tactic -ellipsis">...</div>
    </div>
  }
  if (!props.tactic){
    return;
  }
  
  const [perfectArrows, setPerfectArrows] = React.useState<Arrow[]>([]);
  const thisEl = React.useRef<HTMLInputElement>(null);

  React.useLayoutEffect(() => {
    if (!props.tactic) return;
    const newPerfectArrows : Arrow[] = props.tactic.dependsOnIds
      .filter((hypId) => DependsOnUI.shouldDrawArrowToHypothesis(global, hypId))
      .map((hypId) => createArrow(`hypothesis-${hypId}`, thisEl.current))
      .filter((arrow) : arrow is Arrow => arrow !== null);
    setPerfectArrows(newPerfectArrows);
  }, [props.tactic, global.UIVersion]);

  const isSorried = props.tactic.text.includes("sorry") || props.tactic.text === "done";
  const isSuccess = props.tactic.successGoalId && !isSorried;
  const isPositionMatch = global.settings.isSingleTacticMode ? false : isCursorWithinTactic(global.position, props.tactic.position);

  const text = prettifyTacticText(props.tactic.text);

  const [theorem, setTheorem] = React.useState<AnyTheoremSignature | null>(null);

  const tacticText = FancySubstring.renderTextWithMatches(text, [
    {
      items: props.tactic.theorems,
      getItemString: getTheoremShortName,
      renderMatch: (match, index, text) => (
        <span
          key={`theorem-${index}`}
          className="fancy-substring-theorem"
          onClick={(e) => {
            e.stopPropagation();
            e.preventDefault();
            setTheorem(theorem === match.item ? null : match.item);
          }}
        >
          {text.substring(match.start, match.end)}
        </span>
      )
    },
    {
      items: props.tactic.dependsOnIds
        .map((id) => getHypById(global.proofTree, id)?.name)
        .filter((hypName) => hypName),
      getItemString: (hypName) => hypName,
      renderMatch: (match, index, text) => (
        <span key={`hypothesis-${index}`} className="fancy-substring-hypothesis">
          {text.substring(match.start, match.end)}
        </span>
      )
    }
  ]);

  return (
    <div 
      className={`
        tactic -hint
        ${props.className || ''}
        ${isSuccess ? '-success' : ''}
        ${theorem ? '-with-theorem' : ''}
        ${isSorried ? '-sorried' : ''}
        ${isPositionMatch ? '-position-matches' : ''}
      `} 
      id={props.shardId ?
        `tactic-${props.tactic.id}-${props.shardId}` :
        `tactic-${props.tactic.id}`
      }
      onClick={props.onClick}
      ref={thisEl}
    >
      <Hint>{props.tactic}</Hint>
      {
        isSuccess ?
        <div className="text">
          <span>🎉</span> <span>{tacticText}</span> <span>🎉</span>
        </div> :
        <div className="text">
          {tacticText}
        </div>
      }

      {theorem && <Theorem theorem={theorem}/>}

      {!props.circleEl && perfectArrows.map((arrow, index) =>
        <PerfectArrow key={index} p1={arrow.from} p2={arrow.to}/>
      )}
      {props.circleEl}
    </div>
  );
};

export default TacticNode;
