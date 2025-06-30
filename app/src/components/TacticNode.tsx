import React from "react";
import { Arrow, Position, PositionStartStop, Tactic, AnyTheoremSignature, HypNode } from "types";
import Hint from "./ProofTree/components/BoxEl/components/Hint";
import PerfectArrow from "./PerfectArrow";
import { useGlobalContext } from "src/indexBrowser";
import createArrow from "src/services/createArrow";
import prettifyTacticText from "src/services/prettifyTacticText";
import DependsOnUI from "src/services/DependsOnUI";
import FancySubstring, { SubstringMatch } from "src/services/FancySubstring";
import isCursorWithinTactic from "src/services/isCursorWithinTactic";

interface TacticNodeProps {
  tactic?: Tactic;
  className?: string;
  shardId?: string;
  isActiveGoal?: boolean;
  onClick?: (e: React.MouseEvent) => void;
  circleEl?: React.ReactNode;
}
const TacticNode = (props: TacticNodeProps) => {
  const isEllipsisTactic = (!props.tactic || props.tactic.text.includes("sorry")) && props.isActiveGoal;
  if (isEllipsisTactic) {
    return <div className="active-tactic">
      <div className="tactic -ellipsis">...</div>
    </div>
  }
  if (!props.tactic){
    return;
  }
  
  const [perfectArrows, setPerfectArrows] = React.useState<Arrow[]>([]);
  const thisEl = React.useRef<HTMLInputElement>(null);

  const global = useGlobalContext();

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

  const getTheoremShortName = (theorem: AnyTheoremSignature): string => {
    return theorem.name
      // Skip all modules
      .split('.').at(-1)!
      // Strip "@"
      .split('@').at(-1)!
  };

  // noncomputable def fn_of_sum_ne_inlww {α β₁ β₂ : Type} {f : α → β₁ ⊕ β₂} (hf : ∀ www : α, ∀ b₁ : β₁, f www ≠ ◩b₁) : α → β₂ :=
  // fun nnn => (fn_sum_ne_inl hf nnn).choose
  // BEFORE
  // (a._@.Seymour.Matroid.Operations.Sum3.MatrixLikeSum3._hyg.8589: α )
  // AFTER
  // (anonymous: α )
  const cleanHypName = (name: string) => {
    if (name.includes('_hyg')) {
      return '_';
    } else {
      return name;
    }
  }

  const renderArg = (pLeft: String, pRight: String, name: string | null, type: string) => {
    return <div className="arg" key={name}>
      <span className="parenthesis -left">{pLeft}</span>
      <span className="arg-name">{name ? cleanHypName(name) + ' : ' : ''}</span>
      <span className="arg-type">{type}</span>
      <span className="parenthesis -right">{pRight}</span>
    </div>
  }

  const tacticText = FancySubstring.renderTextWithMatches(
    text,
    props.tactic.theorems,
    getTheoremShortName,
    (match: SubstringMatch<AnyTheoremSignature>, index: number, text: string) => {
      return <span
        key={`theorem-${index}`}
        className="theorem-highlight"
        onClick={(e) => {
          e.stopPropagation();
          e.preventDefault();
          setTheorem(theorem === match.item ? null : match.item);
        }}
      >
        {text.substring(match.start, match.end)}
      </span>
    }
  );

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

      {
        theorem &&
        <section className="theorem-wrapper">
          <div className="theorem">
            <div className="name">{theorem.declarationType} {theorem.name}</div>
            <div className="args">
              <div className="instance-args">
                {theorem.instanceArgs.map((arg) => renderArg("[", "]", null, arg.type))}
              </div>
              <div className="implicit-args">
                {theorem.implicitArgs.map((arg) => renderArg("{", "}", arg.name, arg.type))}
              </div>
              <div className="explicit-args">
                {theorem.explicitArgs.map((arg) => renderArg("(", ")", arg.name, arg.type))}
              </div>
            </div>
            <div className="type">
              : {theorem.type}
            </div>
            {theorem.declarationType === "def" && theorem.body && (
              <div className="body">
                := {theorem.body}
              </div>
            )}
          </div>
        </section>
      }
      {!props.circleEl && perfectArrows.map((arrow, index) =>
        <PerfectArrow key={index} p1={arrow.from} p2={arrow.to}/>
      )}
      {props.circleEl}
    </div>
  );
};

export default TacticNode;
