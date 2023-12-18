import React, { useId } from "react";
import { Tactic } from "types";
import Hint from "./ProofTree/components/BoxEl/components/Hint";

interface TacticNodeProps {
  tactic: Tactic;
  className?: string;
  shardId?: string
}
const TacticNode = (props: TacticNodeProps) => {
  const thisEl = React.useRef(null);
  const handleMouseEnter = () => {
    const releventLeaderLines = window.leaderLines
      .filter((line) => line.end === thisEl.current)
      .forEach((line) => line.show())
  }
  const handleMouseLeave = () => {
    const releventLeaderLines = window.leaderLines
      .filter((line) => line.end === thisEl.current)
      .forEach((line) => line.hide())
  }

  return (
    <div 
      className={`tactic -hint ${props.className || ''}`} 
      id={props.shardId ?
        `tactic-${props.tactic.id}-${props.shardId}` :
        `tactic-${props.tactic.id}`
      }
      onMouseEnter={handleMouseEnter}
      onMouseLeave={handleMouseLeave}
      ref={thisEl}
    >
      <Hint>{props.tactic}</Hint>
      {props.tactic.text}
    </div>
  );
};

export default TacticNode;
