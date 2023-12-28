import React, { useContext, useState } from "react";
import { Arrow, Tactic } from "types";
import Hint from "./ProofTree/components/BoxEl/components/Hint";
import PerfectArrow from "./PerfectArrow";
import { GlobalContext } from "src/indexBrowser";
import createArrow from "src/services/createArrow";

interface TacticNodeProps {
  tactic: Tactic;
  className?: string;
  shardId?: string
}
const TacticNode = (props: TacticNodeProps) => {
  const [perfectArrows, setPerfectArrows] = useState<Arrow[]>([]);
  const thisEl = React.useRef<HTMLInputElement>(null);

  const global = useContext(GlobalContext);

  React.useLayoutEffect(() => {
    const newPerfectArrows : Arrow[] = props.tactic.dependsOnIds
      .map((dependsOnHypId) => createArrow(`hypothesis-${dependsOnHypId}`, thisEl.current))
      .filter((arrow) : arrow is Arrow => arrow !== null);
    setPerfectArrows(newPerfectArrows);
  }, [props.tactic, global.UIVersion]);

  const isSorried = props.tactic.text === "sorry" || props.tactic.text === "done";
  const isSuccess = props.tactic.successGoalId && !isSorried

  return (
    <div 
      className={`tactic -hint ${props.className || ''} ${isSuccess ? '-success' : ''} ${isSorried ? '-sorried' : ''}`} 
      id={props.shardId ?
        `tactic-${props.tactic.id}-${props.shardId}` :
        `tactic-${props.tactic.id}`
      }
      ref={thisEl}
    >
      <Hint>{props.tactic}</Hint>
      {props.tactic.text}
      {perfectArrows.map((arrow, index) =>
        <PerfectArrow key={index} p1={arrow.from} p2={arrow.to}/>
      )}
    </div>
  );
};

export default TacticNode;
