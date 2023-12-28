import React, { useContext, useState } from "react";
import { Arrow, Point, Tactic } from "types";
import Hint from "./ProofTree/components/BoxEl/components/Hint";
import PerfectArrow from "./PerfectArrow";
import distance from "src/services/distance";
import { GlobalContext } from "src/indexBrowser";

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
    const newPerfectArrows : Arrow[] = [];

    props.tactic.dependsOnIds.forEach((dependsOnHypId) => {
      const fromId =`hypothesis-${dependsOnHypId}`;
      const fromEl = document.getElementById(fromId)!;
      const toEl = thisEl.current;
      if (!fromEl || !toEl) return;

      const proofTreeEl = document.getElementsByClassName("proof-tree")[0] as HTMLElement;
      const currentZoom = parseFloat(getComputedStyle(proofTreeEl).transform.split(',')[3]) || 1;

      const pointFrom : Point = {
        x: distance('left', fromEl, proofTreeEl)/currentZoom + fromEl.offsetWidth/2,
        y: distance('top', fromEl, proofTreeEl)/currentZoom + fromEl.offsetHeight
      };

      const pointTo : Point = {
        x: distance('left', toEl, proofTreeEl)/currentZoom + toEl.offsetWidth/2,
        y: distance('top', toEl, proofTreeEl)/currentZoom
      };

      newPerfectArrows.push({ from: pointFrom, to: pointTo })
    });

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
