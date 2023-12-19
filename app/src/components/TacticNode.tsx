import React, { useId, useState } from "react";
import { Arrow, Point, Tactic } from "types";
import Hint from "./ProofTree/components/BoxEl/components/Hint";
import PerfectArrow from "./PerfectArrow";

const distanceTop = (el1: HTMLElement, el2: HTMLElement) => {
  const rect1 = el1.getBoundingClientRect();
  const rect2 = el2.getBoundingClientRect();
  return Math.abs(rect1.top - rect2.top);
}

const distanceLeft = (el1: HTMLElement, el2: HTMLElement) => {
  const rect1 = el1.getBoundingClientRect();
  const rect2 = el2.getBoundingClientRect();
  return Math.abs(rect1.left - rect2.left);
}

interface TacticNodeProps {
  tactic: Tactic;
  className?: string;
  shardId?: string
}
const TacticNode = (props: TacticNodeProps) => {
  const [perfectArrows, setPerfectArrows] = useState<Arrow[]>([]);

  const thisEl = React.useRef<HTMLInputElement>(null);
  const handleMouseEnter = () => {
  }
  const handleMouseLeave = () => {
  }

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
        x: distanceLeft(fromEl, proofTreeEl)/currentZoom + fromEl.offsetWidth/2,
        y: distanceTop(fromEl, proofTreeEl)/currentZoom + fromEl.offsetHeight
      };

      const pointTo : Point = {
        x: distanceLeft(toEl, proofTreeEl)/currentZoom + toEl.offsetWidth/2,
        y: distanceTop(toEl, proofTreeEl)/currentZoom
      };
      
      newPerfectArrows.push({ from: pointFrom, to: pointTo })
    });

    setPerfectArrows(newPerfectArrows);
  }, [props.tactic]);

  return (
    <div 
      className={`tactic -hint ${props.className || ''}`} 
      id={props.shardId ?
        `tactic-${props.tactic.id}-${props.shardId}` :
        `tactic-${props.tactic.id}`
      }
      // onMouseEnter={handleMouseEnter}
      // onMouseLeave={handleMouseLeave}
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
