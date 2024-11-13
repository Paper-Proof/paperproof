import React from "react";
import { Arrow, Tactic } from "types";
import Hint from "./ProofTree/components/BoxEl/components/Hint";
import PerfectArrow from "./PerfectArrow";
import { useGlobalContext } from "src/indexBrowser";
import createArrow from "src/services/createArrow";
import prettifyTacticText from "src/services/prettifyTacticText";

interface TacticNodeProps {
  tactic?: Tactic;
  className?: string;
  shardId?: string;
  isActiveGoal?: boolean
}
const TacticNode = (props: TacticNodeProps) => {
  if ((!props.tactic || props.tactic.text === "sorry") && props.isActiveGoal) {
    return <div className="active-tactic">
      <img src="https://private-user-images.githubusercontent.com/7578559/264729795-58f24cf2-4336-4376-8738-6463e3802ba0.png?jwt=eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJnaXRodWIuY29tIiwiYXVkIjoicmF3LmdpdGh1YnVzZXJjb250ZW50LmNvbSIsImtleSI6ImtleTUiLCJleHAiOjE3MzE0NzEwMTksIm5iZiI6MTczMTQ3MDcxOSwicGF0aCI6Ii83NTc4NTU5LzI2NDcyOTc5NS01OGYyNGNmMi00MzM2LTQzNzYtODczOC02NDYzZTM4MDJiYTAucG5nP1gtQW16LUFsZ29yaXRobT1BV1M0LUhNQUMtU0hBMjU2JlgtQW16LUNyZWRlbnRpYWw9QUtJQVZDT0RZTFNBNTNQUUs0WkElMkYyMDI0MTExMyUyRnVzLWVhc3QtMSUyRnMzJTJGYXdzNF9yZXF1ZXN0JlgtQW16LURhdGU9MjAyNDExMTNUMDQwNTE5WiZYLUFtei1FeHBpcmVzPTMwMCZYLUFtei1TaWduYXR1cmU9ZWRkYTkxZWQ0N2QzZjhiZmI4NzFjNzZlYTc4NmQ5YTU1ODc5NzNmZTcyYmY1ZjNjODYyYjc1MDJlNzEyYjU1OSZYLUFtei1TaWduZWRIZWFkZXJzPWhvc3QifQ.hPFir-MxOhsP9OxlaQ_uOmHBTZVJozmqo7rCvGv0ZFw"/>
      <div className="tactic -ellipsis">...</div>
    </div>
  }
  if (!props.tactic){
    return
  }

  const [perfectArrows, setPerfectArrows] = React.useState<Arrow[]>([]);
  const thisEl = React.useRef<HTMLInputElement>(null);

  const global = useGlobalContext();

  React.useLayoutEffect(() => {
    if (!props.tactic) return
    const newPerfectArrows : Arrow[] = props.tactic.dependsOnIds
      .map((dependsOnHypId) => createArrow(`hypothesis-${dependsOnHypId}`, thisEl.current))
      .filter((arrow) : arrow is Arrow => arrow !== null);
    setPerfectArrows(newPerfectArrows);
  }, [props.tactic, global.UIVersion]);

  const isSorried = props.tactic.text === "sorry" || props.tactic.text === "done";
  const isSuccess = props.tactic.successGoalId && !isSorried

  const text = prettifyTacticText(props.tactic.text)
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
      {isSuccess ? <><span>🎉</span> <span>{text}</span> <span>🎉</span></> : text}
      {perfectArrows.map((arrow, index) =>
        <PerfectArrow key={index} p1={arrow.from} p2={arrow.to}/>
      )}
    </div>
  );
};

export default TacticNode;
