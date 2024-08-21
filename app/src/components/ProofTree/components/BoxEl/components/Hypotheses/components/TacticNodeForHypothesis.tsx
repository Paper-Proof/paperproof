import React from "react";
import { ConvertedProofTree, TabledTactic } from "types";
import BoxEl from "../../..";
import TacticNode from "src/components/TacticNode";

interface TacticNodeForHypothesis {
  cell: TabledTactic;
  colSpan: number;
  proofTree: ConvertedProofTree;
  shouldTacticHaveSelfRespect: boolean
}
const TacticNodeForHypothesis = (props: TacticNodeForHypothesis) => {
  const tactic = props.cell.tactic;

  if (tactic.text === "init") return null

  return (
    <>
      {
        tactic.haveBoxIds.length > 0 &&
        <div className="child-boxes">
          {tactic.haveBoxIds.map((haveBoxId) => (
            <BoxEl
              key={haveBoxId}
              box={props.proofTree.boxes.find((box) => box.id === haveBoxId)!}
              proofTree={props.proofTree}
              highlights={null}
            />
          ))}
        </div>
      }
      <TacticNode
        className={`
          -hypothesis-tactic
          ${props.shouldTacticHaveSelfRespect ? '-with-self-respect' : ''}
        `}
        tactic={props.cell.tactic}
        shardId={props.cell.shardId}
      />
    </>
  );
};

export default TacticNodeForHypothesis;
