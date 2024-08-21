import React from "react";
import { TabledTactic } from "types";
import BoxEl from "src/components/ProofTree/components/BoxEl";
import TacticNode from "src/components/TacticNode";
import { useGlobalContext } from "src/indexBrowser";

interface TacticNodeForHypothesis {
  cell: TabledTactic;
  colSpan: number;
  shouldTacticHaveSelfRespect: boolean
}
const TacticNodeForHypothesis = (props: TacticNodeForHypothesis) => {
  const tactic = props.cell.tactic;
  const { proofTree } = useGlobalContext();

  if (tactic.text === "init") return null

  return (
    <>
      {
        tactic.haveBoxIds.length > 0 &&
        <div className="child-boxes">
          {tactic.haveBoxIds.map((haveBoxId) => (
            <BoxEl
              key={haveBoxId}
              box={proofTree.boxes.find((box) => box.id === haveBoxId)!}
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
