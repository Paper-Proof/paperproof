import React from "react";

import { ConvertedProofTree, Box, HypNode } from "types";
import HypothesisRow from "./HypothesisRow";
import Hint from "./Hint";

interface MyProps {
  box: Box;
  proofTree: ConvertedProofTree;
  depth: number;
}

const getGoalTactic = (proofTree: ConvertedProofTree, goalNodeId: string) => {
  const goalTactic = proofTree.tactics.find((tactic) => tactic.goalArrows.find((goalArrow) => goalArrow.fromId === goalNodeId));

  const successTactic = proofTree.tactics.find((tactic) => tactic.successGoalId === goalNodeId);

  return goalTactic || successTactic;
}

const BoxEl = (props: MyProps) => {
  const childrenBoxes = props.proofTree.boxes.filter((box) => box.parentId === props.box.id);

  return <section className={`box depth-${props.depth}`}>
    {props.box.hypNodes.map((hypNodeRow) =>
      <HypothesisRow proofTree={props.proofTree} depth={props.depth} hypNodeRow={hypNodeRow}/>
    )}
    <div style={{ padding: "10px 0px", color: "#356e9d" }}>Box {props.box.id}</div>
    <div className="child-boxes">
      {childrenBoxes.map((childBox) =>
        <BoxEl key={childBox.id} depth={props.depth + 1} box={childBox} proofTree={props.proofTree}/>
      )}
    </div>

    {props.box.goalNodes.slice().reverse().map((goalNode) =>
      <div key={goalNode.id}>
        {
          getGoalTactic(props.proofTree, goalNode.id) &&
          <div className="tactic -hint">
            <Hint>{getGoalTactic(props.proofTree, goalNode.id)}</Hint>
            {getGoalTactic(props.proofTree, goalNode.id)?.text}
          </div>
        }
        <div className="goal -hint">
          <Hint>{goalNode}</Hint>
          {goalNode.text}
        </div>
      </div>
    )}
  </section>
}

export default BoxEl;
