import React from "react";

import { ConvertedProofTree, Box, HypNode } from "types";

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

const getHypothesisTacticBefore = (proofTree: ConvertedProofTree, hypNodeRow: HypNode[]) => {
  const hypNodeId = hypNodeRow[0]!.id;
  const tactic = proofTree.tactics.find((tactic) => tactic.hypArrows.find((hypArrow) => hypArrow.toIds.includes(hypNodeId)));
  return tactic;
}

const getHypothesisTacticAfter = (proofTree: ConvertedProofTree, hypNodeRow: HypNode[]) => {
  const hypNodeId = hypNodeRow[0]!.id;
  const tactic = proofTree.tactics.find((tactic) => tactic.hypArrows.find((hypArrow) => hypArrow.fromId === hypNodeId));
  return tactic;
}


export const BoxEl = (props: MyProps) => {
  const childrenBoxes = props.proofTree.boxes.filter((box) => box.parentId === props.box.id);

  return <section className={`box depth-${props.depth}`}>
    {props.box.hypNodes.map((hypNodeRow) =>
      <div className="hypothesis-row">
        {
          getHypothesisTacticBefore(props.proofTree, hypNodeRow) &&
          <div className="tactic">
            {getHypothesisTacticBefore(props.proofTree, hypNodeRow)?.text}
          </div>
        }
        <div className="hypotheses">
          {hypNodeRow.map((hypNode) =>
            <div key={hypNode.id} className="hypothesis">
              <span className="name">{hypNode.name}</span>: {hypNode.text}
            </div>
          )}
        </div>
        {
          // getHypothesisTacticAfter(props.proofTree, hypNodeRow) &&
          // <div className="tactic">
          //   {getHypothesisTacticAfter(props.proofTree, hypNodeRow)?.text}
          // </div>
        }
      </div>
    )}
    Box {props.box.id}
    <div className="child-boxes">
      {childrenBoxes.map((childBox) =>
        <BoxEl key={childBox.id} depth={props.depth + 1} box={childBox} proofTree={props.proofTree}/>
      )}
    </div>

    {props.box.goalNodes.slice().reverse().map((goalNode) =>
      <div key={goalNode.id}>
        {
          getGoalTactic(props.proofTree, goalNode.id) &&
          <div className="tactic">
            {getGoalTactic(props.proofTree, goalNode.id)?.text}
          </div>
        }
        <div className="goal">{goalNode.text}</div>
      </div>
    )}
  </section>
}
