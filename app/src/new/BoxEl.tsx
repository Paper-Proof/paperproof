import React from "react";

import { ConvertedProofTree, Box } from "types";

interface MyProps {
  box: Box;
  proofTree: ConvertedProofTree;
  depth: number;
}

const getTactic = (proofTree: ConvertedProofTree, goalNodeId: string) =>
  proofTree.tactics.find((tactic) => tactic.goalArrows.find((goalArrow) => goalArrow.fromId === goalNodeId))

export const BoxEl = (props: MyProps) => {
  const childrenBoxes = props.proofTree.boxes.filter((box) => box.parentId === props.box.id);

  return <section className={`box depth-${props.depth}`}>
    {props.box.hypNodes.map((hypNodeRow) =>
      <div className="hypothesis-row">
        {hypNodeRow.map((hypNode) =>
          <div key={hypNode.id} className="hypothesis">
            <span className="name">{hypNode.name}</span>: {hypNode.text}
          </div>
        )}
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
        <div>
          {
            getTactic(props.proofTree, goalNode.id) &&
            <div className="tactic">
              {getTactic(props.proofTree, goalNode.id)?.text}
            </div>
          }
        </div>
        <div className="goal">{goalNode.text}</div>
      </div>
    )}
  </section>
}
