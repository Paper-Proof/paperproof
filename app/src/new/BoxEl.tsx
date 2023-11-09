import React from "react";

import { ConvertedProofTree, Box } from "types";

interface MyProps {
  box: Box;
  proofTree: ConvertedProofTree;
}

export const BoxEl = (props: MyProps) => {
  const childrenBoxes = props.proofTree.boxes.filter((box) => box.parentId === props.box.id);

  return <section className={`box depth-${props.box.id}`}>
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
        <BoxEl key={childBox.id} box={childBox} proofTree={props.proofTree}/>
      )}
    </div>

    {props.box.goalNodes.map((goalNode) =>
      <div key={goalNode.id} className="goal">{goalNode.text}</div>
    )}
  </section>
}
