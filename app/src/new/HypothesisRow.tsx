import React from "react";

import { ConvertedProofTree, Box, HypNode } from "types";
import BoxEl from "./BoxEl";

interface Props {
  proofTree: ConvertedProofTree;
  depth: number;
  hypNodeRow: HypNode[];
}

const getHypothesisTacticBefore = (proofTree: ConvertedProofTree, hypNodeRow: HypNode[]) => {
  const hypNodeId = hypNodeRow[0]!.id;
  const tactic = proofTree.tactics.find((tactic) => tactic.hypArrows.find((hypArrow) => hypArrow.toIds.includes(hypNodeId)));
  return tactic;
}

export default (props: Props) => {
  const tactic = getHypothesisTacticBefore(props.proofTree, props.hypNodeRow);
  // const haveBoxes = props.proofTree.boxes.filter((box) => tactic.haveBoxIds.includes(box.id));
  return <div className="hypothesis-row">
    {
      tactic &&
      props.proofTree.boxes.filter((box) => tactic.haveBoxIds.includes(box.id))
      .map((haveBox) =>
        <BoxEl proofTree={props.proofTree} depth={props.depth + 1} box={haveBox}/>
      )
    }
    {
      tactic &&
      <div className={`tactic -hint ${(tactic.hypArrows[0].fromId === null && tactic.haveBoxIds.length === 0) ? "-with-margin-top" : ""}`}>
        <pre>{JSON.stringify(tactic, null, 2)}</pre>
        {tactic?.text}
      </div>
    }
    <div className="hypotheses">
      {props.hypNodeRow.map((hypNode) =>
        <div key={hypNode.id} className="hypothesis -hint">
          <pre>{JSON.stringify(hypNode, null, 2)}</pre>
          <span className="name">{hypNode.name}</span>: {hypNode.text}
        </div>
      )}
    </div>
  </div>
}
