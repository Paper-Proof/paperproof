import React from "react";

import { ConvertedProofTree, Box, HypNode, Highlights } from "types";
import Hypotheses from "./components/Hypotheses";
import Hint from "./components/Hint";

import zoomAndScroll from '../../services/zoomAndScroll';
import TacticNode from "../../../TacticNode";

interface MyProps {
  box: Box;
  proofTree: ConvertedProofTree;
  highlights: Highlights
}

const getGoalTactic = (proofTree: ConvertedProofTree, goalNodeId: string) => {
  const goalTactic = proofTree.tactics.find((tactic) => tactic.goalArrows.find((goalArrow) => goalArrow.fromId === goalNodeId));

  const successTactic = proofTree.tactics.find((tactic) => tactic.successGoalId === goalNodeId);

  return goalTactic || successTactic;
}

// "a._@.Mathlib.Init.Algebra.Order._hyg.1764" => "a"
// (https://github.com/leanprover/lean4/blob/d37bbf4292c72798afdff8bf5488df09193fde58/src/Init/Prelude.lean#L4132)
// Note: I was doing this in the parser with `.eraseMacroScopes`, but we depend in hygienic goal usernames, might be dangerous - so I moved it here.
const prettifyGoalUsername = (username : string) => {
  return username.split('._@')[0];
}

const BoxEl = (props: MyProps) => {
  const childrenBoxes = props.proofTree.boxes.filter((box) => box.parentId === props.box.id);

  return <section className="box" id={`box-${props.box.id}`} onClick={zoomAndScroll}>
    <div className="box-insides">
      <Hypotheses proofTree={props.proofTree} hypLayers={props.box.hypLayers} highlights={props.highlights}/>

      <div style={{ padding: "10px 0px", color: "#356e9d" }}>Box {props.box.id}</div>
      <div className="child-boxes">
        {childrenBoxes.map((childBox) =>
          <BoxEl key={childBox.id} box={childBox} proofTree={props.proofTree} highlights={props.highlights}/>
        )}
      </div>

      {props.box.goalNodes.slice().reverse().map((goalNode) =>
        <div key={goalNode.id}>
          {
            getGoalTactic(props.proofTree, goalNode.id) &&
            <TacticNode tactic={getGoalTactic(props.proofTree, goalNode.id)}/>
          }
          <div className={`goal -hint ${!props.highlights || props.highlights.goalId === goalNode.id ? "" : "-faded"}`}>
            <Hint>{goalNode}</Hint>
            {goalNode.text}
          </div>
        </div>
      )}
    </div>

    <div className="goal-username">
      {prettifyGoalUsername(props.box.goalNodes[0].name)}
    </div>
  </section>
}

export default BoxEl;
