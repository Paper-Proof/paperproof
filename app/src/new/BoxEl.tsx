import React from "react";

import { ConvertedProofTree, Box, HypNode } from "types";
import Hypotheses from "./Hypotheses";
import Hint from "./Hint";

import { TransformWrapper, TransformComponent } from "react-zoom-pan-pinch";

interface MyProps {
  box: Box;
  proofTree: ConvertedProofTree;
  zoomToElement: (elementId: string) => void;
}

const getGoalTactic = (proofTree: ConvertedProofTree, goalNodeId: string) => {
  const goalTactic = proofTree.tactics.find((tactic) => tactic.goalArrows.find((goalArrow) => goalArrow.fromId === goalNodeId));

  const successTactic = proofTree.tactics.find((tactic) => tactic.successGoalId === goalNodeId);

  return goalTactic || successTactic;
}

const BoxEl = (props: MyProps) => {
  const childrenBoxes = props.proofTree.boxes.filter((box) => box.parentId === props.box.id);

  // TODO this should be based on .isProof instead!
  const hypLayers = props.box.hypNodes
    .map((hypNodeLayer, index) => {
      if (index === 0) {
        return hypNodeLayer.filter((hypNode) => hypNode.text !== "ℕ" && hypNode.text !== "Prop");
      } else {
        return hypNodeLayer;
      }
    })
    .filter((hypLayer) => hypLayer.length > 0);

  return <TransformComponent>
    <section
      className="box"
      onClick={(event) => {
        event.stopPropagation();
        console.log(`clicked on box ${props.box.id}`);
        props.zoomToElement(`box-${props.box.id}`)
      }}
      id={`box-${props.box.id}`}
    >
      <div className="box-insides">
        <Hypotheses proofTree={props.proofTree} hypLayers={hypLayers}/>

        <div style={{ padding: "10px 0px", color: "#356e9d" }}>Box {props.box.id}</div>
        <div className="child-boxes">
          {childrenBoxes.map((childBox) =>
            <BoxEl zoomToElement={props.zoomToElement} key={childBox.id} box={childBox} proofTree={props.proofTree}/>
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
      </div>

      <div className="goal-username">
        {props.box.goalNodes[0].name}
      </div>
    </section>
  </TransformComponent>
}

export default BoxEl;
