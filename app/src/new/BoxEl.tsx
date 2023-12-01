import React from "react";

import { ConvertedProofTree, Box, HypNode } from "types";
import Hypotheses from "./Hypotheses";
import Hint from "./Hint";

// import scrollIntoView from 'smooth-scroll-into-view-if-needed'
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

  return <section className="box" id={`box-${props.box.id}`}>
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

      <div className="goal-username" onClick={(event) => {
        event.stopPropagation();
        console.log(`clicked on box ${props.box.id}`);
        const box = (event.target as HTMLElement).parentElement;
        console.log({box});
        if (!box) return
        // box.scrollIntoView({ behavior: "smooth", block: "center", inline: "center" })

        scrollIntoView(box, {
          scrollMode: 'always',
          block: 'center',
          inline: 'center',
        })

        // props.zoomToElement(`box-${props.box.id}`)
      }}>
        {props.box.goalNodes[0].name}
      </div>
    </section>
}

export default BoxEl;
