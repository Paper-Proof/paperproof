import React from "react";

import { ConvertedProofTree, Box, HypNode } from "types";
import Hypotheses from "./Hypotheses";
import Hint from "./Hint";

import scrollIntoView from 'smooth-scroll-into-view-if-needed'
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
  
  const zoomOnBox = (event: React.MouseEvent<HTMLElement>) => {
    console.log(`clicked on box ${props.box.id}`);
    event.stopPropagation();
    const box = event.currentTarget.closest('.box') as HTMLElement;
    if (!box) return
    // 1. apply `transform: scale(scaleFactor)` so that `box` can fit into viewport
    const scaleFactor = Math.min(
      window.innerWidth / box.offsetWidth,
      window.innerHeight / box.offsetHeight
    );
    const rootEl = document.getElementById("root")!;
    rootEl.style.transform = `scale(${scaleFactor})`;

    // 2. scroll it into view
    // Predict where the `box` will be after the scale
    const boxRect = box.getBoundingClientRect();
    console.log(boxRect);
    const predictedBoxTop = box.offsetTop * scaleFactor;
    const predictedBoxLeft = box.offsetLeft * scaleFactor;

    // Apply the `scrollTop` and `.scrollLeft`
    // window.scroll({ top: predictedBoxTop, left: predictedBoxLeft })
    // window.scrollTo({ top: 50, left: 20 })
    // const bodyEl = document.getElementsByTagName("body")[0]
    // bodyEl.scroll(100, 50)

    scrollIntoView(box, {
      scrollMode: "always",
      block: "center",
      inline: "center"
    });

    // Make both the `scale() css transform` and
  }

  return <section className="box" id={`box-${props.box.id}`} onClick={zoomOnBox}>
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
}

export default BoxEl;
