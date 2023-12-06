import React from "react";

import { ConvertedProofTree, Box, HypNode, Highlights, Tactic } from "types";
import Hypotheses from "./components/Hypotheses";
import Hint from "./components/Hint";

import zoomAndScroll from '../../services/zoomAndScroll';
import PerfectArrow from "../PerfectArrow";

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

interface TacticNodeProps {
  tactic: Tactic
}
const TacticNode = (props: TacticNodeProps) => {
  const tacticRef = React.useRef<HTMLDivElement | null>(null);
  // const arrows = props.tactic.dependsOnIds.map((hypId) => {
  //   const hypEl = document.getElementById(`hypothesis-${hypId}`);
  //   if (!tacticRef.current || !hypEl) return null;

  //   const hypRect = hypEl.getBoundingClientRect();
  //   const p1 = {x: hypRect.left + hypRect.width / 2, y: hypRect.bottom};

  //   const tacticRect = tacticRef.current.getBoundingClientRect();
  //   const p2 = {x: tacticRect.left + tacticRect.width / 2, y: tacticRect.top};

  //   // const p1 = { x: 0, y: 0 };
  //   // const p2 = { x: 200, y: 200 }

  //   return <PerfectArrow key={hypId} p1={p1} p2={p2}/>
  // });
  return(
    <>
      {/* {arrows} */}
      <div className="tactic -hint" ref={tacticRef}>
        <Hint>{props.tactic}</Hint>
        {props.tactic.text}
      </div>
    </>
  );
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

  return <section className="box" id={`box-${props.box.id}`} onClick={zoomAndScroll}>
    <div className="box-insides">
      <Hypotheses proofTree={props.proofTree} hypLayers={hypLayers} highlights={props.highlights}/>

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
      {props.box.goalNodes[0].name}
    </div>
  </section>
}

export default BoxEl;
