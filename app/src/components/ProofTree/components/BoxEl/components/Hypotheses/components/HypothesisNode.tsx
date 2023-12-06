import React from "react";
import Hint from "../../Hint";
import { Highlights, TabledHyp } from "types";

export interface HypothesisProps {
  cell: TabledHyp;
  highlights: Highlights;
}

const HypothesisNode = (props: HypothesisProps) => {
  return <div
    id={`hypothesis-${props.cell.hypNode.id}`}
    className={`hypothesis -hint ${!props.highlights || props.highlights.hypIds.includes(props.cell.hypNode.id) ? "" : "-faded"}`}
  >
    <Hint>{props.cell}</Hint>
    <span className="name">{props.cell.hypNode.name}</span>: {props.cell.hypNode.text}
  </div>;
};

export default HypothesisNode
