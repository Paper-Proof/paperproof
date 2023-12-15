import React from "react";
import Hint from "../../Hint";
import { Highlights, HypNode, TabledHyp } from "types";

export interface HypothesisProps {
  hypNode: HypNode;
  highlights: Highlights;
}

const HypothesisNode = (props: HypothesisProps) => {
  // Example input: hypNode.name = "h._@.Examples._hyg.1162"
  // Example output: name = "h✝"
  const name = props.hypNode.name &&
    props.hypNode.name.includes(".")
    ? `${props.hypNode.name.split(".")[0]}✝`
    : props.hypNode.name;

  return <div
    id={`hypothesis-${props.hypNode.id}`}
    className={`hypothesis -hint ${!props.highlights || props.highlights.hypIds.includes(props.hypNode.id) ? "" : "-faded"} ${props.hypNode.isProof}`}
  >
    <Hint>{props.hypNode}</Hint>
    {name && <span className="name">{props.hypNode.name}</span>}
    {name && ": "}
    <span className="text">{props.hypNode.text}</span>
  </div>;
};

export default HypothesisNode
