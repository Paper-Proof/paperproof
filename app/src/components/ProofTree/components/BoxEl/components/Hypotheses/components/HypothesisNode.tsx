import React from "react";
import Hint from "../../Hint";
import { Highlights, TabledHyp } from "types";

export interface HypothesisProps {
  cell: TabledHyp;
  highlights: Highlights;
}

const HypothesisNode = (props: HypothesisProps) => {
  const hypNode = props.cell.hypNode;

  // Example input: hypNode.name = "h._@.Examples._hyg.1162"
  // Example output: name = "h✝"
  const name = hypNode.name &&
    hypNode.name.includes(".")
    ? `${hypNode.name.split(".")[0]}✝`
    : hypNode.name;

  return <div
    id={`hypothesis-${hypNode.id}`}
    className={`hypothesis -hint ${!props.highlights || props.highlights.hypIds.includes(hypNode.id) ? "" : "-faded"} ${hypNode.isProof ? '-is-proof' : '-is-not-proof'}`}
  >
    <Hint>{props.cell}</Hint>
    {name && <span className="name">{hypNode.name}</span>}
    {name && ": "}
    <span className="text">{hypNode.text}</span>
  </div>;
};

export default HypothesisNode
