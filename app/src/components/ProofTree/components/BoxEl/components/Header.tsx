import React from "react";
import { Highlights } from "types";
import { Header } from "types/ConvertedProofTree";
import HypothesisNode from "./Hypotheses/components/HypothesisNode";

export interface HeaderProps {
  header: Header | undefined;
  highlights: Highlights;
}

const HeaderEl = (props: HeaderProps) => {
  if (!props.header || (props.header.row1.length === 0 && props.header.row2Status === 'absent')) {
    return null
  }

  return <header className={`-row2Status-${props.header.row2Status}`}>
    <div className="title">hypotheses</div>
    {
      props.header.row1.length > 0 &&
      <div className="row-1">
        {props.header.row1.map((hypNode, index) =>
          <HypothesisNode key={index} hypNode={hypNode} highlights={props.highlights}/>
        )}
      </div>
    }
    {/* We pull up hyp nodes from below to fit into this { position: absolute; } div */}
    <div className="row-2"/>
  </header>
};

export default HeaderEl
