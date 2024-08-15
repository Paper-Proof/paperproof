import React from "react";
import { Header } from "types/ConvertedProofTree";
import HypothesisNode from "./Hypotheses/components/HypothesisNode";

export interface HeaderProps {
  header: Header | undefined;
}

const HeaderEl = (props: HeaderProps) => {
  if (!props.header || (props.header.row1.length === 0 && !props.header.isRow2)) {
    return null
  }

  return <header className={`${props.header.isRow2 ? '-with-normal-hyps' : ''}`}>
    <div className="title">hypotheses</div>
    {
      props.header.row1 &&
      <div className="row-1">
        {props.header.row1.map((hypNode, index) =>
          <HypothesisNode key={index} hypNode={hypNode}/>
        )}
      </div>
    }
    {/* We pull up hyp nodes from below to fit into this { position: absolute; } div */}
    <div className="row-2"/>
  </header>
};

export default HeaderEl
