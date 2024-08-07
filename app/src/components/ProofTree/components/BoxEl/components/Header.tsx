import React from "react";
import { Highlights } from "types";
import { Header } from "types/ConvertedProofTree";
import HypothesisNode from "./Hypotheses/components/HypothesisNode";

export interface HeaderProps {
  header: Header | undefined;
  highlights: Highlights;
}

const HeaderEl = (props: HeaderProps) => {
  if (!props.header || (props.header.row1.length === 0 && !props.header.isRow2)) {
    return null
  }

  return <section className={`header ${props.header.isRow2 ? '-with-normal-hyps' : ''}`}>
    <div className="goal-username">hypotheses</div>
    {
      props.header.row1 &&
      <div className="data-hypotheses">
        {props.header.row1.map((hypNode, index) =>
          <HypothesisNode key={index} hypNode={hypNode} highlights={props.highlights}/>
        )}
      </div>
    }
  </section>
};

export default HeaderEl
