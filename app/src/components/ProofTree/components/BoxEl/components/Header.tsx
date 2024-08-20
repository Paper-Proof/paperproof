import React from "react";
import { Highlights, HypNode } from "types";
import HypothesisNode from "./Hypotheses/components/HypothesisNode";
import { HeaderInfo } from "..";

export interface HeaderProps {
  row1Hyps?: HypNode[];
  highlights: Highlights;
  headerInfo: HeaderInfo
}

const HeaderEl = (props: HeaderProps) => {
  const hi = props.headerInfo
  if (((!props.row1Hyps || props.row1Hyps.length === 0) && hi.ifHoistUp === false)) {
    return null
  }

  return <header className={
    `
    ${!hi.ifHoistUp ? '-row2Absent' : ''}
    ${(hi.ifHoistUp && hi.paddingBottomType === 'big') ? '-hoistAndPaddingBottomBig' : ''}
    ${(hi.ifHoistUp && hi.paddingBottomType === 'small') ? '-hoistAndPaddingBottomSmall' : ''}
    `
  }>
    <div className="title">hypotheses</div>
    {
      props.row1Hyps && props.row1Hyps.length > 0 &&
      <div className="row-1">
        {props.row1Hyps.map((hypNode, index) =>
          <HypothesisNode key={index} hypNode={hypNode} highlights={props.highlights}/>
        )}
      </div>
    }
    {/* We pull up hyp nodes from below to fit into this { position: absolute; } div */}
    <div className="row-2"/>
  </header>
};

export default HeaderEl
