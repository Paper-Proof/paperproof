import React from "react";
import { HypNode } from "types";
import HypothesisNode from "./Hypotheses/components/HypothesisNode";
import { HeaderInfo } from "..";

export interface HeaderProps {
  row1Hyps?: HypNode[];
  headerInfo: HeaderInfo
}

// TODO
// This should be refactored using `anchor-size()` css property
// (https://developer.mozilla.org/en-US/docs/Web/CSS/anchor-size),
// but only when vscode switched from chrome 124 to chrome 125.
// Right now the header lacks height when the hypotheses are lengthy, e.g. here:
//
//   theorem simple_ex (n m : ℕ)
//     (h1 : ∀ {a b : Nat}, a + b = b + a)
//     (h2 : ∀ {a b : Nat}, a = b + b):
//       n + m = m + n := by
//     simp [h1, h2]
//
// To be clear - anchor will be the <td/> with `h1` hypothesis inside,
// and we'll be setting .row-2's { height: '' } based on that element's height.
//
// Or, better, we'll remove .row-2, and start coloring the fake <div> inside of the .hypothesis-table, that will take up the natural height, *and* .proof-tree's width.
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
        <div>
          {
            props.row1Hyps.filter((h) => h.isProof === 'data')
            .map((hypNode, index) => <HypothesisNode key={index} hypNode={hypNode}/>)
          }
        </div>
        {
          props.row1Hyps.filter((h) => h.isProof === 'proof').length > 0 &&
          <div className="single-tactic-hyp-row">
            {
              props.row1Hyps.filter((h) => h.isProof === 'proof')
              .map((hypNode, index) => <HypothesisNode key={index} hypNode={hypNode}/>)
            }
          </div>
        }
      </div>
    }
    {/* We pull up hyp nodes from below to fit into this { position: absolute; } div */}
    <div className="row-2"/>
  </header>
};

export default HeaderEl
