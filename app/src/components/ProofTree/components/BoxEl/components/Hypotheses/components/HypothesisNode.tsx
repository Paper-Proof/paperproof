import React from "react";
import Hint from "../../Hint";
import { HypNode } from "types";
import { useGlobalContext } from "src/indexBrowser";
import prettifyHypothesisUsername from "src/services/prettifyHypothesisUsername";
import Search from "src/components/Search";

export interface HypothesisProps {
  hypNode: HypNode;
  withId?: boolean
}

const HypothesisNode = ({ withId = true, ...props }: HypothesisProps) => {
  const { searchedHypIds } = useGlobalContext();

  const name = prettifyHypothesisUsername(props.hypNode.name)
  const { highlights } = useGlobalContext();

  const isSearched = searchedHypIds.find((searchedId) => props.hypNode.id === searchedId)

  return(
    <Search hypNode={props.hypNode}>
      <div
        id={withId ? `hypothesis-${props.hypNode.id}` : undefined}
        className={`hypothesis -hint ${!highlights || highlights.hypIds.includes(props.hypNode.id) ? "" : "-faded"} ${props.hypNode.isProof} ${isSearched ? '-is-searched' : ''}`}
      >
        <Hint>{props.hypNode}</Hint>
        {name && <span className="name">{props.hypNode.name}</span>}
        {name && ": "}
        <span className="text">{props.hypNode.text}</span>
      </div>
    </Search>
  )
};

export default HypothesisNode
