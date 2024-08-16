import React from "react";
import Hint from "../../Hint";
import { HypNode } from "types";
import leanSearch from "src/services/leanSearch";
import { useGlobalContext } from "src/indexBrowser";

export interface HypothesisProps {
  hypNode: HypNode;
  withId?: boolean
}

const HypothesisNode = ({ withId = true, ...props }: HypothesisProps) => {
  const { searchedHypIds, setSearchedHypIds, proofTree } = useGlobalContext();

  // Example input: hypNode.name = "h._@.Examples._hyg.1162"
  // Example output: name = "h✝"
  const name = props.hypNode.name &&
    props.hypNode.name.includes(".")
    ? `${props.hypNode.name.split(".")[0]}✝`
    : props.hypNode.name;

  const [isNewHypothesisShown, setIsNewHypothesisShown] = React.useState(false);
  const [newHypothesis, setNewHypothesis] = React.useState("");
  const [suggestedTheorems, setSuggestedTheorems] = React.useState<string[]>([]);
  const { highlights } = useGlobalContext();

  const searchTheorems = async () => {
    const allHyps = proofTree.boxes
      .flatMap((box) => box.hypLayers.flatMap((hypLayer) => hypLayer.hypNodes))
    
    const searchedHyps = searchedHypIds
      .map((searchedId) => allHyps.find((hyp) => hyp.id === searchedId)!)

    const searchedHypTexts = searchedHyps.map((h) => h.text)

    const searchString = `given: ${searchedHypTexts.join(',')}, we want: ${newHypothesis}`
    const suggested = await leanSearch(searchString)
    setSuggestedTheorems(suggested)
  }

  const close = (event: React.MouseEvent) => {
    event.stopPropagation();
    setSearchedHypIds([])
    setSuggestedTheorems([])
    setNewHypothesis('')
    setIsNewHypothesisShown(false)
  }

  const onHypothesisClick = (event: React.MouseEvent) => {
    event.stopPropagation();
    const newSearchedHypIds = searchedHypIds.includes(props.hypNode.id)
      ? searchedHypIds.filter(id => id !== props.hypNode.id)
      : [...searchedHypIds, props.hypNode.id];
    setSearchedHypIds(newSearchedHypIds);
  }

  const isSearched = searchedHypIds.find((searchedId) => props.hypNode.id === searchedId)

  return <div className="wow">
    <div
      id={withId ? `hypothesis-${props.hypNode.id}` : undefined}
      className={`hypothesis -hint ${!highlights || highlights.hypIds.includes(props.hypNode.id) ? "" : "-faded"} ${props.hypNode.isProof} ${isSearched ? '-is-searched' : ''}`}
      onClick={onHypothesisClick}
      onDoubleClick={(event) => {
        event.preventDefault();
        event.stopPropagation();
        setIsNewHypothesisShown(true)
      }}
    >
      <Hint>{props.hypNode}</Hint>
      {name && <span className="name">{props.hypNode.name}</span>}
      {name && ": "}
      <span className="text">{props.hypNode.text}</span>
    </div>

    {
      isNewHypothesisShown &&
      <section className="search" onClick={(event) => { event.stopPropagation() }}>
        <div className="hypothesis">
          <input
            value={newHypothesis}
            onChange={(e) => setNewHypothesis(e.target.value)}
            placeholder="New hypothesis"
          />
        </div>
        <div>Please click on theorems you want to use</div>
        <button type="button" onClick={searchTheorems}>
          search
        </button>
        <button type="button" onClick={close}>
          close
        </button>

        {
          suggestedTheorems.length > 0 &&
          <div className="suggested-theorems">
            {
              suggestedTheorems.map((suggestedTheorem, index) =>
                <div key={index} className="theorem">
                  {suggestedTheorem}
                </div>
              )
            }
          </div>
        }
      </section>
    }
  </div>
};

export default HypothesisNode
