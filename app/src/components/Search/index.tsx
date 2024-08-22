import React from 'react';
import { useGlobalContext } from 'src/indexBrowser';
import leanSearch from 'src/services/leanSearch';
import { HypNode } from 'types';
import "./index.css";

interface SearchProps {
  children: React.ReactNode;
  hypNode: HypNode;
}

const Search = (props: SearchProps) => {
  const { searchedHypIds, setSearchedHypIds, proofTree } = useGlobalContext();
  const [isNewHypothesisShown, setIsNewHypothesisShown] = React.useState(false);
  const [newHypothesis, setNewHypothesis] = React.useState("");
  const [suggestedTheorems, setSuggestedTheorems] = React.useState<string[]>([]);

  const searchTheorems = async () => {
    const allHyps = proofTree.boxes
      .flatMap((box) => box.hypLayers.flatMap((hypLayer) => hypLayer.hypNodes));
    
    const searchedHyps = searchedHypIds
      .map((searchedId) => allHyps.find((hyp) => hyp.id === searchedId)!);

    const searchedHypTexts = searchedHyps.map((h) => h.text);

    const searchString = `given: ${searchedHypTexts.join(',')}, we want: ${newHypothesis}`;
    const suggested = await leanSearch(searchString);
    setSuggestedTheorems(suggested);
  };

  const close = (event: React.MouseEvent) => {
    event.stopPropagation();
    setSearchedHypIds([]);
    setSuggestedTheorems([]);
    setNewHypothesis('');
    setIsNewHypothesisShown(false);
  };

  const onHypothesisClick = (event: React.MouseEvent) => {
    event.stopPropagation();
    const newSearchedHypIds = searchedHypIds.includes(props.hypNode.id)
      ? searchedHypIds.filter(id => id !== props.hypNode.id)
      : [...searchedHypIds, props.hypNode.id];
    setSearchedHypIds(newSearchedHypIds);
  }

  return props.children

  return <div className="search-wrapper">
    <div
      onClick={onHypothesisClick}
      onDoubleClick={(event) => {
        event.preventDefault();
        event.stopPropagation();
        setIsNewHypothesisShown(true)
      }}
    >
      {props.children}
    </div>
    {
      isNewHypothesisShown &&
      <section className="search" onClick={(event) => { event.stopPropagation(); }}>
        <div className="hypothesis">
          <input
            value={newHypothesis}
            onChange={(e) => setNewHypothesis(e.target.value)}
            placeholder="New goal"
          />
        </div>
        <div>Please click on hypotheses you want to use</div>
        <button type="button" onClick={searchTheorems}>
          search
        </button>
        <button type="button" onClick={close}>
          close
        </button>

        {suggestedTheorems.length > 0 && (
          <div className="suggested-theorems">
            {suggestedTheorems.map((suggestedTheorem, index) => (
              <div key={index} className="theorem">
                {suggestedTheorem}
              </div>
            ))}
          </div>
        )}
      </section>
    }
  </div>
};

export default Search;
