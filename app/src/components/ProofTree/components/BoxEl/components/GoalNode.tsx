import React from 'react';
import Hint from './Hint';
import { useGlobalContext } from 'src/indexBrowser';
import { GoalNode } from 'types';
import leanSearch from 'src/services/leanSearch';

const GoalNodeEl = ({ goalNode }: { goalNode: GoalNode }) => {
  const { highlights, searchedHypIds, setSearchedHypIds, proofTree } = useGlobalContext();
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

  return (
    <div className="wow">
      <div
        className={`goal -hint ${!highlights || highlights.goalId === goalNode.id ? "" : "-faded"}`}
        onDoubleClick={(event) => {
          event.preventDefault();
          event.stopPropagation();
          window.getSelection()?.removeAllRanges();
          setIsNewHypothesisShown(true);
        }}
        onClick={(event) => {
          event.stopPropagation();
        }}
      >
        <Hint>{goalNode}</Hint>
        {goalNode.text}
      </div>

      {isNewHypothesisShown && (
        <section className="search" onClick={(event) => { event.stopPropagation(); }}>
          <div className="goal">
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
      )}
    </div>
  );
};

export default GoalNodeEl;
