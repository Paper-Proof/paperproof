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
    const suggested = await leanSearch(newHypothesis)
    setSuggestedTheorems(suggested)
  }

  return <div className="wow">
    <div
      id={withId ? `hypothesis-${props.hypNode.id}` : undefined}
      className={`hypothesis -hint ${!highlights || highlights.hypIds.includes(props.hypNode.id) ? "" : "-faded"} ${props.hypNode.isProof}`}
      onClick={(event) => { event.stopPropagation() }}
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
        <button type="button" onClick={searchTheorems}>
          search
        </button>

        {
          suggestedTheorems.length > 0 &&
          <div className="suggested-theorems">
            {
              suggestedTheorems.map((suggestedTheorem) =>
                <div className="theorem">
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
