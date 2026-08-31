import React from 'react';
import katex from 'katex';
import 'katex/dist/katex.min.css';
import Hint from './Hint';
import { useGlobalContext } from 'src/indexBrowser';
import { TypeGoalNode } from 'types';
import fancySubstringHypotheses from 'src/services/fancySubstringHypotheses';

const GoalNodeEl = ({ goalNode }: { goalNode: TypeGoalNode }) => {
  const global = useGlobalContext();
  const { latexSettings } = global;

  const latexString = latexSettings.isActive ? latexSettings.map[goalNode.text] : undefined;

  return (
    <div className={`goal -hint ${global.highlights?.goalId === goalNode.id ? "-highlighted" : ""}`}>
      <Hint>{goalNode}</Hint>
      {latexString
        ? <div className="text" dangerouslySetInnerHTML={{ __html: katex.renderToString(latexString, { throwOnError: false, displayMode: true }) }}/>
        : <div className="text">{fancySubstringHypotheses(goalNode.text, global)}</div>
      }
    </div>
  );
};

export default GoalNodeEl;
