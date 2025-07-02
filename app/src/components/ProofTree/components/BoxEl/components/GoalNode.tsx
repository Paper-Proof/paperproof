import React from 'react';
import Hint from './Hint';
import { useGlobalContext } from 'src/indexBrowser';
import { TypeGoalNode } from 'types';
import fancySubstringHypotheses from 'src/services/fancySubstringHypotheses';

const GoalNodeEl = ({ goalNode }: { goalNode: TypeGoalNode }) => {
  const global = useGlobalContext();

  return (
    <div className={`goal -hint ${global.highlights?.goalId === goalNode.id ? "-highlighted" : ""}`}>
      <Hint>{goalNode}</Hint>
      <div className="text">{fancySubstringHypotheses(goalNode.text, global)}</div>
    </div>
  );
};

export default GoalNodeEl;
