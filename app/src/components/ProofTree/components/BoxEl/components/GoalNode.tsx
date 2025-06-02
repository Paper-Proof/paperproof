import React from 'react';
import Hint from './Hint';
import { useGlobalContext } from 'src/indexBrowser';
import { TypeGoalNode } from 'types';

const GoalNodeEl = ({ goalNode }: { goalNode: TypeGoalNode }) => {
  const { highlights } = useGlobalContext();
  return (
    <div className={`goal -hint ${highlights?.goalId === goalNode.id ? "-highlighted" : ""}`}>
      <Hint>{goalNode}</Hint>
      {goalNode.text}
    </div>
  );
};

export default GoalNodeEl;
