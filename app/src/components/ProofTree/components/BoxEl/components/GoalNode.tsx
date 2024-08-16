import React from 'react';
import Hint from './Hint';
import { useGlobalContext } from 'src/indexBrowser';
import { GoalNode } from 'types';

const GoalNodeEl = ({ goalNode }: { goalNode: GoalNode }) => {
  const { highlights } = useGlobalContext();
  return <div className={`goal -hint ${!highlights || highlights.goalId === goalNode.id ? "" : "-faded"}`}>
    <Hint>{goalNode}</Hint>
    {goalNode.text}
  </div>
};

export default GoalNodeEl;
