import { LeanProofTree } from 'types';

const getStatement = (steps: LeanProofTree): string | null => {
  return steps[0].goalBefore.type ?? null;
};

export default getStatement;
