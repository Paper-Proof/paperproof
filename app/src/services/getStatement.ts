import { LeanProofTree } from 'types';

const getStatement = (steps: LeanProofTree): string | null => {
  return steps[0].goalsBefore[0].type ?? null;
};

export default getStatement;
