import { LeanProofTree } from 'types';

const getStatement = (subSteps: LeanProofTree): string | null => {
  const firstStep = subSteps[0];
  if ('tacticApp' in firstStep) {
    return firstStep.tacticApp.t.goalsBefore[0].type;
  } else if ('haveDecl' in firstStep) {
    return firstStep.haveDecl.t.goalsBefore[0].type;
  }
  return null;
}

export default getStatement;
