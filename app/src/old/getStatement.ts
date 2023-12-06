import { LeanProofTree } from 'types';

// NOTE: this is for updateUI
// (https://github.com/Paper-Proof/paperproof/blob/47dd21da64d8b1ce42a5f1fe921e96072e376023/app/src/services/updateUI/index.ts#L38)
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
