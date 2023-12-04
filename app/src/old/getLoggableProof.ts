import { ProofResponse } from 'types';
import converter from './converter';

// This is resource-heavy, one of the reasons we want a production build that strips console.logs
const getLoggableProof = (proof: ProofResponse) => {
  if (!proof) {
    return null;
  } else if ("error" in proof) {
    return proof;
  } else {
    return converter(proof.proofTree);
  }
}

export default getLoggableProof;
