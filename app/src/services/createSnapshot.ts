const generateSnapshotData = (): { proofTreeHTML: string } => {
  const proofTreeElement = document.querySelector('.proof-tree');
  if (!proofTreeElement) {
    throw new Error('Proof tree not found');
  }
  
  return {
    proofTreeHTML: proofTreeElement.outerHTML
  };
};

const paperproofXYZ = 'https://paperproof.xyz'

export const createSnapshot = async (): Promise<string> => {
  const data = generateSnapshotData();
  
  const response = await fetch(`${paperproofXYZ}/api/snapshot`, {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
    },
    body: JSON.stringify(data),
  });
  
  if (!response.ok) {
    throw new Error(`Failed to create snapshot: ${response.statusText}`);
  }
  
  const result = await response.json();
  return `${paperproofXYZ}/${result.id}`;
};
