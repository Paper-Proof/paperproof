import LeaderLine from './LeaderLine.min.js';

const createDependsOnArrows = () => {
  const el1 = document.getElementsByClassName('hypothesis')[1];
  const el2 = document.getElementsByClassName('hypothesis')[2];
  if (!el1 || !el2) return null;
  const newLeaderLine = new LeaderLine(el1, el2);
  newLeaderLine.setOptions({ path: "straight", startSocket: "bottom", endSocket: "top", size: 4 });
  return newLeaderLine;
}

export default createDependsOnArrows;
