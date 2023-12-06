const hypRect = hypEl.getBoundingClientRect();
const p1 = {x: hypRect.left + hypRect.width / 2, y: hypRect.bottom};

const tacticRect = tacticRef.current.getBoundingClientRect();
const p2 = {x: tacticRect.left + tacticRect.width / 2, y: tacticRect.top};

const p1 = {x: 0, y: 0}
const p2 = {x: 200, y: 200}
return <PerfectArrow key={hypId} p1={p1} p2={p2}/>