import React from 'react';

export default function Nav() {
  return (
    <header style={{position:"relative",zIndex:3,maxWidth:1180,margin:"0 auto",padding:"30px 40px 0",display:"flex",alignItems:"center",justifyContent:"space-between",background:"transparent"}}>
      <a href="/" style={{display:"flex",alignItems:"center",gap:11,textDecoration:"none",color:"#2B2722"}}>
        <img src="/paper.png" alt="Paperproof" style={{width:34,height:34,objectFit:"contain",filter:"drop-shadow(0 2px 3px rgba(0,0,0,0.12))"}} />
        <span style={{fontFamily:"'Newsreader',serif",fontSize:23,fontWeight:500,letterSpacing:"-0.01em"}}>paperproof</span>
      </a>
      <nav style={{display:"flex",alignItems:"center",gap:30,fontFamily:"'Spectral',serif",fontSize:16}}>
        <a href="/playground" style={{textDecoration:"none",color:"#6B6557"}}>Playground</a>
        <a href="https://github.com/Paper-Proof/paperproof" target="_blank" rel="noopener noreferrer" style={{textDecoration:"none",display:"inline-flex",alignItems:"center",gap:7,background:"#2B2722",color:"#FBF7EC",padding:"9px 18px",borderRadius:8,fontSize:15,fontFamily:"'JetBrains Mono',monospace",fontWeight:500}}>GitHub ↗</a>
      </nav>
    </header>
  );
}
