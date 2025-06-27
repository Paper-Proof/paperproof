import React from "react";
import { Arrow, Position, PositionStartStop, Tactic, TheoremSignature } from "types";
import Hint from "./ProofTree/components/BoxEl/components/Hint";
import PerfectArrow from "./PerfectArrow";
import { useGlobalContext } from "src/indexBrowser";
import createArrow from "src/services/createArrow";
import prettifyTacticText from "src/services/prettifyTacticText";

const isPositionWithin = (cursor: Position, tactic: PositionStartStop): boolean => {
  // If tactic spans many lines, it just means it's the last tactic in this proof, and Lean thinks empty lines below belong to this tactic
  const tacticSpansManyLines = tactic.stop.line - tactic.start.line > 1;
  const stopLine = tacticSpansManyLines ? tactic.start.line + 1 : tactic.stop.line;
  const stopCharacter = tacticSpansManyLines ? 0 : tactic.stop.character;
  return (
    cursor.line > tactic.start.line || 
    (cursor.line === tactic.start.line && cursor.character >= tactic.start.character)
  )
  &&
  (
    cursor.line < stopLine || 
    (cursor.line === stopLine && cursor.character < stopCharacter)
  );
};

interface TacticNodeProps {
  tactic?: Tactic;
  className?: string;
  shardId?: string;
  isActiveGoal?: boolean;
  onClick?: (e: React.MouseEvent) => void;
  circleEl?: React.ReactNode;
}
const TacticNode = (props: TacticNodeProps) => {
  const isEllipsisTactic = (!props.tactic || props.tactic.text.includes("sorry")) && props.isActiveGoal;
  if (isEllipsisTactic) {
    return <div className="active-tactic">
      {/* <img src="https://private-user-images.githubusercontent.com/7578559/264729795-58f24cf2-4336-4376-8738-6463e3802ba0.png?jwt=eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJnaXRodWIuY29tIiwiYXVkIjoicmF3LmdpdGh1YnVzZXJjb250ZW50LmNvbSIsImtleSI6ImtleTUiLCJleHAiOjE3MzE0NzEwMTksIm5iZiI6MTczMTQ3MDcxOSwicGF0aCI6Ii83NTc4NTU5LzI2NDcyOTc5NS01OGYyNGNmMi00MzM2LTQzNzYtODczOC02NDYzZTM4MDJiYTAucG5nP1gtQW16LUFsZ29yaXRobT1BV1M0LUhNQUMtU0hBMjU2JlgtQW16LUNyZWRlbnRpYWw9QUtJQVZDT0RZTFNBNTNQUUs0WkElMkYyMDI0MTExMyUyRnVzLWVhc3QtMSUyRnMzJTJGYXdzNF9yZXF1ZXN0JlgtQW16LURhdGU9MjAyNDExMTNUMDQwNTE5WiZYLUFtei1FeHBpcmVzPTMwMCZYLUFtei1TaWduYXR1cmU9ZWRkYTkxZWQ0N2QzZjhiZmI4NzFjNzZlYTc4NmQ5YTU1ODc5NzNmZTcyYmY1ZjNjODYyYjc1MDJlNzEyYjU1OSZYLUFtei1TaWduZWRIZWFkZXJzPWhvc3QifQ.hPFir-MxOhsP9OxlaQ_uOmHBTZVJozmqo7rCvGv0ZFw"/> */}
      <div className="tactic -ellipsis">...</div>
    </div>
  }
  if (!props.tactic){
    return;
  }
  
  const [perfectArrows, setPerfectArrows] = React.useState<Arrow[]>([]);
  const thisEl = React.useRef<HTMLInputElement>(null);

  const global = useGlobalContext();

  React.useLayoutEffect(() => {
    if (!props.tactic) return;
    if (global.settings.isSingleTacticMode) return;
    const newPerfectArrows : Arrow[] = props.tactic.dependsOnIds
      .map((dependsOnHypId) => createArrow(`hypothesis-${dependsOnHypId}`, thisEl.current))
      .filter((arrow) : arrow is Arrow => arrow !== null);
    setPerfectArrows(newPerfectArrows);
  }, [props.tactic, global.UIVersion]);

  const isSorried = props.tactic.text.includes("sorry") || props.tactic.text === "done";
  const isSuccess = props.tactic.successGoalId && !isSorried;
  const isPositionMatch = global.settings.isSingleTacticMode ? false : isPositionWithin(global.position, props.tactic.position);

  const text = prettifyTacticText(props.tactic.text);

  const theorems = props.tactic.theorems || [];
  const [theorem, setTheorem] = React.useState<TheoremSignature | null>(null);

  // Extract short name from theorem (part after last dot)
  const getTheoremShortName = (theoremName: string): string => {
    const lastDotIndex = theoremName.lastIndexOf('.');
    return lastDotIndex !== -1 ? theoremName.substring(lastDotIndex + 1) : theoremName;
  };

  // Find all occurrences of theorem short names in the text
  const findTheoremMatches = (text: string, theorems: TheoremSignature[]) => {
    const matches: Array<{start: number, end: number, theorem: TheoremSignature}> = [];
    
    theorems.forEach(theorem => {
      const shortName = getTheoremShortName(theorem.name);
      let startIndex = 0;
      
      while (true) {
        const index = text.indexOf(shortName, startIndex);
        if (index === -1) break;
        
        // Check if this is a word boundary (not part of a larger identifier)
        const prevChar = index > 0 ? text[index - 1] : ' ';
        const nextChar = index + shortName.length < text.length ? text[index + shortName.length] : ' ';
        const isWordBoundary = !/[a-zA-Z0-9_]/.test(prevChar) && !/[a-zA-Z0-9_]/.test(nextChar);
        
        if (isWordBoundary) {
          matches.push({
            start: index,
            end: index + shortName.length,
            theorem
          });
        }
        
        startIndex = index + 1;
      }
    });
    
    // Sort matches by position to handle overlaps
    return matches.sort((a, b) => a.start - b.start);
  };

  // Render text with theorem highlights
  const renderTextWithTheorems = (text: string, theorems: TheoremSignature[]) => {
    const matches = findTheoremMatches(text, theorems);
    
    if (matches.length === 0) {
      return text;
    }
    
    const parts = [];
    let lastIndex = 0;
    
    matches.forEach((match, index) => {
      // Add text before the match
      if (match.start > lastIndex) {
        parts.push(text.substring(lastIndex, match.start));
      }
      
      // Add the highlighted theorem
      parts.push(
        <span
          key={`theorem-${index}`}
          className="theorem-highlight"
          onClick={(e) => {
            e.stopPropagation();
            e.preventDefault();
            if (theorem === match.theorem) {
              setTheorem(null)
            } else {
              setTheorem(match.theorem);
            }
          }}
        >
          {text.substring(match.start, match.end)}
        </span>
      );
      
      lastIndex = match.end;
    });
    
    // Add remaining text
    if (lastIndex < text.length) {
      parts.push(text.substring(lastIndex));
    }
    
    return parts;
  };

  return (
    <div 
      className={`
        tactic -hint
        ${props.className || ''}
        ${isSuccess ? '-success' : ''}
        ${isSorried ? '-sorried' : ''}
        ${isPositionMatch ? '-position-matches' : ''}
      `} 
      id={props.shardId ?
        `tactic-${props.tactic.id}-${props.shardId}` :
        `tactic-${props.tactic.id}`
      }
      onClick={props.onClick}
      ref={thisEl}
    >
      <Hint>{props.tactic}</Hint>
      {
        isSuccess ?
        <div className="text">
          <span>🎉</span> <span>{renderTextWithTheorems(text, theorems)}</span> <span>🎉</span>
        </div> :
        <div className="text">
          {renderTextWithTheorems(text, theorems)}
        </div>
      }

      {
        theorem &&
        <section className="theorem-wrapper">
          <div className="theorem">
            <div className="name">{theorem.name}</div>
            <div className="args">
              <div className="instance-args">
                {theorem.instanceArgs.map((arg) =>
                  <div className="arg">{`[ ${arg.type} ]`}</div>
                )}
              </div>
              <div className="implicit-args">
                {theorem.implicitArgs.map((arg) =>
                  <div className="arg">{`{ `}<span className="name">{arg.name}</span>{`: ${arg.type} }`}</div>
                )}
              </div>
              <div className="explicit-args">
                {theorem.explicitArgs.map((arg) =>
                  <div className="arg">{`( `}<span className="name">{arg.name}</span>{`: ${arg.type} )`}</div>
                )}
              </div>
            </div>
            <div className="body">
              : {theorem.body}
            </div>
          </div>
        </section>
      }
      {!props.circleEl && perfectArrows.map((arrow, index) =>
        <PerfectArrow key={index} p1={arrow.from} p2={arrow.to}/>
      )}
      {props.circleEl}
    </div>
  );
};

export default TacticNode;
