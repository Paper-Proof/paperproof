import React from "react";
import { AnyTheoremSignature } from "types";

// BEFORE
// (a._@.Seymour.Matroid.Operations.Sum3.MatrixLikeSum3._hyg.8589: α )
// AFTER
// (anonymous: α )
const cleanHypName = (name: string) => {
  if (name.includes('_hyg')) {
    return '_';
  } else {
    return name;
  }
}

const renderArg = (pLeft: String, pRight: String, name: string | null, type: string) => {
  return <div className="arg" key={name}>
    <span className="parenthesis -left">{pLeft}</span>
    <span className="arg-name">{name ? cleanHypName(name) + ' : ' : ''}</span>
    <span className="arg-type">{type}</span>
    <span className="parenthesis -right">{pRight}</span>
  </div>
}

interface TheoremProps {
  theorem: AnyTheoremSignature;
}
const Theorem = ({ theorem }: TheoremProps) =>
  <div className="theorem">
    <div className="name">{theorem.declarationType} {theorem.name}</div>
    <div className="args">
      <div className="instance-args">
        {theorem.instanceArgs.map((arg) => renderArg("[", "]", null, arg.type))}
      </div>
      <div className="implicit-args">
        {theorem.implicitArgs.map((arg) => renderArg("{", "}", arg.name, arg.type))}
      </div>
      <div className="explicit-args">
        {theorem.explicitArgs.map((arg) => renderArg("(", ")", arg.name, arg.type))}
      </div>
    </div>
    <div className="type">
      : {theorem.type}
    </div>
    {theorem.declarationType === "def" && theorem.body && (
      <div className="body">
        := {theorem.body}
      </div>
    )}
  </div>;

export default Theorem;
