import React, { useLayoutEffect, useRef } from "react";
import type * as Public from "../react";
import { ShadowTree } from "./ShadowTree";

export const Paperproof: typeof Public.Paperproof = ({ className, style, ...props }) => {
  const host = useRef<HTMLDivElement>(null);
  const tree = useRef<ShadowTree | null>(null);
  useLayoutEffect(() => {
    tree.current = new ShadowTree(host.current!);
    return () => { tree.current?.unmount(); tree.current = null; };
  }, []);
  useLayoutEffect(() => { tree.current?.render(props); });
  return <div ref={host} className={className} style={style}/>;
};
