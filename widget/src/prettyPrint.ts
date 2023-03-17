export type Info = { text: string } | { tag: Info } | { append: Info[] };

export function unfold(info: any): Info {
  if ("text" in info) {
    return { text: info.text };
  }
  if ("tag" in info) {
    return { tag: unfold(info.tag[1]) };
  }
  if ("append" in info) {
    return { append: info.append.map(unfold) };
  }
  return { text: "bad" };
}

function toString(info: Info): string {
  if ("text" in info) {
    return info.text;
  }
  if ("tag" in info) {
    return toString(info.tag);
  }
  if ("append" in info) {
    return info.append.map(toString).join("");
  }
  return "error";
}

function toTailTag(info: Info): string[] {
  if ("text" in info) {
    return [info.text];
  }
  if ("tag" in info) {
    return toTailTag(info.tag);
  }
  if ("append" in info) {
    return [
      toString({ append: info.append.slice(0, -1) }),
      ...toTailTag(info.append[info.append.length - 1]),
    ];
  }
  return ["error"];
}

export type PiSigma = { type: "∀" | "∃" | ""; v: string };

function trimQuant(s: string) {
  for (let iter = 0; iter < 10; iter++) {
    if (["∀", "∃", "("].some((c) => s.startsWith(c))) {
      s = s.substring(1);
    }
    if (["→", "∧", ",", ")"].some((c) => s.endsWith(c))) {
      s = s.substring(0, s.length - 1);
    }
    s = s.trim();
  }
  return s;
}

function toPiSigma(tt: string): PiSigma {
  const prefix = tt.trim();
  const v = trimQuant(prefix);
  if (prefix.startsWith("∀") || prefix.endsWith("→")) {
    return { v, type: "∀" };
  }
  if (prefix.startsWith("∃") || prefix.endsWith("∧")) {
    return { v, type: "∃" };
  }
  return { v, type: "" };
}

export function toResult(ps: PiSigma[]): string {
  return ps.map((p) => `${p.type} (${p.v})`).join(" ");
}

export function transform(s: Info) {
  return toTailTag(unfold(s)).map(toPiSigma);
}

export function toGoodFormat(s: { type: string; v: string }[]): string[] {
  // forall eps, forall eps > 0 - should go to -> forall eps > 0
  let currentType = "dd";
  let buffer: string[] = [];
  const res: string[] = [];
  function flush() {
    if (buffer.length) {
      // If it starts with introduction, but follow with condition - remove it, e.g. forall eps : Nat
      if (buffer.length > 1 && buffer[0].match(/^\p{L}($| : )/u)) {
        buffer = buffer.slice(1);
      }
      res.push(currentType + buffer.join(" "));
    }
  }
  for (const { type, v } of s) {
    if (type == currentType) {
      buffer.push(v);
    } else {
      flush();
      buffer = [v];
      currentType = type;
    }
  }
  flush();
  return res;
}
