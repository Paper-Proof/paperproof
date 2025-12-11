import Lean

open Lean Elab

namespace Paperproof.Services

/--
  InfoTree has a lot of non-user-written intermediate `TacticInfo`s, this function returns `none` for those.
  @EXAMPLES
  `tInfo.stx`               //=> `(Tactic.tacticSeq1Indented [(Tactic.exact "exact" (Term.proj ab "." (fieldIdx "2")))])`
  `tInfo.stx.getSubstring?` //=> `(some (exact ab.2 ))`
  `tInfo.stx`               //=> `(Tactic.rotateRight "rotate_right" []) -- (that's not actually present in our proof)`
  `tInfo.stx.getSubstring?` //=> `None`
-/
def getTacticSubstring (tInfo : TacticInfo) : Option Substring.Raw :=
  match tInfo.stx.getSubstring? with
  | .some substring => substring
  | .none => none

end Paperproof.Services
