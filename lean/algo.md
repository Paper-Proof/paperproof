Thoughts

We will assume that the tactic always operates on the main goal (first in the list).
We can assume there is no cycles like as the tactic always creates a new goal or preserves the existing one:
goal1 -> tactic1 -> goal2 -> tactic2 -> goal1
If tactic doesn't change anything [1] -> [1] it shouldn't add an edge and be included as a proof step.
If tactic does change main goal [1] -> [2, 3] then it means that there is an incoming edge into [2, 3].
What we should do is to have an incoming edge into every goal mentioned in the InfoTree except top goal.

We can rely on the list of proof steps as it will only contain actual edges to find what goals already have an
incoming edge and will also bubble up the goals which don't have the incoming edge yet. Those unmatched goals
would be matched as a step from [goalBefore -> unmatchedGoals] at the first TacticInfo node referring to the
actual syntax written by the user.


Facts about InfoTree
From one side: Info tree is a map from Elaboration steps into parts of syntax.
There are many elaboration infos:
- TermInfo
- TacticInfo <<---
- CommandInfo
- ...

Algorithm properties
1) We never want to output synthetic SourceInfo, always only what user wrote
2) Every goal ever mentioned in any of TacticInfo nodes should be in the output


 Why it's good to separate before and after
 evalTacticSeq: `apply th1; apply th2`
 Top level: {
    steps: [{tactic: `apply th1`, goalsBefore: [1], goalsAfter: [2]}],
    steps: [{tactic: `apply th2`, goalsBefore: [2], goalsBefore: [3]}],
    goalsBefore: [1], goalsAfter: [3]}
 children: [
  {
    steps: [{tactic: `apply th1`, goalsBefore: [1], goalsAfter: [2]}],
    goalsBefore: [1], goalsAfter: [2]
  }, {
    steps: [{tactic: `apply th2`, goalsBefore: [2], goalsBefore: [3]}]
    goalsBefore: [2], goalsAfter: [3]
  }
 evalCases: `cases h with | inl h1 => apply th1 | inr h2 => apply th2`
 Top level: {
   steps: [
    {tactic: `cases h with`, goalsBefore: [1], goalsAfter: [2, 3]},
   ],
   goalsBefore: [1],
   goalsAfter: []
 }
 children: [
   {steps: [], goalsBefore: [1], goalsAfter: [1]}
   {steps: [{tactic: `apply th1`, goalsBefore: [2], goalsAfter: []}],
      goalsBefore: [2], goalsAfter: []},
   {steps: [{tactic: `apply th2`, goalsBefore: [3], goalsAfter: []}],
      goalsBefore: [3], goalsAfter: []}
 ]
 We want: [cases caused [1] -> [2, 3]]

 evalCases: `cases h with rw [hq] | inl h1 => apply th1 | inr h2 => apply th2`
 Top level: {
   steps: [
    {tactic: `cases h with`, goalsBefore: [1], goalsAfter: [2, 3]},
   ],
   goalsBefore: [1],
   goalsAfter: []
 }
 children: [
   {steps: [], goalsBefore: [1], goalsAfter: [1]}
   {steps: [{tactic: `apply th1`, goalsBefore: [4], goalsAfter: []}],
      goalsBefore: [4], goalsAfter: []},
   {steps: [{tactic: `rw [hq]`, goalsBefore: [2], goalsAfter: [4]}],
      goalsBefore: [2], goalsAfter: [4]},
   {steps: [{tactic: `apply th2`, goalsBefore: [5], goalsAfter: []}],
   goalsBefore: [5], goalsAfter: []}
   {steps: [{tactic: `rw [hq]`, goalsBefore: [3], goalsAfter: [5]}],
      goalsBefore: [3], goalsAfter: [5]},
 ]
 We want: [cases caused [1] -> [2, 3]]

 
 evalMatch: `match l with | [] => ... | a :: ln => ...`
 Top level: {
  steps: [],
  goalsBefore: [1, 2, 3],
  goalsAfter: []
 }
 children: [
  {steps: [], goalsBefore: [2], goalsAfter: []},
  {steps: [], goalsBefore: [3], goalsAfter: []},
 ]
