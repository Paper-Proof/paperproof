
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  have r : p := by sorry
  sorry

if we find the first tactic

// 1. We determine which window we're in by searching by mvarId
// 2. Then we keep adding nodes, arrows, etc. based on .goalsBefore and .goalsAfter of each new tactic.


[
  {
    "haveDecl": {
      "subSteps": [
        {
          "tacticApp": {
            "t": {
              "tacticString": "sorry",
              "tacticDependsOn": [],
              "goalsBefore": [
                {
                  "username": "[anonymous]",
                  "type": "p",
                  "id": "_uniq.14526",
                  "hyps": [
                    {
                      "value": null,
                      "username": "r",
                      "type": "Prop",
                      "id": "_uniq.14522"
                    },
                    {
                      "value": null,
                      "username": "q",
                      "type": "Prop",
                      "id": "_uniq.14521"
                    },
                    {
                      "value": null,
                      "username": "p",
                      "type": "Prop",
                      "id": "_uniq.14520"
                    }
                  ]
                }
              ],
              "goalsAfter": []
            }
          }
        }
      ],
      "name": "have r : p"
    }
  },
  {
    "tacticApp": {
      "t": {
        "tacticString": "sorry",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "p ∧ (q ∨ r✝) ↔ p ∧ q ∨ p ∧ r✝",
            "id": "_uniq.14528",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "p",
                "id": "_uniq.14527"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14522"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14521"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14520"
              }
            ]
          }
        ],
        "goalsAfter": []
      }
    }
  }
]