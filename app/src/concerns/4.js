
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  have hehe : true := by trivial
  sorry 

// To create the parent window,
// Find a 1st tacticApp that is NOT within a haveDecl, and take a look at its goalsBefore[0].


[
  {
    "haveDecl": {
      "subSteps": [
        {
          "tacticApp": {
            "t": {
              "tacticString": "trivial",
              "tacticDependsOn": [],
              "goalsBefore": [
                {
                  "username": "[anonymous]",
                  "type": "true = true",
                  "id": "_uniq.14584",
                  "hyps": [
                    {
                      "value": null,
                      "username": "r",
                      "type": "Prop",
                      "id": "_uniq.14567"
                    },
                    {
                      "value": null,
                      "username": "q",
                      "type": "Prop",
                      "id": "_uniq.14566"
                    },
                    {
                      "value": null,
                      "username": "p",
                      "type": "Prop",
                      "id": "_uniq.14565"
                    }
                  ]
                }
              ],
              "goalsAfter": []
            }
          }
        }
      ],
      "name": "have hehe : true"
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
            "type": "p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r",
            "id": "_uniq.14586",
            "hyps": [
              {
                "value": null,
                "username": "hehe",
                "type": "true = true",
                "id": "_uniq.14585"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14567"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14566"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14565"
              }
            ]
          }
        ],
        "goalsAfter": []
      }
    }
  }
]