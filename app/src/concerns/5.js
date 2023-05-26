example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  have hehe : p := by
    have easy : true := by trivial
    sorry 
  sorry 


[
  {
    // have hehe : p := by
    "haveDecl": {
      "subSteps": [
        {
          // have easy : true := by trivial
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
                        "id": "_uniq.14662",
                        "hyps": [
                          {
                            "value": null,
                            "username": "r",
                            "type": "Prop",
                            "id": "_uniq.14640"
                          },
                          {
                            "value": null,
                            "username": "q",
                            "type": "Prop",
                            "id": "_uniq.14639"
                          },
                          {
                            "value": null,
                            "username": "p",
                            "type": "Prop",
                            "id": "_uniq.14638"
                          }
                        ]
                      }
                    ],
                    "goalsAfter": []
                  }
                }
              }
            ],
            "name": "have easy : true"
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
                  "type": "p",
                  "id": "_uniq.14664",
                  "hyps": [
                    {
                      "value": null,
                      "username": "easy",
                      "type": "true = true",
                      "id": "_uniq.14663"
                    },
                    {
                      "value": null,
                      "username": "r",
                      "type": "Prop",
                      "id": "_uniq.14640"
                    },
                    {
                      "value": null,
                      "username": "q",
                      "type": "Prop",
                      "id": "_uniq.14639"
                    },
                    {
                      "value": null,
                      "username": "p",
                      "type": "Prop",
                      "id": "_uniq.14638"
                    }
                  ]
                }
              ],
              "goalsAfter": []
            }
          }
        }
      ],
      "name": "have hehe : p"
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
            "id": "_uniq.14646",
            "hyps": [
              {
                "value": null,
                "username": "hehe",
                "type": "p",
                "id": "_uniq.14645"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14640"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14639"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14638"
              }
            ]
          }
        ],
        "goalsAfter": []
      }
    }
  }
]