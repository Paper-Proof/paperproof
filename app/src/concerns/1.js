
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by

[
  {
    "tacticApp": {
      "t": {
        "tacticString": "by",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r",
            "id": "_uniq.14568",
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
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r",
            "id": "_uniq.14568",
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
        ]
      }
    }
  }
]