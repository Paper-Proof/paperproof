
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  sorry

[
  {
    "tacticApp": {
      "t": {
        "tacticString": "sorry",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r",
            "id": "_uniq.14550",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14549"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14548"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14547"
              }
            ]
          }
        ],
        "goalsAfter": []
      }
    }
  }
]