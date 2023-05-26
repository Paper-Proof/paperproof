// works
const infoTreeExample_1 = []

// works
const infoTreeExample_2 = []

// TODO
// Make sure renames work (they likely don't).
// Make sure 3 nested windows work.
const infoTreeExample_3 = []

// infinitude of primes, except without lets and {} for now.
const infoTreeExample_4 = []

const infoTreeExample_5 = [
  {
    "tacticApp": {
      "t": {
        "tacticString": "have hehe : ℕ := 5",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r",
            "id": "_uniq.9215",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.9214"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.9213"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.9212"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r",
            "id": "_uniq.9229",
            "hyps": [
              {
                "value": null,
                "username": "hehe",
                "type": "ℕ",
                "id": "_uniq.9228"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.9214"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.9213"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.9212"
              }
            ]
          }
        ]
      }
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
            "id": "_uniq.9229",
            "hyps": [
              {
                "value": null,
                "username": "hehe",
                "type": "ℕ",
                "id": "_uniq.9228"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.9214"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.9213"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.9212"
              }
            ]
          }
        ],
        "goalsAfter": []
      }
    }
  }
]

export { infoTreeExample_1, infoTreeExample_2, infoTreeExample_3, infoTreeExample_4, infoTreeExample_5 }
