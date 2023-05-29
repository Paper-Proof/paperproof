// works
const infoTreeExample_1 = []

// TODO, rw of hypothesis doesn't work
// example : (b = c) → (b = a) → (a = d) := by
//   intro bc ba
//   rw [ba] at bc
//   sorry
const infoTreeExample_2 = [
  {
    "tacticApp": {
      "t": {
        "tacticString": "intro bc ba",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "b = c → b = a → a = d",
            "id": "_uniq.7422",
            "hyps": [
              {
                "value": null,
                "username": "d",
                "type": "α✝",
                "id": "_uniq.7421"
              },
              {
                "value": null,
                "username": "a",
                "type": "α✝",
                "id": "_uniq.7420"
              },
              {
                "value": null,
                "username": "c",
                "type": "α✝",
                "id": "_uniq.7419"
              },
              {
                "value": null,
                "username": "b",
                "type": "α✝",
                "id": "_uniq.7418"
              },
              {
                "value": null,
                "username": "α._@.Examples._hyg.1026",
                "type": "Sort ?u.7410",
                "id": "_uniq.7417"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "a = d",
            "id": "_uniq.7428",
            "hyps": [
              {
                "value": null,
                "username": "ba",
                "type": "b = a",
                "id": "_uniq.7427"
              },
              {
                "value": null,
                "username": "bc",
                "type": "b = c",
                "id": "_uniq.7424"
              },
              {
                "value": null,
                "username": "d",
                "type": "α✝",
                "id": "_uniq.7421"
              },
              {
                "value": null,
                "username": "a",
                "type": "α✝",
                "id": "_uniq.7420"
              },
              {
                "value": null,
                "username": "c",
                "type": "α✝",
                "id": "_uniq.7419"
              },
              {
                "value": null,
                "username": "b",
                "type": "α✝",
                "id": "_uniq.7418"
              },
              {
                "value": null,
                "username": "α._@.Examples._hyg.1026",
                "type": "Sort ?u.7410",
                "id": "_uniq.7417"
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
        "tacticString": "rw ba",
        "tacticDependsOn": [
          "_uniq.7424",
          "_uniq.7427"
        ],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "a = d",
            "id": "_uniq.7428",
            "hyps": [
              {
                "value": null,
                "username": "ba",
                "type": "b = a",
                "id": "_uniq.7427"
              },
              {
                "value": null,
                "username": "bc",
                "type": "b = c",
                "id": "_uniq.7424"
              },
              {
                "value": null,
                "username": "d",
                "type": "α✝",
                "id": "_uniq.7421"
              },
              {
                "value": null,
                "username": "a",
                "type": "α✝",
                "id": "_uniq.7420"
              },
              {
                "value": null,
                "username": "c",
                "type": "α✝",
                "id": "_uniq.7419"
              },
              {
                "value": null,
                "username": "b",
                "type": "α✝",
                "id": "_uniq.7418"
              },
              {
                "value": null,
                "username": "α._@.Examples._hyg.1026",
                "type": "Sort ?u.7410",
                "id": "_uniq.7417"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "a = d",
            "id": "_uniq.7446",
            "hyps": [
              {
                "value": null,
                "username": "ba",
                "type": "b = a",
                "id": "_uniq.7443"
              },
              {
                "value": null,
                "username": "bc",
                "type": "a = c",
                "id": "_uniq.7440"
              },
              {
                "value": null,
                "username": "d",
                "type": "α✝",
                "id": "_uniq.7421"
              },
              {
                "value": null,
                "username": "a",
                "type": "α✝",
                "id": "_uniq.7420"
              },
              {
                "value": null,
                "username": "c",
                "type": "α✝",
                "id": "_uniq.7419"
              },
              {
                "value": null,
                "username": "b",
                "type": "α✝",
                "id": "_uniq.7418"
              },
              {
                "value": null,
                "username": "α._@.Examples._hyg.1026",
                "type": "Sort ?u.7410",
                "id": "_uniq.7417"
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
        "tacticString": "rw rfl",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "a = d",
            "id": "_uniq.7446",
            "hyps": [
              {
                "value": null,
                "username": "ba",
                "type": "b = a",
                "id": "_uniq.7443"
              },
              {
                "value": null,
                "username": "bc",
                "type": "a = c",
                "id": "_uniq.7440"
              },
              {
                "value": null,
                "username": "d",
                "type": "α✝",
                "id": "_uniq.7421"
              },
              {
                "value": null,
                "username": "a",
                "type": "α✝",
                "id": "_uniq.7420"
              },
              {
                "value": null,
                "username": "c",
                "type": "α✝",
                "id": "_uniq.7419"
              },
              {
                "value": null,
                "username": "b",
                "type": "α✝",
                "id": "_uniq.7418"
              },
              {
                "value": null,
                "username": "α._@.Examples._hyg.1026",
                "type": "Sort ?u.7410",
                "id": "_uniq.7417"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "a = d",
            "id": "_uniq.7446",
            "hyps": [
              {
                "value": null,
                "username": "ba",
                "type": "b = a",
                "id": "_uniq.7443"
              },
              {
                "value": null,
                "username": "bc",
                "type": "a = c",
                "id": "_uniq.7440"
              },
              {
                "value": null,
                "username": "d",
                "type": "α✝",
                "id": "_uniq.7421"
              },
              {
                "value": null,
                "username": "a",
                "type": "α✝",
                "id": "_uniq.7420"
              },
              {
                "value": null,
                "username": "c",
                "type": "α✝",
                "id": "_uniq.7419"
              },
              {
                "value": null,
                "username": "b",
                "type": "α✝",
                "id": "_uniq.7418"
              },
              {
                "value": null,
                "username": "α._@.Examples._hyg.1026",
                "type": "Sort ?u.7410",
                "id": "_uniq.7417"
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
            "type": "a = d",
            "id": "_uniq.7446",
            "hyps": [
              {
                "value": null,
                "username": "ba",
                "type": "b = a",
                "id": "_uniq.7443"
              },
              {
                "value": null,
                "username": "bc",
                "type": "a = c",
                "id": "_uniq.7440"
              },
              {
                "value": null,
                "username": "d",
                "type": "α✝",
                "id": "_uniq.7421"
              },
              {
                "value": null,
                "username": "a",
                "type": "α✝",
                "id": "_uniq.7420"
              },
              {
                "value": null,
                "username": "c",
                "type": "α✝",
                "id": "_uniq.7419"
              },
              {
                "value": null,
                "username": "b",
                "type": "α✝",
                "id": "_uniq.7418"
              },
              {
                "value": null,
                "username": "α._@.Examples._hyg.1026",
                "type": "Sort ?u.7410",
                "id": "_uniq.7417"
              }
            ]
          }
        ],
        "goalsAfter": []
      }
    }
  }
]

// TODO
// Make sure renames work (they likely don't).
// Make sure 3 nested windows work.
const infoTreeExample_3 =[
  {
    "tacticApp": {
      "t": {
        "tacticString": "apply Iff.intro",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r",
            "id": "_uniq.8448",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mp",
            "type": "p ∧ (q ∨ r) → p ∧ q ∨ p ∧ r",
            "id": "_uniq.8456",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.8457",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
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
        "tacticString": "intro h",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "mp",
            "type": "p ∧ (q ∨ r) → p ∧ q ∨ p ∧ r",
            "id": "_uniq.8456",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.8457",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mp",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.8461",
            "hyps": [
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.8460"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.8457",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
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
        "tacticString": "cases h.right",
        "tacticDependsOn": [
          "_uniq.8460"
        ],
        "goalsBefore": [
          {
            "username": "mp",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.8461",
            "hyps": [
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.8460"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.8457",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mp.inl",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.8516",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1713",
                "type": "q",
                "id": "_uniq.8502"
              },
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.8460"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mp.inr",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.8530",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1715",
                "type": "r",
                "id": "_uniq.8517"
              },
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.8460"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.8457",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
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
        "tacticString": "exact Or.inl ⟨h.left, ‹q›⟩",
        "tacticDependsOn": [
          "_uniq.8460"
        ],
        "goalsBefore": [
          {
            "username": "mp.inl",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.8516",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1713",
                "type": "q",
                "id": "_uniq.8502"
              },
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.8460"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mp.inr",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.8530",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1715",
                "type": "r",
                "id": "_uniq.8517"
              },
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.8460"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.8457",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mp.inr",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.8530",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1715",
                "type": "r",
                "id": "_uniq.8517"
              },
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.8460"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.8457",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
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
        "tacticString": "exact Or.inr ⟨h.left, ‹r›⟩",
        "tacticDependsOn": [
          "_uniq.8460"
        ],
        "goalsBefore": [
          {
            "username": "mp.inr",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.8530",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1715",
                "type": "r",
                "id": "_uniq.8517"
              },
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.8460"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.8457",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.8457",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
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
        "tacticString": "intro h",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.8457",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mpr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8556",
            "hyps": [
              {
                "value": null,
                "username": "h",
                "type": "p ∧ q ∨ p ∧ r",
                "id": "_uniq.8555"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
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
        "tacticString": "cases h",
        "tacticDependsOn": [
          "_uniq.8555"
        ],
        "goalsBefore": [
          {
            "username": "mpr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8556",
            "hyps": [
              {
                "value": null,
                "username": "h",
                "type": "p ∧ q ∨ p ∧ r",
                "id": "_uniq.8555"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mpr.inl",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8600",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1749",
                "type": "p ∧ q",
                "id": "_uniq.8586"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8614",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1751",
                "type": "p ∧ r",
                "id": "_uniq.8601"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
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
        "tacticString": "rename_i hpq",
        "tacticDependsOn": [
          "_uniq.8586"
        ],
        "goalsBefore": [
          {
            "username": "mpr.inl",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8600",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1749",
                "type": "p ∧ q",
                "id": "_uniq.8586"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8614",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1751",
                "type": "p ∧ r",
                "id": "_uniq.8601"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mpr.inl",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8615",
            "hyps": [
              {
                "value": null,
                "username": "hpq",
                "type": "p ∧ q",
                "id": "_uniq.8586"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8614",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1751",
                "type": "p ∧ r",
                "id": "_uniq.8601"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
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
        "tacticString": "exact ⟨hpq.left, Or.inl hpq.right⟩",
        "tacticDependsOn": [
          "_uniq.8586",
          "_uniq.8586"
        ],
        "goalsBefore": [
          {
            "username": "mpr.inl",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8615",
            "hyps": [
              {
                "value": null,
                "username": "hpq",
                "type": "p ∧ q",
                "id": "_uniq.8586"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          },
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8614",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1751",
                "type": "p ∧ r",
                "id": "_uniq.8601"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8614",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1751",
                "type": "p ∧ r",
                "id": "_uniq.8601"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
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
        "tacticString": "rename_i hpr",
        "tacticDependsOn": [
          "_uniq.8601"
        ],
        "goalsBefore": [
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8614",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1751",
                "type": "p ∧ r",
                "id": "_uniq.8601"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8628",
            "hyps": [
              {
                "value": null,
                "username": "hpr",
                "type": "p ∧ r",
                "id": "_uniq.8601"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
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
        "tacticString": "exact ⟨hpr.left, Or.inr hpr.right⟩",
        "tacticDependsOn": [
          "_uniq.8601",
          "_uniq.8601"
        ],
        "goalsBefore": [
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.8628",
            "hyps": [
              {
                "value": null,
                "username": "hpr",
                "type": "p ∧ r",
                "id": "_uniq.8601"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.8447"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.8446"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.8445"
              }
            ]
          }
        ],
        "goalsAfter": []
      }
    }
  }
]

// infinitude of primes, without {}
const infoTreeExample_4 = [
  {
    "tacticApp": {
      "t": {
        "tacticString": "intro N",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "∀ (N : ℕ), ∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.176",
            "hyps": []
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.178",
            "hyps": [
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
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
        "tacticString": "let M := Nat.factorial N + 1",
        "tacticDependsOn": [
          "_uniq.177"
        ],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.178",
            "hyps": [
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
              }
            ]
          }
        ],
        // Ah okay, so the goal id changed, but I didn't put it into my window's goals, so we can't find that window now.
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.239",
            "hyps": [
              {
                "value": "Nat.factorial N + 1",
                "username": "M",
                "type": "ℕ",
                "id": "_uniq.238"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
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
        "tacticString": "let p := Nat.minFac M",
        "tacticDependsOn": [
          "_uniq.238"
        ],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.239",
            "hyps": [
              {
                "value": "Nat.factorial N + 1",
                "username": "M",
                "type": "ℕ",
                "id": "_uniq.238"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.253",
            "hyps": [
              {
                "value": "Nat.minFac M",
                "username": "p",
                "type": "ℕ",
                "id": "_uniq.252"
              },
              {
                "value": "Nat.factorial N + 1",
                "username": "M",
                "type": "ℕ",
                "id": "_uniq.238"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
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
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.253",
            "hyps": [
              {
                "value": "Nat.minFac M",
                "username": "p",
                "type": "ℕ",
                "id": "_uniq.252"
              },
              {
                "value": "Nat.factorial N + 1",
                "username": "M",
                "type": "ℕ",
                "id": "_uniq.238"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
              }
            ]
          }
        ],
        "goalsAfter": []
      }
    }
  }
]

// lets and haves
const infoTreeExample_5 = [
  {
    "tacticApp": {
      "t": {
        "tacticString": "intro N",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "∀ (N : ℕ), ∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.176",
            "hyps": []
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.178",
            "hyps": [
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
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
        "tacticString": "let M := Nat.factorial N + 1",
        "tacticDependsOn": [
          "_uniq.177"
        ],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.178",
            "hyps": [
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.239",
            "hyps": [
              {
                "value": "Nat.factorial N + 1",
                "username": "M",
                "type": "ℕ",
                "id": "_uniq.238"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
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
        "tacticString": "let p := Nat.minFac M",
        "tacticDependsOn": [
          "_uniq.238"
        ],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.239",
            "hyps": [
              {
                "value": "Nat.factorial N + 1",
                "username": "M",
                "type": "ℕ",
                "id": "_uniq.238"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.253",
            "hyps": [
              {
                "value": "Nat.minFac M",
                "username": "p",
                "type": "ℕ",
                "id": "_uniq.252"
              },
              {
                "value": "Nat.factorial N + 1",
                "username": "M",
                "type": "ℕ",
                "id": "_uniq.238"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
              }
            ]
          }
        ]
      }
    }
  },
  {
    "haveDecl": {
      "t": {
        "tacticString": "have pp : Nat.Prime p := by",
        "tacticDependsOn": [
          "_uniq.252",
          "_uniq.177",
          "_uniq.177"
        ],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.253",
            "hyps": [
              {
                "value": "Nat.minFac M",
                "username": "p",
                "type": "ℕ",
                "id": "_uniq.252"
              },
              {
                "value": "Nat.factorial N + 1",
                "username": "M",
                "type": "ℕ",
                "id": "_uniq.238"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.259",
            "hyps": [
              {
                "value": null,
                "username": "pp",
                "type": "Nat.Prime p",
                "id": "_uniq.258"
              },
              {
                "value": "Nat.minFac M",
                "username": "p",
                "type": "ℕ",
                "id": "_uniq.252"
              },
              {
                "value": "Nat.factorial N + 1",
                "username": "M",
                "type": "ℕ",
                "id": "_uniq.238"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
              }
            ]
          }
        ]
      },
      "subSteps": [
        {
          "tacticApp": {
            "t": {
              "tacticString": "apply Nat.minFac_prime",
              "tacticDependsOn": [],
              "goalsBefore": [
                {
                  "username": "[anonymous]",
                  "type": "Nat.Prime p",
                  "id": "_uniq.257",
                  "hyps": [
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ],
              "goalsAfter": [
                {
                  "username": "n1",
                  "type": "M ≠ 1",
                  "id": "_uniq.264",
                  "hyps": [
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ]
            }
          }
        },
        {
          "haveDecl": {
            "t": {
              "tacticString": "have fac_pos: 0 < Nat.factorial N := by",
              "tacticDependsOn": [
                "_uniq.177",
                "_uniq.177"
              ],
              "goalsBefore": [
                {
                  "username": "n1",
                  "type": "M ≠ 1",
                  "id": "_uniq.264",
                  "hyps": [
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ],
              "goalsAfter": [
                {
                  "username": "n1",
                  "type": "M ≠ 1",
                  "id": "_uniq.301",
                  "hyps": [
                    {
                      "value": null,
                      "username": "fac_pos",
                      "type": "0 < Nat.factorial N",
                      "id": "_uniq.300"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ]
            },
            "subSteps": [
              {
                "tacticApp": {
                  "t": {
                    "tacticString": "exact Nat.factorial_pos N",
                    "tacticDependsOn": [
                      "_uniq.177"
                    ],
                    "goalsBefore": [
                      {
                        "username": "[anonymous]",
                        "type": "0 < Nat.factorial N",
                        "id": "_uniq.299",
                        "hyps": [
                          {
                            "value": "Nat.minFac M",
                            "username": "p",
                            "type": "ℕ",
                            "id": "_uniq.252"
                          },
                          {
                            "value": "Nat.factorial N + 1",
                            "username": "M",
                            "type": "ℕ",
                            "id": "_uniq.238"
                          },
                          {
                            "value": null,
                            "username": "N",
                            "type": "ℕ",
                            "id": "_uniq.177"
                          }
                        ]
                      }
                    ],
                    "goalsAfter": []
                  }
                }
              }
            ],
            "initialGoal": "0 < Nat.factorial N"
          }
        },
        {
          "tacticApp": {
            "t": {
              "tacticString": "linarith",
              "tacticDependsOn": [],
              "goalsBefore": [
                {
                  "username": "n1",
                  "type": "M ≠ 1",
                  "id": "_uniq.301",
                  "hyps": [
                    {
                      "value": null,
                      "username": "fac_pos",
                      "type": "0 < Nat.factorial N",
                      "id": "_uniq.300"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ],
              "goalsAfter": []
            }
          }
        }
      ],
      "initialGoal": "Nat.Prime p"
    }
  },
  {
    "haveDecl": {
      "t": {
        "tacticString": "have ppos: p ≥ N := by",
        "tacticDependsOn": [
          "_uniq.252",
          "_uniq.177",
          "_uniq.252",
          "_uniq.177",
          "_uniq.258",
          "_uniq.252",
          "_uniq.177",
          "_uniq.238",
          "_uniq.252",
          "_uniq.258"
        ],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.259",
            "hyps": [
              {
                "value": null,
                "username": "pp",
                "type": "Nat.Prime p",
                "id": "_uniq.258"
              },
              {
                "value": "Nat.minFac M",
                "username": "p",
                "type": "ℕ",
                "id": "_uniq.252"
              },
              {
                "value": "Nat.factorial N + 1",
                "username": "M",
                "type": "ℕ",
                "id": "_uniq.238"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.1792",
            "hyps": [
              {
                "value": null,
                "username": "ppos",
                "type": "p ≥ N",
                "id": "_uniq.1791"
              },
              {
                "value": null,
                "username": "pp",
                "type": "Nat.Prime p",
                "id": "_uniq.258"
              },
              {
                "value": "Nat.minFac M",
                "username": "p",
                "type": "ℕ",
                "id": "_uniq.252"
              },
              {
                "value": "Nat.factorial N + 1",
                "username": "M",
                "type": "ℕ",
                "id": "_uniq.238"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
              }
            ]
          }
        ]
      },
      "subSteps": [
        {
          "tacticApp": {
            "t": {
              "tacticString": "apply by_contradiction",
              "tacticDependsOn": [],
              "goalsBefore": [
                {
                  "username": "[anonymous]",
                  "type": "p ≥ N",
                  "id": "_uniq.1790",
                  "hyps": [
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime p",
                      "id": "_uniq.258"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ],
              "goalsAfter": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "¬p ≥ N → False",
                  "id": "_uniq.1797",
                  "hyps": [
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime p",
                      "id": "_uniq.258"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
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
              "tacticString": "intro pln",
              "tacticDependsOn": [],
              "goalsBefore": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "¬p ≥ N → False",
                  "id": "_uniq.1797",
                  "hyps": [
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime p",
                      "id": "_uniq.258"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ],
              "goalsAfter": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "False",
                  "id": "_uniq.1799",
                  "hyps": [
                    {
                      "value": null,
                      "username": "pln",
                      "type": "¬p ≥ N",
                      "id": "_uniq.1798"
                    },
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime p",
                      "id": "_uniq.258"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ]
            }
          }
        },
        {
          "haveDecl": {
            "t": {
              "tacticString": "have h₁ : p ∣ Nat.factorial N := by",
              "tacticDependsOn": [
                "_uniq.252",
                "_uniq.177",
                "_uniq.258",
                "_uniq.1798"
              ],
              "goalsBefore": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "False",
                  "id": "_uniq.1799",
                  "hyps": [
                    {
                      "value": null,
                      "username": "pln",
                      "type": "¬p ≥ N",
                      "id": "_uniq.1798"
                    },
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime p",
                      "id": "_uniq.258"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ],
              "goalsAfter": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "False",
                  "id": "_uniq.1813",
                  "hyps": [
                    {
                      "value": null,
                      "username": "h₁",
                      "type": "p ∣ Nat.factorial N",
                      "id": "_uniq.1812"
                    },
                    {
                      "value": null,
                      "username": "pln",
                      "type": "¬p ≥ N",
                      "id": "_uniq.1798"
                    },
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime p",
                      "id": "_uniq.258"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ]
            },
            "subSteps": [
              {
                "tacticApp": {
                  "t": {
                    "tacticString": "apply pp.dvd_factorial.mpr",
                    "tacticDependsOn": [
                      "_uniq.258"
                    ],
                    "goalsBefore": [
                      {
                        "username": "[anonymous]",
                        "type": "p ∣ Nat.factorial N",
                        "id": "_uniq.1811",
                        "hyps": [
                          {
                            "value": null,
                            "username": "pln",
                            "type": "¬p ≥ N",
                            "id": "_uniq.1798"
                          },
                          {
                            "value": null,
                            "username": "pp",
                            "type": "Nat.Prime p",
                            "id": "_uniq.258"
                          },
                          {
                            "value": "Nat.minFac M",
                            "username": "p",
                            "type": "ℕ",
                            "id": "_uniq.252"
                          },
                          {
                            "value": "Nat.factorial N + 1",
                            "username": "M",
                            "type": "ℕ",
                            "id": "_uniq.238"
                          },
                          {
                            "value": null,
                            "username": "N",
                            "type": "ℕ",
                            "id": "_uniq.177"
                          }
                        ]
                      }
                    ],
                    "goalsAfter": [
                      {
                        "username": "[anonymous]",
                        "type": "p ≤ N",
                        "id": "_uniq.1822",
                        "hyps": [
                          {
                            "value": null,
                            "username": "pln",
                            "type": "¬p ≥ N",
                            "id": "_uniq.1798"
                          },
                          {
                            "value": null,
                            "username": "pp",
                            "type": "Nat.Prime p",
                            "id": "_uniq.258"
                          },
                          {
                            "value": "Nat.minFac M",
                            "username": "p",
                            "type": "ℕ",
                            "id": "_uniq.252"
                          },
                          {
                            "value": "Nat.factorial N + 1",
                            "username": "M",
                            "type": "ℕ",
                            "id": "_uniq.238"
                          },
                          {
                            "value": null,
                            "username": "N",
                            "type": "ℕ",
                            "id": "_uniq.177"
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
                    "tacticString": "exact le_of_not_ge pln",
                    "tacticDependsOn": [
                      "_uniq.1798"
                    ],
                    "goalsBefore": [
                      {
                        "username": "[anonymous]",
                        "type": "p ≤ N",
                        "id": "_uniq.1822",
                        "hyps": [
                          {
                            "value": null,
                            "username": "pln",
                            "type": "¬p ≥ N",
                            "id": "_uniq.1798"
                          },
                          {
                            "value": null,
                            "username": "pp",
                            "type": "Nat.Prime p",
                            "id": "_uniq.258"
                          },
                          {
                            "value": "Nat.minFac M",
                            "username": "p",
                            "type": "ℕ",
                            "id": "_uniq.252"
                          },
                          {
                            "value": "Nat.factorial N + 1",
                            "username": "M",
                            "type": "ℕ",
                            "id": "_uniq.238"
                          },
                          {
                            "value": null,
                            "username": "N",
                            "type": "ℕ",
                            "id": "_uniq.177"
                          }
                        ]
                      }
                    ],
                    "goalsAfter": []
                  }
                }
              }
            ],
            "initialGoal": "p ∣ Nat.factorial N"
          }
        },
        {
          "tacticApp": {
            "t": {
              "tacticString": "have h₂ : p ∣ Nat.factorial N + 1 := Nat.minFac_dvd M",
              "tacticDependsOn": [
                "_uniq.252",
                "_uniq.177",
                "_uniq.238"
              ],
              "goalsBefore": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "False",
                  "id": "_uniq.1813",
                  "hyps": [
                    {
                      "value": null,
                      "username": "h₁",
                      "type": "p ∣ Nat.factorial N",
                      "id": "_uniq.1812"
                    },
                    {
                      "value": null,
                      "username": "pln",
                      "type": "¬p ≥ N",
                      "id": "_uniq.1798"
                    },
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime p",
                      "id": "_uniq.258"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ],
              "goalsAfter": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "False",
                  "id": "_uniq.1944",
                  "hyps": [
                    {
                      "value": null,
                      "username": "h₂",
                      "type": "p ∣ Nat.factorial N + 1",
                      "id": "_uniq.1943"
                    },
                    {
                      "value": null,
                      "username": "h₁",
                      "type": "p ∣ Nat.factorial N",
                      "id": "_uniq.1812"
                    },
                    {
                      "value": null,
                      "username": "pln",
                      "type": "¬p ≥ N",
                      "id": "_uniq.1798"
                    },
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime p",
                      "id": "_uniq.258"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
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
              "tacticString": "have h : p ∣ 1 := (Nat.dvd_add_right h₁).mp $ h₂",
              "tacticDependsOn": [
                "_uniq.252",
                "_uniq.1812",
                "_uniq.1943"
              ],
              "goalsBefore": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "False",
                  "id": "_uniq.1944",
                  "hyps": [
                    {
                      "value": null,
                      "username": "h₂",
                      "type": "p ∣ Nat.factorial N + 1",
                      "id": "_uniq.1943"
                    },
                    {
                      "value": null,
                      "username": "h₁",
                      "type": "p ∣ Nat.factorial N",
                      "id": "_uniq.1812"
                    },
                    {
                      "value": null,
                      "username": "pln",
                      "type": "¬p ≥ N",
                      "id": "_uniq.1798"
                    },
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime p",
                      "id": "_uniq.258"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ],
              "goalsAfter": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "False",
                  "id": "_uniq.1969",
                  "hyps": [
                    {
                      "value": null,
                      "username": "h",
                      "type": "p ∣ 1",
                      "id": "_uniq.1968"
                    },
                    {
                      "value": null,
                      "username": "h₂",
                      "type": "p ∣ Nat.factorial N + 1",
                      "id": "_uniq.1943"
                    },
                    {
                      "value": null,
                      "username": "h₁",
                      "type": "p ∣ Nat.factorial N",
                      "id": "_uniq.1812"
                    },
                    {
                      "value": null,
                      "username": "pln",
                      "type": "¬p ≥ N",
                      "id": "_uniq.1798"
                    },
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime p",
                      "id": "_uniq.258"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
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
              "tacticString": "exact Nat.Prime.not_dvd_one pp h",
              "tacticDependsOn": [
                "_uniq.258",
                "_uniq.1968"
              ],
              "goalsBefore": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "False",
                  "id": "_uniq.1969",
                  "hyps": [
                    {
                      "value": null,
                      "username": "h",
                      "type": "p ∣ 1",
                      "id": "_uniq.1968"
                    },
                    {
                      "value": null,
                      "username": "h₂",
                      "type": "p ∣ Nat.factorial N + 1",
                      "id": "_uniq.1943"
                    },
                    {
                      "value": null,
                      "username": "h₁",
                      "type": "p ∣ Nat.factorial N",
                      "id": "_uniq.1812"
                    },
                    {
                      "value": null,
                      "username": "pln",
                      "type": "¬p ≥ N",
                      "id": "_uniq.1798"
                    },
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime p",
                      "id": "_uniq.258"
                    },
                    {
                      "value": "Nat.minFac M",
                      "username": "p",
                      "type": "ℕ",
                      "id": "_uniq.252"
                    },
                    {
                      "value": "Nat.factorial N + 1",
                      "username": "M",
                      "type": "ℕ",
                      "id": "_uniq.238"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.177"
                    }
                  ]
                }
              ],
              "goalsAfter": []
            }
          }
        }
      ],
      "initialGoal": "p ≥ N"
    }
  },
  {
    "tacticApp": {
      "t": {
        "tacticString": "exact ⟨ p, ppos, pp ⟩",
        "tacticDependsOn": [
          "_uniq.252",
          "_uniq.1791",
          "_uniq.258"
        ],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.1792",
            "hyps": [
              {
                "value": null,
                "username": "ppos",
                "type": "p ≥ N",
                "id": "_uniq.1791"
              },
              {
                "value": null,
                "username": "pp",
                "type": "Nat.Prime p",
                "id": "_uniq.258"
              },
              {
                "value": "Nat.minFac M",
                "username": "p",
                "type": "ℕ",
                "id": "_uniq.252"
              },
              {
                "value": "Nat.factorial N + 1",
                "username": "M",
                "type": "ℕ",
                "id": "_uniq.238"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.177"
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
