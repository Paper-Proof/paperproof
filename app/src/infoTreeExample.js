// works
const infoTreeExample_1 = [
  {
    "tacticApp": {
      "t": {
        "tacticString": "intro hello",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "(P → R) → (Q → S) → P ∨ Q → R ∨ S",
            "id": "_uniq.8293",
            "hyps": [
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "(Q → S) → P ∨ Q → R ∨ S",
            "id": "_uniq.8296",
            "hyps": [
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
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
        "tacticString": "intro hi",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "(Q → S) → P ∨ Q → R ∨ S",
            "id": "_uniq.8296",
            "hyps": [
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "P ∨ Q → R ∨ S",
            "id": "_uniq.8299",
            "hyps": [
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
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
        "tacticString": "intro aaa",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "P ∨ Q → R ∨ S",
            "id": "_uniq.8299",
            "hyps": [
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "R ∨ S",
            "id": "_uniq.8302",
            "hyps": [
              {
                "value": null,
                "username": "aaa",
                "type": "P ∨ Q",
                "id": "_uniq.8301"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
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
        "tacticString": "cases aaa",
        "tacticDependsOn": [
          "_uniq.8301"
        ],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "R ∨ S",
            "id": "_uniq.8302",
            "hyps": [
              {
                "value": null,
                "username": "aaa",
                "type": "P ∨ Q",
                "id": "_uniq.8301"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "inl",
            "type": "R ∨ S",
            "id": "_uniq.8348",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1038",
                "type": "P",
                "id": "_uniq.8334"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          },
          {
            "username": "inr",
            "type": "R ∨ S",
            "id": "_uniq.8362",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1040",
                "type": "Q",
                "id": "_uniq.8349"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
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
        "tacticString": "left",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "inl",
            "type": "R ∨ S",
            "id": "_uniq.8348",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1038",
                "type": "P",
                "id": "_uniq.8334"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          },
          {
            "username": "inr",
            "type": "R ∨ S",
            "id": "_uniq.8362",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1040",
                "type": "Q",
                "id": "_uniq.8349"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "inl.h",
            "type": "R",
            "id": "_uniq.8368",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1038",
                "type": "P",
                "id": "_uniq.8334"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          },
          {
            "username": "inr",
            "type": "R ∨ S",
            "id": "_uniq.8362",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1040",
                "type": "Q",
                "id": "_uniq.8349"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
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
        "tacticString": "apply hello",
        "tacticDependsOn": [
          "_uniq.8295"
        ],
        "goalsBefore": [
          {
            "username": "inl.h",
            "type": "R",
            "id": "_uniq.8368",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1038",
                "type": "P",
                "id": "_uniq.8334"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          },
          {
            "username": "inr",
            "type": "R ∨ S",
            "id": "_uniq.8362",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1040",
                "type": "Q",
                "id": "_uniq.8349"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "inl.h",
            "type": "P",
            "id": "_uniq.8370",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1038",
                "type": "P",
                "id": "_uniq.8334"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          },
          {
            "username": "inr",
            "type": "R ∨ S",
            "id": "_uniq.8362",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1040",
                "type": "Q",
                "id": "_uniq.8349"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
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
        "tacticString": "assumption",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "inl.h",
            "type": "P",
            "id": "_uniq.8370",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1038",
                "type": "P",
                "id": "_uniq.8334"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          },
          {
            "username": "inr",
            "type": "R ∨ S",
            "id": "_uniq.8362",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1040",
                "type": "Q",
                "id": "_uniq.8349"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "inr",
            "type": "R ∨ S",
            "id": "_uniq.8362",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1040",
                "type": "Q",
                "id": "_uniq.8349"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
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
        "tacticString": "right",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "inr",
            "type": "R ∨ S",
            "id": "_uniq.8362",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1040",
                "type": "Q",
                "id": "_uniq.8349"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "inr.h",
            "type": "S",
            "id": "_uniq.8376",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1040",
                "type": "Q",
                "id": "_uniq.8349"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
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
        "tacticString": "apply hi",
        "tacticDependsOn": [
          "_uniq.8298"
        ],
        "goalsBefore": [
          {
            "username": "inr.h",
            "type": "S",
            "id": "_uniq.8376",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1040",
                "type": "Q",
                "id": "_uniq.8349"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "inr.h",
            "type": "Q",
            "id": "_uniq.8378",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1040",
                "type": "Q",
                "id": "_uniq.8349"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
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
        "tacticString": "assumption",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "inr.h",
            "type": "Q",
            "id": "_uniq.8378",
            "hyps": [
              {
                "value": null,
                "username": "h._@.PaperProof._hyg.1040",
                "type": "Q",
                "id": "_uniq.8349"
              },
              {
                "value": null,
                "username": "hi",
                "type": "Q → S",
                "id": "_uniq.8298"
              },
              {
                "value": null,
                "username": "hello",
                "type": "P → R",
                "id": "_uniq.8295"
              },
              {
                "value": null,
                "username": "S",
                "type": "Prop",
                "id": "_uniq.8292"
              },
              {
                "value": null,
                "username": "Q",
                "type": "Prop",
                "id": "_uniq.8291"
              },
              {
                "value": null,
                "username": "R",
                "type": "Prop",
                "id": "_uniq.8290"
              },
              {
                "value": null,
                "username": "P",
                "type": "Prop",
                "id": "_uniq.8289"
              }
            ]
          }
        ],
        "goalsAfter": []
      }
    }
  }
]

// works
const infoTreeExample_2 = [
  {
    "tacticApp": {
      "t": {
        "tacticString": "ext x",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "s ∩ t = t ∩ s",
            "id": "_uniq.13418",
            "hyps": [
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "h",
            "type": "x ∈ s ∩ t ↔ x ∈ t ∩ s",
            "id": "_uniq.13443",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
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
        "tacticString": "apply Iff.intro",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "h",
            "type": "x ∈ s ∩ t ↔ x ∈ t ∩ s",
            "id": "_uniq.13443",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "h.mp",
            "type": "x ∈ s ∩ t → x ∈ t ∩ s",
            "id": "_uniq.13451",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          },
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s → x ∈ s ∩ t",
            "id": "_uniq.13452",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
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
        "tacticString": "intro h1",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "h.mp",
            "type": "x ∈ s ∩ t → x ∈ t ∩ s",
            "id": "_uniq.13451",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          },
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s → x ∈ s ∩ t",
            "id": "_uniq.13452",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "h.mp",
            "type": "x ∈ t ∩ s",
            "id": "_uniq.13456",
            "hyps": [
              {
                "value": null,
                "username": "h1",
                "type": "x ∈ s ∩ t",
                "id": "_uniq.13455"
              },
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          },
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s → x ∈ s ∩ t",
            "id": "_uniq.13452",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
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
        "tacticString": "rw Set.inter_comm",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "h.mp",
            "type": "x ∈ t ∩ s",
            "id": "_uniq.13456",
            "hyps": [
              {
                "value": null,
                "username": "h1",
                "type": "x ∈ s ∩ t",
                "id": "_uniq.13455"
              },
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          },
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s → x ∈ s ∩ t",
            "id": "_uniq.13452",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "h.mp",
            "type": "x ∈ s ∩ t",
            "id": "_uniq.13473",
            "hyps": [
              {
                "value": null,
                "username": "h1",
                "type": "x ∈ s ∩ t",
                "id": "_uniq.13455"
              },
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          },
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s → x ∈ s ∩ t",
            "id": "_uniq.13452",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
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
            "username": "h.mp",
            "type": "x ∈ s ∩ t",
            "id": "_uniq.13473",
            "hyps": [
              {
                "value": null,
                "username": "h1",
                "type": "x ∈ s ∩ t",
                "id": "_uniq.13455"
              },
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          },
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s → x ∈ s ∩ t",
            "id": "_uniq.13452",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "h.mp",
            "type": "x ∈ s ∩ t",
            "id": "_uniq.13473",
            "hyps": [
              {
                "value": null,
                "username": "h1",
                "type": "x ∈ s ∩ t",
                "id": "_uniq.13455"
              },
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          },
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s → x ∈ s ∩ t",
            "id": "_uniq.13452",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
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
        "tacticString": "exact h1",
        "tacticDependsOn": [
          "_uniq.13455"
        ],
        "goalsBefore": [
          {
            "username": "h.mp",
            "type": "x ∈ s ∩ t",
            "id": "_uniq.13473",
            "hyps": [
              {
                "value": null,
                "username": "h1",
                "type": "x ∈ s ∩ t",
                "id": "_uniq.13455"
              },
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          },
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s → x ∈ s ∩ t",
            "id": "_uniq.13452",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s → x ∈ s ∩ t",
            "id": "_uniq.13452",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
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
        "tacticString": "intro h1",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s → x ∈ s ∩ t",
            "id": "_uniq.13452",
            "hyps": [
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "h.mpr",
            "type": "x ∈ s ∩ t",
            "id": "_uniq.13479",
            "hyps": [
              {
                "value": null,
                "username": "h1",
                "type": "x ∈ t ∩ s",
                "id": "_uniq.13478"
              },
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
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
        "tacticString": "rw Set.inter_comm",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "h.mpr",
            "type": "x ∈ s ∩ t",
            "id": "_uniq.13479",
            "hyps": [
              {
                "value": null,
                "username": "h1",
                "type": "x ∈ t ∩ s",
                "id": "_uniq.13478"
              },
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s",
            "id": "_uniq.13490",
            "hyps": [
              {
                "value": null,
                "username": "h1",
                "type": "x ∈ t ∩ s",
                "id": "_uniq.13478"
              },
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
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
            "username": "h.mpr",
            "type": "x ∈ t ∩ s",
            "id": "_uniq.13490",
            "hyps": [
              {
                "value": null,
                "username": "h1",
                "type": "x ∈ t ∩ s",
                "id": "_uniq.13478"
              },
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s",
            "id": "_uniq.13490",
            "hyps": [
              {
                "value": null,
                "username": "h1",
                "type": "x ∈ t ∩ s",
                "id": "_uniq.13478"
              },
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
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
        "tacticString": "exact h1",
        "tacticDependsOn": [
          "_uniq.13478"
        ],
        "goalsBefore": [
          {
            "username": "h.mpr",
            "type": "x ∈ t ∩ s",
            "id": "_uniq.13490",
            "hyps": [
              {
                "value": null,
                "username": "h1",
                "type": "x ∈ t ∩ s",
                "id": "_uniq.13478"
              },
              {
                "value": null,
                "username": "x",
                "type": "ℕ",
                "id": "_uniq.13442"
              },
              {
                "value": null,
                "username": "t",
                "type": "Set ℕ",
                "id": "_uniq.13417"
              },
              {
                "value": null,
                "username": "s",
                "type": "Set ℕ",
                "id": "_uniq.13416"
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
const infoTreeExample_3 = [
  {
    "tacticApp": {
      "t": {
        "tacticString": "apply Iff.intro",
        "tacticDependsOn": [],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r",
            "id": "_uniq.14333",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mp",
            "type": "p ∧ (q ∨ r) → p ∧ q ∨ p ∧ r",
            "id": "_uniq.14341",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.14342",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
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
            "id": "_uniq.14341",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.14342",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mp",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.14346",
            "hyps": [
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.14345"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.14342",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
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
          "_uniq.14345"
        ],
        "goalsBefore": [
          {
            "username": "mp",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.14346",
            "hyps": [
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.14345"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.14342",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mp.inl",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.14401",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1786",
                "type": "q",
                "id": "_uniq.14387"
              },
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.14345"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mp.inr",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.14415",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1788",
                "type": "r",
                "id": "_uniq.14402"
              },
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.14345"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.14342",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
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
          "_uniq.14345"
        ],
        "goalsBefore": [
          {
            "username": "mp.inl",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.14401",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1786",
                "type": "q",
                "id": "_uniq.14387"
              },
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.14345"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mp.inr",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.14415",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1788",
                "type": "r",
                "id": "_uniq.14402"
              },
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.14345"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.14342",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mp.inr",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.14415",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1788",
                "type": "r",
                "id": "_uniq.14402"
              },
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.14345"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.14342",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
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
          "_uniq.14345"
        ],
        "goalsBefore": [
          {
            "username": "mp.inr",
            "type": "p ∧ q ∨ p ∧ r",
            "id": "_uniq.14415",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1788",
                "type": "r",
                "id": "_uniq.14402"
              },
              {
                "value": null,
                "username": "h",
                "type": "p ∧ (q ∨ r)",
                "id": "_uniq.14345"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.14342",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mpr",
            "type": "p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)",
            "id": "_uniq.14342",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
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
            "id": "_uniq.14342",
            "hyps": [
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mpr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14441",
            "hyps": [
              {
                "value": null,
                "username": "h",
                "type": "p ∧ q ∨ p ∧ r",
                "id": "_uniq.14440"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
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
          "_uniq.14440"
        ],
        "goalsBefore": [
          {
            "username": "mpr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14441",
            "hyps": [
              {
                "value": null,
                "username": "h",
                "type": "p ∧ q ∨ p ∧ r",
                "id": "_uniq.14440"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mpr.inl",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14485",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1822",
                "type": "p ∧ q",
                "id": "_uniq.14471"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14499",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1824",
                "type": "p ∧ r",
                "id": "_uniq.14486"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
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
          "_uniq.14471"
        ],
        "goalsBefore": [
          {
            "username": "mpr.inl",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14485",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1822",
                "type": "p ∧ q",
                "id": "_uniq.14471"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14499",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1824",
                "type": "p ∧ r",
                "id": "_uniq.14486"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mpr.inl",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14500",
            "hyps": [
              {
                "value": null,
                "username": "hpq",
                "type": "p ∧ q",
                "id": "_uniq.14471"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14499",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1824",
                "type": "p ∧ r",
                "id": "_uniq.14486"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
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
          "_uniq.14471",
          "_uniq.14471"
        ],
        "goalsBefore": [
          {
            "username": "mpr.inl",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14500",
            "hyps": [
              {
                "value": null,
                "username": "hpq",
                "type": "p ∧ q",
                "id": "_uniq.14471"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          },
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14499",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1824",
                "type": "p ∧ r",
                "id": "_uniq.14486"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14499",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1824",
                "type": "p ∧ r",
                "id": "_uniq.14486"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
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
          "_uniq.14486"
        ],
        "goalsBefore": [
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14499",
            "hyps": [
              {
                "value": null,
                "username": "h._@.Examples._hyg.1824",
                "type": "p ∧ r",
                "id": "_uniq.14486"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          }
        ],
        "goalsAfter": [
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14513",
            "hyps": [
              {
                "value": null,
                "username": "hpr",
                "type": "p ∧ r",
                "id": "_uniq.14486"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
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
          "_uniq.14486",
          "_uniq.14486"
        ],
        "goalsBefore": [
          {
            "username": "mpr.inr",
            "type": "p ∧ (q ∨ r)",
            "id": "_uniq.14513",
            "hyps": [
              {
                "value": null,
                "username": "hpr",
                "type": "p ∧ r",
                "id": "_uniq.14486"
              },
              {
                "value": null,
                "username": "r",
                "type": "Prop",
                "id": "_uniq.14332"
              },
              {
                "value": null,
                "username": "q",
                "type": "Prop",
                "id": "_uniq.14331"
              },
              {
                "value": null,
                "username": "p",
                "type": "Prop",
                "id": "_uniq.14330"
              }
            ]
          }
        ],
        "goalsAfter": []
      }
    }
  }
]

const infoTreeExample_4 = [
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

// infinitude of primes, except without lets and {} for now.
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
            "id": "_uniq.296",
            "hyps": []
          }
        ],
        "goalsAfter": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.298",
            "hyps": [
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.297"
              }
            ]
          }
        ]
      }
    }
  },
  {
    "haveDecl": {
      "subSteps": [
        {
          "tacticApp": {
            "t": {
              "tacticString": "apply Nat.minFac_prime",
              "tacticDependsOn": [],
              "goalsBefore": [
                {
                  "username": "[anonymous]",
                  "type": "Nat.Prime (Nat.minFac (Nat.factorial N + 1))",
                  "id": "_uniq.357",
                  "hyps": [
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.297"
                    }
                  ]
                }
              ],
              "goalsAfter": [
                {
                  "username": "n1",
                  "type": "Nat.factorial N + 1 ≠ 1",
                  "id": "_uniq.372",
                  "hyps": [
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.297"
                    }
                  ]
                }
              ]
            }
          }
        },
        {
          "haveDecl": {
            "subSteps": [
              {
                "tacticApp": {
                  "t": {
                    "tacticString": "exact Nat.factorial_pos N",
                    "tacticDependsOn": [
                      "_uniq.297"
                    ],
                    "goalsBefore": [
                      {
                        "username": "[anonymous]",
                        "type": "0 < Nat.factorial N",
                        "id": "_uniq.407",
                        "hyps": [
                          {
                            "value": null,
                            "username": "N",
                            "type": "ℕ",
                            "id": "_uniq.297"
                          }
                        ]
                      }
                    ],
                    "goalsAfter": []
                  }
                }
              }
            ],
            "name": "have fac_pos: 0 < Nat.factorial N"
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
                  "type": "Nat.factorial N + 1 ≠ 1",
                  "id": "_uniq.409",
                  "hyps": [
                    {
                      "value": null,
                      "username": "fac_pos",
                      "type": "0 < Nat.factorial N",
                      "id": "_uniq.408"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.297"
                    }
                  ]
                }
              ],
              "goalsAfter": []
            }
          }
        }
      ],
      "name": "have pp : Nat.Prime (Nat.minFac (Nat.factorial N + 1))"
    }
  },
  {
    "haveDecl": {
      "subSteps": [
        {
          "tacticApp": {
            "t": {
              "tacticString": "apply by_contradiction",
              "tacticDependsOn": [],
              "goalsBefore": [
                {
                  "username": "[anonymous]",
                  "type": "Nat.minFac (Nat.factorial N + 1) ≥ N",
                  "id": "_uniq.3593",
                  "hyps": [
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime (Nat.minFac (Nat.factorial N + 1))",
                      "id": "_uniq.358"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.297"
                    }
                  ]
                }
              ],
              "goalsAfter": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "¬Nat.minFac (Nat.factorial N + 1) ≥ N → False",
                  "id": "_uniq.3600",
                  "hyps": [
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime (Nat.minFac (Nat.factorial N + 1))",
                      "id": "_uniq.358"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.297"
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
                  "type": "¬Nat.minFac (Nat.factorial N + 1) ≥ N → False",
                  "id": "_uniq.3600",
                  "hyps": [
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime (Nat.minFac (Nat.factorial N + 1))",
                      "id": "_uniq.358"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.297"
                    }
                  ]
                }
              ],
              "goalsAfter": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "False",
                  "id": "_uniq.3602",
                  "hyps": [
                    {
                      "value": null,
                      "username": "pln",
                      "type": "¬Nat.minFac (Nat.factorial N + 1) ≥ N",
                      "id": "_uniq.3601"
                    },
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime (Nat.minFac (Nat.factorial N + 1))",
                      "id": "_uniq.358"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.297"
                    }
                  ]
                }
              ]
            }
          }
        },
        {
          "haveDecl": {
            "subSteps": [
              {
                "tacticApp": {
                  "t": {
                    "tacticString": "apply pp.dvd_factorial.mpr",
                    "tacticDependsOn": [
                      "_uniq.358"
                    ],
                    "goalsBefore": [
                      {
                        "username": "[anonymous]",
                        "type": "Nat.minFac (Nat.factorial N + 1) ∣ Nat.factorial N",
                        "id": "_uniq.3654",
                        "hyps": [
                          {
                            "value": null,
                            "username": "pln",
                            "type": "¬Nat.minFac (Nat.factorial N + 1) ≥ N",
                            "id": "_uniq.3601"
                          },
                          {
                            "value": null,
                            "username": "pp",
                            "type": "Nat.Prime (Nat.minFac (Nat.factorial N + 1))",
                            "id": "_uniq.358"
                          },
                          {
                            "value": null,
                            "username": "N",
                            "type": "ℕ",
                            "id": "_uniq.297"
                          }
                        ]
                      }
                    ],
                    "goalsAfter": [
                      {
                        "username": "[anonymous]",
                        "type": "Nat.minFac (Nat.factorial N + 1) ≤ N",
                        "id": "_uniq.3665",
                        "hyps": [
                          {
                            "value": null,
                            "username": "pln",
                            "type": "¬Nat.minFac (Nat.factorial N + 1) ≥ N",
                            "id": "_uniq.3601"
                          },
                          {
                            "value": null,
                            "username": "pp",
                            "type": "Nat.Prime (Nat.minFac (Nat.factorial N + 1))",
                            "id": "_uniq.358"
                          },
                          {
                            "value": null,
                            "username": "N",
                            "type": "ℕ",
                            "id": "_uniq.297"
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
                      "_uniq.3601"
                    ],
                    "goalsBefore": [
                      {
                        "username": "[anonymous]",
                        "type": "Nat.minFac (Nat.factorial N + 1) ≤ N",
                        "id": "_uniq.3665",
                        "hyps": [
                          {
                            "value": null,
                            "username": "pln",
                            "type": "¬Nat.minFac (Nat.factorial N + 1) ≥ N",
                            "id": "_uniq.3601"
                          },
                          {
                            "value": null,
                            "username": "pp",
                            "type": "Nat.Prime (Nat.minFac (Nat.factorial N + 1))",
                            "id": "_uniq.358"
                          },
                          {
                            "value": null,
                            "username": "N",
                            "type": "ℕ",
                            "id": "_uniq.297"
                          }
                        ]
                      }
                    ],
                    "goalsAfter": []
                  }
                }
              }
            ],
            "name": "have h₁ : (Nat.minFac (Nat.factorial N + 1)) ∣ Nat.factorial N"
          }
        },
        {
          "haveDecl": {
            "subSteps": [
              {
                "tacticApp": {
                  "t": {
                    "tacticString": "exact Nat.minFac_dvd (Nat.factorial N + 1)",
                    "tacticDependsOn": [
                      "_uniq.297"
                    ],
                    "goalsBefore": [
                      {
                        "username": "[anonymous]",
                        "type": "Nat.minFac (Nat.factorial N + 1) ∣ Nat.factorial N + 1",
                        "id": "_uniq.3838",
                        "hyps": [
                          {
                            "value": null,
                            "username": "h₁",
                            "type": "Nat.minFac (Nat.factorial N + 1) ∣ Nat.factorial N",
                            "id": "_uniq.3655"
                          },
                          {
                            "value": null,
                            "username": "pln",
                            "type": "¬Nat.minFac (Nat.factorial N + 1) ≥ N",
                            "id": "_uniq.3601"
                          },
                          {
                            "value": null,
                            "username": "pp",
                            "type": "Nat.Prime (Nat.minFac (Nat.factorial N + 1))",
                            "id": "_uniq.358"
                          },
                          {
                            "value": null,
                            "username": "N",
                            "type": "ℕ",
                            "id": "_uniq.297"
                          }
                        ]
                      }
                    ],
                    "goalsAfter": []
                  }
                }
              }
            ],
            "name": "have h₂ : (Nat.minFac (Nat.factorial N + 1)) ∣ Nat.factorial N + 1"
          }
        },
        {
          "haveDecl": {
            "subSteps": [
              {
                "tacticApp": {
                  "t": {
                    "tacticString": "exact (Nat.dvd_add_right h₁).mp $ h₂",
                    "tacticDependsOn": [
                      "_uniq.3655",
                      "_uniq.3839"
                    ],
                    "goalsBefore": [
                      {
                        "username": "[anonymous]",
                        "type": "Nat.minFac (Nat.factorial N + 1) ∣ 1",
                        "id": "_uniq.3940",
                        "hyps": [
                          {
                            "value": null,
                            "username": "h₂",
                            "type": "Nat.minFac (Nat.factorial N + 1) ∣ Nat.factorial N + 1",
                            "id": "_uniq.3839"
                          },
                          {
                            "value": null,
                            "username": "h₁",
                            "type": "Nat.minFac (Nat.factorial N + 1) ∣ Nat.factorial N",
                            "id": "_uniq.3655"
                          },
                          {
                            "value": null,
                            "username": "pln",
                            "type": "¬Nat.minFac (Nat.factorial N + 1) ≥ N",
                            "id": "_uniq.3601"
                          },
                          {
                            "value": null,
                            "username": "pp",
                            "type": "Nat.Prime (Nat.minFac (Nat.factorial N + 1))",
                            "id": "_uniq.358"
                          },
                          {
                            "value": null,
                            "username": "N",
                            "type": "ℕ",
                            "id": "_uniq.297"
                          }
                        ]
                      }
                    ],
                    "goalsAfter": []
                  }
                }
              }
            ],
            "name": "have h : (Nat.minFac (Nat.factorial N + 1)) ∣ 1"
          }
        },
        {
          "tacticApp": {
            "t": {
              "tacticString": "exact Nat.Prime.not_dvd_one pp h",
              "tacticDependsOn": [
                "_uniq.358",
                "_uniq.3941"
              ],
              "goalsBefore": [
                {
                  "username": "a._@.Mathlib.Logic.Basic._hyg.1241",
                  "type": "False",
                  "id": "_uniq.3942",
                  "hyps": [
                    {
                      "value": null,
                      "username": "h",
                      "type": "Nat.minFac (Nat.factorial N + 1) ∣ 1",
                      "id": "_uniq.3941"
                    },
                    {
                      "value": null,
                      "username": "h₂",
                      "type": "Nat.minFac (Nat.factorial N + 1) ∣ Nat.factorial N + 1",
                      "id": "_uniq.3839"
                    },
                    {
                      "value": null,
                      "username": "h₁",
                      "type": "Nat.minFac (Nat.factorial N + 1) ∣ Nat.factorial N",
                      "id": "_uniq.3655"
                    },
                    {
                      "value": null,
                      "username": "pln",
                      "type": "¬Nat.minFac (Nat.factorial N + 1) ≥ N",
                      "id": "_uniq.3601"
                    },
                    {
                      "value": null,
                      "username": "pp",
                      "type": "Nat.Prime (Nat.minFac (Nat.factorial N + 1))",
                      "id": "_uniq.358"
                    },
                    {
                      "value": null,
                      "username": "N",
                      "type": "ℕ",
                      "id": "_uniq.297"
                    }
                  ]
                }
              ],
              "goalsAfter": []
            }
          }
        }
      ],
      "name": "have ppos: (Nat.minFac (Nat.factorial N + 1)) ≥ N"
    }
  },
  {
    "tacticApp": {
      "t": {
        "tacticString": "exact ⟨ (Nat.minFac (Nat.factorial N + 1)), ppos, pp ⟩",
        "tacticDependsOn": [
          "_uniq.297",
          "_uniq.3594",
          "_uniq.358"
        ],
        "goalsBefore": [
          {
            "username": "[anonymous]",
            "type": "∃ p, p ≥ N ∧ Nat.Prime p",
            "id": "_uniq.3595",
            "hyps": [
              {
                "value": null,
                "username": "ppos",
                "type": "Nat.minFac (Nat.factorial N + 1) ≥ N",
                "id": "_uniq.3594"
              },
              {
                "value": null,
                "username": "pp",
                "type": "Nat.Prime (Nat.minFac (Nat.factorial N + 1))",
                "id": "_uniq.358"
              },
              {
                "value": null,
                "username": "N",
                "type": "ℕ",
                "id": "_uniq.297"
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
