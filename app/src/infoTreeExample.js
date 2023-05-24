const infoTreeExample = [
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

export default infoTreeExample