import React, { useState, useRef, useEffect } from 'react';
import { Editor, useMonaco } from '@monaco-editor/react';
import * as monaco from 'monaco-editor';

interface JsonEditorProps {
  value: string;
  onChange: (value: string) => void;
  onValidationChange?: (isValid: boolean, errors: monaco.editor.IMarker[]) => void;
  height?: string;
  theme?: 'vs-dark' | 'light' | 'vs' | 'solarized-light';
}

const JsonEditor: React.FC<JsonEditorProps> = ({
  value,
  onChange,
  onValidationChange,
  height = '400px',
  theme = 'solarized-light'
}) => {
  const editorRef = useRef<monaco.editor.IStandaloneCodeEditor | null>(null);
  const [errors, setErrors] = useState<monaco.editor.IMarker[]>([]);
  const [instructionsCopied, setInstructionsCopied] = useState(false);
  const monacoInstance = useMonaco();

  // Load Solarized Light theme when Monaco is ready
  useEffect(() => {
    if (monacoInstance) {
      console.log('Monaco instance available, loading Solarized Light theme...');
      import('monaco-themes/themes/Solarized-light.json')
        .then((themeData: any) => {
          console.log('Theme data loaded:', themeData);
          monacoInstance.editor.defineTheme('solarized-light', themeData);
          monacoInstance.editor.setTheme('solarized-light');
          console.log('Solarized Light theme loaded and set successfully');
        })
        .catch((error) => {
          console.error('Failed to load Solarized Light theme:', error);
          console.log('Falling back to light theme');
        });
    } else {
      console.log('Monaco instance not yet available');
    }
  }, [monacoInstance]);

  // Configure Monaco with Zod schema before editor mounts
  const handleEditorWillMount = (monaco: any) => {
    console.log('handleEditorWillMount called');
    
    // Load theme in beforeMount as well
    import('monaco-themes/themes/Solarized-light.json')
      .then((themeData: any) => {
        console.log('Loading theme in beforeMount:', themeData);
        monaco.editor.defineTheme('solarized-light', themeData);
        monaco.editor.setTheme('solarized-light');
        console.log('Theme set in beforeMount');
      })
      .catch((error) => {
        console.error('Failed to load theme in beforeMount:', error);
      });
    
    try {
      // Convert Zod schema to JSON Schema
      // Note: We'll do this manually since z.toJSONSchema might not be available in all Zod versions
      const jsonSchema = {
        type: "array",
        items: {
          type: "object",
          required: ["tacticString", "goalBefore", "goalsAfter"],
          properties: {
            tacticString: { type: "string" },
            tacticDependsOn: { type: "array", items: { type: "string" } },
            goalBefore: {
              type: "object",
              required: ["type", "id", "hyps"],
              properties: {
                type: { type: "string" },
                id: { type: "string" },
                username: { type: "string" },
                hyps: {
                  type: "array",
                  items: {
                    type: "object",
                    required: ["type", "id"],
                    properties: {
                      name: { type: "string" },
                      type: { type: "string" },
                      id: { type: "string" },
                      isProof: { type: "string" }
                    }
                  }
                }
              }
            },
            goalsAfter: {
              type: "array",
              items: {
                type: "object",
                required: ["type", "id", "hyps"],
                properties: {
                  type: { type: "string" },
                  id: { type: "string" },
                  username: { type: "string" },
                  hyps: {
                    type: "array",
                    items: {
                      type: "object",
                      required: ["type", "id"],
                      properties: {
                        name: { type: "string" },
                        type: { type: "string" },
                        id: { type: "string" },
                        isProof: { type: "string" }
                      }
                    }
                  }
                }
              }
            },
            spawnedGoals: {
              type: "array",
              items: {
                type: "object",
                required: ["type", "id", "hyps"],
                properties: {
                  type: { type: "string" },
                  id: { type: "string" },
                  username: { type: "string" },
                  hyps: {
                    type: "array",
                    items: {
                      type: "object",
                      required: ["type", "id"],
                      properties: {
                        name: { type: "string" },
                        type: { type: "string" },
                        id: { type: "string" },
                        isProof: { type: "string" }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      };

      // Register the schema with Monaco's JSON language service
      monaco.languages.json.jsonDefaults.setDiagnosticsOptions({
        validate: true,
        schemas: [{
          uri: 'http://myschema/userProofTree',
          fileMatch: ['*'],
          schema: jsonSchema
        }]
      });

      console.log('JSON Schema registered with Monaco');
    } catch (error) {
      console.error('Error setting up Monaco schema:', error);
    }
  };

  // This callback fires when validation is complete!
  const handleValidation = (markers: monaco.editor.IMarker[]) => {
    console.log('Monaco validation markers:', markers);
    setErrors(markers);
    
    // Notify parent of validation status
    if (onValidationChange) {
      const isValid = markers.length === 0;
      console.log('Notifying parent - isValid:', isValid, 'markers:', markers.length);
      onValidationChange(isValid, markers);
    }
  };

  const handleEditorMount = (editor: monaco.editor.IStandaloneCodeEditor, monacoInstance: any) => {
    editorRef.current = editor;
    console.log('Monaco editor mounted', { editor, monacoInstance });
  };

  // Helper to trigger validation manually
  const triggerValidation = () => {
    if (editorRef.current) {
      const model = editorRef.current.getModel();
      if (model) {
        // Trigger validation by slightly modifying and restoring the model
        const position = editorRef.current.getPosition();
        editorRef.current.trigger('', 'editor.action.formatDocument', {});
        if (position) {
          editorRef.current.setPosition(position);
        }
      }
    }
  };

  const exampleValue = `[
  {
    "tacticString": "ext x",
    "goalBefore": {
      "type": "s ∩ t = t ∩ s",
      "id": "goal_1",
      "hyps": [
        {"name": "s", "type": "Set ℕ", "id": "hyp_1"},
        {"name": "t", "type": "Set ℕ", "id": "hyp_2"}
      ]
    },
    "goalsAfter": [{
      "type": "x ∈ s ∩ t ↔ x ∈ t ∩ s",
      "id": "goal_2",
      "hyps": [
        {"name": "s", "type": "Set ℕ", "id": "hyp_1"},
        {"name": "t", "type": "Set ℕ", "id": "hyp_2"},
        {"name": "x", "type": "ℕ", "id": "hyp_3"}
      ]
    }]
  }
]`;

const instructionsText = `Instructions for Creating Mathematical Proof Trees
Overview:
You will convert natural language mathematical proofs into a structured JSON format that represents the proof as a sequence of steps. Each step shows how hypotheses (what we know) and goals (what we're trying to prove) change throughout the proof.
Core Structure:
A proof is an array of tactics (proof steps). Each tactic transforms the proof state:
{
  "tacticString": "introduce x",           // 2-5 word description of the step
  "tacticDependsOn": ["hyp_1", "hyp_2"],  // IDs of hypotheses used (optional)
  "goalBefore": { ... },                   // State before this step
  "goalsAfter": [ ... ],                   // State(s) after this step
  "spawnedGoals": [ ... ]                  // For advanced cases (optional)
}
Data Types:
Hypothesis - represents something we know or have assumed:
{
  "username": "h1",          // Variable name (optional, defaults to "")
  "type": "x ∈ S ∩ T",      // What this hypothesis states
  "id": "hyp_1",            // Unique identifier
  "isProof": "proof"        // Usually "proof" or "data" (optional)
}
Goal - represents what we're trying to prove at a given point:
{
  "type": "x ∈ T ∩ S",                    // Statement to prove
  "id": "goal_1",                          // Unique identifier  
  "username": "h",                         // Optional label (defaults to "")
  "hyps": [ /* array of hypotheses */ ]   // Available hypotheses
}
How to Structure a Proof:
1. Start with initial state: First tactic shows the theorem statement
2. Each step: Describe what happens (introduce variable, rewrite expression, split into cases, etc.)
3. Track changes: 
   - When you introduce a new hypothesis, add it to hyps in goalsAfter
   - When you transform a hypothesis, change its type and give it a new id
   - When the goal changes, update the type in goalsAfter
4. Branching: If proof splits (cases, iff), goalsAfter has multiple goals
5. Dependencies: List IDs of hypotheses actually used in tacticDependsOn

Induction:
When applying induction on a variable n (natural number), create TWO goals:

Goal 1 (base case):
- type: Replace n with 0 in the goal statement
- hyps: Keep all original hypotheses EXCEPT remove n itself

Goal 2 (inductive case):  
- type: Replace n with (n+1) or (succ n) in the goal statement
- hyps: Keep all original hypotheses + add these two NEW hypotheses:
  * n : ℕ (the predecessor, with a NEW id)
  * IH : [statement with n] (inductive hypothesis - the goal statement but for n, with username "IH")

<induction_example>
{
  "tacticString": "induction on n",
  "tacticDependsOn": ["hyp_1"],
  "goalBefore": {
    "type": "0 + n = n",
    "id": "goal_1",
    "hyps": [
      {"username": "n", "type": "ℕ", "id": "hyp_1", "isProof": "data"}
    ]
  },
  "goalsAfter": [
    {
      "type": "0 + 0 = 0",
      "id": "goal_2",
      "username": "base",
      "hyps": []
    },
    {
      "type": "0 + (n+1) = n+1",
      "id": "goal_3",
      "username": "ind",
      "hyps": [
        {"username": "n", "type": "ℕ", "id": "hyp_2", "isProof": "data"},
        {"username": "IH", "type": "0 + n = n", "id": "hyp_3", "isProof": "proof"}
      ]
    }
  ]
}
</induction_example>

Formatting Guidelines:
- tacticString: Use clear 2-5 word descriptions: "introduce x", "rewrite using ∩ definition", "apply commutativity", "cases on h1", "induction on n"
- types: Prefer mathematical unicode (∈, ∩, →, ∧, ∀) over words, but natural language is acceptable for clarity
- IDs: Use simple sequential IDs: "hyp_1", "hyp_2", "goal_1", etc.
- isProof: Use "proof" for assumptions/implications, "data" for concrete objects/values

Example - proving s ∩ t = t ∩ s:
<example>
[
  {
    "tacticString": "intro x",
    "goalBefore": {
      "type": "s ∩ t = t ∩ s",
      "id": "goal_1",
      "hyps": [
        {"username": "s", "type": "Set ℕ", "id": "hyp_1"},
        {"username": "t", "type": "Set ℕ", "id": "hyp_2"}
      ]
    },
    "goalsAfter": [{
      "type": "x ∈ s ∩ t ↔ x ∈ t ∩ s",
      "id": "goal_2",
      "hyps": [
        {"username": "s", "type": "Set ℕ", "id": "hyp_1"},
        {"username": "t", "type": "Set ℕ", "id": "hyp_2"},
        {"username": "x", "type": "ℕ", "id": "hyp_3"}
      ]
    }]
  }
]
</example>

Focus on capturing the logical flow: what we know at each step, what we're proving, and how each action transforms the state.`;

  const copyInstructionsToClipboard = async () => {
    try {
      await navigator.clipboard.writeText(instructionsText);
      setInstructionsCopied(true);
      console.log('Instructions copied to clipboard');
      
      // Reset the copied state after 2 seconds
      setTimeout(() => {
        setInstructionsCopied(false);
      }, 2000);
    } catch (err) {
      console.error('Failed to copy instructions to clipboard:', err);
      // Fallback for older browsers
      const textArea = document.createElement('textarea');
      textArea.value = instructionsText;
      document.body.appendChild(textArea);
      textArea.select();
      document.execCommand('copy');
      document.body.removeChild(textArea);
      setInstructionsCopied(true);
      
      // Reset the copied state after 2 seconds
      setTimeout(() => {
        setInstructionsCopied(false);
      }, 2000);
    }
  };

  return (
    <div>
      {/* Error display */}
      {errors.length > 0 && (
        <div style={{
          background: '#fee',
          border: '1px solid #fcc',
          borderRadius: '4px',
          padding: '10px',
          marginBottom: '10px',
          fontSize: '12px'
        }}>
          <strong>❌ {errors.length} Validation Error(s):</strong>
          <ul style={{ margin: '5px 0', paddingLeft: '20px' }}>
            {errors.map((error, idx) => (
              <li key={idx}>
                <strong>Line {error.startLineNumber}, Column {error.startColumn}:</strong> {error.message}
              </li>
            ))}
          </ul>
        </div>
      )}

      {/* Load example button */}
      <div style={{ marginBottom: '10px' }}>
        <button
          onClick={() => {
            onChange(exampleValue);
            setTimeout(triggerValidation, 100);
          }}
          style={{
            background: '#28a745',
            color: 'white',
            border: 'none',
            padding: '6px 12px',
            borderRadius: '4px',
            cursor: 'pointer',
            fontSize: '12px',
            marginRight: '10px'
          }}
        >
          Load Example JSON
        </button>
        <button
          onClick={() => {
            onChange('{ "invalid": }');
            setTimeout(triggerValidation, 100);
          }}
          style={{
            background: '#dc3545',
            color: 'white',
            border: 'none',
            padding: '6px 12px',
            borderRadius: '4px',
            cursor: 'pointer',
            fontSize: '12px',
            marginRight: '10px'
          }}
        >
          Test Invalid JSON
        </button>
        <button
          onClick={() => {
            onChange('[{"tacticString": 123}]');
            setTimeout(triggerValidation, 100);
          }}
          style={{
            background: '#ffc107',
            color: 'black',
            border: 'none',
            padding: '6px 12px',
            borderRadius: '4px',
            cursor: 'pointer',
            fontSize: '12px',
            marginRight: '10px'
          }}
        >
          Test Schema Error
        </button>
        <span style={{ fontSize: '12px', color: '#333' }}>
          Click <button 
            type="button"
            onClick={copyInstructionsToClipboard}
            style={{
              background: instructionsCopied ? '#4caf50' : '#007bff',
              color: 'white',
              border: 'none',
              padding: '0px 8px',
              borderRadius: '3px',
              cursor: 'pointer',
              fontSize: '12px',
              transition: 'all 0.2s ease'
            }}
          >
            {instructionsCopied ? '✓ Copied!' : 'here'}
          </button> to copy instructions for llm.
        </span>
      </div>

      {/* Monaco Editor */}
      <div style={{ 
        height,
        borderRadius: '4px',
        overflow: 'hidden',
        marginBottom: 40,
      }}>
        <Editor
          height="100%"
          defaultLanguage="json"
          value={value}
          onChange={(value) => onChange(value || '')}
          beforeMount={handleEditorWillMount}
          onMount={handleEditorMount}
          onValidate={handleValidation}
          theme={theme}
          options={{
            minimap: { enabled: false },
            fontSize: 12,
            lineNumbers: 'on',
            wordWrap: 'on',
            formatOnPaste: true,
            formatOnType: true,
            scrollBeyondLastLine: false,
            automaticLayout: true,
            readOnly: false,
            tabSize: 2,
            insertSpaces: true,
            folding: true,
            // Disable confusable character warnings
            unicodeHighlight: {
              ambiguousCharacters: false,
            },
          }}
        />
      </div>
    </div>
  );
};

export default JsonEditor;