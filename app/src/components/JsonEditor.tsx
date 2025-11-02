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
            fontSize: '12px'
          }}
        >
          Test Schema Error
        </button>
      </div>

      {/* Monaco Editor */}
      <div style={{ 
        height, 
        border: '1px solid #ddd', 
        borderRadius: '4px',
        overflow: 'hidden'
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
            bracketMatching: 'always',
            // Disable confusable character warnings
            unicodeHighlight: {
              ambiguousCharacters: false,
            },
          }}
        />
      </div>

      {/* Status indicator */}
      <div style={{ 
        marginTop: '5px', 
        fontSize: '12px',
        color: errors.length === 0 ? '#28a745' : '#dc3545'
      }}>
        {errors.length === 0 
          ? '✅ Valid JSON & Schema' 
          : `❌ ${errors.length} validation error(s)`
        }
      </div>
    </div>
  );
};

export default JsonEditor;