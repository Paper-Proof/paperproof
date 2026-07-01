import React, { useRef, useEffect } from 'react';
import { Editor, useMonaco } from '@monaco-editor/react';
import * as monaco from 'monaco-editor';
import { proofJsonSchema } from '../services/proofSchema';

interface JsonEditorProps {
  value: string;
  onChange: (value: string) => void;
  onValidationChange?: (isValid: boolean, errors: monaco.editor.IMarker[]) => void;
  height?: string;
}

const JsonEditor: React.FC<JsonEditorProps> = ({
  value,
  onChange,
  onValidationChange,
  height = '400px',
}) => {
  const editorRef = useRef<monaco.editor.IStandaloneCodeEditor | null>(null);
  const monacoInstance = useMonaco();

  useEffect(() => {
    if (!monacoInstance) return;
    monacoInstance.editor.defineTheme('paperproof', {
      base: 'vs',
      inherit: false,
      rules: [
        { token: '',                foreground: '3a2a1a' },
        { token: 'string.key.json', foreground: '3a2a1a', fontStyle: 'bold' },
      ],
      colors: { 'editor.background': '#FDF6E3' },
    });
    monacoInstance.editor.setTheme('paperproof');
  }, [monacoInstance]);

  const handleEditorWillMount = (monaco: any) => {
    monaco.languages.json.jsonDefaults.setDiagnosticsOptions({
      validate: true,
      schemas: [{ uri: 'http://myschema/userProofTree', fileMatch: ['*'], schema: proofJsonSchema }],
    });
  };

  const handleValidation = (markers: monaco.editor.IMarker[]) => {
    if (onValidationChange) {
      onValidationChange(markers.length === 0, markers);
    }
  };

  return (
    <div style={{ height, overflow: 'hidden' }}>
      <Editor
        height="100%"
        defaultLanguage="json"
        value={value}
        onChange={(value: string | undefined) => onChange(value || '')}
        beforeMount={handleEditorWillMount}
        onMount={(editor) => { editorRef.current = editor; }}
        onValidate={handleValidation}
        theme="paperproof"
        options={{
          minimap: { enabled: false },
          fontSize: 12,
          lineNumbers: 'on',
          wordWrap: 'on',
          formatOnPaste: true,
          formatOnType: true,
          scrollBeyondLastLine: false,
          automaticLayout: true,
          tabSize: 2,
          insertSpaces: true,
          folding: true,
          unicodeHighlight: { ambiguousCharacters: false },
          stickyScroll: { enabled: false },
        }}
      />
    </div>
  );
};

export default JsonEditor;
