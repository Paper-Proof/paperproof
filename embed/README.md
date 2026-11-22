<h1 align="center">Paperproof Embed</h1>

<h2 align="center">
Proof trees for your own web pages
</h2>

## Usage

### HTML

```html
<script src="https://cdn.jsdelivr.net/npm/paperproof@0.1.3/dist/paperproof-embed.js"></script>

<paperproof-proof>
  <script type="application/json">
    { the proof, as JSON }
  </script>
</paperproof-proof>
```

### React (soon-to-come)

```jsx
import { Paperproof } from "paperproof/react";
import "paperproof/react.css";

<Paperproof proof={proof}/>
```

## Where the JSON comes from

- **Existing Lean proof:** in the Paperproof VSCode extension, right-click the proof and choose "Copy for LLM".
- **Your LLM agent:** tell him to run `npx paperproof instructions`, and he'll convert any natural-language proof into Paperproof format.
