<h1 align="center">Paperproof Embed</h1>

<h2 align="center">
Proof trees for your own web pages
</h2>

## Usage

### HTML

```wikitext
<link rel="paperproof" href="my-styles.css"> <!-- optional: your own CSS for the Paperproof component -->
<script src="https://cdn.jsdelivr.net/npm/paperproof@0.3/dist/paperproof-embed.js"></script>

<paperproof-proof>
  <script type="application/json">
    { the proof, as JSON }
  </script>
</paperproof-proof>
```

### React

```bash
npm install paperproof
```

```wikitext
<link rel="paperproof" href="my-styles.css"> <!-- optional: your own CSS for the Paperproof component -->
import { Paperproof } from "paperproof/react";

<Paperproof proof={proof}/>
```

## Where the JSON comes from

- **Existing Lean proof:** in the Paperproof VSCode extension, right-click the proof and choose "Copy for LLM".
- **Your LLM agent:** tell him to run `npx paperproof instructions`, and he'll convert any natural-language proof into Paperproof format.
