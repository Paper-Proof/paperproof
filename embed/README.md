<h1 align="center">Paperproof Embed</h1>

<h2 align="center">
Proof trees for your own web pages
</h2>

## Putting a proof on a page

```html
<script src="https://cdn.jsdelivr.net/npm/paperproof@0.1.1/dist/paperproof-embed.js"></script>

<paperproof-proof>
  <script type="application/json">
    { the proof, as JSON }
  </script>
</paperproof-proof>
```

## Where the JSON comes from

- **A Lean proof:** in the Paperproof VS Code extension, right-click the proof and choose *Copy for LLM*.
- **An AI agent:** tell it to run `npx paperproof instructions`, which explains the format and how to check its work.
