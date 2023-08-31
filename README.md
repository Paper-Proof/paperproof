# Paperproof

Paperproof is a new proof interface for Lean 4.  

It will inspect how the hypotheses and goals were changing throughout the proof, and display this history - making it exactly equivalent to how we think of a mathematical proof on paper.

Paperproof is in active development, however you can try it already, see the [Installation](#installation) instructions below.

<div>
  <a href="https://www.youtube.com/watch?v=0dVj4ITAF1o">
      <img src="https://github.com/Paper-Proof/paper-proof/assets/7578559/f61bdbc8-1983-4315-af69-99852253d443"/>
  </a>
</div>

You can also watch a Paperproof demo on [youtube](https://www.youtube.com/watch?v=0dVj4ITAF1o), or read our [presentation](https://www.tldraw.com/v/mlp_c_7vS7iofiWJ6_fwACbZyr?viewport=-2196%2C-8449%2C5257%2C2744&page=page%3Ai9kaf9cVmFmT3-gbYZmJD).

## Installation

1. Install the "Paperproof" vscode extension ([link](https://marketplace.visualstudio.com/items?itemName=paperproof.paperproof)).

2. In your `lakefile.lean`, write:

```lean
require Paperproof from git "https://github.com/Paper-Proof/paperproof.git" @ "main"/"lean"
```

3. Then, in your terminal, run:
```shell
lake update Paperproof
```

4. In a Lean file with your theorems, write:
```lean
import Paperproof
```


**You're done!**  

Now, click on the paperproof icon (after you installed the Paperpoof extension, it should appear in all `.lean` files), this will open a paperproof panel within vscode.  

<img width="200" src="https://github.com/Paper-Proof/paperproof/assets/7578559/fd077fbe-36a3-4e94-9fa8-b7a38ffd1eea"/>



You can click on any theorem now - you should see your proof tree rendered.

## Updating

To update Paperproof, you only need to run `lake update Paperproof`. This will fetch the newest version of the Paperpoof Lean library from github, and build it.

Vscode extensions are automatically updated, however you can check for new updates with  
**`cmd+shift+p` => "Extensions: Show Extension Updates"**.  

Paperproof is a development package, so you might want to remove it from your `lakefile.lean` when you're pushing to production. In order to do that, just remove the Paperproof require from `lakefile.lean`, and run `lake update Paperproof`. This will clean up `lake-manifest.json` and `lake-packages` for you.

## Development

You're welcome to contribute to Paperproof, see the instructions in [CONTRIBUTING.md](https://github.com/Paper-Proof/paperproof/blob/main/CONTRIBUTING.md).

## Links

- Progress tracker in Notion ([notion link](https://safe-roof-f44.notion.site/Magic-paper-47f3f2c1d3b940428d7d981ea425a601))
- Paperproof demo ([youtube link](https://www.youtube.com/watch?v=0dVj4ITAF1o))
- Paperproof presentation ([tldraw link](https://www.tldraw.com/v/mlp_c_7vS7iofiWJ6_fwACbZyr?viewport=-2196%2C-8449%2C5257%2C2744&page=page%3Ai9kaf9cVmFmT3-gbYZmJ))
