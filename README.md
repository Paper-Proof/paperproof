# Paperproof

Paperproof is a new proof interface for Lean 4.  

Paperproof will inspect how the hypotheses and goals were changing throughout the proof, and display this history - making it exactly equivalent to how we think of a mathematical proof on paper.

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
```
require Paperproof from git "https://github.com/Paper-Proof/paperproof.git" @ "main"/"lean"
```

3. In a Lean file with your theorems, write:
```
import Paperproof
```


You're done!  

Now, click on the paperproof icon, this will open a paperproof panel within vscode.  

<img width="200" src="https://user-images.githubusercontent.com/7578559/264487253-2d61e34e-6129-4a52-8156-baee20c1d761.jpg"/>

Then, click inside any theorem - you should see your proof tree rendered.

## Development

You're welcome to contribute to Paperproof, see the instructions in [CONTRIBUTING.md](https://github.com/Paper-Proof/paperproof/blob/main/CONTRIBUTING.md).

## Links

- Progress tracker in Notion ([notion link](https://safe-roof-f44.notion.site/Magic-paper-47f3f2c1d3b940428d7d981ea425a601))
- Paperproof demo ([youtube link](https://www.youtube.com/watch?v=0dVj4ITAF1o))
- Paperproof presentation ([tldraw link](https://www.tldraw.com/v/mlp_c_7vS7iofiWJ6_fwACbZyr?viewport=-2196%2C-8449%2C5257%2C2744&page=page%3Ai9kaf9cVmFmT3-gbYZmJ))
