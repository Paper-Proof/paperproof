<h1 align="center">Paperproof</h1>

<h2 align="center">
A new proof interface for Lean 4.  
</h2>

<div align="center">
  <img width="900" alt="Paperproof vscode" src="https://github.com/user-attachments/assets/08c4438a-c940-4dc4-92e8-cd82be4af32a">
</div>

<div align="center">
  <b>Try Paperproof online</b><br/>

  <a href="https://codespaces.new/Paper-Proof/paperproof">
    <img width="200" src="https://github.com/codespaces/badge.svg"/>
  </a>
    
</div>
<br/>

Paperproof will inspect how the hypotheses and goals were changing throughout the Lean 4 proof, and display this history - making it equivalent to how we think of a mathematical proof on paper.



---

In the following tables, you can see what tactics such as `apply`, `rw`, or `cases` look like in Paperproof; and how Paperproof renders real proofs from well-known repos.

<details>
  <summary>
    Common tactics
  </summary>

  <table>
  <tbody>
    
  <tr>
  <th>Lean</th>
  <th>Paperproof</th>
  </tr>
  <tr>
  <td colspan="2" align="center">

**apply**

  </td>
  </tr>
  <tr>
  <td>

```lean
theorem apply (a b: ℝ) : a = b := by
  apply le_antisymm
```

  </td>
  <td align="center">
    <img width="232" alt="image" src="https://github.com/user-attachments/assets/eb183244-22e8-4219-9566-54edf4a590ce">
  </td>
  </tr>

  <tr><td colspan="2" align="center">

**have**

  </td></tr>
  <td>

```lean
theorem have (a b: ℝ)
(h1: a ≤ b) (h2: b ≤ a) : True := by
  have hi := le_antisymm h1 h2
```

  </td>
  <td align="center">
    <img width="232" alt="image" src="https://github.com/user-attachments/assets/162205b8-4c43-4c8e-967d-cd942197c6c5">
  </td>
  </tr>

  <tr><td colspan="2" align="center">

**intro**

  </td></tr>
  <tr>
  <td>

```lean
theorem intro
: ∀ (N: ℕ), ∃ M, N + N = M := by
  intro n
```

  </td>
  <td align="center">
    <img width="232" alt="image" src="https://github.com/user-attachments/assets/9b465827-6f49-4be6-a7fe-7126165c9b2b">
  </td>
  </tr>

  <tr><td colspan="2" align="center">

**rw**

  </td></tr>
  <tr>
  <td>

```lean
theorem rw (a b: ℕ)
(h1: a = b) : (10 * a = 666) := by
  rw [h1]
```

  </td>
  <td align="center">
    <img width="232" alt="image" src="https://github.com/user-attachments/assets/f12799fe-4bbc-48a1-9441-859d814b7512">
  </td>
  </tr>

  <tr><td colspan="2" align="center">

**by_contra**

  </td></tr>
  <tr>
  <td>

```lean
theorem by_contra (m: ℕ)
: 2 ≤ m := by
  by_contra h
```

  </td>
  <td align="center">
    <img width="232" alt="image" src="https://github.com/user-attachments/assets/0274d202-b64c-4bb0-959a-565713ba0140">
  </td>
  </tr>

  <tr><td colspan="2" align="center">

**use**

  </td></tr>
  <tr>
  <td>

```lean
theorem use
: ∃ x: ℕ, x = 5 := by
  use 42
```

  </td>
  <td align="center">
    <img width="232" alt="image" src="https://github.com/user-attachments/assets/eecfec7b-9610-4fee-a9dc-51a6a95dd5f9">
  </td>
  </tr>

  <tr><td colspan="2" align="center">

**induction**

  </td></tr>
  <tr>
  <td>

```lean
theorem induction (n: ℕ)
: Nat.mul 0 n = 0 := by
  induction' n with k ih
```

  </td>
  <td align="center">
    <img width="408" alt="image" src="https://github.com/user-attachments/assets/0f2c746c-9940-4444-8f30-27185a4eb2bc">
  </td>
  </tr>

  <tr><td colspan="2" align="center">

**cases**

  </td></tr>
  <tr>
  <td>

```lean
theorem casesN (n: ℕ)
: Nat.mul 0 n = 0 := by
  cases' n with m
```

  </td>
  <td align="center">
    <img width="385" alt="image" src="https://github.com/user-attachments/assets/15ca7899-a77c-479a-90b9-1fd4159bb0b5">
  </td>
  </tr>
  <tr></tr>
  <tr>
  <td>

```lean
theorem casesAnd (A B C: Prop)
(h: A ∧ B) : C := by
  cases' h with a b
```

  </td>
  <td align="center">
    <img width="217" alt="image" src="https://github.com/user-attachments/assets/077eae28-c1fc-4eb7-b9db-6e37e615e178">
  </td>
  </tr>
  <tr></tr>
  <tr>
  <td>

```lean
theorem casesOr (A B C: Prop)
(h: A ∨ B) : C := by
  cases' h with a b
```

  </td>
  <td align="center">
    <img width="306" alt="image" src="https://github.com/user-attachments/assets/da0592e5-9db0-4548-b475-a0ae7945cd98">
  </td>
  </tr>
  <tr></tr>
  <tr>
  <td>

```lean
inductive Random where
  | hi: ℕ → String → Random
  | hello: (2 + 2 = 4) → Random
  | wow: Random
theorem casesRandom (C: Prop)
(h: Random) : C := by
  cases' h with a b c
```

  </td>
  <td align="center">
    <img width="410px" alt="image" src="https://github.com/user-attachments/assets/ba2d3dd0-06c7-42ae-b409-67f343ee97b2">
  </td>
  </tr>

  </tbody>
  </table>
</details>

<details>
  <summary>
  Full-fledged proofs
  </summary>

  <table>
  <tbody>

  <tr></tr>
    
  <tr>
  <td align="center">

**Mathematics in Lean (Jeremy Avigad, Patrick Massot)** <br/>([mathematics_in_lean/MIL/C05_Elementary_Number_Theory/solutions/Solutions_S03_Infinitely_Many_Primes.lean:155](https://github.com/leanprover-community/mathematics_in_lean/blob/4bc81ddea0a62c3bbd33cbfc4b4b501d2d0dfb03/MIL/C05_Elementary_Number_Theory/solutions/Solutions_S03_Infinitely_Many_Primes.lean#L155))

  </td>
  </tr>
  <tr>
  <td align="center">
    <img width="1136" alt="Mathematics in Lean - Paperproof" src="https://github.com/user-attachments/assets/432dd171-faf8-42c1-a4c2-4d5f62672ff1">
  </td>
  </tr>

  <tr>
  <td align="center">

**Mathlib** <br/>([mathlib4/Mathlib/Algebra/Field/Power.lean:30](https://github.com/leanprover-community/mathlib4/blob/9893bbd22fdca4005b93c8dbff16c1d2de21bc1a/Mathlib/Algebra/Field/Power.lean#L30))

  </td>
  </tr>
  <tr>
  <td align="center">  
    <img width="1042" alt="Mathlib - Paperproof" src="https://github.com/user-attachments/assets/05a69569-3370-4f4e-b50b-aef7a41d50f5">
  </td>
  </tr>

  <tr>
  <td align="center">

**Hitchhiker's Guide to Logical Verification** <br/> **(Anne Baanen, Alexander Bentkamp, Jasmin Blanchette, Johannes Hölzl, Jannis Limperg)** <br/>
([logical_verification_2023/blob/main/lean/LoVe/LoVe05_FunctionalProgramming_Demo.lean:316](https://github.com/blanchette/logical_verification_2023/blob/f709e20d2cd515d4ede3e7d2db30103d4f58aaca/lean/LoVe/LoVe05_FunctionalProgramming_Demo.lean#L316))

  </td>
  </tr>
  <tr>
  <td align="center">
    <img width="1207" alt="Hitchhiker's Guide to Logical Verification - Paperproof" src="https://github.com/user-attachments/assets/4b04b1a9-ddf9-4994-b9ca-a24611a3eb93">
  </td>
  </tr>

  </tbody>
  </table>
</details>

## Installation

1. Install the "Paperproof" vscode extension ([link](https://marketplace.visualstudio.com/items?itemName=paperproof.paperproof)).

2. In your `lakefile.toml`, write:
   
   ```lean
   [[require]]
   name = "Paperproof"
   git = "https://github.com/Paper-Proof/paperproof.git"
   subDir = "lean"
   rev = "main"
   ```

4. Then, in your terminal, run:

   ```shell
   lake update Paperproof
   ```

   > Note:
   > if you're getting "error: unexpected arguments: Paperproof", it means you're on the older version of Lean, and it doesn't support per-package updates. In that case, just run `lake build`.

5. In a Lean file with your theorems, write:

   ```lean
   import Paperproof
   ```

6. **You're done!**

   Now, click on the paperproof icon (after you installed the Paperproof extension, it should appear in all `.lean` files), this will open a Paperproof panel within vscode.

   <img width="200" src="https://github.com/Paper-Proof/paperproof/assets/7578559/fd077fbe-36a3-4e94-9fa8-b7a38ffd1eea"/>

   You can click on any theorem now (well, only tactic-based proofs, those starting with `by`, are supported now) - you should see your proof tree rendered.

> [!TIP]
> If you get a build error when you try to build the paperproof package, please copypaste the error message and create the corresponding issue in Paperproof.
> Lean updates its metaprogramming api frequently - we try to go along with it, and it's helpful when incompatibilities are discovered on time.   
> The quickfix for any Paperproof build error is to use the Lean version mentioned in [Paperproof's lean-toolchain](https://github.com/Paper-Proof/paperproof/blob/main/lean-toolchain).

## Tutorial

If you worked with formal proofs before, you might find Paperproof most similar to proof trees/Gentzen trees. The resemblance is not spurious, we can easily mimic Semantic Tableaux and Natural Deduction trees with Paperproof. All of these interfaces show "the history of a proof" - the way hypotheses and nodes were changing throughout the proof.

Unlike Gentzen, we can make use of css and javascript - so there are many visual syntax sugars on top of what would be a formal proof tree:

- hypotheses aren't repeated when used multiple times,
- goals and hypotheses are visually differentiated,
- variable scopes are shown as darkening backgrounds,
- available hypotheses are indicated via node transparencies,
- and so on.

Below, you will see a table with the main features of Paperproof.

<details>
  <summary>
  Paperproof walkthrough
  </summary>
  <table>
    
  <tbody>
    
  <tr>
  <th>Lean</th>
  <th>Paperproof</th>
  </tr>

  <tr>
  <td colspan="2" align="center">
  <b>Hypotheses are displayed as green nodes, <br/>goals are displayed as red nodes,<br/>tactics are displayed as transparent nodes with dashed borders.</b> 
  </td>
  </tr>

  <tr>
  <td align="center">
    <img width="204" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/afc8000f-ad15-4ed4-b1fa-6740745895c6">
  </td>
  <td align="center">
    <img width="360" alt="image" src="https://github.com/user-attachments/assets/28605079-847b-4353-a6bf-3f668829ff97">
  </td>
  </tr>

  <tr>
  <td colspan="2" align="center">
  <b>A proof should be read "towards the middle".</b><br/>
  So, hypotheses should be read from top to bottom; and goals should be read bottom up.

  </td>
  </tr>

  <tr>
  <td align="center">    
    <img width="308" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/2bd007e9-6fb3-4f32-a17d-d010af53a798">

  </td>
  <td align="center">
    <img width="366" alt="image" src="https://github.com/user-attachments/assets/2899b1fd-063b-4612-8f54-ecb972ab70cd">
  </td>
  </tr>

  
  <tr>
  <td colspan="2" align="center">
  <b>To zoom in on a particular dark box, you can click on it.</b><br/>
  <i>Hint: these boxes represent variable scopes. Don't overthink this however, we'll always highlight the available hypotheses as you're writing the proof, consider these boxes a visual hint that will eventually become second nature.</i>
  </td>
  </tr>

  <tr>
  <td>
  </td>
  <td align="center">
    <img width="332" alt="Screenshot 2024-08-26 at 13 58 30" src="https://github.com/user-attachments/assets/02deceff-f482-4897-af5c-4f7223b8bafb">
  </td>
  </tr>
  </tbody>
  </table>
</details>

## Updating

To update Paperproof, you only need to rerun `lake update Paperproof`. This will fetch the newest version of the Paperproof Lean library from this github repo, and build it.

Vscode extensions are automatically updated, however you can check for new updates with  
**`cmd+shift+p` => "Extensions: Show Extension Updates"**.

Paperproof is a package that's usually only used during development, so you might want to remove it from your `lakefile.lean` when you're pushing to production. In order to do that, just remove the Paperproof require from `lakefile.lean`, and run `lake update Paperproof`. This will clean up `lake-manifest.json` and `lake-packages` for you.

## About Paperproof

**Theoretical:**

- Paperproof ♥️ Semantic Tableaux: [link](https://lakesare.brick.do/paperproof-love-semantic-tableaux-G6rR2BxL5Eyl)
- Paperproof ♥️ Natural Deduction: [link](https://lakesare.brick.do/paperproof-love-natural-deduction-3Mve6W8NgYRJ)
- Paperproof ⚔️ Lean's _#explode_: [link](https://paperproof.brick.do/paperproof-lean-s-explode-Bab05XYMp21q)
- Lean ⚔️ Coq ⚔️ Metamath ⚔️ Isabel proof trees: [link](https://lakesare.brick.do/lean-coq-isabel-and-their-proof-trees-yjnd2O2RgxwV)

**Practical:**

- How to add my Lean repo to Github Codespaces: [link](https://lakesare.brick.do/how-to-add-my-lean-repo-to-github-codespaces-A13P6g7aYwgg)
- Can Paperproof render proof terms: [link](https://paperproof.brick.do/can-paperproof-render-proof-terms-qm1NZZkazb21)
- Paperproof's Architecture: [link](https://paperproof.brick.do/paperproof-s-architecture-P632P44ezDa9)
- Anatomy of the _InfoTree_: [link](https://paperproof.brick.do/wip-info-tree-anatomy-Qdgyz0zkybL2), [link](https://antonkov.github.io/posts/How-to-build-a-proof-tree)

**Videos:**

- a super quick 1-minute demo of Paperproof: [youtube link](https://youtu.be/xiIQ0toSpxQ)
- our Lean Together presentation: [youtube link](https://www.youtube.com/watch?v=DWuAGt2RDaM)
- a full Paperproof tutorial: [youtube link](https://youtu.be/q9w1djIcCvc)

## Development

You're welcome to contribute to Paperproof, see the instructions in [CONTRIBUTING.md](https://github.com/Paper-Proof/paperproof/blob/main/CONTRIBUTING.md).

<div align="center">
<img width="60px" src="https://github.com/Paper-Proof/paperproof/assets/7578559/58f24cf2-4336-4376-8738-6463e3802ba0">
</div>
