<h1 align="center">Paperproof</h1>

<h2 align="center">
A new proof interface for Lean 4.  
</h2>

<div align="center">
  <img width="900" alt="Paperproof vscode" src="https://github.com/Paper-Proof/paperproof/assets/7578559/a5792103-6de4-4e98-aa7a-4bcf51aabd47">
</div>

Paperproof will inspect how the hypotheses and goals were changing throughout the Lean 4 proof, and display this history - making it equivalent to how we think of a mathematical proof on paper.

You can see Paperproof in action on [youtube](https://www.youtube.com/watch?v=0dVj4ITAF1o).  
Here you can read about Paperproof in context of other proof trees: [lakesare.brick.do/lean-coq-isabel-and-their-proof-trees](https://lakesare.brick.do/lean-coq-isabel-and-their-proof-trees-yjnd2O2RgxwV).


## Installation

1. Install the "Paperproof" vscode extension ([link](https://marketplace.visualstudio.com/items?itemName=paperproof.paperproof)).

2. In your `lakefile.lean`, write:
    ```lean
    require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"
    ```

3. Then, in your terminal, run:
    ```shell
    lake update Paperproof
    ```

    *Note: if you're getting "error: unexpected arguments: Paperproof", it means you're on the older version of Lean, and it doesn't support per-package updates. In that case, just run `lake build`.*

4. In a Lean file with your theorems, write:
    ```lean
    import Paperproof
    ```

    
**You're done!**

Now, click on the paperproof icon (after you installed the Paperpoof extension, it should appear in all `.lean` files), this will open a paperproof panel within vscode.  

<img width="200" src="https://github.com/Paper-Proof/paperproof/assets/7578559/fd077fbe-36a3-4e94-9fa8-b7a38ffd1eea"/>

You can click on any theorem now - you should see your proof tree rendered.

## Tutorial

Something that most looks like Paperproof that you have previously encountered is probably Gentzen trees. The resemblance is not spurious, we can easily mimic Semantic Tableaux trees and Natural Deduction trees with Paperproof. All of these interfaces show "the history of a proof" - the way hypotheses and nodes were changing throughout the proof.

Unlike Gentzen, we can make use of css and javascript - so there are many visual syntax sugars on top of what would be a Gentzen tree - we don't repeat hypotheses if we need to use them multiple times, goals and hypotheses are visually differentiated, variable scopes are shown as darkening backgrounds, available hypotheses are indicated via node transparencies, and so on.

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
Hypotheses are displayed as green nodes, goals are displayed as red nodes, tactics are displayed as transparent nodes with dashed borders. 
</td>
</tr>

<tr>
<td>
<img width="204" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/afc8000f-ad15-4ed4-b1fa-6740745895c6">
</td>
<td>
  <img width="350" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/287cf8e6-beeb-42a5-be5f-46eda9e956bd">
</td>
</tr>




<tr>
<td colspan="2" align="center">
A proof should be read "towards the middle" - so, hypotheses should be read from top to bottom; and goals should be read bottom up.  

</td>
</tr>

<tr>
<td>
  
<img width="308" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/2bd007e9-6fb3-4f32-a17d-d010af53a798">


</td>
<td>
  <img width="350" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/066bb876-e7d6-4980-a725-8fe82666b5e1">
</td>
</tr>




<tr>
<td colspan="2" align="center">
If you drag these nodes around you will see arrows, however we're not displaying them to clean up the interface.
</td>
</tr>

<tr>
<td>
</td>
<td>
 <img width="350" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/a5a45209-8822-463c-b942-b395578089e9">

</td>
</tr>




<tr>
<td colspan="2" align="center">
Opaque nodes represent a focused goal, and currently available hypotheses.<br/>  
In general - slightly darker backgrounds demarcate variable scopes - you can only use hypotheses that are outside of your box, you can never dive into some new box. Don't overthink this however, we'll always highlight the available hypotheses as you're writing the proof, consider backgrounds a visual hint that will eventually become second nature.
</td>
</tr>

<tr>
<td>
</td>
<td>
  <img width="350" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/01251e80-6c43-40d2-9439-1f967d978586">

</td>
</tr>




<tr>
<td colspan="2" align="center">
To zoom in on a particular dark box, you can click on it.
</td>
</tr>

<tr>
<td>
</td>
<td>
  <img width="350" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/5408a108-f754-45d7-b4ad-819e4930bc5e">
</td>
</tr>

<tr>
<td colspan="2" align="center">
  To copy text of a particular tactic/hypothesis/goal, right-click on that node. 
</td>
</tr>

<tr>
<td>
</td>
<td>
  <img width="241" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/dbf84af0-32cb-424f-bbf8-ddde5c83b287">
</td>
</tr>



</tbody>
</table>
</details>

And in the following table, you can see what tactics such as `apply`, `rw`, or `cases` look like in Paperproof.

<details>
<summary>
  Common Tactics
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
  theorem apply (a b : ℝ)
  : a = b := by
    apply le_antisymm
  ```

</td>
<td>
  <img width="222" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/bd4f02d1-a1d4-47b2-8c4f-44059a79c543">
</td>
</tr>


<tr><td colspan="2" align="center">

**have**
</td></tr>
<td>

  ```lean
  theorem have_ (a b : ℝ) (h1 : a ≤ b) (h2 : b ≤ a)
  : True := by
    have hi := le_antisymm h1 h2
  ```

</td>
<td>
  <img width="378" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/4f28df15-f5ea-4a9c-982f-5d81945beb41">
</td>
</tr>


<tr><td colspan="2" align="center">

**intro**
</td></tr>
<tr>
<td>

  ```lean
  theorem intro
  : ∀ (N : ℕ), ∃ M, N + N = M := by
    intro n
  ```

</td>
<td>
  <img width="275" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/e1d862cf-0bd8-4705-9ed2-66c282f5a73d">
</td>
</tr> 


<tr><td colspan="2" align="center">

**rw**
</td></tr>
<tr>
<td>

  ```lean
  theorem rw (a b : ℕ) (h1: a = b)
  : (10 * a = 666) := by
    rw [h1]
  ```

</td>
<td>
  <img width="268" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/cf57167c-b4ba-485b-8da2-e60af9f6b3ba">
</td>
</tr> 


<tr><td colspan="2" align="center">

**induction**
</td></tr>
<tr>
<td>

  ```lean
  theorem induction (n : ℕ)
  : Nat.mul 0 n = 0 := by
    induction' n with k ih
  ```

</td>
<td>
  <img width="564" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/45365de6-b5a2-4643-8e8e-82d1bd80f966">
</td>
</tr>


<tr><td colspan="2" align="center">

**cases**
</td></tr>
<tr>
<td>

  ```lean
  theorem casesN (n : ℕ)
  : Nat.mul 0 n = 0 := by
    cases' n with m
  ```

</td>
<td>
  <img width="552" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/b88c9f0c-6ecd-4a78-828f-de84c433a429">
</td>
</tr>
<tr></tr>
<tr>
<td>

  ```lean
  theorem casesAnd (A B C : Prop) (h : A ∧ B)
  : C := by
    cases' h with a b
  ```

</td>
<td>
  <img width="485" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/ec146278-c298-43a3-b793-91b00cf7082c">
</td>
</tr>
<tr></tr>
<tr>
<td>

  ```lean
  theorem casesOr (A B C : Prop) (h : A ∨ B)
  : C := by
    cases' h with a b
  ```

</td>
<td>
  <img width="431" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/d4e11a5f-32a5-463d-ad32-f874c098633b">
</td>
</tr>
<tr></tr>
<tr>
<td>

  ```lean
  inductive Random where
    | hi : ℕ → String → Random
    | hello : (2 + 2 = 4) → Random 
    | wow : Random
  theorem casesRandom (C: Prop) (h : Random)
  : C := by
    cases' h with a b c
  ```

</td>
<td>
  <img width="546" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/cc95c055-4172-4c84-ac62-2f3515fe2383">
</td>
</tr>


<tr><td colspan="2" align="center">

**by_contra**
</td></tr>
<tr>
<td>

  ```lean
  theorem by_contra_ (m : ℕ)
  : 2 ≤ m := by
    by_contra h
  ```

</td>
<td>
  <img width="152" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/2b5fc5bf-783b-4b31-9135-9c24bf3a9d28">
</td>
</tr>


<tr><td colspan="2" align="center">

**use**
</td></tr>
<tr>
<td>

  ```lean
  theorem use
  : ∃ x : Nat, x = 5 := by
    use 42
  ```

</td>
<td>
  <img width="148" alt="image" src="https://github.com/Paper-Proof/paperproof/assets/7578559/e69ffe96-5bfa-4370-9c4c-bfbb2382e75d">
</td>
</tr>
</tbody>
</table>
</details>

In this table, you can see Paperproof rendering real proofs.

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
  <img width="1358" alt="Mathematics in Lean - Paperproof" src="https://github.com/Paper-Proof/paperproof/assets/7578559/765bc84e-4d4c-417f-877e-48bc9a0abe1c">
</td>
</tr>




<tr>
<td align="center">

**Mathlib** <br/>([mathlib4/Mathlib/Algebra/Field/Power.lean:30](https://github.com/leanprover-community/mathlib4/blob/9893bbd22fdca4005b93c8dbff16c1d2de21bc1a/Mathlib/Algebra/Field/Power.lean#L30))
</td>
</tr>
<tr>
<td align="center">  
  <img width="1278" alt="Mathlib - Paperproof" src="https://github.com/Paper-Proof/paperproof/assets/7578559/2103c78e-be6d-46e6-b25d-86cbfb1a5fad">
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
  <img width="1385" alt="Hitchhiker's Guide to Logical Verification - Paperproof" src="https://github.com/Paper-Proof/paperproof/assets/7578559/568e70e0-992e-4a65-a306-6c0693750fe8">
</td>
</tr>

</tbody>
</table>
</details>


## Updating

To update Paperproof, you only need to rerun `lake update Paperproof`. This will fetch the newest version of the Paperpoof Lean library from this github repo, and build it.

Vscode extensions are automatically updated, however you can check for new updates with  
**`cmd+shift+p` => "Extensions: Show Extension Updates"**.  

Paperproof is a package that's usually only used during development, so you might want to remove it from your `lakefile.lean` when you're pushing to production. In order to do that, just remove the Paperproof require from `lakefile.lean`, and run `lake update Paperproof`. This will clean up `lake-manifest.json` and `lake-packages` for you.

## Development

You're welcome to contribute to Paperproof, see the instructions in [CONTRIBUTING.md](https://github.com/Paper-Proof/paperproof/blob/main/CONTRIBUTING.md).


<div align="center">
<img width="60px" src="https://github.com/Paper-Proof/paperproof/assets/7578559/58f24cf2-4336-4376-8738-6463e3802ba0">
</div>
