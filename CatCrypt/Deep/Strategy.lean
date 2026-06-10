/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# Proof Strategy Guide: Deep vs Shallow Embedding

This module documents the recommended proof strategy for CatCrypt-Lean,
informed by the ASIACRYPT 2025 paper "How Hard Can It Be to Formalize a Proof?"
(Dupressoir et al.) which compared three CryptoBox formalizations in EasyCrypt.

## The Blended Approach

CatCrypt-Lean uses a **blended approach** combining the modularity of
state-separating proofs (SSP) with the automation-friendliness of
game-playing proofs.

### Embedding Selection Guide

| Proof component | Embedding | Rationale |
|----------------|-----------|-----------|
| Structural equivalences | **Deep** | Syntactic code equality, no distribution reasoning |
| Package separation/composition | **Deep** | `DeepPackage.sep`, `par`, nominal `atomSep` |
| Game-hopping (coupling, bijection) | **Shallow** | `rHoare`, `liftR`, `SDistr` reasoning |
| FEL / probability bounds | **Shallow** | `pHoare`, `prEventComp`, `failure_event_lemma` |
| Hybrid arguments | **Shallow** | `ssprove_triangle`, `advantage_sum` |
| Oracle invariants | **Shallow** | `pHoare` with heap predicates |

### Typical Proof Flow

```
1. Define games in the deep embedding (RawCode)
   - Use ValidCode to track location access

2. Prove structural equivalences by code equality (deep)
   - These are definitional equalities: c₁ = c₂
   - No distribution reasoning needed

3. Use eval to move to the shallow embedding
   - `ssprove_deep_to_shallow` unfolds DeepRHoare + simplifies eval
   - Or unfold DeepRHoare manually and use eval simp lemmas

4. Prove coupling/FEL/hybrid arguments (shallow)
   - Use `ssprove_sync` for synchronized operations
   - Use `ssprove_sync_bij f` for bijection couplings
   - Use `ssprove_triangle` for game-hopping chains
   - Use `failure_event_lemma` for probability bounds

5. Combine via triangle inequality
   - `ssprove_triangle G₀ [G₁, ..., Gₙ₋₁] Gₙ`
```

### Example: PRF Security

```
-- Deep embedding: define real and ideal games
def game_real : RawCode Bool := do ...  -- uses PRF
def game_ideal : RawCode Bool := do ... -- uses random function

-- Structural: show game decomposition
theorem decomp : game_real = game₁ ∘ game₂ := rfl

-- Shallow: prove coupling
theorem coupling : rHoare eqPre game_real.eval game_ideal.eval eqPost := by
  ssprove_deep_to_shallow
  ssprove_sync
  ...
```

### When to Use the Deep Embedding

1. **Code equality proofs**: When two programs are syntactically equal
   after unfolding definitions, the deep embedding makes this obvious.

2. **Dead code elimination**: Removing unused variables or computations.
   Use `ssprove_dead_code` after moving to shallow.

3. **Inlining**: Substituting definitions. The deep embedding's free monad
   structure makes this straightforward.

4. **Package composition**: When combining packages via `par` or `link`,
   the deep embedding's `DeepPackage` structure handles location tracking.

### When to Use the Shallow Embedding

1. **Distribution reasoning**: Any proof that involves probability
   distributions, expectations, or couplings.

2. **Invariant proofs**: When you need to track heap properties across
   operations using `rHoare` with custom preconditions.

3. **Hybrid arguments**: The triangle inequality and advantage chains
   work on `SPComp` terms in the shallow embedding.

4. **FEL (Failure Event Lemma)**: Bounding advantage via event probability.

### Lessons from the 2025 Paper

The Dupressoir et al. paper showed:

1. **Game-playing** style is easier to formalize when tool automation is good.
   In EasyCrypt, `proc`/`sim`/`auto` work directly on game code.

2. **SSP** style is more modular but harder to formalize because tools
   don't understand package composition ("externalization" is tedious).

3. **Blended** combines the best of both: SSP-style definitions with
   game-playing-style proofs.

Our implementation follows option 3. The bridge library (`CatCrypt.Deep.Bridge`)
enables seamless movement between embeddings.

### Practical Tips

- **Start in the shallow embedding** unless you need structural reasoning.
  Most crypto proofs are about distribution properties.

- **Use `ssprove_code_simpl`** early to normalize SPComp terms before
  applying relational rules.

- **Don't implement full package algebra first** (unlike Rocq SSProve).
  Instead, prove structural equivalences directly as program equalities.

- **For CryptoBox-style proofs**: Define the monolithic oracle in the
  shallow embedding, then decompose into sub-oracles as needed.

## See Also

* `CatCrypt.Deep.Bridge` - Bridge library for moving between embeddings
* `CatCrypt.Deep.Eval` - Deep→Shallow evaluation
* `CatCrypt.Tactics` - Tactic automation for proofs
* `CatCrypt.Examples.Cryptobox` - CryptoBox case study
-/
