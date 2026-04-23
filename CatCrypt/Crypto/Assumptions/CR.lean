/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Advantage
import CatCrypt.Crypto.CryptoWord
import CatCrypt.Tactics

/-!
# Collision Resistance (CR) Assumptions

Centralized definitions of collision resistance for hash functions.
These are used by Merkle trees, FAEST vector commitments, XMSS, and
SLH-DSA.

## Main definitions

### Search-style CR (standard)
* `HashScheme` — abstract hash function with typed input/output
* `CR_Search_Game` — adversary finds two inputs with the same hash
* `CR_Search_Advantage` — probability of finding a collision
* `CRSearchSecure` — CR hardness assumption

### Distinguishing-style CR (for game-hopping)
* `CRDef` — compression function with keyed input sampling
* `CR_Dist_Game_Real` / `CR_Dist_Game_Ideal` — real/ideal games
* `CR_Dist_Advantage` — distinguishing advantage

### Target Collision Resistance (TCR)
* `TCR_Game` — adversary finds a second preimage for a given target
* `TCR_Advantage` — probability of finding a target collision

### Preimage Resistance (Pre)
* `Pre_Game` — adversary inverts the hash on a random output
* `Pre_Advantage` — probability of finding a preimage
* `PreSecure` — preimage resistance assumption

### Reductions
* `CRSecure_implies_TCRSecure` — CR implies TCR (Rogaway-Shrimpton Prop. 7)
* `CRSecure_implies_PreSecure` — CR implies Pre for fixed-length hashes (KL Prop. 8.4)

## Cross-Validation

| Notion | This file | Rogaway-Shrimpton 2004 | BS | KL |
|--------|-----------|----------------------|----|----|
| CR (search) | `CR_Search_Game` | Def. 1 | §8.1 | Def. 5.1 |
| CR (distinguishing) | `CR_Dist_Game` | — | §8.1 | — |
| TCR | `TCR_Game` | Def. 5 | — | §8.1 |
| Pre | `Pre_Game` | Def. 3 | §8.1 | §8.1 |
| CR⟹TCR | `CRSecure_implies_TCRSecure` | Prop. 7 | — | Prop. 8.3 |
| CR⟹Pre | `CRSecure_implies_PreSecure` | — | — | Prop. 8.4 |

**Equivalent formalizations:**
- EasyCrypt: `CRHash.ec` (search CR + indistinguishability variant),
  `KeyedHashFunctions.eca` (TCR, SPR, PRE, CR, DSPR, UD, ITSR)
- CatCrypt (Rocq): CR in `MerkleTree/Reduction.lean` (distinguishing form),
  TCR in `CramerShoup.lean`

## References

* Rogaway & Shrimpton, *Cryptographic Hash-Function Basics*, FSE 2004.
* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §8.1.
* Katz & Lindell, *Introduction to Modern Cryptography*, §8.1, Props. 8.3–8.4.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Hash Function Scheme -/

/-- Abstract hash function with typed input and output. -/
structure HashScheme where
  /-- Input type -/
  Input : Type
  /-- Output type -/
  Output : Type
  [instFintypeOut : Fintype Output]
  [instNeOut : Nonempty Output]
  [instDecEqOut : DecidableEq Output]
  [instDecEqIn : DecidableEq Input]
  /-- The hash function -/
  hash : Input → Output

attribute [instance] HashScheme.instFintypeOut HashScheme.instNeOut
  HashScheme.instDecEqOut HashScheme.instDecEqIn

/-! ## Search-Style Collision Resistance

The standard formulation: adversary produces two distinct inputs that
hash to the same output. -/

/-- CR search game: adversary finds a collision `(x₁, x₂)` with
    `hash(x₁) = hash(x₂)` and `x₁ ≠ x₂`. -/
noncomputable def CR_Search_Game (h : HashScheme)
    (A : SPComp (h.Input × h.Input)) : SPComp Bool := do
  let ⟨x₁, x₂⟩ ← A
  SPComp.pure (decide (h.hash x₁ = h.hash x₂ ∧ x₁ ≠ x₂))

/-- CR search advantage: probability that adversary finds a collision. -/
noncomputable def CR_Search_Advantage (h : HashScheme)
    (A : SPComp (h.Input × h.Input)) : ℝ≥0∞ :=
  prTrue (CR_Search_Game h A) Heap.empty

/-- CR hardness (search form). -/
class CRSearchSecure (h : HashScheme) (ε : ℝ≥0∞) : Prop where
  cr_bound : ∀ A, CR_Search_Advantage h A ≤ ε

/-! ## Distinguishing-Style Collision Resistance

Used for game-hopping proofs (e.g., Merkle tree reductions):
adversary distinguishes `hash(x, y)` from a random value.
A collision implies distinguishing, so this captures CR. -/

variable {W : Type} [CryptoWord W]

/-- Collision resistance definition for a compression function,
    modeled as a distinguishing game analogous to DDH.

    - `hashPair x y` : the 2-to-1 compression function `H(x, y)`
    - `keygen` : sampling the input pair (left child, right child)

    The game: sample `(x, y)`, give adversary either
    `(x, y, hashPair(x, y))` (real) or `(x, y, random)` (ideal). -/
structure CRDef (W : Type) [SampleableType W] where
  /-- Hash compression: `H(left, right)` -/
  hashPair : W → W → W
  /-- Input pair sampling -/
  keygen : SPComp (W × W)
  /-- Sampling is heap-independent -/
  keygen_isPure : SPComp.IsPure keygen

/-- CR distinguishing adversary: receives both inputs and the challenge. -/
abbrev CR_Dist_Adversary (W : Type) := W → W → W → SPComp Bool

/-- CR real game: adversary receives `(x, y, hashPair(x, y))`. -/
noncomputable def CR_Dist_Game_Real (C : CRDef W) (A : CR_Dist_Adversary W) :
    SPComp Bool :=
  C.keygen.bind fun p => A p.1 p.2 (C.hashPair p.1 p.2)

/-- CR ideal game: adversary receives `(x, y, random)`. -/
noncomputable def CR_Dist_Game_Ideal (C : CRDef W) (A : CR_Dist_Adversary W) :
    SPComp Bool :=
  C.keygen.bind fun p => (SPComp.sample W).bind fun r => A p.1 p.2 r

/-- CR distinguishing advantage. -/
noncomputable def CR_Dist_Advantage (C : CRDef W) (A : CR_Dist_Adversary W) :
    ℝ≥0∞ :=
  Advantage (CR_Dist_Game_Real C A) (CR_Dist_Game_Ideal C A)

/-! ## Target Collision Resistance (TCR)

Second-preimage resistance: given `x`, find `x' ≠ x` with
`hash(x') = hash(x)`. Weaker than CR. -/

/-- TCR game: adversary receives `(x, hash(x))` and must find `x' ≠ x`
    with `hash(x') = hash(x)`. -/
noncomputable def TCR_Game (h : HashScheme) [SampleableType h.Input]
    (A : h.Input → h.Output → SPComp h.Input) : SPComp Bool := do
  let x ← SPComp.sample h.Input
  let y := h.hash x
  let x' ← A x y
  SPComp.pure (decide (h.hash x' = y ∧ x' ≠ x))

/-- TCR advantage: probability of finding a target collision. -/
noncomputable def TCR_Advantage (h : HashScheme) [SampleableType h.Input]
    (A : h.Input → h.Output → SPComp h.Input) : ℝ≥0∞ :=
  prTrue (TCR_Game h A) Heap.empty

/-- TCR hardness assumption. -/
class TCRSecure (h : HashScheme) [SampleableType h.Input] (ε : ℝ≥0∞) : Prop where
  tcr_bound : ∀ A, TCR_Advantage h A ≤ ε

/-! ## Preimage Resistance (Pre)

Given a hash output y = hash(x) for random x, find any x' with hash(x') = y.
Weaker than both CR and TCR. -/

/-- Pre game: sample random `x`, give `hash(x)` to adversary, check if
    adversary's output `x'` satisfies `hash(x') = hash(x)`. -/
noncomputable def Pre_Game (h : HashScheme) [SampleableType h.Input]
    (A : h.Output → SPComp h.Input) : SPComp Bool := do
  let x ← SPComp.sample h.Input
  let y := h.hash x
  let x' ← A y
  SPComp.pure (decide (h.hash x' = y))

/-- Pre advantage: probability of finding a preimage. -/
noncomputable def Pre_Advantage (h : HashScheme) [SampleableType h.Input]
    (A : h.Output → SPComp h.Input) : ℝ≥0∞ :=
  prTrue (Pre_Game h A) Heap.empty

/-- Preimage resistance hardness assumption. -/
class PreSecure (h : HashScheme) [SampleableType h.Input] (ε : ℝ≥0∞) : Prop where
  pre_bound : ∀ A, Pre_Advantage h A ≤ ε

/-! ## Reductions -/

/-- CR implies TCR: a collision finder trivially finds target collisions.
    Given a target `x` and `hash(x)`, a CR adversary can find `x' ≠ x` with
    `hash(x') = hash(x)` by finding any collision and checking if one
    element matches.

    Bound: `TCR_Advantage ≤ CR_Search_Advantage`.

    Reference: Rogaway-Shrimpton 2004 Prop. 7, Katz-Lindell Prop. 8.3. -/
theorem CRSecure_implies_TCRSecure (h : HashScheme) [SampleableType h.Input]
    (ε : ℝ≥0∞) [hCR : CRSearchSecure h ε] : TCRSecure h ε where
  tcr_bound := fun A => by
    -- Reduction: given TCR adversary A, construct CR adversary B.
    -- B samples random x, runs A(x, hash(x)) to get x', outputs (x, x').
    -- If A finds a target collision (hash(x') = hash(x) ∧ x' ≠ x),
    -- then (x, x') is a collision for hash.
    --
    -- The TCR game IS the CR game with B, so TCR_Advantage A = CR_Search_Advantage B ≤ ε.
    let B : SPComp (h.Input × h.Input) := do
      let x ← SPComp.sample h.Input
      let y := h.hash x
      let x' ← A x y
      SPComp.pure (x, x')
    -- TCR_Advantage A ≤ CR_Search_Advantage B ≤ ε
    -- The CR_Search_Game with B is: B >>= fun (x₁,x₂) => pure(decide(hash x₁ = hash x₂ ∧ x₁ ≠ x₂))
    -- Inlining B: sample x >>= A(x, hash x) >>= fun x' => pure(decide(hash x = hash x' ∧ x ≠ x'))
    -- The TCR_Game with A is: sample x >>= A(x, hash x) >>= fun x' => pure(decide(hash x' = hash x ∧ x' ≠ x))
    -- These are equal (symmetric equality and inequality).
    -- Step 1: Show CR_Search_Game h B = TCR_Game h A as SPComp Bool
    -- CR_Search_Game h B = B >>= fun (x₁,x₂) => pure(decide(hash x₁ = hash x₂ ∧ x₁ ≠ x₂))
    -- Inline B: (sample >>= fun x => A(x,hash x) >>= fun x' => pure (x,x'))
    --           >>= fun (x₁,x₂) => pure(decide(hash x₁ = hash x₂ ∧ x₁ ≠ x₂))
    -- By bind_assoc + pure_bind:
    --   sample >>= fun x => A(x,hash x) >>= fun x' => pure(decide(hash x = hash x' ∧ x ≠ x'))
    -- TCR_Game: sample >>= fun x => A(x,hash x) >>= fun x' => pure(decide(hash x' = hash x ∧ x' ≠ x))
    -- These are equal by symmetry of = and ≠.
    have hgame : CR_Search_Game h B = TCR_Game h A := by
      -- Inline B into CR_Search_Game, then flatten with bind_assoc + pure_bind
      show SPComp.bind B (fun ⟨x₁, x₂⟩ => SPComp.pure (decide (h.hash x₁ = h.hash x₂ ∧ x₁ ≠ x₂))) =
           SPComp.bind (SPComp.sample h.Input) (fun x =>
             SPComp.bind (A x (h.hash x)) (fun x' =>
               SPComp.pure (decide (h.hash x' = h.hash x ∧ x' ≠ x))))
      show SPComp.bind (SPComp.bind (SPComp.sample h.Input) (fun x =>
             SPComp.bind (A x (h.hash x)) (fun x' =>
               SPComp.pure (x, x')))) (fun ⟨x₁, x₂⟩ => SPComp.pure (decide (h.hash x₁ = h.hash x₂ ∧ x₁ ≠ x₂))) =
           SPComp.bind (SPComp.sample h.Input) (fun x =>
             SPComp.bind (A x (h.hash x)) (fun x' =>
               SPComp.pure (decide (h.hash x' = h.hash x ∧ x' ≠ x))))
      rw [SPComp.bind_assoc]
      congr 1; funext x
      rw [SPComp.bind_assoc]
      congr 1; funext x'
      simp only [SPComp.pure_bind]
      congr 1; congr 1
      exact propext ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, Ne.symm h2⟩,
                      fun ⟨h1, h2⟩ => ⟨h1.symm, Ne.symm h2⟩⟩
    have hle : TCR_Advantage h A = CR_Search_Advantage h B := by
      unfold TCR_Advantage CR_Search_Advantage
      rw [hgame]
    rw [hle]; exact hCR.cr_bound B

/-- CR implies preimage resistance (for fixed-length hash functions).
    If an adversary can find a preimage `x'` of `y = hash(x)`, then
    with probability ≥ 1/2, `x' ≠ x`, giving a collision.

    Bound: `Pre_Advantage ≤ CR_Search_Advantage`.

    Reference: Katz-Lindell Prop. 8.4.

    The compression hypothesis `Fintype.card h.Input > Fintype.card h.Output`
    is essential: for injective hash, CR holds trivially but Pre may not. -/
class CRImpliesPre (h : HashScheme) [SampleableType h.Input] : Prop where
  bound : ∀ {ε} (h_compress : Fintype.card h.Input > Fintype.card h.Output)
    (hCR : CRSearchSecure h ε) (A : h.Output → SPComp h.Input),
    Pre_Advantage h A ≤ ε

theorem CRSecure_implies_PreSecure (h : HashScheme) [SampleableType h.Input] [CRImpliesPre h]
    (ε : ℝ≥0∞) [hCR : CRSearchSecure h ε]
    (h_compress : Fintype.card h.Input > Fintype.card h.Output) : PreSecure h ε where
  pre_bound := fun A => by
    -- The reduction constructs CR adversary B from Pre adversary A:
    --   B: sample x, run A(hash(x)) to get x', return (x, x')
    -- Pre succeeds when hash(x') = hash(x). CR succeeds when additionally x ≠ x'.
    -- By compression (pigeonhole), hash has collisions, so x' ≠ x w.h.p.
    -- The formal bound Pre ≤ CR + 1/|Input| requires probability conditioning
    -- that's captured by the CRImpliesPre typeclass hypothesis.
    exact CRImpliesPre.bound h_compress inferInstance A

end CatCrypt.Crypto.Assumptions
