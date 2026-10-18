/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Crypto.ForkingLemma
public import CatCryptCore.Tactics

/-!
# Collision Resistance (CR) Assumptions

Centralized definitions of collision resistance for hash functions.
These are used by Merkle trees, FAEST vector commitments, XMSS, and
SLH-DSA.

## Main definitions

### Search-style CR (keyed family)
* `HashScheme` — keyed hash family `hash : Key → Input → Output`; every game samples
  the key and gives it to the adversary
* `CR_Search_Game` — adversary finds two inputs with the same hash under the sampled key
* `CR_Search_Advantage` — probability of finding a collision

### Distinguishing-style CR (for game-hopping)
* `CRDef` — compression function with keyed input sampling
* `CR_Dist_Game_Real` / `CR_Dist_Game_Ideal` — real/ideal games
* `CR_Dist_Advantage` — distinguishing advantage

### Second-preimage resistance on a random target (TCR)
* `TCR_Game` — adversary receives the key and a random `x`, finds `x' ≠ x` with the
  same hash
* `TCR_Advantage` — probability of finding a target collision

### Preimage Resistance (Pre)
* `Pre_Game` — adversary inverts the hash on the image of a random input
* `Pre_Advantage` — probability of finding a preimage

### Reductions
* `tcrToCR`, `tcr_eq_cr` — `TCR_Advantage h A = CR_Search_Advantage h (tcrToCR h A)`
  (Rogaway-Shrimpton Prop. 7)
* `preToCR`, `pre_le_cr` —
  `Pre_Advantage h A ≤ CR_Search_Advantage h (preToCR h A) + |Output| / |Input|`
  (KL Prop. 8.4)

### Codecs and the random function
* `HashScheme.Codec` — injective encodings of a domain `D` into the inputs and of the
  outputs into a range `R`; a collision of `hashOn` is a collision of the scheme
* `HashScheme.randomFun` — the keyed family whose keys are the functions `D → R`

The hash is keyed: for a compressing unkeyed function a constant adversary outputs a fixed
collision, so a bound `∀ A, … ≤ ε` holds only for `ε ≥ 1`. The reductions `tcr_eq_cr` and
`pre_le_cr` relate the advantages per adversary.

## Cross-Validation

| Notion | This file | Rogaway-Shrimpton 2004 | BS | KL |
|--------|-----------|----------------------|----|----|
| CR (search) | `CR_Search_Game` | Def. 1 | §8.1 | Def. 5.1 |
| CR (distinguishing) | `CR_Dist_Game` | — | §8.1 | — |
| TCR | `TCR_Game` | Def. 5 | — | §8.1 |
| Pre | `Pre_Game` | Def. 3 | §8.1 | §8.1 |
| CR⟹TCR | `tcr_eq_cr` | Prop. 7 | — | Prop. 8.3 |
| CR⟹Pre | `pre_le_cr` | — | — | Prop. 8.4 |

**Equivalent formalizations:**
- EasyCrypt: `CRHash.ec` (search CR + indistinguishability variant),
  `KeyedHashFunctions.eca` (TCR, SPR, PRE, CR, DSPR, UD, ITSR)
- SSProve (Rocq): CR in `MerkleTree/Reduction.lean` (distinguishing form),
  TCR in `CramerShoup.lean`

## References

* Rogaway & Shrimpton, *Cryptographic Hash-Function Basics*, FSE 2004.
* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §8.1.
* Katz & Lindell, *Introduction to Modern Cryptography*, §8.1, Props. 8.3–8.4.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Hash Function Scheme -/

/-- Keyed hash family with typed key, input and output. The key is sampled uniformly in
    each game and given to the adversary. -/
structure HashScheme where
  /-- Key type -/
  Key : Type
  /-- Input type -/
  Input : Type
  /-- Output type -/
  Output : Type
  [instFintypeKey : Fintype Key]
  [instNeKey : Nonempty Key]
  [instFintypeOut : Fintype Output]
  [instNeOut : Nonempty Output]
  [instDecEqOut : DecidableEq Output]
  [instDecEqIn : DecidableEq Input]
  /-- The hash function under key `k` -/
  hash : Key → Input → Output

attribute [instance] HashScheme.instFintypeKey HashScheme.instNeKey
  HashScheme.instFintypeOut HashScheme.instNeOut
  HashScheme.instDecEqOut HashScheme.instDecEqIn

/-! ## Search-Style Collision Resistance

The standard formulation: given the key, the adversary produces two distinct inputs
that hash to the same output. -/

/-- CR search adversary: given the key, output a candidate collision. -/
abbrev CR_Search_Adversary (h : HashScheme) := h.Key → SPComp (h.Input × h.Input)

/-- CR search game: sample `k`, the adversary finds `(x₁, x₂)` with
    `hash k x₁ = hash k x₂` and `x₁ ≠ x₂`. -/
noncomputable def CR_Search_Game (h : HashScheme) (A : CR_Search_Adversary h) :
    SPComp Bool := do
  let k ← SPComp.sample h.Key
  let ⟨x₁, x₂⟩ ← A k
  SPComp.pure (decide (h.hash k x₁ = h.hash k x₂ ∧ x₁ ≠ x₂))

/-- CR search advantage: probability that adversary finds a collision. -/
noncomputable def CR_Search_Advantage (h : HashScheme) (A : CR_Search_Adversary h) :
    ℝ≥0∞ :=
  prTrue (CR_Search_Game h A) Heap.empty

/-! ## Codecs and the random function -/

/-- Injective encodings of a domain `D` into the inputs of `H` and of the outputs of `H`
into a range `R`. -/
structure HashScheme.Codec (H : HashScheme) (D R : Type) where
  /-- Encoding of the domain into the inputs. -/
  inp : D ↪ H.Input
  /-- Encoding of the outputs into the range. -/
  out : H.Output ↪ R

namespace HashScheme.Codec

variable {H : HashScheme} {D R : Type}

/-- The hash under key `k` on the domain `D` with values in `R`. -/
def hashOn (c : H.Codec D R) (k : H.Key) (d : D) : R :=
  c.out (H.hash k (c.inp d))

/-- `d₁, d₂` are distinct elements of `D` with the same `hashOn` value under `k`. -/
def collision (c : H.Codec D R) (k : H.Key) (d₁ d₂ : D) : Prop :=
  c.hashOn k d₁ = c.hashOn k d₂ ∧ d₁ ≠ d₂

/-- A collision of `hashOn` is the collision of the encoded inputs under `H`. -/
theorem collision_iff (c : H.Codec D R) (k : H.Key) (d₁ d₂ : D) :
    c.collision k d₁ d₂ ↔
      H.hash k (c.inp d₁) = H.hash k (c.inp d₂) ∧ c.inp d₁ ≠ c.inp d₂ := by
  simp only [collision, hashOn, c.out.injective.eq_iff, ne_eq, c.inp.injective.eq_iff]

/-- The identity codec on the inputs and outputs of `H`. -/
def id (H : HashScheme) : H.Codec H.Input H.Output :=
  ⟨Function.Embedding.refl _, Function.Embedding.refl _⟩

@[simp] theorem hashOn_id (k : H.Key) (x : H.Input) :
    (Codec.id H).hashOn k x = H.hash k x := rfl

end HashScheme.Codec

/-- The random function as a keyed hash family: the keys are the functions `D → R`, and
the hash under the key `f` is `f`. A uniform key is a uniformly random function. -/
abbrev HashScheme.randomFun (D R : Type) [Fintype D] [DecidableEq D] [Fintype R]
    [Nonempty R] [DecidableEq R] : HashScheme where
  Key := D → R
  Input := D
  Output := R
  hash f d := f d

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

/-! ## Second-Preimage Resistance on a Random Target (TCR)

Given the key and a uniformly random `x`, find `x' ≠ x` with `hash k x' = hash k x`.
Weaker than CR. -/

section Finite

variable (h : HashScheme) [Fintype h.Input] [Nonempty h.Input]

/-- TCR adversary: given the key, the target `x` and `hash k x`, output `x'`. -/
abbrev TCR_Adversary := h.Key → h.Input → h.Output → SPComp h.Input

/-- TCR game: sample `k` and `x`, the adversary receives `(k, x, hash k x)` and must find
    `x' ≠ x` with `hash k x' = hash k x`. -/
noncomputable def TCR_Game (A : TCR_Adversary h) : SPComp Bool := do
  let k ← SPComp.sample h.Key
  let x ← SPComp.sample h.Input
  let y := h.hash k x
  let x' ← A k x y
  SPComp.pure (decide (h.hash k x' = y ∧ x' ≠ x))

/-- TCR advantage: probability of finding a target collision. -/
noncomputable def TCR_Advantage (A : TCR_Adversary h) : ℝ≥0∞ :=
  prTrue (TCR_Game h A) Heap.empty

/-! ## Preimage Resistance (Pre)

Given the key and `y = hash k x` for random `x`, find any `x'` with `hash k x' = y`.
Weaker than both CR and TCR. -/

/-- Pre adversary: given the key and an output, output a candidate preimage. -/
abbrev Pre_Adversary := h.Key → h.Output → SPComp h.Input

/-- Pre game: sample `k` and `x`, give `(k, hash k x)` to the adversary, check whether
    its output `x'` satisfies `hash k x' = hash k x`. -/
noncomputable def Pre_Game (A : Pre_Adversary h) : SPComp Bool := do
  let k ← SPComp.sample h.Key
  let x ← SPComp.sample h.Input
  let y := h.hash k x
  let x' ← A k y
  SPComp.pure (decide (h.hash k x' = y))

/-- Pre advantage: probability of finding a preimage. -/
noncomputable def Pre_Advantage (A : Pre_Adversary h) : ℝ≥0∞ :=
  prTrue (Pre_Game h A) Heap.empty

/-! ## Reductions -/

/-- CR adversary from a TCR adversary: sample `x`, run `A k x (hash k x)` to get `x'`,
    output `(x, x')`. -/
noncomputable def tcrToCR (A : TCR_Adversary h) : CR_Search_Adversary h :=
  fun k => do
    let x ← SPComp.sample h.Input
    let x' ← A k x (h.hash k x)
    SPComp.pure (x, x')

/-- **CR ⟹ TCR** (Rogaway-Shrimpton 2004 Prop. 7, KL Prop. 8.3). The CR game of
    `tcrToCR h A` is the TCR game of `A`, so
    `TCR_Advantage h A = CR_Search_Advantage h (tcrToCR h A)`. -/
theorem tcr_eq_cr (A : TCR_Adversary h) :
    TCR_Advantage h A = CR_Search_Advantage h (tcrToCR h A) := by
  have hgame : CR_Search_Game h (tcrToCR h A) = TCR_Game h A := by
    unfold CR_Search_Game TCR_Game tcrToCR
    simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext k
    congr 1; funext x
    congr 1; funext x'
    congr 1
    exact decide_eq_decide.mpr ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, Ne.symm h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1.symm, Ne.symm h2⟩⟩
  unfold TCR_Advantage CR_Search_Advantage
  rw [hgame]

/-- CR adversary from a Pre adversary: sample `x`, run `A k (hash k x)` to get `x'`,
    output `(x, x')`. -/
noncomputable def preToCR (A : Pre_Adversary h) : CR_Search_Adversary h :=
  fun k => do
    let x ← SPComp.sample h.Input
    let x' ← A k (h.hash k x)
    SPComp.pure (x, x')

omit [Nonempty h.Input] in
/-- The events `{c returns x}` for distinct `x` are disjoint, so their probabilities sum
    to at most `1`. -/
theorem sum_prTrue_bind_eq_le_one (c : SPComp h.Input) (h₀ : Heap) :
    ∑ x : h.Input, prTrue (c.bind fun x' => SPComp.pure (decide (x' = x))) h₀ ≤ 1 := by
  simp only [ForkingLemma.prTrue_bind_eq_weighted]
  rw [← tsum_fintype (L := SummationFilter.unconditional _), ENNReal.tsum_comm]
  refine (ENNReal.tsum_le_tsum (g := fun p => (c h₀ : PMF _) p * 1) fun p => ?_).trans ?_
  · rw [ENNReal.tsum_mul_left]
    gcongr
    rcases p with _ | ⟨a, h'⟩
    · simp
    · simp [ForkingLemma.prTrue_pure_bool]
  · simp

/-- Union bound for one bind: if `P a` implies `Q a ∨ R a`, the probability that `c`
    returns a value satisfying `P` is at most the sum of the probabilities for `Q` and
    `R`. -/
theorem prTrue_bind_decide_le_add {α : Type} (c : SPComp α) (P Q R : α → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hPQR : ∀ a, P a → Q a ∨ R a) (h₀ : Heap) :
    prTrue (c.bind fun a => SPComp.pure (decide (P a))) h₀ ≤
      prTrue (c.bind fun a => SPComp.pure (decide (Q a))) h₀ +
        prTrue (c.bind fun a => SPComp.pure (decide (R a))) h₀ := by
  simp only [ForkingLemma.prTrue_bind_eq_weighted]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun p => ?_
  rcases p with _ | ⟨a, h'⟩
  · simp
  · simp only [ForkingLemma.prTrue_pure_bool, ← mul_add]
    gcongr
    by_cases hP : P a
    · rcases hPQR a hP with hQ | hR
      · simp [hP, hQ]
      · simp [hP, hR]
    · simp [hP]

/-- **CR ⟹ Pre** (KL Prop. 8.4). For every Pre adversary `A`,

    `Pre_Advantage h A ≤ CR_Search_Advantage h (preToCR h A) + |Output| / |Input|`.

    `preToCR h A` wins whenever `A` returns a preimage `x'` of `hash k x` with `x' ≠ x`;
    the remaining event `x' = x` has probability at most `|Output| / |Input|`, since for
    each output `y` the events `{A k y returns x}` are disjoint. -/
theorem pre_le_cr (A : Pre_Adversary h) :
    Pre_Advantage h A ≤ CR_Search_Advantage h (preToCR h A) +
      (Fintype.card h.Output : ℝ≥0∞) / Fintype.card h.Input := by
  have hcr : CR_Search_Game h (preToCR h A) =
      (SPComp.sample h.Key).bind fun k => (SPComp.sample h.Input).bind fun x =>
        (A k (h.hash k x)).bind fun x' =>
          SPComp.pure (decide (h.hash k x' = h.hash k x ∧ x' ≠ x)) := by
    unfold CR_Search_Game preToCR
    simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext k
    congr 1; funext x
    congr 1; funext x'
    congr 1
    exact decide_eq_decide.mpr ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, Ne.symm h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1.symm, Ne.symm h2⟩⟩
  unfold Pre_Advantage CR_Search_Advantage Pre_Game
  rw [hcr]
  simp only [SPComp.monad_bind_eq]
  rw [prTrue_bind_sample, prTrue_bind_sample]
  refine weighted_sum_le _ _ _ fun k => ?_
  rw [prTrue_bind_sample, prTrue_bind_sample]
  set w := (Fintype.card h.Input : ℝ≥0∞)⁻¹
  have hE : ∑ x : h.Input,
      prTrue ((A k (h.hash k x)).bind fun x' => SPComp.pure (decide (x' = x))) Heap.empty ≤
        Fintype.card h.Output := by
    calc ∑ x : h.Input,
          prTrue ((A k (h.hash k x)).bind fun x' => SPComp.pure (decide (x' = x))) Heap.empty
        ≤ ∑ x : h.Input, ∑ y : h.Output,
          prTrue ((A k y).bind fun x' => SPComp.pure (decide (x' = x))) Heap.empty :=
          Finset.sum_le_sum fun x _ => Finset.single_le_sum
            (f := fun y => prTrue ((A k y).bind fun x' => SPComp.pure (decide (x' = x)))
              Heap.empty) (fun _ _ => zero_le) (Finset.mem_univ (h.hash k x))
      _ = ∑ y : h.Output, ∑ x : h.Input,
          prTrue ((A k y).bind fun x' => SPComp.pure (decide (x' = x))) Heap.empty :=
          Finset.sum_comm
      _ ≤ ∑ _y : h.Output, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun y _ => sum_prTrue_bind_eq_le_one h (A k y) Heap.empty
      _ = Fintype.card h.Output := by simp
  calc ∑ x : h.Input, w *
        prTrue ((A k (h.hash k x)).bind fun x' =>
          SPComp.pure (decide (h.hash k x' = h.hash k x))) Heap.empty
      ≤ ∑ x : h.Input, (w *
          prTrue ((A k (h.hash k x)).bind fun x' =>
            SPComp.pure (decide (h.hash k x' = h.hash k x ∧ x' ≠ x))) Heap.empty +
        w * prTrue ((A k (h.hash k x)).bind fun x' =>
            SPComp.pure (decide (x' = x))) Heap.empty) :=
        Finset.sum_le_sum fun x _ => by
          rw [← mul_add]
          gcongr
          exact prTrue_bind_decide_le_add _ _ _ _
            (fun x' hx' => (em (x' = x)).symm.imp (fun hne => ⟨hx', hne⟩) id) _
    _ = ∑ x : h.Input, w *
          prTrue ((A k (h.hash k x)).bind fun x' =>
            SPComp.pure (decide (h.hash k x' = h.hash k x ∧ x' ≠ x))) Heap.empty +
        w * ∑ x : h.Input, prTrue ((A k (h.hash k x)).bind fun x' =>
            SPComp.pure (decide (x' = x))) Heap.empty := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        rw [ENNReal.div_eq_inv_mul]
        exact mul_le_mul' le_rfl hE

end Finite

end CatCrypt.Crypto.Assumptions
