/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.ForkingLemma

/-!
# Tree-forking lemma for multi-round public-coin interactions

This file states and proves the tree-extraction lemma of `(k₁,…,k_μ)`-special
soundness for μ-round public-coin interactions over `SPComp`, with the knowledge
error of Attema–Cramer–Kohl.

## Model

A round (`Round`) has a finite nonempty challenge set `C`, a prover message type
`M` and an arity `k`. A deterministic prover strategy (`Strategy Y rs`) for the
round list `rs` sends a message at each round and, after the last challenge, an
output `Y`. A probabilistic prover is `P : SPComp (Strategy Y rs)`: a distribution
over strategies, which is the random-tape view of a prover that the rewinding
extractor controls. The verifier is a predicate `V : Transcript rs → Y → Bool` on
the full transcript and the final output.

A transcript tree (`Tree Y rs`) of arity `(k₁,…,k_μ)` stores, at a node of round
`i`, the prover message and `kᵢ` children labelled by challenges. It is accepting
(`Tree.Accepting`) when sibling challenges are pairwise distinct and every leaf
satisfies `V` on its root-to-leaf transcript, and it is consistent with a strategy
(`Tree.Consistent`) when every message and output is the strategy's response to
the challenges on its path.

## Extractor

`extract` is the rewinding extractor on a strategy: at a node of round `i` it
rewinds the prover once for each challenge in `Cᵢ` (at most `|Cᵢ|` rewinds per
node, so at most `∏ |Cᵢ|` prover runs in total), keeps the challenges whose
subtree extraction succeeds, and returns a node built from the first `kᵢ` of them
when there are at least `kᵢ`. `treeExtractor P` runs it on a strategy drawn from
`P`. Every output tree is accepting and consistent (`extract_sound`).

## Main results

* `knowledgeError rs = 1 − ∏ᵢ (1 − (kᵢ − 1)/|Cᵢ|)`.
* `runAccept_le` — for a deterministic strategy, the acceptance probability over
  uniform challenges is at most `κ + (1 − κ)·[extract succeeds]`.
* `acceptProb_le` — for a probabilistic prover accepted with probability `ε`,
  `ε ≤ κ + (1 − κ)·Pr[treeExtractor outputs a tree]`.
* `acceptProb_sub_le_mul` / `acceptProb_sub_le` — `ε − κ ≤ (1 − κ)·Pr[tree]
  ≤ Pr[tree]`.
* `knowledgeError_lt_one` — `κ < 1` when every `kᵢ ≤ |Cᵢ|`;
  `extractProb_const_accept` — a prover accepted on every challenge yields a tree
  with probability at least `1 − κ`.
* `forkSuccProb_le_extractProb` — for μ = 1 and k = 2, the two-branch forking
  experiment `ForkingLemma.forkSuccProb` succeeds with probability at most the
  tree extractor's, so `fork_success_ge` gives a second lower bound
  `acc² − acc/|R|` on the same extraction probability (`single_round_extract_ge`).

## References

* [Attema, Cramer, Kohl, *A Compressed Σ-Protocol Theory for Lattices*, CRYPTO 2021]
* [Attema, Fehr, Klooß, *Fiat–Shamir Transformation of Multi-Round Interactive
  Proofs*, TCC 2022]
* [Bootle, Cerulli, Chaidos, Groth, Petit, *Efficient Zero-Knowledge Arguments for
  Arithmetic Circuits in the Discrete Log Setting*, EUROCRYPT 2016]
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.TreeForking

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Rounds, transcripts, strategies and trees -/

/-- One round of a public-coin interaction: the prover sends a message of type `M`,
the verifier answers with a uniform challenge from the finite nonempty set `C`, and
special soundness asks for `k` distinct challenges at this round. -/
structure Round : Type 1 where
  /-- Challenge set. -/
  C : Type
  /-- Prover message type. -/
  M : Type
  /-- Arity of the transcript tree at this round. -/
  k : ℕ
  [fintype : Fintype C]
  [nonempty : Nonempty C]

attribute [instance] Round.fintype Round.nonempty

/-- Full transcript of the rounds `rs`: one message and one challenge per round. -/
def Transcript : List Round → Type
  | [] => Unit
  | r :: rs => r.M × r.C × Transcript rs

variable {Y : Type}

/-- Deterministic prover strategy for the rounds `rs` with final output `Y`: a
message at each round and a continuation per challenge. -/
def Strategy (Y : Type) : List Round → Type
  | [] => Y
  | r :: rs => r.M × (r.C → Strategy Y rs)

/-- Transcript tree of arity `(k₁,…,k_μ)`: a node of round `r` holds the prover
message and `r.k` children, each labelled by a challenge. -/
def Tree (Y : Type) : List Round → Type
  | [] => Y
  | r :: rs => r.M × (Fin r.k → r.C × Tree Y rs)

/-- Acceptance of a transcript tree under the verifier `V`: sibling challenges are
pairwise distinct and every leaf output is accepted on its root-to-leaf
transcript. -/
def Tree.Accepting : (rs : List Round) → (Transcript rs → Y → Bool) → Tree Y rs → Prop
  | [], V, T => V () T = true
  | _ :: rs, V, T =>
      Function.Injective (fun j => (T.2 j).1) ∧
        ∀ j, Tree.Accepting rs (fun t y => V (T.1, (T.2 j).1, t) y) (T.2 j).2

/-- Consistency of a transcript tree with a strategy: each message and output in the
tree is the strategy's response to the challenges on its path. -/
def Tree.Consistent : (rs : List Round) → Tree Y rs → Strategy Y rs → Prop
  | [], T, s => T = s
  | _ :: rs, T, s => T.1 = s.1 ∧ ∀ j, Tree.Consistent rs (T.2 j).2 (s.2 (T.2 j).1)

/-! ## The honest run and the extractor -/

/-- One run of the interaction between a deterministic strategy and the verifier:
uniform challenges at each round, then the output of `V` on the transcript. -/
noncomputable def runAccept : (rs : List Round) → (Transcript rs → Y → Bool) →
    Strategy Y rs → SPComp Bool
  | [], V, s => SPComp.pure (V () s)
  | r :: rs, V, s =>
      SPComp.bind (SPComp.sample r.C) fun c =>
        runAccept rs (fun t y => V (s.1, c, t) y) (s.2 c)

/-- The rewinding tree extractor on a deterministic strategy. At a node of round `r`
it runs the sub-extractor once for every challenge in `r.C`, and succeeds with the
first `r.k` challenges (in the order of `Finset.equivFin`) whose sub-extraction
succeeds, when there are at least `r.k` of them. -/
noncomputable def extract : (rs : List Round) → (Transcript rs → Y → Bool) →
    Strategy Y rs → Option (Tree Y rs)
  | [], V, s => if V () s then some s else none
  | r :: rs, V, s =>
      if h : r.k ≤ (Finset.univ.filter fun c : r.C =>
          (extract rs (fun t y => V (s.1, c, t) y) (s.2 c)).isSome).card then
        some (s.1, fun j =>
          let c := (Finset.equivFin _).symm (Fin.castLE h j)
          (c.1, (extract rs (fun t y => V (s.1, c.1, t) y) (s.2 c.1)).get
            (Finset.mem_filter.mp c.2).2))
      else none

/-- Extraction at a leaf succeeds exactly when `V` accepts. -/
theorem extract_nil_isSome (V : Transcript [] → Y → Bool) (s : Strategy Y []) :
    (extract [] V s).isSome = V () s := by
  unfold extract
  cases V () s <;> rfl

/-- Extraction at a node succeeds exactly when at least `r.k` challenges have a
successful sub-extraction. -/
theorem extract_cons_isSome (r : Round) (rs : List Round)
    (V : Transcript (r :: rs) → Y → Bool) (s : Strategy Y (r :: rs)) :
    (extract (r :: rs) V s).isSome = true ↔
      r.k ≤ (Finset.univ.filter fun c : r.C =>
        (extract rs (fun t y => V (s.1, c, t) y) (s.2 c)).isSome).card := by
  simp only [extract]
  split_ifs with h
  · exact iff_of_true rfl h
  · simp [h]

/-- Every tree output by the extractor is accepting and consistent with the
strategy. -/
theorem extract_sound : ∀ (rs : List Round) (V : Transcript rs → Y → Bool)
    (s : Strategy Y rs) (T : Tree Y rs), extract rs V s = some T →
      T.Accepting rs V ∧ T.Consistent rs s
  | [], V, s, T, hT => by
      simp only [extract] at hT
      split_ifs at hT with hV
      cases hT
      exact ⟨hV, rfl⟩
  | r :: rs, V, s, T, hT => by
      simp only [extract] at hT
      split_ifs at hT with h
      cases hT
      refine ⟨⟨?_, fun j => ?_⟩, rfl, fun j => ?_⟩
      · intro j₁ j₂ hj
        exact (Fin.castLE_injective h) ((Finset.equivFin _).symm.injective
          (Subtype.ext hj))
      · exact (extract_sound rs _ _ _ (Option.some_get _).symm).1
      · exact (extract_sound rs _ _ _ (Option.some_get _).symm).2

/-! ## Knowledge error -/

/-- Per-round survival factor `1 − (k − 1)/|C|`. -/
noncomputable def Round.survival (r : Round) : ℝ≥0∞ :=
  1 - ((r.k - 1 : ℕ) : ℝ≥0∞) / Fintype.card r.C

/-- The product `∏ᵢ (1 − (kᵢ − 1)/|Cᵢ|)`. -/
noncomputable def survival (rs : List Round) : ℝ≥0∞ :=
  (rs.map Round.survival).prod

/-- The Attema–Cramer–Kohl knowledge error `κ = 1 − ∏ᵢ (1 − (kᵢ − 1)/|Cᵢ|)`. -/
noncomputable def knowledgeError (rs : List Round) : ℝ≥0∞ :=
  1 - survival rs

theorem Round.survival_le_one (r : Round) : r.survival ≤ 1 := tsub_le_self

theorem survival_nil : survival [] = 1 := rfl

theorem survival_cons (r : Round) (rs : List Round) :
    survival (r :: rs) = r.survival * survival rs := by
  simp [survival]

theorem survival_le_one : ∀ rs : List Round, survival rs ≤ 1
  | [] => le_rfl
  | r :: rs => by
      rw [survival_cons]
      exact mul_le_one' r.survival_le_one (survival_le_one rs)

theorem knowledgeError_add_survival (rs : List Round) :
    knowledgeError rs + survival rs = 1 :=
  tsub_add_cancel_of_le (survival_le_one rs)

theorem knowledgeError_le_one (rs : List Round) : knowledgeError rs ≤ 1 := tsub_le_self

/-- `κ < 1` when every arity is at most the size of its challenge set. -/
theorem knowledgeError_lt_one (rs : List Round)
    (hk : ∀ r ∈ rs, r.k ≤ Fintype.card r.C) : knowledgeError rs < 1 := by
  have hpos : ∀ rs : List Round, (∀ r ∈ rs, r.k ≤ Fintype.card r.C) →
      survival rs ≠ 0 := by
    intro rs
    induction rs with
    | nil => intro _; simp [survival_nil]
    | cons r rs ih =>
      intro hk
      rw [survival_cons]
      refine mul_ne_zero ?_ (ih fun r' hr' => hk r' (List.mem_cons_of_mem _ hr'))
      have hN : (0 : ℝ≥0∞) < Fintype.card r.C := by
        exact_mod_cast Fintype.card_pos
      have hlt : ((r.k - 1 : ℕ) : ℝ≥0∞) < Fintype.card r.C := by
        have := hk r List.mem_cons_self
        have : r.k - 1 < Fintype.card r.C := by
          have := Fintype.card_pos (α := r.C); omega
        exact_mod_cast this
      have hdiv : ((r.k - 1 : ℕ) : ℝ≥0∞) / Fintype.card r.C < 1 :=
        (ENNReal.div_lt_iff (Or.inl hN.ne') (Or.inl (ENNReal.natCast_ne_top _))).mpr
          (by simpa using hlt)
      exact (tsub_pos_of_lt hdiv).ne'
  unfold knowledgeError
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (hpos rs hk)

/-- For a single round of arity 2 the knowledge error is `1/|C|`. -/
theorem knowledgeError_single_two (C : Type) [Fintype C] [Nonempty C] (M : Type) :
    knowledgeError [{ C := C, M := M, k := 2 }] = (Fintype.card C : ℝ≥0∞)⁻¹ := by
  simp only [knowledgeError, survival_cons, survival_nil, mul_one, Round.survival]
  have hle : (Fintype.card C : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]; exact_mod_cast Fintype.card_pos
  simp only [Nat.add_one_sub_one, Nat.cast_one, one_div]
  exact ENNReal.sub_sub_cancel ENNReal.one_ne_top hle

/-! ## The deterministic bound -/

/-- Averaging a bound over a uniform challenge: `∑_c |C|⁻¹ · [c ∈ S] = |S|/|C|`. -/
theorem sum_inv_mul_indicator (C : Type) [Fintype C] [Nonempty C] (p : C → Bool) :
    ∑ c : C, (Fintype.card C : ℝ≥0∞)⁻¹ * (if p c = true then 1 else 0) =
      ((Finset.univ.filter fun c => p c = true).card : ℝ≥0∞) / Fintype.card C := by
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ENNReal.div_eq_inv_mul,
    mul_comm]

/-- **Deterministic tree-extraction bound.** For every strategy, the probability
that `V` accepts over uniform challenges is at most
`κ + (1 − κ) · [extract succeeds]`. -/
theorem runAccept_le : ∀ (rs : List Round) (V : Transcript rs → Y → Bool)
    (s : Strategy Y rs) (h₀ : Heap),
      prTrue (runAccept rs V s) h₀ ≤
        knowledgeError rs + survival rs * (if (extract rs V s).isSome then 1 else 0)
  | [], V, s, h₀ => by
      simp only [runAccept, extract, ForkingLemma.prTrue_pure_bool, knowledgeError,
        survival_nil, tsub_self, one_mul, zero_add]
      split_ifs <;> simp_all
  | r :: rs, V, s, h₀ => by
      simp only [runAccept]
      rw [prTrue_bind_sample]
      set κ' := knowledgeError rs
      set σ' := survival rs
      set N := (Fintype.card r.C : ℝ≥0∞)
      set p : r.C → Bool := fun c =>
        (extract rs (fun t y => V (s.1, c, t) y) (s.2 c)).isSome with hp
      have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
      have hstep : ∑ c : r.C, N⁻¹ * prTrue (runAccept rs (fun t y => V (s.1, c, t) y)
          (s.2 c)) h₀ ≤ κ' + σ' * ((Finset.univ.filter fun c => p c = true).card / N) := by
        calc _ ≤ ∑ c : r.C, N⁻¹ * (κ' + σ' * (if p c = true then 1 else 0)) :=
              Finset.sum_le_sum fun c _ => mul_le_mul_right (runAccept_le rs _ _ h₀) _
          _ = (∑ c : r.C, N⁻¹ * κ') +
                σ' * ∑ c : r.C, N⁻¹ * (if p c = true then 1 else 0) := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun c _ => ?_
              ring
          _ = κ' + σ' * ((Finset.univ.filter fun c => p c = true).card / N) := by
              rw [sum_inv_mul_indicator, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
                ← mul_assoc, ENNReal.mul_inv_cancel hN0 hNt, one_mul]
      refine hstep.trans ?_
      have hsum : knowledgeError (r :: rs) + survival (r :: rs) = 1 :=
        knowledgeError_add_survival _
      by_cases hex : (extract (r :: rs) V s).isSome = true
      · rw [if_pos hex, mul_one, hsum]
        calc κ' + σ' * ((Finset.univ.filter fun c => p c = true).card / N)
            ≤ κ' + σ' * 1 := by
              gcongr
              rw [ENNReal.div_le_iff hN0 hNt, one_mul]
              have hc : (Finset.univ.filter fun c => p c = true).card ≤ Fintype.card r.C :=
                (Finset.card_filter_le _ _).trans_eq Finset.card_univ
              exact Nat.cast_le.mpr hc
          _ = 1 := by rw [mul_one]; exact knowledgeError_add_survival rs
      · rw [if_neg hex, mul_zero, add_zero]
        have hcard : (Finset.univ.filter fun c => p c = true).card ≤ r.k - 1 := by
          have h2 : ¬ r.k ≤ (Finset.univ.filter fun c => p c = true).card :=
            (extract_cons_isSome r rs V s).not.mp hex
          omega
        set g := (Finset.univ.filter fun c => p c = true).card
        have hgN : (g : ℝ≥0∞) / N ≤ 1 := by
          rw [ENNReal.div_le_iff hN0 hNt, one_mul]
          have hc : g ≤ Fintype.card r.C :=
            (Finset.card_filter_le _ _).trans_eq Finset.card_univ
          exact Nat.cast_le.mpr hc
        have hgδ : (g : ℝ≥0∞) / N ≤ ((r.k - 1 : ℕ) : ℝ≥0∞) / N := by
          gcongr
        -- `κ' + σ' · g/N = 1 − σ' · (1 − g/N) ≤ 1 − σ' · (1 − (k−1)/N)`.
        have hsplit : κ' + σ' * ((g : ℝ≥0∞) / N) + σ' * (1 - (g : ℝ≥0∞) / N) = 1 := by
          rw [add_assoc, ← mul_add, add_tsub_cancel_of_le hgN, mul_one]
          exact knowledgeError_add_survival rs
        have hfin : σ' * (1 - (g : ℝ≥0∞) / N) ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top
            (mul_le_one' (survival_le_one rs) tsub_le_self)
        have heq : κ' + σ' * ((g : ℝ≥0∞) / N) = 1 - σ' * (1 - (g : ℝ≥0∞) / N) :=
          ENNReal.eq_sub_of_add_eq hfin hsplit
        rw [heq, knowledgeError, survival_cons, Round.survival, mul_comm]
        gcongr

/-! ## The probabilistic bound -/

/-- Affine monotonicity of `prTrue` under `bind`: a pointwise bound
`prTrue (k₁ a) ≤ κ + σ · prTrue (k₂ a)` averages over the first computation. -/
theorem prTrue_bind_le_affine {α : Type} (c : SPComp α) (k₁ k₂ : α → SPComp Bool)
    (κ σ : ℝ≥0∞) (h₀ : Heap)
    (hk : ∀ a h', prTrue (k₁ a) h' ≤ κ + σ * prTrue (k₂ a) h') :
    prTrue (SPComp.bind c k₁) h₀ ≤ κ + σ * prTrue (SPComp.bind c k₂) h₀ := by
  rw [ForkingLemma.prTrue_bind_eq_weighted c k₁, ForkingLemma.prTrue_bind_eq_weighted c k₂]
  calc _ ≤ ∑' p : Option (α × Heap), ((c h₀ : PMF _) p * κ +
          σ * ((c h₀ : PMF _) p *
            (match p with | some ⟨a, h'⟩ => prTrue (k₂ a) h' | none => 0))) := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        cases p with
        | none => simp
        | some p =>
          calc _ ≤ (c h₀ : PMF _) (some p) * (κ + σ * prTrue (k₂ p.1) p.2) :=
                mul_le_mul_right (hk p.1 p.2) _
            _ = _ := by ring
    _ = (∑' p : Option (α × Heap), (c h₀ : PMF _) p) * κ +
          σ * ∑' p : Option (α × Heap), (c h₀ : PMF _) p *
            (match p with | some ⟨a, h'⟩ => prTrue (k₂ a) h' | none => 0) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    _ ≤ κ + _ := by
        rw [(c h₀).tsum_coe, one_mul]; exact le_rfl

/-- Acceptance probability of a probabilistic prover `P` (a distribution over
strategies) against the verifier `V`. -/
noncomputable def acceptProb (rs : List Round) (P : SPComp (Strategy Y rs))
    (V : Transcript rs → Y → Bool) (h₀ : Heap) : ℝ≥0∞ :=
  prTrue (SPComp.bind P (runAccept rs V)) h₀

/-- The tree extractor for a probabilistic prover: draw a strategy from `P` and run
the rewinding extractor `extract` on it. -/
noncomputable def treeExtractor (rs : List Round) (P : SPComp (Strategy Y rs))
    (V : Transcript rs → Y → Bool) : SPComp (Option (Tree Y rs)) :=
  SPComp.bind P fun s => SPComp.pure (extract rs V s)

/-- Probability that the tree extractor outputs a tree. -/
noncomputable def extractProb (rs : List Round) (P : SPComp (Strategy Y rs))
    (V : Transcript rs → Y → Bool) (h₀ : Heap) : ℝ≥0∞ :=
  prTrue (SPComp.bind (treeExtractor rs P V) fun o => SPComp.pure o.isSome) h₀

theorem extractProb_eq (rs : List Round) (P : SPComp (Strategy Y rs))
    (V : Transcript rs → Y → Bool) (h₀ : Heap) :
    extractProb rs P V h₀ =
      prTrue (SPComp.bind P fun s => SPComp.pure (extract rs V s).isSome) h₀ := by
  unfold extractProb treeExtractor
  rw [SPComp.bind_assoc]
  simp only [SPComp.pure_bind]

/-- **Tree-forking lemma.** A prover accepted with probability `ε` yields, through
the rewinding extractor, an accepting `(k₁,…,k_μ)`-tree consistent with its
strategy with probability `p` satisfying `ε ≤ κ + (1 − κ) · p`, where
`κ = knowledgeError rs` and `1 − κ = survival rs`. -/
theorem acceptProb_le (rs : List Round) (P : SPComp (Strategy Y rs))
    (V : Transcript rs → Y → Bool) (h₀ : Heap) :
    acceptProb rs P V h₀ ≤ knowledgeError rs + survival rs * extractProb rs P V h₀ := by
  rw [extractProb_eq, acceptProb]
  refine prTrue_bind_le_affine _ _ _ _ _ h₀ fun s h' => ?_
  rw [ForkingLemma.prTrue_pure_bool]
  exact runAccept_le rs V s h'

/-- `ε − κ ≤ (1 − κ) · Pr[tree extracted]`. -/
theorem acceptProb_sub_le_mul (rs : List Round) (P : SPComp (Strategy Y rs))
    (V : Transcript rs → Y → Bool) (h₀ : Heap) :
    acceptProb rs P V h₀ - knowledgeError rs ≤ survival rs * extractProb rs P V h₀ :=
  tsub_le_iff_left.mpr (acceptProb_le rs P V h₀)

/-- `ε − κ ≤ Pr[tree extracted]`. -/
theorem acceptProb_sub_le (rs : List Round) (P : SPComp (Strategy Y rs))
    (V : Transcript rs → Y → Bool) (h₀ : Heap) :
    acceptProb rs P V h₀ - knowledgeError rs ≤ extractProb rs P V h₀ :=
  (acceptProb_sub_le_mul rs P V h₀).trans
    (mul_le_of_le_one_left zero_le (survival_le_one rs))

/-! ## Satisfiability -/

/-- A run against the verifier that accepts every transcript succeeds with
probability `1`. -/
theorem runAccept_const_true : ∀ (rs : List Round) (s : Strategy Y rs) (h₀ : Heap),
    prTrue (runAccept rs (fun _ _ => true) s) h₀ = 1
  | [], s, h₀ => by simp [runAccept, ForkingLemma.prTrue_pure_bool]
  | r :: rs, s, h₀ => by
      simp only [runAccept]
      rw [prTrue_bind_sample]
      simp only [runAccept_const_true rs, mul_one, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _)

/-- A prover accepted with probability `1` yields a tree with probability at least
`1 − κ`. -/
theorem one_sub_knowledgeError_le_extractProb (rs : List Round)
    (P : SPComp (Strategy Y rs)) (V : Transcript rs → Y → Bool) (h₀ : Heap)
    (hacc : acceptProb rs P V h₀ = 1) :
    1 - knowledgeError rs ≤ extractProb rs P V h₀ :=
  hacc ▸ acceptProb_sub_le rs P V h₀

/-- A deterministic prover run against the always-accepting verifier yields a tree
with probability at least `1 − κ`, which is positive when every `kᵢ ≤ |Cᵢ|`. -/
theorem extractProb_const_accept (rs : List Round) (s : Strategy Y rs) (h₀ : Heap) :
    1 - knowledgeError rs ≤ extractProb rs (SPComp.pure s) (fun _ _ => true) h₀ :=
  one_sub_knowledgeError_le_extractProb rs _ _ h₀ (by
    rw [acceptProb, SPComp.pure_bind, runAccept_const_true])

theorem extractProb_const_accept_pos (rs : List Round) (s : Strategy Y rs) (h₀ : Heap)
    (hk : ∀ r ∈ rs, r.k ≤ Fintype.card r.C) :
    0 < extractProb rs (SPComp.pure s) (fun _ _ => true) h₀ :=
  lt_of_lt_of_le (tsub_pos_of_lt (knowledgeError_lt_one rs hk))
    (extractProb_const_accept rs s h₀)

/-! ## The single-round, arity-2 case -/

section Fork

open ForkingLemma

variable {X Cm R : Type} [Fintype R] [Nonempty R]

/-- The single round of the two-branch forking lemma: challenge set `R`, no
prover message (the commitment is part of the strategy draw), arity `2`. -/
def forkRound (R : Type) [Fintype R] [Nonempty R] : Round := { C := R, M := Unit, k := 2 }

theorem knowledgeError_forkRound :
    knowledgeError [forkRound R] = (Fintype.card R : ℝ≥0∞)⁻¹ :=
  knowledgeError_single_two R Unit

/-- The single-round strategy answering challenge `e` with `f e`. -/
def forkStrategy (f : R → Y) : Strategy Y [forkRound R] := ((), f)

/-- A `ForkableAdversary` as a probabilistic single-round prover: the commitment
phase draws the strategy `e ↦ respond x c e`. -/
noncomputable def forkProver (A : ForkableAdversary X Cm R Y) (x : X) :
    SPComp (Strategy Y [forkRound R]) :=
  SPComp.bind (A.coins x) fun c => SPComp.pure (forkStrategy fun e => A.respond x c e)

theorem acceptProb_forkProver (A : ForkableAdversary X Cm R Y) (x : X)
    (accept : Y → Bool) :
    acceptProb [forkRound R] (forkProver A x) (fun _ y => accept y) Heap.empty =
      ForkingLemma.acceptProb A x accept := by
  unfold acceptProb forkProver ForkingLemma.acceptProb
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  rfl

/-- The two-branch fork succeeds with probability at most the tree extractor's on
`forkProver`: a fork success exhibits two distinct accepting challenges for the
drawn commitment. -/
theorem forkSuccProb_le_extractProb [DecidableEq R] (A : ForkableAdversary X Cm R Y)
    (x : X) (accept : Y → Bool) :
    forkSuccProb A x accept ≤
      extractProb [forkRound R] (forkProver A x) (fun _ y => accept y) Heap.empty := by
  rw [forkSuccProb_decompose, extractProb_eq, forkProver, SPComp.bind_assoc]
  simp only [SPComp.pure_bind]
  rw [prTrue_bind_eq_weighted]
  refine ENNReal.tsum_le_tsum fun p => ?_
  cases p with
  | none => simp
  | some p =>
    obtain ⟨c, h'⟩ := p
    refine mul_le_mul_right ?_ _
    simp only [prTrue_pure_bool]
    split_ifs with hex
    · exact prTrue_le_one _ _
    · have hcard := (extract_cons_isSome (forkRound R) [] _ _).not.mp hex
      unfold condForkProb
      rw [prTrue_bind_sample]
      refine le_of_eq (Finset.sum_eq_zero fun e₁ _ => ?_)
      rw [prTrue_bind_sample, Finset.sum_eq_zero fun e₂ _ => ?_, mul_zero]
      rw [prTrue_pure_bool]
      split_ifs with hacc
      · exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
        obtain ⟨⟨h₁, h₂⟩, hne⟩ := hacc
        refine hcard ?_
        refine Finset.one_lt_card.mpr ⟨e₁, ?_, e₂, ?_, hne⟩ <;>
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩ <;>
          rw [extract_nil_isSome] <;> assumption
      · simp

/-- For μ = 1 and k = 2 the tree-extraction probability of `forkProver` is bounded
below both by `acc − 1/|R|` (`acceptProb_sub_le`) and by the forking-lemma bound
`acc² − acc/|R|` (`fork_success_ge`). -/
theorem single_round_extract_ge [DecidableEq R] (A : ForkableAdversary X Cm R Y)
    (x : X) (accept : Y → Bool) :
    ForkingLemma.acceptProb A x accept - (Fintype.card R : ℝ≥0∞)⁻¹ ≤
        extractProb [forkRound R] (forkProver A x) (fun _ y => accept y) Heap.empty ∧
      ForkingLemma.acceptProb A x accept ^ 2 -
          ForkingLemma.acceptProb A x accept / Fintype.card R ≤
        extractProb [forkRound R] (forkProver A x) (fun _ y => accept y) Heap.empty := by
  refine ⟨?_, (fork_success_ge A x accept).trans (forkSuccProb_le_extractProb A x accept)⟩
  have := acceptProb_sub_le [forkRound R] (forkProver A x) (fun _ y => accept y) Heap.empty
  rwa [acceptProb_forkProver, knowledgeError_forkRound] at this

end Fork

end CatCrypt.Crypto.TreeForking
