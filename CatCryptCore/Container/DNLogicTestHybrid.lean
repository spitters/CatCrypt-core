/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogicMonoClassical
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Proof mining of the hybrid lemma

The averaging step of a hybrid argument: for hybrid values `a 0, …, a q` in `ℚ` with
`ε ≤ |a q - a 0|` and `0 < ε`, some `j < q` has `ε / q ≤ |a (j + 1) - a j|`. Its classical
proof is a reductio: if every gap were below `ε / q`, the triangle inequality would bound
`|a q - a 0|` below `ε`.

This module states the lemma as a classical derivation `hybridCDeriv` of `CDeriv` (the
Π⁰₂ statement `∀ x, ∃ j, gapRel (x, j)` over instances `x` of `q` hops) from one hypothesis,
`triForm`, the triangle inequality in the form `∀ x, ¬ ∀ j, ¬ gapRel (x, j)`. The derivation
eliminates `∃` by reductio ad absurdum; it never names an index.

The hypothesis has a direct Diller–Nahm witness `triW`: at an instance with `q` hops it demands
the gaps at `j = 0, …, q - 1`, and it withstands every counter-witness by the finite averaging
inequality `averaging` (`triW_mat`). The intuitionistic derivation `triNegT` sends the hypothesis
to its negative translation, and the witness of the translated context `triCtxW` is its realizer
at `triW`.

The index finder `hybridFinder` is `CDeriv.extract` at that witness, with the selection
`gapSel` of the largest candidate that satisfies `gapRel`. `hybridFinder_spec` states that its
index `j` satisfies `j < q` and `ε / q ≤ |a (j + 1) - a j|`.

## Use count

The derivation `hybridFull` composes the extraction with `triNegT`: a derivation of the Π⁰₂
statement from the untranslated hypothesis. It uses the hypothesis once (`hybridFull_useCount`),
so its realizer consults the triangle witness at most once (`triChecks_card_le`), and that
consultation demands the `q` gaps at `j < q`, which read the `q + 1` hybrid values
`a 0, …, a q` (`hybridReads_card_le`).

## Comparison with the hybrid reductions

`CatCryptCore/Crypto/HybridArgument.lean` bounds `Adv(G 0, G q)` by the sum of the hop
advantages `Σ_{j < q} Adv(G j, G (j + 1))` (`advantage_hybrid_dep`), and each hop has its own
reduction with a time certificate (`secHybRed`, `stretchHybRed` and `HybridArgumentTimed`); the
uniform form `advantage_hybrid_uniform` is the contrapositive of the averaging step with
`ε / q` per hop. The extracted finder answers the index question of the averaging step: it reads
the `q + 1` hybrid advantages and returns one hop whose gap is at least `ε / q`. A reduction cannot
run it, since a hybrid advantage is a probability and not a value the reduction computes. The
guessing reduction of the textbook argument replaces the `q + 1` evaluations by one uniformly
guessed index and pays the factor `q` in advantage; the sum form of `HybridArgument` pays it as
`q` reductions, one per hop. The use count `q + 1` is the number of hybrids the averaging step
compares, and the loss factor `q` of the guessing reduction is the number of gaps among them.

## Main definitions

* `gapRel`, `triForm` — the Π⁰₂ matrix and the triangle hypothesis;
* `hybridCDeriv` — the classical derivation of the averaging step;
* `triW`, `triNegT`, `triCtxW` — the witness of the hypothesis and of its translation;
* `gapSel`, `hybridFinder` — the selection and the extracted index finder;
* `hybridFull` — the extraction composed with the translation of the hypothesis.

## Main results

* `averaging` — the finite averaging inequality;
* `hybridFinder_spec` — the extracted index is below `q` and has the gap property;
* `hybridFull_useCount`, `triChecks_card_le`, `hybridReads_card_le` — the use count and the
  number of hybrid values read.

Search words: hybrid argument, averaging, proof mining, index search, negative translation,
Markov's principle, use count.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Container.DNLogic.HybridTest

open CatCrypt.Container.DNLogic DPred

/-- An instance of the averaging step: hybrid values `a` and a distance `ε`. -/
structure Hybrids : Type where
  /-- The hybrid values. -/
  a : ℕ → ℚ
  /-- The distance between the end points. -/
  ε : ℚ

/-- The gap property at index `j` for `q` hops: when the end points are at distance at least
`ε > 0`, the hop `j` is below `q` and has a gap at least `ε / q`. -/
def gapAt (q : ℕ+) (h : Hybrids) (j : ℕ) : Prop :=
  0 < h.ε → h.ε ≤ |h.a q - h.a 0| → j < (q : ℕ) ∧ h.ε / q ≤ |h.a (j + 1) - h.a j|

/-- The sort of instances at `q` hops. -/
abbrev HK : ℕ+ → Type := fun _ => Hybrids

/-- The sort of indices. -/
abbrev HL : (Σ _ : ℕ+, Hybrids) → Type := fun _ => ℕ

/-- The Π⁰₂ matrix: the gap property of an index at an instance. -/
def gapRel (z : Σ _ : Σ _ : ℕ+, Hybrids, ℕ) : Prop :=
  gapAt z.1.1 z.1.2 z.2

/-- **The finite averaging inequality.** If no index `j < q` has the gap property, the instance
is contradictory: the gaps below `ε / q` sum below `ε`. -/
theorem averaging (q : ℕ+) (h : Hybrids) (H : ∀ j < (q : ℕ), ¬ gapAt q h j) : False := by
  have hε : 0 < h.ε ∧ h.ε ≤ |h.a q - h.a 0| := by
    by_contra hc
    exact H 0 q.pos fun h1 h2 => absurd ⟨h1, h2⟩ hc
  have hsmall : ∀ j ∈ Finset.range q, |h.a (j + 1) - h.a j| < h.ε / q := by
    intro j hj
    by_contra hc
    exact H j (Finset.mem_range.1 hj) fun _ _ => ⟨Finset.mem_range.1 hj, not_lt.1 hc⟩
  have hlt : |h.a q - h.a 0| < h.ε :=
    calc |h.a q - h.a 0| = |∑ j ∈ Finset.range q, (h.a (j + 1) - h.a j)| := by
          rw [Finset.sum_range_sub]
      _ ≤ ∑ j ∈ Finset.range q, |h.a (j + 1) - h.a j| := Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _j ∈ Finset.range q, h.ε / q :=
          Finset.sum_lt_sum_of_nonempty (by simp) hsmall
      _ = h.ε := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  linarith [hε.2]

/-- The size of a hop index: the index itself. An instance has size `0`. -/
abbrev indS {I : Type} : I → ℕ → ℕ := fun _ => id

/-- The triangle hypothesis `∀ x, ¬ ∀ j, ¬ gapRel (x, j)`. -/
abbrev triForm : Form ℕ+ :=
  .all (K := HK) (sz := 0) (.imp (.all (K := HL) (sz := indS) (Form.not (.atom gapRel))) Form.bot)

/-- Conversion of classical derivations whose side conditions hold by unfolding the
interpretations. -/
def cconv {I : Type} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : CDeriv Γ φ)
    (hdn : φ.negT.dn = ψ.negT.dn := by rfl)
    (hev : ∀ i, φ.eval i → ψ.eval i := by exact fun _ h => h)
    (hevN : ∀ i, φ.negT.eval i → ψ.negT.eval i := by exact fun _ h => h) : CDeriv Γ ψ :=
  .conv hdn hev hevN d

/-- The instance at the bound variable of a universal formula reindexed along `Sigma.fst`, in
classical derivations. -/
def cInstSelf {I : Type} {n : ℕ} {K : I → Type} {s : ∀ i, K i → ℕ} {X : Form (Σ i, K i)}
    {Δ : Fin n → Form (Σ i, K i)} (d : CDeriv Δ ((Form.all (K := K) (sz := s) X).sub Sigma.fst)) :
    CDeriv Δ X :=
  cconv (.allE (K := fun x : Σ i, K i => K x.1) (s := fun x => s x.1)
    (φ := X.sub fun y => ⟨y.1.1, y.2⟩) (fun x => x.2) (cconv d))

/-- **The classical derivation of the averaging step**: for every instance, by reductio, the
assumption that no index has the gap property contradicts the triangle hypothesis. -/
def hybridCDeriv :
    CDeriv (fun _ : Fin 1 => triForm) (Deriv.allEx (X := HK) (Y := HL) 0 indS gapRel) :=
  .allI (.raa (.impE (cInstSelf (.hyp ⟨1, by omega⟩))
    (.allI (.impI (cconv
      (.impE (cconv (ψ := .imp ((Form.ex (K := HL) (sz := indS) (.atom gapRel)).sub Sigma.fst)
          ((Form.bot : Form (Σ _ : ℕ+, Hybrids)).sub Sigma.fst)) (.hyp ⟨1, by omega⟩))
        (cconv
          (.exI (K := fun y : Σ x : Σ _ : ℕ+, Hybrids, ℕ => HL y.1) (s := indS)
            (φ := (Form.atom gapRel).sub fun z => ⟨z.1.1, z.2⟩) (fun y => y.2)
            (cconv (.hyp ⟨0, by omega⟩))))))))))

/-! ## The witness of the triangle hypothesis -/

/-- The witness of the triangle hypothesis at `q` hops: at every instance it demands the gaps at
`j = 0, …, q - 1`. -/
def triW (q : ℕ+) : triForm.dn.W q := fun _ =>
  ⟨fun _ => PUnit.unit, fun _ _ => (Multiset.range q).map fun j => ⟨j, PUnit.unit, PUnit.unit⟩⟩

/-- **The triangle witness is sound**: it withstands every counter-witness, by `averaging`. -/
theorem triW_mat (q : ℕ+) (c : triForm.dn.C q (triW q)) : triForm.dn.mat q (triW q) c := by
  intro hc
  exact averaging q c.1 fun j hj hg => hc ⟨j, PUnit.unit, PUnit.unit⟩
    (Multiset.mem_map.2 ⟨j, Multiset.mem_range.2 hj, rfl⟩) fun _ _ => hg

/-- The intuitionistic derivation of the negative translation of the triangle hypothesis from the
hypothesis. -/
def triNegT : Deriv (fun _ : Fin 1 => triForm) triForm.negT :=
  .allI (.impI (.impI (.impE (Deriv.instSelf (.hyp ⟨2, by omega⟩))
    (.allI (.impI (.impE (.impE (Deriv.instSelf (.hyp ⟨2, by omega⟩))
        (.impI (.impE (.hyp ⟨0, by omega⟩) (.hyp ⟨1, by omega⟩))))
      (Deriv.conv (.hyp ⟨1, by omega⟩))))))))

/-- The witness of the translated context: the realizer of `triNegT` at `triW`. -/
def triCtxW (q : ℕ+) : (ctx fun _ : Fin 1 => triForm.negT).W q :=
  fun _ => triNegT.realize.fwd q fun _ => triW q

/-- The witness of the translated context withstands every counter-witness. -/
theorem triCtxW_mat (q : ℕ+) (c : (ctx fun _ : Fin 1 => triForm.negT).C q (triCtxW q)) :
    (ctx fun _ : Fin 1 => triForm.negT).mat q (triCtxW q) c :=
  triNegT.realize.sound q (fun _ => triW q) c.2 fun x _ => triW_mat q x.2

/-! ## The extracted index finder -/

instance (z : Σ _ : Σ _ : ℕ+, Hybrids, ℕ) : Decidable (gapRel z) := by
  unfold gapRel gapAt
  infer_instance

/-- The selection of the largest candidate index with the gap property. -/
def gapSel (x : Σ _ : ℕ+, Hybrids) (ys : Multiset ℕ) : ℕ :=
  (ys.toFinset.filter fun j => gapRel ⟨x, j⟩).sup id

/-- The selection picks a candidate with the gap property when not all candidates fail it. -/
theorem gapSel_spec (x : Σ _ : ℕ+, Hybrids) (ys : Multiset ℕ)
    (h : (∀ y ∈ ys, ¬ gapRel ⟨x, y⟩) → False) : gapRel ⟨x, gapSel x ys⟩ := by
  have hne : (ys.toFinset.filter fun j => gapRel ⟨x, j⟩).Nonempty := by
    by_contra hn
    exact h fun y hy hg => hn ⟨y, Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hy, hg⟩⟩
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [gapSel, he]
  exact (Finset.mem_filter.1 hj).2

/-- The size of a multiset of candidate indices: its maximum. -/
abbrev gapMS : ∀ _ : Σ _ : ℕ+, Hybrids, Multiset ℕ → ℕ :=
  CDeriv.supSize (K := HK) (L := HL) indS

/-- **The extracted index finder**: `CDeriv.extract` of the classical derivation at the witness
of the translated triangle hypothesis, with the selection `gapSel`. -/
def hybridFinder (q : ℕ+) (h : Hybrids) : ℕ :=
  CDeriv.extract gapRel gapSel gapSel_spec gapMS hybridCDeriv q (triCtxW q) h

/-- **Correctness of the index finder.** When the end points are at distance at least `ε > 0`,
the extracted index `j` satisfies `j < q` and `ε / q ≤ |a (j + 1) - a j|`. -/
theorem hybridFinder_spec (q : ℕ+) (h : Hybrids) (hε : 0 < h.ε)
    (hd : h.ε ≤ |h.a q - h.a 0|) :
    hybridFinder q h < (q : ℕ) ∧
      h.ε / q ≤ |h.a (hybridFinder q h + 1) - h.a (hybridFinder q h)| :=
  CDeriv.extract_spec gapRel gapSel gapSel_spec gapMS hybridCDeriv q (triCtxW q) (triCtxW_mat q) h
    hε hd

/-! ## Use count -/

/-- The extraction composed with the translation of the triangle hypothesis: a derivation of the
Π⁰₂ statement from the untranslated hypothesis. -/
def hybridFull :
    Deriv (fun _ : Fin 1 => triForm) (Deriv.allEx (X := HK) (Y := HL) 0 indS gapRel) :=
  .impE (CDeriv.pi2Imp gapRel gapSel gapSel_spec gapMS _)
    (.impE (.impI (hybridCDeriv.toDerivAt (consF triForm.negT fun _ : Fin 1 => triForm)
      (fun _ => 0) fun _ => rfl)) triNegT)

/-- **Use count.** The composed derivation uses the triangle hypothesis once; a test, computed
by evaluating `Deriv.useCount`. -/
theorem hybridFull_useCount : hybridFull.useCount 0 = 1 := by
  rfl

/-- The counter-witnesses of the triangle hypothesis that the realizer of `hybridFull` demands to
answer the instance `h`: the consultations of the triangle witness. -/
def triChecks (q : ℕ+) (h : Hybrids) : Multiset ((ctx fun _ : Fin 1 => triForm).C q
    fun _ => triW q) :=
  hybridFull.realize.back q (fun _ => triW q) ⟨h, PUnit.unit⟩

/-- The realizer consults the triangle witness at most once. -/
theorem triChecks_card_le (q : ℕ+) (h : Hybrids) : (triChecks q h).card ≤ 1 := by
  have hb := hybridFull.card_back_le 0 q (fun _ => triW q) ⟨h, PUnit.unit⟩
  rw [hybridFull_useCount, Multiset.countP_eq_card.2 fun x _ => Subsingleton.elim _ _] at hb
  exact_mod_cast hb

/-- The gap indices that the consultations of the triangle witness demand. -/
def gapReads (q : ℕ+) (h : Hybrids) : Multiset ℕ :=
  (triChecks q h).bind fun c => ((triW q c.2.1).2 c.2.2.1 c.2.2.2).map Sigma.fst

/-- The hybrid values that the demanded gaps read: `a j` and `a (j + 1)` for each gap `j`. -/
def hybridReads (q : ℕ+) (h : Hybrids) : Finset ℕ :=
  ((gapReads q h).bind fun j => {j, j + 1}).toFinset

/-- Every demanded gap index is below `q`. -/
theorem lt_of_mem_gapReads (q : ℕ+) (h : Hybrids) (j : ℕ) (hj : j ∈ gapReads q h) :
    j < (q : ℕ) := by
  simp only [gapReads, Multiset.mem_bind] at hj
  obtain ⟨c, -, hc⟩ := hj
  obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hc
  change s ∈ (Multiset.range q).map _ at hs
  obtain ⟨j', hj', rfl⟩ := Multiset.mem_map.1 hs
  exact Multiset.mem_range.1 hj'

/-- **Hybrid evaluations.** The realizer reads at most the `q + 1` hybrid values
`a 0, …, a q`. -/
theorem hybridReads_card_le (q : ℕ+) (h : Hybrids) : (hybridReads q h).card ≤ q + 1 := by
  have hsub : hybridReads q h ⊆ Finset.range (q + 1) := by
    intro k hk
    simp only [hybridReads, Multiset.mem_toFinset, Multiset.mem_bind, Multiset.insert_eq_cons,
      Multiset.mem_cons, Multiset.mem_singleton] at hk
    obtain ⟨j, hj, hk⟩ := hk
    have := lt_of_mem_gapReads q h j hj
    rw [Finset.mem_range]
    omega
  simpa using Finset.card_le_card hsub

end CatCrypt.Container.DNLogic.HybridTest
