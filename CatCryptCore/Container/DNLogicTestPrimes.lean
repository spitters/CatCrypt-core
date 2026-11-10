/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogicMonoClassical
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Euclid's theorem in the classical DN logic: extraction and bound

Euclid's proof that every `n` has a prime `p > n`, as a classical derivation `CDeriv` of
`∀ n, ∃ p, n < p ∧ p prime` from two hypotheses:

* `euclidH0`, `∀ n, ∃ q, q prime ∧ q ∣ n! + 1`, the existence of a prime factor of `n! + 1`;
* `euclidH1`, `∀ n q, (q prime ∧ q ∣ n! + 1) → ¬(n < q ∧ q prime) → ⊥`, the step of Euclid's
  argument: a prime factor of `n! + 1` that is at most `n` divides `n!` and `1`.

The derivation `euclidDeriv` takes the prime factor `q` of `n! + 1` given by `euclidH0` and proves
`n < q ∧ q prime` by reductio ad absurdum from `euclidH1`. The hypotheses enter through the
negative translation as witnesses of their translations, the realizers of the closed derivations
`euclidH0Deriv` (from the realized axiom `minFacHom`, the least prime factor `Nat.minFac` of
`n! + 1`) and `euclidH1Deriv` (from the atom rule `Deriv.atom₂` at Euclid's lemma
`euclidRel_of_facRel`).

`euclidExtract` is the function extracted through the negative translation, Markov's principle and
the selection `euclidSel` (the largest candidate that is a prime above `n`), and
`euclidExtract_spec` states that it gives a prime above its argument. `euclidBound` is the bound of
the monotone interpretation, computed from the majorant `m ↦ m! + 1` of the least prime factor.
The quantifiers over numbers carry the size `idS` (a number is its own size) and the multisets of
candidates the maximum size `mSize`. `euclidExtract_le` and `euclid_exists_le` bound the extracted
function and a prime above `n` by the bound, with no hypothesis on sizes.

## Main results

* `euclidExtract_spec` — the extracted function gives a prime above its argument;
* `euclidExtract_le`, `euclid_exists_le` — the bound extraction of Euclid's theorem.

## References

* U. Kohlenbach, *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*,
  Springer (2008).

Search words: Euclid, infinitely many primes, proof mining, bound extraction, negative
translation, Markov's principle, monotone functional interpretation.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Container.DNLogic.Euclid

open DPred CatCrypt.Core Form

/-- The sort context of the bound variable `n`. -/
abbrev J0 : Type := Σ _ : PUnit.{1}, ℕ

/-- The sort context of the variables `n` and `q`. -/
abbrev J : Type := Σ _ : J0, ℕ

/-- `q` is a prime factor of `n! + 1`. -/
def facRel (z : J) : Prop := z.2.Prime ∧ z.2 ∣ z.1.2.factorial + 1

/-- `q` is a prime above `n`. -/
def euclidRel (z : J) : Prop := z.1.2 < z.2 ∧ z.2.Prime

/-- **Euclid's lemma.** A prime factor of `n! + 1` is above `n`. -/
theorem euclidRel_of_facRel (z : J) (h : facRel z) : euclidRel z := by
  refine ⟨?_, h.1⟩
  by_contra hle
  have hd : z.2 ∣ z.1.2.factorial := Nat.dvd_factorial h.1.pos (by omega)
  have h1 : z.2 ∣ 1 := (Nat.dvd_add_right hd).mp h.2
  exact h.1.one_lt.ne' (Nat.dvd_one.mp h1)

/-- The size on numbers at every sort context: a number has size itself. -/
abbrev idS {I : Type} : I → ℕ → ℕ := fun _ => id

/-- The hypothesis `∀ n, ∃ q, q prime ∧ q ∣ n! + 1`. -/
abbrev euclidH0 : Form PUnit.{1} :=
  Deriv.allEx (X := fun _ => ℕ) (Y := fun _ => ℕ) idS idS facRel

/-- The hypothesis `∀ n q, (q prime ∧ q ∣ n! + 1) → ¬(n < q ∧ q prime) → ⊥`. -/
abbrev euclidH1 : Form PUnit.{1} :=
  .all (K := fun _ => ℕ) (sz := idS) (.all (K := fun _ : J0 => ℕ) (sz := idS)
    (.imp (.atom facRel) (.imp (Form.not (.atom euclidRel)) Form.bot)))

/-- The context of Euclid's derivation. -/
def euclidCtx : Fin 2 → Form PUnit.{1} := consF euclidH0 (consF euclidH1 Fin.elim0)

/-- Conversion of a classical derivation from `φ` to `ψ`, with the side conditions by `rfl` when
the two formulas are definitionally equal after unfolding the interpretations. -/
def cconv {I : Type} {n : ℕ} {Δ : Fin n → Form I} (φ ψ : Form I) (d : CDeriv Δ φ)
    (hdn : φ.negT.dn = ψ.negT.dn := by rfl)
    (hev : ∀ i, φ.eval i → ψ.eval i := by exact fun _ h => h)
    (hevN : ∀ i, φ.negT.eval i → ψ.negT.eval i := by exact fun _ h => h) : CDeriv Δ ψ :=
  .conv hdn hev hevN d

/-- The instance of a universal hypothesis reindexed along `Sigma.fst` at the bound variable, as a
classical derivation. -/
def instSelfC {I : Type} {n : ℕ} {K : I → Type} {s : ∀ i, K i → ℕ} {X : Form (Σ i, K i)}
    {Δ : Fin n → Form (Σ i, K i)} (d : CDeriv Δ ((Form.all (K := K) (sz := s) X).sub Sigma.fst)) :
    CDeriv Δ X :=
  cconv ((X.sub fun y : (Σ x : Σ i, K i, K x.1) => (⟨y.1.1, y.2⟩ : Σ i, K i)).sub
      fun x : (Σ i, K i) => (⟨x, x.2⟩ : Σ x : Σ i, K i, K x.1)) X
    (.allE (K := fun x : Σ i, K i => K x.1) (s := fun x => s x.1)
      (φ := X.sub fun y => ⟨y.1.1, y.2⟩) (fun x => x.2) (cconv _ _ d))

/-- The body of `euclidH1`: `(q prime ∧ q ∣ n! + 1) → ¬(n < q ∧ q prime) → ⊥`. -/
abbrev euclidH1Body : Form J := .imp (.atom facRel) (.imp (Form.not (.atom euclidRel)) Form.bot)

/-- The instance of `euclidH1` at the variables `n` and `q` of the sort context `J`. -/
def h1At {n : ℕ} {Δ : Fin n → Form J}
    (d : CDeriv Δ ((euclidH1.sub Sigma.fst).sub Sigma.fst)) : CDeriv Δ euclidH1Body :=
  instSelfC (cconv _ ((Form.all (K := fun _ : J0 => ℕ) (sz := idS) euclidH1Body).sub Sigma.fst)
    (.allE (K := fun _ : J => ℕ) (s := idS) (fun j => j.1.2)
      (cconv _ (.all (K := fun _ : J => ℕ) (sz := idS)
          ((Form.all (K := fun _ : J0 => ℕ) (sz := idS) euclidH1Body).sub
            fun y : (Σ _ : J, ℕ) => (⟨y.1.1.1, y.2⟩ : J0))) d)))

/-- **Euclid's theorem as a classical derivation.** For `n`, the prime factor `q` of `n! + 1` given
by `euclidH0` is a prime above `n`, by reductio from `euclidH1`. -/
def euclidDeriv : CDeriv euclidCtx
    (Deriv.allEx (X := fun _ => ℕ) (Y := fun _ => ℕ) idS idS euclidRel) :=
  .allI (.exE (K := fun _ : J0 => ℕ) (s := idS) (φ := .atom facRel)
    (instSelfC (cconv _ (euclidH0.sub Sigma.fst) (.hyp ⟨0, by omega⟩)))
    (cconv (.ex (K := fun _ : J => ℕ) (sz := idS) (.atom fun z => euclidRel ⟨z.1.1, z.2⟩)) _
      (.exI (fun j => j.2) (cconv (.atom euclidRel) _
        (.raa (.impE (.impE (h1At (cconv _ _ (.hyp ⟨3, by omega⟩))) (.hyp ⟨1, by omega⟩))
          (.hyp ⟨0, by omega⟩)))))))

/-! ## The hypotheses as closed derivations of their negative translations -/

/-- The least prime factor of `n! + 1` is a prime factor of `n! + 1`. -/
theorem facRel_minFac (x : J0) : facRel ⟨x, (x.2.factorial + 1).minFac⟩ := by
  have h : x.2.factorial + 1 ≠ 1 := by have := Nat.factorial_pos x.2; omega
  exact ⟨Nat.minFac_prime h, Nat.minFac_dvd _⟩

/-- The realized axiom `∃ q, q prime ∧ q ∣ n! + 1`, realized by the least prime factor
`Nat.minFac (n! + 1)`. -/
def minFacHom : (Form.top : Form J0).dn.Hom
    (Form.ex (K := fun _ : J0 => ℕ) (sz := idS) (.atom facRel)).dn where
  fwd x _ := ⟨(x.2.factorial + 1).minFac, PUnit.unit⟩
  back _ _ _ := 0
  sound x _ _ _ := facRel_minFac x

/-- The negative translation of `euclidH0` as a closed derivation, from the realized axiom
`minFacHom`. -/
def euclidH0Deriv : Deriv (Fin.elim0 : Fin 0 → Form PUnit.{1}) euclidH0.negT :=
  .allI (.impI (.exE (K := fun _ : J0 => ℕ) (s := idS) (φ := .atom facRel) (ψ := Form.bot)
    (.hom minFacHom 0 (fun _ _ _ => by simp [minFacHom]) (fun x _ => ⟨_, facRel_minFac x⟩) .topI)
    (Deriv.conv (ψ := Form.bot.sub Sigma.fst)
      (.impE (Deriv.instSelf (.hyp ⟨1, by omega⟩ : Deriv _
          ((Form.all (K := fun _ : J0 => ℕ) (sz := idS)
            (Form.not (Form.not (Form.not (.atom facRel))))).sub Sigma.fst)))
        (.impI (.impE (.hyp ⟨0, by omega⟩) (.hyp ⟨1, by omega⟩)))))))

/-- The negative translation of `euclidH1` as a closed derivation, from Euclid's lemma
`euclidRel_of_facRel` as an atom rule. -/
def euclidH1Deriv : Deriv (Fin.elim0 : Fin 0 → Form PUnit.{1}) euclidH1.negT :=
  .allI (.allI (.impI (.impI (.impI
    (.impE (.impE (.hyp ⟨1, by omega⟩)
        (.impI (.impE (.hyp ⟨3, by omega⟩) (.impI (.impE (.hyp ⟨1, by omega⟩)
          (.atom₂ (p := facRel) (q := facRel) (fun z h _ => euclidRel_of_facRel z h)
            (.hyp ⟨0, by omega⟩) (.hyp ⟨0, by omega⟩)))))))
      (.hyp ⟨0, by omega⟩))))))

/-- The witness of the translated hypotheses: the realizers of `euclidH0Deriv` and
`euclidH1Deriv`. -/
def euclidW : (ctx fun k => (euclidCtx k).negT).W PUnit.unit
  | ⟨0, _⟩ => euclidH0Deriv.realize.fwd PUnit.unit fun k => k.elim0
  | ⟨1, _⟩ => euclidH1Deriv.realize.fwd PUnit.unit fun k => k.elim0

/-- The witness `euclidW` withstands every counter-witness of the translated hypotheses. -/
theorem euclidW_mat (c : (ctx fun k => (euclidCtx k).negT).C PUnit.unit euclidW) :
    (ctx fun k => (euclidCtx k).negT).mat PUnit.unit euclidW c := by
  obtain ⟨⟨k, hk⟩, c⟩ := c
  match k, hk, c with
  | 0, _, c => exact euclidH0Deriv.realize.sound _ _ c fun x _ => x.1.elim0
  | 1, _, c => exact euclidH1Deriv.realize.sound _ _ c fun x _ => x.1.elim0

/-! ## The extracted function -/

instance (z : J) : Decidable (euclidRel z) := inferInstanceAs (Decidable (_ < _ ∧ _))

/-- The selection: the largest candidate that is a prime above `n`. -/
def euclidSel (x : J0) (ys : Multiset ℕ) : ℕ := (ys.filter fun y => euclidRel ⟨x, y⟩).sup

/-- A nonempty multiset of numbers contains its maximum. -/
theorem sup_mem_of_ne_zero (s : Multiset ℕ) (hs : s ≠ 0) : s.sup ∈ s := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    rw [Multiset.sup_cons]
    by_cases h0 : s = 0
    · subst h0
      simp
    · rcases le_total a s.sup with h | h
      · rw [sup_eq_right.mpr h]
        exact Multiset.mem_cons_of_mem (ih h0)
      · rw [sup_eq_left.mpr h]
        exact Multiset.mem_cons_self _ _

/-- The selection picks a prime above `n` when not all candidates fail. -/
theorem euclidSel_spec (x : J0) (ys : Multiset ℕ)
    (h : (∀ y ∈ ys, ¬ euclidRel ⟨x, y⟩) → False) : euclidRel ⟨x, euclidSel x ys⟩ := by
  have hne : ys.filter (fun y => euclidRel ⟨x, y⟩) ≠ 0 := by
    intro h0
    exact h fun y hy hr => by
      have : y ∈ ys.filter (fun y => euclidRel ⟨x, y⟩) := Multiset.mem_filter.mpr ⟨hy, hr⟩
      rw [h0] at this
      simp at this
  exact (Multiset.mem_filter.mp (sup_mem_of_ne_zero _ hne)).2

/-- The size of a multiset of candidates: its maximum, through `CDeriv.supSize`. -/
abbrev mSize : ∀ _ : J0, Multiset ℕ → ℕ :=
  CDeriv.supSize (K := fun _ : PUnit.{1} => ℕ) (L := fun _ : J0 => ℕ) idS

/-- **The function extracted from Euclid's proof**, through the negative translation, Markov's
principle and the selection `euclidSel`. -/
def euclidExtract (n : ℕ) : ℕ :=
  CDeriv.extract euclidRel euclidSel euclidSel_spec mSize euclidDeriv PUnit.unit euclidW n

/-- **Correctness of the extracted function.** It gives a prime above its argument. -/
theorem euclidExtract_spec (n : ℕ) : n < euclidExtract n ∧ (euclidExtract n).Prime := by
  have h := CDeriv.extract_spec euclidRel euclidSel euclidSel_spec mSize euclidDeriv PUnit.unit
    euclidW euclidW_mat n
  simpa only [euclidRel, euclidExtract] using h

/-! ## Majorant data and the extracted bound -/

/-- The identity majorant of a conversion between formulas whose majorant types and
majorization agree definitionally. -/
local macro "conv_maj%" : term =>
  `(HomMaj.ofFun _ (fun b => b) (fun _ bc => bc) (by
    intro i a ba ha
    refine ⟨ha, fun bc c hc x hx => ?_⟩
    have e : x = c := Multiset.mem_singleton.1 hx
    subst e
    exact hc))

/-- The environment of the empty sort context. -/
abbrev R0 : ℕ → PUnit.{1} → Prop := fun _ _ => True

/-- The majorant `m ↦ m! + 1` of the least prime factor of `n! + 1`. -/
def minFacMaj :
    HomMaj (envExt R0 (K := fun _ => ℕ) idS) Form.top
      (Form.ex (K := fun _ : J0 => ℕ) (sz := idS) (.atom facRel)) minFacHom :=
  ⟨(fun m _ => (m.factorial + 1, ()), fun _ _ _ => []), by
    intro m x hx _ _ _
    refine ⟨⟨?_, trivial⟩, fun _ _ _ y hy => ?_⟩
    · have hx2 : x.2 ≤ m := hx.2
      change (x.2.factorial + 1).minFac ≤ m.factorial + 1
      exact (Nat.minFac_le (by omega)).trans
        (Nat.add_le_add_right (Nat.factorial_le hx2) 1)
    · simp [minFacHom] at hy⟩

/-- The majorant data of `euclidH0Deriv`: the majorant of `minFacHom`. -/
def euclidH0MajD : Deriv.MajD euclidH0Deriv R0 :=
  (((), minFacMaj), ((Deriv.instSelf_majD _ _ (), ((), ())), conv_maj%))

/-- The majorant data of `euclidH1Deriv`: it has no term and no realized axiom. -/
def euclidH1MajD : Deriv.MajD euclidH1Deriv R0 :=
  (((), ((), ((), ((), ())))), ())

/-- The majorants of the translated hypotheses: the bounds of `euclidH0Deriv` and
`euclidH1Deriv`. -/
def euclidHm : CtxB fun k => (euclidCtx k).negT
  | ⟨0, _⟩ => (Deriv.bnd euclidH0Deriv R0 euclidH0MajD (fun k => k.elim0) 0).1
  | ⟨1, _⟩ => (Deriv.bnd euclidH1Deriv R0 euclidH1MajD (fun k => k.elim0) 0).1

/-- The majorants `euclidHm` majorize the witnesses `euclidW`. -/
theorem euclidHm_maj (k : Fin 2) :
    Maj (euclidCtx k).negT PUnit.unit (euclidHm k) (euclidW k) := by
  match k with
  | ⟨0, _⟩ =>
    exact (Deriv.bnd_sound euclidH0Deriv R0 (fun _ _ _ _ _ => trivial) euclidH0MajD
      (fun k => k.elim0) 0 PUnit.unit trivial (fun k => k.elim0) fun k => k.elim0).1
  | ⟨1, _⟩ =>
    exact (Deriv.bnd_sound euclidH1Deriv R0 (fun _ _ _ _ _ => trivial) euclidH1MajD
      (fun k => k.elim0) 0 PUnit.unit trivial (fun k => k.elim0) fun k => k.elim0).1

/-- The majorant data of `instSelfC`: the majorant `id` of the bound variable. -/
def instSelfC_majData {I : Type} {n : ℕ} {K : I → Type} {s : ∀ i, K i → ℕ}
    {X : Form (Σ i, K i)} {Δ : Fin n → Form (Σ i, K i)}
    (d : CDeriv Δ ((Form.all (K := K) (sz := s) X).sub Sigma.fst))
    (R : ℕ → I → Prop) (D : CDeriv.MajData d (envExt R s)) :
    CDeriv.MajData (instSelfC d) (envExt R s) :=
  ((Deriv.sndTermMaj s R, (D, conv_maj%)), conv_maj%)

/-- The environment of the variables `n` and `q`. -/
abbrev R2 : ℕ → J → Prop :=
  envExt (envExt R0 (K := fun _ => ℕ) idS) (K := fun _ : J0 => ℕ) idS

/-- The majorant data of `h1At`. -/
def h1At_majData {n : ℕ} {Δ : Fin n → Form J}
    (d : CDeriv Δ ((euclidH1.sub Sigma.fst).sub Sigma.fst))
    (D : CDeriv.MajData d R2) :
    CDeriv.MajData (h1At d) R2 :=
  instSelfC_majData _ _ ((⟨id, fun _ _ h => h.1.2⟩, (D, conv_maj%)), conv_maj%)

/-- The majorant data of `euclidDeriv`: the majorant `id` of each instantiated variable. -/
def euclidMajData : CDeriv.MajData euclidDeriv R0 :=
  (instSelfC_majData _ R0 ((), conv_maj%),
    ((Deriv.sndTermMaj idS _, (((h1At_majData _ ((), conv_maj%), ()), ()), conv_maj%)),
      conv_maj%))

/-- The selection is bounded by the maximum of the candidates. -/
theorem euclidSel_le (x : J0) (ys : Multiset ℕ) (B : ℕ) (h : mSize x ys ≤ B) :
    euclidSel x ys ≤ B := by
  change (ys.map id).sup ≤ B at h
  rw [Multiset.map_id] at h
  exact (Multiset.sup_mono (Multiset.filter_subset _ _)).trans h

/-- The majorant data of Markov's principle and of the selection at the maximum size of a multiset
of numbers: the selection has the majorant `id`. -/
def euclidPi2Maj : CDeriv.Pi2Maj euclidRel euclidSel euclidSel_spec mSize idS idS R0 :=
  CDeriv.Pi2Maj.ofSup euclidRel euclidSel euclidSel_spec id
    (fun x ys B h => euclidSel_le x ys B h) R0

/-- **The bound extracted from Euclid's proof** by the monotone interpretation of the extracted
derivation `CDeriv.pi2`. -/
def euclidBound : ℕ →o ℕ :=
  pi2Bound (Deriv.bnd (CDeriv.pi2 euclidRel euclidSel euclidSel_spec mSize euclidDeriv) R0
    (CDeriv.pi2MajD euclidRel euclidSel euclidSel_spec mSize euclidDeriv R0 euclidMajData
      euclidPi2Maj) euclidHm 0).1

/-- **The extracted function is bounded by the extracted bound.** -/
theorem euclidExtract_le (n : ℕ) : euclidExtract n ≤ euclidBound n :=
  (CDeriv.extract_costMaj' euclidRel euclidSel euclidSel_spec mSize euclidDeriv R0
    (fun _ _ _ _ _ => trivial) euclidMajData euclidPi2Maj euclidHm 0
    PUnit.unit trivial euclidW euclidHm_maj).2 n

/-- **Bound extraction of Euclid's theorem.** Every `n` has a prime above `n` and at most the
extracted bound at `n`. -/
theorem euclid_exists_le (n : ℕ) : ∃ p, p ≤ euclidBound n ∧ n < p ∧ p.Prime := by
  obtain ⟨y, hy, hp⟩ := CDeriv.exists_le_extract_pi2Bound' euclidRel euclidSel euclidSel_spec
    mSize euclidDeriv R0 (fun _ _ _ _ _ => trivial) euclidMajData euclidPi2Maj
    euclidHm 0 PUnit.unit trivial euclidW euclidHm_maj euclidW_mat n
  exact ⟨y, hy, hp⟩

end CatCrypt.Container.DNLogic.Euclid
