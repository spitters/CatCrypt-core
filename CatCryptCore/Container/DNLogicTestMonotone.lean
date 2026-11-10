/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogicMonoClassical
public import CatCryptCore.Container.DNLogicMono
public import CatCryptCore.Container.DNLogicNeg
public import CatCryptCore.Container.DNLogicMetastable
public import CatCryptCore.Container.DNLogicTestPrimes
public import Mathlib.Order.PartialSups
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# The iteration axiom of the monotone convergence benchmark

The combinatorial core of the metastability of a nondecreasing sequence `a : ℕ → ℚ` with values
in `[0, 1]`, as a realized axiom of the Diller–Nahm logic. The formula `gapHyp a` is

`∀ k, ¬ ∀ n, ∃ m, n ≤ m ∧ a m - a n > 1 / (k + 1)`.

The sequence `a` is a parameter of the terms: the sort context of `gapHyp a` is `PUnit`, the sorts
are the numbers `k`, `n`, `m` with the identity as size, and only the atom `gapRel a` mentions `a`.

The morphism `iterHom` from `⊤` to the negative translation of `gapHyp a` demands no
counter-witness of its premise, which is the uniform bound `N = 0` of `Deriv.hom`. Given `k` and a
witness of the translated `∀ n, ∃ m, …`, which yields for each `n` a finite multiset of candidates
`m`, its forward map demands the points `n₀ = 0`, `n_(j+1) = sup (h n_j)` for `j < k + 1`. Its
matrix obligation is the telescoping argument `telescope_gt`.

The majorant `iterHomMaj` sends a majorant `h*` of the candidate function to the list of the
iterates at `0` of `partialSups ĥ*`, the running maximum of `ĥ* x`, the maximum of the candidates
of `h* x`, of length `m + 1` at the bound `m` of `k`.

The classical derivation `cauchyDeriv` proves the Cauchy statement
`∀ k, ∃ n, ∀ m, n ≤ m → a m - a n ≤ 1 / (k + 1)` by reductio from `gapHyp a` and the atom link
`linkHyp a`, the entailment `¬ gap → cauchy` between the two atoms, which `CDeriv` has no rule for.
Both hypotheses are realized by closed derivations of their translations, `iterDeriv` and
`linkDeriv`, with the majorants `cauchyHm` from `Deriv.bnd`. `cauchy_candidates` is the
counterexample reading: at a function `G` with a Howard majorant `Gs` some candidate `n` satisfies
the atom at every `m ∈ G n`, and every candidate is at most the abstract bound `cauchyBound`.

## Main results

* `telescope_gt` — more than `k` increments above `1 / (k + 1)` contradict values in `[0, 1]`;
* `iter_le_iterMaj` — the iterates of a function lie below those of the running maximum of its
  Howard majorant;
* `iterHom`, `iterDeriv` — the realized axiom and its derivation from `⊤`;
* `iterHomMaj`, `iterMajD` — the majorant of the realized axiom;
* `cauchyDeriv`, `cauchyMajData` — the classical derivation of the Cauchy statement and its
  majorant data;
* `cauchyHm`, `cauchyHm_maj` — the majorants of the translated hypotheses;
* `cauchy_candidates` — the candidates of the counterexample reading and their bound.

## References

* T. Tao, *Structure and Randomness*, AMS (2008), finite convergence principle.
* A. Sipoş, *Rates of metastability for iterations on the unit interval*, J. Math. Anal. Appl. 502
  (2021).
* U. Kohlenbach, *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*,
  Springer (2008).

Search words: metastability, monotone convergence, finite convergence principle, proof mining,
rate of metastability, running maximum, partial supremum, Howard majorant, Diller–Nahm.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Container.DNLogic.Monotone

open DPred CatCrypt.Core Form

/-! ## Telescoping and iterates -/

/-- **The telescoping bound.** At least `k + 1` successive increments above `1 / (k + 1)` of a
sequence along arbitrary points contradict values in `[0, 1]`. -/
theorem telescope_gt {a : ℕ → ℚ} (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) {k K : ℕ}
    (hK : k + 1 ≤ K) {x : ℕ → ℕ}
    (hinc : ∀ j < K, 1 / ((k : ℚ) + 1) < a (x (j + 1)) - a (x j)) : False := by
  have hsum : ∑ _j ∈ Finset.range K, (1 / ((k : ℚ) + 1)) <
      ∑ j ∈ Finset.range K, (a (x (j + 1)) - a (x j)) :=
    Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by omega))
      fun j hj => hinc j (Finset.mem_range.1 hj)
  rw [Finset.sum_range_sub (fun j => a (x j)), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hk : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have hKk : (k : ℚ) + 1 ≤ K := by exact_mod_cast hK
  have hone : 1 ≤ (K : ℚ) * (1 / ((k : ℚ) + 1)) := by
    rw [mul_one_div, le_div_iff₀ hk]
    linarith
  linarith [h0 (x 0), h1 (x K)]

/-- The iterates at `0` of a function lie below those of a Howard majorant of it. -/
theorem iter_le_iter_of_maj {h hs : ℕ → ℕ} (hm : ∀ n x, n ≤ x → h n ≤ hs x) (j : ℕ) :
    h^[j] 0 ≤ hs^[j] 0 := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hm _ _ ih

/-- **The iterates at `0` of a function lie below those of the running maximum of a Howard
majorant.** -/
theorem iter_le_iterMaj {h hs : ℕ → ℕ} (hm : ∀ n x, n ≤ x → h n ≤ hs x) (j : ℕ) :
    h^[j] 0 ≤ (partialSups hs)^[j] 0 :=
  iter_le_iter_of_maj (fun n x hnx => (hm n x hnx).trans (le_partialSups hs x)) j

/-- The iterates at `0` of a function lie below those of its running maximum. -/
theorem iter_le_iter_partialSups (g : ℕ → ℕ) (j : ℕ) :
    g^[j] 0 ≤ (partialSups g)^[j] 0 :=
  iter_le_iter_of_maj (fun _ _ h => le_partialSups_of_le g h) j

/-! ## The formula -/

/-- A number is its own size. -/
abbrev idS {I : Type} : I → ℕ → ℕ := fun _ => id

/-- The sort context of the bound variable `k`. -/
abbrev J0 : Type := Σ _ : PUnit.{1}, ℕ

/-- The sort context of the bound variables `k` and `n`. -/
abbrev J1 : Type := Σ _ : J0, ℕ

/-- The sort context of the bound variables `k`, `n` and `m`. -/
abbrev J2 : Type := Σ _ : J1, ℕ

variable (a : ℕ → ℚ)

/-- The atom `n ≤ m ∧ a m - a n > 1 / (k + 1)` at `⟨⟨⟨_, k⟩, n⟩, m⟩`. -/
def gapRel (z : J2) : Prop := z.1.2 ≤ z.2 ∧ 1 / ((z.1.1.2 : ℚ) + 1) < a z.2 - a z.1.2

/-- The formula `∀ n, ∃ m, n ≤ m ∧ a m - a n > 1 / (k + 1)` over `k`. -/
def gapForm : Form J0 :=
  .all (K := fun _ : J0 => ℕ) (sz := idS)
    (.ex (K := fun _ : J1 => ℕ) (sz := idS) (.atom (gapRel a)))

/-- The formula `∀ k, ¬ ∀ n, ∃ m, n ≤ m ∧ a m - a n > 1 / (k + 1)`. -/
def gapHyp : Form PUnit.{1} := .all (K := fun _ => ℕ) (sz := idS) (Form.not (gapForm a))

/-- The formula `∀ m, ¬ (atom)ᴺ` over `k` and `n`, the premise of the negation under `∀ n` of the
negative translation of `gapForm a`. -/
abbrev candForm : Form J1 :=
  .all (K := fun _ : J1 => ℕ) (sz := idS) (Form.not (.atom (gapRel a) : Form J2).negT)

/-! ## The trivial witnesses -/

/-- The witness of `¬ p` that demands the atom. -/
def refuteW {I : Type} (p : I → Prop) (i : I) : (Form.not (.atom p : Form I)).dn.W i :=
  ⟨fun _ => PUnit.unit, fun _ _ => {PUnit.unit}⟩

/-- The witness of `¬ pᴺ` that answers each witness of `¬¬ p` with `refuteW`. -/
def dnegW {I : Type} (p : I → Prop) (i : I) : (Form.not (.atom p : Form I).negT).dn.W i :=
  ⟨fun _ => PUnit.unit, fun _ _ => {⟨refuteW p i, PUnit.unit⟩}⟩

/-- `dnegW` withstands every counter-witness at a point where the atom fails. -/
theorem dnegW_mat {I : Type} {p : I → Prop} {i : I} (hp : ¬ p i)
    (c : (Form.not (.atom p : Form I).negT).dn.C i (dnegW p i)) :
    (Form.not (.atom p : Form I).negT).dn.mat i (dnegW p i) c :=
  fun hq => hq _ (Multiset.mem_singleton_self _) fun _ _ hz =>
    hp (hz _ (Multiset.mem_singleton_self _))

/-- The trivial witness of `candForm a`. -/
def trivW (x : J1) : (candForm a).dn.W x := fun m => dnegW (gapRel a) ⟨x, m⟩

/-- The largest candidate `m` that a witness of the translated `∀ n, ∃ m, …` names at `n`. -/
def step (k : J0) (w : (gapForm a).negT.dn.W k) (n : ℕ) : ℕ :=
  (((w n).2 (trivW a ⟨k, n⟩) PUnit.unit).map Sigma.fst).sup

/-- The candidates of the forward map: the points `(step w)^[j] 0` for `j < k + 1`, each with the
trivial witness of `candForm a`. -/
def iterCand (k : J0) (w : (gapForm a).negT.dn.W k) : Multiset ((gapForm a).negT.dn.C k w) :=
  (Multiset.range (k.2 + 1)).map fun j =>
    ⟨(step a k w)^[j] 0, ⟨trivW a ⟨k, (step a k w)^[j] 0⟩, PUnit.unit⟩⟩

variable {a}

/-- A withstood candidate `n` has a candidate `m` at the gap. -/
theorem exists_gap (k : J0) (w : (gapForm a).negT.dn.W k) (n : ℕ)
    (hm : (gapForm a).negT.dn.mat k w ⟨n, ⟨trivW a ⟨k, n⟩, PUnit.unit⟩⟩) :
    ∃ m ∈ ((w n).2 (trivW a ⟨k, n⟩) PUnit.unit).map Sigma.fst, gapRel a ⟨⟨k, n⟩, m⟩ := by
  by_contra hne
  exact hm fun y hy => dnegW_mat (fun hg => hne ⟨y.1, Multiset.mem_map_of_mem _ hy, hg⟩) y.2

/-- A withstood candidate `n` has an increment above `1 / (k + 1)` to its largest candidate. -/
theorem gap_step (hmono : Monotone a) (k : J0) (w : (gapForm a).negT.dn.W k) (n : ℕ)
    (hm : (gapForm a).negT.dn.mat k w ⟨n, ⟨trivW a ⟨k, n⟩, PUnit.unit⟩⟩) :
    1 / ((k.2 : ℚ) + 1) < a (step a k w n) - a n := by
  obtain ⟨m, hmem, _, hgap⟩ := exists_gap k w n hm
  have hgap' : 1 / ((k.2 : ℚ) + 1) < a m - a n := hgap
  have hle : a m ≤ a (step a k w n) := hmono (Multiset.le_sup hmem)
  linarith

/-- **The matrix obligation of the realized axiom.** A witness of the translated
`∀ n, ∃ m, …` cannot withstand all candidates of `iterCand`. -/
theorem iterCand_false (hmono : Monotone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) (k : J0)
    (w : (gapForm a).negT.dn.W k)
    (H : ∀ x ∈ iterCand a k w, (gapForm a).negT.dn.mat k w x) : False := by
  refine telescope_gt h0 h1 (k := k.2) (K := k.2 + 1) le_rfl
    (x := fun j => (step a k w)^[j] 0) fun j hj => ?_
  have hg := gap_step hmono k w _ (H _ (Multiset.mem_map.2 ⟨j, Multiset.mem_range.2 hj, rfl⟩))
  simp only [Function.iterate_succ_apply']
  exact hg

/-- The classical truth of the negative translation of `gapHyp a`. -/
theorem gapHyp_eval (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) (i : PUnit.{1}) :
    (gapHyp a).negT.eval i := by
  intro k hX
  have hex : ∀ n, ∃ m, gapRel a ⟨⟨⟨i, k⟩, n⟩, m⟩ := fun n => by
    by_contra h
    exact hX n fun m hm => hm fun hp => h ⟨m, hp⟩
  choose f hf using hex
  refine (telescope_gt h0 h1 (k := k) (K := k + 1) le_rfl (x := fun j => f^[j] 0)
    fun j _ => ?_).elim
  simp only [Function.iterate_succ_apply']
  exact (hf _).2

/-! ## The realized axiom -/

/-- The forward map of the realized axiom at `k`: the witness of `¬¬⊥` that demands nothing, and
the candidates `iterCand`. -/
def iterFwd (a : ℕ → ℚ) (k : J0) : (Form.not (gapForm a)).negT.dn.W k :=
  ⟨fun _ => notW (Form.not Form.bot) k, fun w _ => iterCand a k w⟩

/-- **The realized axiom**: the morphism from `⊤` to the negative translation of `gapHyp a`. It
demands no counter-witness of `⊤`. -/
def iterHom (hmono : Monotone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) :
    (Form.top : Form PUnit.{1}).dn.Hom (gapHyp a).negT.dn where
  fwd i _ k := iterFwd a ⟨i, k⟩
  back _ _ _ := 0
  sound i _ c _ := fun H _ => (iterCand_false hmono h0 h1 ⟨i, c.1⟩ c.2.1 H).elim

/-- **The derivation of the translated axiom from `⊤`**, by `Deriv.hom` with `N = 0`. -/
def iterDeriv (hmono : Monotone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) {n : ℕ}
    (Γ : Fin n → Form PUnit.{1}) : Deriv Γ (gapHyp a).negT :=
  .hom (iterHom hmono h0 h1) 0 (fun _ _ _ => le_rfl) (fun i _ => gapHyp_eval h0 h1 i) .topI

/-! ## The majorant of the realized axiom -/

/-- The majorant of `refuteW`. -/
def refuteB {I : Type} (p : I → Prop) : (Form.not (.atom p : Form I)).B :=
  (fun _ => (), fun _ _ => [()])

/-- The majorant of `dnegW`. -/
def dnegB {I : Type} (p : I → Prop) : (Form.not (.atom p : Form I).negT).B :=
  (fun _ => (), fun _ _ => [(refuteB p, ())])

/-- `refuteB` majorizes `refuteW`. -/
theorem refute_maj {I : Type} (p : I → Prop) (i : I) :
    Maj (Form.not (.atom p : Form I)) i (refuteB p) (refuteW p i) :=
  fun _ _ _ => ⟨trivial, fun _ _ _ _ _ => ⟨(), List.mem_singleton_self _, trivial⟩⟩

/-- `dnegB` majorizes `dnegW`. -/
theorem dneg_maj {I : Type} (p : I → Prop) (i : I) :
    Maj (Form.not (.atom p : Form I).negT) i (dnegB p) (dnegW p i) := by
  intro _ _ _
  refine ⟨trivial, fun _ _ _ x hx => ⟨(refuteB p, ()), List.mem_singleton_self _, ?_⟩⟩
  obtain rfl : x = ⟨refuteW p i, PUnit.unit⟩ := Multiset.mem_singleton.1 hx
  exact ⟨refute_maj p i, trivial⟩

variable (a)

/-- The majorant of the trivial witness of `candForm a`. -/
def trivB : (candForm a).B := fun _ => dnegB (gapRel a)

/-- The maximum of the candidates that the majorant `hs` names at `x`. -/
def maxCand (hs : (gapForm a).negT.B) (x : ℕ) : ℕ :=
  ((((hs x).2 (trivB a) ()).map Prod.fst : List ℕ) : Multiset ℕ).sup

/-- The `j`-th iterate at `0` of the running maximum of `maxCand a hs`. -/
def iterMaj (hs : (gapForm a).negT.B) (j : ℕ) : ℕ := (partialSups (maxCand a hs))^[j] 0

variable {a}

/-- `trivB` majorizes `trivW`. -/
theorem triv_maj (x : J1) : Maj (candForm a) x (trivB a) (trivW a x) :=
  fun m _ _ => dneg_maj (gapRel a) ⟨x, m⟩

/-- The largest candidate at `n` is at most the maximum of the majorant's candidates at any
`x ≥ n`. -/
theorem step_le_maxCand (k : J0) (w : (gapForm a).negT.dn.W k) (hs : (gapForm a).negT.B)
    (hw : Maj (gapForm a).negT k hs w) (n x : ℕ) (hnx : n ≤ x) :
    step a k w n ≤ maxCand a hs x := by
  refine Multiset.sup_le.2 fun m hm => ?_
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hm
  obtain ⟨b, hb, hc⟩ := ((hw n x hnx) _ _ (triv_maj _)).2 () PUnit.unit trivial y hy
  exact (hc.1).trans (Multiset.le_sup (Multiset.mem_coe.2 (List.mem_map.2 ⟨b, hb, rfl⟩)))

/-- **The majorant of the realized axiom.** It sends a majorant of a witness of the translated
`∀ n, ∃ m, …` to the first `m + 1` iterates `iterMaj` at the bound `m` of `k`. -/
def iterHomMaj (hmono : Monotone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1)
    (R : ℕ → PUnit.{1} → Prop) :
    HomMaj R Form.top (gapHyp a).negT (iterHom hmono h0 h1) :=
  ⟨(fun _ _ m => (fun _ => (fun _ => (), fun _ _ => []), fun hs _ =>
      (List.range (m + 1)).map fun j => (iterMaj a hs j, (trivB a, ()))),
    fun _ _ _ => []), by
    intro _ i _ _ _ _
    refine ⟨fun k m hkm w hs hw => ⟨fun _ _ _ => ⟨trivial, fun _ _ _ x hx => ?_⟩,
      fun _ _ _ x hx => ?_⟩, fun _ _ _ x hx => ?_⟩
    · exact absurd hx (Multiset.notMem_zero x)
    · have hx' : x ∈ iterCand a ⟨i, k⟩ w := hx
      obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hx'
      exact ⟨(iterMaj a hs j, (trivB a, ())),
        List.mem_map.2 ⟨j, List.mem_range.2 (Nat.lt_succ_of_le
          ((Nat.le_of_lt_succ (Multiset.mem_range.1 hj)).trans hkm)), rfl⟩,
        iter_le_iterMaj (fun n x hnx => step_le_maxCand ⟨i, k⟩ w hs hw n x hnx) j,
        triv_maj _, trivial⟩
    · exact absurd hx (Multiset.notMem_zero x)⟩

/-- The majorant data of `iterDeriv`: the majorant `iterHomMaj`. -/
def iterMajD (hmono : Monotone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) {n : ℕ}
    (Γ : Fin n → Form PUnit.{1}) (R : ℕ → PUnit.{1} → Prop) :
    Deriv.MajD (iterDeriv hmono h0 h1 Γ) R :=
  ((), iterHomMaj hmono h0 h1 R)

/-! ## The Cauchy statement as a classical derivation -/

open Euclid (cconv instSelfC instSelfC_majData R0)

/-- The identity majorant of a conversion between formulas whose majorant types and
majorization agree definitionally. -/
local macro "conv_maj%" : term =>
  `(HomMaj.ofFun _ (fun b => b) (fun _ bc => bc) (by
    intro i a ba ha
    refine ⟨ha, fun bc c hc x hx => ?_⟩
    have e : x = c := Multiset.mem_singleton.1 hx
    subst e
    exact hc))

variable (a)

/-- The atom `n ≤ m → a m - a n ≤ 1 / (k + 1)` at `⟨⟨⟨_, k⟩, n⟩, m⟩`. -/
def cauchyRel (z : J2) : Prop := z.1.2 ≤ z.2 → a z.2 - a z.1.2 ≤ 1 / ((z.1.1.2 : ℚ) + 1)

/-- The formula `∀ m, n ≤ m → a m - a n ≤ 1 / (k + 1)` over `k` and `n`. -/
abbrev cauchyAll : Form J1 := .all (K := fun _ : J1 => ℕ) (sz := idS) (.atom (cauchyRel a))

/-- The formula `∃ n, ∀ m, n ≤ m → a m - a n ≤ 1 / (k + 1)` over `k`. -/
abbrev cauchyEx : Form J0 := .ex (K := fun _ : J0 => ℕ) (sz := idS) (cauchyAll a)

/-- **The Cauchy statement** `∀ k, ∃ n, ∀ m, n ≤ m → a m - a n ≤ 1 / (k + 1)`. -/
abbrev cauchyForm : Form PUnit.{1} :=
  Deriv.allExAll (K := fun _ : PUnit.{1} => ℕ) (L := fun _ : J0 => ℕ) (M := fun _ : J1 => ℕ)
    idS idS idS (cauchyRel a)

/-- The sort context of the hypothesis `linkHyp a`: its bound triple `⟨⟨⟨_, k⟩, n⟩, m⟩`. -/
abbrev L2 : Type := Σ _ : PUnit.{1}, J2

/-- The formula `¬ gap → cauchy` over the bound triple. -/
abbrev linkBody : Form L2 :=
  .imp (Form.not (.atom fun z : L2 => gapRel a z.2)) (.atom fun z : L2 => cauchyRel a z.2)

/-- **The atom link** `∀ z, ¬ gap z → cauchy z`, the classical step between the two atoms. The
quantifier has size `0`: its realizer is uniform in `z`. -/
def linkHyp : Form PUnit.{1} := .all (K := fun _ => J2) (sz := fun _ _ => 0) (linkBody a)

/-- The context of the derivation of the Cauchy statement. -/
def cauchyCtx : Fin 2 → Form PUnit.{1} := consF (gapHyp a) (consF (linkHyp a) Fin.elim0)

/-- The instance of `linkHyp a` at the variables `k`, `n`, `m` of the sort context `J2`. -/
def linkAt {n : ℕ} {Δ : Fin n → Form J2}
    (d : CDeriv Δ ((((linkHyp a).sub Sigma.fst).sub Sigma.fst).sub Sigma.fst)) :
    CDeriv Δ (.imp (Form.not (.atom (gapRel a))) (.atom (cauchyRel a))) :=
  cconv _ _ (.allE (K := fun _ : J2 => J2) (s := fun _ _ => 0) (fun j => j)
    (φ := (linkBody a).sub fun y : (Σ _ : J2, J2) => (⟨PUnit.unit, y.2⟩ : L2))
    (cconv _ (.all (K := fun _ : J2 => J2) (sz := fun _ _ => 0) _) d))

/-- The formula `∃ m, gap (k, n, m)` over `k` and `n`. -/
abbrev gapEx : Form J1 := .ex (K := fun _ : J1 => ℕ) (sz := idS) (.atom (gapRel a))

/-- The step at the atom: from the negation of `∃ m, gap` and the atom link, the atom `cauchy`. -/
def cauchyAtom {n : ℕ} {Δ : Fin n → Form J2}
    (dneg : CDeriv (consF (.atom (gapRel a)) Δ) (Form.not ((gapEx a).sub Sigma.fst)))
    (dlink : CDeriv Δ (.imp (Form.not (.atom (gapRel a))) (.atom (cauchyRel a)))) :
    CDeriv Δ (.atom (cauchyRel a)) :=
  .impE dlink (.impI (.impE dneg
    (cconv (.ex (K := fun _ : J2 => ℕ) (sz := idS)
        (.atom fun z : (Σ _ : J2, ℕ) => gapRel a ⟨z.1.1, z.2⟩)) _
      (.exI (fun j => j.2) (cconv (.atom (gapRel a)) _ (.hyp ⟨0, by omega⟩))))))

/-- The step at `n`: the negation of `∃ n, ∀ m, cauchy` refuted by a proof of `∀ m, cauchy`. -/
def cauchyGap {n : ℕ} {Δ : Fin n → Form J1}
    (dneg : CDeriv Δ (Form.not ((cauchyEx a).sub Sigma.fst)))
    (dall : CDeriv Δ (cauchyAll a)) : CDeriv Δ Form.bot :=
  .impE dneg (cconv (.ex (K := fun _ : J1 => ℕ) (sz := idS)
      ((cauchyAll a).sub fun y : (Σ _ : J1, ℕ) => (⟨y.1.1, y.2⟩ : J1))) _
    (.exI (fun j => j.2) (cconv (cauchyAll a) _ dall)))

/-- **The Cauchy statement as a classical derivation** from `gapHyp a` and the atom link
`linkHyp a`: by reductio, the classical quantifier shift `¬ ∃ n ∀ m, p → ∀ n ∃ m, ¬ p` feeds the
hypothesis at `k`. -/
def cauchyDeriv : CDeriv (cauchyCtx a) (cauchyForm a) :=
  .allI (.raa (.impE
    (instSelfC (cconv _ ((gapHyp a).sub Sigma.fst) (.hyp ⟨1, by omega⟩)))
    (cconv (.all (K := fun _ : J0 => ℕ) (sz := idS) (gapEx a)) _
      (.allI (.raa (cauchyGap a (cconv _ _ (.hyp ⟨1, by omega⟩))
        (.allI (cauchyAtom a (cconv _ _ (.hyp ⟨1, by omega⟩))
          (linkAt a (cconv _ _ (.hyp ⟨3, by omega⟩)))))))))))

/-! ## The realized atom link -/

/-- `¬ gap` implies `cauchy`. -/
theorem cauchyRel_of_not_gap (z : J2) (h : ¬ gapRel a z) : cauchyRel a z := by
  intro hnm
  by_contra hlt
  exact h ⟨hnm, not_le.1 hlt⟩

/-- The witness of `¬¬ p` that demands one counter-witness of `¬ p`. -/
def ddW {I : Type} (p : I → Prop) (i : I) : (Form.not (Form.not (.atom p))).dn.W i :=
  ⟨fun _ => PUnit.unit, fun _ _ => {⟨PUnit.unit, PUnit.unit⟩}⟩

/-- The majorant of `ddW`. -/
def ddB {I : Type} (p : I → Prop) : (Form.not (Form.not (.atom p : Form I))).B :=
  (fun _ => (), fun _ _ => [((), ())])

/-- `ddB` majorizes `ddW`. -/
theorem dd_maj {I : Type} (p : I → Prop) (i : I) :
    Maj (Form.not (Form.not (.atom p : Form I))) i (ddB p) (ddW p i) :=
  fun _ _ _ => ⟨trivial, fun _ _ _ _ _ => ⟨((), ()), List.mem_singleton_self _, trivial, trivial⟩⟩

/-- The witness of the translated atom link at the bound triple `z`. -/
def linkFwd (z : L2) : (linkBody a).negT.dn.W z :=
  ⟨fun _ => ddW (fun z : L2 => cauchyRel a z.2) z,
    fun _ _ => {⟨ddW (fun z : L2 => gapRel a z.2) z,
      ⟨refuteW (fun _ : L2 => False) z, PUnit.unit⟩⟩}⟩

/-- **The atom link as a realized axiom**: the morphism from `⊤` to the negative translation of
`linkHyp a`. -/
def linkHom : (Form.top : Form PUnit.{1}).dn.Hom (linkHyp a).negT.dn where
  fwd i _ z := linkFwd a ⟨i, z⟩
  back _ _ _ := 0
  sound i _ c _ := fun hP hQ => by
    by_cases hg : gapRel a c.1
    · exact (hP _ (Multiset.mem_singleton_self _) (fun y _ hz =>
        hz _ (Multiset.mem_singleton_self _) fun _ _ => hg)) fun _ _ hz =>
        hz _ (Multiset.mem_singleton_self _)
    · exact hQ _ (Multiset.mem_singleton_self _) fun _ _ => cauchyRel_of_not_gap a _ hg

/-- The negative translation of `linkHyp a` as a closed derivation, from the realized axiom. -/
def linkDeriv : Deriv (Fin.elim0 : Fin 0 → Form PUnit.{1}) (linkHyp a).negT :=
  .hom (linkHom a) 0 (fun _ _ _ => le_rfl) (fun i _ z hp hc => by
    by_cases hg : gapRel a z
    · exact hp (fun h => h hg) fun h => h
    · exact hc (cauchyRel_of_not_gap a z hg)) .topI

/-- The majorant of the translated atom link. -/
def linkB : (linkBody a).negT.B :=
  (fun _ => ddB (fun z : L2 => cauchyRel a z.2),
    fun _ _ => [(ddB (fun z : L2 => gapRel a z.2), (refuteB (fun _ : L2 => False), ()))])

/-- The majorant of the realized atom link. -/
def linkHomMaj (R : ℕ → PUnit.{1} → Prop) :
    HomMaj R Form.top (linkHyp a).negT (linkHom a) :=
  ⟨(fun _ _ _ => linkB a, fun _ _ _ => []), by
    intro _ i _ _ _ _
    refine ⟨fun z _ _ x bx hx => ⟨dd_maj _ _, fun _ _ _ d hd => ?_⟩, fun _ _ _ x hx => ?_⟩
    · have hd' := Multiset.mem_singleton.1 hd
      subst hd'
      exact ⟨_, List.mem_singleton_self _, dd_maj _ _, refute_maj _ _, trivial⟩
    · exact absurd hx (Multiset.notMem_zero x)⟩

/-- The majorant data of `linkDeriv`. -/
def linkMajD (R : ℕ → PUnit.{1} → Prop) : Deriv.MajD (linkDeriv a) R :=
  ((), linkHomMaj a R)

/-! ## The witnesses and majorants of the translated hypotheses -/

variable {a}

/-- The witness of the translated hypotheses: the realizers of `iterDeriv` and `linkDeriv`. -/
def cauchyW (hmono : Monotone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) :
    (ctx fun k => (cauchyCtx a k).negT).W PUnit.unit
  | ⟨0, _⟩ => (iterDeriv hmono h0 h1 Fin.elim0).realize.fwd PUnit.unit fun k => k.elim0
  | ⟨1, _⟩ => (linkDeriv a).realize.fwd PUnit.unit fun k => k.elim0

/-- `cauchyW` withstands every counter-witness of the translated hypotheses. -/
theorem cauchyW_mat (hmono : Monotone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1)
    (c : (ctx fun k => (cauchyCtx a k).negT).C PUnit.unit (cauchyW hmono h0 h1)) :
    (ctx fun k => (cauchyCtx a k).negT).mat PUnit.unit (cauchyW hmono h0 h1) c := by
  obtain ⟨⟨k, hk⟩, c⟩ := c
  match k, hk, c with
  | 0, _, c => exact (iterDeriv hmono h0 h1 Fin.elim0).realize.sound _ _ c fun x _ => x.1.elim0
  | 1, _, c => exact (linkDeriv a).realize.sound _ _ c fun x _ => x.1.elim0

/-- The majorants of the translated hypotheses, through `Deriv.bnd` of the closed derivations. -/
def cauchyHm (hmono : Monotone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) :
    CtxB fun k => (cauchyCtx a k).negT
  | ⟨0, _⟩ => (Deriv.bnd (iterDeriv hmono h0 h1 Fin.elim0) R0
      (iterMajD hmono h0 h1 Fin.elim0 R0) (fun k => k.elim0) 0).1
  | ⟨1, _⟩ => (Deriv.bnd (linkDeriv a) R0 (linkMajD a R0) (fun k => k.elim0) 0).1

/-- The majorants `cauchyHm` majorize the witnesses `cauchyW`. -/
theorem cauchyHm_maj (hmono : Monotone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) (k : Fin 2) :
    Maj (cauchyCtx a k).negT PUnit.unit (cauchyHm hmono h0 h1 k) (cauchyW hmono h0 h1 k) := by
  match k with
  | ⟨0, _⟩ =>
    exact (Deriv.bnd_sound (iterDeriv hmono h0 h1 Fin.elim0) R0 (fun _ _ _ _ _ => trivial)
      (iterMajD hmono h0 h1 Fin.elim0 R0) (fun k => k.elim0) 0 PUnit.unit trivial
      (fun k => k.elim0) fun k => k.elim0).1
  | ⟨1, _⟩ =>
    exact (Deriv.bnd_sound (linkDeriv a) R0 (fun _ _ _ _ _ => trivial) (linkMajD a R0)
      (fun k => k.elim0) 0 PUnit.unit trivial (fun k => k.elim0) fun k => k.elim0).1

/-! ## The majorant data of the derivation -/

variable (a) in
/-- The majorant data of `linkAt`: the constant `0` bounds the size of the instantiated triple. -/
def linkAtMajData {R : ℕ → J2 → Prop} {n : ℕ} {Δ : Fin n → Form J2}
    (d : CDeriv Δ ((((linkHyp a).sub Sigma.fst).sub Sigma.fst).sub Sigma.fst))
    (D : CDeriv.MajData d R) : CDeriv.MajData (linkAt a d) R :=
  ((⟨fun _ => 0, fun _ _ _ => le_rfl⟩, (D, conv_maj%)), conv_maj%)

variable (a) in
/-- The majorant data of `cauchyAtom`: the majorant `id` of the variable `m`. -/
def cauchyAtomD {R : ℕ → J1 → Prop} {n : ℕ} {Δ : Fin n → Form J2}
    {dneg : CDeriv (consF (.atom (gapRel a)) Δ) (Form.not ((gapEx a).sub Sigma.fst))}
    {dlink : CDeriv Δ (.imp (Form.not (.atom (gapRel a))) (.atom (cauchyRel a)))}
    (Dneg : CDeriv.MajData dneg (envExt R (K := fun _ : J1 => ℕ) idS))
    (Dlink : CDeriv.MajData dlink (envExt R (K := fun _ : J1 => ℕ) idS)) :
    CDeriv.MajData (cauchyAtom a dneg dlink) (envExt R (K := fun _ : J1 => ℕ) idS) :=
  (Dlink, (Dneg, ((Deriv.sndTermMaj idS _, ((), conv_maj%)), conv_maj%)))

variable (a) in
/-- The majorant data of `cauchyGap`: the majorant `id` of the variable `n`. -/
def cauchyGapD {R : ℕ → J0 → Prop} {n : ℕ} {Δ : Fin n → Form J1}
    {dneg : CDeriv Δ (Form.not ((cauchyEx a).sub Sigma.fst))}
    {dall : CDeriv Δ (cauchyAll a)}
    (Dneg : CDeriv.MajData dneg (envExt R (K := fun _ : J0 => ℕ) idS))
    (Dall : CDeriv.MajData dall (envExt R (K := fun _ : J0 => ℕ) idS)) :
    CDeriv.MajData (cauchyGap a dneg dall) (envExt R (K := fun _ : J0 => ℕ) idS) :=
  (Dneg, ((Deriv.sndTermMaj idS _, (Dall, conv_maj%)), conv_maj%))

variable (a) in
/-- The majorant data of `cauchyDeriv`: the majorant `id` of each instantiated variable and the
identity majorant of each conversion. -/
def cauchyMajData : CDeriv.MajData (cauchyDeriv a) R0 :=
  (instSelfC_majData _ R0 ((), conv_maj%),
    (cauchyGapD a ((), conv_maj%)
      (cauchyAtomD a ((), conv_maj%) (linkAtMajData a _ ((), conv_maj%))), conv_maj%))

variable (a) in
/-- The bound on the candidates at `k` and a majorant `Gs` of the counterexample function, read
from the bound of the translated derivation of the Cauchy statement. -/
def cauchyBound (hmono : Monotone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) (k : ℕ)
    (Gs : ℕ → List ℕ) : ℕ :=
  CDeriv.metaBound (K := fun _ : PUnit.{1} => ℕ) (L := fun _ : J0 => ℕ) (M := fun _ : J1 => ℕ)
    idS idS idS (cauchyRel a)
    (Deriv.bnd (cauchyDeriv a).translate R0 (CDeriv.translateMajD (cauchyDeriv a) R0
      (cauchyMajData a)) (cauchyHm hmono h0 h1) 0).1 k Gs

/-- **The counterexample reading of the Cauchy statement.** For a counterexample function `G` with
a Howard majorant `Gs`, the realizer of the translated derivation gives candidates at `k`, each at
most the abstract bound `cauchyBound`, and one candidate `n` satisfies
`n ≤ m → a m - a n ≤ 1 / (k + 1)` at every `m ∈ G n`. -/
theorem cauchy_candidates (hmono : Monotone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) (k : ℕ)
    (G : ℕ → Multiset ℕ) (Gs : ℕ → List ℕ)
    (hG : ∀ y j, y ≤ j → ∀ z ∈ G y, ∃ b ∈ Gs j, z ≤ b) :
    (∀ y ∈ CDeriv.metaCandidates (K := fun _ : PUnit.{1} => ℕ) (L := fun _ : J0 => ℕ)
        (M := fun _ : J1 => ℕ) idS idS idS (cauchyRel a)
        ((cauchyDeriv a).translate.realize.fwd PUnit.unit (cauchyW hmono h0 h1)) k G,
      y ≤ cauchyBound a hmono h0 h1 k Gs) ∧
    ∃ y ∈ CDeriv.metaCandidates (K := fun _ : PUnit.{1} => ℕ) (L := fun _ : J0 => ℕ)
        (M := fun _ : J1 => ℕ) idS idS idS (cauchyRel a)
        ((cauchyDeriv a).translate.realize.fwd PUnit.unit (cauchyW hmono h0 h1)) k G,
      ∀ z ∈ G y, cauchyRel a ⟨⟨⟨PUnit.unit, k⟩, y⟩, z⟩ :=
  CDeriv.exAll_candidates idS idS idS (cauchyRel a) (cauchyDeriv a) R0
    (fun _ _ _ _ _ => trivial) (cauchyMajData a) (cauchyHm hmono h0 h1) 0 PUnit.unit trivial
    (cauchyW hmono h0 h1) (cauchyHm_maj hmono h0 h1) (cauchyW_mat hmono h0 h1) k k le_rfl G Gs hG

end CatCrypt.Container.DNLogic.Monotone
