/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogicMonoClassical
public import CatCryptCore.Container.DNLogicMono
public import CatCryptCore.Container.DNLogicNeg
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

## Main results

* `telescope_gt` — more than `k` increments above `1 / (k + 1)` contradict values in `[0, 1]`;
* `iter_le_iterMaj` — the iterates of a function lie below those of the running maximum of its
  Howard majorant;
* `iterHom`, `iterDeriv` — the realized axiom and its derivation from `⊤`;
* `iterHomMaj`, `iterMajD` — the majorant of the realized axiom.

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

end CatCrypt.Container.DNLogic.Monotone
