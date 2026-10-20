/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.OWF
public import CatCryptCore.Crypto.HybridArgument
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.BindSwap

/-!
# Forward-secure pseudorandom generators

A forward-secure PRG (FS-PRG) is a stateful generator: each step maps the state `s` to an
output `r` and a next state `s'`. Forward security asks that after a compromise of the state
reached after `n` steps, the `n` earlier outputs together with that state are
indistinguishable from uniform outputs and a uniform state (Alwen, Coretti and Dodis, the
double-ratchet decomposition, Definition 9). The step is a PRG
`G : PRGDef St (Out × St)` of the core PRG game.

## Main definitions

* `fsprgRun` — the outputs and the final state of `n` steps from a state
* `fsprg_real`, `fsprg_ideal`, `FSPRG_Advantage` — the forward-security game: `n` outputs
  and the final state from a uniform initial state, against `n` uniform outputs and a
  uniform state
* `fsprgHyb` — the hybrid in which the first `i` outputs are uniform
* `fsprgView`, `fsprgRedOf`, `fsprgRed` — the PRG distinguisher of hybrid step `i`, which
  samples `i` uniform outputs and calls the adversary on the view built from them and the
  challenge

## Main results

* `fsprgHyb_zero`, `fsprgHyb_self` — the end points of the hybrids are the two games
* `fsprgHyb_bind_eq_real`, `fsprgHyb_succ_bind_eq_ideal` — hybrid step `i` is the PRG game
  of `fsprgRed`
* `fsprg_advantage_le` — for every adversary `A`, the FS-PRG advantage is at most the sum of
  the PRG advantages of the `n` reductions `fsprgRed G n i A`
* `fsprgRedOf.tree.timeBound_timed` — the time of the costed reduction

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4.1
* M. Bellare, B. Yee, *Forward-Security in Private-Key Cryptography*, CT-RSA 2003
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-! ## The stateful generator -/

/-- The outputs and the final state of `n` steps of the stateful generator `G` from the state
`s`: step `k` maps the state `s_k` to the output and the next state `G.stretch s_k`. -/
def fsprgRun {St Out : Type} (G : PRGDef St (Out × St)) : ℕ → St → List Out × St
  | 0, s => ([], s)
  | n + 1, s =>
    ((G.stretch s).1 :: (fsprgRun G n (G.stretch s).2).1, (fsprgRun G n (G.stretch s).2).2)

/-- `fsprgRun` of `n + 1` steps is the first output followed by `n` steps from the next
state. -/
theorem fsprgRun_succ {St Out : Type} (G : PRGDef St (Out × St)) (n : ℕ) (s : St) :
    fsprgRun G (n + 1) s =
      ((G.stretch s).1 :: (fsprgRun G n (G.stretch s).2).1,
        (fsprgRun G n (G.stretch s).2).2) := rfl

variable {St Out : Type} [Fintype St] [Nonempty St] [Fintype Out] [Nonempty Out]

/-! ## The forward-security game -/

/-- FS-PRG real game: the `n` outputs and the final state of the generator from a uniform
state. -/
noncomputable def fsprg_real (G : PRGDef St (Out × St)) (n : ℕ) : SPComp (List Out × St) := do
  let s ← SPComp.sample St
  SPComp.pure (fsprgRun G n s)

/-- FS-PRG ideal game: `n` uniform outputs and a uniform state. -/
noncomputable def fsprg_ideal (n : ℕ) : SPComp (List Out × St) := do
  let v ← SPComp.sample (Fin n → Out)
  let s ← SPComp.sample St
  SPComp.pure (List.ofFn v, s)

/-- FS-PRG advantage of the distinguisher `A`, which receives the outputs and the state
reached after them. -/
noncomputable def FSPRG_Advantage (G : PRGDef St (Out × St)) (n : ℕ)
    (A : List Out × St → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (fsprg_real G n) (fsprg_ideal n) A

/-! ## Hybrids and the reduction -/

/-- Hybrid `i` of `n`: the first `i` outputs are uniform, the remaining `n - i` outputs and
the final state are generated from a uniform state. -/
noncomputable def fsprgHyb (G : PRGDef St (Out × St)) (n i : ℕ) :
    SPComp (List Out × St) := do
  let v ← SPComp.sample (Fin i → Out)
  let s ← SPComp.sample St
  SPComp.pure (List.ofFn v ++ (fsprgRun G (n - i) s).1, (fsprgRun G (n - i) s).2)

/-- The view of hybrid step `i` built from the `i` uniform outputs `v` and the PRG challenge
`y`: the outputs `v`, the challenge output `y.1`, and the outputs and final state of the
remaining `n - (i + 1)` steps from the challenge state `y.2`. -/
def fsprgView (G : PRGDef St (Out × St)) (n i : ℕ) (v : Fin i → Out) (y : Out × St) :
    List Out × St :=
  (List.ofFn v ++ y.1 :: (fsprgRun G (n - (i + 1)) y.2).1, (fsprgRun G (n - (i + 1)) y.2).2)

/-- The PRG distinguisher with the view function `view`: on the challenge `y`, it samples `i`
uniform outputs `v` and calls `A` on `view v y`. -/
noncomputable def fsprgRedOf {i : ℕ} (view : (Fin i → Out) → Out × St → List Out × St)
    (A : List Out × St → SPComp Bool) (y : Out × St) : SPComp Bool := do
  let v ← SPComp.sample (Fin i → Out)
  A (view v y)

/-- The PRG distinguisher of hybrid step `i`: `fsprgRedOf` with the view `fsprgView`. -/
noncomputable def fsprgRed (G : PRGDef St (Out × St)) (n i : ℕ)
    (A : List Out × St → SPComp Bool) : Out × St → SPComp Bool :=
  fsprgRedOf (fsprgView G n i) A

omit [Fintype St] [Nonempty St] [Fintype Out] [Nonempty Out] in
/-- The list of a vector extended at the end by `a` is the list of the vector followed by
`a`. -/
theorem ofFn_snoc {α : Type} {n : ℕ} (v : Fin n → α) (a : α) :
    List.ofFn (Fin.snoc (α := fun _ => α) v a) = List.ofFn v ++ [a] := by
  rw [List.ofFn_succ_last]; simp

/-- The list of a vector extended at the front by `a` is `a` followed by the list of the
vector. -/
theorem ofFn_cons {α : Type} {n : ℕ} (v : Fin n → α) (a : α) :
    List.ofFn (Fin.cons (α := fun _ => α) a v) = a :: List.ofFn v := by
  simp [List.ofFn_succ]

omit [Fintype St] [Nonempty St] in
/-- Binding a uniform sample of a type with one element is the continuation at that
element. -/
theorem sample_bind_unique {α β : Type} [Fintype α] [Unique α] (k : α → SPComp β) :
    SPComp.bind (SPComp.sample α) k = k default := by
  have hk : k = fun _ => k default := by
    funext a; rw [Unique.eq_default a]
  rw [hk]
  funext h
  simp only [SPComp.bind_def, SPComp.sample, SDistr.bind_assoc, SDistr.pure_bind,
    SDistr.uniform_bind_const]

/-- Hybrid `0` is the real game. -/
theorem fsprgHyb_zero (G : PRGDef St (Out × St)) (n : ℕ) :
    fsprgHyb G n 0 = fsprg_real G n := by
  unfold fsprgHyb fsprg_real; simp [sample_bind_unique]

/-- Hybrid `n` is the ideal game. -/
theorem fsprgHyb_self (G : PRGDef St (Out × St)) (n : ℕ) :
    fsprgHyb G n n = fsprg_ideal n := by
  simp only [fsprgHyb, fsprg_ideal, Nat.sub_self, fsprgRun, List.append_nil]

/-- Hybrid `i < n` is the real PRG game of `fsprgRed G n i A`. -/
theorem fsprgHyb_bind_eq_real (G : PRGDef St (Out × St)) {n i : ℕ} (hi : i < n)
    (A : List Out × St → SPComp Bool) :
    (fsprgHyb G n i).bind A = (prg_real G).bind (fsprgRed G n i A) := by
  have hn : n - i = n - (i + 1) + 1 := by omega
  simp only [fsprgHyb, prg_real, fsprgRed, fsprgRedOf, fsprgView, hn, fsprgRun_succ,
    SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  exact SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)

/-- Hybrid `i + 1` is the ideal PRG game of `fsprgRed G n i A`. -/
theorem fsprgHyb_succ_bind_eq_ideal (G : PRGDef St (Out × St)) (n i : ℕ)
    (A : List Out × St → SPComp Bool) :
    (fsprgHyb G n (i + 1)).bind A =
      (prg_ideal (Output := Out × St)).bind (fsprgRed G n i A) := by
  simp only [fsprgHyb, SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  rw [← SPComp.sample_bind_equiv (Fin.snocEquiv fun _ => Out)]
  have he : ∀ (a : Out) (v : Fin i → Out), (Fin.snocEquiv fun _ => Out) (a, v) =
      Fin.snoc (α := fun _ => Out) v a := fun _ _ => rfl
  simp only [prg_ideal, fsprgRed, fsprgRedOf, fsprgView, SPComp.sample_prod_eq,
    SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind, he, ofFn_snoc,
    List.append_assoc, List.singleton_append]
  congr 1; funext a
  exact SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)

/-- **Forward security from PRG security.** For every distinguisher `A`, the FS-PRG advantage
over `n` steps is at most the sum over the hybrid steps `i < n` of the PRG advantages of the
reductions `fsprgRed G n i A`. -/
theorem fsprg_advantage_le (G : PRGDef St (Out × St)) (n : ℕ)
    (A : List Out × St → SPComp Bool) :
    FSPRG_Advantage G n A ≤
      ∑ i ∈ Finset.range n, PRG_Advantage G (fsprgRed G n i A) := by
  unfold FSPRG_Advantage
  rw [← fsprgHyb_zero, ← fsprgHyb_self]
  refine (HybridArgument.advantage_hybrid_dep (fsprgHyb G n) A n).trans
    (Finset.sum_le_sum fun i hi => le_of_eq ?_)
  unfold AdvantageA PRG_Advantage AdvantageA
  rw [fsprgHyb_bind_eq_real G (Finset.mem_range.mp hi), fsprgHyb_succ_bind_eq_ideal]

/-! ## The costed reduction -/

derive_reduction fsprgRedOf (adv := A)

/-- A sample node whose branches, each with its step cost, take time at most `T` has time at
most `1 + T`. -/
theorem timedSample_time_le {α : Type} (γ : Type) (finγ : Fintype γ)
    (neγ : Nonempty γ) (c : γ → ℕ) (k : γ → SPTree.Timed α) (T : ℕ)
    (h : ∀ b, c b + (k b).time ≤ T) : (SPTree.Timed.sample γ finγ neγ c k).time ≤ 1 + T := by
  rw [SPTree.Timed.time_sample]
  exact Nat.add_le_add_left (Finset.sup_le fun b _ => h b) 1

omit [Fintype St] [Nonempty St] in
/-- **Time of the FS-PRG reduction.** With the costed adversary `A` of time at most `T` and
call cost at most `a`, and the view function of cost at most `tv`, the costed reduction has
time at most `T + a + tv + 3`: one sample of the uniform outputs, one view, one adversary
call and the steps between them. For `fsprgRed G n i A` the view is `fsprgView G n i`, whose
cost is that of `n - (i + 1)` generator steps. -/
theorem fsprgRedOf.tree.timeBound_timed {i : ℕ}
    (view : (Fin i → Out) → Out × St → List Out × St)
    (viewCost : (Fin i → Out) → Out × St → ℕ)
    (A : List Out × St → SPTree.Timed Bool) (ACost : List Out × St → ℕ)
    {T a tv : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hv : ∀ v y, viewCost v y ≤ tv) (y : Out × St) :
    SPTree.Timed.stepTime (fsprgRedOf.tree.timed view viewCost A ACost y) ≤
      T + a + tv + 3 := by
  simp only [SPTree.Timed.stepTime, fsprgRedOf.tree.timed, SPTree.Timed.time_sample]
  have hs : (Finset.univ.sup fun b : Fin i → Out =>
      1 + (ACost (view b y) + (1 + viewCost b y)) + (A (view b y)).time) ≤ T + a + tv + 2 :=
    Finset.sup_le fun b _ => by
      have := hA (view b y); have := hAc (view b y); have := hv b y; omega
  omega

end CatCrypt.Crypto.Messaging
