/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.Core.SPTreeTimedOps
public import CatCryptCore.Tactics.ClassicalCostAudit

/-!
# Lemmas and definitions of the costed forms of `derive_timed`

The erasure lemmas, costed combinators and time bounds that the costed forms and erasure
theorems derived by `derive_timed` (`CatCryptCore.Tactics.DeriveTimed`) refer to:

* erasure of a step-prefixed tree commutes with `if` and dependent `if`
  (`OracleAdv.Timed.erase_snd_ite`, `OracleAdv.Timed.erase_snd_dite`);
* the time of a handler (`OracleAdv.Timed.timeBound_fold`);
* the costed simulation with costed closures in its state (`OracleAdv.Timed.simulateHat`), its
  erasure (`OracleAdv.Timed.erase_simulateHat_bind`) and its time
  (`OracleAdv.Timed.timeBound_simulateHat`, `OracleAdv.Timed.timeBound_simulateHat_inv`);
* the leaves of a costed tree (`OracleAdv.Timed.AllRet`) and their sequencing and monotonicity;
* the binds of `if` of oracle trees and computation trees (`OracleAdv.ite_bind`,
  `SPTree.ite_bind`);
* the case analysis of an optional value (`DeriveTimed.optionDispatch`), the compile equations
  of sampling from a sub-distribution, the companions of reads after updates
  (`DeriveTimed.updateCompanion_le`), and the costed folds (`DeriveTimed.foldlHat`,
  `DeriveTimed.foldrHat`) with their erasure and companion bounds.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv.Timed

variable {D R α : Type}

/-- Erasure of a step-prefixed tree commutes with `if`. -/
theorem erase_snd_ite (c : Prop) [Decidable c] (x y : ℕ × Timed D R α) :
    (if c then x else y).2.erase = if c then x.2.erase else y.2.erase := by
  split <;> rfl

/-- Erasure of a step-prefixed tree commutes with a dependent `if`. -/
theorem erase_snd_dite (c : Prop) [Decidable c] (x : c → ℕ × Timed D R α)
    (y : ¬c → ℕ × Timed D R α) :
    (if h : c then x h else y h).2.erase = if h : c then (x h).2.erase else (y h).2.erase := by
  split <;> rfl

/-- **Time of a handler.** Let `H` interpret a costed tree from a state, with overhead at most
`h` per unit of the tree: at a `rand` or `query` node whose continuation has step cost `c`,
`H` takes time `M` whenever every continuation `k b` takes time `M - (1 + h) * (1 + c b)`
from every state; at a leaf it takes time `r`. Then an adversary of time `T` is handled in
time `(1 + h) * T + r`. A costed form that `derive_timed` derives by recursion over an oracle
tree is such an `H`, and `OracleAdv.Timed.simulate` and `subst` are its stateful and stateless
cases with the cost of each query in the handler (`timeBound_simulate`). -/
theorem timeBound_fold {S D' R' β : Type} (H : Timed D R α → S → ℕ × Timed D' R' β)
    {h r : ℕ} (hret : ∀ a s, StepTimeBound (H (ret a) s) r)
    (hrand : ∀ {γ : Type} (p : PMF γ) (c : γ → ℕ) (k : γ → Timed D R α) (s : S) (M : ℕ),
      1 + h ≤ M → (∀ b, (1 + h) * (1 + c b) ≤ M) →
      (∀ b s', StepTimeBound (H (k b) s') (M - (1 + h) * (1 + c b))) →
      StepTimeBound (H (rand p c k) s) M)
    (hquery : ∀ (d : D) (c : R → ℕ) (k : R → Timed D R α) (s : S) (M : ℕ),
      1 + h ≤ M → (∀ b, (1 + h) * (1 + c b) ≤ M) →
      (∀ b s', StepTimeBound (H (k b) s') (M - (1 + h) * (1 + c b))) →
      StepTimeBound (H (query d c k) s) M)
    {A : Timed D R α} {T : ℕ} (hA : A.TimeBound T) (s : S) :
    StepTimeBound (H A s) ((1 + h) * T + r) := by
  induction A generalizing T s with
  | ret a => exact (hret a s).mono (Nat.le_add_left r _)
  | rand p c k ih =>
    refine hrand p c k s _ ?_ (fun b => ?_) (fun b s' => (ih b (hA.2 b).2 s').mono ?_)
    · exact (Nat.le_mul_of_pos_right _ hA.1).trans (Nat.le_add_right _ _)
    · have := (hA.2 b).1; have := hA.1
      exact (Nat.mul_le_mul_left _ (by omega)).trans (Nat.le_add_right _ _)
    · have e : (1 + h) * T = (1 + h) * (1 + c b) + (1 + h) * (T - 1 - c b) := by
        rw [← Nat.mul_add]; congr 1; have := (hA.2 b).1; have := hA.1; omega
      omega
  | query d c k ih =>
    refine hquery d c k s _ ?_ (fun b => ?_) (fun b s' => (ih b (hA.2 b).2 s').mono ?_)
    · exact (Nat.le_mul_of_pos_right _ hA.1).trans (Nat.le_add_right _ _)
    · have := (hA.2 b).1; have := hA.1
      exact (Nat.mul_le_mul_left _ (by omega)).trans (Nat.le_add_right _ _)
    · have e : (1 + h) * T = (1 + h) * (1 + c b) + (1 + h) * (T - 1 - c b) := by
        rw [← Nat.mul_add]; congr 1; have := (hA.2 b).1; have := hA.1; omega
      omega

/-- An `if` between two pairs is the pair of the `if`s of their components. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.ite_prod_mk {β γ : Type _} (c : Prop) [Decidable c]
    (a b : β) (a' b' : γ) :
    (if c then (a, a') else (b, b')) = (if c then a else b, if c then a' else b') := by
  split <;> rfl

/-- The first component of an `if` between two pairs. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.fst_ite {β γ : Type _} (c : Prop) [Decidable c]
    (p q : β × γ) : (if c then p else q).1 = if c then p.1 else q.1 := by
  split <;> rfl

/-- The second component of an `if` between two pairs. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.snd_ite {β γ : Type _} (c : Prop) [Decidable c]
    (p q : β × γ) : (if c then p else q).2 = if c then p.2 else q.2 := by
  split <;> rfl

/-- Erasure of a costed oracle tree commutes with an `if`. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.erase_ite_oracle {D R α : Type} (c : Prop)
    [Decidable c] (x y : Timed D R α) :
    (if c then x else y).erase = if c then x.erase else y.erase := by
  split <;> rfl

/-- `Sum.map` of two identity functions is the identity; stated with the functions as
abstractions, so that it applies to the round trip `fun x => (ι x).1` of erasure and lift, which
is an identity up to eta. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.sum_map_id_fun {α β : Type _} (x : α ⊕ β) :
    Sum.map (fun a => a) (fun b => b) x = x := by
  cases x <;> rfl

/-- The recursor of `Bool` at a constant motive is the `if` on its major premise. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.boolRec_eq_ite {α : Sort _} (f t : α) (b : Bool) :
    Bool.rec (motive := fun _ => α) f t b = if b = true then t else f := by
  cases b <;> rfl

/-- Erasure of a costed computation tree commutes with an `if`. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.erase_ite_spTree {α : Type} (c : Prop)
    [Decidable c] (x y : CatCrypt.Core.SPTree.Timed α) :
    (if c then x else y).erase = if c then x.erase else y.erase := by
  split <;> rfl

/-- The costed simulation of a handler whose state `Ŝ` carries costed closures: the
simulation `simulate impl A s`, with the erasure `ε : Ŝ → S` of the state and a lift
`ι : S → Ŝ` as parameters, which state its erasure theorem `erase_simulateHat_bind`. -/
@[expose] def simulateHat {D' R' S Ŝ : Type} (_ε : Ŝ → S) (_ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ)) (A : Timed D R α) (s : Ŝ) :
    ℕ × Timed D' R' (α × Ŝ) :=
  simulate impl A s

/-- **Erasure of a costed simulation with costed closures in its state.** If the erased
handler depends on the state only through its erasure `ε` (`h`), and so does the
continuation `k` (`hk`), then the erased costed simulation followed by `k` is the
simulation of the erased handler from the erased state, followed by `k` on the lifted
state. -/
theorem erase_simulateHat_bind {D' R' S Ŝ β : Type} (ε : Ŝ → S) (ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ))
    (h : ∀ s d, (impl s d).2.erase.bind (fun y => .ret (y.1, ε y.2)) =
      (impl (ι (ε s)) d).2.erase.bind (fun y => .ret (y.1, ε y.2)))
    (A : Timed D R α) (s : Ŝ) (k : α × Ŝ → OracleAdv D' R' β)
    (hk : ∀ y, k y = k (y.1, ι (ε y.2))) :
    (simulateHat ε ι impl A s).2.erase.bind k =
      (OracleAdv.simulate (fun s d => (impl (ι s) d).2.erase.bind fun y => .ret (y.1, ε y.2))
        A.erase (ε s)).bind fun y => k (y.1, ι y.2) := by
  unfold simulateHat
  induction A generalizing s with
  | ret a => exact hk (a, s)
  | rand p c k' ih => simp only [simulate, erase, OracleAdv.simulate, OracleAdv.bind, ih]
  | query d c k' ih =>
    simp only [simulate, delay, erase, OracleAdv.simulate, erase_bind]
    rw [← h s d]
    simp only [OracleAdv.bind_assoc, OracleAdv.bind_ret, ih]

/-- An oracle tree followed by `ret` is the tree. -/
theorem bind_ret_eq (t : OracleAdv D R α) : t.bind (fun y => .ret y) = t := by
  induction t with
  | ret a => rfl
  | rand p k ih => simp only [OracleAdv.bind, ih]
  | query d k ih => simp only [OracleAdv.bind, ih]

/-- **Sequencing after a tree with costed closures in its result.** If `t` followed by the
erasure `ε` of its results is `t₀`, and the continuation `k` depends on a result only through
its erasure, then `t` followed by `k` is `t₀` followed by `k` on the lifted result. -/
theorem bind_hat {α' β : Type} (ε : α' → α) (ι : α → α') (t : OracleAdv D R α')
    (t₀ : OracleAdv D R α) (h : t.bind (fun y => .ret (ε y)) = t₀)
    (k : α' → OracleAdv D R β) (hk : ∀ y, k y = k (ι (ε y))) :
    t.bind k = t₀.bind fun y => k (ι y) := by
  subst h
  rw [OracleAdv.bind_assoc]
  exact congrArg t.bind (funext hk)

/-- `AllRet P A`: every leaf `ret a` of the costed tree `A` satisfies `P a`. -/
@[expose] def AllRet (P : α → Prop) : Timed D R α → Prop
  | ret a => P a
  | rand _ _ k => ∀ b, AllRet P (k b)
  | query _ _ k => ∀ r, AllRet P (k r)

/-- Times add under sequencing when the continuation is bounded on the leaves of the tree
only (`timeBound_bind`, with the continuation's bound required where `P` holds). -/
theorem timeBound_bind_of_allRet {β : Type} {P : α → Prop} {A : Timed D R α}
    {f : α → ℕ × Timed D R β} {m n : ℕ} (hA : A.TimeBound m) (hP : AllRet P A)
    (hf : ∀ a, P a → StepTimeBound (f a) n) : StepTimeBound (A.bind f) (m + n) := by
  induction A generalizing m with
  | ret a => exact (hf a hP).mono (Nat.le_add_left n m)
  | rand p c k ih =>
    have h1 := hA.1
    simp only [bind, stepTimeBound_zero, timeBound_rand_iff]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hA.2 b).1
    exact (stepTimeBound_delay (c := c b) (ih b (hA.2 b).2 (hP b))).mono (by omega)
  | query d c k ih =>
    have h1 := hA.1
    simp only [bind, stepTimeBound_zero, timeBound_query_iff]
    refine ⟨by omega, fun r => ?_⟩
    have h2 := (hA.2 r).1
    exact (stepTimeBound_delay (c := c r) (ih r (hA.2 r).2 (hP r))).mono (by omega)

/-- **Simulation time with a state invariant.** Let `Inv i` hold of the states reached
after `i` queries: a program of `impl` from a state with `Inv i` has time at most `t i` and
returns states with `Inv (i + 1)`. Then an adversary of time `T` with at most `q` queries,
simulated from a state with `Inv i`, has time at most `T + ∑_{j < q} t (i + j)`. A handler
whose state carries a table of costed closures, whose companions grow by a bounded amount per
query, has a per-query time `t j` that grows with `j`, which a single uniform bound
(`timeBound_simulate`) does not state. -/
theorem timeBound_simulateHat_inv {D' R' S Ŝ : Type} (ε : Ŝ → S) (ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ)) (Inv : ℕ → Ŝ → Prop) (t : ℕ → ℕ)
    (himpl : ∀ i s d, Inv i s →
      StepTimeBound (impl s d) (t i) ∧ AllRet (fun y => Inv (i + 1) y.2) (impl s d).2)
    {A : Timed D R α} {T q : ℕ} (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q)
    (i : ℕ) (s : Ŝ) (hs : Inv i s) :
    StepTimeBound (simulateHat ε ι impl A s) (T + ∑ j ∈ Finset.range q, t (i + j)) := by
  unfold simulateHat
  induction A generalizing T q i s with
  | ret a => exact ⟨Nat.zero_le _, trivial⟩
  | rand p c k ih =>
    have h1 := hA.1
    simp only [simulate, stepTimeBound_zero, timeBound_rand_iff]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hA.2 b).1
    exact (stepTimeBound_delay (c := c b) (ih b (hA.2 b).2 (hq b) i s hs)).mono (by omega)
  | query d c k ih =>
    cases q with
    | zero => exact (hq : False).elim
    | succ q =>
      have hsum : ∑ j ∈ Finset.range (q + 1), t (i + j) =
          ∑ j ∈ Finset.range q, t (i + 1 + j) + t i := by
        rw [Finset.sum_range_succ']
        simp only [Nat.add_zero]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_assoc, Nat.add_comm 1 j]
      rw [hsum]
      have hk : ∀ x : R × Ŝ, Inv (i + 1) x.2 →
          StepTimeBound (delay (c x.1) (simulate impl (k x.1) x.2))
            (T - 1 + ∑ j ∈ Finset.range q, t (i + 1 + j)) := fun x hx =>
        (stepTimeBound_delay (ih x.1 (hA.2 x.1).2 (hq x.1) (i + 1) x.2 hx)).mono
          (by have := (hA.2 x.1).1; omega)
      have hi := himpl i s d hs
      have h := stepTimeBound_delay (c := (impl s d).1)
        (timeBound_bind_of_allRet hi.1.2 hi.2 hk)
      exact h.mono (by have := hi.1.1; have := hA.1; omega)

/-- Every leaf of a sequencing satisfies `P` when every leaf `a` of the first tree satisfies
`Q` and the continuation at such an `a` has all its leaves in `P`. -/
theorem allRet_bind {β : Type} {Q : α → Prop} {P : β → Prop} {A : Timed D R α}
    {f : α → ℕ × Timed D R β} (hA : AllRet Q A) (hf : ∀ a, Q a → AllRet P (f a).2) :
    AllRet P (A.bind f).2 := by
  induction A with
  | ret a => exact hf a hA
  | rand p c k ih => exact fun b => ih b (hA b)
  | query d c k ih => exact fun r => ih r (hA r)

/-- `AllRet` is monotone in its predicate. -/
theorem allRet_mono {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) {A : Timed D R α}
    (h : AllRet P A) : AllRet Q A := by
  induction A with
  | ret a => exact hPQ a h
  | rand p c k ih => exact fun b => ih b (h b)
  | query d c k ih => exact fun r => ih r (h r)

/-- **Final state of a simulation under a state invariant.** With `Inv` monotone in its
index and every program of `impl` from a state with `Inv i` returning states with
`Inv (i + 1)`, a simulation of an adversary with at most `q` queries from a state with
`Inv i` returns states with `Inv (i + q)`. -/
theorem allRet_simulateHat_inv {D' R' S Ŝ : Type} (ε : Ŝ → S) (ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ)) (Inv : ℕ → Ŝ → Prop)
    (himpl : ∀ i s d, Inv i s → AllRet (fun y => Inv (i + 1) y.2) (impl s d).2)
    (hmono : ∀ i s, Inv i s → Inv (i + 1) s)
    {A : Timed D R α} {q : ℕ} (hq : A.erase.IsQueryBound q) (i : ℕ) (s : Ŝ) (hs : Inv i s) :
    AllRet (fun y => Inv (i + q) y.2) (simulateHat ε ι impl A s).2 := by
  unfold simulateHat
  induction A generalizing q i s with
  | ret a =>
    change Inv (i + q) s
    clear hq
    induction q with
    | zero => exact hs
    | succ q ih => exact hmono _ _ ih
  | rand p c k ih => exact fun b => ih b (hq b) i s hs
  | query d c k ih =>
    cases q with
    | zero => exact (hq : False).elim
    | succ q =>
      refine allRet_bind (himpl i s d hs) fun x hx => ?_
      have h := ih x.1 (hq x.1) (i + 1) x.2 hx
      rwa [show i + 1 + q = i + (q + 1) by omega] at h

/-- **Simulation time of a handler over tables.** If the programs of `impl` from a lifted state
`ι s` have time at most `t` and return lifted states (`y.2 = ι (ε y.2)`), then an adversary of
time `T` with at most `q` queries, simulated from a lifted state, has time at most `T + q * t`.
This is `timeBound_simulateHat_inv` at the invariant that the state is a lift. -/
theorem timeBound_simulateHat {D' R' S Ŝ : Type} (ε : Ŝ → S) (ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ)) {t : ℕ}
    (himpl : ∀ s d, StepTimeBound (impl (ι s) d) t)
    (hret : ∀ s d, AllRet (fun y => y.2 = ι (ε y.2)) (impl (ι s) d).2)
    {A : Timed D R α} {T q : ℕ} (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q) (s : S) :
    StepTimeBound (simulateHat ε ι impl A (ι s)) (T + q * t) := by
  have h := timeBound_simulateHat_inv ε ι impl (fun _ x => ∃ s, x = ι s) (fun _ => t)
    (fun _ x d ⟨s, hs⟩ => hs ▸ ⟨himpl s d, allRet_mono (fun y hy => ⟨ε y.2, hy⟩) (hret s d)⟩)
    hA hq 0 (ι s) ⟨s, rfl⟩
  simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul] using h

end CatCrypt.Crypto.OracleAdv.Timed

namespace CatCrypt.Core.SPTree.Timed

/-- **Sequencing after a computation tree with costed closures in its result.** If `t`
followed by the erasure `ε` of its results is `t₀`, and the continuation `k` depends on a
result only through its erasure, then `t` followed by `k` is `t₀` followed by `k` on the
lifted result. -/
theorem bind_hat {α α' β : Type} (ε : α' → α) (ι : α → α') (t : SPTree α')
    (t₀ : SPTree α) (h : t.bind (fun y => .ret (ε y)) = t₀)
    (k : α' → SPTree β) (hk : ∀ y, k y = k (ι (ε y))) :
    t.bind k = t₀.bind fun y => k (ι y) := by
  subst h
  rw [SPTree.bind_assoc]
  exact congrArg t.bind (funext hk)

end CatCrypt.Core.SPTree.Timed

namespace CatCrypt.Crypto.OracleAdv

/-- The bind of an `if` is the `if` of the binds. -/
theorem ite_bind {D R α β : Type} (c : Prop) [Decidable c] (t e : OracleAdv D R α)
    (f : α → OracleAdv D R β) :
    (if c then t else e).bind f = if c then t.bind f else e.bind f := by
  split <;> rfl

/-- The bind of a dependent `if` is the dependent `if` of the binds. -/
theorem dite_bind {D R α β : Type} (c : Prop) [Decidable c] (t : c → OracleAdv D R α)
    (e : ¬c → OracleAdv D R α) (f : α → OracleAdv D R β) :
    (if h : c then t h else e h).bind f = if h : c then (t h).bind f else (e h).bind f := by
  split <;> rfl

end CatCrypt.Crypto.OracleAdv

namespace CatCrypt.Core.SPTree

/-- The bind of an `if` is the `if` of the binds. -/
theorem ite_bind {α β : Type} (c : Prop) [Decidable c] (t e : SPTree α) (f : α → SPTree β) :
    (if c then t else e).bind f = if c then t.bind f else e.bind f := by
  split <;> rfl

/-- The bind of a dependent `if` is the dependent `if` of the binds. -/
theorem dite_bind {α β : Type} (c : Prop) [Decidable c] (t : c → SPTree α) (e : ¬c → SPTree α)
    (f : α → SPTree β) :
    (if h : c then t h else e h).bind f = if h : c then (t h).bind f else (e h).bind f := by
  split <;> rfl

end CatCrypt.Core.SPTree

namespace CatCrypt.Tactics.DeriveTimed

open CatCrypt.Core

/-- The case analysis of `x : Option α` by `n` on `none` and `s` on `some`, written as a
`match`. Its matcher `optionDispatch.match_1` is the form in which a dispatch `Option.elim x n s`,
`Option.casesOn x n s` or `Option.rec n s x` on an optional value that is not a constructor is
kept (`optionDispatch?`). -/
@[expose] def optionDispatch.{u, w} {α : Type u} (motive : Option α → Sort w) (x : Option α)
    (n : motive none) (s : (a : α) → motive (some a)) : motive x :=
  match x with
  | none => n
  | some a => s a

/-- `Option.elim` is the case analysis `optionDispatch` at the constant motive. -/
theorem elim_eq_optionDispatch {α β : Type} (x : Option α) (n : β) (s : α → β) :
    x.elim n s = optionDispatch (fun _ => β) x n s := by
  cases x <;> rfl

/-- The compile equation of a sampling node of a sub-distribution followed by a continuation. -/
theorem compile_sampleDist_eq {α β : Type} {μ : Prob.SDistr β} {k : β → SPTree α}
    {k₀ : β → SPComp α} (h : ∀ b, (k b).compile = k₀ b) :
    (SPTree.sampleDist β μ k).compile = SPComp.bind (liftSDistr μ) k₀ := by
  simp only [SPTree.compile, funext h]

/-- The compile equation of a sampling node of a sub-distribution that returns its sample. -/
theorem compile_sampleDist_ret {β : Type} {μ : Prob.SDistr β} :
    (SPTree.sampleDist β μ fun b => .ret b).compile = liftSDistr μ := by
  simp only [SPTree.compile]
  exact SPComp.bind_pure _

/-- **A read after an update.** The companion of the costed closure of `Function.update f a v`,
a lookup, exceeds a bound `B` of the companion `fCost` of `f` by at most three. -/
theorem updateCompanion_le {α : Type} [DecidableEq α] (fCost : α → ℕ) {B : ℕ}
    (h : ∀ x, fCost x ≤ B) (a x : α) :
    2 + (if x = a then 0 else 1 + fCost x) ≤ B + 3 := by
  have := h x
  split <;> omega

/-- **Reads after `k` updates.** Companions `c k` bounded by `B` at `k = 0`, each of which is
bounded by `M + d` wherever the one before is bounded by `M` (an update, `updateCompanion_le`
with `d = 3`), are bounded by `B + d k`. -/
theorem companion_le_of_step {α : Type} (c : ℕ → α → ℕ) {B d : ℕ} (h0 : ∀ x, c 0 x ≤ B)
    (hs : ∀ k M, (∀ x, c k x ≤ M) → ∀ x, c (k + 1) x ≤ M + d) :
    ∀ k x, c k x ≤ B + d * k := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    intro x
    have := hs k _ ih x
    grind

/-- **Total cost of the reads after updates.** At most `r` reads after each of `g` updates, a
read after `i` updates costing at most `B + d i`, cost at most `g r B + d r g²`: the cost is
quadratic in the number of updates. -/
theorem sum_companion_le (g r B d : ℕ) (cost : ℕ → ℕ) (h : ∀ i, cost i ≤ r * (B + d * i)) :
    ((List.range g).map cost).sum ≤ g * r * B + d * r * (g * g) := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    have hg := h g
    grind

universe uA uC uB

/-- The costed left fold at an accumulator `α` holding functions, whose costed values have type
`α × C`: `List.foldl f' i l`, with the plain step `f` as a further argument, so that the erasure
lemma `foldlHat_fst` determines `f` from its left side. -/
@[expose] def foldlHat {α : Type uA} {C : Type uC} {β : Type uB} (_f : α → β → α)
    (f' : α × C → β → α × C) (i : α × C) (l : List β) : α × C :=
  List.foldl f' i l

/-- The erasure of the costed left fold: the left fold of the plain step from the erased
accumulator, when the costed step erases to the plain step. -/
theorem foldlHat_fst {α : Type uA} {C : Type uC} {β : Type uB} (f : α → β → α)
    (f' : α × C → β → α × C) (h : ∀ a x, (f' a x).1 = f a.1 x) (i : α × C) (l : List β) :
    (foldlHat f f' i l).1 = List.foldl f i.1 l := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    simp only [foldlHat, List.foldl_cons] at ih ⊢
    rw [ih, h]

/-- The costed right fold at an accumulator `α` holding functions, whose costed values have type
`α × C`: `List.foldr f' i l`, with the plain step `f` as a further argument (`foldrHat_fst`). -/
@[expose] def foldrHat {α : Type uA} {C : Type uC} {β : Type uB} (_f : β → α → α)
    (f' : β → α × C → α × C) (i : α × C) (l : List β) : α × C :=
  List.foldr f' i l

/-- The erasure of the costed right fold: the right fold of the plain step from the erased
accumulator, when the costed step erases to the plain step. -/
theorem foldrHat_fst {α : Type uA} {C : Type uC} {β : Type uB} (f : β → α → α)
    (f' : β → α × C → α × C) (h : ∀ x a, (f' x a).1 = f x a.1) (i : α × C) (l : List β) :
    (foldrHat f f' i l).1 = List.foldr f i.1 l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [foldrHat, List.foldr_cons] at ih ⊢
    rw [h, ih]

/-- **Reads after a costed left fold.** A costed step that raises the bound of the companion by
at most `d` (an update: `d = 3`, `updateCompanion_le`) leaves the companion of the fold bounded
by `B + d · |l|` when that of the initial accumulator is bounded by `B`. -/
theorem foldlHat_snd_le {α : Type uA} {X : Type uC} {β : Type uB} (f : α → β → α)
    (f' : α × (X → ℕ) → β → α × (X → ℕ)) {d : ℕ}
    (hs : ∀ a x M, (∀ y, a.2 y ≤ M) → ∀ y, (f' a x).2 y ≤ M + d) (l : List β) :
    ∀ (i : α × (X → ℕ)) (B : ℕ), (∀ y, i.2 y ≤ B) →
      ∀ y, (foldlHat f f' i l).2 y ≤ B + d * l.length := by
  induction l with
  | nil => simp [foldlHat]
  | cons x l ih =>
    intro i B h y
    have := ih (f' i x) (B + d) (hs i x B h) y
    simp only [foldlHat, List.foldl_cons, List.length_cons] at this ⊢
    grind

/-- **Reads after a costed right fold.** A costed step that raises the bound of the companion by
at most `d` leaves the companion of the fold bounded by `B + d · |l|` when that of the initial
accumulator is bounded by `B`. -/
theorem foldrHat_snd_le {α : Type uA} {X : Type uC} {β : Type uB} (f : β → α → α)
    (f' : β → α × (X → ℕ) → α × (X → ℕ)) {d : ℕ}
    (hs : ∀ x a M, (∀ y, a.2 y ≤ M) → ∀ y, (f' x a).2 y ≤ M + d) (l : List β)
    (i : α × (X → ℕ)) (B : ℕ) (h : ∀ y, i.2 y ≤ B) :
    ∀ y, (foldrHat f f' i l).2 y ≤ B + d * l.length := by
  induction l with
  | nil => simpa [foldrHat] using h
  | cons x l ih =>
    intro y
    have := hs x _ _ ih y
    simp only [foldrHat, List.foldr_cons, List.length_cons] at this ⊢
    grind

end CatCrypt.Tactics.DeriveTimed

end
