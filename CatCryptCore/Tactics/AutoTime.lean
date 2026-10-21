/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.SPTreeTimedOps
public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.Tactics.AutoDispatchCore
public import Mathlib.Tactic.Linarith

/-!
# The time-bound procedure `time_bound`

`time_bound` proves the time bounds of costed trees in the step-prefixed convention of
`derive_timed`:

* `SPTree.Timed.stepTime x ≤ B` and `t.time ≤ B` for costed computation trees;
* `OracleAdv.Timed.StepTimeBound x n` and `A.TimeBound n` for costed oracle adversaries.

The procedure is syntax-directed on the costed tree. A goal is kept in an accumulated form:
`P + stepTime x ≤ B` (or `P + t.time ≤ B`) for computation trees, and `StepTimeBound x (B - P)`
(or `A.TimeBound (B - P)`) for oracle adversaries, where `P` is the cost of the path already
traversed. Each node of the tree is consumed by one rule lemma of this module:

* a pair `(c, t)` and `delay c x` add `c` to `P`; a pair `(c + y.1, y.2)` is read as `y` after
  `c`; a tree `y.2` on a path whose cost `P` has the summand `y.1` is read as `y`, the summand
  removed from `P` (`time_snd_fst`: a costed prefix bind `C + (D + y.1) + y.2.time` nested in
  the arithmetic of a `delay`); `map` is read as `bind`;
* a node `sample`, `get`, `set`, `rand`, `query` adds its unit and its step cost and leaves one
  goal for every branch (`∀ b`), so that a maximum over a finite support becomes a universal
  statement;
* `bind A f` with `A` a node is pushed into the node; with `A` not a node, the time of `A` is
  added to `P` (`stepTime_bind_le`, `timeBound_bind`) and the continuation is bounded for
  every value;
* `if`, `if h :` and `match` are split, and a recursor or `casesOn` on a local variable is
  split by `cases` on the variable;
* a definition is unfolded when its body is visible and it is not recursive.

A subtree that no rule consumes is bounded by a source: a local hypothesis whose conclusion
bounds it (`∀ x, (A x).time ≤ T`, `∀ x, (A x).TimeBound T`), or, below the definition named in
the goal, the theorem `N.timeBound_timed` (or `N.timeBound`) of a definition `N.timed` (or
`N`), or the theorem `Ns.timeBound_f` of a combinator `Ns.f` (`timeBound_simulate`,
`timeBound_mapQuery`). The premises of a source are closed in this order:

* by a local hypothesis whose type unifies with the premise, or, for a cost bound
  `∀ x, c x ≤ ?t` whose bound is still free, by reflexivity when `c x` does not depend on `x`;
* a time premise `∀ x, StepTimeBound (g x) ?t` (or another kind) with a free bound, by a
  source of `g x` whose bound does not depend on `x`;
* a query bound `A.erase.IsQueryBound ?q` of a costed adversary, by
  `OracleAdv.Timed.isQueryBound_of_timeBound` from a time bound of `A`;
* any other premise, by the procedure.

An arithmetic leaf is closed by `omega`, then `linarith`, then `nlinarith`, after its step
costs `x.1` are reduced (when `x` is a `delay` or its head definition unfolds to a pair) or
bounded by a source of `x`, and after the bounded atoms are added: for every subterm `f a` of
the leaf and every local hypothesis `∀ x, f x ≤ b`, the instance `f a ≤ b[a/x]`; for every
subtype value `↑m`, its invariant `m.property`; for every registered cost `f.timedCost a`, the
instance of `f.timedCost_eq` or `f.timedCost_le` (premises by the context). When these fail
and the leaf contains an `if` or a `match`, the leaf is split on its condition or scrutinee and
each case is solved again.

Every reduction to weak head normal form, unfolding and case split runs under its own
heartbeat budget (`stepHeartbeats`); a step that exceeds it is not taken, and the subtree is
treated as one that no rule consumes.

Definitions whose bodies are not visible from the calling module are unfolded by the lemmas
of the simp set `time_bound_simps` (an equation `R.timed … = …`), applied where unfolding
fails.

`time_bound` is registered with `catcrypt_auto` as the arm of the shape `time bound`, read
in the direct stage on goals whose head is `StepTimeBound` or `TimeBound`, or that are `≤`
over `ℕ` mentioning `SPTree.Timed.stepTime` or `SPTree.Timed.time`.

## Main definitions

* `time_bound` — the procedure
* `time_bound_simps` — the simp set of unfolding equations
-/

public section

set_option autoImplicit false

/-- Unfolding equations of costed definitions whose bodies `time_bound` does not see. -/
register_simp_attr time_bound_simps

namespace CatCrypt.Tactics.AutoTime

open CatCrypt.Core CatCrypt.Crypto

/-! ## Rules for costed computation trees -/

section SPTree

variable {α β : Type} {P B : ℕ}

theorem st_start {x : ℕ × SPTree.Timed α} (h : 0 + SPTree.Timed.stepTime x ≤ B) :
    SPTree.Timed.stepTime x ≤ B := by
  simpa using h

theorem time_start {t : SPTree.Timed α} (h : 0 + t.time ≤ B) : t.time ≤ B := by
  simpa using h

theorem st_pair {c : ℕ} {t : SPTree.Timed α} (h : P + c + t.time ≤ B) :
    P + SPTree.Timed.stepTime (c, t) ≤ B := by
  simp only [SPTree.Timed.stepTime]
  omega

/-- A pair `(e, y.2)` whose step cost `e` is `c + y.1`: the pair is `y` after `c`. -/
theorem st_pair_fst {e c : ℕ} {y : ℕ × SPTree.Timed α} (he : e = c + y.1)
    (h : P + c + SPTree.Timed.stepTime y ≤ B) : P + SPTree.Timed.stepTime (e, y.2) ≤ B := by
  subst he
  simp only [SPTree.Timed.stepTime] at h ⊢
  omega

theorem fst_le_of_stepTime {x : ℕ × SPTree.Timed α} {E : ℕ}
    (h : SPTree.Timed.stepTime x ≤ E) : x.1 ≤ E := by
  simp only [SPTree.Timed.stepTime] at h
  omega

theorem st_delay {c : ℕ} {x : ℕ × SPTree.Timed α} (h : P + c + SPTree.Timed.stepTime x ≤ B) :
    P + SPTree.Timed.stepTime (SPTree.Timed.delay c x) ≤ B := by
  rw [SPTree.Timed.stepTime_delay]
  omega

theorem st_map {f : α → β} {fc : α → ℕ} {A : SPTree.Timed α}
    (h : P + SPTree.Timed.stepTime (A.bind fun a => (fc a, .ret (f a))) ≤ B) :
    P + SPTree.Timed.stepTime (A.map f fc) ≤ B :=
  h

theorem st_ite {c : Prop} [Decidable c] {x y : ℕ × SPTree.Timed α}
    (hx : c → P + SPTree.Timed.stepTime x ≤ B) (hy : ¬c → P + SPTree.Timed.stepTime y ≤ B) :
    P + SPTree.Timed.stepTime (if c then x else y) ≤ B := by
  by_cases hc : c
  · simpa only [if_pos hc] using hx hc
  · simpa only [if_neg hc] using hy hc

theorem st_dite {c : Prop} [Decidable c] {x : c → ℕ × SPTree.Timed α}
    {y : ¬c → ℕ × SPTree.Timed α} (hx : ∀ h : c, P + SPTree.Timed.stepTime (x h) ≤ B)
    (hy : ∀ h : ¬c, P + SPTree.Timed.stepTime (y h) ≤ B) :
    P + SPTree.Timed.stepTime (if h : c then x h else y h) ≤ B := by
  by_cases hc : c
  · simpa only [dif_pos hc] using hx hc
  · simpa only [dif_neg hc] using hy hc

theorem st_bind_ret {a : α} {f : α → ℕ × SPTree.Timed β}
    (h : P + SPTree.Timed.stepTime (f a) ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.ret a).bind f) ≤ B := by
  simpa only [SPTree.Timed.bind] using h

theorem st_bind_sample {γ : Type} {fγ : Fintype γ} {nγ : Nonempty γ} {c : γ → ℕ}
    {k : γ → SPTree.Timed α} {f : α → ℕ × SPTree.Timed β}
    (h : ∀ b, P + 1 + c b + SPTree.Timed.stepTime ((k b).bind f) ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.sample γ fγ nγ c k).bind f) ≤ B := by
  let _ := fγ
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_sample, Nat.zero_add]
  have hs : (Finset.univ.sup fun b => c b + (SPTree.Timed.bind (k b) f).1 +
      (SPTree.Timed.bind (k b) f).2.time) ≤ B - P - 1 :=
    Finset.sup_le fun b _ => by
      have := h b
      simp only [SPTree.Timed.stepTime] at this
      omega
  have h0 := h (Classical.choice nγ)
  omega

theorem st_bind_get {l : Location} {c : l.ty → ℕ} {k : l.ty → SPTree.Timed α}
    {f : α → ℕ × SPTree.Timed β} (h0 : P + 1 ≤ B)
    (h : ∀ v, P + 1 + c v + SPTree.Timed.stepTime ((k v).bind f) ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.get l c k).bind f) ≤ B := by
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_get, Nat.zero_add]
  have hs : (Finset.univ.sup fun v => c v + (SPTree.Timed.bind (k v) f).1 +
      (SPTree.Timed.bind (k v) f).2.time) ≤ B - P - 1 :=
    Finset.sup_le fun v _ => by
      have := h v
      simp only [SPTree.Timed.stepTime] at this
      omega
  omega

theorem st_bind_set {l : Location} {v : l.ty} {c : ℕ} {t : SPTree.Timed α}
    {f : α → ℕ × SPTree.Timed β} (h : P + 1 + c + SPTree.Timed.stepTime (t.bind f) ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.set l v c t).bind f) ≤ B := by
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_set] at h ⊢
  omega

theorem st_bind_fail {f : α → ℕ × SPTree.Timed β} (h : P ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.fail : SPTree.Timed α).bind f) ≤ B := by
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_fail]
  omega

/-- A bind after a tree `A` that is not a node: the time of `A` joins the path. -/
theorem st_bind {A : SPTree.Timed α} {f : α → ℕ × SPTree.Timed β} (h0 : P + A.time ≤ B)
    (h : ∀ a, P + A.time + SPTree.Timed.stepTime (f a) ≤ B) :
    P + SPTree.Timed.stepTime (A.bind f) ≤ B := by
  have := SPTree.Timed.stepTime_bind_le A f (B - P - A.time) fun a => by
    have := h a
    omega
  omega

theorem st_of {x : ℕ × SPTree.Timed α} {T : ℕ} (h : SPTree.Timed.stepTime x ≤ T)
    (h0 : P + T ≤ B) : P + SPTree.Timed.stepTime x ≤ B := by
  omega

theorem time_ret {a : α} (h : P ≤ B) : P + (SPTree.Timed.ret a).time ≤ B := by
  simp only [SPTree.Timed.time_ret]
  omega

theorem time_sample {γ : Type} {fγ : Fintype γ} {nγ : Nonempty γ} {c : γ → ℕ}
    {k : γ → SPTree.Timed α} (h : ∀ b, P + 1 + c b + (k b).time ≤ B) :
    P + (SPTree.Timed.sample γ fγ nγ c k).time ≤ B := by
  let _ := fγ
  rw [SPTree.Timed.time_sample]
  have hs : (Finset.univ.sup fun b => c b + (k b).time) ≤ B - P - 1 :=
    Finset.sup_le fun b _ => by
      have := h b
      omega
  have h0 := h (Classical.choice nγ)
  omega

theorem time_get {l : Location} {c : l.ty → ℕ} {k : l.ty → SPTree.Timed α} (h0 : P + 1 ≤ B)
    (h : ∀ v, P + 1 + c v + (k v).time ≤ B) : P + (SPTree.Timed.get l c k).time ≤ B := by
  rw [SPTree.Timed.time_get]
  have hs : (Finset.univ.sup fun v => c v + (k v).time) ≤ B - P - 1 :=
    Finset.sup_le fun v _ => by
      have := h v
      omega
  omega

theorem time_set {l : Location} {v : l.ty} {c : ℕ} {t : SPTree.Timed α}
    (h : P + 1 + c + t.time ≤ B) : P + (SPTree.Timed.set l v c t).time ≤ B := by
  rw [SPTree.Timed.time_set]
  omega

theorem time_fail (h : P ≤ B) : P + (SPTree.Timed.fail : SPTree.Timed α).time ≤ B := by
  rw [SPTree.Timed.time_fail]
  omega

/-- The tree `y.2` on a path whose cost `P` has the summand `y.1`: the two are `stepTime y`. -/
theorem time_snd_fst {Q : ℕ} {y : ℕ × SPTree.Timed α} (he : P = Q + y.1)
    (h : Q + SPTree.Timed.stepTime y ≤ B) : P + y.2.time ≤ B := by
  subst he
  simp only [SPTree.Timed.stepTime] at h
  omega

theorem time_snd {x : ℕ × SPTree.Timed α} (h : P + SPTree.Timed.stepTime x ≤ B) :
    P + x.2.time ≤ B := by
  simp only [SPTree.Timed.stepTime] at h
  omega

theorem time_ite {c : Prop} [Decidable c] {x y : SPTree.Timed α}
    (hx : c → P + x.time ≤ B) (hy : ¬c → P + y.time ≤ B) :
    P + (if c then x else y).time ≤ B := by
  by_cases hc : c
  · simpa only [if_pos hc] using hx hc
  · simpa only [if_neg hc] using hy hc

theorem time_dite {c : Prop} [Decidable c] {x : c → SPTree.Timed α} {y : ¬c → SPTree.Timed α}
    (hx : ∀ h : c, P + (x h).time ≤ B) (hy : ∀ h : ¬c, P + (y h).time ≤ B) :
    P + (if h : c then x h else y h).time ≤ B := by
  by_cases hc : c
  · simpa only [dif_pos hc] using hx hc
  · simpa only [dif_neg hc] using hy hc

theorem time_of {t : SPTree.Timed α} {T : ℕ} (h : t.time ≤ T) (h0 : P + T ≤ B) :
    P + t.time ≤ B := by
  omega

end SPTree

/-! ## Rules for costed oracle adversaries -/

section Oracle

variable {D R α β : Type} {P B : ℕ}

theorem tb_start {A : OracleAdv.Timed D R α} {n : ℕ} (h : A.TimeBound (n - 0)) :
    A.TimeBound n := by
  simpa using h

theorem stb_start {x : ℕ × OracleAdv.Timed D R α} {n : ℕ}
    (h : OracleAdv.Timed.StepTimeBound x (n - 0)) : OracleAdv.Timed.StepTimeBound x n := by
  simpa using h

theorem tb_ret {a : α} {n : ℕ} : (OracleAdv.Timed.ret a : OracleAdv.Timed D R α).TimeBound n :=
  trivial

theorem tb_rand {γ : Type} {p : PMF γ} {c : γ → ℕ} {k : γ → OracleAdv.Timed D R α}
    (h0 : P + 1 ≤ B) (h1 : ∀ b, P + 1 + c b ≤ B)
    (h2 : ∀ b, (k b).TimeBound (B - (P + 1 + c b))) :
    (OracleAdv.Timed.rand p c k).TimeBound (B - P) := by
  refine ⟨by omega, fun b => ⟨by have := h1 b; omega, ?_⟩⟩
  have e : B - P - 1 - c b = B - (P + 1 + c b) := by omega
  rw [e]
  exact h2 b

theorem tb_query {d : D} {c : R → ℕ} {k : R → OracleAdv.Timed D R α}
    (h0 : P + 1 ≤ B) (h1 : ∀ r, P + 1 + c r ≤ B)
    (h2 : ∀ r, (k r).TimeBound (B - (P + 1 + c r))) :
    (OracleAdv.Timed.query d c k).TimeBound (B - P) := by
  refine ⟨by omega, fun r => ⟨by have := h1 r; omega, ?_⟩⟩
  have e : B - P - 1 - c r = B - (P + 1 + c r) := by omega
  rw [e]
  exact h2 r

theorem tb_ite {c : Prop} [Decidable c] {x y : OracleAdv.Timed D R α}
    (hx : c → x.TimeBound (B - P)) (hy : ¬c → y.TimeBound (B - P)) :
    (if c then x else y).TimeBound (B - P) := by
  by_cases hc : c
  · simpa only [if_pos hc] using hx hc
  · simpa only [if_neg hc] using hy hc

theorem tb_dite {c : Prop} [Decidable c] {x : c → OracleAdv.Timed D R α}
    {y : ¬c → OracleAdv.Timed D R α} (hx : ∀ h : c, (x h).TimeBound (B - P))
    (hy : ∀ h : ¬c, (y h).TimeBound (B - P)) :
    (if h : c then x h else y h).TimeBound (B - P) := by
  by_cases hc : c
  · simpa only [dif_pos hc] using hx hc
  · simpa only [dif_neg hc] using hy hc

theorem tb_of {A : OracleAdv.Timed D R α} {T : ℕ} (h : A.TimeBound T) (h0 : P + T ≤ B) :
    A.TimeBound (B - P) :=
  h.mono (by omega)

theorem tb_snd {x : ℕ × OracleAdv.Timed D R α} (h : OracleAdv.Timed.StepTimeBound x (B - P)) :
    x.2.TimeBound (B - P) :=
  h.2.mono (Nat.sub_le _ _)

theorem stb_pair {c : ℕ} {A : OracleAdv.Timed D R α} (h0 : P + c ≤ B)
    (h : A.TimeBound (B - (P + c))) : OracleAdv.Timed.StepTimeBound (c, A) (B - P) := by
  refine ⟨by dsimp only; omega, ?_⟩
  have e : B - P - c = B - (P + c) := by omega
  simpa only [e] using h

/-- A pair `(e, y.2)` whose step cost `e` is `c + y.1`: the pair is `y` after `c`. -/
theorem stb_pair_fst {e c : ℕ} {y : ℕ × OracleAdv.Timed D R α} (he : e = c + y.1)
    (h0 : P + c ≤ B) (h : OracleAdv.Timed.StepTimeBound y (B - (P + c))) :
    OracleAdv.Timed.StepTimeBound (e, y.2) (B - P) := by
  subst he
  obtain ⟨h1, h2⟩ := h
  refine ⟨by dsimp only; omega, ?_⟩
  have e' : B - P - (c + y.1) = B - (P + c) - y.1 := by omega
  dsimp only
  rw [e']
  exact h2

theorem fst_le_of_stb {x : ℕ × OracleAdv.Timed D R α} {E : ℕ}
    (h : OracleAdv.Timed.StepTimeBound x E) : x.1 ≤ E :=
  h.1

theorem stb_delay {c : ℕ} {x : ℕ × OracleAdv.Timed D R α} (h0 : P + c ≤ B)
    (h : OracleAdv.Timed.StepTimeBound x (B - (P + c))) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay c x) (B - P) :=
  (OracleAdv.Timed.stepTimeBound_delay h).mono (by omega)

theorem stb_ite {c : Prop} [Decidable c] {x y : ℕ × OracleAdv.Timed D R α}
    (hx : c → OracleAdv.Timed.StepTimeBound x (B - P))
    (hy : ¬c → OracleAdv.Timed.StepTimeBound y (B - P)) :
    OracleAdv.Timed.StepTimeBound (if c then x else y) (B - P) := by
  by_cases hc : c
  · simpa only [if_pos hc] using hx hc
  · simpa only [if_neg hc] using hy hc

theorem stb_dite {c : Prop} [Decidable c] {x : c → ℕ × OracleAdv.Timed D R α}
    {y : ¬c → ℕ × OracleAdv.Timed D R α}
    (hx : ∀ h : c, OracleAdv.Timed.StepTimeBound (x h) (B - P))
    (hy : ∀ h : ¬c, OracleAdv.Timed.StepTimeBound (y h) (B - P)) :
    OracleAdv.Timed.StepTimeBound (if h : c then x h else y h) (B - P) := by
  by_cases hc : c
  · simpa only [dif_pos hc] using hx hc
  · simpa only [dif_neg hc] using hy hc

theorem stb_bind_ret {a : α} {f : α → ℕ × OracleAdv.Timed D R β}
    (h : OracleAdv.Timed.StepTimeBound (f a) (B - P)) :
    OracleAdv.Timed.StepTimeBound ((OracleAdv.Timed.ret a).bind f) (B - P) := by
  simpa only [OracleAdv.Timed.bind] using h

theorem stb_bind_rand {γ : Type} {p : PMF γ} {c : γ → ℕ} {k : γ → OracleAdv.Timed D R α}
    {f : α → ℕ × OracleAdv.Timed D R β} (h0 : P + 1 ≤ B) (h1 : ∀ b, P + 1 + c b ≤ B)
    (h2 : ∀ b, OracleAdv.Timed.StepTimeBound ((k b).bind f) (B - (P + 1 + c b))) :
    OracleAdv.Timed.StepTimeBound ((OracleAdv.Timed.rand p c k).bind f) (B - P) := by
  simp only [OracleAdv.Timed.bind, OracleAdv.Timed.stepTimeBound_zero]
  refine ⟨by omega, fun b => ⟨?_, ?_⟩⟩ <;> dsimp only
  · have := h1 b
    have := (h2 b).1
    omega
  · have := h1 b
    have := (h2 b).1
    have e : B - P - 1 - (c b + ((k b).bind f).1) = B - (P + 1 + c b) - ((k b).bind f).1 := by
      omega
    rw [e]
    exact (h2 b).2

theorem stb_bind_query {d : D} {c : R → ℕ} {k : R → OracleAdv.Timed D R α}
    {f : α → ℕ × OracleAdv.Timed D R β} (h0 : P + 1 ≤ B) (h1 : ∀ r, P + 1 + c r ≤ B)
    (h2 : ∀ r, OracleAdv.Timed.StepTimeBound ((k r).bind f) (B - (P + 1 + c r))) :
    OracleAdv.Timed.StepTimeBound ((OracleAdv.Timed.query d c k).bind f) (B - P) := by
  simp only [OracleAdv.Timed.bind, OracleAdv.Timed.stepTimeBound_zero]
  refine ⟨by omega, fun r => ⟨?_, ?_⟩⟩ <;> dsimp only
  · have := h1 r
    have := (h2 r).1
    omega
  · have := h1 r
    have := (h2 r).1
    have e : B - P - 1 - (c r + ((k r).bind f).1) = B - (P + 1 + c r) - ((k r).bind f).1 := by
      omega
    rw [e]
    exact (h2 r).2

/-- A bind after an adversary `A` of time `T` that is not a node: `T` joins the path. -/
theorem stb_bind {A : OracleAdv.Timed D R α} {f : α → ℕ × OracleAdv.Timed D R β} {T : ℕ}
    (hA : A.TimeBound T) (h0 : P + T ≤ B)
    (hf : ∀ a, OracleAdv.Timed.StepTimeBound (f a) (B - (P + T))) :
    OracleAdv.Timed.StepTimeBound (A.bind f) (B - P) :=
  (OracleAdv.Timed.timeBound_bind hA hf).mono (by omega)

theorem stb_of {x : ℕ × OracleAdv.Timed D R α} {T : ℕ}
    (h : OracleAdv.Timed.StepTimeBound x T) (h0 : P + T ≤ B) :
    OracleAdv.Timed.StepTimeBound x (B - P) :=
  h.mono (by omega)

end Oracle

/-! ## The procedure -/

meta section

open Lean Meta Elab Tactic

/-- The forms of a time goal, by the subterm that carries the tree. -/
inductive Kind where
  /-- `P + SPTree.Timed.stepTime x ≤ B` -/
  | step
  /-- `P + t.time ≤ B` -/
  | time
  /-- `A.TimeBound (B - P)` -/
  | tb
  /-- `StepTimeBound x (B - P)` -/
  | stb

/-- The rule that closes a goal of kind `k` from a bound of its tree. -/
def Kind.ofRule : Kind → Name
  | .step => ``st_of
  | .time => ``time_of
  | .tb => ``tb_of
  | .stb => ``stb_of

/-- The left side of an inequality `l ≤ r` over `ℕ`. -/
def natLe? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``LE.le 4 && (e.getArg! 0).isConstOf ``Nat then
    some (e.getArg! 2, e.getArg! 3)
  else none

/-- The tree of a bound of kind `k`: `y` in `stepTime y ≤ E`, `y.time ≤ E`, `y.TimeBound E`,
`StepTimeBound y E`. -/
def Kind.treeOf (k : Kind) (e : Expr) : Option Expr :=
  match k with
  | .step => do
    let (l, _) ← natLe? e
    guard (l.isAppOfArity ``SPTree.Timed.stepTime 2)
    return l.appArg!
  | .time => do
    let (l, _) ← natLe? e
    guard (l.isAppOfArity ``SPTree.Timed.time 2)
    return l.appArg!
  | .tb => if e.isAppOfArity ``OracleAdv.Timed.TimeBound 5 then some (e.getArg! 3) else none
  | .stb =>
    if e.isAppOfArity ``OracleAdv.Timed.StepTimeBound 5 then some (e.getArg! 3) else none

/-- Constants read as tree structure, never unfolded. -/
def structural : List Name :=
  [``Prod.mk, ``Prod.fst, ``Prod.snd, ``ite, ``dite, ``SPTree.Timed.bind,
    ``SPTree.Timed.map, ``SPTree.Timed.delay, ``SPTree.Timed.stepTime, ``SPTree.Timed.time,
    ``OracleAdv.Timed.bind, ``OracleAdv.Timed.delay, ``OracleAdv.Timed.TimeBound,
    ``OracleAdv.Timed.StepTimeBound]

/-- Whether the body of the definition `n` is visible and not recursive. -/
def unfoldableDef (n : Name) : MetaM Bool := do
  let env ← getEnv
  if structural.contains n then return false
  if env.contains (n ++ `_sunfold) then return false
  let some (.defnInfo d) := env.find? n | return false
  let rec_ := d.value.find? fun
    | .const m _ => m == ``WellFounded.fix || m.lastComponentAsString == "brecOn"
    | _ => false
  return rec_.isNone

/-- The heartbeat budget, in thousands, of one reduction or case split of the procedure. -/
def stepHeartbeats : Nat := 50000

/-- `x` under its own budget of `stepHeartbeats` heartbeats (at most the enclosing budget);
`none`, with the state restored, when it fails or exceeds the budget. An interrupt is passed
on. -/
def capped {α : Type} (x : MetaM α) : MetaM (Option α) := do
  let s ← saveState
  let cap (c : Core.Context) : Core.Context :=
    let m := if c.maxHeartbeats == 0 then stepHeartbeats * 1000
      else min c.maxHeartbeats (stepHeartbeats * 1000)
    { c with maxHeartbeats := m }
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context cap (some <$> x))
    fun e => do
      if e.isInterrupt then throw e
      s.restore
      return none

/-- `whnfR e` under the budget of `capped`; `e` itself when the budget is exceeded. -/
def whnfC (e : Expr) : MetaM Expr := do
  return (← capped (whnfR e)).getD e

/-- The tree `e` with its head definition unfolded, then reduced by `whnfR`, under the budget
of `capped`. -/
def unfoldTree? (e : Expr) : MetaM (Option Expr) := do
  let some n := e.getAppFn.constName? | return none
  unless ← unfoldableDef n do return none
  let r ← capped do
    let some e' ← withDefault (unfoldDefinition? e) | return none
    return some (← whnfR e'.headBeta)
  return r.join

/-- The local variable that an application of a recursor or `casesOn` analyses, when it is
one. -/
def recMajor? (e : Expr) : MetaM (Option FVarId) := do
  let some n := e.getAppFn.constName? | return none
  let some info := (← getEnv).find? n | return none
  let idx? ← match info with
    | .recInfo r => pure (some r.getMajorIdx)
    | _ =>
      if isCasesOnRecursor (← getEnv) n then
        let ind ← getConstInfoInduct n.getPrefix
        pure (some (ind.numParams + 1 + ind.numIndices))
      else pure none
  let some i := idx? | return none
  let some a := e.getAppArgs[i]? | return none
  return if a.isFVar then some a.fvarId! else none

/-- The target of `g` with the subterm `x` replaced by the definitionally equal `x'`. -/
def replaceIn (g : MVarId) (x x' : Expr) : MetaM MVarId := do
  if x == x' then return g
  let t ← instantiateMVars (← g.getType)
  g.replaceTargetDefEq (t.replace fun e => if e == x then some x' else none)

/-- Apply the rule lemma `n` to `g`: its conclusion is unified with the target at reducible
transparency, each term of `hints` is assigned to the first unassigned argument whose type it
has, and the unassigned premises are returned. `none` when the rule does not apply. -/
def applyRule (g : MVarId) (n : Name) (hints : List Expr := []) :
    MetaM (Option (List MVarId)) := g.withContext do
  let s ← saveState
  let e ← mkConstWithFreshMVarLevels n
  let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType e)
  unless ← withReducible (isDefEq concl (← g.getType)) do
    s.restore
    return none
  for pf in hints do
    let pty ← inferType pf
    let mut done := false
    for m in ms do
      if done then break
      if ← m.mvarId!.isAssigned then continue
      if ← isDefEq (← inferType m) pty then
        m.mvarId!.assign pf
        done := true
    unless done do
      s.restore
      return none
  let mut gs := []
  for m in ms do
    let m := m.mvarId!
    unless ← m.isAssigned do
      unless ← isProp (← m.getType) do
        s.restore
        return none
      gs := gs ++ [m]
  g.assign (mkAppN e ms)
  return some gs

/-- The applications in `e` without loose bound variables. -/
partial def appsOf (e : Expr) (acc : Array Expr) : Array Expr :=
  match e with
  | .app f a =>
    let acc := if e.hasLooseBVars then acc else acc.push e
    appsOf a (appsOf f acc)
  | .mdata _ b => appsOf b acc
  | .lam _ t b _ => appsOf b (appsOf t acc)
  | .forallE _ t b _ => appsOf b (appsOf t acc)
  | .proj _ _ b =>
    let acc := if e.hasLooseBVars then acc else acc.push e
    appsOf b acc
  | _ => acc

/-- The pair `y` of a first projection `y.1`, as an application of `Prod.fst` or as a
primitive projection. -/
def fstOf? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Prod.fst 3 then some e.appArg!
  else match e with
    | .proj ``Prod 0 y => some y
    | _ => none

/-- The pair `y` of a second projection `y.2`, as an application of `Prod.snd` or as a
primitive projection. -/
def sndOf? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Prod.snd 3 then some e.appArg!
  else match e with
    | .proj ``Prod 1 y => some y
    | _ => none

/-- The first projection `o` with its pair replaced by `y`. -/
def withFstArg (o y : Expr) : Expr :=
  match o with
  | .proj n i _ => .proj n i y
  | _ => mkApp3 o.getAppFn (o.getArg! 0) (o.getArg! 1) y

/-- Bounded atoms: for every subterm `f a` of the target and every local hypothesis
`∀ x, f x ≤ b` without propositional premises, the instance `f a ≤ b[a/x]` is added to the
context. -/
def addBoundedAtoms (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let subs := appsOf tgt #[]
  let mut g := g
  let mut added : Array Expr := #[]
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    unless ty.isForall do continue
    let s0 ← saveState
    let (ms0, _, body0) ← forallMetaTelescopeReducing ty
    let some (pat, _) := natLe? body0 | s0.restore; continue
    let hd := pat.getAppFn
    let nargs := pat.getAppNumArgs
    let hasProp ← ms0.anyM fun m => do isProp (← inferType m)
    s0.restore
    if hasProp || !(hd.isConst || hd.isFVar) then continue
    for s in subs do
      unless s.getAppNumArgs == nargs && s.getAppFn == hd do continue
      let s1 ← saveState
      let (ms, _, body) ← forallMetaTelescopeReducing ty
      let some (l, _) := natLe? body | s1.restore; continue
      if ← isDefEq l s then
        let pf ← instantiateMVars (mkAppN ld.toExpr ms)
        if pf.hasExprMVar then
          s1.restore
          continue
        let pty ← instantiateMVars (← inferType pf)
        s1.restore
        if added.contains pty then continue
        added := added.push pty
        let (_, g') ← (← g.assert `hb pty pf).intro1P
        g := g'
      else
        s1.restore
  return g

/-- The invariant `m.property` of every subterm `↑m` of the target, added to the context. -/
def addSubtypeFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let mut g := g
  let mut seen : Array Expr := #[]
  for s in appsOf tgt #[] do
    unless s.isAppOfArity ``Subtype.val 3 do continue
    let m := s.appArg!
    if seen.contains m then continue
    seen := seen.push m
    let pf ← mkAppM ``Subtype.property #[m]
    let pty ← instantiateMVars (← inferType pf)
    let (_, g') ← (← g.assert `hs pty.headBeta pf).intro1P
    g := g'
  return g

/-- Close an arithmetic leaf by `omega`, then `linarith`, then `nlinarith`, after adding the
bounded atoms and the invariants of subtype values. -/
def closeArithCore (g : MVarId) : TacticM Unit := do
  let g ← addBoundedAtoms g
  let g ← addSubtypeFacts g
  for tac in #[← `(tactic| omega), ← `(tactic| linarith), ← `(tactic| nlinarith)] do
    let s ← saveState
    try
      setGoals [g]
      evalTactic tac
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()
    s.restore
  throwError "time_bound: arithmetic leaf not closed{indentExpr (← g.getType)}"

/-- The theorems `N.timeBound_timed`, `N.timeBound` of the definition `N.timed` at the head
of `x`, `M.timeBound` of a head `M`, and `Ns.timeBound_f` of a combinator `Ns.f`
(`OracleAdv.Timed.timeBound_simulate` of `OracleAdv.Timed.simulate`). -/
def envSources (x : Expr) : MetaM (Array Expr) := do
  let some n := x.getAppFn.constName? | return #[]
  let last := n.lastComponentAsString
  let cands :=
    (if last == "timed" then
      [n.getPrefix ++ `timeBound_timed, n.getPrefix ++ `timeBound] else []) ++
      [n ++ `timeBound, Name.str n.getPrefix ("timeBound_" ++ last)]
  let env ← getEnv
  cands.filter env.contains |>.toArray.mapM mkConstWithFreshMVarLevels

/-- Close the proposition `mid` from the context: a local hypothesis whose type unifies with
it, or, for `∀ x, l ≤ ?r` with `?r` unassigned and independent of `x`, reflexivity. -/
def closeByContext (mid : MVarId) : MetaM Bool := mid.withContext do
  let ty ← instantiateMVars (← mid.getType)
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    let s ← saveState
    if ← isDefEq ty ld.type then
      mid.assign ld.toExpr
      return true
    s.restore
  let s ← saveState
  let ok ← forallTelescopeReducing ty fun xs body => do
    let some (l, r) := natLe? body | return false
    unless (← instantiateMVars r).getAppFn.isMVar do return false
    unless ← isDefEq r l do return false
    mid.assign (← mkLambdaFVars xs (← mkAppM ``Nat.le_refl #[l]))
    return true
  unless ok do s.restore
  return ok

/-- The lemmas `f.timedCost_eq`, `f.timedCost_le` of the registered cost `f.timedCost`. -/
def costLemmas (n : Name) : MetaM (Array Expr) := do
  match n with
  | .str p s =>
    let env ← getEnv
    [Name.str p (s ++ "_eq"), Name.str p (s ++ "_le")].filter env.contains
      |>.toArray.mapM mkConstWithFreshMVarLevels
  | _ => return #[]

/-- Registered costs: for every subterm `f.timedCost a` of the target, the instance at `a` of
`f.timedCost_eq` (an equation) or `f.timedCost_le` (a bound), with its premises closed by
`closeByContext`, is added to the context. -/
def addCostFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let mut g := g
  let mut added : Array Expr := #[]
  for s in appsOf tgt #[] do
    let some n := s.getAppFn.constName? | continue
    unless n.lastComponentAsString == "timedCost" do continue
    for c in ← costLemmas n do
      let st ← saveState
      let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
      let lhs? := if body.isAppOfArity ``Eq 3 then some (body.getArg! 1)
        else (natLe? body).map (·.1)
      let some l := lhs? | st.restore; continue
      unless ← isDefEq l s do
        st.restore
        continue
      let mut ok := true
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        unless ← isProp (← mid.getType) do continue
        unless ← closeByContext mid do
          ok := false
          break
      let pf ← instantiateMVars (mkAppN c ms)
      if !ok || pf.hasExprMVar then
        st.restore
        continue
      let pty ← instantiateMVars (← inferType pf)
      if added.contains pty then continue
      added := added.push pty
      let (_, g') ← (← g.assert `hc pty pf).intro1P
      g := g'
  return g

/-- The step cost `x.1` of a pair `x` whose head definition unfolds to a pair, replaced by the
first component of that pair, in the target. -/
def reduceStepCosts (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let tgt' ← Meta.transform tgt (post := fun e => do
    let some y := fstOf? e | return .continue
    let mut x ← whnfC y
    for _ in [0:8] do
      if x.isAppOfArity ``Prod.mk 4 then break
      if x.isAppOf ``SPTree.Timed.delay || x.isAppOf ``OracleAdv.Timed.delay then
        match ← withDefault (unfoldDefinition? x) with
        | some x' => x ← whnfC x'.headBeta
        | none => break
      else
        match ← unfoldTree? x with
        | some x' => x := x'
        | none => break
    if x.isAppOfArity ``Prod.mk 4 then return .visit (x.getArg! 2)
    return .continue)
  if tgt' == tgt then return g
  g.replaceTargetDefEq tgt'

mutual

/-- An arithmetic leaf: the step costs of pairs are reduced, each remaining step cost `x.1` of a
costed tree is bounded by a source of `x`, and `closeArithCore` closes the goal. -/
partial def closeArith (g : MVarId) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let g ← reduceStepCosts g
  let mut g := g
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  let mut seen : Array Expr := #[]
  for s in appsOf tgt #[] do
    let some x := fstOf? s | continue
    if seen.contains x then continue
    seen := seen.push x
    let xty ← g.withContext do whnfR (← inferType x)
    let snd := if xty.isAppOfArity ``Prod 2 then xty.getArg! 1 else xty
    let kind? : Option (Kind × Name) :=
      if snd.isAppOf ``SPTree.Timed then some (.step, ``fst_le_of_stepTime)
      else if snd.isAppOf ``OracleAdv.Timed then some (.stb, ``fst_le_of_stb)
      else none
    let some (k, lem) := kind? | continue
    let g0 := g
    let r ← g0.withContext do
      match ← findSource k x env fuel with
      | some pf =>
        let fact ← mkAppM lem #[pf]
        let (_, g') ← (← g0.assert `hx (← inferType fact) fact).intro1P
        pure (some g')
      | none => pure none
    if let some g' := r then g := g'
  let gc ← addCostFacts g
  let s ← saveState
  try
    closeArithCore gc
  catch e =>
    s.restore
    -- an `if` or `match` in the leaf: split on its condition or scrutinee
    let some (some gs) ← capped (splitTarget? gc) | throw e
    for g' in gs do solve g' env (fuel - 1)

/-- A premise of a source with metavariables in its type: by the context
(`closeByContext`); a time premise `∀ x, StepTimeBound (g x) ?t` (or another kind) by a
source of `g x` whose bound does not depend on `x`; a query bound `A.erase.IsQueryBound ?q`
of a costed adversary by `isQueryBound_of_timeBound` from a time bound of `A`. -/
partial def solvePremise (mid : MVarId) (env : Bool) (fuel : Nat) : TacticM Bool :=
    mid.withContext do
  if ← closeByContext mid then return true
  let ty ← instantiateMVars (← mid.getType)
  let s ← saveState
  let r ← forallTelescopeReducing ty fun xs body => do
    for k in [Kind.stb, .tb, .step, .time] do
      if let some x := k.treeOf body then
        if let some pf ← findSource k x env fuel then
          if ← isDefEq (← inferType pf) body then
            mid.assign (← mkLambdaFVars xs pf)
            return true
    if body.isAppOfArity ``OracleAdv.IsQueryBound 5 then
      let a := body.getArg! 3
      if a.isAppOfArity ``OracleAdv.Timed.erase 4 then
        if let some pf ← findSource .tb a.appArg! env fuel then
          let q ← mkAppM ``OracleAdv.Timed.isQueryBound_of_timeBound #[pf]
          if ← isDefEq (← inferType q) body then
            mid.assign (← mkLambdaFVars xs q)
            return true
    return false
  unless r do s.restore
  return r

/-- A proof that the tree `x` of kind `k` is bounded, from a local hypothesis or (when `env`)
a theorem of `envSources`, with its premises closed by the context or by `solve`. -/
partial def findSource (k : Kind) (x : Expr) (env : Bool) (fuel : Nat) :
    TacticM (Option Expr) := do
  let locals ← (← getLCtx).getFVars.filterM fun f => do
    return !(← f.fvarId!.getDecl).isImplementationDetail
  let envs ← if env then envSources x else pure #[]
  let cands := locals ++ envs
  for c in cands do
    let s ← saveState
    try
      let cty ← instantiateMVars (← inferType c)
      let (ms, bis, body) ← forallMetaTelescopeReducing cty
      let some y := k.treeOf body | throwError "no"
      unless ← withReducible (isDefEq y x) do throwError "no"
      -- premises: the context first, then instances, then `solvePremise`, then the procedure
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        if ← isProp (← mid.getType) then
          discard <| closeByContext mid
      for m in ms, bi in bis do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        if bi.isInstImplicit then
          mid.assign (← synthInstance (← mid.getType))
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        unless ← isProp (← mid.getType) do continue
        if ← solvePremise mid env (fuel - 1) then continue
        if (← instantiateMVars (← mid.getType)).hasExprMVar then continue
        solve mid env (fuel - 1)
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        unless ← isProp (← mid.getType) do throwError "no"
        if ← solvePremise mid env (fuel - 1) then continue
        if (← instantiateMVars (← mid.getType)).hasExprMVar then throwError "no"
        solve mid env (fuel - 1)
      let pf ← instantiateMVars (mkAppN c ms)
      if pf.hasExprMVar then throwError "no"
      return some pf
    catch _ =>
      s.restore
  return none

/-- A subtree that no structural rule consumes: a source, else the unfolding of its head
definition, else the simp set `time_bound_simps`, else (computation trees) an arithmetic
leaf. -/
partial def leaf (g : MVarId) (k : Kind) (x : Expr) (env : Bool) (fuel : Nat) :
    TacticM Unit := g.withContext do
  if let some pf ← findSource k x env fuel then
    if ← applyAndSolve g k.ofRule [pf] env fuel then return
  if let some x' ← unfoldTree? x then
    solve (← replaceIn g x x') true (fuel - 1)
    return
  let s ← saveState
  try
    setGoals [g]
    evalTactic (← `(tactic| simp only [time_bound_simps]))
    let gs ← getGoals
    for g' in gs do solve g' true (fuel - 1)
    return
  catch _ => s.restore
  match k with
  | .step | .time => closeArith g env fuel
  | _ => throwError "time_bound: no bound for the subtree{indentExpr x}"

/-- Apply the rule `n` and solve its premises. -/
partial def applyAndSolve (g : MVarId) (n : Name) (hints : List Expr) (env : Bool)
    (fuel : Nat) : TacticM Bool := do
  let some gs ← applyRule g n hints | return false
  for g' in gs do solve g' env (fuel - 1)
  return true

/-- Apply the rule `n`, failing when it does not apply. -/
partial def rule (g : MVarId) (n : Name) (env : Bool) (fuel : Nat) (hints : List Expr := []) :
    TacticM Unit := do
  unless ← applyAndSolve g n hints env fuel do
    throwError "time_bound: rule {n} does not apply to{indentExpr (← g.getType)}"

/-- Split a `match` at the head of the tree, or case on the local variable that a recursor or
`casesOn` at the head analyses, when there is one. -/
partial def splitMatch (g : MVarId) (x : Expr) (env : Bool) (fuel : Nat) : TacticM Bool := do
  if (← matchMatcherApp? x).isSome then
    let some (some gs) ← capped (splitTarget? g) | return false
    for g' in gs do solve g' env (fuel - 1)
    return true
  let some fv ← recMajor? x | return false
  let s ← saveState
  try
    let some subgoals ← capped (g.cases fv) | return false
    for sg in subgoals do solve sg.mvarId env (fuel - 1)
    return true
  catch _ =>
    s.restore
    return false

/-- A pair `(e, y.2)`: by `fstRule` when the step cost `e` has the summand `y.1` (with
`e = c + y.1` closed by `omega`), else by `plainRule`. -/
partial def pairRule (g : MVarId) (x : Expr) (plainRule fstRule : Name) (env : Bool)
    (fuel : Nat) : TacticM Unit := do
  let e := x.getArg! 2
  let snd0 := x.getArg! 3
  let snd ← if (sndOf? snd0).isSome then pure snd0 else whnfC snd0
  if let some y := sndOf? snd then
    let fsts := (appsOf e #[]).filter fun t => (fstOf? t).isSome
    for o in fsts do
      let s ← saveState
      if ← withReducible (isDefEq (fstOf? o).get! y) then
        let y1 := withFstArg o y
        let e' := e.replace fun t => if t == o then some y1 else none
        let c := e.replace fun t => if t == o then some (mkNatLit 0) else none
        let x' := mkApp4 x.getAppFn (x.getArg! 0) (x.getArg! 1) e' snd
        let g' ← replaceIn g x x'
        try
          if ← applyAndSolve g' fstRule [c] env fuel then return
        catch _ => pure ()
      s.restore
  rule g plainRule env fuel

/-- `P + stepTime x ≤ B`. -/
partial def stepCase (g : MVarId) (x : Expr) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let x' ← whnfC x
  let g ← replaceIn g x x'
  g.withContext do
  if x'.isAppOfArity ``Prod.mk 4 then pairRule g x' ``st_pair ``st_pair_fst env fuel
  else if x'.isAppOf ``SPTree.Timed.delay then rule g ``st_delay env fuel
  else if x'.isAppOf ``SPTree.Timed.map then rule g ``st_map env fuel
  else if x'.isAppOfArity ``ite 5 then rule g ``st_ite env fuel
  else if x'.isAppOfArity ``dite 5 then rule g ``st_dite env fuel
  else if x'.isAppOfArity ``SPTree.Timed.bind 4 then
    let a := x'.getArg! 2
    let a' ← whnfC a
    let a' := (← unfoldTree? a').getD a'
    let node : Option Name :=
      if a'.isAppOf ``SPTree.Timed.ret then some ``st_bind_ret
      else if a'.isAppOf ``SPTree.Timed.sample then some ``st_bind_sample
      else if a'.isAppOf ``SPTree.Timed.get then some ``st_bind_get
      else if a'.isAppOf ``SPTree.Timed.set then some ``st_bind_set
      else if a'.isAppOf ``SPTree.Timed.fail then some ``st_bind_fail
      else none
    match node with
    | some n => rule (← replaceIn g a a') n env fuel
    | none => rule g ``st_bind env fuel
  else if ← splitMatch g x' env fuel then return
  else leaf g .step x' env fuel

/-- `P + y.2.time ≤ B` with the summand `y.1` in `P` (up to reducible defeq): the two are
read as `stepTime y` (`time_snd_fst`). -/
partial def sndWithFst (g : MVarId) (y : Expr) (env : Bool) (fuel : Nat) :
    TacticM Bool := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some (l, _) := natLe? tgt | return false
  unless l.isAppOfArity ``HAdd.hAdd 6 do return false
  let p := l.getArg! 4
  let fsts := (appsOf p #[]).filter fun t => (fstOf? t).isSome
  for o in fsts do
    let s ← saveState
    if ← withReducible (isDefEq (fstOf? o).get! y) then
      let y1 := withFstArg o y
      let p' := p.replace fun t => if t == o then some y1 else none
      let q := p.replace fun t => if t == o then some (mkNatLit 0) else none
      let g' ← replaceIn g p p'
      try
        if ← applyAndSolve g' ``time_snd_fst [q] env fuel then return true
      catch _ => pure ()
    s.restore
  return false

/-- `P + t.time ≤ B`. -/
partial def treeCase (g : MVarId) (t : Expr) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let t1 ← whnfC t
  -- a stuck second projection keeps its form `Prod.snd y`
  let t' := if (sndOf? t1).isSome && (sndOf? t).isSome then t else t1
  let g ← replaceIn g t t'
  g.withContext do
  if t'.isAppOf ``SPTree.Timed.ret then rule g ``time_ret env fuel
  else if t'.isAppOf ``SPTree.Timed.sample then rule g ``time_sample env fuel
  else if t'.isAppOf ``SPTree.Timed.get then rule g ``time_get env fuel
  else if t'.isAppOf ``SPTree.Timed.set then rule g ``time_set env fuel
  else if t'.isAppOf ``SPTree.Timed.fail then rule g ``time_fail env fuel
  else if t'.isAppOfArity ``ite 5 then rule g ``time_ite env fuel
  else if t'.isAppOfArity ``dite 5 then rule g ``time_dite env fuel
  else if let some y := sndOf? t' then
    if ← sndWithFst g y env fuel then return
    rule g ``time_snd env fuel
  else if ← splitMatch g t' env fuel then return
  else leaf g .time t' env fuel

/-- `A.TimeBound (B - P)`. -/
partial def tbCase (g : MVarId) (a : Expr) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let a' ← whnfC a
  let g ← replaceIn g a a'
  g.withContext do
  if a'.isAppOf ``OracleAdv.Timed.ret then rule g ``tb_ret env fuel
  else if a'.isAppOf ``OracleAdv.Timed.rand then rule g ``tb_rand env fuel
  else if a'.isAppOf ``OracleAdv.Timed.query then rule g ``tb_query env fuel
  else if a'.isAppOfArity ``ite 5 then rule g ``tb_ite env fuel
  else if a'.isAppOfArity ``dite 5 then rule g ``tb_dite env fuel
  else if (sndOf? a').isSome then rule g ``tb_snd env fuel
  else if ← splitMatch g a' env fuel then return
  else leaf g .tb a' env fuel

/-- `StepTimeBound x (B - P)`. -/
partial def stbCase (g : MVarId) (x : Expr) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let x' ← whnfC x
  let g ← replaceIn g x x'
  g.withContext do
  if x'.isAppOfArity ``Prod.mk 4 then pairRule g x' ``stb_pair ``stb_pair_fst env fuel
  else if x'.isAppOf ``OracleAdv.Timed.delay then rule g ``stb_delay env fuel
  else if x'.isAppOfArity ``ite 5 then rule g ``stb_ite env fuel
  else if x'.isAppOfArity ``dite 5 then rule g ``stb_dite env fuel
  else if x'.isAppOfArity ``OracleAdv.Timed.bind 6 then
    let a := x'.getArg! 4
    let a' ← whnfC a
    let a' := (← unfoldTree? a').getD a'
    let node : Option Name :=
      if a'.isAppOf ``OracleAdv.Timed.ret then some ``stb_bind_ret
      else if a'.isAppOf ``OracleAdv.Timed.rand then some ``stb_bind_rand
      else if a'.isAppOf ``OracleAdv.Timed.query then some ``stb_bind_query
      else none
    match node with
    | some n => rule (← replaceIn g a a') n env fuel
    | none =>
      let some pf ← findSource .tb a env fuel |
        throwError "time_bound: no time bound for the adversary{indentExpr a}"
      rule g ``stb_bind env fuel [pf]
  else if ← splitMatch g x' env fuel then return
  else leaf g .stb x' env fuel

/-- One goal of the procedure. -/
partial def solve (g : MVarId) (env : Bool) (fuel : Nat) : TacticM Unit := g.withContext do
  if fuel == 0 then throwError "time_bound: depth bound reached"
  let tgt ← instantiateMVars (← g.getType)
  if tgt.isForall then
    let (_, g') ← g.intro1P
    solve g' env (fuel - 1)
  else if tgt.isAppOfArity ``And 2 then rule g ``And.intro env fuel
  else if tgt.isConstOf ``True then g.assign (mkConst ``True.intro)
  else if let some (l, _) := natLe? tgt then
    if l.isAppOfArity ``SPTree.Timed.stepTime 2 then rule g ``st_start env fuel
    else if l.isAppOfArity ``SPTree.Timed.time 2 then rule g ``time_start env fuel
    else if l.isAppOfArity ``HAdd.hAdd 6 then
      let y := l.appArg!
      if y.isAppOfArity ``SPTree.Timed.stepTime 2 then stepCase g y.appArg! env fuel
      else if y.isAppOfArity ``SPTree.Timed.time 2 then treeCase g y.appArg! env fuel
      else closeArith g env fuel
    else closeArith g env fuel
  else if tgt.isAppOfArity ``OracleAdv.Timed.TimeBound 5 then
    if (tgt.getArg! 4).isAppOfArity ``HSub.hSub 6 then tbCase g (tgt.getArg! 3) env fuel
    else rule g ``tb_start env fuel
  else if tgt.isAppOfArity ``OracleAdv.Timed.StepTimeBound 5 then
    if (tgt.getArg! 4).isAppOfArity ``HSub.hSub 6 then stbCase g (tgt.getArg! 3) env fuel
    else rule g ``stb_start env fuel
  else
    let s ← saveState
    try
      g.assumption
    catch _ =>
      s.restore
      closeArith g env fuel

end

/-- The depth bound of `time_bound`. -/
def maxDepth : Nat := 512

/-- `time_bound` proves `SPTree.Timed.stepTime x ≤ B`, `t.time ≤ B`,
`OracleAdv.Timed.StepTimeBound x n` and `A.TimeBound n` by consuming the costed tree node by
node, bounding the subtrees it cannot consume by local hypotheses or by the time theorems of
the definitions below the one named in the goal, and closing the arithmetic leaves by `omega`
or `linarith` with the bounded atoms of the context (see the module docstring). -/
syntax (name := timeBoundStx) "time_bound" : tactic

@[tactic timeBoundStx] def evalTimeBound : Tactic := fun _ => do
  let g ← getMainGoal
  let rest := (← getGoals).tail
  solve g false maxDepth
  setGoals rest

end

end CatCrypt.Tactics.AutoTime

/-! ## Registration with `catcrypt_auto` -/

catcrypt_auto_shape "time bound" direct priority 120 :=
  any [app CatCrypt.Crypto.OracleAdv.Timed.TimeBound,
    app CatCrypt.Crypto.OracleAdv.Timed.StepTimeBound,
    all [app LE.le, mentions [CatCrypt.Core.SPTree.Timed.stepTime, CatCrypt.Core.SPTree.Timed.time]]]

catcrypt_auto_arm "time bound" order 10 := "time_bound"

end
