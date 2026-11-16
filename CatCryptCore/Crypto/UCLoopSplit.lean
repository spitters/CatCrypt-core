/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCDeferred

/-!
# Splitting a run at a stopping time, and deferred sampling of a state-dependent challenge

**Two-stage runs.** For a decidable predicate `use t e` on the system state and the event, the
first stage `loopTo S bad Z use n c` runs the joint run of `Z` and `S` from `c` until the first
activation whose system state `t` and event `e` satisfy `use t e` (a stopping time), or until
the budget of `n` activations ends. It returns the split point: the remaining budget, the
configuration (with the environment state after `Z` chose `e`), and the event `e` when the
run stopped at a use. The second stage `loopRest S bad Z` performs the stopped activation and
continues for the remaining budget. The run is the first stage followed by the second
(`loop_split_at`, `run_split_at`).

**Deferred sampling of a state-dependent challenge.** Let `c t` be a computation that neither
touches the heap nor fails, depending on the system state `t`, `Y v` a family of systems and
`Yc` a system whose step at a use is the step of `Y v` averaged over `v` drawn from `c t`, and
whose later steps agree with those of `Y v` (in the states of `post`, which the steps keep).
Then the run of `Yc` is its first stage followed by the draw of `v` from `c t`, with `t` the
system state at the split, and the second stage of `Y v` (`loop_deferred_at`,
`run_deferred_at`). The two-stage form is the game of an adversary that outputs the state at
the first use before the challenge is drawn. At a constant challenge, with the systems
agreeing before the use, the draw moves to the start of the run (`run_deferred_of_split`,
the statement of `run_deferred`).

## Main definitions

* `loopTo`: the first stage, up to the first use.
* `loopRest`: the second stage, from a split point.

## Main results

* `loop_split_at`, `run_split_at`: a run is its first stage followed by its second stage.
* `loopTo_congr`: systems whose steps agree before the use have the same first stage.
* `loop_deferred_at`, `run_deferred_at`: deferred sampling of a state-dependent challenge.
* `run_deferred_of_split`: deferred sampling of a fixed challenge, from the two-stage form.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete

section Split

variable {α τ ζ E O : Type}

/-- The first stage of a run: the joint run of `Z` and `S` from `c` until the first activation
whose system state `t` and event `e` satisfy `use t e`, or until the budget of `n` activations
ends. The result is the remaining budget, the configuration (at a use, with the environment
state after `Z` chose the event), and the event of the use, if any. -/
noncomputable def loopTo (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O)
    (use : τ → E → Prop) [DecidableRel use] :
    ℕ → ζ × τ × Bool → SPComp (ℕ × (ζ × τ × Bool) × Option E)
  | 0, c => SPComp.pure (0, c, none)
  | n + 1, c =>
    SPComp.bind (Z.next c.1) fun a =>
      if use c.2.1 a.2 then SPComp.pure (n, (a.1, c.2.1, c.2.2), some a.2)
      else
        SPComp.bind (S.step c.2.1 a.2) fun p =>
          SPComp.bind (Z.obs a.1 p.2) fun z =>
            loopTo S bad Z use n (z, p.1, c.2.2 || bad p.1)

/-- The second stage of a run from a split point: at a use, the step of `S` at the event of the
use, the observation by `Z`, and the run for the remaining budget; otherwise the
configuration. -/
noncomputable def loopRest (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O) :
    ℕ × (ζ × τ × Bool) × Option E → SPComp (ζ × τ × Bool)
  | (_, c, none) => SPComp.pure c
  | (n, c, some e) =>
    SPComp.bind (S.step c.2.1 e) fun p =>
      SPComp.bind (Z.obs c.1 p.2) fun z =>
        loop S bad Z n (z, p.1, c.2.2 || bad p.1)

/-- **Splitting a run at a stopping time.** The run of `n` activations from `c` is the first
stage up to the first use followed by the second stage. -/
theorem loop_split_at (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O)
    (use : τ → E → Prop) [DecidableRel use] :
    ∀ (n : ℕ) (c : ζ × τ × Bool),
      loop S bad Z n c = SPComp.bind (loopTo S bad Z use n c) (loopRest S bad Z) := by
  intro n
  induction n with
  | zero => intro c; simp only [loop, loopTo, SPComp.pure_bind, loopRest]
  | succ n ih =>
    intro c
    simp only [loop, loopTo, SPComp.bind_assoc]
    congr 1; funext a
    split_ifs
    · simp only [SPComp.pure_bind, loopRest]
    · simp only [SPComp.bind_assoc, ih]

/-- **Splitting the full run at a stopping time.** -/
theorem run_split_at (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O)
    (use : τ → E → Prop) [DecidableRel use] :
    run S bad Z = SPComp.bind (loopTo S bad Z use Z.rounds (Z.init, S.init, bad S.init))
      (loopRest S bad Z) :=
  loop_split_at S bad Z use _ _

/-- At a split point, the system state lies in an invariant of the steps that holds at the
start, and the event of a use satisfies `use` at that state. -/
theorem loopTo_inv (S : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O)
    (use : τ → E → Prop) [DecidableRel use] (Inv : τ → Prop)
    (hinv : ∀ t e q, Inv t → IsOutcome (S.step t e) q → Inv q.1) :
    ∀ (n : ℕ) (c : ζ × τ × Bool) (s : ℕ × (ζ × τ × Bool) × Option E),
      Inv c.2.1 → IsOutcome (loopTo S bad Z use n c) s →
        Inv s.2.1.2.1 ∧ ∀ e, s.2.2 = some e → use s.2.1.2.1 e := by
  intro n
  induction n with
  | zero =>
    intro c s hc hs
    simp only [loopTo] at hs
    obtain rfl := isOutcome_pure hs
    exact ⟨hc, fun e he => by cases he⟩
  | succ n ih =>
    intro c s hc hs
    simp only [loopTo] at hs
    obtain ⟨a, _, ha⟩ := isOutcome_bind hs
    split_ifs at ha with hu
    · obtain rfl := isOutcome_pure ha
      exact ⟨hc, fun e he => by cases he; exact hu⟩
    · obtain ⟨p, hp, hp'⟩ := isOutcome_bind ha
      obtain ⟨z, _, hz⟩ := isOutcome_bind hp'
      exact ih _ s (hinv _ _ p hc hp) hz

/-- Systems whose steps agree before the use, on an invariant of the steps of `S`, have the
same first stage. -/
theorem loopTo_congr (S S' : Sys τ E O) (bad : τ → Bool) (Z : Strat ζ E O)
    (use : τ → E → Prop) [DecidableRel use] (Inv : τ → Prop)
    (hinv : ∀ t e q, Inv t → IsOutcome (S.step t e) q → Inv q.1)
    (heq : ∀ t e, Inv t → ¬ use t e → S'.step t e = S.step t e) :
    ∀ (n : ℕ) (c : ζ × τ × Bool), Inv c.2.1 → loopTo S' bad Z use n c = loopTo S bad Z use n c := by
  intro n
  induction n with
  | zero => intro c _; rfl
  | succ n ih =>
    intro c hc
    simp only [loopTo]
    congr 1; funext a
    split_ifs with hu
    · rfl
    · rw [heq _ _ hc hu]
      refine bind_congr_isOutcome fun p hp => ?_
      congr 1; funext z
      exact ih _ (hinv _ _ p hc hp)

/-- **Deferred sampling of a state-dependent challenge, second stage.** At a split point whose
system state `t` lies in the invariant, the second stage of `Yc` is the second stage of `Y v`
averaged over `v` drawn from `c t`. -/
theorem loopRest_deferred (c : τ → SPComp α) (hc : ∀ t, SPComp.IsPure (c t))
    (hcn : ∀ t, SPComp.NoFail (c t))
    (Y : α → Sys τ E O) (Yc : Sys τ E O) (Inv post : τ → Prop) (use : τ → E → Prop)
    (hinv : ∀ t e q, Inv t → IsOutcome (Yc.step t e) q → Inv q.1)
    (hinvY : ∀ v t e q, Inv t → IsOutcome ((Y v).step t e) q → Inv q.1)
    (hpost : ∀ v t e, Inv t → post t → (Y v).step t e = Yc.step t e)
    (hmono : ∀ t e q, Inv t → post t → IsOutcome (Yc.step t e) q → post q.1)
    (huse : ∀ t e, Inv t → ¬ post t → use t e →
      Yc.step t e = SPComp.bind (c t) fun v => (Y v).step t e)
    (hused : ∀ v t e q, Inv t → ¬ post t → use t e → IsOutcome ((Y v).step t e) q → post q.1)
    (bad : τ → Bool) (Z : Strat ζ E O) (n : ℕ) (k : ζ × τ × Bool) (e : E)
    (hk : Inv k.2.1) (hu : use k.2.1 e) :
    loopRest Yc bad Z (n, k, some e) =
      SPComp.bind (c k.2.1) fun v => loopRest (Y v) bad Z (n, k, some e) := by
  have hP := loop_deferred_post Y Yc Inv post hinv hpost hmono bad Z
  by_cases hp : post k.2.1
  · have h : ∀ v, loopRest (Y v) bad Z (n, k, some e) = loopRest Yc bad Z (n, k, some e) := by
      intro v
      simp only [loopRest]
      rw [hpost v _ e hk hp]
      refine bind_congr_isOutcome fun q hq => ?_
      congr 1; funext z
      exact hP _ _ _ _ v (hinv _ e q hk hq) (hmono _ e q hk hp hq)
    simp only [h]
    exact (bind_const_of_isPure (hc _) (hcn _) _).symm
  · simp only [loopRest]
    rw [huse _ e hk hp hu, SPComp.bind_assoc]
    congr 1; funext v
    refine bind_congr_isOutcome fun q hq => ?_
    congr 1; funext z
    exact (hP _ _ _ _ v (hinvY v _ e q hk hq) (hused v _ e q hk hp hu hq)).symm

/-- **Deferred sampling of a state-dependent challenge.** From a configuration in the
invariant, the run of `Yc` is its first stage up to the first use, followed by the draw of `v`
from `c t`, with `t` the system state at the split, and the second stage of `Y v`. -/
theorem loop_deferred_at (c : τ → SPComp α) (hc : ∀ t, SPComp.IsPure (c t))
    (hcn : ∀ t, SPComp.NoFail (c t))
    (Y : α → Sys τ E O) (Yc : Sys τ E O) (Inv post : τ → Prop) (use : τ → E → Prop)
    [DecidableRel use]
    (hinv : ∀ t e q, Inv t → IsOutcome (Yc.step t e) q → Inv q.1)
    (hinvY : ∀ v t e q, Inv t → IsOutcome ((Y v).step t e) q → Inv q.1)
    (hpost : ∀ v t e, Inv t → post t → (Y v).step t e = Yc.step t e)
    (hmono : ∀ t e q, Inv t → post t → IsOutcome (Yc.step t e) q → post q.1)
    (huse : ∀ t e, Inv t → ¬ post t → use t e →
      Yc.step t e = SPComp.bind (c t) fun v => (Y v).step t e)
    (hused : ∀ v t e q, Inv t → ¬ post t → use t e → IsOutcome ((Y v).step t e) q → post q.1)
    (bad : τ → Bool) (Z : Strat ζ E O) (n : ℕ) (k : ζ × τ × Bool) (hk : Inv k.2.1) :
    loop Yc bad Z n k =
      SPComp.bind (loopTo Yc bad Z use n k) fun s =>
        SPComp.bind (c s.2.1.2.1) fun v => loopRest (Y v) bad Z s := by
  rw [loop_split_at Yc bad Z use n k]
  refine bind_congr_isOutcome fun s hs => ?_
  have hsI := loopTo_inv Yc bad Z use Inv hinv n k s hk hs
  rcases s with ⟨m, k', _ | e⟩
  · simp only [loopRest]
    exact (bind_const_of_isPure (hc _) (hcn _) _).symm
  · exact loopRest_deferred c hc hcn Y Yc Inv post use hinv hinvY hpost hmono huse hused bad Z
      m k' e hsI.1 (hsI.2 e rfl)

/-- **Deferred sampling of a state-dependent challenge for flagged runs.** When the initial
state of `Yc` lies in the invariant, the full run of `Yc` is its first stage up to the first
use, followed by the draw of `v` from `c t`, with `t` the system state at the split, and the
second stage of `Y v`. -/
theorem run_deferred_at (c : τ → SPComp α) (hc : ∀ t, SPComp.IsPure (c t))
    (hcn : ∀ t, SPComp.NoFail (c t))
    (Y : α → Sys τ E O) (Yc : Sys τ E O) (Inv post : τ → Prop) (use : τ → E → Prop)
    [DecidableRel use] (hi0 : Inv Yc.init)
    (hinv : ∀ t e q, Inv t → IsOutcome (Yc.step t e) q → Inv q.1)
    (hinvY : ∀ v t e q, Inv t → IsOutcome ((Y v).step t e) q → Inv q.1)
    (hpost : ∀ v t e, Inv t → post t → (Y v).step t e = Yc.step t e)
    (hmono : ∀ t e q, Inv t → post t → IsOutcome (Yc.step t e) q → post q.1)
    (huse : ∀ t e, Inv t → ¬ post t → use t e →
      Yc.step t e = SPComp.bind (c t) fun v => (Y v).step t e)
    (hused : ∀ v t e q, Inv t → ¬ post t → use t e → IsOutcome ((Y v).step t e) q → post q.1)
    (bad : τ → Bool) (Z : Strat ζ E O) :
    run Yc bad Z =
      SPComp.bind (loopTo Yc bad Z use Z.rounds (Z.init, Yc.init, bad Yc.init)) fun s =>
        SPComp.bind (c s.2.1.2.1) fun v => loopRest (Y v) bad Z s :=
  loop_deferred_at c hc hcn Y Yc Inv post use hinv hinvY hpost hmono huse hused bad Z _ _ hi0

/-- **Deferred sampling of a fixed challenge, from the two-stage form.** Under the hypotheses
of `run_deferred` (without the condition that the initial state is not in `post`), the full
run of `Yc` is the full run of `Y v` averaged over `v` drawn from `c` before the run. -/
theorem run_deferred_of_split (c : SPComp α) (hc : SPComp.IsPure c) (hcn : SPComp.NoFail c)
    (Y : α → Sys τ E O) (Yc : Sys τ E O) (Inv post : τ → Prop) (use : τ → E → Prop)
    (hinit : ∀ v, (Y v).init = Yc.init) (hi0 : Inv Yc.init)
    (hinv : ∀ t e q, Inv t → IsOutcome (Yc.step t e) q → Inv q.1)
    (hinvY : ∀ v t e q, Inv t → IsOutcome ((Y v).step t e) q → Inv q.1)
    (hpost : ∀ v t e, Inv t → post t → (Y v).step t e = Yc.step t e)
    (hmono : ∀ t e q, Inv t → post t → IsOutcome (Yc.step t e) q → post q.1)
    (hfree : ∀ v t e, Inv t → ¬ post t → ¬ use t e → (Y v).step t e = Yc.step t e)
    (huse : ∀ t e, Inv t → ¬ post t → use t e →
      Yc.step t e = SPComp.bind c fun v => (Y v).step t e)
    (hused : ∀ v t e q, Inv t → ¬ post t → use t e → IsOutcome ((Y v).step t e) q → post q.1)
    (bad : τ → Bool) (Z : Strat ζ E O) :
    SPComp.bind c (fun v => run (Y v) bad Z) = run Yc bad Z := by
  classical
  have hfirst : ∀ v, loopTo (Y v) bad Z use Z.rounds (Z.init, Yc.init, bad Yc.init) =
      loopTo Yc bad Z use Z.rounds (Z.init, Yc.init, bad Yc.init) := by
    intro v
    refine loopTo_congr Yc (Y v) bad Z use Inv hinv (fun t e ht hu => ?_) _ _ hi0
    by_cases hp : post t
    · exact hpost v t e ht hp
    · exact hfree v t e ht hp hu
  rw [run_deferred_at (fun _ => c) (fun _ => hc) (fun _ => hcn) Y Yc Inv post use hi0 hinv
    hinvY hpost hmono huse hused bad Z]
  simp only [fun v => run_split_at (Y v) bad Z use, hinit, hfirst]
  exact SPComp.isPure_bind_comm_left c _ _ hc

end Split

end CatCrypt.Crypto.UCTransparent
