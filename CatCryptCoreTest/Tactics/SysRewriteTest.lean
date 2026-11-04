/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.SysRewriteAuto

/-!
# Tests of `sys_step_map`, `sys_step_pres`, `sys_step_port`, `sys_congr`, `trace_eq_chain` and
the `catcrypt_auto` shapes of `SysRewriteAuto`

The systems are a latch on one bit: the first event is stored and answered with `false`, every
later event is answered with the stored bit. `latch` keeps the bit in an option, `latch₂` in a
flag and a bit; the state map is `fun t => (t.isSome, t.getD false)`. The proofs by
`sys_step_map` split the state on the `match` of the real step, as the steps need it. The
multi-call hybrid `thrice` calls the flipping bit `flip` three times per activation; its
activations are evaluated one call at a time.
-/

set_option autoImplicit false

namespace CatCrypt.Tactics.SysRewriteTest

open CatCrypt.Core CatCrypt.Crypto.UCTransparent
open scoped CatCrypt.Crypto.UCTransparent.Sys

/-- A latch on one bit with the bit in an option. -/
noncomputable def latch : Sys (Option Bool) Bool Bool where
  init := none
  step t e := match t with
    | none => SPComp.pure (some e, false)
    | some b => SPComp.pure (some b, b)

/-- A latch on one bit with a flag and the bit. -/
noncomputable def latch₂ : Sys (Bool × Bool) Bool Bool where
  init := (false, false)
  step t e := if t.1 then SPComp.pure (t, t.2) else SPComp.pure ((true, e), false)

/-- The state map from `latch` to `latch₂`. -/
def latchMap (t : Option Bool) : Bool × Bool := (t.isSome, t.getD false)

/-! ## `sys_step_map` -/

/-- A step map without invariant: every leaf closes. -/
example : latch ≈ₜ latch₂ := by
  sys_step_map latchMap (fun _ => True) using [latch, latch₂, latchMap]

/-- A realization at distance `0`, by the same step map. -/
example : Realizes latch latch₂ (fun _ _ => 0) := by
  sys_step_map latchMap (fun _ => True) using [latch, latch₂, latchMap]

/-- With an invariant on `latch₂`: the stored bit is `false` while the flag is unset. -/
example : latch₂ ≈ₜ latch := by
  sys_step_map (fun t => if t.1 then some t.2 else none) (fun t => t.1 = false → t.2 = false)
    using [latch, latch₂]

/-! ## `sys_step_pres` -/

/-- The invariant of the last example, preserved by the steps of `latch₂`. -/
example : ∀ (t : Bool × Bool) (e : Bool), (t.1 = false → t.2 = false) →
    ∀ q, IsOutcome (latch₂.step t e) q → (q.1.1 = false → q.1.2 = false) := by
  sys_step_pres using [latch₂]

/-! ## Activations of multi-call hybrids and ports -/

/-- A bit that is flipped at each event and answered. -/
noncomputable def flip : Sys Bool Unit Bool where
  init := false
  step b _ := SPComp.pure (!b, !b)

/-- A hybrid that calls its subroutine three times per activation and answers the last answer. -/
noncomputable def thrice : MultiHybrid Unit Unit Bool Unit Bool where
  init := ()
  fuel := 2
  start _ _ := SPComp.pure ((), .inl ())
  resume _ _ := SPComp.pure ((), .inl ())
  finish _ o := SPComp.pure ((), o)
  start_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _
  resume_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _
  finish_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _

/-- An activation with three calls, evaluated one call at a time. -/
example : flip ≈ₜ thrice.withSub flip := by
  sys_step_map (fun t => ((), t)) (fun _ => True)
    using [flip, thrice, MultiHybrid.withSub]

/-- The step obligation of a step map on the events of one port, in its own declaration. -/
theorem latch_port : Sys.StepPort latch latch₂ (fun _ => True) latchMap id := by
  sys_step_port using [latch, latch₂, latchMap]

/-- A step map whose step obligation is given port by port. -/
example : latch ≈ₜ latch₂ := by
  sys_step_map latchMap (fun _ => True) (ports := [latch_port]) using [latch, latch₂, latchMap]

/-! ## `sys_congr` and `trace_eq_chain` -/

variable {τ υ ρ E O E' O' : Type}

/-- A congruence under the relabelling of ports. -/
example (X : Sys τ E O) (Y : Sys υ E O) (h : X ≈ₜ Y) (fe : E' → E) (fo : O → O') :
    X.mapPorts fe fo ≈ₜ Y.mapPorts fe fo := by
  sys_congr
  exact h

/-- A chain of two hypotheses, one used backwards. -/
example (X : Sys τ E O) (Y : Sys υ E O) (Z : Sys ρ E O) (h₁ : X ≈ₜ Y) (h₂ : Z ≈ₜ Y) :
    X ≈ₜ Z := by
  trace_eq_chain

/-- A chain behind a realization at distance `0`. -/
example (X : Sys τ E O) (Y : Sys υ E O) (h : Y ≈ₜ X) : Realizes X Y (fun _ _ => 0) := by
  trace_eq_chain

/-! ## `catcrypt_auto` -/

/-- The shape `trace equivalence`, arm `trace_eq_chain`. -/
example (X : Sys τ E O) (Y : Sys υ E O) (Z : Sys ρ E O) (h₁ : X ≈ₜ Y) (h₂ : Y ≈ₜ Z) :
    X ≈ₜ Z := by
  catcrypt_auto

/-- The shape `trace equivalence`, arm `sys_congr`. -/
example (X : Sys τ E O) (Y : Sys υ E O) (h : X ≈ₜ Y) (fe : E' → E) (fo : O → O') :
    X.mapPorts fe fo ≈ₜ Y.mapPorts fe fo := by
  catcrypt_auto

/-- The shape `realization at distance zero`, arm `trace_eq_chain`. -/
example (X : Sys τ E O) (Y : Sys υ E O) (h : X ≈ₜ Y) : Realizes X Y (fun _ _ => 0) := by
  catcrypt_auto

end CatCrypt.Tactics.SysRewriteTest
