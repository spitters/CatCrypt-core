/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LoopRewriteAttr
public import CatCryptCore.Crypto.UCLoopbackTraced
public import CatCryptCore.Quantum.QSysCat

/-!
# Loop rewriting with the trace laws

The tactic `loop_rw` rewrites a goal about feedback loops with the simp set `loop_simps`: the
trace laws of a traced symmetric monoidal category and the unfolding equations of the unbounded
feedback loop, each a directed rewrite step. On a morphism `trace U f` of a traced category it

* moves pre- and post-processing outside the loop (tightening, `trace_whiskerRight_comp`,
  `trace_comp_whiskerRight`);
* slides a morphism on the feedback wire from the entry of the loop to its exit (dinaturality,
  `trace_whiskerLeft_comp`);
* removes a loop whose feedback wire is the unit (`trace_tensorUnit`), splits a loop over a
  tensor product of wires (`trace_tensor`), and moves a loop inside a whiskering
  (`whiskerLeft_trace`);
* replaces a loop that only forwards its wire, the trace of the symmetry, by the identity
  (yanking, `trace_braiding`).

The carriers are the category `SysCat` of classical reactive systems and the categories
`QSysCat R` of quantum reactive systems, whose trace is the unbounded loopback `loopbackω`. On
both, a feedback wire that is never entered vanishes (`SysCat.trace_whiskerRight_self`,
`QSysCat.trace_whiskerRight_self`), and the first activation of a loopback unrolls
(`Sys.fbRunω_inl`, `QRSys.fbRunω_inl`). The dynamic-circuit loop `whileBit` adds its own
equations to the simp set in `CatCrypt.Quantum.DynCircuitLoopRw`.

## Main definitions

* `loop_rw`, `loop_rw [h₁, …]`: rewriting with `loop_simps` and the associativity and unit
  laws of composition, with extra rewrite rules.

## Main results

* `CategoryTheory.TracedCategory.trace_comp_comp_whiskerRight`: tightening on the output side
  behind a composite.
* `Sys.fbRunω_inl`, `QRSys.fbRunω_inl`: unrolling of the first activation of a loopback.
* `Sys.loopbackω_par_ofFun_id`, `QRSys.loopbackω_par_ofFun_id`: the loopback of a system beside
  the forwarding of the wire is the system.
* `SysCat.trace_whiskerRight_self`, `QSysCat.trace_whiskerRight_self`: vanishing of an unused
  feedback wire.
* `SysCat.trace_tighten_vanish`, `QSysCat.trace_tighten_yank`, `QSysCat.trace_slide_yank`,
  `Sys.loopbackω_step_of_exit`: goals closed by `loop_rw`.
-/

@[expose] public section

set_option autoImplicit false

/-! ## The trace laws as directed steps -/

namespace CategoryTheory.TracedCategory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [TracedCategory C]

/-- **Tightening on the output side behind a composite.** Post-processing `h ▷ U` at the end of
a composite of two morphisms leaves the loop. -/
theorem trace_comp_comp_whiskerRight (U : C) {X Z Y Y' : C} (f₁ : X ⊗ U ⟶ Z)
    (f₂ : Z ⟶ Y ⊗ U) (h : Y ⟶ Y') :
    trace U (f₁ ≫ f₂ ≫ h ▷ U) = trace U (f₁ ≫ f₂) ≫ h := by
  rw [← Category.assoc, trace_comp_whiskerRight]

attribute [loop_simps] trace_whiskerRight_comp trace_comp_whiskerRight
  trace_comp_comp_whiskerRight trace_whiskerLeft_comp trace_tensorUnit trace_tensor
  whiskerLeft_trace trace_braiding trace_braiding_inv

end CategoryTheory.TracedCategory

/-! ## The tactic -/

namespace CatCrypt.Tactics.LoopRewrite

open Lean Parser Tactic

/-- `loop_rw` rewrites a goal about feedback loops with the simp set `loop_simps` (the trace
laws as directed steps and the unrolling of a loopback) and the associativity and unit laws of
composition, closing the goal when both sides meet. `loop_rw [h₁, …]` adds rewrite rules. -/
syntax (name := loopRw) "loop_rw" (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| loop_rw) =>
    `(tactic| simp only [loop_simps, CategoryTheory.Category.assoc,
      CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id])
  | `(tactic| loop_rw [$args,*]) =>
    `(tactic| simp only [loop_simps, CategoryTheory.Category.assoc,
      CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id, $args,*])

end CatCrypt.Tactics.LoopRewrite

/-! ## Classical reactive systems -/

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete

namespace Sys

variable {τ E O X : Type}

/-- **Unrolling.** The unbounded activation from an outer event is one step of the system,
followed on a wire value by the unbounded activation from that wire value. -/
theorem fbRunω_inl (S : Sys τ (E ⊕ X) (O ⊕ X)) (e : E) (t : τ) :
    S.fbRunω (.inl e) t = SPComp.bind (S.step t (.inl e)) fun q =>
      Sum.elim (fun o => SPComp.pure (q.1, o)) (fun x => S.fbRunω (.inr x) q.1) q.2 :=
  fbRunω_eq S (.inl e) t

/-- **An unused feedback wire vanishes.** The loopback of `S` beside the forwarding of the wire
`X` is `S`: an outer event never reaches the wire. -/
theorem loopbackω_par_ofFun_id (S : Sys τ E O) :
    StepMapOn (S.par (ofFun (id : X → X))).loopbackω S (fun _ => True) Prod.fst := by
  refine StepMapOn.of_step _ rfl fun s e => ?_
  rw [loopbackω_step, fbRunω_eq, par_step_inl]
  simp [SPComp.map, SPComp.bind_assoc]

attribute [loop_simps] loopbackω_step fbRunω_inl

/-- **A test of `loop_rw`.** A loopback whose system exits at once on an outer event returns
that exit: unrolling, then the monad and sum laws. -/
theorem loopbackω_step_of_exit (S : Sys τ (E ⊕ X) (O ⊕ X)) (t t' : τ) (e : E) (o : O)
    (h : S.step t (.inl e) = SPComp.pure (t', .inl o)) :
    S.loopbackω.step t e = SPComp.pure (t', o) := by
  loop_rw [h, SPComp.pure_bind, Sum.elim_inl]

end Sys

namespace SysCat

open CategoryTheory MonoidalCategory

/-- Unfolding lemma of the trace of `SysCat`: the trace of the traced category is
`SysCat.trace`. -/
@[loop_simps]
theorem trace_def (U : SysCat) {X Y : SysCat} (f : X ⊗ U ⟶ Y ⊗ U) :
    SysCat.trace U f = TracedCategory.trace U f :=
  rfl

/-- **Vanishing of an unused feedback wire.** The trace of `f ▷ U` is `f`. -/
@[loop_simps]
theorem trace_whiskerRight_self (U : SysCat) {X Y : SysCat} (f : X ⟶ Y) :
    TracedCategory.trace U (f ▷ U) = f := by
  induction f using Quotient.inductionOn with
  | h A => exact Quotient.sound (Sys.loopbackω_par_ofFun_id (X := U.P) A.sys).stepEq

/-- **A test of `loop_rw`.** Pre-processing leaves the loop, then the unused wire vanishes. -/
theorem trace_tighten_vanish (U : SysCat) {X' X Y : SysCat} (g : X' ⟶ X) (h : X ⟶ Y) :
    TracedCategory.trace U (g ▷ U ≫ h ▷ U) = g ≫ h := by
  loop_rw

end SysCat

end CatCrypt.Crypto.UCTransparent

/-! ## Quantum reactive systems -/

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum

namespace QRSys

variable {R : Type} [Fintype R] {τ E O X : Type}

/-- **Unrolling.** The unbounded activation from an outer event is one step of the system,
followed on a wire value by the unbounded activation from that wire value. -/
theorem fbRunω_inl (S : QRSys R τ (E ⊕ X) (O ⊕ X)) (e : E) (t : τ) :
    S.fbRunω (.inl e) t = (S.step t (.inl e)).bind fun q =>
      Sum.elim (fun o => SubInstrument.pure (q.1, o)) (fun x => S.fbRunω (.inr x) q.1) q.2 :=
  fbRunω_eq S (.inl e) t

/-- **An unused feedback wire vanishes.** The loopback of `S` beside the forwarding of the wire
`X` is `S`: an outer event never reaches the wire. -/
theorem loopbackω_par_ofFun_id (S : QRSys R τ E O) :
    StepMap (S.par (ofFun (id : X → X))).loopbackω S Prod.fst := by
  refine ⟨rfl, fun s e => ?_⟩
  rw [loopbackω_step, fbRunω_eq, par_step_inl]
  simp [SubInstrument.bind_assoc]

attribute [loop_simps] loopbackω_step fbRunω_inl

end QRSys

namespace QSysCat

open CategoryTheory MonoidalCategory

variable {R : Type} [Fintype R]

/-- Unfolding lemma of the trace of `QSysCat R`: the trace of the traced category is
`QSysCat.trace`. -/
@[loop_simps]
theorem trace_def (U : QSysCat R) {X Y : QSysCat R} (f : X ⊗ U ⟶ Y ⊗ U) :
    QSysCat.trace U f = TracedCategory.trace U f :=
  rfl

/-- **Vanishing of an unused feedback wire.** The trace of `f ▷ U` is `f`. -/
@[loop_simps]
theorem trace_whiskerRight_self (U : QSysCat R) {X Y : QSysCat R} (f : X ⟶ Y) :
    TracedCategory.trace U (f ▷ U) = f := by
  induction f using Quotient.inductionOn with
  | h A => exact Quotient.sound (QRSys.loopbackω_par_ofFun_id (X := U.P) A.sys).stepEq

/-- **A test of `loop_rw`.** Pre- and post-processing leave the loop, and the loop of the
symmetry is the identity. -/
theorem trace_tighten_yank (U : QSysCat R) {X' Y : QSysCat R} (g : X' ⟶ U) (h : U ⟶ Y) :
    TracedCategory.trace U (g ▷ U ≫ (β_ U U).hom ≫ h ▷ U) = g ≫ h := by
  loop_rw

/-- **A test of `loop_rw`.** A morphism on the feedback wire slides to the exit, crosses the
symmetry, leaves the loop, and the loop of the symmetry is the identity. -/
theorem trace_slide_yank (U : QSysCat R) (k : U ⟶ U) :
    TracedCategory.trace U (U ◁ k ≫ (β_ U U).hom) = k := by
  loop_rw [← BraidedCategory.braiding_naturality_left]

end QSysCat

end CatCrypt.Quantum.ReactiveUC
