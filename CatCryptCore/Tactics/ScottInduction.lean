/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public import CatCryptCore.ForMathlib.Order.ScottInduction
public import CatCryptCore.Quantum.QSysCat

/-!
# The `scott_induction` tactic

Scott induction (fixed-point induction) proves a property `P` of a least fixed point from `P`
at the bottom element, the preservation of `P` by the map, and admissibility of `P` (an
admissible predicate is closed under ω-suprema of chains, `OmegaCompletePartialOrder.Admissible`).

The tactic `scott_induction` finds in the goal a term of one of the shapes

* `f.lfp` for `f : γ →o γ` on a complete lattice (`OrderHom.lfp_scott_induction`),
* `ωSup (fixedPoints.iterateChain f x h)` (`OmegaCompletePartialOrder.ωSup_iterateChain_induction`),
* `S.fbRunω`, the unbounded activation of the loopback of a quantum reactive system as a
  function of the event and the state (`QRSys.fbRunω_scott_induction`),

abstracts it from the goal into the predicate `P`, and leaves the goals of the corresponding
induction theorem: the side conditions of the term (continuity), admissibility of `P`, `P` at
the start of the iteration, and the preservation step. Admissibility is discharged by
`scott_admissible` when `P` is built from conjunctions, universal quantifications, upper bounds
by a constant, inequalities and equations between maps that `fun_prop` proves ω-Scott-continuous.

`scott_induction e` abstracts the term `e`; `scott_induction using thm` applies the induction
theorem `thm`, whose conclusion is a predicate variable applied to a term.

## Main definitions

* `QRSys.fbStep`: one unfolding of the loopback of a quantum reactive system, the map whose
  least fixed point is `QRSys.fbRunω`.
* `scott_induction`, `scott_admissible`: the tactics.

## Main results

* `QRSys.fbRunω_eq_ωSup`: `fbRunω` is the supremum of the chain of the fuel-bounded runs.
* `QRSys.fbRunω_scott_induction`: Scott induction for the unbounded activation.
* `QRSys.fbRunω_mono`: the unbounded activation is monotone in the steps of the system.
* `QRSys.fbRunω_le_of_fbStep_le`: the unbounded activation is below every prefixed point of
  `fbStep` (Park induction).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.ReactiveUC.QRSys

open _root_.Quantum OmegaCompletePartialOrder

variable {R : Type} [Fintype R] {τ E O X : Type}

/-- One unfolding of the loopback of `S`: one step of `S`, followed on an output `inl o` by the
end of the activation and on an output `inr x` by the activation `h` from the event `inr x`. -/
noncomputable def fbStep (S : QRSys R τ (E ⊕ X) (O ⊕ X))
    (h : E ⊕ X → τ → SubInstrument R R (τ × O)) : E ⊕ X → τ → SubInstrument R R (τ × O) :=
  fun g t => (S.step t g).bind fun q =>
    Sum.elim (fun o => SubInstrument.pure (q.1, o)) (fun x => h (.inr x) q.1) q.2

/-- `fbStep` is monotone in the activation it continues with. -/
theorem fbStep_mono (S : QRSys R τ (E ⊕ X) (O ⊕ X)) : Monotone S.fbStep := by
  intro h h' hh g t
  refine SubInstrument.bind_mono_right _ fun q => ?_
  rcases q with ⟨t', o | x⟩
  · exact le_rfl
  · exact hh _ _

/-- The chain of the fuel-bounded activations of the loopback of `S`, as functions of the event
and the state. -/
noncomputable def fbFunChain (S : QRSys R τ (E ⊕ X) (O ⊕ X)) :
    Chain (E ⊕ X → τ → SubInstrument R R (τ × O)) :=
  ⟨fun n g t => S.fbRunFail n g t, fun _ _ hmn g t => S.fbRunFail_mono g t hmn⟩

/-- Unfolding lemma of `fbRunω`: the unbounded activation is the supremum of the chain of the
fuel-bounded activations. -/
theorem fbRunω_eq_ωSup (S : QRSys R τ (E ⊕ X) (O ⊕ X)) : S.fbRunω = ωSup S.fbFunChain :=
  rfl

/-- The first fuel-bounded activation is `fbStep` of the failing activation. -/
theorem fbFunChain_zero (S : QRSys R τ (E ⊕ X) (O ⊕ X)) :
    S.fbFunChain 0 = S.fbStep fun _ _ => SubInstrument.fail := by
  funext g t
  rfl

/-- Each further fuel-bounded activation is `fbStep` of the previous one. -/
theorem fbFunChain_succ (S : QRSys R τ (E ⊕ X) (O ⊕ X)) (n : ℕ) :
    S.fbFunChain (n + 1) = S.fbStep (S.fbFunChain n) := by
  funext g t
  rfl

/-- **Scott induction for the unbounded activation.** An admissible predicate on activations
that holds for the failing activation and is preserved by `fbStep` holds for `fbRunω`. -/
theorem fbRunω_scott_induction (S : QRSys R τ (E ⊕ X) (O ⊕ X))
    {P : (E ⊕ X → τ → SubInstrument R R (τ × O)) → Prop} (hP : Admissible P)
    (h0 : P fun _ _ => SubInstrument.fail) (hstep : ∀ h, P h → P (S.fbStep h)) :
    P S.fbRunω := by
  rw [fbRunω_eq_ωSup]
  exact ωSup_induction hP _ S.fbStep S.fbFunChain_succ (S.fbFunChain_zero ▸ hstep _ h0) hstep

end CatCrypt.Quantum.ReactiveUC.QRSys

namespace CatCrypt.Tactics.ScottInduction

open Lean Meta Elab Tactic

/-- Discharges an admissibility goal `OmegaCompletePartialOrder.Admissible P` for `P` built
from `True`, conjunctions, universal quantifications, upper bounds by a constant, and
inequalities and equations between maps proved ω-Scott-continuous (and monotone on the right
of an inequality) by `fun_prop`. -/
syntax (name := scottAdmissibleStx) "scott_admissible" : tactic

macro_rules
  | `(tactic| scott_admissible) => `(tactic| first
      | exact OmegaCompletePartialOrder.Admissible.const_true
      | exact OmegaCompletePartialOrder.Admissible.le_const _
      | (refine OmegaCompletePartialOrder.Admissible.and ?_ ?_ <;> scott_admissible)
      | (refine OmegaCompletePartialOrder.Admissible.forall_ fun _ => ?_; scott_admissible)
      | (refine OmegaCompletePartialOrder.Admissible.le ?_ ?_ <;>
          first | fun_prop | exact monotone_const)
      | (refine OmegaCompletePartialOrder.Admissible.eq ?_ ?_ <;> fun_prop))

/-- Scott induction on a least fixed point, a supremum of iterates or an unbounded loopback
activation in the goal: abstracts the term into a predicate and leaves the premises of the
induction theorem (continuity side conditions, admissibility unless `scott_admissible` proves
it, the base case and the step). `scott_induction e` abstracts the term `e`;
`scott_induction using thm` uses the induction theorem `thm`. -/
syntax (name := scottInductionStx)
  "scott_induction" (ppSpace colGt term:max)? (" using " ident)? : tactic

meta section

/-- The induction theorems tried by `scott_induction`, in order. Each concludes `P t` for a
predicate variable `P`. -/
def scottInductionLemmas : Array Name :=
  #[``OrderHom.lfp_scott_induction,
    ``OmegaCompletePartialOrder.ωSup_iterateChain_induction,
    ``CatCrypt.Quantum.ReactiveUC.QRSys.fbRunω_scott_induction]

/-- Applies the induction theorem `thm` to the goal `g`: matches the term of its conclusion
`P t` against the goal (or against `target?`), abstracts it into the motive `P`, and returns the
premises left open, or `none` when the theorem does not apply. -/
def scottApply (g : MVarId) (thm : Name) (target? : Option Expr) :
    MetaM (Option (List MVarId)) :=
  g.withContext do
    let s ← saveState
    try
      let c ← mkConstWithFreshMVarLevels thm
      let (mvs, bis, concl) ← forallMetaTelescopeReducing (← inferType c)
      let pm := concl.getAppFn
      unless pm.isMVar && concl.getAppNumArgs == 1 do
        throwError "scott_induction: the conclusion of {thm} is not a predicate application"
      let t := concl.appArg!
      if let some e := target? then
        unless ← isDefEq t e do throwError "scott_induction: term does not match"
      let gType ← instantiateMVars (← g.getType)
      let abst ← kabstract gType (← instantiateMVars t)
      unless abst.hasLooseBVars do throwError "scott_induction: no occurrence"
      let t ← instantiateMVars t
      let abst ← instantiateMVars abst
      let motive := mkLambda `x .default (← inferType t) abst
      unless ← isDefEq pm motive do throwError "scott_induction: motive"
      unless ← isDefEq (← instantiateMVars concl) gType do throwError "scott_induction: type"
      let mut newGoals : List MVarId := []
      for m in mvs, bi in bis do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        if bi.isInstImplicit then
          let inst ← synthInstance (← inferType m)
          unless ← isDefEq m inst do throwError "scott_induction: instance"
        else
          newGoals := newGoals ++ [mid]
      g.assign (mkAppN c mvs)
      return some newGoals
    catch _ =>
      s.restore
      return none

/-- The elaborator of `scott_induction`: the first induction theorem that applies, then
`scott_admissible` on each admissibility premise. -/
@[tactic scottInductionStx]
def evalScottInduction : Tactic := fun stx => withMainContext do
  let g ← getMainGoal
  let target? ← match stx[1].getOptional? with
    | some e => some <$> elabTerm e none
    | none => pure none
  let lemmas ← match stx[2].getOptional? with
    | some u => pure #[← realizeGlobalConstNoOverloadWithInfo u[1]]
    | none => pure scottInductionLemmas
  for thm in lemmas do
    if let some gs ← scottApply g thm target? then
      let mut out : List MVarId := []
      for g' in gs do
        let ty ← instantiateMVars (← g'.getType)
        if ty.isAppOf ``OmegaCompletePartialOrder.Admissible then
          let s ← saveState
          let ok ← try
              let r ← evalTacticAt (← `(tactic| scott_admissible)) g'
              pure r.isEmpty
            catch _ => pure false
          if ok then continue
          s.restore
        out := out ++ [g']
      replaceMainGoal out
      return
  throwError "scott_induction: the goal contains no least fixed point, supremum of iterates \
    or unbounded loopback activation that an induction theorem applies to"

end

end CatCrypt.Tactics.ScottInduction

namespace CatCrypt.Quantum.ReactiveUC.QRSys

open _root_.Quantum OmegaCompletePartialOrder

variable {R : Type} [Fintype R] {τ E O X : Type}

/-- The unbounded activation of the loopback is monotone in the steps of the system. -/
theorem fbRunω_mono {S S' : QRSys R τ (E ⊕ X) (O ⊕ X)}
    (h : ∀ t g, S.step t g ≤ S'.step t g) : S.fbRunω ≤ S'.fbRunω := by
  scott_induction
  · intro g t
    exact SubInstrument.fail_le _
  · intro k hk g t
    rw [fbRunω_eq S' g t]
    exact (S.fbStep_mono hk g t).trans (SubInstrument.bind_mono_left (h t g) _)

/-- **Park induction.** The unbounded activation of the loopback is below every prefixed point
of `fbStep`. -/
theorem fbRunω_le_of_fbStep_le (S : QRSys R τ (E ⊕ X) (O ⊕ X))
    {B : E ⊕ X → τ → SubInstrument R R (τ × O)} (hB : S.fbStep B ≤ B) : S.fbRunω ≤ B := by
  scott_induction
  · intro g t
    exact SubInstrument.fail_le _
  · intro k hk
    exact (S.fbStep_mono hk).trans hB

end CatCrypt.Quantum.ReactiveUC.QRSys
