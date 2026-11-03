/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Category.ProtBicatReactive
public import CatCryptCore.Crypto.UCCoupling
public import CatCryptCore.Crypto.UCLoopbackTrace

/-!
# The protocol bicategory in the category of reactive systems

The protocol bicategory `ProtBicat SPComp` (coPara on the Kleisli category of `SPComp`) has
types as 0-cells, one-shot protocols `P : ProtObj SPComp a b` with a leakage interface
`P.iface` as 1-cells, and simulators `ProtMor`, `ProtMorε` as 2-cells. This file relates it to
the reactive systems `Sys τ E O` of `UCTransparent`, their cascade `Sys.seq`, their step
equivalence `Sys.StepEq` (the equality of morphisms of the category of systems `SysCat`) and
realization behind a simulator `RealizesSim`.

A 1-cell `P` is sent to the stateless system `P.toSys`, a one-state Mealy machine that answers
each event `x` by a fresh run of `P.prot x` (`Sys.stateless`). Its outputs lie in `Option`, as
those of the one-activation system `Sys.oneShot` do, so that the simulators `simWrapSim` of
`ProtBicatReactive` apply to it; the stateless system never outputs `none`.

* Horizontal composition is the cascade: `(P.hcomp Q).toSys` is step equivalent to the cascade
  of `P.toSys` with the router `hcompRouter P Q`, the parallel composition of `Q.toSys` with the
  forwarding system on the leakage of `P`, with its ports relabelled so that the honest output
  of `P` enters `Q` and the leakage of `P` goes to the left summand of the outer leakage
  (`ProtObj.toSys_hcomp_stepEq`).
* The identity 1-cell `hid α` is sent to the forwarding system on `α`, with outputs placed in
  the honest summand beside the empty interface (`ProtObj.toSys_hid_stepEq`).
* An exact 2-cell `f : ProtMor P Q` with a lossless simulator gives realization of `P.toSys` by
  `Q.toSys` behind `simWrapSim ev f.sim` at distance `0` (`ProtMor.realizesSim_toSys`); an
  approximate 2-cell `f : ProtMorε P Q ε` gives it with the bound `ε` per activation, that is
  `Z.input.rounds * ε` for an environment `Z` (`ProtMorε.realizesSim_toSys`).

## Main definitions

* `Sys.stateless π` — the stateless system answering each event by a run of `π`.
* `UCMonad.ProtObj.toSys P` — the system of a 1-cell.
* `UCMonad.ProtObj.hcompRouter P Q` — the router cascaded after `P.toSys`.

## Main results

* `realizes_stateless_of_sdist` — a statistical distance `ε` between Kleisli maps gives
  realization between their stateless systems with bound `Z.input.rounds * ε`.
* `realizes_stateless_simWrap` — the stateless system of `π` post-composed with `sim` on the
  leak and `simWrap sim` over the stateless system of `π` realize each other at distance `0`.
* `UCMonad.ProtObj.toSys_hcomp_stepEq`, `UCMonad.ProtObj.toSys_hid_stepEq` — horizontal
  composition and identity.
* `UCMonad.ProtMor.realizesSim_toSys`, `UCMonad.ProtMorε.realizesSim_toSys`,
  `UCMonad.ProtMorε.realizesSim_toSys_vcomp` — 2-cells as realizations behind simulators.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational CatCrypt.Crypto.UCCoupling
open scoped ENNReal

variable {hon α out L L' τ : Type}

/-- The stateless system of the Kleisli map `π`: a one-state Mealy machine that answers each
event `x` by a fresh run of `π x`, its result in `some`. -/
noncomputable def Sys.stateless (π : hon → SPComp α) : Sys Unit hon (Option α) where
  init := ()
  step _ x := SPComp.map (fun r => ((), some r)) (π x)

/-- Unfolding lemma of `Sys.stateless`: a step. -/
theorem Sys.stateless_step (π : hon → SPComp α) (t : Unit) (x : hon) :
    (Sys.stateless π).step t x = SPComp.map (fun r => ((), some r)) (π x) :=
  rfl

/-- A statistical distance `ε` between `π₁` and `π₂` gives realization of the stateless system
of `π₂` by that of `π₁` with the bound `ε` per activation. -/
theorem realizes_stateless_of_sdist {π₁ π₂ : hon → SPComp α} {ε : ℝ≥0∞}
    (h : sdist π₁ π₂ ≤ ε) :
    Realizes (Sys.stateless π₁) (Sys.stateless π₂) (fun _ Z => Z.input.rounds * ε) := by
  refine realizes_of_couplingApprox _ _ (fun _ _ => True) ε trivial fun t u x _ => ?_
  have hx : sdist (fun _ : Unit => π₁ x) (fun _ : Unit => π₂ x) ≤ ε := by
    refine le_trans ?_ h
    unfold sdist
    exact iSup_mono fun D => iSup_le fun _ => le_iSup_of_le x le_rfl
  rw [Sys.stateless_step, Sys.stateless_step]
  unfold SPComp.map
  refine rHoareApprox_mono_eps (le_of_eq (add_zero ε)) (rHoareApprox_bind
    (rHoareApprox_of_sdist hx) fun r r' => rHoareApprox_of_rHoare ?_)
  exact rHoare_ret fun _ _ hh => ⟨hh.2, trivial, by rw [hh.1]⟩

/-- The stateless system of `π` followed by `sim` on the leak, and `simWrap sim` over the
stateless system of `π`, realize each other at distance `0`. -/
theorem realizes_stateless_simWrap (π : hon → SPComp (out ⊕ L)) (sim : L → SPComp L')
    (hsim : ∀ l, SPComp.NoFail (sim l)) :
    Realizes (Sys.stateless fun a => SPComp.bind (π a) (mapSum SPComp.pure sim))
      ((simWrap sim hsim).withSub (Sys.stateless π)) (fun _ _ => 0) := by
  refine realizes_zero_of_stepMap _ _ (fun _ => ((), ())) rfl fun t e => ?_
  rw [simWrap_withSub_step]
  simp [Sys.stateless, leakMap, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end CatCrypt.Crypto.UCTransparent

namespace UCMonad

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open scoped ENNReal

variable {a b c hon out : Type}

/-- The reactive system of the 1-cell `P` of the protocol bicategory: the stateless system of
`P.prot`, with honest outputs and leakage on the summands of its output. -/
noncomputable def ProtObj.toSys (P : ProtObj SPComp a b) : Sys Unit a (Option (b ⊕ P.iface)) :=
  Sys.stateless P.prot

/-- The relabelling of the events of the router of `P.hcomp Q`: an honest output of `P` is an
event of `Q`, a leak of `P` and the absent output are forwarded. -/
def hcompRouteEv {L : Type} : Option (b ⊕ L) → b ⊕ Option L
  | none => .inr none
  | some (.inl m) => .inl m
  | some (.inr l) => .inr (some l)

/-- The relabelling of the outputs of the router of `P.hcomp Q`: outputs of `Q` keep their
honest part and put their leak in the right summand, forwarded leaks of `P` go to the left
summand. -/
def hcompRouteOut {L L₂ : Type} : Option (c ⊕ L₂) ⊕ Option L → Option (c ⊕ (L ⊕ L₂))
  | .inl o => o.map (Sum.map id Sum.inr)
  | .inr o => o.map fun l => .inr (.inl l)

/-- The router cascaded after `P.toSys` in the image of `P.hcomp Q`: `Q.toSys` in parallel with
the forwarding system on the leakage of `P`, with ports relabelled by `hcompRouteEv` and
`hcompRouteOut`. -/
noncomputable def ProtObj.hcompRouter (P : ProtObj SPComp a b) (Q : ProtObj SPComp b c) :
    Sys (Unit × Unit) (Option (b ⊕ P.iface)) (Option (c ⊕ (P.iface ⊕ Q.iface))) :=
  (Q.toSys.par (Sys.ofFun (id : Option P.iface → Option P.iface))).mapPorts
    hcompRouteEv hcompRouteOut

/-- **Horizontal composition is the cascade.** The system of `P.hcomp Q` is step equivalent to
the cascade of `P.toSys` with the router of `Q.toSys` beside the forwarding of the leakage of
`P`. -/
theorem ProtObj.toSys_hcomp_stepEq (P : ProtObj SPComp a b) (Q : ProtObj SPComp b c) :
    Sys.StepEq (⟨Unit × (Unit × Unit), P.toSys.seq (P.hcompRouter Q)⟩ : SysObj _ _)
      ⟨Unit, (P.hcomp Q).toSys⟩ := by
  refine Sys.StepMapOn.stepEq (Inv := fun _ => True) (f := fun _ => ())
    { init_inv := trivial
      init_map := rfl
      pres := fun _ _ _ _ _ => trivial
      step := fun s x _ => ?_ }
  simp only [SPComp.map, toSys, hcompRouter, Sys.seq_step, Sys.stateless_step,
    Sys.mapPorts_step, SPComp.bind_assoc, SPComp.pure_bind, hcomp, SPComp.monad_pure_eq,
    SPComp.monad_bind_eq]
  congr 1; funext r
  rcases r with m | l
  · simp only [hcompRouteEv, Sys.par_step_inl, Sys.stateless_step, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext y
    rcases y with o | j <;> simp [hcompRouteOut, SPComp.pure_bind]
  · simp [hcompRouteEv, hcompRouteOut, Sys.par_step_inr, Sys.ofFun, SPComp.map,
      SPComp.pure_bind]

/-- **The identity 1-cell is the forwarding system.** The system of `hid α` is step equivalent
to the forwarding system on `α` with its outputs in the honest summand. -/
theorem ProtObj.toSys_hid_stepEq (α : Type) :
    Sys.StepEq (⟨Unit, (ProtObj.hid (T := SPComp) α).toSys⟩ : SysObj _ _)
      ((SysObj.idSys α).mapPorts id fun x => some (Sum.inl x)) := by
  refine Sys.StepMapOn.stepEq (Inv := fun _ => True) (f := id)
    { init_inv := trivial
      init_map := rfl
      pres := fun _ _ _ _ _ => trivial
      step := fun s x _ => ?_ }
  simp [ProtObj.toSys, ProtObj.hid, Sys.stateless, SysObj.idSys, Sys.ofFun,
    Sys.mapPorts_step, SPComp.map]

/-- **An exact 2-cell as a realization.** For `f : ProtMor P Q` with a lossless simulator,
`Q.toSys` realizes `P.toSys` behind `simWrapSim ev f.sim` at distance `0`. -/
theorem ProtMor.realizesSim_toSys {P Q : ProtObj SPComp hon out} (f : ProtMor P Q)
    (hsim : ∀ l, SPComp.NoFail (f.sim l)) (ev : hon → hon → Prop) :
    RealizesSim Q.toSys P.toSys (simWrapSim ev f.sim hsim) (fun _ _ => 0) := by
  have hQ : (fun a => SPComp.bind (P.prot a) (mapSum SPComp.pure f.sim)) = Q.prot :=
    funext f.comm
  have h := realizes_stateless_simWrap P.prot f.sim hsim
  rw [hQ] at h
  exact h

/-- **An approximate 2-cell as a realization.** For `f : ProtMorε P Q ε` with a lossless
simulator, `Q.toSys` realizes `P.toSys` behind `simWrapSim ev f.sim` with the bound `ε` per
activation. -/
theorem ProtMorε.realizesSim_toSys {P Q : ProtObj SPComp hon out} {ε : ℝ≥0∞}
    (f : ProtMorε P Q ε) (hsim : ∀ l, SPComp.NoFail (f.sim l)) (ev : hon → hon → Prop) :
    RealizesSim Q.toSys P.toSys (simWrapSim ev f.sim hsim)
      (fun _ Z => Z.input.rounds * ε) := by
  have hd : sdist Q.prot (fun a => SPComp.bind (P.prot a) (mapSum SPComp.pure f.sim)) ≤ ε := by
    rw [sdist_sym]
    exact f.dist
  have h := Realizes.trans (realizes_stateless_of_sdist hd)
    (realizes_stateless_simWrap P.prot f.sim hsim)
  exact fun ζ => (h ζ).mono fun Z => by simp

/-- **Vertical composition.** For `f : ProtMorε P Q ε₁` and `g : ProtMorε Q R ε₂` with lossless
simulators, `R.toSys` realizes `P.toSys` behind the composite of `simWrapSim ev g.sim` and
`simWrapSim ev f.sim`, with the bound `ε₁ + ε₂` per activation. -/
theorem ProtMorε.realizesSim_toSys_vcomp {P Q R : ProtObj SPComp hon out} {ε₁ ε₂ : ℝ≥0∞}
    (f : ProtMorε P Q ε₁) (g : ProtMorε Q R ε₂) (hf : ∀ l, SPComp.NoFail (f.sim l))
    (hg : ∀ l, SPComp.NoFail (g.sim l)) (ev : hon → hon → Prop) :
    RealizesSim R.toSys P.toSys ((simWrapSim ev g.sim hg).comp (simWrapSim ev f.sim hf))
      (fun _ Z => Z.input.rounds * (ε₁ + ε₂)) := by
  have h₁ := (f.vcomp g).realizesSim_toSys
    (fun l => Assumptions.SPComp.bind_noFail (hf l) hg) ev
  have h₂ := realizes_simWrap_comp f.sim g.sim hf hg P.toSys
  have h := Realizes.trans h₁ fun ζ => (h₂ ζ).symm
  exact fun ζ => (h ζ).mono fun Z => by simp

end UCMonad
