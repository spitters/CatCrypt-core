/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCOneShot
public import CatCryptCore.Crypto.UCSimulator
public import CatCryptCore.Crypto.UCMonad.SPCompInstance
public import CatCryptCore.Category.ProtBicatApprox

/-!
# 2-cells of the protocol bicategory as reactive realizations

A protocol object `P : ProtObj SPComp hon out` is a one-shot protocol
`P.prot : hon → SPComp (out ⊕ P.iface)`; its reactive form is the one-activation system
`Sys.oneShot P.prot`. A simulator `sim : L → SPComp L'` between leak interfaces becomes the
multi-call simulator `simWrap sim`: one call per activation (fuel `0`), forwarding the outer
event to the subroutine and applying `sim` to the leak branch of the answer (`leakMap sim`). It
is opaque for the view `leakView ev` that relates outputs with equal leak parts, for every
relation `ev` on events, so it is a bundled simulator (`simWrapSim`).

An exact 2-cell `f : ProtMor P Q` gives realization of `Sys.oneShot P.prot` by
`Sys.oneShot Q.prot` behind `simWrapSim f.sim` at distance `0`; an approximate 2-cell
`f : ProtMorε P Q ε` gives it at the one-shot bound of the constant `ε`. The image of the
vertical composite `f.vcomp g` is the composite of the simulators `simWrapSim g.sim` and
`simWrapSim f.sim`, up to a realization at distance `0` (`realizes_simWrap_comp`).

The simulators of `simWrap` are required to be lossless, since the steps of a `MultiHybrid`
are.

## Main definitions

* `leakMap sim` — `sim` on the leak branch of an optional one-shot result.
* `simWrap sim hsim` — the one-call simulator applying `sim` to the leak of each answer.
* `leakView ev` — the view of a one-shot interface: events related by `ev`, outputs with equal
  leak parts.
* `simWrapSim ev sim hsim` — `simWrap sim hsim` as a bundled simulator.

## Main results

* `simWrap_opaque` — `simWrap sim hsim` is opaque from `leakView ev` to `leakView ev`.
* `realizes_oneShot_simWrap` — `Sys.oneShot` of `π` post-composed with `sim` on the leak and
  `simWrap sim` over `Sys.oneShot π` realize each other at distance `0`.
* `realizes_simWrap_comp` — `simWrap g` over `simWrap f` over `X` and `simWrap` of the Kleisli
  composite over `X` realize each other at distance `0`.
* `ProtMor.realizesSim_oneShot`, `ProtMorε.realizesSim_oneShot` — 2-cells as realizations
  behind `simWrapSim`.
* `ProtMorε.realizesSim_oneShot_vcomp` — the vertical composite as realization behind the
  composite simulator.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational
open scoped ENNReal

variable {hon out L L' L'' τ : Type}

/-- `sim` applied to the leak branch of an optional one-shot result: `none` and honest outputs
are kept. -/
noncomputable def leakMap (sim : L → SPComp L') :
    Option (out ⊕ L) → SPComp (Option (out ⊕ L'))
  | none => SPComp.pure none
  | some x => SPComp.map some (mapSum SPComp.pure sim x)

/-- `leakMap` of a lossless simulator never fails. -/
theorem leakMap_noFail {sim : L → SPComp L'} (hsim : ∀ l, SPComp.NoFail (sim l))
    (o : Option (out ⊕ L)) : SPComp.NoFail (leakMap sim o) := by
  rcases o with _ | x | l
  · exact SPComp.pure_noFail _
  · exact Assumptions.SPComp.bind_noFail (Assumptions.SPComp.bind_noFail
      (SPComp.pure_noFail _) fun _ => SPComp.pure_noFail _) fun _ => SPComp.pure_noFail _
  · exact Assumptions.SPComp.bind_noFail (Assumptions.SPComp.bind_noFail
      (hsim l) fun _ => SPComp.pure_noFail _) fun _ => SPComp.pure_noFail _

/-- `leakMap` of a Kleisli composite is the composite of the `leakMap`s. -/
theorem leakMap_bind (f : L → SPComp L') (g : L' → SPComp L'') (o : Option (out ⊕ L)) :
    SPComp.bind (leakMap f o) (leakMap g) = leakMap (fun l => SPComp.bind (f l) g) o := by
  rcases o with _ | x | l
  · simp [leakMap, SPComp.pure_bind]
  · simp [leakMap, SPComp.map, SPComp.pure_bind]
  · simp [leakMap, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- The one-call simulator of `sim`: it forwards the outer event to its subroutine and applies
`sim` to the leak branch of the answer. -/
noncomputable def simWrap (sim : L → SPComp L') (hsim : ∀ l, SPComp.NoFail (sim l)) :
    MultiHybrid Unit hon (Option (out ⊕ L')) hon (Option (out ⊕ L)) where
  init := ()
  fuel := 0
  start _ e := SPComp.pure ((), .inl e)
  resume _ o := SPComp.map (fun r => ((), .inr r)) (leakMap sim o)
  finish _ o := SPComp.map (fun r => ((), r)) (leakMap sim o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ o := Assumptions.SPComp.bind_noFail (leakMap_noFail hsim o) fun _ =>
    SPComp.pure_noFail _
  finish_noFail _ o := Assumptions.SPComp.bind_noFail (leakMap_noFail hsim o) fun _ =>
    SPComp.pure_noFail _

/-- The leak part of an optional one-shot result. -/
def leakPart : Option (out ⊕ L) → Option (Option L) :=
  Option.map (Sum.elim (fun _ => none) some)

/-- The view of a one-shot interface with leak `L`: events related by `ev`, outputs with equal
leak parts. -/
def leakView (ev : hon → hon → Prop) : PubView hon (Option (out ⊕ L)) where
  ev := ev
  out o o' := leakPart o = leakPart o'

/-- `leakMap sim` on outputs with equal leak parts, coupled at equal heaps, gives outputs with
equal leak parts. -/
theorem rHoare_leakMap (sim : L → SPComp L') (o o' : Option (out ⊕ L))
    (h : leakPart o = leakPart o') :
    rHoare eqPre (leakMap sim o) (leakMap sim o')
      (fun r h₁ r' h₂ => h₁ = h₂ ∧ leakPart r = leakPart r') := by
  rcases o with _ | x | l <;> rcases o' with _ | x' | l' <;>
    simp only [leakPart, Option.map_none, Option.map_some, Sum.elim_inl, Sum.elim_inr,
      Option.some.injEq, reduceCtorEq] at h
  · exact rHoare_ret fun _ _ e => ⟨e, rfl⟩
  · simp only [leakMap, mapSum_inl, SPComp.map, SPComp.pure_bind]
    exact rHoare_ret fun _ _ e => ⟨e, rfl⟩
  · subst h
    exact rHoare_conseq (fun _ _ hh => hh)
      (fun _ _ _ _ hp => by obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl⟩) (rHoare_refl _)

/-- `simWrap sim hsim` is opaque from `leakView ev` to `leakView ev`. -/
theorem simWrap_opaque (ev : hon → hon → Prop) (sim : L → SPComp L')
    (hsim : ∀ l, SPComp.NoFail (sim l)) :
    (simWrap (out := out) sim hsim).Opaque (leakView ev) (leakView ev) := by
  refine ⟨fun _ _ => True, trivial, ?_, ?_, ?_⟩
  · intro s s' e e' _ he
    exact rHoare_ret fun _ _ h => ⟨h, trivial, he⟩
  · intro s s' o o' _ ho
    change rHoare eqPre (SPComp.map (fun r => ((), Sum.inr r)) (leakMap sim o))
      (SPComp.map (fun r => ((), Sum.inr r)) (leakMap sim o')) _
    refine rHoare_bind (rHoare_leakMap sim o o' ho) fun r r' => rHoare_ret fun _ _ h => ?_
    exact ⟨h.1, trivial, h.2⟩
  · intro s s' o o' _ ho
    refine rHoare_bind (rHoare_leakMap sim o o' ho) fun r r' => rHoare_ret fun _ _ h => ?_
    exact ⟨h.1, trivial, h.2⟩

/-- `simWrap sim hsim` as a bundled simulator for the view `leakView ev`. -/
noncomputable def simWrapSim (ev : hon → hon → Prop) (sim : L → SPComp L')
    (hsim : ∀ l, SPComp.NoFail (sim l)) :
    Simulator hon (Option (out ⊕ L')) hon (Option (out ⊕ L)) (leakView ev) (leakView ev) :=
  Simulator.ofMultiHybrid (simWrap sim hsim) (simWrap_opaque ev sim hsim)

/-- One step of `simWrap sim hsim` over `X` is one step of `X` followed by `leakMap sim`. -/
theorem simWrap_withSub_step (sim : L → SPComp L') (hsim : ∀ l, SPComp.NoFail (sim l))
    (X : Sys τ hon (Option (out ⊕ L))) (t : Unit × τ) (e : hon) :
    ((simWrap sim hsim).withSub X).step t e =
      SPComp.bind (X.step t.2 e) fun q =>
        SPComp.map (fun r => (((), q.1), r)) (leakMap sim q.2) := by
  simp [MultiHybrid.withSub, simWrap, MultiHybrid.drive, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind]

/-- `Sys.oneShot` of `π` followed by `sim` on the leak, and `simWrap sim` over
`Sys.oneShot π`, realize each other at distance `0`. -/
theorem realizes_oneShot_simWrap (π : hon → SPComp (out ⊕ L)) (sim : L → SPComp L')
    (hsim : ∀ l, SPComp.NoFail (sim l)) :
    Realizes (Sys.oneShot fun a => SPComp.bind (π a) (mapSum SPComp.pure sim))
      ((simWrap sim hsim).withSub (Sys.oneShot π)) (fun _ _ => 0) := by
  refine realizes_zero_of_stepMap _ _ (fun t => ((), t)) rfl fun t e => ?_
  rw [simWrap_withSub_step]
  cases t
  · simp [leakMap, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · simp [leakMap, SPComp.map, SPComp.pure_bind]

/-- `simWrap g` over `simWrap f` over `X`, and `simWrap` of the Kleisli composite of `f` and
`g` over `X`, realize each other at distance `0`. -/
theorem realizes_simWrap_comp (f : L → SPComp L') (g : L' → SPComp L'')
    (hf : ∀ l, SPComp.NoFail (f l)) (hg : ∀ l, SPComp.NoFail (g l))
    (X : Sys τ hon (Option (out ⊕ L))) :
    Realizes ((simWrap g hg).withSub ((simWrap f hf).withSub X))
      ((simWrap (fun l => SPComp.bind (f l) g)
        fun l => Assumptions.SPComp.bind_noFail (hf l) hg).withSub X) (fun _ _ => 0) := by
  refine realizes_zero_of_stepMap _ _ (fun t => ((), t.2.2)) rfl fun t e => ?_
  rw [simWrap_withSub_step, simWrap_withSub_step, simWrap_withSub_step]
  simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext q
  rw [← leakMap_bind]
  simp only [SPComp.bind_assoc]

end CatCrypt.Crypto.UCTransparent

namespace UCMonad

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open scoped ENNReal

variable {hon out : Type}

/-- **An exact 2-cell as a realization.** For `f : ProtMor P Q` with a lossless simulator,
`Sys.oneShot Q.prot` realizes `Sys.oneShot P.prot` behind `simWrapSim ev f.sim` at distance
`0`. -/
theorem ProtMor.realizesSim_oneShot {P Q : ProtObj SPComp hon out} (f : ProtMor P Q)
    (hsim : ∀ l, SPComp.NoFail (f.sim l)) (ev : hon → hon → Prop) :
    RealizesSim (Sys.oneShot Q.prot) (Sys.oneShot P.prot) (simWrapSim ev f.sim hsim)
      (fun _ _ => 0) := by
  have hQ : (fun a => SPComp.bind (P.prot a) (mapSum SPComp.pure f.sim)) = Q.prot :=
    funext f.comm
  have h := realizes_oneShot_simWrap P.prot f.sim hsim
  rw [hQ] at h
  exact h

/-- **An approximate 2-cell as a realization.** For `f : ProtMorε P Q ε` with a lossless
simulator, `Sys.oneShot Q.prot` realizes `Sys.oneShot P.prot` behind `simWrapSim ev f.sim`
with the one-shot bound of the constant `ε`. -/
theorem ProtMorε.realizesSim_oneShot {P Q : ProtObj SPComp hon out} {ε : ℝ≥0∞}
    (f : ProtMorε P Q ε) (hsim : ∀ l, SPComp.NoFail (f.sim l)) (ev : hon → hon → Prop) :
    RealizesSim (Sys.oneShot Q.prot) (Sys.oneShot P.prot) (simWrapSim ev f.sim hsim)
      (oneShotBound fun _ => ε) := by
  have hd : DistC (fun a => SPComp.bind (P.prot a) (mapSum SPComp.pure f.sim)) Q.prot
      (fun _ => ε) :=
    DistC_const_iff.mpr f.dist
  have h₁ := realizes_oneShot_of_distC hd.symm
  have h₂ := Realizes.trans h₁ (realizes_oneShot_simWrap P.prot f.sim hsim)
  exact fun ζ => (h₂ ζ).mono fun Z => by simp

/-- **Vertical composition.** For `f : ProtMorε P Q ε₁` and `g : ProtMorε Q R ε₂` with lossless
simulators, `Sys.oneShot R.prot` realizes `Sys.oneShot P.prot` behind the composite of
`simWrapSim ev g.sim` and `simWrapSim ev f.sim`, with the one-shot bound of `ε₁ + ε₂`: the
realization of `f.vcomp g` followed by `realizes_simWrap_comp`. -/
theorem ProtMorε.realizesSim_oneShot_vcomp {P Q R : ProtObj SPComp hon out} {ε₁ ε₂ : ℝ≥0∞}
    (f : ProtMorε P Q ε₁) (g : ProtMorε Q R ε₂) (hf : ∀ l, SPComp.NoFail (f.sim l))
    (hg : ∀ l, SPComp.NoFail (g.sim l)) (ev : hon → hon → Prop) :
    RealizesSim (Sys.oneShot R.prot) (Sys.oneShot P.prot)
      ((simWrapSim ev g.sim hg).comp (simWrapSim ev f.sim hf))
      (oneShotBound fun _ => ε₁ + ε₂) := by
  have h₁ := (f.vcomp g).realizesSim_oneShot
    (fun l => Assumptions.SPComp.bind_noFail (hf l) hg) ev
  have h₂ := realizes_simWrap_comp f.sim g.sim hf hg (Sys.oneShot P.prot)
  have h := Realizes.trans h₁ fun ζ => (h₂ ζ).symm
  exact fun ζ => (h ζ).mono fun Z => by simp

end UCMonad
