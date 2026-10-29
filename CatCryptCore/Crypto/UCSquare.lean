/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulator

/-!
# Squares of open systems and simulators

A square with top `π : Open EF OF EG OG`, bottom `π' : Open EF' OF' EG' OG'`, left simulator
`SG` from `(EG', OG')` to `(EG, OG)` and right simulator `SF` from `(EF', OF')` to `(EF, OF)`
states that for every admissible subroutine `K` on `(EG', OG')`, the system `π` over `SG` over
`K` realizes `SF` over `π'` over `K`, with a bound `b K` that depends on `K` and on the outer
environment (`Square`). Squares compose vertically along a common horizontal edge
(`Square.vcomp`, the bounds added after reducing the environment through the right simulator)
and horizontally along a common vertical edge (`Square.hcomp`, the bounds added after reducing
the environment through the top system); the identity squares are `Square.idH` and
`Square.idV`. A square whose horizontal edges are closed systems (`Open.closed`) and whose left
edge is the identity is realization behind the right simulator (`Square.ofRealizesSim`,
`Square.toRealizesSim`, `Square.closed_iff`).

The composition theorems of hybrid and multi-call hybrid protocols follow as the horizontal
composite of the identity square on the protocol with the square of the subroutine
realization, followed by the vertical composite with the square of the hybrid realization
(`Hybrid.realizes_compose_ofSquare`, `MultiHybrid.realizes_compose_ofSquare`,
`Hybrid.transparent_compose_ofSquare`).

## Main definitions

* `Square π π' SG SF A b`: the square with admissibility `A` and bound `b`.

## Main results

* `Square.vcomp`, `Square.hcomp`, `Square.whisker`: composition and whiskering.
* `Square.idH`, `Square.idV`: identity squares, at bound `0`.
* `Square.closed_iff`: the closed column is `RealizesSim`.
* `Hybrid.realizes_compose_ofSquare`, `MultiHybrid.realizes_compose_ofSquare`,
  `Hybrid.transparent_compose_ofSquare`: the composition theorems from squares.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-- The square with top `π`, bottom `π'`, left simulator `SG` and right simulator `SF`, at the
admissibility `A` and the bound `b`: for every subroutine `K` with `A K`, the system `π` over
`SG` over `K` realizes `SF` over `π'` over `K` with bound `b K`. -/
structure Square {EF OF EG OG EF' OF' EG' OG' : Type} {VF : PubView EF OF}
    {VG : PubView EG OG} {VF' : PubView EF' OF'} {VG' : PubView EG' OG'}
    (π : Open EF OF EG OG) (π' : Open EF' OF' EG' OG')
    (SG : Simulator EG OG EG' OG' VG VG') (SF : Simulator EF OF EF' OF' VF VF')
    (A : {τ : Type} → Sys τ EG' OG' → Prop)
    (b : {τ : Type} → Sys τ EG' OG' → (ζ : Type) → Env (Strat ζ EF OF) ζ → ℝ≥0∞) : Prop where
  /-- The realization at every admissible subroutine `K`. -/
  realizes : ∀ {τ : Type} (K : Sys τ EG' OG'), A K →
    Realizes (π.withSub (SG.withSub K)) (SF.withSub (π'.withSub K)) (b K)

namespace Square

variable {EF OF EG OG EF' OF' EG' OG' : Type} {VF : PubView EF OF} {VG : PubView EG OG}
  {VF' : PubView EF' OF'} {VG' : PubView EG' OG'}

/-- A square holds for a smaller admissibility and a larger bound. -/
theorem mono {π : Open EF OF EG OG} {π' : Open EF' OF' EG' OG'}
    {SG : Simulator EG OG EG' OG' VG VG'} {SF : Simulator EF OF EF' OF' VF VF'}
    {A A' : {τ : Type} → Sys τ EG' OG' → Prop}
    {b b' : {τ : Type} → Sys τ EG' OG' → (ζ : Type) → Env (Strat ζ EF OF) ζ → ℝ≥0∞}
    (h : Square π π' SG SF A b) (hA : ∀ {τ : Type} (K : Sys τ EG' OG'), A' K → A K)
    (hb : ∀ {τ : Type} (K : Sys τ EG' OG') ζ Z, b K ζ Z ≤ b' K ζ Z) :
    Square π π' SG SF A' b' :=
  ⟨fun K hK ζ => (h.realizes K (hA K hK) ζ).mono (hb K ζ)⟩

/-- The horizontal identity square on `π`: the identity simulators on both sides, at bound
`0`. -/
theorem idH (π : Open EF OF EG OG) (A : {τ : Type} → Sys τ EG OG → Prop) :
    Square π π (Simulator.id EG OG VG) (Simulator.id EF OF VF) A (fun _ _ _ => 0) :=
  ⟨fun _ _ _ => DistC.refl _⟩

/-- The vertical identity square on the simulator `S`: the identity open systems on top and
bottom, at bound `0`. -/
theorem idV (S : Simulator EG OG EG' OG' VG VG') (A : {τ : Type} → Sys τ EG' OG' → Prop) :
    Square (Open.id EG OG) (Open.id EG' OG') S S A (fun _ _ _ => 0) :=
  ⟨fun _ _ _ => DistC.refl _⟩

/-- **Vertical composition.** The square `α` on top of the square `β`, along the bottom `π'`
of `α`, with the right simulator of `α` an open system: the bound is that of `α` at
`SG'.withSub K` plus that of `β` at the environment reduced through `SF`. -/
theorem vcomp {EF'' OF'' EG'' OG'' : Type} {VF'' : PubView EF'' OF''} {VG'' : PubView EG'' OG''}
    {π : Open EF OF EG OG} {π' : Open EF' OF' EG' OG'} {π'' : Open EF'' OF'' EG'' OG''}
    {SG : Simulator EG OG EG' OG' VG VG'} {SF : SimR EF OF EF' OF' VF VF'}
    {SG' : Simulator EG' OG' EG'' OG'' VG' VG''} {SF' : Simulator EF' OF' EF'' OF'' VF' VF''}
    {Aα : {τ : Type} → Sys τ EG' OG' → Prop} {Aβ A : {τ : Type} → Sys τ EG'' OG'' → Prop}
    {bα : {τ : Type} → Sys τ EG' OG' → (ζ : Type) → Env (Strat ζ EF OF) ζ → ℝ≥0∞}
    {bβ : {τ : Type} → Sys τ EG'' OG'' → (ζ : Type) → Env (Strat ζ EF' OF') ζ → ℝ≥0∞}
    (α : Square π π' SG SF.toSimulator Aα bα) (β : Square π' π'' SG' SF' Aβ bβ)
    (hA : ∀ {τ : Type} (K : Sys τ EG'' OG''), A K →
      Aα (SG'.withSub K) ∧ Aβ K ∧ SF.Adm (π'.withSub (SG'.withSub K)) ∧
        SF.Adm (SF'.withSub (π''.withSub K))) :
    Square π π'' (SG.comp SG') (SF.toSimulator.comp SF') A
      (fun K ζ Z => bα (SG'.withSub K) ζ Z + bβ K (SF.Ctx ζ) (SF.toOpen.reduceEnv Z)) :=
  ⟨fun K hK =>
    Realizes.trans (α.realizes _ (hA K hK).1)
      (SF.toOpen.realizes_withSub (hA K hK).2.2.1 (hA K hK).2.2.2
        (β.realizes K (hA K hK).2.1))⟩

/-- **Horizontal composition.** The square `α` to the left of the square `β`, along the left
simulator `SG` of `α`: the bound is that of `β` at the environment reduced through `π` plus that
of `α` at `ρ'.withSub K`. -/
theorem hcomp {EH OH EH' OH' : Type} {VH : PubView EH OH} {VH' : PubView EH' OH'}
    {π : Open EF OF EG OG} {π' : Open EF' OF' EG' OG'}
    {ρ : Open EG OG EH OH} {ρ' : Open EG' OG' EH' OH'}
    {SH : Simulator EH OH EH' OH' VH VH'} {SG : Simulator EG OG EG' OG' VG VG'}
    {SF : Simulator EF OF EF' OF' VF VF'}
    {Aα : {τ : Type} → Sys τ EG' OG' → Prop} {Aβ A : {τ : Type} → Sys τ EH' OH' → Prop}
    {bα : {τ : Type} → Sys τ EG' OG' → (ζ : Type) → Env (Strat ζ EF OF) ζ → ℝ≥0∞}
    {bβ : {τ : Type} → Sys τ EH' OH' → (ζ : Type) → Env (Strat ζ EG OG) ζ → ℝ≥0∞}
    (α : Square π π' SG SF Aα bα) (β : Square ρ ρ' SH SG Aβ bβ)
    (hA : ∀ {τ : Type} (K : Sys τ EH' OH'), A K →
      Aβ K ∧ Aα (ρ'.withSub K) ∧ π.Adm (ρ.withSub (SH.withSub K)) ∧
        π.Adm (SG.withSub (ρ'.withSub K))) :
    Square (π.comp ρ) (π'.comp ρ') SH SF A
      (fun K ζ Z => bβ K (π.Ctx ζ) (π.reduceEnv Z) + bα (ρ'.withSub K) ζ Z) :=
  ⟨fun K hK =>
    Realizes.trans
      (π.realizes_withSub (hA K hK).2.2.1 (hA K hK).2.2.2 (β.realizes K (hA K hK).1))
      (α.realizes _ (hA K hK).2.1)⟩

/-- **Whiskering** by an open system `P` on top: a square with the identity right simulator
gives the square of the composites with `P`, with the bound at the environment reduced through
`P`. -/
theorem whisker {E O : Type} {V : PubView E O} (P : Open E O EF OF)
    {π : Open EF OF EG OG} {π' : Open EF OF EG' OG'} {SG : Simulator EG OG EG' OG' VG VG'}
    {A A' : {τ : Type} → Sys τ EG' OG' → Prop}
    {b : {τ : Type} → Sys τ EG' OG' → (ζ : Type) → Env (Strat ζ EF OF) ζ → ℝ≥0∞}
    (α : Square π π' SG (Simulator.id EF OF VF) A b)
    (hA : ∀ {τ : Type} (K : Sys τ EG' OG'), A' K →
      A K ∧ P.Adm (π.withSub (SG.withSub K)) ∧ P.Adm (π'.withSub K)) :
    Square (P.comp π) (P.comp π') SG (Simulator.id E O V) A'
      (fun K ζ Z => b K (P.Ctx ζ) (P.reduceEnv Z)) := by
  have h := hcomp (idH P (VG := VF) (VF := V) (fun _ => True)) α (A := A')
    fun K hK => ⟨(hA K hK).1, trivial, (hA K hK).2.1, (hA K hK).2.2⟩
  refine ⟨fun K hK ζ Z => ?_⟩
  simpa only [add_zero] using h.realizes K hK ζ Z

/-- A realization behind `S` is a square whose horizontal edges are closed systems, with the
identity on the left. -/
theorem ofRealizesSim {VU : PubView Unit Unit} {τ υ : Type} {R : Sys τ EF OF}
    {I : Sys υ EF' OF'} {S : Simulator EF OF EF' OF' VF VF'}
    {b : (ζ : Type) → Env (Strat ζ EF OF) ζ → ℝ≥0∞} (h : RealizesSim R I S b)
    (A : {τ : Type} → Sys τ Unit Unit → Prop) :
    Square (Open.closed R) (Open.closed I) (Simulator.id Unit Unit VU) S A (fun _ => b) :=
  ⟨fun _ _ => h⟩

/-- A square whose horizontal edges are closed systems, with the identity on the left, is a
realization behind its right simulator, with the bound at every admissible subroutine. -/
theorem toRealizesSim {VU : PubView Unit Unit} {τ υ : Type} {R : Sys τ EF OF}
    {I : Sys υ EF' OF'} {S : Simulator EF OF EF' OF' VF VF'}
    {A : {τ : Type} → Sys τ Unit Unit → Prop}
    {b : {τ : Type} → Sys τ Unit Unit → (ζ : Type) → Env (Strat ζ EF OF) ζ → ℝ≥0∞}
    (h : Square (Open.closed R) (Open.closed I) (Simulator.id Unit Unit VU) S A b)
    {τ' : Type} (K : Sys τ' Unit Unit) (hK : A K) : RealizesSim R I S (b K) :=
  h.realizes K hK

/-- **The closed column**: a square whose horizontal edges are closed systems, with the identity
on the left, every subroutine admissible and a bound independent of the subroutine, is a
realization behind the right simulator. -/
theorem closed_iff {VU : PubView Unit Unit} {τ υ : Type} {R : Sys τ EF OF}
    {I : Sys υ EF' OF'} {S : Simulator EF OF EF' OF' VF VF'}
    {b : (ζ : Type) → Env (Strat ζ EF OF) ζ → ℝ≥0∞} :
    Square (Open.closed R) (Open.closed I) (Simulator.id Unit Unit VU) S (fun _ => True)
      (fun _ => b) ↔ RealizesSim R I S b :=
  ⟨fun h => h.toRealizesSim (⟨(), fun t _ => SPComp.pure (t, ())⟩ : Sys Unit Unit Unit) trivial,
    fun h => ⟨fun _ _ => h⟩⟩

end Square

/-! ## The composition theorems from squares -/

namespace Hybrid

variable {σ τ υ E O EG OG : Type}

/-- **Hybrid composition** (composition plumbing), from squares: the horizontal composite of
the identity square on `π` with the square of `X` over `Y`, followed by the vertical composite
with the square of `π.withSub Y` over `I`. The statement is that of `Hybrid.realizes_compose`. -/
theorem realizes_compose_ofSquare {υ' : Type} (π : Hybrid σ E O EG OG) (X : Sys τ EG OG)
    (Y : Sys υ EG OG) (I : Sys υ' E O)
    (b₁ : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞)
    (b₂ : (ζ : Type) → Env (Strat ζ EG OG) ζ → ℝ≥0∞)
    (h₁ : Realizes (π.withSub Y) I b₁) (h₂ : Realizes X Y b₂) :
    Realizes (π.withSub X) I (fun ζ Z => b₂ (ζ × σ) (π.reduceEnv Z) + b₁ ζ Z) := by
  let VU : PubView Unit Unit := PubView.ofProj _root_.id _root_.id
  let VG : PubView EG OG := PubView.ofProj _root_.id _root_.id
  let V : PubView E O := PubView.ofProj _root_.id _root_.id
  have hβ := Square.ofRealizesSim (VU := VU) (S := Simulator.id EG OG VG) h₂ (fun _ => True)
  have hh := Square.hcomp (Square.idH (Open.ofHybrid π) (VF := V) (fun _ => True)) hβ
    (A := fun _ => True) fun _ _ => ⟨trivial, trivial, trivial, trivial⟩
  have hγ : Square ((Open.ofHybrid π).comp (Open.closed Y)) (Open.closed I)
      (Simulator.id Unit Unit VU) (SimR.id E O V).toSimulator (fun _ => True)
      (fun _ => b₁) := ⟨fun _ _ => h₁⟩
  have hv := Square.vcomp (SF := SimR.id E O V) (A := fun _ => True) hh hγ fun _ _ =>
    ⟨trivial, trivial, trivial, trivial⟩
  have h := hv.realizes (⟨(), fun t _ => SPComp.pure (t, ())⟩ : Sys Unit Unit Unit) trivial
  intro ζ Z
  refine le_of_le_of_eq (h ζ Z) ?_
  simp only [add_zero]
  exact congrArg₂ (fun E E' => b₂ (ζ × σ) E + b₁ ζ E') (Open.reduceEnv_ofHybrid π Z)
    (Open.reduceEnv_id Z)

/-- **Transparent hybrid composition** (composition plumbing), from squares. The statement is
that of `Hybrid.transparent_compose`. -/
theorem transparent_compose_ofSquare {σG : Type} (π : Hybrid σ E O EG OG)
    (ρ S_G : Sys σG EG OG) (G : TFunc σG EG OG)
    (S_F : Sys (σ × σG × Trace σG EG OG × Bool) E O)
    (F : TFunc (σ × σG × Trace σG EG OG × Bool) E O)
    (hρ : ∀ s e, SPComp.NoFail (ρ.step s e)) (hSG : ∀ s e, SPComp.NoFail (S_G.step s e))
    (hSF : ∀ s e, SPComp.NoFail (S_F.step s e))
    (hinitG : S_G.init = ρ.init) (hinitF : S_F.init = (π.withSub (ideal G S_G)).init)
    (hsimG : ∀ s (tr : Trace σG EG OG) e,
      SPComp.bind (ρ.step s e) (fun p => if G.guard (tr ++ [(e, p.2, p.1)])
        then SPComp.pure p else SPComp.fail) =
      SPComp.bind (S_G.step s e) (fun p => if G.guard (tr ++ [(e, p.2, p.1)])
        then SPComp.pure p else SPComp.fail))
    (hsimF : ∀ s (tr : Trace (σ × σG × Trace σG EG OG × Bool) E O) e,
      SPComp.bind ((π.withSub (ideal G S_G)).step s e)
        (fun p => if F.guard (tr ++ [(e, p.2, p.1)]) then SPComp.pure p else SPComp.fail) =
      SPComp.bind (S_F.step s e)
        (fun p => if F.guard (tr ++ [(e, p.2, p.1)]) then SPComp.pure p else SPComp.fail)) :
    Realizes (π.withSub ρ) (ideal F S_F) (fun _ Z =>
      guardFail ρ G.guard (π.reduceEnv Z) + guardFail (π.withSub (ideal G S_G)) F.guard Z) :=
  realizes_compose_ofSquare π ρ (ideal G S_G) (ideal F S_F) _ _
    (transparent_realizes (π.withSub (ideal G S_G)) F S_F hinitF
      (withSub_noFail π _ (ideal_noFail G S_G hSG)) hSF hsimF)
    (transparent_realizes ρ G S_G hinitG hρ hSG hsimG)

end Hybrid

namespace MultiHybrid

variable {σ τ υ E O EG OG : Type}

/-- **Multi-call hybrid composition** (composition plumbing), from squares: the horizontal
composite of the identity square on `π` with the square of `X` over `Y`, followed by the
vertical composite with the square of `π.withSub Y` over `I`. The statement is that of
`MultiHybrid.realizes_compose`. -/
theorem realizes_compose_ofSquare {υ' : Type} (π : MultiHybrid σ E O EG OG) (idle : EG)
    (oX oY : OG) (X : Sys τ EG OG) (Y : Sys υ EG OG) (I : Sys υ' E O)
    (hX : IdleAt X idle oX) (hY : IdleAt Y idle oY)
    (b₁ : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞)
    (b₂ : (ζ : Type) → Env (Strat ζ EG OG) ζ → ℝ≥0∞)
    (h₁ : Realizes (π.withSub Y) I b₁) (h₂ : Realizes X Y b₂) :
    Realizes (π.withSub X) I
      (fun ζ Z => b₂ (RState σ ζ EG O) (π.reduceEnv idle Z) + b₁ ζ Z) := by
  let VU : PubView Unit Unit := PubView.ofProj _root_.id _root_.id
  let VG : PubView EG OG := PubView.ofProj _root_.id _root_.id
  let V : PubView E O := PubView.ofProj _root_.id _root_.id
  have hβ := Square.ofRealizesSim (VU := VU) (S := Simulator.id EG OG VG) h₂ (fun _ => True)
  have hh := Square.hcomp (Square.idH (Open.ofMultiHybrid π idle) (VF := V) (fun _ => True)) hβ
    (A := fun _ => True) fun _ _ => ⟨trivial, trivial, ⟨oX, hX⟩, ⟨oY, hY⟩⟩
  have hγ : Square ((Open.ofMultiHybrid π idle).comp (Open.closed Y)) (Open.closed I)
      (Simulator.id Unit Unit VU) (SimR.id E O V).toSimulator (fun _ => True)
      (fun _ => b₁) := ⟨fun _ _ => h₁⟩
  have hv := Square.vcomp (SF := SimR.id E O V) (A := fun _ => True) hh hγ fun _ _ =>
    ⟨trivial, trivial, trivial, trivial⟩
  have h := hv.realizes (⟨(), fun t _ => SPComp.pure (t, ())⟩ : Sys Unit Unit Unit) trivial
  intro ζ Z
  refine le_of_le_of_eq (h ζ Z) ?_
  simp only [add_zero]
  exact congrArg₂ (fun E E' => b₂ (RState σ ζ EG O) E + b₁ ζ E')
    (Open.reduceEnv_ofMultiHybrid π idle Z) (Open.reduceEnv_id Z)

end MultiHybrid

end CatCrypt.Crypto.UCTransparent
