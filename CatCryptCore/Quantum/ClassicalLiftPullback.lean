/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.ClassicalLiftReflect
public import CatCryptCore.Crypto.UCPullbackSemantics
public import CatCryptCore.Quantum.QPullback

/-!
# The classical lift as a pullback of advantage theories

The classical lift `liftQSys` is a change of semantics from classical reactive systems to
quantum reactive systems, stated as a pullback `liftPullback` between advantage theories
(`AdvPullback` of `CatCrypt.Crypto.UCTransparent`).

* The source is the view theory `viewTheory E O`: classical systems tested by classical
  strategies with heap-independent activations (`StratPure`); the advantage of a strategy is the
  statistical distance of the two views from the empty heap, the supremum over all
  distinguishers.
* The target is the lift theory `liftTheory E O d`: quantum systems tested by the environments
  `liftStrat Z` that are lifts of the same classical strategies; the advantage is the diamond
  distance `cpDist` of the two quantum views.
* The relation sends a heap-independent system `S` to its lift `liftQSys S`; the pull of tests
  sends the lifted environment `liftStrat Z` to its classical strategy `Z`.

The advantage equation of the pullback (`cpDist_qview_liftQSys`) is the diagonal-embedding
distance identity: the quantum view of a lift is the diagonal embedding of the classical view
(`qview_liftQSys_toQComp`), and the diamond distance of diagonal embeddings is their statistical
distance (`ClassicalDiamondLift.qdistDiamond_classicalEmbed_eq`). Since the pull of tests has a
section (it is the identity on strategies), the pullback also reflects realizations
(`AdvPullback.realizes_of_rel`).

Realization in the view theory at a constant bound is classical realization `Realizes` against
every classical environment, for heap-independent systems (`viewTheory_realizes_iff`): an
environment whose strategy keeps state on the heap is replaced by the carried environment
`carryEnv`, which has the same advantage. Realization in the lift theory at a constant bound is
the diamond-norm bound `QUCEmulatesDiamond` on the views of the lifted environments
(`liftTheory_realizes_iff`). With these two bridges the pullback law gives
`quc_liftQSys_of_realizes_le` and `quc_liftQSys_of_realizes`, and the reflection gives
`quc_liftQSys_iff_realizes`.

Search words: classical lift, change of semantics, pullback, reflection, diagonal embedding,
diamond norm, statistical distance, carried heap.

## Main definitions

* `viewTheory`, `liftTheory`, `liftPullback`

## Main results

* `AdvPullback.realizes_of_rel`: reflection along a pullback whose pull of tests has a section.
* `cpDist_qview_liftQSys`: the advantage equation of the classical lift.
* `viewTheory_realizes_iff`, `liftTheory_realizes_iff`: realization in the two theories.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.AdvPullback

open scoped ENNReal

universe u v u' v'

variable {T : AdvTheory.{u, v}} {T' : AdvTheory.{u', v'}}

/-- **Reflection along a pullback.** If the pull of tests has a section `s`, a realization of
related images with bound `b ∘ pull` gives the realization of the sources with bound `b`. -/
theorem realizes_of_rel (F : AdvPullback T T') {x y : T.System} {x' y' : T'.System}
    (hx : F.Rel x x') (hy : F.Rel y y') (s : T.Test → T'.Test) (hs : ∀ t, F.pull (s t) = t)
    {b : T.Test → ℝ≥0∞} (h : T'.Realizes x' y' fun t => b (F.pull t)) : T.Realizes x y b :=
  fun t => by
    have ht : T'.adv x' y' (s t) ≤ b (F.pull (s t)) := h (s t)
    rw [F.adv_rel hx hy, hs] at ht
    exact ht

end CatCrypt.Crypto.UCTransparent.AdvPullback

namespace CatCrypt.Quantum.ClassicalLiftSys

open CatCrypt.Core CatCrypt.Prob
open CatCrypt.Crypto.UCTransparent CatCrypt.Quantum.ReactiveUC
open CatCrypt.Crypto.UCMonad.DiamondNorm UCMonad.SDistrUC
open CatCrypt.Crypto.SDistrLift CatCrypt.Crypto.UCTransport
open CatCrypt.Crypto.UCConcrete (Env)
open scoped ENNReal

variable {τ υ E O ζ : Type} {d : ℕ}

/-- The view theory of classical reactive systems: tests are strategies with heap-independent
activations on any state type, and the advantage of a strategy `Z` is the statistical distance of
the views of `Z` from the empty heap. -/
noncomputable def viewTheory (E O : Type) : AdvTheory.{1, 1} where
  System := Σ τ : Type, Sys τ E O
  Test := Σ ζ : Type, {Z : Strat ζ E O // StratPure Z}
  adv X Y Z := sdistD (fun _ : Unit => heapFree (view X.2 Z.2.1))
    (fun _ => heapFree (view Y.2 Z.2.1))

/-- The quantum advantage theory restricted to lifted environments: quantum reactive systems on
`Fin d`, tested by the lifts `liftStrat Z` of strategies `Z` with heap-independent activations,
with the diamond distance of the two views as advantage. -/
noncomputable def liftTheory (E O : Type) (d : ℕ) : AdvTheory.{1, 1} where
  System := QSysObj E O d
  Test := Σ ζ : Type, {Z : Strat ζ E O // StratPure Z}
  adv X Y Z := cpDist (qview X.sys (liftStrat Z.2.1)) (qview Y.sys (liftStrat Z.2.1))

/-- **Advantage equation of the classical lift.** Against a lifted heap-independent strategy, the
diamond distance of the views of the lifts of heap-independent systems is the statistical
distance of the classical views from the empty heap. -/
theorem cpDist_qview_liftQSys [NeZero d] {S : Sys τ E O} {I : Sys υ E O} (hS : S.HeapPure)
    (hI : I.HeapPure) (Z : {Z : Strat ζ E O // StratPure Z}) :
    cpDist (qview (liftQSys (d := d) S) (liftStrat Z.1)) (qview (liftQSys I) (liftStrat Z.1)) =
      sdistD (fun _ : Unit => heapFree (view S Z.1)) (fun _ => heapFree (view I Z.1)) := by
  have e := ClassicalDiamondLift.qdistDiamond_classicalEmbed_eq (d := d)
    (fun _ : Unit => heapFree (view S Z.1)) (fun _ => heapFree (view I Z.1))
  refine le_antisymm ?_ ?_
  · exact quc_congr _ _ e.le (funext fun _ => (qview_liftQSys_toQComp hS Z).symm)
      (funext fun _ => (qview_liftQSys_toQComp hI Z).symm)
  · rw [← e]
    exact quc_congr _ _ (le_refl (cpDist (qview (liftQSys (d := d) S) (liftStrat Z.1))
      (qview (liftQSys I) (liftStrat Z.1))))
      (funext fun _ => qview_liftQSys_toQComp hS Z) (funext fun _ => qview_liftQSys_toQComp hI Z)

/-- **The classical lift as a pullback.** A heap-independent classical system is related to its
lift `liftQSys`, and the lifted environment `liftStrat Z` is pulled back to its classical
strategy `Z`. -/
noncomputable def liftPullback (E O : Type) (d : ℕ) [NeZero d] :
    AdvPullback (viewTheory E O) (liftTheory E O d) where
  Rel X X' := X.2.HeapPure ∧ X' = { H := Unit, τ := X.1, sys := liftQSys X.2 }
  pull Z := Z
  adv_rel := by
    rintro ⟨_, S⟩ _ ⟨_, I⟩ _ ⟨hS, rfl⟩ ⟨hI, rfl⟩ ⟨ζ, Z⟩
    exact cpDist_qview_liftQSys hS hI Z

/-- **Realization in the view theory.** For heap-independent systems, realization at the constant
bound `ε` in the view theory is classical realization at `ε` against every classical environment;
an environment whose strategy keeps state on the heap is replaced by its carried environment
`carryEnv`. -/
theorem viewTheory_realizes_iff {S : Sys τ E O} {I : Sys υ E O} (hS : S.HeapPure)
    (hI : I.HeapPure) {ε : ℝ≥0∞} :
    (viewTheory E O).Realizes ⟨τ, S⟩ ⟨υ, I⟩ (fun _ => ε) ↔
      Realizes S I fun _ _ => ε := by
  constructor
  · intro h ζ Z
    refine (adv_carryEnv hS hI Z).symm.le.trans
      ((adv_le_sdistD_heapFree_view hS hI (carryEnv Z) (carryStrat_stratPure _ _)).trans ?_)
    exact iSup₂_le fun D a => le_trans (le_iSup₂_of_le D () le_rfl) (h ⟨_, a⟩)
  · intro h Z
    exact sdistD_heapFree_view_le h fun _ : Unit => Z.2.1

/-- **Realization in the lift theory.** Realization at the constant bound `ε` in the lift theory
is the diamond-norm bound `ε` between the views of the two quantum systems against the lifted
environments, for every state type. -/
theorem liftTheory_realizes_iff (X Y : QSysObj E O d) {ε : ℝ≥0∞} :
    (liftTheory E O d).Realizes X Y (fun _ => ε) ↔
      ∀ ζ : Type, QUCEmulatesDiamond ε
        (fun Z : {Z : Strat ζ E O // StratPure Z} => (qview X.sys (liftStrat Z.1)).toQComp)
        (fun Z => (qview Y.sys (liftStrat Z.1)).toQComp)
        (fun Z => CPComp.branch_cp (qview X.sys (liftStrat Z.1)))
        (fun Z => CPComp.branch_cp (qview Y.sys (liftStrat Z.1))) := by
  constructor
  · intro h ζ
    exact (quc_iff_cpDist _ _).2 fun Z => h ⟨ζ, Z⟩
  · intro h Z
    exact (quc_iff_cpDist _ _).1 (h Z.1) Z.2

/-- `quc_liftQSys_of_realizes_le` is the law of `liftPullback`. -/
example [NeZero d] {S : Sys τ E O} {I : Sys υ E O} (hS : S.HeapPure) (hI : I.HeapPure)
    {ε : ℝ≥0∞} (h : Realizes S I fun _ _ => ε) (ζ : Type) :
    QUCEmulatesDiamond ε
      (fun Z : {Z : Strat ζ E O // StratPure Z} =>
        (qview (liftQSys (d := d) S) (liftStrat Z.1)).toQComp)
      (fun Z => (qview (liftQSys I) (liftStrat Z.1)).toQComp)
      (fun Z => CPComp.branch_cp (qview (liftQSys S) (liftStrat Z.1)))
      (fun Z => CPComp.branch_cp (qview (liftQSys I) (liftStrat Z.1))) :=
  (liftTheory_realizes_iff { H := Unit, τ := τ, sys := liftQSys S }
    { H := Unit, τ := υ, sys := liftQSys I }).1
    ((liftPullback E O d).realizes_rel (x := ⟨τ, S⟩) (y := ⟨υ, I⟩)
      (x' := { H := Unit, τ := τ, sys := liftQSys S })
      (y' := { H := Unit, τ := υ, sys := liftQSys I }) ⟨hS, rfl⟩ ⟨hI, rfl⟩
      (b := fun _ => ε) ((viewTheory_realizes_iff hS hI).2 h)) ζ

/-- `quc_liftQSys_of_realizes` is the law of `liftPullback` at the bound `0`. -/
example [NeZero d] {S : Sys τ E O} {I : Sys υ E O} (hS : S.HeapPure) (hI : I.HeapPure)
    (h : Realizes S I fun _ _ => 0) (ζ : Type) :
    QUCEmulatesDiamond 0
      (fun Z : {Z : Strat ζ E O // StratPure Z} =>
        (qview (liftQSys (d := d) S) (liftStrat Z.1)).toQComp)
      (fun Z => (qview (liftQSys I) (liftStrat Z.1)).toQComp)
      (fun Z => CPComp.branch_cp (qview (liftQSys S) (liftStrat Z.1)))
      (fun Z => CPComp.branch_cp (qview (liftQSys I) (liftStrat Z.1))) :=
  (liftTheory_realizes_iff { H := Unit, τ := τ, sys := liftQSys S }
    { H := Unit, τ := υ, sys := liftQSys I }).1
    ((liftPullback E O d).realizes_rel (x := ⟨τ, S⟩) (y := ⟨υ, I⟩)
      (x' := { H := Unit, τ := τ, sys := liftQSys S })
      (y' := { H := Unit, τ := υ, sys := liftQSys I }) ⟨hS, rfl⟩ ⟨hI, rfl⟩
      (b := fun _ => 0) ((viewTheory_realizes_iff hS hI).2 h)) ζ

/-- `quc_liftQSys_iff_realizes` is the law of `liftPullback` and its reflection. -/
example [NeZero d] {S : Sys τ E O} {I : Sys υ E O} (hS : S.HeapPure) (hI : I.HeapPure)
    {ε : ℝ≥0∞} :
    Realizes S I (fun _ _ => ε) ↔
      ∀ ζ : Type, QUCEmulatesDiamond ε
        (fun Z : {Z : Strat ζ E O // StratPure Z} =>
          (qview (liftQSys (d := d) S) (liftStrat Z.1)).toQComp)
        (fun Z => (qview (liftQSys I) (liftStrat Z.1)).toQComp)
        (fun Z => CPComp.branch_cp (qview (liftQSys S) (liftStrat Z.1)))
        (fun Z => CPComp.branch_cp (qview (liftQSys I) (liftStrat Z.1))) :=
  ⟨fun h => (liftTheory_realizes_iff { H := Unit, τ := τ, sys := liftQSys S }
      { H := Unit, τ := υ, sys := liftQSys I }).1
      ((liftPullback E O d).realizes_rel (x := ⟨τ, S⟩) (y := ⟨υ, I⟩)
        (x' := { H := Unit, τ := τ, sys := liftQSys S })
        (y' := { H := Unit, τ := υ, sys := liftQSys I }) ⟨hS, rfl⟩ ⟨hI, rfl⟩
        (b := fun _ => ε) ((viewTheory_realizes_iff hS hI).2 h)),
    fun h => (viewTheory_realizes_iff hS hI).1
      ((liftPullback E O d).realizes_of_rel (x := ⟨τ, S⟩) (y := ⟨υ, I⟩)
        (x' := { H := Unit, τ := τ, sys := liftQSys S })
        (y' := { H := Unit, τ := υ, sys := liftQSys I }) ⟨hS, rfl⟩ ⟨hI, rfl⟩ id
        (fun _ => rfl) (b := fun _ => ε)
        ((liftTheory_realizes_iff { H := Unit, τ := τ, sys := liftQSys S }
          { H := Unit, τ := υ, sys := liftQSys I }).2 h))⟩

end CatCrypt.Quantum.ClassicalLiftSys
