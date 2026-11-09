/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.Commitments.KZG.KnowledgeSoundness
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the KZG knowledge-soundness reduction

The t-SDH reduction `ks_to_tSDH A` of `CatCryptCore.Examples.Commitments.KZG.KnowledgeSoundness`
runs the AGM adversary `A` on the SRS, forms the difference polynomial
`δ(X) = φ(X) - y - ψ(X)·(X - z)` of its output, samples an index `i` and, when the `i`-th root
`r` of `δ` exists, answers `(0, g₁^(1/r))` (or `(1, g₁)` at `r = 0`).

`ks_to_tSDH.tree` is the computation tree of the reduction, generic in the output type of the
adversary, with the adversary a tree-valued binder and the three non-elementary steps binders
of the tree: `diffPoly` (polynomial arithmetic on the representations), `rootList` (the roots
of a polynomial as a list; `Polynomial.roots` has no algorithm in Mathlib) and `invExp`
(`r ↦ g₁^(1/r)`, an inversion in the field and an exponentiation in `G₁`). The zero test
`r = 0` is decided by a `[DecidableEq (ZMod P.p)]` binder. `ks_to_tSDH.compile_tree`
instantiates the binders at the operations of `ks_to_tSDH`; the costed form
`ks_to_tSDH.tree.timed` and its erasure theorem come from `derive_timed`. A reduction that runs
the same root guess on another adversary output has this tree at its own output type and
difference polynomial.

## Cost model

The cost rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per node and per call, the
registered list costs of `CatCryptCore.Tactics.StdCosts`. The costed form has a cost companion
for each binder: the adversary has time at most `T` and call cost at most `a`, `diffPolyCost`
at most `d`, `rootListCost` at most `ρ` and `invExpCost` at most `e`. The read of the `i`-th
root costs at most `2 i + 1 ≤ 2 t + 1` (`List.get?Internal.timedCost_le_index`).

## Main results

* `ks_to_tSDH.tree`, `ks_to_tSDH.diffPoly` — the computation tree and the difference polynomial
* `ks_to_tSDH.compile_tree` — the tree compiles to `ks_to_tSDH`
* `ks_to_tSDH.tree.timed`, `ks_to_tSDH.tree.erase_timed` — the costed form and its erasure
* `ks_to_tSDH.compile_erase_timed` — the erased costed form compiles to `ks_to_tSDH A`
* `ks_to_tSDH.tree.timeBound_timed` — time at most `T + a + d + ρ + e + 2 t + 10`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.Commitments.KZG

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.PairingGroup
open Polynomial

variable (P : PairingGroup) (t : ℕ)

/-- The computation tree of `ks_to_tSDH`, with the adversary `A`, the difference polynomial
`diffPoly`, the list of roots `rootList` and the map `invExp : r ↦ g₁^(1/r)` as binders. -/
noncomputable def ks_to_tSDH.tree [DecidableEq (ZMod P.p)] {O : Type}
    (A : (Fin (t + 1) → P.G₁) → SPTree O) (diffPoly : O → Polynomial (ZMod P.p))
    (rootList : Polynomial (ZMod P.p) → List (ZMod P.p))
    (invExp : ZMod P.p → P.G₁) (pk : Fin (t + 1) → P.G₁) : SPTree (ZMod P.p × P.G₁) :=
  (A pk).bind fun out =>
    let δ := diffPoly out
    .sample (Fin (t + 1)) inferInstance inferInstance fun i =>
      match (rootList δ)[i.val]? with
      | some r => if r = 0 then .ret (1, P.g₁) else .ret (0, invExp r)
      | none => .ret (0, 1)

/-- The difference polynomial `φ(X) - y - ψ(X)·(X - z)` of an output of the adversary. -/
noncomputable def ks_to_tSDH.diffPoly
    (out : AGMRepr P t × ZMod P.p × ZMod P.p × AGMRepr P t) : Polynomial (ZMod P.p) :=
  out.1.toPoly - C out.2.2.1 - out.2.2.2.toPoly * (X - C out.2.1)

/-- The tree `ks_to_tSDH.tree` compiles to `ks_to_tSDH`. -/
theorem ks_to_tSDH.compile_tree [DecidableEq (ZMod P.p)] (A : AGMAdversary P t)
    (A' : (Fin (t + 1) → P.G₁) → SPTree (AGMRepr P t × ZMod P.p × ZMod P.p × AGMRepr P t))
    (hA : ∀ pk, (A' pk).compile = A.run pk) (pk : Fin (t + 1) → P.G₁) :
    (ks_to_tSDH.tree P t A' (ks_to_tSDH.diffPoly P t) (fun δ => δ.roots.toList)
      (fun r => P.g₁ ^ᵍ r⁻¹) pk).compile = ks_to_tSDH P t A pk := by
  simp only [ks_to_tSDH.tree, ks_to_tSDH, ks_to_tSDH.diffPoly, SPTree.compile_bind, hA]
  grind [SPTree.compile]

derive_timed ks_to_tSDH.tree

/-- The erased costed form, at the operations of `ks_to_tSDH`, compiles to `ks_to_tSDH A`
when the costed adversary `A'` erases and compiles to `A.run`. -/
theorem ks_to_tSDH.compile_erase_timed [DecidableEq (ZMod P.p)] (A : AGMAdversary P t)
    (A' : (Fin (t + 1) → P.G₁) →
      SPTree.Timed (AGMRepr P t × ZMod P.p × ZMod P.p × AGMRepr P t))
    (ACost : (Fin (t + 1) → P.G₁) → ℕ) (hA : ∀ pk, (A' pk).erase.compile = A.run pk)
    (diffPolyCost : AGMRepr P t × ZMod P.p × ZMod P.p × AGMRepr P t → ℕ)
    (rootListCost : Polynomial (ZMod P.p) → ℕ) (invExpCost : ZMod P.p → ℕ)
    (pk : Fin (t + 1) → P.G₁) (pkCost : Fin (t + 1) → ℕ) :
    (ks_to_tSDH.tree.timed P t A' ACost (ks_to_tSDH.diffPoly P t) diffPolyCost
      (fun δ => δ.roots.toList) rootListCost (fun r => P.g₁ ^ᵍ r⁻¹) invExpCost pk
      pkCost).2.erase.compile = ks_to_tSDH P t A pk := by
  rw [ks_to_tSDH.tree.erase_timed]
  exact ks_to_tSDH.compile_tree P t A _ hA pk

/-- **Time of the knowledge-soundness reduction.** One call of the adversary (time `T`, call
cost `a`), one difference polynomial (`d`), one root list (`ρ`), the read of one root
(`2 t + 1`), one zero test and at most one inversion with exponentiation (`e`). -/
theorem ks_to_tSDH.tree.timeBound_timed [DecidableEq (ZMod P.p)] {O : Type}
    (A : (Fin (t + 1) → P.G₁) → SPTree.Timed O) (ACost : (Fin (t + 1) → P.G₁) → ℕ)
    (diffPoly : O → Polynomial (ZMod P.p)) (diffPolyCost : O → ℕ)
    (rootList : Polynomial (ZMod P.p) → List (ZMod P.p)) (rootListCost : Polynomial (ZMod P.p) → ℕ)
    (invExp : ZMod P.p → P.G₁) (invExpCost : ZMod P.p → ℕ)
    (pk : Fin (t + 1) → P.G₁) (pkCost : Fin (t + 1) → ℕ) {T a d ρ e : ℕ}
    (hA : ∀ pk, (A pk).time ≤ T) (hAC : ∀ pk, ACost pk ≤ a)
    (hd : ∀ out, diffPolyCost out ≤ d) (hρ : ∀ δ, rootListCost δ ≤ ρ)
    (he : ∀ r, invExpCost r ≤ e) :
    SPTree.Timed.stepTime (ks_to_tSDH.tree.timed P t A ACost diffPoly diffPolyCost rootList
      rootListCost invExp invExpCost pk pkCost) ≤ T + a + d + ρ + e + 2 * t + 10 := by
  have hg : ∀ (l : List (ZMod P.p)) (i : Fin (t + 1)),
      List.get?Internal.timedCost l i ≤ 2 * t + 1 := fun l i => by
    have := List.get?Internal.timedCost_le_index l i
    omega
  rw [ks_to_tSDH.tree.timed, SPTree.Timed.stepTime_delay]
  refine Nat.le_trans (Nat.add_le_add_left (SPTree.Timed.stepTime_bind_le (A pk) _
    (d + ρ + e + 2 * t + 9) fun out => ?_) _) ?_
  · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_sample]
    refine le_trans (Nat.add_le_add (Nat.add_le_add_left (hd _) 1)
      (Nat.add_le_add_left (Finset.sup_le (a := ρ + e + 2 * t + 7) fun i _ => ?_) 1)) (by omega)
    generalize diffPoly _ = δ
    have h1 := hg (rootList δ) i
    have h2 := hρ δ
    split
    · split <;> (simp only [SPTree.Timed.delay, SPTree.Timed.time_ret]; have := he ‹_›; omega)
    · simp only [SPTree.Timed.time_ret]
      omega
  · have := hA pk
    have := hAC pk
    omega

end CatCrypt.Examples.Commitments.KZG
