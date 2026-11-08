/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareJoint
public import CatCryptCore.Crypto.AKE.X3DHSquareSignedTimed
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Running time of the simulator of X3DH with a joint identity and signing key

`derive_simulator x3dhJointSim` defines the costed form `x3dhJointSim.timed` of the layer
`sigLayerJ` over the X3DH simulator, with the costed steps of the one-call layer `sigLayerJH` as
binders, and proves its erasure and its graded time theorem from those of `x3dhSim`. At the
steps `jPreT` and `jPostT`, each the distribution of `jPre` or `jPost` as one sampling node
(`pmfT`), of step cost `tl`, the costed simulator erases to `x3dhJointSim G`
(`x3dhJointSim_erases_layer`), and after `i` activations an activation costs at most
`tl + 2 + 200 + 20 tc + 20 te + 20 tf + 40 i` (`x3dhJointSim_timeBoundGraded_layer`). The step
cost `tl` of the layer is the cost of its decisions, of a lookup in the Fiat–Shamir table of one
party and of a simulated signature (`FiatShamirROM.simStep`).

No module imports this file.

## Main results

* `x3dhJointSim.timed`, `x3dhJointSim.erase_timed`, `x3dhJointSim.timeBoundGraded_timed`
  (derived): the costed simulator, its erasure and its graded time.
* `x3dhJointSim_erases_layer`, `x3dhJointSim_timeBoundGraded_layer`: the costed simulator at
  the costed steps of the layer erases to `x3dhJointSim` and its graded time bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.FiatShamirROM CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.AKE.X3DHSquareSigned (pmfT pmfT_erase pmfT_time)

derive_simulator x3dhJointSim

section Simulator

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt] {K : Type}

/-- The costed `pre` step of the joint signature layer: the distribution of `jPre` as one
sampling node. -/
noncomputable def jPreT (l : JSt P) (e : JEv P) : SPTree.Timed (JSt P × OEv P.Stmt) :=
  pmfT (jPre P l e)

/-- The costed `post` step of the joint signature layer: the distribution of `jPost` as one
sampling node. -/
noncomputable def jPostT (l : JSt P) (o : OOut P.Wit P.Stmt K) :
    SPTree.Timed (JSt P × JOut P K) :=
  pmfT (jPost P l o)

variable {S W : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K]

/-- **Erasure of the costed simulator of X3DH with a joint key**: the derived costed form
`x3dhJointSim.timed` at the costed steps `jPreT`, `jPostT` of the layer, each of step cost `tl`,
erases to `x3dhJointSim G`. -/
theorem x3dhJointSim_erases_layer (G : DHGroup S W) (tl : ℕ) (coeCost : S ≃ W → S → ℕ)
    (expCost : W → S → ℕ) (toFunCost : S → ℕ) :
    (x3dhJointSim.timed (K := K) G (jPreT _) (fun _ _ => tl) (jPostT _) (fun _ _ => tl)
      coeCost expCost toFunCost).Erases (x3dhJointSim G) :=
  x3dhJointSim.erase_timed G _ _ _ _ coeCost expCost toFunCost
    (fun _ _ => pmfT_erase _) (fun _ _ => pmfT_erase _)

/-- **Graded running time of the costed simulator of X3DH with a joint key.** At the costed
steps `jPreT`, `jPostT` of the layer, of step cost `tl`, and group operations of costs at most
`tc`, `te`, `tf`, after `i` activations every activation costs at most
`tl + 2 + 200 + 20 tc + 20 te + 20 tf + 40 i`: the layer adds a constant to each step, and the
X3DH simulator below grows by `40` per activation with its key-derivation table and its
notices. -/
theorem x3dhJointSim_timeBoundGraded_layer (G : DHGroup S W) (tl : ℕ)
    (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ) (toFunCost : S → ℕ) {tc te tf : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf) :
    (x3dhJointSim.timed (K := K) G (jPreT _) (fun _ _ => tl) (jPostT _) (fun _ _ => tl)
      coeCost expCost toFunCost).TimeBoundGraded
      (tl + 2 + (200 + 20 * tc + 20 * te + 20 * tf)) 40 := by
  have h := x3dhJointSim.timeBoundGraded_timed (K := K) G (jPreT _) (fun _ _ => tl)
    (jPostT _) (fun _ _ => tl) coeCost expCost toFunCost (T_pre := 1) (T_post := 1)
    (fun _ _ => by simp [jPreT]) (fun _ _ => le_rfl) (fun _ _ => by simp [jPostT])
    (fun _ _ => le_rfl) hc he hf
  simpa [Nat.add_assoc] using h

end Simulator

end CatCrypt.Crypto.AKE.X3DHSquare
