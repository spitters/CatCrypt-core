/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Anon.Signalling
public import CatCryptCore.Crypto.ROProgramming
public import CatCryptCore.Crypto.UCConcrete

/-!
# Anonymity of anonymous signalling as a game pair

The anonymity game of the construct of `Anon.Signalling` as a game pair `anonUCReal`,
`anonUCIdeal` indexed by the adversary's choice stage, whose output is the adversary's view
(hash key, choice, group root, nullifier, proof). The advantage of a distinguisher `D` on the
pair is the anonymity advantage of the guess stage `guessOf D` that runs `D` on the view
(`anonUC_advantage_eq`), so `anonAdvantage_le` bounds it by `anonUCBound`, the statistical
zero-knowledge error plus the PRF advantage of `prfRed` (instance `anonUCGameAdvBoundC`).
`UCFromGameC` turns the instance into a concrete UC emulation.

## Main definitions

* `outBool` — the output bit of a Boolean computation run from the empty heap
* `AnonView`, `guessOf` — the adversary's view and the guess stage of a distinguisher
* `anonViewReal`, `anonViewIdeal`, `anonUCReal`, `anonUCIdeal` — the game pair
* `anonUCBound` — the bound of `anonAdvantage_le` at `guessOf D`

## Main results

* `prTrue_liftPMF_bind` — a lifted distribution followed by a distinguisher
* `anonUC_advantage_eq` — the pair's advantage is `anonAdvantage` at `guessOf D`
* `anonUCGameAdvBoundC` — the concrete game bound of the pair
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Anon.Signalling

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.PRPPRF CatCrypt.Crypto.Signatures
open CatCrypt.Crypto.ROProgramming (liftPMF_isPure)
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCDSL
open scoped ENNReal

/-! ## The output bit of a distinguisher -/

/-- The output bit of `Dist a` run from the empty heap, `false` on failure. -/
noncomputable def outBool {α : Type} (Dist : α → SPComp Bool) (a : α) : PMF Bool :=
  (Dist a Heap.empty).map fun r => match r with | some (b, _) => b | none => false

theorem outBool_apply_true {α : Type} (Dist : α → SPComp Bool) (a : α) :
    outBool Dist a true = prTrue (Dist a) Heap.empty := by
  unfold outBool prTrue
  rw [PMF.map_apply]
  have hsupp : Function.support (fun r : Option (Bool × Heap) =>
      if true = (match r with | some (b, _) => b | none => false) then (Dist a Heap.empty) r
      else 0) ⊆ Set.range (fun h : Heap => some (true, h)) := by
    intro r hr
    rcases r with _ | ⟨b, h⟩
    · simp_all
    · cases b
      · simp_all
      · simp_all
  symm
  convert (Function.Injective.tsum_eq (fun h₁ h₂ e => by simpa using e) hsupp) using 1
  · simp
  · simp_all

/-- A lifted distribution followed by a distinguisher, from the empty heap, outputs `true`
with the probability that the output bit of the distinguisher on a sample is `true`. -/
theorem prTrue_liftPMF_bind {α : Type} (p : PMF α) (Dist : α → SPComp Bool) :
    prTrue ((liftPMF p).bind Dist) Heap.empty = (p.bind (outBool Dist)) true := by
  rw [prTrue_bind_eq_weighted, PMF.bind_apply]
  simp only [liftPMF, PMF.map_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (some (a, Heap.empty)) fun o ho => by simp [ho]]
  simp [outBool_apply_true]

/-! ## Anonymity as a game pair -/

section AnonUC

variable {H : HashScheme} {K E N M Pf Root Path PK SK Sig : Type}

/-- The view of the anonymity adversary: the hash key, its choice, the group root, the
nullifier and the proof. -/
abbrev AnonView (H : HashScheme) (E N M Pf Root : Type) : Type :=
  H.Key × Choice N E M × Root × N × Pf

/-- The guess stage that runs the distinguisher `D` on the view, from the empty heap. -/
noncomputable def guessOf (D : AnonView H E N M Pf Root → SPComp Bool) :
    H.Key → Choice N E M → Root → N → Pf → PMF Bool :=
  fun hk c r nf π => outBool D (hk, c, r, nf, π)

variable [Fintype K] [Nonempty K] [Fintype N] [Nonempty N]

/-- The view in the real anonymity game of `S` for the choice stage `choose`. -/
noncomputable def anonViewReal (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (choose : H.Key → PMF (Choice N E M)) : PMF (AnonView H E N M Pf Root) :=
  (anonPre choose).bind fun t => (S.prove (S.stmtOf t) (S.witOf t)).map fun π =>
    (t.2.1, t.2.2, (S.stmtOf t).1, (S.stmtOf t).2.2.1, π)

/-- The view in the ideal anonymity game of `S`: a uniform commitment, a uniform nullifier and
a simulated proof. -/
noncomputable def anonViewIdeal (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (choose : H.Key → PMF (Choice N E M)) : PMF (AnonView H E N M Pf Root) :=
  (PMF.uniformOfFintype H.Key).bind fun hk => (choose hk).bind fun c =>
    (PMF.uniformOfFintype N).bind fun cm => (PMF.uniformOfFintype N).bind fun nf =>
      (S.sim (S.acc.root hk (c.group cm), c.scope, nf, c.msg)).map fun π =>
        (hk, c, S.acc.root hk (c.group cm), nf, π)

/-- The real anonymity game of `S`, indexed by the choice stage. -/
noncomputable def anonUCReal (S : Scheme H K E N M Pf Root Path PK SK Sig) :
    (H.Key → PMF (Choice N E M)) → SPComp (AnonView H E N M Pf Root) :=
  fun choose => liftPMF (anonViewReal S choose)

/-- The ideal anonymity game of `S`, indexed by the choice stage. -/
noncomputable def anonUCIdeal (S : Scheme H K E N M Pf Root Path PK SK Sig) :
    (H.Key → PMF (Choice N E M)) → SPComp (AnonView H E N M Pf Root) :=
  fun choose => liftPMF (anonViewIdeal S choose)

instance anonUCReal_pureGame (S : Scheme H K E N M Pf Root Path PK SK Sig) :
    PureGame (anonUCReal S) :=
  ⟨fun _ => liftPMF_isPure _⟩

instance anonUCIdeal_pureGame (S : Scheme H K E N M Pf Root Path PK SK Sig) :
    PureGame (anonUCIdeal S) :=
  ⟨fun _ => liftPMF_isPure _⟩

/-- The advantage of `D` on the game pair at `choose` is the anonymity advantage of the
stages `choose`, `guessOf D`. -/
theorem anonUC_advantage_eq (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (choose : H.Key → PMF (Choice N E M)) (D : AnonView H E N M Pf Root → SPComp Bool) :
    AdvantageA (anonUCReal S choose) (anonUCIdeal S choose) D =
      anonAdvantage S choose (guessOf D) := by
  have hg : ∀ p : PMF Bool, prTrue (pmfGame p) Heap.empty = p true :=
    fun p => prTrue_liftPMF p Heap.empty
  unfold AdvantageA anonAdvantage Advantage anonUCReal anonUCIdeal
  simp only [prTrue_liftPMF_bind, hg]
  simp only [anonViewReal, anonViewIdeal, anonReal, anonIdeal, guessOf, PMF.bind_bind,
    PMF.bind_map, Function.comp_def]
  rfl

/-- The anonymity bound of `S` at the choice stage `choose` and the distinguisher `D`: the
statistical zero-knowledge error plus the PRF advantage of `prfRed` for the guess stage
`guessOf D`. -/
noncomputable def anonUCBound [DecidableEq E] (S : Scheme H K E N M Pf Root Path PK SK Sig) :
    (H.Key → PMF (Choice N E M)) → (AnonView H E N M Pf Root → SPComp Bool) → ℝ≥0∞ :=
  fun choose D => zkError S + PRF_q_Advantage S.prf (prfRed S.groupRoot S.sim choose (guessOf D))

/-- Every distinguisher's advantage on the anonymity game pair of `S` is at most
`anonUCBound S`, from `anonAdvantage_le`. -/
instance anonUCGameAdvBoundC [DecidableEq E] [DecidableEq N]
    (S : Scheme H K E N M Pf Root Path PK SK Sig) :
    GameAdvBoundC (anonUCReal S) (anonUCIdeal S) (anonUCBound S) :=
  ⟨fun choose D => (anonUC_advantage_eq S choose D).trans_le (anonAdvantage_le S choose _)⟩

end AnonUC

end CatCrypt.Crypto.Anon.Signalling
