/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SealedSender
public import CatCryptCore.Crypto.PKE.GamesTimed
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Time of the Sealed Sender reduction

The costed mirrors of the IND-CCA adversary (`INDCCAAdversary.Timed`) and of the
sender-anonymity adversary (`SenderAnonAdversary.Timed`, the result type of reductions that
build one), by `derive_timed_structure`, and the costed form of `senderAnonReduction` (by `derive_reduction`),
with its erasure theorem and its time bound. No module imports this file.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per `rand` and `query` node and per
bookkeeping step; the recipient check `valid` is a data function with cost companion
`validCost`; relabelling an answer costs `OracleAdv.mapQueryAnswer.timed` its registered unit
plus the cost of `acceptAnswer`.

## Main results

* `senderAnonReduction.timed`, `senderAnonReduction.erase_timed` — the costed reduction and its
  erasure
* `senderAnonReduction.timeBound_timed` — for stages of `A` of times `T₁`, `T₂` and call costs
  `a₁`, `a₂`, and `valid` of cost at most `v`, the two stages of the reduction take time at
  most `3 + a₁ + T₁ + q₁ (v + 6)` and `2 + a₂ + T₂ + q₂ (v + 6)`: the time of `A` plus a
  constant per acceptance query
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PKE.Games

derive_timed_structure INDCCAAdversary

end CatCrypt.Crypto.PKE.Games

namespace CatCrypt.Crypto.Messaging.SealedSender

open CatCrypt.Crypto.PKE.Games OracleAdv.Timed

derive_timed_structure SenderAnonAdversary

derive_reduction senderAnonReduction

/-- **Time of the Sealed Sender reduction.** For costed stages `choose`, `guess` erasing to the
stages of `A`, of times at most `T₁`, `T₂` and call costs at most `a₁`, `a₂`, and a recipient
check of cost at most `v`, the first stage of the costed reduction takes time at most
`3 + a₁ + T₁ + q₁ * (v + 6)` and the second at most `2 + a₂ + T₂ + q₂ * (v + 6)`. -/
theorem senderAnonReduction.timeBound_timed {PK Cert Inner C : Type}
    (valid : Cert × Inner → Bool) (validCost : Cert × Inner → ℕ) {q₁ q₂ : ℕ}
    (A : SenderAnonAdversary PK Cert Inner C q₁ q₂)
    (choose : PK → OracleAdv.Timed C Bool (Cert × Cert × Inner × A.St)) (chooseCost : PK → ℕ)
    (guess : A.St → C → OracleAdv.Timed C Bool Bool) (guessCost : A.St → C → ℕ)
    {T₁ T₂ a₁ a₂ v : ℕ}
    (hce : ∀ pk, (choose pk).erase = A.choose pk)
    (hge : ∀ st c, (guess st c).erase = A.guess st c)
    (hc : ∀ pk, (choose pk).TimeBound T₁) (hg : ∀ st c, (guess st c).TimeBound T₂)
    (hcc : ∀ pk, chooseCost pk ≤ a₁) (hgc : ∀ st c, guessCost st c ≤ a₂)
    (hv : ∀ x, validCost x ≤ v) :
    (senderAnonReduction.timed valid validCost A choose chooseCost guess guessCost).TimeBound
      (3 + a₁ + T₁ + q₁ * (v + 6)) (2 + a₂ + T₂ + q₂ * (v + 6)) := by
  have hq : (1 + 0) + (1 + (v + 4)) = v + 6 := by omega
  refine ⟨fun pk => ?_, fun st c => ?_⟩
  · show StepTimeBound (senderAnonReduction.choose.tree.timed valid validCost A choose chooseCost
      guess guessCost pk) _
    rw [senderAnonReduction.choose.tree.timed]
    refine (stepTimeBound_delay (timeBound_bind
      (f := fun x => (1, OracleAdv.Timed.ret (chalPair x))) (n := 1) (stepTimeBound_zero.1
      (OracleAdv.mapQueryAnswer.timeBound_timed id (acceptAnswer valid) (a := 0) (b := v + 4)
        (fun _ => le_rfl) ?_ (hc pk) (q := q₁) ?_)) fun _ => ⟨le_rfl, trivial⟩)).mono ?_
    · intro r
      cases r with
      | none => simp
      | some x => have := hv x; simp only; omega
    · rw [hce pk]; exact A.isQueryBound₁ pk
    · simp only [OracleAdv.mapQueryAnswer.timed]
      rw [hq]; have := hcc pk; omega
  · show StepTimeBound (senderAnonReduction.guess.tree.timed valid validCost A choose chooseCost
      guess guessCost st c) _
    refine (stepTimeBound_delay
      (OracleAdv.mapQueryAnswer.timeBound_timed id (acceptAnswer valid) (a := 0) (b := v + 4)
        (fun _ => le_rfl) ?_ (hg st c) (q := q₂) ?_)).mono ?_
    · intro r
      cases r with
      | none => simp
      | some x => have := hv x; simp only; omega
    · rw [hge st c]; exact A.isQueryBound₂ st c
    · rw [hq]; have := hgc st c; omega

end CatCrypt.Crypto.Messaging.SealedSender
