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
# Time of the Sealed Sender reductions

The costed mirrors of the IND-CCA adversary (`INDCCAAdversary.Timed`) and of the
sender-anonymity adversary (`SenderAnonAdversary.Timed`, the result type of reductions that
build one), by `derive_timed_structure`, and the costed forms of `senderAnonReduction`,
`F_SealedSender.fixSenderReduction` and `F_SealedSender.viewReduction` (by
`derive_reduction`), with their erasure theorems and time bounds. Only time companion files
import this file.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per `rand` and `query` node and per
bookkeeping step; the recipient check `valid` is a data function with cost companion
`validCost`; the derived relabelling `OracleAdv.mapQueryAnswer.timed` charges a constant per
node of the adversary and the cost of `acceptAnswer` per answer.

## Main results

* `senderAnonReduction.timed`, `senderAnonReduction.erase_timed` — the costed reduction and its
  erasure
* `senderAnonReduction.timeBound_timed` — for stages of `A` of times `T₁`, `T₂` and call costs
  `a₁`, `a₂`, and `valid` of cost at most `v`, the two stages of the reduction take time at
  most `4 + a₁ + 4 T₁ + q₁ (v + 7)` and `3 + a₂ + 4 T₂ + q₂ (v + 7)`: linear in the time of
  `A`, with a constant per acceptance query
* `F_SealedSender.fixSenderReduction.timeBound_timed` — for stages of `A` of times `T₁`, `T₂`
  and call costs `a₁`, `a₂`: at most `1 + a₁ + T₁` and `1 + a₂ + T₂`
* `F_SealedSender.viewReduction.timeBound_timed` — for the distinguisher `D` of views of cost
  at most `d`: `0` and at most `2 + d`
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
`4 + a₁ + 4 * T₁ + q₁ * (v + 7)` and the second at most `3 + a₂ + 4 * T₂ + q₂ * (v + 7)`. -/
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
      (4 + a₁ + 4 * T₁ + q₁ * (v + 7)) (3 + a₂ + 4 * T₂ + q₂ * (v + 7)) := by
  have hq : 0 + (v + 4) + 3 = v + 7 := by omega
  refine ⟨fun pk => ?_, fun st c => ?_⟩
  · obtain ⟨H, hdef, hH⟩ : ∃ H : Option (Cert × Inner) → ℕ,
        senderAnonReduction.choose.tree.timed valid validCost A choose chooseCost guess
          guessCost pk =
          delay (2 + chooseCost pk +
            (OracleAdv.mapQueryAnswer.timed id (fun _ => 0) (acceptAnswer valid) H (choose pk)).1)
            ((OracleAdv.mapQueryAnswer.timed id (fun _ => 0) (acceptAnswer valid) H
              (choose pk)).2.bind fun x => (1, OracleAdv.Timed.ret (chalPair x))) ∧
        ∀ r, H r ≤ v + 4 :=
      ⟨_, rfl, fun r => by cases r with
        | none => simp
        | some x => have := hv x; simp only; omega⟩
    have hm := OracleAdv.mapQueryAnswer.timeBound_timed id (gCost := fun _ => 0)
      (acceptAnswer valid) (a := 0) (b := v + 4) (fun _ => le_rfl) hH (hc pk) (q := q₁)
      (by rw [hce pk]; exact A.isQueryBound₁ pk)
    rw [hq] at hm
    have hb := timeBound_bind (f := fun x => (1, OracleAdv.Timed.ret (chalPair x)))
      (n := 1) hm.2 fun _ => ⟨le_rfl, trivial⟩
    show StepTimeBound (senderAnonReduction.choose.tree.timed valid validCost A choose chooseCost
      guess guessCost pk) _
    rw [hdef]
    refine (stepTimeBound_delay hb).mono ?_
    have := hm.1
    have := hcc pk
    omega
  · obtain ⟨H, hdef, hH⟩ : ∃ H : Option (Cert × Inner) → ℕ,
        senderAnonReduction.guess.tree.timed valid validCost A choose chooseCost guess
          guessCost st c =
          delay (2 + guessCost st c)
            (OracleAdv.mapQueryAnswer.timed id (fun _ => 0) (acceptAnswer valid) H
              (guess st c)) ∧
        ∀ r, H r ≤ v + 4 :=
      ⟨_, rfl, fun r => by cases r with
        | none => simp
        | some x => have := hv x; simp only; omega⟩
    have hm := OracleAdv.mapQueryAnswer.timeBound_timed id (gCost := fun _ => 0)
      (acceptAnswer valid) (a := 0) (b := v + 4) (fun _ => le_rfl) hH (hg st c) (q := q₂)
      (by rw [hge st c]; exact A.isQueryBound₂ st c)
    rw [hq] at hm
    show StepTimeBound (senderAnonReduction.guess.tree.timed valid validCost A choose chooseCost
      guess guessCost st c) _
    rw [hdef]
    refine (stepTimeBound_delay hm).mono ?_
    have := hgc st c
    omega

end CatCrypt.Crypto.Messaging.SealedSender

namespace CatCrypt.Crypto.Signal.SealedSender.F_SealedSender

open CatCrypt.Crypto OracleAdv.Timed

derive_reduction fixSenderReduction

derive_reduction viewReduction

/-- **Time of `fixSenderReduction`.** For costed stages of times at most `T₁`, `T₂` and call
costs at most `a₁`, `a₂`, the stages of the costed reduction take time at most `1 + a₁ + T₁`
and `1 + a₂ + T₂`. -/
theorem fixSenderReduction.timeBound_timed {PK Cert Inner C : Type} (cert₀ : Cert) {q₁ q₂ : ℕ}
    (A : FAdversary PK Cert Inner C q₁ q₂)
    (choose : PK → OracleAdv.Timed C Bool (Cert × Inner × A.St)) (chooseCost : PK → ℕ)
    (guess : A.St → C → OracleAdv.Timed C Bool Bool) (guessCost : A.St → C → ℕ)
    {T₁ T₂ a₁ a₂ : ℕ} (hc : ∀ pk, (choose pk).TimeBound T₁)
    (hg : ∀ st c, (guess st c).TimeBound T₂) (hcc : ∀ pk, chooseCost pk ≤ a₁)
    (hgc : ∀ st c, guessCost st c ≤ a₂) :
    (fixSenderReduction.timed cert₀ A choose chooseCost guess guessCost).TimeBound
      (1 + a₁ + T₁) (1 + a₂ + T₂) := by
  refine ⟨fun pk => ?_, fun st c => ?_⟩
  · show StepTimeBound (fixSenderReduction.choose.tree.timed cert₀ A choose chooseCost guess
      guessCost pk) _
    rw [fixSenderReduction.choose.tree.timed]
    refine (stepTimeBound_delay (timeBound_bind
      (f := fun x => (0, OracleAdv.Timed.ret (x.1, cert₀, x.2.1, x.2.2))) (n := 0) (hc pk)
      fun _ => ⟨le_rfl, trivial⟩)).mono ?_
    have := hcc pk
    omega
  · show StepTimeBound (fixSenderReduction.guess.tree.timed cert₀ A choose chooseCost guess
      guessCost st c) _
    have := hgc st c
    exact ⟨by simp only [fixSenderReduction.guess.tree.timed]; omega,
      (hg st c).mono (by simp only [fixSenderReduction.guess.tree.timed]; omega)⟩

/-- **Time of `viewReduction`.** For a distinguisher of cost at most `d`, the first stage of
the costed reduction takes time `0` (it returns its choice) and the second at most `2 + d`. -/
theorem viewReduction.timeBound_timed {PK Cert Inner C : Type} (cert cert₀ : Cert) (m : Inner)
    (D : PK × C → PMF Bool) (DCost : PK × C → ℕ) {d : ℕ} (hD : ∀ x, DCost x ≤ d) :
    (viewReduction.timed cert cert₀ m D DCost).TimeBound 0 (2 + d) := by
  refine ⟨fun pk => ?_, fun pk c => ?_⟩
  · show StepTimeBound (viewReduction.choose.tree.timed cert cert₀ m D DCost pk) _
    simp only [viewReduction.choose.tree.timed, StepTimeBound]
    exact ⟨le_rfl, trivial⟩
  · show StepTimeBound (viewReduction.guess.tree.timed cert cert₀ m D DCost pk c) _
    have := hD (pk, c)
    simp only [viewReduction.guess.tree.timed, StepTimeBound, TimeBound]
    exact ⟨by omega, by omega, fun _ => ⟨by omega, trivial⟩⟩

end CatCrypt.Crypto.Signal.SealedSender.F_SealedSender
