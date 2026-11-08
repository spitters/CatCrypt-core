/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.SealedSender.Anonymity
public import CatCryptCore.Crypto.Messaging.SealedSenderTimed
public import CatCryptCore.Crypto.ECH.Scheme
import CatCryptCore.Tactics.DeriveReduction

/-!
# Time of the Sealed Sender reduction to HPKE IND-CCA

The costed forms of `HPKE.BaseCCA.labelCCAReduction` and of `Anonymity.senderAnonReduction` (by
`derive_reduction`, over the costed mirrors `PKE.Games.ROMLabelCCAAdversary.Timed` of
`PKE.GamesTimed` and `HPKEAdversary.Timed` of `ECH.Scheme`), their erasure theorems and their
time bounds. No module imports this file.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per `rand` and `query` node and per
bookkeeping step; the recipient check `valid` is a data function with cost companion
`validCost`, priced in `Messaging.SealedSender.senderAnonROMReduction.timeBound_timed`.

## Main results

* `labelCCAReduction.timed`, `labelCCAReduction.erase_timed` — the costed HPKE adversary of a
  labelled IND-CCA adversary against `hpkePKE S` and its erasure
* `labelCCAReduction.timeBound_timed` — for costed stages whose steps take time at most `S₁`,
  `S₂`, the stages of the reduction take time at most `1 + S₁` and `1 + S₂`
* `senderAnonReduction.timed`, `senderAnonReduction.erase_timed` — the costed reduction and its
  erasure
* `senderAnonReduction.timeBound_timed` — for stages of `A` of times `T₁`, `T₂` and call costs
  `a₁`, `a₂`, and `valid` of cost at most `v`, the stages of the reduction take time at most
  `1 + (4 + a₁ + 4 T₁ + (qH + qD) (v + 12))` and `1 + (3 + a₂ + 4 T₂ + (qH + qD) (v + 12))`:
  linear in the time of `A`, with a constant per query
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.HPKE.BaseCCA

open CatCrypt.Crypto OracleAdv.Timed

derive_reduction labelCCAReduction

/-- **Time of `labelCCAReduction`.** For costed stages of `B` whose steps (call cost and tree)
take time at most `S₁` and `S₂`, the stages of the costed reduction take time at most `1 + S₁`
and `1 + S₂`. -/
theorem labelCCAReduction.timeBound_timed {PK C D H AD M CT : Type} {qH qD : ℕ}
    (B : PKE.Games.ROMLabelCCAAdversary PK AD M (C × AD × CT) D H qH qD qD)
    (choose : PK → OracleAdv.Timed (D ⊕ (C × AD × CT)) (H ⊕ Option M) (M × M × AD × B.St))
    (chooseCost : PK → ℕ)
    (guess : B.St → C × AD × CT → OracleAdv.Timed (D ⊕ (C × AD × CT)) (H ⊕ Option M) Bool)
    (guessCost : B.St → C × AD × CT → ℕ) {S₁ S₂ : ℕ}
    (hc : ∀ pk, StepTimeBound (chooseCost pk, choose pk) S₁)
    (hg : ∀ st c, StepTimeBound (guessCost st c, guess st c) S₂) :
    (labelCCAReduction.timed B choose chooseCost guess guessCost).TimeBound (1 + S₁) (1 + S₂) := by
  refine ⟨fun pk => ?_, fun st c => ?_⟩
  · show StepTimeBound (labelCCAReduction.choose.tree.timed B choose chooseCost guess
      guessCost pk) _
    rw [labelCCAReduction.choose.tree.timed]
    have hb := timeBound_bind
      (f := fun x => (0, OracleAdv.Timed.ret (x.1, x.2.1, x.2.2.1, x.2.2.1, x.2.2.2))) (n := 0)
      (hc pk).2 fun _ => ⟨le_rfl, trivial⟩
    refine (stepTimeBound_delay (c := 1 + chooseCost pk) hb).mono ?_
    have := (hc pk).1
    omega
  · show StepTimeBound (labelCCAReduction.guess.tree.timed B choose chooseCost guess
      guessCost st c) _
    have h := hg st.2 (c.1, st.1, c.2)
    have := h.1
    exact ⟨by simp only [labelCCAReduction.guess.tree.timed]; omega,
      h.2.mono (by simp only [labelCCAReduction.guess.tree.timed]; omega)⟩

end CatCrypt.Crypto.HPKE.BaseCCA

namespace CatCrypt.Crypto.Signal.SealedSender.Anonymity

open CatCrypt.Crypto OracleAdv.Timed Messaging.SealedSender

derive_reduction senderAnonReduction

/-- **Time of the Sealed Sender reduction to HPKE.** For costed stages `choose`, `guess`
erasing to the stages of `A`, of times at most `T₁`, `T₂` and call costs at most `a₁`, `a₂`, and
a recipient check of cost at most `v`, the costed reduction at the costed stages of
`senderAnonROMReduction.timed` of these stages takes time at most
`1 + (4 + a₁ + 4 * T₁ + (qH + qD) * (v + 12))` in its first stage and
`1 + (3 + a₂ + 4 * T₂ + (qH + qD) * (v + 12))` in its second: linear in the time of `A`, with a
constant per query. -/
theorem senderAnonReduction.timeBound_timed {PK C D H AD Cert Inner CT : Type}
    (valid : Cert × Inner → Bool) (validCost : Cert × Inner → ℕ) {qH qD : ℕ}
    (A : SenderAnonAdversary PK C D H AD Cert Inner CT qH qD)
    (choose : PK → OracleAdv.Timed (D ⊕ (C × AD × CT)) (H ⊕ Bool)
      (Cert × Cert × Inner × AD × A.St)) (chooseCost : PK → ℕ)
    (guess : A.St → C × AD × CT → OracleAdv.Timed (D ⊕ (C × AD × CT)) (H ⊕ Bool) Bool)
    (guessCost : A.St → C × AD × CT → ℕ) {T₁ T₂ a₁ a₂ v : ℕ}
    (hce : ∀ pk, (choose pk).erase = A.choose pk)
    (hge : ∀ st c, (guess st c).erase = A.guess st c)
    (hc : ∀ pk, (choose pk).TimeBound T₁) (hg : ∀ st c, (guess st c).TimeBound T₂)
    (hcc : ∀ pk, chooseCost pk ≤ a₁) (hgc : ∀ st c, guessCost st c ≤ a₂)
    (hv : ∀ x, validCost x ≤ v) :
    (senderAnonReduction.timed valid validCost A
        (senderAnonROMReduction.timed valid validCost A choose chooseCost guess guessCost).choose
        (senderAnonROMReduction.timed valid validCost A choose chooseCost guess
          guessCost).chooseCost
        (senderAnonROMReduction.timed valid validCost A choose chooseCost guess guessCost).guess
        (senderAnonROMReduction.timed valid validCost A choose chooseCost guess
          guessCost).guessCost).TimeBound
      (1 + (4 + a₁ + 4 * T₁ + (qH + qD) * (v + 12)))
      (1 + (3 + a₂ + 4 * T₂ + (qH + qD) * (v + 12))) :=
  have h := senderAnonROMReduction.timeBound_timed valid validCost A
    choose chooseCost guess guessCost hce hge hc hg hcc hgc hv
  HPKE.BaseCCA.labelCCAReduction.timeBound_timed _ _ _ _ _ h.1 h.2

end CatCrypt.Crypto.Signal.SealedSender.Anonymity
