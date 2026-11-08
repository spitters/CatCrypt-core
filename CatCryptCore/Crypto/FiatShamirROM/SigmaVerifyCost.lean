/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Timed

/-!
# The verifier step of a Fiat–Shamir signature over a Σ-protocol

The verifier point of the Fiat–Shamir signature `P.toProtocol M` over a Σ-protocol `P` is the
pair `(a, m)` of the commitment of the signature `(a, z)` and the message. Its cost companion is
derived by `derive_cost` from the field `vkey` of `P.toProtocol M`, it has a constant majorant in
the length of the list of values, and the bound `VerifyCostLe` of one verifier step follows by
`Protocol.verifyCostLe_of_costMajOn`. The time of the rewinding reduction
`extractReduction.timed` at the derived companion holds without a hypothesis on the verifier.

## Main results

* `Sigma.vkeyFn` — the verifier point of `P.toProtocol M`, and its derived cost
  `Sigma.vkeyFn.timedCost`
* `Sigma.vkeyFn_costMajOn` — a constant majorant of the derived cost
* `Sigma.verifyCostLe_vkeyFn` — `VerifyCostLe` at the derived cost
* `extractReduction.timeBound_timed_vkeyFn` — the time of the rewinding reduction at the
  derived cost

Search words: cost companion, verifier key, majorant, Fiat–Shamir, time certificate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Crypto

namespace Sigma

variable (P : Sigma) (M : Type) [DecidableEq M]

/-- The verifier point of the Fiat–Shamir signature `P.toProtocol M`: the field `vkey`. -/
def vkeyFn : (P.toProtocol M).Stmt → (P.toProtocol M).Msg → (P.toProtocol M).Sig →
    List (P.toProtocol M).Ch → (P.toProtocol M).Key :=
  (P.toProtocol M).vkey

derive_cost vkeyFn

/-- The derived cost of the verifier point has the majorant zero in the length of the list of
values: the pair `(a, m)` is a constructor applied to a projection and a variable. -/
theorem vkeyFn_costMajOn (x : (P.toProtocol M).Stmt) (m : (P.toProtocol M).Msg)
    (σ : (P.toProtocol M).Sig) :
    CostMajOn (P.toProtocol M).V List.length (fun _ => 0) (vkeyFn.timedCost P M x m σ) :=
  ⟨fun _ _ _ => le_rfl, fun _ _ => by grind [vkeyFn.timedCost]⟩

/-- One verifier step of `P.toProtocol M` at the derived cost of the verifier point costs at
most `8`: the append of the one value and the case analyses of the step. -/
theorem verifyCostLe_vkeyFn : (P.toProtocol M).VerifyCostLe (vkeyFn.timedCost P M) 8 := by
  simpa using (P.toProtocol M).verifyCostLe_of_costMajOn _ (vkeyFn_costMajOn P M)

end Sigma

section Rewinding

variable {P : Sigma} {M : Type} [DecidableEq M]

/-- **Time of the rewinding reduction at the derived verifier cost.** With `A'` of time `T` and
at most `qH` hash and `qS` signing queries, the costed relation reduction at the derived cost
`Sigma.vkeyFn.timedCost` of the verifier point has time at most
`2 * (T + 17 + ((tH + tF + 1) * (qH + 1) + (tS + 1) * qS)) + tExt`. -/
theorem extractReduction.timeBound_timed_vkeyFn {qH qS : ℕ} (A : Adversary P M qH qS)
    {A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M)}
    (hA : ∀ x, (A' x).erase = A.run x) (tH tS tF tExt : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (x : P.Stmt) :
    OracleAdv.Timed.StepTimeBound
      (extractReduction.timed (Sigma.vkeyFn.timedCost P M) tH tS tF tExt A' x)
      (2 * (T + 17 + ((tH + tF + 1) * (qH + 1) + (tS + 1) * qS)) + tExt) := by
  simpa using extractReduction.timeBound_timed A hA (Sigma.vkeyFn.timedCost P M) 8
    (Sigma.verifyCostLe_vkeyFn P M) tH tS tF tExt hT x

end Rewinding

end CatCrypt.Crypto.FiatShamirROM
