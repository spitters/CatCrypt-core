/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SaltedAEAD
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.AutoTime.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the salted-AEAD reductions

Costed forms of the reductions `saltedPRFRed` and `saltedAEADRed` of
`CatCryptCore.Crypto.Messaging.SaltedAEAD`, by `derive_reduction`, with their erasure theorems
`saltedPRFRed.erase_timed` and `saltedAEADRed.erase_timed`.

## Cost model

The cost rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per `rand` and per `query` node,
the costs `encryptCost` and `decryptCost` of encryption and decryption of `D` as companions.

## Main results

* `saltedKeyImpl.stepTimeBound_timed` — one simulated query of `saltedPRFRed` takes time at most
  `a + 9` for encryption and decryption of cost at most `a`
* `saltedPRFRed.timeBound_timed` — an adversary of time `T` with at most `q` queries gives a
  reduction of time at most `T + q (a + 8)`

No module imports this file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging

derive_reduction saltedPRFRed

derive_reduction saltedAEADRed

/-- One simulated query of `saltedPRFRed` takes time at most `a + 9` when encryption and
decryption of `D` cost at most `a`. -/
theorem saltedKeyImpl.stepTimeBound_timed {W : Type} [SampleableType W] {C AD S : Type}
    (D : Assumptions.AEADDef W C AD) (encryptCost : W → W → AD → ℕ)
    (decryptCost : W → C → AD → ℕ) {a : ℕ} (he : ∀ k pt ad, encryptCost k pt ad ≤ a)
    (hd : ∀ k ct ad, decryptCost k ct ad ≤ a) (u : Unit)
    (q : Assumptions.AEAD_CCA_Query W C (S × AD)) :
    OracleAdv.Timed.StepTimeBound
      (OracleAdv.Timed.delay 1 (saltedKeyImpl.timed D u q encryptCost decryptCost))
      ((a + 8) + 1) := by
  rcases q with ⟨pt, s, ad⟩ | ⟨ct, s, ad⟩
  · refine ⟨by simp [saltedKeyImpl.timed, OracleAdv.Timed.delay], ?_⟩
    simp only [saltedKeyImpl.timed, OracleAdv.Timed.delay, queryUnsalt]
    time_bound
  · refine ⟨by simp [saltedKeyImpl.timed, OracleAdv.Timed.delay], ?_⟩
    simp only [saltedKeyImpl.timed, OracleAdv.Timed.delay, queryUnsalt]
    time_bound

/-- **Time of the dual-PRF reduction.** An adversary of time `T` with at most `q` queries, and
encryption and decryption of `D` of cost at most `a`, give a reduction of time at most
`T + q (a + 8)`. -/
theorem saltedPRFRed.timeBound_timed {W : Type} [SampleableType W] {C AD S : Type}
    (D : Assumptions.AEADDef W C AD)
    {A' : OracleAdv.Timed (Assumptions.AEAD_CCA_Query W C (S × AD))
      (Assumptions.AEAD_CCA_Answer W C) Bool}
    (encryptCost : W → W → AD → ℕ) (decryptCost : W → C → AD → ℕ) {a T q : ℕ}
    (he : ∀ k pt ad, encryptCost k pt ad ≤ a) (hd : ∀ k ct ad, decryptCost k ct ad ≤ a)
    (hT : A'.TimeBound T) (hq : A'.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (saltedPRFRed.timed D A' encryptCost decryptCost)
      (T + q * (a + 8)) := by
  have h := Constructions.SIVNonce.timeBound_simulate_succ
    (fun u q => OracleAdv.Timed.delay 1 (saltedKeyImpl.timed D u q encryptCost decryptCost))
    (fun u q => saltedKeyImpl.stepTimeBound_timed D encryptCost decryptCost he hd u q) hT hq ()
  have h' := OracleAdv.Timed.stepTimeBound_delay
    (c := (OracleAdv.Timed.simulate (fun u q => OracleAdv.Timed.delay 1
      (saltedKeyImpl.timed D u q encryptCost decryptCost)) A' ()).1)
    (OracleAdv.Timed.timeBound_bind (n := 0) (f := fun y => (0, .ret y.1)) h.2
      fun _ => ⟨le_rfl, trivial⟩)
  exact h'.mono (by have := h.1; omega)

end CatCrypt.Crypto.Messaging
