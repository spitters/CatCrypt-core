/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirGeneric.SchnorrInstance
public import CatCryptCore.Crypto.FiatShamirROM.Timed

/-!
# EUF-CMA security of Schnorr signatures in the random-oracle model: the reduction

The discrete-logarithm reduction `dlReduction A` for an EUF-CMA adversary `A`
against Schnorr signatures in the random-oracle model is the witness-finding
reduction of the generic Fiat–Shamir theorem (`FiatShamirROM.extractReduction`)
at the Schnorr Σ-protocol (`FiatShamirROM.schnorrSigma`), read as a
discrete-logarithm adversary (`FiatShamirROM.dlOfWitness`). On the challenge
`pk` it runs the simulated EUF-CMA game (signing queries answered from `pk` by
programming the random oracle) as a forking run: at every fresh random-oracle
value `e₁` it continues the run, and when the forgery `(m, (a, z₁))` verifies
against that value, it runs the rest of the game again from the same state with
a fresh value `e₂`, obtaining a second forgery `(m, (a, z₂))` at the same point.
It outputs `(z₁ − z₂)/(e₁ − e₂)`.

The reduction runs `A` at most twice, answers its queries with the simulated
oracle, and performs a subtraction and a division in the scalar field.

## Main definitions

* `dlReduction A` — the discrete-logarithm adversary
* `dlReduction.timed` — its costed form, `FiatShamirROM.extractReduction.timed` at
  `schnorrSigma gp`

## Main results

* `schnorr_rom_eufcma` — for every adversary with at most `qH` hash and `qS`
  signing queries,
  `ε'·(ε'/(qH + 1) − 1/|Scalar|) ≤ DL_Advantage (dlReduction A)` with
  `ε' = eufcmaAdvantage A − qS·(qH + 1 + qS)/|Scalar|`; it is the generic
  Fiat–Shamir theorem `FiatShamirROM.fiatShamir_rom_eufcma` at `schnorrSigma`
  through the equality of the two EUF-CMA advantages
  (`FiatShamirROM.eufcmaAdvantage_toGeneric`)
* `dlReduction.run_erase_timed`, `dlReduction.timeBound_timed` — the costed form erases to
  `dlReduction A`, and with the adversary of time `T` it has time at most
  `2 * (T + (2 * tV + 1) + ((tH + tF + 1) * (qH + 1) + (tS + 1) * qS)) + tExt`

## References

* D. Pointcheval, J. Stern, *Security arguments for digital signatures and blind
  signatures*, J. Cryptology 13(3), 2000.
* M. Bellare, G. Neven, *Multi-signatures in the plain public-key model and a
  general forking lemma*, CCS 2006.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SchnorrROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Examples.Schnorr
open scoped ENNReal

variable {gp : GroupParam} {M : Type} [DecidableEq M] {qH qS : ℕ}

/-- **The discrete-logarithm reduction.** On the challenge `pk`, run the
simulated EUF-CMA game as a forking run and output `(z₁ − z₂)/(e₁ − e₂)` from the
two forgeries and the two random-oracle values at the fork point: the generic
Fiat–Shamir reduction at `schnorrSigma gp`. -/
noncomputable def dlReduction (A : Adversary gp M qH qS) : gp.G → SPComp gp.Scalar :=
  FiatShamirROM.dlOfWitness gp (FiatShamirROM.extractReduction (FiatShamirROM.toGeneric A))

/-- **EUF-CMA security of Schnorr signatures in the random-oracle model.** For
every adversary `A` making at most `qH` hash queries and `qS` signing queries, with
`ε' = eufcmaAdvantage A − qS·(qH + 1 + qS)/|Scalar|`,

`ε'·(ε'/(qH + 1) − 1/|Scalar|) ≤ DL_Advantage (dlReduction A)`,

where `dlReduction A` runs `A` at most twice. The loss `qS·(qH + 1 + qS)/|Scalar|`
is the signing simulation, the rest the forking bound; both are those of the
generic Fiat–Shamir theorem at `schnorrSigma gp`. -/
theorem schnorr_rom_eufcma (A : Adversary gp M qH qS) :
    (eufcmaAdvantage A - ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) / Fintype.card gp.Scalar) *
        ((eufcmaAdvantage A - ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) / Fintype.card gp.Scalar) /
            ((qH + 1 : ℕ) : ℝ≥0∞) - 1 / Fintype.card gp.Scalar) ≤
      DL_Advantage gp (dlReduction A) :=
  FiatShamirROM.schnorr_rom_eufcma_of_generic A

/-! ## The costed reduction -/

/-- The costed discrete-logarithm reduction on the challenge `pk`: the costed rewinding
reduction `FiatShamirROM.extractReduction.timed` at `schnorrSigma gp` for the costed
adversary `A'`, with the verifier's query at the cost companion `vkeyCost` of the verifier
point, step cost `tH` per hash query, `tS` per signing query, `tF` for the fork decision and
`tExt` for the extractor. -/
noncomputable def dlReduction.timed (vkeyCost :
    ((FiatShamirROM.schnorrSigma gp).toProtocol M).VkeyCost)
    (tH tS tF tExt : ℕ)
    (A' : gp.G → OracleAdv.Timed (FiatShamirROM.Query (FiatShamirROM.schnorrSigma gp) M)
      (FiatShamirROM.Answer (FiatShamirROM.schnorrSigma gp))
      (FiatShamirROM.Forgery (FiatShamirROM.schnorrSigma gp) M))
    (pk : gp.G) : ℕ × OracleAdv.Timed Empty Empty gp.Scalar :=
  FiatShamirROM.extractReduction.timed (P := FiatShamirROM.schnorrSigma gp) vkeyCost tH tS tF
    tExt A' pk

/-- Under any oracle, the erased costed reduction, read as a discrete-logarithm adversary
by `dlOfWitness`, is `dlReduction A`, for a costed adversary `A'` whose erasure is the
generic adversary `toGeneric A`. -/
theorem dlReduction.run_erase_timed (A : Adversary gp M qH qS)
    (A' : gp.G → OracleAdv.Timed (FiatShamirROM.Query (FiatShamirROM.schnorrSigma gp) M)
      (FiatShamirROM.Answer (FiatShamirROM.schnorrSigma gp))
      (FiatShamirROM.Forgery (FiatShamirROM.schnorrSigma gp) M))
    (hA : ∀ x, (A' x).erase = (FiatShamirROM.toGeneric A).run x)
    (vkeyCost : ((FiatShamirROM.schnorrSigma gp).toProtocol M).VkeyCost) (tH tS tF tExt : ℕ)
    {U : Type} (O' : U → Empty → PMF (Empty × U)) (u : U) :
    FiatShamirROM.dlOfWitness gp (fun pk =>
      (OracleAdv.run O' (dlReduction.timed vkeyCost tH tS tF tExt A' pk).2.erase u).map
        Prod.fst) =
      dlReduction A := by
  unfold dlReduction
  congr 1
  funext pk
  exact FiatShamirROM.extractReduction.run_erase_timed (FiatShamirROM.toGeneric A) A' hA
    vkeyCost tH tS tF tExt O' u pk

/-- **Time of the discrete-logarithm reduction.** With the costed adversary `A'` of time
`T` on every challenge and `tV` a bound of the derived verifier step
(`FiatShamirROM.Protocol.VerifyCostLe`), the costed reduction has time at most
`2 * (T + (2 * tV + 1) + ((tH + tF + 1) * (qH + 1) + (tS + 1) * qS)) + tExt`: the adversary
with the verifier's query is run at most twice, each hash query is charged its step, its
node and the fork decision, each signing query its step and its node, and the extractor is
called once. -/
theorem dlReduction.timeBound_timed (A : Adversary gp M qH qS)
    {A' : gp.G → OracleAdv.Timed (FiatShamirROM.Query (FiatShamirROM.schnorrSigma gp) M)
      (FiatShamirROM.Answer (FiatShamirROM.schnorrSigma gp))
      (FiatShamirROM.Forgery (FiatShamirROM.schnorrSigma gp) M)}
    (hA : ∀ x, (A' x).erase = (FiatShamirROM.toGeneric A).run x)
    (vkeyCost : ((FiatShamirROM.schnorrSigma gp).toProtocol M).VkeyCost) (tV : ℕ)
    (hV : ((FiatShamirROM.schnorrSigma gp).toProtocol M).VerifyCostLe vkeyCost tV)
    (tH tS tF tExt : ℕ) {T : ℕ} (hT : ∀ x, (A' x).TimeBound T) (pk : gp.G) :
    OracleAdv.Timed.StepTimeBound (dlReduction.timed vkeyCost tH tS tF tExt A' pk)
      (2 * (T + (2 * tV + 1) + ((tH + tF + 1) * (qH + 1) + (tS + 1) * qS)) + tExt) := by
  have h := FiatShamirROM.extractReduction.timeBound_timed (FiatShamirROM.toGeneric A) hA
    vkeyCost tV hV tH tS tF tExt hT pk
  rw [FiatShamirROM.Sigma.toProtocol_V] at h
  exact h.mono (by omega)

end CatCrypt.Crypto.SchnorrROM
