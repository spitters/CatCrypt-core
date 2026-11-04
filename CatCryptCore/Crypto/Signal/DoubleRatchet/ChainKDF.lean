/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.DoubleRatchet
public import CatCryptCore.Crypto.Constructions.NMACPRF
public import CatCryptCore.Crypto.PRGFromPRF

/-!
# The chain KDF of the Signal symmetric ratchet as a PRF

The symmetric ratchet of the Signal double ratchet derives from the chain key `CK` the message
key `MK = KDF(CK, c₁)` and the next chain key `CK' = KDF(CK, c₂)` at two distinct constant
inputs (Perrin–Marlinspike §5.2: HMAC with key `CK` on the bytes `0x01` and `0x02`). The
chain step is the two-point generator `PRGFromPRF.twoPointPRG kdf c₁ c₂`, so its PRG advantage
is the adaptive PRF advantage of `kdf` against a two-query reduction
(`PRGFromPRF.prg_advantage_twoPointPRG_le`).

The statements below are over the double ratchet of core `Messaging.DoubleRatchet` with the
Diffie–Hellman CKA over a cyclic group `G`, any root step `R`, the chain step
`twoPointPRG kdf c₁ c₂` and any core AEAD scheme `D`.

## Main definitions

* `epochChainBound kdf c₁ c₂ D term m X` — the FS-AEAD bound of one epoch with the chain step
  `twoPointPRG kdf c₁ c₂`, with the term `term` for each two-query reduction to the chain KDF
* `chainKDFBound` — the DDH and root-step terms of `Messaging.sm_dh_advantage_le` and
  `epochChainBound` summed over the epochs
* `hmacChainBound` — the HMAC bound of `hmac_prf_bound` at a two-query adversary

## Main results

* `fsaead_advantage_twoPointPRG_le` — the FS-AEAD advantage of one epoch is at most
  `epochChainBound` with the adaptive PRF advantage of `kdf`
* `signal_dr_confidentiality_prf` — the secure-messaging advantage is at most
  `chainKDFBound` with the adaptive PRF advantage of the chain KDF at the two-query reductions
  `twoPointRed c₁ c₂` of the FS-PRG reductions
* `signal_dr_confidentiality_hmac` — the same with the chain KDF HMAC over a compression
  function, each PRF term bounded by the HMAC bound `hmacChainBound`

## References

* T. Perrin, M. Marlinspike, *The Double Ratchet Algorithm*, §5.2 (`KDF_CK`)
* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019
* M. Bellare, *New Proofs for NMAC and HMAC: Security without Collision-Resistance*,
  CRYPTO 2006
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.DoubleRatchet.ChainKDF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
  CatCrypt.Crypto.Assumptions CatCrypt.Crypto.PRPPRF CatCrypt.Crypto.PRGFromPRF
  CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

variable {RK W B Ct : Type} [Fintype RK] [Nonempty RK] [CryptoWord W] [SampleableType Ct]

/-- The FS-AEAD bound of one epoch with the chain step `twoPointPRG kdf c₁ c₂`, the messages
`m` and the FS-AEAD adversary `X`: for each message `i` the term `term` at the two-query
reduction `twoPointRed c₁ c₂` of the FS-PRG reduction, and for each message `j` the one-time
AEAD advantage of `D` at the encryption reduction. -/
noncomputable def epochChainBound (kdf : W → B → W) (c₁ c₂ : B) (D : AEADDef W Ct)
    (term : OracleAdv B W Bool → ℝ≥0∞) (m : List (W × W)) (X : List Ct × W → SPComp Bool) :
    ℝ≥0∞ :=
  ∑ i ∈ Finset.range m.length,
      term (twoPointRed c₁ c₂ (fsprgRed (twoPointPRG kdf c₁ c₂) m.length i (fsaeadPost D m X))) +
    ∑ j ∈ Finset.range m.length,
      AEAD_Advantage D (m.getD j default).1 (m.getD j default).2
        (fsaeadRed D m j (m.length - (j + 1)) X)

/-- The bound of the double ratchet with the Diffie–Hellman CKA over `G`, the root step `R` and
the chain step `twoPointPRG kdf c₁ c₂` at the adversary `A`: for each epoch `t`, the DDH
advantage of `ckaDDHRed` at `smCKARed`, the PRG advantage of `R` at `smRootRed`, and
`epochChainBound` at `smAEADRed`. -/
noncomputable def chainKDFBound (G : Type) [CyclicGroup G] (R : PRGDef (RK × G) (RK × W))
    (kdf : W → B → W) (c₁ c₂ : B) (D : AEADDef W Ct) (term : OracleAdv B W Bool → ℝ≥0∞)
    (msgs : List (List (W × W))) (A : SMView G Ct → SPComp Bool) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range msgs.length,
      DDH_Advantage G (ckaDDHRed t (msgs.length - (t + 1))
        (smCKARed R (twoPointPRG kdf c₁ c₂) D msgs t A)) +
    ∑ t ∈ Finset.range msgs.length,
      PRG_Advantage R (smRootRed (dhCKA G) R (twoPointPRG kdf c₁ c₂) D msgs t
        (msgs.length - (t + 1)) A) +
    ∑ t ∈ Finset.range msgs.length,
      epochChainBound kdf c₁ c₂ D term (msgs.getD t [])
        (smAEADRed (dhCKA G) (twoPointPRG kdf c₁ c₂) D msgs t (msgs.length - (t + 1)) A)

variable [DecidableEq B]

omit [Fintype RK] [Nonempty RK] in
/-- **FS-AEAD with a PRF chain KDF.** For distinct chain inputs `c₁ ≠ c₂` and every FS-AEAD
adversary `X`, the FS-AEAD advantage of the chain step `twoPointPRG kdf c₁ c₂` and `D` on the
messages `m` is at most `epochChainBound` with the adaptive PRF advantage of `kdf`. -/
theorem fsaead_advantage_twoPointPRG_le (kdf : W → B → W) {c₁ c₂ : B} (hc : c₁ ≠ c₂)
    (D : AEADDef W Ct) (m : List (W × W)) (X : List Ct × W → SPComp Bool) :
    FSAEAD_Advantage (twoPointPRG kdf c₁ c₂) D m X ≤
      epochChainBound kdf c₁ c₂ D (PRF_q_Advantage kdf) m X := by
  refine (fsaead_advantage_le _ D m X).trans ?_
  unfold epochChainBound
  gcongr with i hi
  exact prg_advantage_twoPointPRG_le kdf hc _

/-- **Confidentiality of the Signal double ratchet with a PRF chain KDF.** For distinct chain
inputs `c₁ ≠ c₂` and every adversary `A`, the secure-messaging advantage of the double ratchet
with the Diffie–Hellman CKA over `G`, the root step `R`, the chain step
`CK ↦ (kdf CK c₁, kdf CK c₂)` and the AEAD scheme `D` is at most `chainKDFBound` with the
adaptive PRF advantage of `kdf`: the DDH and root-step PRG advantages, plus, for each epoch `t`
and message `i`, the adaptive PRF advantage of `kdf` against the two-query reduction
`twoPointRed c₁ c₂` of the FS-PRG reduction, plus the one-time AEAD advantages of the
encryption reductions. -/
theorem signal_dr_confidentiality_prf (G : Type) [CyclicGroup G] (R : PRGDef (RK × G) (RK × W))
    (kdf : W → B → W) {c₁ c₂ : B} (hc : c₁ ≠ c₂) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (A : SMView G Ct → SPComp Bool) :
    SM_Advantage (dhCKA G) R (twoPointPRG kdf c₁ c₂) D msgs A ≤
      chainKDFBound G R kdf c₁ c₂ D (PRF_q_Advantage kdf) msgs A := by
  refine (sm_dh_advantage_le G R (twoPointPRG kdf c₁ c₂) D msgs A).trans ?_
  unfold chainKDFBound
  gcongr with t ht
  exact fsaead_advantage_twoPointPRG_le kdf hc D _ _

/-! ## The chain KDF as HMAC -/

section HMAC

open CatCrypt.Crypto.Constructions.NMACPRF CatCrypt.Crypto.Constructions.ECBCPRF

variable {Bk : Type} [XorOp Bk] [DecidableEq Bk] [Nontrivial Bk] {ℓ : ℕ}

/-- The HMAC bound of `hmac_prf_bound` at an adversary `X` with two queries: the PRF advantage
of the dual key family against `hmacKeyAdv`, the PRF advantage of `f` against the outer NMAC
reduction and the cascade reductions, and the collision term `1 / |W|`. -/
noncomputable def hmacChainBound (f : W → Bk → W) (fpad : W → Bk) (iv : W) (ipad opad : Bk)
    (kpad : W → Bk) (X : OracleAdv (Msg Bk ℓ) W Bool) : ℝ≥0∞ :=
  PRF_q_Advantage (hmacKeyFamily f iv kpad) (hmacKeyAdv f fpad ipad opad X) +
    (PRF_q_Advantage f (nmacOuterAdv f fpad X) +
      ∑ j ∈ Finset.range 2, ∑ i ∈ Finset.range j,
        ∑ n ∈ Finset.range (2 * ℓ + 1), PRF_q_Advantage f (cascadeAdv f X i j n) +
      ((2 * (2 - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card W)

omit [SampleableType Ct] in
/-- The PRF advantage of HMAC against a two-point reduction is at most `hmacChainBound`. -/
theorem prf_hmac_twoPointRed_le (f : W → Bk → W) {fpad : W → Bk}
    (hfpad : Function.Injective fpad) (iv : W) {ipad opad : Bk} (hpad : ipad ≠ opad)
    (kpad : W → Bk) (c₁ c₂ : Msg Bk ℓ) (X : PRG_Adversary (W × W)) :
    PRF_q_Advantage (hmac f fpad iv ipad opad kpad ℓ) (twoPointRed c₁ c₂ X) ≤
      hmacChainBound f fpad iv ipad opad kpad (twoPointRed c₁ c₂ X) :=
  hmac_prf_bound f hfpad iv hpad kpad _ 2 (isQueryBound_twoPointRed c₁ c₂ X)

/-- **Confidentiality of the Signal double ratchet with the HMAC chain KDF.** For distinct
chain inputs `c₁ ≠ c₂`, `ipad ≠ opad`, an injective padding `fpad` and every adversary `A`, the
secure-messaging advantage of the double ratchet with chain KDF HMAC over the compression
function `f` is at most `chainKDFBound` with the HMAC bound `hmacChainBound` at the two-query
reductions `twoPointRed c₁ c₂` of the FS-PRG reductions. -/
theorem signal_dr_confidentiality_hmac (G : Type) [CyclicGroup G] (R : PRGDef (RK × G) (RK × W))
    (f : W → Bk → W) {fpad : W → Bk} (hfpad : Function.Injective fpad) (iv : W)
    {ipad opad : Bk} (hpad : ipad ≠ opad) (kpad : W → Bk) {c₁ c₂ : Msg Bk ℓ} (hc : c₁ ≠ c₂)
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (A : SMView G Ct → SPComp Bool) :
    SM_Advantage (dhCKA G) R (twoPointPRG (hmac f fpad iv ipad opad kpad ℓ) c₁ c₂) D msgs A ≤
      chainKDFBound G R (hmac f fpad iv ipad opad kpad ℓ) c₁ c₂ D
        (hmacChainBound f fpad iv ipad opad kpad) msgs A := by
  refine (signal_dr_confidentiality_prf G R (hmac f fpad iv ipad opad kpad ℓ) hc D msgs
    A).trans ?_
  unfold chainKDFBound epochChainBound
  gcongr with t ht i hi
  exact prf_hmac_twoPointRed_le f hfpad iv hpad kpad c₁ c₂ _

end HMAC

end CatCrypt.Crypto.Signal.DoubleRatchet.ChainKDF
