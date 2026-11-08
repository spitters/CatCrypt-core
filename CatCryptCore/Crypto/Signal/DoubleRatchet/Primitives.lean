/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.DoubleRatchet_CKA
public import CatCryptCore.Crypto.HKDF.HMACModel
public import CatCryptCore.Crypto.PRGFromPRF
public import CatCryptCore.Crypto.Assumptions.ODH
public import CatCryptCore.Crypto.Constructions.CBCINDCPA
public import CatCryptCore.ForMathlib.PMFUniform
import CatCryptCore.Tactics.DeriveReduction
import CatCryptCore.Tactics.DeriveTimed

/-!
# The primitives of the Signal double ratchet

`signal_dr_confidentiality` bounds the secure-messaging advantage of the Signal double ratchet
by DDH advantages, PRG advantages of the root step `hkdfRoot kdf` and FS-AEAD advantages. This
module bounds the root-step PRG terms by the HMAC advantages of HKDF, and states the bound for
the message encryption of libsignal (AES-256-CBC with a truncated HMAC-SHA256 tag) in place of
the encryption-only FS-AEAD of `signal_dr_confidentiality`.

## The root step

Signal derives the next root key and the chain key of an epoch as the 64 bytes
`HKDF(salt = rk, ikm = DH output, info = "WhisperRatchet")` (Perrin–Marlinspike §5.2, `KDF_RK`;
libsignal `RootKey::create_chain` in `rust/protocol/src/ratchet/keys.rs`): HKDF-Extract keyed
by the root key on the encoded DH output, then the first two blocks `T(1)`, `T(2)` of
HKDF-Expand, the root key and the chain key. The single-shot
game `HKDF_Advantage` of `HKDF_UC` gives one output block, so the root step is bounded by the
Extract term of `hkdf_advantage_le` (`extract_advantage_le`) and an Expand term at two queries:

* the root-step PRG game samples the root key and the DH output; averaging over the DH output
  (`PRGFromPRF.prg_advantage_prod_le_avg`) leaves for each DH output
  the HKDF game with uniform salt and that input keying material;
* Extract under a uniform salt is replaced by a uniform pseudorandom key at the one-query HMAC
  bound of `extract_advantage_le`;
* the two Expand blocks from a uniform pseudorandom key are the PRG
  `HMACModel.twoBlockExpand` of two chained HMAC evaluations, whose PRG advantage is at most
  the HMAC bound `hmacBound P 2` of the two-query reduction `twoBlockExpandRed`
  (`HMACModel.prg_advantage_twoBlockExpand_le`).

## Main definitions

* `signalRootKdf P encI info` — the Signal root step over HKDF of `P`, and `rootExtractRed`, the
  Extract reduction of its root-step PRG game
* `MsgCipher`, `signalMsgAEAD C` — the Signal message encryption: key expansion, AES-CBC with a
  derived IV, HMAC tag truncated to 8 bytes
* `msgKeyRed`, `msgCbcAdv`, `msgTagRed` — its reductions to the key expansion, the CBC
  real-or-random game and the PRF game of the tag function

## Main results

* `prg_advantage_signalRoot_le` — the root-step PRG advantage is at most the average Extract
  HMAC bound plus the two-query Expand HMAC bound
* `signal_dr_confidentiality_hkdf` — `signal_dr_confidentiality` with the root step over HKDF
* `aead_advantage_signalMsg_le` — the one-time real-or-random advantage of the message
  encryption is at most a PRG, a PRP (with `n(n-1)/|B|`) and a PRF advantage
* `signal_dr_confidentiality_etm` — the double ratchet with root step over HKDF and the Signal
  message encryption, bounded by DDH, HMAC, chain-PRG, key-expansion PRG, PRP and PRF terms
* time certificates of every reduction (`*.timeBound_timed`)

## References

* T. Perrin, M. Marlinspike, *The Double Ratchet Algorithm*, §5.2 (`KDF_RK`)
* H. Krawczyk, *Cryptographic Extraction and Key Derivation: The HKDF Scheme*, CRYPTO 2010
* M. Bellare, *New Proofs for NMAC and HMAC: Security without Collision-Resistance*,
  CRYPTO 2006
* RFC 5869
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.DoubleRatchet.Primitives

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
  CatCrypt.Crypto.PRPPRF CatCrypt.Crypto.PRGFromPRF CatCrypt.Crypto.Signal.DoubleRatchet_CKA
  CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

/-! ## The root step over HKDF -/

section RootKDF

open CatCrypt.Crypto.HKDF.HMACModel CatCrypt.Crypto.HKDF_UC
  CatCrypt.Crypto.Constructions.KBKDFPRF CatCrypt.Crypto.Constructions.ECBCPRF

variable {K B : Type} [CryptoWord K] [DecidableEq B] [Nontrivial B] [XorOp B]
  (P : HkdfHmac K B)

/-- **The Signal root step over HKDF** (`KDF_RK`): from the root key `rk`, the HKDF salt, and
the DH output `I`, encoded as input keying material by `encI`, the 64 bytes of
`HKDF(rk, encI I, info)`: HKDF-Extract of `P`, then the two blocks `twoBlockExpand P info`, the
next root key and the chain key. -/
def signalRootKdf {G : Type} (encI : G → K) (info : K) (rk : K) (I : G) : K × K :=
  (twoBlockExpand P info).stretch ((hkdfDef P).extract rk (encI I))

/-- The Extract reduction of the root step at the DH output `I`: the one-query HMAC adversary
asking `P.enc (encI I)` and running `A` on the two Expand blocks of the answer. -/
noncomputable def rootExtractRed {G : Type} (encI : G → K) (info : K)
    (A : Assumptions.PRG_Adversary (K × K)) (I : G) : OracleAdv (Msg B P.ℓ) K Bool :=
  oneQueryAdv (P.enc (encI I)) fun prk => A ((twoBlockExpand P info).stretch prk)

variable {G : Type} [Fintype G] [Nonempty G]

/-- **The Signal root step over HKDF is a PRG.** For an Expand encoding injective in the
counter on `1, 2` and every adversary `A`, the PRG advantage of the root step
`hkdfRoot (signalRootKdf P encI info)` on a uniform root key and DH output is at most the
average over the DH outputs `I` of the one-query HMAC bound of the Extract reduction
`rootExtractRed`, plus the two-query HMAC bound of the Expand reduction `twoBlockExpandRed`. -/
theorem prg_advantage_signalRoot_le (encI : G → K) (info : K) (hinj : MsgInjOn P.msg 2)
    (A : Assumptions.PRG_Adversary (K × K)) :
    Assumptions.PRG_Advantage (hkdfRoot (signalRootKdf P encI info)) A ≤
      ∑ I : G, (Fintype.card G : ℝ≥0∞)⁻¹ * hmacBound P 1 (rootExtractRed P encI info A I) +
        hmacBound P 2 (twoBlockExpandRed P info A) := by
  refine (prg_advantage_prod_le_avg _ A).trans ?_
  have hstep : ∀ I : G,
      AdvantageA ((SPComp.sample K).bind fun rk =>
          SPComp.pure ((hkdfRoot (signalRootKdf P encI info)).stretch (rk, I)))
        Assumptions.prg_ideal A ≤
      hmacBound P 1 (rootExtractRed P encI info A I) +
        hmacBound P 2 (twoBlockExpandRed P info A) := by
    intro I
    have hmid := advantageA_triangle
      ((SPComp.sample K).bind fun rk =>
        SPComp.pure ((hkdfRoot (signalRootKdf P encI info)).stretch (rk, I)))
      (Assumptions.prg_real (twoBlockExpand P info)) Assumptions.prg_ideal A
    refine hmid.trans (add_le_add ?_ (prg_advantage_twoBlockExpand_le P info hinj A))
    refine le_of_eq_of_le ?_ (extract_advantage_le P (encI I) _)
    unfold Extract_Advantage AdvantageA extract_real extract_ideal
    simp only [Assumptions.prg_real, hkdfRoot, signalRootKdf, SPComp.monad_bind_eq,
      SPComp.bind_assoc, SPComp.pure_bind]
  calc _ ≤ ∑ I : G, (Fintype.card G : ℝ≥0∞)⁻¹ *
          (hmacBound P 1 (rootExtractRed P encI info A I) +
            hmacBound P 2 (twoBlockExpandRed P info A)) :=
        Finset.sum_le_sum fun I _ => by gcongr; exact hstep I
    _ = _ := by
        have hG : (Fintype.card G : ℝ≥0∞) ≠ 0 := by simp
        rw [Finset.sum_congr rfl fun I _ => mul_add _ _ _, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel hG (ENNReal.natCast_ne_top _), one_mul]

/-- **Confidentiality of the Signal double ratchet with the root step over HKDF.** For an
Expand encoding injective in the counter on `1, 2` and every adversary `A`, the secure-messaging
advantage of the Signal double ratchet with root step `signalRootKdf P encI info` (HKDF of `P`
keyed by the root key on the encoded DH output, two Expand blocks) is at most the DDH and
FS-AEAD advantages of `signal_dr_confidentiality`, plus, for each epoch `t`, the average over
the DH outputs of the one-query HMAC bound of the Extract reduction and the two-query HMAC
bound of the Expand reduction, both built from the root-step reduction `smRootRed`. -/
theorem signal_dr_confidentiality_hkdf (G : Type) [CyclicGroup G] (encI : G → K) (info : K)
    (hinj : MsgInjOn P.msg 2) (cfg : FSAEAD.FSAEADConfig K) (msgs : List (List K))
    (A : SMView G K → SPComp Bool) :
    SM_Advantage (dhCKA G) (hkdfRoot (signalRootKdf P encI info)) (FSAEAD.toPRG cfg)
        (FSAEAD.toAEAD cfg) (signalMsgs msgs) A ≤
      ∑ t ∈ Finset.range msgs.length,
          DDH_Advantage G (ckaDDHRed t (msgs.length - (t + 1))
            (smCKARed (hkdfRoot (signalRootKdf P encI info)) (FSAEAD.toPRG cfg)
              (FSAEAD.toAEAD cfg) (signalMsgs msgs) t A)) +
        ∑ t ∈ Finset.range msgs.length,
          (∑ I : G, (Fintype.card G : ℝ≥0∞)⁻¹ * hmacBound P 1 (rootExtractRed P encI info
              (smRootRed (dhCKA G) (hkdfRoot (signalRootKdf P encI info)) (FSAEAD.toPRG cfg)
                (FSAEAD.toAEAD cfg) (signalMsgs msgs) t (msgs.length - (t + 1)) A) I) +
            hmacBound P 2 (twoBlockExpandRed P info
              (smRootRed (dhCKA G) (hkdfRoot (signalRootKdf P encI info)) (FSAEAD.toPRG cfg)
                (FSAEAD.toAEAD cfg) (signalMsgs msgs) t (msgs.length - (t + 1)) A))) +
        ∑ t ∈ Finset.range msgs.length,
          FSAEAD.FSAEAD_Advantage cfg (msgs.getD t [])
            (smAEADRed (dhCKA G) (FSAEAD.toPRG cfg) (FSAEAD.toAEAD cfg)
              (signalMsgs msgs) t (msgs.length - (t + 1)) A) := by
  refine (signal_dr_confidentiality G (signalRootKdf P encI info) cfg msgs A).trans ?_
  gcongr with t ht
  exact prg_advantage_signalRoot_le P encI info hinj _

end RootKDF

/-! ## The message encryption of Signal

libsignal encrypts a message under its message key `MK` by expanding `MK` with HKDF (info
`"WhisperMessageKeys"`, 80 bytes; `MessageKeys::derive_keys` in
`rust/protocol/src/ratchet/keys.rs`) into a 32-byte AES-256 key, a 32-byte HMAC-SHA256 key and
a 16-byte IV, encrypting the padded plaintext with AES-256-CBC under that key and IV, and
appending the HMAC-SHA256 tag of the two identity keys and the serialized message, truncated to
its first 8 bytes (`SignalMessage::MAC_LENGTH = 8` and `SignalMessage::compute_mac` in
`rust/protocol/src/protocol.rs`, libsignal `main`, checked 2026-11-03; the Double Ratchet
specification, §5.2, recommends this construction). The IV is not sent; the model below
includes the ciphertext blocks and the tag, not the IV.

`MsgCipher` abstracts this as the key expansion `derive`, the block cipher `E`, the encoding of
a plaintext as `n` blocks and the tag function `T` on the associated data and the ciphertext
blocks, with tag space `Tag`; for libsignal `Fintype.card Tag = 2 ^ 64`. The one-time
real-or-random advantage `AEAD_Advantage` of `signalMsgAEAD C` is at most the PRG advantage of
the key expansion, the CBC real-or-random terms of `cbc_ror_bound` at one query (the IND-CPA
half of encrypt-then-MAC in `AESCBC_HMAC`: a PRP advantage of `E` and `n(n-1) / |B|`) and a
one-query PRF advantage of `T` (`aead_advantage_signalMsg_le`). The tag length enters only the
authenticity term `q / |Tag|` of `etm_int_ctxt_le_prf`, which the confidentiality game does not
contain. -/

section MessageAEAD

open CatCrypt.Crypto.Constructions.CBCINDCPA CatCrypt.Crypto.Constructions.ECBCPRF

/-- Ciphertexts of `n` blocks with a tag are uniformly sampleable. -/
instance instSampleableTypeBlocksTag {B Tag : Type} {n : ℕ} [SampleableType B]
    [SampleableType Tag] : SampleableType ((Fin n → B) × Tag) where

/-- The message encryption of Signal with message keys `K`, blocks `B`, block-cipher keys
`KE`, MAC keys `KM`, tags `Tag` and plaintexts of `n` blocks. -/
structure MsgCipher (K B KE KM Tag : Type) (n : ℕ) where
  /-- Expansion of the message key into the cipher key, the IV and the MAC key (HKDF with info
  `"WhisperMessageKeys"`). -/
  derive : K → KE × B × KM
  /-- The block cipher (AES-256). -/
  E : KE → B → B
  /-- The padded plaintext as `n` blocks. -/
  encode : K → Fin n → B
  /-- The tag of the associated data and the ciphertext blocks (HMAC-SHA256 truncated to
  8 bytes). -/
  T : KM → K × List B → Tag
  /-- Decryption of ciphertext blocks under a cipher key and an IV. -/
  dec : KE → B → (Fin n → B) → Option K

variable {K B KE KM Tag : Type} {n : ℕ}

variable [CryptoWord B]

/-- The ciphertext of `pt` with associated data `ad` under the cipher key `ke`, the IV `iv`
and the MAC key `km`: the CBC blocks and their tag. -/
def msgCt (C : MsgCipher K B KE KM Tag n) (ke : KE) (iv : B) (km : KM) (pt ad : K) :
    (Fin n → B) × Tag :=
  (cbcVec (C.E ke) iv (C.encode pt), C.T km (ad, List.ofFn (cbcVec (C.E ke) iv (C.encode pt))))

variable [CryptoWord K] [SampleableType Tag] [Fintype KE] [Nonempty KE] [Fintype KM] [Nonempty KM]

/-- **The Signal message encryption** as a core AEAD scheme: encryption expands the message
key and returns `msgCt`; decryption checks the tag and decrypts the blocks. -/
def signalMsgAEAD (C : MsgCipher K B KE KM Tag n) : Assumptions.AEADDef K ((Fin n → B) × Tag) where
  encrypt mk pt ad := msgCt C (C.derive mk).1 (C.derive mk).2.1 (C.derive mk).2.2 pt ad
  decrypt mk ct ad := if C.T (C.derive mk).2.2 (ad, List.ofFn ct.1) = ct.2 then
    C.dec (C.derive mk).1 (C.derive mk).2.1 ct.1 else none

/-- The key expansion of `C` as a PRG on message keys. -/
def derivePRG (C : MsgCipher K B KE KM Tag n) : Assumptions.PRGDef K (KE × B × KM) :=
  ⟨C.derive⟩

/-- The PRG distinguisher of the key expansion: run `A` on the ciphertext of `pt` under the
challenge keys. -/
noncomputable def msgKeyRed (C : MsgCipher K B KE KM Tag n) (pt ad : K)
    (A : Assumptions.AEAD_Adversary ((Fin n → B) × Tag)) :
    Assumptions.PRG_Adversary (KE × B × KM) :=
  fun k => A (msgCt C k.1 k.2.1 k.2.2 pt ad)

/-- The plaintext `pt` as a CBC message of `n` blocks. -/
def msgOf (C : MsgCipher K B KE KM Tag n) (pt : K) : Msg B n :=
  ⟨List.ofFn (C.encode pt), by simp⟩

/-- The CBC real-or-random adversary: ask the encryption of `pt`, sample a MAC key, and run `A`
on the blocks of the answer and their tag. It asks one query. -/
noncomputable def msgCbcAdv (C : MsgCipher K B KE KM Tag n) (pt ad : K)
    (A : Assumptions.AEAD_Adversary ((Fin n → B) × Tag)) : OracleAdv (Msg B n) (B × List B) Bool :=
  .query (msgOf C pt) fun ct => .rand (PMF.uniformFintype KM) fun km =>
    .rand (outBool A (blocksVec ct.2, C.T km (ad, List.ofFn (blocksVec (n := n) ct.2)))) .ret

/-- The PRF adversary against the tag function: sample uniform blocks `c`, ask the tag of
`(ad, c)` and run `A` on the blocks and the answer. It asks one query. -/
noncomputable def msgTagRed (ad : K) (A : Assumptions.AEAD_Adversary ((Fin n → B) × Tag)) :
    OracleAdv (K × List B) Tag Bool :=
  .rand (PMF.uniformFintype (Fin n → B)) fun c => .query (ad, List.ofFn c) fun τ =>
    .rand (outBool A (c, τ)) .ret

omit [CryptoWord K] [SampleableType Tag] in
/-- The CBC real game against `msgCbcAdv` is the ideal PRG game of the key expansion against
`msgKeyRed`: uniform cipher key, IV and MAC key. -/
theorem prTrue_cbcRealGame_msgCbcAdv (C : MsgCipher K B KE KM Tag n) (pt ad : K)
    (A : Assumptions.AEAD_Adversary ((Fin n → B) × Tag)) :
    prTrue (cbcRealGame C.E (msgCbcAdv C pt ad A)) Heap.empty =
      prTrue ((Assumptions.prg_ideal (Output := KE × B × KM)).bind (msgKeyRed C pt ad A))
        Heap.empty := by
  rw [cbcRealGame, prTrue_liftPMF, Assumptions.prg_ideal, sample_eq_liftPMF, prTrue_liftPMF_bind,
    PMF.uniform_prod_eq_bind]
  congr 1
  simp only [msgCbcAdv, OracleAdv.run_query, OracleAdv.run_rand, OracleAdv.run_ret, encOracle,
    cbcEncrypt, PMF.uniform_prod_eq_bind, PMF.bind_map, PMF.map_bind, PMF.bind_bind,
    PMF.map_comp, Function.comp_def, PMF.pure_map, PMF.bind_pure, msgOf]
  rfl

omit [CryptoWord K] [SampleableType Tag] [Fintype KE] [Nonempty KE] in
/-- The CBC random game against `msgCbcAdv` is the real PRF game of the tag function against
`msgTagRed`: uniform blocks, and their tag under a uniform MAC key. -/
theorem prTrue_cbcRandGame_msgCbcAdv (C : MsgCipher K B KE KM Tag n) (pt ad : K)
    (A : Assumptions.AEAD_Adversary ((Fin n → B) × Tag)) :
    prTrue (cbcRandGame (msgCbcAdv C pt ad A)) Heap.empty =
      prTrue (realGame C.T (msgTagRed ad A)) Heap.empty := by
  rw [cbcRandGame, prTrue_liftPMF, realGame, prTrue_liftPMF]
  congr 1
  simp only [msgCbcAdv, msgTagRed, OracleAdv.run_query, OracleAdv.run_rand, OracleAdv.run_ret,
    randOracle, keyedOracle, randCiphertext, msgOf, List.length_ofFn, randBlocks_eq_map_ofFn,
    PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.pure_map,
    PMF.bind_pure, PMF.pure_bind, blocksVec_ofFn, PMF.bind_const]
  exact PMF.bind_comm _ _ _

omit [Fintype KE] [Nonempty KE] [Fintype KM] [Nonempty KM] in
/-- The random-function game against `msgTagRed` is the ideal one-time game: uniform blocks
and a uniform tag. -/
theorem prTrue_rfGame_msgTagRed (ad : K) (A : Assumptions.AEAD_Adversary ((Fin n → B) × Tag)) :
    prTrue (rfGame (msgTagRed ad A)) Heap.empty =
      prTrue (Assumptions.AEAD_Game_Ideal A) Heap.empty := by
  rw [rfGame, prTrue_liftPMF, Assumptions.AEAD_Game_Ideal, SPComp.monad_bind_eq,
    sample_eq_liftPMF, prTrue_liftPMF_bind]
  erw [PMF.uniform_prod_eq_bind]
  congr 1
  simp only [msgTagRed, rfOracle, List.lookup_nil, OracleAdv.run_query, OracleAdv.run_rand,
    OracleAdv.run_ret, PMF.bind_bind, PMF.bind_map, PMF.map_bind, Function.comp_def, PMF.pure_map,
    PMF.bind_pure]

derive_reduction msgKeyRed (adv := A)

derive_timed msgCbcAdv

derive_timed msgTagRed

/-- The CBC blocks of `M` under `f` of cost at most `k` cost at most `2 k + 10` units per block
and two more. -/
theorem cbcBlocks_timedCost_le (f : B → B) (fCost : B → ℕ) {k : ℕ} (hf : ∀ x, fCost x ≤ k)
    (s : B) (M : List B) : cbcBlocks.timedCost f fCost s M ≤ (2 * k + 10) * M.length + 2 := by
  induction M generalizing s with
  | nil => simp [cbcBlocks.timedCost]
  | cons m ms ih =>
    have h1 := ih (f (CryptoWord.wxor s m))
    have h2 := hf (CryptoWord.wxor s m)
    simp only [cbcBlocks.timedCost, List.length_cons, Nat.mul_succ]
    generalize (2 * k + 10) * ms.length = X at *
    omega

omit [CryptoWord K] [SampleableType Tag] [Fintype KE] [Nonempty KE] [Fintype KM] [Nonempty KM] in
/-- **Time of the key-expansion distinguisher.** With the costed adversary `A` of time at most
`T` and call cost at most `a`, the tag function of cost at most `τ`, the block cipher of cost at
most `e` and the encoding of cost at most `c` per block, the costed distinguisher has time at
most `T + a + τ + ((2 e + c + 18) n + 20) n + 10`: the CBC encryption of `n` blocks, the tag and
one call of `A`. -/
theorem msgKeyRed.tree.timeBound_timed (C : MsgCipher K B KE KM Tag n) (pt ad : K)
    (A : (Fin n → B) × Tag → SPTree.Timed Bool) (ACost : (Fin n → B) × Tag → ℕ) {T a : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (TCost : KM → K × List B → ℕ) {τ : ℕ}
    (hT : ∀ km x, TCost km x ≤ τ) (ECost : KE → B → ℕ) {e : ℕ} (hE : ∀ ke x, ECost ke x ≤ e)
    (encodeCost : K → Fin n → ℕ) {c : ℕ} (hc : ∀ p i, encodeCost p i ≤ c) (k : KE × B × KM) :
    SPTree.Timed.stepTime (msgKeyRed.tree.timed C pt ad A ACost k TCost ECost encodeCost) ≤
      T + a + τ + ((2 * e + c + 18) * n + 20) * n + 10 := by
  simp only [SPTree.Timed.stepTime, msgKeyRed.tree.timed]
  have hCB := cbcBlocks_timedCost_le (C.E k.1) (fun x => 1 + ECost k.1 x) (k := e + 1)
    (fun x => by have := hE k.1 x; omega) k.2.1 (List.ofFn (C.encode pt))
  have hFE := Fin.foldr.loop.timedCost_le n (fun x1 x2 => C.encode pt x1 :: x2)
    (fun x1 _ => 1 + encodeCost pt x1) (k := c + 1) (fun i _ => by have := hc pt i; omega) n
    le_rfl []
  rw [List.length_ofFn] at hCB
  refine le_trans (b := 1 + (a + (2 + (τ + (3 + ((((2 * e + c + 18) * n + 17) + 3) * n + 4)))))
    + T) ?_ (by ring_nf; omega)
  gcongr
  · exact hAc _
  · exact hT _ _
  · refine Fin.foldr.loop.timedCost_le _ _ _ (fun i x => ?_) _ _ _
    have hG := List.getD.timedCost_le_index (cbcBlocks (C.E k.1) k.2.1 (List.ofFn (C.encode pt)))
      i default
    have hi := i.isLt
    have h1 : (2 * (e + 1) + 10) * n = 2 * (e * n) + 12 * n := by ring
    have h2 : (c + 1 + 3) * n = c * n + 4 * n := by ring
    have h3 : (2 * e + c + 18) * n = 2 * (e * n) + c * n + 18 * n := by ring
    omega
  · exact hA _

omit [CryptoWord K] [Fintype KE] [Nonempty KE] [Fintype KM] [Nonempty KM] in
open OracleAdv.Timed in
/-- **Time of the tag-function adversary.** With the adversary `A` of cost at most `a`, the
costed one-query adversary `msgTagRed` has time at most `4 n + 16 + a`: the list of the `n`
blocks, one query and one call of `A`. -/
theorem msgTagRed.timeBound_timed (ad : K) (A : Assumptions.AEAD_Adversary ((Fin n → B) × Tag))
    (ACost : (Fin n → B) × Tag → ℕ) {a : ℕ} (hA : ∀ x, ACost x ≤ a) :
    StepTimeBound (msgTagRed.timed ad A ACost) (4 * n + 16 + a) := by
  have hF : ∀ b : Fin n → B, Fin.foldr.loop.timedCost n (fun x1 x2 => b x1 :: x2)
      (fun _ _ => 1) n le_rfl [] ≤ 4 * n + 4 := fun b =>
    (Fin.foldr.loop.timedCost_le n _ _ (k := 1) (fun _ _ => le_rfl) n le_rfl []).trans
      (by omega)
  unfold msgTagRed.timed
  simp only [stepTimeBound_zero, TimeBound]
  refine ⟨by omega, fun b => ?_⟩
  have := hF b
  grind

omit [CryptoWord K] [SampleableType Tag] [Fintype KE] [Nonempty KE] in
open OracleAdv.Timed in
/-- **Time of the CBC adversary.** With the adversary `A` of cost at most `a`, the tag function
of cost at most `τ` and the encoding of cost at most `c` per block, the costed CBC adversary
has time at most `(c + 4) n + (2 n + 9) n + a + τ + 30`: the message of `n` blocks, one query,
the vector of the `n` answer blocks, the tag and one call of `A`. -/
theorem msgCbcAdv.timeBound_timed (C : MsgCipher K B KE KM Tag n) (pt ad : K)
    (A : Assumptions.AEAD_Adversary ((Fin n → B) × Tag)) (ACost : (Fin n → B) × Tag → ℕ) {a : ℕ}
    (hA : ∀ x, ACost x ≤ a) (TCost : KM → K × List B → ℕ) {τ : ℕ} (hT : ∀ km x, TCost km x ≤ τ)
    (encodeCost : K → Fin n → ℕ) {c : ℕ} (hc : ∀ p i, encodeCost p i ≤ c) :
    StepTimeBound (msgCbcAdv.timed C pt ad A ACost TCost encodeCost)
      ((c + 4) * n + (2 * n + 9) * n + a + τ + 30) := by
  have hFE := Fin.foldr.loop.timedCost_le n (fun x1 x2 => C.encode pt x1 :: x2)
    (fun x1 _ => 1 + encodeCost pt x1) (k := c + 1) (fun i _ => by have := hc pt i; omega) n
    le_rfl []
  have hFB : ∀ ct : B × List B, Fin.foldr.loop.timedCost n
      (fun x1 x2 => blocksVec (n := n) ct.2 x1 :: x2)
      (fun x1 _ => 2 + List.getD.timedCost ct.2 (↑x1) default) n le_rfl [] ≤
        (2 * n + 9) * n + 4 := fun ct =>
    Fin.foldr.loop.timedCost_le n _ _ (k := 2 * n + 6) (fun i _ => by
      have := List.getD.timedCost_le_index ct.2 i default; have := i.isLt; omega) n le_rfl []
  have h4 : (c + 1 + 3) * n = (c + 4) * n := by ring
  rw [h4] at hFE
  unfold msgCbcAdv.timed
  simp only [StepTimeBound, TimeBound]
  generalize (c + 4) * n = X at *
  generalize (2 * n + 9) * n = Y at *
  refine ⟨by omega, by omega, fun ct => ⟨by omega, by omega, fun km => ?_⟩⟩
  have := hFB ct
  have := hA (blocksVec ct.2, C.T km (ad, List.ofFn (blocksVec (n := n) ct.2)))
  have := hT km (ad, List.ofFn (blocksVec (n := n) ct.2))
  refine ⟨by omega, by omega, fun _ => ⟨by omega, trivial⟩⟩

omit [CryptoWord K] [SampleableType Tag] [Fintype KE] [Nonempty KE] in
/-- The CBC adversary asks one query. -/
theorem isQueryBound_msgCbcAdv (C : MsgCipher K B KE KM Tag n) (pt ad : K)
    (A : Assumptions.AEAD_Adversary ((Fin n → B) × Tag)) :
    (msgCbcAdv C pt ad A).IsQueryBound 1 := by
  simp [msgCbcAdv, OracleAdv.IsQueryBound]

/-- **One-time security of the Signal message encryption.** For every plaintext `pt`,
associated data `ad` and adversary `A`, the advantage of `A` in distinguishing the encryption
of `pt` under a uniform message key from a uniform ciphertext is at most the PRG advantage of
the key expansion against `msgKeyRed`, the CBC real-or-random bound of `cbc_ror_bound` at one
query (the PRP advantage of the block cipher against `cbcRorAdv (msgCbcAdv C pt ad A)` and
`n(n-1) / |B|`), and the PRF advantage of the tag function against the one-query adversary
`msgTagRed ad A`. -/
theorem aead_advantage_signalMsg_le (C : MsgCipher K B KE KM Tag n) (pt ad : K)
    (A : Assumptions.AEAD_Adversary ((Fin n → B) × Tag)) :
    Assumptions.AEAD_Advantage (signalMsgAEAD C) pt ad A ≤
      Assumptions.PRG_Advantage (derivePRG C) (msgKeyRed C pt ad A) +
        (PRP_q_Advantage C.E (cbcRorAdv (msgCbcAdv C pt ad A)) +
          ((n * (n - 1) : ℕ) : ℝ≥0∞) / Fintype.card B) +
        PRF_q_Advantage C.T (msgTagRed ad A) := by
  have hPRG : Advantage (Assumptions.AEAD_Game_Real (signalMsgAEAD C) pt ad A)
      ((Assumptions.prg_ideal (Output := KE × B × KM)).bind (msgKeyRed C pt ad A)) =
      Assumptions.PRG_Advantage (derivePRG C) (msgKeyRed C pt ad A) := by
    simp only [Assumptions.AEAD_Game_Real, Assumptions.PRG_Advantage, AdvantageA,
      Assumptions.prg_real, SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
    rfl
  have hCBC : Advantage ((Assumptions.prg_ideal (Output := KE × B × KM)).bind
      (msgKeyRed C pt ad A)) (realGame C.T (msgTagRed ad A)) =
      CBC_ROR_Advantage C.E (msgCbcAdv C pt ad A) := by
    unfold CBC_ROR_Advantage Advantage
    rw [prTrue_cbcRealGame_msgCbcAdv, prTrue_cbcRandGame_msgCbcAdv]
  have hPRF : Advantage (realGame C.T (msgTagRed ad A)) (Assumptions.AEAD_Game_Ideal A) =
      PRF_q_Advantage C.T (msgTagRed ad A) := by
    unfold PRF_q_Advantage Advantage
    rw [prTrue_rfGame_msgTagRed]
  have hror := cbc_ror_bound C.E (msgCbcAdv C pt ad A) 1 (isQueryBound_msgCbcAdv C pt ad A)
  simp only [one_mul] at hror
  unfold Assumptions.AEAD_Advantage
  set G₁ := (Assumptions.prg_ideal (Output := KE × B × KM)).bind (msgKeyRed C pt ad A)
  set G₂ := realGame C.T (msgTagRed ad A)
  calc Advantage (Assumptions.AEAD_Game_Real (signalMsgAEAD C) pt ad A)
        (Assumptions.AEAD_Game_Ideal A)
      ≤ Advantage (Assumptions.AEAD_Game_Real (signalMsgAEAD C) pt ad A) G₁ +
          Advantage G₁ (Assumptions.AEAD_Game_Ideal A) := advantage_triangle _ _ _
    _ ≤ Advantage (Assumptions.AEAD_Game_Real (signalMsgAEAD C) pt ad A) G₁ +
          (Advantage G₁ G₂ + Advantage G₂ (Assumptions.AEAD_Game_Ideal A)) :=
        add_le_add le_rfl (advantage_triangle _ _ _)
    _ ≤ _ := by
        rw [hPRG, hCBC, hPRF, ← add_assoc]
        gcongr

end MessageAEAD

/-! ## The double ratchet over its primitives -/

section Composition

open CatCrypt.Crypto.HKDF.HMACModel CatCrypt.Crypto.Constructions.KBKDFPRF
  CatCrypt.Crypto.Constructions.CBCINDCPA

variable {K Bh B KE KM Tag : Type} {n : ℕ} [CryptoWord K] [DecidableEq Bh] [Nontrivial Bh]
  [XorOp Bh] [CryptoWord B] [SampleableType Tag] [Fintype KE] [Nonempty KE] [Fintype KM]
  [Nonempty KM]

/-- **Confidentiality of the Signal double ratchet over its primitives.** The double ratchet
with the Diffie–Hellman CKA over `G`, the root step over HKDF of `P` (`signalRootKdf`), the
chain step `F` and the Signal message encryption `signalMsgAEAD C` (AES-CBC with a derived IV
and a truncated HMAC tag over the associated data and the blocks) on the epochs `msgs` of
plaintexts with associated data. For an Expand encoding injective in the counter on `1, 2` and
every adversary `A`, the secure-messaging advantage is at most the sum over the epochs `t` of

* the DDH advantage of `ckaDDHRed` at `smCKARed`;
* the root-step HMAC bounds of `signal_dr_confidentiality_hkdf` at `smRootRed`;
* the PRG advantages of the chain step at the FS-PRG reductions of `smAEADRed`;
* for each message `j` of the epoch, the PRG advantage of the message-key expansion, the PRP
  advantage of the block cipher with the term `n(n-1) / |B|`, and the PRF advantage of the tag
  function, at the reductions of `aead_advantage_signalMsg_le` built from the FS-AEAD
  reduction `fsaeadRed` of `smAEADRed`.

The game exposes no decryption oracle, so no authenticity statement follows from it; an
authenticity bound needs a secure-messaging game with a receive oracle, whose forgery event is
then bounded per message by `etm_int_ctxt_le_prf` (with the term `q / |Tag|`, `2 ^ -64` per
query for the 8-byte tag). -/
theorem signal_dr_confidentiality_etm (G : Type) [CyclicGroup G] (P : HkdfHmac K Bh)
    (encI : G → K) (info : K) (hinj : MsgInjOn P.msg 2) (F : Assumptions.PRGDef K (K × K))
    (C : MsgCipher K B KE KM Tag n) (msgs : List (List (K × K)))
    (A : SMView G ((Fin n → B) × Tag) → SPComp Bool) :
    SM_Advantage (dhCKA G) (hkdfRoot (signalRootKdf P encI info)) F (signalMsgAEAD C) msgs A ≤
      ∑ t ∈ Finset.range msgs.length,
          DDH_Advantage G (ckaDDHRed t (msgs.length - (t + 1))
            (smCKARed (hkdfRoot (signalRootKdf P encI info)) F (signalMsgAEAD C) msgs t A)) +
        ∑ t ∈ Finset.range msgs.length,
          (∑ I : G, (Fintype.card G : ℝ≥0∞)⁻¹ * hmacBound P 1 (rootExtractRed P encI info
              (smRootRed (dhCKA G) (hkdfRoot (signalRootKdf P encI info)) F (signalMsgAEAD C)
                msgs t (msgs.length - (t + 1)) A) I) +
            hmacBound P 2 (twoBlockExpandRed P info
              (smRootRed (dhCKA G) (hkdfRoot (signalRootKdf P encI info)) F (signalMsgAEAD C)
                msgs t (msgs.length - (t + 1)) A))) +
        ∑ t ∈ Finset.range msgs.length,
          (∑ i ∈ Finset.range (msgs.getD t []).length,
              Assumptions.PRG_Advantage F (fsprgRed F (msgs.getD t []).length i
                (fsaeadPost (signalMsgAEAD C) (msgs.getD t [])
                  (smAEADRed (dhCKA G) F (signalMsgAEAD C) msgs t (msgs.length - (t + 1)) A))) +
            ∑ j ∈ Finset.range (msgs.getD t []).length,
              (Assumptions.PRG_Advantage (derivePRG C)
                  (msgKeyRed C ((msgs.getD t []).getD j default).1
                    ((msgs.getD t []).getD j default).2
                    (fsaeadRed (signalMsgAEAD C) (msgs.getD t []) j
                      ((msgs.getD t []).length - (j + 1))
                      (smAEADRed (dhCKA G) F (signalMsgAEAD C) msgs t
                        (msgs.length - (t + 1)) A))) +
                (PRP_q_Advantage C.E (cbcRorAdv (msgCbcAdv C ((msgs.getD t []).getD j default).1
                    ((msgs.getD t []).getD j default).2
                    (fsaeadRed (signalMsgAEAD C) (msgs.getD t []) j
                      ((msgs.getD t []).length - (j + 1))
                      (smAEADRed (dhCKA G) F (signalMsgAEAD C) msgs t
                        (msgs.length - (t + 1)) A)))) +
                  ((n * (n - 1) : ℕ) : ℝ≥0∞) / Fintype.card B) +
                PRF_q_Advantage C.T (msgTagRed ((msgs.getD t []).getD j default).2
                  (fsaeadRed (signalMsgAEAD C) (msgs.getD t []) j
                    ((msgs.getD t []).length - (j + 1))
                    (smAEADRed (dhCKA G) F (signalMsgAEAD C) msgs t
                      (msgs.length - (t + 1)) A))))) := by
  refine (sm_dh_advantage_le G (hkdfRoot (signalRootKdf P encI info)) F (signalMsgAEAD C) msgs
    A).trans ?_
  gcongr with t ht t ht
  · exact prg_advantage_signalRoot_le P encI info hinj _
  · refine (fsaead_advantage_le F (signalMsgAEAD C) (msgs.getD t []) _).trans ?_
    gcongr with j hj
    exact aead_advantage_signalMsg_le C _ _ _

end Composition

end CatCrypt.Crypto.Signal.DoubleRatchet.Primitives
