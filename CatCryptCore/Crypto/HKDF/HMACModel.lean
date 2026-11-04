/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.HKDF_UC
public import CatCryptCore.Crypto.Constructions.KBKDFPRF
public import CatCryptCore.Crypto.PRGFromPRF

/-!
# HKDF over HMAC with the compression function as primitive

`HkdfHmac K B` fixes RFC 5869 HKDF over HMAC (RFC 2104) with chaining values `K`,
blocks `B` and the compression function `f : K → B → K` (the parameters of
`Constructions.NMACPRF.hmac`), keys padded into a block by `kpad`, input keying
material encoded as a message by `enc`, and the Expand input
`T(i-1) ∥ info ∥ i` encoded as a message by `msg`.

* `hkdfDef P : HKDFDef K` is the single-shot scheme of `HKDF_UC` built from
  HMAC: `extract salt ikm = HMAC(salt, enc ikm)` and
  `expand prk info = HMAC(prk, msg none info 1)`, the first Expand block `T(1)`
  (`hkdfDef_expand_eq`).
* Its single-shot games are one-query PRF games of HMAC
  (`extract_advantage_eq`, `expand_advantage_eq`), so every Extract, Expand
  and composed HKDF advantage of `HKDF_UC` is bounded by the HMAC bound of
  `hmac_prf_bound` for an explicit one-query reduction, in terms of the
  compression function.
* The multi-query forms: HKDF-Extract keyed by the salt with adaptive input
  keying material, and HKDF-Expand keyed by the pseudorandom key with adaptive
  contexts and `n` blocks per context, concretely UC-emulate the
  variable-length random-function functionality `FVarPRF` with the HMAC bound
  of the chain reduction.

## Main definitions

* `HkdfHmac`, `hkdfDef`
* `oneQueryAdv` — the adversary asking one query and running a distinguisher
  on the answer
* `hmacBound P q R` — the HMAC bound of `hmac_prf_bound` for an adversary `R`
  asking at most `q` queries
* `hkdfHmacBound P` — the composed single-shot HKDF bound
* `extractOne`, `hkdfExtractL`, `hkdfExpandL` — the chain encodings of Extract
  (one block) and Expand (`n` blocks) as variable-length PRFs

## Main results

* `extract_advantage_eq`, `expand_advantage_eq` — the single-shot games are
  one-query PRF games of HMAC
* `extract_advantage_le`, `expand_advantage_le`, `hkdf_advantage_le` — the
  single-shot bounds in terms of the compression function
* `hkdf_hmac_uc_secure` — concrete UC emulation of `HKDF_UC` with bound
  `hkdfHmacBound P`
* `hkdfExtractGameAdvBoundC`, `hkdfExpandGameAdvBoundC` — the multi-query game
  bounds `hkdfExtractBound`, `hkdfExpandBound` in terms of `hmacBound`; concrete UC
  emulation of `FVarPRF` follows by `UCFromGameC.uc`

## References

* H. Krawczyk. *Cryptographic Extraction and Key Derivation: The HKDF Scheme.*
  CRYPTO 2010.
* M. Bellare. *New Proofs for NMAC and HMAC: Security without Collision
  Resistance.* CRYPTO 2006.
* RFC 5869, RFC 2104.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.HKDF.HMACModel

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.HKDF_UC CatCrypt.Crypto.Constructions.QueryList
open CatCrypt.Crypto.Constructions.ECBCPRF CatCrypt.Crypto.Constructions.NMACPRF
open CatCrypt.Crypto.Constructions.HKDFPRF CatCrypt.Crypto.Constructions.KBKDFPRF
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCDSL
open scoped ENNReal

/-! ## One-query games -/

section OneQuery

variable {K D R : Type}

/-- The adversary asking the single query `d` and outputting a sample of the output bit
of `Dist` on the answer. It runs `Dist` once. -/
noncomputable def oneQueryAdv (d : D) (Dist : R → SPComp Bool) : OracleAdv D R Bool :=
  .query d fun r => .rand (outBool Dist r) .ret

theorem isQueryBound_oneQueryAdv (d : D) (Dist : R → SPComp Bool) :
    (oneQueryAdv d Dist).IsQueryBound 1 :=
  fun _ _ => trivial

derive_timed oneQueryAdv

open OracleAdv.Timed in
/-- **Time of the one-query reduction.** With the distinguisher of cost at most `d` on every
answer, the costed one-query adversary has time at most `8 + d`. -/
theorem oneQueryAdv.timeBound_timed {D R : Type} (x : D) (Dist : R → SPComp Bool)
    (DistCost : R → ℕ) {d : ℕ} (hD : ∀ r, DistCost r ≤ d) :
    StepTimeBound (oneQueryAdv.timed x Dist DistCost) (8 + d) := by
  unfold oneQueryAdv.timed
  simp only [stepTimeBound_zero, TimeBound]
  grind

variable [Fintype K] [Nonempty K]

variable [Fintype R] [Nonempty R] [DecidableEq D]

/-- **A single-shot PRF game is a one-query PRF game.** The advantage of `Dist` between
`F k d` for a uniform key `k` and a uniform value is the PRF advantage of
`oneQueryAdv d Dist`. -/
theorem advantageA_sample_eq_PRF_q_Advantage (F : K → D → R) (d : D)
    (Dist : R → SPComp Bool) :
    AdvantageA ((SPComp.sample K).bind fun k => SPComp.pure (F k d)) (SPComp.sample R) Dist =
      PRF_q_Advantage F (oneQueryAdv d Dist) := by
  rw [sample_eq_liftPMF K, liftPMF_bind_pure, sample_eq_liftPMF R]
  unfold AdvantageA PRF_q_Advantage Advantage realGame rfGame
  simp only [prTrue_liftPMF_bind, prTrue_liftPMF, oneQueryAdv,
    OracleAdv.run_query, keyedOracle, rfOracle, PMF.pure_bind, OracleAdv.run_rand,
    OracleAdv.run_ret, PMF.map_bind, PMF.bind_map, Function.comp_def, List.lookup_nil,
    PMF.pure_map, PMF.bind_pure]

end OneQuery

/-! ## HKDF over HMAC -/

/-- RFC 5869 HKDF over HMAC with the compression function `f : K → B → K`: the
parameters of `Constructions.NMACPRF.hmac` (the padding `fpad` of a chaining value into a
block, the initial value `iv`, the pads `ipad ≠ opad`, the padding `kpad` of a key into a
block, the message length bound `ℓ` in blocks), the encoding `enc` of input keying
material as a message and the encoding `msg` of `T(i-1) ∥ info ∥ i` as a message. -/
structure HkdfHmac (K B : Type) [XorOp B] where
  /-- Compression function. -/
  f : K → B → K
  /-- Padding of a chaining value into a block. -/
  fpad : K → B
  /-- Initial chaining value. -/
  iv : K
  /-- Inner pad. -/
  ipad : B
  /-- Outer pad. -/
  opad : B
  /-- Padding of a key (salt or pseudorandom key) into a block. -/
  kpad : K → B
  /-- Bound on the number of message blocks. -/
  ℓ : ℕ
  /-- Encoding of input keying material as a message. -/
  enc : K → Msg B ℓ
  /-- Encoding of the previous block, the context and the counter as a message. -/
  msg : Option K → K → ℕ → Msg B ℓ
  fpad_injective : Function.Injective fpad
  ipad_ne_opad : ipad ≠ opad

variable {K B : Type} [SampleableType K] [DecidableEq B] [Nontrivial B] [XorOp B]

namespace HkdfHmac

variable (P : HkdfHmac K B)

/-- HMAC of `P` keyed by `k`. -/
abbrev mac : K → Msg B P.ℓ → K :=
  hmac P.f P.fpad P.iv P.ipad P.opad P.kpad P.ℓ

end HkdfHmac

variable (P : HkdfHmac K B)

/-- **The single-shot HKDF scheme of HMAC**: Extract is HMAC keyed by the salt on the
encoded input keying material, Expand is the first block `T(1)` of the Expand chain
keyed by the pseudorandom key. -/
def hkdfDef : HKDFDef K where
  extract salt ikm := hkdfExtract P.f P.fpad P.iv P.ipad P.opad P.kpad P.ℓ salt (P.enc ikm)
  expand prk info := P.mac prk (P.msg none info 1)

omit [DecidableEq B] [Nontrivial B] in
/-- The Expand function of `hkdfDef P` is the first block of RFC 5869 HKDF-Expand. -/
theorem hkdfDef_expand_eq (prk info : K) :
    (hkdfDef P).expand prk info =
      (hkdfExpand P.f P.fpad P.iv P.ipad P.opad P.kpad P.ℓ P.msg 1 prk info).head :=
  rfl

/-- The HMAC bound of `hmac_prf_bound` for an adversary `R` asking at most `q` queries:
the related-key PRF advantage of the HMAC key derivation against `hmacKeyAdv`, the PRF
advantages of the compression function against the outer and cascade reductions, and the
collision term. -/
noncomputable def hmacBound (q : ℕ) (R : OracleAdv (Msg B P.ℓ) K Bool) : ℝ≥0∞ :=
  PRF_q_Advantage (hmacKeyFamily P.f P.iv P.kpad) (hmacKeyAdv P.f P.fpad P.ipad P.opad R) +
    (PRF_q_Advantage P.f (nmacOuterAdv P.f P.fpad R) +
      ∑ j ∈ Finset.range q, ∑ i ∈ Finset.range j,
        ∑ m ∈ Finset.range (2 * P.ℓ + 1), PRF_q_Advantage P.f (cascadeAdv P.f R i j m) +
      ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card K)

/-- For one query the cascade and collision terms of `hmacBound` vanish. -/
theorem hmacBound_one (R : OracleAdv (Msg B P.ℓ) K Bool) :
    hmacBound P 1 R =
      PRF_q_Advantage (hmacKeyFamily P.f P.iv P.kpad) (hmacKeyAdv P.f P.fpad P.ipad P.opad R) +
        PRF_q_Advantage P.f (nmacOuterAdv P.f P.fpad R) := by
  simp_all [hmacBound]

theorem prf_mac_le_hmacBound (R : OracleAdv (Msg B P.ℓ) K Bool) (q : ℕ)
    (hR : R.IsQueryBound q) : PRF_q_Advantage P.mac R ≤ hmacBound P q R :=
  hmac_prf_bound P.f P.fpad_injective P.iv P.ipad_ne_opad P.kpad R q hR

/-! ## Single-shot bounds -/

omit [Nontrivial B] in
/-- **HKDF-Extract of HMAC as a one-query PRF game.** -/
theorem extract_advantage_eq (ikm : K) (A : K → SPComp Bool) :
    Extract_Advantage (hkdfDef P) ikm A = PRF_q_Advantage P.mac (oneQueryAdv (P.enc ikm) A) :=
  advantageA_sample_eq_PRF_q_Advantage P.mac (P.enc ikm) A

omit [Nontrivial B] in
/-- **HKDF-Expand of HMAC as a one-query PRF game.** -/
theorem expand_advantage_eq (info : K) (A : K → SPComp Bool) :
    Expand_Advantage (hkdfDef P) info A =
      PRF_q_Advantage P.mac (oneQueryAdv (P.msg none info 1) A) :=
  advantageA_sample_eq_PRF_q_Advantage P.mac (P.msg none info 1) A

/-- **HKDF-Extract of HMAC**: the Extract advantage of `A` is at most the one-query HMAC
bound for `oneQueryAdv (P.enc ikm) A`. -/
theorem extract_advantage_le (ikm : K) (A : K → SPComp Bool) :
    Extract_Advantage (hkdfDef P) ikm A ≤ hmacBound P 1 (oneQueryAdv (P.enc ikm) A) := by
  simp_all [extract_advantage_eq, prf_mac_le_hmacBound, isQueryBound_oneQueryAdv]

/-- **HKDF-Expand of HMAC**: the Expand advantage of `A` is at most the one-query HMAC
bound for `oneQueryAdv (P.msg none info 1) A`. -/
theorem expand_advantage_le (info : K) (A : K → SPComp Bool) :
    Expand_Advantage (hkdfDef P) info A ≤
      hmacBound P 1 (oneQueryAdv (P.msg none info 1) A) := by
  simp_all [expand_advantage_eq, prf_mac_le_hmacBound, isQueryBound_oneQueryAdv]

/-- The composed single-shot HKDF bound at `(ikm, info)` for the distinguisher `A`: the
one-query HMAC bound of the Extract reduction `hkdfExtractReduction` and of the Expand
distinguisher `A`. -/
noncomputable def hkdfHmacBound : K × K → (K → SPComp Bool) → ℝ≥0∞ :=
  fun i A =>
    hmacBound P 1 (oneQueryAdv (P.enc i.1) (hkdfExtractReduction (hkdfDef P) i.2 A)) +
      hmacBound P 1 (oneQueryAdv (P.msg none i.2 1) A)

/-- **HKDF of HMAC** (Krawczyk 2010 over Bellare 2006): the advantage of every
distinguisher against Extract-then-Expand with a uniform salt is at most
`hkdfHmacBound P (ikm, info) A`. -/
theorem hkdf_advantage_le (ikm info : K) (A : K → SPComp Bool) :
    HKDF_Advantage (hkdfDef P) ikm info A ≤ hkdfHmacBound P (ikm, info) A :=
  (hkdf_advantage_bound (hkdfDef P) ikm info A).trans
    (add_le_add (extract_advantage_le P ikm _) (expand_advantage_le P info A))

/-- Every distinguisher `D` separates the HKDF games of `hkdfDef P` at `(ikm, info)` by at
most `hkdfHmacBound P (ikm, info) D` (`hkdf_advantage_le`). -/
instance hkdf_hmac_gameAdvBoundC :
    GameAdvBoundC (fun i : K × K => hkdf_real (hkdfDef P) i.1 i.2)
      (fun _ => (hkdf_ideal : SPComp K)) (hkdfHmacBound P) :=
  ⟨fun i D => hkdf_advantage_le P i.1 i.2 D⟩

/-- **Concrete UC security of HKDF over HMAC.** The single-shot HKDF protocol of
`hkdfDef P` concretely UC-emulates the uniform-key functionality with gap at most
`hkdfHmacBound P` at the environment's input and the distinguisher `envReduction A Z`. -/
theorem hkdf_hmac_uc_secure (V : Type) :
    UCEmulatesCSim (hkdfSpec K V) (hkdfReal (hkdfDef P)) hkdfIdeal id
      (gameUCBound (hkdfHmacBound P)) :=
  UCFromGameC.uc

/-! ## Multi-query Extract and Expand -/

/-- The encoding of a message as the input of a one-block chain: the message itself. -/
def extractOne : Option K → Msg B P.ℓ → ℕ → Msg B P.ℓ := fun _ m _ => m

omit [SampleableType K] [DecidableEq B] [Nontrivial B] in
theorem msgInjOn_extractOne : MsgInjOn (extractOne P) 1 :=
  fun _ _ _ _ i i' h1 h2 h3 h4 he => ⟨he, by omega⟩

/-- HKDF-Extract with adaptive input keying material as a variable-length PRF with one
block per query. -/
def hkdfExtractL (salt : K) (ikm : Msg B P.ℓ) : List K :=
  [hkdfExtract P.f P.fpad P.iv P.ipad P.opad P.kpad P.ℓ salt ikm]

omit [SampleableType K] [DecidableEq B] [Nontrivial B] in
theorem hkdfExtractL_eq : hkdfExtractL P = expandVar P.mac (extractOne P) (fun _ => 1) :=
  rfl

/-- HKDF-Expand with adaptive contexts as a variable-length PRF with `n` blocks per
context. -/
def hkdfExpandL (n : ℕ) (prk info : K) : List K :=
  (hkdfExpand P.f P.fpad P.iv P.ipad P.opad P.kpad P.ℓ P.msg n prk info).toList

omit [SampleableType K] [DecidableEq B] [Nontrivial B] in
theorem hkdfExpandL_eq (n : ℕ) : hkdfExpandL P n = expandVar P.mac P.msg (fun _ => n) :=
  rfl

/-- Game bound of HKDF-Extract keyed by the salt on strategies asking at most `q` input
keying materials: the HMAC bound at `q` queries for the reduction
`expandVarAdv (extractOne P) (fun _ => 1) (prfDistAdv q S Dist)`. -/
noncomputable def hkdfExtractBound (q : ℕ) :
    PRFStrategy (Msg B P.ℓ) K → (List (Msg B P.ℓ × List K) → SPComp Bool) → ℝ≥0∞ :=
  fun S Dist => hmacBound P q (expandVarAdv (extractOne P) (fun _ => 1) (prfDistAdv q S Dist))

/-- On strategies asking at most `q` adaptive input keying materials, every distinguisher
separates the real protocol of Extract under a uniform salt from `FVarPRF` with one uniform
block per fresh query by at most `hkdfExtractBound P q`. With the `PureGame` instances of
`prfReal` and `FVarPRF`, `UCFromGameC.uc` gives concrete UC emulation with simulator
`S = A`. -/
instance hkdfExtractGameAdvBoundC (q : ℕ) :
    GameAdvBoundC (prfReal (hkdfExtractL P) q) (FVarPRF (fun _ => 1) q)
      (hkdfExtractBound P q) :=
  ⟨fun S Dist => by
    have h := prf_mac_le_hmacBound P
      (expandVarAdv (extractOne P) (fun _ => 1) (prfDistAdv q S Dist)) (q * 1)
      (isQueryBound_expandVarAdv (extractOne P) (fun _ => le_rfl)
        (isQueryBound_prfDistAdv q S _))
    rw [mul_one] at h
    exact ((gameAdvBoundC_expandVar P.mac (msgInjOn_extractOne P) (fun _ => le_rfl) q).bound_le
      S Dist).trans h⟩

/-- Game bound of the `n`-block HKDF-Expand chain on strategies asking at most `q`
contexts: the HMAC bound at `q n` queries for the reduction
`expandVarAdv P.msg (fun _ => n) (prfDistAdv q S Dist)`. -/
noncomputable def hkdfExpandBound (n q : ℕ) :
    PRFStrategy K K → (List (K × List K) → SPComp Bool) → ℝ≥0∞ :=
  fun S Dist => hmacBound P (q * n) (expandVarAdv P.msg (fun _ => n) (prfDistAdv q S Dist))

/-- For `P.msg` injective in the context and the counter on the counters `1, …, n`, and
strategies asking at most `q` adaptive contexts, every distinguisher separates the real
protocol of the `n`-block Expand chain under a uniform pseudorandom key from `FVarPRF` with
`n` uniform blocks per fresh context by at most `hkdfExpandBound P n q`, the HMAC bound for
a reduction asking at most `q n` queries. With the `PureGame` instances of `prfReal` and
`FVarPRF`, `UCFromGameC.uc` gives concrete UC emulation with simulator `S = A`. -/
theorem hkdfExpandGameAdvBoundC {n : ℕ} (hinj : MsgInjOn P.msg n) (q : ℕ) :
    GameAdvBoundC (prfReal (hkdfExpandL P n) q) (FVarPRF (fun _ => n) q)
      (hkdfExpandBound P n q) :=
  ⟨fun S Dist => ((gameAdvBoundC_expandVar P.mac hinj (fun _ => le_rfl) q).bound_le S Dist).trans
    (prf_mac_le_hmacBound P _ (q * n)
      (isQueryBound_expandVarAdv P.msg (fun _ => le_rfl) (isQueryBound_prfDistAdv q S _)))⟩

section TwoBlocks

open CatCrypt.Crypto.PRGFromPRF

/-! ## The first two blocks of HKDF-Expand

The first two blocks of HKDF-Expand from a uniform pseudorandom key are the PRG `chainPRG` of
two chained HMAC evaluations, whose input at the second block depends on the first; its PRG
advantage is the adaptive PRF advantage of HMAC against the two-query reduction `chainRed`
(`PRGFromPRF.prg_advantage_chainPRG_le`), at most the HMAC bound `hmacBound P 2`. -/

/-- The first two blocks `T(1) = HMAC(prk, msg none info 1)` and
`T(2) = HMAC(prk, msg T(1) info 2)` of HKDF-Expand of `P` (RFC 5869 §2.3) as a PRG on the
pseudorandom key. -/
def twoBlockExpand (info : K) : Assumptions.PRGDef K (K × K) :=
  chainPRG P.mac (P.msg none info 1) fun t => P.msg (some t) info 2

omit [SampleableType K] [DecidableEq B] [Nontrivial B] in
/-- The two blocks of `twoBlockExpand P info` are the first two blocks of RFC 5869 HKDF-Expand
of `P` with output length two blocks. -/
theorem twoBlockExpand_stretch (info prk : K) :
    (twoBlockExpand P info).stretch prk =
      ((Constructions.HKDFPRF.hkdfExpand P.f P.fpad P.iv P.ipad P.opad P.kpad P.ℓ P.msg 2 prk
          info).head,
        (Constructions.HKDFPRF.hkdfExpand P.f P.fpad P.iv P.ipad P.opad P.kpad P.ℓ P.msg 2 prk
          info).tail.head) := by
  simp [twoBlockExpand, chainPRG, Constructions.HKDFPRF.hkdfExpand, Constructions.HKDFPRF.expand,
    Constructions.HKDFPRF.expandVec]

/-- The reduction of the two Expand blocks: the two-query HMAC adversary `chainRed` of the
blocks. -/
noncomputable def twoBlockExpandRed (info : K) (A : Assumptions.PRG_Adversary (K × K)) :
    OracleAdv (Msg B P.ℓ) K Bool :=
  chainRed (P.msg none info 1) (fun t => P.msg (some t) info 2) A

derive_timed twoBlockExpandRed

omit [SampleableType K] [DecidableEq B] [Nontrivial B] in
open OracleAdv.Timed in
/-- **Time of the Expand reduction.** With the adversary `A` of cost at most `a` and the Expand
encoding of cost at most `c`, the costed reduction `twoBlockExpandRed` has time at most
`12 + 2 c + a`. -/
theorem twoBlockExpandRed.timeBound_timed (info : K) (A : Assumptions.PRG_Adversary (K × K))
    (ACost : K × K → ℕ) {a : ℕ} (hA : ∀ y, ACost y ≤ a) (msgCost : Option K → K → ℕ → ℕ)
    {c : ℕ} (hmsg : ∀ p x i, msgCost p x i ≤ c) :
    StepTimeBound (twoBlockExpandRed.timed P info A ACost msgCost) (12 + 2 * c + a) := by
  unfold twoBlockExpandRed.timed chainRed.timed
  refine (stepTimeBound_delay (n := 10 + c + a) ?_).mono (by grind)
  simp only [stepTimeBound_zero, TimeBound]
  grind

omit [SampleableType K] [DecidableEq B] [Nontrivial B] in
/-- For an Expand encoding injective in the counter on `1, 2`, the second Expand input differs
from the first. -/
theorem msg_two_ne_one {info : K} (hinj : MsgInjOn P.msg 2) (t : K) :
    P.msg (some t) info 2 ≠ P.msg none info 1 := fun h => by
  have := (hinj (some t) none info info 2 1 (by omega) le_rfl le_rfl (by omega) h).2
  omega

/-- The PRG advantage of the two Expand blocks is at most the HMAC bound at two queries of the
Expand reduction. -/
theorem prg_advantage_twoBlockExpand_le (info : K) (hinj : MsgInjOn P.msg 2)
    (A : Assumptions.PRG_Adversary (K × K)) :
    Assumptions.PRG_Advantage (twoBlockExpand P info) A ≤
      hmacBound P 2 (twoBlockExpandRed P info A) :=
  (prg_advantage_chainPRG_le P.mac (msg_two_ne_one P hinj) A).trans
    (prf_mac_le_hmacBound P _ 2 (isQueryBound_chainRed _ _ A))

end TwoBlocks

end CatCrypt.Crypto.HKDF.HMACModel
