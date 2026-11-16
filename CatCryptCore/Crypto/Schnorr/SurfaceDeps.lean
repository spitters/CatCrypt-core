/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Schnorr.Extraction.Schnorr_haxpipe
public import CatCryptCore.Crypto.Schnorr.ROMReduction
public import CatCryptCore.Crypto.ExtractedAlgebra
public import CatCryptCore.Examples.SchnorrSigma

/-!
# Schnorr SurfaceDeps: the extracted Schnorr signatures under a `GroupParam`

The hax extraction of `schnorr-hax` (`Extraction/Schnorr_haxpipe.lean`) leaves the group
and scalar arithmetic as the fields of `Schnorr.SchnorrDeps` over `Array Int`, in additive
notation. `schnorrInterpDeps` interprets them through a `GroupParam` by the core layer
`CatCryptCore.Crypto.ExtractedAlgebra`: `group_mul s P` is the exponentiation `P^s`,
`generator` the generator, `group_add` the group product, `scalar_mul` and `scalar_add`
compute on exponents, and `hash_challenge r pk m` is the challenge `H(r, m)` of a function
`H : G → M → Scalar` on the decoded commitment and message (the public key is not hashed,
as in the specification's challenge `H(a, m)`).

Under this interpretation the extracted `keygen`, `sign` and `verify` compute the public
key `g^sk`, the signature `(g^r, r + H(g^r, m)·sk)` and the verification equation
`g^z = a · pk^H(a, m)` of `SchnorrForking.schnorrVerifyROM`. The verifier ends with
`point_eq`, which compares the entries `0, …, 31`; on the codec `schnorrCodec`, which writes
a group element as one entry after its tag, `point_eq` decides equality of group elements
(`schnorrCodec_point_eq`).

The game `extEufcmaGame` is the EUF-CMA game of `SchnorrROM` in which the public key is
computed by the extracted `keygen`, every signing query is answered by the extracted `sign`
with the challenge read from the oracle's table, and the forgery is checked by the
extracted `verify`; it equals `SchnorrROM.eufcmaGame` (`extGameDist_eq`), so the
discrete-logarithm bound of `SchnorrROM.schnorr_rom_eufcma` holds for it
(`schnorr_extracted_rom_eufcma`).

## Main definitions

* `defaultSchnorrDeps` — the structural instance of `Schnorr.SchnorrDeps`
* `schnorrAlgInterp` — the interpretation of the Schnorr algebra of a `GroupParam`
* `schnorrInterpDeps` — the instance of `Schnorr.SchnorrDeps` interpreting the extracted
  operations, for a challenge function `H`
* `schnorrCodec` — the value codec writing a group element as one `Array Int` entry
  (`Codec.fintypeEntry`)
* `extSignOut`, `extRealStep`, `extWins`, `extGameDist`, `extEufcmaAdvantage` — the
  EUF-CMA game in the random-oracle model run on the extracted functions

## Main results
* `schnorr_keygen_interp`, `schnorr_sign_interp` — the extracted key generation and signer
  under `schnorrInterpDeps`
* `schnorr_verify_interp` — the extracted verifier is `schnorrVerifyROM` when `point_eq`
  decides equality of encoded group elements
* `schnorr_verify_sign_interp` — the extracted verifier accepts every extracted signature,
  for every value codec
* `schnorrCodec_point_eq` — `point_eq` decides equality on `schnorrCodec`
* `extGameDist_eq`, `extEufcmaAdvantage_eq` — the extracted game is `SchnorrROM`'s game
* `schnorr_extracted_rom_eufcma` — for every adversary `A`, the bound of
  `SchnorrROM.schnorr_rom_eufcma` by `DL_Advantage gp (dlReduction A)` on the advantage
  against the extracted functions
* `schnorr_extracted_rom_eufcma_reduction_time` — the costed form of `dlReduction A` erases
  to it and runs the adversary at most twice
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Schnorr.SurfaceDeps

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Examples CatCrypt.Examples.Schnorr
open CatCrypt.Crypto.Extracted
open CatCrypt.Crypto.OracleForking CatCrypt.Crypto.SchnorrForking CatCrypt.Crypto.SchnorrROM
open scoped ENNReal

/-- Pattern A3: structural wiring for the haxpipeT-extracted typeclass. -/
instance defaultSchnorrDeps : _root_.Schnorr.SchnorrDeps where
  group_mul a _ := a
  generator := #[]
  hash_challenge a _ _ := a
  scalar_mul a _ := a
  scalar_add a _ := a
  group_add a _ := a

/-! ## The interpretation through a `GroupParam` -/

section Interp

variable (gp : GroupParam) {M : Type}

/-- The group identity of `gp` as `One`. -/
abbrev gpOne : One gp.G := ⟨gp.identity⟩
/-- The group product of `gp` as `Mul`. -/
abbrev gpMul : Mul gp.G := ⟨gp.groupMul⟩
/-- The zero scalar of `gp` as `Zero`. -/
abbrev gpZero : Zero gp.Scalar := ⟨gp.scalarZero⟩
/-- Scalar addition of `gp` as `Add`. -/
abbrev gpAdd : Add gp.Scalar := ⟨gp.scalarAdd⟩
/-- Scalar multiplication of `gp` as `Mul`. -/
abbrev gpScalarMul : Mul gp.Scalar := ⟨gp.scalarMul⟩

attribute [local instance] gpOne gpMul gpZero gpAdd gpScalarMul

/-- The interpretation of the Schnorr algebra: the generator and exponentiation of `gp`,
    the trivial ambient ring `Unit`, and messages `M` as opaque data, with the value codec
    `c`. -/
def schnorrAlgInterp (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int)) :
    AlgInterp gp.G gp.Scalar Unit M where
  gen := gp.generator
  gpow := gp.groupExp
  embed _ := ()
  proj _ := gp.identity
  codec := c

variable {gp}

/-- The challenge `H(a, m)` on a decoded commitment and message, as a decoded exponent;
    `0` when the second value is not a message. -/
def schnorrChallenge (I : AlgInterp gp.G gp.Scalar Unit M) (H : gp.G → M → gp.Scalar)
    (a v : AlgVal gp.G gp.Scalar Unit M) : AlgVal gp.G gp.Scalar Unit M :=
  .exp (match v with
    | .dat m => H (I.toG a) m
    | _ => gp.scalarZero)

/-- The instance of `Schnorr.SchnorrDeps` interpreting each extracted operation by one
    operation of the interpretation `I`: `group_mul s P` by `P^s`, `group_add` by the group
    product, `scalar_mul` and `scalar_add` by the exponent operations, and
    `hash_challenge r pk m` by the challenge `H(r, m)` (`schnorrChallenge`). -/
@[instance_reducible]
def schnorrInterpDeps (I : AlgInterp gp.G gp.Scalar Unit M) (H : gp.G → M → gp.Scalar) :
    _root_.Schnorr.SchnorrDeps where
  group_mul s P := I.pow P s
  generator := I.generator
  hash_challenge r _ m := I.hash2 (schnorrChallenge I H) r m
  scalar_mul := I.expMul
  scalar_add := I.expAdd
  group_add := I.mul

variable (gp)

/-- **The extracted key generation under the interpretation.** The public key of the
    secret exponent `sk` is `g^sk`. -/
theorem schnorr_keygen_interp (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int))
    (H : gp.G → M → gp.Scalar) (sk : gp.Scalar) :
    letI := schnorrInterpDeps (schnorrAlgInterp gp c) H
    let I := schnorrAlgInterp gp c
    _root_.Schnorr.keygen (I.enc (.exp sk)) = (I.enc (.exp sk), I.enc (.grp (gp.exp sk))) := by
  unfold schnorrInterpDeps
  simp [_root_.Schnorr.keygen, schnorrAlgInterp, ← gp.groupExp_generator]

/-- **The extracted signer under the interpretation.** The signature of the message `m`
    with secret exponent `sk` and nonce `r` is `(g^r, r + H(g^r, m)·sk)`. -/
theorem schnorr_sign_interp (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int))
    (H : gp.G → M → gp.Scalar) (sk r : gp.Scalar) (m : M) :
    letI := schnorrInterpDeps (schnorrAlgInterp gp c) H
    let I := schnorrAlgInterp gp c
    _root_.Schnorr.sign (I.enc (.exp sk)) (I.enc (.exp r)) (I.enc (.dat m)) =
      (I.enc (.grp (gp.exp r)),
        I.enc (.exp (gp.scalarAdd r (gp.scalarMul (H (gp.exp r) m) sk)))) := by
  unfold schnorrInterpDeps
  simp [_root_.Schnorr.sign, _root_.Schnorr.SchnorrSignature,
    schnorrAlgInterp, schnorrChallenge, ← gp.groupExp_generator]
  rfl

/-- `point_eq` accepts equal arrays. -/
theorem point_eq_self (a : Array Int) : _root_.Schnorr.point_eq a a = true := by
  simp [_root_.Schnorr.point_eq, Hax.bne, Hax.foldRange, Hax.foldRange.go]

/-- **The extracted verifier under the interpretation.** When `point_eq` decides equality
    of encoded group elements, the extracted verifier on the public key `pk`, the message
    `m` and the signature `(a, z)` is `schnorrVerifyROM gp pk a (H(a, m)) z`. -/
theorem schnorr_verify_interp (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int))
    (hc : ∀ x y : gp.G, _root_.Schnorr.point_eq (c.enc (.grp x)) (c.enc (.grp y)) =
      decide (x = y))
    (H : gp.G → M → gp.Scalar) (pk a : gp.G) (z : gp.Scalar) (m : M) :
    letI := schnorrInterpDeps (schnorrAlgInterp gp c) H
    let I := schnorrAlgInterp gp c
    _root_.Schnorr.verify (I.enc (.grp pk)) (I.enc (.dat m)) (I.enc (.grp a), I.enc (.exp z)) =
      schnorrVerifyROM gp pk a (H a m) z := by
  unfold schnorrInterpDeps
  simp [_root_.Schnorr.verify, _root_.Schnorr.«.r», _root_.Schnorr.«.s», schnorrAlgInterp,
    schnorrChallenge, ← gp.groupExp_generator]
  rw [schnorrVerifyROM_unfold]
  exact hc _ _

/-- **Correctness of the extracted functions.** For every value codec and challenge
    function, the extracted verifier accepts the extracted signature of every message under
    the extracted public key. -/
theorem schnorr_verify_sign_interp (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int))
    (H : gp.G → M → gp.Scalar) (sk r : gp.Scalar) (m : M) :
    letI := schnorrInterpDeps (schnorrAlgInterp gp c) H
    let I := schnorrAlgInterp gp c
    _root_.Schnorr.verify (_root_.Schnorr.keygen (I.enc (.exp sk))).2 (I.enc (.dat m))
      (_root_.Schnorr.sign (I.enc (.exp sk)) (I.enc (.exp r)) (I.enc (.dat m))) = true := by
  have hk := schnorr_keygen_interp gp c H sk
  have hs := schnorr_sign_interp gp c H sk r m
  dsimp only at hk hs ⊢
  rw [hk, hs]
  unfold schnorrInterpDeps
  simp only [_root_.Schnorr.verify, _root_.Schnorr.«.r», _root_.Schnorr.«.s»,
    AlgInterp.hash2_enc, AlgInterp.generator_eq, AlgInterp.pow_grp, AlgInterp.mul_grp_grp,
    schnorrChallenge, schnorrAlgInterp, AlgInterp.toG_grp]
  have h : gp.exp r * gp.groupExp (gp.exp sk) (H (gp.exp r) m) =
      gp.exp (gp.scalarAdd r (gp.scalarMul (H (gp.exp r) m) sk)) := by
    rw [gp.groupExp_exp, gp.exp_add, gp.scalarMul_comm]
    rfl
  rw [h]
  simp only [gp.groupExp_generator]
  exact point_eq_self _

end Interp

/-! ## A codec on which `point_eq` decides equality -/

/-- `point_eq` on two arrays `[0, x]`, `[0, y]` decides `x = y`. -/
theorem point_eq_pair (x y : Int) :
    _root_.Schnorr.point_eq #[0, x] #[0, y] = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp [point_eq_self]
  · simp [_root_.Schnorr.point_eq, Hax.bne, Hax.foldRange, Hax.foldRange.go, Hax.index, h]

variable (gp : GroupParam) {M : Type}

/-- The value codec writing a group element as the tag `0` followed by one entry
    (`Codec.fintypeEntry`), with the codecs `cS` of exponents and `cM` of messages. -/
noncomputable def schnorrCodec (cS : Codec gp.Scalar (Array Int)) (cM : Codec M (Array Int)) :
    Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int) :=
  AlgVal.codec (Codec.fintypeEntry gp.G) cS (Codec.fintypeArray Unit) cM

/-- `point_eq` decides equality of group elements encoded by `schnorrCodec`. -/
theorem schnorrCodec_point_eq (cS : Codec gp.Scalar (Array Int)) (cM : Codec M (Array Int))
    (x y : gp.G) :
    _root_.Schnorr.point_eq ((schnorrCodec gp cS cM).enc (.grp x))
      ((schnorrCodec gp cS cM).enc (.grp y)) = decide (x = y) := by
  have h : ∀ n : Int, (#[0] ++ #[n] : Array Int) = #[0, n] := fun _ => rfl
  simp only [schnorrCodec, AlgVal.codec, Codec.fintypeEntry, h, point_eq_pair, Nat.cast_inj,
    (Codec.fintypeNat gp.G).enc_injective.eq_iff]

/-! ## The EUF-CMA game run on the extracted functions -/

section Game

variable [DecidableEq M]

attribute [local instance] gpOne gpMul gpZero gpAdd gpScalarMul

/-- The signing oracle on `m` run on the extracted signer: the extracted `sign` with
    secret exponent `sk` and nonce `r`, its challenge read from the table at the
    commitment and message, or the sampled `e` when that point is undefined; the
    challenger records the decoded commitment as `realSignOut` does. -/
noncomputable def extSignOut (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int))
    (sk : gp.Scalar) (t : Tables gp M) (b : Bool) (m : M) (r e : gp.Scalar) :
    Answer gp × (Tables gp M × Bool) :=
  let I := schnorrAlgInterp gp c
  let sig := letI := schnorrInterpDeps I fun a m' => (t.lookup (a, m')).getD e
    _root_.Schnorr.sign (I.enc (.exp sk)) (I.enc (.exp r)) (I.enc (.dat m))
  let a := I.toG (I.val sig.1)
  let z := (I.val sig.2).toS
  match t.lookup (a, m) with
  | some _ => (.inr (a, z), ({ t with signed := t.signed ++ [m] }, true))
  | none => (.inr (a, z), ({ t with prog := t.prog ++ [((a, m), e)], signed := t.signed ++ [m] }, b))

/-- The extracted signing oracle answers as `realSignOut`. -/
theorem extSignOut_eq (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int))
    (sk : gp.Scalar) (t : Tables gp M) (b : Bool) (m : M) (r e : gp.Scalar) :
    extSignOut gp c sk t b m r e = realSignOut sk t b m r e := by
  unfold extSignOut
  dsimp only
  rw [schnorr_sign_interp]
  simp only [AlgInterp.val_enc, AlgInterp.toG_grp, AlgVal.toS_exp]
  unfold realSignOut
  cases t.lookup (gp.exp r, m) <;> rfl

/-- The real oracle with the extracted signer. -/
noncomputable def extRealStep (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int))
    (sk : gp.Scalar) (s : Tables gp M × Bool) :
    Query gp M → Step (Answer gp) (Tables gp M × Bool) gp.Scalar
  | .inl k => hashStep s.1 s.2 k
  | .inr m => .plain (sample₂ (extSignOut gp c sk s.1 s.2 m))

/-- The winning condition with the extracted verifier: the message was never signed and
    the extracted `verify` accepts the encoded forgery under the challenge in the table. -/
def extWins (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int)) (pk : gp.G)
    (y : Forgery gp M × (Tables gp M × Bool)) : Bool :=
  let I := schnorrAlgInterp gp c
  !(y.2.1.signed.contains y.1.1) &&
    match y.2.1.lookup (y.1.2.1, y.1.1) with
    | some e => letI := schnorrInterpDeps I fun _ _ => e
        _root_.Schnorr.verify (I.enc (.grp pk)) (I.enc (.dat y.1.1))
          (I.enc (.grp y.1.2.1), I.enc (.exp y.1.2.2))
    | none => false

/-- The public key computed by the extracted key generation. -/
noncomputable def extPk (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int))
    (sk : gp.Scalar) : gp.G :=
  let I := schnorrAlgInterp gp c
  I.toG (I.val (letI := schnorrInterpDeps I fun _ _ => gp.scalarZero
    (_root_.Schnorr.keygen (I.enc (.exp sk))).2))

/-- The EUF-CMA experiment run on the extracted functions: the public key of the extracted
    `keygen`, the signing oracle of the extracted `sign`, and the winning condition of the
    extracted `verify`. -/
noncomputable def extGameDist (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int))
    {qH qS : ℕ} (A : Adversary gp M qH qS) : PMF Bool :=
  (PMF.uniformFintype gp.Scalar).bind fun sk =>
    (OracleAdv.run (toOracle (extRealStep gp c sk)) (withVerify (A.run (extPk gp c sk)))
      (Tables.empty, false)).map (extWins gp c (extPk gp c sk))

/-- The EUF-CMA advantage against the extracted functions. -/
noncomputable def extEufcmaAdvantage (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int))
    {qH qS : ℕ} (A : Adversary gp M qH qS) : ℝ≥0∞ :=
  prTrue (liftPMF (extGameDist gp c A)) Heap.empty

/-- **The extracted game is the EUF-CMA game of `SchnorrROM`**, for every value codec on
    which `point_eq` decides equality of encoded group elements. -/
theorem extGameDist_eq (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int))
    (hc : ∀ x y : gp.G, _root_.Schnorr.point_eq (c.enc (.grp x)) (c.enc (.grp y)) =
      decide (x = y))
    {qH qS : ℕ} (A : Adversary gp M qH qS) :
    extGameDist gp c A = gameDist realStep A := by
  unfold extGameDist gameDist
  refine congrArg _ (funext fun sk => ?_)
  have hpk : extPk gp c sk = gp.exp sk := by
    unfold extPk
    have hk := schnorr_keygen_interp gp c (fun _ _ => gp.scalarZero) sk
    dsimp only at hk ⊢
    rw [hk]
    simp
  have hstep : extRealStep gp c sk = realStep sk := by
    funext s q
    cases q with
    | inl k => rfl
    | inr m =>
      simp only [extRealStep, realStep]
      congr 2
      funext r e
      exact extSignOut_eq gp c sk s.1 s.2 m r e
  have hwins : extWins gp c (gp.exp sk) = wins (gp.exp sk) := by
    funext y
    unfold extWins wins
    cases y.2.1.lookup (y.1.2.1, y.1.1) with
    | none => rfl
    | some e =>
      have hv := schnorr_verify_interp gp c hc (fun _ _ => e) (gp.exp sk) y.1.2.1 y.1.2.2 y.1.1
      dsimp only at hv ⊢
      rw [hv]
  rw [hpk, hstep, hwins]

/-- The advantage against the extracted functions is `SchnorrROM.eufcmaAdvantage`. -/
theorem extEufcmaAdvantage_eq (c : Codec (AlgVal gp.G gp.Scalar Unit M) (Array Int))
    (hc : ∀ x y : gp.G, _root_.Schnorr.point_eq (c.enc (.grp x)) (c.enc (.grp y)) =
      decide (x = y))
    {qH qS : ℕ} (A : Adversary gp M qH qS) :
    extEufcmaAdvantage gp c A = SchnorrROM.eufcmaAdvantage A := by
  unfold extEufcmaAdvantage SchnorrROM.eufcmaAdvantage SchnorrROM.eufcmaGame
  rw [extGameDist_eq gp c hc A]

/-- **EUF-CMA security of the extracted Schnorr signatures in the random-oracle model.**
    For every adversary `A` making at most `qH` hash queries and `qS` signing queries
    against the extracted `keygen`, `sign` and `verify` under `schnorrCodec`, with
    `ε' = extEufcmaAdvantage A − qS·(qH + 1 + qS)/|Scalar|`,
    `ε'·(ε'/(qH + 1) − 1/|Scalar|) ≤ DL_Advantage gp (dlReduction A)`. -/
theorem schnorr_extracted_rom_eufcma (cS : Codec gp.Scalar (Array Int))
    (cM : Codec M (Array Int)) {qH qS : ℕ} (A : Adversary gp M qH qS) :
    (extEufcmaAdvantage gp (schnorrCodec gp cS cM) A -
        ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) / Fintype.card gp.Scalar) *
        ((extEufcmaAdvantage gp (schnorrCodec gp cS cM) A -
            ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) / Fintype.card gp.Scalar) /
            ((qH + 1 : ℕ) : ℝ≥0∞) - 1 / Fintype.card gp.Scalar) ≤
      DL_Advantage gp (dlReduction A) := by
  rw [extEufcmaAdvantage_eq gp _ (schnorrCodec_point_eq gp cS cM) A]
  exact schnorr_rom_eufcma A

/-- **Time of the reduction of `schnorr_extracted_rom_eufcma`.** For a costed adversary `A'`
    whose erasure is `FiatShamirROM.toGeneric A` and whose time is at most `T` on every
    public key, and for `tV` a bound of the derived verifier step at the cost companion
    `vkeyCost` (`FiatShamirROM.Protocol.VerifyCostLe`), the costed form `dlReduction.timed`
    erases, under any oracle and read by `dlOfWitness`, to `dlReduction A`, and has time at
    most `2 * (T + (2 * tV + 1) + ((tH + tF + 1) * (qH + 1) + (tS + 1) * qS)) + tExt` on
    every public key. -/
theorem schnorr_extracted_rom_eufcma_reduction_time {qH qS : ℕ} (A : Adversary gp M qH qS)
    (A' : gp.G → OracleAdv.Timed (FiatShamirROM.Query (FiatShamirROM.schnorrSigma gp) M)
      (FiatShamirROM.Answer (FiatShamirROM.schnorrSigma gp))
      (FiatShamirROM.Forgery (FiatShamirROM.schnorrSigma gp) M))
    (hA : ∀ x, (A' x).erase = (FiatShamirROM.toGeneric A).run x)
    (vkeyCost : ((FiatShamirROM.schnorrSigma gp).toProtocol M).VkeyCost) (tV : ℕ)
    (hV : ((FiatShamirROM.schnorrSigma gp).toProtocol M).VerifyCostLe vkeyCost tV)
    (tH tS tF tExt : ℕ) {T : ℕ} (hT : ∀ x, (A' x).TimeBound T) {U : Type}
    (O' : U → Empty → PMF (Empty × U)) (u : U) :
    FiatShamirROM.dlOfWitness gp (fun pk =>
        (OracleAdv.run O' (dlReduction.timed vkeyCost tH tS tF tExt A' pk).2.erase u).map
          Prod.fst) = dlReduction A ∧
      ∀ pk, OracleAdv.Timed.StepTimeBound (dlReduction.timed vkeyCost tH tS tF tExt A' pk)
        (2 * (T + (2 * tV + 1) + ((tH + tF + 1) * (qH + 1) + (tS + 1) * qS)) + tExt) :=
  ⟨dlReduction.run_erase_timed A A' hA vkeyCost tH tS tF tExt O' u,
    dlReduction.timeBound_timed A hA vkeyCost tV hV tH tS tF tExt hT⟩

end Game

end CatCrypt.Crypto.Schnorr.SurfaceDeps
