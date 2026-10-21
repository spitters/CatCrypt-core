/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SigmaProtocol.Extraction.Sigma_haxpipe
public import CatCryptCore.Crypto.SigmaProtocol.Extraction.SigmaProofs_haxpipe
public import CatCryptCore.Crypto.Ristretto255.Param
public import CatCryptCore.Hax.FoldRange
public import CatCryptCore.Crypto.FiatShamirROM.DuplexSpongeNIZK
import CatCryptCore.Tactics.AutoDispatchExt
public import Mathlib.Data.ZMod.Basic

/-!
# Sigma Protocol: the extracted Schnorr proof under a group interpretation

`Extraction/Sigma_haxpipe.lean` is the haxpipeT extraction of the crate `sigma-hax`:
a Fiat–Shamir Schnorr proof (`prove`, `verify`, `simulate`) and its interactive
typestate prover (`Init_send_commitment`, `AwaitingChallenge_recv_challenge`,
`run_sigma`), over 32-byte values and the operations of the class
`Sigma.SigmaDeps`.

A `SigmaGroupModel S P` interprets those operations in a module `P` over a
commutative ring `S`: scalars decode to `S`, group elements to `P`, `group_mul`
is the scalar action, `group_add` the group law, and the scalar operations the
ring operations. `modelSigmaDeps` is the `SigmaDeps` instance of a model, and
`defaultSigmaDeps` that of `zmodModel`, the cyclic group of the Ristretto255
order `ℓ` with generator `1`.

## Main results

* `run_sigma_eq_prove` — for every `SigmaDeps`, the typestate prover answering the
  Fiat–Shamir challenge produces the proof of `prove`
* `prove_verify` — completeness of the extracted code: under every group model,
  `verify` accepts the proof that `prove` builds from a witness `w` for the
  statement `w • g`
* `simulate_verify` — under every group model, the transcript of `simulate`
  satisfies the verification equation, and `verify` accepts it whenever the hash
  of the statement and simulated commitment is the chosen challenge (the
  programmed random oracle)

## The `sigma-proofs` extraction

`Extraction/SigmaProofs_haxpipe.lean` is the haxpipeT extraction of the crate
`sigma-proofs-hax`: Σ-protocols for linear relations over byte-encoded scalars and group
elements and the operations of the class `SigmaProofs.SigmaProofsDeps`. A
`GroupEncoding gp` gives encodings of the scalars and elements of a core `GroupParam`
with decodings that invert them; `groupSigmaProofsDeps` interprets the operations in `gp`,
and `defaultSigmaProofsDeps` is its instance at ristretto255 (`RistrettoParam`) with
32-byte little-endian encodings. `decodeRel` decodes an extracted instance to a core
`LinearRelation`, with a weighted element per term, since extracted terms carry
coefficients and core terms do not.

* `Instance_map_eq`, `Instance_prover_commit_eq`, `Instance_prover_response_eq`,
  `Instance_simulate_commitment_eq`, `Instance_simulate_response_eq`,
  `Instance_verifier_ok_iff`, `extCompact_ok_iff` — on a well-formed instance the
  extracted map, prover, simulator and verifiers are the components of `linearSigma`
  and `linearCompactVerify` of the decoded relation
* `compute_image_eq`, `Instance_new_image` — the image built by `Instance_new`
* `validate_scalar_lt`, `Instance_new_wellFormed` — an instance built by `Instance_new`
  is well formed
* `validate_ok_iff_checks` — on equations with one image term each and indices in the
  `u32` range, `validate` succeeds with `n` scalars exactly when its ten checks hold
* `validate_ok_iff`, `Instance_new_ok_iff` — on equations in the core layout (one image
  term, coefficients one), `validate` and `Instance_new` succeed with `n` scalars exactly
  when the counts are at most `U32_MAX` and the relation `layoutRel` satisfies the draft's
  `LinearRelation.ValidateInstance` with `n` scalars
* `extSigma_eq` — the Σ-protocol of the extracted functions is `linearSigma` of the
  decoded relations; with `extSigma_complete`, `extSigma_specialSound`,
  `extSigma_perfectHVZK`, `extSigma_ksExtractProb_ge`, `extSigma_zkReal_le_zkSim`,
  `extSigma_dsKsExtractProb_ge` and `extSigma_dsZkReal_le_zkSim`, the strong
  Fiat–Shamir and duplex-sponge proofs whose prover and verifier are the extracted
  functions are knowledge sound and zero knowledge

## Statements not carried by this file

The UC statement over `PureSigmaCrypto` (`sigma_hax_uc_secure`,
`sigma_hax_uc_bound_mono`, `pureSigma_shvzk`) restated `sigma_uc_zk_secure` for an
arbitrary protocol and never referred to the extracted functions; it is removed,
and the facts above about `prove`, `verify` and `simulate` replace it. A security
theorem over the extraction needs the zero-knowledge of the Fiat–Shamir proof in
the random-oracle model with a programmed oracle, which the extraction's
non-interactive `prove` requires and the interactive `sigma_uc_zk_secure` does
not provide.

The modules `HaxTypesNIZK.lean` and `Linear_Sigma_haxpipe.lean` are removed. They
stated UC theorems for an arbitrary `SigmaProtocol` with SHVZK, and their surface
fields `f_schnorr_prove` and `f_schnorr_verify_algebraic` were unconstrained, with
correspondence theorems of the form `f = f`. The extraction they named
(`sigma_proofs.lean` of verified-dalek) is not part of this workspace's build, so
no statement about its functions can be made here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SigmaProtocol.SurfaceDeps

/-- The ghost record of the typestate FSM (`SigmaGhost` in
    `sigma-hax/src/typestate_fsm.rs`): the ghost state is the ordered trace
    of communication actions. Each hook appends the header `[kind, tag, n]`
    followed by the `n` payload entries, with `kind` `0` for `send_msg` (tag
    `0`) and `2` for `event`. -/
def sigmaGhostRecord (kind : Int) (ghost : Array Int) (tag : Int) (payload : Array Int) :
    Array Int :=
  ghost ++ #[kind, tag, payload.size] ++ payload

/-! ## Group models -/

/-- A group interpretation of the operations of `Sigma.SigmaDeps`: scalars encode
elements of the commutative ring `S`, group elements encode elements of the
`S`-module `P`, with generator `g`. Decoding inverts encoding, and the all-zero
32-byte value decodes to the zero scalar. `hash` is the Fiat–Shamir hash on encoded
values. -/
structure SigmaGroupModel (S P : Type) [CommRing S] [AddCommGroup P] [Module S P] where
  /-- The generator. -/
  g : P
  /-- Encoding of scalars. -/
  encS : S → Array Int
  /-- Decoding of scalars. -/
  decS : Array Int → S
  /-- Encoding of group elements. -/
  encP : P → Array Int
  /-- Decoding of group elements. -/
  decP : Array Int → P
  /-- The Fiat–Shamir hash of a statement and a commitment. -/
  hash : Array Int → Array Int → Array Int
  decS_encS : ∀ s, decS (encS s) = s
  decP_encP : ∀ p, decP (encP p) = p
  decS_zero : decS (Hax.repeat_ (0 : Int) (32 : Int)) = 0

variable {S P : Type} [CommRing S] [AddCommGroup P] [Module S P]

/-- The `SigmaDeps` instance of a group model: `group_mul` is the scalar action,
`group_add` the group law, the scalar operations are those of the ring, each on
decoded arguments with an encoded result. The ghost hooks append to the trace
(`sigmaGhostRecord`). -/
@[instance_reducible]
def modelSigmaDeps (M : SigmaGroupModel S P) : Sigma.SigmaDeps where
  group_mul a b := M.encP (M.decS a • M.decP b)
  generator := M.encP M.g
  hash_challenge := M.hash
  scalar_mul a b := M.encS (M.decS a * M.decS b)
  scalar_add a b := M.encS (M.decS a + M.decS b)
  group_add a b := M.encP (M.decP a + M.decP b)
  scalar_sub a b := M.encS (M.decS a - M.decS b)
  event := sigmaGhostRecord 2
  send_msg ghost msg := sigmaGhostRecord 0 ghost 0 msg

section ModelOps

variable (M : SigmaGroupModel S P) (a b : Array Int)

@[simp] theorem modelSigmaDeps_group_mul :
    @Sigma.group_mul (modelSigmaDeps M) a b = M.encP (M.decS a • M.decP b) := rfl

@[simp] theorem modelSigmaDeps_generator :
    @Sigma.generator (modelSigmaDeps M) = M.encP M.g := rfl

@[simp] theorem modelSigmaDeps_hash_challenge :
    @Sigma.hash_challenge (modelSigmaDeps M) a b = M.hash a b := rfl

@[simp] theorem modelSigmaDeps_scalar_mul :
    @Sigma.scalar_mul (modelSigmaDeps M) a b = M.encS (M.decS a * M.decS b) := rfl

@[simp] theorem modelSigmaDeps_scalar_add :
    @Sigma.scalar_add (modelSigmaDeps M) a b = M.encS (M.decS a + M.decS b) := rfl

@[simp] theorem modelSigmaDeps_scalar_sub :
    @Sigma.scalar_sub (modelSigmaDeps M) a b = M.encS (M.decS a - M.decS b) := rfl

@[simp] theorem modelSigmaDeps_group_add :
    @Sigma.group_add (modelSigmaDeps M) a b = M.encP (M.decP a + M.decP b) := rfl

end ModelOps

/-! ## The extracted comparisons -/

/-- The extracted scalar comparison accepts equal values. -/
theorem scalar_eq_self [Sigma.SigmaDeps] (a : Array Int) : Sigma.scalar_eq a a = true :=
  Hax.foldRange_rel (R := fun b (_ : Unit) => b = true) (fb := fun _ u => u) (ib := ()) rfl
    (fun _ b _ hb => by simp [Hax.bne, hb])

/-- The extracted point comparison accepts equal values. -/
theorem point_eq_self [Sigma.SigmaDeps] (a : Array Int) : Sigma.point_eq a a = true :=
  Hax.foldRange_rel (R := fun b (_ : Unit) => b = true) (fb := fun _ u => u) (ib := ()) rfl
    (fun _ b _ hb => by simp [Hax.bne, hb])

/-! ## Facts about the extracted functions -/

/-- The typestate prover, answering the Fiat–Shamir challenge of the statement and
its commitment, produces the proof of `prove`. -/
theorem run_sigma_eq_prove [Sigma.SigmaDeps] (ghost witness statement nonce : Array Int) :
    (Sigma.run_sigma ghost witness nonce
      (Sigma.hash_challenge statement (Sigma.group_mul nonce Sigma.generator))).1 =
      Sigma.prove witness statement nonce := rfl

/-- Completeness of the extracted proof: under a group model, `verify` accepts the
proof that `prove` builds from the encoded witness `w` and nonce `n` for the
statement `w • g`. -/
theorem prove_verify (M : SigmaGroupModel S P) (w n : S) :
    letI := modelSigmaDeps M
    Sigma.verify (M.encP (w • M.g)) (Sigma.prove (M.encS w) (M.encP (w • M.g)) (M.encS n)) =
      true := by
  simp [Sigma.verify, Sigma.prove, Sigma.SigmaProof, Sigma.«SigmaProof.commitment»,
    Sigma.«.challenge», Sigma.«.response», scalar_eq_self, Hax.beq, M.decS_encS, M.decP_encP,
    add_smul, mul_smul, point_eq_self]

/-- The transcript of the extracted simulator satisfies the verification equation
`z • g = C + c • X`, and `verify` accepts it when the hash of the statement and the
simulated commitment `C` is the chosen challenge `c`. -/
theorem simulate_verify (M : SigmaGroupModel S P) (statement challenge response : Array Int)
    (hhash : M.hash statement
      (@Sigma.simulate (modelSigmaDeps M) statement challenge response).1 = challenge) :
    letI := modelSigmaDeps M
    Sigma.verify statement (Sigma.simulate statement challenge response) = true := by
  simp [Sigma.simulate, Sigma.SigmaProof, Sigma.ZERO_SCALAR, M.decS_encS, M.decP_encP,
    M.decS_zero] at hhash
  simp [Sigma.verify, Sigma.simulate, Sigma.SigmaProof, Sigma.«SigmaProof.commitment»,
    Sigma.«.challenge», Sigma.«.response», Sigma.ZERO_SCALAR, hhash, scalar_eq_self, Hax.beq,
    M.decS_encS, M.decP_encP, M.decS_zero, point_eq_self]

/-! ## The default instance -/

/-- The order `ℓ = 2^252 + 27742317777372353535851937790883648493` of the Ristretto255
group. -/
abbrev ristrettoOrder : ℕ := 2 ^ 252 + 27742317777372353535851937790883648493

instance : NeZero ristrettoOrder := ⟨by decide⟩

/-- The cyclic group `ZMod ℓ` of the Ristretto255 order as a module over itself, with
generator `1`. A value is encoded as the one-entry array of its representative in
`[0, ℓ)` and decoded from its first entry. The hash is the encoded sum of the
decoded arguments; the theorems above hold for every hash. -/
def zmodModel : SigmaGroupModel (ZMod ristrettoOrder) (ZMod ristrettoOrder) where
  g := 1
  encS s := #[(s.val : Int)]
  decS a := ((a.getD 0 0 : Int) : ZMod ristrettoOrder)
  encP s := #[(s.val : Int)]
  decP a := ((a.getD 0 0 : Int) : ZMod ristrettoOrder)
  hash a b := #[((((a.getD 0 0 : Int) : ZMod ristrettoOrder) +
    ((b.getD 0 0 : Int) : ZMod ristrettoOrder)).val : Int)]
  decS_encS s := by simp [Array.getD]
  decP_encP p := by simp [Array.getD]
  decS_zero := by simp [Hax.repeat_]

/-- The `SigmaDeps` instance of the extraction: the group model `zmodModel`. -/
instance defaultSigmaDeps : Sigma.SigmaDeps := modelSigmaDeps zmodModel

/-! ## The `sigma-proofs` extraction over a prime-order group -/

section SigmaProofsBridge

open CatCrypt.Examples CatCrypt.Crypto.FiatShamirROM

/-- Encodings of the scalars and elements of the group `gp` as byte arrays, with
decodings that invert them. -/
structure GroupEncoding (gp : GroupParam) where
  /-- Encoding of scalars. -/
  encS : gp.Scalar → Array Int
  /-- Decoding of scalars. -/
  decS : Array Int → gp.Scalar
  /-- Encoding of group elements. -/
  encG : gp.G → Array Int
  /-- Decoding of group elements. -/
  decG : Array Int → gp.G
  decS_encS : ∀ s, decS (encS s) = s
  decG_encG : ∀ x, decG (encG x) = x

variable {gp : GroupParam} (E : GroupEncoding gp)

/-- The multi-scalar multiplication of `gp` on encoded vectors: the encoding of the product
of `(decG bases[i]) ^ (decS scalars[i])` over `i < scalars.size`, accumulated from the
identity in index order. -/
def groupMsm (scalars bases : Array (Array Int)) : Array Int :=
  Hax.foldRange 0 (Hax.array_len scalars) (E.encG gp.identity) fun i acc =>
    E.encG (gp.groupMul (E.decG acc)
      (gp.groupExp (E.decG (Hax.index bases i)) (E.decS (Hax.index scalars i))))

/-- The row-wise multi-scalar multiplication: entry `j` is `groupMsm` of the scalars and
bases of row `j`. -/
def groupMsmRows (rows : Array (Array (Array Int) × Array (Array Int))) : Array (Array Int) :=
  rows.map fun r => groupMsm E r.1 r.2

/-- The `SigmaProofsDeps` instance of a group with encodings: each operation decodes its
arguments, applies the operation of `gp` and encodes the result; `group_mul s p` is the
power `p ^ s`, `msm` and `msm_vartime` are both `groupMsm`, `msm_rows_vartime` is
`groupMsmRows`, and the comparisons compare decoded values. -/
@[instance_reducible]
def groupSigmaProofsDeps : SigmaProofs.SigmaProofsDeps where
  msm := groupMsm E
  msm_vartime := groupMsm E
  msm_rows_vartime := groupMsmRows E
  identity := E.encG gp.identity
  group_mul s p := E.encG (gp.groupExp (E.decG p) (E.decS s))
  group_add a b := E.encG (gp.groupMul (E.decG a) (E.decG b))
  generator := E.encG gp.generator
  scalar_mul a b := E.encS (gp.scalarMul (E.decS a) (E.decS b))
  group_eq a b := decide (E.decG a = E.decG b)
  scalar_add a b := E.encS (gp.scalarAdd (E.decS a) (E.decS b))
  scalar_sub a b := E.encS (gp.scalarSub (E.decS a) (E.decS b))
  scalar_neg a := E.encS (gp.scalarNeg (E.decS a))
  scalar_zero := E.encS gp.scalarZero
  scalar_one := E.encS gp.scalarOne
  scalar_eq a b := decide (E.decS a = E.decS b)

section Ops

/-! The unfolding lemmas of the fields of `groupSigmaProofsDeps`. -/

variable (a b : Array Int)

@[simp] theorem groupSigmaProofsDeps_identity :
    @SigmaProofs.SigmaProofsDeps.identity (groupSigmaProofsDeps E) = E.encG gp.identity := rfl

@[simp] theorem groupSigmaProofsDeps_generator :
    @SigmaProofs.SigmaProofsDeps.generator (groupSigmaProofsDeps E) = E.encG gp.generator := rfl

@[simp] theorem groupSigmaProofsDeps_group_mul :
    @SigmaProofs.SigmaProofsDeps.group_mul (groupSigmaProofsDeps E) a b =
      E.encG (gp.groupExp (E.decG b) (E.decS a)) := rfl

@[simp] theorem groupSigmaProofsDeps_group_add :
    @SigmaProofs.SigmaProofsDeps.group_add (groupSigmaProofsDeps E) a b =
      E.encG (gp.groupMul (E.decG a) (E.decG b)) := rfl

@[simp] theorem groupSigmaProofsDeps_group_eq :
    @SigmaProofs.SigmaProofsDeps.group_eq (groupSigmaProofsDeps E) a b =
      decide (E.decG a = E.decG b) := rfl

@[simp] theorem groupSigmaProofsDeps_scalar_mul :
    @SigmaProofs.SigmaProofsDeps.scalar_mul (groupSigmaProofsDeps E) a b =
      E.encS (gp.scalarMul (E.decS a) (E.decS b)) := rfl

@[simp] theorem groupSigmaProofsDeps_scalar_add :
    @SigmaProofs.SigmaProofsDeps.scalar_add (groupSigmaProofsDeps E) a b =
      E.encS (gp.scalarAdd (E.decS a) (E.decS b)) := rfl

@[simp] theorem groupSigmaProofsDeps_scalar_sub :
    @SigmaProofs.SigmaProofsDeps.scalar_sub (groupSigmaProofsDeps E) a b =
      E.encS (gp.scalarSub (E.decS a) (E.decS b)) := rfl

@[simp] theorem groupSigmaProofsDeps_scalar_neg :
    @SigmaProofs.SigmaProofsDeps.scalar_neg (groupSigmaProofsDeps E) a =
      E.encS (gp.scalarNeg (E.decS a)) := rfl

@[simp] theorem groupSigmaProofsDeps_scalar_zero :
    @SigmaProofs.SigmaProofsDeps.scalar_zero (groupSigmaProofsDeps E) = E.encS gp.scalarZero :=
  rfl

@[simp] theorem groupSigmaProofsDeps_scalar_one :
    @SigmaProofs.SigmaProofsDeps.scalar_one (groupSigmaProofsDeps E) = E.encS gp.scalarOne :=
  rfl

@[simp] theorem groupSigmaProofsDeps_scalar_eq :
    @SigmaProofs.SigmaProofsDeps.scalar_eq (groupSigmaProofsDeps E) a b =
      decide (E.decS a = E.decS b) := rfl

@[simp] theorem groupSigmaProofsDeps_msm (sc bs : Array (Array Int)) :
    @SigmaProofs.SigmaProofsDeps.msm (groupSigmaProofsDeps E) sc bs = groupMsm E sc bs := rfl

@[simp] theorem groupSigmaProofsDeps_msm_vartime (sc bs : Array (Array Int)) :
    @SigmaProofs.SigmaProofsDeps.msm_vartime (groupSigmaProofsDeps E) sc bs =
      groupMsm E sc bs := rfl

@[simp] theorem groupSigmaProofsDeps_msm_rows_vartime
    (rows : Array (Array (Array Int) × Array (Array Int))) :
    @SigmaProofs.SigmaProofsDeps.msm_rows_vartime (groupSigmaProofsDeps E) rows =
      groupMsmRows E rows := rfl

/-- The row-wise multi-scalar multiplication of an array of rows given by `f` is the array
of the `msm_vartime` of each row. -/
theorem msm_rows_vartime_ofFn {N : ℕ} (f : Fin N → Array (Array Int) × Array (Array Int)) :
    @SigmaProofs.SigmaProofsDeps.msm_rows_vartime (groupSigmaProofsDeps E) (Array.ofFn f) =
      Array.ofFn fun j =>
        @SigmaProofs.SigmaProofsDeps.msm_vartime (groupSigmaProofsDeps E) (f j).1 (f j).2 := by
  simp [groupMsmRows, Array.map_ofFn, Function.comp_def]

end Ops

/-! ### Vectors of scalars and elements -/

/-- The index read at the `usize` cast of `x`. -/
def uidx (x : Int) : ℕ := (Hax.castVal_w Hax.usizeBits x).toNat

/-- The encoding of a vector of scalars. -/
def encVec {k : ℕ} (v : Fin k → gp.Scalar) : Array (Array Int) := Array.ofFn fun j => E.encS (v j)

@[simp] theorem size_encVec {k : ℕ} (v : Fin k → gp.Scalar) : (encVec E v).size = k := by
  simp [encVec]

/-- The decoding of an array of scalars as a vector of length `k`. -/
def decVec (k : ℕ) (a : Array (Array Int)) : Fin k → gp.Scalar := fun j => E.decS (Hax.index a j)

/-- The encoding of a vector of group elements. -/
def encCom {k : ℕ} (a : Fin k → gp.G) : Array (Array Int) := Array.ofFn fun j => E.encG (a j)

/-- The decoding of an array of group elements as a vector of length `k`. -/
def decCom (k : ℕ) (a : Array (Array Int)) : Fin k → gp.G := fun j => E.decG (Hax.index a j)

theorem index_ofFn {α : Type} [Inhabited α] {k : ℕ} (f : Fin k → α) (j : ℕ) (h : j < k) :
    Hax.index (Array.ofFn f) (j : Int) = f ⟨j, h⟩ := by
  grind only [Hax.index_natCast, Array.size_ofFn, Array.getElem_ofFn]

theorem index_castVal_ofFn {α : Type} [Inhabited α] {k : ℕ} (f : Fin k → α) (x : Int)
    (h : uidx x < k) : Hax.index (Array.ofFn f) (Hax.castVal_w Hax.usizeBits x) = f ⟨uidx x, h⟩ := by
  grind only [Hax.index_eq_getElem, uidx.eq_def, Array.size_ofFn, Array.getElem_ofFn]

@[simp] theorem decVec_encVec {k : ℕ} (v : Fin k → gp.Scalar) : decVec E k (encVec E v) = v := by
  funext j
  simp [decVec, encVec, index_ofFn _ _ j.isLt, E.decS_encS]

@[simp] theorem decCom_encCom {k : ℕ} (a : Fin k → gp.G) : decCom E k (encCom E a) = a := by
  funext j
  simp [decCom, encCom, index_ofFn _ _ j.isLt, E.decG_encG]

/-! ### Loops of the extraction -/

/-- The loop pushing `g j` for `j < N` onto the empty array builds the array of the
`g j`. -/
theorem foldRange_push_ofFn {α : Type} (N : ℕ) (g : Int → α) :
    Hax.foldRange 0 (N : Int) #[] (fun j out => Hax.push out (g j)) =
      Array.ofFn fun j : Fin N => g j := by
  have key := Hax.foldRange_induct (P := fun (i : Int) (acc : Array α) =>
      acc.size = i.toNat ∧ ∀ (j : ℕ) (h : j < acc.size), acc[j] = g j)
    (lo := 0) (hi := (N : Int)) (f := fun j out => Hax.push out (g j)) (init := #[])
    (by omega) (by simp) (by
      intro i a h0 _ ⟨hs, hj⟩
      refine ⟨?_, fun j hj' => ?_⟩
      · simp [Hax.push, hs]; omega
      · simp only [Hax.push, Array.getElem_push]
        split
        · exact hj j _
        · simp [Hax.push] at hj'
          have : j = i.toNat := by omega
          subst this
          simp [Int.toNat_of_nonneg h0])
  refine Array.ext (by simpa using key.1) fun j h1 h2 => ?_
  simp [key.2 j h1]

/-- The loop clearing a flag at every `j < N` with `q j = false` ends with the flag set
exactly when `q j` holds for all `j < N`. -/
theorem foldRange_all (N : ℕ) (q : Int → Bool) :
    Hax.foldRange 0 (N : Int) true
        (fun j acc => if Hax.beq (q j) (0 : Bool) then false else acc) = true ↔
      ∀ j : ℕ, j < N → q j = true := by
  have key := Hax.foldRange_induct (P := fun (i : Int) (acc : Bool) =>
      (acc = true ↔ ∀ j : ℕ, j < i.toNat → q j = true))
    (lo := 0) (hi := (N : Int))
    (f := fun j acc => if Hax.beq (q j) (0 : Bool) then false else acc) (init := true)
    (by omega) (by simp) (by
      intro i a h0 _ ha
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      have hi : ((i.toNat : ℕ) : Int) = i := Int.toNat_of_nonneg h0
      constructor
      · intro h j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · cases hq : q i <;> simp_all [Hax.beq]
        · cases hq : q i <;> simp_all [Hax.beq]
      · intro h
        have hq : q i = true := hi ▸ h i.toNat (Nat.lt_succ_self _)
        simpa [Hax.beq, hq, ha] using fun j hj => h j (Nat.lt_succ_of_lt hj))
  simpa using key

attribute [local instance] GroupParam.scalarCommRing

/-- A loop whose step multiplies an encoded power of the generator by the `k`-th power
`exp (f k)` computes the encoding of `exp` of the sum of the `f k`. -/
theorem foldRange_encG_exp (N : ℕ) (step : Int → Array Int → Array Int) (f : ℕ → gp.Scalar)
    (init : Array Int) (h0 : init = E.encG (gp.exp 0))
    (hs : ∀ k : ℕ, k < N → ∀ s, step k (E.encG (gp.exp s)) = E.encG (gp.exp (s + f k))) :
    Hax.foldRange 0 (N : Int) init step = E.encG (gp.exp (∑ k ∈ Finset.range N, f k)) := by
  have key := Hax.foldRange_induct (P := fun (i : Int) (acc : Array Int) =>
      acc = E.encG (gp.exp (∑ k ∈ Finset.range i.toNat, f k)))
    (lo := 0) (hi := (N : Int)) (f := step) (init := init)
    (by omega) (by simpa using h0) (by
      intro i a h0 hi ha
      have h := hs i.toNat (by omega) (∑ k ∈ Finset.range i.toNat, f k)
      rw [Int.toNat_of_nonneg h0] at h
      rw [ha, show (i + 1).toNat = i.toNat + 1 by omega, Finset.sum_range_succ, h])
  simpa using key

/-- The scalar `∑ k, decS sc[k] · dlog (decG bs[k])` over the indices of `sc`: the discrete
logarithm of the multi-scalar multiplication of `sc` and `bs`. -/
noncomputable def dotVal (sc bs : Array (Array Int)) : gp.Scalar :=
  ∑ k ∈ Finset.range sc.size,
    E.decS (Hax.index sc (k : Int)) * gp.dlog (E.decG (Hax.index bs (k : Int)))

theorem dotVal_push (sc bs : Array (Array Int)) (x y : Array Int) (h : sc.size = bs.size) :
    dotVal E (sc.push x) (bs.push y) = dotVal E sc bs + E.decS x * gp.dlog (E.decG y) := by
  unfold dotVal
  rw [Array.size_push, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk := Finset.mem_range.mp hk
    rw [Hax.index_natCast _ _ (by simp; omega), Hax.index_natCast _ _ (by simp; omega),
      Hax.index_natCast _ _ hk, Hax.index_natCast _ _ (by omega)]
    simp [Array.getElem_push, hk, show k < bs.size by omega]
  · rw [Hax.index_natCast _ _ (by simp), Hax.index_natCast _ _ (by simp [h])]
    simp [Array.getElem_push, h]

/-- The extracted multi-scalar multiplication is the encoded power of the generator to
`dotVal`. -/
theorem msm_eq (sc bs : Array (Array Int)) :
    @SigmaProofs.msm (groupSigmaProofsDeps E) sc bs = E.encG (gp.exp (dotVal E sc bs)) := by
  rw [groupSigmaProofsDeps_msm]
  unfold groupMsm dotVal
  simp only [Hax.array_len]
  apply foldRange_encG_exp
  · exact congrArg E.encG gp.exp_zero.symm
  · intro k _ s
    simp only [E.decG_encG]
    rw [GroupParam.groupMul_eq_exp, GroupParam.dlog_exp, GroupParam.groupExp_eq_exp]
    simp only [GroupParam.scalarMul_eq_mul, GroupParam.scalarAdd_eq_add, mul_comm,
      GroupParam.dlog_exp]

/-- The extracted variable-time multi-scalar multiplication is the encoded power of the
generator to `dotVal`. -/
theorem msm_vartime_eq (sc bs : Array (Array Int)) :
    @SigmaProofs.msm_vartime (groupSigmaProofsDeps E) sc bs =
      E.encG (gp.exp (dotVal E sc bs)) :=
  msm_eq E sc bs

/-- A loop that gathers a scalar vector and a base vector of equal lengths, and whose step
`k` adds `f k` to their `dotVal`, ends with vectors of equal lengths whose `dotVal` is the
sum of the `f k`. -/
theorem foldRange_gather_dot (N : ℕ)
    (step : Int → Array (Array Int) × Array (Array Int) → Array (Array Int) × Array (Array Int))
    (f : ℕ → gp.Scalar)
    (hs : ∀ k : ℕ, k < N → ∀ s b : Array (Array Int), s.size = b.size →
      (step k (s, b)).1.size = (step k (s, b)).2.size ∧
        dotVal E (step k (s, b)).1 (step k (s, b)).2 = dotVal E s b + f k) :
    (Hax.foldRange 0 (N : Int) (#[], #[]) step).1.size =
        (Hax.foldRange 0 (N : Int) (#[], #[]) step).2.size ∧
      dotVal E (Hax.foldRange 0 (N : Int) (#[], #[]) step).1
          (Hax.foldRange 0 (N : Int) (#[], #[]) step).2 = ∑ k ∈ Finset.range N, f k := by
  have key := Hax.foldRange_induct
    (P := fun (i : Int) (p : Array (Array Int) × Array (Array Int)) =>
      p.1.size = p.2.size ∧ dotVal E p.1 p.2 = ∑ k ∈ Finset.range i.toNat, f k)
    (lo := 0) (hi := (N : Int)) (f := step) (init := (#[], #[]))
    (by omega) (by simp [dotVal]) (by
      rintro i ⟨s, b⟩ h0 hi ⟨hsz, hd⟩
      have h := hs i.toNat (by omega) s b hsz
      rw [Int.toNat_of_nonneg h0] at h
      refine ⟨h.1, ?_⟩
      rw [h.2, hd, show (i + 1).toNat = i.toNat + 1 by omega, Finset.sum_range_succ])
  simpa using key

/-! ### Decoding an extracted instance

An extracted `Instance` is a tuple `(elements, equations, image, num_scalars)`. Its
element array is the one of `Instance_new` (draft-irtf-cfrg-sigma-protocols-03 §3.5):
index `0` holds the generator and the statement elements follow. Each equation carries image terms
`(element index, coefficient)` and terms `(scalar index, element index, coefficient)`;
row `i` of the extracted map sends a scalar vector `w` to the product of
`elements[e] ^ (coefficient · w[s])` over its terms. A core `LinearRelation` has no
coefficients, so the decoding lists the weighted elements `elements[e] ^ coefficient`:
the element of index `i < m` is the stored image of equation `i`, and the term `k` of
equation `i` reads the element of index `m + i·K + k`, for the bound `K` on the number
of terms of an equation. -/

/-- An upper bound on the number of terms of an equation of the instance: the total
number of terms. -/
def termBound (inst : SigmaProofs.Instance_T) : ℕ := (inst.2.1.toList.map fun e => e.2.size).sum

/-- The weighted element `elements[e] ^ coefficient` of the term `k` of equation `i`. -/
def termElem (inst : SigmaProofs.Instance_T) (i k : ℕ) : gp.G :=
  gp.groupExp
    (E.decG (Hax.index inst.1
      (Hax.castVal_w Hax.usizeBits (Hax.index (Hax.index inst.2.1 (i : Int)).2 (k : Int)).2.1)))
    (E.decS (Hax.index (Hax.index inst.2.1 (i : Int)).2 (k : Int)).2.2)

/-- The decoded element of index `p` for an instance with `m` equations. -/
def decodeElem (m : ℕ) (inst : SigmaProofs.Instance_T) (p : ℕ) : gp.G :=
  if p < m then E.decG (Hax.index inst.2.2.1 (p : Int))
  else termElem E inst ((p - m) / termBound inst) ((p - m) % termBound inst)

/-- The core linear relation with `n` scalars and `m` equations of an extracted
instance. -/
def decodeRel (n m : ℕ) (inst : SigmaProofs.Instance_T) : LinearRelation gp n m where
  elements := (List.range (m + m * termBound inst)).map (decodeElem E m inst)
  equations i :=
    { lhs := i
      terms := (List.range (Hax.index inst.2.1 ((i : ℕ) : Int)).2.size).map fun k : ℕ =>
        (uidx (Hax.index (Hax.index inst.2.1 ((i : ℕ) : Int)).2 (k : Int)).1,
          (m + (i : ℕ) * termBound inst + k : ℕ)) }

theorem size_le_termBound (inst : SigmaProofs.Instance_T) (i : Int) :
    (Hax.index inst.2.1 i).2.size ≤ termBound inst := by
  unfold Hax.index termBound
  split_ifs
  · exact List.le_sum_of_mem (List.mem_map.mpr ⟨_, Array.getElem_mem_toList _, rfl⟩)
  · exact List.le_sum_of_mem (List.mem_map.mpr ⟨_, Array.getElem_mem_toList _, rfl⟩)
  · exact Nat.zero_le _

theorem term_index_lt (m i k K : ℕ) (hi : i < m) (hk : k < K) : i * K + k < m * K :=
  calc i * K + k < i * K + K := by omega
    _ = (i + 1) * K := by ring
    _ ≤ m * K := Nat.mul_le_mul_right _ hi

theorem decodeRel_elem (n m : ℕ) (inst : SigmaProofs.Instance_T) (p : ℕ)
    (hp : p < m + m * termBound inst) :
    (decodeRel E n m inst).elem p = decodeElem E m inst p := by
  simp [LinearRelation.elem, decodeRel, List.getD_eq_getElem?_getD, hp]

theorem decodeRel_elem_term (n m : ℕ) (inst : SigmaProofs.Instance_T) (i k : ℕ) (hi : i < m)
    (hk : k < (Hax.index inst.2.1 (i : Int)).2.size) :
    (decodeRel E n m inst).elem (m + i * termBound inst + k) = termElem E inst i k := by
  have hK := size_le_termBound inst (i : Int)
  have hlt := term_index_lt m i k (termBound inst) hi (by omega)
  rw [decodeRel_elem E n m inst _ (by omega)]
  have hpos : 0 < termBound inst := by omega
  simp only [decodeElem, show ¬ (m + i * termBound inst + k < m) by omega, if_false,
    show m + i * termBound inst + k - m = k + termBound inst * i by rw [Nat.mul_comm]; omega,
    Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt (by omega : k < termBound inst),
    Nat.mod_eq_of_lt (by omega : k < termBound inst), zero_add]

theorem decodeRel_image (n m : ℕ) (inst : SigmaProofs.Instance_T) (i : Fin m) :
    (decodeRel E n m inst).image i = E.decG (Hax.index inst.2.2.1 (i : Int)) := by
  rw [LinearRelation.image, decodeRel_elem E n m inst _ (by
    have := i.isLt; simp only [decodeRel]; nlinarith)]
  simp [decodeElem, decodeRel]

/-- The indices of the decoded relation are in range exactly when every scalar index of
a term of one of its `m` equations is below `n`. -/
theorem decodeRel_validate_iff (n m : ℕ) (inst : SigmaProofs.Instance_T) :
    (decodeRel E n m inst).IndexValid ↔
      ∀ i : ℕ, i < m → ∀ k : ℕ, k < (Hax.index inst.2.1 (i : Int)).2.size →
        uidx (Hax.index (Hax.index inst.2.1 (i : Int)).2 (k : Int)).1 < n := by
  simp only [LinearRelation.IndexValid, decodeRel, List.length_map, List.length_range,
    List.mem_map, List.mem_range]
  constructor
  · intro h i hi k hk
    exact ((h ⟨i, hi⟩).2 _ ⟨k, hk, rfl⟩).1
  · intro h i
    refine ⟨by nlinarith [i.isLt], ?_⟩
    rintro t ⟨k, hk, rfl⟩
    have hK := size_le_termBound inst ((i : ℕ) : Int)
    exact ⟨h i i.isLt k hk,
      by have := term_index_lt m i k (termBound inst) i.isLt (by omega); omega⟩

/-! ### The extracted map -/

/-- The evaluation pairs of row `i` on an encoded scalar vector are a scalar vector and a
base vector of equal lengths whose `dotVal` is the discrete logarithm of row `i` of the
decoded map, when the scalar indices of the row are in range. -/
theorem Instance_evaluation_pairs_dot (n : ℕ) (inst : SigmaProofs.Instance_T)
    (w : Fin n → gp.Scalar) (i : ℕ)
    (hv : ∀ k : ℕ, k < (Hax.index inst.2.1 (i : Int)).2.size →
      uidx (Hax.index (Hax.index inst.2.1 (i : Int)).2 (k : Int)).1 < n) :
    (@SigmaProofs.Instance_evaluation_pairs (groupSigmaProofsDeps E) inst (i : Int)
        (encVec E w)).1.size =
      (@SigmaProofs.Instance_evaluation_pairs (groupSigmaProofsDeps E) inst (i : Int)
        (encVec E w)).2.size ∧
    dotVal E (@SigmaProofs.Instance_evaluation_pairs (groupSigmaProofsDeps E) inst (i : Int)
        (encVec E w)).1
      (@SigmaProofs.Instance_evaluation_pairs (groupSigmaProofsDeps E) inst (i : Int)
        (encVec E w)).2 =
      ∑ k ∈ Finset.range (Hax.index inst.2.1 (i : Int)).2.size,
        gp.scalarMul (gp.dlog (termElem E inst i k))
          (vecGet w (uidx (Hax.index (Hax.index inst.2.1 (i : Int)).2 (k : Int)).1)) := by
  unfold SigmaProofs.Instance_evaluation_pairs
  simp only [SigmaProofs.«.equations», SigmaProofs.«Equation.terms», SigmaProofs.«.elements»,
    Hax.array_len]
  apply foldRange_gather_dot
  intro k hk s b hsb
  simp only [Hax.push]
  refine ⟨by simp [hsb], ?_⟩
  rw [dotVal_push E _ _ _ _ hsb, encVec, index_castVal_ofFn _ _ (hv k hk)]
  simp only [groupSigmaProofsDeps_scalar_mul, E.decS_encS, termElem, vecGet, dif_pos (hv k hk)]
  congr 1
  rw [GroupParam.groupExp_eq_exp, GroupParam.dlog_exp]
  simp only [GroupParam.scalarMul_eq_mul]
  ring

/-- Row `i` of the extracted linear map on an encoded scalar vector is the encoding of
row `i` of the map of the decoded relation, when the scalar indices of the row are in
range. -/
theorem Instance_map_row_eq (n m : ℕ) (inst : SigmaProofs.Instance_T) (w : Fin n → gp.Scalar)
    (i : ℕ) (hi : i < m)
    (hv : ∀ k : ℕ, k < (Hax.index inst.2.1 (i : Int)).2.size →
      uidx (Hax.index (Hax.index inst.2.1 (i : Int)).2 (k : Int)).1 < n) :
    @SigmaProofs.Instance_map_row (groupSigmaProofsDeps E) inst (i : Int) (encVec E w) =
      E.encG ((decodeRel E n m inst).map w ⟨i, hi⟩) := by
  rw [LinearRelation.map_eq_exp]
  have hlin : (decodeRel E n m inst).lin w ⟨i, hi⟩ =
      ∑ k ∈ Finset.range (Hax.index inst.2.1 (i : Int)).2.size,
        gp.scalarMul (gp.dlog (termElem E inst i k))
          (vecGet w (uidx (Hax.index (Hax.index inst.2.1 (i : Int)).2 (k : Int)).1)) := by
    simp only [LinearRelation.lin, decodeRel, List.map_map]
    show List.sum _ = _
    simp only [Finset.sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]
    congr 1
    apply List.map_congr_left
    intro k hk
    exact congrArg₂ _ (congrArg _ (decodeRel_elem_term E n m inst i k hi (List.mem_range.mp hk)))
      rfl
  rw [hlin]
  unfold SigmaProofs.Instance_map_row
  have hd := (Instance_evaluation_pairs_dot E n inst w i hv).2
  generalize @SigmaProofs.Instance_evaluation_pairs (groupSigmaProofsDeps E) inst (i : Int)
    (encVec E w) = p at hd ⊢
  obtain ⟨v, b⟩ := p
  dsimp only at hd ⊢
  rw [msm_eq, Hax.deref, Hax.deref, hd]

/-- An extracted instance with `n` scalars and `m` equations whose decoded relation has
its indices in range. -/
def WellFormed (n m : ℕ) (inst : SigmaProofs.Instance_T) : Prop :=
  inst.2.2.2 = (n : Int) ∧ inst.2.1.size = m ∧ (decodeRel E n m inst).IndexValid

instance (n m : ℕ) (inst : SigmaProofs.Instance_T) : Decidable (WellFormed E n m inst) := by
  unfold WellFormed; infer_instance

variable {E}

/-- The extracted linear map on an encoded scalar vector is the encoding of the map of
the decoded relation. -/
theorem Instance_map_eq {n m : ℕ} {inst : SigmaProofs.Instance_T} (h : WellFormed E n m inst)
    (w : Fin n → gp.Scalar) :
    @SigmaProofs.Instance_map (groupSigmaProofsDeps E) inst (encVec E w) =
      encCom E ((decodeRel E n m inst).map w) := by
  unfold SigmaProofs.Instance_map
  simp only [SigmaProofs.«.equations», Hax.array_len, h.2.1]
  rw [foldRange_push_ofFn]
  unfold encCom
  congr 1
  funext j
  exact Instance_map_row_eq E n m inst w j j.isLt
    ((decodeRel_validate_iff E n m inst).mp h.2.2 j j.isLt)

/-- The extracted copy of an array of scalars is the array. -/
theorem copy_scalars_eq [SigmaProofs.SigmaProofsDeps] (xs : Array (Array Int)) :
    SigmaProofs.copy_scalars xs = xs := by
  unfold SigmaProofs.copy_scalars
  simp only [Hax.array_len]
  rw [foldRange_push_ofFn]
  refine Array.ext (by simp) fun j h1 h2 => ?_
  simp [Hax.index_natCast]

/-- The extracted prover commitment on encoded witness and nonces is the encoding of the
map of the nonces, with the prover state holding the nonces and the witness. -/
theorem Instance_prover_commit_eq {n m : ℕ} {inst : SigmaProofs.Instance_T}
    (h : WellFormed E n m inst) (w r : Fin n → gp.Scalar) :
    @SigmaProofs.Instance_prover_commit (groupSigmaProofsDeps E) inst (encVec E w) (encVec E r) =
      .ok (encCom E ((decodeRel E n m inst).map r), (encVec E r, encVec E w)) := by
  unfold SigmaProofs.Instance_prover_commit
  simp [SigmaProofs.«Instance.num_scalars», Hax.bne, Hax.bor, Hax.array_len, h.1, size_encVec,
    Instance_map_eq h, copy_scalars_eq, SigmaProofs.ProverState]

/-- The extracted prover response on the state of nonces `r` and witness `w` and the
challenge `c` is the encoding of `r + c·w`. -/
theorem Instance_prover_response_eq {n m : ℕ} {inst : SigmaProofs.Instance_T}
    (h : WellFormed E n m inst) (w r : Fin n → gp.Scalar) (c : gp.Scalar) :
    @SigmaProofs.Instance_prover_response (groupSigmaProofsDeps E) inst (encVec E r, encVec E w)
        (E.encS c) =
      .ok (encVec E fun j => gp.scalarAdd (r j) (gp.scalarMul c (w j))) := by
  unfold SigmaProofs.Instance_prover_response
  simp only [SigmaProofs.«Instance.num_scalars», SigmaProofs.«.witness», SigmaProofs.«.nonces»,
    Hax.bne, Hax.bor, Hax.array_len, h.1, size_encVec, beq_self_eq_true, Bool.not_true,
    Bool.or_self, Bool.false_eq_true, if_false, groupSigmaProofsDeps_scalar_add,
    groupSigmaProofsDeps_scalar_mul]
  rw [foldRange_push_ofFn]
  unfold encVec
  congr 2
  funext j
  rw [index_ofFn _ _ j.isLt, index_ofFn _ _ j.isLt]
  simp only [E.decS_encS, gp.scalarMul_comm]

/-- The extracted simulated commitment is the encoding of the commitment `simCommit` of the
decoded relation, `map z · image^(−c)`. -/
theorem Instance_simulate_commitment_eq {n m : ℕ} {inst : SigmaProofs.Instance_T}
    (h : WellFormed E n m inst) (c : gp.Scalar) (z : Fin n → gp.Scalar) :
    @SigmaProofs.Instance_simulate_commitment (groupSigmaProofsDeps E) inst (E.encS c)
        (encVec E z) =
      .ok (encCom E ((decodeRel E n m inst).simCommit c z)) := by
  unfold SigmaProofs.Instance_simulate_commitment
  simp only [SigmaProofs.«Instance.num_scalars», SigmaProofs.«.equations»,
    SigmaProofs.«Instance.image», Hax.bne, Hax.array_len, h.1, h.2.1, size_encVec,
    beq_self_eq_true, Bool.not_true, Bool.false_eq_true, if_false,
    groupSigmaProofsDeps_scalar_neg]
  rw [foldRange_push_ofFn, Hax.deref, msm_rows_vartime_ofFn]
  unfold encCom
  congr 2
  funext j
  have hv := (decodeRel_validate_iff E n m inst).mp h.2.2 j j.isLt
  have hsz := (Instance_evaluation_pairs_dot E n inst z j hv).1
  have hrow := Instance_map_row_eq E n m inst z j j.isLt hv
  unfold SigmaProofs.Instance_map_row at hrow
  generalize @SigmaProofs.Instance_evaluation_pairs (groupSigmaProofsDeps E) inst
    ((j : ℕ) : Int) (encVec E z) = p at hsz hrow ⊢
  obtain ⟨v, b⟩ := p
  dsimp only at hsz hrow ⊢
  rw [msm_eq, Hax.deref, Hax.deref] at hrow
  have hmap := congrArg E.decG hrow
  rw [E.decG_encG, E.decG_encG] at hmap
  rw [msm_vartime_eq]
  simp only [Hax.push]
  rw [dotVal_push E _ _ _ _ hsz]
  simp only [E.decS_encS, LinearRelation.simCommit, decodeRel_image, gp.groupInv_groupExp]
  rw [show (decodeRel E n m inst).map z j = gp.exp (dotVal E v b) from hmap.symm,
    GroupParam.groupExp_eq_exp, GroupParam.groupMul_eq_exp, GroupParam.dlog_exp,
    GroupParam.dlog_exp]
  simp only [GroupParam.scalarMul_eq_mul, GroupParam.scalarAdd_eq_add, mul_comm]

/-- The extracted simulated response is the simulator randomness. -/
theorem Instance_simulate_response_eq {n m : ℕ} {inst : SigmaProofs.Instance_T}
    (h : WellFormed E n m inst) (z : Fin n → gp.Scalar) :
    @SigmaProofs.Instance_simulate_response (groupSigmaProofsDeps E) inst (encVec E z) =
      .ok (encVec E z) := by
  unfold SigmaProofs.Instance_simulate_response
  simp [SigmaProofs.«Instance.num_scalars», Hax.bne, Hax.array_len, h.1, copy_scalars_eq,
    size_encVec]

/-- The extracted verifier accepts a commitment array `a`, the challenge `c` and the
response `z` exactly when `a` holds `m` elements whose decoding is the commitment
`simCommit c z` of the decoded relation. -/
theorem Instance_verifier_ok_iff {n m : ℕ} {inst : SigmaProofs.Instance_T}
    (h : WellFormed E n m inst) (a : Array (Array Int)) (c : gp.Scalar) (z : Fin n → gp.Scalar) :
    @SigmaProofs.Instance_verifier (groupSigmaProofsDeps E) inst a (E.encS c) (encVec E z) =
        .ok () ↔
      a.size = m ∧ decCom E m a = (decodeRel E n m inst).simCommit c z := by
  unfold SigmaProofs.Instance_verifier
  rw [Instance_simulate_commitment_eq h]
  by_cases ha : a.size = m
  · have hsz : (encCom E ((decodeRel E n m inst).simCommit c z)).size = m := by simp [encCom]
    have hall := foldRange_all m (fun j => @SigmaProofs.SigmaProofsDeps.group_eq
      (groupSigmaProofsDeps E) (Hax.index (encCom E ((decodeRel E n m inst).simCommit c z)) j)
      (Hax.index a j))
    simp only [SigmaProofs.«Instance.num_scalars», SigmaProofs.«.equations», Hax.array_len, h.1,
      h.2.1, ha, size_encVec, hsz, Hax.bne, Hax.bor, beq_self_eq_true, Bool.not_true,
      Bool.or_self, Bool.false_eq_true, if_false]
    generalize Hax.foldRange _ _ _ _ = F at hall ⊢
    have key : decCom E m a = (decodeRel E n m inst).simCommit c z ↔ F = true := by
      rw [hall, funext_iff]
      refine ⟨fun hc j hj => ?_, fun hc j => ?_⟩
      · have := hc ⟨j, hj⟩
        simp_all [encCom, decCom, index_ofFn, E.decG_encG]
      · have := hc j j.isLt
        simp_all [encCom, decCom, index_ofFn, E.decG_encG]
    rw [key]
    cases F <;> simp
  · simp [SigmaProofs.«Instance.num_scalars», SigmaProofs.«.equations», Hax.array_len, h.1,
      h.2.1, ha, Hax.bne, Hax.bor]

/-- The extracted compact acceptance test accepts exactly equal decoded challenges. -/
theorem compact_accept_ok_iff (c e : Array Int) :
    @SigmaProofs.compact_accept (groupSigmaProofsDeps E) c e = .ok () ↔ E.decS c = E.decS e := by
  unfold SigmaProofs.compact_accept
  by_cases hce : E.decS c = E.decS e <;> simp [hce]

/-! ### The image computed by `Instance_new` -/

variable (E) in
/-- The image of equation `j` over the element array `els`: the product of
`els[e] ^ coefficient` over its image terms `(e, coefficient)`. -/
def imageComb (els : Array (Array Int))
    (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))) (j : ℕ) : gp.G :=
  ((List.range (Hax.index eqs (j : Int)).1.size).map fun k : ℕ =>
      gp.groupExp
        (E.decG (Hax.index els
          (Hax.castVal_w Hax.usizeBits (Hax.index (Hax.index eqs (j : Int)).1 (k : Int)).1)))
        (E.decS (Hax.index (Hax.index eqs (j : Int)).1 (k : Int)).2)).foldr
    gp.groupMul gp.identity

theorem foldr_groupMul_eq_exp (l : List gp.G) :
    l.foldr gp.groupMul gp.identity = gp.exp (l.map gp.dlog).sum := by
  induction l with
  | nil => exact gp.exp_zero.symm
  | cons a l ih =>
    rw [List.foldr_cons, ih, GroupParam.groupMul_eq_exp, GroupParam.dlog_exp]
    rfl

/-- The extracted image entry of an equation is the encoded power of the generator to the
sum of `decS coefficient · dlog els[e]` over its image terms `(e, coefficient)`. -/
theorem image_entry_dot (els : Array (Array Int))
    (eq : (Array (Int × Array Int)) × (Array (Int × Int × Array Int))) :
    @SigmaProofs.image_entry (groupSigmaProofsDeps E) els eq =
      E.encG (gp.exp (∑ k ∈ Finset.range eq.1.size,
        E.decS (Hax.index eq.1 (k : Int)).2 *
          gp.dlog (E.decG (Hax.index els
            (Hax.castVal_w Hax.usizeBits (Hax.index eq.1 (k : Int)).1))))) := by
  unfold SigmaProofs.image_entry
  simp only [SigmaProofs.«Equation.image», Hax.array_len]
  rw [msm_vartime_eq, Hax.deref, Hax.deref]
  congr 2
  refine (foldRange_gather_dot E _ _ _ fun k _ s b hsb => ?_).2
  simp only [Hax.push]
  exact ⟨by simp [hsb], dotVal_push E _ _ _ _ hsb⟩

/-- The decoded extracted column entry of an equation for the scalar index `q` is `exp` of
the sum of `decS coefficient · dlog els[e]` over its terms `(q, e, coefficient)`. -/
theorem column_entry_dot (els : Array (Array Int))
    (eq : (Array (Int × Array Int)) × (Array (Int × Int × Array Int))) (q : Int) :
    @SigmaProofs.column_entry (groupSigmaProofsDeps E) els eq q =
      E.encG (gp.exp (∑ k ∈ Finset.range eq.2.size,
        if (Hax.index eq.2 (k : Int)).1 = q then
          E.decS (Hax.index eq.2 (k : Int)).2.2 *
            gp.dlog (E.decG (Hax.index els
              (Hax.castVal_w Hax.usizeBits (Hax.index eq.2 (k : Int)).2.1)))
        else 0)) := by
  unfold SigmaProofs.column_entry
  simp only [Hax.array_len]
  rw [msm_vartime_eq, Hax.deref, Hax.deref]
  congr 2
  refine (foldRange_gather_dot E _ _ _ fun k _ s b hsb => ?_).2
  by_cases hq : (Hax.index eq.2 (k : Int)).1 = q
  · have hb : Hax.beq (Hax.index (SigmaProofs.«Equation.terms» eq) (k : Int)).1 q = true := by
      simp [SigmaProofs.«Equation.terms», Hax.beq, hq]
    rw [if_pos hb, if_pos hq]
    simp only [Hax.push]
    exact ⟨by simp [hsb], dotVal_push E _ _ _ _ hsb⟩
  · have hb : ¬ Hax.beq (Hax.index (SigmaProofs.«Equation.terms» eq) (k : Int)).1 q = true := by
      simp [SigmaProofs.«Equation.terms», Hax.beq, hq]
    rw [if_neg hb, if_neg hq]
    exact ⟨hsb, by simp⟩

/-- The extracted `compute_image` is the array of the encoded images `imageComb`. -/
theorem compute_image_eq (els : Array (Array Int))
    (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))) :
    @SigmaProofs.compute_image (groupSigmaProofsDeps E) els eqs =
      Array.ofFn fun j : Fin eqs.size => E.encG (imageComb E els eqs j) := by
  unfold SigmaProofs.compute_image
  simp only [Hax.array_len]
  rw [foldRange_push_ofFn]
  congr 1
  funext j
  rw [imageComb, foldr_groupMul_eq_exp, List.map_map]
  have hsum : ∀ (N : ℕ) (g : ℕ → gp.Scalar),
      ((List.range N).map g).sum = ∑ k ∈ Finset.range N, g k := by
    intro N g
    simp only [Finset.sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]
  rw [hsum, image_entry_dot]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Function.comp_apply, GroupParam.groupExp_eq_exp, GroupParam.dlog_exp,
    GroupParam.scalarMul_eq_mul, mul_comm]

/-- An instance built by the extracted `Instance_new` from the statement elements `els` and
the equations `eqs` has the equations `eqs`, and the image of its decoded relation is the
product `imageComb` of its image terms over its element array. -/
theorem Instance_new_image {els : Array (Array Int)}
    {eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))}
    {inst : SigmaProofs.Instance_T}
    (h : @SigmaProofs.Instance_new (groupSigmaProofsDeps E) els eqs = .ok inst) (n : ℕ) :
    inst.2.1 = eqs ∧ ∀ i : Fin eqs.size,
      (decodeRel E n eqs.size inst).image i = imageComb E inst.1 eqs i := by
  unfold SigmaProofs.Instance_new at h
  simp only [Hax.deref] at h
  split at h
  · simp only [SigmaProofs.Instance, Except.ok.injEq] at h
    subst h
    refine ⟨rfl, fun i => ?_⟩
    rw [decodeRel_image, compute_image_eq, index_ofFn _ _ i.isLt, E.decG_encG]
  · simp at h

/-! ### Validation

The extracted `validate` implements the ten checks of draft-irtf-cfrg-sigma-protocols-03
§3.5 in order and returns the code of the first that fails: (1) there is an equation;
(2) every equation has image terms and terms; (3) the counts are at most `U32_MAX`;
(4) every element index is below the number of elements; (5) every element other than
the generator occurs in an equation; (6) every scalar index up to the largest occurs in
a term; (7) element `0` is the generator; (8) no element is the identity; (9) no image
entry is the identity; (10) no column of the linear map is the identity. On success it
returns the number of scalars, one more than the largest scalar index of a term.

The indices of `decodeRel` are in range (`LinearRelation.IndexValid`) when its scalar
indices are: its element indices are in range by construction. `validate_scalar_lt`
states that a successful validation bounds every scalar index of a term by the number of
scalars it returns, for scalar indices in the `u32` range. -/

/-- The `usize` cast leaves a value in the `u32` range unchanged. -/
theorem castVal_usize_of_lt {x : Int} (h0 : 0 ≤ x) (h : x < 2 ^ 32) :
    Hax.castVal_w Hax.usizeBits x = x := by
  refine Hax.castVal_w_of_lt h0 (lt_of_lt_of_le h ?_)
  rcases System.Platform.numBits_eq with hw | hw <;> simp [Hax.usizeBits, hw]

/-- `foldRange_induct` for a loop whose result is named by an equation. -/
theorem foldRange_induct_of_eq {α : Type} {P : Int → α → Prop} {lo hi : Int}
    {f : Int → α → α} {init r : α} (heq : Hax.foldRange lo hi init f = r) (hle : lo ≤ hi)
    (h0 : P lo init) (hstep : ∀ i a, lo ≤ i → i < hi → P i a → P (i + 1) (f i a)) : P hi r :=
  heq ▸ Hax.foldRange_induct hle h0 hstep

/-- A stage of the extracted `validate` that runs only while the failure code is `0`
returns the failure code `0` only if it received `0`. -/
theorem guard_eq_zero {f X : Int} (h : (if Hax.beq f 0 = true then X else f) = 0) : f = 0 := by
  by_cases hf : f = 0
  · exact hf
  · simp [Hax.beq, hf] at h

/-- A successful extracted validation returns a nonnegative number of scalars above every
scalar index of a term, for scalar indices in the `u32` range. -/
theorem validate_scalar_lt [SigmaProofs.SigmaProofsDeps] {els : Array (Array Int)}
    {eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))} {k : Int}
    (h : SigmaProofs.validate els eqs = .ok k)
    (hsi : ∀ j : ℕ, j < eqs.size → ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
      0 ≤ (Hax.index (Hax.index eqs (j : Int)).2 (t : Int)).1 ∧
        (Hax.index (Hax.index eqs (j : Int)).2 (t : Int)).1 < 2 ^ 32) :
    0 ≤ k ∧ ∀ j : ℕ, j < eqs.size → ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
      uidx (Hax.index (Hax.index eqs (j : Int)).2 (t : Int)).1 < k.toNat := by
  unfold SigmaProofs.validate at h
  extract_lets ne c0 c1 m9 f19 c2 m8 f17 f16 c3 m7 f14 eu1 c4 m6 f12 eu ms nt c5 m5 f10 c6 su1 su
    m4 f8 c7 m3 f6 c8 m2 f4 c9 m1 f2 nz1 nz c10 m0 f0 at h
  split at h
  · simp at h
  · rename_i hF
    simp only [Except.ok.injEq] at h
    subst h
    have hz : f0 = 0 := by simpa [Hax.bne] using hF
    have h12 : m6.1 = 0 := guard_eq_zero (guard_eq_zero (guard_eq_zero (guard_eq_zero
      (guard_eq_zero (guard_eq_zero hz)))))
    have hms : 0 ≤ ms ∧ ms < 2 ^ 32 ∧ ∀ j : ℕ, j < eqs.size →
        ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
          (Hax.index (Hax.index eqs (j : Int)).2 (t : Int)).1 ≤ ms := by
      revert h12
      unfold ms m6
      clear hF hz f0 m0 c10 nz nz1 f2 m1 c9 f4 m2 c8 f6 m3 c7 f8 m4 su su1 c6 f10 m5 c5 nt ms eu
        f12 m6
      split
      · rename_i hc
        intro _
        split
        rename_i a b c d heq
        refine foldRange_induct_of_eq (P := fun (i : Int) (x : Int × Array Bool × Int × Int) =>
          0 ≤ x.2.2.1 ∧ x.2.2.1 < 2 ^ 32 ∧ ∀ j : ℕ, j < i.toNat →
            ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
              (Hax.index (Hax.index eqs (j : Int)).2 (t : Int)).1 ≤ x.2.2.1) heq ?_ ?_ ?_
        · exact Int.zero_le_ofNat eqs.size
        · grind only
        · intro i x hi0 hilt hx
          obtain ⟨f, u, s, n⟩ := x
          obtain ⟨hs0, hs1, hsa⟩ := hx
          dsimp only
          have hiT : ((i.toNat : ℕ) : Int) = i := Int.toNat_of_nonneg hi0
          generalize hR : Hax.foldRange 0
            (Hax.array_len (SigmaProofs.«Equation.terms» (Hax.index eqs i))) _ _ = R
          have hT := foldRange_induct_of_eq
            (P := fun (t : Int) (y : Int × Array Bool × Int × Int) =>
            0 ≤ y.2.2.1 ∧ y.2.2.1 < 2 ^ 32 ∧ s ≤ y.2.2.1 ∧ ∀ t' : ℕ, t' < t.toNat →
              (Hax.index (Hax.index eqs i).2 (t' : Int)).1 ≤ y.2.2.1) hR
            (Int.zero_le_ofNat _) ⟨hs0, hs1, le_rfl, by simp⟩ ?_
          · obtain ⟨hr0, hr1, hsr, hrt⟩ := hT
            refine ⟨hr0, hr1, fun j hj t ht => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp (show j < i.toNat + 1 by omega) with hj' | rfl
            · exact (hsa j hj' t ht).trans hsr
            · rw [hiT] at ht ⊢
              exact hrt t (by simpa [Hax.array_len_eq_size, SigmaProofs.«Equation.terms»] using ht)
          · intro t y ht0 htlt hy
            obtain ⟨fy, uy, sy, ny⟩ := y
            obtain ⟨hy0, hy1, hsy, hyt⟩ := hy
            dsimp only at hy0 hy1 hsy hyt hs0 hs1
            have hi' : i.toNat < eqs.size := by
              rw [Hax.array_len_eq_size] at hilt
              omega
            have ht' : t.toNat < (Hax.index eqs ((i.toNat : ℕ) : Int)).2.size := by
              rw [Hax.array_len_eq_size] at htlt
              rw [hiT]
              exact (Int.toNat_lt ht0).mpr htlt
            have hst := hsi i.toNat hi' t.toNat ht'
            rw [hiT, Int.toNat_of_nonneg ht0] at hst
            dsimp only
            have key : ∀ nm : Int, nm = (if Hax.gt (Hax.index (Hax.index eqs i).2 t).1 sy = true
                then (Hax.index (Hax.index eqs i).2 t).1 else sy) →
                sy ≤ nm ∧ (Hax.index (Hax.index eqs i).2 t).1 ≤ nm ∧ 0 ≤ nm ∧ nm < 2 ^ 32 := by
              intro nm hnm
              split at hnm <;> rename_i hg <;> simp only [Hax.gt, decide_eq_true_eq] at hg <;>
                subst hnm <;> omega
            obtain ⟨k1, k2, k3, k4⟩ := key _ rfl
            refine ⟨k3, k4, hsy.trans k1, fun t' ht' => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp (show t' < t.toNat + 1 by omega) with h' | rfl
            · exact (hyt t' h').trans k1
            · rw [Int.toNat_of_nonneg ht0]
              exact k2
      · rename_i hc
        intro h12
        simp_all [Hax.beq]
    obtain ⟨hm0, hm1, hall⟩ := hms
    rw [castVal_usize_of_lt hm0 hm1]
    refine ⟨by simp only [Hax.add]; omega, fun j hj t ht => ?_⟩
    obtain ⟨hs0, hs1'⟩ := hsi j hj t ht
    have := hall j hj t ht
    rw [uidx, castVal_usize_of_lt hs0 hs1']
    simp only [Hax.add]
    omega

/-- An instance built by the extracted `Instance_new` from equations whose scalar indices
are in the `u32` range is well formed, with the number of scalars that `validate`
returned. -/
theorem Instance_new_wellFormed {els : Array (Array Int)}
    {eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))}
    {inst : SigmaProofs.Instance_T}
    (h : @SigmaProofs.Instance_new (groupSigmaProofsDeps E) els eqs = .ok inst)
    (hsi : ∀ j : ℕ, j < eqs.size → ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
      0 ≤ (Hax.index (Hax.index eqs (j : Int)).2 (t : Int)).1 ∧
        (Hax.index (Hax.index eqs (j : Int)).2 (t : Int)).1 < 2 ^ 32) :
    WellFormed E inst.2.2.2.toNat eqs.size inst := by
  unfold SigmaProofs.Instance_new at h
  simp only [Hax.deref] at h
  split at h
  · rename_i val hv
    simp only [SigmaProofs.Instance, Except.ok.injEq] at h
    subst h
    obtain ⟨h0, hlt⟩ := @validate_scalar_lt (groupSigmaProofsDeps E) _ _ _ hv hsi
    exact ⟨(Int.toNat_of_nonneg h0).symm, rfl, (decodeRel_validate_iff E _ _ _).mpr hlt⟩
  · simp at h

/-! ### Validation in the draft's layout

A core `LinearRelation` has no coefficients and one image element per equation. The
relation `layoutRel` reads equations in that form (one image term, coefficients one)
over the element array of `validate`, whose element `0` is the generator;
`validate_ok_iff` states that on such equations, with indices in the `u32` range,
`validate` succeeds with `n` scalars exactly when the counts are at most `U32_MAX` and the
relation satisfies the draft's `ValidateInstance` with `n` scalars. -/

/-- A stage of the extracted `validate` that runs only while the failure code is `0`
returns `0` exactly when it received `0` and the stage returns `0`. -/
theorem guard_eq_zero_iff {f X : Int} :
    (if Hax.beq f 0 = true then X else f) = 0 ↔ f = 0 ∧ X = 0 := by
  by_cases hf : f = 0 <;> simp [Hax.beq, hf]

open Classical in
/-- A loop whose step replaces the accumulator by `K` at the indices satisfying `c`
returns `K` when some index of the range satisfies `c`, and its initial value
otherwise. -/
theorem foldRange_set_const {α : Type} (lo hi : Int) (init K : α) (c : Int → Prop)
    [DecidablePred c] :
    Hax.foldRange lo hi init (fun j a => if c j then K else a) =
      if ∃ j, lo ≤ j ∧ j < hi ∧ c j then K else init := by
  by_cases hle : lo ≤ hi
  · refine Hax.foldRange_induct (P := fun i a =>
      a = if ∃ j, lo ≤ j ∧ j < i ∧ c j then K else init) hle (by simp; omega) ?_
    intro i a hlo hi ha
    subst ha
    split_ifs <;> grind
  · rw [Hax.foldRange_stop _ _ _ _ (by omega), if_neg]
    rintro ⟨j, h1, h2, -⟩
    omega

/-- `foldRange_set_const` for a failure code `K ≠ 0`: the loop returns `0` exactly when
its initial value is `0` and no index of the range satisfies `c`. -/
theorem foldRange_set_eq_zero_iff (lo hi : Int) (init K : Int) (hK : K ≠ 0) (c : Int → Prop)
    [DecidablePred c] :
    Hax.foldRange lo hi init (fun j a => if c j then K else a) = 0 ↔
      init = 0 ∧ ∀ j, lo ≤ j → j < hi → ¬ c j := by
  classical
  rw [foldRange_set_const]
  aesop

/-- `foldRange_set_const` for a flag set to `true`. -/
theorem foldRange_set_true_iff (lo hi : Int) (c : Int → Prop) [DecidablePred c] :
    Hax.foldRange lo hi false (fun j a => if c j then true else a) = true ↔
      ∃ j, lo ≤ j ∧ j < hi ∧ c j := by
  classical
  rw [foldRange_set_const]
  simp_all

/-- Setting an in-range entry of a flag array marks that entry and keeps the others. -/
theorem index_array_update_true_iff (a : Array Bool) (p q : Int) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpa : p.toNat < a.size) :
    Hax.index (Hax.array_update a q true) p = true ↔ Hax.index a p = true ∨ p = q := by
  by_cases hpq : p = q
  · subst hpq
    rw [Hax.index_array_update_same _ hpa]
    simp
  · rw [Hax.index_array_update_of_ne _ hpa (by omega)]
    simp [hpq]

/-- The fresh flag array `from_elem false N` has no entry set. -/
theorem index_from_elem_false (N p : Int) : Hax.index (Hax.from_elem false N) p = false := by
  unfold Hax.index Hax.from_elem
  split_ifs <;> simp

/-- A loop over the range `[0, 1)` is its step at `0`. -/
theorem foldRange_one {α : Type} (init : α) (f : Int → α → α) :
    Hax.foldRange 0 1 init f = f 0 init := by
  rw [Hax.foldRange_step 0 1 _ _ (by norm_num)]
  exact Hax.foldRange_stop _ _ _ _ (by norm_num)

/-- The scalar index of the term `t` of equation `j`. -/
abbrev termScalar (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int))))
    (j t : Int) : Int := (Hax.index (Hax.index eqs j).2 t).1

/-- The element index of the term `t` of equation `j`. -/
abbrev termElemIdx (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int))))
    (j t : Int) : Int := (Hax.index (Hax.index eqs j).2 t).2.1

/-- The element index of the first image term of equation `j`. -/
abbrev imageElemIdx (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int))))
    (j : Int) : Int := (Hax.index (Hax.index eqs j).1 0).1

/-- The loop of check 4 of the extracted `validate` on equations with one image term each
and indices in the `u32` range: its failure code is `0` exactly when every element index
is below the number of elements, its flag array marks exactly the element indices that
occur, its scalar bound is the largest scalar index (or `0`), and its term count is the
number of terms. -/
theorem validate_terms_loop [SigmaProofs.SigmaProofsDeps] (els : Array (Array Int))
    (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int))))
    (hL : ∀ j : ℕ, j < eqs.size → (Hax.index eqs (j : Int)).1.size = 1 ∧
      0 ≤ imageElemIdx eqs j ∧ imageElemIdx eqs j < 2 ^ 32 ∧
      ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
        0 ≤ termScalar eqs j t ∧ termScalar eqs j t < 2 ^ 32 ∧
        0 ≤ termElemIdx eqs j t ∧ termElemIdx eqs j t < 2 ^ 32) :
    ∀ R, Hax.foldRange 0 (Hax.array_len eqs)
      ((0 : Int), Hax.from_elem false (Hax.array_len els), (0 : Int), (0 : Int))
      (fun j (failed, element_used, max_scalar, num_terms) =>
        let equation := Hax.index eqs j
        let (failed, element_used) := Hax.foldRange 0
          (Hax.array_len (SigmaProofs.«Equation.image» equation)) (failed, element_used)
          fun k (failed, element_used) =>
            let element_index := (Hax.index (SigmaProofs.«Equation.image» equation) k).1
            if Hax.ge (Hax.castVal_w Hax.usizeBits element_index) (Hax.array_len els) then
              ((4 : Int), element_used)
            else
              let element_used := (Hax.array_update element_used
                (Hax.castVal_w Hax.usizeBits element_index) true : Array Bool)
              (failed, element_used)
        Hax.foldRange 0 (Hax.array_len (SigmaProofs.«Equation.terms» equation))
          (failed, element_used, max_scalar, num_terms)
          fun k (failed, element_used, max_scalar, num_terms) =>
            let (scalar_index, element_index, _) := Hax.index (SigmaProofs.«Equation.terms» equation) k
            let failed := if Hax.ge (Hax.castVal_w Hax.usizeBits element_index)
              (Hax.array_len els) then (4 : Int) else failed
            let element_used := if Hax.ge (Hax.castVal_w Hax.usizeBits element_index)
              (Hax.array_len els) then element_used else (Hax.array_update element_used
                (Hax.castVal_w Hax.usizeBits element_index) true : Array Bool)
            let max_scalar := if Hax.gt scalar_index max_scalar then scalar_index else max_scalar
            let num_terms := Hax.add num_terms (1 : Int)
            (failed, element_used, max_scalar, num_terms)) = R →
    (R.1 = 0 ↔ ∀ j : ℕ, j < eqs.size → imageElemIdx eqs j < els.size ∧
        ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size → termElemIdx eqs j t < els.size) ∧
      R.2.1.size = els.size ∧
      (∀ p : ℕ, p < els.size → (Hax.index R.2.1 (p : Int) = true ↔
        ∃ j : ℕ, j < eqs.size ∧ (imageElemIdx eqs j = p ∨
          ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧ termElemIdx eqs j t = p))) ∧
      0 ≤ R.2.2.1 ∧ R.2.2.1 < 2 ^ 32 ∧
      (∀ j : ℕ, j < eqs.size → ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
        termScalar eqs j t ≤ R.2.2.1) ∧
      (R.2.2.1 = 0 ∨ ∃ j : ℕ, j < eqs.size ∧
        ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧ termScalar eqs j t = R.2.2.1) ∧
      R.2.2.2 = ∑ j ∈ Finset.range eqs.size, ((Hax.index eqs (j : Int)).2.size : Int) := by
  intro R hR
  have key := foldRange_induct_of_eq (P := fun (i : Int) (x : Int × Array Bool × Int × Int) =>
      (x.1 = 0 ↔ ∀ j : ℕ, j < i.toNat → imageElemIdx eqs j < els.size ∧
        ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size → termElemIdx eqs j t < els.size) ∧
      x.2.1.size = els.size ∧
      (∀ p : ℕ, p < els.size → (Hax.index x.2.1 (p : Int) = true ↔
        ∃ j : ℕ, j < i.toNat ∧ (imageElemIdx eqs j = p ∨
          ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧ termElemIdx eqs j t = p))) ∧
      0 ≤ x.2.2.1 ∧ x.2.2.1 < 2 ^ 32 ∧
      (∀ j : ℕ, j < i.toNat → ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
        termScalar eqs j t ≤ x.2.2.1) ∧
      (x.2.2.1 = 0 ∨ ∃ j : ℕ, j < i.toNat ∧
        ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧ termScalar eqs j t = x.2.2.1) ∧
      x.2.2.2 = ∑ j ∈ Finset.range i.toNat, ((Hax.index eqs (j : Int)).2.size : Int))
    hR (by simp [Hax.array_len]) ?_ ?_
  · simpa [Hax.array_len] using key
  · exact ⟨by simp, by simp [Hax.from_elem, Hax.array_len], fun p _ => by
      simp [index_from_elem_false], by norm_num, by norm_num, by simp, by simp, by simp⟩
  · clear hR
    intro i x hi0 hilt hx
    obtain ⟨f, u, s, c⟩ := x
    obtain ⟨hf, hus, hu, hs0, hs1, hsa, hsm, hc⟩ := hx
    dsimp only at hf hus hu hs0 hs1 hsa hsm hc ⊢
    have hiT : ((i.toNat : ℕ) : Int) = i := Int.toNat_of_nonneg hi0
    have hi' : i.toNat < eqs.size := by rw [Hax.array_len_eq_size] at hilt; omega
    obtain ⟨hsz1, hie0, hie1, hterm⟩ := hL i.toNat hi'
    rw [hiT] at hsz1 hie0 hie1 hterm
    rw [show (i + 1).toNat = i.toNat + 1 by omega]
    have himg : Hax.array_len (SigmaProofs.«Equation.image» (Hax.index eqs i)) = 1 := by
      simp [Hax.array_len, SigmaProofs.«Equation.image», hsz1]
    rw [himg]
    generalize hIM : Hax.foldRange 0 1 (f, u) _ = IM
    obtain ⟨f', u'⟩ := IM
    rw [foldRange_one] at hIM
    have hie0' : 0 ≤ (Hax.index (SigmaProofs.«Equation.image» (Hax.index eqs i)) 0).1 := hie0
    have hie1' : (Hax.index (SigmaProofs.«Equation.image» (Hax.index eqs i)) 0).1 < 2 ^ 32 :=
      hie1
    dsimp only at hIM
    rw [castVal_usize_of_lt hie0' hie1'] at hIM
    have hNe : Hax.array_len els = (els.size : Int) := rfl
    have hIM' : (f' = 0 ↔ f = 0 ∧ imageElemIdx eqs i < els.size) ∧ u'.size = els.size ∧
        ∀ p : ℕ, p < els.size →
          (Hax.index u' (p : Int) = true ↔ Hax.index u p = true ∨ imageElemIdx eqs i = p) := by
      split at hIM <;> rename_i hge <;> simp only [Prod.mk.injEq] at hIM <;>
        obtain ⟨rfl, rfl⟩ := hIM <;> simp only [Hax.ge, hNe, decide_eq_true_eq] at hge
      · have hge' : (els.size : Int) ≤ imageElemIdx eqs i := hge
        refine ⟨by omega, hus, fun p hp => ⟨Or.inl, fun h => h.elim id fun h => ?_⟩⟩
        omega
      · have hge' : imageElemIdx eqs i < (els.size : Int) := not_le.mp hge
        refine ⟨⟨fun h => ⟨h, hge'⟩, fun h => h.1⟩, by rw [Hax.size_array_update_eq, hus],
          fun p hp => ?_⟩
        rw [index_array_update_true_iff _ _ _ (by omega) hie0' (by omega)]
        exact or_congr Iff.rfl eq_comm
    clear hIM
    obtain ⟨hf', hus', hu'⟩ := hIM'
    dsimp only
    generalize hT : Hax.foldRange 0 _ (f', u', s, c) _ = T
    have hTi := foldRange_induct_of_eq (P := fun (t : Int) (y : Int × Array Bool × Int × Int) =>
        (y.1 = 0 ↔ f' = 0 ∧ ∀ t' : ℕ, t' < t.toNat → termElemIdx eqs i t' < els.size) ∧
        y.2.1.size = els.size ∧
        (∀ p : ℕ, p < els.size → (Hax.index y.2.1 (p : Int) = true ↔
          Hax.index u' p = true ∨ ∃ t' : ℕ, t' < t.toNat ∧ termElemIdx eqs i t' = p)) ∧
        0 ≤ y.2.2.1 ∧ y.2.2.1 < 2 ^ 32 ∧ s ≤ y.2.2.1 ∧
        (∀ t' : ℕ, t' < t.toNat → termScalar eqs i t' ≤ y.2.2.1) ∧
        (y.2.2.1 = s ∨ ∃ t' : ℕ, t' < t.toNat ∧ termScalar eqs i t' = y.2.2.1) ∧
        y.2.2.2 = c + t) hT (by simp [Hax.array_len])
      ⟨by simp, hus', fun p _ => by simp, hs0, hs1, le_rfl, by simp, Or.inl rfl, by simp⟩ ?_
    · obtain ⟨hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9⟩ := hTi
      have hsz : (Hax.array_len (SigmaProofs.«Equation.terms» (Hax.index eqs i))).toNat =
          (Hax.index eqs i).2.size := by simp [Hax.array_len, SigmaProofs.«Equation.terms»]
      rw [hsz] at hT1 hT3 hT7 hT8
      refine ⟨?_, hT2, fun p hp => ?_, hT4, hT5, ?_, ?_, ?_⟩
      · simp only [Nat.forall_lt_succ_right, hiT]
        rw [hT1, hf', hf, and_assoc]
      · rw [hT3 p hp, hu' p hp, hu p hp]
        simp only [Nat.exists_lt_succ_right, hiT]
        rw [or_assoc]
      · simp only [Nat.forall_lt_succ_right, hiT]
        exact ⟨fun j hj t ht => (hsa j hj t ht).trans hT6, hT7⟩
      · simp only [Nat.exists_lt_succ_right, hiT]
        rcases hT8 with h | h
        · rcases hsm with h' | h'
          · exact Or.inl (h.trans h')
          · exact Or.inr (Or.inl (h ▸ h'))
        · exact Or.inr (Or.inr h)
      · rw [hT9, hc, Finset.sum_range_succ, hiT]
        simp [Hax.array_len, SigmaProofs.«Equation.terms»]
    · intro t y ht0 htlt hy
      obtain ⟨fy, uy, sy, ny⟩ := y
      obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9⟩ := hy
      dsimp only at hy1 hy2 hy3 hy4 hy5 hy6 hy7 hy8 hy9 ⊢
      have htT : ((t.toNat : ℕ) : Int) = t := Int.toNat_of_nonneg ht0
      have ht' : t.toNat < (Hax.index eqs i).2.size := by
        simp only [Hax.array_len, SigmaProofs.«Equation.terms»] at htlt; omega
      obtain ⟨hs0', hs1', he0, he1⟩ := hterm t.toNat ht'
      rw [htT] at hs0' hs1' he0 he1
      have hEe : termElemIdx eqs i t =
          (Hax.index (SigmaProofs.«Equation.terms» (Hax.index eqs i)) t).2.1 := rfl
      have hSs : termScalar eqs i t =
          (Hax.index (SigmaProofs.«Equation.terms» (Hax.index eqs i)) t).1 := rfl
      rw [hEe] at he0 he1
      rw [castVal_usize_of_lt he0 he1, show (t + 1).toNat = t.toNat + 1 by omega]
      simp only [Nat.forall_lt_succ_right, Nat.exists_lt_succ_right, htT, hEe, hSs]
      rw [hSs] at hs0' hs1'
      generalize (Hax.index (SigmaProofs.«Equation.terms» (Hax.index eqs i)) t).2.1 = e
        at he0 he1 ⊢
      generalize (Hax.index (SigmaProofs.«Equation.terms» (Hax.index eqs i)) t).1 = sc
        at hs0' hs1' ⊢
      simp only [Hax.ge, Hax.gt, Hax.add, hNe, decide_eq_true_eq]
      refine ⟨?_, ?_, fun p hp => ?_, ?_, ?_, ?_, ⟨fun t' ht'' => ?_, ?_⟩, ?_, by omega⟩
      · by_cases hge : (els.size : Int) ≤ e
        · rw [if_pos hge]
          exact ⟨fun h => absurd h (by norm_num), fun h => absurd h.2.2 (not_lt.mpr hge)⟩
        · rw [if_neg hge, hy1]
          exact ⟨fun h => ⟨h.1, h.2, lt_of_not_ge hge⟩, fun h => ⟨h.1, h.2.1⟩⟩
      · split_ifs
        · exact hy2
        · rw [Hax.size_array_update_eq, hy2]
      · by_cases hge : (els.size : Int) ≤ e
        · rw [if_pos hge, hy3 p hp]
          exact or_congr Iff.rfl ⟨Or.inl, fun h => h.elim id fun h => by omega⟩
        · rw [if_neg hge, index_array_update_true_iff _ _ _ (by omega) he0 (by omega), hy3 p hp,
            or_assoc]
          exact or_congr Iff.rfl (or_congr Iff.rfl eq_comm)
      · split_ifs <;> omega
      · split_ifs <;> omega
      · split_ifs <;> omega
      · have := hy7 t' ht''
        split_ifs <;> omega
      · split_ifs <;> omega
      · split_ifs with hlt
        · exact Or.inr (Or.inr rfl)
        · rcases hy8 with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)

/-- The loop of check 6 of the extracted `validate` marking the scalar indices of the
terms in a fresh flag array of length `M` above all of them marks exactly the scalar
indices that occur. -/
theorem validate_scalar_used_loop
    (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))) (M : Int)
    (hL : ∀ j : ℕ, j < eqs.size → ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
      0 ≤ termScalar eqs j t ∧ termScalar eqs j t < 2 ^ 32 ∧ termScalar eqs j t < M) :
    ∀ su, Hax.foldRange 0 (Hax.array_len eqs) (Hax.from_elem false M)
      (fun j scalar_used =>
        let equation := Hax.index eqs j
        Hax.foldRange 0 (Hax.array_len (SigmaProofs.«Equation.terms» equation)) scalar_used
          fun k scalar_used =>
            let scalar_index := (Hax.index (SigmaProofs.«Equation.terms» equation) k).1
            let scalar_used := (Hax.array_update scalar_used
              (Hax.castVal_w Hax.usizeBits scalar_index) true : Array Bool)
            scalar_used) = su →
    su.size = M.toNat ∧ ∀ q : ℕ, q < M.toNat → (Hax.index su (q : Int) = true ↔
      ∃ j : ℕ, j < eqs.size ∧ ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧
        termScalar eqs j t = q) := by
  intro su hsu
  have key := foldRange_induct_of_eq (P := fun (i : Int) (x : Array Bool) =>
      x.size = M.toNat ∧ ∀ q : ℕ, q < M.toNat → (Hax.index x (q : Int) = true ↔
        ∃ j : ℕ, j < i.toNat ∧ ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧
          termScalar eqs j t = q))
    hsu (by simp [Hax.array_len])
    ⟨by simp [Hax.from_elem], fun q _ => by simp [index_from_elem_false]⟩ ?_
  · simpa [Hax.array_len] using key
  · clear hsu
    intro i x hi0 hilt hx
    obtain ⟨hxs, hx⟩ := hx
    have hiT : ((i.toNat : ℕ) : Int) = i := Int.toNat_of_nonneg hi0
    have hi' : i.toNat < eqs.size := by rw [Hax.array_len_eq_size] at hilt; omega
    dsimp only
    generalize hT : Hax.foldRange 0 _ x _ = Y
    have hR := foldRange_induct_of_eq (P := fun (t : Int) (y : Array Bool) =>
        y.size = M.toNat ∧ ∀ q : ℕ, q < M.toNat → (Hax.index y (q : Int) = true ↔
          Hax.index x (q : Int) = true ∨ ∃ t' : ℕ, t' < t.toNat ∧ termScalar eqs i t' = q))
      hT (by simp [Hax.array_len]) ⟨hxs, fun q _ => by simp⟩ ?_
    · have hsz : (Hax.array_len (SigmaProofs.«Equation.terms» (Hax.index eqs i))).toNat =
          (Hax.index eqs i).2.size := by simp [Hax.array_len, SigmaProofs.«Equation.terms»]
      rw [hsz] at hR
      refine ⟨hR.1, fun q hq => ?_⟩
      rw [show (i + 1).toNat = i.toNat + 1 by omega, hR.2 q hq, hx q hq]
      simp only [Nat.exists_lt_succ_right, hiT]
    · intro t y ht0 htlt hy
      obtain ⟨hys, hy⟩ := hy
      have htT : ((t.toNat : ℕ) : Int) = t := Int.toNat_of_nonneg ht0
      have ht' : t.toNat < (Hax.index eqs i).2.size := by
        simp only [Hax.array_len, SigmaProofs.«Equation.terms»] at htlt; omega
      obtain ⟨hs0, hs1, hsM⟩ := hL i.toNat hi' t.toNat ht'
      rw [hiT, htT] at hs0 hs1 hsM
      have hs0' : 0 ≤ (Hax.index (SigmaProofs.«Equation.terms» (Hax.index eqs i)) t).1 := hs0
      have hs1' : (Hax.index (SigmaProofs.«Equation.terms» (Hax.index eqs i)) t).1 < 2 ^ 32 :=
        hs1
      rw [castVal_usize_of_lt hs0' hs1']
      refine ⟨by rw [Hax.size_array_update_eq, hys], fun q hq => ?_⟩
      rw [index_array_update_true_iff _ _ _ (by omega) hs0' (by omega), hy q hq,
        show (t + 1).toNat = t.toNat + 1 by omega]
      simp only [Nat.exists_lt_succ_right, htT]
      rw [or_assoc]
      exact or_congr Iff.rfl (or_congr Iff.rfl eq_comm)

/-- Check 7 of the extracted `validate` on the failure code `0`. -/
theorem validate_check7_iff [SigmaProofs.SigmaProofsDeps] (els : Array (Array Int)) :
    (if Hax.beq (Hax.array_len els) 0 = true then (7 : Int) else
      if Hax.beq (SigmaProofs.group_eq (Hax.index els 0) SigmaProofs.generator) 0 = true then 7
      else 0) = 0 ↔
      els.size ≠ 0 ∧ SigmaProofs.group_eq (Hax.index els 0) SigmaProofs.generator = true := by
  cases hg : SigmaProofs.group_eq (Hax.index els 0) SigmaProofs.generator <;>
    by_cases hs : els.size = 0 <;> simp [Hax.beq, Hax.array_len, hs]

/-- Check 6 of the extracted `validate` on the failure code `0`. -/
theorem validate_check6_iff (ms nt : Int) (su : Array Bool) :
    (if Hax.ge ms nt = true then (6 : Int) else
      Hax.foldRange 0 (Hax.add ms 1) 0 fun s failed =>
        if Hax.beq (Hax.index su s) 0 = true then 6 else failed) = 0 ↔
      ¬ nt ≤ ms ∧ ∀ s, 0 ≤ s → s < Hax.add ms 1 → ¬ Hax.beq (Hax.index su s) 0 = true := by
  by_cases hg : nt ≤ ms
  · rw [if_pos (by simp [Hax.ge, hg])]
    exact ⟨fun h' => absurd h' (by decide), fun h' => absurd hg h'.1⟩
  · rw [if_neg (by simp [Hax.ge, hg]), foldRange_set_eq_zero_iff 0 _ 0 6 (by decide)]
    exact ⟨fun h' => ⟨hg, h'.2⟩, fun h' => ⟨rfl, h'.2⟩⟩

/-- A statement over the integers of `[a, b)` for `0 ≤ a` is a statement over the natural
numbers of that range. -/
theorem forall_int_range_iff (a : ℕ) (b : Int) (P : Int → Prop) :
    (∀ s : Int, (a : Int) ≤ s → s < b → P s) ↔ ∀ q : ℕ, a ≤ q → (q : Int) < b → P q := by
  refine ⟨fun h q h1 h2 => h q (by omega) h2, fun h s h1 h2 => ?_⟩
  have e : ((s.toNat : ℕ) : Int) = s := Int.toNat_of_nonneg (by omega)
  rw [← e]
  exact h _ (by omega) (by omega)

/-- The count checks 2 and 3 of the extracted `validate` on equations with one image term
each and fewer than `2^64` terms. -/
theorem validate_counts_iff [SigmaProofs.SigmaProofsDeps]
    (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int))))
    (hm : eqs.size < 2 ^ 64)
    (hL : ∀ j : ℕ, j < eqs.size → (Hax.index eqs (j : Int)).1.size = 1 ∧
      (Hax.index eqs (j : Int)).2.size < 2 ^ 64) :
    ((∀ j, 0 ≤ j → j < Hax.array_len eqs → ¬ Hax.bor
      (Hax.beq (Hax.array_len (SigmaProofs.«Equation.image» (Hax.index eqs j))) 0)
      (Hax.beq (Hax.array_len (SigmaProofs.«Equation.terms» (Hax.index eqs j))) 0) = true) ↔
        ∀ j : ℕ, j < eqs.size → 0 < (Hax.index eqs (j : Int)).2.size) ∧
    (¬ Hax.gt (Hax.castVal_w 64 (Hax.array_len eqs)) SigmaProofs.U32_MAX = true ↔
      eqs.size ≤ 4294967295) ∧
    ((∀ j, 0 ≤ j → j < Hax.array_len eqs → ¬ Hax.bor
        (Hax.gt (Hax.castVal_w 64 (Hax.array_len (SigmaProofs.«Equation.image» (Hax.index eqs j))))
          SigmaProofs.U32_MAX)
        (Hax.gt (Hax.castVal_w 64 (Hax.array_len (SigmaProofs.«Equation.terms» (Hax.index eqs j))))
          SigmaProofs.U32_MAX) = true) ↔
      ∀ j : ℕ, j < eqs.size → (Hax.index eqs (j : Int)).2.size ≤ 4294967295) := by
  have hc : ∀ x : ℕ, x < 2 ^ 64 → Hax.castVal_w 64 (x : Int) = x := fun x hx =>
    Hax.castVal_w_of_lt (by omega) (by exact_mod_cast hx)
  refine ⟨?_, ?_, ?_⟩
  · rw [show (0 : Int) = ((0 : ℕ) : Int) from rfl, forall_int_range_iff]
    refine forall_congr' fun j => ?_
    simp only [Hax.array_len, Nat.cast_lt, zero_le, true_implies]
    refine imp_congr_right fun hj => ?_
    simp [Hax.bor, Hax.beq, SigmaProofs.«Equation.image», SigmaProofs.«Equation.terms»,
      (hL j hj).1, Nat.pos_iff_ne_zero]
  · simp only [Hax.array_len, hc _ hm, Hax.gt, SigmaProofs.U32_MAX, decide_eq_true_eq, not_lt]
    omega
  · rw [show (0 : Int) = ((0 : ℕ) : Int) from rfl, forall_int_range_iff]
    refine forall_congr' fun j => ?_
    simp only [Hax.array_len, Nat.cast_lt, zero_le, true_implies]
    refine imp_congr_right fun hj => ?_
    simp only [SigmaProofs.«Equation.image», SigmaProofs.«Equation.terms», (hL j hj).1,
      hc _ (hL j hj).2, hc 1 (by norm_num), Hax.bor, Hax.gt, SigmaProofs.U32_MAX]
    simp

/-- The distinct scalar indices `0, …, M` of the terms number at most the terms. -/
theorem succ_le_sum_terms
    (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))) (M : ℕ)
    (h : ∀ q : ℕ, q ≤ M → ∃ j : ℕ, j < eqs.size ∧
      ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧ termScalar eqs j t = q) :
    M + 1 ≤ ∑ j ∈ Finset.range eqs.size, (Hax.index eqs (j : Int)).2.size := by
  classical
  have hsub : Finset.range (M + 1) ⊆ (Finset.range eqs.size).biUnion fun j =>
      (Finset.range (Hax.index eqs (j : Int)).2.size).image
        fun t : ℕ => (termScalar eqs j t).toNat := by
    intro q hq
    obtain ⟨j, hj, t, ht, he⟩ := h q (by simp at hq; omega)
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    exact ⟨j, hj, t, ht, by rw [he]; simp⟩
  calc M + 1 = (Finset.range (M + 1)).card := by simp
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.card_image_le.trans (by simp)

/-- On equations with one image term each and indices in the `u32` range, the extracted
`validate` succeeds with `n` scalars exactly when its ten checks hold with `n` one more than
the largest scalar index: the counts are at most `U32_MAX` (check 3), there is an equation
and every equation has a term (checks 1, 2), the element indices are in range (check 4),
every element other than element `0` occurs (check 5), the scalar indices are exactly
those below `n` (check 6), element `0` is the generator (check 7) and no element, image
entry or column entry of a scalar below `n` in every row is the identity (checks 8–10). -/
theorem validate_ok_iff_checks [SigmaProofs.SigmaProofsDeps] {els : Array (Array Int)}
    {eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))}
    (hm : eqs.size < 2 ^ 64)
    (hL : ∀ j : ℕ, j < eqs.size → (Hax.index eqs (j : Int)).1.size = 1 ∧
      0 ≤ imageElemIdx eqs j ∧ imageElemIdx eqs j < 2 ^ 32 ∧
      (Hax.index eqs (j : Int)).2.size < 2 ^ 64 ∧
      ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
        0 ≤ termScalar eqs j t ∧ termScalar eqs j t < 2 ^ 32 ∧
        0 ≤ termElemIdx eqs j t ∧ termElemIdx eqs j t < 2 ^ 32)
    (n : ℕ) :
    SigmaProofs.validate els eqs = .ok (n : Int) ↔
      (eqs.size ≤ 4294967295 ∧ ∀ j : ℕ, j < eqs.size →
        (Hax.index eqs (j : Int)).2.size ≤ 4294967295) ∧
      0 < eqs.size ∧ (∀ j : ℕ, j < eqs.size → 0 < (Hax.index eqs (j : Int)).2.size) ∧
      (∀ j : ℕ, j < eqs.size → imageElemIdx eqs j < els.size ∧
        ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size → termElemIdx eqs j t < els.size) ∧
      (∀ p : ℕ, 1 ≤ p → p < els.size → ∃ j : ℕ, j < eqs.size ∧ (imageElemIdx eqs j = p ∨
        ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧ termElemIdx eqs j t = p)) ∧
      (∀ j : ℕ, j < eqs.size → ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
        termScalar eqs j t < n) ∧
      (∀ q : ℕ, q < n → ∃ j : ℕ, j < eqs.size ∧
        ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧ termScalar eqs j t = q) ∧
      (0 < els.size ∧ SigmaProofs.group_eq (Hax.index els 0) SigmaProofs.generator = true) ∧
      (∀ p : ℕ, p < els.size →
        SigmaProofs.group_eq (Hax.index els (p : Int)) SigmaProofs.identity = false) ∧
      (∀ j : ℕ, j < eqs.size → SigmaProofs.group_eq
        (SigmaProofs.image_entry els (Hax.index eqs (j : Int))) SigmaProofs.identity = false) ∧
      (∀ q : ℕ, q < n → ∃ j : ℕ, j < eqs.size ∧ SigmaProofs.group_eq
        (SigmaProofs.column_entry els (Hax.index eqs (j : Int)) q) SigmaProofs.identity =
          false) := by
  unfold SigmaProofs.validate
  extract_lets ne c0 c1 m9 f19 c2 m8 f17 f16 c3 m7 f14 eu1 c4 m6 f12 eu ms nt c5 m5 f10 c6 su1 su
    m4 f8 c7 m3 f6 c8 m2 f4 c9 m1 f2 nz1 nz c10 m0 f0
  have hfin : (if Hax.bne f0 0 = true then
      (Except.error (SigmaProofs.InvalidInstance (some f0)) : Except (Option Int) Int)
      else Except.ok (Hax.add (Hax.castVal_w Hax.usizeBits ms) 1)) = Except.ok (n : Int) ↔
      f0 = 0 ∧ Hax.add (Hax.castVal_w Hax.usizeBits ms) 1 = n := by
    by_cases h : f0 = 0 <;> simp [Hax.bne, h]
  rw [hfin]
  have e10 : f0 = 0 ↔ f2 = 0 ∧ ∀ s, 0 ≤ s → s < Hax.add (Hax.castVal_w Hax.usizeBits ms) 1 →
      ¬ ((!Hax.foldRange 0 (Hax.array_len eqs) false fun j nonzero =>
          if Hax.beq (SigmaProofs.group_eq (SigmaProofs.column_entry els (Hax.index eqs j)
            (Hax.castVal_w 32 s)) SigmaProofs.identity) 0 = true then true else nonzero) =
              true) := by
    show (if Hax.beq f2 0 = true then _ else f2) = 0 ↔ _
    rw [guard_eq_zero_iff]
    exact and_congr_right fun h => (foldRange_set_eq_zero_iff 0 _ f2 10 (by decide) _).trans
      (and_iff_right h)
  have e9 : f2 = 0 ↔ f4 = 0 ∧ ∀ j, 0 ≤ j → j < Hax.array_len eqs →
      ¬ SigmaProofs.group_eq (SigmaProofs.image_entry els (Hax.index eqs j))
        SigmaProofs.identity = true := by
    show (if Hax.beq f4 0 = true then _ else f4) = 0 ↔ _
    rw [guard_eq_zero_iff]
    exact and_congr_right fun h => (foldRange_set_eq_zero_iff 0 _ f4 9 (by decide) _).trans
      (and_iff_right h)
  have e8 : f4 = 0 ↔ f6 = 0 ∧ ∀ i, 0 ≤ i → i < Hax.array_len els →
      ¬ SigmaProofs.group_eq (Hax.index els i) SigmaProofs.identity = true := by
    show (if Hax.beq f6 0 = true then _ else f6) = 0 ↔ _
    rw [guard_eq_zero_iff]
    exact and_congr_right fun h => (foldRange_set_eq_zero_iff 0 _ f6 8 (by decide) _).trans
      (and_iff_right h)
  have e7 : f6 = 0 ↔ f8 = 0 ∧ els.size ≠ 0 ∧
      SigmaProofs.group_eq (Hax.index els 0) SigmaProofs.generator = true := by
    show (if Hax.beq f8 0 = true then _ else f8) = 0 ↔ _
    rw [guard_eq_zero_iff]
    refine and_congr_right fun h => ?_
    rw [h]
    exact validate_check7_iff els
  have e6 : f8 = 0 ↔ f10 = 0 ∧ ¬ nt ≤ Hax.castVal_w Hax.usizeBits ms ∧
      ∀ s, 0 ≤ s → s < Hax.add (Hax.castVal_w Hax.usizeBits ms) 1 →
        ¬ Hax.beq (Hax.index su s) 0 = true := by
    show (if Hax.beq f10 0 = true then _ else f10) = 0 ↔ _
    rw [guard_eq_zero_iff]
    refine and_congr_right fun h => ?_
    rw [h]
    exact validate_check6_iff _ nt su
  have e5 : f10 = 0 ↔ f12 = 0 ∧ ∀ i, 1 ≤ i → i < Hax.array_len els →
      ¬ Hax.beq (Hax.index eu i) 0 = true := by
    show (if Hax.beq f12 0 = true then _ else f12) = 0 ↔ _
    rw [guard_eq_zero_iff]
    exact and_congr_right fun h => (foldRange_set_eq_zero_iff 1 _ f12 5 (by decide) _).trans
      (and_iff_right h)
  have hL4 : ∀ j : ℕ, j < eqs.size → (Hax.index eqs (j : Int)).1.size = 1 ∧
      0 ≤ imageElemIdx eqs j ∧ imageElemIdx eqs j < 2 ^ 32 ∧
      ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
        0 ≤ termScalar eqs j t ∧ termScalar eqs j t < 2 ^ 32 ∧
        0 ≤ termElemIdx eqs j t ∧ termElemIdx eqs j t < 2 ^ 32 := fun j hj =>
    ⟨(hL j hj).1, (hL j hj).2.1, (hL j hj).2.2.1, (hL j hj).2.2.2.2⟩
  have h4 : f14 = 0 →
      (f12 = 0 ↔ ∀ j : ℕ, j < eqs.size → imageElemIdx eqs j < els.size ∧
        ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size → termElemIdx eqs j t < els.size) ∧
      eu.size = els.size ∧
      (∀ p : ℕ, p < els.size → (Hax.index eu (p : Int) = true ↔
        ∃ j : ℕ, j < eqs.size ∧ (imageElemIdx eqs j = p ∨
          ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧ termElemIdx eqs j t = p))) ∧
      0 ≤ ms ∧ ms < 2 ^ 32 ∧
      (∀ j : ℕ, j < eqs.size → ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
        termScalar eqs j t ≤ ms) ∧
      (ms = 0 ∨ ∃ j : ℕ, j < eqs.size ∧
        ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧ termScalar eqs j t = ms) ∧
      nt = ∑ j ∈ Finset.range eqs.size, ((Hax.index eqs (j : Int)).2.size : Int) := fun h =>
    validate_terms_loop els eqs hL4 m6 (by
      show _ = (if Hax.beq f14 0 = true then _ else _)
      rw [if_pos (by rw [h]; rfl), h])
  have e4 : f12 = 0 ↔ f14 = 0 ∧ ∀ j : ℕ, j < eqs.size → imageElemIdx eqs j < els.size ∧
      ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size → termElemIdx eqs j t < els.size := by
    by_cases h : f14 = 0
    · rw [(h4 h).1]
      exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
    · have e : f12 = f14 := by
        show (if Hax.beq f14 0 = true then _ else (f14, eu1, c0, c0)).1 = f14
        rw [if_neg (by simp [Hax.beq, h])]
      rw [e]
      exact ⟨fun h' => absurd h' h, fun h' => absurd h'.1 h⟩
  have e3 : f14 = 0 ↔ f17 = 0 ∧
      ¬ Hax.gt (Hax.castVal_w 64 (Hax.array_len eqs)) SigmaProofs.U32_MAX = true ∧
      ∀ j, 0 ≤ j → j < Hax.array_len eqs → ¬ Hax.bor
        (Hax.gt (Hax.castVal_w 64 (Hax.array_len (SigmaProofs.«Equation.image» (Hax.index eqs j))))
          SigmaProofs.U32_MAX)
        (Hax.gt (Hax.castVal_w 64 (Hax.array_len (SigmaProofs.«Equation.terms» (Hax.index eqs j))))
          SigmaProofs.U32_MAX) = true := by
    show (if Hax.beq f17 0 = true then _ else f17) = 0 ↔ _
    rw [guard_eq_zero_iff]
    refine and_congr_right fun h => (foldRange_set_eq_zero_iff 0 _ f16 3 (by decide) _).trans ?_
    refine and_congr_left fun _ => ?_
    show (if Hax.gt (Hax.castVal_w 64 (Hax.array_len eqs)) SigmaProofs.U32_MAX = true then
      (3 : Int) else f17) = 0 ↔ _
    rw [h]
    by_cases hg : Hax.gt (Hax.castVal_w 64 (Hax.array_len eqs)) SigmaProofs.U32_MAX = true <;>
      simp [hg]
  have e2 : f17 = 0 ↔ f19 = 0 ∧ ∀ j, 0 ≤ j → j < Hax.array_len eqs → ¬ Hax.bor
      (Hax.beq (Hax.array_len (SigmaProofs.«Equation.image» (Hax.index eqs j))) 0)
      (Hax.beq (Hax.array_len (SigmaProofs.«Equation.terms» (Hax.index eqs j))) 0) = true := by
    show (if Hax.beq f19 0 = true then _ else f19) = 0 ↔ _
    rw [guard_eq_zero_iff]
    exact and_congr_right fun h => (foldRange_set_eq_zero_iff 0 _ f19 2 (by decide) _).trans
      (and_iff_right h)
  have e1 : f19 = 0 ↔ eqs.size ≠ 0 := by
    show (if Hax.beq (Hax.array_len eqs) 0 = true then (1 : Int) else 0) = 0 ↔ _
    by_cases hs : eqs.size = 0 <;> simp [Hax.beq, Hax.array_len, hs]
  have hsuF : f14 = 0 → su.size = (Hax.add (Hax.castVal_w Hax.usizeBits ms) 1).toNat ∧
      ∀ q : ℕ, q < (Hax.add (Hax.castVal_w Hax.usizeBits ms) 1).toNat →
        (Hax.index su (q : Int) = true ↔ ∃ j : ℕ, j < eqs.size ∧
          ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧ termScalar eqs j t = q) := by
    intro h
    obtain ⟨-, -, -, hm0, hm1, hall, -, -⟩ := h4 h
    refine validate_scalar_used_loop eqs _ (fun j hj t ht => ?_) su rfl
    obtain ⟨a, b, -, -⟩ := (hL4 j hj).2.2.2 t ht
    rw [castVal_usize_of_lt hm0 hm1]
    exact ⟨a, b, by have := hall j hj t ht; simp only [Hax.add]; omega⟩
  clear_value ne c0 c1 m9 f19 c2 m8 f17 f16 c3 m7 f14 eu1 c4 m6 f12 eu ms nt c5 m5 f10 c6 su1 su
    m4 f8 c7 m3 f6 c8 m2 f4 c9 m1 f2 nz1 nz c10 m0 f0
  simp only [e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, and_assoc]
  have hNe : Hax.array_len els = (els.size : Int) := rfl
  have hMe : Hax.array_len eqs = (eqs.size : Int) := rfl
  have h0 : (0 : Int) = ((0 : ℕ) : Int) := rfl
  have hb0 : (0 : Bool) = false := rfl
  obtain ⟨N2, N3, N3b⟩ := validate_counts_iff eqs hm fun j hj => ⟨(hL j hj).1, (hL j hj).2.2.2.1⟩
  have N5 : (∀ i : Int, 1 ≤ i → i < Hax.array_len els → ¬ Hax.beq (Hax.index eu i) 0 = true) ↔
      ∀ p : ℕ, 1 ≤ p → p < els.size → Hax.index eu (p : Int) = true := by
    rw [show (1 : Int) = ((1 : ℕ) : Int) from rfl, forall_int_range_iff, hNe]
    simp [Hax.beq, hb0]
  have N8 : (∀ i : Int, 0 ≤ i → i < Hax.array_len els →
      ¬ SigmaProofs.group_eq (Hax.index els i) SigmaProofs.identity = true) ↔
      ∀ p : ℕ, p < els.size →
        SigmaProofs.group_eq (Hax.index els (p : Int)) SigmaProofs.identity = false := by
    rw [h0, forall_int_range_iff, hNe]
    simp
  have N9 : (∀ j : Int, 0 ≤ j → j < Hax.array_len eqs → ¬ SigmaProofs.group_eq
      (SigmaProofs.image_entry els (Hax.index eqs j)) SigmaProofs.identity = true) ↔
      ∀ j : ℕ, j < eqs.size → SigmaProofs.group_eq
        (SigmaProofs.image_entry els (Hax.index eqs (j : Int))) SigmaProofs.identity = false := by
    rw [h0, forall_int_range_iff, hMe]
    simp
  have N6 : ∀ M : Int, (∀ s : Int, 0 ≤ s → s < M → ¬ Hax.beq (Hax.index su s) 0 = true) ↔
      ∀ q : ℕ, (q : Int) < M → Hax.index su (q : Int) = true := by
    intro M
    rw [h0, forall_int_range_iff]
    simp [Hax.beq, hb0]
  have N10 : ∀ M : Int, M ≤ 2 ^ 32 → ((∀ s : Int, 0 ≤ s → s < M →
      ¬ (!Hax.foldRange 0 (Hax.array_len eqs) false fun j nonzero =>
          if Hax.beq (SigmaProofs.group_eq (SigmaProofs.column_entry els (Hax.index eqs j)
            (Hax.castVal_w 32 s)) SigmaProofs.identity) 0 = true then true else nonzero) = true) ↔
      ∀ q : ℕ, (q : Int) < M → ∃ j : ℕ, j < eqs.size ∧ SigmaProofs.group_eq
        (SigmaProofs.column_entry els (Hax.index eqs (j : Int)) q) SigmaProofs.identity =
          false) := by
    intro M hM
    rw [h0, forall_int_range_iff]
    refine forall_congr' fun q => ?_
    simp only [zero_le, true_implies]
    refine imp_congr_right fun hq => ?_
    rw [Hax.castVal_w_of_lt (w := 32) (x := (q : Int)) (by omega) (by omega)]
    simp only [foldRange_set_true_iff, Bool.not_eq_true', Bool.not_eq_false, hMe]
    constructor
    · rintro ⟨j, hj0, hj1, hj2⟩
      exact ⟨j.toNat, by omega, by rw [Int.toNat_of_nonneg hj0]; simpa [Hax.beq, hb0] using hj2⟩
    · rintro ⟨j, hj, hj2⟩
      exact ⟨j, by omega, by omega, by simpa [Hax.beq, hb0] using hj2⟩
  constructor
  · rintro ⟨r1, r2, r3a, r3b, r4, r5, -, r6, r7a, r7b, r8, r9, r10, rn⟩
    have hf14 : f14 = 0 := e3.mpr ⟨e2.mpr ⟨e1.mpr r1, r2⟩, r3a, r3b⟩
    obtain ⟨-, -, hu, hms0, hms1, hall, -, -⟩ := h4 hf14
    obtain ⟨-, hsu⟩ := hsuF hf14
    have hcv : Hax.castVal_w Hax.usizeBits ms = ms := castVal_usize_of_lt hms0 hms1
    rw [hcv] at r6 r10 rn hsu
    simp only [Hax.add] at r6 r10 rn hsu
    rw [N6] at r6
    rw [N10 _ (by omega)] at r10
    refine ⟨N3.mp r3a, N3b.mp r3b, by omega, N2.mp r2, r4,
      fun p hp1 hp => (hu p hp).mp (N5.mp r5 p hp1 hp),
      fun j hj t ht => by have := hall j hj t ht; omega,
      fun q hq => (hsu q (by omega)).mp (r6 q (by omega)), by omega, r7b, N8.mp r8, N9.mp r9,
      fun q hq => r10 q (by omega)⟩
  · rintro ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13⟩
    have hf14 : f14 = 0 :=
      e3.mpr ⟨e2.mpr ⟨e1.mpr (by omega), N2.mpr r4⟩, N3.mpr r1, N3b.mpr r2⟩
    obtain ⟨-, -, hu, hms0, hms1, hall, hmax, hnt⟩ := h4 hf14
    obtain ⟨-, hsu⟩ := hsuF hf14
    have hcv : Hax.castVal_w Hax.usizeBits ms = ms := castVal_usize_of_lt hms0 hms1
    rw [hcv] at hsu
    simp only [Hax.add] at hsu
    have hn1 : 1 ≤ n := by
      have := r7 0 r3 0 (r4 0 r3)
      have := ((hL 0 r3).2.2.2.2 0 (r4 0 r3)).1
      omega
    have hmsn : ms + 1 = n := by
      obtain ⟨j, hj, t, ht, he⟩ := r8 (n - 1) (by omega)
      have h1 := hall j hj t ht
      rcases hmax with h | ⟨j', hj', t', ht', he'⟩
      · omega
      · have := r7 j' hj' t' ht'
        omega
    have hcard := succ_le_sum_terms eqs ms.toNat fun q hq => r8 q (by omega)
    rw [hcv, N6, N10 _ (by simp only [Hax.add]; omega)]
    simp only [Hax.add]
    refine ⟨by omega, N2.mpr r4, N3.mpr r1, N3b.mpr r2, r5,
      N5.mpr fun p hp1 hp => (hu p hp).mpr (r6 p hp1 hp), ?_,
      fun q hq => (hsu q (by omega)).mpr (r8 q (by omega)), by omega, r10, N8.mpr r11,
      N9.mpr r12, fun q hq => r13 q (by omega), by omega⟩
    rw [hnt]
    have : ((∑ j ∈ Finset.range eqs.size, (Hax.index eqs (j : Int)).2.size : ℕ) : Int) =
        ∑ j ∈ Finset.range eqs.size, ((Hax.index eqs (j : Int)).2.size : Int) := by push_cast; rfl
    omega

variable (E) in
/-- The core relation with `n` scalars and `m` equations over the element array `els` and
the equations `eqs`, read in the core layout: the image of equation `i` is the element of
its first image term, and its terms are the pairs (scalar index, element index) of its
terms. -/
def layoutRel (n m : ℕ) (els : Array (Array Int))
    (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))) :
    LinearRelation gp n m where
  elements := els.toList.map E.decG
  equations i :=
    { lhs := uidx (Hax.index (Hax.index eqs ((i : ℕ) : Int)).1 0).1
      terms := (List.range (Hax.index eqs ((i : ℕ) : Int)).2.size).map fun k : ℕ =>
        (uidx (Hax.index (Hax.index eqs ((i : ℕ) : Int)).2 (k : Int)).1,
          uidx (Hax.index (Hax.index eqs ((i : ℕ) : Int)).2 (k : Int)).2.1) }

variable (E) in
/-- Equations in the core layout with indices in the `u32` range: fewer than `2^64`
equations, each with one image term of coefficient one and fewer than `2^64` terms,
every term of coefficient one, every index in `[0, 2^32)`. -/
def CoreLayout (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))) :
    Prop :=
  eqs.size < 2 ^ 64 ∧ ∀ j : ℕ, j < eqs.size →
    (Hax.index eqs (j : Int)).1.size = 1 ∧
    0 ≤ (Hax.index (Hax.index eqs (j : Int)).1 0).1 ∧
    (Hax.index (Hax.index eqs (j : Int)).1 0).1 < 2 ^ 32 ∧
    E.decS (Hax.index (Hax.index eqs (j : Int)).1 0).2 = gp.scalarOne ∧
    (Hax.index eqs (j : Int)).2.size < 2 ^ 64 ∧
    ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
      0 ≤ (Hax.index (Hax.index eqs (j : Int)).2 (t : Int)).1 ∧
      (Hax.index (Hax.index eqs (j : Int)).2 (t : Int)).1 < 2 ^ 32 ∧
      0 ≤ (Hax.index (Hax.index eqs (j : Int)).2 (t : Int)).2.1 ∧
      (Hax.index (Hax.index eqs (j : Int)).2 (t : Int)).2.1 < 2 ^ 32 ∧
      E.decS (Hax.index (Hax.index eqs (j : Int)).2 (t : Int)).2.2 = gp.scalarOne

/-- The sum over the filtered range is the sum over the range of the guarded summands. -/
theorem sum_map_filter_range (N : ℕ) (p : ℕ → Bool) (g : ℕ → gp.Scalar) :
    (((List.range N).filter p).map g).sum = ∑ k ∈ Finset.range N, if p k then g k else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    cases h : p N <;> simp [h]

/-- The decoded image entry of an equation with one image term of coefficient one is its
image element. -/
theorem image_entry_decG (els : Array (Array Int))
    (eq : (Array (Int × Array Int)) × (Array (Int × Int × Array Int)))
    (h1 : eq.1.size = 1) (hc : E.decS (Hax.index eq.1 0).2 = gp.scalarOne) :
    E.decG (@SigmaProofs.image_entry (groupSigmaProofsDeps E) els eq) =
      E.decG (Hax.index els (Hax.castVal_w Hax.usizeBits (Hax.index eq.1 0).1)) := by
  rw [image_entry_dot, E.decG_encG, h1, Finset.sum_range_one, Nat.cast_zero, hc]
  exact (congrArg gp.exp (one_mul _)).trans (gp.exp_dlog _)

/-- The decoded column entry of an equation whose terms have coefficient one is `exp` of
the sum of the discrete logarithms of the elements of its terms of scalar index `q`. -/
theorem column_entry_decG (els : Array (Array Int))
    (eq : (Array (Int × Array Int)) × (Array (Int × Int × Array Int))) (q : Int)
    (hc : ∀ k : ℕ, k < eq.2.size → E.decS (Hax.index eq.2 (k : Int)).2.2 = gp.scalarOne) :
    E.decG (@SigmaProofs.column_entry (groupSigmaProofsDeps E) els eq q) =
      gp.exp (∑ k ∈ Finset.range eq.2.size, if (Hax.index eq.2 (k : Int)).1 = q then
        gp.dlog (E.decG (Hax.index els
          (Hax.castVal_w Hax.usizeBits (Hax.index eq.2 (k : Int)).2.1))) else 0) := by
  rw [column_entry_dot, E.decG_encG]
  refine congrArg gp.exp (Finset.sum_congr rfl fun k hk => ?_)
  split_ifs
  · rw [hc k (Finset.mem_range.mp hk)]
    exact one_mul _
  · rfl

/-- An element of `layoutRel` in range is the decoded entry of `els`. -/
theorem layoutRel_elem (n m : ℕ) (els : Array (Array Int))
    (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))) (k : ℕ)
    (hk : k < els.size) : (layoutRel E n m els eqs).elem k = E.decG (Hax.index els (k : Int)) := by
  simp [LinearRelation.elem, layoutRel, List.getD_eq_getElem?_getD, hk, Hax.index_natCast]

/-- A column entry of `layoutRel` is `exp` of the sum of the discrete logarithms of the
elements of the terms of the given scalar index. -/
theorem layoutRel_column (n m : ℕ) (els : Array (Array Int))
    (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))) (j : ℕ)
    (i : Fin m) :
    (layoutRel E n m els eqs).column j i =
      gp.exp (∑ k ∈ Finset.range (Hax.index eqs ((i : ℕ) : Int)).2.size,
        if uidx (termScalar eqs i k) = j then
          gp.dlog ((layoutRel E n m els eqs).elem (uidx (termElemIdx eqs i k))) else 0) := by
  unfold LinearRelation.column
  rw [foldr_groupMul_eq_exp]
  congr 1
  simp only [layoutRel, List.filter_map, List.map_map]
  rw [sum_map_filter_range]
  exact Finset.sum_congr rfl fun k _ => by simp [Function.comp_def]

variable (E) in
/-- The decoded image entry of equation `i` in the core layout is the image entry of
`layoutRel`. -/
theorem image_entry_eq_image (n : ℕ) (els : Array (Array Int))
    (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int))))
    (hL : CoreLayout E eqs) (i : Fin eqs.size) (hi : imageElemIdx eqs i < els.size) :
    E.decG (@SigmaProofs.image_entry (groupSigmaProofsDeps E) els (Hax.index eqs ((i : ℕ) : Int))) =
      (layoutRel E n eqs.size els eqs).image i := by
  obtain ⟨h1, h0, h32, hc, -⟩ := hL.2 i i.isLt
  rw [image_entry_decG _ _ h1 hc, LinearRelation.image]
  have hx : uidx (imageElemIdx eqs i) = (imageElemIdx eqs i).toNat := by
    rw [uidx, castVal_usize_of_lt h0 h32]
  show _ = (layoutRel E n eqs.size els eqs).elem (uidx (imageElemIdx eqs i))
  have h0' : 0 ≤ imageElemIdx eqs i := h0
  rw [layoutRel_elem n eqs.size els eqs _ (by rw [hx]; omega), hx, Int.toNat_of_nonneg h0,
    castVal_usize_of_lt h0 h32]

variable (E) in
/-- The decoded column entry of equation `i` in the core layout is the column entry of
`layoutRel`, when its element indices are in range. -/
theorem column_entry_eq_column (n : ℕ) (els : Array (Array Int))
    (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int))))
    (hL : CoreLayout E eqs) (i : Fin eqs.size)
    (hi : ∀ t : ℕ, t < (Hax.index eqs ((i : ℕ) : Int)).2.size → termElemIdx eqs i t < els.size)
    (j : ℕ) :
    E.decG (@SigmaProofs.column_entry (groupSigmaProofsDeps E) els
        (Hax.index eqs ((i : ℕ) : Int)) j) =
      (layoutRel E n eqs.size els eqs).column j i := by
  obtain ⟨-, -, -, -, -, ht⟩ := hL.2 i i.isLt
  rw [column_entry_decG _ _ _ fun k hk => (ht k hk).2.2.2.2, layoutRel_column]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hs0, hs1, he0, he1, -⟩ := ht k (Finset.mem_range.mp hk)
  have hs0' : 0 ≤ termScalar eqs i k := hs0
  have he0' : 0 ≤ termElemIdx eqs i k := he0
  have hs : uidx (termScalar eqs i k) = (termScalar eqs i k).toNat := by
    rw [uidx, castVal_usize_of_lt hs0 hs1]
  have he : uidx (termElemIdx eqs i k) = (termElemIdx eqs i k).toNat := by
    rw [uidx, castVal_usize_of_lt he0 he1]
  have hlt := hi k (Finset.mem_range.mp hk)
  rw [hs, he, layoutRel_elem n eqs.size els eqs _ (by omega), Int.toNat_of_nonneg he0',
    castVal_usize_of_lt he0 he1]
  by_cases hj : (termScalar eqs i k).toNat = j
  · rw [if_pos hj, if_pos (show termScalar eqs i k = (j : Int) by omega)]
  · rw [if_neg hj, if_neg (fun h => hj (by have : termScalar eqs i k = (j : Int) := h; omega))]

/-- On equations in the core layout, the extracted `validate` succeeds with `n` scalars
exactly when the number of equations and the number of terms of each are at most
`U32_MAX` and `layoutRel` satisfies the draft's `ValidateInstance` with `n` scalars. -/
theorem validate_ok_iff {els : Array (Array Int)}
    {eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))}
    (hL : CoreLayout E eqs) (n : ℕ) :
    @SigmaProofs.validate (groupSigmaProofsDeps E) els eqs = .ok (n : Int) ↔
      (eqs.size ≤ 4294967295 ∧ ∀ j : ℕ, j < eqs.size →
        (Hax.index eqs (j : Int)).2.size ≤ 4294967295) ∧
      (layoutRel E n eqs.size els eqs).ValidateInstance := by
  obtain ⟨hm, hL'⟩ := hL
  rw [@validate_ok_iff_checks (groupSigmaProofsDeps E) els eqs hm (fun j hj =>
    ⟨(hL' j hj).1, (hL' j hj).2.1, (hL' j hj).2.2.1, (hL' j hj).2.2.2.2.1,
      fun t ht => ((hL' j hj).2.2.2.2.2 t ht).imp_right fun h => ⟨h.1, h.2.1, h.2.2.1⟩⟩) n]
  refine and_congr_right fun _ => ?_
  have hu : ∀ x : Int, 0 ≤ x → x < 2 ^ 32 → uidx x = x.toNat := fun x h0 h1 => by
    rw [uidx, castVal_usize_of_lt h0 h1]
  have hiE : ∀ j : ℕ, j < eqs.size →
      uidx (imageElemIdx eqs j) = (imageElemIdx eqs j).toNat ∧ 0 ≤ imageElemIdx eqs j :=
    fun j hj => ⟨hu _ (hL' j hj).2.1 (hL' j hj).2.2.1, (hL' j hj).2.1⟩
  have htS : ∀ j : ℕ, j < eqs.size → ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
      uidx (termScalar eqs j t) = (termScalar eqs j t).toNat ∧ 0 ≤ termScalar eqs j t :=
    fun j hj t ht => ⟨hu _ ((hL' j hj).2.2.2.2.2 t ht).1 ((hL' j hj).2.2.2.2.2 t ht).2.1,
      ((hL' j hj).2.2.2.2.2 t ht).1⟩
  have htE : ∀ j : ℕ, j < eqs.size → ∀ t : ℕ, t < (Hax.index eqs (j : Int)).2.size →
      uidx (termElemIdx eqs j t) = (termElemIdx eqs j t).toNat ∧ 0 ≤ termElemIdx eqs j t :=
    fun j hj t ht => ⟨hu _ ((hL' j hj).2.2.2.2.2 t ht).2.2.1
      ((hL' j hj).2.2.2.2.2 t ht).2.2.2.1, ((hL' j hj).2.2.2.2.2 t ht).2.2.1⟩
  have hlen : (layoutRel E n eqs.size els eqs).elements.length = els.size := by simp [layoutRel]
  have hmem : ∀ (i : Fin eqs.size) (x : ℕ × ℕ),
      x ∈ ((layoutRel E n eqs.size els eqs).equations i).terms ↔
        ∃ k : ℕ, k < (Hax.index eqs ((i : ℕ) : Int)).2.size ∧
          (uidx (termScalar eqs i k), uidx (termElemIdx eqs i k)) = x := by
    intro i x
    simp [layoutRel]
  have hlhs : ∀ i : Fin eqs.size,
      ((layoutRel E n eqs.size els eqs).equations i).lhs = uidx (imageElemIdx eqs i) :=
    fun _ => rfl
  have hnil : ∀ i : Fin eqs.size, ((layoutRel E n eqs.size els eqs).equations i).terms ≠ [] ↔
      0 < (Hax.index eqs ((i : ℕ) : Int)).2.size := by
    intro i
    simp [layoutRel, Nat.pos_iff_ne_zero]
  have hge : ∀ a : Array Int, (@SigmaProofs.SigmaProofsDeps.group_eq (groupSigmaProofsDeps E) a
      (@SigmaProofs.SigmaProofsDeps.identity (groupSigmaProofsDeps E)) = false) ↔
        E.decG a ≠ gp.identity := by
    intro a
    simp [E.decG_encG]
  have hhead : (layoutRel E n eqs.size els eqs).elements.head? = some gp.generator ↔
      0 < els.size ∧ @SigmaProofs.SigmaProofsDeps.group_eq (groupSigmaProofsDeps E)
        (Hax.index els 0) (@SigmaProofs.SigmaProofsDeps.generator (groupSigmaProofsDeps E)) =
          true := by
    rcases Nat.eq_zero_or_pos els.size with h0 | h0 <;>
      simp [layoutRel, h0, E.decG_encG, Hax.index, Array.eq_empty_of_size_eq_zero,
        List.head?_eq_getElem?]
  have hnoid : (∀ g ∈ (layoutRel E n eqs.size els eqs).elements, g ≠ gp.identity) ↔
      ∀ p : ℕ, p < els.size → @SigmaProofs.SigmaProofsDeps.group_eq (groupSigmaProofsDeps E)
        (Hax.index els (p : Int)) (@SigmaProofs.SigmaProofsDeps.identity (groupSigmaProofsDeps E)) =
          false := by
    simp [layoutRel, Array.mem_iff_getElem, E.decG_encG]
    exact ⟨fun h p hp => by rw [Hax.index_natCast _ _ hp]; exact h _ p hp rfl,
      fun h g p hp hg => by subst hg; rw [← Hax.index_natCast _ _ hp]; exact h p hp⟩
  constructor
  · rintro ⟨k3, k4, k5, k6, k7, k8, k9, k11, k12, k13⟩
    refine ⟨k3, fun i => (hnil i).mpr (k4 i i.isLt), fun i => ⟨?_, fun x hx => ?_⟩,
      fun k hk hk0 => ?_, fun q hq => ?_, hhead.mpr k9, hnoid.mpr k11, fun i => ?_,
      fun q hq => ?_⟩
    · rw [hlhs, hlen, (hiE i i.isLt).1]
      have := (k5 i i.isLt).1
      omega
    · obtain ⟨k, hk, rfl⟩ := (hmem i x).mp hx
      rw [(htS i i.isLt k hk).1, (htE i i.isLt k hk).1]
      have := k7 i i.isLt k hk
      have := (k5 i i.isLt).2 k hk
      have := (htS i i.isLt k hk).2
      have := (htE i i.isLt k hk).2
      constructor <;> omega
    · rw [hlen] at hk
      obtain ⟨j, hj, h | ⟨t, ht, h⟩⟩ := k6 k (by omega) hk
      · refine ⟨⟨j, hj⟩, Or.inl ?_⟩
        rw [hlhs]
        simp only
        rw [(hiE j hj).1, h]
        simp
      · refine ⟨⟨j, hj⟩, Or.inr ⟨_, (hmem ⟨j, hj⟩ _).mpr ⟨t, ht, rfl⟩, ?_⟩⟩
        simp only
        rw [(htE j hj t ht).1, h]
        simp
    · obtain ⟨j, hj, t, ht, h⟩ := k8 q hq
      refine ⟨⟨j, hj⟩, _, (hmem ⟨j, hj⟩ _).mpr ⟨t, ht, rfl⟩, ?_⟩
      simp only
      rw [(htS j hj t ht).1, h]
      simp
    · rw [← image_entry_eq_image E n els eqs ⟨hm, hL'⟩ i (k5 i i.isLt).1]
      exact (hge _).mp (k12 i i.isLt)
    · obtain ⟨j, hj, h⟩ := k13 q hq
      refine ⟨⟨j, hj⟩, ?_⟩
      rw [← column_entry_eq_column E n els eqs ⟨hm, hL'⟩ ⟨j, hj⟩ (k5 j hj).2 q]
      exact (hge _).mp h
  · intro v
    have k5F : ∀ i : Fin eqs.size, imageElemIdx eqs ((i : ℕ) : Int) < els.size ∧
        ∀ t : ℕ, t < (Hax.index eqs ((i : ℕ) : Int)).2.size →
          termElemIdx eqs ((i : ℕ) : Int) t < els.size := by
      intro i
      obtain ⟨h1, h2⟩ := v.indexValid i
      rw [hlhs, hlen, (hiE i i.isLt).1] at h1
      refine ⟨by have := (hiE i i.isLt).2; omega, fun t ht => ?_⟩
      have h3 := (h2 _ ((hmem i _).mpr ⟨t, ht, rfl⟩)).2
      rw [hlen, (htE i i.isLt t ht).1] at h3
      have := (htE i i.isLt t ht).2
      omega
    have k6 : ∀ p : ℕ, 1 ≤ p → p < els.size → ∃ j : ℕ, j < eqs.size ∧
        (imageElemIdx eqs j = p ∨
          ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧ termElemIdx eqs j t = p) := by
      intro p hp1 hp
      obtain ⟨i, h⟩ := v.element_used p (by rw [hlen]; exact hp) (by omega)
      refine ⟨i, i.isLt, ?_⟩
      rcases h with h | ⟨x, hx, hx2⟩
      · left
        rw [hlhs, (hiE i i.isLt).1] at h
        have := (hiE i i.isLt).2
        omega
      · right
        obtain ⟨k, hk, rfl⟩ := (hmem i x).mp hx
        simp only at hx2
        rw [(htE i i.isLt k hk).1] at hx2
        exact ⟨k, hk, by have := (htE i i.isLt k hk).2; omega⟩
    have k7F : ∀ i : Fin eqs.size, ∀ t : ℕ, t < (Hax.index eqs ((i : ℕ) : Int)).2.size →
        termScalar eqs ((i : ℕ) : Int) t < n := by
      intro i t ht
      have h := ((v.indexValid i).2 _ ((hmem i _).mpr ⟨t, ht, rfl⟩)).1
      rw [(htS i i.isLt t ht).1] at h
      have := (htS i i.isLt t ht).2
      omega
    have k8 : ∀ q : ℕ, q < n → ∃ j : ℕ, j < eqs.size ∧
        ∃ t : ℕ, t < (Hax.index eqs (j : Int)).2.size ∧ termScalar eqs j t = q := by
      intro q hq
      obtain ⟨i, x, hx, hx1⟩ := v.scalar_used q hq
      obtain ⟨k, hk, rfl⟩ := (hmem i x).mp hx
      simp only at hx1
      rw [(htS i i.isLt k hk).1] at hx1
      exact ⟨i, i.isLt, k, hk, by have := (htS i i.isLt k hk).2; omega⟩
    have k12F : ∀ i : Fin eqs.size, @SigmaProofs.SigmaProofsDeps.group_eq (groupSigmaProofsDeps E)
        (@SigmaProofs.image_entry (groupSigmaProofsDeps E) els (Hax.index eqs ((i : ℕ) : Int)))
        (@SigmaProofs.SigmaProofsDeps.identity (groupSigmaProofsDeps E)) = false := by
      intro i
      rw [hge, image_entry_eq_image E n els eqs ⟨hm, hL'⟩ i (k5F i).1]
      exact v.image_ne_identity i
    have k13 : ∀ q : ℕ, q < n → ∃ j : ℕ, j < eqs.size ∧
        @SigmaProofs.SigmaProofsDeps.group_eq (groupSigmaProofsDeps E)
          (@SigmaProofs.column_entry (groupSigmaProofsDeps E) els (Hax.index eqs (j : Int)) q)
          (@SigmaProofs.SigmaProofsDeps.identity (groupSigmaProofsDeps E)) = false := by
      intro q hq
      obtain ⟨i, h⟩ := v.column_ne_identity q hq
      refine ⟨i, i.isLt, ?_⟩
      rw [hge, column_entry_eq_column E n els eqs ⟨hm, hL'⟩ i (k5F i).2 q]
      exact h
    exact ⟨v.equations_pos, fun j hj => (hnil ⟨j, hj⟩).mp (v.terms_ne_nil _),
      fun j hj => k5F ⟨j, hj⟩, k6, fun j hj => k7F ⟨j, hj⟩, k8, hhead.mp v.head_generator,
      hnoid.mp v.elements_ne_identity, fun j hj => k12F ⟨j, hj⟩, k13⟩

/-- The element array that the extracted `Instance_new` builds from the statement elements
`els`: the generator followed by `els`. -/
theorem instance_elements_eq [SigmaProofs.SigmaProofsDeps] (els : Array (Array Int)) :
    Hax.foldRange 0 (Hax.array_len els) (Hax.push #[] SigmaProofs.generator)
        (fun i a => Hax.push a (Hax.index els i)) = #[SigmaProofs.generator] ++ els := by
  have key := Hax.foldRange_induct (P := fun (i : Int) (a : Array (Array Int)) =>
      a.toList = SigmaProofs.generator :: els.toList.take i.toNat)
    (lo := 0) (hi := Hax.array_len els) (f := fun i a => Hax.push a (Hax.index els i))
    (init := Hax.push #[] SigmaProofs.generator) (by simp [Hax.array_len]) (by simp [Hax.push])
    (by
      intro i a h0 hi ha
      have hi' : i.toNat < els.size := by simp only [Hax.array_len] at hi; omega
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one]
      simp [Hax.push, ha, Hax.index_eq_getElem hi', hi'])
  apply Array.toList_inj.mp
  rw [key]
  simp [Hax.array_len]

/-- On equations in the core layout, the extracted `Instance_new` succeeds with `n` scalars
exactly when the counts are at most `U32_MAX` and `layoutRel` over the generator followed
by the statement elements satisfies the draft's `ValidateInstance` with `n` scalars. -/
theorem Instance_new_ok_iff {els : Array (Array Int)}
    {eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))}
    (hL : CoreLayout E eqs) (n : ℕ) :
    (∃ inst, @SigmaProofs.Instance_new (groupSigmaProofsDeps E) els eqs = .ok inst ∧
        inst.2.2.2 = (n : Int)) ↔
      (eqs.size ≤ 4294967295 ∧ ∀ j : ℕ, j < eqs.size →
        (Hax.index eqs (j : Int)).2.size ≤ 4294967295) ∧
      (layoutRel E n eqs.size (#[E.encG gp.generator] ++ els) eqs).ValidateInstance := by
  rw [← validate_ok_iff hL n, ← groupSigmaProofsDeps_generator E,
    ← @instance_elements_eq (groupSigmaProofsDeps E) els]
  unfold SigmaProofs.Instance_new
  simp only [Hax.deref]
  split
  · rename_i v hv
    rw [hv]
    simp [SigmaProofs.Instance]
  · rename_i r hr
    rw [hr]
    simp

/-! ### The Σ-protocol of the extracted functions -/

variable (E) in
/-- The statements of the extracted protocol: extracted instances well formed for `n`
scalars and `m` equations. -/
abbrev ExtStmt (n m : ℕ) := {inst : SigmaProofs.Instance_T // WellFormed E n m inst}

variable (E) in
/-- The Σ-protocol whose commitment, response, verifier and simulator are the extracted
functions `Instance_prover_commit`, `Instance_prover_response`, `Instance_verifier` and
`Instance_simulate_transcript` on encoded arguments, with decoded results. The extraction
has no special-soundness extractor; the extractor is that of `linearSigma`. -/
noncomputable def extSigma (n m : ℕ) (gen : PMF (ExtStmt E n m × (Fin n → gp.Scalar))) :
    Sigma where
  Stmt := ExtStmt E n m
  Wit := Fin n → gp.Scalar
  Com := Fin m → gp.G
  Ch := gp.Scalar
  Resp := Fin n → gp.Scalar
  Rand := Fin n → gp.Scalar
  SimRand := Fin n → gp.Scalar
  inhWit := ⟨fun _ => gp.scalarZero⟩
  rel s w := (decodeRel E n m s.1).Holds w
  gen := gen
  commit s w r :=
    match @SigmaProofs.Instance_prover_commit (groupSigmaProofsDeps E) s.1 (encVec E w)
        (encVec E r) with
    | .ok (a, _) => decCom E m a
    | .error _ => fun _ => gp.identity
  respond s w r c :=
    match @SigmaProofs.Instance_prover_commit (groupSigmaProofsDeps E) s.1 (encVec E w)
        (encVec E r) with
    | .ok (_, st) =>
      match @SigmaProofs.Instance_prover_response (groupSigmaProofsDeps E) s.1 st (E.encS c) with
      | .ok z => decVec E n z
      | .error _ => fun _ => gp.scalarZero
    | .error _ => fun _ => gp.scalarZero
  verify s a c z :=
    match @SigmaProofs.Instance_verifier (groupSigmaProofsDeps E) s.1 (encCom E a) (E.encS c)
        (encVec E z) with
    | .ok _ => true
    | .error _ => false
  simulate s c z :=
    match @SigmaProofs.Instance_simulate_transcript (groupSigmaProofsDeps E) s.1 (encVec E z)
        (E.encS c) with
    | .ok (a, _, z') => (decCom E m a, decVec E n z')
    | .error _ => (fun _ => gp.identity, z)
  extract _ _ c z c' z' j := gp.scalarDiv (gp.scalarSub (z j) (z' j)) (gp.scalarSub c c')

variable {n m : ℕ} {gen : PMF (ExtStmt E n m × (Fin n → gp.Scalar))}

noncomputable instance : DecidableEq (extSigma E n m gen).Stmt := Classical.decEq _

theorem extSigma_commit (s : ExtStmt E n m) (w r : Fin n → gp.Scalar) :
    (extSigma E n m gen).commit s w r = (decodeRel E n m s.1).map r := by
  simp [extSigma, Instance_prover_commit_eq s.2]

theorem extSigma_respond (s : ExtStmt E n m) (w r : Fin n → gp.Scalar) (c : gp.Scalar) :
    (extSigma E n m gen).respond s w r c = fun j => gp.scalarAdd (r j) (gp.scalarMul c (w j)) := by
  simp [extSigma, Instance_prover_commit_eq s.2, Instance_prover_response_eq s.2]

theorem extSigma_verify_iff (s : ExtStmt E n m) (a : Fin m → gp.G) (c : gp.Scalar)
    (z : Fin n → gp.Scalar) :
    (extSigma E n m gen).verify s a c z = true ↔ a = (decodeRel E n m s.1).simCommit c z := by
  have hv := Instance_verifier_ok_iff s.2 (encCom E a) c z
  rw [decCom_encCom] at hv
  simp only [show (encCom E a).size = m by simp [encCom], true_and] at hv
  simp only [extSigma]
  rw [← hv]
  split <;> simp_all

theorem extSigma_simulate (s : ExtStmt E n m) (c : gp.Scalar) (z : Fin n → gp.Scalar) :
    (extSigma E n m gen).simulate s c z = ((decodeRel E n m s.1).simCommit c z, z) := by
  simp [extSigma, SigmaProofs.Instance_simulate_transcript, Instance_simulate_response_eq s.2,
    Instance_simulate_commitment_eq s.2, Hax.deref]

/-- The Σ-protocol of the extracted functions is the Σ-protocol `linearSigma` of the
decoded relations. -/
theorem extSigma_eq :
    extSigma E n m gen = linearSigma gp n m (fun s : ExtStmt E n m => decodeRel E n m s.1) gen := by
  unfold extSigma linearSigma
  congr 1
  · funext s w r
    exact extSigma_commit (gen := gen) s w r
  · funext s w r c
    exact extSigma_respond (gen := gen) s w r c
  · funext s a c z
    exact Bool.eq_iff_iff.mpr ((extSigma_verify_iff (gen := gen) s a c z).trans
      (linearSigma_verify_iff (fun s : ExtStmt E n m => decodeRel E n m s.1) gen s a c z).symm)
  · funext s c z
    exact extSigma_simulate (gen := gen) s c z

/-- The extracted compact verification of `(c, z)`, the compact commitment followed by the
comparison of `c` with the challenge `H` of the decoded commitment, accepts exactly when
the compact verifier `linearCompactVerify` of the decoded relation accepts. -/
theorem extCompact_ok_iff (H : ExtStmt E n m → (Fin m → gp.G) → gp.Scalar) (s : ExtStmt E n m)
    (c : gp.Scalar) (z : Fin n → gp.Scalar) :
    (match @SigmaProofs.Instance_compact_commitment (groupSigmaProofsDeps E) s.1 (E.encS c)
        (encVec E z) with
      | .ok a => @SigmaProofs.compact_accept (groupSigmaProofsDeps E) (E.encS c)
          (E.encS (H s (decCom E m a)))
      | .error e => .error e) = .ok () ↔
      linearCompactVerify (fun s : ExtStmt E n m => decodeRel E n m s.1) H s c z = true := by
  simp only [SigmaProofs.Instance_compact_commitment, Instance_simulate_commitment_eq s.2,
    decCom_encCom, compact_accept_ok_iff, E.decS_encS, linearCompactVerify, decide_eq_true_eq]
  exact eq_comm

/-! ### Security of the extracted protocol -/

open scoped ENNReal
open CatCrypt.Crypto.FiatShamirROM.DuplexSponge

theorem extSigma_complete : (extSigma E n m gen).Complete :=
  extSigma_eq ▸ linearSigma_complete _ gen

theorem extSigma_specialSound : (extSigma E n m gen).SpecialSound :=
  extSigma_eq ▸ linearSigma_specialSound _ gen

theorem extSigma_perfectHVZK (hgen : ∀ s w, (s, w) ∈ gen.support → (decodeRel E n m s.1).Holds w) :
    (extSigma E n m gen).PerfectHVZK :=
  extSigma_eq ▸ linearSigma_perfectHVZK _ gen hgen

/-- The extracted protocol has perfect HVZK at every pair of the relation. -/
theorem extSigma_statHVZKAt (s : ExtStmt E n m) (w : Fin n → gp.Scalar)
    (hw : (decodeRel E n m s.1).Holds w) : (extSigma E n m gen).StatHVZKAt s w 0 := by
  have h := (extSigma_perfectHVZK (gen := PMF.pure (s, w)) fun s' w' hsw => by
    rw [PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsw
    obtain ⟨rfl, rfl⟩ := hsw
    exact hw).statHVZK s w ((PMF.mem_support_pure_iff _ _).mpr rfl)
  exact h

/-- **Knowledge soundness of the strong Fiat–Shamir proofs of the extracted protocol.**
For every adversary `A` with at most `qH` random-oracle queries, with
`ε = ksAdvantage A`, `ε·(ε/(qH + 1) − 1/|Scalar|) ≤ ksExtractProb A`. -/
theorem extSigma_ksExtractProb_ge {Sid : Type} [DecidableEq Sid] {qH : ℕ}
    (A : KSAdversary (extSigma E n m gen) Sid qH) :
    ksAdvantage A * (ksAdvantage A / ((qH + 1 : ℕ) : ℝ≥0∞) - 1 / Fintype.card gp.Scalar) ≤
      ksExtractProb A :=
  ksExtractProb_ge extSigma_specialSound A

/-- **Zero knowledge of the strong Fiat–Shamir proofs of the extracted protocol.** For a
commitment bound `γ` at every pair of the relation and every distinguisher with at most
`qH` random-oracle and `qP` proving queries, `zkReal D ≤ zkSim D + qP·(qH + qP)·γ`. -/
theorem extSigma_zkReal_le_zkSim {Sid : Type} [DecidableEq Sid] {γ : ℝ≥0∞}
    (hγ : ∀ s w, (decodeRel E n m s.1).Holds w → (extSigma E n m gen).CommitBoundAt s w γ)
    {qH qP : ℕ} (D : ZKDistinguisher (extSigma E n m gen) Sid qH qP) :
    zkReal D ≤ zkSim D + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ := by
  have h := zkReal_le_zkSim (P := extSigma E n m gen) (δ := 0) (γ := γ)
    (fun s w hw => extSigma_statHVZKAt s w hw) hγ D
  simpa only [mul_zero, zero_add] using h

/-- **Knowledge soundness of the duplex-sponge proofs of the extracted protocol.** For
prefix-free encodings and a challenge decoding with the minorant `(1 − β)·uniform`, every
adversary with at most `qH` oracle queries satisfies, with
`ε = dsKsAdvantage A − (qH + 1)·β`, `ε·(ε/(qH + 1) − 1/|Scalar|) ≤ ksExtractProb A`. -/
theorem extSigma_dsKsExtractProb_ge (Dp : DSParams (extSigma E n m gen))
    (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA) {β : ℝ≥0∞}
    (hβ : ∀ c, (1 - β) * PMF.uniformOfFintype gp.Scalar c ≤
      (PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB c)
    {qH : ℕ} (A : KSAdversary (extSigma E n m gen) SessionId qH) :
    (dsKsAdvantage Dp A - (qH + 1 : ℕ) * β) *
        ((dsKsAdvantage Dp A - (qH + 1 : ℕ) * β) / ((qH + 1 : ℕ) : ℝ≥0∞) -
          1 / Fintype.card gp.Scalar) ≤
      ksExtractProb A :=
  dsKsExtractProb_ge Dp extSigma_specialSound hX hA hβ A

/-- **Zero knowledge of the duplex-sponge proofs of the extracted protocol.** For a
commitment bound `γ` at every pair of the relation and every distinguisher with at most
`qH` random-oracle and `qP` proving queries against the transform with byte challenges,
`zkReal D ≤ zkSim D + qP·(qH + qP)·γ`. -/
theorem extSigma_dsZkReal_le_zkSim (Dp : DSParams (extSigma E n m gen)) {γ : ℝ≥0∞}
    (hγ : ∀ s w, (decodeRel E n m s.1).Holds w → (extSigma E n m gen).CommitBoundAt s w γ)
    {qH qP : ℕ} (Dz : ZKDistinguisher Dp.sigmaBytes SessionId qH qP) :
    zkReal Dz ≤ zkSim Dz + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ := by
  have h := dsZkReal_le_zkSim Dp (δ := 0) (γ := γ)
    (fun s w hw => extSigma_statHVZKAt s w hw) hγ Dz
  simpa only [mul_zero, zero_add] using h

/-! ### The default instance: ristretto255 with 32-byte little-endian encodings -/

/-- The 32 little-endian base-256 digits of `x` (of `x mod 256^32`). -/
def bytesLE32 (x : ℕ) : Array Int := Array.ofFn fun i : Fin 32 => ((x / 256 ^ (i : ℕ) % 256 : ℕ) : Int)

/-- The little-endian value of the first 32 entries of a byte array. -/
def ofBytesLE32 (a : Array Int) : ℕ := ∑ i : Fin 32, (a.getD i 0).toNat * 256 ^ (i : ℕ)

theorem ofBytesLE32_bytesLE32 (x : ℕ) : ofBytesLE32 (bytesLE32 x) = x % 256 ^ 32 := by
  have hsum : ∀ k, ∑ i ∈ Finset.range k, x / 256 ^ i % 256 * 256 ^ i = x % 256 ^ k := by
    intro k
    induction k with
    | zero => simp [Nat.mod_one]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul]
      ring
  rw [← hsum 32, ← Fin.sum_univ_eq_sum_range]
  unfold ofBytesLE32 bytesLE32
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [i.isLt, dite_true, Option.getD_some, Int.toNat_natCast]

theorem curve25519_l_lt : CatCrypt.Crypto.Ristretto255.curve25519_l < 256 ^ 32 := by
  unfold CatCrypt.Crypto.Ristretto255.curve25519_l
  norm_num

open CatCrypt.Crypto.Ristretto255 in
/-- The encodings of ristretto255 scalars and elements, both `ZMod ℓ` in `RistrettoParam`:
the 32 little-endian bytes of the representative in `[0, ℓ)`, decoded as the
little-endian value of the first 32 bytes reduced modulo `ℓ`. -/
noncomputable def ristrettoEncoding : GroupEncoding RistrettoParam where
  encS s := bytesLE32 (ZMod.val (n := curve25519_l) s)
  decS a := ((ofBytesLE32 a : ℕ) : ZMod curve25519_l)
  encG x := bytesLE32 (ZMod.val (n := curve25519_l) x)
  decG a := ((ofBytesLE32 a : ℕ) : ZMod curve25519_l)
  decS_encS s := by
    show ((ofBytesLE32 (bytesLE32 (ZMod.val (n := curve25519_l) s)) : ℕ) : ZMod curve25519_l) = s
    rw [ofBytesLE32_bytesLE32, Nat.mod_eq_of_lt ((ZMod.val_lt _).trans curve25519_l_lt),
      ZMod.natCast_zmod_val]
  decG_encG x := by
    show ((ofBytesLE32 (bytesLE32 (ZMod.val (n := curve25519_l) x)) : ℕ) : ZMod curve25519_l) = x
    rw [ofBytesLE32_bytesLE32, Nat.mod_eq_of_lt ((ZMod.val_lt _).trans curve25519_l_lt),
      ZMod.natCast_zmod_val]

/-- The `SigmaProofsDeps` instance of the extraction: ristretto255 (`RistrettoParam`) with
the encodings `ristrettoEncoding`. -/
noncomputable instance defaultSigmaProofsDeps : SigmaProofs.SigmaProofsDeps :=
  groupSigmaProofsDeps ristrettoEncoding

end SigmaProofsBridge

end CatCrypt.Crypto.SigmaProtocol.SurfaceDeps
