/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.WeakPRF
public import CatCryptCore.Examples.CyclicGroupRingPow
public import CatCryptCore.Crypto.OracleAdversary
public import CatCryptCore.Crypto.SPCompPMF

/-!
# Deterministic verifiable encryption (Chase, Perrin, Zaverucha 2020, §4)

A deterministic symmetric-key encryption with public verifiability, as a record `DetVE` of
algorithms with coins as explicit inputs, in the random-oracle model: the algorithms take the
random oracle `h : Hash` as an argument, the games sample it uniformly, and the adversary
queries it through `hcall`. The record has a setup of public parameters `Par`, key generation
`derive h s` from a seed `s` (the function `Derive`), the public key `pk`, deterministic
encryption `enc` and decryption `dec`, and the relation `rel` that the proof `π_Enc` of
`Prove` shows, with the honest commitments `commit` and witness `witness`.

The instance `DetVE.cpz20` is the scheme of §4.1 over a cyclic group `G` with an exponent ring
(`CyclicGroupRing`). The random oracle is the pair `(HashToG, Derive)`, the parameters are the
generators `(G_{a1}, G_{a2}, G_{y1}, G_{y2})`, and a message `m` is encrypted under the key
`(a1, a2)` as `E1 = HashToG(m)^{a1}`, `E2 = E1^{a2} · EncodeToG(m)`.

## Main definitions

* `DetVE` — the record; `DetVE.RelComplete` — the honest witness satisfies `rel`.
* `DetVE.cpz20` — the scheme of §4.1.
* `DetVE.cpaGame`, `DetVE.CPA_Advantage` — Definition 6 (real-or-random, each message
  encrypted at most once).
* `DetVE.uniqueCtGame`, `DetVE.UniqueCt_Advantage` — Definition 8 (unique ciphertexts).
* `DetVE.advKeyGame`, `DetVE.AdvKey_Advantage` — Definition 9 (correctness under adversarially
  chosen keys).
* `DetVE.ciGame`, `DetVE.CI_Advantage`, `DetVE.piGame`, `DetVE.PI_Advantage` — Definition 12
  (ciphertext and plaintext integrity).
* `DetVE.ccaGame`, `DetVE.CCA_Advantage` — CCA security for deterministic encryption
  (§7.2, Theorem 13), real-or-random as Definition 6 with a decryption oracle.

## Main results

* `DetVE.cpz20_dec_enc` — decryption inverts encryption when `EncodeToG` is decoded by
  `DecodeFromG` and `E1 ≠ 1`.
* `DetVE.cpz20_relComplete` — the witness `(a1, a2, z, -z a1)` satisfies the relation of
  `π_Enc` at the commitments `C_{y1} = G_{y1}^z M1`, `C_{y2} = G_{y2}^z M2`.

## References

* M. Chase, T. Perrin, G. Zaverucha, *The Signal Private Group System and Anonymous
  Credentials Supporting Efficient Verifiable Encryption*, CCS 2020, §4.1 and §7.2
  (Definitions 6, 8, 9, 12; Theorems 7, 10, 13). <https://eprint.iacr.org/2019/1416>
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KVAC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.OT
open scoped ENNReal

/-! ## The record -/

/-- A deterministic symmetric-key encryption with public verifiability in the random-oracle
model (CPZ20 §4, §7.2). The random oracle is a function `h : Hash` sampled uniformly, queried
at `HQ` with answers `HA` through `hcall`. -/
structure DetVE where
  /-- Public parameters, sampled uniformly by the setup. -/
  Par : Type
  /-- The functions of the random oracle. -/
  Hash : Type
  /-- Queries to the random oracle. -/
  HQ : Type
  /-- Answers of the random oracle. -/
  HA : Type
  /-- Seeds of key generation. -/
  Seed : Type
  /-- Secret keys. -/
  Key : Type
  /-- Public keys. -/
  PK : Type
  /-- Plaintexts. -/
  Msg : Type
  /-- Ciphertexts. -/
  Ct : Type
  /-- Commitments to a plaintext, the public input of `rel` beside key and ciphertext. -/
  Com : Type
  /-- Randomness of a commitment. -/
  ComRnd : Type
  /-- Witnesses of `rel`. -/
  Wit : Type
  [finPar : Fintype Par]
  [nePar : Nonempty Par]
  [finHash : Fintype Hash]
  [neHash : Nonempty Hash]
  [finSeed : Fintype Seed]
  [neSeed : Nonempty Seed]
  [finMsg : Fintype Msg]
  [neMsg : Nonempty Msg]
  [decMsg : DecidableEq Msg]
  [decCt : DecidableEq Ct]
  /-- Evaluation of the random oracle `h` at a query. -/
  hcall : Hash → HQ → HA
  /-- Key derivation from a seed (`Derive`). -/
  derive : Hash → Seed → Key
  /-- The public key of a secret key. -/
  pk : Par → Key → PK
  /-- Deterministic encryption. -/
  enc : Hash → Key → Msg → Ct
  /-- Decryption, `none` on rejection. -/
  dec : Hash → Key → Ct → Option Msg
  /-- The commitments to a plaintext with the given randomness. -/
  commit : Par → Hash → Msg → ComRnd → Com
  /-- The honest witness of `rel` for a key and a commitment randomness. -/
  witness : Key → ComRnd → Wit
  /-- The relation proved by `Prove`: the ciphertext encrypts, under a key consistent with
  the public key, the plaintext committed in the commitments. -/
  rel : Par → PK → Ct → Com → Wit → Prop

attribute [instance] DetVE.finPar DetVE.nePar DetVE.finHash DetVE.neHash DetVE.finSeed
  DetVE.neSeed DetVE.finMsg DetVE.neMsg DetVE.decMsg DetVE.decCt

namespace DetVE

variable (D : DetVE)

/-- The honest witness satisfies the relation at the honest commitments to the plaintext of
an honest encryption. -/
def RelComplete : Prop :=
  ∀ (par : D.Par) (h : D.Hash) (s : D.Seed) (m : D.Msg) (z : D.ComRnd),
    D.rel par (D.pk par (D.derive h s)) (D.enc h (D.derive h s) m) (D.commit par h m z)
      (D.witness (D.derive h s) z)

/-! ## Oracles -/

/-- Queries of the CPA game: a random-oracle query or an encryption query. -/
abbrev CpaQ := D.HQ ⊕ D.Msg

/-- Answers of the CPA game: a random-oracle answer, or a ciphertext (`none` for a repeated
plaintext). -/
abbrev CpaA := D.HA ⊕ Option D.Ct

/-- The CPA oracle at the random oracle `h` and the key `k`, real (`b = false`) or random
(`b = true`); its state is the list of plaintexts queried. A repeated plaintext is answered
with `none`; a fresh plaintext `m` with `enc h k m`, or with `enc h k r` for a uniform `r`. -/
noncomputable def cpaOracle (h : D.Hash) (k : D.Key) (b : Bool) (log : List D.Msg) :
    D.CpaQ → PMF (D.CpaA × List D.Msg)
  | .inl q => PMF.pure (.inl (D.hcall h q), log)
  | .inr m =>
    if m ∈ log then PMF.pure (.inr none, log)
    else if b then (PMF.uniformFintype D.Msg).map fun r => (.inr (some (D.enc h k r)), m :: log)
    else PMF.pure (.inr (some (D.enc h k m)), m :: log)

/-- The random-oracle-only oracle at `h`, stateless. -/
noncomputable def hashOracle (h : D.Hash) (s : Unit) (q : D.HQ) : PMF (D.HA × Unit) :=
  PMF.pure (D.hcall h q, s)

/-- The uniform distribution of the setup: parameters, random oracle and seed. -/
noncomputable def setup : PMF (D.Par × D.Hash × D.Seed) :=
  (PMF.uniformFintype D.Par).bind fun par => (PMF.uniformFintype D.Hash).bind fun h =>
    (PMF.uniformFintype D.Seed).map fun s => (par, h, s)

/-! ## Definition 6: CPA security of deterministic encryption -/

/-- The CPA game of Definition 6 in world `b`: set up `par`, `h` and the key
`k = derive h s`, run `A par (pk par k)` against `cpaOracle h k b`, and return its guess. -/
noncomputable def cpaGame (b : Bool) (A : D.Par → D.PK → OracleAdv D.CpaQ D.CpaA Bool) :
    SPComp Bool :=
  liftPMF (D.setup.bind fun x =>
    (OracleAdv.run (D.cpaOracle x.2.1 (D.derive x.2.1 x.2.2) b)
      (A x.1 (D.pk x.1 (D.derive x.2.1 x.2.2))) []).map Prod.fst)

/-- **CPA advantage (CPZ20 Definition 6).** The distinguishing advantage of `A` between the
real encryption oracle and the oracle encrypting uniform plaintexts, each plaintext queried at
most once. -/
noncomputable def CPA_Advantage (A : D.Par → D.PK → OracleAdv D.CpaQ D.CpaA Bool) :
    ℝ≥0∞ :=
  Advantage (D.cpaGame false A) (D.cpaGame true A)

/-! ## Definition 8: unique ciphertexts -/

open Classical in
/-- The unique-ciphertexts game of Definition 8: `A`, with access to the random oracle, outputs
a key `k` and ciphertexts `c₁ ≠ c₂` that decrypt to the same plaintext. -/
noncomputable def uniqueCtGame (A : OracleAdv D.HQ D.HA (D.Key × D.Ct × D.Ct)) :
    SPComp Bool :=
  liftPMF ((PMF.uniformFintype D.Hash).bind fun h =>
    (OracleAdv.run (D.hashOracle h) A ()).map fun x =>
      decide (x.1.2.1 ≠ x.1.2.2 ∧ D.dec h x.1.1 x.1.2.1 = D.dec h x.1.1 x.1.2.2 ∧
        (D.dec h x.1.1 x.1.2.1).isSome))

/-- **Unique-ciphertexts advantage (CPZ20 Definition 8).** -/
noncomputable def UniqueCt_Advantage (A : OracleAdv D.HQ D.HA (D.Key × D.Ct × D.Ct)) :
    ℝ≥0∞ :=
  prTrue (D.uniqueCtGame A) Heap.empty

/-! ## Definition 9: correctness under adversarially chosen keys -/

/-- The game of Definition 9: `A`, with access to the random oracle, outputs a seed `s` and a
plaintext `m` such that `m` does not decrypt correctly under the key `derive h s`. -/
noncomputable def advKeyGame (A : OracleAdv D.HQ D.HA (D.Seed × D.Msg)) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype D.Hash).bind fun h =>
    (OracleAdv.run (D.hashOracle h) A ()).map fun x =>
      decide (D.dec h (D.derive h x.1.1) (D.enc h (D.derive h x.1.1) x.1.2) ≠ some x.1.2))

/-- **Advantage against correctness under adversarially chosen keys (CPZ20 Definition 9).** -/
noncomputable def AdvKey_Advantage (A : OracleAdv D.HQ D.HA (D.Seed × D.Msg)) : ℝ≥0∞ :=
  prTrue (D.advKeyGame A) Heap.empty

/-! ## Definition 12: ciphertext and plaintext integrity -/

/-- Answers of the integrity games: a random-oracle answer, or a ciphertext. -/
abbrev IntA := D.HA ⊕ Option D.Ct

/-- The encryption oracle of the integrity games at `h` and `k`; its state is the list of the
plaintexts queried with their ciphertexts. A repeated plaintext is answered with `none`. -/
noncomputable def intOracle (h : D.Hash) (k : D.Key) (log : List (D.Msg × D.Ct)) :
    D.CpaQ → PMF (D.IntA × List (D.Msg × D.Ct))
  | .inl q => PMF.pure (.inl (D.hcall h q), log)
  | .inr m =>
    if m ∈ log.map Prod.fst then PMF.pure (.inr none, log)
    else PMF.pure (.inr (some (D.enc h k m)), (m, D.enc h k m) :: log)

/-- The run of an integrity adversary: set up `par`, `h` and `k = derive h s`, run
`A par (pk par k)` against `intOracle h k`, and score its output ciphertext with `win`. -/
noncomputable def intGame
    (win : D.Hash → D.Key → D.Ct → List (D.Msg × D.Ct) → Bool)
    (A : D.Par → D.PK → OracleAdv D.CpaQ D.IntA D.Ct) : SPComp Bool :=
  liftPMF (D.setup.bind fun x =>
    (OracleAdv.run (D.intOracle x.2.1 (D.derive x.2.1 x.2.2))
      (A x.1 (D.pk x.1 (D.derive x.2.1 x.2.2))) []).map fun y =>
        win x.2.1 (D.derive x.2.1 x.2.2) y.1 y.2)

/-- The ciphertext-integrity win of Definition 12: `c*` is no ciphertext of an encryption
query and decrypts. -/
def ciWin (h : D.Hash) (k : D.Key) (c : D.Ct) (log : List (D.Msg × D.Ct)) : Bool :=
  decide (c ∉ log.map Prod.snd) && (D.dec h k c).isSome

/-- The plaintext-integrity win of Definition 12: `c*` decrypts to a plaintext of no
encryption query. -/
def piWin (h : D.Hash) (k : D.Key) (c : D.Ct) (log : List (D.Msg × D.Ct)) : Bool :=
  match D.dec h k c with
  | some m => decide (m ∉ log.map Prod.fst)
  | none => false

/-- The ciphertext-integrity game of Definition 12. -/
noncomputable def ciGame (A : D.Par → D.PK → OracleAdv D.CpaQ D.IntA D.Ct) : SPComp Bool :=
  D.intGame D.ciWin A

/-- The plaintext-integrity game of Definition 12. -/
noncomputable def piGame (A : D.Par → D.PK → OracleAdv D.CpaQ D.IntA D.Ct) : SPComp Bool :=
  D.intGame D.piWin A

/-- **Ciphertext-integrity advantage (CPZ20 Definition 12).** -/
noncomputable def CI_Advantage (A : D.Par → D.PK → OracleAdv D.CpaQ D.IntA D.Ct) : ℝ≥0∞ :=
  prTrue (D.ciGame A) Heap.empty

/-- **Plaintext-integrity advantage (CPZ20 Definition 12).** -/
noncomputable def PI_Advantage (A : D.Par → D.PK → OracleAdv D.CpaQ D.IntA D.Ct) : ℝ≥0∞ :=
  prTrue (D.piGame A) Heap.empty

/-! ## CCA security of deterministic encryption -/

/-- Queries of the CCA game: a random-oracle query, an encryption query or a decryption
query. -/
abbrev CcaQ := D.HQ ⊕ D.Msg ⊕ D.Ct

/-- Answers of the CCA game: a random-oracle answer, a ciphertext, or a decryption. -/
abbrev CcaA := D.HA ⊕ Option D.Ct ⊕ Option D.Msg

/-- The CCA oracle at `h` and `k` in world `b`; its state is the list of the plaintexts
queried and the list of the ciphertexts returned. Encryption queries are answered as by
`cpaOracle`; a decryption query at a returned ciphertext is answered with `none`, at any other
ciphertext `c` with `dec h k c`. -/
noncomputable def ccaOracle (h : D.Hash) (k : D.Key) (b : Bool)
    (st : List D.Msg × List D.Ct) : D.CcaQ → PMF (D.CcaA × (List D.Msg × List D.Ct))
  | .inl q => PMF.pure (.inl (D.hcall h q), st)
  | .inr (.inl m) =>
    if m ∈ st.1 then PMF.pure (.inr (.inl none), st)
    else if b then (PMF.uniformFintype D.Msg).map fun r =>
      (.inr (.inl (some (D.enc h k r))), (m :: st.1, D.enc h k r :: st.2))
    else PMF.pure (.inr (.inl (some (D.enc h k m))), (m :: st.1, D.enc h k m :: st.2))
  | .inr (.inr c) =>
    if c ∈ st.2 then PMF.pure (.inr (.inr none), st)
    else PMF.pure (.inr (.inr (D.dec h k c)), st)

/-- The CCA game in world `b`: as `cpaGame`, with the oracle `ccaOracle`. -/
noncomputable def ccaGame (b : Bool) (A : D.Par → D.PK → OracleAdv D.CcaQ D.CcaA Bool) :
    SPComp Bool :=
  liftPMF (D.setup.bind fun x =>
    (OracleAdv.run (D.ccaOracle x.2.1 (D.derive x.2.1 x.2.2) b)
      (A x.1 (D.pk x.1 (D.derive x.2.1 x.2.2))) ([], [])).map Prod.fst)

/-- **CCA advantage of deterministic encryption (CPZ20 §7.2, Theorem 13).** The real-or-random
advantage of Definition 6 with a decryption oracle that refuses the returned ciphertexts. -/
noncomputable def CCA_Advantage (A : D.Par → D.PK → OracleAdv D.CcaQ D.CcaA Bool) :
    ℝ≥0∞ :=
  Advantage (D.ccaGame false A) (D.ccaGame true A)

end DetVE

/-! ## The scheme of §4.1 -/

namespace DetVE

variable {G : Type} [CGR : CyclicGroupRing G]

/-- The commutative group of a cyclic group with exponent ring. -/
@[reducible] def commGroupOf : CommGroup G where
  mul := CGR.mul
  mul_assoc := CGR.mul_assoc
  one := CGR.one
  one_mul x := by
    change CGR.mul CGR.one x = x
    rw [CGR.mul_comm, CGR.mul_one]
  mul_one := CGR.mul_one
  inv := CGR.inv
  inv_mul_cancel x := by
    change CGR.mul (CGR.inv x) x = CGR.one
    rw [CGR.mul_comm, CGR.mul_inv]
  mul_comm := CGR.mul_comm

/-- `(x · y) · x⁻¹ = y`. -/
theorem mul_mul_inv_left (x y : G) : CGR.mul (CGR.mul x y) (CGR.inv x) = y := by
  let := commGroupOf (G := G)
  change x * y * x⁻¹ = y
  rw [mul_comm x y]
  exact mul_inv_cancel_right y x

/-- `(x · M) · (y · M)⁻¹ = x · y⁻¹`. -/
theorem mul_mul_inv_mul_right (x y M : G) :
    CGR.mul (CGR.mul x M) (CGR.inv (CGR.mul y M)) = CGR.mul x (CGR.inv y) := by
  let := commGroupOf (G := G)
  change x * M * (y * M)⁻¹ = x * y⁻¹
  group

/-- The third equation of `π_Enc` at the honest witness:
`M1^{a1} = (G_{y1}^z M1)^{a1} G_{y1}^{-z a1}`. -/
theorem elemPow_eq_commit_mul (gy1 M1 : G) (a1 z : CGR.Exp) :
    CyclicGroup.elemPow M1 a1 =
      CGR.mul (CyclicGroup.elemPow (CGR.mul (CyclicGroup.elemPow gy1 z) M1) a1)
        (CyclicGroup.elemPow gy1 (CGR.expNeg (CGR.expMul z a1))) := by
  rw [CyclicGroupRing.mul_elemPow, ← CyclicGroupRing.elemPow_mul, CyclicGroupRing.elemPow_neg]
  exact (mul_mul_inv_left _ _).symm

variable [DecidableEq G]

variable (Msg Seed : Type) [Fintype Msg] [Nonempty Msg] [DecidableEq Msg] [Fintype Seed]
  [Nonempty Seed] [DecidableEq Seed]

/-- **The deterministic verifiable encryption of CPZ20 §4.1.** Over the cyclic group `G`, with
`EncodeToG = encode` and `DecodeFromG = decode`:

* the random oracle is the pair `(HashToG, Derive) : (Msg → G) × (Seed → Exp²)`;
* the parameters are `(G_{a1}, G_{a2}, G_{y1}, G_{y2})`;
* the key of a seed `s` is `(a1, a2) = Derive(s)`, the public key `G_{a1}^{a1} G_{a2}^{a2}`;
* `Enc((a1, a2), m) = (E1, E2)` with `E1 = HashToG(m)^{a1}`, `E2 = E1^{a2} · EncodeToG(m)`;
* `Dec((a1, a2), (E1, E2))` decodes `m' = DecodeFromG(E2 / E1^{a2})` and returns it when
  `E1 = HashToG(m')^{a1}` and `E1 ≠ 1`;
* the commitments are `C_{y1} = G_{y1}^z M1`, `C_{y2} = G_{y2}^z M2`, the witness
  `(a1, a2, z, z1)` with `z1 = -z a1`, and the relation that of `π_Enc`:
  `pk = G_{a1}^{a1} G_{a2}^{a2}`, `C_{y2}/E2 = G_{y2}^z / E1^{a2}`,
  `E1 = C_{y1}^{a1} G_{y1}^{z1}`. -/
noncomputable def cpz20 (encode : Msg → G) (decode : G → Option Msg) : DetVE where
  Par := G × G × G × G
  Hash := (Msg → G) × (Seed → CGR.Exp × CGR.Exp)
  HQ := Msg ⊕ Seed
  HA := G ⊕ (CGR.Exp × CGR.Exp)
  Seed := Seed
  Key := CGR.Exp × CGR.Exp
  PK := G
  Msg := Msg
  Ct := G × G
  Com := G × G
  ComRnd := CGR.Exp
  Wit := CGR.Exp × CGR.Exp × CGR.Exp × CGR.Exp
  hcall h
    | .inl m => .inl (h.1 m)
    | .inr s => .inr (h.2 s)
  derive h s := h.2 s
  pk par k := CGR.mul (CyclicGroup.elemPow par.1 k.1) (CyclicGroup.elemPow par.2.1 k.2)
  enc h k m :=
    (CyclicGroup.elemPow (h.1 m) k.1,
      CGR.mul (CyclicGroup.elemPow (CyclicGroup.elemPow (h.1 m) k.1) k.2) (encode m))
  dec h k c := (decode (CGR.mul c.2 (CGR.inv (CyclicGroup.elemPow c.1 k.2)))).bind fun m =>
    if c.1 = CyclicGroup.elemPow (h.1 m) k.1 ∧ c.1 ≠ CGR.one then some m else none
  commit par h m z :=
    (CGR.mul (CyclicGroup.elemPow par.2.2.1 z) (h.1 m),
      CGR.mul (CyclicGroup.elemPow par.2.2.2 z) (encode m))
  witness k z := (k.1, k.2, z, CGR.expNeg (CGR.expMul z k.1))
  rel par pk c C w :=
    pk = CGR.mul (CyclicGroup.elemPow par.1 w.1) (CyclicGroup.elemPow par.2.1 w.2.1) ∧
    CGR.mul C.2 (CGR.inv c.2) =
      CGR.mul (CyclicGroup.elemPow par.2.2.2 w.2.2.1)
        (CGR.inv (CyclicGroup.elemPow c.1 w.2.1)) ∧
    c.1 = CGR.mul (CyclicGroup.elemPow C.1 w.1) (CyclicGroup.elemPow par.2.2.1 w.2.2.2)

variable {Msg Seed}

/-- **Correctness of §4.1.** Decryption inverts encryption under the key `k = (a1, a2)` when
`DecodeFromG` inverts `EncodeToG` at `m` and `E1 = HashToG(m)^{a1} ≠ 1`. -/
theorem cpz20_dec_enc (encode : Msg → G) (decode : G → Option Msg)
    (h : (Msg → G) × (Seed → CGR.Exp × CGR.Exp)) (k : CGR.Exp × CGR.Exp) (m : Msg)
    (hdec : decode (encode m) = some m) (hE1 : CyclicGroup.elemPow (h.1 m) k.1 ≠ CGR.one) :
    (cpz20 Msg Seed encode decode).dec h k ((cpz20 Msg Seed encode decode).enc h k m) =
      some m := by
  simp [cpz20, mul_mul_inv_left, hdec, hE1]

/-- **Completeness of the relation of `π_Enc` (§4.1).** The witness `(a1, a2, z, -z a1)`
satisfies the relation at the public key, an honest encryption and the honest commitments. -/
theorem cpz20_relComplete (encode : Msg → G) (decode : G → Option Msg) :
    (cpz20 Msg Seed encode decode).RelComplete := by
  intro par h s m z
  dsimp only [cpz20]
  exact ⟨rfl, mul_mul_inv_mul_right _ _ _, elemPow_eq_commit_mul _ _ _ _⟩

end DetVE

end CatCrypt.Crypto.KVAC
