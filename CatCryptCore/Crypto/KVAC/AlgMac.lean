/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.CyclicGroupRingPow
public import CatCryptCore.Crypto.OracleAdversary
public import CatCryptCore.Crypto.SPCompPMF

/-!
# Algebraic MACs and their unforgeability games

An algebraic MAC (Chase, Meiklejohn, Zaverucha 2014; Chase, Perrin, Zaverucha 2020, §2.3) as a
record `AlgMac` of algorithms with coins as explicit inputs: uniform public parameters `Par`
(the generators, which the schemes derive with a random oracle `HashToG`), key generation from
uniform coins, the public issuer parameters `pk`, the MAC from uniform coins, verification, and
the helper predicate `help` of the helper oracle.

The games are those of CPZ20 Definition 2 over oracle adversaries: the adversary receives the
parameters and the issuer parameters, queries a MAC oracle (and, in suf-cmva, a verification
oracle; in suf-cmva-Help, also the helper oracle), and outputs a forgery `(m*, σ*)`. It wins
when `σ*` verifies on `m*` and the forgery is fresh: `m*` was not MACed (uf-cma), or the pair
`(m*, σ*)` was not an answer of the MAC oracle (suf-cma, suf-cmva, suf-cmva-Help).

The instance `AlgMac.macGGM` is `MAC_GGM` (CMZ14, CPZ20 Definition 1) over a cyclic group `G`
with exponent ring, whose verification rejects `U = 1`.

## Main definitions

* `AlgMac`, `AlgMac.Correct` — the record and its correctness.
* `AlgMac.cmaOracle`, `AlgMac.cmvaOracle`, `AlgMac.helpOracle` — the oracles; their state is the
  list of MAC queries with their answers.
* `AlgMac.forgeGame` — the forgery game of an oracle and a freshness test.
* `AlgMac.ufCmaGame`, `AlgMac.UFCMA_Advantage` — uf-cma.
* `AlgMac.sufCmaGame`, `AlgMac.SUFCMA_Advantage` — suf-cma.
* `AlgMac.sufCmvaGame`, `AlgMac.SUFCMVA_Advantage` — suf-cmva.
* `AlgMac.sufCmvaHelpGame`, `AlgMac.SUFCMVAHelp_Advantage` — suf-cmva with the helper oracle
  `help` (Orrù 2024, the oracle `Help(A0, A, Z)` of the μCMZ unforgeability proof).
* `AlgMac.macGGM` — `MAC_GGM`.

## Main results

* `AlgMac.macGGM_verify_mac` — a `MAC_GGM` tag with `U ≠ 1` verifies.
* `AlgMac.macGGM_verify_one` — `MAC_GGM` verification rejects every tag with `U = 1`.

## Targets of later work

The following statements are the targets of the next steps of the zkgroup MAC programme; they
are not stated here as theorems.

* cmva to cma (CPZ20 Lemma 3, [BS20, Thm 6.1]): for a MAC with deterministic verification and
  an adversary `A` with `q_m` MAC and `q_v` verification queries,
  `SUFCMVA_Advantage A ≤ (q_v + 1) · SUFCMA_Advantage (B A)`, where `B A` guesses the index of the
  first verification query that accepts a fresh pair, answers the earlier ones with `false` and
  outputs that pair as its forgery.
* CPZ20 Theorem 14, Type 1 forgeries (`t*` not output by the MAC oracle): a reduction `B1` to
  `UFCMA_Advantage` of `macGGM`, which programs the generators `G_{x0} = U`, `G_{x1} = U^z` from a
  `MAC_GGM` tag on a random `z`.
* CPZ20 Theorem 14, Types 2 and 3 (`t* = t_i` for a MAC query `i`): a guess of `i*` among the `q_m`
  MAC queries and a DDH reduction `B2`, with the statistical terms of the uniform parameters;
  together, `SUFCMA_Advantage macN A ≤ UFCMA_Advantage macGGM (B1 A) + q_m · (DDH_Advantage (B2 A)
  + ε_stat)`.

## References

* M. Chase, S. Meiklejohn, G. Zaverucha, *Algebraic MACs and Keyed-Verification Anonymous
  Credentials*, CCS 2014. <https://eprint.iacr.org/2013/516>
* M. Chase, T. Perrin, G. Zaverucha, *The Signal Private Group System and Anonymous
  Credentials Supporting Efficient Verifiable Encryption*, CCS 2020, §2.3 (Definitions 1, 2,
  Lemma 3) and §7.3 (Theorem 14). <https://eprint.iacr.org/2019/1416>
* M. Orrù, *Revisiting Keyed-Verification Anonymous Credentials*, 2024.
  <https://eprint.iacr.org/2024/1552>
* D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Theorem 6.1.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KVAC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.OT
open scoped ENNReal

/-! ## The record -/

/-- An algebraic MAC with uniform public parameters, key generation and MAC from uniform coins,
deterministic verification, public issuer parameters and a helper predicate. -/
structure AlgMac where
  /-- Public parameters (the generators), sampled uniformly. -/
  Par : Type
  /-- Coins of key generation. -/
  KeyCoins : Type
  /-- Secret keys. -/
  Key : Type
  /-- Issuer parameters, given to the adversary. -/
  PK : Type
  /-- Messages. -/
  Msg : Type
  /-- Coins of the MAC algorithm. -/
  MacCoins : Type
  /-- Tags. -/
  Tag : Type
  /-- Queries to the helper oracle. -/
  HelpQ : Type
  [finPar : Fintype Par]
  [nePar : Nonempty Par]
  [finKeyCoins : Fintype KeyCoins]
  [neKeyCoins : Nonempty KeyCoins]
  [finMacCoins : Fintype MacCoins]
  [neMacCoins : Nonempty MacCoins]
  [decMsg : DecidableEq Msg]
  [decTag : DecidableEq Tag]
  /-- Key generation from coins. -/
  keyGen : Par → KeyCoins → Key
  /-- The issuer parameters of a key. -/
  pk : Par → Key → PK
  /-- The MAC of a message with the given coins. -/
  mac : Par → Key → Msg → MacCoins → Tag
  /-- Verification of a tag on a message. -/
  verify : Par → Key → Msg → Tag → Bool
  /-- The helper predicate, answered by the helper oracle. -/
  help : Par → Key → HelpQ → Bool

attribute [instance] AlgMac.finPar AlgMac.nePar AlgMac.finKeyCoins AlgMac.neKeyCoins
  AlgMac.finMacCoins AlgMac.neMacCoins AlgMac.decMsg AlgMac.decTag

namespace AlgMac

variable (M : AlgMac)

/-- Correctness: every tag produced by the MAC algorithm verifies. -/
def Correct : Prop :=
  ∀ (par : M.Par) (kc : M.KeyCoins) (m : M.Msg) (r : M.MacCoins),
    M.verify par (M.keyGen par kc) m (M.mac par (M.keyGen par kc) m r) = true

/-! ## Oracles -/

/-- The state of the oracles: the MAC queries with their answers. -/
abbrev Log := List (M.Msg × M.Tag)

/-- A MAC query at `m` under `k`: sample the coins uniformly, answer the tag and log the pair. -/
noncomputable def macStep (par : M.Par) (k : M.Key) (log : M.Log) (m : M.Msg) :
    PMF (M.Tag × M.Log) :=
  (PMF.uniformFintype M.MacCoins).map fun r => (M.mac par k m r, (m, M.mac par k m r) :: log)

/-- The oracle of uf-cma and suf-cma: MAC queries only. -/
noncomputable def cmaOracle (par : M.Par) (k : M.Key) (log : M.Log) (m : M.Msg) :
    PMF (M.Tag × M.Log) :=
  M.macStep par k log m

/-- Queries of suf-cmva: a MAC query or a verification query. -/
abbrev CmvaQ := M.Msg ⊕ (M.Msg × M.Tag)

/-- Answers of suf-cmva: a tag or a verification bit. -/
abbrev CmvaA := M.Tag ⊕ Bool

/-- The oracle of suf-cmva: MAC queries as in `cmaOracle`, verification queries answered with
`verify` and not logged. -/
noncomputable def cmvaOracle (par : M.Par) (k : M.Key) (log : M.Log) :
    M.CmvaQ → PMF (M.CmvaA × M.Log)
  | .inl m => (M.macStep par k log m).map fun x => (.inl x.1, x.2)
  | .inr q => PMF.pure (.inr (M.verify par k q.1 q.2), log)

/-- Queries of suf-cmva-Help: a MAC query, a verification query or a helper query. -/
abbrev HelpQry := M.Msg ⊕ (M.Msg × M.Tag) ⊕ M.HelpQ

/-- Answers of suf-cmva-Help: a tag, a verification bit or a helper bit. -/
abbrev HelpAns := M.Tag ⊕ Bool ⊕ Bool

/-- The oracle of suf-cmva-Help: as `cmvaOracle`, and helper queries answered with `help`. -/
noncomputable def helpOracle (par : M.Par) (k : M.Key) (log : M.Log) :
    M.HelpQry → PMF (M.HelpAns × M.Log)
  | .inl m => (M.macStep par k log m).map fun x => (.inl x.1, x.2)
  | .inr (.inl q) => PMF.pure (.inr (.inl (M.verify par k q.1 q.2)), log)
  | .inr (.inr q) => PMF.pure (.inr (.inr (M.help par k q)), log)

/-! ## Games -/

/-- The uniform distribution of the setup: parameters and key coins. -/
noncomputable def setup : PMF (M.Par × M.KeyCoins) :=
  (PMF.uniformFintype M.Par).bind fun par =>
    (PMF.uniformFintype M.KeyCoins).map fun kc => (par, kc)

/-- Freshness of uf-cma: the message of the forgery was not MACed. -/
def weakFresh (out : M.Msg × M.Tag) (log : M.Log) : Bool :=
  decide (out.1 ∉ log.map Prod.fst)

/-- Freshness of the strong games: the forgery is no answer of the MAC oracle. -/
def strongFresh (out : M.Msg × M.Tag) (log : M.Log) : Bool :=
  decide (out ∉ log)

/-- The forgery game of the oracle `O` and the freshness test `fresh`: set up `par` and the key
`k`, run `A par (pk par k)` against `O par k` from the empty log, and accept when the forgery
verifies under `k` and is fresh against the final log. -/
noncomputable def forgeGame {Q Ans : Type}
    (O : M.Par → M.Key → M.Log → Q → PMF (Ans × M.Log))
    (fresh : M.Msg × M.Tag → M.Log → Bool)
    (A : M.Par → M.PK → OracleAdv Q Ans (M.Msg × M.Tag)) : SPComp Bool :=
  liftPMF (M.setup.bind fun x =>
    (OracleAdv.run (O x.1 (M.keyGen x.1 x.2)) (A x.1 (M.pk x.1 (M.keyGen x.1 x.2))) []).map
      fun y => M.verify x.1 (M.keyGen x.1 x.2) y.1.1 y.1.2 && fresh y.1 y.2)

/-- The uf-cma game (CPZ20 Definition 2). -/
noncomputable def ufCmaGame (A : M.Par → M.PK → OracleAdv M.Msg M.Tag (M.Msg × M.Tag)) :
    SPComp Bool :=
  M.forgeGame M.cmaOracle M.weakFresh A

/-- **uf-cma advantage (CPZ20 Definition 2).** The probability that `A`, with MAC queries,
outputs a valid tag on a message it did not query. -/
noncomputable def UFCMA_Advantage
    (A : M.Par → M.PK → OracleAdv M.Msg M.Tag (M.Msg × M.Tag)) : ℝ≥0∞ :=
  prTrue (M.ufCmaGame A) Heap.empty

/-- The suf-cma game (CPZ20 Definition 2). -/
noncomputable def sufCmaGame (A : M.Par → M.PK → OracleAdv M.Msg M.Tag (M.Msg × M.Tag)) :
    SPComp Bool :=
  M.forgeGame M.cmaOracle M.strongFresh A

/-- **suf-cma advantage (CPZ20 Definition 2).** The probability that `A`, with MAC queries,
outputs a valid pair that is no answer of the MAC oracle. -/
noncomputable def SUFCMA_Advantage
    (A : M.Par → M.PK → OracleAdv M.Msg M.Tag (M.Msg × M.Tag)) : ℝ≥0∞ :=
  prTrue (M.sufCmaGame A) Heap.empty

/-- The suf-cmva game (CPZ20 Definition 2). -/
noncomputable def sufCmvaGame (A : M.Par → M.PK → OracleAdv M.CmvaQ M.CmvaA (M.Msg × M.Tag)) :
    SPComp Bool :=
  M.forgeGame M.cmvaOracle M.strongFresh A

/-- **suf-cmva advantage (CPZ20 Definition 2).** The suf-cma advantage of an adversary that
also queries a verification oracle. -/
noncomputable def SUFCMVA_Advantage
    (A : M.Par → M.PK → OracleAdv M.CmvaQ M.CmvaA (M.Msg × M.Tag)) : ℝ≥0∞ :=
  prTrue (M.sufCmvaGame A) Heap.empty

/-- The suf-cmva-Help game: suf-cmva with the helper oracle. -/
noncomputable def sufCmvaHelpGame
    (A : M.Par → M.PK → OracleAdv M.HelpQry M.HelpAns (M.Msg × M.Tag)) : SPComp Bool :=
  M.forgeGame M.helpOracle M.strongFresh A

/-- **suf-cmva-Help advantage (Orrù 2024, MAC security with the oracle `Help`).** The
suf-cmva advantage of an adversary that also queries the helper predicate. -/
noncomputable def SUFCMVAHelp_Advantage
    (A : M.Par → M.PK → OracleAdv M.HelpQry M.HelpAns (M.Msg × M.Tag)) : ℝ≥0∞ :=
  prTrue (M.sufCmvaHelpGame A) Heap.empty

end AlgMac

/-! ## `MAC_GGM` -/

namespace AlgMac

variable (G : Type) [CGR : CyclicGroupRing G] [DecidableEq G] [DecidableEq CGR.Exp]

/-- The exponent `x0 + x1 m` of `MAC_GGM` under the key `(x0, x1)`. -/
def ggmExp (k : CGR.Exp × CGR.Exp) (m : CGR.Exp) : CGR.Exp :=
  CGR.expAdd k.1 (CGR.expMul k.2 m)

/-- **`MAC_GGM` (CMZ14; CPZ20 Definition 1).** Over the cyclic group `G`:

* no parameters and no issuer parameters;
* the key is `(x0, x1)`, uniform;
* `MAC((x0, x1), m)` with coins `U` is `(U, U^{x0 + x1 m})`;
* `Verify((x0, x1), m, (U, U'))` accepts when `U ≠ 1` and `U' = U^{x0 + x1 m}`;
* the helper predicate at `(A0, A1, Z)` tests `Z = A0^{x0} A1^{x1}`, which at `(U, U^m, U')` is
  the equation of verification. -/
noncomputable def macGGM : AlgMac where
  Par := Unit
  KeyCoins := CGR.Exp × CGR.Exp
  Key := CGR.Exp × CGR.Exp
  PK := Unit
  Msg := CGR.Exp
  MacCoins := G
  Tag := G × G
  HelpQ := G × G × G
  keyGen _ kc := kc
  pk _ _ := ()
  mac _ k m U := (U, CyclicGroup.elemPow U (ggmExp G k m))
  verify _ k m σ := decide (σ.1 ≠ CGR.one ∧ σ.2 = CyclicGroup.elemPow σ.1 (ggmExp G k m))
  help _ k q := decide (q.2.2 = CGR.mul (CyclicGroup.elemPow q.1 k.1)
    (CyclicGroup.elemPow q.2.1 k.2))

/-- **Correctness of `MAC_GGM`.** A tag with `U ≠ 1` verifies. -/
theorem macGGM_verify_mac (par : Unit) (k : CGR.Exp × CGR.Exp) (m : CGR.Exp) (U : G)
    (hU : U ≠ CGR.one) :
    (macGGM G).verify par k m ((macGGM G).mac par k m U) = true := by
  simp [macGGM, hU]

/-- `MAC_GGM` verification rejects every tag with `U = 1`; without the check, `(1, 1)` would
verify on every message under every key. -/
theorem macGGM_verify_one (par : Unit) (k : CGR.Exp × CGR.Exp) (m : CGR.Exp) (V : G) :
    (macGGM G).verify par k m (CGR.one, V) = false := by
  simp [macGGM]

end AlgMac

end CatCrypt.Crypto.KVAC
