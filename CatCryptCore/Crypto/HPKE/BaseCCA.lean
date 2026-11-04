/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PKE.FOTransformT
public import CatCryptCore.Crypto.KEM.Games
public import CatCryptCore.Crypto.Constructions.HKDFPRF
public import CatCryptCore.ForMathlib.PMFSupport

/-!
# HPKE Base mode is IND-CCA secure: KEM, key schedule and one-time AEAD

HPKE Base mode single-shot encryption (RFC 9180, §5.1 and §6.1) to a public key `pk`
with associated data `ad` runs the KEM encapsulation `(k, enc) ← Encap(pk)`, derives
the AEAD key and base nonce `kd = KeySchedule(k)`, and returns `(enc, Seal(kd, ad, m))`;
decryption of `(enc, ad, ct)` runs `Decap(sk, enc)` and `Open(KeySchedule(k), ad, ct)`.
The KEM `S.kem` is a `KEM.Games.ROMScheme` whose programs query a random oracle
`D → H`, the key schedule `S.sched : K → Kd` is a function of the KEM key (the
`info` string is fixed), and `S.aead` is a deterministic AEAD keyed by `kd`.

## The game

`hpkeGame S A b` is IND-CCA in the random-oracle model (Alwen–Blanchet–Hauck–Kiltz–
Lipp–Riepel, EUROCRYPT 2021, §6): the challenger generates `(pk, sk)`; the first
stage of `A` receives `pk`, has the random oracle and a decryption oracle, and
returns `(m₀, m₁, ad)`; the challenger encapsulates to `pk` and seals `m₀` (`b = true`)
or `m₁` (`b = false`); the second stage receives `(enc*, ct*)`, has both oracles, and
the decryption oracle answers `none` on `(enc*, ad, ct*)`. Challenger and adversary
share one lazily sampled random-oracle table. The advantage is the distance between
the two values of `b`.

## The one-time AEAD games

* `otcpaGame` — a uniform key `kd`; the adversary chooses `(m₀, m₁, ad)` and
  guesses from `Seal(kd, ad, m_b)`.
* `otctxtGame` — a uniform key `kd`; the adversary has a decryption oracle before
  and after one encryption `Seal(kd, ad, m)` of its choice, which refuses the
  challenge after the encryption; it wins when some query decrypts.
* `schedGame` — the key schedule applied to a uniform KEM key against a uniform
  `kd`; `schedAdvantage_eq_prf` relates it to the PRF advantage of a function
  queried at two distinct labels, and `hkdfSched_advantage_le` instantiates it with
  HKDF Extract-then-Expand keyed by the KEM key.

## Main results

* `hpke_base_indcca` — for a KEM that is correct for every random-oracle function
  and every adversary `A`,
  `hpkeAdvantage S A ≤ Σ_{b} (romINDCCAAdvantage S.kem (kemReduction S A b) +
    schedAdvantage S.sched (schedReduction S A b) +
    otctxtAdvantage S.aead (ctxtReduction S A b)) + otcpaAdvantage S.aead (cpaReduction S A)`
* `hpke_base_indcca_dhkem` in `HPKE.BaseCCADHKEM` combines it with `dhkem_indcca`.

## Relation to `HPKESecurity.hpke_advantage_bound`

`HPKESecurity.hpke_advantage_bound` bounds a real-or-random game for one fixed
plaintext against an eavesdropper: the adversary sees the encapsulation and the
ciphertext, not the recipient public key, and has no decryption oracle and no random
oracle. It is stated over `SPComp` on words `W` with a DDH-based KEM. `hpkeGame` gives
the adversary the public key, the choice of the messages and associated data, the
random oracle and a decryption oracle; the eavesdropper game is the special case of
an adversary that asks no queries and ignores the public key, up to the change from
left-or-right to real-or-random. The statements live on different types and neither
is restated in terms of the other.

## Proof outline

1. The random oracle is sampled eagerly and the challenge encapsulation is moved
   before the first stage; with correctness, decryption queries on `enc*` are
   answered with the encapsulated key. The game is the real-key game of the KEM
   against `kemReduction S A b`; its random-key game uses an independent KEM key.
2. The key schedule of the independent KEM key is replaced by a uniform `kd`
   (`schedReduction`).
3. Decryption queries on `enc*` are answered `none`; the two games agree until such a
   query decrypts, which `ctxtReduction` detects.
4. The remaining game depends on `kd` only through the challenge ciphertext
   (`cpaReduction`).

## References

* R. Barnes, K. Bhargavan, B. Lipp, C. Wood, *Hybrid Public Key Encryption*,
  RFC 9180, §5.1, §6.1.
* J. Alwen, B. Blanchet, E. Hauck, E. Kiltz, B. Lipp, D. Riepel, *Analysing the
  HPKE Standard*, EUROCRYPT 2021, ePrint 2020/1499.
* R. Cramer, V. Shoup, *Design and Analysis of Practical Public-Key Encryption
  Schemes Secure against Adaptive Chosen Ciphertext Attack*, SIAM J. Comput. 2003,
  §7 (KEM/DEM composition).
* M. Bellare, C. Namprempre, *Authenticated Encryption*, ASIACRYPT 2000.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.HPKE.BaseCCA

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.KEM.Games
open CatCrypt.Crypto.PKE.FOTransformT (keyedRO extDist run_roOracle_map_fst_eq extDist_empty)
open CatCrypt.Crypto.Constructions.ECBCPRF (toOuterMeasure_flag_eq toOuterMeasure_le_add_flag)
open scoped ENNReal

/-! ## One-time AEAD -/

/-- A deterministic AEAD whose key `kd` holds the key and the nonce: `enc kd ad m` is
`Seal` and `dec kd ad ct` is `Open`. -/
structure OTAEAD (Kd AD M CT : Type) where
  /-- Authenticated encryption. -/
  enc : Kd → AD → M → CT
  /-- Authenticated decryption; `none` rejects. -/
  dec : Kd → AD → CT → Option M

section OneTime

variable {Kd AD M CT : Type} [Fintype Kd] [Nonempty Kd] (E : OTAEAD Kd AD M CT)

variable (AD M CT) in
/-- A two-stage one-time IND-CPA adversary. -/
structure OTCPAAdversary : Type 1 where
  /-- The state passed from the first to the second stage. -/
  St : Type
  /-- The first stage, returning two messages, associated data and a state. -/
  choose : PMF (M × M × AD × St)
  /-- The second stage on the challenge ciphertext. -/
  guess : St → CT → PMF Bool

/-- The one-time IND-CPA experiment with challenge bit `b`: a uniform key, and the
challenge seals the first message when `b = true` and the second when `b = false`. -/
noncomputable def otcpaGame (A : OTCPAAdversary AD M CT) (b : Bool) : PMF Bool :=
  (PMF.uniformFintype Kd).bind fun kd => A.choose.bind fun x =>
    A.guess x.2.2.2 (E.enc kd x.2.2.1 (if b then x.1 else x.2.1))

/-- The one-time IND-CPA advantage. -/
noncomputable def otcpaAdvantage (A : OTCPAAdversary AD M CT) : ℝ≥0∞ :=
  Advantage (liftPMF (otcpaGame E A true)) (liftPMF (otcpaGame E A false))

variable [DecidableEq AD] [DecidableEq CT]

/-- The decryption oracle for the key `kd` with the challenge `chal`: it answers
`none` on the challenge and `Open(kd, ad, ct)` otherwise, and sets the flag when the
answer is not `none`. -/
noncomputable def otDecOracle (kd : Kd) (chal : Option (AD × CT)) (fl : Bool) (q : AD × CT) :
    PMF (Option M × Bool) :=
  if chal = some q then PMF.pure (none, fl) else
    PMF.pure (E.dec kd q.1 q.2, fl || (E.dec kd q.1 q.2).isSome)

variable (AD M CT) in
/-- A two-stage one-time INT-CTXT adversary with at most `q` decryption queries in
each stage. -/
structure OTCTXTAdversary (q : ℕ) : Type 1 where
  /-- The state passed from the first to the second stage. -/
  St : Type
  /-- The first stage, with decryption queries, returning the associated data and the
  message to encrypt. -/
  choose : OracleAdv (AD × CT) (Option M) (AD × M × St)
  /-- The second stage on the ciphertext, with decryption queries. -/
  guess : St → CT → OracleAdv (AD × CT) (Option M) Unit
  /-- The first-stage query bound. -/
  isQueryBound₁ : choose.IsQueryBound q
  /-- The second-stage query bound. -/
  isQueryBound₂ : ∀ st ct, (guess st ct).IsQueryBound q

/-- The one-time INT-CTXT experiment: a uniform key; the first stage runs against the
decryption oracle; the challenger seals the chosen message; the second stage runs
against the decryption oracle refusing the challenge. The result is the flag: some
decryption query, other than the challenge, did not reject. -/
noncomputable def otctxtGame {q : ℕ} (A : OTCTXTAdversary AD M CT q) : PMF Bool :=
  (PMF.uniformFintype Kd).bind fun kd =>
    (OracleAdv.run (otDecOracle E kd none) A.choose false).bind fun x =>
      (OracleAdv.run (otDecOracle E kd (some (x.1.1, E.enc kd x.1.1 x.1.2.1)))
        (A.guess x.1.2.2 (E.enc kd x.1.1 x.1.2.1)) x.2).map fun y => y.2

/-- The one-time INT-CTXT advantage: the success probability of the experiment. -/
noncomputable def otctxtAdvantage {q : ℕ} (A : OTCTXTAdversary AD M CT q) : ℝ≥0∞ :=
  prTrue (liftPMF (otctxtGame E A)) Heap.empty

end OneTime

/-! ## Key schedule -/

section Schedule

variable {K Kd : Type} [Fintype K] [Nonempty K] [Fintype Kd] [Nonempty Kd]

/-- The key-schedule experiment for the distinguisher `B`: `B` receives the key
schedule of a uniform KEM key (`b = true`) or a uniform `kd` (`b = false`). -/
noncomputable def schedGame (sched : K → Kd) (B : Kd → PMF Bool) (b : Bool) : PMF Bool :=
  if b then (PMF.uniformFintype K).bind fun k => B (sched k)
  else (PMF.uniformFintype Kd).bind B

/-- The key-schedule advantage. -/
noncomputable def schedAdvantage (sched : K → Kd) (B : Kd → PMF Bool) : ℝ≥0∞ :=
  Advantage (liftPMF (schedGame sched B true)) (liftPMF (schedGame sched B false))

/-- The PRF distinguisher built from a key-schedule distinguisher `B`: it queries the
labels `iKey` and `iNonce` once each and runs `B` once on the pair of answers. -/
def schedPrfAdv {I V : Type} (iKey iNonce : I) (B : V × V → PMF Bool) : OracleAdv I V Bool :=
  .query iKey fun v₁ => .query iNonce fun v₂ => .rand (B (v₁, v₂)) .ret

omit [Fintype Kd] [Nonempty Kd] in
/-- A key schedule that evaluates a keyed function at two distinct labels has the PRF
advantage of `schedPrfAdv` as its advantage. -/
theorem schedAdvantage_eq_prf {I V : Type} [DecidableEq I] [DecidableEq V] [Fintype V]
    [Nonempty V] (F : K → I → V) {iKey iNonce : I} (hne : iKey ≠ iNonce)
    (B : V × V → PMF Bool) :
    schedAdvantage (fun k => (F k iKey, F k iNonce)) B =
      PRF_q_Advantage F (schedPrfAdv iKey iNonce B) := by
  have hreal : schedGame (fun k => (F k iKey, F k iNonce)) B true =
      (PMF.uniformFintype K).bind fun k =>
        (OracleAdv.run (keyedOracle F k) (schedPrfAdv iKey iNonce B) ()).map Prod.fst := by
    simp only [schedGame, ite_true, schedPrfAdv, OracleAdv.run_query, OracleAdv.run_rand,
      OracleAdv.run_ret, keyedOracle, PMF.pure_bind, PMF.map_bind, PMF.pure_map, PMF.bind_pure]
  have hideal : schedGame (fun k => (F k iKey, F k iNonce)) B false =
      (OracleAdv.run rfOracle (schedPrfAdv iKey iNonce B) []).map Prod.fst := by
    have hb : (iNonce == iKey) = false := beq_false_of_ne (Ne.symm hne)
    have hl : ∀ v : V, List.lookup iNonce [(iKey, v)] = none := fun v => by
      simp_all
    simp only [schedGame, Bool.false_eq_true, ite_false, schedPrfAdv, OracleAdv.run_query,
      OracleAdv.run_rand, OracleAdv.run_ret, rfOracle, List.lookup_nil, PMF.bind_map,
      Function.comp_def, hl, PMF.map_bind, PMF.pure_map, PMF.bind_pure, PMF.uniform_prod_eq_bind,
      PMF.bind_bind]
  unfold schedAdvantage PRF_q_Advantage realGame rfGame
  rw [hreal, hideal]

end Schedule

/-! ## HKDF key schedule -/

section HKDFSchedule

open CatCrypt.Crypto.Constructions.HKDFPRF

variable {Kb D I Kp Sa Mi : Type} [Fintype Kb] [Nonempty Kb] [DecidableEq Kb] [Fintype Kp]
  [Nonempty Kp] [Fintype Sa] [Nonempty Sa] [DecidableEq D] [DecidableEq I] [DecidableEq Mi]

/-- **The HKDF key schedule.** For HKDF Extract-then-Expand keyed by the KEM key as the
salt, with fixed input keying material `ikm` (in HPKE Base mode, the labelled empty
pre-shared key) and the key and base nonce expanded at the distinct labels `iKey` and
`iNonce`, the key-schedule advantage of every distinguisher `B` is at most the
extraction advantage of `extractAdv` plus the expansion advantage of `expandAdv`,
each run on `schedPrfAdv iKey iNonce B`. -/
theorem hkdfSched_advantage_le (X : Sa → Mi → Kp) (H : Kp → D → Kb)
    {msg : Option Kb → I → ℕ → D} (hinj : MsgInj msg) (n : ℕ) (ikm : Mi)
    {iKey iNonce : I} (hne : iKey ≠ iNonce)
    (B : List.Vector Kb n × List.Vector Kb n → PMF Bool) :
    schedAdvantage (fun salt => (hkdfSalted X H msg n ikm salt iKey,
        hkdfSalted X H msg n ikm salt iNonce)) B ≤
      PRF_q_Advantage X (extractAdv H msg n ikm (schedPrfAdv iKey iNonce B)) +
        PRF_q_Advantage H (expandAdv msg n (schedPrfAdv iKey iNonce B)) := by
  simp_all [hkdfSalted_prf_bound, schedAdvantage_eq_prf]

end HKDFSchedule

/-! ## Runs with unit state -/

section UnitRuns

variable {Q A Q' A' α β : Type}

/-- A distribution on pairs with a unit second component is determined by its first
marginal. -/
theorem bind_unit (p : PMF (β × Unit)) (g : β × Unit → PMF α) :
    p.bind g = (p.map Prod.fst).bind fun b => g (b, ()) := by
  rw [PMF.bind_map]
  rfl

/-- Running a simulated adversary followed by a continuation against a unit-state
oracle. -/
theorem run_bind_unit (O : Unit → Q' → PMF (A' × Unit)) (W : OracleAdv Q' A' α)
    (g : α → OracleAdv Q' A' β) (u : Unit) :
    OracleAdv.run O (W.bind g) u =
      ((OracleAdv.run O W u).map Prod.fst).bind fun a => OracleAdv.run O (g a) () := by
  grind [OracleAdv.run_bind, bind_unit]

end UnitRuns

/-! ## The KEM IND-CCA oracle as one program against the random oracle -/

section CCAProgram

variable {PK SK K C D H : Type} [DecidableEq C]

/-- The program answering one query of a KEM IND-CCA adversary against the random oracle,
for the secret key `sk` and the challenge `enc*`: a random-oracle query is forwarded, a
decapsulation query on `enc*` is answered `none`, and any other decapsulation query runs
decapsulation. -/
def ccaProg (R : ROMScheme PK SK K C D H) (sk : SK) (cstar : C) :
    D ⊕ C → OracleAdv D H (H ⊕ Option K)
  | .inl d => .query d fun h => .ret (.inl h)
  | .inr c => if c = cstar then .ret (.inr none) else
      (R.decaps sk c).bind fun ko => .ret (.inr ko)

/-- The oracle of the KEM IND-CCA game is the substitution of `ccaProg`. -/
theorem run_romCCAOracle_eq [DecidableEq D] [Fintype H] [Nonempty H]
    (R : ROMScheme PK SK K C D H) {α : Type} (sk : SK) (cstar : C)
    (W : OracleAdv (D ⊕ C) (H ⊕ Option K) α) (T : D → Option H) :
    OracleAdv.run (romCCAOracle R sk cstar) W T =
      OracleAdv.run roOracle (OracleAdv.subst (ccaProg R sk cstar) W) T := by
  rw [OracleAdv.run_subst]
  congr 1
  funext T' d
  cases d with
  | inl d =>
    simp only [ccaProg, romCCAOracle, OracleAdv.run_query, OracleAdv.run_ret]
    rw [← PMF.bind_pure_comp]; rfl
  | inr c =>
    simp only [ccaProg, romCCAOracle]
    split_ifs
    · simp
    · simp only [OracleAdv.run_bind, OracleAdv.run_ret]
      rw [← PMF.bind_pure_comp]; rfl

end CCAProgram

/-! ## HPKE Base mode -/

section HPKE

variable {PK SK K C D H Kd AD M CT : Type}

variable (PK SK K C D H Kd AD M CT) in
/-- HPKE Base mode single-shot encryption: a KEM in the random-oracle model, a key
schedule and a one-time AEAD. -/
structure HPKEBase where
  /-- The KEM. -/
  kem : ROMScheme PK SK K C D H
  /-- The key schedule, from the KEM key to the AEAD key and base nonce. -/
  sched : K → Kd
  /-- The AEAD. -/
  aead : OTAEAD Kd AD M CT

variable [DecidableEq D] [Fintype H] [Nonempty H] [DecidableEq C] [DecidableEq AD]
  [DecidableEq CT]

variable (S : HPKEBase PK SK K C D H Kd AD M CT)

/-- The challenge ciphertext for the AEAD key `kd`, the first-stage output `x` and the
bit `b`. -/
def chalCT {St : Type} (kd : Kd) (x : M × M × AD × St) (b : Bool) : CT :=
  S.aead.enc kd x.2.2.1 (if b then x.1 else x.2.1)

/-- The program answering one query of an HPKE adversary against the random oracle,
for the secret key `sk` and the challenge `chal`: a random-oracle query is forwarded; a
decryption query `(enc, ad, ct)` is answered `none` when it is the challenge, and
otherwise by decapsulating `enc` and opening `ct` under the key schedule. -/
def hpkeProg (sk : SK) (chal : Option (C × AD × CT)) :
    D ⊕ (C × AD × CT) → OracleAdv D H (H ⊕ Option M)
  | .inl d => .query d fun h => .ret (.inl h)
  | .inr q => if chal = some q then .ret (.inr none) else
      (S.kem.decaps sk q.1).bind fun ko =>
        .ret (.inr (ko.bind fun k => S.aead.dec (S.sched k) q.2.1 q.2.2))

variable (PK C D H AD M CT) in
/-- A two-stage IND-CCA adversary against HPKE with at most `qH` random-oracle queries
and `qD` decryption queries in each stage. -/
structure HPKEAdversary (qH qD : ℕ) : Type 1 where
  /-- The state passed from the first to the second stage. -/
  St : Type
  /-- The first stage on the public key, returning two messages, associated data and
  a state. -/
  choose : PK → OracleAdv (D ⊕ (C × AD × CT)) (H ⊕ Option M) (M × M × AD × St)
  /-- The second stage on the challenge encapsulation and ciphertext. -/
  guess : St → C × CT → OracleAdv (D ⊕ (C × AD × CT)) (H ⊕ Option M) Bool
  /-- The first-stage random-oracle query bound. -/
  isQueryBoundH₁ : ∀ pk, (choose pk).IsQueryBoundBy (Sum.elim (fun _ => 1) fun _ => 0) qH
  /-- The first-stage decryption query bound. -/
  isQueryBoundD₁ : ∀ pk, (choose pk).IsQueryBoundBy (Sum.elim (fun _ => 0) fun _ => 1) qD
  /-- The second-stage random-oracle query bound. -/
  isQueryBoundH₂ : ∀ st c, (guess st c).IsQueryBoundBy (Sum.elim (fun _ => 1) fun _ => 0) qH
  /-- The second-stage decryption query bound. -/
  isQueryBoundD₂ : ∀ st c, (guess st c).IsQueryBoundBy (Sum.elim (fun _ => 0) fun _ => 1) qD

/-- The IND-CCA experiment for HPKE Base mode with challenge bit `b`. The first stage
runs from the empty random-oracle table; the challenger encapsulates against the
resulting table and seals the chosen message; the second stage continues from the
table reached by encapsulation. -/
noncomputable def hpkeGame {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool) :
    PMF Bool :=
  S.kem.keygen.bind fun kp =>
    (OracleAdv.run roOracle (OracleAdv.subst (hpkeProg S kp.2 none) (A.choose kp.1))
      emptyTable).bind fun x =>
      (OracleAdv.run roOracle (S.kem.encaps kp.1) x.2).bind fun e =>
        (OracleAdv.run roOracle
          (OracleAdv.subst
            (hpkeProg S kp.2 (some (e.1.2, x.1.2.2.1, chalCT S (S.sched e.1.1) x.1 b)))
            (A.guess x.1.2.2.2 (e.1.2, chalCT S (S.sched e.1.1) x.1 b))) e.2).map Prod.fst

/-- The IND-CCA advantage of `A` against HPKE Base mode. -/
noncomputable def hpkeAdvantage {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) : ℝ≥0∞ :=
  Advantage (liftPMF (hpkeGame S A true)) (liftPMF (hpkeGame S A false))

/-- Correctness of a KEM in the random-oracle model for every oracle function: for
every generated key pair, every function `f : D → H` answering the oracle, and every
outcome `(k, enc)` of encapsulation against `f`, decapsulation of `enc` against `f`
returns `some k`. -/
def ROMCorrect (S : ROMScheme PK SK K C D H) : Prop :=
  ∀ kp ∈ S.keygen.support, ∀ f : D → H,
    ∀ e ∈ (OracleAdv.run (keyedRO f) (S.encaps kp.1) ()).support,
      (OracleAdv.run (keyedRO f) (S.decaps kp.2 e.1.2) ()).map Prod.fst = PMF.pure (some e.1.1)

/-! ### The KEM reduction -/

/-- The program of the KEM reduction answering one query of an HPKE adversary, for the
challenge encapsulation `enc*`, the AEAD key `kd` and the second-stage challenge `chal`:
a random-oracle query is forwarded; a decryption query on `enc*` is answered by opening
under `kd` (`none` on the challenge); any other decryption query forwards one
decapsulation query and opens under the key schedule of the answer. -/
def redProg (cstar : C) (kd : Kd) (chal : Option (AD × CT)) :
    D ⊕ (C × AD × CT) → OracleAdv (D ⊕ C) (H ⊕ Option K) (H ⊕ Option M)
  | .inl d => .query (.inl d) fun a => .ret (Sum.elim Sum.inl (fun _ => .inr none) a)
  | .inr q => if q.1 = cstar then
        .ret (.inr (if chal = some q.2 then none else S.aead.dec kd q.2.1 q.2.2))
      else .query (.inr q.1) fun a =>
        .ret (.inr (Sum.elim (fun _ => none)
          (fun ko => ko.bind fun k => S.aead.dec (S.sched k) q.2.1 q.2.2) a))

/-- The body of the KEM reduction on the public key `pk`, the challenge `enc*` and the
AEAD key `kd`: it runs both stages of `A` once, answering queries with `redProg`, and
seals the chosen message selected by `b` under `kd`. -/
def redRun {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool) (pk : PK)
    (cstar : C) (kd : Kd) : OracleAdv (D ⊕ C) (H ⊕ Option K) Bool :=
  (OracleAdv.subst (redProg S cstar kd none) (A.choose pk)).bind fun x =>
    OracleAdv.subst (redProg S cstar kd (some (x.2.2.1, chalCT S kd x b)))
      (A.guess x.2.2.2 (cstar, chalCT S kd x b))

/-- The query cost counting random-oracle queries of an HPKE adversary. -/
def costH : D ⊕ (C × AD × CT) → ℕ := Sum.elim (fun _ => 1) fun _ => 0

/-- The query cost counting decryption queries of an HPKE adversary. -/
def costD : D ⊕ (C × AD × CT) → ℕ := Sum.elim (fun _ => 0) fun _ => 1

omit [DecidableEq D] [Fintype H] [Nonempty H] in
theorem redProg_costH (cstar : C) (kd : Kd) (chal : Option (AD × CT))
    (d : D ⊕ (C × AD × CT)) :
    (redProg S cstar kd chal d).IsQueryBoundBy (Sum.elim (fun _ => 1) fun _ => 0)
      (costH d) := by
  cases d with
  | inl d => exact ⟨le_rfl, fun _ => trivial⟩
  | inr q =>
    simp only [redProg, costH, Sum.elim_inr]
    split
    · trivial
    · exact ⟨le_rfl, fun _ => trivial⟩

omit [DecidableEq D] [Fintype H] [Nonempty H] in
theorem redProg_costD (cstar : C) (kd : Kd) (chal : Option (AD × CT))
    (d : D ⊕ (C × AD × CT)) :
    (redProg S cstar kd chal d).IsQueryBoundBy (Sum.elim (fun _ => 0) fun _ => 1)
      (costD d) := by
  cases d with
  | inl d => exact ⟨le_rfl, fun _ => trivial⟩
  | inr q =>
    simp only [redProg, costD, Sum.elim_inr]
    split
    · trivial
    · exact ⟨le_rfl, fun _ => trivial⟩

/-- The IND-CCA adversary against the KEM built from an HPKE adversary `A` and a bit
`b`: on `(pk, enc*, k)` it runs both stages of `A` once with the AEAD key
`S.sched k`, forwards every random-oracle query, and forwards one decapsulation query
per decryption query of `A` on an encapsulation other than `enc*`. -/
def kemReduction {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool) :
    ROMINDCCAAdversary PK K C D H (qH + qH) (qD + qD) where
  run pk cstar k := redRun S A b pk cstar (S.sched k)
  isQueryBoundH pk cstar _ :=
    OracleAdv.isQueryBoundBy_bind
      (OracleAdv.isQueryBoundBy_subst costH _ (redProg_costH S cstar _ none)
        (A.isQueryBoundH₁ pk)) fun _ =>
      OracleAdv.isQueryBoundBy_subst costH _ (redProg_costH S cstar _ _) (A.isQueryBoundH₂ _ _)
  isQueryBoundD pk cstar _ :=
    OracleAdv.isQueryBoundBy_bind
      (OracleAdv.isQueryBoundBy_subst costD _ (redProg_costD S cstar _ none)
        (A.isQueryBoundD₁ pk)) fun _ =>
      OracleAdv.isQueryBoundBy_subst costD _ (redProg_costD S cstar _ _) (A.isQueryBoundD₂ _ _)

/-! ### The key-schedule reduction -/

/-- The key-schedule distinguisher built from an HPKE adversary `A` and a bit `b`: on
`kd` it generates a key pair, encapsulates against a lazily sampled random oracle, and
runs `redRun` once, answering the random oracle from the table and decapsulation
queries with the secret key. -/
noncomputable def schedReduction {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD)
    (b : Bool) (kd : Kd) : PMF Bool :=
  S.kem.keygen.bind fun kp =>
    (OracleAdv.run roOracle (S.kem.encaps kp.1) emptyTable).bind fun e =>
      (OracleAdv.run (romCCAOracle S.kem kp.2 e.1.2) (redRun S A b kp.1 e.1.2 kd) e.2).map
        Prod.fst

/-! ### The AEAD reductions -/

omit [DecidableEq C] [DecidableEq AD] [DecidableEq CT] in
variable (H) in
/-- The lazily sampled random oracle as a program on the table, without queries. -/
noncomputable def roProg {D' R' : Type} (T : D → Option H) (d : D) :
    OracleAdv D' R' (H × (D → Option H)) :=
  match T d with
  | some h => .ret (h, T)
  | none => .rand (PMF.uniformFintype H) fun h => .ret (h, Function.update T d (some h))

/-- The program of the INT-CTXT reduction answering one query of an HPKE adversary on
the random-oracle table `T`, for the secret key `sk` and the challenge `enc*`: a
random-oracle query is answered from the table; a decryption query on `enc*` forwards
`(ad, ct)` to the decryption oracle; any other decryption query is answered by
decapsulating against the table and opening under the key schedule. -/
noncomputable def ctxtProg (sk : SK) (cstar : C) (T : D → Option H) :
    D ⊕ (C × AD × CT) → OracleAdv (AD × CT) (Option M) ((H ⊕ Option M) × (D → Option H))
  | .inl d => (roProg H T d).bind fun r => .ret (.inl r.1, r.2)
  | .inr q => if q.1 = cstar then .query q.2 fun mo => .ret (.inr mo, T) else
      (OracleAdv.simulate (roProg H) (S.kem.decaps sk q.1) T).bind fun r =>
        .ret (.inr (r.1.bind fun k => S.aead.dec (S.sched k) q.2.1 q.2.2), r.2)

theorem isQueryBoundBy_zero {D' R' α : Type} (A : OracleAdv D' R' α) :
    A.IsQueryBoundBy (fun _ => 0) 0 := by
  induction A with
  | ret a => trivial
  | rand p k ih => exact ih
  | query d k ih => exact ⟨le_rfl, ih⟩

omit [DecidableEq C] [DecidableEq AD] [DecidableEq CT] in
theorem isQueryBound_roProg {D' R' : Type} (T : D → Option H) (d : D) :
    (roProg (D' := D') (R' := R') H T d).IsQueryBound 0 := by
  unfold roProg; split
  · trivial
  · exact fun _ => trivial

omit [DecidableEq AD] [DecidableEq CT] in
theorem isQueryBound_ctxtProg (sk : SK) (cstar : C) (T : D → Option H)
    (d : D ⊕ (C × AD × CT)) : (ctxtProg S sk cstar T d).IsQueryBound (costD d) := by
  cases d with
  | inl d =>
    have h := OracleAdv.isQueryBound_bind (isQueryBound_roProg (D' := AD × CT)
      (R' := Option M) T d) (f := fun r => (.ret (.inl r.1, r.2) :
        OracleAdv (AD × CT) (Option M) ((H ⊕ Option M) × (D → Option H)))) (n := 0)
      fun _ => trivial
    simpa [costD, ctxtProg] using h
  | inr q =>
    simp only [ctxtProg, costD, Sum.elim_inr]
    split
    · exact fun _ => trivial
    · have h := OracleAdv.isQueryBound_bind
        (OracleAdv.isQueryBound_simulate (roProg (D' := AD × CT) (R' := Option M) H)
          (fun _ => 0) (fun s d => isQueryBound_roProg s d)
          (isQueryBoundBy_zero (S.kem.decaps sk q.1)) T)
        (f := fun r => (.ret (.inr (r.1.bind fun k => S.aead.dec (S.sched k) q.2.1 q.2.2), r.2) :
          OracleAdv (AD × CT) (Option M) ((H ⊕ Option M) × (D → Option H)))) (n := 0)
        fun _ => trivial
      exact h.mono (by omega)

/-- The one-time INT-CTXT adversary built from an HPKE adversary `A` and a bit `b`. The
first stage generates a key pair, encapsulates against a lazily sampled random-oracle
table and runs the first stage of `A`; it asks for the encryption of the message
selected by `b`. The second stage runs the second stage of `A` on the challenge
encapsulation and the ciphertext. Both stages answer queries with `ctxtProg`, which
forwards the decryption queries of `A` on the challenge encapsulation. -/
noncomputable def ctxtReduction {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD)
    (b : Bool) : OTCTXTAdversary AD M CT qD where
  St := A.St × (D → Option H) × C × SK
  choose := .rand S.kem.keygen fun kp =>
    (OracleAdv.simulate (roProg H) (S.kem.encaps kp.1) emptyTable).bind fun e =>
      (OracleAdv.simulate (ctxtProg S kp.2 e.1.2) (A.choose kp.1) e.2).bind fun x =>
        .ret (x.1.2.2.1, (if b then x.1.1 else x.1.2.1), (x.1.2.2.2, x.2, e.1.2, kp.2))
  guess st ct :=
    (OracleAdv.simulate (ctxtProg S st.2.2.2 st.2.2.1) (A.guess st.1 (st.2.2.1, ct)) st.2.1).bind
      fun _ => .ret ()
  isQueryBound₁ kp := by
    have h₁ := OracleAdv.isQueryBound_simulate (roProg (D' := AD × CT) (R' := Option M) H)
      (fun _ => 0) (fun s d => isQueryBound_roProg s d)
      (isQueryBoundBy_zero (S.kem.encaps kp.1)) emptyTable
    have h := OracleAdv.isQueryBound_bind h₁ (n := qD) fun e => by
      have h₂ := OracleAdv.isQueryBound_bind
        (OracleAdv.isQueryBound_simulate _ costD (isQueryBound_ctxtProg S kp.2 e.1.2)
          (A.isQueryBoundD₁ kp.1) e.2)
        (f := fun x => (.ret (x.1.2.2.1, (if b then x.1.1 else x.1.2.1),
          (x.1.2.2.2, x.2, e.1.2, kp.2)) :
          OracleAdv (AD × CT) (Option M) (AD × M × (A.St × (D → Option H) × C × SK))))
        (n := 0) fun _ => trivial
      simpa using h₂
    simpa using h
  isQueryBound₂ st ct := by
    have h := OracleAdv.isQueryBound_bind
      (OracleAdv.isQueryBound_simulate _ costD (isQueryBound_ctxtProg S st.2.2.2 st.2.2.1)
        (A.isQueryBoundD₂ st.1 (st.2.2.1, ct)) st.2.1)
      (f := fun _ => (.ret () : OracleAdv (AD × CT) (Option M) Unit)) (n := 0) fun _ => trivial
    simpa using h

/-- The oracle of the games after decryption queries on `enc*` are rejected, for the
secret key `sk` and the challenge `enc*`: a random-oracle query is answered from the
table; a decryption query on `enc*` is answered `none`; any other decryption query is
answered by decapsulating against the table and opening under the key schedule. -/
noncomputable def nOracle (sk : SK) (cstar : C) (T : D → Option H) :
    D ⊕ (C × AD × CT) → PMF ((H ⊕ Option M) × (D → Option H))
  | .inl d => (roOracle T d).map fun r => (.inl r.1, r.2)
  | .inr q => if q.1 = cstar then PMF.pure (.inr none, T) else
      (OracleAdv.run roOracle (S.kem.decaps sk q.1) T).map fun r =>
        (.inr (r.1.bind fun k => S.aead.dec (S.sched k) q.2.1 q.2.2), r.2)

/-- The one-time IND-CPA adversary built from an HPKE adversary `A`. The first stage
generates a key pair, encapsulates against a lazily sampled random oracle, and runs
the first stage of `A` against `nOracle`; the second stage runs the second stage of
`A` on the challenge encapsulation and ciphertext against `nOracle`. -/
noncomputable def cpaReduction {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) :
    OTCPAAdversary AD M CT where
  St := A.St × (D → Option H) × C × SK
  choose := S.kem.keygen.bind fun kp =>
    (OracleAdv.run roOracle (S.kem.encaps kp.1) emptyTable).bind fun e =>
      (OracleAdv.run (nOracle S kp.2 e.1.2) (A.choose kp.1) e.2).map fun x =>
        (x.1.1, x.1.2.1, x.1.2.2.1, (x.1.2.2.2, x.2, e.1.2, kp.2))
  guess st ct :=
    (OracleAdv.run (nOracle S st.2.2.2 st.2.2.1) (A.guess st.1 (st.2.2.1, ct)) st.2.1).map
      Prod.fst

/-! ### The KEM hop -/

section KEMHop

/-- The HPKE experiment for the key pair `kp` as one program against the random oracle. -/
def hpkeProgram {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool)
    (kp : PK × SK) : OracleAdv D H Bool :=
  (OracleAdv.subst (hpkeProg S kp.2 none) (A.choose kp.1)).bind fun x =>
    (S.kem.encaps kp.1).bind fun e =>
      OracleAdv.subst (hpkeProg S kp.2 (some (e.2, x.2.2.1, chalCT S (S.sched e.1) x b)))
        (A.guess x.2.2.2 (e.2, chalCT S (S.sched e.1) x b))

/-- The real-key KEM experiment against `kemReduction S A b` for the key pair `kp` as one
program against the random oracle. -/
def kemProgram {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool)
    (kp : PK × SK) : OracleAdv D H Bool :=
  (S.kem.encaps kp.1).bind fun e =>
    OracleAdv.subst (ccaProg S.kem kp.2 e.2) (redRun S A b kp.1 e.2 (S.sched e.1))

theorem hpkeGame_eq_program {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool) :
    hpkeGame S A b = S.kem.keygen.bind fun kp =>
      (OracleAdv.run roOracle (hpkeProgram S A b kp) emptyTable).map Prod.fst := by
  unfold hpkeGame hpkeProgram
  refine congrArg _ (funext fun kp => ?_)
  simp only [OracleAdv.run_bind, PMF.map_bind]

theorem kemGame_eq_program [Fintype K] [Nonempty K] {qH qD : ℕ}
    (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool) :
    romINDCCAGame S.kem (kemReduction S A b) true = S.kem.keygen.bind fun kp =>
      (OracleAdv.run roOracle (kemProgram S A b kp) emptyTable).map Prod.fst := by
  unfold romINDCCAGame kemProgram
  refine congrArg _ (funext fun kp => ?_)
  simp only [ite_true, PMF.bind_const, run_romCCAOracle_eq, OracleAdv.run_bind, PMF.map_bind]
  rfl

omit [DecidableEq C] [DecidableEq AD] [DecidableEq CT] in
/-- Lazy and eager sampling of the random oracle for a program started from the empty
table. -/
theorem run_emptyTable_eq_eager [Fintype D] {α : Type} (W : OracleAdv D H α) :
    (OracleAdv.run roOracle W emptyTable).map Prod.fst =
      (PMF.uniformFintype (D → H)).bind fun f =>
        (OracleAdv.run (keyedRO f) W ()).map Prod.fst := by
  rw [run_roOracle_map_fst_eq, extDist_empty]

omit [DecidableEq D] [Fintype H] [Nonempty H] in
/-- The answers of the KEM reduction against the KEM oracle for a function `f` are the
answers of the HPKE decryption oracle, when decapsulation of `enc*` returns the
encapsulated key. -/
theorem run_redProg_ccaProg_eq (f : D → H) (sk : SK) (e : K × C)
    (hdec : (OracleAdv.run (keyedRO f) (S.kem.decaps sk e.2) ()).map Prod.fst =
      PMF.pure (some e.1))
    (chal : Option (AD × CT)) :
    (fun u q => OracleAdv.run (fun u' d => OracleAdv.run (keyedRO f) (ccaProg S.kem sk e.2 d) u')
        (redProg S e.2 (S.sched e.1) chal q) u) =
      fun u q => OracleAdv.run (keyedRO f) (hpkeProg S sk (chal.map fun p => (e.2, p)) q) u := by
  funext u q
  cases u
  cases q with
  | inl d => simp [redProg, ccaProg, hpkeProg, keyedRO]
  | inr q =>
    obtain ⟨c, ad, ct⟩ := q
    by_cases hc : c = e.2
    · subst hc
      have hch : (chal.map fun p => (e.2, p)) = some (e.2, ad, ct) ↔ chal = some (ad, ct) := by
        cases chal <;> simp
      simp only [redProg, hpkeProg, ite_true, OracleAdv.run_ret]
      by_cases h : chal = some (ad, ct)
      · simp [h]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (hch.mp h')), run_bind_unit, hdec,
          PMF.pure_bind]
        simp
    · have hch : (chal.map fun p => (e.2, p)) ≠ some (c, ad, ct) := by
        cases chal <;> simp [Ne.symm hc]
      simp only [redProg, hpkeProg, hc, ite_false, hch, OracleAdv.run_query,
        ccaProg, run_bind_unit, OracleAdv.run_ret, PMF.bind_map, Function.comp_def,
        PMF.pure_bind, PMF.bind_bind]
      rfl

omit [DecidableEq D] [Fintype H] [Nonempty H] in
/-- For a fixed random-oracle function, the HPKE experiment and the real-key KEM
experiment against `kemReduction S A b` have the same output distribution, when
decapsulation of every encapsulation returns its key. -/
theorem hpkeProgram_eager_eq {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool)
    (kp : PK × SK) (f : D → H)
    (hcorr : ∀ e ∈ (OracleAdv.run (keyedRO f) (S.kem.encaps kp.1) ()).support,
      (OracleAdv.run (keyedRO f) (S.kem.decaps kp.2 e.1.2) ()).map Prod.fst =
        PMF.pure (some e.1.1)) :
    (OracleAdv.run (keyedRO f) (hpkeProgram S A b kp) ()).map Prod.fst =
      (OracleAdv.run (keyedRO f) (kemProgram S A b kp) ()).map Prod.fst := by
  simp only [hpkeProgram, kemProgram, redRun, OracleAdv.subst_bind, run_bind_unit,
    OracleAdv.run_subst, PMF.map_bind]
  rw [PMF.bind_comm]
  refine PMF.bind_congr_support _ _ _ fun e he => ?_
  obtain ⟨e', he', rfl⟩ : ∃ e' ∈ (OracleAdv.run (keyedRO f) (S.kem.encaps kp.1) ()).support,
      e'.1 = e := by simpa [PMF.support_map] using he
  have h := run_redProg_ccaProg_eq S f kp.2 e'.1 (hcorr e' he')
  simp only [h, Option.map_none, Option.map_some]

/-- **KEM hop.** For a KEM correct for every random-oracle function, the HPKE experiment
with bit `b` is the real-key KEM experiment against `kemReduction S A b`. -/
theorem hpkeGame_eq_kemGame [Fintype K] [Nonempty K] [Fintype D] (hcorr : ROMCorrect S.kem)
    {qH qD : ℕ}
    (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool) :
    hpkeGame S A b = romINDCCAGame S.kem (kemReduction S A b) true := by
  rw [hpkeGame_eq_program, kemGame_eq_program]
  refine PMF.bind_congr_support _ _ _ fun kp hkp => ?_
  rw [run_emptyTable_eq_eager, run_emptyTable_eq_eager]
  exact congrArg _ (funext fun f => hpkeProgram_eager_eq S A b kp f (hcorr kp hkp f))

/-- **Key-schedule hop.** The random-key KEM experiment against `kemReduction S A b` is
the key-schedule experiment of `schedReduction S A b` on the key schedule of a uniform
KEM key. -/
theorem kemGame_false_eq_schedGame [Fintype K] [Nonempty K] {qH qD : ℕ}
    (A : HPKEAdversary PK C D H AD M CT qH qD)
    (b : Bool) [Fintype Kd] [Nonempty Kd] :
    romINDCCAGame S.kem (kemReduction S A b) false =
        schedGame S.sched (schedReduction S A b) true := by
  simp only [romINDCCAGame, schedGame, schedReduction, kemReduction, ite_true,
    Bool.false_eq_true, ite_false]
  rw [PMF.bind_comm (PMF.uniformFintype K)]
  refine congrArg _ (funext fun kp => ?_)
  rw [PMF.bind_comm (PMF.uniformFintype K)]

end KEMHop

/-! ### The integrity hop -/

section CtxtHop

/-- The oracle of the games in which the challenge encapsulation has the independent AEAD
key `kd`, on the random-oracle table and a flag. A random-oracle query is answered from
the table. A decryption query on `enc*` is answered `none` on the challenge; otherwise
it is answered by opening under `kd` when `real` and by `none` when not, and the flag is
set when opening does not reject. Any other decryption query is answered by
decapsulating against the table and opening under the key schedule. -/
noncomputable def okOracle (real : Bool) (sk : SK) (cstar : C) (kd : Kd)
    (chal : Option (AD × CT)) (s : (D → Option H) × Bool) :
    D ⊕ (C × AD × CT) → PMF ((H ⊕ Option M) × ((D → Option H) × Bool))
  | .inl d => (roOracle s.1 d).map fun r => (.inl r.1, (r.2, s.2))
  | .inr q => if q.1 = cstar then
      (if chal = some q.2 then PMF.pure (.inr none, s) else
        PMF.pure (.inr (if real then S.aead.dec kd q.2.1 q.2.2 else none),
          (s.1, s.2 || (S.aead.dec kd q.2.1 q.2.2).isSome)))
    else (OracleAdv.run roOracle (S.kem.decaps sk q.1) s.1).map fun r =>
      (.inr (r.1.bind fun k => S.aead.dec (S.sched k) q.2.1 q.2.2), (r.2, s.2))

/-- Both stages of `A` against `okOracle real` for the AEAD key `kd`, after key
generation and encapsulation; the result carries the final table and flag. -/
noncomputable def okDist (real : Bool) {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD)
    (b : Bool) (kd : Kd) : PMF (Bool × ((D → Option H) × Bool)) :=
  S.kem.keygen.bind fun kp =>
    (OracleAdv.run roOracle (S.kem.encaps kp.1) emptyTable).bind fun e =>
      (OracleAdv.run (okOracle S real kp.2 e.1.2 kd none) (A.choose kp.1) (e.2, false)).bind
        fun x => OracleAdv.run (okOracle S real kp.2 e.1.2 kd (some (x.1.2.2.1, chalCT S kd x.1 b)))
          (A.guess x.1.2.2.2 (e.1.2, chalCT S kd x.1 b)) x.2

theorem okOracle_true_map (sk : SK) (cstar : C) (kd : Kd) (chal : Option (AD × CT))
    (s : (D → Option H) × Bool) (q : D ⊕ (C × AD × CT)) :
    (okOracle S true sk cstar kd chal s q).map (Prod.map id Prod.fst) =
      OracleAdv.run (romCCAOracle S.kem sk cstar) (redProg S cstar kd chal q) s.1 := by
  cases q with
  | inl d =>
    simp only [okOracle, redProg, OracleAdv.run_query, romCCAOracle,
      OracleAdv.run_ret, PMF.map_comp, PMF.bind_map, Function.comp_def]
    rfl
  | inr q =>
    simp only [okOracle, redProg]
    split_ifs with hc hch
    · simp [PMF.pure_map]
    · simp [PMF.pure_map]
    · simp only [OracleAdv.run_query, romCCAOracle, hc, ite_false, OracleAdv.run_ret, PMF.map_comp,
        PMF.bind_map, Function.comp_def]
      rfl

theorem schedReduction_eq_okDist {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD)
    (b : Bool) (kd : Kd) :
    schedReduction S A b kd = (okDist S true A b kd).map Prod.fst := by
  have hrun : ∀ (sk : SK) (cstar : C) (chal : Option (AD × CT)) {α : Type}
      (W : OracleAdv (D ⊕ (C × AD × CT)) (H ⊕ Option M) α) (T : D → Option H) (fl : Bool),
      OracleAdv.run (romCCAOracle S.kem sk cstar) (OracleAdv.subst (redProg S cstar kd chal) W)
        T = (OracleAdv.run (okOracle S true sk cstar kd chal) W (T, fl)).map
          (Prod.map id Prod.fst) := by
    intro sk cstar chal α W T fl
    rw [OracleAdv.run_subst, OracleAdv.run_map_state _
      (fun T q => OracleAdv.run (romCCAOracle S.kem sk cstar) (redProg S cstar kd chal q) T)
      Prod.fst (fun s q => okOracle_true_map S sk cstar kd chal s q) W (T, fl)]
  unfold schedReduction okDist redRun
  simp only [PMF.map_bind]
  refine congrArg _ (funext fun kp => congrArg _ (funext fun e => ?_))
  rw [OracleAdv.run_bind, hrun kp.2 e.1.2 none _ e.2 false, PMF.bind_map, PMF.map_bind]
  refine congrArg _ (funext fun x => ?_)
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  rw [hrun kp.2 e.1.2 _ _ x.2.1 x.2.2, PMF.map_comp]
  rfl

theorem okOracle_apply_true_false (real : Bool) (sk : SK) (cstar : C) (kd : Kd)
    (chal : Option (AD × CT)) (T : D → Option H) (q : D ⊕ (C × AD × CT)) (a : H ⊕ Option M)
    (T' : D → Option H) : okOracle S real sk cstar kd chal (T, true) q (a, (T', false)) = 0 := by
  cases q with
  | inl d => rw [okOracle, PMF.map_apply]; simp
  | inr q =>
    simp only [okOracle]
    by_cases hc : q.1 = cstar
    · by_cases hch : chal = some q.2
      · simp [hc, hch, PMF.pure_apply]
      · simp [hc, hch, PMF.pure_apply]
    · rw [ite_eq_right hc, PMF.map_apply]; simp

theorem okOracle_apply_false_eq (sk : SK) (cstar : C) (kd : Kd) (chal : Option (AD × CT))
    (s : (D → Option H) × Bool) (q : D ⊕ (C × AD × CT)) (a : H ⊕ Option M) (T' : D → Option H) :
    okOracle S true sk cstar kd chal s q (a, (T', false)) =
      okOracle S false sk cstar kd chal s q (a, (T', false)) := by
  cases q with
  | inl d => rfl
  | inr q =>
    simp only [okOracle]
    by_cases hc : q.1 = cstar
    · by_cases hch : chal = some q.2
      · simp [hc, hch]
      · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_right hch, ite_eq_right hch]
        cases h : S.aead.dec kd q.2.1 q.2.2 with
        | none => simp
        | some m => simp [PMF.pure_apply]
    · rw [ite_eq_right hc, ite_eq_right hc]

omit [DecidableEq AD] [DecidableEq CT] [DecidableEq D] [Fintype H] [Nonempty H]
  [DecidableEq C] in
/-- **Identical until bad, for two stages.** A second stage run after first-stage
distributions that agree on unflagged outcomes, against oracles with sticky flags that
agree on transitions into unflagged states, gives distributions that agree on unflagged
outcomes. -/
theorem bind_run_apply_flag_false_eq {Q R α β σ : Type} (p₁ p₂ : PMF (α × (σ × Bool)))
    (hp : ∀ a t, p₁ (a, (t, false)) = p₂ (a, (t, false)))
    (O₁ O₂ : α → σ × Bool → Q → PMF (R × (σ × Bool)))
    (h₁ : ∀ x t d r t', O₁ x (t, true) d (r, (t', false)) = 0)
    (h₂ : ∀ x t d r t', O₂ x (t, true) d (r, (t', false)) = 0)
    (hagree : ∀ x s d r t', O₁ x s d (r, (t', false)) = O₂ x s d (r, (t', false)))
    (W : α → OracleAdv Q R β) (c : β) (t' : σ) :
    (p₁.bind fun x => OracleAdv.run (O₁ x.1) (W x.1) x.2) (c, (t', false)) =
      (p₂.bind fun x => OracleAdv.run (O₂ x.1) (W x.1) x.2) (c, (t', false)) := by
  simp only [PMF.bind_apply]
  refine tsum_congr fun x => ?_
  obtain ⟨a, t, fl⟩ := x
  cases fl with
  | false =>
    rw [hp, OracleAdv.run_apply_flag_false_eq (O₁ a) (O₂ a) (h₁ a) (h₂ a) (hagree a)]
  | true =>
    grind [OracleAdv.run_flag_apply_false_of_true, mul_zero]

theorem okDist_apply_false_eq {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool)
    (kd : Kd) (c : Bool) (t : D → Option H) :
    okDist S true A b kd (c, (t, false)) = okDist S false A b kd (c, (t, false)) := by
  unfold okDist
  simp only [PMF.bind_apply]
  refine tsum_congr fun kp => congrArg _ (tsum_congr fun e => congrArg _ ?_)
  rw [← PMF.bind_apply, ← PMF.bind_apply]
  refine bind_run_apply_flag_false_eq _ _ (fun a t => ?_)
    (fun x => okOracle S true kp.2 e.1.2 kd (some (x.2.2.1, chalCT S kd x b)))
    (fun x => okOracle S false kp.2 e.1.2 kd (some (x.2.2.1, chalCT S kd x b)))
    (fun x t d r t' => okOracle_apply_true_false S _ _ _ _ _ t d r t')
    (fun x t d r t' => okOracle_apply_true_false S _ _ _ _ _ t d r t')
    (fun x s d r t' => okOracle_apply_false_eq S _ _ _ _ s d r t')
    (fun x => A.guess x.2.2.2 (e.1.2, chalCT S kd x b)) c t
  exact OracleAdv.run_apply_flag_false_eq _ _ (okOracle_apply_true_false S _ _ _ _ _)
    (okOracle_apply_true_false S _ _ _ _ _) (okOracle_apply_false_eq S _ _ _ _) _ _ a t

omit [DecidableEq C] [DecidableEq AD] [DecidableEq CT] in
theorem run_roProg_query {Q R σ : Type} (O : σ → Q → PMF (R × σ)) (T : D → Option H) (d : D)
    (s : σ) :
    OracleAdv.run O (roProg H T d) s = (roOracle T d).map fun r => (r, s) := by
  unfold roProg roOracle
  cases T d with
  | some h => simp [PMF.pure_map]
  | none => simp [PMF.map]

omit [DecidableEq C] [DecidableEq AD] [DecidableEq CT] in
/-- A simulation by the random-oracle program runs as the lazily sampled random oracle,
leaving the state of any outer oracle unchanged. -/
theorem run_simulate_roProg {Q R σ α : Type} (O : σ → Q → PMF (R × σ)) (W : OracleAdv D H α)
    (T : D → Option H) (s : σ) :
    OracleAdv.run O (OracleAdv.simulate (roProg H) W T) s =
      (OracleAdv.run roOracle W T).map fun x => (x, s) := by
  induction W generalizing T with
  | ret a => simp [OracleAdv.simulate, PMF.pure_map]
  | rand p k ih => simp only [OracleAdv.simulate, OracleAdv.run_rand, PMF.map_bind, ih]
  | query d k ih =>
    simp only [OracleAdv.simulate, OracleAdv.run_bind, run_roProg_query, OracleAdv.run_query,
      PMF.bind_map, PMF.map_bind, Function.comp_def, ih]

theorem simOracle_ctxtProg_eq (sk : SK) (cstar : C) (kd : Kd) (chal : Option (AD × CT)) :
    OracleAdv.simOracle (ctxtProg S sk cstar) (otDecOracle S.aead kd chal) =
      okOracle S true sk cstar kd chal := by
  funext s q
  obtain ⟨T, fl⟩ := s
  cases q with
  | inl d =>
    simp only [OracleAdv.simOracle, ctxtProg, okOracle, OracleAdv.run_bind, run_roProg_query,
      OracleAdv.run_ret, PMF.bind_map, PMF.map_bind, Function.comp_def, PMF.pure_map]
    rfl
  | inr q =>
    simp only [OracleAdv.simOracle, ctxtProg, okOracle]
    split_ifs with hc hch
    · simp [otDecOracle, hch, PMF.pure_map]
    · simp [otDecOracle, hch, PMF.pure_map]
    · simp only [OracleAdv.run_bind, run_simulate_roProg, OracleAdv.run_ret, PMF.bind_map,
        PMF.map_bind, Function.comp_def, PMF.pure_map]
      rfl

theorem otctxtGame_eq_okDist {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool)
    [Fintype Kd] [Nonempty Kd] :
    otctxtGame S.aead (ctxtReduction S A b) =
      (PMF.uniformFintype Kd).bind fun kd => (okDist S true A b kd).map fun y => y.2.2 := by
  have hrun : ∀ (sk : SK) (cstar : C) (kd : Kd) (chal : Option (AD × CT)) {α : Type}
      (W : OracleAdv (D ⊕ (C × AD × CT)) (H ⊕ Option M) α) (T : D → Option H) (fl : Bool),
      OracleAdv.run (otDecOracle S.aead kd chal) (OracleAdv.simulate (ctxtProg S sk cstar) W T) fl =
        (OracleAdv.run (okOracle S true sk cstar kd chal) W (T, fl)).map
          fun x => ((x.1, x.2.1), x.2.2) := by
    intro sk cstar kd chal α W T fl
    rw [OracleAdv.run_simulate, simOracle_ctxtProg_eq]
  unfold otctxtGame ctxtReduction okDist
  refine congrArg _ (funext fun kd => ?_)
  simp only [OracleAdv.run_rand, OracleAdv.run_bind, run_simulate_roProg, hrun, OracleAdv.run_ret,
    PMF.bind_bind, PMF.bind_map, PMF.map_bind, Function.comp_def, PMF.pure_bind, PMF.pure_map]
  rfl

theorem okOracle_false_map (sk : SK) (cstar : C) (kd : Kd) (chal : Option (AD × CT))
    (s : (D → Option H) × Bool) (q : D ⊕ (C × AD × CT)) :
    (okOracle S false sk cstar kd chal s q).map (Prod.map id Prod.fst) =
        nOracle S sk cstar s.1 q := by
  cases q with
  | inl d => simp only [okOracle, nOracle, PMF.map_comp]; rfl
  | inr q =>
    simp only [okOracle, nOracle]
    by_cases hc : q.1 = cstar
    · grind [PMF.pure_map]
    · simp only [hc, ite_false, PMF.map_comp]; rfl

theorem otcpaGame_eq_okDist {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool)
    [Fintype Kd] [Nonempty Kd] :
    otcpaGame S.aead (cpaReduction S A) b =
      (PMF.uniformFintype Kd).bind fun kd => (okDist S false A b kd).map Prod.fst := by
  have hn : ∀ (sk : SK) (cstar : C) (kd : Kd) (chal : Option (AD × CT)) {α : Type}
      (W : OracleAdv (D ⊕ (C × AD × CT)) (H ⊕ Option M) α) (s : (D → Option H) × Bool),
      (OracleAdv.run (okOracle S false sk cstar kd chal) W s).map (Prod.map id Prod.fst) =
        OracleAdv.run (nOracle S sk cstar) W s.1 := fun sk cstar kd chal α W s =>
    OracleAdv.run_map_state _ _ _ (okOracle_false_map S sk cstar kd chal) W s
  unfold otcpaGame cpaReduction okDist
  refine congrArg _ (funext fun kd => ?_)
  simp only [PMF.bind_bind, PMF.map_bind, PMF.bind_map, Function.comp_def]
  refine congrArg _ (funext fun kp => congrArg _ (funext fun e => ?_))
  have h2 : ∀ x : (M × M × AD × A.St) × ((D → Option H) × Bool),
      (OracleAdv.run (okOracle S false kp.2 e.1.2 kd (some (x.1.2.2.1, chalCT S kd x.1 b)))
        (A.guess x.1.2.2.2 (e.1.2, chalCT S kd x.1 b)) x.2).map Prod.fst =
      (OracleAdv.run (nOracle S kp.2 e.1.2) (A.guess x.1.2.2.2 (e.1.2, chalCT S kd x.1 b))
        x.2.1).map Prod.fst := by
    intro x
    rw [← hn, PMF.map_comp]; rfl
  simp only [h2]
  rw [← hn kp.2 e.1.2 kd none (A.choose kp.1) (e.2, false), PMF.bind_map]
  rfl

omit [DecidableEq AD] [DecidableEq CT] [DecidableEq D] [Fintype H] [Nonempty H]
  [DecidableEq C] in
theorem advantage_symm (G₀ G₁ : SPComp Bool) : Advantage G₀ G₁ = Advantage G₁ G₀ := by
  simp_all [Advantage, max_comm]

/-- **Integrity hop.** Replacing opening under the independent AEAD key by `none` on
decryption queries for `enc*` changes the output distribution by at most the one-time
INT-CTXT advantage of `ctxtReduction S A b`. -/
theorem schedGame_otcpaGame_le [Fintype K] [Nonempty K] {qH qD : ℕ}
    (A : HPKEAdversary PK C D H AD M CT qH qD) (b : Bool)
    [Fintype Kd] [Nonempty Kd] :
    Advantage (liftPMF (schedGame S.sched (schedReduction S A b) false))
      (liftPMF (otcpaGame S.aead (cpaReduction S A) b)) ≤
    otctxtAdvantage S.aead (ctxtReduction S A b) := by
  set p₁ := (PMF.uniformFintype Kd).bind fun kd => okDist S true A b kd
  set p₂ := (PMF.uniformFintype Kd).bind fun kd => okDist S false A b kd
  have h₁ : schedGame S.sched (schedReduction S A b) false = p₁.map Prod.fst := by
    simp only [schedGame, Bool.false_eq_true, ite_false, p₁, PMF.map_bind]
    exact congrArg _ (funext fun kd => schedReduction_eq_okDist S A b kd)
  have h₂ : otcpaGame S.aead (cpaReduction S A) b = p₂.map Prod.fst := by
    rw [otcpaGame_eq_okDist, PMF.map_bind]
  have h₃ : otctxtGame S.aead (ctxtReduction S A b) = p₁.map fun y => y.2.2 := by
    rw [otctxtGame_eq_okDist, PMF.map_bind]
  have h : ∀ a t, p₁ (a, (t, false)) = p₂ (a, (t, false)) := by
    intro a t
    simp only [p₁, p₂, PMF.bind_apply, okDist_apply_false_eq]
  rw [h₁, h₂, otctxtAdvantage, h₃]
  simp only [Advantage, prTrue_liftPMF_map]
  refine max_le (tsub_le_iff_left.mpr ?_) (tsub_le_iff_left.mpr ?_)
  · rw [toOuterMeasure_flag_eq _ _ h]
    simpa only [Set.mem_singleton_iff] using toOuterMeasure_le_add_flag _ _ h {true}
  · simpa only [Set.mem_singleton_iff] using
      toOuterMeasure_le_add_flag _ _ (fun a t => (h a t).symm) {true}

end CtxtHop

/-! ### The theorem -/

/-- **HPKE Base mode is IND-CCA secure.** For HPKE Base mode `S` whose KEM is correct for
every random-oracle function (`ROMCorrect S.kem`), and every two-stage adversary `A`
with the public key, the random oracle and a decryption oracle,

`hpkeAdvantage S A ≤ Σ_{b ∈ {true, false}} (romINDCCAAdvantage S.kem (kemReduction S A b) +
  schedAdvantage S.sched (schedReduction S A b) + otctxtAdvantage S.aead (ctxtReduction S A b))
  + otcpaAdvantage S.aead (cpaReduction S A)`.

Each reduction runs both stages of `A` once. `kemReduction S A b` forwards the random-oracle
queries of `A` and one decapsulation query per decryption query on another encapsulation;
`schedReduction S A b` and `cpaReduction S A` generate the key pair, sample the random oracle
lazily and answer decryption queries with the secret key; `ctxtReduction S A b` does the same
and forwards decryption queries on the challenge encapsulation. The bound follows the
KEM/DEM composition of Cramer and Shoup with the key schedule as an extra hop; the KEM terms
appear once per challenge bit. -/
theorem hpke_base_indcca [Fintype K] [Nonempty K] [Fintype D] [Fintype Kd] [Nonempty Kd]
    (hcorr : ROMCorrect S.kem)
    {qH qD : ℕ} (A : HPKEAdversary PK C D H AD M CT qH qD) :
    hpkeAdvantage S A ≤
      romINDCCAAdvantage S.kem (kemReduction S A true) +
        schedAdvantage S.sched (schedReduction S A true) +
        otctxtAdvantage S.aead (ctxtReduction S A true) +
        otcpaAdvantage S.aead (cpaReduction S A) +
        otctxtAdvantage S.aead (ctxtReduction S A false) +
        schedAdvantage S.sched (schedReduction S A false) +
        romINDCCAAdvantage S.kem (kemReduction S A false) := by
  have hK : ∀ b, Advantage (liftPMF (hpkeGame S A b))
      (liftPMF (romINDCCAGame S.kem (kemReduction S A b) false)) =
      romINDCCAAdvantage S.kem (kemReduction S A b) := fun b => by
    rw [hpkeGame_eq_kemGame S hcorr A b]; rfl
  have hS : ∀ b, Advantage (liftPMF (romINDCCAGame S.kem (kemReduction S A b) false))
      (liftPMF (schedGame S.sched (schedReduction S A b) false)) =
      schedAdvantage S.sched (schedReduction S A b) := fun b => by
    rw [kemGame_false_eq_schedGame]; rfl
  unfold hpkeAdvantage
  calc Advantage (liftPMF (hpkeGame S A true)) (liftPMF (hpkeGame S A false))
      ≤ Advantage (liftPMF (hpkeGame S A true))
            (liftPMF (romINDCCAGame S.kem (kemReduction S A true) false)) +
          Advantage (liftPMF (romINDCCAGame S.kem (kemReduction S A true) false))
            (liftPMF (schedGame S.sched (schedReduction S A true) false)) +
          Advantage (liftPMF (schedGame S.sched (schedReduction S A true) false))
            (liftPMF (otcpaGame S.aead (cpaReduction S A) true)) +
          Advantage (liftPMF (otcpaGame S.aead (cpaReduction S A) true))
            (liftPMF (otcpaGame S.aead (cpaReduction S A) false)) +
          Advantage (liftPMF (otcpaGame S.aead (cpaReduction S A) false))
            (liftPMF (schedGame S.sched (schedReduction S A false) false)) +
          Advantage (liftPMF (schedGame S.sched (schedReduction S A false) false))
            (liftPMF (romINDCCAGame S.kem (kemReduction S A false) false)) +
          Advantage (liftPMF (romINDCCAGame S.kem (kemReduction S A false) false))
            (liftPMF (hpkeGame S A false)) := by
        refine (advantage_triangle _ (liftPMF (romINDCCAGame S.kem (kemReduction S A false) false))
          _).trans (add_le_add ?_ le_rfl)
        refine (advantage_triangle _ (liftPMF (schedGame S.sched (schedReduction S A false) false))
          _).trans (add_le_add ?_ le_rfl)
        refine (advantage_triangle _ (liftPMF (otcpaGame S.aead (cpaReduction S A) false))
          _).trans (add_le_add ?_ le_rfl)
        refine (advantage_triangle _ (liftPMF (otcpaGame S.aead (cpaReduction S A) true))
          _).trans (add_le_add ?_ le_rfl)
        refine (advantage_triangle _ (liftPMF (schedGame S.sched (schedReduction S A true) false))
          _).trans (add_le_add ?_ le_rfl)
        exact advantage_triangle _ _ _
    _ ≤ _ := by
        rw [hK, hS, advantage_symm (liftPMF (otcpaGame S.aead (cpaReduction S A) false))
            (liftPMF (schedGame S.sched (schedReduction S A false) false)),
          advantage_symm (liftPMF (schedGame S.sched (schedReduction S A false) false))
            (liftPMF (romINDCCAGame S.kem (kemReduction S A false) false)), hS,
          advantage_symm (liftPMF (romINDCCAGame S.kem (kemReduction S A false) false))
            (liftPMF (hpkeGame S A false)), hK]
        gcongr
        · exact schedGame_otcpaGame_le S A true
        · exact le_of_eq rfl
        · exact schedGame_otcpaGame_le S A false

end HPKE

end CatCrypt.Crypto.HPKE.BaseCCA
