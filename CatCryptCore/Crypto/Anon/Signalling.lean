/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.CR
public import CatCryptCore.Crypto.PRPPRFSwitching
public import CatCryptCore.Crypto.SDist
public import CatCryptCore.Crypto.Signatures.EUFCMAPMF
public import CatCryptCore.Tactics.DeriveTimed

/-!
# Anonymous signalling from a membership proof, a PRF nullifier and a signed group root

The construct shared by Semaphore, RLN and OpenID4VP presentations. A member holds an
identity secret `k`, the key of a PRF `prf : K → Option E → N`. Its identity commitment is
`prf k none`, a leaf of a group accumulator (a Merkle tree) over a keyed hash `H`
(core `Assumptions.CR`); the authority of the group signs the group root with a signature
scheme (core `Signatures.EUFCMAPMF`). A signal on a message `m` in scope `e` (an epoch,
an external nullifier, a verifier nonce) carries the nullifier `prf k (some e)` and a
zero-knowledge proof that the signer knows a leaf of the group and its secret.

Two properties are bounded, each per adversary.

* Anonymity. The adversary chooses the other members and the scope and message, sees the
  group root, the nullifier and the proof, and guesses. In the ideal game the commitment and
  the nullifier are uniform and the proof is simulated, so the view does not depend on the
  identity secret. The proof becomes simulated at the cost of the statistical
  zero-knowledge error `zkError` (a statistical distance over true statements, numeric), and
  the PRF values become uniform at the cost of the adaptive PRF advantage of `prfRed`
  (core `PRF_q_Advantage`), a reduction that asks for the commitment and the nullifier.
* Membership unforgeability. The adversary chooses a group, receives the authority's
  signature on its root and outputs a root, a signature, a leaf and a path; it wins when the
  signature and the path verify and the leaf is not a member. Either the root was not signed,
  a forgery against the EUF-CMA game of `sigRed` (core `eufcmaAdvantage`), or the path opens
  the signed root at a non-member, and the accumulator's extractor gives a collision of `H`
  found by `crRed` (core `CR_Search_Advantage`). The leaf and the path are the membership
  witness that a knowledge extractor of the proof system returns.

## Main definitions

* `Accumulator` — a group accumulator over `H` with honest paths, verification and a
  collision extractor for paths that open a root at a non-member
* `prfOf` — the PRF of a commitment function and a nullifier function
* `Scheme`, `Choice`, `Adversary` — the construct, the adversary's choice and the adversary
* `anonReal`, `anonHyb`, `anonIdeal`, `anonAdvantage` — the anonymity games
* `zkError` — the statistical distance between honest proofs and simulated proofs
* `bindGame`, `bindAdvantage` — membership unforgeability
* `signalAdvantage` — the sum of the two advantages
* `prfRed`, `sigRed`, `crRedTree`, `crRed` — the reductions, with costed forms

## Main results

* `anonAdvantage_le` — anonymity advantage at most `zkError` plus the PRF advantage of
  `prfRed`
* `bindAdvantage_le` — forging advantage at most the CR advantage of `crRed` plus the
  EUF-CMA advantage of `sigRed`
* `signalAdvantage_le` — the sum of the four terms bounds the sum of the two advantages
* `prfRed.timeBound_timed`, `sigRed.timeBound_timed`, `crRedTree.timeBound_timed`,
  `crRed.timeBound_timed` — the reductions run in the adversary's time plus a constant number
  of primitive calls

## References

* Semaphore, *Zero-knowledge signalling on Ethereum*, Privacy and Scaling Explorations, 2022
* Waku, *Rate-Limiting Nullifier*, RFC 32/RLN-V1, 2023
* OpenID for Verifiable Presentations 1.0, OpenID Foundation, 2025
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Anon.Signalling

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.PRPPRF CatCrypt.Crypto.Signatures
open scoped ENNReal

/-! ## The construct -/

/-- A group accumulator over the keyed hash `H`: the root of a list of leaves, the honest
path of the leaf at a position, path verification, and an extractor that turns a path opening
the root of `L` at a leaf outside `L` into a collision of `H`. -/
structure Accumulator (H : HashScheme) (Leaf Root Path : Type) where
  /-- The root of a group. -/
  root : H.Key → List Leaf → Root
  /-- The honest path of the leaf at a position. -/
  path : H.Key → List Leaf → ℕ → Path
  /-- Path verification against a root. -/
  verify : H.Key → Root → Leaf → Path → Bool
  /-- The collision extractor. -/
  extract : H.Key → List Leaf → Leaf → Path → H.Input × H.Input
  /-- A path opening the root of `L` at a leaf outside `L` yields a collision. -/
  extract_collision : ∀ hk L x p, verify hk (root hk L) x p = true → x ∉ L →
    H.hash hk (extract hk L x p).1 = H.hash hk (extract hk L x p).2 ∧
      (extract hk L x p).1 ≠ (extract hk L x p).2

/-- The adversary's choice in the anonymity game: the members before and after the signer,
the scope and the message. -/
structure Choice (N E M : Type) where
  /-- Members before the signer. -/
  pre : List N
  /-- Members after the signer. -/
  post : List N
  /-- The scope of the signal. -/
  scope : E
  /-- The message. -/
  msg : M

/-- The group of a choice with the signer's commitment `cm` inserted. -/
def Choice.group {N E M : Type} (c : Choice N E M) (cm : N) : List N := c.pre ++ cm :: c.post

/-- The PRF of a commitment function and a nullifier function of the identity secret: the
commitment at `none` and the nullifier of scope `e` at `some e`. -/
def prfOf {K E N : Type} (commit : K → N) (nullifier : K → E → N) : K → Option E → N
  | k, none => commit k
  | k, some e => nullifier k e

/-- Anonymous signalling: the PRF keyed by the identity secret (commitment at `none`,
nullifiers at `some e`), the group accumulator, the proof system with its simulator on
statements `(root, scope, nullifier, message)` and witnesses `(secret, path)`, and the
authority's signature scheme on roots. -/
structure Scheme (H : HashScheme) (K E N M Pf Root Path PK SK Sig : Type) : Type 1 where
  /-- The PRF of commitments and nullifiers. -/
  prf : K → Option E → N
  /-- The group accumulator. -/
  acc : Accumulator H N Root Path
  /-- The honest prover. -/
  prove : Root × E × N × M → K × Path → PMF Pf
  /-- The simulator. -/
  sim : Root × E × N × M → PMF Pf
  /-- The authority's signature scheme. -/
  sig : PSigScheme Root PK SK Sig

/-- An adversary against anonymous signalling: the stages `choose`, `guess` of the anonymity
game and the stages `group`, `forge` of the forging game. -/
structure Adversary (H : HashScheme) (E N M Pf Root Path PK Sig : Type) where
  /-- Choose the other members, the scope and the message. -/
  choose : H.Key → PMF (Choice N E M)
  /-- Guess from the root, the nullifier and the proof. -/
  guess : H.Key → Choice N E M → Root → N → Pf → PMF Bool
  /-- Choose the group whose root the authority signs. -/
  group : H.Key → PK → PMF (List N)
  /-- Output a root, a signature, a leaf and a path. -/
  forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path)

variable {H : HashScheme} {K E N M Pf Root Path PK SK Sig : Type}

namespace Scheme

variable (S : Scheme H K E N M Pf Root Path PK SK Sig)

/-- The statement of the signal at `(k, hk, c)`: the root of the group with the commitment
of `k`, the scope, the nullifier of `k` and the message. -/
def stmtOf (t : K × H.Key × Choice N E M) : Root × E × N × M :=
  (S.acc.root t.2.1 (t.2.2.group (S.prf t.1 none)), t.2.2.scope, S.prf t.1 (some t.2.2.scope),
    t.2.2.msg)

/-- The root of the group of the choice `c` with the commitment `cm`. -/
def groupRoot (hk : H.Key) (c : Choice N E M) (cm : N) : Root := S.acc.root hk (c.group cm)

/-- The witness of the signal at `(k, hk, c)`: the secret and the honest path of the
commitment. -/
def witOf (t : K × H.Key × Choice N E M) : K × Path :=
  (t.1, S.acc.path t.2.1 (t.2.2.group (S.prf t.1 none)) t.2.2.pre.length)

end Scheme

/-! ## Anonymity -/

section Anonymity

variable [Fintype K] [Nonempty K] [Fintype N] [Nonempty N]

/-- The secret, the hash key and the adversary's choice. -/
noncomputable def anonPre (choose : H.Key → PMF (Choice N E M)) :
    PMF (K × H.Key × Choice N E M) :=
  (PMF.uniformFintype K).bind fun k => (PMF.uniformFintype H.Key).bind fun hk =>
    (choose hk).map fun c => (k, hk, c)

/-- The adversary's guess on the root, the nullifier and the proof `π` at `(k, hk, c)`. -/
noncomputable def anonCont (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (guess : H.Key → Choice N E M → Root → N → Pf → PMF Bool) (t : K × H.Key × Choice N E M)
    (π : Pf) : PMF Bool :=
  guess t.2.1 t.2.2 (S.stmtOf t).1 (S.stmtOf t).2.2.1 π

/-- The real anonymity game: an honest signal of a uniform identity. -/
noncomputable def anonReal (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (choose : H.Key → PMF (Choice N E M))
    (guess : H.Key → Choice N E M → Root → N → Pf → PMF Bool) : PMF Bool :=
  (anonPre choose).bind fun t => (S.prove (S.stmtOf t) (S.witOf t)).bind (anonCont S guess t)

/-- The anonymity game with a simulated proof. -/
noncomputable def anonHyb (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (choose : H.Key → PMF (Choice N E M))
    (guess : H.Key → Choice N E M → Root → N → Pf → PMF Bool) : PMF Bool :=
  (anonPre choose).bind fun t => (S.sim (S.stmtOf t)).bind (anonCont S guess t)

/-- The ideal anonymity game: a uniform commitment, a uniform nullifier and a simulated
proof; no identity secret. -/
noncomputable def anonIdeal (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (choose : H.Key → PMF (Choice N E M))
    (guess : H.Key → Choice N E M → Root → N → Pf → PMF Bool) : PMF Bool :=
  (PMF.uniformFintype H.Key).bind fun hk => (choose hk).bind fun c =>
    (PMF.uniformFintype N).bind fun cm => (PMF.uniformFintype N).bind fun nf =>
      (S.sim (S.acc.root hk (c.group cm), c.scope, nf, c.msg)).bind fun π =>
        guess hk c (S.acc.root hk (c.group cm)) nf π

/-- The anonymity advantage. -/
noncomputable def anonAdvantage (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (choose : H.Key → PMF (Choice N E M))
    (guess : H.Key → Choice N E M → Root → N → Pf → PMF Bool) : ℝ≥0∞ :=
  Advantage (liftPMF (anonReal S choose guess)) (liftPMF (anonIdeal S choose guess))

/-- The statistical zero-knowledge error: the statistical distance between the honest proof
and the simulated proof, over the true statements of signals with their witnesses. -/
noncomputable def zkError (S : Scheme H K E N M Pf Root Path PK SK Sig) : ℝ≥0∞ :=
  sdist (fun t : K × H.Key × Choice N E M => liftPMF (S.prove (S.stmtOf t) (S.witOf t)))
    (fun t => liftPMF (S.sim (S.stmtOf t)))

/-- The PRF reduction: sample the hash key, run the choice, ask the PRF oracle for the
commitment and the nullifier, simulate the proof and return the guess. -/
noncomputable def prfRed (groupRoot : H.Key → Choice N E M → N → Root) (sim : Root × E × N × M → PMF Pf)
    (choose : H.Key → PMF (Choice N E M))
    (guess : H.Key → Choice N E M → Root → N → Pf → PMF Bool) : OracleAdv (Option E) N Bool :=
  .rand (PMF.uniformFintype H.Key) fun hk => .rand (choose hk) fun c =>
    .query none fun cm => .query (some c.scope) fun nf =>
      .rand (sim (groupRoot hk c cm, c.scope, nf, c.msg)) fun π =>
        .rand (guess hk c (groupRoot hk c cm) nf π) fun b => .ret b

variable (S : Scheme H K E N M Pf Root Path PK SK Sig) (choose : H.Key → PMF (Choice N E M))
  (guess : H.Key → Choice N E M → Root → N → Pf → PMF Bool)

omit [Fintype N] [Nonempty N] in
/-- **Zero-knowledge hop.** Simulating the proof changes the probability of `true` by at most
the statistical zero-knowledge error. -/
theorem advantage_real_hyb_le :
    Advantage (liftPMF (anonReal S choose guess)) (liftPMF (anonHyb S choose guess)) ≤
      zkError S := by
  have e : ∀ (f : K × H.Key × Choice N E M → PMF Pf),
      liftPMF ((anonPre choose).bind fun t => (f t).bind (anonCont S guess t)) =
        SPComp.bind (liftPMF (anonPre choose)) fun t =>
          SPComp.bind (liftPMF (f t)) fun π => liftPMF (anonCont S guess t π) := by
    intro f
    simp only [liftPMF_bind_liftPMF]
  change absDiff _ _ ≤ _
  rw [anonReal, anonHyb, e, e]
  refine absDiff_prTrue_bind_le _ _ _ _ _ (fun t h' => ?_) (fun t h' => ?_)
  · exact le_add_of_absDiff_le
      (sdist_le_of_forall (f := fun t => liftPMF (S.prove (S.stmtOf t) (S.witOf t)))
        (g := fun t => liftPMF (S.sim (S.stmtOf t))) le_rfl
        (fun π => liftPMF (anonCont S guess t π)) t h')
  · refine le_add_of_absDiff_le ?_
    rw [absDiff_comm]
    exact sdist_le_of_forall (f := fun t => liftPMF (S.prove (S.stmtOf t) (S.witOf t)))
      (g := fun t => liftPMF (S.sim (S.stmtOf t))) le_rfl
      (fun π => liftPMF (anonCont S guess t π)) t h'

omit [Fintype N] [Nonempty N] in
/-- The real PRF game of `prfRed` is the game with a simulated proof. -/
theorem prfReal_eq [DecidableEq E] :
    realGame S.prf (prfRed S.groupRoot S.sim choose guess) = liftPMF (anonHyb S choose guess) := by
  unfold realGame anonHyb anonPre
  congr 1
  simp [prfRed, Scheme.groupRoot, keyedOracle, PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def]
  rfl

omit [Fintype K] [Nonempty K] in
/-- The random-function game of `prfRed` is the ideal game. -/
theorem prfIdeal_eq [DecidableEq E] [DecidableEq N] :
    rfGame (prfRed S.groupRoot S.sim choose guess) = liftPMF (anonIdeal S choose guess) := by
  unfold rfGame anonIdeal
  congr 1
  simp [prfRed, Scheme.groupRoot, rfOracle, PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def]
  refine congrArg _ (funext fun hk => congrArg _ (funext fun c => congrArg _ (funext fun cm => ?_)))
  split
  · rename_i r hr
    cases hr
  · simp [PMF.bind_map, Function.comp_def]

/-- **Anonymity.** For every adversary, the anonymity advantage is at most the statistical
zero-knowledge error plus the adaptive PRF advantage of `prfRed`. -/
theorem anonAdvantage_le [DecidableEq E] [DecidableEq N] :
    anonAdvantage S choose guess ≤
      zkError S + PRF_q_Advantage S.prf (prfRed S.groupRoot S.sim choose guess) := by
  unfold anonAdvantage PRF_q_Advantage
  rw [prfReal_eq, prfIdeal_eq]
  exact (advantage_triangle _ _ _).trans (add_le_add (advantage_real_hyb_le S choose guess) le_rfl)

end Anonymity

/-! ## Membership unforgeability -/

section Binding

variable [DecidableEq N]

/-- The forging game: the authority's key pair and the hash key are sampled, the adversary
chooses a group, receives the signature on its root and outputs a root, a signature, a leaf
and a path; it wins when both verify and the leaf is not a member. -/
noncomputable def bindGame (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (group : H.Key → PK → PMF (List N))
    (forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path)) : PMF Bool :=
  (PMF.uniformFintype S.sig.KR).bind fun kr => (PMF.uniformFintype H.Key).bind fun hk =>
    (group hk (S.sig.keygen kr).1).bind fun L =>
      (S.sig.sign (S.sig.keygen kr).2 (S.acc.root hk L)).bind fun σ =>
        (forge hk (S.sig.keygen kr).1 L σ).map fun o =>
          S.sig.verify (S.sig.keygen kr).1 o.1 o.2.1 && S.acc.verify hk o.1 o.2.2.1 o.2.2.2 &&
            !decide (o.2.2.1 ∈ L)

/-- The forging advantage: the probability of winning the forging game. -/
noncomputable def bindAdvantage (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (group : H.Key → PK → PMF (List N))
    (forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path)) : ℝ≥0∞ :=
  bindGame S group forge true

/-- The EUF-CMA reduction on the public key: sample the hash key, run the group choice, ask
for the signature on its root and output the adversary's root and signature. -/
noncomputable def sigRed (root : H.Key → List N → Root) (group : H.Key → PK → PMF (List N))
    (forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path)) (pk : PK) :
    OracleAdv Root Sig (Root × Sig) :=
  .rand (PMF.uniformFintype H.Key) fun hk => .rand (group hk pk) fun L =>
    .query (root hk L) fun σ => .rand (forge hk pk L σ) fun o => .ret (o.1, o.2.1)

/-- The collision reduction on the hash key, as a tree with no queries: sample the authority's
key pair, sign the root of the adversary's group and extract from the adversary's leaf and
path. -/
noncomputable def crRedTree {KR : Type} [Fintype KR] [Nonempty KR] (keygen : KR → PK × SK)
    (sign : SK → Root → PMF Sig) (root : H.Key → List N → Root)
    (extract : H.Key → List N → N → Path → H.Input × H.Input)
    (group : H.Key → PK → PMF (List N))
    (forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path)) (hk : H.Key) :
    OracleAdv Unit Unit (H.Input × H.Input) :=
  .rand (PMF.uniformFintype KR) fun kr => .rand (group hk (keygen kr).1) fun L =>
    .rand (sign (keygen kr).2 (root hk L)) fun σ =>
      .rand (forge hk (keygen kr).1 L σ) fun o => .ret (extract hk L o.2.2.1 o.2.2.2)

/-- The output distribution of a tree that asks no queries. -/
noncomputable def runNoQuery {α : Type} (t : OracleAdv Unit Unit α) : PMF α :=
  (OracleAdv.run (fun (_ : Unit) (_ : Unit) => PMF.pure ((), ())) t ()).map Prod.fst

/-- The collision reduction, a CR search adversary running `crRedTree`. -/
noncomputable def crRed (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (group : H.Key → PK → PMF (List N))
    (forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path)) : CR_Search_Adversary H :=
  fun hk => liftPMF (runNoQuery (crRedTree S.sig.keygen S.sig.sign S.acc.root S.acc.extract
    group forge hk))

omit [DecidableEq N] in
/-- Union bound under a bind: if each branch of `f` is at most the sum of the branches of `g`
and `h`, so is the bind. -/
theorem bind_true_le_add {α : Type} (p : PMF α) (f g h : α → PMF Bool)
    (hle : ∀ a, f a true ≤ g a true + h a true) :
    (p.bind f) true ≤ (p.bind g) true + (p.bind h) true := by
  simp only [PMF.bind_apply]
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun a => by rw [← mul_add]; gcongr; exact hle a

/-- The forging experiment with the event `ev` of the adversary's output in place of the
winning condition. -/
noncomputable def bindShape (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (group : H.Key → PK → PMF (List N))
    (forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path))
    (ev : S.sig.KR → H.Key → List N → Root × Sig × N × Path → Bool) : PMF Bool :=
  (PMF.uniformFintype S.sig.KR).bind fun kr => (PMF.uniformFintype H.Key).bind fun hk =>
    (group hk (S.sig.keygen kr).1).bind fun L =>
      (S.sig.sign (S.sig.keygen kr).2 (S.acc.root hk L)).bind fun σ =>
        (forge hk (S.sig.keygen kr).1 L σ).map (ev kr hk L)

variable (S : Scheme H K E N M Pf Root Path PK SK Sig) (group : H.Key → PK → PMF (List N))
  (forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path))

omit [DecidableEq N] in
/-- The EUF-CMA game of `sigRed` is the forging experiment with the event "the signature
verifies on a root other than the signed one". -/
theorem eufcma_sigRed_eq [DecidableEq Root] :
    eufcmaAdvantage S.sig.toSigScheme (toEUFAdversary (sigRed S.acc.root group forge)) =
      bindShape S group forge (fun kr hk L o =>
        S.sig.verify (S.sig.keygen kr).1 o.1 o.2.1 && !([S.acc.root hk L].contains o.1)) true := by
  rw [eufcmaAdvantage_toEUFAdversary]
  unfold eufDist bindShape
  congr 2
  funext kr
  simp [sigRed, signOracle, PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def]
  rfl

omit [DecidableEq N] in
/-- The CR search game of `crRed` is the forging experiment with the event "the extractor
returns a collision". -/
theorem cr_crRed_eq :
    CR_Search_Advantage H (crRed S group forge) =
      bindShape S group forge (fun _ hk L o =>
        decide (H.hash hk (S.acc.extract hk L o.2.2.1 o.2.2.2).1 =
            H.hash hk (S.acc.extract hk L o.2.2.1 o.2.2.2).2 ∧
          (S.acc.extract hk L o.2.2.1 o.2.2.2).1 ≠ (S.acc.extract hk L o.2.2.1 o.2.2.2).2))
        true := by
  unfold CR_Search_Advantage CR_Search_Game crRed
  simp only [SPComp.monad_bind_eq, sample_eq_liftPMF, liftPMF_bind_pure, liftPMF_bind_liftPMF,
    prTrue_liftPMF]
  unfold bindShape
  rw [PMF.bind_comm (PMF.uniformFintype S.sig.KR)]
  congr 2
  funext hk
  simp [runNoQuery, crRedTree, PMF.map_bind, PMF.pure_map]
  rfl

/-- **Membership unforgeability.** For every adversary, the forging advantage is at most the
CR advantage of `crRed` plus the EUF-CMA advantage of `sigRed`. -/
theorem bindAdvantage_le [DecidableEq Root] :
    bindAdvantage S group forge ≤
      CR_Search_Advantage H (crRed S group forge) +
      eufcmaAdvantage S.sig.toSigScheme (toEUFAdversary (sigRed S.acc.root group forge)) := by
  rw [cr_crRed_eq, eufcma_sigRed_eq, add_comm]
  unfold bindAdvantage bindGame bindShape
  refine bind_true_le_add _ _ _ _ fun kr => bind_true_le_add _ _ _ _ fun hk =>
    bind_true_le_add _ _ _ _ fun L => bind_true_le_add _ _ _ _ fun σ => ?_
  simp only [← PMF.bind_pure_comp]
  refine bind_true_le_add _ _ _ _ fun o => ?_
  rcases o with ⟨r, s, x, p⟩
  have hc := S.acc.extract_collision hk L x p
  by_cases hr : r = S.acc.root hk L <;> by_cases hv : S.acc.verify hk r x p = true <;>
    by_cases hx : x ∈ L <;> simp_all [PMF.pure_apply]
  split_ifs <;> simp

end Binding

/-! ## Anonymous signalling -/

section Signalling

variable [Fintype K] [Nonempty K] [Fintype N] [Nonempty N] [DecidableEq E] [DecidableEq N]
  [DecidableEq Root]

/-- The advantage against anonymous signalling: the anonymity advantage of the stages
`choose`, `guess` plus the forging advantage of the stages `group`, `forge`. -/
noncomputable def signalAdvantage (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (A : Adversary H E N M Pf Root Path PK Sig) : ℝ≥0∞ :=
  anonAdvantage S A.choose A.guess + bindAdvantage S A.group A.forge

/-- **Anonymous signalling.** For every adversary, the signalling advantage is at most the
statistical zero-knowledge error, plus the PRF advantage of `prfRed`, plus the CR advantage of
`crRed`, plus the EUF-CMA advantage of `sigRed`. -/
theorem signalAdvantage_le (S : Scheme H K E N M Pf Root Path PK SK Sig)
    (A : Adversary H E N M Pf Root Path PK Sig) :
    signalAdvantage S A ≤
      zkError S + PRF_q_Advantage S.prf (prfRed S.groupRoot S.sim A.choose A.guess) +
      CR_Search_Advantage H (crRed S A.group A.forge) +
      eufcmaAdvantage S.sig.toSigScheme (toEUFAdversary (sigRed S.acc.root A.group A.forge)) := by
  unfold signalAdvantage
  calc _ ≤ (zkError S + PRF_q_Advantage S.prf (prfRed S.groupRoot S.sim A.choose A.guess)) +
        (CR_Search_Advantage H (crRed S A.group A.forge) +
          eufcmaAdvantage S.sig.toSigScheme
            (toEUFAdversary (sigRed S.acc.root A.group A.forge))) :=
        add_le_add (anonAdvantage_le S A.choose A.guess) (bindAdvantage_le S A.group A.forge)
    _ = _ := by rw [add_assoc (zkError S + _)]

end Signalling

/-! ## Costed reductions -/

derive_timed prfRed

derive_timed sigRed

derive_timed crRedTree

section Time

open OracleAdv.Timed

variable {E N M Pf Root Path PK SK Sig : Type}

/-- **Time of the PRF reduction.** With the choice, the group root, the simulator and the
guess of cost at most `a`, `r`, `s` and `g`, the costed PRF reduction has time at most
`11 + a + 2 * r + s + g`: four samples, two queries, the simulator, the guess and the two
evaluations of the group root. -/
theorem prfRed.timeBound_timed (groupRoot : H.Key → Choice N E M → N → Root)
    (groupRootCost : H.Key → Choice N E M → N → ℕ) (sim : Root × E × N × M → PMF Pf)
    (simCost : Root × E × N × M → ℕ) (choose : H.Key → PMF (Choice N E M))
    (chooseCost : H.Key → ℕ) (guess : H.Key → Choice N E M → Root → N → Pf → PMF Bool)
    (guessCost : H.Key → Choice N E M → Root → N → Pf → ℕ) {a r s g : ℕ}
    (hA : ∀ hk, chooseCost hk ≤ a) (hR : ∀ hk c cm, groupRootCost hk c cm ≤ r)
    (hS : ∀ x, simCost x ≤ s) (hG : ∀ hk c rt nf π, guessCost hk c rt nf π ≤ g) :
    StepTimeBound (prfRed.timed groupRoot groupRootCost sim simCost choose chooseCost guess
      guessCost) (11 + a + 2 * r + s + g) := by
  unfold prfRed.timed
  simp only [stepTimeBound_zero, TimeBound]
  refine ⟨by omega, fun hk => ?_⟩
  have := hA hk
  refine ⟨by omega, by omega, fun c => ⟨by omega, by omega, fun cm =>
    ⟨by omega, by omega, fun nf => ?_⟩⟩⟩
  have := hR hk c cm
  have := hS (groupRoot hk c cm, c.scope, nf, c.msg)
  refine ⟨by omega, by omega, fun π => ?_⟩
  have := hG hk c (groupRoot hk c cm) nf π
  exact ⟨by omega, by omega, fun _ => ⟨by omega, trivial⟩⟩

/-- **Time of the EUF-CMA reduction.** With the group choice, the root and the forger of cost
at most `g`, `r` and `f`, the costed EUF-CMA reduction has time at most `7 + g + r + f`. -/
theorem sigRed.timeBound_timed (root : H.Key → List N → Root) (rootCost : H.Key → List N → ℕ)
    (group : H.Key → PK → PMF (List N)) (groupCost : H.Key → PK → ℕ)
    (forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path))
    (forgeCost : H.Key → PK → List N → Sig → ℕ) {g r f : ℕ}
    (hG : ∀ hk pk, groupCost hk pk ≤ g) (hR : ∀ hk L, rootCost hk L ≤ r)
    (hF : ∀ hk pk L σ, forgeCost hk pk L σ ≤ f) (pk : PK) :
    StepTimeBound (sigRed.timed root rootCost group groupCost forge forgeCost pk)
      (7 + g + r + f) := by
  unfold sigRed.timed
  simp only [stepTimeBound_zero, TimeBound]
  refine ⟨by omega, fun hk => ?_⟩
  have := hG hk pk
  refine ⟨by omega, by omega, fun L => ?_⟩
  have := hR hk L
  refine ⟨by omega, by omega, fun σ => ?_⟩
  have := hF hk pk L σ
  exact ⟨by omega, by omega, fun _ => ⟨by omega, trivial⟩⟩

/-- **Time of the collision tree.** With key generation, signing, the root, the extractor,
the group choice and the forger of cost at most `k`, `sg`, `r`, `x`, `g` and `f`, the costed
collision tree has time at most `12 + 3 * k + sg + r + x + g + f`. -/
theorem crRedTree.timeBound_timed {KR : Type} [Fintype KR] [Nonempty KR]
    (keygen : KR → PK × SK) (keygenCost : KR → ℕ) (sign : SK → Root → PMF Sig)
    (signCost : SK → Root → ℕ) (root : H.Key → List N → Root) (rootCost : H.Key → List N → ℕ)
    (extract : H.Key → List N → N → Path → H.Input × H.Input)
    (extractCost : H.Key → List N → N → Path → ℕ)
    (group : H.Key → PK → PMF (List N)) (groupCost : H.Key → PK → ℕ)
    (forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path))
    (forgeCost : H.Key → PK → List N → Sig → ℕ) {k sg r x g f : ℕ}
    (hK : ∀ kr, keygenCost kr ≤ k) (hSg : ∀ sk m, signCost sk m ≤ sg)
    (hR : ∀ hk L, rootCost hk L ≤ r) (hX : ∀ hk L y p, extractCost hk L y p ≤ x)
    (hG : ∀ hk pk, groupCost hk pk ≤ g) (hF : ∀ hk pk L σ, forgeCost hk pk L σ ≤ f)
    (hk : H.Key) :
    StepTimeBound (crRedTree.timed keygen keygenCost sign signCost root rootCost extract
      extractCost group groupCost forge forgeCost hk) (12 + 3 * k + sg + r + x + g + f) := by
  unfold crRedTree.timed
  simp only [stepTimeBound_zero, TimeBound]
  refine ⟨by omega, fun kr => ?_⟩
  have := hK kr
  have := hG hk (keygen kr).1
  refine ⟨by omega, by omega, fun L => ?_⟩
  have := hSg (keygen kr).2 (root hk L)
  have := hR hk L
  refine ⟨by omega, by omega, fun σ => ?_⟩
  have := hF hk (keygen kr).1 L σ
  refine ⟨by omega, by omega, fun o => ?_⟩
  have := hX hk L o.2.2.1 o.2.2.2
  exact ⟨by omega, trivial⟩

/-- The costed form of `crRed`: the costed collision tree at the algorithms of `S`. -/
noncomputable def crRed.timed [DecidableEq N] {K E M Pf : Type}
    (S : Scheme H K E N M Pf Root Path PK SK Sig) (keygenCost : S.sig.KR → ℕ)
    (signCost : SK → Root → ℕ) (rootCost : H.Key → List N → ℕ)
    (extractCost : H.Key → List N → N → Path → ℕ)
    (group : H.Key → PK → PMF (List N)) (groupCost : H.Key → PK → ℕ)
    (forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path))
    (forgeCost : H.Key → PK → List N → Sig → ℕ) (hk : H.Key) :
    ℕ × OracleAdv.Timed Unit Unit (H.Input × H.Input) :=
  crRedTree.timed S.sig.keygen keygenCost S.sig.sign signCost S.acc.root rootCost S.acc.extract
    extractCost group groupCost forge forgeCost hk

/-- The costed form of `crRed` erases to the collision tree that `crRed` runs. -/
theorem crRed.erase_timed [DecidableEq N] {K E M Pf : Type}
    (S : Scheme H K E N M Pf Root Path PK SK Sig) (keygenCost : S.sig.KR → ℕ)
    (signCost : SK → Root → ℕ) (rootCost : H.Key → List N → ℕ)
    (extractCost : H.Key → List N → N → Path → ℕ)
    (group : H.Key → PK → PMF (List N)) (groupCost : H.Key → PK → ℕ)
    (forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path))
    (forgeCost : H.Key → PK → List N → Sig → ℕ) (hk : H.Key) :
    crRed S group forge hk = liftPMF (runNoQuery
      (crRed.timed S keygenCost signCost rootCost extractCost group groupCost forge forgeCost
        hk).2.erase) := by
  rw [crRed.timed, crRedTree.erase_timed]
  rfl

/-- **Time of `crRed`**, the bound of `crRedTree.timeBound_timed` at the algorithms of `S`. -/
theorem crRed.timeBound_timed [DecidableEq N] {K E M Pf : Type}
    (S : Scheme H K E N M Pf Root Path PK SK Sig) (keygenCost : S.sig.KR → ℕ)
    (signCost : SK → Root → ℕ) (rootCost : H.Key → List N → ℕ)
    (extractCost : H.Key → List N → N → Path → ℕ)
    (group : H.Key → PK → PMF (List N)) (groupCost : H.Key → PK → ℕ)
    (forge : H.Key → PK → List N → Sig → PMF (Root × Sig × N × Path))
    (forgeCost : H.Key → PK → List N → Sig → ℕ) {k sg r x g f : ℕ}
    (hK : ∀ kr, keygenCost kr ≤ k) (hSg : ∀ sk m, signCost sk m ≤ sg)
    (hR : ∀ hk L, rootCost hk L ≤ r) (hX : ∀ hk L y p, extractCost hk L y p ≤ x)
    (hG : ∀ hk pk, groupCost hk pk ≤ g) (hF : ∀ hk pk L σ, forgeCost hk pk L σ ≤ f)
    (hk : H.Key) :
    StepTimeBound (crRed.timed S keygenCost signCost rootCost extractCost group groupCost forge
      forgeCost hk) (12 + 3 * k + sg + r + x + g + f) :=
  crRedTree.timeBound_timed _ _ _ _ _ _ _ _ _ _ _ _ hK hSg hR hX hG hF hk

end Time

end CatCrypt.Crypto.Anon.Signalling
