/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.DHPAKE
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Crypto.OracleSimulation

/-!
# Straight-line password extraction for Diffie–Hellman PAKEs

A simulator for a Diffie–Hellman PAKE plays an honest party without knowing its password:
it sends `simMsg z` for a secret `z` of its own. A trapdoor `trap pw z` gives, for every
password `pw`, the secret with which an honest party holding `pw` sends the same message.
When the adversary queries the key-derivation oracle at a key `k` for the peer message
`peer`, the simulator recognises the password the query was made for by the match test
`key pw (trap pw z) peer = k`, run over the candidate passwords.

The generic kit `DHExtractKit` states this interface; `extract` scans the candidates.

* `extract_sound`: an extracted password `pw` is correct: the real session with password
  `pw` and secret `trap pw z` sends the simulated message and derives the queried key.
* `extract_eq_of_not_doubleMatch`: a query at the real key of a candidate password is
  extracted to that password unless two queries match two distinct passwords.

The instances:

* **CPace** (`cpaceKit`). The password generator `gen pw = H1(pw)` is programmed by the
  simulator to `g^{td pw}`; the simulated message is `g^z = gen pw ^ (z / td pw)`, and the
  match test is `k = peer^(z / td pw)`, the Diffie–Hellman value of `g^z` and `peer` over the
  generator `gen pw` (`cpace_matchTest_iff`). The three bad events of the realization proof:
  - a double match on the passwords of generators `g^{c₁}`, `g^{c₂}` is a solution of the
    simultaneous Diffie–Hellman game `sdhGame` on the challenge `(g^z, g^{c₁}, g^{c₂})`
    (`cpace_doubleMatch_sdhWins`, `sdhWins_pub_iff`). At the level of games, the
    double-match game `dmGame` (the adversary sees `g^z` and the generator table, queries
    the match test as an oracle, and outputs two matches for distinct passwords) is bounded
    by the strong SDH game `ssdhGame` of Abdalla–Haase–Hesse, whose adversary queries the
    restricted DDH oracles `DDH(gen_i, X, ·, ·)`: `dmGame_le_ssdhGame` gives
    `Pr[dmGame A] ≤ 2 · Pr[ssdhGame (ssdhReduction A)]`. The reduction programs the
    generator of each password as `gen₁^r` or `gen₂^r` by a coin, answers each match query
    by one DDH query, and runs in the adversary's time plus one exponentiation per query
    (`ssdhReduction.timeBound_timed`);
  - a match against a generator independent of the adversary's view (an `H1` point it never
    queried) has probability at most `1/|S|` per query (`cpace_fresh_generator_le`), an
    information-theoretic term;
  - a query at the key of a passive session (both messages simulated) is a CDH solution for
    the explicit reduction `passiveCDHReduction`, which raises the query to the trapdoor
    (`passiveGame_eq_cdh`); its costed form runs in the adversary's time plus one
    exponentiation (`passiveCDHReduction.tree.timeBound_timed`).
* **Password-masked DH** (`dhpakeKit`, over `DHPAKE`): the simulator plays the server with
  `g^z`, and `unmask pw z` is the discrete logarithm of the unmasked message. SPAKE2 is the
  instance `spake2` with masks `M^pw`, `N^pw` of known logarithms `m`, `n`
  (`spake2Unmask pw z = z - n · pw`); OEKE is the instance whose `unmask` is read off the
  simulator's ideal-cipher table. A matched query is the honest key-hash input of the
  session (`dhpake_extract_hashInput`).

## References

* M. Abdalla, B. Haase, J. Hesse, *Security Analysis of CPace*, ASIACRYPT 2021
* D. Pointcheval, G. Wang, *VTBPEKE: Verifier-based Two-Basis Password Exponential Key
  Exchange*, ASIACRYPT 2017 (the simultaneous Diffie–Hellman problem)
* M. Abdalla, D. Pointcheval, *Simple Password-Based Encrypted Key Exchange Protocols*,
  CT-RSA 2005
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.DHExtract

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.PAKE.DH
open scoped ENNReal

/-! ## The generic kit -/

/-- **A straight-line extraction kit.** An honest party holding the password `pw` with
    secret `y` sends `msg pw y` and, on the peer message `peer`, derives the key
    `key pw y peer` provided it accepts `peer`. The simulator sends `simMsg z`, and the
    trapdoor `trap pw z` is the secret with which a party holding `pw` sends `simMsg z`. -/
structure DHExtractKit (S M K Pw : Type) where
  /-- The honest message of a party holding `pw` with secret `y`. -/
  msg : Pw → S → M
  /-- The key of a party holding `pw` with secret `y` on the peer message. -/
  key : Pw → S → M → K
  /-- The protocol's check on the peer message (CPace rejects the identity). -/
  accept : M → Bool
  /-- The simulator's message for its secret `z`. -/
  simMsg : S → M
  /-- The trapdoor: the secret of a party holding `pw` that sends `simMsg z`. -/
  trap : Pw → S → S
  /-- A party holding `pw` with secret `trap pw z` sends the simulated message. -/
  msg_trap : ∀ pw z, msg pw (trap pw z) = simMsg z

namespace DHExtractKit

variable {S M K Pw : Type} [DecidableEq K] (E : DHExtractKit S M K Pw)

/-- **The match test.** The query `k` for the peer message `peer` was made for the password
    `pw`: the peer message is accepted and `k` is the key of the party holding `pw` that
    sent the simulated message `simMsg z`. -/
def matchTest (z : S) (peer : M) (k : K) (pw : Pw) : Bool :=
  E.accept peer && decide (E.key pw (E.trap pw z) peer = k)

/-- **Extraction.** The first candidate password passing the match test. -/
def extract (z : S) (cands : List Pw) (peer : M) (k : K) : Option Pw :=
  cands.find? (E.matchTest z peer k)

/-- **The double-match event.** Two queries `k₁, k₂` among `ks` for the peer message
    `peer` pass the match test for two distinct candidate passwords. -/
def DoubleMatch (z : S) (cands : List Pw) (peer : M) (ks : List K) : Prop :=
  ∃ k₁ ∈ ks, ∃ k₂ ∈ ks, ∃ pw₁ ∈ cands, ∃ pw₂ ∈ cands,
    pw₁ ≠ pw₂ ∧ E.matchTest z peer k₁ pw₁ = true ∧ E.matchTest z peer k₂ pw₂ = true

/-- **An extracted password is correct.** If the query `k` extracts `pw`, then `pw` is a
    candidate, the peer message is accepted, and the real session with password `pw` and
    secret `trap pw z` sends the simulated message and derives the key `k`. -/
theorem extract_sound {z : S} {cands : List Pw} {peer : M} {k : K} {pw : Pw}
    (h : E.extract z cands peer k = some pw) :
    pw ∈ cands ∧ E.accept peer = true ∧ E.msg pw (E.trap pw z) = E.simMsg z ∧
      E.key pw (E.trap pw z) peer = k := by
  have hm := List.find?_some h
  have hmem := List.mem_of_find?_eq_some h
  simp only [matchTest, Bool.and_eq_true, decide_eq_true_eq] at hm
  exact ⟨hmem, hm.1, E.msg_trap pw z, hm.2⟩

/-- A query passing the match test for some candidate is extracted. -/
theorem extract_isSome {z : S} {cands : List Pw} {peer : M} {k : K} {pw : Pw}
    (hpw : pw ∈ cands) (hm : E.matchTest z peer k pw = true) :
    (E.extract z cands peer k).isSome := by
  grind [extract, List.find?_isSome]

/-- **Two extracted passwords are a double match.** Two queries of `ks` for one peer
    message that extract distinct passwords witness `DoubleMatch`. -/
theorem doubleMatch_of_extract {z : S} {cands : List Pw} {peer : M} {ks : List K}
    {k₁ k₂ : K} {pw₁ pw₂ : Pw} (hk₁ : k₁ ∈ ks) (hk₂ : k₂ ∈ ks)
    (h₁ : E.extract z cands peer k₁ = some pw₁) (h₂ : E.extract z cands peer k₂ = some pw₂)
    (hne : pw₁ ≠ pw₂) : E.DoubleMatch z cands peer ks :=
  ⟨k₁, hk₁, k₂, hk₂, pw₁, List.mem_of_find?_eq_some h₁, pw₂, List.mem_of_find?_eq_some h₂,
    hne, List.find?_some h₁, List.find?_some h₂⟩

/-- **Straight-line extraction is complete.** A query `k ∈ ks` passing the match test for
    the candidate `pw` is extracted to `pw` unless the queries `ks` contain a double
    match. -/
theorem extract_eq_of_not_doubleMatch {z : S} {cands : List Pw} {peer : M} {ks : List K}
    {k : K} {pw : Pw} (hk : k ∈ ks) (hpw : pw ∈ cands) (hm : E.matchTest z peer k pw = true)
    (hnd : ¬ E.DoubleMatch z cands peer ks) : E.extract z cands peer k = some pw := by
  obtain ⟨pw', hpw'⟩ := Option.isSome_iff_exists.mp (E.extract_isSome hpw hm)
  by_cases hne : pw' = pw
  · rw [hpw', hne]
  · exact absurd ⟨k, hk, k, hk, pw', List.mem_of_find?_eq_some hpw', pw, hpw, hne,
      List.find?_some hpw', hm⟩ hnd

end DHExtractKit

/-! ## The prime-order group -/

/-- **A prime-order group in exponent form.** Scalars `S` form a field (`ZMod p`), so
    every nonzero scalar has an inverse; `pub s = g^s` is a bijection onto the group and
    `exp Y s = Y^s` satisfies `(g^a)^b = g^{ab}`. -/
structure DHGroup (S W : Type) [Field S] where
  /-- The public value of a scalar, `s ↦ g^s`. -/
  pub : S ≃ W
  /-- Exponentiation, `exp Y s = Y^s`. -/
  exp : W → S → W
  /-- `(g^a)^b = g^{ab}`. -/
  exp_pub : ∀ a b, exp (pub a) b = pub (a * b)
  /-- The group operation, `mul Y Z = Y · Z`. -/
  mul : W → W → W
  /-- `g^a · g^b = g^{a + b}`. -/
  mul_pub : ∀ a b, mul (pub a) (pub b) = pub (a + b)

namespace DHGroup

variable {S W : Type} [Field S] (G : DHGroup S W)

/-- The discrete logarithm, the inverse of `pub`. -/
def dlog (Y : W) : S := G.pub.symm Y

/-- Unfolding lemma of `dlog` on a public value. -/
@[simp] theorem dlog_pub (s : S) : G.dlog (G.pub s) = s := G.pub.symm_apply_apply s

/-- `pub` of the discrete logarithm. -/
@[simp] theorem pub_dlog (Y : W) : G.pub (G.dlog Y) = Y := G.pub.apply_symm_apply Y

/-- The group operation in terms of the discrete logarithm. -/
theorem mul_eq (Y Z : W) : G.mul Y Z = G.pub (G.dlog Y + G.dlog Z) := by
  rw [← G.mul_pub, pub_dlog, pub_dlog]

/-- The discrete logarithm of a product is the sum of the discrete logarithms. -/
@[simp] theorem dlog_mul (Y Z : W) : G.dlog (G.mul Y Z) = G.dlog Y + G.dlog Z := by
  rw [mul_eq, dlog_pub]

/-- The group operation is commutative. -/
theorem mul_comm (Y Z : W) : G.mul Y Z = G.mul Z Y := by
  rw [mul_eq, mul_eq, add_comm]

/-- The group operation is associative. -/
theorem mul_assoc (Y Z U : W) : G.mul (G.mul Y Z) U = G.mul Y (G.mul Z U) := by
  simp only [mul_eq, dlog_pub, add_assoc]

/-- `g^0` is the identity on the right. -/
@[simp] theorem mul_pub_zero (Y : W) : G.mul Y (G.pub 0) = Y := by
  rw [mul_eq, dlog_pub, add_zero, pub_dlog]

/-- `g^0` is the identity on the left. -/
@[simp] theorem pub_zero_mul (Y : W) : G.mul (G.pub 0) Y = Y := by
  rw [mul_comm, mul_pub_zero]

/-- Exponentiation in terms of the discrete logarithm. -/
theorem exp_eq (Y : W) (s : S) : G.exp Y s = G.pub (G.dlog Y * s) := by
  simpa [dlog] using G.exp_pub (G.pub.symm Y) s

/-- `(Y^a)^b = Y^{ab}`. -/
theorem exp_exp (Y : W) (a b : S) : G.exp (G.exp Y a) b = G.exp Y (a * b) := by
  rw [exp_eq, exp_eq, exp_eq, dlog_pub, _root_.mul_assoc]

/-- Exponentiation distributes over the group operation: `(Y · Z)^s = Y^s · Z^s`. -/
theorem exp_mul (Y Z : W) (s : S) : G.exp (G.mul Y Z) s = G.mul (G.exp Y s) (G.exp Z s) := by
  simp only [exp_eq, mul_eq, dlog_pub, add_mul]

/-- `Y^a · Y^b = Y^{a + b}`. -/
theorem mul_exp_exp (Y : W) (a b : S) : G.mul (G.exp Y a) (G.exp Y b) = G.exp Y (a + b) := by
  rw [exp_eq, exp_eq, exp_eq, mul_pub, mul_add]

/-- `Y^{-1}` is the inverse of `Y`: `Y · Y^{-1} = g^0`. -/
theorem mul_exp_neg_one (Y : W) : G.mul Y (G.exp Y (-1)) = G.pub 0 := by
  rw [mul_eq, exp_eq, dlog_pub, mul_neg_one, add_neg_cancel]

/-- Exponentiation of an element other than the identity is injective. -/
theorem exp_injective {Y : W} (hY : Y ≠ G.pub 0) : Function.Injective (G.exp Y) := by
  intro a b h
  have hd : G.dlog Y ≠ 0 := fun h0 => hY (by rw [← h0, dlog, Equiv.apply_symm_apply])
  rw [exp_eq, exp_eq] at h
  exact mul_left_cancel₀ hd (G.pub.injective h)

/-- The Diffie–Hellman value of `X` and `Y` over the generator `gen`:
    `Y^{dlog X / dlog gen}`, which is `Y^x` for `X = gen^x`. -/
def cdhIn (gen X Y : W) : W := G.exp Y (G.dlog X * (G.dlog gen)⁻¹)

/-- **Changing the generator by an exponent.** For `u ≠ 0`, `k^u` is the Diffie–Hellman value
    of `X` and `Y` over `gen` iff `k` is that value over `gen^u`. -/
theorem exp_eq_cdhIn_iff {u : S} (hu : u ≠ 0) (gen X Y k : W) :
    G.exp k u = G.cdhIn gen X Y ↔ k = G.cdhIn (G.exp gen u) X Y := by
  simp only [cdhIn, exp_eq, dlog_pub, G.pub.injective.eq_iff, mul_inv]
  conv_rhs => rw [← G.pub_dlog k, G.pub.injective.eq_iff]
  grind

/-- The group as a `DHPAKE` with one password and identity masks, `dh x Y = Y^x`; its
    `cdhDef` is the CDH group of `G`. -/
def toDHPAKE : DHPAKE S W PUnit where
  pubEquiv := G.pub
  dh x Y := G.exp Y x
  maskC _ := Equiv.refl W
  maskS _ := Equiv.refl W

end DHGroup

/-! ## CPace -/

section CPace

variable {S W Pw : Type} [Field S] [DecidableEq W] (G : DHGroup S W)

/-- **The CPace kit.** The generator of the password `pw` is `g^{td pw}` (the value the
    simulator programs at `H1(pw)`); an honest party with secret `y` sends `gen^y` and on
    the peer message `peer ≠ 1` derives `peer^y`. The simulator sends `g^z`, and the
    trapdoor is `z / td pw`. -/
def cpaceKit (td : Pw → S) (htd : ∀ pw, td pw ≠ 0) : DHExtractKit S W W Pw where
  msg pw y := G.exp (G.pub (td pw)) y
  key _ y peer := G.exp peer y
  accept peer := decide (peer ≠ G.pub 0)
  simMsg z := G.pub z
  trap pw z := z * (td pw)⁻¹
  msg_trap pw z := by
    rw [G.exp_pub, mul_comm z, ← mul_assoc, mul_inv_cancel₀ (htd pw), one_mul]

/-- **The CPace match test is a Diffie–Hellman relation.** A query `k` for `peer` passes the
    test for `pw` iff `peer` is not the identity and `k` is the Diffie–Hellman value of the
    simulated message `g^z` and `peer` over the generator `g^{td pw}`. -/
theorem cpace_matchTest_iff (td : Pw → S) (htd : ∀ pw, td pw ≠ 0) (z : S) (peer k : W)
    (pw : Pw) :
    (cpaceKit G td htd).matchTest z peer k pw = true ↔
      peer ≠ G.pub 0 ∧ k = G.cdhIn (G.pub (td pw)) (G.pub z) peer := by
  simp only [DHExtractKit.matchTest, cpaceKit, DHGroup.cdhIn, DHGroup.dlog_pub,
    Bool.and_eq_true, decide_eq_true_eq]
  grind

/-- **The CPace extraction is correct.** A query `k` for `peer` extracting `pw` is the key
    of the real CPace session with password `pw` and secret `y = z / td pw`: that session
    sends the simulated message `g^z` and derives `peer^y = k`. -/
theorem cpace_extract_sound (td : Pw → S) (htd : ∀ pw, td pw ≠ 0) {z : S}
    {cands : List Pw} {peer k : W} {pw : Pw}
    (h : (cpaceKit G td htd).extract z cands peer k = some pw) :
    G.exp (G.pub (td pw)) (z * (td pw)⁻¹) = G.pub z ∧ G.exp peer (z * (td pw)⁻¹) = k :=
  ⟨((cpaceKit G td htd).extract_sound h).2.2.1, ((cpaceKit G td htd).extract_sound h).2.2.2⟩

/-! ### Simultaneous Diffie–Hellman -/

/-- The winning condition of the simultaneous Diffie–Hellman problem on the challenge
    `(X, gen₁, gen₂)`: an output `(Y, K₁, K₂)` with `Y` not the identity and `K_i` the
    Diffie–Hellman value of `X` and `Y` over `gen_i`. -/
def SDHWins (X gen₁ gen₂ : W) (o : W × W × W) : Prop :=
  o.1 ≠ G.pub 0 ∧ o.2.1 = G.cdhIn gen₁ X o.1 ∧ o.2.2 = G.cdhIn gen₂ X o.1

instance (X gen₁ gen₂ : W) (o : W × W × W) : Decidable (SDHWins G X gen₁ gen₂ o) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **A CPace double match is a simultaneous Diffie–Hellman solution.** Queries `k₁`, `k₂`
    for `peer` matching the passwords `pw₁`, `pw₂` give the output `(peer, k₁, k₂)` on the
    challenge `(g^z, gen pw₁, gen pw₂)`. -/
theorem cpace_doubleMatch_sdhWins (td : Pw → S) (htd : ∀ pw, td pw ≠ 0) {z : S}
    {peer k₁ k₂ : W} {pw₁ pw₂ : Pw}
    (h₁ : (cpaceKit G td htd).matchTest z peer k₁ pw₁ = true)
    (h₂ : (cpaceKit G td htd).matchTest z peer k₂ pw₂ = true) :
    SDHWins G (G.pub z) (G.pub (td pw₁)) (G.pub (td pw₂)) (peer, k₁, k₂) := by
  rw [cpace_matchTest_iff] at h₁ h₂
  exact ⟨h₁.1, h₁.2, h₂.2⟩

variable [Fintype S] [Nonempty S]

/-- An adversary against the simultaneous Diffie–Hellman problem. -/
abbrev SDHAdversary (W : Type) := W → W → W → PMF (W × W × W)

/-- **The simultaneous Diffie–Hellman game** (Pointcheval–Wang): the challenger samples
    `x`, `c₁`, `c₂`, the adversary receives `(g^x, g^{c₁}, g^{c₂})`, and it wins with
    `SDHWins`. The strong variant `sSDH` of Abdalla–Haase–Hesse adds a restricted DDH
    oracle; the reductions of this file make no oracle query. -/
noncomputable def sdhGame (A : SDHAdversary W) : PMF Bool :=
  (PMF.uniformFintype S).bind fun x => (PMF.uniformFintype S).bind fun c₁ =>
  (PMF.uniformFintype S).bind fun c₂ =>
    (A (G.pub x) (G.pub c₁) (G.pub c₂)).map fun o =>
      decide (SDHWins G (G.pub x) (G.pub c₁) (G.pub c₂) o)

omit [Fintype S] [Nonempty S] [DecidableEq W] in
/-- The SDH winning condition on a challenge of public values, in exponent form: the keys
    are `Y^(x / c₁)` and `Y^(x / c₂)`, the CPace match tests of the simulated message `g^x`
    for the generators `g^{c₁}`, `g^{c₂}`. -/
theorem sdhWins_pub_iff (x c₁ c₂ : S) (o : W × W × W) :
    SDHWins G (G.pub x) (G.pub c₁) (G.pub c₂) o ↔
      o.1 ≠ G.pub 0 ∧ o.2.1 = G.exp o.1 (x * c₁⁻¹) ∧ o.2.2 = G.exp o.1 (x * c₂⁻¹) := by
  simp only [SDHWins, DHGroup.cdhIn, DHGroup.dlog_pub]

/-! ### A generator independent of the adversary's view -/

/-- **A match against a fresh generator.** For a peer message `peer` other than the
    identity, a nonzero simulator secret `z` and any key `k` fixed before the trapdoor `c`
    of the generator is sampled, the match `k = peer^(z / c)` holds with probability at
    most `1/|S|`: the map `c ↦ peer^(z / c)` is injective. -/
theorem cpace_fresh_generator_le {peer : W} (hpeer : peer ≠ G.pub 0) {z : S} (hz : z ≠ 0)
    (k : W) :
    ((PMF.uniformFintype S).map fun c => decide (k = G.exp peer (z * c⁻¹))) true ≤
      (Fintype.card S : ℝ≥0∞)⁻¹ := by
  classical
  rw [PMF.map_uniform_apply]
  calc ((Finset.univ.filter fun c => decide (k = G.exp peer (z * c⁻¹)) = true).card :
        ℝ≥0∞) * (Fintype.card S : ℝ≥0∞)⁻¹
      ≤ 1 * (Fintype.card S : ℝ≥0∞)⁻¹ := by
        gcongr
        exact_mod_cast Finset.card_le_one.mpr fun a ha b hb => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha hb
          have h := G.exp_injective hpeer (ha.symm.trans hb)
          exact inv_injective (mul_left_cancel₀ hz h)
    _ = (Fintype.card S : ℝ≥0∞)⁻¹ := one_mul _

/-! ### Passive sessions -/

/-- An adversary against a passive CPace session for a password with generator `g^c`: it
    sees the two simulated messages and outputs a key query. -/
abbrev PassiveAdversary (W : Type) := W → W → SPComp W

/-- **The passive-session experiment.** Both parties are simulated with the messages
    `g^a`, `g^b` drawn by the key generation of the CDH group of `G`; the adversary wins
    when its query is the key `(g^b)^(a / c)` of the session with the password of
    generator `g^c`. -/
noncomputable def passiveGame [SampleableType W] (c : S) (A : PassiveAdversary W) :
    SPComp Bool :=
  SPComp.bind (cdhDef G.toDHPAKE).keygen fun ka =>
  SPComp.bind (cdhDef G.toDHPAKE).keygen fun kb =>
  SPComp.bind (A ka.2 kb.2) fun k => SPComp.pure (decide (k = G.exp kb.2 (G.dlog ka.1 * c⁻¹)))

/-- **The CDH reduction for passive sessions.** On the CDH challenge `(g^a, g^b)` it runs
    the passive adversary on the challenge as the two simulated messages and raises its
    query to the trapdoor `c`. -/
noncomputable def passiveCDHReduction (c : S) (A : PassiveAdversary W) : CDH_Adversary W :=
  fun gA gB => SPComp.bind (A gA gB) fun k => SPComp.pure (G.exp k c)

/-- **A passive-session query is a CDH solution.** For a nonzero trapdoor `c`, the
    passive-session experiment of `A` succeeds with the CDH advantage of
    `passiveCDHReduction G c A`. -/
theorem passiveGame_eq_cdh [SampleableType W] {c : S} (hc : c ≠ 0) (A : PassiveAdversary W) :
    prTrue (passiveGame G c A) Heap.empty =
      CDH_Advantage (cdhDef G.toDHPAKE) (passiveCDHReduction G c A) := by
  have hiff : ∀ (k Y : W) (a : S), (k = G.exp Y (a * c⁻¹)) ↔ (G.exp k c = G.exp Y a) := by
    intro k Y a
    rw [G.exp_eq k, G.exp_eq Y, G.exp_eq Y, G.pub.injective.eq_iff]
    constructor
    · rintro rfl
      grind [DHGroup.dlog_pub]
    · intro hk
      rw [← G.pub.apply_symm_apply k]
      grind [DHGroup.dlog]
  unfold CDH_Advantage CDH_Game passiveGame passiveCDHReduction
  simp only [SPComp.monad_bind_eq]
  congr 1
  refine congrArg _ (funext fun ka => congrArg _ (funext fun kb => ?_))
  rw [SPComp.bind_assoc]
  refine congrArg _ (funext fun k => ?_)
  rw [SPComp.pure_bind]
  exact congrArg _ (decide_eq_decide.mpr (hiff k kb.2 _))

derive_reduction passiveCDHReduction

omit [DecidableEq W] [Fintype S] [Nonempty S] in
/-- **Time of the passive-session CDH reduction.** A passive adversary `A` of time at most
    `T` and call cost at most `a`, with an exponentiation of cost at most `te`, gives a CDH
    adversary of time at most `T + a + te + 2`. -/
theorem passiveCDHReduction.tree.timeBound_timed (c : S) (A : W → W → SPTree.Timed W)
    (ACost : W → W → ℕ) (gA gB : W) (exp : W → S → W) (expCost : W → S → ℕ) {T a te : ℕ}
    (hA : ∀ x y, (A x y).time ≤ T) (hAc : ∀ x y, ACost x y ≤ a)
    (he : ∀ x s, expCost x s ≤ te) :
    SPTree.Timed.stepTime (passiveCDHReduction.tree.timed G c A ACost gA gB exp expCost) ≤
      T + a + te + 2 := by
  time_bound

/-! ### Double matches and the strong simultaneous Diffie–Hellman problem -/

/-- **The restricted DDH oracle** of the strong SDH problem on the challenge
    `(X, gen₁, gen₂)`: the query `(i, Y, K)` asks whether `Y` is not the identity and `K` is
    the Diffie–Hellman value of `X` and `Y` over `gen₁` (`i = true`) or `gen₂` (`i = false`).
    Each DDH test has its first two arguments fixed to `(gen_i, X)`; the identity test on `Y`
    is public. -/
noncomputable def ssdhOracle (X gen₁ gen₂ : W) (s : Unit) (q : Bool × W × W) :
    PMF (Bool × Unit) :=
  PMF.pure
    (decide (q.2.1 ≠ G.pub 0 ∧ q.2.2 = G.cdhIn (if q.1 then gen₁ else gen₂) X q.2.1), s)

/-- An adversary against the strong SDH problem: on the challenge `(X, gen₁, gen₂)` it
    queries the restricted DDH oracle and outputs `(Y, K₁, K₂)`. -/
abbrev SSDHAdversary (W : Type) := W → W → W → OracleAdv (Bool × W × W) Bool (W × W × W)

/-- **The match oracle** of the double-match game with the simulated message `X` and the
    generator table `H`: the query `(pw, peer, k)` asks whether `peer` is not the identity and
    `k` is the Diffie–Hellman value of `X` and `peer` over `H pw`, the CPace match test
    (`dmOracle_eq_matchTest`). -/
noncomputable def dmOracle (X : W) (H : Pw → W) (s : Unit) (q : Pw × W × W) :
    PMF (Bool × Unit) :=
  PMF.pure (decide (q.2.1 ≠ G.pub 0 ∧ q.2.2 = G.cdhIn (H q.1) X q.2.1), s)

/-- **The double-match winning condition** on the output `(peer, k₁, k₂, pw₁, pw₂)`: the
    passwords are distinct and `(peer, k₁, k₂)` solves the SDH problem on `(X, H pw₁, H pw₂)`,
    so that both queries pass the match test. -/
def DMWins (X : W) (H : Pw → W) (o : W × W × W × Pw × Pw) : Prop :=
  o.2.2.2.1 ≠ o.2.2.2.2 ∧ SDHWins G X (H o.2.2.2.1) (H o.2.2.2.2) (o.1, o.2.1, o.2.2.1)

instance [DecidableEq Pw] (X : W) (H : Pw → W) (o : W × W × W × Pw × Pw) :
    Decidable (DMWins G X H o) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- An adversary against CPace double matches: on the simulated message `X` and the
    generator table `H` it queries the match oracle and outputs `(peer, k₁, k₂, pw₁, pw₂)`. -/
abbrev DMAdversary (W Pw : Type) :=
  W → (Pw → W) → OracleAdv (Pw × W × W) Bool (W × W × W × Pw × Pw)

/-- The generator table of the strong SDH reduction: the generator of `pw` is
    `gen₁^{r pw}` or `gen₂^{r pw}` according to the coin `b pw`. -/
def ssdhTable (gen₁ gen₂ : W) (b : Pw → Bool) (r : Pw → Sˣ) (pw : Pw) : W :=
  G.exp (if b pw then gen₁ else gen₂) (r pw)

/-- The output of the strong SDH reduction on a double match `(peer, k₁, k₂, pw₁, pw₂)`: the
    keys raised to the exponents of their passwords, the key of the password with coin `true`
    first. -/
def ssdhConvert (b : Pw → Bool) (r : Pw → Sˣ) (o : W × W × W × Pw × Pw) : W × W × W :=
  if b o.2.2.2.1 = true then (o.1, G.exp o.2.1 (r o.2.2.2.1), G.exp o.2.2.1 (r o.2.2.2.2))
  else (o.1, G.exp o.2.2.1 (r o.2.2.2.2), G.exp o.2.1 (r o.2.2.2.1))

/-- **The strong SDH reduction for double matches.** On the challenge `(X, gen₁, gen₂)` it
    flips a coin `b pw` and draws a nonzero exponent `r pw` for every password, gives the
    double-match adversary the simulated message `X` and the generator table
    `ssdhTable gen₁ gen₂ b r`, answers each match query `(pw, peer, k)` by the DDH query
    `(b pw, peer, k^{r pw})`, and converts the output with `ssdhConvert`. -/
noncomputable def ssdhReduction [Fintype Pw] [DecidableEq Pw] [DecidableEq S]
    (A : DMAdversary W Pw) : SSDHAdversary W :=
  fun X gen₁ gen₂ =>
    .rand (PMF.uniformFintype (Pw → Bool)) fun b =>
    .rand (PMF.uniformFintype (Pw → Sˣ)) fun r =>
      (OracleAdv.mapQuery (fun q => (b q.1, q.2.1, G.exp q.2.2 (r q.1)))
        (A X (ssdhTable G gen₁ gen₂ b r))).bind fun o => .ret (ssdhConvert G b r o)

derive_reduction ssdhReduction

omit [DecidableEq W] [Nonempty S] in
/-- **Time of the strong SDH reduction.** A double-match adversary of time at most `T` with
    at most `q` match queries and call cost at most `a`, with exponentiations of cost at most
    `te`, gives a strong SDH adversary of time at most `a + T + q (te + 4) + 2 te + 10`: one
    exponentiation per query and two for the output. -/
theorem ssdhReduction.timeBound_timed [Fintype Pw] [DecidableEq Pw] [DecidableEq S]
    (A : W → (Pw → W) → OracleAdv.Timed (Pw × W × W) Bool (W × W × W × Pw × Pw))
    (ACost : W → (Pw → W) → ℕ) (X gen₁ gen₂ : W) (expCost : W → S → ℕ) {T q a te : ℕ}
    (hA : ∀ X H, (A X H).TimeBound T) (hq : ∀ X H, (A X H).erase.IsQueryBound q)
    (hAc : ∀ X H, ACost X H ≤ a) (he : ∀ Y s, expCost Y s ≤ te) :
    OracleAdv.Timed.StepTimeBound (ssdhReduction.timed G A ACost X gen₁ gen₂ expCost)
      (a + T + q * (te + 4) + 2 * te + 10) := by
  have hB : ∀ (b : Pw → Bool) (r : Pw → Sˣ), OracleAdv.Timed.StepTimeBound
      ((OracleAdv.Timed.mapQuery (fun qr => (b qr.1, qr.2.1, G.exp qr.2.2 ↑(r qr.1)))
        (fun qr => 3 + (expCost qr.2.2 ↑(r qr.1) + 1)) (A X (ssdhTable G gen₁ gen₂ b r))).bind
        fun o => (3 + if b o.2.2.2.1 = true then
            1 + (expCost o.2.1 ↑(r o.2.2.2.1) + 1) + (1 + (expCost o.2.2.1 ↑(r o.2.2.2.2) + 1))
          else 1 + (expCost o.2.2.1 ↑(r o.2.2.2.2) + 1) + (1 + (expCost o.2.1 ↑(r o.2.2.2.1) + 1)),
          OracleAdv.Timed.ret (ssdhConvert G b r o)))
      (T + q * (te + 4) + (2 * te + 7)) := fun b r =>
    OracleAdv.Timed.timeBound_bind
      (OracleAdv.Timed.timeBound_mapQuery _ _ (fun qr => by have := he qr.2.2 (r qr.1); omega)
        (hA _ _) (hq _ _))
      fun o => ⟨by
        have := he o.2.1 (r o.2.2.2.1)
        have := he o.2.2.1 (r o.2.2.2.2)
        split <;> omega, trivial⟩
  unfold ssdhReduction.timed
  refine ⟨Nat.zero_le _, by omega, fun b => ⟨Nat.zero_le _, by grind, fun r => ?_⟩⟩
  dsimp only
  obtain ⟨h1, h2⟩ := hB b r
  have := hAc X (ssdhTable G gen₁ gen₂ b r)
  exact ⟨by omega, h2.mono (by omega)⟩

variable [DecidableEq S]

/-- **The strong simultaneous Diffie–Hellman game** `sSDH` (Abdalla–Haase–Hesse): the
    challenger samples `x` and two generators `g^{c₁}`, `g^{c₂}` (`c_i ≠ 0`); the adversary
    receives `(g^x, g^{c₁}, g^{c₂})`, queries `ssdhOracle`, and wins with `SDHWins`. -/
noncomputable def ssdhGame (A : SSDHAdversary W) : PMF Bool :=
  (PMF.uniformFintype S).bind fun x => (PMF.uniformFintype Sˣ).bind fun c₁ =>
  (PMF.uniformFintype Sˣ).bind fun c₂ =>
    (OracleAdv.run (ssdhOracle G (G.pub x) (G.pub c₁) (G.pub c₂))
      (A (G.pub x) (G.pub c₁) (G.pub c₂)) ()).map fun y =>
        decide (SDHWins G (G.pub x) (G.pub c₁) (G.pub c₂) y.1)

variable [Fintype Pw] [DecidableEq Pw]

/-- **The double-match game.** The challenger samples the simulator's secret `z` and a
    nonzero trapdoor `td pw` for every password, programs the generator table
    `H pw = g^{td pw}`, and runs the adversary on `g^z` and `H` against the match oracle; it
    wins with `DMWins`. -/
noncomputable def dmGame (A : DMAdversary W Pw) : PMF Bool :=
  (PMF.uniformFintype S).bind fun z => (PMF.uniformFintype (Pw → Sˣ)).bind fun td =>
    (OracleAdv.run (dmOracle G (G.pub z) fun pw => G.pub (td pw))
      (A (G.pub z) fun pw => G.pub (td pw)) ()).map fun y =>
        decide (DMWins G (G.pub z) (fun pw => G.pub (td pw)) y.1)

omit [Fintype S] [Nonempty S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw] in
/-- The match oracle of the double-match game answers with the CPace match test of the
    trapdoors `td`. -/
theorem dmOracle_eq_matchTest (td : Pw → Sˣ) (z : S) (s : Unit) (q : Pw × W × W) :
    dmOracle G (G.pub z) (fun pw => G.pub (td pw)) s q =
      PMF.pure ((cpaceKit G (fun pw => (td pw : S)) fun pw => (td pw).ne_zero).matchTest z
        q.2.1 q.2.2 q.1, s) := by
  have h := cpace_matchTest_iff G (fun pw => (td pw : S)) (fun pw => (td pw).ne_zero) z
    q.2.1 q.2.2 q.1
  simp only [dmOracle]
  congr 2
  grind

omit [Fintype S] [Nonempty S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw] in
/-- The reduction's translated DDH queries answer the match oracle of its generator table. -/
theorem ssdhOracle_translate (X gen₁ gen₂ : W) (b : Pw → Bool) (r : Pw → Sˣ) :
    (fun s (q : Pw × W × W) =>
        ssdhOracle G X gen₁ gen₂ s (b q.1, q.2.1, G.exp q.2.2 (r q.1))) =
      dmOracle G X (ssdhTable G gen₁ gen₂ b r) := by
  funext s q
  simp only [ssdhOracle, dmOracle, ssdhTable]
  congr 2
  exact decide_eq_decide.mpr
    (and_congr_right fun _ => G.exp_eq_cdhIn_iff (r q.1).ne_zero _ _ _ _)

omit [Fintype S] [Nonempty S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw] [DecidableEq W] in
/-- **A double match on passwords of distinct coins is an SDH solution.** -/
theorem sdhWins_ssdhConvert {X gen₁ gen₂ : W} {b : Pw → Bool} {r : Pw → Sˣ}
    {o : W × W × W × Pw × Pw} (hw : DMWins G X (ssdhTable G gen₁ gen₂ b r) o)
    (hb : b o.2.2.2.1 ≠ b o.2.2.2.2) :
    SDHWins G X gen₁ gen₂ (ssdhConvert G b r o) := by
  obtain ⟨peer, k₁, k₂, pw₁, pw₂⟩ := o
  obtain ⟨-, hY, h₁, h₂⟩ := hw
  rw [ssdhTable, ← G.exp_eq_cdhIn_iff (r pw₁).ne_zero] at h₁
  rw [ssdhTable, ← G.exp_eq_cdhIn_iff (r pw₂).ne_zero] at h₂
  simp only [ssdhConvert, SDHWins] at hY h₁ h₂ hb ⊢
  cases hb₁ : b pw₁ <;> cases hb₂ : b pw₂ <;> simp_all

omit [Nonempty S] in
/-- The run of the reduction against the restricted DDH oracle is the run of the
    double-match adversary against the match oracle of the reduction's generator table. -/
theorem run_ssdhReduction (A : DMAdversary W Pw) (X gen₁ gen₂ : W) :
    (OracleAdv.run (ssdhOracle G X gen₁ gen₂) (ssdhReduction G A X gen₁ gen₂) ()).map
        (fun y => decide (SDHWins G X gen₁ gen₂ y.1)) =
      (PMF.uniformFintype (Pw → Bool)).bind fun b =>
      (PMF.uniformFintype (Pw → Sˣ)).bind fun r =>
        (OracleAdv.run (dmOracle G X (ssdhTable G gen₁ gen₂ b r))
          (A X (ssdhTable G gen₁ gen₂ b r)) ()).map fun y =>
            decide (SDHWins G X gen₁ gen₂ (ssdhConvert G b r y.1)) := by
  simp only [ssdhReduction, OracleAdv.run_rand, OracleAdv.run_bind, OracleAdv.run_mapQuery,
    OracleAdv.run_ret, PMF.map_bind, ssdhOracle_translate]
  refine congrArg _ (funext fun b => congrArg _ (funext fun r => ?_))
  simp only [PMF.pure_map]
  exact PMF.bind_pure_comp _ _

omit [Fintype S] [Nonempty S] [DecidableEq S] [DecidableEq W] in
/-- **Two distinct passwords get distinct coins with probability one half.** -/
theorem two_mul_coin_tsum {pw₁ pw₂ : Pw} (h : pw₁ ≠ pw₂) :
    2 * ∑' b : Pw → Bool, PMF.uniformFintype (Pw → Bool) b *
      (if b pw₁ ≠ b pw₂ then 1 else 0) = 1 := by
  let σ : (Pw → Bool) → (Pw → Bool) := fun b => Function.update b pw₂ (!b pw₂)
  have hσ : Function.Involutive σ := fun b => by
    funext p
    by_cases hp : p = pw₂ <;> simp [σ, Function.update, hp]
  have hswap : ∀ b : Pw → Bool, (σ b pw₁ ≠ σ b pw₂) ↔ (b pw₁ = b pw₂) := fun b => by
    simp [σ, h]
  have hperm : ∑' b : Pw → Bool, PMF.uniformFintype (Pw → Bool) b *
      (if b pw₁ ≠ b pw₂ then 1 else 0) = ∑' b : Pw → Bool, PMF.uniformFintype (Pw → Bool) b *
      (if b pw₁ = b pw₂ then 1 else 0) := by
    rw [← (hσ.toPerm σ).tsum_eq]
    refine tsum_congr fun b => ?_
    simp only [Function.Involutive.coe_toPerm, PMF.uniformFintype_apply, hswap]
  rw [two_mul]
  nth_rewrite 2 [hperm]
  rw [← ENNReal.tsum_add]
  refine (tsum_congr fun b => ?_).trans (PMF.uniformFintype (Pw → Bool)).tsum_coe
  by_cases hb : b pw₁ = b pw₂ <;> simp [hb]

/-- A bind whose continuations are bounded by `k` times others is bounded by `k` times the
    bind of the others. -/
theorem bind_apply_le_mul {α β : Type} (p : PMF α) (f g : α → PMF β) (b : β) (k : ℝ≥0∞)
    (h : ∀ a, f a b ≤ k * g a b) : (p.bind f) b ≤ k * (p.bind g) b := by
  rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun a => by
    rw [mul_left_comm]
    gcongr
    exact h a

/-- The probability of a decided event, as a sum over the outcomes satisfying it. -/
theorem map_decide_apply_true {α : Type} (p : PMF α) (P : α → Prop) [DecidablePred P] :
    (p.map fun a => decide (P a)) true = ∑' a, if P a then p a else 0 := by
  rw [PMF.map_apply]
  refine tsum_congr fun a => ?_
  by_cases h : P a <;> simp [h]

omit [Nonempty S] in
/-- **The inner bound.** For a fixed simulated message `g^x` and fixed nonzero generators,
    the double-match probability over the trapdoors is at most twice the success probability
    of the reduction. -/
theorem dm_inner_le (A : DMAdversary W Pw) (x : S) (c₁ c₂ : Sˣ) :
    ((PMF.uniformFintype (Pw → Sˣ)).bind fun td =>
      (OracleAdv.run (dmOracle G (G.pub x) fun pw => G.pub (td pw))
        (A (G.pub x) fun pw => G.pub (td pw)) ()).map fun y =>
          decide (DMWins G (G.pub x) (fun pw => G.pub (td pw)) y.1)) true ≤
    2 * ((OracleAdv.run (ssdhOracle G (G.pub x) (G.pub c₁) (G.pub c₂))
      (ssdhReduction G A (G.pub x) (G.pub c₁) (G.pub c₂)) ()).map fun y =>
        decide (SDHWins G (G.pub x) (G.pub c₁) (G.pub c₂) y.1)) true := by
  rw [run_ssdhReduction]
  let Hf : (Pw → Sˣ) → Pw → W := fun td pw => G.pub (td pw)
  let R : (Pw → W) → PMF ((W × W × W × Pw × Pw) × Unit) := fun H =>
    OracleAdv.run (dmOracle G (G.pub x) H) (A (G.pub x) H) ()
  let E : (Pw → Sˣ) → (W × W × W × Pw × Pw) × Unit → ℝ≥0∞ := fun td y =>
    if DMWins G (G.pub x) (Hf td) y.1 then R (Hf td) y else 0
  let c : (Pw → Bool) → (W × W × W × Pw × Pw) × Unit → ℝ≥0∞ := fun b y =>
    if b y.1.2.2.2.1 ≠ b y.1.2.2.2.2 then 1 else 0
  let F : (Pw → Bool) → (Pw → W) → ℝ≥0∞ := fun b H => ∑' y,
    if DMWins G (G.pub x) H y.1 ∧ b y.1.2.2.2.1 ≠ b y.1.2.2.2.2 then R H y else 0
  let φ : (Pw → Bool) → (Pw → Sˣ) ≃ (Pw → Sˣ) := fun b =>
    Equiv.piCongrRight fun pw => Equiv.mulLeft (if b pw then c₁ else c₂)
  have htab : ∀ b r, ssdhTable G (G.pub c₁) (G.pub c₂) b r = Hf (φ b r) := fun b r => by
    funext pw
    by_cases hb : b pw = true <;> simp [ssdhTable, hb, φ, Hf, G.exp_pub]
  have hstep : ∀ b r, F b (ssdhTable G (G.pub c₁) (G.pub c₂) b r) ≤
      (PMF.map (fun y => decide (SDHWins G (G.pub x) (G.pub c₁) (G.pub c₂)
        (ssdhConvert G b r y.1))) (R (ssdhTable G (G.pub c₁) (G.pub c₂) b r))) true := by
    intro b r
    rw [map_decide_apply_true]
    refine ENNReal.tsum_le_tsum fun y => ?_
    by_cases h1 : DMWins G (G.pub x) (ssdhTable G (G.pub c₁) (G.pub c₂) b r) y.1 ∧
      b y.1.2.2.2.1 ≠ b y.1.2.2.2.2
    · simp only [h1.1, h1.2, sdhWins_ssdhConvert G h1.1 h1.2, ne_eq, not_false_eq_true,
        and_self, ite_true, le_refl]
    · simp only [h1, ite_false, zero_le]
  have hre : ∀ b, ∑' r, PMF.uniformFintype (Pw → Sˣ) r *
      F b (ssdhTable G (G.pub c₁) (G.pub c₂) b r) =
      ∑' td, PMF.uniformFintype (Pw → Sˣ) td * ∑' y, E td y * c b y := by
    intro b
    refine Eq.trans ?_ ((φ b).tsum_eq fun td =>
      PMF.uniformFintype (Pw → Sˣ) td * ∑' y, E td y * c b y)
    refine tsum_congr fun r => ?_
    rw [htab, PMF.uniformFintype_apply, PMF.uniformFintype_apply]
    congr 1
    refine tsum_congr fun y => ?_
    by_cases hD : DMWins G (G.pub x) (Hf (φ b r)) y.1 <;>
      by_cases hc : b y.1.2.2.2.1 ≠ b y.1.2.2.2.2 <;> simp [E, c, hD, hc]
  have hcoin : ∀ td y, E td y * (2 * ∑' b, PMF.uniformFintype (Pw → Bool) b * c b y) =
      E td y := by
    intro td y
    by_cases hD : DMWins G (G.pub x) (Hf td) y.1
    · simp only [c]
      rw [two_mul_coin_tsum hD.1, mul_one]
    · simp [E, hD]
  calc ((PMF.uniformFintype (Pw → Sˣ)).bind fun td =>
        (R (Hf td)).map fun y => decide (DMWins G (G.pub x) (Hf td) y.1)) true
      = ∑' td, PMF.uniformFintype (Pw → Sˣ) td * ∑' y, E td y := by
        rw [PMF.bind_apply]
        exact tsum_congr fun td => by rw [map_decide_apply_true]
    _ = ∑' td, PMF.uniformFintype (Pw → Sˣ) td *
          ∑' y, E td y * (2 * ∑' b, PMF.uniformFintype (Pw → Bool) b * c b y) := by
        simp only [hcoin]
    _ = 2 * ∑' b, PMF.uniformFintype (Pw → Bool) b *
          ∑' td, PMF.uniformFintype (Pw → Sˣ) td * ∑' y, E td y * c b y := by
        simp only [← ENNReal.tsum_mul_left]
        refine Eq.trans ?_ ENNReal.tsum_comm
        refine tsum_congr fun td => Eq.trans ?_ ENNReal.tsum_comm
        exact tsum_congr fun y => tsum_congr fun b => by ring
    _ = 2 * ∑' b, PMF.uniformFintype (Pw → Bool) b * ∑' r, PMF.uniformFintype (Pw → Sˣ) r *
          F b (ssdhTable G (G.pub c₁) (G.pub c₂) b r) := by
        simp only [hre]
    _ ≤ 2 * ((PMF.uniformFintype (Pw → Bool)).bind fun b =>
          (PMF.uniformFintype (Pw → Sˣ)).bind fun r =>
            (R (ssdhTable G (G.pub c₁) (G.pub c₂) b r)).map fun y =>
              decide (SDHWins G (G.pub x) (G.pub c₁) (G.pub c₂)
                (ssdhConvert G b r y.1))) true := by
        rw [PMF.bind_apply]
        gcongr with b
        rw [PMF.bind_apply]
        gcongr with r
        exact hstep b r

/-- **A CPace double match reduces to strong SDH** (tightly, up to the factor `2` of the
    reduction's coins). For every double-match adversary `A`,
    `Pr[dmGame A] ≤ 2 · Pr[ssdhGame (ssdhReduction A)]`. -/
theorem dmGame_le_ssdhGame (A : DMAdversary W Pw) :
    dmGame G A true ≤ 2 * ssdhGame G (ssdhReduction G A) true := by
  have hconst : dmGame G A = (PMF.uniformFintype S).bind fun x =>
      (PMF.uniformFintype Sˣ).bind fun _ => (PMF.uniformFintype Sˣ).bind fun _ =>
        (PMF.uniformFintype (Pw → Sˣ)).bind fun td =>
          (OracleAdv.run (dmOracle G (G.pub x) fun pw => G.pub (td pw))
            (A (G.pub x) fun pw => G.pub (td pw)) ()).map fun y =>
              decide (DMWins G (G.pub x) (fun pw => G.pub (td pw)) y.1) := by
    simp only [PMF.bind_const, dmGame]
  rw [hconst, ssdhGame]
  exact bind_apply_le_mul _ _ _ _ _ fun x => bind_apply_le_mul _ _ _ _ _ fun c₁ =>
    bind_apply_le_mul _ _ _ _ _ fun c₂ => dm_inner_le G A x c₁ c₂

end CPace

/-! ## Password-masked Diffie–Hellman: SPAKE2 and OEKE -/

section Masked

variable {S W Pw : Type}

/-- **The kit of a password-masked DH PAKE.** The simulator plays the server with the
    message `g^z`; `unmask pw z` is the server secret of a party holding `pw` that sends
    `g^z` (the discrete logarithm of the unmasked message), and the key on the client
    message `X*` is `dh y (maskC pw)⁻¹(X*)`. -/
def dhpakeKit (P : DHPAKE S W Pw) (unmask : Pw → S → S)
    (hunmask : ∀ pw z, msgS P pw (unmask pw z) = P.pubEquiv z) : DHExtractKit S W W Pw where
  msg := msgS P
  key pw y peer := P.dh y ((P.maskC pw).symm peer)
  accept _ := true
  simMsg := P.pubEquiv
  trap := unmask
  msg_trap := hunmask

/-- **A matched query is the honest key-hash input.** With `dh` symmetric on public values,
    a query `k` for the client message `X*` extracting `pw` is the last component of the
    key-hash input `(pw, X*, g^z, k)` of the honest session with password `pw`, client secret
    the logarithm of the unmasked `X*`, and server secret `unmask pw z`. -/
theorem dhpake_extract_hashInput [DecidableEq W] (P : DHPAKE S W Pw) (unmask : Pw → S → S)
    (hunmask : ∀ pw z, msgS P pw (unmask pw z) = P.pubEquiv z)
    (hcomm : ∀ x y, P.dh y (P.pubEquiv x) = P.dh x (P.pubEquiv y)) {z : S} {cands : List Pw}
    {peer k : W} {pw : Pw} (h : (dhpakeKit P unmask hunmask).extract z cands peer k = some pw) :
    hashInput P pw (P.pubEquiv.symm ((P.maskC pw).symm peer)) (unmask pw z) =
      (pw, peer, P.pubEquiv z, k) := by
  obtain ⟨-, -, -, hkey⟩ := (dhpakeKit P unmask hunmask).extract_sound h
  simp only [dhpakeKit] at hkey
  simp only [hashInput, msgC, Equiv.apply_symm_apply, hunmask, Prod.mk.injEq, true_and]
  rw [← hcomm, Equiv.apply_symm_apply, hkey]

variable [Field S] (G : DHGroup S W)

/-- The SPAKE2 mask `Y ↦ Y · g^{t · e}` for the logarithm `t` of the mask base and the
    password encoding `e`, written in exponent form. -/
def spake2Mask (t e : S) : W ≃ W :=
  (G.pub.symm.trans (Equiv.addRight (t * e))).trans G.pub

/-- **SPAKE2** over `G`: the masks `M^pw = g^{m · enc pw}` and `N^pw = g^{n · enc pw}`, and
    `dh x Y = Y^x`. -/
def spake2 (enc : Pw → S) (m n : S) : DHPAKE S W Pw where
  pubEquiv := G.pub
  dh x Y := G.exp Y x
  maskC pw := spake2Mask G m (enc pw)
  maskS pw := spake2Mask G n (enc pw)

/-- The SPAKE2 trapdoor: the server of a party holding `pw` that sends `g^z` has secret
    `z - n · enc pw`. -/
def spake2Unmask (enc : Pw → S) (n : S) (pw : Pw) (z : S) : S := z - n * enc pw

/-- The SPAKE2 trapdoor sends the simulated message. -/
theorem spake2_msgS_unmask (enc : Pw → S) (m n : S) (pw : Pw) (z : S) :
    msgS (spake2 G enc m n) pw (spake2Unmask enc n pw z) = (spake2 G enc m n).pubEquiv z := by
  simp [msgS, spake2, spake2Mask, spake2Unmask]

/-- `dh` of SPAKE2 is symmetric on public values. -/
theorem spake2_dh_comm (enc : Pw → S) (m n x y : S) :
    (spake2 G enc m n).dh y ((spake2 G enc m n).pubEquiv x) =
      (spake2 G enc m n).dh x ((spake2 G enc m n).pubEquiv y) := by
  simp [spake2, G.exp_pub, mul_comm]

/-- **The SPAKE2 kit**: `dhpakeKit` with the trapdoor `spake2Unmask`. -/
def spake2Kit (enc : Pw → S) (m n : S) : DHExtractKit S W W Pw :=
  dhpakeKit (spake2 G enc m n) (spake2Unmask enc n) (spake2_msgS_unmask G enc m n)

end Masked

end CatCrypt.Crypto.PAKE.DHExtract
