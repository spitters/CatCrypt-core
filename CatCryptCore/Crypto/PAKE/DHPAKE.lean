/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.CDH
public import CatCryptCore.Crypto.OracleUpTo
public import CatCryptCore.Crypto.OracleBadDraw
public import CatCryptCore.Crypto.ExtractedOracle
public import CatCryptCore.Crypto.Signatures.EUFCMAPMF
public import CatCryptCore.Crypto.FiatShamirROM.Timed
public import CatCryptCore.Crypto.ROProgramming
public import CatCryptCore.Crypto.TVHops

/-!
# Diffie–Hellman PAKE in the random-oracle model: the generic bound

A Diffie–Hellman PAKE (the shape of SPAKE2, PAK and EKE): the client draws a secret `x`
and a message `X*` from its key generation `keyC pw`, the server draws `y` and `Y*` from
`keyS pw`, and the session key is `H(pw, X*, Y*, Z)` for the Diffie–Hellman value
`Z = dh x (g^y)`, with `H` a lazily sampled random oracle. A message is a sampled public
value: the group element `g^x` masked by a password-keyed bijection (`DHPAKE`, SPAKE2), a
uniform representative of `g^x` encrypted under the password (EKE over an encoding whose
inverse map is randomised), or `g^x` in clear.

The game `dhpakeGame` is a find-then-guess game in the style of Bellare–Pointcheval–
Rogaway: a bit `c` selects the real session key or a uniform key; the adversary sees the
transcript `(X*, Y*)` and the key, queries `H` at most `qH` times, and outputs a bit and
`qS` password guesses, one per session it attacks online. It succeeds when its bit is
`c` or one of its guesses is the password.

The statistical hypothesis is a message certificate `MsgCert` for each party: a
password-independent law `ν` and a bound `δ` on the total variation distance between the
law of the message under every password and `ν`. A share whose law does not depend on the
password contributes `0` (`MsgCert.clear`); a hidden share contributes the bound of the
`SamplerCert` of its encoding (`MsgCert.hidden` in `PAKE.DHPAKEHidden`).

For every adversary `D` (`sampled_success_le`),
`Pr[success] ≤ 1/2 + qS/|Pw| + qH · CDH_Advantage (cdhDef P) (cdhReduction P D) + δC + δS`.
The terms `qS/|Pw|` and `δC + δS` are information-theoretic; `cdhReduction P D` is an
explicit CDH adversary. For password-masked messages under bijections (`DHPAKE`) both
bounds are `0` and the statement is `dhpake_success_le`.

The proof: the game is identical, until `D` queries `H` at the honest input
`(pw, X*, Y*, Z)`, to a hybrid in which the key is uniform and independent of the oracle
(`OracleAdv.run_toOuterMeasure_le_add_flagOn`). In the hybrid the messages are replaced by
draws from the reference laws at a cost of `δC + δS`; then the view is independent of the
password, so the bit is guessed with probability `1/2` and a guess hits the password with
probability at most `qS/|Pw|`. The probability of the query is at most `qH` times the
success probability of the reduction. The reduction rerandomises the CDH challenge
`(g^a, g^b)`: the key generation is given with a rerandomiser `rerC pw` that maps a public
value `g^a` to an offset `r` and a message, such that the secret `shift r a` and the
message have the law of the key generation for uniform `a` (for a key generation that
rejects the points without a representative, `r` is found by trying `g^a · g^r`). The
reduction runs `D` on the rerandomised messages and maps the last component of a uniformly
chosen query back by `unblind`. The cost of programming the honest point is
`ROProgramming.run_update_le`.

## Main definitions

* `SampledDHPAKE` — the group (`pubEquiv : S ≃ G`, `dh`), the key generations of the
  parties and their rerandomisers
* `DHPAKE`, `DHPAKE.toSampled` — password masks that are bijections of the group
* `DHPAKEAdversary` — an adversary with `qH` oracle queries and `qS` password guesses
* `dhpakeGame` — the find-then-guess game
* `MsgCert`, `MsgCert.clear` — message certificates
* `cdhDef`, `cdhReduction` — the CDH group of `P` and the CDH adversary built from `D`
* `cdhReduction.timed` — the costed form of the reduction

## Main results

* `sampled_success_le` — the generic bound with the statistical terms of the certificates
* `dhpake_success_le` — the bound for bijective masks, without statistical terms
* `cdhReduction.run_erase_timed`, `cdhReduction.timeBound_timed` — the costed reduction
  erases to `cdhReduction` and runs in time `T + (tH + 1) · qH + tOut + tRer + 3`, with
  `tRer` the cost of the two rerandomisations

## References

* M. Bellare, D. Pointcheval, P. Rogaway, *Authenticated Key Exchange Secure against
  Dictionary Attacks*, EUROCRYPT 2000
* M. Abdalla, D. Pointcheval, *Simple Password-Based Encrypted Key Exchange Protocols*,
  CT-RSA 2005
* D. J. Bernstein, M. Hamburg, A. Krasnova, T. Lange, *Elligator: Elliptic-curve points
  indistinguishable from uniform random strings*, CCS 2013
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.DH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal
open CatCrypt.Crypto.ROProgramming
open PMF (indicator_le_mul_guess bind_apply_le_add_tsum tsum_le_mul_bind_apply
  bind_apply_le_of_le uniformFintype_map_equiv)

/-! ## The protocol and the game -/

/-- A Diffie–Hellman PAKE with sampled public values: secrets `S`, group elements `G` with
    `pubEquiv s = g^s` a bijection (a prime-order group), messages `W`, the Diffie–Hellman
    function `dh x Y = Y^x`, and the key generations `keyC pw`, `keyS pw` of the parties,
    each a law of a secret and a message. Each key generation comes with a rerandomiser:
    from a public value `g^a` it draws an offset `r` and a message such that, for uniform
    `a`, the secret `shift r a` and the message have the law of the key generation; and
    `unblind r t (g^a) (g^b)` maps the Diffie–Hellman value of the shifted secrets back to
    `dh a (g^b)`. -/
structure SampledDHPAKE (S G W Pw : Type) [Fintype S] [Nonempty S] where
  /-- The public value of a secret, `s ↦ g^s`. -/
  pubEquiv : S ≃ G
  /-- The Diffie–Hellman function, `dh x Y = Y^x`. -/
  dh : S → G → G
  /-- The client's key generation: a secret and its message. -/
  keyC : Pw → PMF (S × W)
  /-- The server's key generation: a secret and its message. -/
  keyS : Pw → PMF (S × W)
  /-- The offsets of the rerandomisers. -/
  R : Type
  /-- The client's rerandomiser: an offset and a message from a public value. -/
  rerC : Pw → G → PMF (R × W)
  /-- The server's rerandomiser: an offset and a message from a public value. -/
  rerS : Pw → G → PMF (R × W)
  /-- The secret of a rerandomised public value, `(r, a) ↦ a + r`. -/
  shift : R → S → S
  /-- The Diffie–Hellman value of the original public values from that of the shifted ones. -/
  unblind : R → R → G → G → G → G
  /-- The client's rerandomiser of a uniform public value has the law of its key generation. -/
  keyC_eq : ∀ pw, ((PMF.uniformFintype S).bind fun a =>
    (rerC pw (pubEquiv a)).map fun c => (shift c.1 a, c.2)) = keyC pw
  /-- The server's rerandomiser of a uniform public value has the law of its key generation. -/
  keyS_eq : ∀ pw, ((PMF.uniformFintype S).bind fun b =>
    (rerS pw (pubEquiv b)).map fun c => (shift c.1 b, c.2)) = keyS pw
  /-- Unblinding the Diffie–Hellman value of the shifted secrets. -/
  unblind_dh : ∀ r t a b, unblind r t (pubEquiv a) (pubEquiv b)
    (dh (shift r a) (pubEquiv (shift t b))) = dh a (pubEquiv b)

/-- An adversary against a Diffie–Hellman PAKE with messages `W` and group `G`: on the
    transcript `(X*, Y*)` and a session key it queries the key hash
    `H : Pw × W × W × G → K` adaptively, at most `qH` times on every path, and outputs a
    bit and `qS` password guesses. -/
structure DHPAKEAdversary (Pw W K : Type) (qH qS : ℕ) (G : Type := W) where
  /-- The interaction with the random oracle. -/
  run : W → W → K → OracleAdv (Pw × W × W × G) K (Bool × (Fin qS → Pw))
  /-- At most `qH` queries on every path. -/
  isQueryBound : ∀ X Y k, (run X Y k).IsQueryBound qH

variable {S G W Pw K : Type} [Fintype S] [Nonempty S] [SampleableType G]
  [Fintype Pw] [Nonempty Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] {qH qS : ℕ}

section Sampled

variable [DecidableEq W]

/-- The success predicate: the bit equals `c` or a guess equals the password. -/
def success (c : Bool) (pw : Pw) (o : Bool × (Fin qS → Pw)) : Bool :=
  (o.1 == c) || decide (∃ i, o.2 i = pw)

/-- The input of the key hash in a session with password `pw` and key pairs `xm`, `ym`:
    `(pw, X*, Y*, g^{xy})`. -/
def sessionInput (P : SampledDHPAKE S G W Pw) (pw : Pw) (xm ym : S × W) : Pw × W × W × G :=
  (pw, xm.2, ym.2, P.dh xm.1 (P.pubEquiv ym.1))

/-- **The find-then-guess game.** Sample the bit `c`, the password and the key pairs of
    the parties; the real key is the answer of the lazily sampled oracle at the honest
    input; the adversary receives the real key if `c` holds and a uniform key otherwise,
    and runs against the same oracle. -/
noncomputable def dhpakeGame (P : SampledDHPAKE S G W Pw) (D : DHPAKEAdversary Pw W K qH qS G) :
    PMF Bool :=
  (PMF.uniformFintype Bool).bind fun c => (PMF.uniformFintype Pw).bind fun pw =>
  (P.keyC pw).bind fun xm => (P.keyS pw).bind fun ym =>
    (roOracle emptyTable (sessionInput P pw xm ym)).bind fun kt =>
    (if c then PMF.pure kt.1 else PMF.uniformFintype K).bind fun k =>
      (OracleAdv.run roOracle (D.run xm.2 ym.2 k) kt.2).map fun z => success c pw z.1

/-- The hybrid game: a uniform key and a fresh oracle. -/
noncomputable def dhpakeHybrid (P : SampledDHPAKE S G W Pw)
    (D : DHPAKEAdversary Pw W K qH qS G) : PMF Bool :=
  (PMF.uniformFintype Bool).bind fun c => (PMF.uniformFintype Pw).bind fun pw =>
  (P.keyC pw).bind fun xm => (P.keyS pw).bind fun ym =>
  (PMF.uniformFintype K).bind fun k =>
    (OracleAdv.run roOracle (D.run xm.2 ym.2 k) emptyTable).map fun z => success c pw z.1

/-- The reference game: the hybrid game with the messages drawn from the laws `νC`, `νS`,
    which do not depend on the password. -/
noncomputable def dhpakeRef (νC νS : PMF W) (D : DHPAKEAdversary Pw W K qH qS G) : PMF Bool :=
  (PMF.uniformFintype Bool).bind fun c => (PMF.uniformFintype Pw).bind fun pw =>
  νC.bind fun X => νS.bind fun Y => (PMF.uniformFintype K).bind fun k =>
    (OracleAdv.run roOracle (D.run X Y k) emptyTable).map fun z => success c pw z.1

/-- The probability that the adversary queries the honest input in the hybrid game. -/
noncomputable def dhpakeQueryProb (P : SampledDHPAKE S G W Pw)
    (D : DHPAKEAdversary Pw W K qH qS G) : ℝ≥0∞ :=
  ∑' pw, PMF.uniformFintype Pw pw * ∑' xm, P.keyC pw xm * ∑' ym, P.keyS pw ym *
  ∑' k, PMF.uniformFintype K k * queryProb (sessionInput P pw xm ym) (D.run xm.2 ym.2 k)

/-! ## Message certificates -/

/-- A certificate for the messages of a key generation `key`: a law `ν` that does not
    depend on the password and a bound `δ` on the total variation distance between the
    law of the message under every password and `ν`. -/
structure MsgCert (key : Pw → PMF (S × W)) where
  /-- The reference law of the message. -/
  ν : PMF W
  /-- The bound. -/
  δ : ℝ≥0∞
  /-- The law of the message under every password is within `δ` of `ν`. -/
  tv_le : ∀ pw, tvDist (((key pw).map Prod.snd).map some) (ν.map some) ≤ δ

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype Pw] [Nonempty Pw] [DecidableEq Pw] in
/-- **A share in clear**: a message law `m` that does not depend on the password has the
    certificate `(m, 0)`. -/
noncomputable def MsgCert.clear (key : Pw → PMF (S × W)) (m : PMF W)
    (h : ∀ pw, (key pw).map Prod.snd = m) : MsgCert key where
  ν := m
  δ := 0
  tv_le pw := by rw [h pw, tvDist_self]

/-! ## The CDH reduction -/

/-- The CDH group of `P` as a core `DDHDef`: key generation samples `s` and publishes
    `g^s` as both components, and `ecdh (g^s) Y = dh s Y`. -/
noncomputable def cdhDef (P : SampledDHPAKE S G W Pw) : DDHDef G where
  ecdh priv pub := P.dh (P.pubEquiv.symm priv) pub
  keygen := liftPMF ((PMF.uniformFintype S).map fun s => (P.pubEquiv s, P.pubEquiv s))
  keygen_isPure := liftPMF_isPure _

/-- The rerandomisation of the CDH challenge `(gA, gB)`: a uniform password and the offsets
    and messages of both rerandomisers. -/
noncomputable def rerDist (P : SampledDHPAKE S G W Pw) (gA gB : G) :
    PMF (Pw × (P.R × W) × (P.R × W)) :=
  (PMF.uniformFintype Pw).bind fun pw => (P.rerC pw gA).bind fun c =>
    (P.rerS pw gB).map fun s => (pw, c, s)

/-- The output distribution of the reduction on the challenge `(gA, gB)`: rerandomise the
    challenge (`rerDist`), draw a uniform key, run `D` on the two messages against a lazily
    sampled oracle with a query log, and unblind the last component of the query at a
    uniform position of the log. -/
noncomputable def cdhDist (P : SampledDHPAKE S G W Pw) (D : DHPAKEAdversary Pw W K qH qS G)
    (gA gB : G) : PMF G :=
  (rerDist P gA gB).bind fun v => (PMF.uniformFintype K).bind fun k =>
    (OracleAdv.run (OracleAdv.withLog roOracle) (D.run v.2.1.2 v.2.2.2 k) (emptyTable, [])).bind
      fun z => (PMF.uniformFintype (Fin (max qH 1))).map fun i : Fin (max qH 1) =>
        P.unblind v.2.1.1 v.2.2.1 gA gB (z.2.2.getD (i : ℕ) (v.1, v.2.1.2, v.2.2.2, gA)).2.2.2

/-- **The CDH reduction.** On the challenge `(gA, gB)` it samples from `cdhDist`. -/
noncomputable def cdhReduction (P : SampledDHPAKE S G W Pw)
    (D : DHPAKEAdversary Pw W K qH qS G) : CDH_Adversary G :=
  fun gA gB => liftPMF (cdhDist P D gA gB)

/-- The CDH advantage of `cdhReduction P D` as a probability over the secrets. -/
theorem cdhAdvantage_cdhReduction (P : SampledDHPAKE S G W Pw)
    (D : DHPAKEAdversary Pw W K qH qS G) :
    CDH_Advantage (cdhDef P) (cdhReduction P D) =
      ((PMF.uniformFintype S).bind fun a => (PMF.uniformFintype S).bind fun b =>
        (cdhDist P D (P.pubEquiv a) (P.pubEquiv b)).map
          fun c => decide (c = P.dh a (P.pubEquiv b))) true := by
  unfold CDH_Advantage
  rw [← prTrue_liftPMF _ Heap.empty]
  congr 1
  funext h
  unfold CDH_Game
  simp only [SPComp.monad_bind_eq, cdhDef, cdhReduction]
  rw [liftPMF_bind_apply, PMF.bind_map]
  conv_rhs => unfold liftPMF
  rw [PMF.map_bind]
  refine congrArg _ (funext fun a => ?_)
  simp only [Function.comp_apply]
  rw [liftPMF_bind_apply, PMF.bind_map, PMF.map_bind]
  refine congrArg _ (funext fun b => ?_)
  simp only [Function.comp_apply]
  rw [liftPMF_bind_apply, PMF.map_comp]
  simp only [SPComp.pure, SDistr.pure, Equiv.symm_apply_apply]
  rw [← PMF.bind_pure_comp]
  rfl

/-! ## The bound -/

/-- **Identical until the honest input is queried.** -/
theorem dhpakeGame_le_hybrid (P : SampledDHPAKE S G W Pw) (D : DHPAKEAdversary Pw W K qH qS G) :
    dhpakeGame P D true ≤ dhpakeHybrid P D true + dhpakeQueryProb P D := by
  unfold dhpakeGame dhpakeHybrid
  rw [show dhpakeQueryProb P D = ∑' c : Bool, PMF.uniformFintype Bool c * dhpakeQueryProb P D
    by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]]
  refine bind_apply_le_add_tsum _ _ _ _ _ fun c => ?_
  · unfold dhpakeQueryProb
    refine bind_apply_le_add_tsum _ _ _ _ _ fun pw => ?_
    refine bind_apply_le_add_tsum _ _ _ _ _ fun xm => ?_
    refine bind_apply_le_add_tsum _ _ _ _ _ fun ym => ?_
    rw [Extracted.roOracle_emptyTable_eq, PMF.bind_map]
    cases c
    · simp only [Function.comp_def, Bool.false_eq_true, ite_false]
      refine bind_apply_le_of_le _ _ _ _ fun y0 => ?_
      exact bind_apply_le_add_tsum _ _ _ _ _ fun k => run_update_le _ y0 _ _
    · simp only [Function.comp_def, ite_true, PMF.pure_bind]
      exact bind_apply_le_add_tsum _ _ _ _ _ fun k => run_update_le _ k _ _

/-- **The messages replaced by the reference laws.** The hybrid game is within the bounds of
    the message certificates of the reference game. -/
theorem dhpakeHybrid_le_ref (P : SampledDHPAKE S G W Pw) (cC : MsgCert P.keyC)
    (cS : MsgCert P.keyS) (D : DHPAKEAdversary Pw W K qH qS G) :
    dhpakeHybrid P D true ≤ dhpakeRef cC.ν cS.ν D true + (cC.δ + cS.δ) := by
  have hc : ∀ {α : Type} (p : PMF α), cC.δ + cS.δ = ∑' a, p a * (cC.δ + cS.δ) := fun p => by
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  unfold dhpakeHybrid dhpakeRef
  rw [hc (PMF.uniformFintype Bool)]
  refine bind_apply_le_add_tsum _ _ _ _ _ fun c => ?_
  rw [hc (PMF.uniformFintype Pw)]
  refine bind_apply_le_add_tsum _ _ _ _ _ fun pw => ?_
  have hS : ∀ X : W, (((P.keyS pw).map Prod.snd).bind fun Y => (PMF.uniformFintype K).bind
      fun k => (OracleAdv.run roOracle (D.run X Y k) emptyTable).map fun z => success c pw z.1)
      true ≤ (cS.ν.bind fun Y => (PMF.uniformFintype K).bind fun k =>
        (OracleAdv.run roOracle (D.run X Y k) emptyTable).map fun z => success c pw z.1) true +
        cS.δ := fun X =>
    (bind_apply_le_add_tvDist _ _ _ _).trans (add_le_add le_rfl (cS.tv_le pw))
  have h1 := (bind_apply_le_add_tvDist ((P.keyC pw).map Prod.snd) cC.ν (fun X =>
    ((P.keyS pw).map Prod.snd).bind fun Y => (PMF.uniformFintype K).bind fun k =>
      (OracleAdv.run roOracle (D.run X Y k) emptyTable).map fun z => success c pw z.1)
      true).trans (add_le_add le_rfl (cC.tv_le pw))
  have h2 := bind_apply_le_add_tsum cC.ν _ _ (fun _ => cS.δ) true fun X => hS X
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul] at h2
  simp only [PMF.bind_map, Function.comp_def] at h1 h2
  calc _ ≤ _ := h1
    _ ≤ _ := add_le_add h2 le_rfl
    _ = _ := by ring

/-- For a fixed output `o`, a uniform bit and a uniform password make `o` succeed with
    probability at most `1/2 + qS/|Pw|`. -/
theorem success_prob_le (o : Bool × (Fin qS → Pw)) :
    ((PMF.uniformFintype Bool).bind fun c => (PMF.uniformFintype Pw).bind fun pw =>
      PMF.pure (success c pw o)) true ≤ 2⁻¹ + qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ := by
  have hsplit : ((PMF.uniformFintype Bool).bind fun c => (PMF.uniformFintype Pw).bind
      fun pw => PMF.pure (success c pw o)) true ≤
      ((PMF.uniformFintype Bool).bind fun c => PMF.pure (o.1 == c)) true +
        ((PMF.uniformFintype Pw).bind fun pw => PMF.pure (decide (∃ i, o.2 i = pw))) true := by
    set G := ((PMF.uniformFintype Pw).bind fun pw => PMF.pure (decide (∃ i, o.2 i = pw))) true
    have hc : ∀ c : Bool, ((PMF.uniformFintype Pw).bind fun pw =>
        PMF.pure (success c pw o)) true ≤ PMF.pure (o.1 == c) true + G := by
      intro c
      have h := bind_apply_le_add_tsum (PMF.uniformFintype Pw)
        (fun pw => PMF.pure (success c pw o)) (fun _ => PMF.pure (o.1 == c))
        (fun pw => PMF.pure (decide (∃ i, o.2 i = pw)) true) true fun pw => by
          unfold success
          cases (o.1 == c) <;> cases (decide (∃ i, o.2 i = pw)) <;> simp
      rwa [PMF.bind_const, ← PMF.bind_apply] at h
    have h := bind_apply_le_add_tsum (PMF.uniformFintype Bool) _
      (fun c => PMF.pure (o.1 == c)) (fun _ => G) true hc
    rwa [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul] at h
  have hbit : ((PMF.uniformFintype Bool).bind fun c => PMF.pure (o.1 == c)) true = 2⁻¹ := by
    simp [PMF.bind_apply, tsum_fintype, PMF.pure_apply]
  have hguess : ((PMF.uniformFintype Pw).bind fun pw => PMF.pure (decide (∃ i, o.2 i = pw)))
      true ≤ qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ := by
    rw [PMF.bind_apply, tsum_fintype]
    calc ∑ pw, PMF.uniformFintype Pw pw * PMF.pure (decide (∃ i, o.2 i = pw)) true
        ≤ ∑ pw, ∑ i : Fin qS, PMF.uniformFintype Pw pw *
            (if o.2 i = pw then (1 : ℝ≥0∞) else 0) := by
          refine Finset.sum_le_sum fun pw _ => ?_
          rw [← Finset.mul_sum]
          gcongr
          by_cases h : ∃ i, o.2 i = pw
          · obtain ⟨i, hi⟩ := h
            have hle := Finset.single_le_sum (f := fun j : Fin qS =>
              if o.2 j = pw then (1 : ℝ≥0∞) else 0) (fun _ _ => by positivity) (Finset.mem_univ i)
            have h1 : PMF.pure (decide (∃ i, o.2 i = pw)) true = 1 := by
              simp only [PMF.pure_apply]
              rw [ite_eq_left (by rw [eq_comm, decide_eq_true_eq]; exact ⟨i, hi⟩)]
            rw [h1]
            refine le_trans (le_of_eq ?_) hle
            simp [hi]
          · simp [h, PMF.pure_apply]
      _ = ∑ i : Fin qS, (Fintype.card Pw : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [PMF.uniformFintype_apply]
      _ = qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ := by simp
  exact hsplit.trans (by rw [hbit]; gcongr)

omit [Fintype S] [Nonempty S] in
/-- **The reference game.** With messages drawn from laws that do not depend on the
    password, the bit is guessed with probability `1/2` and one of `qS` guesses hits the
    password with probability at most `qS/|Pw|`. -/
theorem dhpakeRef_le (νC νS : PMF W) (D : DHPAKEAdversary Pw W K qH qS G) :
    dhpakeRef νC νS D true ≤ 2⁻¹ + qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ := by
  set view := νC.bind fun X => νS.bind fun Y => (PMF.uniformFintype K).bind fun k =>
      (OracleAdv.run roOracle (D.run X Y k) emptyTable).map Prod.fst with hview
  have heq : dhpakeRef νC νS D = view.bind fun o => (PMF.uniformFintype Bool).bind fun c =>
      (PMF.uniformFintype Pw).bind fun pw => PMF.pure (success c pw o) := by
    rw [PMF.bind_comm view (PMF.uniformFintype Bool)]
    unfold dhpakeRef
    refine congrArg _ (funext fun c => ?_)
    rw [PMF.bind_comm view (PMF.uniformFintype Pw)]
    refine congrArg _ (funext fun pw => ?_)
    rw [hview]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
    rfl
  rw [heq]
  exact bind_apply_le_of_le _ _ _ _ success_prob_le

/-- Two sums of weighted sums in the other order. -/
private theorem tsum_mul_tsum_mul_comm {α β : Type} (p : α → ℝ≥0∞) (q : β → ℝ≥0∞)
    (F : α → β → ℝ≥0∞) :
    ∑' x, p x * ∑' y, q y * F x y = ∑' y, q y * ∑' x, p x * F x y := by
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun y => tsum_congr fun x => mul_left_comm _ _ _

omit [DecidableEq W] in
/-- An expectation over a key generation is the expectation over the rerandomisation of a
    uniform public value. -/
private theorem tsum_key_mul (key : PMF (S × W)) {R : Type} (rer : S → PMF (R × W))
    (shift : R → S → S)
    (h : ((PMF.uniformFintype S).bind fun a => (rer a).map fun c => (shift c.1 a, c.2)) = key)
    (F : S × W → ℝ≥0∞) :
    ∑' xm, key xm * F xm =
      ∑' a, PMF.uniformFintype S a * ∑' c, rer a c * F (shift c.1 a, c.2) := by
  rw [← h, PMF.tsum_bind_mul]
  exact tsum_congr fun a => congrArg _ (PMF.tsum_mul_comp_eq_map _ _ _).symm

/-- The query probability is at most `qH` times the CDH advantage of the reduction. -/
theorem dhpakeQueryProb_le (P : SampledDHPAKE S G W Pw) (D : DHPAKEAdversary Pw W K qH qS G) :
    dhpakeQueryProb P D ≤ qH * CDH_Advantage (cdhDef P) (cdhReduction P D) := by
  rw [cdhAdvantage_cdhReduction]
  unfold dhpakeQueryProb
  simp only [tsum_key_mul _ _ _ (P.keyC_eq _), tsum_key_mul _ _ _ (P.keyS_eq _)]
  refine (tsum_mul_tsum_mul_comm _ _ _).trans_le ?_
  refine tsum_le_mul_bind_apply _ _ _ _ _ fun a _ => ?_
  conv_lhs => enter [1, pw, 2]; rw [tsum_mul_tsum_mul_comm]
  refine (tsum_mul_tsum_mul_comm _ _ _).trans_le ?_
  refine tsum_le_mul_bind_apply _ _ _ _ _ fun b _ => ?_
  simp only [cdhDist, rerDist, PMF.map_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine tsum_le_mul_bind_apply _ _ _ _ _ fun pw _ => ?_
  refine tsum_le_mul_bind_apply _ _ _ _ _ fun c _ => ?_
  refine tsum_le_mul_bind_apply _ _ _ _ _ fun s _ => ?_
  refine tsum_le_mul_bind_apply _ _ _ _ _ fun k _ => ?_
  rw [queryProb_eq_log]
  refine tsum_le_mul_bind_apply _ _ _ _ _ fun z hz => ?_
  have hlen : z.2.2.length ≤ qH := by
    simpa using OracleAdv.sum_cost_log_le_of_mem_support roOracle (fun _ => 1) _ qH
      ((D.isQueryBound _ _ _).isQueryBoundBy_one) emptyTable [] z
      ((PMF.mem_support_iff _ _).mpr hz)
  rw [PMF.map_comp]
  exact indicator_le_mul_guess z.2.2 _ _ hlen
    (fun d => decide (P.unblind c.1 s.1 (P.pubEquiv a) (P.pubEquiv b) d.2.2.2 =
      P.dh a (P.pubEquiv b))) (by simp [sessionInput, P.unblind_dh])

/-- **The generic bound for a Diffie–Hellman PAKE with sampled public values.** For every
    adversary `D` asking at most `qH` queries of the key hash and making `qS` online
    password guesses, and message certificates `cC`, `cS` of the key generations, the
    success probability in the find-then-guess game is at most
    `1/2 + qS/|Pw| + qH · CDH_Advantage (cdhDef P) (cdhReduction P D) + cC.δ + cS.δ`. -/
theorem sampled_success_le (P : SampledDHPAKE S G W Pw) (cC : MsgCert P.keyC)
    (cS : MsgCert P.keyS) (D : DHPAKEAdversary Pw W K qH qS G) :
    dhpakeGame P D true ≤ 2⁻¹ + qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ +
      qH * CDH_Advantage (cdhDef P) (cdhReduction P D) + (cC.δ + cS.δ) :=
  calc dhpakeGame P D true ≤ dhpakeHybrid P D true + dhpakeQueryProb P D :=
        dhpakeGame_le_hybrid P D
    _ ≤ (2⁻¹ + qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ + (cC.δ + cS.δ)) +
          qH * CDH_Advantage (cdhDef P) (cdhReduction P D) :=
        add_le_add ((dhpakeHybrid_le_ref P cC cS D).trans
          (by gcongr; exact dhpakeRef_le _ _ D)) (dhpakeQueryProb_le P D)
    _ = _ := by ring

/-! ## Password masks that are bijections -/

/-- A Diffie–Hellman PAKE with password-masked messages: secrets `S`, group elements `W`
    with `pubEquiv s = g^s` a bijection (a prime-order group), the Diffie–Hellman function
    `dh x Y = Y^x`, and for every password the client and server masks, bijections of the
    group (`X ↦ X · M^pw` and `Y ↦ Y · N^pw` in SPAKE2). -/
structure DHPAKE (S W Pw : Type) where
  /-- The public value of a secret, `s ↦ g^s`. -/
  pubEquiv : S ≃ W
  /-- The Diffie–Hellman function, `dh x Y = Y^x`. -/
  dh : S → W → W
  /-- The client's password mask. -/
  maskC : Pw → W ≃ W
  /-- The server's password mask. -/
  maskS : Pw → W ≃ W

/-- The client's message `maskC pw (g^x)`. -/
def msgC (P : DHPAKE S W Pw) (pw : Pw) (x : S) : W := P.maskC pw (P.pubEquiv x)

/-- The server's message `maskS pw (g^y)`. -/
def msgS (P : DHPAKE S W Pw) (pw : Pw) (y : S) : W := P.maskS pw (P.pubEquiv y)

/-- The input of the key hash in an honest session: `(pw, X*, Y*, g^{xy})`. -/
def hashInput (P : DHPAKE S W Pw) (pw : Pw) (x y : S) : Pw × W × W × W :=
  (pw, msgC P pw x, msgS P pw y, P.dh x (P.pubEquiv y))

/-- The masked protocol as a protocol with sampled public values: uniform secrets, the
    masked public values as messages, and the rerandomisers that mask the challenge
    itself (offsets in `PUnit`, `shift` and `unblind` the identities). -/
noncomputable def DHPAKE.toSampled (P : DHPAKE S W Pw) : SampledDHPAKE S W W Pw where
  pubEquiv := P.pubEquiv
  dh := P.dh
  keyC pw := (PMF.uniformFintype S).map fun x => (x, msgC P pw x)
  keyS pw := (PMF.uniformFintype S).map fun y => (y, msgS P pw y)
  R := PUnit
  rerC pw X := PMF.pure (PUnit.unit, P.maskC pw X)
  rerS pw Y := PMF.pure (PUnit.unit, P.maskS pw Y)
  shift _ a := a
  unblind _ _ _ _ Z := Z
  keyC_eq _ := by simp only [PMF.pure_map]; rfl
  keyS_eq _ := by simp only [PMF.pure_map]; rfl
  unblind_dh _ _ _ _ := rfl

end Sampled

section Bijective

variable [SampleableType W]

/-- The client's messages of a masked protocol are uniform under every password. -/
noncomputable def DHPAKE.msgCertC (P : DHPAKE S W Pw) : MsgCert P.toSampled.keyC :=
  MsgCert.clear _ (PMF.uniformFintype W) fun pw => by
    rw [DHPAKE.toSampled, PMF.map_comp]
    exact uniformFintype_map_equiv (P.pubEquiv.trans (P.maskC pw))

/-- The server's messages of a masked protocol are uniform under every password. -/
noncomputable def DHPAKE.msgCertS (P : DHPAKE S W Pw) : MsgCert P.toSampled.keyS :=
  MsgCert.clear _ (PMF.uniformFintype W) fun pw => by
    rw [DHPAKE.toSampled, PMF.map_comp]
    exact uniformFintype_map_equiv (P.pubEquiv.trans (P.maskS pw))

/-- **The generic bound for a Diffie–Hellman PAKE with bijective masks.** For every
    adversary `D` asking at most `qH` queries of the key hash and making `qS` online
    password guesses, the success probability in the find-then-guess game is at most
    `1/2 + qS/|Pw| + qH · CDH_Advantage (cdhDef P) (cdhReduction P D)`: the bound of
    `sampled_success_le` with both message certificates at `0`. -/
theorem dhpake_success_le (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS) :
    dhpakeGame P.toSampled D true ≤ 2⁻¹ + qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ +
      qH * CDH_Advantage (cdhDef P.toSampled) (cdhReduction P.toSampled D) := by
  have h := sampled_success_le P.toSampled P.msgCertC P.msgCertS D
  have h0 : P.msgCertC.δ + P.msgCertS.δ = 0 := by
    simp [DHPAKE.msgCertC, DHPAKE.msgCertS, MsgCert.clear]
  rwa [h0, add_zero] at h

end Bijective

/-! ## The costed reduction -/

variable [DecidableEq W]

variable (qH) in
/-- The costed run of the reduction after the rerandomisation `v` and the key `k`: the
    costed adversary `D'` against the logged lazily sampled oracle, each query at step cost
    `tH`, then the uniform index into the log and the unblinded output, at step cost
    `tOut`. -/
noncomputable def cdhReduction.timedRun (P : SampledDHPAKE S G W Pw) (tH tOut : ℕ)
    (D' : W → W → K → OracleAdv.Timed (Pw × W × W × G) K (Bool × (Fin qS → Pw)))
    (gA gB : G) (v : Pw × (P.R × W) × (P.R × W)) (k : K) :
    ℕ × OracleAdv.Timed Empty Empty G :=
  OracleAdv.Timed.stepBind
    (OracleAdv.Timed.runOracle (OracleAdv.withLog roOracle) (fun _ => tH)
      (D' v.2.1.2 v.2.2.2 k) (emptyTable, []))
    fun z => (0, .rand (PMF.uniformFintype (Fin (max qH 1))) (fun _ => tOut)
      fun i => .ret (P.unblind v.2.1.1 v.2.2.1 gA gB
        (z.2.2.getD (i : ℕ) (v.1, v.2.1.2, v.2.2.2, gA)).2.2.2))

variable (qH) in
/-- **The costed CDH reduction.** On the challenge `(gA, gB)`: rerandomise it (one node of
    step cost `tRer`, the password and both rerandomisers), sample the key (one node), then
    `cdhReduction.timedRun`. -/
noncomputable def cdhReduction.timed (P : SampledDHPAKE S G W Pw) (tRer tH tOut : ℕ)
    (D' : W → W → K → OracleAdv.Timed (Pw × W × W × G) K (Bool × (Fin qS → Pw)))
    (gA gB : G) : ℕ × OracleAdv.Timed Empty Empty G :=
  (0, .rand (rerDist P gA gB) (fun _ => tRer) fun v =>
    .rand (PMF.uniformFintype K)
      (fun k => (cdhReduction.timedRun qH P tH tOut D' gA gB v k).1)
      fun k => (cdhReduction.timedRun qH P tH tOut D' gA gB v k).2)

/-- Under any oracle, the erased costed reduction has the output distribution
    `cdhDist P D gA gB` of `cdhReduction P D`, for a costed adversary `D'` whose erasure
    is `D.run`. -/
theorem cdhReduction.run_erase_timed (P : SampledDHPAKE S G W Pw)
    (D : DHPAKEAdversary Pw W K qH qS G)
    (D' : W → W → K → OracleAdv.Timed (Pw × W × W × G) K (Bool × (Fin qS → Pw)))
    (hD : ∀ X Y k, (D' X Y k).erase = D.run X Y k) (tRer tH tOut : ℕ)
    {U : Type} (O' : U → Empty → PMF (Empty × U)) (u : U) (gA gB : G) :
    (OracleAdv.run O' (cdhReduction.timed qH P tRer tH tOut D' gA gB).2.erase u).map
      Prod.fst = cdhDist P D gA gB := by
  simp only [cdhReduction.timed, OracleAdv.Timed.erase, OracleAdv.run_rand, PMF.map_bind,
    cdhDist]
  refine congrArg _ (funext fun v => congrArg _ (funext fun k => ?_))
  rw [cdhReduction.timedRun, OracleAdv.Timed.erase_stepBind,
    OracleAdv.run_bind_map_fst_empty, OracleAdv.Timed.run_erase_runOracle, hD]
  refine congrArg _ (funext fun z => ?_)
  simp only [OracleAdv.Timed.erase, OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind,
    PMF.pure_map]
  rfl

/-- **Time of the CDH reduction.** With the costed adversary `D'` of time `T` on every
    input and erasure `D.run` (at most `qH` queries), the costed reduction has time at
    most `T + (tH + 1) * qH + tOut + tRer + 3`: the rerandomisation at step cost `tRer`,
    the key node, the adversary with each query charged its step `tH` and its oracle node,
    and the uniform index with the output. -/
theorem cdhReduction.timeBound_timed (P : SampledDHPAKE S G W Pw)
    (D : DHPAKEAdversary Pw W K qH qS G)
    (D' : W → W → K → OracleAdv.Timed (Pw × W × W × G) K (Bool × (Fin qS → Pw)))
    (hD : ∀ X Y k, (D' X Y k).erase = D.run X Y k) (tRer tH tOut : ℕ)
    {T : ℕ} (hT : ∀ X Y k, (D' X Y k).TimeBound T) (gA gB : G) :
    OracleAdv.Timed.StepTimeBound (cdhReduction.timed qH P tRer tH tOut D' gA gB)
      (T + (tH + 1) * qH + tOut + tRer + 3) := by
  have hR : ∀ v k, OracleAdv.Timed.StepTimeBound
      (cdhReduction.timedRun qH P tH tOut D' gA gB v k) (T + (tH + 1) * qH + (1 + tOut)) := by
    intro v k
    have hq : (D' v.2.1.2 v.2.2.2 k).erase.IsQueryBoundBy
        (fun _ => tH + 1) ((tH + 1) * qH) := by
      rw [hD]
      exact ((D.isQueryBound _ _ _).isQueryBoundBy_one.mul_left (tH + 1)).of_cost_le
        fun _ => by simp
    refine OracleAdv.Timed.timeBound_stepBind
      (OracleAdv.Timed.timeBound_runOracle _ _ (hT _ _ _) hq _) fun z => ?_
    refine ⟨Nat.zero_le _, (OracleAdv.Timed.timeBound_rand_iff _ _ _ _).2
      ⟨by omega, fun _ => ⟨by omega, trivial⟩⟩⟩
  simp only [cdhReduction.timed, OracleAdv.Timed.StepTimeBound,
    OracleAdv.Timed.timeBound_rand_iff]
  refine ⟨Nat.zero_le _, by omega, fun v => ⟨by omega, by omega, fun k => ?_⟩⟩
  have h := hR v k
  simp only [OracleAdv.Timed.StepTimeBound] at h
  exact ⟨by omega, h.2.mono (by omega)⟩

end CatCrypt.Crypto.PAKE.DH
