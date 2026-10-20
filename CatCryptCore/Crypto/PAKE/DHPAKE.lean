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

/-!
# Diffie–Hellman PAKE in the random-oracle model: the generic bound

A Diffie–Hellman PAKE with password-masked messages (the shape of SPAKE2, PAK and EKE
over a fixed encoding): the client sends `X* = maskC pw (g^x)`, the server sends
`Y* = maskS pw (g^y)`, and the session key is `H(pw, X*, Y*, Z)` for the Diffie–Hellman
value `Z = dh x (g^y)`, with `H` a lazily sampled random oracle. The masks are
bijections of the group for every password.

The game `dhpakeGame` is a find-then-guess game in the style of Bellare–Pointcheval–
Rogaway: a bit `c` selects the real session key or a uniform key; the adversary sees the
transcript `(X*, Y*)` and the key, queries `H` at most `qH` times, and outputs a bit and
`qS` password guesses, one per session it attacks online. It succeeds when its bit is
`c` or one of its guesses is the password.

For every adversary `D` (`dhpake_success_le`),
`Pr[success] ≤ 1/2 + qS/|Pw| + qH · CDH_Advantage (cdhDef P) (cdhReduction P D)`.
The online-guessing term `qS/|Pw|` is information-theoretic; `cdhReduction P D` is an
explicit CDH adversary.

The proof: the game is identical, until `D` queries `H` at the honest input
`(pw, X*, Y*, Z)`, to a hybrid in which the key is uniform and independent of the oracle
(`OracleAdv.run_toOuterMeasure_le_add_flagOn`). In the hybrid the transcript is uniform
whatever the password, so the bit is guessed with probability `1/2` and a guess hits the
password with probability at most `qS/|Pw|`. The probability of the query is at most
`qH` times the success probability of the reduction, which embeds a CDH challenge
`(g^a, g^b)` as the unmasked messages and returns the last component of a uniformly
chosen query.

## Main definitions

* `DHPAKE` — the group (`pubEquiv : S ≃ W`, `dh`) and the password masks
* `DHPAKEAdversary` — an adversary with `qH` oracle queries and `qS` password guesses
* `dhpakeGame` — the find-then-guess game
* `cdhDef`, `cdhReduction` — the CDH group of `P` and the CDH adversary built from `D`
* `cdhReduction.timed` — the costed form of the reduction

## Main results

* `run_update_le` — programming one point of the lazily sampled oracle costs at most the
  probability of querying it
* `dhpake_success_le` — the generic bound
* `cdhReduction.run_erase_timed`, `cdhReduction.timeBound_timed` — the costed reduction
  erases to `cdhReduction` and runs in time `T + (tH + 1) · qH + tOut + 4`

## References

* M. Bellare, D. Pointcheval, P. Rogaway, *Authenticated Key Exchange Secure against
  Dictionary Attacks*, EUROCRYPT 2000
* M. Abdalla, D. Pointcheval, *Simple Password-Based Encrypted Key Exchange Protocols*,
  CT-RSA 2005
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.DH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.Signatures (liftPMF liftPMF_bind_apply prTrue_liftPMF)
open scoped ENNReal

/-! ## Programming one point of the lazily sampled oracle -/

section Programmed

variable {X Y : Type} [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- The lazily sampled random oracle with the point `s` programmed to the value `y`. -/
noncomputable def progOracle (s : X) (y : Y) (T : X → Option Y) (d : X) :
    PMF (Y × (X → Option Y)) :=
  if d = s then PMF.pure (y, T) else roOracle T d

/-- Recording the programmed point in the table turns one call of `progOracle s y` into
    one call of the lazily sampled oracle. -/
theorem progOracle_map_update (s : X) (y : Y) (T : X → Option Y) (d : X) :
    (progOracle s y T d).map (Prod.map id fun T => Function.update T s (some y)) =
      roOracle (Function.update T s (some y)) d := by
  unfold progOracle
  split_ifs with hd
  · subst hd
    simp [roOracle, PMF.pure_map]
  · have hT : Function.update T s (some y) d = T d := Function.update_of_ne hd _ _
    unfold roOracle
    rw [hT]
    rcases T d with _ | h
    · simp only [PMF.map_comp]
      congr 1
      funext h
      simp [Function.update_comm hd]
    · simp [PMF.pure_map]

/-- The probability that a run of `A` against the lazily sampled oracle from the empty
    table queries the point `s`. -/
noncomputable def queryProb {α : Type} (s : X) (A : OracleAdv X Y α) : ℝ≥0∞ :=
  (OracleAdv.run (OracleAdv.flagOn (· = s) roOracle) A (emptyTable, false)).toOuterMeasure
    {z | z.2.2 = true}

theorem map_apply_eq_toOuterMeasure {α σ : Type} (p : PMF (α × σ)) (f : α → Bool) :
    (p.map fun z => f z.1) true = p.toOuterMeasure {z | z.1 ∈ {a | f a = true}} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

/-- **Programming one point costs at most the probability of querying it.** A run against
    the oracle whose table holds `s ↦ y` gives every output event at most its probability
    against the empty table plus the probability of querying `s`. -/
theorem run_update_le {α : Type} (s : X) (y : Y) (A : OracleAdv X Y α) (f : α → Bool) :
    ((OracleAdv.run roOracle A (Function.update emptyTable s (some y))).map fun z => f z.1)
        true ≤
      ((OracleAdv.run roOracle A emptyTable).map fun z => f z.1) true + queryProb s A := by
  have hagree : ∀ (T : X → Option Y) d, ¬ (d = s) → progOracle s y T d = roOracle T d :=
    fun T d hd => if_neg hd
  have hmap := OracleAdv.run_map_state (progOracle s y) roOracle
    (fun T => Function.update T s (some y)) (progOracle_map_update s y) A emptyTable
  rw [map_apply_eq_toOuterMeasure, map_apply_eq_toOuterMeasure, ← hmap,
    PMF.toOuterMeasure_map_apply]
  have h := OracleAdv.run_toOuterMeasure_le_add_flagOn (· = s) _ _ hagree A emptyTable
    {a | f a = true}
  exact h

/-- The query probability through the query log. -/
theorem queryProb_eq_log {α : Type} (s : X) (A : OracleAdv X Y α) :
    queryProb s A = ∑' z, OracleAdv.run (OracleAdv.withLog roOracle) A (emptyTable, []) z *
      (if ∃ d ∈ z.2.2, d = s then 1 else 0) := by
  classical
  unfold queryProb
  rw [OracleAdv.run_flagOn_eq_withLog, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
  refine tsum_congr fun z => ?_
  by_cases h : ∃ d ∈ z.2.2, d = s <;> simp [Set.indicator]

end Programmed

/-! ## Guessing a query and averaging -/

/-- `max q 1` is positive, so a uniform index below it is well defined. -/
instance maxOneNeZero (q : ℕ) : NeZero (max q 1) := ⟨by omega⟩

/-- A uniform position among `max q 1` hits the first occurrence of `s` in a list of at
    most `q` entries with probability `1/q`. -/
theorem indicator_le_mul_guess {X : Type} [DecidableEq X] {q : ℕ} (l : List X) (s dflt : X)
    (hl : l.length ≤ q) (f : X → Bool) (hf : f s = true) :
    (if ∃ d ∈ l, d = s then (1 : ℝ≥0∞) else 0) ≤
      q * ((PMF.uniformOfFintype (Fin (max q 1))).map
        fun i : Fin (max q 1) => f (l.getD (i : ℕ) dflt)) true := by
  split_ifs with h
  · obtain ⟨d, hd, rfl⟩ := h
    obtain ⟨j, hj, hjd⟩ := List.getElem_of_mem hd
    have hq : max q 1 = q := by omega
    have hjq : j < max q 1 := by omega
    have hterm : (PMF.uniformOfFintype (Fin (max q 1))) ⟨j, hjq⟩ ≤
        ((PMF.uniformOfFintype (Fin (max q 1))).map
          fun i : Fin (max q 1) => f (l.getD (i : ℕ) dflt)) true := by
      rw [PMF.map_apply]
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum ⟨j, hjq⟩)
      simp [List.getElem?_eq_getElem hj, hjd, hf]
    calc (1 : ℝ≥0∞) = q * (q : ℝ≥0∞)⁻¹ :=
          (ENNReal.mul_inv_cancel (by exact_mod_cast (show q ≠ 0 by omega))
            (ENNReal.natCast_ne_top q)).symm
      _ ≤ _ := by
          gcongr
          refine le_trans (le_of_eq ?_) hterm
          simp [PMF.uniformOfFintype_apply, hq]
  · positivity

theorem bind_apply_le_add_tsum {X β : Type} (μ : PMF X) (f g : X → PMF β) (h : X → ℝ≥0∞)
    (b : β) (hfg : ∀ x, f x b ≤ g x b + h x) :
    (μ.bind f) b ≤ (μ.bind g) b + ∑' x, μ x * h x := by
  rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun x => by rw [← mul_add]; gcongr; exact hfg x

theorem tsum_le_mul_bind_apply {X β : Type} (μ : PMF X) (h : X → ℝ≥0∞) (g : X → PMF β)
    (c : ℝ≥0∞) (b : β) (hg : ∀ x, μ x ≠ 0 → h x ≤ c * g x b) :
    ∑' x, μ x * h x ≤ c * (μ.bind g) b := by
  rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : μ x = 0
  · simp [hx]
  · rw [mul_left_comm]
    gcongr
    exact hg x hx

/-- A bind whose continuations all give `b` probability at most `C` gives it probability
    at most `C`. -/
theorem bind_apply_le_of_le {X β : Type} (μ : PMF X) (f : X → PMF β) (b : β) (C : ℝ≥0∞)
    (hf : ∀ x, f x b ≤ C) : (μ.bind f) b ≤ C := by
  rw [PMF.bind_apply]
  calc ∑' x, μ x * f x b ≤ ∑' x, μ x * C := ENNReal.tsum_le_tsum fun x => by gcongr; exact hf x
    _ = C := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The image of a uniform distribution under an equivalence is uniform. -/
theorem uniformOfFintype_map_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] (e : α ≃ β) : (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b) fun a ha => by
    rw [if_neg]; rintro rfl; exact ha (e.symm_apply_apply a).symm]
  simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]

/-- A probability mass function lifted to a computation is heap-independent. -/
theorem liftPMF_isPure {α : Type} (p : PMF α) : SPComp.IsPure (liftPMF p) := by
  refine ⟨p.map some, fun h => ?_⟩
  simp only [liftPMF, SDistr.bind, SDistr.pure, PMF.bind_map]
  rw [← PMF.bind_pure_comp]
  rfl

/-! ## The protocol and the game -/

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

/-- An adversary against `DHPAKE`: on the transcript `(X*, Y*)` and a session key it
    queries the key hash `H : Pw × W × W × W → K` adaptively, at most `qH` times on every
    path, and outputs a bit and `qS` password guesses. -/
structure DHPAKEAdversary (Pw W K : Type) (qH qS : ℕ) where
  /-- The interaction with the random oracle. -/
  run : W → W → K → OracleAdv (Pw × W × W × W) K (Bool × (Fin qS → Pw))
  /-- At most `qH` queries on every path. -/
  isQueryBound : ∀ X Y k, (run X Y k).IsQueryBound qH

variable {S W Pw K : Type} [Fintype S] [Nonempty S] [SampleableType W]
  [Fintype Pw] [Nonempty Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] {qH qS : ℕ}

/-- The success predicate: the bit equals `c` or a guess equals the password. -/
def success (c : Bool) (pw : Pw) (o : Bool × (Fin qS → Pw)) : Bool :=
  (o.1 == c) || decide (∃ i, o.2 i = pw)

/-- The client's message `maskC pw (g^x)`. -/
def msgC (P : DHPAKE S W Pw) (pw : Pw) (x : S) : W := P.maskC pw (P.pubEquiv x)

/-- The server's message `maskS pw (g^y)`. -/
def msgS (P : DHPAKE S W Pw) (pw : Pw) (y : S) : W := P.maskS pw (P.pubEquiv y)

/-- The input of the key hash in an honest session: `(pw, X*, Y*, g^{xy})`. -/
def hashInput (P : DHPAKE S W Pw) (pw : Pw) (x y : S) : Pw × W × W × W :=
  (pw, msgC P pw x, msgS P pw y, P.dh x (P.pubEquiv y))

/-- **The find-then-guess game.** Sample the bit `c`, the secrets `x`, `y` and the
    password; the real key is the answer of the lazily sampled oracle at the honest input;
    the adversary receives the real key if `c` holds and a uniform key otherwise, and runs
    against the same oracle. -/
noncomputable def dhpakeGame (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS) :
    PMF Bool :=
  (PMF.uniformOfFintype Bool).bind fun c => (PMF.uniformOfFintype S).bind fun x =>
  (PMF.uniformOfFintype S).bind fun y => (PMF.uniformOfFintype Pw).bind fun pw =>
    (roOracle emptyTable (hashInput P pw x y)).bind fun kt =>
    (if c then PMF.pure kt.1 else PMF.uniformOfFintype K).bind fun k =>
      (OracleAdv.run roOracle (D.run (msgC P pw x) (msgS P pw y) k) kt.2).map
        fun z => success c pw z.1

/-- The hybrid game: a uniform key and a fresh oracle. -/
noncomputable def dhpakeHybrid (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS) :
    PMF Bool :=
  (PMF.uniformOfFintype Bool).bind fun c => (PMF.uniformOfFintype S).bind fun x =>
  (PMF.uniformOfFintype S).bind fun y => (PMF.uniformOfFintype Pw).bind fun pw =>
  (PMF.uniformOfFintype K).bind fun k =>
    (OracleAdv.run roOracle (D.run (msgC P pw x) (msgS P pw y) k) emptyTable).map
      fun z => success c pw z.1

/-- The probability that the adversary queries the honest input in the hybrid game. -/
noncomputable def dhpakeQueryProb (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS) :
    ℝ≥0∞ :=
  ∑' x, PMF.uniformOfFintype S x * ∑' y, PMF.uniformOfFintype S y *
  ∑' pw, PMF.uniformOfFintype Pw pw * ∑' k, PMF.uniformOfFintype K k *
    queryProb (hashInput P pw x y) (D.run (msgC P pw x) (msgS P pw y) k)

/-! ## The CDH reduction -/

/-- The CDH group of `P` as a core `DDHDef`: key generation samples `s` and publishes
    `g^s` as both components, and `ecdh (g^s) Y = dh s Y`. -/
noncomputable def cdhDef (P : DHPAKE S W Pw) : DDHDef W where
  ecdh priv pub := P.dh (P.pubEquiv.symm priv) pub
  keygen := liftPMF ((PMF.uniformOfFintype S).map fun s => (P.pubEquiv s, P.pubEquiv s))
  keygen_isPure := liftPMF_isPure _

/-- The output distribution of the reduction on the challenge `(gA, gB)`: sample the
    password and a uniform key, run `D` on `(maskC pw gA, maskS pw gB)` against a lazily
    sampled oracle with a query log, and return the last component of the query at a
    uniform position of the log. -/
noncomputable def cdhDist (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS)
    (gA gB : W) : PMF W :=
  (PMF.uniformOfFintype Pw).bind fun pw => (PMF.uniformOfFintype K).bind fun k =>
    (OracleAdv.run (OracleAdv.withLog roOracle)
      (D.run (P.maskC pw gA) (P.maskS pw gB) k) (emptyTable, [])).bind fun z =>
    (PMF.uniformOfFintype (Fin (max qH 1))).map fun i : Fin (max qH 1) =>
      (z.2.2.getD (i : ℕ) (pw, gA, gB, gA)).2.2.2

/-- **The CDH reduction.** On the challenge `(gA, gB)` it samples from `cdhDist`. -/
noncomputable def cdhReduction (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS) :
    CDH_Adversary W :=
  fun gA gB => liftPMF (cdhDist P D gA gB)

/-- The CDH advantage of `cdhReduction P D` as a probability over the secrets. -/
theorem cdhAdvantage_cdhReduction (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS) :
    CDH_Advantage (cdhDef P) (cdhReduction P D) =
      ((PMF.uniformOfFintype S).bind fun a => (PMF.uniformOfFintype S).bind fun b =>
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
theorem dhpakeGame_le_hybrid (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS) :
    dhpakeGame P D true ≤ dhpakeHybrid P D true + dhpakeQueryProb P D := by
  unfold dhpakeGame dhpakeHybrid
  rw [show dhpakeQueryProb P D = ∑' c : Bool, PMF.uniformOfFintype Bool c * dhpakeQueryProb P D
    by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]]
  refine bind_apply_le_add_tsum _ _ _ _ _ fun c => ?_
  · unfold dhpakeQueryProb
    refine bind_apply_le_add_tsum _ _ _ _ _ fun x => ?_
    refine bind_apply_le_add_tsum _ _ _ _ _ fun y => ?_
    refine bind_apply_le_add_tsum _ _ _ _ _ fun pw => ?_
    rw [Extracted.roOracle_emptyTable_eq, PMF.bind_map]
    cases c
    · simp only [Function.comp_def, Bool.false_eq_true, if_false]
      refine bind_apply_le_of_le _ _ _ _ fun y0 => ?_
      exact bind_apply_le_add_tsum _ _ _ _ _ fun k => run_update_le _ y0 _ _
    · simp only [Function.comp_def, if_true, PMF.pure_bind]
      exact bind_apply_le_add_tsum _ _ _ _ _ fun k => run_update_le _ k _ _

/-- For a fixed output `o`, a uniform bit and a uniform password make `o` succeed with
    probability at most `1/2 + qS/|Pw|`. -/
theorem success_prob_le (o : Bool × (Fin qS → Pw)) :
    ((PMF.uniformOfFintype Bool).bind fun c => (PMF.uniformOfFintype Pw).bind fun pw =>
      PMF.pure (success c pw o)) true ≤ 2⁻¹ + qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ := by
  have hsplit : ((PMF.uniformOfFintype Bool).bind fun c => (PMF.uniformOfFintype Pw).bind
      fun pw => PMF.pure (success c pw o)) true ≤
      ((PMF.uniformOfFintype Bool).bind fun c => PMF.pure (o.1 == c)) true +
        ((PMF.uniformOfFintype Pw).bind fun pw => PMF.pure (decide (∃ i, o.2 i = pw))) true := by
    set G := ((PMF.uniformOfFintype Pw).bind fun pw => PMF.pure (decide (∃ i, o.2 i = pw))) true
    have hc : ∀ c : Bool, ((PMF.uniformOfFintype Pw).bind fun pw =>
        PMF.pure (success c pw o)) true ≤ PMF.pure (o.1 == c) true + G := by
      intro c
      have h := bind_apply_le_add_tsum (PMF.uniformOfFintype Pw)
        (fun pw => PMF.pure (success c pw o)) (fun _ => PMF.pure (o.1 == c))
        (fun pw => PMF.pure (decide (∃ i, o.2 i = pw)) true) true fun pw => by
          unfold success
          cases (o.1 == c) <;> cases (decide (∃ i, o.2 i = pw)) <;> simp
      rwa [PMF.bind_const, ← PMF.bind_apply] at h
    have h := bind_apply_le_add_tsum (PMF.uniformOfFintype Bool) _
      (fun c => PMF.pure (o.1 == c)) (fun _ => G) true hc
    rwa [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul] at h
  have hbit : ((PMF.uniformOfFintype Bool).bind fun c => PMF.pure (o.1 == c)) true = 2⁻¹ := by
    simp [PMF.bind_apply, tsum_fintype, PMF.pure_apply]
  have hguess : ((PMF.uniformOfFintype Pw).bind fun pw => PMF.pure (decide (∃ i, o.2 i = pw)))
      true ≤ qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ := by
    rw [PMF.bind_apply, tsum_fintype]
    calc ∑ pw, PMF.uniformOfFintype Pw pw * PMF.pure (decide (∃ i, o.2 i = pw)) true
        ≤ ∑ pw, ∑ i : Fin qS, PMF.uniformOfFintype Pw pw *
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
              rw [if_pos (by rw [eq_comm, decide_eq_true_eq]; exact ⟨i, hi⟩)]
            rw [h1]
            refine le_trans (le_of_eq ?_) hle
            simp [hi]
          · simp [h, PMF.pure_apply]
      _ = ∑ i : Fin qS, (Fintype.card Pw : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [PMF.uniformOfFintype_apply]
      _ = qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ := by simp
  exact hsplit.trans (by rw [hbit]; gcongr)

omit [Fintype Pw] [Nonempty Pw] in
/-- In the hybrid game the adversary's view is independent of the password. -/
theorem hybrid_view_eq (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS) (pw : Pw) :
    ((PMF.uniformOfFintype S).bind fun x => (PMF.uniformOfFintype S).bind fun y =>
      (PMF.uniformOfFintype K).bind fun k =>
        (OracleAdv.run roOracle (D.run (msgC P pw x) (msgS P pw y) k) emptyTable).map
          Prod.fst) =
      ((PMF.uniformOfFintype W).bind fun X => (PMF.uniformOfFintype W).bind fun Y =>
        (PMF.uniformOfFintype K).bind fun k =>
          (OracleAdv.run roOracle (D.run X Y k) emptyTable).map Prod.fst) := by
  nth_rewrite 1 [← uniformOfFintype_map_equiv (P.pubEquiv.trans (P.maskC pw))]
  rw [PMF.bind_map]
  refine congrArg _ (funext fun x => ?_)
  rw [← uniformOfFintype_map_equiv (P.pubEquiv.trans (P.maskS pw))]
  simp only [Function.comp_apply]
  rw [PMF.bind_map]
  rfl

/-- **The hybrid game.** With a uniform key the transcript is uniform whatever the
    password: the bit is guessed with probability `1/2` and one of `qS` guesses hits the
    password with probability at most `qS/|Pw|`. -/
theorem dhpakeHybrid_le (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS) :
    dhpakeHybrid P D true ≤ 2⁻¹ + qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ := by
  set view := (PMF.uniformOfFintype W).bind fun X => (PMF.uniformOfFintype W).bind fun Y =>
    (PMF.uniformOfFintype K).bind fun k =>
      (OracleAdv.run roOracle (D.run X Y k) emptyTable).map Prod.fst with hview
  have heq : dhpakeHybrid P D = view.bind fun o => (PMF.uniformOfFintype Bool).bind fun c =>
      (PMF.uniformOfFintype Pw).bind fun pw => PMF.pure (success c pw o) := by
    rw [PMF.bind_comm view (PMF.uniformOfFintype Bool)]
    unfold dhpakeHybrid
    refine congrArg _ (funext fun c => ?_)
    rw [PMF.bind_comm view (PMF.uniformOfFintype Pw)]
    simp only [PMF.bind_comm (PMF.uniformOfFintype S) (PMF.uniformOfFintype Pw)]
    refine congrArg _ (funext fun pw => ?_)
    rw [hview, ← hybrid_view_eq P D pw]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
    rfl
  rw [heq]
  exact bind_apply_le_of_le _ _ _ _ success_prob_le

/-- The query probability is at most `qH` times the CDH advantage of the reduction. -/
theorem dhpakeQueryProb_le (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS) :
    dhpakeQueryProb P D ≤ qH * CDH_Advantage (cdhDef P) (cdhReduction P D) := by
  rw [cdhAdvantage_cdhReduction]
  refine tsum_le_mul_bind_apply _ _ _ _ _ fun x _ => ?_
  refine tsum_le_mul_bind_apply _ _ _ _ _ fun y _ => ?_
  simp only [cdhDist, PMF.map_bind]
  refine tsum_le_mul_bind_apply _ _ _ _ _ fun pw _ => ?_
  refine tsum_le_mul_bind_apply _ _ _ _ _ fun k _ => ?_
  rw [queryProb_eq_log]
  refine tsum_le_mul_bind_apply _ _ _ _ _ fun z hz => ?_
  have hlen : z.2.2.length ≤ qH := by
    simpa using OracleAdv.sum_cost_log_le_of_mem_support roOracle (fun _ => 1) _ qH
      ((D.isQueryBound _ _ _).isQueryBoundBy_one) emptyTable [] z
      ((PMF.mem_support_iff _ _).mpr hz)
  rw [PMF.map_comp]
  exact indicator_le_mul_guess z.2.2 (hashInput P pw x y) _ hlen
    (fun d => decide (d.2.2.2 = P.dh x (P.pubEquiv y))) (by simp [hashInput])

/-- **The generic bound for a Diffie–Hellman PAKE in the random-oracle model.** For every
    adversary `D` asking at most `qH` queries of the key hash and making `qS` online
    password guesses, the success probability in the find-then-guess game is at most
    `1/2 + qS/|Pw| + qH · CDH_Advantage (cdhDef P) (cdhReduction P D)`. -/
theorem dhpake_success_le (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS) :
    dhpakeGame P D true ≤ 2⁻¹ + qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ +
      qH * CDH_Advantage (cdhDef P) (cdhReduction P D) :=
  (dhpakeGame_le_hybrid P D).trans
    (add_le_add (dhpakeHybrid_le P D) (dhpakeQueryProb_le P D))

/-! ## The costed reduction -/

variable (qH) in
/-- The costed run of the reduction after the password `pw` and the key `k`: the costed
    adversary `D'` against the logged lazily sampled oracle, each query at step cost `tH`,
    then the uniform index into the log and the output, at step cost `tOut`. -/
noncomputable def cdhReduction.timedRun (P : DHPAKE S W Pw) (tH tOut : ℕ)
    (D' : W → W → K → OracleAdv.Timed (Pw × W × W × W) K (Bool × (Fin qS → Pw)))
    (gA gB : W) (pw : Pw) (k : K) : ℕ × OracleAdv.Timed Empty Empty W :=
  OracleAdv.Timed.stepBind
    (OracleAdv.Timed.runOracle (OracleAdv.withLog roOracle) (fun _ => tH)
      (D' (P.maskC pw gA) (P.maskS pw gB) k) (emptyTable, []))
    fun z => (0, .rand (PMF.uniformOfFintype (Fin (max qH 1))) (fun _ => tOut)
      fun i => .ret (z.2.2.getD (i : ℕ) (pw, gA, gB, gA)).2.2.2)

variable (qH) in
/-- **The costed CDH reduction.** On the challenge `(gA, gB)`: sample the password and
    the key (one node each), then `cdhReduction.timedRun`. -/
noncomputable def cdhReduction.timed (P : DHPAKE S W Pw) (tH tOut : ℕ)
    (D' : W → W → K → OracleAdv.Timed (Pw × W × W × W) K (Bool × (Fin qS → Pw)))
    (gA gB : W) : ℕ × OracleAdv.Timed Empty Empty W :=
  (0, .rand (PMF.uniformOfFintype Pw) (fun _ => 0) fun pw =>
    .rand (PMF.uniformOfFintype K)
      (fun k => (cdhReduction.timedRun qH P tH tOut D' gA gB pw k).1)
      fun k => (cdhReduction.timedRun qH P tH tOut D' gA gB pw k).2)

omit [Fintype S] [Nonempty S] in
/-- Under any oracle, the erased costed reduction has the output distribution
    `cdhDist P D gA gB` of `cdhReduction P D`, for a costed adversary `D'` whose erasure
    is `D.run`. -/
theorem cdhReduction.run_erase_timed (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS)
    (D' : W → W → K → OracleAdv.Timed (Pw × W × W × W) K (Bool × (Fin qS → Pw)))
    (hD : ∀ X Y k, (D' X Y k).erase = D.run X Y k) (tH tOut : ℕ)
    {U : Type} (O' : U → Empty → PMF (Empty × U)) (u : U) (gA gB : W) :
    (OracleAdv.run O' (cdhReduction.timed qH P tH tOut D' gA gB).2.erase u).map Prod.fst =
      cdhDist P D gA gB := by
  simp only [cdhReduction.timed, OracleAdv.Timed.erase, OracleAdv.run_rand, PMF.map_bind,
    cdhDist]
  refine congrArg _ (funext fun pw => congrArg _ (funext fun k => ?_))
  rw [cdhReduction.timedRun, OracleAdv.Timed.erase_stepBind,
    OracleAdv.run_bind_map_fst_empty, OracleAdv.Timed.run_erase_runOracle, hD]
  refine congrArg _ (funext fun z => ?_)
  simp only [OracleAdv.Timed.erase, OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind,
    PMF.pure_map]
  rfl

omit [Fintype S] [Nonempty S] in
/-- **Time of the CDH reduction.** With the costed adversary `D'` of time `T` on every
    input and erasure `D.run` (at most `qH` queries), the costed reduction has time at
    most `T + (tH + 1) * qH + tOut + 3`: two sampling nodes, the adversary with each query
    charged its step `tH` and its oracle node, and the uniform index with the output. -/
theorem cdhReduction.timeBound_timed (P : DHPAKE S W Pw) (D : DHPAKEAdversary Pw W K qH qS)
    (D' : W → W → K → OracleAdv.Timed (Pw × W × W × W) K (Bool × (Fin qS → Pw)))
    (hD : ∀ X Y k, (D' X Y k).erase = D.run X Y k) (tH tOut : ℕ)
    {T : ℕ} (hT : ∀ X Y k, (D' X Y k).TimeBound T) (gA gB : W) :
    OracleAdv.Timed.StepTimeBound (cdhReduction.timed qH P tH tOut D' gA gB)
      (T + (tH + 1) * qH + tOut + 3) := by
  have hR : ∀ pw k, OracleAdv.Timed.StepTimeBound
      (cdhReduction.timedRun qH P tH tOut D' gA gB pw k) (T + (tH + 1) * qH + (1 + tOut)) := by
    intro pw k
    have hq : (D' (P.maskC pw gA) (P.maskS pw gB) k).erase.IsQueryBoundBy
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
  refine ⟨Nat.zero_le _, by omega, fun pw => ⟨Nat.zero_le _, by omega, fun k => ?_⟩⟩
  have h := hR pw k
  simp only [OracleAdv.Timed.StepTimeBound] at h
  exact ⟨by omega, h.2.mono (by omega)⟩

end CatCrypt.Crypto.PAKE.DH
