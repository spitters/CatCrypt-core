/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PRPPRFSwitching

/-!
# The PKEY game against oracle adversaries with query bounds

The adversary is an `OracleAdv (PKEYQuery PK) (PK × Bool) Bool`. It interacts
with the PKEY challenger only through three queries: `gen` (sample a fresh honest
key pair), `csetpk pk` (register `pk` as a corrupt key) and `honpk pk` (ask
whether `pk` is honest). There is no secret-key oracle.

The challenger samples key pairs from `kg : PMF (PK × SK)` whose public-key
marginal is uniform. A collision is a sampled public key that is already
registered. Game `false` registers the sampled key as honest regardless; game
`true` leaves the state unchanged on a collision. Both games set a flag on a
collision. The two oracles agree on every transition that keeps the flag
cleared, so the advantage is bounded by the probability of the flag, which is at
most `(q_gen (q_gen - 1) + 2 q_gen q_csetpk) / (2 |PK|)`.

## Main definitions

* `PKEYQuery`, `PKEYState`, `pkeyOracle` — queries, challenger state, oracle
* `IsPKEYBound A q_gen q_csetpk` — query bound with separate counters
* `pkeyGame`, `pkeyQAdvantage` — the games and the advantage

## Main results

* `run_pkeyOracle_flag_le` — the flag bound
* `pkeyQAdvantage_le` — the advantage bound

This game replaces, for the PKEY switching step, the game `PKEY` of
`CatCrypt.Examples.Cryptobox` (module `Cryptobox.PKEY`), whose adversary is an
`SPComp` program with a `getsk` oracle and unrestricted heap access and whose
switching bounds `pkeyAdvantage_le_collision` and `pkey_switching` take the
up-to-bad agreement and the collision bound as hypotheses (finding 15 of the
vacuity sweep). The Cryptobox chain is not rebased on this game.
-/

@[expose] public section

namespace CatCrypt.Examples.Cryptobox.PKEYQ

open CatCrypt.Core CatCrypt.Prob CatCrypt.Unary CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open scoped ENNReal

/-- Queries of the PKEY game: generate an honest key, register a corrupt public
key, ask whether a public key is honest. -/
inductive PKEYQuery (PK : Type) where
  /-- Generate a fresh honest key pair and return its public key. -/
  | gen
  /-- Register `pk` as a corrupt public key. -/
  | csetpk (pk : PK)
  /-- Ask whether `pk` is an honest public key. -/
  | honpk (pk : PK)

variable {PK SK : Type} [Fintype PK] [Nonempty PK] [DecidableEq PK]

/-- Challenger state: honest public keys, corrupt public keys and the table of
secret keys of honest public keys. -/
structure PKEYState (PK SK : Type) where
  /-- Honest public keys. -/
  hon : Finset PK
  /-- Corrupt public keys. -/
  cor : Finset PK
  /-- Secret keys of the honest public keys. -/
  sks : List (PK × SK)

namespace PKEYState

/-- The initial state with no registered keys. -/
def init : PKEYState PK SK := ⟨∅, ∅, []⟩

/-- The registered public keys, honest or corrupt. -/
def reg (s : PKEYState PK SK) : Finset PK := s.hon ∪ s.cor

/-- Register the key pair `x` as honest. -/
def register (s : PKEYState PK SK) (x : PK × SK) : PKEYState PK SK :=
  ⟨insert x.1 s.hon, s.cor, x :: s.sks⟩

/-- Register `pk` as corrupt. -/
def corrupt (s : PKEYState PK SK) (pk : PK) : PKEYState PK SK :=
  ⟨s.hon, insert pk s.cor, s.sks⟩

omit [Fintype PK] [Nonempty PK] in
/-- Registering an unregistered honest key adds one registered key. -/
theorem card_reg_register (s : PKEYState PK SK) (x : PK × SK) (hx : x.1 ∉ s.reg) :
    (s.register x).reg.card = s.reg.card + 1 := by
  simp only [reg, register, Finset.insert_union]
  exact Finset.card_insert_of_notMem hx

omit [Fintype PK] [Nonempty PK] in
/-- Registering an unregistered corrupt key adds one registered key. -/
theorem card_reg_corrupt (s : PKEYState PK SK) (pk : PK) (hpk : pk ∉ s.reg) :
    (s.corrupt pk).reg.card = s.reg.card + 1 := by
  simp only [reg, corrupt, Finset.union_insert]
  exact Finset.card_insert_of_notMem hpk

end PKEYState

/-- One `gen` transition on the sampled key pair `x` from state `s` with flag
`fl`. Without a collision, `x` is registered as honest. On a collision the flag
is set; game `false` registers `x` as honest and game `true` leaves the state
unchanged and answers `false`. -/
def genStep (b : Bool) (s : PKEYState PK SK) (fl : Bool) (x : PK × SK) :
    (PK × Bool) × (PKEYState PK SK × Bool) :=
  if x.1 ∈ s.reg then
    if b then ((x.1, false), (s, true)) else ((x.1, true), (s.register x, true))
  else ((x.1, true), (s.register x, fl))

/-- The PKEY oracle of game `b` on flagged states. `gen` samples a key pair from
`kg` and applies `genStep`; `csetpk pk` registers `pk` as corrupt when it is not
registered and answers whether it did; `honpk pk` answers whether `pk` is
honest. -/
noncomputable def pkeyOracle (kg : PMF (PK × SK)) (b : Bool) :
    PKEYState PK SK × Bool → PKEYQuery PK → PMF ((PK × Bool) × (PKEYState PK SK × Bool))
  | (s, fl), .gen => kg.map (genStep b s fl)
  | (s, fl), .csetpk pk =>
    if pk ∈ s.reg then PMF.pure ((pk, false), (s, fl))
    else PMF.pure ((pk, true), (s.corrupt pk, fl))
  | (s, fl), .honpk pk => PMF.pure ((pk, decide (pk ∈ s.hon)), (s, fl))

/-- `IsPKEYBound A q_gen q_csetpk`: every path of `A` asks at most `q_gen`
`gen` queries and at most `q_csetpk` `csetpk` queries; `honpk` queries are not
counted. -/
def IsPKEYBound {R α : Type} : OracleAdv (PKEYQuery PK) R α → ℕ → ℕ → Prop
  | .ret _, _, _ => True
  | .rand _ k, g, c => ∀ b, IsPKEYBound (k b) g c
  | .query .gen k, g, c => 1 ≤ g ∧ ∀ r, IsPKEYBound (k r) (g - 1) c
  | .query (.csetpk _) k, g, c => 1 ≤ c ∧ ∀ r, IsPKEYBound (k r) g (c - 1)
  | .query (.honpk _) k, g, c => ∀ r, IsPKEYBound (k r) g c

/-- The PKEY game `b`: run `A` against `pkeyOracle kg b` from the initial state
with the flag cleared and return its output bit. -/
noncomputable def pkeyGame (kg : PMF (PK × SK)) (b : Bool)
    (A : OracleAdv (PKEYQuery PK) (PK × Bool) Bool) : SPComp Bool :=
  liftPMF ((OracleAdv.run (pkeyOracle kg b) A (PKEYState.init, false)).map Prod.fst)

/-- The PKEY advantage of the oracle adversary `A`. -/
noncomputable def pkeyQAdvantage (kg : PMF (PK × SK))
    (A : OracleAdv (PKEYQuery PK) (PK × Bool) Bool) : ℝ≥0∞ :=
  Advantage (pkeyGame kg false A) (pkeyGame kg true A)

/-! ## Identical until the flag -/

omit [Fintype PK] [Nonempty PK] in
/-- Neither oracle clears a set flag. -/
theorem pkeyOracle_apply_true_false (kg : PMF (PK × SK)) (b : Bool) (s : PKEYState PK SK)
    (d : PKEYQuery PK) (r : PK × Bool) (s' : PKEYState PK SK) :
    pkeyOracle kg b (s, true) d (r, (s', false)) = 0 := by
  cases d with
  | gen =>
    simp only [pkeyOracle, PMF.map_apply]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    by_cases hx : x.1 ∈ s.reg <;> cases b <;> simp [genStep, hx]
  | csetpk pk =>
    simp only [pkeyOracle]
    split_ifs <;> simp [PMF.pure_apply]
  | honpk pk => simp [pkeyOracle, PMF.pure_apply]

omit [Fintype PK] [Nonempty PK] in
/-- The two oracles agree on every transition into a state with the flag
cleared. -/
theorem pkeyOracle_apply_false_eq (kg : PMF (PK × SK)) (s : PKEYState PK SK × Bool)
    (d : PKEYQuery PK) (r : PK × Bool) (s' : PKEYState PK SK) :
    pkeyOracle kg false s d (r, (s', false)) = pkeyOracle kg true s d (r, (s', false)) := by
  obtain ⟨s, fl⟩ := s
  cases d with
  | gen =>
    simp only [pkeyOracle, PMF.map_apply]
    refine tsum_congr fun x => ?_
    by_cases hx : x.1 ∈ s.reg
    · simp [genStep, hx]
    · have e : genStep false s fl x = genStep true s fl x := by
        unfold genStep; rw [ite_eq_right hx, ite_eq_right hx]
      by_cases h : (r, s', false) = genStep false s fl x
      · rw [ite_eq_left h, ite_eq_left (h.trans e)]
      · rw [ite_eq_right h, ite_eq_right fun h' => h (h'.trans e.symm)]
  | csetpk pk => rfl
  | honpk pk => rfl

/-! ## The flag bound -/

variable {α : Type}

/-- **Flag bound.** From a state with the flag cleared and `m` registered
public keys, an adversary asking at most `g` `gen` queries and `c` `csetpk`
queries sets the flag in game `false` with probability at most
`(∑ i < g, (m + i + c)) / |PK|`. -/
theorem run_pkeyOracle_flag_le (kg : PMF (PK × SK))
    (hkg : kg.map Prod.fst = PMF.uniformFintype PK)
    (A : OracleAdv (PKEYQuery PK) (PK × Bool) α) (g c : ℕ) (hA : IsPKEYBound A g c)
    (s : PKEYState PK SK) :
    (OracleAdv.run (pkeyOracle kg false) A (s, false)).toOuterMeasure {x | x.2.2 = true} ≤
      ((∑ i ∈ Finset.range g, (s.reg.card + i + c) : ℕ) : ℝ≥0∞) / Fintype.card PK := by
  induction A generalizing g c s with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (OracleAdv.run (pkeyOracle kg false) (k b) (s, false)).toOuterMeasure _
        ≤ ∑' b, p b * (((∑ i ∈ Finset.range g, (s.reg.card + i + c) : ℕ) : ℝ≥0∞) /
            Fintype.card PK) :=
          ENNReal.tsum_le_tsum fun b => by gcongr; exact ih b g c (hA b) s
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    set N : ℝ≥0∞ := (Fintype.card PK : ℝ≥0∞)
    rw [OracleAdv.run_query]
    cases d with
    | gen =>
      obtain ⟨hg, hk⟩ := hA
      obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hk
      simp only [pkeyOracle, PMF.bind_map, Function.comp_def]
      rw [PMF.toOuterMeasure_bind_apply]
      set B : ℝ≥0∞ := ((∑ i ∈ Finset.range g, ((s.reg.card + 1) + i + c) : ℕ) : ℝ≥0∞) / N
      have hterm : ∀ x : PK × SK,
          (OracleAdv.run (pkeyOracle kg false) (k (genStep false s false x).1)
            (genStep false s false x).2).toOuterMeasure {x | x.2.2 = true} ≤
          Set.indicator {x : PK × SK | x.1 ∈ s.reg} 1 x + B := by
        intro x
        by_cases hx : x.1 ∈ s.reg
        · rw [Set.indicator_of_mem (by exact hx)]
          exact ((MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
            ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))).trans le_self_add
        · rw [Set.indicator_of_notMem (by exact hx), zero_add]
          have h := ih (x.1, true) g c (hk _) (s.register x)
          simp only [genStep, ite_eq_right hx]
          rwa [PKEYState.card_reg_register s x hx] at h
      calc ∑' x, kg x * (OracleAdv.run (pkeyOracle kg false) (k (genStep false s false x).1)
            (genStep false s false x).2).toOuterMeasure {x | x.2.2 = true}
          ≤ ∑' x, kg x * (Set.indicator {x : PK × SK | x.1 ∈ s.reg} 1 x + B) :=
            ENNReal.tsum_le_tsum fun x => by gcongr; exact hterm x
        _ = kg.toOuterMeasure {x : PK × SK | x.1 ∈ s.reg} + B := by
            simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
              PMF.toOuterMeasure_apply]
            congr 1
            refine tsum_congr fun x => ?_
            by_cases hx : x.1 ∈ s.reg
            · simp [Set.indicator_of_mem, hx]
            · simp [Set.indicator_of_notMem, hx]
        _ = s.reg.card / N + B := by
            have hpre : {x : PK × SK | x.1 ∈ s.reg} = Prod.fst ⁻¹' (s.reg : Set PK) := rfl
            rw [hpre, ← PMF.toOuterMeasure_map_apply, hkg,
              PMF.toOuterMeasure_uniformFintype_apply]
            simp [N]
        _ ≤ _ := by
            rw [ENNReal.div_add_div_same, ← Nat.cast_add]
            gcongr
            rw [Finset.sum_range_succ', Finset.sum_congr rfl fun i _ =>
              (by ring : s.reg.card + (i + 1) + c = s.reg.card + 1 + i + c)]
            omega
    | csetpk pk =>
      obtain ⟨hc, hk⟩ := hA
      obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hk
      simp only [pkeyOracle]
      split_ifs with hpk
      · rw [PMF.pure_bind]
        refine (ih _ g c (hk _) s).trans ?_
        gcongr
        omega
      · rw [PMF.pure_bind]
        refine (ih _ g c (hk _) (s.corrupt pk)).trans_eq ?_
        rw [PKEYState.card_reg_corrupt s pk hpk]
        rw [Finset.sum_congr rfl fun i _ =>
          (by ring : s.reg.card + 1 + i + c = s.reg.card + i + (c + 1))]
    | honpk pk =>
      simp only [pkeyOracle, PMF.pure_bind]
      exact ih _ g c (hA _) s

/-! ## Flagged games -/

/-- Game `b` with the final flag written to the heap location `flagLoc`. -/
noncomputable def pkeyFlagGame (kg : PMF (PK × SK)) (b : Bool)
    (A : OracleAdv (PKEYQuery PK) (PK × Bool) Bool) : SPComp Bool :=
  fun h => (OracleAdv.run (pkeyOracle kg b) A (PKEYState.init, false)).map
    fun x => some (x.1, h.set flagLoc x.2.2)

omit [Fintype PK] [Nonempty PK] in
/-- The flagged game returns `true` with the same probability as the game. -/
theorem prTrue_pkeyFlagGame (kg : PMF (PK × SK)) (b : Bool)
    (A : OracleAdv (PKEYQuery PK) (PK × Bool) Bool) :
    prTrue (pkeyFlagGame kg b A) Heap.empty = prTrue (pkeyGame kg b A) Heap.empty := by
  rw [pkeyGame, prTrue_liftPMF_map, prTrue_eq_prEventComp]
  unfold prEventComp prEvent pkeyFlagGame
  convert tsum_ite_map_some _ (fun x : Bool × (PKEYState PK SK × Bool) =>
    (x.1, Heap.empty.set flagLoc x.2.2)) (fun y => y.1 = true)

omit [Fintype PK] [Nonempty PK] in
/-- The flag event of the flagged game is the flag event of the run. -/
theorem prEventComp_pkeyFlagGame (kg : PMF (PK × SK)) (b : Bool)
    (A : OracleAdv (PKEYQuery PK) (PK × Bool) Bool) :
    prEventComp (pkeyFlagGame kg b A) Heap.empty (fun _ h' => h'.get flagLoc = true) =
      (OracleAdv.run (pkeyOracle kg b) A (PKEYState.init, false)).toOuterMeasure
        {x | x.2.2 = true} := by
  unfold prEventComp prEvent pkeyFlagGame
  have := tsum_ite_map_some (OracleAdv.run (pkeyOracle kg b) A (PKEYState.init, false))
    (fun x : Bool × (PKEYState PK SK × Bool) => (x.1, Heap.empty.set flagLoc x.2.2))
    (fun y => y.2.get flagLoc = true)
  simpa using this

omit [Fintype PK] [Nonempty PK] in
/-- The flagged game is lossless. -/
theorem isLossless_pkeyFlagGame (kg : PMF (PK × SK)) (b : Bool)
    (A : OracleAdv (PKEYQuery PK) (PK × Bool) Bool) : isLossless (pkeyFlagGame kg b A) := by
  intro h
  simp [SDistr.mass, pkeyFlagGame, PMF.map_apply]

/-! ## The advantage bound -/

/-- Closed form of the collision sum:
`2 ∑ i < g, (i + c) = g (g - 1) + 2 g c`. -/
theorem two_mul_sum_range_add (g c : ℕ) :
    2 * (∑ i ∈ Finset.range g, (i + c)) = g * (g - 1) + 2 * (g * c) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_add,
    mul_comm 2 (∑ i ∈ Finset.range g, i), Finset.sum_range_id_mul_two]

/-- **PKEY advantage bound.** An oracle adversary asking at most `q_gen` `gen`
queries and `q_csetpk` `csetpk` queries has PKEY advantage at most
`(q_gen (q_gen - 1) + 2 q_gen q_csetpk) / (2 |PK|)` when the public-key marginal
of key generation is uniform. -/
theorem pkeyQAdvantage_le (kg : PMF (PK × SK)) (hkg : kg.map Prod.fst = PMF.uniformFintype PK)
    (A : OracleAdv (PKEYQuery PK) (PK × Bool) Bool) (q_gen q_csetpk : ℕ)
    (hA : IsPKEYBound A q_gen q_csetpk) :
    pkeyQAdvantage kg A ≤
      ((q_gen * (q_gen - 1) + 2 * (q_gen * q_csetpk) : ℕ) : ℝ≥0∞) / (2 * Fintype.card PK) := by
  have hadv : pkeyQAdvantage kg A =
      Advantage (pkeyFlagGame kg false A) (pkeyFlagGame kg true A) := by
    simp only [pkeyQAdvantage, Advantage, prTrue_pkeyFlagGame]
  rw [hadv]
  refine (failure_event_lemma _ _ Heap.empty (fun h => h.get flagLoc = true) ?_
    (isLossless_implies_if _ (isLossless_pkeyFlagGame kg false A))).trans ?_
  · intro b h' hbad
    simp only [pkeyFlagGame, PMF.map_apply]
    refine tsum_congr fun x => ?_
    obtain ⟨a, t, fl⟩ := x
    cases fl with
    | false =>
      rw [OracleAdv.run_apply_flag_false_eq (pkeyOracle kg false) (pkeyOracle kg true)
        (pkeyOracle_apply_true_false kg false) (pkeyOracle_apply_true_false kg true)
        (pkeyOracle_apply_false_eq kg)]
    | true =>
      have hne : some (b, h') ≠ some (a, Heap.empty.set flagLoc true) := by
        grind [Heap.get_set_same, Heap.get_set_other]
      simp only [hne, ite_false]
  · rw [prEventComp_pkeyFlagGame]
    refine (run_pkeyOracle_flag_le kg hkg A q_gen q_csetpk hA PKEYState.init).trans_eq ?_
    have h0 : (PKEYState.init : PKEYState PK SK).reg.card = 0 := rfl
    rw [h0, ← two_mul_sum_range_add, Nat.cast_mul, Nat.cast_ofNat,
      ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
    simp only [zero_add]

end CatCrypt.Examples.Cryptobox.PKEYQ
