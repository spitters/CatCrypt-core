/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.SignerHybrid
public import CatCryptCore.Crypto.FiatShamirROM.StraightLineCls
public import CatCryptCore.Crypto.FiatShamirROM.StatHVZK
public import CatCryptCore.Crypto.FiatShamirROM.Game

/-!
# Fiat–Shamir in the random-oracle model: the game at a sampler with the programmed flag

The game `attGameByP P D` at a sampler `D` whose signing answer `attSignOutP` is the
answer `attSignOut` of the attempt with the flag also set when a programmed entry of
the attempt lands on a point defined in the tables (`Protocol.Attempt.progHit`). The
real signing oracle sets its flag on the same event, so the real game and the game at
the witness sampler agree until the flag is set: the EUF-CMA advantage is at most the
probability that the forgery wins or the flag is set in the game at the witness
sampler, with no term for programmed collisions.

At a sampler the programmed collisions are charged together with the hidden entries
by a class-wise key bound of the sampler (`Protocol.AttKeyBoundClsAtN`) over oracles
with at most `N` defined points.

## Main definitions

* `Protocol.Attempt.progHit`, `Protocol.Attempt.charged` — a programmed entry of an
  attempt lands on a defined point; the entries charged in the key bound of a sampler
* `attSignOutP`, `attSignP`, `attStepP` — the signing answer of an attempt with the
  programmed flag, the signing oracle and the oracle of the game
* `attGameByP P D A`, `attAdvantageByP P D A` — the game at the sampler `D` whose
  outcome is decided by `P`, and its advantage
* `Protocol.AttKeyBoundClsAtN κ N D xw Γ` — the class-wise bound on guessing the
  points of programmed and hidden entries of a sampler, against oracles with at most
  `N` defined points

## Main results

* `Protocol.eufcma_le_witP` — the EUF-CMA advantage is at most the probability that
  the forgery wins or the flag is set in the game at the witness sampler
* `run_attP_flag_le_cls` — the class-wise bound on the flag of a run at a sampler
* `Protocol.att_le_simP_cls` — the probability that the forgery wins or the flag is
  set in the game at a sampler with HVZK distance `δ` and key bound `Γ` is at most the
  simulated-game advantage plus the expectation over generated pairs of
  `qS·δ(x, w) + Σ_c qS·(q c + Vc c + μc c·qS)·Γ(x, w) c`
* `KeyBoundClsAt.attKeyBoundClsAtN_wit` — the class-wise key bound of the protocol is
  the key bound of the witness sampler
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open CatCrypt.Crypto.Constructions.ECBCPRF (tsum_bind_mul tsum_pure_mul)
open scoped ENNReal

/-! ## Programmed hits and charged entries of an attempt -/

namespace Protocol.Attempt

variable {G : Protocol} (a : G.Attempt)

/-- A programmed entry of the attempt with the values `e` against the tables `t` lands
on a point defined in `t`. -/
def progHit (t : G.Tables) (e : Fin G.μ → G.Ch) : Bool :=
  (List.finRange G.μ).any fun i =>
    !G.ev i && (t.lookupAll (a.key (a.vals t.lookupAll e) i)).isSome

/-- Entry `i` of the attempt with the values `e` against `look` is charged in the key
bound of a sampler: it is programmed or hidden, and it is hidden or the hidden
entries of the attempt are at points undefined in `look`. -/
def charged (look : G.Key → Option G.Ch) (e : Fin G.μ → G.Ch) (i : Fin G.μ) : Bool :=
  (!G.ev i || !a.pub (a.vals look e) i) &&
    (!a.pub (a.vals look e) i || a.hidFresh look (a.vals look e))

end Protocol.Attempt

/-! ## The game -/

section ProgGame

variable {G : Protocol}

/-- The signing answer on `m` of the attempt `a` with the values `e` from the tables
`t`: the answer and tables of `attSignOut`, with the flag also set when a programmed
entry lands on a point defined in `t`. -/
def attSignOutP (t : G.Tables) (b : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch)
    (a : G.Attempt) : G.Answer × (G.Tables × Bool) :=
  ((attSignOut t b m e a).1, ((attSignOut t b m e a).2.1,
    (attSignOut t b m e a).2.2 || a.progHit t e))

/-- The signing oracle with the programmed flag of the sampler `D` for the pair `xw`
on `m` from the state `s`: uniform values `e`, then an attempt from `D xw m e`. -/
noncomputable def attSignP (D : G.Sampler) (xw : G.Stmt × G.Wit) (s : G.Tables × Bool)
    (m : G.Msg) : PMF (G.Answer × (G.Tables × Bool)) :=
  (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind fun e =>
    (D xw m e).map (attSignOutP s.1 s.2 m e)

/-- The oracle of the game with the programmed flag at the sampler `D` for the pair
`xw`: the hash queries of the real game and the signing oracle `attSignP D xw`. -/
noncomputable def attStepP (D : G.Sampler) (xw : G.Stmt × G.Wit) (s : G.Tables × Bool) :
    G.Query → Step G.Answer (G.Tables × Bool) G.Ch
  | .inl k => realHashStep s.1 s.2 k
  | .inr m => .plain (attSignP D xw s m)

/-- The game with the programmed flag at the sampler `D` whose outcome is decided by
the predicate `P`. -/
noncomputable def attGameByP (P : G.Stmt → G.Forgery × (G.Tables × Bool) → Bool)
    (D : G.Sampler) {qH qS : ℕ} (A : G.Adversary qH qS) : SPComp Bool :=
  PRPPRF.pmfGame (gameDistBy P (attStepP D) A)

/-- The advantage in the game with the programmed flag at the sampler `D` whose
outcome is decided by `P`. -/
noncomputable def attAdvantageByP (P : G.Stmt → G.Forgery × (G.Tables × Bool) → Bool)
    (D : G.Sampler) {qH qS : ℕ} (A : G.Adversary qH qS) : ℝ≥0∞ :=
  prTrue (attGameByP P D A) Heap.empty

theorem attStepP_inl (D : G.Sampler) (xw : G.Stmt × G.Wit) (s : G.Tables × Bool)
    (k : G.Key) : toOracle (attStepP D xw) s (.inl k) = toOracle (realStep xw) s (.inl k) :=
  rfl

/-- Without a programmed hit the signing answer with the programmed flag is the
signing answer of the attempt. -/
theorem attSignOutP_of_progHit (t : G.Tables) (b : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch)
    (a : G.Attempt) (h : a.progHit t e = false) :
    attSignOutP t b m e a = attSignOut t b m e a := by
  simp [attSignOutP, h]

/-- The programmed hit of the real attempt is `progColl`. -/
theorem progHit_witAttempt (x : G.Stmt) (w : G.Wit) (t : G.Tables) (m : G.Msg)
    (e : Fin G.μ → G.Ch) (r : G.Rand) :
    (G.witAttempt x w m r).progHit t e = progColl x w t m e r := rfl

/-- A signing answer with the programmed flag of an attempt none of whose points is
among the entries `l` commutes with adding `l` to the hidden entries. -/
theorem attSignOutP_addRejs (t : G.Tables) (b : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch)
    (a : G.Attempt) (l : List (G.Key × G.Ch))
    (hk : ∀ i, a.key (a.vals t.lookupAll e) i ∉ l.map Prod.fst) :
    attSignOutP (t.addRejs l) b m e a =
      Prod.map id (Prod.map (Protocol.Tables.addRejs l) id) (attSignOutP t b m e a) := by
  have hv : a.vals (t.addRejs l).lookupAll e = a.vals t.lookupAll e :=
    effVec_congr _ _ a.key_causal e _ fun i => by
      change (if G.ev i then (t.addRejs l).lookupAll else fun _ => none)
          (a.key (a.vals t.lookupAll e) i) =
        (if G.ev i then t.lookupAll else fun _ => none) (a.key (a.vals t.lookupAll e) i)
      cases G.ev i
      · rfl
      · exact Protocol.lookupAll_addRejs_of_notMem l t (hk i)
  have hp : a.progHit (t.addRejs l) e = a.progHit t e := by
    unfold Protocol.Attempt.progHit
    rw [hv]
    refine congrArg (List.any _) (funext fun i => ?_)
    rw [Protocol.lookupAll_addRejs_of_notMem l t (hk i)]
  simp only [attSignOutP, hp, attSignOut_addRejs t b m e a l hk]
  rfl

end ProgGame

/-! ## Runs of the game with the programmed flag -/

section ProgRun

variable {G : Protocol} {α : Type} (D : G.Sampler) (xw : G.Stmt × G.Wit)

theorem attSignP_bind {β : Type} (s : G.Tables × Bool) (m : G.Msg)
    (g : G.Answer × (G.Tables × Bool) → PMF β) :
    (attSignP D xw s m).bind g = (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind fun e =>
      (D xw m e).bind fun a => g (attSignOutP s.1 s.2 m e a) := by
  simp only [attSignP, PMF.bind_bind, PMF.bind_map, Function.comp_def]

theorem exists_mem_support_attSignP {s : G.Tables × Bool} {m : G.Msg}
    {o : G.Answer × (G.Tables × Bool)} (ho : o ∈ (attSignP D xw s m).support) :
    ∃ e, ∃ a ∈ (D xw m e).support, o = attSignOutP s.1 s.2 m e a := by
  simp only [attSignP, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at ho
  obtain ⟨e, _, a, ha, rfl⟩ := ho
  exact ⟨e, a, ha, rfl⟩

/-- Every transition of the game with the programmed flag extends the tables, by at
most one entry for a hash query and at most `μ` entries for a signing query. -/
theorem attStepP_support (s : G.Tables × Bool) (d : G.Query)
    (o : G.Answer × (G.Tables × Bool)) (ho : o ∈ (toOracle (attStepP D xw) s d).support) :
    s.1.Le o.2.1 ∧ o.2.1.size ≤ s.1.size + Sum.elim (fun _ => 1) (fun _ => G.μ) d := by
  cases d with
  | inl k => exact realStep_support xw s (.inl k) o ho
  | inr m =>
    obtain ⟨e, a, -, rfl⟩ := exists_mem_support_attSignP D xw ho
    exact attSignOut_support _ _ _ _ _

/-- The flag of a transition of the game with the programmed flag stays set. -/
theorem attStepP_flag (t : G.Tables) (d : G.Query) (o : G.Answer × (G.Tables × Bool))
    (ho : o ∈ (toOracle (attStepP D xw) (t, true) d).support) : o.2.2 = true := by
  cases d with
  | inl k => exact realStep_flag xw t (.inl k) o ho
  | inr m =>
    obtain ⟨e, a, -, rfl⟩ := exists_mem_support_attSignP D xw ho
    simp [attSignOutP, attSignOut]

theorem run_attP_support_le (A : OracleAdv G.Query G.Answer α)
    (s : G.Tables × Bool) (y : α × (G.Tables × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (attStepP D xw)) A s).support) : s.1.Le y.2.1 := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact Protocol.Tables.Le.refl _
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b s hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    exact (attStepP_support D xw s d o ho).1.trans (ih o.1 o.2 hy)

theorem run_attP_support_flag (A : OracleAdv G.Query G.Answer α)
    (s : G.Tables × Bool) (y : α × (G.Tables × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (attStepP D xw)) A s).support) (hs : s.2 = true) :
    y.2.2 = true := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact hs
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b s hb hs
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    obtain ⟨t, b⟩ := s
    dsimp only at hs
    subst hs
    exact ih o.1 o.2 hy (attStepP_flag D xw t d o ho)

/-- A run of the game with the programmed flag from tables in which `k₀` is defined
defines `k₀` at the end. -/
theorem run_attP_keys_eq_one (A : OracleAdv G.Query G.Answer α)
    (s : G.Tables × Bool) (k₀ : G.Key) (hk : k₀ ∈ s.1.keys) (E : Set (α × (G.Tables × Bool)))
    (hE : ∀ y, k₀ ∈ y.2.1.keys → y ∈ E) :
    (OracleAdv.run (toOracle (attStepP D xw)) A s).toOuterMeasure E = 1 :=
  toOuterMeasure_eq_one_of_support _ _ fun y hy =>
    hE y ((run_attP_support_le D xw A s y hy).keys_subset hk)

/-- A run of the game with the programmed flag started with the flag set gives a test
that is at least `1` on the outcomes with the flag set an expectation at least `1`. -/
theorem one_le_tsum_run_attP_flag (A : OracleAdv G.Query G.Answer α) (s : G.Tables × Bool)
    (hs : s.2 = true) (g : α × (G.Tables × Bool) → ℝ≥0∞) (hg : ∀ y, y.2.2 = true → 1 ≤ g y) :
    1 ≤ ∑' y, OracleAdv.run (toOracle (attStepP D xw)) A s y * g y := by
  calc (1 : ℝ≥0∞) = ∑' y, OracleAdv.run (toOracle (attStepP D xw)) A s y * 1 := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := ENNReal.tsum_le_tsum fun y => by
        by_cases hy : OracleAdv.run (toOracle (attStepP D xw)) A s y = 0
        · simp [hy]
        · exact mul_le_mul_right (hg y (run_attP_support_flag D xw A s y
            ((PMF.mem_support_iff _ _).mpr hy) hs)) _

/-- A run of the game with the programmed flag started with the flag set gives every
test of `offFlag` the value `0`. -/
theorem run_attP_offFlag_true (A : OracleAdv G.Query G.Answer α) (t : G.Tables)
    (g : α × (G.Tables × Bool) → ℝ≥0∞) :
    ∑' y, OracleAdv.run (toOracle (attStepP D xw)) A (t, true) y * offFlag g y = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun y => ?_
  obtain ⟨a, t', fl⟩ := y
  cases fl with
  | true => simp [offFlag]
  | false =>
    rw [OracleAdv.run_flag_apply_false_of_true _ (fun t d r t' =>
      (PMF.apply_eq_zero_iff _ _).mpr fun hx => Bool.noConfusion (attStepP_flag D xw t d _ hx)),
      zero_mul]

/-- A signing query in the induction of `run_attP_addRejs_flag_le`. -/
theorem run_attP_addRejs_sign_le (l : List (G.Key × G.Ch))
    (k : G.Answer → OracleAdv G.Query G.Answer α) (t : G.Tables) (m : G.Msg)
    (ih : ∀ c (t' : G.Tables) (b' : Bool),
      (OracleAdv.run (toOracle (attStepP D xw)) (k c) (t'.addRejs l, b')).toOuterMeasure
          {y | y.2.2 = true} ≤
        (OracleAdv.run (toOracle (attStepP D xw)) (k c) (t', b')).toOuterMeasure
          {y | y.2.2 = true ∨ ∃ p ∈ l, p.1 ∈ y.2.1.keys}) :
    (OracleAdv.run (toOracle (attStepP D xw)) (.query (.inr m) k)
        (t.addRejs l, false)).toOuterMeasure {y | y.2.2 = true} ≤
      (OracleAdv.run (toOracle (attStepP D xw)) (.query (.inr m) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true ∨ ∃ p ∈ l, p.1 ∈ y.2.1.keys} := by
  simp only [OracleAdv.run_query, toOracle, attStepP, Step.toPMF, attSignP_bind,
    PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun a => mul_le_mul_right ?_ _) _
  by_cases hc : ∃ i, a.key (a.vals t.lookupAll e) i ∈ l.map Prod.fst
  · obtain ⟨i, hi⟩ := hc
    obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hi
    refine (toOuterMeasure_le_one _ _).trans (le_of_eq
      (run_attP_keys_eq_one D xw _ _ p.1 ?_ _ fun y hy => Or.inr ⟨p, hp, hy⟩).symm)
    rw [hpk]
    exact attSignOut_key _ _ _ _ _ i
  · rw [attSignOutP_addRejs t false m e a l fun i hi => hc ⟨i, hi⟩]
    exact ih _ _ _

/-- **Hidden entries change the flag only where they are reached**, for the game with
the programmed flag. -/
theorem run_attP_addRejs_flag_le (l : List (G.Key × G.Ch))
    (A : OracleAdv G.Query G.Answer α) (t : G.Tables) (b : Bool) :
    (OracleAdv.run (toOracle (attStepP D xw)) A (t.addRejs l, b)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (OracleAdv.run (toOracle (attStepP D xw)) A (t, b)).toOuterMeasure
        {y | y.2.2 = true ∨ ∃ p ∈ l, p.1 ∈ y.2.1.keys} := by
  induction A generalizing t b with
  | ret a =>
    simp only [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    split_ifs with h1 h2 <;> first | exact le_rfl | exact zero_le | exact absurd (Or.inl h1) h2
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    exact ENNReal.tsum_le_tsum fun c => mul_le_mul_right (ih c t b) _
  | query d k ih =>
    by_cases hb : b = true ∨ ∃ p ∈ l, p.1 ∈ t.keys
    · refine (toOuterMeasure_le_one _ _).trans (le_of_eq ?_)
      refine (toOuterMeasure_eq_one_of_support _ _ fun y hy => ?_).symm
      rcases hb with hb | ⟨p, hp, hk⟩
      · exact Or.inl (run_attP_support_flag D xw _ (t, b) y hy hb)
      · exact Or.inr ⟨p, hp, (run_attP_support_le D xw _ (t, b) y hy).keys_subset hk⟩
    simp only [not_or, Bool.not_eq_true, not_exists, not_and] at hb
    obtain ⟨rfl, hk⟩ := hb
    cases d with
    | inl key =>
      by_cases hke : key ∈ l.map Prod.fst
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hke
        refine (toOuterMeasure_le_one _ _).trans (le_of_eq ?_)
        refine (toOuterMeasure_eq_one_of_support _ _ fun y hy => ?_).symm
        rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
        obtain ⟨o, ho, hy⟩ := hy
        exact Or.inr ⟨p, hp, (run_attP_support_le D xw _ o.2 y hy).keys_subset
          (realStep_key_inl xw _ _ o ho)⟩
      · rw [OracleAdv.run_query, OracleAdv.run_query, attStepP_inl, attStepP_inl,
          realStep_addRejs_inl xw l t false key hke,
          PMF.bind_map, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
        exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (ih o.1 o.2.1 o.2.2) _
    | inr m => exact run_attP_addRejs_sign_le D xw l k t m fun c => ih c

/-- Every transition of the game with the programmed flag at a sampler whose attempts
are in their classes adds at most `hashCost c d` points of class `c` for a hash query
and at most `μc c` for a signing query. -/
theorem attStepP_count_le (κ : G.Classes) (hκ : G.AttClassesAt κ D xw) (s : G.Tables × Bool)
    (d : G.Query) (o : G.Answer × (G.Tables × Bool))
    (ho : o ∈ (toOracle (attStepP D xw) s d).support) (c : κ.ι) :
    κ.count o.2.1.keys c ≤ κ.count s.1.keys c + κ.hashCost c d +
      Sum.elim (fun _ => 0) (fun _ => κ.μc c) d := by
  cases d with
  | inl k => exact realStep_count_le κ xw s (.inl k) o ho c
  | inr m =>
    obtain ⟨e, a, ha, rfl⟩ := exists_mem_support_attSignP D xw ho
    simpa [Protocol.Classes.hashCost, attSignOutP] using
      attSignOut_count_le κ s.1 s.2 m e (hκ m e a ha) c

/-- Along a run of the game with the programmed flag at a sampler whose attempts are in
their classes, with at most `q` signing queries and hash queries of total cost at most
`n` for the class `c`, the tables gain at most `n + μc c·q` points of class `c`. -/
theorem run_attP_support_size_cls (κ : G.Classes) (hκ : G.AttClassesAt κ D xw)
    (A : OracleAdv G.Query G.Answer α) (c : κ.ι) (h q n : ℕ) (hA : IsQueryBound₂ A h q)
    (hn : A.IsQueryBoundBy (κ.hashCost c) n) (s : G.Tables × Bool) (y : α × (G.Tables × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (attStepP D xw)) A s).support) :
    κ.count y.2.1.keys c ≤ κ.count s.1.keys c + n + κ.μc c * q := by
  induction A generalizing h q n s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    show κ.count s.1.keys c ≤ _
    omega
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b h q n (hA b) (hn b) s hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    have hs := attStepP_count_le D xw κ hκ s d o ho c
    obtain ⟨hn1, hn2⟩ := hn
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        have := ih o.1 h q _ (hA o.1) (hn2 o.1) o.2 hy
        simp only [Sum.elim_inl] at hs
        omega
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        have := ih o.1 h q _ (hA o.1) (hn2 o.1) o.2 hy
        simp only [Sum.elim_inr] at hs
        rw [Nat.mul_succ]
        omega

end ProgRun

/-! ## The witness sampler -/

section ProgWit

variable {G : Protocol} {α : Type}

/-- One real signing step against the signing step with the programmed flag of the
witness sampler, for a test `Y` of the outcome bounded by `1` and by `Y'`, with `Y'`
at least `1` on the outcomes with the flag set. -/
theorem realSign_le_witSignP (xw : G.Stmt × G.Wit) (s : G.Tables × Bool) (m : G.Msg)
    (Y Y' : G.Answer × (G.Tables × Bool) → ℝ≥0∞) (hY1 : ∀ o, Y o ≤ 1)
    (hY' : ∀ o, o.2.2 = true → 1 ≤ Y' o) (hY : ∀ o, Y o ≤ Y' o) :
    ∑' o, toOracle (realStep xw) s (.inr m) o * Y o ≤
      ∑' o, toOracle (attStepP G.witSampler xw) s (.inr m) o * Y' o := by
  obtain ⟨t, b⟩ := s
  simp only [toOracle, realStep, attStepP, attSignP, Protocol.witSampler, Step.toPMF, sampleVec,
    tsum_bind_mul, tsum_map_mul']
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _) _
  by_cases hc : progColl xw.1 xw.2 t m e r = true
  · refine (hY1 _).trans (hY' _ ?_)
    simp only [attSignOutP, progHit_witAttempt, hc, Bool.or_true]
  · have hc' : (G.witAttempt xw.1 xw.2 m r).progHit t e = false := by
      rw [progHit_witAttempt]
      simpa using hc
    rw [attSignOutP_of_progHit t b m e _ hc',
      ← realSignOut_eq_attSignOut xw.1 xw.2 t b m e r fun i hi => ?_]
    · exact hY _
    · simp only [progColl, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true, not_exists, not_and] at hc
      simpa using hc i hi

/-- **Identical until the flag, for runs.** A test `g` with values in `[0, 1]` of the
real run is at most the test `g' ≥ g` of the run with the programmed flag at the
witness sampler, when `g'` is at least `1` on the outcomes with the flag set. -/
theorem run_real_le_witP (xw : G.Stmt × G.Wit) (A : OracleAdv G.Query G.Answer α)
    (s : G.Tables × Bool) (g g' : α × (G.Tables × Bool) → ℝ≥0∞) (hg : ∀ y, g y ≤ 1)
    (hgg : ∀ y, g y ≤ g' y) (hg' : ∀ y, y.2.2 = true → 1 ≤ g' y) :
    ∑' y, OracleAdv.run (toOracle (realStep xw)) A s y * g y ≤
      ∑' y, OracleAdv.run (toOracle (attStepP G.witSampler xw)) A s y * g' y := by
  induction A generalizing s with
  | ret a =>
    simp only [OracleAdv.run_ret, tsum_pure_mul]
    exact hgg _
  | rand p k ih =>
    simp only [OracleAdv.run_rand, tsum_bind_mul]
    exact ENNReal.tsum_le_tsum fun c => mul_le_mul_right (ih c s) _
  | query d k ih =>
    simp only [OracleAdv.run_query, tsum_bind_mul]
    cases d with
    | inl key =>
      rw [attStepP_inl]
      exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (ih o.1 o.2) _
    | inr m =>
      refine realSign_le_witSignP xw s m _ _ (fun o => ?_)
        (fun o ho => one_le_tsum_run_attP_flag _ xw _ o.2 ho g' hg') fun o => ih o.1 o.2
      exact (ENNReal.tsum_le_tsum fun y => mul_le_of_le_one_right' (hg y)).trans
        (le_of_eq (PMF.tsum_coe _))

/-- **Programmed entries programmed, with the programmed flag.** For every protocol and
every adversary, the EUF-CMA advantage is at most the probability that the forgery
wins or the flag is set in the game with the programmed flag at the witness
sampler. -/
theorem Protocol.eufcma_le_witP {qH qS : ℕ} (A : G.Adversary qH qS) :
    eufcmaAdvantage A ≤ attAdvantageByP winsOrFlag G.witSampler A := by
  unfold eufcmaAdvantage attAdvantageByP eufcmaGame attGameByP
  rw [prTrue_gameDist, prTrue_gameDistBy]
  refine ENNReal.tsum_le_tsum fun xw => mul_le_mul_right ?_ _
  rw [toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite]
  refine run_real_le_witP xw _ _ _ (fun y => if winsOrFlag xw.1 y = true then 1 else 0)
    (fun y => by split_ifs <;> simp) (fun y => ?_) (fun y hy => ?_)
  · by_cases hw : wins xw.1 y = true
    · simp [winsOrFlag, hw]
    · simp [hw]
  · simp [winsOrFlag, hy]

end ProgWit

/-! ## The key bound of a sampler with programmed entries charged -/

namespace Protocol

variable (G : Protocol)

/-- **Class-wise key bound of a sampler at one pair, against oracles with at most `N`
defined points.** For the pair `xw`, every class `c`, every message, every oracle
`look` defined on at most `N` points and every randomized guesser `Q` on traces, the
expected number of charged entries of class `c` of an attempt from `D xw m e` against
`look` whose point the guess from `guessView` hits, under uniform values `e`, is at
most `Γ c`. -/
def AttKeyBoundClsAtN (κ : G.Classes) (N : ℕ) (D : G.Sampler) (xw : G.Stmt × G.Wit)
    (Γ : κ.ι → ℝ≥0∞) : Prop :=
  ∀ (c : κ.ι) (m : G.Msg) (look : G.Key → Option G.Ch),
    (∃ ks : List G.Key, ks.length ≤ N ∧ ∀ k, (look k).isSome → k ∈ ks) →
    ∀ (Q : G.Trace → PMF G.Key),
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
      ∑ i ∈ Finset.univ.filter (fun i => κ.ecls i = c),
        (if a.charged look e i then
          Q (a.guessView look e i) (a.key (a.vals look e) i) else 0) ≤ Γ c

variable {G}

/-- The class-wise key bound of the protocol at a pair is the key bound of the witness
sampler against every oracle. -/
theorem KeyBoundClsAt.attKeyBoundClsAtN_wit {κ : G.Classes} {x : G.Stmt} {w : G.Wit}
    {Γ : κ.ι → ℝ≥0∞} (h : G.KeyBoundClsAt κ x w Γ) (N : ℕ) :
    G.AttKeyBoundClsAtN κ N G.witSampler (x, w) Γ := by
  intro c m look _ Q
  simp only [witSampler, tsum_map_mul']
  exact h c m look Q

end Protocol

/-! ## The flag of the game with the programmed flag -/

section ProgFlagBound

variable {G : Protocol} {α : Type} (D : G.Sampler) (xw : G.Stmt × G.Wit)

/-- The rest of a run of the game with the programmed flag after a signing attempt on
`m` from `t` with the trace `tr`, the flag cleared and the hidden entries left out. -/
noncomputable def attContRunP (k : G.Answer → OracleAdv G.Query G.Answer α) (t : G.Tables)
    (m : G.Msg) (tr : G.Trace) : PMF (α × (G.Tables × Bool)) :=
  OracleAdv.run (toOracle (attStepP D xw)) (k (traceOut t false m tr).1)
    ((traceOut t false m tr).2.1, false)

/-- **Guessing the charged points of one class of an attempt.** For a sampler whose
attempts are in their classes with class-wise key bound `Γ` against oracles with at
most `N` defined points, an oracle `look` defined on at most `N` points, and runs
`R tr` indexed by traces whose final tables have at most `L` points of class `c` on the
traces `guessView` of the attempts of the sampler, the expectation over the values
and the attempts of the number of charged entries of class `c` whose point is defined
at the end of `R (guessView …)` is at most `L·Γ c`. -/
theorem tsum_attP_guess_le_cls (κ : G.Classes) {Γ : κ.ι → ℝ≥0∞} (hκ : G.AttClassesAt κ D xw)
    (N : ℕ) (hΓ : G.AttKeyBoundClsAtN κ N D xw Γ) (c : κ.ι) (m : G.Msg)
    (look : G.Key → Option G.Ch)
    (hlook : ∃ ks : List G.Key, ks.length ≤ N ∧ ∀ k, (look k).isSome → k ∈ ks)
    (R : G.Trace → PMF (α × (G.Tables × Bool))) (L : ℕ)
    (hL : ∀ e, ∀ a ∈ (D xw m e).support, ∀ i, ∀ y ∈ (R (a.guessView look e i)).support,
      κ.count y.2.1.keys c ≤ L) :
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
      ∑ i ∈ Finset.univ.filter (fun i => κ.ecls i = c), (if a.charged look e i then
        (R (a.guessView look e i)).toOuterMeasure
          {y | a.key (a.vals look e) i ∈ y.2.1.keys} else 0) ≤ L * Γ c := by
  rcases isEmpty_or_nonempty G.Key with hK | ⟨⟨k₀⟩⟩
  · refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun e => mul_eq_zero_of_right _
      (ENNReal.tsum_eq_zero.mpr fun a => mul_eq_zero_of_right _ ?_))) zero_le
    have : IsEmpty (Fin G.μ) := ⟨fun i => hK.false (a.key (fun _ => Classical.arbitrary _) i)⟩
    simp
  -- the guess of the `j`-th point of class `c` of the final tables
  let Q : ℕ → G.Trace → PMF G.Key := fun j tr =>
    (R tr).map fun y => (y.2.1.keys.filter fun k => κ.cls k = c).getD j k₀
  have h1 : ∀ e, ∀ a ∈ (D xw m e).support, ∀ i ∈ Finset.univ.filter (fun i => κ.ecls i = c),
      (if a.charged look e i then
        (R (a.guessView look e i)).toOuterMeasure
          {y | a.key (a.vals look e) i ∈ y.2.1.keys} else 0) ≤
      ∑ j ∈ Finset.range L, (if a.charged look e i then
        Q j (a.guessView look e i) (a.key (a.vals look e) i) else 0) := fun e a ha i hi => by
    split_ifs
    · refine le_trans (MeasureTheory.measure_mono fun y hy => ?_)
        (toOuterMeasure_mem_le_sum (R (a.guessView look e i))
          (fun y => y.2.1.keys.filter fun k => κ.cls k = c) L k₀
          (a.key (a.vals look e) i) (hL e a ha i))
      refine List.mem_filter.mpr ⟨hy, ?_⟩
      simpa [hκ m e a ha] using (Finset.mem_filter.mp hi).2
    · exact zero_le
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
        ∑ j ∈ Finset.range L, ∑ i ∈ Finset.univ.filter (fun i => κ.ecls i = c),
          (if a.charged look e i then
            Q j (a.guessView look e i) (a.key (a.vals look e) i) else 0) := by
        refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun a => ?_) _
        by_cases ha : D xw m e a = 0
        · simp [ha]
        refine mul_le_mul_right ?_ _
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun i hi => h1 e a ((PMF.mem_support_iff _ _).mpr ha) i hi
    _ = ∑ j ∈ Finset.range L, ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e *
          ∑' a, D xw m e a * ∑ i ∈ Finset.univ.filter (fun i => κ.ecls i = c),
            (if a.charged look e i then
              Q j (a.guessView look e i) (a.key (a.vals look e) i) else 0) :=
        tsum_mul_tsum_dep_finsetSum _ (fun e a => D xw m e a) _ _
    _ ≤ ∑ _j ∈ Finset.range L, Γ c := Finset.sum_le_sum fun j _ => hΓ c m look hlook (Q j)
    _ = L * Γ c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- One signing attempt in the induction of `run_attP_flag_le_cls`. -/
theorem attP_flag_sign_term_le_cls (κ : G.Classes) {Γ : κ.ι → ℝ≥0∞}
    (k : G.Answer → OracleAdv G.Query G.Answer α) (n : κ.ι → ℕ) (h q N : ℕ) (t : G.Tables)
    (ht : t.rej = []) (hN : t.size + G.μ + h + G.μ * q ≤ N) (m : G.Msg) (e : Fin G.μ → G.Ch)
    {a : G.Attempt} (hκ : ∀ v i, κ.cls (a.key v i) = κ.ecls i)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] → t'.size + h + G.μ * q ≤ N →
      (OracleAdv.run (toOracle (attStepP D xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ n q t') :
    (OracleAdv.run (toOracle (attStepP D xw)) (k (attSignOutP t false m e a).1)
        (attSignOutP t false m e a).2).toOuterMeasure {y | y.2.2 = true} ≤
      ∑ c, ((q * (κ.count t.keys c + κ.μc c + n c + κ.μc c * q) : ℕ) : ℝ≥0∞) * Γ c +
        ∑ i, (if a.charged t.lookup e i then
          (attContRunP D xw k t m (a.guessView t.lookup e i)).toOuterMeasure
            {y | a.key (a.vals t.lookup e) i ∈ y.2.1.keys} else 0) := by
  set v := a.vals t.lookup e with hv
  by_cases hc : ∃ i, a.charged t.lookup e i = true ∧ (t.lookup (a.key v i)).isSome
  · obtain ⟨i, hf, hi⟩ := hc
    refine (toOuterMeasure_le_one _ _).trans (le_trans ?_ le_add_self)
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun i =>
      if a.charged t.lookup e i then
        (attContRunP D xw k t m (a.guessView t.lookup e i)).toOuterMeasure
          {y | a.key v i ∈ y.2.1.keys} else 0) (fun _ _ => zero_le) (Finset.mem_univ i))
    have hg : a.guessView t.lookup e i = ([], [], none) := by
      simp only [Protocol.Attempt.guessView, ← hv, hi, Bool.or_true, if_true]
    simp only [hf, if_true, hg]
    refine (run_attP_keys_eq_one D xw _ _ _ ?_ _ fun y hy => hy).symm
    exact (le_traceOut t false m _).keys_subset (Protocol.lookup_isSome_mem_keys hi)
  have hc' : ∀ i, a.charged t.lookup e i = true → t.lookup (a.key v i) = none :=
    fun i hi => Option.isNone_iff_eq_none.mp (by
      cases hl : t.lookup (a.key v i)
      · rfl
      · exact absurd ⟨i, hi, by simp [hl]⟩ hc)
  have hpub : ∀ i, a.pub v i = false → t.lookup (a.key v i) = none := fun i hp =>
    hc' i (by simp [Protocol.Attempt.charged, ← hv, hp])
  have hfr : a.hidFresh t.lookup v = true := List.all_eq_true.mpr fun i _ => by
    cases hp : a.pub v i
    · simp [hpub i hp]
    · simp
  have hev : ∀ i, G.ev i = false → t.lookup (a.key v i) = none := fun i hi =>
    hc' i (by simp [Protocol.Attempt.charged, ← hv, hi, hfr])
  have hla : t.lookupAll = t.lookup := funext (Protocol.lookupAll_of_rej_nil ht)
  have hph : a.progHit t e = false := by
    simp only [Protocol.Attempt.progHit, hla, ← hv]
    refine List.any_eq_false.mpr fun i _ => ?_
    cases hi : G.ev i
    · simp [hev i hi]
    · simp
  rw [attSignOutP_of_progHit t false m e a hph, attSignOut_of_fresh t false m e a
    (fun i hf => (Protocol.lookupAll_of_rej_nil ht _).trans (hpub i hf))
    (fun i _ _ _ => by rw [ht]; exact lookupIn_nil _)]
  set T₀ : G.Tables := (traceOut t false m (a.trace v)).2.1
  have hT : ({ T₀ with rej := t.rej ++ a.hidEntries v } : G.Tables) =
      T₀.addRejs (a.hidEntries v) := by
    simp only [Protocol.Tables.addRejs, T₀, rej_traceOut, ht, List.nil_append,
      List.append_nil]
  have hT₀ : T₀.size ≤ t.size + G.μ := by
    have h1 := size_traceOut_le t false m (a.trace v)
    have h2 := a.length_entries v
    have h3 := rej_traceOut t false m (a.trace v)
    simp only [Protocol.Attempt.trace] at h1 h3
    simp only [Protocol.Tables.size, T₀, Protocol.Attempt.trace, h3]
    omega
  rw [hT]
  refine (run_attP_addRejs_flag_le D xw _ _ T₀ false).trans ?_
  refine (MeasureTheory.measure_mono (fun y hy => hy)).trans
    ((MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_))
  · refine (ih _ T₀ (by rw [rej_traceOut, ht]) (by omega)).trans
      (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right ?_ zero_le)
    have h1 : κ.count T₀.keys c ≤ κ.count t.keys c +
        κ.count ((a.evEntries v).map Prod.fst) c +
        κ.count ((a.pubEntries v).map Prod.fst) c :=
      count_traceOut_le κ t false m (a.trace v) c
    have h2 := Protocol.Attempt.count_trace_entries κ hκ v c
    exact_mod_cast Nat.mul_le_mul_left _ (by omega)
  · calc _ ≤ (attContRunP D xw k t m (a.trace v)).toOuterMeasure
            (⋃ i ∈ Finset.univ.filter (fun i => a.pub v i = false),
              {y | a.key v i ∈ y.2.1.keys}) := by
          refine MeasureTheory.measure_mono fun y hy => ?_
          obtain ⟨p, hp, hk⟩ := hy
          obtain ⟨i, hi, rfl⟩ := Protocol.Attempt.mem_entries hp
          simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨i, by simpa using hi, hk⟩
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => a.pub v i = false),
            (attContRunP D xw k t m (a.trace v)).toOuterMeasure
              {y | a.key v i ∈ y.2.1.keys} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ = ∑ i ∈ Finset.univ.filter (fun i => a.pub v i = false),
            (if a.charged t.lookup e i then
              (attContRunP D xw k t m (a.guessView t.lookup e i)).toOuterMeasure
                {y | a.key v i ∈ y.2.1.keys} else 0) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : a.pub v i = false := (Finset.mem_filter.mp hi).2
          have hch : a.charged t.lookup e i = true := by
            simp [Protocol.Attempt.charged, ← hv, hi']
          have hg : a.guessView t.lookup e i = a.trace v := by
            simp only [Protocol.Attempt.guessView, ← hv, hi', hpub i hi', Option.isSome_none,
              Bool.or_false, Bool.false_eq_true, if_false]
          rw [hch, if_pos rfl, hg]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- A hash query in the induction of `run_attP_flag_le_cls`. -/
theorem attP_flag_hash_step_le_cls (κ : G.Classes) {Γ : κ.ι → ℝ≥0∞}
    (k : G.Answer → OracleAdv G.Query G.Answer α) (n : κ.ι → ℕ) (h q N : ℕ) (t : G.Tables)
    (ht : t.rej = []) (hN : t.size + (h + 1) + G.μ * q ≤ N) (key : G.Key)
    (hn : ∀ c, κ.hashCost c (.inl key) ≤ n c)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] → t'.size + h + G.μ * q ≤ N →
      (OracleAdv.run (toOracle (attStepP D xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ (fun c => n c - κ.hashCost c (.inl key)) q t') :
    (OracleAdv.run (toOracle (attStepP D xw)) (.query (.inl key) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ n q t := by
  rw [OracleAdv.run_query]
  simp only [toOracle, attStepP, realHashStep]
  cases hl : t.lookup key with
  | some e =>
    simp only [Step.toPMF, PMF.pure_bind]
    refine (ih _ t ht (by omega)).trans
      (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right ?_ zero_le)
    exact_mod_cast Nat.mul_le_mul_left _ (by dsimp only; omega)
  | none =>
    have hr : lookupIn t.rej key = none := by rw [ht]; exact lookupIn_nil key
    simp only [hr, Step.toPMF, PMF.bind_map, Function.comp_def, PMF.toOuterMeasure_bind_apply]
    calc ∑' e, PMF.uniformOfFintype G.Ch e * (OracleAdv.run (toOracle (attStepP D xw))
          (k (.inl e)) ({ t with hash := t.hash ++ [(key, e)] }, false)).toOuterMeasure _
        ≤ ∑' e, PMF.uniformOfFintype G.Ch e * flagBoundCls κ Γ n q t := by
          refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
          have hs : ({ t with hash := t.hash ++ [(key, e)] } : G.Tables).size = t.size + 1 := by
            simp only [Protocol.Tables.size, List.length_append, List.length_singleton]
            omega
          refine (ih _ { t with hash := t.hash ++ [(key, e)] } ht (by omega)).trans
            (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right ?_ zero_le)
          have h1 := hn c
          have h2 := count_hash_append κ t key e c
          exact_mod_cast Nat.mul_le_mul_left _ (by dsimp only; omega)
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The guess terms of a signing attempt in the induction of `run_attP_flag_le_cls`:
the expectation over the values and the attempts of the number of charged entries
whose point is defined at the end of the rest of the run is at most
`Σ_c (L_c + μc c + n_c + μc c·q)·Γ c`. -/
theorem attP_flag_guess_le_cls (κ : G.Classes) {Γ : κ.ι → ℝ≥0∞} (hκ : G.AttClassesAt κ D xw)
    (N : ℕ) (hΓ : G.AttKeyBoundClsAtN κ N D xw Γ) (k : G.Answer → OracleAdv G.Query G.Answer α)
    (h q : ℕ) (n : κ.ι → ℕ) (hk : ∀ r, IsQueryBound₂ (k r) h q)
    (hn : ∀ c r, (k r).IsQueryBoundBy (κ.hashCost c) (n c)) (t : G.Tables) (htN : t.size ≤ N)
    (m : G.Msg) :
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
      ∑ i, (if a.charged t.lookup e i then
        (attContRunP D xw k t m (a.guessView t.lookup e i)).toOuterMeasure
          {y | a.key (a.vals t.lookup e) i ∈ y.2.1.keys} else 0) ≤
      ∑ c, ((κ.count t.keys c + κ.μc c + n c + κ.μc c * q : ℕ) : ℝ≥0∞) * Γ c := by
  simp only [← Finset.sum_fiberwise Finset.univ κ.ecls]
  rw [tsum_mul_tsum_dep_finsetSum]
  refine Finset.sum_le_sum fun c _ => ?_
  refine tsum_attP_guess_le_cls D xw κ hκ N hΓ c m t.lookup
    ⟨t.keys, by rw [Protocol.Tables.length_keys]; exact htN,
      fun _ hk' => Protocol.lookup_isSome_mem_keys hk'⟩
    (attContRunP D xw k t m) _ fun e a ha i y hy => ?_
  have h1 := run_attP_support_size_cls D xw κ hκ _ c h q (n c) (hk _) (hn c _) _ y hy
  have h2 := Protocol.Attempt.count_guessView_le κ (hκ m e a ha) t.lookup e i c
  have h3 := count_traceOut_le κ t false m (a.guessView t.lookup e i) c
  dsimp only at h1
  omega

/-- A signing query in the induction of `run_attP_flag_le_cls`. -/
theorem attP_flag_sign_step_le_cls (κ : G.Classes) {Γ : κ.ι → ℝ≥0∞}
    (hκ : G.AttClassesAt κ D xw) (N : ℕ) (hΓ : G.AttKeyBoundClsAtN κ N D xw Γ)
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ) (n : κ.ι → ℕ)
    (hk : ∀ r, IsQueryBound₂ (k r) h q)
    (hn : ∀ c r, (k r).IsQueryBoundBy (κ.hashCost c) (n c)) (t : G.Tables) (ht : t.rej = [])
    (hN : t.size + h + G.μ * (q + 1) ≤ N) (m : G.Msg)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] → t'.size + h + G.μ * q ≤ N →
      (OracleAdv.run (toOracle (attStepP D xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ n q t') :
    (OracleAdv.run (toOracle (attStepP D xw)) (.query (.inr m) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ n (q + 1) t := by
  rw [Nat.mul_succ] at hN
  set L : κ.ι → ℕ := fun c => κ.count t.keys c + κ.μc c + n c + κ.μc c * q with hL
  set B : ℝ≥0∞ := ∑ c, ((q * L c : ℕ) : ℝ≥0∞) * Γ c with hB
  -- the guess terms of the attempt `a` with the values `e`
  set S : (Fin G.μ → G.Ch) → G.Attempt → ℝ≥0∞ := fun e a =>
    ∑ i, (if a.charged t.lookup e i then
      (attContRunP D xw k t m (a.guessView t.lookup e i)).toOuterMeasure
        {y | a.key (a.vals t.lookup e) i ∈ y.2.1.keys} else 0) with hS
  have hterm : ∀ e a, a ∈ (D xw m e).support →
      (OracleAdv.run (toOracle (attStepP D xw)) (k (attSignOutP t false m e a).1)
        (attSignOutP t false m e a).2).toOuterMeasure {y | y.2.2 = true} ≤ B + S e a :=
    fun e a ha => attP_flag_sign_term_le_cls D xw κ k n h q N t ht (by omega) m e
      (hκ m e a ha) ih
  have hsum : ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e *
      ∑' a, D xw m e a * S e a ≤ ∑ c, (L c : ℝ≥0∞) * Γ c :=
    attP_flag_guess_le_cls D xw κ hκ N hΓ k h q n hk hn t (by omega) m
  rw [OracleAdv.run_query]
  simp only [toOracle, attStepP, Step.toPMF, attSignP_bind, PMF.toOuterMeasure_bind_apply]
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e *
        ∑' a, D xw m e a * (B + S e a) :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun a => by
            by_cases ha : D xw m e a = 0
            · simp [ha]
            · exact mul_le_mul_right (hterm e a ((PMF.mem_support_iff _ _).mpr ha)) _) _
    _ = B + ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e *
          ∑' a, D xw m e a * S e a := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ B + ∑ c, (L c : ℝ≥0∞) * Γ c := add_le_add_right hsum _
    _ = _ := by
        rw [hB, flagBoundCls, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hL]
        push_cast
        ring

/-- **Class-wise collision bound with the programmed flag.** For a sampler whose
attempts are in their classes with class-wise key bound `Γ` at the pair against
oracles with at most `N` defined points, from tables with no hidden entry, with `L_c`
points of class `c` and the flag cleared, a run of the game with the programmed flag
asking at most `h` hash and `q` signing queries, with hash queries of total cost at
most `n c` for each class `c`, and with `|t| + h + μ·q ≤ N`, sets the flag with
probability at most `Σ_c q·(L_c + n c + μc c·q)·Γ c`. -/
theorem run_attP_flag_le_cls (κ : G.Classes) {Γ : κ.ι → ℝ≥0∞} (hκ : G.AttClassesAt κ D xw)
    (N : ℕ) (hΓ : G.AttKeyBoundClsAtN κ N D xw Γ) (A : OracleAdv G.Query G.Answer α)
    (h q : ℕ) (hA : IsQueryBound₂ A h q) (n : κ.ι → ℕ)
    (hn : ∀ c, A.IsQueryBoundBy (κ.hashCost c) (n c)) (t : G.Tables) (ht : t.rej = [])
    (hN : t.size + h + G.μ * q ≤ N) :
    (OracleAdv.run (toOracle (attStepP D xw)) A (t, false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ n q t := by
  induction A generalizing h q n t with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (OracleAdv.run (toOracle (attStepP D xw)) (k b) (t, false)).toOuterMeasure _
        ≤ ∑' b, p b * flagBoundCls κ Γ n q t :=
          ENNReal.tsum_le_tsum fun b =>
            mul_le_mul_right (ih b h q (hA b) n (fun c => hn c b) t ht hN) _
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        exact attP_flag_hash_step_le_cls D xw κ k n h q N t ht hN key (fun c => (hn c).1)
          fun a t' ht' hN' => ih a h q (hA a) _ (fun c => (hn c).2 a) t' ht' hN'
    | inr m =>
      have hn' : ∀ c r, (k r).IsQueryBoundBy (κ.hashCost c) (n c) := fun c r => by
        simpa [Protocol.Classes.hashCost] using (hn c).2 r
      cases q with
      | zero => exact hA.elim
      | succ q =>
        exact attP_flag_sign_step_le_cls D xw κ hκ N hΓ k h q n hA hn' t ht hN m
          fun a t' ht' hN' => ih a h q (hA a) n (fun c => hn' c a) t' ht' hN'

end ProgFlagBound

/-! ## The statistical hop with the programmed flag -/

section ProgStat

variable {G : Protocol} {α : Type} (D : G.Sampler) (xw : G.Stmt × G.Wit)

/-- On the outcomes with the flag cleared, the signing answer with the programmed flag
is the signing answer of the attempt. -/
theorem offFlag_attSignOutP_le (F : G.Answer × (G.Tables × Bool) → ℝ≥0∞) (t : G.Tables)
    (b : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch) (a : G.Attempt) :
    offFlag F (attSignOutP t b m e a) ≤ offFlag F (attSignOut t b m e a) := by
  cases hp : a.progHit t e
  · rw [attSignOutP_of_progHit t b m e a hp]
  · simp [offFlag, attSignOutP, hp]

/-- A test of `offFlag` on one transition of the game with the programmed flag is at
most the test on one transition of the game at the sampler. -/
theorem attStepP_offFlag_le (s : G.Tables × Bool) (d : G.Query)
    (F : G.Answer × (G.Tables × Bool) → ℝ≥0∞) :
    ∑' o, toOracle (attStepP D xw) s d o * offFlag F o ≤
      ∑' o, toOracle (attStep D xw) s d o * offFlag F o := by
  cases d with
  | inl k => exact le_of_eq rfl
  | inr m =>
    simp only [toOracle, attStepP, attStep, Step.toPMF, attSignP, attSign, tsum_bind_mul,
      tsum_map_mul']
    exact ENNReal.tsum_le_tsum fun e => mul_le_mul_right (ENNReal.tsum_le_tsum fun a =>
      mul_le_mul_right (offFlag_attSignOutP_le F s.1 s.2 m e a) _) _

/-- A test of `offFlag` on a run of the game with the programmed flag is at most the
test on the run of the game at the sampler. -/
theorem run_attP_offFlag_le (A : OracleAdv G.Query G.Answer α) (s : G.Tables × Bool)
    (g : α × (G.Tables × Bool) → ℝ≥0∞) :
    ∑' y, OracleAdv.run (toOracle (attStepP D xw)) A s y * offFlag g y ≤
      ∑' y, OracleAdv.run (toOracle (attStep D xw)) A s y * offFlag g y := by
  induction A generalizing s with
  | ret a =>
    simp only [OracleAdv.run_ret, tsum_pure_mul]
    exact le_rfl
  | rand p k ih =>
    simp only [OracleAdv.run_rand, tsum_bind_mul]
    exact ENNReal.tsum_le_tsum fun c => mul_le_mul_right (ih c s) _
  | query d k ih =>
    simp only [OracleAdv.run_query, tsum_bind_mul]
    set Z : G.Answer × (G.Tables × Bool) → ℝ≥0∞ := fun o =>
      ∑' y, OracleAdv.run (toOracle (attStep D xw)) (k o.1) o.2 y * offFlag g y with hZ
    have hpt : ∀ o : G.Answer × (G.Tables × Bool),
        ∑' y, OracleAdv.run (toOracle (attStepP D xw)) (k o.1) o.2 y * offFlag g y ≤
          offFlag Z o := by
      rintro ⟨r, t, fl⟩
      cases fl with
      | true =>
        rw [run_attP_offFlag_true]
        exact zero_le
      | false => exact ih r (t, false)
    calc _ ≤ ∑' o, toOracle (attStepP D xw) s d o * offFlag Z o :=
          ENNReal.tsum_le_tsum fun o => mul_le_mul_right (hpt o) _
      _ ≤ ∑' o, toOracle (attStep D xw) s d o * offFlag Z o := attStepP_offFlag_le D xw s d Z
      _ ≤ _ := ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offFlag_le Z o) _

/-- The forgery wins or the flag is set in the game with the programmed flag with
probability at most winning in the simulated run, plus `q·δ`, plus the probability
that the run with the programmed flag sets the flag. -/
theorem run_attP_winsOrFlag_le_stat {δ : ℝ≥0∞} (hZK : G.AttHVZKAt D xw δ)
    (A : OracleAdv G.Query G.Answer G.Forgery) (h q : ℕ) (hA : IsQueryBound₂ A h q)
    (s : G.Tables × Bool) (x : G.Stmt) :
    (OracleAdv.run (toOracle (attStepP D xw)) A s).toOuterMeasure
        {y | winsOrFlag x y = true} ≤
      (OracleAdv.run (toOracle (simStep xw.1)) A s).toOuterMeasure {y | wins x y = true} +
        q * δ +
      (OracleAdv.run (toOracle (attStepP D xw)) A s).toOuterMeasure {y | y.2.2 = true} := by
  set g : G.Forgery × (G.Tables × Bool) → ℝ≥0∞ := fun y => if wins x y = true then 1 else 0
  have hg : ∀ y, g y ≤ 1 := fun y => by simp only [g]; split_ifs <;> simp
  have hgr : RejInsensitive g := fun _ _ => rfl
  have hgf : FlagInsensitive g := fun _ _ => rfl
  rw [toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite]
  calc _ ≤ ∑' y, OracleAdv.run (toOracle (attStepP D xw)) A s y *
          (offFlag g y + if y.2.2 = true then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun y => mul_le_mul_right ?_ _
        by_cases hf : y.2.2 = true <;> by_cases hw : wins x y = true <;>
          simp [offFlag, g, winsOrFlag, hf, hw]
    _ = ∑' y, OracleAdv.run (toOracle (attStepP D xw)) A s y * offFlag g y +
          ∑' y, OracleAdv.run (toOracle (attStepP D xw)) A s y *
            (if y.2.2 = true then 1 else 0) := by
        simp only [mul_add]
        rw [ENNReal.tsum_add]
    _ ≤ _ := add_le_add ((run_attP_offFlag_le D xw A s g).trans
        (run_att_le_sim D xw hZK A h q hA s g hg hgr hgf)) le_rfl

end ProgStat

/-! ## Signing-oracle simulation with the programmed flag -/

section ProgSim

variable {G : Protocol}

/-- **Signing-oracle simulation with the programmed flag, class by class.** For a
protocol with key classes `κ`, every adversary with at most `qH` hash and `qS` signing
queries whose hash queries at points of class `c` are at most `q c` on every path,
and a sampler whose generated pairs `xw` have statistical HVZK distance `δ xw`,
attempts in their classes and class-wise key bound `Γ xw` against oracles with at
most `qH + V + μ·qS` defined points, the probability that the forgery wins or the
flag is set in the game with the programmed flag at the sampler is at most the
simulated-game advantage plus the expectation over the generator of
`qS·δ(x, w) + Σ_c qS·(q c + Vc c + μc c·qS)·Γ(x, w) c`. -/
theorem Protocol.att_le_simP_cls (κ : G.Classes) (D : G.Sampler) {qH qS : ℕ}
    {δ : G.Stmt × G.Wit → ℝ≥0∞} {Γ : G.Stmt × G.Wit → κ.ι → ℝ≥0∞}
    (hZK : ∀ xw ∈ G.gen.support, G.AttHVZKAt D xw (δ xw))
    (hκ : ∀ xw ∈ G.gen.support, G.AttClassesAt κ D xw)
    (hΓ : ∀ xw ∈ G.gen.support, G.AttKeyBoundClsAtN κ (qH + G.V + G.μ * qS) D xw (Γ xw))
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ x c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) :
    attAdvantageByP winsOrFlag D A ≤ simAdvantage A +
      ∑' xw, G.gen xw * (qS * δ xw +
        ∑ c, ((qS * (q c + κ.Vc c + κ.μc c * qS) : ℕ) : ℝ≥0∞) * Γ xw c) := by
  unfold attAdvantageByP simAdvantage attGameByP simGame
  rw [prTrue_gameDistBy, prTrue_gameDist, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun xw => ?_
  rw [← mul_add]
  by_cases hxw : xw ∈ G.gen.support
  · have hB := isQueryBound₂_withVerify xw.1 _ qH qS (A.isQueryBound xw.1)
    refine mul_le_mul_right ?_ _
    refine (run_attP_winsOrFlag_le_stat D xw (hZK xw hxw) _ (qH + G.V) qS hB _ _).trans ?_
    rw [add_assoc]
    refine add_le_add le_rfl (add_le_add le_rfl ?_)
    refine (run_attP_flag_le_cls D xw κ (hκ xw hxw) _ (hΓ xw hxw) _ (qH + G.V) qS hB
      (fun c => q c + κ.Vc c) (fun c => isQueryBoundBy_withVerify_cls κ c xw.1 _ _ (hq xw.1 c))
      Protocol.Tables.empty rfl (by simp [Protocol.Tables.empty, Protocol.Tables.size])).trans
      (le_of_eq ?_)
    simp [flagBoundCls, Protocol.Tables.empty, Protocol.Tables.keys, Protocol.Classes.count]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hxw]

end ProgSim

end CatCrypt.Crypto.FiatShamirROM
