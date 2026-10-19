/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.KeyRecovery
public import CatCryptCore.Crypto.FiatShamirROM.KeyRecoveryMult

/-!
# Fiat–Shamir in the random-oracle model: IV multiplicity and the flag of the exempt game

Each signing attempt of a sampler has at most one entry of the class `c₀`, the IV
point of the attempt, and `ivOf` reads the IV off a point. The counts
`ivCnt κ c₀ ivOf t v` are the numbers of programmed and hidden entries of class `c₀`
in the tables `t` with the IV `v`. A hash query keeps the counts, and a signing query
adds at most one point, of the IV `v` with probability at most `p` when the sampler
draws the IV point with the IV `v` with probability at most `p` against every oracle
(`Protocol.AttIvFreshAt`). A run with at most `qS` signing queries of the exempt game
`attStepPR ρ D` or of the game with the programmed flag `attStepP D` therefore ends
with more than `K` IV points sharing an IV with probability at most
`C(qS, K + 1)·p^K`.

When every hidden entry of the sampler is of a marked class (`Protocol.AllHiddenR`),
the hidden entries stay in the tables of the exempt game and its hash queries never set
the flag. A signing query sets it only when a charged entry lands on a defined point,
charged by the class-wise key bound with marked classes, or when an evaluated public
entry lands on a hidden point, charged by the landing bound `Protocol.AttEvLandAt`. The
key bound and the landing bound are used on the oracles satisfying `B`; a predicate `Bt`
on tables that implies `B` and is inherited by smaller tables adds the probability that
the final tables fail `Bt`, and the IV multiplicity bound instantiates it.

The counts `entCnt κ c₀ π t v` are the numbers of distinct entries of class `c₀` among
all entries of the tables `t` whose projection under `π` is `v`. Every query of the
exempt game adds at most one such entry: a hash query at a fresh point of class `c₀`
with a uniform value, and a signing query with the entry of class `c₀` of its attempt
when that entry is programmed or at an undefined point. A run with at most `h` hash and
`q` signing queries therefore ends with more than `K` entries sharing a projection with
probability at most `C(h + q, K + 1)·p^K`, which instantiates `Bt` as well.

The EUF-CMA bound with key recovery chains the game with the programmed flag at the
witness sampler, the hybrid over the signing queries to the sampler `D`, the coupling
with the exempt game, the statistical hop to the simulated game for the test that the
forgery wins or the recovery succeeds, and the flag bound of the exempt game. A
successful recovery in the simulated game is a relation attack by the explicit
reduction `recReduction ρ dflt A`, which runs the adversary against the simulated
oracle and applies the recovery to the visible entries of the final tables.

## Main definitions

* `ivCnt κ c₀ ivOf t` — the counts per IV of the programmed and hidden entries of
  class `c₀` in the tables `t`
* `Protocol.AttIvFreshAt κ c₀ ivOf D xw p` — the sampler draws an IV point with a
  given IV with probability at most `p`, against every oracle
* `signCost` — the query cost `1` on signing queries and `0` on hash queries
* `entCnt κ c₀ π t` — the counts per projection of the distinct entries of class `c₀`
  in the tables `t`
* `Protocol.AttEntFreshAt κ c₀ π D xw p` — the sampler draws an entry of class `c₀`,
  programmed or at an undefined point, with a given projection with probability at most
  `p`, against every oracle
* `Protocol.AttEvLandAt ρ D xw N εev B` — an evaluated public entry of an attempt lands
  on one of given points of marked classes with probability at most `εev`, against the
  oracles satisfying `B`
* `Protocol.AllHiddenR ρ D xw` — every hidden entry of the sampler is of a marked class
* `RejMarked ρ t` — every hidden entry of the tables `t` is of a marked class
* `recReduction ρ dflt A` — the relation adversary that runs `A` with the verifier's
  queries against the simulated oracle and recovers a witness from the visible entries

## Main results

* `ivCnt_attSignOut` — a signing answer keeps the counts or adds one IV point
* `freshMult_attStepPR`, `freshMult_attStepP` — the exempt game and the game with
  the programmed flag satisfy `OracleAdv.FreshMult` for the counts `ivCnt`
* `run_attPR_not_ivMult_le`, `run_attP_not_ivMult_le` — a run with at most `qS`
  signing queries ends with more than `K` IV points sharing an IV with probability at
  most `C(qS, K + 1)·p^K`
* `entCnt_attSignOut` — a signing answer keeps the counts `entCnt` or adds one entry
* `card_le_entCnt` — points of class `c₀` defined in the tables with a given projection
  are at most `entCnt` many
* `freshMult_attStepPR_entCnt`, `run_attPR_not_entMult_le` — the exempt game satisfies
  `OracleAdv.FreshMult` for the counts `entCnt` with cost `1` per query, and a run with
  at most `h` hash and `q` signing queries ends with more than `K` entries sharing a
  projection with probability at most `C(h + q, K + 1)·p^K`
* `run_attPR_flag_le_cls` — a run of the exempt game sets the flag with probability at
  most `Σ_c q·(L_c + n c + μc c·q)·Γ c + q·εev` plus the probability that its final
  tables fail `Bt`
* `run_attPR_flag_le_cls_ivMult` — the same bound from the empty tables with the
  multiplicity bound `C(qS, K + 1)·p^K` in place of the last term
* `Protocol.sim_recTest_le_relAdvantage` — a successful recovery in the simulated game
  is bounded by the relation advantage of `recReduction ρ dflt A`
* `run_attPR_recR_le_sim`, `Protocol.attAdvantageByPR_recR_le_sim` — the exempt game
  decided by a winning forgery, the flag or a successful recovery against the simulated
  game, the recovery, `qS·δ` and the flag bound
* `Protocol.eufcma_le_simPRB_cls` — the EUF-CMA advantage is at most the simulated-game
  advantage plus the relation advantage of `recReduction ρ dflt A` plus the expectation
  of `qS·δ + Σ_c qS·(q c + Vc c + μc c·qS)·Γ c + qS·εev` and the probability that the
  final tables fail `Bt`, plus the hybrid advantages
* `Protocol.eufcma_le_simPRB_cls_ivMult` — the same bound with `C(qS, K + 1)·p^K` in
  place of the last expected term
* `Protocol.eufcma_le_simPRB_cls_entMult` — the same bound with
  `C(qH + V + qS, K + 1)·p^K` in place of the last expected term, for the multiplicity
  of entry values
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open scoped ENNReal

section IvMult

variable {G : Protocol} {V : Type} [DecidableEq V]

/-- The IVs of the entries of class `c₀` among the entries `l`. -/
def ivVals (κ : G.Classes) (c₀ : κ.ι) (ivOf : G.Key → V) (l : List (G.Key × G.Ch)) :
    List V :=
  (l.filter fun p => κ.cls p.1 = c₀).map fun p => ivOf p.1

/-- The counts per IV of the programmed and hidden entries of class `c₀` in the
tables `t`. -/
def ivCnt (κ : G.Classes) (c₀ : κ.ι) (ivOf : G.Key → V) (t : G.Tables) : V → ℕ :=
  fun v => (ivVals κ c₀ ivOf (t.prog ++ t.rej)).count v

/-- **Fresh IVs of a sampler.** For every message, every oracle `look` and every IV
`v`, an attempt from `D xw m e` under uniform values `e` has an entry of class `c₀`
against `look` with the IV `v` with probability at most `p`. -/
def Protocol.AttIvFreshAt (κ : G.Classes) (c₀ : κ.ι) (ivOf : G.Key → V) (D : G.Sampler)
    (xw : G.Stmt × G.Wit) (p : ℝ≥0∞) : Prop :=
  ∀ (m : G.Msg) (look : G.Key → Option G.Ch) (v : V),
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
      (if (List.finRange G.μ).any (fun i => decide (κ.cls (a.key (a.vals look e) i) = c₀) &&
          decide (ivOf (a.key (a.vals look e) i) = v)) then 1 else 0) ≤ p

/-- The query cost `1` on signing queries and `0` on hash queries. -/
def signCost : G.Query → ℕ := Sum.elim (fun _ => 0) fun _ => 1

theorem ivCnt_append (κ : G.Classes) (c₀ : κ.ι) (ivOf : G.Key → V) (t : G.Tables)
    (P H : List (G.Key × G.Ch)) (v : V) :
    (ivVals κ c₀ ivOf ((t.prog ++ P) ++ (t.rej ++ H))).count v =
      ivCnt κ c₀ ivOf t v + (ivVals κ c₀ ivOf (P ++ H)).count v := by
  simp only [ivCnt, ivVals, List.filter_append, List.map_append, List.count_append]
  omega

/-- The points of a sublist of the programmed public entries followed by a sublist of
the hidden entries of an attempt are distinct. -/
theorem Protocol.Attempt.nodup_pub_hid (a : G.Attempt) (w : Fin G.μ → G.Ch)
    {P H : List (G.Key × G.Ch)} (hP : P.Sublist (a.pubEntries w))
    (hH : H.Sublist (a.hidEntries w)) : ((P ++ H).map Prod.fst).Nodup := by
  refine ((hP.append hH).map Prod.fst).nodup ?_
  rw [List.map_append, List.nodup_append]
  refine ⟨a.nodup_entries w _, a.nodup_entries w _, fun x hx y hy hxy => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
  obtain ⟨i, hi, rfl⟩ := Protocol.Attempt.mem_entries hp
  obtain ⟨j, hj, rfl⟩ := Protocol.Attempt.mem_entries hq
  obtain rfl := a.key_inj w i j hxy
  simp_all

/-- **A signing answer adds at most one IV point.** For an attempt with at most one
entry of class `c₀`, the signing answer keeps the counts `ivCnt` or adds one point of
the IV of an entry of class `c₀`. -/
theorem ivCnt_attSignOut (κ : G.Classes) (c₀ : κ.ι) (ivOf : G.Key → V) (t : G.Tables)
    (b : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch) (a : G.Attempt)
    (hone : ∀ i j, κ.cls (a.key (a.vals t.lookupAll e) i) = c₀ →
      κ.cls (a.key (a.vals t.lookupAll e) j) = c₀ → i = j) :
    ivCnt κ c₀ ivOf (attSignOut t b m e a).2.1 = ivCnt κ c₀ ivOf t ∨
      ∃ i, κ.cls (a.key (a.vals t.lookupAll e) i) = c₀ ∧
        ivCnt κ c₀ ivOf (attSignOut t b m e a).2.1 =
          OracleAdv.addCnt (ivCnt κ c₀ ivOf t) (ivOf (a.key (a.vals t.lookupAll e) i)) := by
  set w := a.vals t.lookupAll e with hw
  obtain ⟨P, hP, hprog⟩ := programAll_prog_eq (hashAll t (a.trace w).1) b (a.trace w).2.1
  set H := (a.hidEntries w).filter fun p => (t.lookupAll p.1).isNone
  have hT : ivCnt κ c₀ ivOf (attSignOut t b m e a).2.1 =
      fun v => ivCnt κ c₀ ivOf t v + (ivVals κ c₀ ivOf (P ++ H)).count v := by
    funext v
    rw [← ivCnt_append]
    change (ivVals κ c₀ ivOf ((programAll (hashAll t (a.trace w).1) b (a.trace w).2.1).1.prog ++
      (t.rej ++ H))).count v = _
    rw [hprog]
    rfl
  have hHs : H.Sublist (a.hidEntries w) := List.filter_sublist
  have hnd := a.nodup_pub_hid w hP hHs
  set L := (P ++ H).filter fun p => κ.cls p.1 = c₀ with hL
  have hmem : ∀ x ∈ L, ∃ i, κ.cls (a.key w i) = c₀ ∧ x = (a.key w i, w i) := by
    intro x hx
    obtain ⟨hx, hc⟩ := List.mem_filter.mp hx
    have hx' : x ∈ a.pubEntries w ++ a.hidEntries w :=
      (hP.append hHs).subset hx
    obtain ⟨i, rfl⟩ : ∃ i, x = (a.key w i, w i) := by
      rcases List.mem_append.mp hx' with h | h
      · obtain ⟨i, -, h⟩ := Protocol.Attempt.mem_entries h
        exact ⟨i, h⟩
      · obtain ⟨i, -, h⟩ := Protocol.Attempt.mem_entries h
        exact ⟨i, h⟩
    exact ⟨i, by simpa using hc, rfl⟩
  cases hLe : L with
  | nil =>
    left
    rw [hT]
    funext v
    simp [ivVals, ← hL, hLe]
  | cons x l =>
    right
    obtain ⟨i, hi, rfl⟩ := hmem x (by rw [hLe]; exact List.mem_cons_self)
    have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons y l =>
        exfalso
        obtain ⟨j, hj, rfl⟩ := hmem y (by rw [hLe]; simp)
        obtain rfl := hone i j hi hj
        have : (L.map Prod.fst).Nodup := hnd.sublist ((List.filter_sublist : L.Sublist (P ++ H)).map _)
        rw [hLe] at this
        simp at this
    refine ⟨i, hi, ?_⟩
    rw [hT]
    funext v
    simp only [ivVals, ← hL, hLe, hl, List.map_cons, List.map_nil, OracleAdv.addCnt]
    by_cases hv : v = ivOf (a.key w i)
    · subst hv
      simp
    · simp [Function.update_of_ne hv, Ne.symm hv]

/-- Adding a point of the IV `w` and adding a point of the IV `v` give the same
counts only for `w = v`. -/
theorem addCnt_inj {c : V → ℕ} {w v : V} (h : OracleAdv.addCnt c w = OracleAdv.addCnt c v) :
    w = v := by
  by_contra hne
  have := congrFun h v
  simp [OracleAdv.addCnt, Function.update_of_ne (Ne.symm hne)] at this

/-- An attempt of a sampler whose attempts are in their classes, with at most one
entry of class `c₀`, has at most one entry of class `c₀` for all values. -/
theorem Protocol.AttClassesAt.eq_of_cls {κ : G.Classes} {D : G.Sampler}
    {xw : G.Stmt × G.Wit} (hκ : G.AttClassesAt κ D xw) {c₀ : κ.ι} (hμ : κ.μc c₀ ≤ 1)
    {m : G.Msg} {e : Fin G.μ → G.Ch} {a : G.Attempt} (ha : a ∈ (D xw m e).support)
    (w : Fin G.μ → G.Ch) (i j : Fin G.μ) (hi : κ.cls (a.key w i) = c₀)
    (hj : κ.cls (a.key w j) = c₀) : i = j :=
  Finset.card_le_one.mp hμ i (by simp [← hκ m e a ha w i, hi]) j
    (by simp [← hκ m e a ha w j, hj])

/-- **The point probability of a signing oracle.** A signing oracle drawing uniform
values `e` and an attempt from `D xw m e`, whose answers have the tables of
`attSignOut`, adds a point of the IV `v` with probability at most `p` for a sampler
with fresh IVs. -/
theorem sign_ivPoint_le {κ : G.Classes} {c₀ : κ.ι} {ivOf : G.Key → V} {D : G.Sampler}
    {xw : G.Stmt × G.Wit} {p : ℝ≥0∞} (hκ : G.AttClassesAt κ D xw) (hμ : κ.μc c₀ ≤ 1)
    (hp : G.AttIvFreshAt κ c₀ ivOf D xw p) (s : G.Tables × Bool) (m : G.Msg) (v : V)
    (f : (Fin G.μ → G.Ch) → G.Attempt → G.Answer × (G.Tables × Bool))
    (hf : ∀ e a, (f e a).2.1 = (attSignOut s.1 s.2 m e a).2.1) :
    ((PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind fun e => (D xw m e).map (f e)).toOuterMeasure
      {x | ivCnt κ c₀ ivOf x.2.1 = OracleAdv.addCnt (ivCnt κ c₀ ivOf s.1) v} ≤ p := by
  rw [PMF.toOuterMeasure_bind_apply]
  refine le_trans (ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _) (hp m s.1.lookupAll v)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hE : a ∈ f e ⁻¹' {x | ivCnt κ c₀ ivOf x.2.1 = OracleAdv.addCnt (ivCnt κ c₀ ivOf s.1) v}
  · rw [Set.indicator_of_mem hE]
    by_cases ha : D xw m e a = 0
    · simp [ha]
    have hcnt : ivCnt κ c₀ ivOf (attSignOut s.1 s.2 m e a).2.1 =
        OracleAdv.addCnt (ivCnt κ c₀ ivOf s.1) v := by
      rw [← hf]
      exact hE
    rcases ivCnt_attSignOut κ c₀ ivOf s.1 s.2 m e a
        (hκ.eq_of_cls hμ ((PMF.mem_support_iff _ _).mpr ha) _) with h | ⟨i, hi, h⟩
    · exact absurd (h.symm.trans hcnt) (OracleAdv.addCnt_ne _ _).symm
    · have hv := addCnt_inj (h.symm.trans hcnt)
      have hany : (List.finRange G.μ).any (fun i =>
          decide (κ.cls (a.key (a.vals s.1.lookupAll e) i) = c₀) &&
            decide (ivOf (a.key (a.vals s.1.lookupAll e) i) = v)) = true :=
        List.any_eq_true.mpr ⟨i, List.mem_finRange i, by simp [hi, hv]⟩
      rw [if_pos hany, mul_one]
  · rw [Set.indicator_of_notMem hE]
    exact zero_le

/-- A hash query of the exempt game keeps the programmed and hidden entries. -/
theorem attStepPR_inl_tables {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop}
    (ρ : G.Recovery κ rel) (D : G.Sampler) (xw : G.Stmt × G.Wit) (s : G.Tables × Bool)
    (k : G.Key) (x : G.Answer × (G.Tables × Bool))
    (hx : x ∈ (toOracle (attStepPR ρ D xw) s (.inl k)).support) :
    x.2.1.prog = s.1.prog ∧ x.2.1.rej = s.1.rej := by
  obtain ⟨t, b⟩ := s
  simp only [toOracle, attStepPR, realHashStepR] at hx
  cases hl : t.lookup k with
  | some c =>
    simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨rfl, rfl⟩
  | none =>
    cases hr : lookupIn t.rej k with
    | some c =>
      simp only [hl, hr, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨rfl, rfl⟩
    | none =>
      simp only [hl, hr, Step.toPMF, PMF.support_map, Set.mem_image] at hx
      obtain ⟨c, _, rfl⟩ := hx
      exact ⟨rfl, rfl⟩

/-- A hash query of the game with the programmed flag keeps the programmed and hidden
entries. -/
theorem attStepP_inl_tables (D : G.Sampler) (xw : G.Stmt × G.Wit) (s : G.Tables × Bool)
    (k : G.Key) (x : G.Answer × (G.Tables × Bool))
    (hx : x ∈ (toOracle (attStepP D xw) s (.inl k)).support) :
    x.2.1.prog = s.1.prog ∧ x.2.1.rej = s.1.rej := by
  obtain ⟨t, b⟩ := s
  simp only [toOracle, attStepP, realHashStep] at hx
  cases hl : t.lookup k with
  | some c =>
    simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨rfl, rfl⟩
  | none =>
    cases hr : lookupIn t.rej k with
    | some c =>
      simp only [hl, hr, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨rfl, rfl⟩
    | none =>
      simp only [hl, hr, Step.toPMF, PMF.support_map, Set.mem_image] at hx
      obtain ⟨c, _, rfl⟩ := hx
      exact ⟨rfl, rfl⟩

/-- A hash query that keeps the programmed and hidden entries adds no IV point. -/
theorem ivCnt_of_tables {κ : G.Classes} {c₀ : κ.ι} {ivOf : G.Key → V} {t t' : G.Tables}
    (h : t'.prog = t.prog ∧ t'.rej = t.rej) : ivCnt κ c₀ ivOf t' = ivCnt κ c₀ ivOf t := by
  unfold ivCnt
  rw [h.1, h.2]

/-- A hash query adds a point of the IV `v` with probability `0`. -/
theorem hash_ivPoint_eq_zero {κ : G.Classes} {c₀ : κ.ι} {ivOf : G.Key → V}
    (q : PMF (G.Answer × (G.Tables × Bool))) (s : G.Tables × Bool) (v : V)
    (hq : ∀ x ∈ q.support, x.2.1.prog = s.1.prog ∧ x.2.1.rej = s.1.rej) :
    q.toOuterMeasure {x | ivCnt κ c₀ ivOf x.2.1 = OracleAdv.addCnt (ivCnt κ c₀ ivOf s.1) v} =
      0 := by
  refine (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr (Set.disjoint_left.mpr fun x hx hE => ?_)
  exact OracleAdv.addCnt_ne (ivCnt κ c₀ ivOf s.1) v (hE.symm.trans (ivCnt_of_tables (hq x hx)))

variable {κ : G.Classes} {c₀ : κ.ι} {ivOf : G.Key → V} {D : G.Sampler}
  {xw : G.Stmt × G.Wit} {p : ℝ≥0∞}

/-- **Fresh IVs in the exempt game.** For a sampler whose attempts are in their
classes, with at most one entry of class `c₀` and fresh IVs, each query of the exempt
game adds at most one IV point, only on signing queries, and a point of a given IV
with probability at most `p`. -/
theorem freshMult_attStepPR {rel : G.Stmt → G.Wit → Prop} (ρ : G.Recovery κ rel)
    (hκ : G.AttClassesAt κ D xw) (hμ : κ.μc c₀ ≤ 1) (hp : G.AttIvFreshAt κ c₀ ivOf D xw p) :
    OracleAdv.FreshMult (toOracle (attStepPR ρ D xw)) signCost
      (fun s => ivCnt κ c₀ ivOf s.1) p where
  supp s d x hx := by
    cases d with
    | inl k => exact Or.inl (ivCnt_of_tables (attStepPR_inl_tables ρ D xw s k x hx))
    | inr m =>
      simp only [toOracle, attStepPR, Step.toPMF, attSignPR, PMF.mem_support_bind_iff,
        PMF.support_map, Set.mem_image] at hx
      obtain ⟨e, _, a, ha, rfl⟩ := hx
      rcases ivCnt_attSignOut κ c₀ ivOf s.1 s.2 m e a (hκ.eq_of_cls hμ ha _) with h | ⟨i, -, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨le_rfl, _, h⟩
  point s d v := by
    cases d with
    | inl k =>
      rw [hash_ivPoint_eq_zero _ s v fun x hx => attStepPR_inl_tables ρ D xw s k x hx]
      exact zero_le
    | inr m =>
      exact sign_ivPoint_le hκ hμ hp s m v _ fun _ _ => rfl

/-- **Fresh IVs in the game with the programmed flag.** For a sampler whose attempts
are in their classes, with at most one entry of class `c₀` and fresh IVs, each query
adds at most one IV point, only on signing queries, and a point of a given IV with
probability at most `p`. -/
theorem freshMult_attStepP (hκ : G.AttClassesAt κ D xw) (hμ : κ.μc c₀ ≤ 1)
    (hp : G.AttIvFreshAt κ c₀ ivOf D xw p) :
    OracleAdv.FreshMult (toOracle (attStepP D xw)) signCost
      (fun s => ivCnt κ c₀ ivOf s.1) p where
  supp s d x hx := by
    cases d with
    | inl k => exact Or.inl (ivCnt_of_tables (attStepP_inl_tables D xw s k x hx))
    | inr m =>
      obtain ⟨e, a, ha, rfl⟩ := exists_mem_support_attSignP D xw hx
      rcases ivCnt_attSignOut κ c₀ ivOf s.1 s.2 m e a (hκ.eq_of_cls hμ ha _) with h | ⟨i, -, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨le_rfl, _, h⟩
  point s d v := by
    cases d with
    | inl k =>
      rw [hash_ivPoint_eq_zero _ s v fun x hx => attStepP_inl_tables D xw s k x hx]
      exact zero_le
    | inr m =>
      exact sign_ivPoint_le hκ hμ hp s m v _ fun _ _ => rfl

/-- **Multiplicity of the IVs in the exempt game.** For a sampler whose attempts are
in their classes, with at most one entry of class `c₀` and fresh IVs with point
probability `p`, a run of the exempt game asking at most `qS` signing queries, from
tables with no IV point, ends with more than `K` IV points sharing an IV with
probability at most `C(qS, K + 1)·p^K`. -/
theorem run_attPR_not_ivMult_le [Fintype V] {α : Type} {rel : G.Stmt → G.Wit → Prop}
    (ρ : G.Recovery κ rel) (hκ : G.AttClassesAt κ D xw) (hμ : κ.μc c₀ ≤ 1)
    (hp : G.AttIvFreshAt κ c₀ ivOf D xw p) (K : ℕ) (A : OracleAdv G.Query G.Answer α)
    (qH qS : ℕ) (hA : IsQueryBound₂ A qH qS) (s : G.Tables × Bool)
    (hs : ivCnt κ c₀ ivOf s.1 = 0) :
    (OracleAdv.run (toOracle (attStepPR ρ D xw)) A s).toOuterMeasure
        {y | ¬ OracleAdv.MultB K (ivCnt κ c₀ ivOf y.2.1)} ≤ qS.choose (K + 1) * p ^ K :=
  OracleAdv.run_not_multB_le (freshMult_attStepPR ρ hκ hμ hp) K A qS
    (by simpa [signCost] using hA.isQueryBoundBy 0 1) s hs

/-- **Multiplicity of the IVs in the game with the programmed flag.** For a sampler
whose attempts are in their classes, with at most one entry of class `c₀` and fresh
IVs with point probability `p`, a run asking at most `qS` signing queries, from
tables with no IV point, ends with more than `K` IV points sharing an IV with
probability at most `C(qS, K + 1)·p^K`. -/
theorem run_attP_not_ivMult_le [Fintype V] {α : Type} (hκ : G.AttClassesAt κ D xw)
    (hμ : κ.μc c₀ ≤ 1) (hp : G.AttIvFreshAt κ c₀ ivOf D xw p) (K : ℕ) (A : OracleAdv G.Query G.Answer α)
    (qH qS : ℕ) (hA : IsQueryBound₂ A qH qS) (s : G.Tables × Bool)
    (hs : ivCnt κ c₀ ivOf s.1 = 0) :
    (OracleAdv.run (toOracle (attStepP D xw)) A s).toOuterMeasure
        {y | ¬ OracleAdv.MultB K (ivCnt κ c₀ ivOf y.2.1)} ≤ qS.choose (K + 1) * p ^ K :=
  OracleAdv.run_not_multB_le (freshMult_attStepP hκ hμ hp) K A qS
    (by simpa [signCost] using hA.isQueryBoundBy 0 1) s hs

/-- The empty tables have no IV point. -/
theorem ivCnt_empty (κ : G.Classes) (c₀ : κ.ι) (ivOf : G.Key → V) :
    ivCnt κ c₀ ivOf (Protocol.Tables.empty : G.Tables) = 0 := by
  funext v
  simp [ivCnt, ivVals, Protocol.Tables.empty]

/-- The counts `ivCnt` grow along extensions of the tables. -/
theorem ivCnt_le_of_le (κ : G.Classes) (c₀ : κ.ι) (ivOf : G.Key → V) {t t' : G.Tables}
    (h : t.Le t') (v : V) : ivCnt κ c₀ ivOf t v ≤ ivCnt κ c₀ ivOf t' v :=
  (((h.1.sublist.append h.2.2.sublist).filter _).map _).count_le v

end IvMult

/-! ## Multiplicity of the values of the entries of a class -/

section EntMult

variable {G : Protocol} {V : Type} [DecidableEq V]

/-- The counts per value `v` of the entries of class `c₀` in the set `S` whose
projection under `π` is `v`. -/
def setCnt (κ : G.Classes) (c₀ : κ.ι) (π : G.Key × G.Ch → V)
    (S : Finset (G.Key × G.Ch)) : V → ℕ :=
  fun v => (S.filter fun p => κ.cls p.1 = c₀ ∧ π p = v).card

/-- The counts per value `v` of the distinct entries of class `c₀` among the
programmed, hash and hidden entries of the tables `t` whose projection under `π` is
`v`. An entry recorded twice, in `hash` and in `rej`, counts once. -/
def entCnt (κ : G.Classes) (c₀ : κ.ι) (π : G.Key × G.Ch → V) (t : G.Tables) : V → ℕ :=
  setCnt κ c₀ π (t.prog ++ t.hash ++ t.rej).toFinset

/-- **Fresh entry values of a sampler.** For every message, every oracle `look` and
every value `v`, an attempt from `D xw m e` under uniform values `e` has an entry `i`
of class `c₀` against `look`, programmed or at a point undefined in `look`, with
projection `π (k, e i) = v` at its point `k` with probability at most `p`. -/
def Protocol.AttEntFreshAt (κ : G.Classes) (c₀ : κ.ι) (π : G.Key × G.Ch → V)
    (D : G.Sampler) (xw : G.Stmt × G.Wit) (p : ℝ≥0∞) : Prop :=
  ∀ (m : G.Msg) (look : G.Key → Option G.Ch) (v : V),
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
      (if (List.finRange G.μ).any (fun i => decide (κ.cls (a.key (a.vals look e) i) = c₀) &&
          (!G.ev i || (look (a.key (a.vals look e) i)).isNone) &&
          decide (π (a.key (a.vals look e) i, e i) = v)) then 1 else 0) ≤ p

/-- The value of an entry of an attempt that is programmed or at a point undefined in
`look` is its value in `e`. -/
theorem Protocol.Attempt.vals_eq_of_fresh (a : G.Attempt) (look : G.Key → Option G.Ch)
    (e : Fin G.μ → G.Ch) (i : Fin G.μ)
    (h : (!G.ev i || (look (a.key (a.vals look e) i)).isNone) = true) :
    a.vals look e i = e i := by
  cases hi : G.ev i
  · change effVal _ a.key e i = _
    rw [effVal_eq _ a.key a.key_causal e i, if_neg (by simp [hi])]
    rfl
  · rw [a.vals_of_ev look e i hi]
    simp only [hi, Bool.not_true, Bool.false_or, Option.isNone_iff_eq_none] at h
    rw [h, Option.getD_none]

/-- **Adding a set of entries with at most one entry of class `c₀`.** The counts of
`A ∪ N` are the counts of `A`, or the counts of `A` with one point added at the
projection of an entry of class `c₀` of `N` outside `A`. -/
theorem setCnt_union (κ : G.Classes) (c₀ : κ.ι) (π : G.Key × G.Ch → V)
    (A N : Finset (G.Key × G.Ch))
    (hN : ∀ y ∈ N, ∀ z ∈ N, κ.cls y.1 = c₀ → κ.cls z.1 = c₀ → y = z) :
    setCnt κ c₀ π (A ∪ N) = setCnt κ c₀ π A ∨
      ∃ x ∈ N, κ.cls x.1 = c₀ ∧ x ∉ A ∧
        setCnt κ c₀ π (A ∪ N) = OracleAdv.addCnt (setCnt κ c₀ π A) (π x) := by
  by_cases h : ∃ x ∈ N, κ.cls x.1 = c₀ ∧ x ∉ A
  · obtain ⟨x, hxN, hxc, hxA⟩ := h
    refine Or.inr ⟨x, hxN, hxc, hxA, funext fun v => ?_⟩
    by_cases hv : π x = v
    · subst hv
      have hf : (A ∪ N).filter (fun p => κ.cls p.1 = c₀ ∧ π p = π x) =
          insert x (A.filter fun p => κ.cls p.1 = c₀ ∧ π p = π x) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro ⟨hy | hy, hc, hπ⟩
          · exact Or.inr ⟨hy, hc, hπ⟩
          · exact Or.inl (hN y hy x hxN hc hxc)
        · rintro (rfl | ⟨hy, hc, hπ⟩)
          · exact ⟨Or.inr hxN, hxc, rfl⟩
          · exact ⟨Or.inl hy, hc, hπ⟩
      simp only [setCnt, hf, OracleAdv.addCnt, Function.update_self]
      rw [Finset.card_insert_of_notMem (by simp [hxA])]
    · have hf : (A ∪ N).filter (fun p => κ.cls p.1 = c₀ ∧ π p = v) =
          A.filter fun p => κ.cls p.1 = c₀ ∧ π p = v := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hy | hy, hc, hπ⟩
          · exact ⟨hy, hc, hπ⟩
          · obtain rfl := hN y hy x hxN hc hxc
            exact absurd hπ hv
        · rintro ⟨hy, hc, hπ⟩
          exact ⟨Or.inl hy, hc, hπ⟩
      simp only [setCnt, hf, OracleAdv.addCnt, Function.update_of_ne (Ne.symm hv)]
  · refine Or.inl (funext fun v => ?_)
    simp only [setCnt]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hy | hy, hc, hπ⟩
      · exact ⟨hy, hc, hπ⟩
      · refine ⟨?_, hc, hπ⟩
        by_contra hyA
        exact h ⟨y, hy, hc, hyA⟩
    · rintro ⟨hy, hc, hπ⟩
      exact ⟨Or.inl hy, hc, hπ⟩

/-- The empty tables have no entry. -/
theorem entCnt_empty (κ : G.Classes) (c₀ : κ.ι) (π : G.Key × G.Ch → V) :
    entCnt κ c₀ π (Protocol.Tables.empty : G.Tables) = 0 := by
  funext v
  simp [entCnt, setCnt, Protocol.Tables.empty]

/-- The counts `entCnt` grow along extensions of the tables. -/
theorem entCnt_le_of_le (κ : G.Classes) (c₀ : κ.ι) (π : G.Key × G.Ch → V) {t t' : G.Tables}
    (h : t.Le t') (v : V) : entCnt κ c₀ π t v ≤ entCnt κ c₀ π t' v := by
  unfold entCnt setCnt
  refine Finset.card_le_card (Finset.filter_subset_filter
    (fun p : G.Key × G.Ch => κ.cls p.1 = c₀ ∧ π p = v) fun x hx => ?_)
  simp only [List.mem_toFinset, List.mem_append] at hx ⊢
  rcases hx with (hx | hx) | hx
  · exact Or.inl (Or.inl (h.1.subset hx))
  · exact Or.inl (Or.inr (h.2.1.subset hx))
  · exact Or.inr (h.2.2.subset hx)

/-- **Points of class `c₀` with a given projection.** A finite set `S` of points of
class `c₀`, each defined in the tables `t` with a value whose projection with the
point under `π` is `v`, has at most `entCnt κ c₀ π t v` elements. -/
theorem card_le_entCnt (κ : G.Classes) (c₀ : κ.ι) (π : G.Key × G.Ch → V) (t : G.Tables)
    (v : V) (S : Finset G.Key)
    (hS : ∀ k ∈ S, κ.cls k = c₀ ∧ ∃ c, t.lookupAll k = some c ∧ π (k, c) = v) :
    S.card ≤ entCnt κ c₀ π t v := by
  unfold entCnt setCnt
  refine Finset.card_le_card_of_surjOn Prod.fst fun k hk => ?_
  obtain ⟨hc, c, hl, hπ⟩ := hS k hk
  refine ⟨(k, c), ?_, rfl⟩
  have hmem : (k, c) ∈ t.prog ++ t.hash ++ t.rej := by
    unfold Protocol.Tables.lookupAll at hl
    cases hl' : t.lookup k with
    | some c' =>
      rw [hl', Option.some_or] at hl
      cases hl
      exact List.mem_append_left _ (Protocol.mem_of_lookup_eq_some hl')
    | none =>
      rw [hl', Option.none_or] at hl
      exact List.mem_append_right _ (mem_of_lookupIn_eq_some hl)
  exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, hc, hπ⟩

/-- A hash entry `(k, c)` added to the tables keeps the counts `entCnt` or, for a
point `k` of class `c₀`, adds one point at `π (k, c)`; it keeps the counts when the
entry is already recorded. -/
theorem entCnt_hash_append (κ : G.Classes) (c₀ : κ.ι) (π : G.Key × G.Ch → V) (t : G.Tables)
    (k : G.Key) (c : G.Ch) :
    entCnt κ c₀ π { t with hash := t.hash ++ [(k, c)] } = entCnt κ c₀ π t ∨
      ((k, c) ∉ t.prog ++ t.hash ++ t.rej ∧ κ.cls k = c₀ ∧
        entCnt κ c₀ π { t with hash := t.hash ++ [(k, c)] } =
          OracleAdv.addCnt (entCnt κ c₀ π t) (π (k, c))) := by
  have hset : (t.prog ++ (t.hash ++ [(k, c)]) ++ t.rej).toFinset =
      (t.prog ++ t.hash ++ t.rej).toFinset ∪ {(k, c)} := by
    simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
      LawfulSingleton.insert_empty_eq]
    ac_rfl
  rcases setCnt_union κ c₀ π (t.prog ++ t.hash ++ t.rej).toFinset {(k, c)}
    (fun y hy z hz _ _ => (Finset.mem_singleton.mp hy).trans (Finset.mem_singleton.mp hz).symm)
    with h | ⟨x, hx, hxc, hxA, h⟩
  · exact Or.inl (by unfold entCnt; rw [hset, h])
  · obtain rfl := Finset.mem_singleton.mp hx
    exact Or.inr ⟨fun hm => hxA (List.mem_toFinset.mpr hm), hxc, by unfold entCnt; rw [hset, h]⟩

/-- **A signing answer adds at most one entry of class `c₀`.** For an attempt with at
most one entry of class `c₀`, the signing answer keeps the counts `entCnt` or adds one
point at the projection `π (k, e i)` of an entry `i` of class `c₀` at the point `k`,
programmed or at a point undefined in the tables. -/
theorem entCnt_attSignOut (κ : G.Classes) (c₀ : κ.ι) (π : G.Key × G.Ch → V) (t : G.Tables)
    (b : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch) (a : G.Attempt)
    (hone : ∀ i j, κ.cls (a.key (a.vals t.lookupAll e) i) = c₀ →
      κ.cls (a.key (a.vals t.lookupAll e) j) = c₀ → i = j) :
    entCnt κ c₀ π (attSignOut t b m e a).2.1 = entCnt κ c₀ π t ∨
      ∃ i, κ.cls (a.key (a.vals t.lookupAll e) i) = c₀ ∧
        (!G.ev i || (t.lookupAll (a.key (a.vals t.lookupAll e) i)).isNone) = true ∧
        entCnt κ c₀ π (attSignOut t b m e a).2.1 =
          OracleAdv.addCnt (entCnt κ c₀ π t) (π (a.key (a.vals t.lookupAll e) i, e i)) := by
  set w := a.vals t.lookupAll e with hw
  obtain ⟨P, hP, hprog⟩ := programAll_prog_eq (hashAll t (a.trace w).1) b (a.trace w).2.1
  set Hs := (a.evEntries w).filter fun p => (t.lookup p.1).isNone with hHs
  set H := (a.hidEntries w).filter fun p => (t.lookupAll p.1).isNone with hH
  set A := (t.prog ++ t.hash ++ t.rej).toFinset with hA
  have hset : ((attSignOut t b m e a).2.1.prog ++ (attSignOut t b m e a).2.1.hash ++
      (attSignOut t b m e a).2.1.rej).toFinset = A ∪ (P ++ Hs ++ H).toFinset := by
    have h1 : (attSignOut t b m e a).2.1.prog = t.prog ++ P := hprog
    have h2 : (attSignOut t b m e a).2.1.hash = t.hash ++ Hs :=
      (programAll_tables (hashAll t (a.trace w).1) b (a.trace w).2.1).1
    have h3 : (attSignOut t b m e a).2.1.rej = t.rej ++ H := rfl
    rw [h1, h2, h3]
    simp only [hA, List.toFinset_append]
    ac_rfl
  have hentry : ∀ x ∈ P ++ Hs ++ H, ∃ i, x = (a.key w i, w i) ∧
      (x ∉ A → (!G.ev i || (t.lookupAll (a.key w i)).isNone) = true) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨i, hi, rfl⟩ := Protocol.Attempt.mem_entries (hP.subset hx)
        refine ⟨i, rfl, fun _ => ?_⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi
        simp [hi.1]
      · obtain ⟨hx, hlk⟩ := List.mem_filter.mp hx
        obtain ⟨i, hi, rfl⟩ := Protocol.Attempt.mem_entries hx
        refine ⟨i, rfl, fun hxA => ?_⟩
        simp only [Bool.and_eq_true] at hi
        simp only [hi.1, Bool.not_true, Bool.false_or]
        cases hl : t.lookupAll (a.key w i) with
        | none => rfl
        | some c =>
          exfalso
          have hl0 : t.lookup (a.key w i) = none := by simpa using hlk
          have hr : lookupIn t.rej (a.key w i) = some c := by
            simpa [Protocol.Tables.lookupAll, hl0] using hl
          have hv : w i = c := by
            rw [hw, a.vals_of_ev t.lookupAll e i hi.1, ← hw, hl, Option.getD_some]
          refine hxA (List.mem_toFinset.mpr (List.mem_append_right _ ?_))
          rw [hv]
          exact mem_of_lookupIn_eq_some hr
    · obtain ⟨hx, hlk⟩ := List.mem_filter.mp hx
      obtain ⟨i, -, rfl⟩ := Protocol.Attempt.mem_entries hx
      exact ⟨i, rfl, fun _ => Bool.or_eq_true_iff.mpr (Or.inr hlk)⟩
  have hsub : ∀ y ∈ (P ++ Hs ++ H).toFinset, ∀ z ∈ (P ++ Hs ++ H).toFinset,
      κ.cls y.1 = c₀ → κ.cls z.1 = c₀ → y = z := by
    intro y hy z hz hyc hzc
    obtain ⟨i, rfl, -⟩ := hentry y (List.mem_toFinset.mp hy)
    obtain ⟨j, rfl, -⟩ := hentry z (List.mem_toFinset.mp hz)
    obtain rfl := hone i j hyc hzc
    rfl
  unfold entCnt
  rw [hset]
  rcases setCnt_union κ c₀ π A _ hsub with h | ⟨x, hx, hxc, hxA, h⟩
  · exact Or.inl h
  · obtain ⟨i, rfl, hg⟩ := hentry x (List.mem_toFinset.mp hx)
    refine Or.inr ⟨i, hxc, hg hxA, ?_⟩
    rw [h, ← a.vals_eq_of_fresh t.lookupAll e i (hg hxA)]

/-- **The point probability of a signing oracle for entry values.** A signing oracle
drawing uniform values `e` and an attempt from `D xw m e`, whose answers have the
tables of `attSignOut`, adds a point at the value `v` with probability at most `p` for
a sampler with fresh entry values. -/
theorem sign_entPoint_le {κ : G.Classes} {c₀ : κ.ι} {π : G.Key × G.Ch → V} {D : G.Sampler}
    {xw : G.Stmt × G.Wit} {p : ℝ≥0∞} (hκ : G.AttClassesAt κ D xw) (hμ : κ.μc c₀ ≤ 1)
    (hp : G.AttEntFreshAt κ c₀ π D xw p) (s : G.Tables × Bool) (m : G.Msg) (v : V)
    (f : (Fin G.μ → G.Ch) → G.Attempt → G.Answer × (G.Tables × Bool))
    (hf : ∀ e a, (f e a).2.1 = (attSignOut s.1 s.2 m e a).2.1) :
    ((PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind fun e => (D xw m e).map (f e)).toOuterMeasure
      {x | entCnt κ c₀ π x.2.1 = OracleAdv.addCnt (entCnt κ c₀ π s.1) v} ≤ p := by
  rw [PMF.toOuterMeasure_bind_apply]
  refine le_trans (ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _) (hp m s.1.lookupAll v)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hE : a ∈ f e ⁻¹' {x | entCnt κ c₀ π x.2.1 = OracleAdv.addCnt (entCnt κ c₀ π s.1) v}
  · rw [Set.indicator_of_mem hE]
    by_cases ha : D xw m e a = 0
    · simp [ha]
    have hcnt : entCnt κ c₀ π (attSignOut s.1 s.2 m e a).2.1 =
        OracleAdv.addCnt (entCnt κ c₀ π s.1) v := by
      rw [← hf]
      exact hE
    rcases entCnt_attSignOut κ c₀ π s.1 s.2 m e a
        (hκ.eq_of_cls hμ ((PMF.mem_support_iff _ _).mpr ha) _) with h | ⟨i, hi, hg, h⟩
    · exact absurd (h.symm.trans hcnt) (OracleAdv.addCnt_ne _ _).symm
    · have hv := addCnt_inj (h.symm.trans hcnt)
      have hany : (List.finRange G.μ).any (fun i =>
          decide (κ.cls (a.key (a.vals s.1.lookupAll e) i) = c₀) &&
            (!G.ev i || (s.1.lookupAll (a.key (a.vals s.1.lookupAll e) i)).isNone) &&
            decide (π (a.key (a.vals s.1.lookupAll e) i, e i) = v)) = true :=
        List.any_eq_true.mpr ⟨i, List.mem_finRange i, by simp [hi, hg, hv]⟩
      rw [if_pos hany, mul_one]
  · rw [Set.indicator_of_notMem hE]
    exact zero_le

/-- **The point probability of a hash query of the exempt game for entry values.** When
a uniform value `c` at a point `k` of class `c₀` has projection `π (k, c) = v` with
probability at most `p`, a hash query adds a point at the value `v` with probability at
most `p`. -/
theorem hash_entPoint_le {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop} {c₀ : κ.ι}
    {π : G.Key × G.Ch → V} {p : ℝ≥0∞} (ρ : G.Recovery κ rel) (D : G.Sampler)
    (xw : G.Stmt × G.Wit)
    (hpH : ∀ k, κ.cls k = c₀ → ∀ v,
      (PMF.uniformOfFintype G.Ch).toOuterMeasure {c | π (k, c) = v} ≤ p)
    (s : G.Tables × Bool) (k : G.Key) (v : V) :
    (toOracle (attStepPR ρ D xw) s (.inl k)).toOuterMeasure
      {x | entCnt κ c₀ π x.2.1 = OracleAdv.addCnt (entCnt κ c₀ π s.1) v} ≤ p := by
  obtain ⟨t, b⟩ := s
  simp only [toOracle, attStepPR, realHashStepR]
  cases hl : t.lookup k with
  | some c =>
    simp only [Step.toPMF, PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq]
    rw [if_neg fun h => OracleAdv.addCnt_ne _ _ h.symm]
    exact zero_le
  | none =>
    cases hr : lookupIn t.rej k with
    | some c =>
      simp only [Step.toPMF, PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq]
      rw [if_neg]
      · exact zero_le
      intro h
      rcases entCnt_hash_append κ c₀ π t k c with h' | ⟨hm, -, -⟩
      · exact OracleAdv.addCnt_ne _ _ (h.symm.trans h')
      · exact hm (List.mem_append_right _ (mem_of_lookupIn_eq_some hr))
    | none =>
      simp only [Step.toPMF, PMF.toOuterMeasure_map_apply]
      by_cases hc : κ.cls k = c₀
      · refine le_trans (MeasureTheory.measure_mono fun c hc' => ?_) (hpH k hc v)
        simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hc' ⊢
        rcases entCnt_hash_append κ c₀ π t k c with h | ⟨-, -, h⟩
        · exact absurd (h.symm.trans hc') (OracleAdv.addCnt_ne _ _).symm
        · exact addCnt_inj (h.symm.trans hc')
      · refine le_of_eq_of_le ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
          (Set.disjoint_left.mpr fun c _ hc' => ?_)) zero_le
        simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hc'
        rcases entCnt_hash_append κ c₀ π t k c with h | ⟨-, h, -⟩
        · exact OracleAdv.addCnt_ne _ _ (hc'.symm.trans h)
        · exact hc h

variable {κ : G.Classes} {c₀ : κ.ι} {π : G.Key × G.Ch → V} {D : G.Sampler}
  {xw : G.Stmt × G.Wit} {p : ℝ≥0∞}

/-- **Fresh entry values in the exempt game.** For a sampler whose attempts are in
their classes, with at most one entry of class `c₀` and fresh entry values, and uniform
hash answers at points of class `c₀` with point probability `p`, each query of the
exempt game adds at most one point to the counts `entCnt`, at a given value with
probability at most `p`. -/
theorem freshMult_attStepPR_entCnt {rel : G.Stmt → G.Wit → Prop} (ρ : G.Recovery κ rel)
    (hκ : G.AttClassesAt κ D xw) (hμ : κ.μc c₀ ≤ 1) (hp : G.AttEntFreshAt κ c₀ π D xw p)
    (hpH : ∀ k, κ.cls k = c₀ → ∀ v,
      (PMF.uniformOfFintype G.Ch).toOuterMeasure {c | π (k, c) = v} ≤ p) :
    OracleAdv.FreshMult (toOracle (attStepPR ρ D xw)) (fun _ => 1)
      (fun s => entCnt κ c₀ π s.1) p where
  supp s d x hx := by
    cases d with
    | inl k =>
      obtain ⟨t, b⟩ := s
      simp only [toOracle, attStepPR, realHashStepR] at hx
      cases hl : t.lookup k with
      | some c =>
        simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hx
        subst hx
        exact Or.inl rfl
      | none =>
        cases hr : lookupIn t.rej k with
        | some c =>
          simp only [hl, hr, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hx
          subst hx
          rcases entCnt_hash_append κ c₀ π t k c with h | ⟨hm, -, -⟩
          · exact Or.inl h
          · exact absurd (List.mem_append_right _ (mem_of_lookupIn_eq_some hr)) hm
        | none =>
          simp only [hl, hr, Step.toPMF, PMF.support_map, Set.mem_image] at hx
          obtain ⟨c, _, rfl⟩ := hx
          rcases entCnt_hash_append κ c₀ π t k c with h | ⟨-, -, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨le_rfl, _, h⟩
    | inr m =>
      simp only [toOracle, attStepPR, Step.toPMF, attSignPR, PMF.mem_support_bind_iff,
        PMF.support_map, Set.mem_image] at hx
      obtain ⟨e, _, a, ha, rfl⟩ := hx
      rcases entCnt_attSignOut κ c₀ π s.1 s.2 m e a (hκ.eq_of_cls hμ ha _) with
        h | ⟨i, -, -, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨le_rfl, _, h⟩
  point s d v := by
    cases d with
    | inl k => exact hash_entPoint_le ρ D xw hpH s k v
    | inr m => exact sign_entPoint_le hκ hμ hp s m v _ fun _ _ => rfl

/-- **Multiplicity of the entry values in the exempt game.** For a sampler whose
attempts are in their classes, with at most one entry of class `c₀` and fresh entry
values, and uniform hash answers at points of class `c₀`, with point probability `p`,
a run of the exempt game asking at most `h` hash and `q` signing queries, from tables
with no entry of class `c₀`, ends with more than `K` entries of class `c₀` sharing a
projection with probability at most `C(h + q, K + 1)·p^K`. -/
theorem run_attPR_not_entMult_le [Fintype V] {α : Type} {rel : G.Stmt → G.Wit → Prop}
    (ρ : G.Recovery κ rel) (hκ : G.AttClassesAt κ D xw) (hμ : κ.μc c₀ ≤ 1)
    (hp : G.AttEntFreshAt κ c₀ π D xw p)
    (hpH : ∀ k, κ.cls k = c₀ → ∀ v,
      (PMF.uniformOfFintype G.Ch).toOuterMeasure {c | π (k, c) = v} ≤ p)
    (K : ℕ) (A : OracleAdv G.Query G.Answer α) (h q : ℕ) (hA : IsQueryBound₂ A h q)
    (s : G.Tables × Bool) (hs : entCnt κ c₀ π s.1 = 0) :
    (OracleAdv.run (toOracle (attStepPR ρ D xw)) A s).toOuterMeasure
        {y | ¬ OracleAdv.MultB K (entCnt κ c₀ π y.2.1)} ≤ (h + q).choose (K + 1) * p ^ K :=
  OracleAdv.run_not_multB_le (freshMult_attStepPR_entCnt ρ hκ hμ hp hpH) K A (h + q)
    (by
      have h1 := (hA.isQueryBoundBy 1 1).of_cost_le (cost' := fun _ => 1)
        (fun d => by cases d <;> exact le_rfl)
      simpa using h1) s hs

end EntMult

/-! ## The flag of the exempt game -/

section RecFlag

variable {G : Protocol} {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop} {α : Type}

theorem lookupIn_isSome_of_mem {K C : Type} [DecidableEq K] {l : List (K × C)} {k : K}
    (h : k ∈ l.map Prod.fst) : (lookupIn l k).isSome := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    by_cases hk : k = p.1
    · subst hk
      simp [lookupIn, findKey, List.findIdx?_cons]
    · rw [lookupIn_cons_of_ne p l hk]
      rw [List.map_cons, List.mem_cons] at h
      exact ih (h.resolve_left hk)

/-- **Evaluated public entries landing on hidden points, for a sampler, over the oracles
satisfying `B`.** For every message, every oracle `look` satisfying `B` and defined on
at most `N` points and every list `hs` of points of marked classes defined in `look`,
an attempt from `D xw m e` under uniform values `e` has an evaluated public entry
against `look` at a point of `hs` with probability at most `εev`. -/
def Protocol.AttEvLandAt (ρ : G.Recovery κ rel) (D : G.Sampler) (xw : G.Stmt × G.Wit)
    (N : ℕ) (εev : ℝ≥0∞) (B : (G.Key → Option G.Ch) → Prop) : Prop :=
  ∀ (m : G.Msg) (look : G.Key → Option G.Ch), B look →
    (∃ ks : List G.Key, ks.length ≤ N ∧ ∀ k, (look k).isSome → k ∈ ks) →
    ∀ hs : List G.Key, (∀ k ∈ hs, ρ.R (κ.cls k) = true ∧ (look k).isSome = true) →
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
      (if (List.finRange G.μ).any (fun i => G.ev i && a.pub (a.vals look e) i &&
          decide (a.key (a.vals look e) i ∈ hs)) then 1 else 0) ≤ εev

/-- **The hidden entries of a sampler are of marked classes.** Every hidden entry of
every attempt from `D xw m e`, for all values, is of a marked class. -/
def Protocol.AllHiddenR (ρ : G.Recovery κ rel) (D : G.Sampler) (xw : G.Stmt × G.Wit) :
    Prop :=
  ∀ (m : G.Msg) (e : Fin G.μ → G.Ch), ∀ a ∈ (D xw m e).support,
    ∀ (v : Fin G.μ → G.Ch) (i : Fin G.μ), a.pub v i = false → ρ.R (κ.cls (a.key v i)) = true

/-- The hidden entries of the tables `t` are of marked classes. -/
def RejMarked (ρ : G.Recovery κ rel) (t : G.Tables) : Prop :=
  ∀ p ∈ t.rej, ρ.R (κ.cls p.1) = true

variable (ρ : G.Recovery κ rel) (D : G.Sampler) (xw : G.Stmt × G.Wit)

/-- A transition of the exempt game has the answer and tables of a transition of the
game with the programmed flag. -/
theorem attStepPR_support_attStepP (s : G.Tables × Bool) (d : G.Query)
    (o : G.Answer × (G.Tables × Bool)) (ho : o ∈ (toOracle (attStepPR ρ D xw) s d).support) :
    ∃ o' ∈ (toOracle (attStepP D xw) s d).support, o'.1 = o.1 ∧ o'.2.1 = o.2.1 := by
  obtain ⟨t, b⟩ := s
  cases d with
  | inl k =>
    simp only [toOracle, attStepPR, attStepP, realHashStepR, realHashStep] at ho ⊢
    cases hl : t.lookup k with
    | some c =>
      simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho ⊢
      subst ho
      exact ⟨_, rfl, rfl, rfl⟩
    | none =>
      cases hr : lookupIn t.rej k with
      | some c =>
        simp only [hl, hr, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho ⊢
        subst ho
        exact ⟨_, rfl, rfl, rfl⟩
      | none =>
        simp only [hl, hr, Step.toPMF, PMF.support_map, Set.mem_image] at ho ⊢
        obtain ⟨c, hc, rfl⟩ := ho
        exact ⟨_, ⟨c, hc, rfl⟩, rfl, rfl⟩
  | inr m =>
    simp only [toOracle, attStepPR, Step.toPMF, attSignPR, PMF.mem_support_bind_iff,
      PMF.support_map, Set.mem_image] at ho
    obtain ⟨e, he, a, ha, rfl⟩ := ho
    refine ⟨attSignOutP t b m e a, ?_, rfl, rfl⟩
    simp only [toOracle, attStepP, Step.toPMF, attSignP, PMF.mem_support_bind_iff,
      PMF.support_map, Set.mem_image]
    exact ⟨e, he, a, ha, rfl⟩

/-- A run of the exempt game extends the tables. -/
theorem run_attPR_support_le (A : OracleAdv G.Query G.Answer α) (s : G.Tables × Bool)
    (y : α × (G.Tables × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (attStepPR ρ D xw)) A s).support) : s.1.Le y.2.1 := by
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
    obtain ⟨o', ho', -, h2⟩ := attStepPR_support_attStepP ρ D xw s d o ho
    exact ((attStepP_support D xw s d o' ho').1.trans (h2 ▸ Protocol.Tables.Le.refl _)).trans
      (ih o.1 o.2 hy)

/-- A hash query in the induction of `run_attPR_flagB_le_cls`. -/
theorem attPR_flag_hash_step_le {Γ : κ.ι → ℝ≥0∞} (εev : ℝ≥0∞)
    (E : Set (α × (G.Tables × Bool))) (k : G.Answer → OracleAdv G.Query G.Answer α)
    (n : κ.ι → ℕ) (h q N : ℕ) (t : G.Tables) (ht : RejMarked ρ t)
    (hN : t.size + (h + 1) + G.μ * q ≤ N) (key : G.Key)
    (hn : ∀ c, κ.hashCost c (.inl key) ≤ n c)
    (ih : ∀ c (t' : G.Tables), RejMarked ρ t' → t'.size + h + G.μ * q ≤ N →
      (OracleAdv.run (toOracle (attStepPR ρ D xw)) (k c) (t', false)).toOuterMeasure E ≤
        flagBoundCls κ Γ (fun c => n c - κ.hashCost c (.inl key)) q t' + q * εev) :
    (OracleAdv.run (toOracle (attStepPR ρ D xw)) (.query (.inl key) k) (t, false)).toOuterMeasure
        E ≤ flagBoundCls κ Γ n q t + q * εev := by
  have hmono : ∀ t' : G.Tables,
      (∀ c, κ.count t'.keys c ≤ κ.count t.keys c + κ.hashCost c (.inl key)) →
      flagBoundCls κ Γ (fun c => n c - κ.hashCost c (.inl key)) q t' + q * εev ≤
        flagBoundCls κ Γ n q t + q * εev := fun t' ht' =>
    add_le_add (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (by
      have h1 := ht' c
      have h2 := hn c
      exact_mod_cast Nat.mul_le_mul_left q (by dsimp only; omega)) zero_le) le_rfl
  have hs : ∀ e, ({ t with hash := t.hash ++ [(key, e)] } : G.Tables).size = t.size + 1 :=
    fun e => by
      simp only [Protocol.Tables.size, List.length_append, List.length_singleton]
      omega
  rw [OracleAdv.run_query]
  simp only [toOracle, attStepPR, realHashStepR]
  cases hl : t.lookup key with
  | some e =>
    simp only [Step.toPMF, PMF.pure_bind]
    exact (ih _ t ht (by omega)).trans (hmono t fun c => Nat.le_add_right _ _)
  | none =>
    cases hr : lookupIn t.rej key with
    | some c =>
      have hR : ρ.R (κ.cls key) = true := ht _ (mem_of_lookupIn_eq_some hr)
      simp only [Step.toPMF, PMF.pure_bind, hR, Bool.not_true, Bool.or_false]
      exact (ih _ { t with hash := t.hash ++ [(key, c)] } ht (by rw [hs]; omega)).trans
        (hmono _ fun c' => (count_hash_append κ t key c c').le)
    | none =>
      simp only [Step.toPMF, PMF.bind_map, Function.comp_def, PMF.toOuterMeasure_bind_apply]
      calc ∑' e, PMF.uniformOfFintype G.Ch e * (OracleAdv.run (toOracle (attStepPR ρ D xw))
            (k (.inl e)) ({ t with hash := t.hash ++ [(key, e)] }, false)).toOuterMeasure E
          ≤ ∑' e, PMF.uniformOfFintype G.Ch e * (flagBoundCls κ Γ n q t + q * εev) :=
            ENNReal.tsum_le_tsum fun e => mul_le_mul_right
              ((ih _ { t with hash := t.hash ++ [(key, e)] } ht (by rw [hs]; omega)).trans
              (hmono _ fun c' => (count_hash_append κ t key e c').le)) _
        _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Charged entries of an attempt at defined points.** For a sampler whose attempts
are in their classes with the class-wise key bound `Γ` with marked classes over the
oracles satisfying `B` with at most `N` defined points, and tables `t` with at most
`N` entries whose oracle satisfies `B`, the expected number of charged entries of an
attempt against `t.lookupAll` at points defined in `t` is at most
`Σ_c L_c·Γ c`, with `L_c` the points of class `c` in `t`. -/
theorem tsum_attPR_hit_le_cls {Γ : κ.ι → ℝ≥0∞} {B : (G.Key → Option G.Ch) → Prop} {N : ℕ}
    (hκ : G.AttClassesAt κ D xw) (hΓ : G.AttKeyBoundClsAtNRB ρ N D xw Γ B) (m : G.Msg)
    (t : G.Tables) (hB : B t.lookupAll) (htN : t.size ≤ N) :
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
      ∑ i, (if a.charged t.lookupAll e i &&
          (t.lookupAll (a.key (a.vals t.lookupAll e) i)).isSome then (1 : ℝ≥0∞) else 0) ≤
      ∑ c, (κ.count t.keys c : ℝ≥0∞) * Γ c := by
  rcases isEmpty_or_nonempty G.Key with hK | ⟨⟨k₀⟩⟩
  · refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun e => mul_eq_zero_of_right _
      (ENNReal.tsum_eq_zero.mpr fun a => mul_eq_zero_of_right _ ?_))) zero_le
    have : IsEmpty (Fin G.μ) := ⟨fun i => hK.false (a.key (fun _ => Classical.arbitrary _) i)⟩
    simp
  simp only [← Finset.sum_fiberwise Finset.univ κ.ecls]
  rw [tsum_mul_tsum_dep_finsetSum]
  refine Finset.sum_le_sum fun c _ => ?_
  set look := t.lookupAll with hlook
  set L := κ.count t.keys c with hL
  -- the guess of the `j`-th point of class `c` of the tables
  let Q : ℕ → G.Trace → PMF G.Key := fun j _ =>
    (PMF.pure ()).map fun _ => (t.keys.filter fun k => κ.cls k = c).getD j k₀
  have h1 : ∀ e, ∀ a ∈ (D xw m e).support, ∀ i ∈ Finset.univ.filter (fun i => κ.ecls i = c),
      (if a.charged look e i && (look (a.key (a.vals look e) i)).isSome then (1 : ℝ≥0∞)
        else 0) ≤
      ∑ j ∈ Finset.range L, (if a.charged look e i &&
          (!ρ.R (κ.ecls i) || (look (a.key (a.vals look e) i)).isSome) then
        Q j (a.guessView look e i) (a.key (a.vals look e) i) else 0) := fun e a ha i hi => by
    by_cases hch : (a.charged look e i && (look (a.key (a.vals look e) i)).isSome) = true
    · have hch' : (a.charged look e i &&
          (!ρ.R (κ.ecls i) || (look (a.key (a.vals look e) i)).isSome)) = true := by
        simp only [Bool.and_eq_true, Bool.or_eq_true] at hch ⊢
        exact ⟨hch.1, Or.inr hch.2⟩
      rw [if_pos hch]
      simp only [hch', if_true]
      have hmem : a.key (a.vals look e) i ∈ t.keys.filter fun k => κ.cls k = c := by
        simp only [Bool.and_eq_true] at hch
        refine List.mem_filter.mpr ⟨Protocol.lookupAll_isSome_mem hch.2, ?_⟩
        simpa [hκ m e a ha] using (Finset.mem_filter.mp hi).2
      calc (1 : ℝ≥0∞) = (PMF.pure ()).toOuterMeasure
            {y | a.key (a.vals look e) i ∈ (fun _ : Unit => t.keys.filter fun k => κ.cls k = c) y} := by
            rw [PMF.toOuterMeasure_pure_apply, if_pos (show () ∈ _ from hmem)]
        _ ≤ _ := toOuterMeasure_mem_le_sum _ _ L k₀ _ fun _ _ => le_rfl
    · rw [if_neg hch]
      exact zero_le
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
        ∑ j ∈ Finset.range L, ∑ i ∈ Finset.univ.filter (fun i => κ.ecls i = c),
          (if a.charged look e i &&
              (!ρ.R (κ.ecls i) || (look (a.key (a.vals look e) i)).isSome) then
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
            (if a.charged look e i &&
                (!ρ.R (κ.ecls i) || (look (a.key (a.vals look e) i)).isSome) then
              Q j (a.guessView look e i) (a.key (a.vals look e) i) else 0) :=
        tsum_mul_tsum_dep_finsetSum _ (fun e a => D xw m e a) _ _
    _ ≤ ∑ _j ∈ Finset.range L, Γ c := Finset.sum_le_sum fun j _ => hΓ c m look hB
          ⟨t.keys, by rw [Protocol.Tables.length_keys]; exact htN,
            fun _ hk' => Protocol.lookupAll_isSome_mem hk'⟩ (Q j)
    _ = L * Γ c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- One signing attempt in the induction of `run_attPR_flagB_le_cls`: the probability
that the rest of the run sets the flag is at most the number of charged entries at
defined points, plus `1` when an evaluated public entry lands on a hidden point, plus
the bound for the tables after the attempt. -/
theorem attPR_flag_sign_term_le {Γ : κ.ι → ℝ≥0∞} {εev : ℝ≥0∞} (hR : G.AllHiddenR ρ D xw)
    (Bt : G.Tables → Prop) (k : G.Answer → OracleAdv G.Query G.Answer α) (n : κ.ι → ℕ)
    (h q N : ℕ) (t : G.Tables) (ht : RejMarked ρ t) (hN : t.size + G.μ + h + G.μ * q ≤ N)
    (m : G.Msg) (e : Fin G.μ → G.Ch) {a : G.Attempt} (ha : a ∈ (D xw m e).support)
    (hκa : ∀ v i, κ.cls (a.key v i) = κ.ecls i)
    (ih : ∀ c (t' : G.Tables), RejMarked ρ t' → t'.size + h + G.μ * q ≤ N →
      (OracleAdv.run (toOracle (attStepPR ρ D xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true ∧ Bt y.2.1} ≤ flagBoundCls κ Γ n q t' + q * εev) :
    (OracleAdv.run (toOracle (attStepPR ρ D xw)) (k (attSignOutPR ρ t false m e a).1)
        (attSignOutPR ρ t false m e a).2).toOuterMeasure {y | y.2.2 = true ∧ Bt y.2.1} ≤
      ∑ i, (if a.charged t.lookupAll e i &&
          (t.lookupAll (a.key (a.vals t.lookupAll e) i)).isSome then (1 : ℝ≥0∞) else 0) +
        (if (List.finRange G.μ).any (fun i => G.ev i && a.pub (a.vals t.lookupAll e) i &&
            decide (a.key (a.vals t.lookupAll e) i ∈ t.rej.map Prod.fst)) then 1 else 0) +
        (∑ c, ((q * (κ.count t.keys c + κ.μc c + n c + κ.μc c * q) : ℕ) : ℝ≥0∞) * Γ c +
          q * εev) := by
  set look := t.lookupAll with hlook
  set v := a.vals look e with hv
  by_cases hc : ∃ i, a.charged look e i = true ∧ (look (a.key v i)).isSome = true
  · obtain ⟨i, hi1, hi2⟩ := hc
    refine (toOuterMeasure_le_one _ _).trans (le_add_right (le_add_right ?_))
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun i =>
      if a.charged look e i && (look (a.key v i)).isSome then (1 : ℝ≥0∞) else 0)
      (fun _ _ => zero_le) (Finset.mem_univ i))
    simp [hi1, hi2]
  simp only [not_exists, not_and, Bool.not_eq_true] at hc
  have hhid : ∀ i, a.pub v i = false → (look (a.key v i)).isSome = false := fun i hp =>
    hc i (by simp [Protocol.Attempt.charged, ← hv, hp])
  have hfr : a.hidFresh look v = true := List.all_eq_true.mpr fun i _ => by
    cases hp : a.pub v i
    · simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using hhid i hp
    · simp
  have hprog : ∀ i, G.ev i = false → (look (a.key v i)).isSome = false := fun i hi =>
    hc i (by simp [Protocol.Attempt.charged, ← hv, hi, hfr])
  set o := attSignOutPR ρ t false m e a with ho
  cases hf : o.2.2 with
  | true =>
    refine (toOuterMeasure_le_one _ _).trans (le_add_right (le_trans ?_ le_add_self))
    have hEv : (List.finRange G.μ).any (fun i => G.ev i && a.pub v i &&
        decide (a.key v i ∈ t.rej.map Prod.fst)) = true := by
      have hf' : attFlagR ρ t e a = true := by simpa [o, attSignOutPR] using hf
      simp only [attFlagR, ← hlook, ← hv, Bool.or_eq_true, List.any_eq_true, List.mem_finRange,
        true_and] at hf'
      rcases hf' with ⟨i, hi⟩ | ⟨i, hi⟩
      · cases hp : a.pub v i
        · simp only [hp, Bool.false_eq_true, if_false] at hi
          exact absurd hi (by simp [hhid i hp])
        · simp only [hp, if_true, Bool.and_eq_true] at hi
          obtain ⟨⟨hev, -⟩, hrej⟩ := hi
          exact List.any_eq_true.mpr ⟨i, List.mem_finRange i,
            by simp [hev, hp, lookupIn_isSome_mem hrej]⟩
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi
        obtain ⟨⟨hev, hsome⟩, -⟩ := hi
        exact absurd hsome (by simp [hprog i hev])
    rw [if_pos hEv]
  | false =>
    have ho2 : o.2 = ((attSignOut t false m e a).2.1, false) := Prod.ext rfl hf
    rw [ho2]
    refine le_trans ?_ le_add_self
    have hT := attSignOut_support t false m e a
    refine (ih _ _ ?_ (by omega)).trans (add_le_add (Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_right ?_ zero_le) le_rfl)
    · intro p hp
      change p ∈ t.rej ++ _ at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ht p hp
      · obtain ⟨j, hj, rfl⟩ := Protocol.Attempt.mem_entries (List.mem_filter.mp hp).1
        simp only [Bool.not_eq_true'] at hj
        exact hR m e a ha _ j hj
    · have := attSignOut_count_le κ t false m e hκa c
      exact_mod_cast Nat.mul_le_mul_left q (by omega)

/-- A signing query in the induction of `run_attPR_flagB_le_cls`. -/
theorem attPR_flag_sign_step_le {Γ : κ.ι → ℝ≥0∞} {B : (G.Key → Option G.Ch) → Prop}
    {εev : ℝ≥0∞} (hκ : G.AttClassesAt κ D xw) (hR : G.AllHiddenR ρ D xw) (N : ℕ)
    (hΓ : G.AttKeyBoundClsAtNRB ρ N D xw Γ B) (hev : G.AttEvLandAt ρ D xw N εev B)
    (Bt : G.Tables → Prop) (hBt : ∀ t, Bt t → B t.lookupAll)
    (hBmono : ∀ t t' : G.Tables, t.Le t' → Bt t' → Bt t)
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ) (n : κ.ι → ℕ) (t : G.Tables)
    (ht : RejMarked ρ t) (hN : t.size + h + G.μ * (q + 1) ≤ N) (m : G.Msg)
    (ih : ∀ c (t' : G.Tables), RejMarked ρ t' → t'.size + h + G.μ * q ≤ N →
      (OracleAdv.run (toOracle (attStepPR ρ D xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true ∧ Bt y.2.1} ≤ flagBoundCls κ Γ n q t' + q * εev) :
    (OracleAdv.run (toOracle (attStepPR ρ D xw)) (.query (.inr m) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true ∧ Bt y.2.1} ≤ flagBoundCls κ Γ n (q + 1) t + ((q + 1 : ℕ) : ℝ≥0∞) * εev := by
  rw [Nat.mul_succ] at hN
  by_cases hB : Bt t
  swap
  · refine le_trans (le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
      (Set.disjoint_left.mpr fun y hy hE =>
        hB (hBmono _ _ (run_attPR_support_le ρ D xw _ _ y hy) hE.2)))) zero_le
  have hhs : ∀ k' ∈ t.rej.map Prod.fst,
      ρ.R (κ.cls k') = true ∧ (t.lookupAll k').isSome = true := by
    intro k' hk'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk'
    refine ⟨ht p hp, ?_⟩
    unfold Protocol.Tables.lookupAll
    cases hl : t.lookup p.1 with
    | some _ => rfl
    | none => simpa using lookupIn_isSome_of_mem hk'
  have hlookN : ∃ ks : List G.Key, ks.length ≤ N ∧ ∀ k, (t.lookupAll k).isSome → k ∈ ks :=
    ⟨t.keys, by rw [Protocol.Tables.length_keys]; omega,
      fun _ hk' => Protocol.lookupAll_isSome_mem hk'⟩
  set S : (Fin G.μ → G.Ch) → G.Attempt → ℝ≥0∞ := fun e a =>
    ∑ i, (if a.charged t.lookupAll e i &&
      (t.lookupAll (a.key (a.vals t.lookupAll e) i)).isSome then (1 : ℝ≥0∞) else 0) with hS
  set Ev : (Fin G.μ → G.Ch) → G.Attempt → ℝ≥0∞ := fun e a =>
    if (List.finRange G.μ).any (fun i => G.ev i && a.pub (a.vals t.lookupAll e) i &&
      decide (a.key (a.vals t.lookupAll e) i ∈ t.rej.map Prod.fst)) then 1 else 0 with hEv
  set B0 : ℝ≥0∞ :=
    ∑ c, ((q * (κ.count t.keys c + κ.μc c + n c + κ.μc c * q) : ℕ) : ℝ≥0∞) * Γ c +
      q * εev with hB0
  have hterm : ∀ e a, a ∈ (D xw m e).support →
      (OracleAdv.run (toOracle (attStepPR ρ D xw)) (k (attSignOutPR ρ t false m e a).1)
        (attSignOutPR ρ t false m e a).2).toOuterMeasure {y | y.2.2 = true ∧ Bt y.2.1} ≤
        S e a + Ev e a + B0 :=
    fun e a ha => attPR_flag_sign_term_le ρ D xw hR Bt k n h q N t ht (by omega) m e ha
      (hκ m e a ha) ih
  have hsumS : ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a * S e a ≤
      ∑ c, (κ.count t.keys c : ℝ≥0∞) * Γ c :=
    tsum_attPR_hit_le_cls ρ D xw hκ hΓ m t (hBt t hB) (by omega)
  have hsumEv : ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a * Ev e a ≤
      εev := hev m t.lookupAll (hBt t hB) hlookN _ hhs
  rw [OracleAdv.run_query]
  simp only [toOracle, attStepPR, Step.toPMF, attSignPR, PMF.bind_bind, PMF.bind_map,
    Function.comp_def, PMF.toOuterMeasure_bind_apply]
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e *
        ∑' a, D xw m e a * (S e a + Ev e a + B0) :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun a => by
            by_cases ha : D xw m e a = 0
            · simp [ha]
            · exact mul_le_mul_right (hterm e a ((PMF.mem_support_iff _ _).mpr ha)) _) _
    _ = (∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a * S e a) +
          (∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a * Ev e a) + B0 := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ (∑ c, (κ.count t.keys c : ℝ≥0∞) * Γ c) + εev + B0 :=
        add_le_add (add_le_add hsumS hsumEv) le_rfl
    _ ≤ _ := by
        have h1 : ∑ c, (κ.count t.keys c : ℝ≥0∞) * Γ c +
            ∑ c, ((q * (κ.count t.keys c + κ.μc c + n c + κ.μc c * q) : ℕ) : ℝ≥0∞) * Γ c ≤
            flagBoundCls κ Γ n (q + 1) t := by
          rw [flagBoundCls, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun c _ => ?_
          rw [← add_mul]
          refine mul_le_mul_of_nonneg_right ?_ zero_le
          have : κ.count t.keys c + q * (κ.count t.keys c + κ.μc c + n c + κ.μc c * q) ≤
              (q + 1) * (κ.count t.keys c + n c + κ.μc c * (q + 1)) := by
            nlinarith [Nat.zero_le (n c), Nat.zero_le (κ.μc c), Nat.zero_le q]
          exact_mod_cast this
        calc (∑ c, (κ.count t.keys c : ℝ≥0∞) * Γ c) + εev + B0 =
              (∑ c, (κ.count t.keys c : ℝ≥0∞) * Γ c +
                ∑ c, ((q * (κ.count t.keys c + κ.μc c + n c + κ.μc c * q) : ℕ) : ℝ≥0∞) *
                  Γ c) + ((q + 1 : ℕ) : ℝ≥0∞) * εev := by
              rw [hB0]
              push_cast
              ring
          _ ≤ _ := add_le_add h1 le_rfl

/-- **The flag of the exempt game on the tables satisfying `Bt`.** For a sampler whose
attempts are in their classes, whose hidden entries are of marked classes, with the
class-wise key bound `Γ` with marked classes over the oracles satisfying `B` and the
landing bound `εev` over the oracles satisfying `B` with at most `N` defined points, and a predicate
`Bt` on tables, implying `B` of their oracle and inherited by smaller tables: from
tables whose hidden entries are of marked classes, with the flag cleared, a run of the
exempt game asking at most `h` hash and `q` signing queries, with hash queries of total
cost at most `n c` for each class `c`, and with `|t| + h + μ·q ≤ N`, ends with the
flag set and tables satisfying `Bt` with probability at most
`Σ_c q·(L_c + n c + μc c·q)·Γ c + q·εev`. -/
theorem run_attPR_flagB_le_cls {Γ : κ.ι → ℝ≥0∞} {B : (G.Key → Option G.Ch) → Prop}
    {εev : ℝ≥0∞} (hκ : G.AttClassesAt κ D xw) (hR : G.AllHiddenR ρ D xw) (N : ℕ)
    (hΓ : G.AttKeyBoundClsAtNRB ρ N D xw Γ B) (hev : G.AttEvLandAt ρ D xw N εev B)
    (Bt : G.Tables → Prop) (hBt : ∀ t, Bt t → B t.lookupAll)
    (hBmono : ∀ t t' : G.Tables, t.Le t' → Bt t' → Bt t)
    (A : OracleAdv G.Query G.Answer α) (h q : ℕ) (hA : IsQueryBound₂ A h q) (n : κ.ι → ℕ)
    (hn : ∀ c, A.IsQueryBoundBy (κ.hashCost c) (n c)) (t : G.Tables) (ht : RejMarked ρ t)
    (hN : t.size + h + G.μ * q ≤ N) :
    (OracleAdv.run (toOracle (attStepPR ρ D xw)) A (t, false)).toOuterMeasure
        {y | y.2.2 = true ∧ Bt y.2.1} ≤ flagBoundCls κ Γ n q t + q * εev := by
  induction A generalizing h q n t with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (OracleAdv.run (toOracle (attStepPR ρ D xw)) (k b) (t, false)).toOuterMeasure
          {y | y.2.2 = true ∧ Bt y.2.1}
        ≤ ∑' b, p b * (flagBoundCls κ Γ n q t + q * εev) :=
          ENNReal.tsum_le_tsum fun b =>
            mul_le_mul_right (ih b h q (hA b) n (fun c => hn c b) t ht hN) _
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        exact attPR_flag_hash_step_le ρ D xw εev _ k n h q N t ht hN key (fun c => (hn c).1)
          fun a t' ht' hN' => ih a h q (hA a) _ (fun c => (hn c).2 a) t' ht' hN'
    | inr m =>
      have hn' : ∀ c r, (k r).IsQueryBoundBy (κ.hashCost c) (n c) := fun c r => by
        simpa [Protocol.Classes.hashCost] using (hn c).2 r
      cases q with
      | zero => exact hA.elim
      | succ q =>
        exact attPR_flag_sign_step_le ρ D xw hκ hR N hΓ hev Bt hBt hBmono k h q n t ht hN m
          fun a t' ht' hN' => ih a h q (hA a) n (fun c => hn' c a) t' ht' hN'

/-- **Class-wise flag bound of the exempt game.** For a sampler whose attempts are in
their classes, whose hidden entries are of marked classes, with the class-wise key
bound `Γ` with marked classes over the oracles satisfying `B` and the landing bound
`εev` over the oracles satisfying `B` with at most `N` defined points, and a predicate
`Bt` on tables, implying `B` of their oracle and inherited by smaller tables: from tables whose hidden
entries are of marked classes, with `L_c` points of class `c` and the flag cleared, a
run of the exempt game asking at most `h` hash and `q` signing queries, with hash
queries of total cost at most `n c` for each class `c`, and with `|t| + h + μ·q ≤ N`,
sets the flag with probability at most `Σ_c q·(L_c + n c + μc c·q)·Γ c + q·εev` plus
the probability that its final tables fail `Bt`. -/
theorem run_attPR_flag_le_cls {Γ : κ.ι → ℝ≥0∞} {B : (G.Key → Option G.Ch) → Prop}
    {εev : ℝ≥0∞} (hκ : G.AttClassesAt κ D xw) (hR : G.AllHiddenR ρ D xw) (N : ℕ)
    (hΓ : G.AttKeyBoundClsAtNRB ρ N D xw Γ B) (hev : G.AttEvLandAt ρ D xw N εev B)
    (Bt : G.Tables → Prop) (hBt : ∀ t, Bt t → B t.lookupAll)
    (hBmono : ∀ t t' : G.Tables, t.Le t' → Bt t' → Bt t)
    (A : OracleAdv G.Query G.Answer α) (h q : ℕ) (hA : IsQueryBound₂ A h q) (n : κ.ι → ℕ)
    (hn : ∀ c, A.IsQueryBoundBy (κ.hashCost c) (n c)) (t : G.Tables) (ht : RejMarked ρ t)
    (hN : t.size + h + G.μ * q ≤ N) :
    (OracleAdv.run (toOracle (attStepPR ρ D xw)) A (t, false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ n q t + q * εev +
      (OracleAdv.run (toOracle (attStepPR ρ D xw)) A (t, false)).toOuterMeasure
        {y | ¬ Bt y.2.1} := by
  calc _ ≤ (OracleAdv.run (toOracle (attStepPR ρ D xw)) A (t, false)).toOuterMeasure
        ({y | y.2.2 = true ∧ Bt y.2.1} ∪ {y | ¬ Bt y.2.1}) :=
        MeasureTheory.measure_mono fun y hy => by
          by_cases hb : Bt y.2.1
          · exact Or.inl ⟨hy, hb⟩
          · exact Or.inr hb
    _ ≤ _ := (MeasureTheory.measure_union_le _ _).trans (add_le_add
        (run_attPR_flagB_le_cls ρ D xw hκ hR N hΓ hev Bt hBt hBmono A h q hA n hn t ht hN) le_rfl)

/-- **Class-wise flag bound of the exempt game with bounded IV multiplicity.** For a
sampler whose attempts are in their classes, with at most one entry of class `c₀` and
fresh IVs with point probability `p`, whose hidden entries are of marked classes, with
the class-wise key bound `Γ` with marked classes over the oracles satisfying `B` and
the landing bound `εev` over the oracles satisfying `B` with at most `N` defined points, where `B`
holds on the oracle of every table with at most `K` IV points per IV: a run of the
exempt game from the empty tables asking at most `qH` hash and `qS` signing queries,
with hash queries of total cost at most `n c` for each class `c`, and with
`qH + μ·qS ≤ N`, sets the flag with probability at most
`Σ_c qS·(n c + μc c·qS)·Γ c + qS·εev + C(qS, K + 1)·p^K`. -/
theorem run_attPR_flag_le_cls_ivMult {V : Type} [DecidableEq V] [Fintype V]
    {Γ : κ.ι → ℝ≥0∞} {B : (G.Key → Option G.Ch) → Prop} {εev p : ℝ≥0∞} {c₀ : κ.ι}
    {ivOf : G.Key → V} (hκ : G.AttClassesAt κ D xw) (hR : G.AllHiddenR ρ D xw) (N : ℕ)
    (hΓ : G.AttKeyBoundClsAtNRB ρ N D xw Γ B) (hev : G.AttEvLandAt ρ D xw N εev B)
    (hμ : κ.μc c₀ ≤ 1) (hp : G.AttIvFreshAt κ c₀ ivOf D xw p) (K : ℕ)
    (hB : ∀ t : G.Tables, OracleAdv.MultB K (ivCnt κ c₀ ivOf t) → B t.lookupAll)
    (A : OracleAdv G.Query G.Answer α) (qH qS : ℕ) (hA : IsQueryBound₂ A qH qS)
    (n : κ.ι → ℕ) (hn : ∀ c, A.IsQueryBoundBy (κ.hashCost c) (n c))
    (hN : qH + G.μ * qS ≤ N) :
    (OracleAdv.run (toOracle (attStepPR ρ D xw)) A (Protocol.Tables.empty, false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ n qS Protocol.Tables.empty + qS * εev +
      qS.choose (K + 1) * p ^ K :=
  (run_attPR_flag_le_cls ρ D xw hκ hR N hΓ hev (fun t => OracleAdv.MultB K (ivCnt κ c₀ ivOf t))
    hB (fun _ _ hle h v => (ivCnt_le_of_le κ c₀ ivOf hle v).trans (h v)) A qH qS hA n hn _
    (fun p hp => by simp [Protocol.Tables.empty] at hp)
    (by simpa [Protocol.Tables.size, Protocol.Tables.empty] using hN)).trans
    (add_le_add le_rfl (run_attPR_not_ivMult_le ρ hκ hμ hp K A qH qS hA _
      (ivCnt_empty κ c₀ ivOf)))

end RecFlag

/-! ## The EUF-CMA bound with key recovery -/

section RecHead

variable {G : Protocol} {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop}

/-- **The key-recovery reduction.** On the statement `x` it runs the adversary `A`
followed by the verifier's queries against the simulated oracle from the empty tables,
and returns the witness that the recovery `ρ` gives from the visible entries of the
final tables, or `dflt x` when the recovery gives none. -/
noncomputable def recReduction (ρ : G.Recovery κ rel) (dflt : G.Stmt → G.Wit) {qH qS : ℕ}
    (A : G.Adversary qH qS) (x : G.Stmt) : PMF G.Wit :=
  (OracleAdv.run (toOracle (simStep x)) (withVerify x (A.run x))
    (Protocol.Tables.empty, false)).map fun y =>
      (ρ.recover x (y.2.1.prog ++ y.2.1.hash)).getD (dflt x)

/-- **Recovery in the simulated game is a relation attack.** The expectation over the
generator of the probability that the recovery succeeds on the visible entries of the
final tables of the simulated run is at most the relation advantage of the reduction
`recReduction ρ dflt A`. -/
theorem Protocol.sim_recTest_le_relAdvantage (ρ : G.Recovery κ rel) (dflt : G.Stmt → G.Wit)
    {qH qS : ℕ} (A : G.Adversary qH qS) :
    ∑' xw, G.gen xw * (OracleAdv.run (toOracle (simStep xw.1)) (withVerify xw.1 (A.run xw.1))
      (Protocol.Tables.empty, false)).toOuterMeasure {y | recTest ρ xw.1 y.2.1 = true} ≤
      G.relAdvantage rel (recReduction ρ dflt A) := by
  rw [Protocol.relAdvantage_eq_tsum]
  refine ENNReal.tsum_le_tsum fun xw => mul_le_mul_right ?_ _
  unfold recReduction
  rw [PMF.toOuterMeasure_map_apply]
  refine MeasureTheory.measure_mono fun y hy => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, recTest, Option.isSome_iff_exists] at hy ⊢
  obtain ⟨w, hw⟩ := hy
  rw [hw, Option.getD_some]
  exact ρ.sound _ _ _ hw

variable (ρ : G.Recovery κ rel) {D : G.Sampler} {xw : G.Stmt × G.Wit}

/-- **The exempt game against the simulated game, for runs.** For a recovery complete at
the sampler, whose hidden entries are of marked classes, with statistical HVZK distance
`δ`, the class-wise key bound `Γ` with marked classes over the oracles satisfying `B`
and the landing bound `εev` over the oracles satisfying `B` with at most `N` defined points, and a
predicate `Bt` on tables, implying `B` of their oracle and inherited by smaller tables:
a run of the exempt game from the empty tables asking at most `h` hash and `q` signing
queries, with hash queries of total cost at most `n c` for each class `c`, and with
`h + μ·q ≤ N`, ends with a winning forgery, the flag set or a successful recovery with
probability at most the probability of a winning forgery in the simulated run, plus
the probability of a successful recovery in the simulated run, plus `q·δ`, plus
`Σ_c q·(n c + μc c·q)·Γ c + q·εev` and the probability that the final tables of the
exempt run fail `Bt`. -/
theorem run_attPR_recR_le_sim (hrec : ρ.CompleteAt D xw) {δ : ℝ≥0∞}
    (hZK : G.AttHVZKAt D xw δ) {Γ : κ.ι → ℝ≥0∞} {B : (G.Key → Option G.Ch) → Prop}
    {εev : ℝ≥0∞} (hκ : G.AttClassesAt κ D xw) (hR : G.AllHiddenR ρ D xw) (N : ℕ)
    (hΓ : G.AttKeyBoundClsAtNRB ρ N D xw Γ B) (hev : G.AttEvLandAt ρ D xw N εev B)
    (Bt : G.Tables → Prop) (hBt : ∀ t, Bt t → B t.lookupAll)
    (hBmono : ∀ t t' : G.Tables, t.Le t' → Bt t' → Bt t)
    (A : OracleAdv G.Query G.Answer G.Forgery) (h q : ℕ) (hA : IsQueryBound₂ A h q)
    (n : κ.ι → ℕ) (hn : ∀ c, A.IsQueryBoundBy (κ.hashCost c) (n c)) (hN : h + G.μ * q ≤ N) :
    (OracleAdv.run (toOracle (attStepPR ρ D xw)) A (Protocol.Tables.empty, false)).toOuterMeasure
        {y | (winsOrFlag xw.1 y || recTest ρ xw.1 y.2.1) = true} ≤
      (OracleAdv.run (toOracle (simStep xw.1)) A (Protocol.Tables.empty, false)).toOuterMeasure
          {y | wins xw.1 y = true} +
        (OracleAdv.run (toOracle (simStep xw.1)) A (Protocol.Tables.empty, false)).toOuterMeasure
          {y | recTest ρ xw.1 y.2.1 = true} + q * δ +
        (flagBoundCls κ Γ n q Protocol.Tables.empty + q * εev +
          (OracleAdv.run (toOracle (attStepPR ρ D xw)) A
            (Protocol.Tables.empty, false)).toOuterMeasure {y | ¬ Bt y.2.1}) := by
  set R := OracleAdv.run (toOracle (attStepPR ρ D xw)) A (Protocol.Tables.empty, false)
  set S := OracleAdv.run (toOracle (simStep xw.1)) A (Protocol.Tables.empty, false)
  set g : G.Forgery × (G.Tables × Bool) → ℝ≥0∞ :=
    fun y => if (wins xw.1 y || recTest ρ xw.1 y.2.1) = true then 1 else 0 with hgdef
  have hg : ∀ y, g y ≤ 1 := fun y => by simp only [g]; split_ifs <;> simp
  have hgr : RejInsensitive g := fun _ _ => rfl
  have hgf : FlagInsensitive g := fun _ _ => rfl
  have hgs : ∀ y, recTest ρ xw.1 y.2.1 = true → g y = 1 := fun y hy => by simp [g, hy]
  have hA' : R.toOuterMeasure {y | (winsOrFlag xw.1 y || recTest ρ xw.1 y.2.1) = true} ≤
      ∑' y, R y * offFlag g y + R.toOuterMeasure {y | y.2.2 = true} := by
    rw [toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun y => ?_
    rw [← mul_add]
    refine mul_le_mul_right ?_ _
    by_cases hf : y.2.2 = true
    · rw [if_pos hf]
      split_ifs <;> simp
    · have hf' : y.2.2 = false := by simpa using hf
      rw [show offFlag g y = g y from if_neg hf, if_neg hf, add_zero]
      simp only [g, winsOrFlag, hf', Bool.or_false, Bool.or_eq_true]
      exact le_rfl
  have hC : ∑' y, S y * g y ≤ S.toOuterMeasure {y | wins xw.1 y = true} +
      S.toOuterMeasure {y | recTest ρ xw.1 y.2.1 = true} := by
    rw [toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun y => ?_
    rw [← mul_add]
    refine mul_le_mul_right ?_ _
    by_cases hw : wins xw.1 y = true <;> by_cases hr : recTest ρ xw.1 y.2.1 = true <;>
      simp [g, hw, hr]
  calc _ ≤ ∑' y, R y * offFlag g y + R.toOuterMeasure {y | y.2.2 = true} := hA'
    _ ≤ ∑' y, S y * g y + q * δ + R.toOuterMeasure {y | y.2.2 = true} :=
        add_le_add (run_attPR_le_sim ρ hrec hZK A h q hA _ (recInv_empty ρ xw.1) g hg hgr hgf
          hgs) le_rfl
    _ ≤ _ := add_le_add (add_le_add hC le_rfl)
        (run_attPR_flag_le_cls ρ D xw hκ hR N hΓ hev Bt hBt hBmono A h q hA n hn _
          (fun p hp => by simp [Protocol.Tables.empty] at hp)
          (by simpa [Protocol.Tables.size, Protocol.Tables.empty] using hN))

/-- **The exempt game against the simulated game and the relation game.** For a
recovery `ρ`, complete at the sampler `D` and with the hidden entries of `D` of marked
classes at every generated pair `xw`, a sampler with statistical HVZK distance `δ xw`,
attempts in their classes, the class-wise key bound `Γ xw` with marked classes over the
oracles satisfying `B xw` and the landing bound `εev xw` over the oracles satisfying
`B xw` with at most `qH + V + μ·qS` defined points, a predicate `Bt xw` on tables implying `B xw` of their
oracle and inherited by smaller tables, and every adversary with at most `qH` hash and
`qS` signing queries whose hash queries at points of class `c` are at most `q c` on
every path: the advantage that the forgery wins, the flag is set or the recovery
succeeds in the exempt game is at most the simulated-game advantage plus the relation
advantage of `recReduction ρ dflt A` plus the expectation over the generator of
`qS·δ(x, w) + Σ_c qS·(q c + Vc c + μc c·qS)·Γ(x, w) c + qS·εev(x, w)` and the
probability that the final tables of the exempt run fail `Bt (x, w)`. -/
theorem Protocol.attAdvantageByPR_recR_le_sim (D : G.Sampler) (dflt : G.Stmt → G.Wit)
    {qH qS : ℕ} {δ : G.Stmt × G.Wit → ℝ≥0∞} {Γ : G.Stmt × G.Wit → κ.ι → ℝ≥0∞}
    {B : G.Stmt × G.Wit → (G.Key → Option G.Ch) → Prop} {εev : G.Stmt × G.Wit → ℝ≥0∞}
    (hrec : ∀ xw ∈ G.gen.support, ρ.CompleteAt D xw)
    (hZK : ∀ xw ∈ G.gen.support, G.AttHVZKAt D xw (δ xw))
    (hκ : ∀ xw ∈ G.gen.support, G.AttClassesAt κ D xw)
    (hR : ∀ xw ∈ G.gen.support, G.AllHiddenR ρ D xw)
    (hΓ : ∀ xw ∈ G.gen.support,
      G.AttKeyBoundClsAtNRB ρ (qH + G.V + G.μ * qS) D xw (Γ xw) (B xw))
    (hev : ∀ xw ∈ G.gen.support,
      G.AttEvLandAt ρ D xw (qH + G.V + G.μ * qS) (εev xw) (B xw))
    (Bt : G.Stmt × G.Wit → G.Tables → Prop) (hBt : ∀ xw t, Bt xw t → B xw t.lookupAll)
    (hBmono : ∀ xw (t t' : G.Tables), t.Le t' → Bt xw t' → Bt xw t)
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ x c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) :
    attAdvantageByPR (fun x y => winsOrFlag x y || recTest ρ x y.2.1) ρ D A ≤
      simAdvantage A + G.relAdvantage rel (recReduction ρ dflt A) +
      ∑' xw, G.gen xw * (qS * δ xw +
        ∑ c, ((qS * (q c + κ.Vc c + κ.μc c * qS) : ℕ) : ℝ≥0∞) * Γ xw c + qS * εev xw +
        (OracleAdv.run (toOracle (attStepPR ρ D xw)) (withVerify xw.1 (A.run xw.1))
          (Protocol.Tables.empty, false)).toOuterMeasure {y | ¬ Bt xw y.2.1}) := by
  unfold attAdvantageByPR attGameByPR simAdvantage simGame
  rw [prTrue_gameDistBy, prTrue_gameDist]
  refine le_trans ?_ (add_le_add (add_le_add le_rfl (Protocol.sim_recTest_le_relAdvantage ρ dflt A))
    le_rfl)
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun xw => ?_
  rw [← mul_add, ← mul_add]
  by_cases hxw : xw ∈ G.gen.support
  · have hB := isQueryBound₂_withVerify xw.1 _ qH qS (A.isQueryBound xw.1)
    refine mul_le_mul_right ?_ _
    refine (run_attPR_recR_le_sim ρ (hrec xw hxw) (hZK xw hxw) (hκ xw hxw) (hR xw hxw) _
      (hΓ xw hxw) (hev xw hxw) (Bt xw) (hBt xw) (hBmono xw) _ (qH + G.V) qS hB
      (fun c => q c + κ.Vc c) (fun c => isQueryBoundBy_withVerify_cls κ c xw.1 _ _ (hq xw.1 c))
      le_rfl).trans (le_of_eq ?_)
    simp only [flagBoundCls, Protocol.Tables.empty, Protocol.Tables.keys,
      Protocol.Classes.count]
    simp
    ring
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hxw]

/-- **EUF-CMA through the programmed flag, the hybrid, the exempt game, the simulation
and key recovery, class by class.** For a recovery `ρ`, complete at the sampler `D` and
with the hidden entries of `D` of marked classes at every generated pair `xw`, a
sampler with statistical HVZK distance `δ xw`, attempts in their classes, the
class-wise key bound `Γ xw` with marked classes over the oracles satisfying `B xw` and
the landing bound `εev xw` over the oracles satisfying `B xw` with at most
`qH + V + μ·qS` defined points, a predicate `Bt xw` on tables implying `B xw` of their oracle and inherited by smaller
tables, and every adversary with at most `qH` hash and `qS` signing queries whose hash
queries at points of class `c` are at most `q c` on every path: the EUF-CMA advantage
is at most the simulated-game advantage plus the relation advantage of the reduction
`recReduction ρ dflt A` plus the expectation over the generator of
`qS·δ(x, w) + Σ_c qS·(q c + Vc c + μc c·qS)·Γ(x, w) c + qS·εev(x, w)` and the
probability that the final tables of the exempt run fail `Bt (x, w)`, plus the sum
over `k < qS` of the advantages of the hybrid distinguishers
`hybDistByP winsOrFlag G.witSampler D k A` between the challenge oracles with the
programmed flag of the witness sampler and of `D`. -/
theorem Protocol.eufcma_le_simPRB_cls (D : G.Sampler) (dflt : G.Stmt → G.Wit)
    {qH qS : ℕ} {δ : G.Stmt × G.Wit → ℝ≥0∞} {Γ : G.Stmt × G.Wit → κ.ι → ℝ≥0∞}
    {B : G.Stmt × G.Wit → (G.Key → Option G.Ch) → Prop} {εev : G.Stmt × G.Wit → ℝ≥0∞}
    (hrec : ∀ xw ∈ G.gen.support, ρ.CompleteAt D xw)
    (hZK : ∀ xw ∈ G.gen.support, G.AttHVZKAt D xw (δ xw))
    (hκ : ∀ xw ∈ G.gen.support, G.AttClassesAt κ D xw)
    (hR : ∀ xw ∈ G.gen.support, G.AllHiddenR ρ D xw)
    (hΓ : ∀ xw ∈ G.gen.support,
      G.AttKeyBoundClsAtNRB ρ (qH + G.V + G.μ * qS) D xw (Γ xw) (B xw))
    (hev : ∀ xw ∈ G.gen.support,
      G.AttEvLandAt ρ D xw (qH + G.V + G.μ * qS) (εev xw) (B xw))
    (Bt : G.Stmt × G.Wit → G.Tables → Prop) (hBt : ∀ xw t, Bt xw t → B xw t.lookupAll)
    (hBmono : ∀ xw (t t' : G.Tables), t.Le t' → Bt xw t' → Bt xw t)
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ x c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) :
    eufcmaAdvantage A ≤
      simAdvantage A + G.relAdvantage rel (recReduction ρ dflt A) +
      ∑' xw, G.gen xw * (qS * δ xw +
        ∑ c, ((qS * (q c + κ.Vc c + κ.μc c * qS) : ℕ) : ℝ≥0∞) * Γ xw c + qS * εev xw +
        (OracleAdv.run (toOracle (attStepPR ρ D xw)) (withVerify xw.1 (A.run xw.1))
          (Protocol.Tables.empty, false)).toOuterMeasure {y | ¬ Bt xw y.2.1}) +
      ∑ k ∈ Finset.range qS, Advantage (chalGameP G.witSampler (hybDistByP winsOrFlag
          G.witSampler D k A)) (chalGameP D (hybDistByP winsOrFlag G.witSampler D k A)) :=
  (Protocol.eufcma_le_witP A).trans
    ((Protocol.attAdvantage_hybrid_byP winsOrFlag G.witSampler D A).trans
      (add_le_add ((Protocol.attAdvantageByP_le_recR ρ D hrec A).trans
        (Protocol.attAdvantageByPR_recR_le_sim ρ D dflt hrec hZK hκ hR hΓ hev Bt hBt hBmono A
          q hq)) le_rfl))

/-- **EUF-CMA with key recovery and bounded IV multiplicity, class by class.** The bound
of `Protocol.eufcma_le_simPRB_cls` for a sampler whose attempts have at most one entry
of class `c₀` and fresh IVs with point probability `p` at every generated pair, where
`B xw` holds on the oracle of every table with at most `K` IV points per IV: the
probability that the final tables fail the multiplicity bound is replaced by
`C(qS, K + 1)·p^K`. -/
theorem Protocol.eufcma_le_simPRB_cls_ivMult {V : Type} [DecidableEq V] [Fintype V]
    (D : G.Sampler) (dflt : G.Stmt → G.Wit) {qH qS : ℕ} {δ : G.Stmt × G.Wit → ℝ≥0∞}
    {Γ : G.Stmt × G.Wit → κ.ι → ℝ≥0∞} {B : G.Stmt × G.Wit → (G.Key → Option G.Ch) → Prop}
    {εev : G.Stmt × G.Wit → ℝ≥0∞} {p : ℝ≥0∞} {c₀ : κ.ι} {ivOf : G.Key → V}
    (hrec : ∀ xw ∈ G.gen.support, ρ.CompleteAt D xw)
    (hZK : ∀ xw ∈ G.gen.support, G.AttHVZKAt D xw (δ xw))
    (hκ : ∀ xw ∈ G.gen.support, G.AttClassesAt κ D xw)
    (hR : ∀ xw ∈ G.gen.support, G.AllHiddenR ρ D xw)
    (hΓ : ∀ xw ∈ G.gen.support,
      G.AttKeyBoundClsAtNRB ρ (qH + G.V + G.μ * qS) D xw (Γ xw) (B xw))
    (hev : ∀ xw ∈ G.gen.support,
      G.AttEvLandAt ρ D xw (qH + G.V + G.μ * qS) (εev xw) (B xw))
    (hμ : κ.μc c₀ ≤ 1) (hp : ∀ xw ∈ G.gen.support, G.AttIvFreshAt κ c₀ ivOf D xw p) (K : ℕ)
    (hB : ∀ xw (t : G.Tables), OracleAdv.MultB K (ivCnt κ c₀ ivOf t) → B xw t.lookupAll)
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ x c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) :
    eufcmaAdvantage A ≤
      simAdvantage A + G.relAdvantage rel (recReduction ρ dflt A) +
      ∑' xw, G.gen xw * (qS * δ xw +
        ∑ c, ((qS * (q c + κ.Vc c + κ.μc c * qS) : ℕ) : ℝ≥0∞) * Γ xw c + qS * εev xw +
        qS.choose (K + 1) * p ^ K) +
      ∑ k ∈ Finset.range qS, Advantage (chalGameP G.witSampler (hybDistByP winsOrFlag
          G.witSampler D k A)) (chalGameP D (hybDistByP winsOrFlag G.witSampler D k A)) := by
  refine (Protocol.eufcma_le_simPRB_cls ρ D dflt hrec hZK hκ hR hΓ hev
    (fun _ t => OracleAdv.MultB K (ivCnt κ c₀ ivOf t)) hB
    (fun _ _ _ hle h v => (ivCnt_le_of_le κ c₀ ivOf hle v).trans (h v)) A q hq).trans ?_
  refine add_le_add (add_le_add le_rfl (ENNReal.tsum_le_tsum fun xw => ?_)) le_rfl
  by_cases hxw : xw ∈ G.gen.support
  · refine mul_le_mul_right (add_le_add le_rfl ?_) _
    exact run_attPR_not_ivMult_le ρ (hκ xw hxw) hμ (hp xw hxw) K _ (qH + G.V) qS
      (isQueryBound₂_withVerify xw.1 _ qH qS (A.isQueryBound xw.1)) _ (ivCnt_empty κ c₀ ivOf)
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hxw]

/-- **EUF-CMA with key recovery and bounded multiplicity of entry values, class by
class.** The bound of `Protocol.eufcma_le_simPRB_cls` for a sampler whose attempts have
at most one entry of class `c₀` and fresh entry values under the projection `π` with
point probability `p` at every generated pair, with uniform hash answers at points of
class `c₀` of point probability `p`, where `B xw` holds on the oracle of every table
with at most `K` entries of class `c₀` per projection: the probability that the final
tables fail the multiplicity bound is replaced by `C(qH + V + qS, K + 1)·p^K`. -/
theorem Protocol.eufcma_le_simPRB_cls_entMult {V : Type} [DecidableEq V] [Fintype V]
    (D : G.Sampler) (dflt : G.Stmt → G.Wit) {qH qS : ℕ} {δ : G.Stmt × G.Wit → ℝ≥0∞}
    {Γ : G.Stmt × G.Wit → κ.ι → ℝ≥0∞} {B : G.Stmt × G.Wit → (G.Key → Option G.Ch) → Prop}
    {εev : G.Stmt × G.Wit → ℝ≥0∞} {p : ℝ≥0∞} {c₀ : κ.ι} {π : G.Key × G.Ch → V}
    (hrec : ∀ xw ∈ G.gen.support, ρ.CompleteAt D xw)
    (hZK : ∀ xw ∈ G.gen.support, G.AttHVZKAt D xw (δ xw))
    (hκ : ∀ xw ∈ G.gen.support, G.AttClassesAt κ D xw)
    (hR : ∀ xw ∈ G.gen.support, G.AllHiddenR ρ D xw)
    (hΓ : ∀ xw ∈ G.gen.support,
      G.AttKeyBoundClsAtNRB ρ (qH + G.V + G.μ * qS) D xw (Γ xw) (B xw))
    (hev : ∀ xw ∈ G.gen.support,
      G.AttEvLandAt ρ D xw (qH + G.V + G.μ * qS) (εev xw) (B xw))
    (hμ : κ.μc c₀ ≤ 1) (hp : ∀ xw ∈ G.gen.support, G.AttEntFreshAt κ c₀ π D xw p)
    (hpH : ∀ k, κ.cls k = c₀ → ∀ v,
      (PMF.uniformOfFintype G.Ch).toOuterMeasure {c | π (k, c) = v} ≤ p) (K : ℕ)
    (hB : ∀ xw (t : G.Tables), OracleAdv.MultB K (entCnt κ c₀ π t) → B xw t.lookupAll)
    (A : G.Adversary qH qS) (q : κ.ι → ℕ)
    (hq : ∀ x c, (A.run x).IsQueryBoundBy (κ.hashCost c) (q c)) :
    eufcmaAdvantage A ≤
      simAdvantage A + G.relAdvantage rel (recReduction ρ dflt A) +
      ∑' xw, G.gen xw * (qS * δ xw +
        ∑ c, ((qS * (q c + κ.Vc c + κ.μc c * qS) : ℕ) : ℝ≥0∞) * Γ xw c + qS * εev xw +
        (qH + G.V + qS).choose (K + 1) * p ^ K) +
      ∑ k ∈ Finset.range qS, Advantage (chalGameP G.witSampler (hybDistByP winsOrFlag
          G.witSampler D k A)) (chalGameP D (hybDistByP winsOrFlag G.witSampler D k A)) := by
  refine (Protocol.eufcma_le_simPRB_cls ρ D dflt hrec hZK hκ hR hΓ hev
    (fun _ t => OracleAdv.MultB K (entCnt κ c₀ π t)) hB
    (fun _ _ _ hle h v => (entCnt_le_of_le κ c₀ π hle v).trans (h v)) A q hq).trans ?_
  refine add_le_add (add_le_add le_rfl (ENNReal.tsum_le_tsum fun xw => ?_)) le_rfl
  by_cases hxw : xw ∈ G.gen.support
  · refine mul_le_mul_right (add_le_add le_rfl ?_) _
    exact run_attPR_not_entMult_le ρ (hκ xw hxw) hμ (hp xw hxw) hpH K _ (qH + G.V) qS
      (isQueryBound₂_withVerify xw.1 _ qH qS (A.isQueryBound xw.1)) _ (entCnt_empty κ c₀ π)
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hxw]

end RecHead

end CatCrypt.Crypto.FiatShamirROM
