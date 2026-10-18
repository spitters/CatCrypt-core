/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.KeyRecovery
public import CatCryptCore.Crypto.FiatShamirROM.KeyRecoveryMult

/-!
# Fiat–Shamir in the random-oracle model: multiplicity of the IVs of signing attempts

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

## Main definitions

* `ivCnt κ c₀ ivOf t` — the counts per IV of the programmed and hidden entries of
  class `c₀` in the tables `t`
* `Protocol.AttIvFreshAt κ c₀ ivOf D xw p` — the sampler draws an IV point with a
  given IV with probability at most `p`, against every oracle
* `signCost` — the query cost `1` on signing queries and `0` on hash queries

## Main results

* `ivCnt_attSignOut` — a signing answer keeps the counts or adds one IV point
* `freshMult_attStepPR`, `freshMult_attStepP` — the exempt game and the game with
  the programmed flag satisfy `OracleAdv.FreshMult` for the counts `ivCnt`
* `run_attPR_not_ivMult_le`, `run_attP_not_ivMult_le` — a run with at most `qS`
  signing queries ends with more than `K` IV points sharing an IV with probability at
  most `C(qS, K + 1)·p^K`
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

end IvMult

end CatCrypt.Crypto.FiatShamirROM
