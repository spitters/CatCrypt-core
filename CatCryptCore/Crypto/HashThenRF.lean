/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PRPPRFSwitching
public import CatCryptCore.Crypto.Constructions.ECBCPRFFlag
public import CatCryptCore.Crypto.OracleCollision
public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.ForMathlib.PMFUniform
public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.AutoDispatchExt

/-!
# Hash then random function

A keyed hash family `H : K → M → B` is `ε`-almost universal when two distinct messages
have the same hash under a uniform key with probability at most `ε`. A random function on
`B` queried at `H k m`, for a uniform hidden key `k`, is indistinguishable from a random
function on `M`: an adversary asking at most `q` adaptive queries (`OracleAdv`) has
advantage at most `q(q-1)/2 · ε`. Replacing the random function by a keyed function `F`
costs the PRF advantage of `F` against the explicit reduction `hashRed H A`, which samples
the hash key and asks each query `m` of `A` at `H k m`.

The `ε`-almost-Δ-universal property (`IsAlmostDeltaUniversal`, differences in an additive
group; for GHASH and POLYVAL the group is a binary field, where the difference is XOR)
implies `ε`-almost universality at the difference `0`.

## Main definitions

* `IsAlmostUniversal H ε`, `IsAlmostDeltaUniversal H ε` — almost-universal and
  almost-Δ-universal hash families
* `hashRFGame H A` — `A` against the lazy random function on `B` queried at `H k m`, for a
  uniform key `k`
* `HashRF_Advantage H A` — the advantage of `A` in distinguishing `hashRFGame H A` from the
  lazy random function on `M`
* `hashPRF F H` — the keyed function `(k₁, k₂) ↦ F k₁ ∘ H k₂`
* `hashRed H A` — the reduction to the PRF security of `F`; `hashRed.timed` its costed form

## Main results

* `IsAlmostDeltaUniversal.isAlmostUniversal` — almost-Δ-universal implies almost universal
* `prob_queryCollision_le` — an `ε`-almost-universal family has a collision on a list of
  `n` messages with probability at most `n(n-1)/2 · ε`
* `advantage_compose_le` — a lazy random function queried through `c φ`, for a uniform `φ`,
  is distinguished from a lazy random function by at most the expected probability that
  `c φ` maps two distinct recorded queries to the same point
* `hashRF_advantage_le` — for an `ε`-almost-universal `H` and an adversary with at most `q`
  queries, `HashRF_Advantage H A ≤ q(q-1)/2 · ε`
* `hashPRF_advantage_le` — `PRF_q_Advantage (hashPRF F H) A ≤
  PRF_q_Advantage F (hashRed H A) + q(q-1)/2 · ε`
* `hashRed.timeBound_timed` — the costed reduction (`derive_timed`) runs in time
  `1 + T + q (2 + t₀)` for an adversary of time `T` with `q` queries and hash cost at most
  `t₀`

## Proof

The random function on `B` keeps a table on `M` read through `H k` (`realFlag`); the random
function on `M` keeps the same table (`idealFlag`). Both set a flag when the query is not
`consistent`, that is, when a recorded query other than the current one has the same hash.
The two flagged oracles agree on every transition that leaves the flag cleared
(`OracleAdv.run_apply_flag_false_eq`), and a set flag in the ideal run comes from a
collision of the final table (`idealFlag_support_rel`). The ideal run does not depend on the
key, so the collision probability is the expectation over the final table of the collision
probability over the key, bounded by `n(n-1)/2 · ε` for a table of `n ≤ q` entries.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.HashThenRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.Constructions.ECBCPRF (toOuterMeasure_le_add_flag toOuterMeasure_flag_eq
  run_support_rel tsum_pure_mul)
open PMF (tsum_bind_mul)
open CatCrypt.Crypto.OracleAdv (QueryCollision)
open scoped ENNReal

/-! ## Almost-universal hash families -/

section Universal

variable {K M B : Type} [Fintype K] [Nonempty K]

/-- `H` is `ε`-almost universal: two distinct messages have the same hash under a uniform
key with probability at most `ε`. -/
def IsAlmostUniversal (H : K → M → B) (ε : ℝ≥0∞) : Prop :=
  ∀ m₁ m₂ : M, m₁ ≠ m₂ →
    (PMF.uniformOfFintype K).toOuterMeasure {k | H k m₁ = H k m₂} ≤ ε

/-- `H` is `ε`-almost Δ-universal: for two distinct messages and every difference `δ`, the
hashes under a uniform key differ by `δ` with probability at most `ε`. In a group of
characteristic two (GHASH, POLYVAL) the difference is XOR. -/
def IsAlmostDeltaUniversal [AddCommGroup B] (H : K → M → B) (ε : ℝ≥0∞) : Prop :=
  ∀ m₁ m₂ : M, m₁ ≠ m₂ → ∀ δ : B,
    (PMF.uniformOfFintype K).toOuterMeasure {k | H k m₁ - H k m₂ = δ} ≤ ε

/-- An `ε`-almost-Δ-universal family is `ε`-almost universal. -/
theorem IsAlmostDeltaUniversal.isAlmostUniversal [AddCommGroup B] {H : K → M → B}
    {ε : ℝ≥0∞} (h : IsAlmostDeltaUniversal H ε) : IsAlmostUniversal H ε := by
  intro m₁ m₂ hne; simpa [sub_eq_zero] using h m₁ m₂ hne 0

/-- For an `ε`-almost-universal family, `m` has the hash of another message of `L` with
probability at most `|L| · ε`. -/
theorem prob_exists_coll_le {H : K → M → B} {ε : ℝ≥0∞} (hH : IsAlmostUniversal H ε)
    (m : M) (L : List M) :
    (PMF.uniformOfFintype K).toOuterMeasure {k | ∃ y ∈ L, m ≠ y ∧ H k m = H k y} ≤
      L.length * ε := by
  set μ := (PMF.uniformOfFintype K).toOuterMeasure
  induction L with
  | nil => simp
  | cons y L ih =>
    have hy : μ {k | m ≠ y ∧ H k m = H k y} ≤ ε := by
      by_cases hmy : m = y
      · simp [hmy]
      · exact (MeasureTheory.measure_mono fun k hk => hk.2).trans (hH m y hmy)
    calc μ {k | ∃ z ∈ y :: L, m ≠ z ∧ H k m = H k z}
        ≤ μ ({k | m ≠ y ∧ H k m = H k y} ∪ {k | ∃ z ∈ L, m ≠ z ∧ H k m = H k z}) := by
          refine MeasureTheory.measure_mono fun k hk => ?_
          obtain ⟨z, hz, hmz, hk⟩ := hk
          rcases List.mem_cons.mp hz with rfl | hz
          · exact Or.inl ⟨hmz, hk⟩
          · exact Or.inr ⟨z, hz, hmz, hk⟩
      _ ≤ μ {k | m ≠ y ∧ H k m = H k y} + μ {k | ∃ z ∈ L, m ≠ z ∧ H k m = H k z} :=
          MeasureTheory.measure_union_le _ _
      _ ≤ ε + L.length * ε := add_le_add hy ih
      _ = (y :: L).length * ε := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- **Collision bound.** For an `ε`-almost-universal family, two distinct messages of a list
of `n` messages have the same hash with probability at most `n(n-1)/2 · ε`. -/
theorem prob_queryCollision_le {H : K → M → B} {ε : ℝ≥0∞} (hH : IsAlmostUniversal H ε)
    (L : List M) :
    (PMF.uniformOfFintype K).toOuterMeasure {k | QueryCollision (H k) L} ≤
      ((L.length * (L.length - 1) / 2 : ℕ) : ℝ≥0∞) * ε := by
  set μ := (PMF.uniformOfFintype K).toOuterMeasure
  rw [← Finset.sum_range_id]
  induction L with
  | nil => simp [QueryCollision]
  | cons a L ih =>
    calc μ {k | QueryCollision (H k) (a :: L)}
        ≤ μ ({k | ∃ y ∈ L, a ≠ y ∧ H k a = H k y} ∪ {k | QueryCollision (H k) L}) := by
          refine MeasureTheory.measure_mono fun k hk => ?_
          obtain ⟨x, hx, y, hy, hxy, hk⟩ := hk
          rcases List.mem_cons.mp hx with hxa | hxL <;>
            rcases List.mem_cons.mp hy with hya | hyL
          · exact (hxy (hxa.trans hya.symm)).elim
          · subst hxa; exact Or.inl ⟨y, hyL, hxy, hk⟩
          · subst hya; exact Or.inl ⟨x, hxL, Ne.symm hxy, hk.symm⟩
          · exact Or.inr ⟨x, hxL, y, hyL, hxy, hk⟩
      _ ≤ μ {k | ∃ y ∈ L, a ≠ y ∧ H k a = H k y} + μ {k | QueryCollision (H k) L} :=
          MeasureTheory.measure_union_le _ _
      _ ≤ L.length * ε + ((∑ i ∈ Finset.range L.length, i : ℕ) : ℝ≥0∞) * ε :=
          add_le_add (prob_exists_coll_le hH a L) ih
      _ = ((∑ i ∈ Finset.range (a :: L).length, i : ℕ) : ℝ≥0∞) * ε := by
          rw [List.length_cons, Finset.sum_range_succ]
          push_cast
          ring

end Universal

/-! ## A random function composed with a keyed map -/

section Compose

variable {M B R : Type} [DecidableEq M] [DecidableEq B] [Fintype R] [Nonempty R] {α : Type}

/-- No recorded query other than `d` has the same image under `c` as `d`. -/
def consistent (c : M → B) (T : List (M × R)) (d : M) : Bool :=
  decide (∀ p ∈ T, c p.1 = c d → p.1 = d)

/-- The table of a lazy random function on `B`, read off a table on `M` through `c`. -/
def projC (c : M → B) (T : List (M × R)) : List (B × R) :=
  T.map fun p => (c p.1, p.2)

omit [Fintype R] [Nonempty R] in
theorem lookup_projC_of_consistent (c : M → B) (T : List (M × R)) (d : M)
    (h : ∀ p ∈ T, c p.1 = c d → p.1 = d) :
    List.lookup (c d) (projC c T) = List.lookup d T := by
  induction T with
  | nil => rfl
  | cons p T ih =>
    obtain ⟨a, b⟩ := p
    have ih' := ih fun p hp => h p (by simp [hp])
    simp only [projC, List.map_cons] at ih' ⊢
    by_cases hca : c d = c a
    · have had : a = d := h (a, b) (by simp) hca.symm
      subst had
      simp
    · have had : d ≠ a := fun h' => hca (h' ▸ rfl)
      have h1 : (c d == c a) = false := by simpa using hca
      have h2 : (d == a) = false := by simpa using had
      simp only [List.lookup_cons, h1, h2]
      exact ih'

omit [DecidableEq B] [Fintype R] [Nonempty R] in
theorem mem_of_lookup_eq_some (T : List (M × R)) (d : M) (r : R)
    (h : List.lookup d T = some r) : (d, r) ∈ T := by
  induction T with
  | nil => simp at h
  | cons p T ih =>
    obtain ⟨a, b⟩ := p
    by_cases hda : d = a
    · subst hda
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      simp [h]
    · have h2 : (d == a) = false := by simpa using hda
      simp only [List.lookup_cons, h2] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- The random function on `B` queried at `c d`, with its table read through `c` and a flag
set when the query is not `consistent`. -/
noncomputable def realFlag (c : M → B) (s : List (M × R) × Bool) (d : M) :
    PMF (R × (List (M × R) × Bool)) :=
  match List.lookup (c d) (projC c s.1) with
  | some r => PMF.pure (r, (s.1, s.2 || !consistent c s.1 d))
  | none => (PMF.uniformOfFintype R).map fun r =>
      (r, ((d, r) :: s.1, s.2 || !consistent c s.1 d))

/-- The random function on `M`, with a flag set when the query is not `consistent`. -/
noncomputable def idealFlag (c : M → B) (s : List (M × R) × Bool) (d : M) :
    PMF (R × (List (M × R) × Bool)) :=
  match List.lookup d s.1 with
  | some r => PMF.pure (r, (s.1, s.2 || !consistent c s.1 d))
  | none => (PMF.uniformOfFintype R).map fun r =>
      (r, ((d, r) :: s.1, s.2 || !consistent c s.1 d))

theorem realFlag_map (c : M → B) (s : List (M × R) × Bool) (d : M) :
    (realFlag c s d).map (Prod.map id fun s => projC c s.1) = rfOracle (projC c s.1) (c d) := by
  unfold realFlag rfOracle
  cases List.lookup (c d) (projC c s.1) with
  | some r => simp [PMF.pure_map]
  | none => simp [PMF.map_comp, Function.comp_def, projC]

theorem idealFlag_map (c : M → B) (s : List (M × R) × Bool) (d : M) :
    (idealFlag c s d).map (Prod.map id Prod.fst) = rfOracle s.1 d := by
  unfold idealFlag rfOracle
  cases List.lookup d s.1 with
  | some r => simp [PMF.pure_map]
  | none => simp [PMF.map_comp, Function.comp_def]

theorem realFlag_apply_true_false (c : M → B) (t : List (M × R)) (d : M) (r : R)
    (t' : List (M × R)) : realFlag c (t, true) d (r, (t', false)) = 0 := by
  unfold realFlag
  cases List.lookup (c d) (projC c t) with
  | some r₀ => simp [PMF.pure_apply]
  | none => simp [PMF.map_apply]

theorem idealFlag_apply_true_false (c : M → B) (t : List (M × R)) (d : M) (r : R)
    (t' : List (M × R)) : idealFlag c (t, true) d (r, (t', false)) = 0 := by
  unfold idealFlag
  cases List.lookup d t with
  | some r₀ => simp [PMF.pure_apply]
  | none => simp [PMF.map_apply]

theorem realFlag_apply_false_eq (c : M → B) (s : List (M × R) × Bool) (d : M) (r : R)
    (t' : List (M × R)) :
    realFlag c s d (r, (t', false)) = idealFlag c s d (r, (t', false)) := by
  by_cases hc : consistent c s.1 d = true
  · unfold realFlag idealFlag
    rw [lookup_projC_of_consistent c s.1 d (by simpa [consistent] using hc)]
  · have hc' : consistent c s.1 d = false := by simpa using hc
    unfold realFlag idealFlag
    cases List.lookup (c d) (projC c s.1) <;> cases List.lookup d s.1 <;>
      simp [hc', PMF.pure_apply, PMF.map_apply]

/-- Every reachable state of `idealFlag` extends the initial table, and a set flag comes
from the initial flag or a collision in the final table. -/
theorem idealFlag_support_rel (c : M → B) (A : OracleAdv M R α) (s : List (M × R) × Bool) :
    ∀ x ∈ (OracleAdv.run (idealFlag c) A s).support,
      (∃ U, x.2.1 = U ++ s.1) ∧
        (x.2.2 = true → s.2 = true ∨ QueryCollision c (x.2.1.map Prod.fst)) := by
  have hmono : ∀ T U : List (M × R), QueryCollision c (T.map Prod.fst) →
      QueryCollision c ((U ++ T).map Prod.fst) := by
    rintro T U ⟨a, ha, b, hb, hne, hcab⟩
    exact ⟨a, by simp only [List.map_append, List.mem_append]; exact Or.inr ha,
      b, by simp only [List.map_append, List.mem_append]; exact Or.inr hb, hne, hcab⟩
  refine run_support_rel (idealFlag c)
    (fun s s' => (∃ U, s'.1 = U ++ s.1) ∧
      (s'.2 = true → s.2 = true ∨ QueryCollision c (s'.1.map Prod.fst)))
    (fun s => ⟨⟨[], rfl⟩, fun h => Or.inl h⟩) ?_ ?_ A s
  · rintro a b e ⟨⟨U, hU⟩, hab⟩ ⟨⟨U', hU'⟩, hbe⟩
    refine ⟨⟨U' ++ U, by rw [hU', hU, List.append_assoc]⟩, fun he => ?_⟩
    rcases hbe he with hb | hcoll
    · rcases hab hb with ha | hcoll'
      · exact Or.inl ha
      · right; rw [hU']; exact hmono _ _ hcoll'
    · exact Or.inr hcoll
  · rintro ⟨T, fl⟩ d x hx
    have hnc : consistent c T d = false →
        QueryCollision c (((d, x.1) :: T).map Prod.fst) ∧
        ∀ r, List.lookup d T = some r → QueryCollision c (T.map Prod.fst) := by
      intro hc
      simp only [consistent, decide_eq_false_iff_not, not_forall] at hc
      obtain ⟨p, hp, hcp, hpd⟩ := hc
      have hpm : p.1 ∈ ((d, x.1) :: T).map Prod.fst :=
        List.mem_cons_of_mem _ (List.mem_map_of_mem hp)
      refine ⟨⟨p.1, hpm, d, by simp, hpd, hcp⟩, fun r hr => ?_⟩
      exact ⟨p.1, List.mem_map_of_mem hp, d,
        List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup_eq_some T d r hr), hpd, hcp⟩
    unfold idealFlag at hx
    cases hl : List.lookup d T with
    | some r =>
      rw [hl] at hx
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨⟨[], rfl⟩, fun h => ?_⟩
      cases hcT : consistent c T d
      · exact Or.inr ((hnc hcT).2 r hl)
      · simp_all
    | none =>
      rw [hl] at hx
      simp only [PMF.support_map, PMF.support_uniformOfFintype, Set.top_eq_univ,
        Set.image_univ, Set.mem_range] at hx
      obtain ⟨r, rfl⟩ := hx
      refine ⟨⟨[(d, r)], rfl⟩, fun h => ?_⟩
      cases hcT : consistent c T d
      · exact Or.inr (hnc hcT).1
      · simp_all

/-- **Composition bound.** Averaged over a uniform `φ`, the lazy random function on `B`
queried through `c φ` is distinguished from the lazy random function on `M` with advantage
at most the expected probability, over the final table of the ideal run, that `c φ` maps
two distinct recorded queries to the same point. -/
theorem advantage_compose_le {F : Type} [Fintype F] [Nonempty F] (c : F → M → B)
    (A : OracleAdv M R Bool) :
    Advantage (liftPMF ((PMF.uniformOfFintype F).bind fun φ =>
        (OracleAdv.run (fun t d => rfOracle t (c φ d)) A []).map Prod.fst)) (rfGame A) ≤
      ∑' x, OracleAdv.run rfOracle A [] x *
        (PMF.uniformOfFintype F).toOuterMeasure
          {φ | QueryCollision (c φ) (x.2.map Prod.fst)} := by
  set u := PMF.uniformOfFintype F
  set p₁ : F → PMF (Bool × (List (M × R) × Bool)) := fun φ =>
    OracleAdv.run (realFlag (c φ)) A ([], false)
  set p₂ : F → PMF (Bool × (List (M × R) × Bool)) := fun φ =>
    OracleAdv.run (idealFlag (c φ)) A ([], false)
  have hagree : ∀ φ a t, p₁ φ (a, (t, false)) = p₂ φ (a, (t, false)) := fun φ a t =>
    OracleAdv.run_apply_flag_false_eq _ _ (realFlag_apply_true_false (c φ))
      (idealFlag_apply_true_false (c φ)) (realFlag_apply_false_eq (c φ)) A _ a t
  have hreal : ∀ φ, (OracleAdv.run (fun t d => rfOracle t (c φ d)) A []).map Prod.fst =
      (p₁ φ).map Prod.fst := by
    intro φ
    have h := OracleAdv.run_map_state (realFlag (c φ)) (fun t d => rfOracle t (c φ d))
      (fun s => projC (c φ) s.1) (realFlag_map (c φ)) A ([], false)
    change _ = OracleAdv.run _ A [] at h
    rw [← h, PMF.map_comp]
    rfl
  have hideal : ∀ φ, (OracleAdv.run rfOracle A []).map Prod.fst = (p₂ φ).map Prod.fst := by
    intro φ
    have h := OracleAdv.run_map_state (idealFlag (c φ)) rfOracle Prod.fst
      (idealFlag_map (c φ)) A ([], false)
    change _ = OracleAdv.run _ A [] at h
    rw [← h, PMF.map_comp]
    rfl
  have hL : prTrue (liftPMF (u.bind fun φ =>
      (OracleAdv.run (fun t d => rfOracle t (c φ d)) A []).map Prod.fst)) Heap.empty =
      ∑' φ, u φ * (p₁ φ).toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} := by
    simp only [hreal, ← PMF.map_bind, prTrue_liftPMF_map, PMF.toOuterMeasure_bind_apply]
    rfl
  have hR : prTrue (rfGame A) Heap.empty =
      ∑' φ, u φ * (p₂ φ).toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} := by
    have h1 : ∀ φ, (p₂ φ).toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} =
        (OracleAdv.run rfOracle A []).toOuterMeasure {x | x.1 = true} := by
      intro φ
      have := congrArg (fun q : PMF Bool => q.toOuterMeasure {true}) (hideal φ)
      simp only [PMF.toOuterMeasure_map_apply] at this
      exact this.symm
    simp only [h1, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    unfold rfGame
    simp_all [prTrue_liftPMF_map]
  set e := ∑' φ, u φ * (p₂ φ).toOuterMeasure {x | x.2.2 = true} with he
  have hle₁ : ∑' φ, u φ * (p₁ φ).toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} ≤
      ∑' φ, u φ * (p₂ φ).toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} + e := by
    rw [he, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun φ => by
      rw [← mul_add]; gcongr; exact toOuterMeasure_le_add_flag _ _ (hagree φ) _
  have hle₂ : ∑' φ, u φ * (p₂ φ).toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} ≤
      ∑' φ, u φ * (p₁ φ).toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} + e := by
    rw [he, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun φ => ?_
    rw [← mul_add, ← toOuterMeasure_flag_eq _ _ (hagree φ)]
    gcongr
    exact toOuterMeasure_le_add_flag _ _ (fun a t => (hagree φ a t).symm) _
  have hflag : e ≤ ∑' φ, u φ * (OracleAdv.run rfOracle A []).toOuterMeasure
      {x | QueryCollision (c φ) (x.2.map Prod.fst)} := by
    refine ENNReal.tsum_le_tsum fun φ => ?_
    gcongr
    have hmap := OracleAdv.run_map_state (idealFlag (c φ)) rfOracle Prod.fst
      (idealFlag_map (c φ)) A ([], false)
    rw [← hmap, PMF.toOuterMeasure_map_apply]
    refine PMF.toOuterMeasure_mono _ fun x ⟨hx, hsupp⟩ => ?_
    rcases (idealFlag_support_rel (c φ) A ([], false) x hsupp).2 hx with h | h
    · exact (Bool.false_ne_true h).elim
    · exact h
  have hfub : ∑' φ, u φ * (OracleAdv.run rfOracle A []).toOuterMeasure
      {x | QueryCollision (c φ) (x.2.map Prod.fst)} = ∑' x, OracleAdv.run rfOracle A [] x *
        u.toOuterMeasure {φ | QueryCollision (c φ) (x.2.map Prod.fst)} := by
    simp only [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun x => tsum_congr fun φ => ?_
    by_cases h : QueryCollision (c φ) (x.2.map Prod.fst)
    · have h' : φ ∈ {φ | QueryCollision (c φ) (x.2.map Prod.fst)} := h
      have h'' : x ∈ {x : Bool × List (M × R) | QueryCollision (c φ) (x.2.map Prod.fst)} := h
      (clear he; simp_all [mul_comm])
    · have h' : φ ∉ {φ | QueryCollision (c φ) (x.2.map Prod.fst)} := h
      have h'' : x ∉ {x : Bool × List (M × R) | QueryCollision (c φ) (x.2.map Prod.fst)} := h
      (clear he; simp_all [mul_zero])
  simp only [Advantage, hL, hR]
  refine max_le (tsub_le_iff_left.mpr ?_) (tsub_le_iff_left.mpr ?_)
  · exact hle₁.trans (add_le_add le_rfl (hflag.trans hfub.le))
  · exact hle₂.trans (add_le_add le_rfl (hflag.trans hfub.le))

omit [DecidableEq B] in
/-- A function `h` of the table bounded by a monotone function `Φ` of its length has
expectation at most `Φ (|t| + n)` over the final table of a lazy random function run from
`t` by an adversary asking at most `n` queries. -/
theorem tsum_run_rfOracle_le (h : List (M × R) → ℝ≥0∞) (Φ : ℕ → ℝ≥0∞) (hΦ : Monotone Φ)
    (hh : ∀ T, h T ≤ Φ T.length) (A : OracleAdv M R α) (n : ℕ) (hA : A.IsQueryBound n)
    (t : List (M × R)) :
    ∑' x, OracleAdv.run rfOracle A t x * h x.2 ≤ Φ (t.length + n) := by
  induction A generalizing n t with
  | ret a =>
    rw [OracleAdv.run_ret, tsum_pure_mul (g := fun x : α × List (M × R) => h x.2)]
    exact (hh t).trans (hΦ (by omega))
  | rand p k ih =>
    rw [OracleAdv.run_rand, tsum_bind_mul]
    calc ∑' b, p b * ∑' x, OracleAdv.run rfOracle (k b) t x * h x.2
        ≤ ∑' b, p b * Φ (t.length + n) :=
          ENNReal.tsum_le_tsum fun b => by gcongr; exact ih b n (hA b) t
      _ = Φ (t.length + n) := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    cases n with
    | zero => exact hA.elim
    | succ n =>
    cases hl : List.lookup d t with
    | some r =>
      have hq : rfOracle t d = PMF.pure (r, t) := by simp only [rfOracle, hl]
      rw [OracleAdv.run_query, hq, PMF.pure_bind]
      exact (ih r n (hA r) t).trans (hΦ (by omega))
    | none =>
      have hq : rfOracle t d = (PMF.uniformOfFintype R).map fun r => (r, (d, r) :: t) := by
        grind [rfOracle]
      rw [OracleAdv.run_query, hq, PMF.bind_map, tsum_bind_mul]
      calc ∑' r, PMF.uniformOfFintype R r * ∑' x, OracleAdv.run rfOracle (k r) ((d, r) :: t) x *
            h x.2
          ≤ ∑' r, PMF.uniformOfFintype R r * Φ (t.length + (n + 1)) := by
            refine ENNReal.tsum_le_tsum fun r => ?_
            gcongr
            refine (ih r n (hA r) _).trans (hΦ ?_)
            simp only [List.length_cons]
            omega
        _ = Φ (t.length + (n + 1)) := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Compose

/-! ## Hash then random function -/

section HashRF

variable {K M B R : Type} [Fintype K] [Nonempty K] [DecidableEq M] [DecidableEq B]
  [Fintype R] [Nonempty R]

/-- The lazy random function on `B` queried at `H k m` for a uniform key `k`, against `A`. -/
noncomputable def hashRFGame (H : K → M → B) (A : OracleAdv M R Bool) : SPComp Bool :=
  liftPMF ((PMF.uniformOfFintype K).bind fun k =>
    (OracleAdv.run rfOracle (OracleAdv.mapQuery (H k) A) []).map Prod.fst)

/-- The advantage of `A` in distinguishing the hashed random function from the lazy random
function on `M`. -/
noncomputable def HashRF_Advantage (H : K → M → B) (A : OracleAdv M R Bool) : ℝ≥0∞ :=
  Advantage (hashRFGame H A) (rfGame A)

/-- **Hash then random function.** For an `ε`-almost-universal hash family `H` and an
adversary asking at most `q` adaptive queries, the random function on `B` queried at
`H k m` for a uniform hidden key `k` is distinguished from a random function on `M` with
advantage at most `q(q-1)/2 · ε`. -/
theorem hashRF_advantage_le {H : K → M → B} {ε : ℝ≥0∞} (hH : IsAlmostUniversal H ε)
    (A : OracleAdv M R Bool) (q : ℕ) (hA : A.IsQueryBound q) :
    HashRF_Advantage H A ≤ ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) * ε := by
  have hmono : Monotone fun n : ℕ => ((n * (n - 1) / 2 : ℕ) : ℝ≥0∞) * ε := fun a b hab =>
    mul_le_mul_left (Nat.cast_le.mpr
      (Nat.div_le_div_right (Nat.mul_le_mul hab (Nat.sub_le_sub_right hab 1)))) ε
  unfold HashRF_Advantage hashRFGame
  simp only [OracleAdv.run_mapQuery]
  refine (advantage_compose_le H A).trans ((tsum_run_rfOracle_le
    (fun T => (PMF.uniformOfFintype K).toOuterMeasure
      {k | QueryCollision (H k) (T.map Prod.fst)}) _ hmono (fun T => ?_) A q hA []).trans_eq
    (by rw [List.length_nil, zero_add]))
  simpa using prob_queryCollision_le hH (T.map Prod.fst)

end HashRF

/-! ## Hash then PRF -/

section HashPRF

variable {K₁ K₂ M B R : Type} [Fintype K₁] [Nonempty K₁] [Fintype K₂] [Nonempty K₂]

/-- The keyed function `F k₁ ∘ H k₂` with the key pair `(k₁, k₂)`. -/
def hashPRF (F : K₁ → B → R) (H : K₂ → M → B) (k : K₁ × K₂) (m : M) : R :=
  F k.1 (H k.2 m)

/-- Reduction to the PRF security of `F`: sample the hash key `k₂` and ask each query `m`
of `A` at `H k₂ m`. -/
noncomputable def hashRed (H : K₂ → M → B) {R : Type} (A : OracleAdv M R Bool) :
    OracleAdv B R Bool :=
  .rand (PMF.uniformOfFintype K₂) fun k₂ => OracleAdv.mapQuery (H k₂) A

theorem isQueryBound_hashRed (H : K₂ → M → B) {A : OracleAdv M R Bool} {q : ℕ}
    (hA : A.IsQueryBound q) : (hashRed H A).IsQueryBound q :=
  fun _ => OracleAdv.isQueryBound_mapQuery _ hA

derive_timed hashRed

/-- For an adversary of time `T` with at most `q` queries and a hash cost at most `t₀`, the
costed reduction `hashRed.timed` runs in time at most `1 + T + q (2 + t₀)`: one unit for
sampling the hash key and `2 + t₀` for renaming each query. -/
theorem hashRed.timeBound_timed (H : K₂ → M → B) (HCost : K₂ → M → ℕ) {t₀ : ℕ}
    (hc : ∀ k m, HCost k m ≤ t₀) {A : OracleAdv.Timed M R Bool} {T q : ℕ}
    (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (hashRed.timed H HCost A) (1 + T + q * (2 + t₀)) := by
  unfold hashRed.timed
  exact ⟨Nat.zero_le _, by omega, fun k₂ => ⟨Nat.zero_le _,
    (OracleAdv.Timed.timeBound_mapQuery (H k₂) _ (fun m => Nat.add_le_add_left (hc k₂ m) 2)
      hA hq).mono (by simp only; omega)⟩⟩

theorem realGame_hashPRF_eq [DecidableEq M] [DecidableEq R] [Fintype R] [Nonempty R]
    (F : K₁ → B → R) (H : K₂ → M → B) (A : OracleAdv M R Bool) :
    realGame (hashPRF F H) A = realGame F (hashRed H A) := by
  unfold realGame hashRed
  congr 1
  simp only [OracleAdv.run_rand, OracleAdv.run_mapQuery, PMF.map_bind]
  rw [PMF.uniform_prod_eq_bind, PMF.bind_bind]
  refine congrArg _ (funext fun k₁ => ?_)
  rw [PMF.bind_map]
  rfl

theorem rfGame_hashRed_eq [DecidableEq B] [DecidableEq R] [Fintype R] [Nonempty R]
    (H : K₂ → M → B) (A : OracleAdv M R Bool) :
    rfGame (hashRed H A) = hashRFGame H A := by
  unfold rfGame hashRFGame hashRed
  simp only [OracleAdv.run_rand, PMF.map_bind]

/-- **Hash then PRF.** For a keyed function `F`, an `ε`-almost-universal hash family `H` and
an adversary asking at most `q` adaptive queries, the PRF advantage of `F k₁ ∘ H k₂` is at
most the PRF advantage of `F` against `hashRed H A` (at most `q` queries) plus
`q(q-1)/2 · ε`. -/
theorem hashPRF_advantage_le [DecidableEq M] [DecidableEq B] [DecidableEq R] [Fintype R]
    [Nonempty R] (F : K₁ → B → R) {H : K₂ → M → B} {ε : ℝ≥0∞}
    (hH : IsAlmostUniversal H ε) (A : OracleAdv M R Bool) (q : ℕ) (hA : A.IsQueryBound q) :
    PRF_q_Advantage (hashPRF F H) A ≤
      PRF_q_Advantage F (hashRed H A) + ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) * ε := by
  unfold PRF_q_Advantage
  rw [realGame_hashPRF_eq]
  refine (advantage_triangle _ (rfGame (hashRed H A)) _).trans (add_le_add le_rfl ?_)
  rw [rfGame_hashRed_eq]
  exact hashRF_advantage_le hH A q hA

end HashPRF

end CatCrypt.Crypto.HashThenRF
