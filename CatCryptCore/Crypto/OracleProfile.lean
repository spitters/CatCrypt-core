/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DillerNahm
public import CatCryptCore.Crypto.OracleQueryVec
public import CatCryptCore.Crypto.OracleSubst

/-!
# The query profile of an oracle adversary

The profile of an adversary is the set of pairs (multiset of queries, result) over its paths. Query
bounds, per-oracle counts and provenance are evaluations of it, in the style of the provenance
semirings of Green, Karvounarakis and Tannen (*Provenance semirings*, PODS 2007): for each result,
the profile is a polynomial with Boolean coefficients in the queries, where a union is the addition
and the pointwise sum of multisets is the multiplication, and a charge is a homomorphism to the
semiring `(ℕ∞, ⊔, +)`.

A query bound quantifies over paths, and a query node with an empty answer type has no path below
it, so that the evaluation theorems from the profile to a bound take `[Nonempty R]`.

The queries of a path forget the answers, so that the profile of a substitution is not a function
of the profile of the adversary. The set `traces A` keeps the answers in order, and
`mem_profile_simulate_iff` and `mem_profile_subst_iff` state the exact laws on it. The state of a
simulation is threaded along the order of a trace (`Threads`). The law of Moss and von Glehn
(*Dialectica models of type theory*, LICS 2018), where a substitution is `Multiset.bind` and
composes as `DNLens.comp`, holds when each program asks a fixed multiset of queries for each of its
answers (`profile_subst_of_demand`).

`Within c A n Q` is the budget-passing fold at the charge `c`: it says that each path of `A` costs
at most `n` and that the result `a` of the path satisfies `Q a` at the budget left. Unlike a bound
at a fixed budget, it has an equation at every constructor and at `bind`.

## Main definitions

* `OracleAdv.charge` — the value of a multiset of queries at a charge;
* `OracleAdv.profile`, `OracleAdv.traces` — the paths of an adversary, without and with answers;
* `OracleAdv.Threads` — the state of a simulation along a trace;
* `OracleAdv.demandAt`, `OracleAdv.demandLens` — the demand of a program and its Diller–Nahm form;
* `OracleAdv.Within` — the budget-passing fold.

## Main results

* `isQueryBoundBy_iff_profile`, `isQueryBound_iff_profile`, `isQueryBound₂_iff_profile`,
  `mayOnlyCall_iff_profile`, `isQueryProfile_iff_profile` — the notions as evaluations;
* `cost_eq_iSup_profile` — the cost fold is the supremum of the charge over the profile;
* `mem_profile_bind`, `profile_ite`, `profile_mapQuery`, `profile_eq_image_traces` — the laws;
* `mem_profile_simulate_iff`, `mem_profile_subst_iff`, `profile_subst_subset`,
  `profile_subst_of_demand` — the substitution laws;
* `demandLens_comp`, `charge_bind_eq_price` — the Diller–Nahm form of a fixed demand;
* `within_iff_profile`, `within_bind`, `isQueryBoundBy_iff_within` — the fold and its equations.

Search words: query profile, provenance semiring, path multiset, trace, Diller–Nahm, query bound,
budget-passing fold, per-oracle count, correlated bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

open scoped Pointwise

variable {D D' R R' α β : Type}

/-! ## The value of a multiset at a charge -/

/-- The sum of the charges of a multiset of queries. -/
def charge (c : D → ℕ) (m : Multiset D) : ℕ := (m.map c).sum

/-- The empty multiset costs nothing. -/
@[simp] theorem charge_zero (c : D → ℕ) : charge c 0 = 0 := by simp [charge]

/-- A query adds its charge. -/
@[simp] theorem charge_cons (c : D → ℕ) (d : D) (m : Multiset D) :
    charge c (d ::ₘ m) = c d + charge c m := by simp [charge]

/-- The charge is additive. -/
@[simp] theorem charge_add (c : D → ℕ) (m m' : Multiset D) :
    charge c (m + m') = charge c m + charge c m' := by simp [charge]

/-- The charge `1` is the cardinality. -/
theorem charge_one (m : Multiset D) : charge (fun _ => 1) m = Multiset.card m := by
  simp [charge]

/-- The charge of a bound multiset is the charge at the charges of the demands. -/
theorem charge_bind (c : D' → ℕ) (m : Multiset D) (δ : D → Multiset D') :
    charge c (m.bind δ) = charge (fun d => charge c (δ d)) m := by
  simp [charge, Multiset.map_bind, Multiset.sum_bind]

/-! ## The profile -/

/-- The set of pairs (multiset of queries, result) over the paths of an adversary. -/
def profile : OracleAdv D R α → Set (Multiset D × α)
  | ret a => {(0, a)}
  | rand _ k => ⋃ b, profile (k b)
  | query d k => ⋃ r, (fun x => (d ::ₘ x.1, x.2)) '' profile (k r)

/-- The profile of a leaf is one path without queries. -/
@[simp] theorem mem_profile_ret {a : α} {x : Multiset D × α} :
    x ∈ profile (ret a : OracleAdv D R α) ↔ x = (0, a) := Iff.rfl

/-- The profile of a sampling node is the union over the samples. -/
@[simp] theorem mem_profile_rand {γ : Type} {p : PMF γ} {k : γ → OracleAdv D R α}
    {x : Multiset D × α} : x ∈ profile (rand p k) ↔ ∃ b, x ∈ profile (k b) := by
  simp [profile]

/-- A query adds the query to each path of each answer. -/
@[simp] theorem mem_profile_query {d : D} {k : R → OracleAdv D R α} {x : Multiset D × α} :
    x ∈ profile (query d k) ↔ ∃ r, ∃ y ∈ profile (k r), x = (d ::ₘ y.1, y.2) := by
  simp [profile, eq_comm]

/-- Each adversary has a path when the answer type is inhabited. -/
theorem profile_nonempty [Nonempty R] (A : OracleAdv D R α) : (profile A).Nonempty := by
  induction A with
  | ret a => exact ⟨(0, a), rfl⟩
  | rand p k ih =>
    obtain ⟨b, -⟩ := p.support_nonempty
    obtain ⟨x, hx⟩ := ih b
    exact ⟨x, mem_profile_rand.2 ⟨b, hx⟩⟩
  | query d k ih =>
    obtain ⟨r⟩ := ‹Nonempty R›
    obtain ⟨x, hx⟩ := ih r
    exact ⟨_, mem_profile_query.2 ⟨r, x, hx, rfl⟩⟩

/-- The profile of a sequential composition is the sums of the paths, the result of the first path
being passed to the second. -/
theorem mem_profile_bind {A : OracleAdv D R α} {f : α → OracleAdv D R β} {x : Multiset D × β} :
    x ∈ profile (A.bind f) ↔
      ∃ y ∈ profile A, ∃ z ∈ profile (f y.2), x = (y.1 + z.1, z.2) := by
  induction A generalizing x with
  | ret a =>
    simp only [bind, mem_profile_ret, exists_eq_left, zero_add]
    exact ⟨fun h => ⟨x, h, rfl⟩, by rintro ⟨z, hz, rfl⟩; exact hz⟩
  | rand p k ih =>
    simp only [bind, mem_profile_rand, ih]
    constructor
    · rintro ⟨b, y, hy, z, hz, rfl⟩
      exact ⟨y, ⟨b, hy⟩, z, hz, rfl⟩
    · rintro ⟨y, ⟨b, hy⟩, z, hz, rfl⟩
      exact ⟨b, y, hy, z, hz, rfl⟩
  | query d k ih =>
    simp only [bind, mem_profile_query, ih]
    constructor
    · rintro ⟨r, y, ⟨u, hu, v, hv, rfl⟩, rfl⟩
      exact ⟨(d ::ₘ u.1, u.2), ⟨r, u, hu, rfl⟩, v, hv, by simp⟩
    · rintro ⟨y, ⟨r, u, hu, rfl⟩, z, hz, rfl⟩
      exact ⟨r, (u.1 + z.1, z.2), ⟨u, hu, z, hz, rfl⟩, by simp⟩

/-- The profile of a branch is the profile of the arm taken. -/
theorem profile_ite (p : Prop) [Decidable p] (A B : OracleAdv D R α) :
    profile (if p then A else B) = if p then profile A else profile B :=
  apply_ite profile p A B

/-- Renaming queries renames the multisets of the profile. -/
theorem profile_mapQuery (g : D → D') (A : OracleAdv D R α) :
    profile (mapQuery g A) = (fun x => (x.1.map g, x.2)) '' profile A := by
  ext x
  induction A generalizing x with
  | ret a => simp [mapQuery, eq_comm]
  | rand p k ih =>
    simp only [mapQuery, mem_profile_rand, ih, Set.mem_image]
    constructor
    · rintro ⟨b, y, hy, rfl⟩
      exact ⟨y, ⟨b, hy⟩, rfl⟩
    · rintro ⟨y, ⟨b, hy⟩, rfl⟩
      exact ⟨b, y, hy, rfl⟩
  | query d k ih =>
    simp only [mapQuery, mem_profile_query, ih, Set.mem_image]
    constructor
    · rintro ⟨r, y, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨(d ::ₘ u.1, u.2), ⟨r, u, hu, rfl⟩, by simp⟩
    · rintro ⟨y, ⟨r, u, hu, rfl⟩, rfl⟩
      exact ⟨r, _, ⟨u, hu, rfl⟩, by simp⟩

/-! ## The notions as evaluations -/

/-- A bound at a charge bounds the charge of each path. -/
theorem IsQueryBoundBy.charge_le {c : D → ℕ} {A : OracleAdv D R α} {n : ℕ}
    (h : A.IsQueryBoundBy c n) : ∀ x ∈ profile A, charge c x.1 ≤ n := by
  induction A generalizing n with
  | ret a => rintro x rfl; simp
  | rand p k ih =>
    intro x hx
    obtain ⟨b, hb⟩ := mem_profile_rand.1 hx
    exact ih b (h b) x hb
  | query d k ih =>
    intro x hx
    obtain ⟨r, y, hy, rfl⟩ := mem_profile_query.1 hx
    have := ih r (h.2 r) y hy
    have := h.1
    simp only [charge_cons]
    omega

/-- A bound at a charge is a bound of the charge of each path. -/
theorem isQueryBoundBy_iff_profile [Nonempty R] {c : D → ℕ} {A : OracleAdv D R α} {n : ℕ} :
    A.IsQueryBoundBy c n ↔ ∀ x ∈ profile A, charge c x.1 ≤ n := by
  refine ⟨IsQueryBoundBy.charge_le, fun h => ?_⟩
  induction A generalizing n with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b fun x hx => h x (mem_profile_rand.2 ⟨b, hx⟩)
  | query d k ih =>
    have hq : ∀ r, ∀ y ∈ profile (k r), c d + charge c y.1 ≤ n := fun r y hy => by
      simpa using h _ (mem_profile_query.2 ⟨r, y, hy, rfl⟩)
    obtain ⟨r⟩ := ‹Nonempty R›
    obtain ⟨y, hy⟩ := profile_nonempty (k r)
    have := hq r y hy
    exact ⟨by omega, fun r' => ih r' fun z hz => by have := hq r' z hz; omega⟩

/-- A bound of `n` queries bounds the cardinality of each path. -/
theorem isQueryBound_iff_profile [Nonempty R] {A : OracleAdv D R α} {n : ℕ} :
    A.IsQueryBound n ↔ ∀ x ∈ profile A, Multiset.card x.1 ≤ n := by
  simp only [isQueryBound_iff_isQueryBoundBy_one, isQueryBoundBy_iff_profile, charge_one]

/-- The two-kind bound bounds the counts of the two summands on each path. -/
theorem isQueryBound₂_iff_profile [Nonempty R] {D₁ D₂ : Type} {A : OracleAdv (D₁ ⊕ D₂) R α}
    {h q : ℕ} :
    OracleForking.IsQueryBound₂ A h q ↔
      ∀ x ∈ profile A, charge chargeInl x.1 ≤ h ∧ charge chargeInr x.1 ≤ q := by
  simp only [isQueryBound₂_iff, isQueryBoundBy_iff_profile]
  grind

/-- `MayOnlyCall S A` says that each query of each path lies in `S`. -/
theorem mayOnlyCall_iff_profile [Nonempty R] {S : Set D} {A : OracleAdv D R α} :
    MayOnlyCall S A ↔ ∀ x ∈ profile A, ∀ d ∈ x.1, d ∈ S := by
  simp only [MayOnlyCall, isQueryBoundBy_iff_profile, Nat.le_zero, charge,
    Multiset.sum_eq_zero_iff, Multiset.mem_map]
  simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, outsideCharge]
  refine forall₂_congr fun x _ => forall₂_congr fun d _ => ?_
  split <;> simp [*]

/-- `IsQueryProfile` is the conjunction, over the paths, of the three bounds. -/
theorem isQueryProfile_iff_profile [Nonempty R] {D₁ D₂ : Type} {A : OracleAdv (D₁ ⊕ D₂) R α}
    {a b n : ℕ} :
    IsQueryProfile A a b n ↔ ∀ x ∈ profile A,
      charge chargeInl x.1 ≤ a ∧ charge chargeInr x.1 ≤ b ∧ Multiset.card x.1 ≤ n := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩ x hx
    exact ⟨h₁.charge_le x hx, h₂.charge_le x hx, isQueryBound_iff_profile.1 h₃ x hx⟩
  · intro h
    exact ⟨isQueryBoundBy_iff_profile.2 fun x hx => (h x hx).1,
      isQueryBoundBy_iff_profile.2 fun x hx => (h x hx).2.1,
      isQueryBound_iff_profile.2 fun x hx => (h x hx).2.2⟩

/-- A bound on the cost fold is a bound of the charge of each path. -/
theorem cost_le_iff_profile [Nonempty R] (c : D → ℕ) (A : OracleAdv D R α) (n : ℕ) :
    Container.cost (AdvSig.posCost c) (toFreeM A) ≤ n ↔ ∀ x ∈ profile A, charge c x.1 ≤ n := by
  rw [← isQueryBoundBy_iff_cost_le, isQueryBoundBy_iff_profile]

/-- The cost fold at a charge is the supremum of the charge over the profile: a charge is a
homomorphism from the profile to the semiring `(ℕ∞, ⊔, +)`. -/
theorem cost_eq_iSup_profile [Nonempty R] (c : D → ℕ) (A : OracleAdv D R α) :
    Container.cost (AdvSig.posCost c) (toFreeM A) =
      ⨆ x ∈ profile A, (charge c x.1 : ℕ∞) := by
  have key : ∀ n : ℕ, Container.cost (AdvSig.posCost c) (toFreeM A) ≤ n ↔
      (⨆ x ∈ profile A, (charge c x.1 : ℕ∞)) ≤ n := fun n => by
    rw [cost_le_iff_profile]
    simp only [iSup_le_iff, Nat.cast_le]
  refine le_antisymm ?_ ?_
  · induction h : (⨆ x ∈ profile A, (charge c x.1 : ℕ∞)) using ENat.recTopCoe with
    | top => exact le_top
    | coe n => exact (key n).2 h.le
  · induction h : Container.cost (AdvSig.posCost c) (toFreeM A) using ENat.recTopCoe with
    | top => exact le_top
    | coe n => exact (key n).1 h.le

/-! ## Traces -/

/-- The set of pairs (queries with their answers in order, result) over the paths of an
adversary. -/
def traces : OracleAdv D R α → Set (List (D × R) × α)
  | ret a => {([], a)}
  | rand _ k => ⋃ b, traces (k b)
  | query d k => ⋃ r, (fun x => ((d, r) :: x.1, x.2)) '' traces (k r)

/-- The profile is the set of traces with the answers and the order forgotten. -/
theorem profile_eq_image_traces (A : OracleAdv D R α) :
    profile A = (fun x => (((x.1.map Prod.fst : List D) : Multiset D), x.2)) '' traces A := by
  ext x
  induction A generalizing x with
  | ret a => simp [traces]
  | rand p k ih =>
    simp only [mem_profile_rand, ih, traces, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨b, y, hy, rfl⟩
      exact ⟨y, ⟨b, hy⟩, rfl⟩
    · rintro ⟨y, ⟨b, hy⟩, rfl⟩
      exact ⟨b, y, hy, rfl⟩
  | query d k ih =>
    simp only [mem_profile_query, ih, traces, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨r, y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨_, ⟨r, t, ht, rfl⟩, by simp⟩
    · rintro ⟨y, ⟨r, t, ht, rfl⟩, rfl⟩
      exact ⟨r, _, ⟨t, ht, rfl⟩, by simp⟩

/-- `Threads impl t s m s'`: the programs of `impl` answer the queries of the trace `t` in order
with the answers of `t`, from the state `s` to the state `s'`, asking the multiset `m` of queries
in all. -/
def Threads {S : Type} (impl : S → D → OracleAdv D' R' (R × S)) :
    List (D × R) → S → Multiset D' → S → Prop
  | [], s, m, s' => m = 0 ∧ s' = s
  | (d, r) :: t, s, m, s' =>
    ∃ y s₁ z, (y, (r, s₁)) ∈ profile (impl s d) ∧ Threads impl t s₁ z s' ∧ m = y + z

/-- The exact law of a simulation: a path of `simulate impl A s` is a trace of `A` whose answers
the programs give from the state `s`, the state being threaded in the order of the trace. -/
theorem mem_profile_simulate_iff {S : Type} {impl : S → D → OracleAdv D' R' (R × S)}
    {A : OracleAdv D R α} {s : S} {x : Multiset D' × (α × S)} :
    x ∈ profile (simulate impl A s) ↔
      ∃ t, (t, x.2.1) ∈ traces A ∧ Threads impl t s x.1 x.2.2 := by
  obtain ⟨m, a, s'⟩ := x
  induction A generalizing m a s s' with
  | ret b =>
    simp only [simulate, mem_profile_ret, traces, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨[], ⟨rfl, rfl⟩, rfl, rfl⟩
    · rintro ⟨t, ⟨rfl, rfl⟩, h₁, h₂⟩
      exact ⟨h₁, rfl, h₂⟩
  | rand p k ih =>
    simp only [simulate, mem_profile_rand, ih, traces, Set.mem_iUnion]
    grind
  | query d k ih =>
    simp only [simulate, mem_profile_bind, traces, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨⟨y, r, s₁⟩, hy, ⟨z, a', s₂⟩, hz, h⟩
      obtain ⟨t, ht, hth⟩ := (ih r _ _ _).1 hz
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨(d, r) :: t, ⟨r, (t, _), ht, rfl⟩, y, s₁, z, hy, hth, rfl⟩
    · rintro ⟨t, ⟨r, ⟨t', a'⟩, hu, hu'⟩, hth⟩
      simp only [Prod.mk.injEq] at hu'
      obtain ⟨rfl, rfl⟩ := hu'
      obtain ⟨y, s₁, z, hy, ht, rfl⟩ := hth
      exact ⟨(y, (r, s₁)), hy, (z, (_, s')), (ih r _ _ _).2 ⟨t', hu, ht⟩, rfl⟩

/-! ## The demand of a program -/

/-- The multisets of queries with which the program `impl d` gives the answer `r`. -/
def demandAt (impl : D → OracleAdv D' R' R) (d : D) (r : R) : Set (Multiset D') :=
  {m | (m, r) ∈ profile (impl d)}

/-- The multisets of queries of the paths of the program `impl d`. -/
def demand (impl : D → OracleAdv D' R' R) (d : D) : Set (Multiset D') :=
  Prod.fst '' profile (impl d)

/-- The exact law of a substitution: a path of `subst impl A` is a trace of `A` together with, for
each of its queries, a path of the program that gives the answer of the trace. -/
theorem mem_profile_subst_iff {impl : D → OracleAdv D' R' R} {A : OracleAdv D R α}
    {x : Multiset D' × α} :
    x ∈ profile (subst impl A) ↔
      ∃ t, (t, x.2) ∈ traces A ∧ x.1 ∈ (t.map fun e => demandAt impl e.1 e.2).sum := by
  obtain ⟨m, a⟩ := x
  induction A generalizing m a with
  | ret b =>
    simp only [subst_ret, mem_profile_ret, traces, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨[], ⟨rfl, rfl⟩, by simp⟩
    · rintro ⟨t, ⟨rfl, rfl⟩, h⟩
      exact ⟨by simpa using h, rfl⟩
  | rand p k ih =>
    simp only [subst_rand, mem_profile_rand, ih, traces, Set.mem_iUnion]
    grind
  | query d k ih =>
    simp only [subst_query, mem_profile_bind, traces, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨y, hy, z, hz, h⟩
      obtain ⟨t, ht, hm⟩ := (ih y.2 (m := z.1) (a := z.2)).1 hz
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, ha⟩ := h
      refine ⟨(d, y.2) :: t, ⟨y.2, (t, a), by simpa [ha] using ht, rfl⟩, ?_⟩
      simp only [List.map_cons, List.sum_cons]
      exact Set.add_mem_add (by simpa [demandAt] using hy) hm
    · rintro ⟨t, ⟨r, ⟨t', a'⟩, hu, hu'⟩, hm⟩
      simp only [Prod.mk.injEq] at hu'
      obtain ⟨rfl, rfl⟩ := hu'
      simp only [List.map_cons, List.sum_cons] at hm
      obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.1 hm
      exact ⟨(y, r), hy, (z, _), (ih r _ _).2 ⟨t', hu, hz⟩, rfl⟩

/-- The law of a substitution on the profile alone is an inclusion: a path of `subst impl A` lies
over a path of `A`, each query being replaced by the multiset of a path of its program. -/
theorem profile_subst_subset {impl : D → OracleAdv D' R' R} {A : OracleAdv D R α}
    {x : Multiset D' × α} (hx : x ∈ profile (subst impl A)) :
    ∃ m, (m, x.2) ∈ profile A ∧ x.1 ∈ (m.map (demand impl)).sum := by
  obtain ⟨m', a⟩ := x
  induction A generalizing m' a with
  | ret b =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_profile_ret.1 hx)
    exact ⟨0, rfl, by simp⟩
  | rand p k ih =>
    rw [subst_rand] at hx
    obtain ⟨b, hb⟩ := mem_profile_rand.1 hx
    obtain ⟨m, hm, hm'⟩ := ih b _ _ hb
    exact ⟨m, mem_profile_rand.2 ⟨b, hm⟩, hm'⟩
  | query d k ih =>
    rw [subst_query, mem_profile_bind] at hx
    obtain ⟨y, hy, z, hz, h⟩ := hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨m, hm, hm'⟩ := ih y.2 _ _ hz
    refine ⟨d ::ₘ m, mem_profile_query.2 ⟨y.2, (m, z.2), hm, rfl⟩, ?_⟩
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact Set.add_mem_add ⟨y, hy, rfl⟩ hm'

/-- When the program `impl d` asks exactly the multiset `δ d` for each of its answers, the profile
of a substitution is the image of the profile under `Multiset.bind`. -/
theorem profile_subst_of_demand {impl : D → OracleAdv D' R' R} {δ : D → Multiset D'}
    (h : ∀ d r, demandAt impl d r = {δ d}) (A : OracleAdv D R α) :
    profile (subst impl A) = (fun x => (x.1.bind δ, x.2)) '' profile A := by
  have hd : ∀ d y r, (y, r) ∈ profile (impl d) ↔ y = δ d := fun d y r => by
    change y ∈ demandAt impl d r ↔ _
    rw [h]
    rfl
  ext x
  induction A generalizing x with
  | ret a => simp [eq_comm]
  | rand p k ih =>
    simp only [subst_rand, mem_profile_rand, ih, Set.mem_image]
    constructor
    · rintro ⟨b, y, hy, rfl⟩
      exact ⟨y, ⟨b, hy⟩, rfl⟩
    · rintro ⟨y, ⟨b, hy⟩, rfl⟩
      exact ⟨b, y, hy, rfl⟩
  | query d k ih =>
    simp only [subst_query, mem_profile_bind, ih, Set.mem_image, mem_profile_query]
    constructor
    · rintro ⟨⟨y, r⟩, hy, z, ⟨u, hu, rfl⟩, rfl⟩
      obtain rfl := (hd d y r).1 hy
      exact ⟨(d ::ₘ u.1, u.2), ⟨r, u, hu, rfl⟩, by simp⟩
    · rintro ⟨y, ⟨r, u, hu, rfl⟩, rfl⟩
      exact ⟨(δ d, r), (hd d _ r).2 rfl, _, ⟨u, hu, rfl⟩, by simp⟩

/-- A fixed demand as a Diller–Nahm morphism: the object with one shape and positions `D'` maps to
the one with positions `D`, a position `d` demanding the multiset `δ d`. -/
def demandLens (δ : D → Multiset D') :
    Container.DNLens ⟨PUnit.{1}, fun _ => D'⟩ ⟨PUnit.{1}, fun _ => D⟩ where
  toFunA := id
  toFunB _ := δ

/-- A substitution of fixed demands composes as the Diller–Nahm morphisms. -/
theorem demandLens_comp {D'' : Type} (δ : D → Multiset D') (δ' : D' → Multiset D'') :
    (demandLens δ).comp (demandLens δ') = demandLens fun d => (δ d).bind δ' := rfl

/-- The price of a demand is its charge, so that `DNLens.price_comp` is `charge_bind`. -/
theorem charge_bind_eq_price (c : D' → ℕ) (δ : D → Multiset D') (d : D) :
    (demandLens δ).price (fun _ => c) PUnit.unit d = charge c (δ d) := rfl

/-! ## The budget-passing fold -/

/-- `Within c A n Q`: on each path of `A` the charge `c` sums to at most `n`, and the result `a` of
the path satisfies `Q a` at the budget left. -/
def Within (c : D → ℕ) : OracleAdv D R α → ℕ → (α → ℕ → Prop) → Prop
  | ret a, n, Q => Q a n
  | rand _ k, n, Q => ∀ b, Within c (k b) n Q
  | query d k, n, Q => c d ≤ n ∧ ∀ r, Within c (k r) (n - c d) Q

/-- The fold at a leaf is the postcondition. -/
theorem within_ret {c : D → ℕ} {a : α} {n : ℕ} {Q : α → ℕ → Prop} :
    Within c (ret a : OracleAdv D R α) n Q ↔ Q a n := Iff.rfl

/-- The fold at a sampling node quantifies over the samples. -/
theorem within_rand {c : D → ℕ} {γ : Type} {p : PMF γ} {k : γ → OracleAdv D R α} {n : ℕ}
    {Q : α → ℕ → Prop} : Within c (rand p k) n Q ↔ ∀ b, Within c (k b) n Q := Iff.rfl

/-- The fold at a query subtracts its charge from the budget. -/
theorem within_query {c : D → ℕ} {d : D} {k : R → OracleAdv D R α} {n : ℕ} {Q : α → ℕ → Prop} :
    Within c (query d k) n Q ↔ c d ≤ n ∧ ∀ r, Within c (k r) (n - c d) Q := Iff.rfl

/-- The fold at a sequential composition is the fold of the first part, with the fold of the second
as its postcondition. -/
theorem within_bind {c : D → ℕ} {A : OracleAdv D R α} {f : α → OracleAdv D R β} {n : ℕ}
    {Q : β → ℕ → Prop} :
    Within c (A.bind f) n Q ↔ Within c A n fun a n' => Within c (f a) n' Q := by
  induction A generalizing n with
  | ret a => exact Iff.rfl
  | rand p k ih => exact forall_congr' fun b => ih b
  | query d k ih => exact and_congr_right fun _ => forall_congr' fun r => ih r

/-- The fold at a renaming is the fold of the adversary at the composed charge. -/
theorem within_mapQuery {c : D' → ℕ} {g : D → D'} {A : OracleAdv D R α} {n : ℕ}
    {Q : α → ℕ → Prop} : Within c (mapQuery g A) n Q ↔ Within (fun d => c (g d)) A n Q := by
  induction A generalizing n with
  | ret a => exact Iff.rfl
  | rand p k ih => exact forall_congr' fun b => ih b
  | query d k ih => exact and_congr_right fun _ => forall_congr' fun r => ih r

/-- A bound at a charge is the fold with the trivial postcondition. -/
theorem isQueryBoundBy_iff_within {c : D → ℕ} {A : OracleAdv D R α} {n : ℕ} :
    A.IsQueryBoundBy c n ↔ Within c A n fun _ _ => True := by
  induction A generalizing n with
  | ret a => exact Iff.rfl
  | rand p k ih => exact forall_congr' fun b => ih b
  | query d k ih => exact and_congr_right fun _ => forall_congr' fun r => ih r

/-- A query bound is the fold at the charge `1` with the trivial postcondition. -/
theorem isQueryBound_iff_within {A : OracleAdv D R α} {n : ℕ} :
    A.IsQueryBound n ↔ Within (fun _ => 1) A n fun _ _ => True := by
  rw [isQueryBound_iff_isQueryBoundBy_one, isQueryBoundBy_iff_within]

/-- `IsQueryProfile` is the conjunction of its three bounds. -/
theorem isQueryProfile_iff_and {D₁ D₂ : Type} {A : OracleAdv (D₁ ⊕ D₂) R α} {a b n : ℕ} :
    IsQueryProfile A a b n ↔
      A.IsQueryBoundBy chargeInl a ∧ A.IsQueryBoundBy chargeInr b ∧ A.IsQueryBound n :=
  ⟨fun h => ⟨h.inl, h.inr, h.total⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- The fold on the profile: each path is within budget and its result satisfies the postcondition
at the budget left. -/
theorem Within.mem_profile {c : D → ℕ} {A : OracleAdv D R α} {n : ℕ} {Q : α → ℕ → Prop}
    (h : Within c A n Q) : ∀ x ∈ profile A, charge c x.1 ≤ n ∧ Q x.2 (n - charge c x.1) := by
  induction A generalizing n with
  | ret a => rintro x rfl; exact ⟨by simp, by simpa using within_ret.1 h⟩
  | rand p k ih =>
    intro x hx
    obtain ⟨b, hb⟩ := mem_profile_rand.1 hx
    exact ih b (h b) x hb
  | query d k ih =>
    intro x hx
    obtain ⟨r, y, hy, rfl⟩ := mem_profile_query.1 hx
    obtain ⟨h₁, h₂⟩ := ih r (h.2 r) y hy
    have := h.1
    simp only [charge_cons]
    rw [show n - (c d + charge c y.1) = n - c d - charge c y.1 by omega]
    exact ⟨by omega, h₂⟩

/-- The fold is the evaluation of the profile at a charge and a postcondition. -/
theorem within_iff_profile [Nonempty R] {c : D → ℕ} {A : OracleAdv D R α} {n : ℕ}
    {Q : α → ℕ → Prop} :
    Within c A n Q ↔ ∀ x ∈ profile A, charge c x.1 ≤ n ∧ Q x.2 (n - charge c x.1) := by
  refine ⟨Within.mem_profile, fun h => ?_⟩
  induction A generalizing n with
  | ret a => exact within_ret.2 (by simpa using (h (0, a) rfl).2)
  | rand p k ih => exact fun b => ih b fun x hx => h x (mem_profile_rand.2 ⟨b, hx⟩)
  | query d k ih =>
    have hq : ∀ r, ∀ y ∈ profile (k r), c d + charge c y.1 ≤ n ∧
        Q y.2 (n - (c d + charge c y.1)) := fun r y hy => by
      simpa using h _ (mem_profile_query.2 ⟨r, y, hy, rfl⟩)
    obtain ⟨r⟩ := ‹Nonempty R›
    obtain ⟨y, hy⟩ := profile_nonempty (k r)
    have := (hq r y hy).1
    refine ⟨by omega, fun r' => ih r' fun z hz => ?_⟩
    obtain ⟨h₁, h₂⟩ := hq r' z hz
    rw [show n - c d - charge c z.1 = n - (c d + charge c z.1) by omega]
    exact ⟨by omega, h₂⟩

/-- A known bound enters the fold: it spends its budget `k`, and the postcondition holds at each
budget at least the rest. The charge of the bound is pointwise at least that of the fold. -/
theorem within_of_bound {c c₀ : D → ℕ} {A : OracleAdv D R α} {k n : ℕ} {Q : α → ℕ → Prop}
    (hA : A.IsQueryBoundBy c₀ k) (hc : ∀ d, c d ≤ c₀ d) (hk : k ≤ n)
    (hQ : ∀ a n', n - k ≤ n' → Q a n') : Within c A n Q := by
  induction A generalizing k n with
  | ret a => exact hQ a n (by omega)
  | rand p r ih => exact fun b => ih b (hA b) hk hQ
  | query d r ih =>
    have h₀ := hA.1
    have h₁ := hc d
    refine ⟨by omega, fun x => ih x (hA.2 x) (k := k - c₀ d) (by omega) fun a n' hn' => ?_⟩
    exact hQ a n' (by omega)

/-- Two known bounds whose charges sum to at least that of the fold enter it together. -/
theorem within_of_add {c c₁ c₂ : D → ℕ} {A : OracleAdv D R α} {a b n : ℕ} {Q : α → ℕ → Prop}
    (h₁ : A.IsQueryBoundBy c₁ a) (h₂ : A.IsQueryBoundBy c₂ b) (hc : ∀ d, c d ≤ c₁ d + c₂ d)
    (hk : a + b ≤ n) (hQ : ∀ x n', n - (a + b) ≤ n' → Q x n') : Within c A n Q :=
  within_of_bound (h₁.add h₂) hc hk hQ

end CatCrypt.Crypto.OracleAdv
