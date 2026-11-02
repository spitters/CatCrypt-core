/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.CodeCost
public import CatCryptCore.Crypto.OracleAdversaryFree
public import CatCryptCore.Crypto.OracleBadDraw

/-!
# Per-oracle query counts, provenance and the cost fold of an oracle adversary

A statement about the queries of an adversary is a bound `IsQueryBoundBy cost A n` at a charge
`cost`. Three families of charges are named here.

* The charge `oracleCharge o i` counts the queries that the labelling `o` assigns to the oracle
  `i`; a bound for each `i` is a per-oracle query count. On a sum signature the charges
  `chargeInl`, `chargeInr` count the queries of one summand.
* The charge `outsideCharge S` is `0` on `S` and `1` elsewhere; the bound `0` at it is
  `MayOnlyCall S A`, which says that every query on every path of `A` lies in `S`.
  `MayAsk A d` is the set of queries occurring in the tree of `A`, and
  `mayOnlyCall_iff_mayAsk` characterises `MayOnlyCall` by it.
* The constant charge `1` is a total count (`isQueryBound_iff_isQueryBoundBy_one`).

A total count and per-oracle counts of the same adversary are independent facts about its paths:
on branches that query different oracles, the total is the maximum of the totals of the branches
and each per-oracle count the maximum of the counts of that oracle. `IsQueryProfile` records the
three bounds together; `IsQueryProfile.bind` adds them and `IsQueryProfile.ite` takes the maximum
of each.

## Main definitions

* `OracleAdv.oracleCharge`, `OracleAdv.chargeInl`, `OracleAdv.chargeInr` — the charges selecting
  one oracle;
* `OracleAdv.outsideCharge`, `OracleAdv.MayOnlyCall`, `OracleAdv.MayAsk` — provenance of a run;
* `OracleAdv.IsQueryProfile` — a total bound with bounds for the two summands.

## Main results

* `isQueryBoundBy_iff_cost_le`, `isQueryBound_iff_cost_le` — a query bound is a bound on the cost
  fold `Container.cost` of the tree of the adversary;
* `isQueryBound₂_iff` — the two-kind bound `IsQueryBound₂` is a bound at each of `chargeInl` and
  `chargeInr`;
* `isQueryBound_of_oracleCharge`, `IsQueryBound.oracleCharge` — per-oracle counts sum to a total
  count and a total count bounds each per-oracle count;
* `mayOnlyCall_iff_mayAsk`, `mayOnlyCall_bind`, `mayOnlyCall_simulate`, `mayOnlyCall_mapQuery`,
  `mayOnlyCall_inter`, `MayOnlyCall.congr_cost` — the algebra of provenance.

Search words: query bound, per-oracle count, query vector, provenance, may only call, charge,
cost fold, correlated branches.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

variable {D D' R R' α β : Type}

/-! ## General facts on charges -/

/-- A query bound is a cost bound at the constant charge `1`. -/
theorem isQueryBound_iff_isQueryBoundBy_one {A : OracleAdv D R α} {n : ℕ} :
    A.IsQueryBound n ↔ A.IsQueryBoundBy (fun _ => 1) n := by
  refine ⟨IsQueryBound.isQueryBoundBy_one, fun h => ?_⟩
  induction A generalizing n with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (h b)
  | query d k ih =>
    obtain ⟨h₁, h₂⟩ := h
    cases n with
    | zero => grind
    | succ n => exact fun r => ih r (h₂ r)

/-- Every adversary has the bound `n` at the zero charge. -/
theorem isQueryBoundBy_zero (A : OracleAdv D R α) (n : ℕ) :
    A.IsQueryBoundBy (fun _ => 0) n := by
  induction A with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b
  | query d k ih => exact ⟨Nat.zero_le n, fun r => ih r⟩

/-- Bounds at a finite family of charges sum to a bound at the sum of the charges. -/
theorem isQueryBoundBy_sum {ι : Type} (s : Finset ι) {c : ι → D → ℕ} {v : ι → ℕ}
    {A : OracleAdv D R α} (h : ∀ i ∈ s, A.IsQueryBoundBy (c i) (v i)) :
    A.IsQueryBoundBy (fun d => ∑ i ∈ s, c i d) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isQueryBoundBy_zero A 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ## The cost fold -/

/-- A query bound at the charge `c` is a bound on the cost fold of the tree of the adversary at
the charge `AdvSig.posCost c`. -/
theorem isQueryBoundBy_iff_cost_le (c : D → ℕ) (A : OracleAdv D R α) (n : ℕ) :
    A.IsQueryBoundBy c n ↔ Container.cost (AdvSig.posCost c) (toFreeM A) ≤ n := by
  rw [isQueryBoundBy_iff_isRollBound, PFunctor.FreeM.isRollBound_iff_wpFold_charge]
  rfl

/-- A bound of `n` queries is a bound on the cost fold at the charge `1` per query. -/
theorem isQueryBound_iff_cost_le (A : OracleAdv D R α) (n : ℕ) :
    A.IsQueryBound n ↔ Container.cost (AdvSig.posCost fun _ => 1) (toFreeM A) ≤ n := by
  rw [isQueryBound_iff_isQueryBoundBy_one, isQueryBoundBy_iff_cost_le]

/-! ## Counts of one oracle -/

/-- The charge counting the queries that the labelling `o` assigns to the oracle `i`. -/
def oracleCharge {ι : Type} [DecidableEq ι] (o : D → ι) (i : ι) (d : D) : ℕ :=
  if o d = i then 1 else 0

/-- The charge counting the queries of the left summand. -/
abbrev chargeInl {D₁ D₂ : Type} : D₁ ⊕ D₂ → ℕ := Sum.elim (fun _ => 1) fun _ => 0

/-- The charge counting the queries of the right summand. -/
abbrev chargeInr {D₁ D₂ : Type} : D₁ ⊕ D₂ → ℕ := Sum.elim (fun _ => 0) fun _ => 1

/-- Per-oracle counts sum to a total count. -/
theorem isQueryBound_of_oracleCharge {ι : Type} [Fintype ι] [DecidableEq ι] (o : D → ι)
    {v : ι → ℕ} {A : OracleAdv D R α} (h : ∀ i, A.IsQueryBoundBy (oracleCharge o i) (v i)) :
    A.IsQueryBound (∑ i, v i) := by
  rw [isQueryBound_iff_isQueryBoundBy_one]
  refine (isQueryBoundBy_sum Finset.univ fun i _ => h i).of_cost_le fun d => ?_
  simp [oracleCharge]

/-- A total count bounds the count of each oracle. -/
theorem IsQueryBound.oracleCharge {ι : Type} [DecidableEq ι] (o : D → ι) (i : ι)
    {A : OracleAdv D R α} {n : ℕ} (h : A.IsQueryBound n) :
    A.IsQueryBoundBy (OracleAdv.oracleCharge o i) n := by
  refine h.isQueryBoundBy_one.of_cost_le fun d => ?_
  unfold OracleAdv.oracleCharge
  split <;> omega

/-- The two-kind bound is a bound at each of the charges of the two summands. -/
theorem isQueryBound₂_iff {D₁ D₂ : Type} {A : OracleAdv (D₁ ⊕ D₂) R α} {h q : ℕ} :
    OracleForking.IsQueryBound₂ A h q ↔
      A.IsQueryBoundBy chargeInl h ∧ A.IsQueryBoundBy chargeInr q := by
  induction A generalizing h q with
  | ret a => exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  | rand p k ih =>
    simp only [OracleForking.IsQueryBound₂, IsQueryBoundBy, ih]
    exact forall_and
  | query d k ih =>
    cases d with
    | inl d =>
      cases h with
      | zero => simp [OracleForking.IsQueryBound₂, IsQueryBoundBy]
      | succ h =>
        simp only [OracleForking.IsQueryBound₂, IsQueryBoundBy, ih, Sum.elim_inl,
          Nat.le_add_left, true_and, Nat.add_sub_cancel, Nat.zero_le, Nat.sub_zero]
        exact forall_and
    | inr d =>
      cases q with
      | zero => simp [OracleForking.IsQueryBound₂, IsQueryBoundBy]
      | succ q =>
        cases h <;>
        · simp only [OracleForking.IsQueryBound₂, IsQueryBoundBy, ih, Sum.elim_inr,
            Nat.le_add_left, true_and, Nat.add_sub_cancel, Nat.zero_le, Nat.sub_zero]
          exact forall_and

/-- Counts at the two summands sum to a total count. -/
theorem isQueryBound_of_inl_inr {D₁ D₂ : Type} {A : OracleAdv (D₁ ⊕ D₂) R α} {a b : ℕ}
    (h₁ : A.IsQueryBoundBy chargeInl a) (h₂ : A.IsQueryBoundBy chargeInr b) :
    A.IsQueryBound (a + b) := by
  rw [isQueryBound_iff_isQueryBoundBy_one]
  refine (h₁.add h₂).of_cost_le fun d => ?_
  cases d <;> simp

/-! ## A total count with per-oracle counts -/

/-- `IsQueryProfile A a b n`: every path of `A` asks at most `a` queries of the left summand, at
most `b` queries of the right summand and at most `n` queries in all. -/
structure IsQueryProfile {D₁ D₂ : Type} (A : OracleAdv (D₁ ⊕ D₂) R α) (a b n : ℕ) : Prop where
  /-- The count of the left summand. -/
  inl : A.IsQueryBoundBy chargeInl a
  /-- The count of the right summand. -/
  inr : A.IsQueryBoundBy chargeInr b
  /-- The total count. -/
  total : A.IsQueryBound n

namespace IsQueryProfile

variable {D₁ D₂ : Type}

/-- A total count alone gives a profile with that count at each summand. -/
theorem of_total {A : OracleAdv (D₁ ⊕ D₂) R α} {n : ℕ} (h : A.IsQueryBound n) :
    IsQueryProfile A n n n where
  inl := h.isQueryBoundBy_one.of_cost_le fun d => by cases d <;> simp
  inr := h.isQueryBoundBy_one.of_cost_le fun d => by cases d <;> simp
  total := h

/-- Counts at the two summands give a profile with their sum as the total count. -/
theorem of_inl_inr {A : OracleAdv (D₁ ⊕ D₂) R α} {a b : ℕ}
    (h₁ : A.IsQueryBoundBy chargeInl a) (h₂ : A.IsQueryBoundBy chargeInr b) :
    IsQueryProfile A a b (a + b) := ⟨h₁, h₂, isQueryBound_of_inl_inr h₁ h₂⟩

/-- A profile is monotone in each of its counts. -/
theorem mono {A : OracleAdv (D₁ ⊕ D₂) R α} {a a' b b' n n' : ℕ} (h : IsQueryProfile A a b n)
    (ha : a ≤ a') (hb : b ≤ b') (hn : n ≤ n') : IsQueryProfile A a' b' n' :=
  ⟨h.inl.mono ha, h.inr.mono hb, h.total.mono hn⟩

/-- Sequential composition adds each count. -/
theorem bind {A : OracleAdv (D₁ ⊕ D₂) R α} {f : α → OracleAdv (D₁ ⊕ D₂) R β} {a b n a' b' n' : ℕ}
    (hA : IsQueryProfile A a b n) (hf : ∀ x, IsQueryProfile (f x) a' b' n') :
    IsQueryProfile (A.bind f) (a + a') (b + b') (n + n') :=
  ⟨isQueryBoundBy_bind hA.inl fun x => (hf x).inl, isQueryBoundBy_bind hA.inr fun x => (hf x).inr,
    isQueryBound_bind hA.total fun x => (hf x).total⟩

/-- A branch takes the maximum of each count, the total count included: the total of a branch
querying one oracle in each arm is the larger total of the arms. -/
theorem ite (p : Prop) [Decidable p] {A B : OracleAdv (D₁ ⊕ D₂) R α} {a b n a' b' n' : ℕ}
    (hA : IsQueryProfile A a b n) (hB : IsQueryProfile B a' b' n') :
    IsQueryProfile (if p then A else B) (max a a') (max b b') (max n n') := by
  split
  · exact hA.mono (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
  · exact hB.mono (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)

end IsQueryProfile

/-! ## Provenance -/

open Classical in
/-- The charge `0` on `S` and `1` elsewhere. -/
noncomputable def outsideCharge (S : Set D) (d : D) : ℕ := if d ∈ S then 0 else 1

/-- `MayOnlyCall S A`: every query on every path of `A` lies in `S`, stated as the bound `0` at
the charge `outsideCharge S`. -/
def MayOnlyCall (S : Set D) (A : OracleAdv D R α) : Prop :=
  A.IsQueryBoundBy (outsideCharge S) 0

/-- `A.MayAsk d`: the query `d` occurs in the tree of `A`. -/
def MayAsk : OracleAdv D R α → D → Prop
  | ret _, _ => False
  | rand _ k, d => ∃ b, MayAsk (k b) d
  | query d' k, d => d = d' ∨ ∃ r, MayAsk (k r) d

@[simp] theorem outsideCharge_of_mem {S : Set D} {d : D} (h : d ∈ S) : outsideCharge S d = 0 := by
  simp [outsideCharge, h]

theorem outsideCharge_of_notMem {S : Set D} {d : D} (h : d ∉ S) : outsideCharge S d = 1 := by
  simp [outsideCharge, h]

theorem outsideCharge_le_one (S : Set D) (d : D) : outsideCharge S d ≤ 1 := by
  unfold outsideCharge; split <;> omega

theorem outsideCharge_eq_zero {S : Set D} {d : D} : outsideCharge S d = 0 ↔ d ∈ S := by
  by_cases h : d ∈ S <;> simp [outsideCharge, h]

@[simp] theorem mayOnlyCall_ret (S : Set D) (a : α) : MayOnlyCall S (ret a : OracleAdv D R α) :=
  trivial

theorem mayOnlyCall_rand_iff {S : Set D} {β' : Type} {p : PMF β'} {k : β' → OracleAdv D R α} :
    MayOnlyCall S (rand p k) ↔ ∀ b, MayOnlyCall S (k b) :=
  Iff.rfl

theorem mayOnlyCall_query_iff {S : Set D} {d : D} {k : R → OracleAdv D R α} :
    MayOnlyCall S (query d k) ↔ d ∈ S ∧ ∀ r, MayOnlyCall S (k r) := by
  simp [MayOnlyCall, IsQueryBoundBy, outsideCharge_eq_zero]

/-- `MayOnlyCall S A` holds exactly when every query occurring in the tree of `A` lies in `S`. -/
theorem mayOnlyCall_iff_mayAsk {S : Set D} {A : OracleAdv D R α} :
    MayOnlyCall S A ↔ ∀ d, A.MayAsk d → d ∈ S := by
  induction A with
  | ret a => simp [MayAsk]
  | rand p k ih =>
    simp only [mayOnlyCall_rand_iff, ih, MayAsk]
    grind
  | query d k ih =>
    simp only [mayOnlyCall_query_iff, ih, MayAsk]
    grind

/-- Provenance as the cost fold: `MayOnlyCall S A` says the cost at `outsideCharge S` is zero. -/
theorem mayOnlyCall_iff_cost_eq_zero {S : Set D} {A : OracleAdv D R α} :
    MayOnlyCall S A ↔ Container.cost (AdvSig.posCost (outsideCharge S)) (toFreeM A) = 0 := by
  rw [MayOnlyCall, isQueryBoundBy_iff_cost_le]
  simp

/-- Provenance is monotone in the set of allowed queries. -/
theorem MayOnlyCall.mono {S T : Set D} {A : OracleAdv D R α} (h : MayOnlyCall S A)
    (hST : S ⊆ T) : MayOnlyCall T A := by
  refine IsQueryBoundBy.of_cost_le (fun d => ?_) h
  by_cases hd : d ∈ S
  · simp [outsideCharge_of_mem hd, outsideCharge_of_mem (hST hd)]
  · simpa [outsideCharge_of_notMem hd] using outsideCharge_le_one T d

/-- Two provenance statements of one adversary combine to the intersection. -/
theorem mayOnlyCall_inter {S T : Set D} {A : OracleAdv D R α} (hS : MayOnlyCall S A)
    (hT : MayOnlyCall T A) : MayOnlyCall (S ∩ T) A := by
  refine IsQueryBoundBy.of_cost_le (fun d => ?_) (hS.add hT)
  by_cases h₁ : d ∈ S <;> by_cases h₂ : d ∈ T <;>
    simp [outsideCharge, h₁, h₂]

/-- Provenance composes sequentially without any budget. -/
theorem mayOnlyCall_bind {S : Set D} {A : OracleAdv D R α} {f : α → OracleAdv D R β}
    (hA : MayOnlyCall S A) (hf : ∀ x, MayOnlyCall S (f x)) : MayOnlyCall S (A.bind f) :=
  isQueryBoundBy_bind hA hf

/-- A simulated adversary calls only `S'` when the adversary calls only `S` and the program
answering each query of `S` calls only `S'`. -/
theorem mayOnlyCall_simulate {S : Type} {Q : Set D} {Q' : Set D'}
    (impl : S → D → OracleAdv D' R' (R × S)) (himpl : ∀ s, ∀ d ∈ Q, MayOnlyCall Q' (impl s d))
    {A : OracleAdv D R α} (hA : MayOnlyCall Q A) (s : S) :
    MayOnlyCall Q' (simulate impl A s) := by
  induction A generalizing s with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b) s
  | query d k ih =>
    obtain ⟨hd, hk⟩ := mayOnlyCall_query_iff.mp hA
    exact mayOnlyCall_bind (himpl s d hd) fun x => ih x.1 (hk x.1) x.2

/-- Renaming queries transports provenance along the image of the allowed set. -/
theorem mayOnlyCall_mapQuery {Q : Set D} {Q' : Set D'} (c : D → D') (hc : ∀ d ∈ Q, c d ∈ Q')
    {A : OracleAdv D R α} (hA : MayOnlyCall Q A) : MayOnlyCall Q' (mapQuery c A) := by
  refine isQueryBoundBy_mapQuery c (fun d => ?_) hA
  by_cases hd : d ∈ Q
  · simp [outsideCharge_of_mem hd, outsideCharge_of_mem (hc d hd)]
  · simpa [outsideCharge_of_notMem hd] using outsideCharge_le_one Q' (c d)

/-- On an adversary calling only `S`, a bound at a charge holds at every charge agreeing with it
on `S`. -/
theorem MayOnlyCall.congr_cost {S : Set D} {c c' : D → ℕ} {A : OracleAdv D R α} {n : ℕ}
    (hA : MayOnlyCall S A) (hc : ∀ d ∈ S, c' d = c d) (h : A.IsQueryBoundBy c n) :
    A.IsQueryBoundBy c' n := by
  induction A generalizing n with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b) (h b)
  | query d k ih =>
    obtain ⟨hd, hk⟩ := mayOnlyCall_query_iff.mp hA
    obtain ⟨h₁, h₂⟩ := h
    rw [← hc d hd] at h₁ h₂
    exact ⟨h₁, fun r => ih r (hk r) (h₂ r)⟩

/-- An adversary calling only `S` has the bound `0` at every charge vanishing on `S`. -/
theorem MayOnlyCall.isQueryBoundBy_zero {S : Set D} {c : D → ℕ} {A : OracleAdv D R α}
    (hA : MayOnlyCall S A) (hc : ∀ d ∈ S, c d = 0) : A.IsQueryBoundBy c 0 :=
  hA.congr_cost (fun d hd => (hc d hd).trans (outsideCharge_of_mem hd).symm) hA

end CatCrypt.Crypto.OracleAdv
