/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversary

/-!
# Sequencing and simulation of adaptive oracle adversaries

`OracleAdv.bind A f` runs the adaptive adversary `A` and continues with `f` on its
output. `OracleAdv.simulate impl A s` turns an adversary `A` with queries in `D`
into an adversary with queries in `D'`: every query `d` of `A` is answered by the
program `impl s d`, which may flip coins and ask queries in `D'`, and which
returns the answer together with the next simulator state. This is the shape of a
reduction that keeps its own tables and forwards some queries to its challenger.

## Main definitions

* `OracleAdv.bind` — sequential composition of adversaries
* `OracleAdv.simulate impl A s` — `A` with each query answered by a program of
  `impl`, started from simulator state `s`
* `OracleAdv.IsQueryBoundBy cost A n` — every path of `A` has total query cost at
  most `n`, where the query `d` costs `cost d`
* `roOracle`, `emptyTable` — the lazily sampled random oracle on a table
  `D → Option H`

## Main results

* `OracleAdv.run_bind` — running a composition is running the first part and
  then the second
* `OracleAdv.run_simulate` — running a simulated adversary against `O'` is running
  the original adversary against the composite oracle that runs `impl` against
  `O'`; `OracleAdv.run_simulate_fst` — the same with the simulator state dropped
* `OracleAdv.isQueryBound_simulate` — a simulated adversary asks at most the total
  cost of its original queries, when the program answering `d` asks at most
  `cost d` queries; `OracleAdv.isQueryBound_simulate_mul` — `q` queries answered by
  programs of at most `c` queries give at most `q * c` queries
* `OracleAdv.isQueryBoundBy_mapQuery` — renaming queries preserves a cost bound
  when no renamed query costs more than the original
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open scoped ENNReal

namespace OracleAdv

variable {D R D' R' α β : Type}

/-- Run `A`, then continue with `f` applied to its output. -/
def bind : OracleAdv D R α → (α → OracleAdv D R β) → OracleAdv D R β
  | ret a, f => f a
  | rand p k, f => rand p fun b => bind (k b) f
  | query d k, f => query d fun r => bind (k r) f

@[simp] theorem bind_ret (a : α) (f : α → OracleAdv D R β) : bind (ret a) f = f a := rfl

theorem bind_assoc {γ : Type} (A : OracleAdv D R α) (f : α → OracleAdv D R β)
    (g : β → OracleAdv D R γ) : (A.bind f).bind g = A.bind fun x => (f x).bind g := by
  induction A with
  | ret a => rfl
  | rand p k ih => simp only [bind, ih]
  | query d k ih => simp only [bind, ih]

/-- Running `A.bind f` runs `A` and then `f` on its output from the reached state. -/
theorem run_bind {S : Type} (O : S → D → PMF (R × S)) (A : OracleAdv D R α)
    (f : α → OracleAdv D R β) (s : S) :
    run O (A.bind f) s = (run O A s).bind fun x => run O (f x.1) x.2 := by
  induction A generalizing s with
  | ret a => simp [bind, run_ret, PMF.pure_bind]
  | rand p k ih => simp only [bind, run_rand, PMF.bind_bind, ih]
  | query d k ih => simp only [bind, run_query, PMF.bind_bind, ih]

theorem isQueryBound_bind {A : OracleAdv D R α} {f : α → OracleAdv D R β} {m n : ℕ}
    (hA : IsQueryBound A m) (hf : ∀ a, IsQueryBound (f a) n) :
    IsQueryBound (A.bind f) (m + n) := by
  induction A generalizing m with
  | ret a => exact (hf a).mono (Nat.le_add_left n m)
  | rand p k ih => exact fun b => ih b (hA b)
  | query d k ih =>
    cases m with
    | zero => exact hA.elim
    | succ m =>
      rw [Nat.add_right_comm]
      exact fun r => ih r (hA r)

/-- The adversary `A` with every query `d` answered by the program `impl s d` from
the current simulator state `s`; the program returns the answer and the next
simulator state. -/
def simulate {S : Type} (impl : S → D → OracleAdv D' R' (R × S)) :
    OracleAdv D R α → S → OracleAdv D' R' (α × S)
  | ret a, s => ret (a, s)
  | rand p k, s => rand p fun b => simulate impl (k b) s
  | query d k, s => bind (impl s d) fun x => simulate impl (k x.1) x.2

theorem simulate_bind {S : Type} (impl : S → D → OracleAdv D' R' (R × S)) (A : OracleAdv D R α)
    (g : α → OracleAdv D R β) (s : S) :
    simulate impl (A.bind g) s = (simulate impl A s).bind fun x => simulate impl (g x.1) x.2 := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih => simp only [bind, simulate, ih]
  | query d k ih =>
    simp only [bind, simulate, ih, bind_assoc]

/-- The oracle on joint states that answers `d` by running `impl s d` against `O'`. -/
noncomputable def simOracle {S U : Type} (impl : S → D → OracleAdv D' R' (R × S))
    (O' : U → D' → PMF (R' × U)) (s : S × U) (d : D) : PMF (R × (S × U)) :=
  (run O' (impl s.1 d) s.2).map fun x => (x.1.1, (x.1.2, x.2))

/-- Running the simulated adversary against `O'` is running `A` against the
composite oracle `simOracle impl O'`. -/
theorem run_simulate {S U : Type} (impl : S → D → OracleAdv D' R' (R × S))
    (O' : U → D' → PMF (R' × U)) (A : OracleAdv D R α) (s : S) (u : U) :
    run O' (simulate impl A s) u =
      (run (simOracle impl O') A (s, u)).map fun x => ((x.1, x.2.1), x.2.2) := by
  induction A generalizing s u with
  | ret a => simp [simulate, PMF.pure_map]
  | rand p k ih => simp only [simulate, run_rand, PMF.map_bind, ih]
  | query d k ih =>
    simp only [simulate, run_bind, run_query, simOracle, PMF.bind_map, PMF.map_bind]
    refine congrArg _ (funext fun x => ?_)
    exact ih x.1.1 x.1.2 x.2

/-- The output of the simulated adversary, with the simulator state dropped, is the output
of `A` against the composite oracle. -/
theorem run_simulate_fst {S U : Type} (impl : S → D → OracleAdv D' R' (R × S))
    (O' : U → D' → PMF (R' × U)) (A : OracleAdv D R α) (s : S) (u : U) :
    (run O' ((simulate impl A s).bind fun x => ret x.1) u).map Prod.fst =
      (run (simOracle impl O') A (s, u)).map Prod.fst := by
  rw [run_bind, run_simulate]
  simp [PMF.map_bind, PMF.bind_map, Function.comp_def, PMF.pure_map]
  rfl

/-- `IsQueryBoundBy cost A n`: on every path of `A` the sum of `cost d` over the
queries `d` is at most `n`. -/
def IsQueryBoundBy (cost : D → ℕ) : OracleAdv D R α → ℕ → Prop
  | ret _, _ => True
  | rand _ k, n => ∀ b, IsQueryBoundBy cost (k b) n
  | query d k, n => cost d ≤ n ∧ ∀ r, IsQueryBoundBy cost (k r) (n - cost d)

/-- Query costs add: bounds for two costs give a bound for their sum. -/
theorem IsQueryBoundBy.add {c₁ c₂ : D → ℕ} {A : OracleAdv D R α} {a b : ℕ}
    (h₁ : A.IsQueryBoundBy c₁ a) (h₂ : A.IsQueryBoundBy c₂ b) :
    A.IsQueryBoundBy (fun d => c₁ d + c₂ d) (a + b) := by
  induction A generalizing a b with
  | ret x => trivial
  | rand p k ih => exact fun x => ih x (h₁ x) (h₂ x)
  | query d k ih =>
    refine ⟨Nat.add_le_add h₁.1 h₂.1, fun r => ?_⟩
    have h := ih r (h₁.2 r) (h₂.2 r)
    rwa [show a + b - (c₁ d + c₂ d) = (a - c₁ d) + (b - c₂ d) by
      have := h₁.1; have := h₂.1; omega]

theorem IsQueryBoundBy.mono {c : D → ℕ} {A : OracleAdv D R α} {a b : ℕ}
    (h : A.IsQueryBoundBy c a) (hab : a ≤ b) : A.IsQueryBoundBy c b := by
  induction A generalizing a b with
  | ret x => trivial
  | rand p k ih => exact fun x => ih x (h x) hab
  | query d k ih => exact ⟨h.1.trans hab, fun r => ih r (h.2 r) (by omega)⟩

/-- A cost bound scales with the cost. -/
theorem IsQueryBoundBy.mul_left {c : D → ℕ} {A : OracleAdv D R α} {n : ℕ}
    (h : A.IsQueryBoundBy c n) (a : ℕ) : A.IsQueryBoundBy (fun d => a * c d) (a * n) := by
  induction A generalizing n with
  | ret x => trivial
  | rand p k ih => exact fun b => ih b (h b)
  | query d k ih =>
    refine ⟨Nat.mul_le_mul_left a h.1, fun r => ?_⟩
    rw [← Nat.mul_sub]
    exact ih r (h.2 r)

theorem isQueryBoundBy_bind {c : D → ℕ} {A : OracleAdv D R α} {f : α → OracleAdv D R β}
    {a b : ℕ} (hA : A.IsQueryBoundBy c a) (hf : ∀ x, (f x).IsQueryBoundBy c b) :
    (A.bind f).IsQueryBoundBy c (a + b) := by
  induction A generalizing a with
  | ret x => exact (hf x).mono (Nat.le_add_left b a)
  | rand p k ih => exact fun x => ih x (hA x)
  | query d k ih =>
    refine ⟨hA.1.trans (Nat.le_add_right a b), fun r => ?_⟩
    have h := ih r (hA.2 r)
    rwa [show a + b - c d = a - c d + b by have := hA.1; omega]

/-- A simulated adversary asks at most the total cost of the original adversary's
queries, when the program answering `d` asks at most `cost d` queries. -/
theorem isQueryBound_simulate {S : Type} (impl : S → D → OracleAdv D' R' (R × S))
    (cost : D → ℕ) (himpl : ∀ s d, IsQueryBound (impl s d) (cost d))
    {A : OracleAdv D R α} {n : ℕ} (hA : IsQueryBoundBy cost A n) (s : S) :
    IsQueryBound (simulate impl A s) n := by
  induction A generalizing n s with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b) s
  | query d k ih =>
    obtain ⟨hle, hk⟩ := hA
    have h := isQueryBound_bind (himpl s d) (fun x => ih x.1 (hk x.1) x.2)
    rwa [Nat.add_sub_cancel' hle] at h

/-- An adversary with at most `q` queries, each answered by a program with at most `c`
queries, gives a simulated adversary with at most `q * c` queries. -/
theorem isQueryBound_simulate_mul {S : Type} {impl : S → D → OracleAdv D' R' (R × S)} {c : ℕ}
    (himpl : ∀ s d, (impl s d).IsQueryBound c) {A : OracleAdv D R α} {q : ℕ}
    (hA : A.IsQueryBound q) (s : S) : (simulate impl A s).IsQueryBound (q * c) := by
  induction A generalizing q s with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b) s
  | query d k ih =>
    cases q with
    | zero => exact hA.elim
    | succ q =>
      rw [Nat.succ_mul, Nat.add_comm]
      exact isQueryBound_bind (himpl s d) fun x => ih x.1 (hA x.1) x.2

/-- A simulated adversary has target cost at most the source cost of the original
adversary, when the program answering `d` has target cost at most `cost d`. -/
theorem isQueryBoundBy_simulate {S : Type} (impl : S → D → OracleAdv D' R' (R × S))
    (cost : D → ℕ) (cost' : D' → ℕ) (himpl : ∀ s d, (impl s d).IsQueryBoundBy cost' (cost d))
    {A : OracleAdv D R α} {n : ℕ} (hA : A.IsQueryBoundBy cost n) (s : S) :
    (simulate impl A s).IsQueryBoundBy cost' n := by
  induction A generalizing n s with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b) s
  | query d k ih =>
    obtain ⟨hle, hk⟩ := hA
    have h := isQueryBoundBy_bind (himpl s d) (fun x => ih x.1 (hk x.1) x.2)
    rwa [Nat.add_sub_cancel' hle] at h

/-- Renaming queries along `c` preserves a cost bound when each renamed query costs
at most the original one. -/
theorem isQueryBoundBy_mapQuery (c : D → D') {cost : D → ℕ} {cost' : D' → ℕ}
    (hc : ∀ d, cost' (c d) ≤ cost d) {A : OracleAdv D R α} {n : ℕ}
    (hA : A.IsQueryBoundBy cost n) : (mapQuery c A).IsQueryBoundBy cost' n := by
  induction A generalizing n with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b)
  | query d k ih =>
    exact ⟨(hc d).trans hA.1, fun r => (ih r (hA.2 r)).mono (by have := hc d; omega)⟩

end OracleAdv

/-! ## Lazily sampled random oracle -/

section RandomOracle

variable {D H : Type} [DecidableEq D] [Fintype H] [Nonempty H]

/-- The lazily sampled random oracle with table `T`: a defined point returns its
value, an undefined point samples a uniform value and records it. -/
noncomputable def roOracle (T : D → Option H) (d : D) : PMF (H × (D → Option H)) :=
  match T d with
  | some h => PMF.pure (h, T)
  | none => (PMF.uniformFintype H).map fun h => (h, Function.update T d (some h))

omit [Fintype H] [Nonempty H] in
/-- The empty random-oracle table. -/
def emptyTable : D → Option H := fun _ => none

end RandomOracle

end CatCrypt.Crypto
