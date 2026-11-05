/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Tests of `derive_time_bound` on costed oracle adversaries

A recursive costed oracle adversary `stepsFx.timed` with a hand-proved time theorem whose
premises are two cost bounds at one bound `c` and a bound `M` of the cost companions of its state
(`CompBound`), and whose conclusion carries the leaf invariant `CompBound (M + n)`; and a
reduction `redFx.timed` that samples, runs `stepsFx.timed` from a state with bounded companions,
and continues with a step cost that reads the companions of the returned state (under a
dependent `if` and in the step cost of a `Fin.foldr` loop) and an adversary binder `A`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBoundOracleTest

open CatCrypt.Crypto.OracleAdv.Timed

/-- The cost companions of the state `st` are at most `M`, and so is its index. -/
def CompBound (M : ℕ) (st : ℕ × (Fin 4 → ℕ)) : Prop := (∀ a, st.2 a ≤ M) ∧ st.1 ≤ M

/-- `n` queries: each charges `fCost` and `hCost` at its index and the first companion of the
state, and raises the index and every companion by one. -/
def stepsFx.timed (fCost hCost : ℕ → ℕ) (st : ℕ × (Fin 4 → ℕ)) :
    ℕ → ℕ × CatCrypt.Crypto.OracleAdv.Timed ℕ ℕ (ℕ × (Fin 4 → ℕ))
  | 0 => (0, .ret st)
  | n + 1 => (fCost n + hCost n + st.2 0,
      .query st.1 (fun _ => (stepsFx.timed fCost hCost (st.1 + 1, fun a => st.2 a + 1) n).1)
        fun _ => (stepsFx.timed fCost hCost (st.1 + 1, fun a => st.2 a + 1) n).2)

/-- The time of `n` queries from a state with companions at most `M`, and the companions of the
returned states. -/
theorem stepsFx.timeBound_timed (fCost hCost : ℕ → ℕ) (st : ℕ × (Fin 4 → ℕ)) {c M : ℕ}
    (hf : ∀ i, fCost i ≤ c) (hh : ∀ i, hCost i ≤ c) (hst : CompBound M st) (n : ℕ) :
    StepTimeBound (stepsFx.timed fCost hCost st n) (n * (2 * c + M + n + 2)) ∧
      AllRet (CompBound (M + n)) (stepsFx.timed fCost hCost st n).2 := by
  induction n generalizing st M with
  | zero => exact ⟨⟨Nat.zero_le _, trivial⟩, hst⟩
  | succ n ih =>
    have hs' : CompBound (M + 1) (st.1 + 1, fun a => st.2 a + 1) :=
      ⟨fun a => by
        have := hst.1 a
        dsimp only
        omega, by
        have := hst.2
        dsimp only
        omega⟩
    obtain ⟨ih1, ih3⟩ := ih (st.1 + 1, fun a => st.2 a + 1) hs'
    have h0 := hst.1 0
    have hn := hf n
    have hn' := hh n
    refine ⟨by time_fold, ?_⟩
    simp only [stepsFx.timed, AllRet]
    intro _
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ih3

/-- The name of the reduction `redFx.timed`. -/
def redFx : Unit := ()

/-- A reduction: sample `b`, run three queries from the state `(|x|, fun _ => |x| + 2)`, then
charge `gCost`, companions of the returned state and a loop over them, and run `A`. -/
noncomputable def redFx.timed (fCost hCost : ℕ → ℕ) (gCost : (Fin 4 → ℕ) → ℕ)
    (A : (Fin 4 → ℕ) → CatCrypt.Crypto.OracleAdv.Timed ℕ ℕ Bool) (x : List ℕ) :
    ℕ × CatCrypt.Crypto.OracleAdv.Timed ℕ ℕ Bool :=
  (0, .rand (PMF.pure (2 : Fin 4))
    (fun b => 1 + (stepsFx.timed fCost hCost (x.length, fun _ => x.length + 2) 3).1 +
      ((stepsFx.timed fCost hCost (x.length, fun _ => x.length + 2) 3).2.bind fun st =>
        delay (gCost st.2 + st.2 b + (if h : x.length < 4 then st.2 ⟨x.length, h⟩ else 0) +
            Fin.foldr.loop.timedCost 4 (fun i acc => acc + st.2 i)
              (fun i _ => if h : (i : ℕ) < 2 then st.2 ⟨i, by omega⟩ else 1) 4 le_rfl 0)
          (0, A st.2)).1)
    fun b => ((stepsFx.timed fCost hCost (x.length, fun _ => x.length + 2) 3).2.bind fun st =>
        delay (gCost st.2 + st.2 b + (if h : x.length < 4 then st.2 ⟨x.length, h⟩ else 0) +
            Fin.foldr.loop.timedCost 4 (fun i acc => acc + st.2 i)
              (fun i _ => if h : (i : ℕ) < 2 then st.2 ⟨i, by omega⟩ else 1) 4 le_rfl 0)
          (0, A st.2)).2)

derive_time_bound redFx

/-- The derived bound at one bound `c` of the costs: linear in `c`, `|x|` and the time of `A`. -/
example (fCost hCost : ℕ → ℕ) (gCost : (Fin 4 → ℕ) → ℕ)
    (A : (Fin 4 → ℕ) → CatCrypt.Crypto.OracleAdv.Timed ℕ ℕ Bool) (x : List ℕ) {c T : ℕ}
    (hf : ∀ a, fCost a ≤ c) (hh : ∀ a, hCost a ≤ c) (hg : ∀ a, gCost a ≤ c)
    (hA : ∀ a, (A a).TimeBound T) :
    StepTimeBound (redFx.timed fCost hCost gCost A x) (7 * c + 10 * x.length + T + 100) :=
  (redFx.timeBound_timed fCost hCost gCost A x hf hh hg hA).mono (by grind)

end CatCrypt.Tactics.DeriveTimeBoundOracleTest
