/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.AutoTime

/-!
# Tests for the costed value of a returned state under `derive_timed`

* `red`: the simulation of `CatCryptCore.Tactics.DeriveTimedBindTest`, whose handler `hImpl`
  has the leaf `.ret (0, { st with found := some q })` and calls `lazyT`, whose leaf
  `.ret (k, st)` returns the state unchanged. Under `derive_timed` both leaves return the
  incoming cost companion of the table `tab`.

## Main results

* `hImpl.timed_found` — the leaf of `hImpl` that updates `found` returns the companion `c`
* `lazyT.timed_some` — the leaf of `lazyT` that returns the state returns the companion `c`
* `hImpl.timeBound` — the time of the costed handler, by `time_bound`
* `red.timeBound` — the time of the costed simulation, through
  `OracleAdv.Timed.timeBound_simulateHat_inv` with the invariant that the table's companion is
  at most `3 i` after `i` queries
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedReturnStateTest

open CatCrypt.Crypto

/-- A simulation state with a table holding functions. -/
structure St where
  /-- The lazily sampled table. -/
  tab : ℕ → Option (Fin 4)
  /-- The query found, if any. -/
  found : Option ℕ

/-- The lazily sampled table at `c`. -/
noncomputable def lazyT (st : St) (c : ℕ) : OracleAdv ℕ Bool (Fin 4 × St) :=
  match st.tab c with
  | some k => .ret (k, st)
  | none => .rand (PMF.uniformFintype (Fin 4)) fun k =>
      .ret (k, { st with tab := Function.update st.tab c (some k) })

/-- A handler with an `if` under the binder of a query node. -/
noncomputable def hImpl (st : St) (q : ℕ) : OracleAdv ℕ Bool (Fin 4 × St) :=
  .query q fun b =>
    if b then (if q = 0 then .ret (0, { st with found := some q }) else lazyT st q)
    else lazyT st (q + 1)

/-- The simulation of `hImpl`. -/
noncomputable def red (A : OracleAdv ℕ (Fin 4) Bool) : OracleAdv ℕ Bool (Option ℕ) :=
  (OracleAdv.simulate hImpl A ⟨fun _ => none, none⟩).bind fun x => .ret x.2.found

derive_timed red

example (A : OracleAdv.Timed ℕ (Fin 4) Bool) : (red.timed A).2.erase = red A.erase :=
  red.erase_timed A

/-- At a present entry, the costed `lazyT` returns the table with the incoming companion. -/
theorem lazyT.timed_some (st : St) (x : ℕ) (c : ℕ → ℕ) (k : Fin 4) (h : st.tab x = some k) :
    (lazyT.timed st x c).2 = OracleAdv.Timed.ret (k, (fun a => st.tab a, c), st.found) := by
  simp [lazyT.timed, OracleAdv.Timed.delay, h]

/-- The costed `hImpl` at query `0` answered `true` returns the table with the incoming
companion. -/
theorem hImpl.timed_found (st : St) (c : ℕ → ℕ) :
    ∃ f k, (hImpl.timed st 0 c).2 = OracleAdv.Timed.query 0 f k ∧
      k true = OracleAdv.Timed.ret (0, (fun a => st.tab a, c), some 0) :=
  ⟨_, _, rfl, rfl⟩

/-- A table companion bounded by `b` bounds the time of the costed handler by `2 b + 20`. -/
theorem hImpl.timeBound (st : St) (q : ℕ) (c : ℕ → ℕ) {b : ℕ} (hc : ∀ x, c x ≤ b) :
    OracleAdv.Timed.StepTimeBound (hImpl.timed st q c) (2 * b + 20) := by
  time_bound

/-- An adversary of time `T` asking at most `q` queries gives a costed simulation of time at
most `T + ∑_{j < q} (6 j + 21) + 2`: query `j` meets a table companion of at most `3 j`. -/
theorem red.timeBound {A : OracleAdv.Timed ℕ (Fin 4) Bool} {T q : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (red.timed A)
      (T + ∑ j ∈ Finset.range q, (2 * (3 * (0 + j)) + 21) + 2) := by
  unfold red.timed
  have himpl : ∀ (i : ℕ) (s : ((ℕ → Option (Fin 4)) × (ℕ → ℕ)) × Option ℕ) (d : ℕ),
      (∀ x, s.1.2 x ≤ 3 * i) →
      OracleAdv.Timed.StepTimeBound
        (OracleAdv.Timed.delay 1 (hImpl.timed { tab := s.1.1, found := s.2 } d s.1.2))
        (2 * (3 * i) + 21) ∧
      OracleAdv.Timed.AllRet (fun y => ∀ x, y.2.1.2 x ≤ 3 * (i + 1))
        (OracleAdv.Timed.delay 1 (hImpl.timed { tab := s.1.1, found := s.2 } d s.1.2)).2 := by
    intro i s d hs
    refine ⟨?_, ?_⟩
    · exact (OracleAdv.Timed.stepTimeBound_delay (hImpl.timeBound _ d _ hs)).mono (by omega)
    · intro r
      cases r <;> simp only [OracleAdv.Timed.delay, lazyT.timed] <;> split_ifs <;> (try split) <;>
        simp only [OracleAdv.Timed.AllRet] <;> intros <;> grind
  have hX := OracleAdv.Timed.timeBound_simulateHat_inv
    (fun y : ((ℕ → Option (Fin 4)) × (ℕ → ℕ)) × Option ℕ => ({ tab := y.1.1, found := y.2 } : St))
    (fun y : St => ((fun a => y.tab a, fun _ => 0), y.found))
    (fun st q => OracleAdv.Timed.delay 1 (hImpl.timed { tab := st.1.1, found := st.2 } q st.1.2))
    (fun i s => ∀ x, s.1.2 x ≤ 3 * i) (fun i => 2 * (3 * i) + 21) himpl hA hq 0
    ((fun _ => none, fun _ => 0), none) (fun _ => Nat.zero_le _)
  refine (OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.timeBound_bind (n := 0) hX.2
    (fun _ => ?_))).mono (by have := hX.1; omega)
  exact ⟨le_rfl, trivial⟩

end CatCrypt.Tactics.DeriveTimedReturnStateTest
