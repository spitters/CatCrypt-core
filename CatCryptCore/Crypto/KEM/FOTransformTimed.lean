/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KEM.FOTransform
public import CatCryptCore.Crypto.OracleAdversaryRelabelTimed

/-!
# Costed form of the plaintext-checking lift of the FO reduction

`liftP A` asks each plaintext-checking query of `A` as the right summand of the combined
oracle and reads its answer back through `Sum.elim`; it is the relabelling
`OracleAdv.mapQueryAnswer` (`liftP_eq_mapQueryAnswer`). Its costed form `liftP.timed` is
registered for `derive_timed` in the binder convention of `CatCryptCore.Tactics.DeriveTimed`.

## Cost model

The registered costs of `CatCryptCore.Crypto.OracleAdversaryTimed`: one unit per `rand` and
per `query` node. The query relabelling `Sum.inr` is a constructor and free; reading an
answer back through `Sum.elim` costs one unit, charged on the continuation of the query.

## Main definitions

* `liftP.timed` — the costed form of `liftP`

## Main results

* `liftP_eq_mapQueryAnswer` — `liftP` is a relabelling of queries and answers
* `liftP.erase_timed` — `(liftP.timed A').2.erase = liftP A'.erase`
* `liftP.timeBound_timed` — an adversary of time `T` with at most `q` queries gives time at
  most `T + q`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KEM.FOTransform

/-- `liftP` asks each query `q` as `.inr q` and reads each answer through `Sum.elim`. -/
theorem liftP_eq_mapQueryAnswer {M C R α : Type} (A : OracleAdv (M × C) Bool α) :
    liftP (R := R) A = A.mapQueryAnswer Sum.inr fun a => a.elim (fun _ => false) id := by
  induction A with
  | ret a => rfl
  | rand p k ih => simp only [liftP, OracleAdv.mapQueryAnswer, ih]
  | query d k ih => simp only [liftP, OracleAdv.mapQueryAnswer, ih]

/-- The costed form of `liftP`: one unit per query for reading the answer back. -/
noncomputable def liftP.timed {M C R α : Type} (A : OracleAdv.Timed (M × C) Bool α) :
    ℕ × OracleAdv.Timed (M ⊕ (M × C)) (R ⊕ Bool) α :=
  (0, A.mapQueryAnswer Sum.inr (fun _ => 0) (fun a => a.elim (fun _ => false) id) fun _ => 1)

/-- Erasing the step costs of `liftP.timed A` gives `liftP` of the erased adversary. -/
theorem liftP.erase_timed {M C R α : Type} (A : OracleAdv.Timed (M × C) Bool α) :
    (liftP.timed (R := R) A).2.erase = liftP A.erase := by
  rw [liftP_eq_mapQueryAnswer]
  exact OracleAdv.Timed.erase_mapQueryAnswer _ _ _ _ A

/-- An adversary of time `T` with at most `q` queries gives a lift of time at most
`T + q`. -/
theorem liftP.timeBound_timed {M C R α : Type} {A : OracleAdv.Timed (M × C) Bool α} {T q : ℕ}
    (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (liftP.timed (R := R) A) (T + q) := by
  have h := OracleAdv.Timed.timeBound_mapQueryAnswer (Sum.inr (α := M)) (fun _ => 0)
    (fun a : R ⊕ Bool => a.elim (fun _ => false) id) (fun _ => 1) (t₀ := 0) (u₀ := 1)
    (fun _ => le_rfl) (fun _ => le_rfl) hA hq
  simpa [liftP.timed, OracleAdv.Timed.stepTimeBound_zero] using h

end CatCrypt.Crypto.KEM.FOTransform
