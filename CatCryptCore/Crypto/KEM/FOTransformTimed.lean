/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KEM.FOTransform
public import CatCryptCore.Crypto.OracleAdversaryRelabelTimed
public import CatCryptCore.Crypto.PKE.GamesTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

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
* `uRedRun.timed`, `uRedROM.timed` — the costed forms of the OW-PCA reduction, derived by
  `derive_timed` and `derive_reduction`

## Main results

* `liftP_eq_mapQueryAnswer` — `liftP` is a relabelling of queries and answers
* `liftP.erase_timed` — `(liftP.timed A').2.erase = liftP A'.erase`
* `liftP.bind_ret` — `(liftP X).bind (fun y => .ret (f y)) = liftP (X.bind fun y => .ret (f y))`,
  the naturality lemma that `derive_timed` uses at a call of `liftP` at a costed state
* `liftP.timeBound_timed` — an adversary of time `T` with at most `q` queries gives time at
  most `T + q`
* `isQueryBound_of_bind_ret`, `allRet_mapQueryAnswer` — query bounds and result invariants
  through a result map and a relabelling
* `simImpl.isQueryBound_erase`, `liftP.stepTimeBound_bind` — the query bound of the erased
  handler and the time of a lifted handler followed by its result map
* `simImpl.timeBound`, `simImplFO.timeBound` — one query of the costed handlers, with table
  companions at most `b`, takes time at most `2 b + 13` and `2 b + 19`
* `simImpl.allRet_le`, `simImplFO.allRet_le` — the table companions grow by at most `3` per
  query
* `uRedRun.timeBound`, `uRedROM.timeBound` — the costed reduction `uRedRun.timed` (from
  `derive_timed`) and the costed adversary `uRedROM.timed` (from `derive_reduction`) take time at
  most `rc + T + ∑_{j < q} (6 j + 20) + 5` (`+ 6` for `uRedROM`)
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

/-- `liftP` commutes with a bind into `ret`: relabelling the queries and then mapping the
result is mapping the result and then relabelling. -/
theorem liftP.bind_ret {M C R α β : Type} (X : OracleAdv (M × C) Bool α) (f : α → β) :
    (liftP (R := R) X).bind (fun y => .ret (f y)) = liftP (X.bind fun y => .ret (f y)) := by
  induction X with
  | ret a => rfl
  | rand p k ih => simp only [liftP, OracleAdv.bind, ih]
  | query q k ih => simp only [liftP, OracleAdv.bind, ih]

/-- An adversary of time `T` with at most `q` queries gives a lift of time at most
`T + q`. -/
theorem liftP.timeBound_timed {M C R α : Type} {A : OracleAdv.Timed (M × C) Bool α} {T q : ℕ}
    (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (liftP.timed (R := R) A) (T + q) := by
  have h := OracleAdv.Timed.timeBound_mapQueryAnswer (Sum.inr (α := M)) (fun _ => 0)
    (fun a : R ⊕ Bool => a.elim (fun _ => false) id) (fun _ => 1) (t₀ := 0) (u₀ := 1)
    (fun _ => le_rfl) (fun _ => le_rfl) hA hq
  simpa [liftP.timed, OracleAdv.Timed.stepTimeBound_zero] using h

derive_timed uRedRun

derive_reduction uRedROM

open OracleAdv.Timed

variable {PK M C R K : Type} [Nonempty R] [Nonempty M] [DecidableEq M] [DecidableEq C]
  [Fintype K] [Nonempty K]

/-- A query bound of a program whose results are mapped is a query bound of the program. -/
theorem isQueryBound_of_bind_ret {D R' α β : Type} {A : OracleAdv D R' α} (g : α → β) {n : ℕ}
    (h : (A.bind fun y => .ret (g y)).IsQueryBound n) : A.IsQueryBound n := by
  induction A generalizing n with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (h b)
  | query d k ih =>
    cases n with
    | zero => exact h.elim
    | succ n => exact fun a => ih a (h a)

omit [Nonempty M] in
/-- The erased costed handler `simImpl.timed` asks at most one query, and none on a
decapsulation query. -/
theorem simImpl.isQueryBound_erase (cstar : C) (kstar : K) (st : FOTransformU.SimState M C K)
    (d : (M × C) ⊕ C) (LDCost : C → ℕ) (LQCost : M × C → ℕ) :
    (FOTransformU.simImpl.timed cstar kstar st d LDCost LQCost).2.erase.IsQueryBound
      (Sum.elim (fun _ => 1) (fun _ => 0) d) := by
  have h := FOTransformU.isQueryBound_simImpl cstar kstar st d
  rw [← FOTransformU.simImpl.erase_timed cstar kstar st d LDCost LQCost] at h
  exact isQueryBound_of_bind_ret _ h

omit [Nonempty R] [Nonempty M] [DecidableEq M] [DecidableEq C] in
/-- A costed program `X` followed by its lift `liftP`, a result map of cost `2` and the
delays that `derive_timed` inserts takes time at most `N + q + 5`, for `X` of time `N` with
at most `q` queries. -/
theorem liftP.stepTimeBound_bind {β γ : Type} (X : ℕ × OracleAdv.Timed (M × C) Bool β)
    (f : β → ℕ × OracleAdv.Timed (M ⊕ (M × C)) (R ⊕ Bool) γ) {N q : ℕ}
    (hX : StepTimeBound X N) (hq : X.2.erase.IsQueryBound q) (hf : ∀ x, StepTimeBound (f x) 2) :
    StepTimeBound (delay 1 (delay (2 + X.1 + (liftP.timed (R := R) X.2).1)
      ((liftP.timed (R := R) X.2).2.bind f))) (N + q + 5) := by
  have h := liftP.timeBound_timed (R := R) hX.2 hq
  have hB := timeBound_bind h.2 hf
  have h1 := hX.1
  have h2 := h.1
  exact (stepTimeBound_delay (stepTimeBound_delay hB)).mono (by omega)

/-- Relabelling queries and answers keeps the results of a costed program. -/
theorem allRet_mapQueryAnswer {D D' R₁ R₂ α : Type} (g : D → D') (t : D → ℕ) (h : R₂ → R₁)
    (u : R₂ → ℕ) {P : α → Prop} {A : OracleAdv.Timed D R₁ α} (hA : AllRet P A) :
    AllRet P (A.mapQueryAnswer g t h u) := by
  induction A with
  | ret a => exact hA
  | rand p c k ih => exact fun b => ih b (hA b)
  | query d c k ih => exact fun r => ih (h r) (hA (h r))

omit [Nonempty M] in
/-- The costed handler `simImpl.timed` returns tables whose companions exceed the bound `b`
of those it receives by at most `3`. -/
theorem simImpl.allRet_le (cstar : C) (kstar : K) (st : FOTransformU.SimState M C K)
    (d : (M × C) ⊕ C) (LDCost : C → ℕ) (LQCost : M × C → ℕ) {b : ℕ}
    (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b) :
    AllRet (fun y => (∀ x, y.2.1.2 x ≤ b + 3) ∧ (∀ x, y.2.2.1.2 x ≤ b + 3))
      (FOTransformU.simImpl.timed cstar kstar st d LDCost LQCost).2 := by
  rcases d with q | c <;>
    dsimp only [FOTransformU.simImpl.timed, FOTransformU.lazyDProg.timed,
      FOTransformU.lazyQProg.timed, delay] <;>
    (repeat' (first | split_ifs | split | intro _ | dsimp only [AllRet])) <;>
    refine ⟨fun x => ?_, fun x => ?_⟩ <;> (try split) <;> (try have := hD x) <;>
    (try have := hQ x) <;> omega

omit [Nonempty M] in
/-- One query of the costed handler `simImpl.timed`, with the two table companions at most
`b`, takes time at most `2 b + 13`. -/
theorem simImpl.timeBound (cstar : C) (kstar : K) (st : FOTransformU.SimState M C K)
    (d : (M × C) ⊕ C) (LDCost : C → ℕ) (LQCost : M × C → ℕ) {b : ℕ}
    (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b) :
    StepTimeBound (FOTransformU.simImpl.timed cstar kstar st d LDCost LQCost)
      (2 * b + 13) := by
  rcases d with q | c
  · time_bound
  · time_bound

omit [Nonempty M] in
/-- One query of the costed handler `simImplFO.timed`, with the two table companions at most
`b`, takes time at most `2 b + 19`. -/
theorem simImplFO.timeBound (cstar : C) (kstar : K) (st : FOTransformU.SimState M C K)
    (d : (M ⊕ (M × C)) ⊕ C) (LDCost : C → ℕ) (LQCost : M × C → ℕ) {b : ℕ}
    (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b) :
    StepTimeBound (simImplFO.timed (R := R) cstar kstar st d LDCost LQCost) (2 * b + 19) := by
  have hs : ∀ s : R ⊕ Bool, (@Sum.rec R Bool (fun _ => ℕ) (fun _ => 0) (fun _ => 0) s) = 0 :=
    fun s => by cases s <;> rfl
  rcases d with (m | q) | c
  · simp only [simImplFO.timed, hs]; show StepTimeBound _ _; time_bound
  all_goals
    simp only [simImplFO.timed]
    refine (liftP.stepTimeBound_bind _ _ (simImpl.timeBound cstar kstar st _ LDCost LQCost hD hQ)
      (simImpl.isQueryBound_erase cstar kstar st _ LDCost LQCost) fun x => ?_).mono (by simp)
    rcases x with ⟨_ | _, _⟩ <;> exact ⟨le_rfl, trivial⟩

omit [Nonempty M] in
/-- The costed handler `simImplFO.timed` returns tables whose companions exceed the bound `b`
of those it receives by at most `3`. -/
theorem simImplFO.allRet_le (cstar : C) (kstar : K) (st : FOTransformU.SimState M C K)
    (d : (M ⊕ (M × C)) ⊕ C) (LDCost : C → ℕ) (LQCost : M × C → ℕ) {b : ℕ}
    (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b) :
    AllRet (fun y => (∀ x, y.2.1.2 x ≤ b + 3) ∧ (∀ x, y.2.2.1.2 x ≤ b + 3))
      (simImplFO.timed (R := R) cstar kstar st d LDCost LQCost).2 := by
  rcases d with (m | q) | c
  · intro _
    exact ⟨fun x => (hD x).trans (Nat.le_add_right _ _),
      fun x => (hQ x).trans (Nat.le_add_right _ _)⟩
  all_goals
    simp only [simImplFO.timed, delay]
    exact allRet_bind (allRet_mapQueryAnswer _ _ _ _
      (simImpl.allRet_le cstar kstar st _ LDCost LQCost hD hQ)) fun _ h => h

/-- **Time of `uRedRun.timed`.** With the call of `B.run pk c` of cost at most `rc`, and
`B.run pk c k` of time at most `T` with at most `q` queries for every `k`, the costed
reduction takes time at most `rc + T + ∑_{j < q} (6 j + 20) + 5`: query `j` meets table
companions of at most `3 j`. -/
theorem uRedRun.timeBound {qRO qD : ℕ} (B : Games.ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD)
    (pk : PK) (c : C) (runCost : PK → C → K → ℕ) {rc T q : ℕ}
    (hr : ∀ k, runCost pk c k ≤ rc) (hA : ∀ k, (ofAdv (B.run pk c k)).TimeBound T)
    (hq : ∀ k, (B.run pk c k).IsQueryBound q) :
    StepTimeBound (uRedRun.timed B pk c runCost)
      (rc + T + ∑ j ∈ Finset.range q, (2 * (3 * (0 + j)) + 20) + 5) := by
  unfold uRedRun.timed
  refine stepTimeBound_zero.2 ⟨by omega, fun kstar => ?_⟩
  have himpl : ∀ (i : ℕ) (s : ((C → Option K) × (C → ℕ)) × ((M × C → Option K) × (M × C → ℕ)) ×
        Option M) (d : (M ⊕ (M × C)) ⊕ C),
      ((∀ x, s.1.2 x ≤ 3 * i) ∧ (∀ x, s.2.1.2 x ≤ 3 * i)) →
      StepTimeBound (delay 1 (simImplFO.timed (R := R) c kstar
          { LD := s.1.1, LQ := s.2.1.1, found := s.2.2 } d s.1.2 s.2.1.2))
        (2 * (3 * i) + 20) ∧
      AllRet (fun y => (∀ x, y.2.1.2 x ≤ 3 * (i + 1)) ∧ (∀ x, y.2.2.1.2 x ≤ 3 * (i + 1)))
        (delay 1 (simImplFO.timed (R := R) c kstar
          { LD := s.1.1, LQ := s.2.1.1, found := s.2.2 } d s.1.2 s.2.1.2)).2 := by
    intro i s d hs
    refine ⟨?_, ?_⟩
    · exact (stepTimeBound_delay (simImplFO.timeBound c kstar _ d _ _ hs.1 hs.2)).mono
        (by omega)
    · exact allRet_mono (fun y hy => ⟨fun x => (hy.1 x).trans (by omega),
        fun x => (hy.2 x).trans (by omega)⟩) (simImplFO.allRet_le c kstar _ d _ _ hs.1 hs.2)
  have hX := OracleAdv.Timed.timeBound_simulateHat_inv
    (fun y : ((C → Option K) × (C → ℕ)) × ((M × C → Option K) × (M × C → ℕ)) × Option M =>
      ({ LD := y.1.1, LQ := y.2.1.1, found := y.2.2 } : FOTransformU.SimState M C K))
    (fun y : FOTransformU.SimState M C K =>
      ((fun a => y.LD a, fun _ => 0), (fun a => y.LQ a, fun _ => 0), y.found))
    (fun st a => delay 1 (simImplFO.timed (R := R) c kstar
      { LD := st.1.1, LQ := st.2.1.1, found := st.2.2 } a st.1.2 st.2.1.2))
    (fun i s => (∀ x, s.1.2 x ≤ 3 * i) ∧ (∀ x, s.2.1.2 x ≤ 3 * i))
    (fun i => 2 * (3 * i) + 20) himpl (hA kstar)
    (by simpa using hq kstar) 0
    ((fun _ => none, fun _ => 0), (fun _ => none, fun _ => 0), none)
    ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  have key : ∀ {β : Type} (X : ℕ × OracleAdv.Timed (M ⊕ M × C) (R ⊕ Bool) β)
      (f : β → ℕ × OracleAdv.Timed (M ⊕ M × C) (R ⊕ Bool) M) (N₁ N₂ : ℕ),
      StepTimeBound X (N₁ + N₂) → (∀ x, StepTimeBound (f x) 2) →
      1 + runCost pk c kstar + 1 + X.1 + (X.2.bind f).1 ≤ rc + N₁ + N₂ + 5 - 1 ∧
        (X.2.bind f).2.TimeBound
          (rc + N₁ + N₂ + 5 - 1 - (1 + runCost pk c kstar + 1 + X.1 + (X.2.bind f).1)) := by
    intro β X f N₁ N₂ hX hf
    have hB := timeBound_bind hX.2 hf
    have h1 := hX.1
    have h2 := hB.1
    have h3 := hr kstar
    exact ⟨by omega, hB.2.mono (by omega)⟩
  exact key _ _ _ _ hX fun _ => ⟨le_rfl, trivial⟩

/-- **Time of `uRedROM.timed`.** The bound of `uRedRun.timeBound`, for every public key and
challenge. -/
theorem uRedROM.timeBound {qRO qD : ℕ}
    (B : Games.ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) (runCost : PK → C → K → ℕ)
    {rc T q : ℕ} (hr : ∀ pk c k, runCost pk c k ≤ rc)
    (hA : ∀ pk c k, (ofAdv (B.run pk c k)).TimeBound T)
    (hq : ∀ pk c k, (B.run pk c k).IsQueryBound q) :
    (uRedROM.timed B runCost).TimeBound
      (rc + T + ∑ j ∈ Finset.range q, (2 * (3 * (0 + j)) + 20) + 6) :=
  fun pk c => by
    unfold uRedROM.timed
    dsimp only
    unfold uRedROM.run.tree.timed
    exact (stepTimeBound_delay (uRedRun.timeBound B pk c runCost (hr pk c) (hA pk c)
      (hq pk c))).mono (by omega)

end CatCrypt.Crypto.KEM.FOTransform
