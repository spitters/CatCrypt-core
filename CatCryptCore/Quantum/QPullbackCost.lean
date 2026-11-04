/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QPullbackCascade
public import CatCryptCore.Quantum.QSimTimed
public import CatCryptCore.Quantum.QTreeKind

/-!
# Quantum time certificates of environments with quantum memory

The costed mirrors `QStratQ.Timed` of environments with quantum memory (`QStratQ`,
`QRealizesMem.lean`) and `QSys.Timed` of quantum systems are derived by
`derive_timed_structure` over the quantum tree kind (`QTreeKind.lean`): each step field is a
costed instrument `QInstrT` with a cost companion. The time bound `ZT.TimeBound n o` bounds each
`next` activation of `ZT` (its step cost followed by its costed computation, weighed by
`ProgE.Bound Costed.weight`) by `n` and each `obs` activation by `o`, from every state; the time
bound `XT.TimeBound s` of a costed system bounds each activation by `s`.

An environment `Z` has time `(n, o, q)` (`QEnvTimeBound Z ZT n o q`) when the costed environment
`ZT` erases to `Z`, its activations are bounded by `n` and `o`, and `Z` makes at most `q`
activations. The view of a quantum environment returns its final state, and realization
(`QRealizesQB`) bounds the diamond distance of the views, which ranges over all final
measurements; the environment carries no distinguisher whose time would be bounded.
`QRealizesQBTime R I n o q b` is realization against the environments with memory of time
`(n, o, q)`.

The costed form `QSimQ.absorb.timed` of absorption is derived by `derive_reduction`; it erases
to the absorption (`QSimQ.absorb_timed_erases`), and absorbing a simulator whose `pre` and
`post` steps take time at most `a` and `b` into an environment of activation times `n` and `o`
gives activation times `n + a + 2` and `b + o + 2` (`QSimQ.absorb_timeBound`).

A costed pullback `F : QCostedPullbackQ E O E' O' d` is a pullback over environments with memory
(`QEnvPullbackQ`) with a costed environment reduction `F.pullT`, constants `F.nextC`, `F.obsC`
added to the activation times and a map `r ↦ F.roundsMul * r + F.roundsAdd` of the activation
count. Costed pullbacks compose (`QCostedPullbackQ.comp`) and satisfy the costed pullback law
(`QCostedPullbackQ.realizes_map`, `QCostedPullbackQ.realizesTime_map`). Absorption
(`QSimQ.toQCostedPullbackQ`, `QSimQ.toQCostedPullbackQL`) and the two cascade contexts
(`QSys.cascadeLeft.toCosted`, `QSys.cascadeRight.toCosted`) are costed pullbacks, which gives the
composition theorem for the quantum cascade with the time of both reduced environments
(`QRealizesQB.cascade_timed`).

Search words: quantum time certificate, costed quantum environment, quantum environment,
environment with quantum memory, activation time, activation count, costed pullback,
composition theorem, quantum cascade, simulator absorption.

## Main definitions

* `QStratQ.Timed`, `QStratQ.Timed.Erases`, `QStratQ.Timed.TimeBound`: derived costed
  environments with memory; `QSys.Timed`, `QSys.Timed.Erases`, `QSys.Timed.TimeBound`: derived
  costed quantum systems.
* `QSimQ.absorb.timed`: the derived costed absorption.
* `QEnvTimeBound Z ZT n o q`: the time of a quantum environment with memory.
* `QRealizesQBTime R I n o q b`: realization against the environments of time `(n, o, q)`.
* `QCostedPullbackQ`, `QCostedPullbackQ.comp`: costed pullbacks over environments with memory.
* `QSimQ.toQCostedPullbackQ`, `QSimQ.toQCostedPullbackQL`, `QSys.cascadeLeft.toCosted`,
  `QSys.cascadeRight.toCosted`: the costed instances.

## Main results

* `QSimQ.absorb_timeBound`: the time of absorption, `n + a + 2` and `b + o + 2`.
* `QCostedPullbackQ.pull_envTimeBound`: the time of the reduced environment.
* `QCostedPullbackQ.realizes_map`, `QCostedPullbackQ.realizesTime_map`: the costed pullback law.
* `QCostedPullbackQ.realizes_twoHole`: the composition theorem for two holes with the time of
  each reduced environment.
* `QRealizesQB.cascade_timed`: the composition theorem for the quantum cascade with the time of
  each reduced environment.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum CatCrypt.Crypto.Party
open CatCrypt.Crypto.UCTransport (QSysObj)
open scoped ENNReal

/-! ## Derived costed forms -/

derive_timed_structure QStratQ

derive_timed_structure QSys

derive_reduction QSimQ.absorb

/-- A time bound of a costed environment holds at larger bounds. -/
theorem QStratQ.Timed.TimeBound.mono {K : Type} [Fintype K] {ζ E O : Type} {d : ℕ}
    {ZT : QStratQ.Timed K ζ E O d} {n o n' o' : ℕ} (h : ZT.TimeBound n o) (hn : n ≤ n')
    (ho : o ≤ o') : ZT.TimeBound n' o' :=
  ⟨fun z => (h.1 z).mono hn, fun z g => (h.2 z g).mono ho⟩

/-- **Time of absorption.** The environment `Z` with the simulator absorbed, costed by the
costed environment `ZT` of activation times `n` and `o` and by costed simulator steps whose
`pre` steps take time at most `a` and whose `post` steps take time at most `b`: each `next`
activation takes time at most `n + a + 2` and each `obs` activation at most `b + o + 2`. -/
theorem QSimQ.absorb_timeBound {K : Type} [Fintype K] {ζ E O : Type} {d : ℕ}
    {M σ EG OG : Type} [Fintype M] (S : QSimQ M σ E O EG OG d) (Z : QStratQ K ζ E O d)
    {ZT : QStratQ.Timed K ζ E O d} (pre : σ → E → QInstrT (Fin d × M) (σ × EG) fun _ => Fin d × M)
    (preCost : σ → E → ℕ) (post : σ → OG → QInstrT (Fin d × M) (σ × O) fun _ => Fin d × M)
    (postCost : σ → OG → ℕ) {n o a b : ℕ} (hZ : ZT.TimeBound n o)
    (hpre : ∀ s e, QInstrT.StepTimeBound (preCost s e, pre s e) a)
    (hpost : ∀ s g, QInstrT.StepTimeBound (postCost s g, post s g) b) :
    (QSimQ.absorb.timed S Z ZT.next ZT.nextCost pre preCost post postCost ZT.obs
      ZT.obsCost).TimeBound (n + a + 2) (b + o + 2) := by
  refine ⟨fun c => ?_, fun c g => ?_⟩
  · change QInstrT.StepTimeBound (QSimQ.absorb.next.tree.timed S Z ZT.next ZT.nextCost pre
      preCost post postCost ZT.obs ZT.obsCost c) _
    unfold QSimQ.absorb.next.tree.timed
    refine (QInstrT.stepTimeBound_delay_bind _ _ _ (t := n - ZT.nextCost c.1) (u := 1 + a)
      ((QInstrT.bound_placeLeft _ _ _ _ _ _).2 (hZ.1 c.1).2) fun x => ?_).mono
      (by have := (hZ.1 c.1).1; omega)
    exact (QInstrT.stepTimeBound_delay_bind _ _ _ (t := a - preCost c.2 x.2)
      ((QInstrT.bound_placeRight _ _ _ _ _ _).2 (hpre c.2 x.2).2) fun _ =>
        QInstrT.stepTimeBound_ret _ _).mono (by have := (hpre c.2 x.2).1; omega)
  · change QInstrT.StepTimeBound (QSimQ.absorb.obs.tree.timed S Z ZT.next ZT.nextCost pre
      preCost post postCost ZT.obs ZT.obsCost c g) _
    unfold QSimQ.absorb.obs.tree.timed
    refine (QInstrT.stepTimeBound_delay_bind _ _ _ (t := b - postCost c.2 g) (u := 1 + o)
      ((QInstrT.bound_placeRight _ _ _ _ _ _).2 (hpost c.2 g).2) fun x => ?_).mono
      (by have := (hpost c.2 g).1; omega)
    exact (QInstrT.stepTimeBound_delay_bind _ _ _ (t := o - ZT.obsCost c.1 x.2)
      ((QInstrT.bound_placeLeft _ _ _ _ _ _).2 (hZ.2 c.1 x.2).2) fun _ =>
        QInstrT.stepTimeBound_ret _ _).mono (by have := (hZ.2 c.1 x.2).1; omega)

/-! ## The time of a quantum environment with memory -/

/-- The quantum environment `Z` with memory `K` has time `(n, o, q)`: the costed environment `ZT`
erases to `Z`, each `next` activation of `ZT` (step cost followed by its costed computation)
costs at most `n` and each `obs` activation at most `o`, and `Z` makes at most `q`
activations. -/
structure QEnvTimeBound {K : Type} [Fintype K] {ζ E O : Type} {d : ℕ} (Z : QStratQ K ζ E O d)
    (ZT : QStratQ.Timed K ζ E O d) (n o q : ℕ) : Prop where
  /-- The costed environment erases to `Z`. -/
  erases : ZT.Erases Z
  /-- The time of an activation. -/
  timeBound : ZT.TimeBound n o
  /-- The number of activations. -/
  rounds_le : Z.rounds ≤ q

/-- The time of an environment holds at larger bounds. -/
theorem QEnvTimeBound.mono {K : Type} [Fintype K] {ζ E O : Type} {d : ℕ}
    {Z : QStratQ K ζ E O d} {ZT : QStratQ.Timed K ζ E O d} {n o q n' o' q' : ℕ}
    (h : QEnvTimeBound Z ZT n o q) (hn : n ≤ n') (ho : o ≤ o') (hq : q ≤ q') :
    QEnvTimeBound Z ZT n' o' q' where
  erases := h.erases
  timeBound := h.timeBound.mono hn ho
  rounds_le := h.rounds_le.trans hq

/-! ## Realization against time-bounded quantum environments -/

section RealizesTime

variable {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
variable {τ υ E O : Type} {d : ℕ}

/-- `R` realizes `I` with the environment-dependent bound `b` against every quantum environment
with memory of time `(n, o, q)`. -/
def QRealizesQBTime (R : QSys H τ E O d) (I : QSys H' υ E O d) (n o q : ℕ)
    (b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞) :
    Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ζ : Type) (Z : QStratQ K ζ E O d)
    (ZT : QStratQ.Timed K ζ E O d), QEnvTimeBound Z ZT n o q →
      cpDist (qviewQ R Z) (qviewQ I Z) ≤ b K ζ Z

/-- A realization against environments with memory is a realization against the environments of
every time. -/
theorem QRealizesQB.realizesQBTime {R : QSys H τ E O d} {I : QSys H' υ E O d}
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞}
    (h : QRealizesQB R I b) (n o q : ℕ) : QRealizesQBTime R I n o q b :=
  fun K _ _ ζ Z _ _ => h K ζ Z

/-- Realization against the environments of time `(n', o', q')` is realization against the
environments of every smaller time `(n, o, q)`. -/
theorem QRealizesQBTime.mono {R : QSys H τ E O d} {I : QSys H' υ E O d} {n o q n' o' q' : ℕ}
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞}
    (h : QRealizesQBTime R I n' o' q' b) (hn : n ≤ n') (ho : o ≤ o') (hq : q ≤ q') :
    QRealizesQBTime R I n o q b :=
  fun K _ _ ζ Z ZT hT => h K ζ Z ZT (hT.mono hn ho hq)

end RealizesTime

/-! ## Costed pullbacks over environments with memory -/

/-- A costed pullback over environments with memory: a pullback `QEnvPullbackQ` with a costed
form `pullT` of its environment reduction, which erases to the reduced environment, adds at
most `nextC` to the time of a `next` activation and `obsC` to the time of an `obs` activation,
and maps an activation count `r` to at most `roundsMul * r + roundsAdd`. -/
structure QCostedPullbackQ (E O E' O' : Type) (d : ℕ) : Type 1 extends
    QEnvPullbackQ E O E' O' d where
  /-- The costed environment reduction. -/
  pullT : {K : Type} → [Fintype K] → [DecidableEq K] → {ζ : Type} → QStratQ K ζ E' O' d →
    QStratQ.Timed K ζ E' O' d → QStratQ.Timed (Mem K) (Ctx ζ) E O d
  /-- The time added to a `next` activation. -/
  nextC : ℕ
  /-- The time added to an `obs` activation. -/
  obsC : ℕ
  /-- The factor of the activation count. -/
  roundsMul : ℕ
  /-- The activations added. -/
  roundsAdd : ℕ
  /-- Erasure of the costed reduction. -/
  pullT_erases : ∀ {K : Type} [Fintype K] [DecidableEq K] {ζ : Type} (Z : QStratQ K ζ E' O' d)
    (ZT : QStratQ.Timed K ζ E' O' d), ZT.Erases Z → (pullT Z ZT).Erases (pull Z)
  /-- Time of the costed reduction. -/
  pullT_timeBound : ∀ {K : Type} [Fintype K] [DecidableEq K] {ζ : Type}
    (Z : QStratQ K ζ E' O' d) (ZT : QStratQ.Timed K ζ E' O' d) {n o : ℕ},
    ZT.TimeBound n o → (pullT Z ZT).TimeBound (n + nextC) (o + obsC)
  /-- The activation count of the reduced environment. -/
  pull_rounds_le : ∀ {K : Type} [Fintype K] [DecidableEq K] {ζ : Type}
    (Z : QStratQ K ζ E' O' d), (pull Z).rounds ≤ roundsMul * Z.rounds + roundsAdd

namespace QCostedPullbackQ

variable {E O E₁ O₁ E₂ O₂ : Type} {d : ℕ}

/-- **Time of the reduced environment.** If `Z` has time `(n, o, q)` with the costed environment
`ZT`, then `F.pull Z` has time `(n + F.nextC, o + F.obsC, F.roundsMul * q + F.roundsAdd)` with
the costed environment `F.pullT Z ZT`. -/
theorem pull_envTimeBound (F : QCostedPullbackQ E O E₁ O₁ d) {K : Type} [Fintype K]
    [DecidableEq K] {ζ : Type} {Z : QStratQ K ζ E₁ O₁ d} {ZT : QStratQ.Timed K ζ E₁ O₁ d}
    {n o q : ℕ} (h : QEnvTimeBound Z ZT n o q) :
    QEnvTimeBound (F.pull Z) (F.pullT Z ZT) (n + F.nextC) (o + F.obsC)
      (F.roundsMul * q + F.roundsAdd) where
  erases := F.pullT_erases Z ZT h.erases
  timeBound := F.pullT_timeBound Z ZT h.timeBound
  rounds_le := (F.pull_rounds_le Z).trans (by gcongr; exact h.rounds_le)

/-- **Composition of costed pullbacks**: the costed reduction of `G` followed by that of `F`;
the activation constants add, and the maps of the activation count compose. -/
def comp (F : QCostedPullbackQ E O E₁ O₁ d) (G : QCostedPullbackQ E₁ O₁ E₂ O₂ d) :
    QCostedPullbackQ E O E₂ O₂ d where
  toQEnvPullbackQ := F.toQEnvPullbackQ.comp G.toQEnvPullbackQ
  pullT Z ZT := F.pullT (G.pull Z) (G.pullT Z ZT)
  nextC := G.nextC + F.nextC
  obsC := G.obsC + F.obsC
  roundsMul := F.roundsMul * G.roundsMul
  roundsAdd := F.roundsMul * G.roundsAdd + F.roundsAdd
  pullT_erases Z ZT h := F.pullT_erases _ _ (G.pullT_erases Z ZT h)
  pullT_timeBound Z ZT n o h := by
    have := F.pullT_timeBound (G.pull Z) _ (G.pullT_timeBound Z ZT h)
    rw [Nat.add_assoc, Nat.add_assoc] at this
    exact this
  pull_rounds_le Z := by
    have h1 := F.pull_rounds_le (G.pull Z)
    have h2 := Nat.mul_le_mul_left F.roundsMul (G.pull_rounds_le Z)
    change (F.pull (G.pull Z)).rounds ≤ _
    rw [Nat.mul_add, ← Nat.mul_assoc] at h2
    omega

/-- **Costed pullback law.** If `X` realizes `Y` against environments with memory with bound
`b`, both admissible, then `F.map X` realizes `F.map Y` with bound `b` at the pulled-back
environment, and the pulled-back environment of an environment of time `(n, o, q)` has time
`(n + F.nextC, o + F.obsC, F.roundsMul * q + F.roundsAdd)`. -/
theorem realizes_map (F : QCostedPullbackQ E O E₁ O₁ d) {X Y : QSysObj E O d} (hX : F.Adm X)
    (hY : F.Adm Y)
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞}
    (h : QRealizesQB X.sys Y.sys b) :
    QRealizesQB (F.map X).sys (F.map Y).sys
        (fun K _ _ ζ Z => b (F.Mem K) (F.Ctx ζ) (F.pull Z)) ∧
      ∀ {K : Type} [Fintype K] [DecidableEq K] {ζ : Type} (Z : QStratQ K ζ E₁ O₁ d)
        (ZT : QStratQ.Timed K ζ E₁ O₁ d) {n o q : ℕ}, QEnvTimeBound Z ZT n o q →
          QEnvTimeBound (F.pull Z) (F.pullT Z ZT) (n + F.nextC) (o + F.obsC)
            (F.roundsMul * q + F.roundsAdd) :=
  ⟨F.toQEnvPullbackQ.realizes_map hX hY h, fun _ _ _ _ _ hT => F.pull_envTimeBound hT⟩

/-- **Costed pullback law against time-bounded environments.** If `X` realizes `Y` with bound `b`
against the environments of time `(n + F.nextC, o + F.obsC, F.roundsMul * q + F.roundsAdd)`,
both admissible, then `F.map X` realizes `F.map Y` with bound `b` at the pulled-back
environment against the environments of time `(n, o, q)`. -/
theorem realizesTime_map (F : QCostedPullbackQ E O E₁ O₁ d) {X Y : QSysObj E O d}
    (hX : F.Adm X) (hY : F.Adm Y) {n o q : ℕ}
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E O d → ℝ≥0∞}
    (h : QRealizesQBTime X.sys Y.sys (n + F.nextC) (o + F.obsC)
      (F.roundsMul * q + F.roundsAdd) b) :
    QRealizesQBTime (F.map X).sys (F.map Y).sys n o q
      fun K _ _ ζ Z => b (F.Mem K) (F.Ctx ζ) (F.pull Z) :=
  fun K _ _ ζ Z ZT hT => by
    rw [F.view_map hX, F.view_map hY]
    exact le_trans (cpDist_bind_pure_le _ _ _) (h _ _ _ _ (F.pull_envTimeBound hT))

/-- **Composition theorem for two holes with time certificates.** As
`QEnvPullbackQ.realizes_twoHole`; in addition, the reduced environment of each hole of an
environment of time `(n, o, q)` has the time given by its costed pullback. -/
theorem realizes_twoHole (F : QCostedPullbackQ E₁ O₁ E O d) (G : QCostedPullbackQ E₂ O₂ E O d)
    {X X' : QSysObj E₁ O₁ d} {Y Y' : QSysObj E₂ O₂ d}
    (hX : F.Adm X) (hX' : F.Adm X') (hY : G.Adm Y) (hY' : G.Adm Y')
    (hmid : ∀ (K : Type) [Fintype K] [DecidableEq K] (ζ : Type) (Z : QStratQ K ζ E O d),
      qviewQ (F.map X').sys Z = qviewQ (G.map Y).sys Z)
    {bX : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E₁ O₁ d →
      ℝ≥0∞}
    {bY : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E₂ O₂ d →
      ℝ≥0∞}
    (hXr : QRealizesQB X.sys X'.sys bX) (hYr : QRealizesQB Y.sys Y'.sys bY) :
    QRealizesQB (F.map X).sys (G.map Y').sys
        (fun K _ _ ζ Z => bX (F.Mem K) (F.Ctx ζ) (F.pull Z) + bY (G.Mem K) (G.Ctx ζ) (G.pull Z)) ∧
      ∀ {K : Type} [Fintype K] [DecidableEq K] {ζ : Type} (Z : QStratQ K ζ E O d)
        (ZT : QStratQ.Timed K ζ E O d) {n o q : ℕ}, QEnvTimeBound Z ZT n o q →
          QEnvTimeBound (F.pull Z) (F.pullT Z ZT) (n + F.nextC) (o + F.obsC)
              (F.roundsMul * q + F.roundsAdd) ∧
            QEnvTimeBound (G.pull Z) (G.pullT Z ZT) (n + G.nextC) (o + G.obsC)
              (G.roundsMul * q + G.roundsAdd) :=
  ⟨F.toQEnvPullbackQ.realizes_twoHole G.toQEnvPullbackQ hX hX' hY hY' hmid hXr hYr,
    fun _ _ _ _ _ hT => ⟨F.pull_envTimeBound hT, G.pull_envTimeBound hT⟩⟩

end QCostedPullbackQ

/-! ## Costed absorption -/

namespace QSimQ

variable {K M σ E O EG OG ζ : Type} [Fintype K] [Fintype M] {d : ℕ}

/-- The costed absorption erases to the absorption: for costed simulator steps erasing to the
steps of `S` and a costed environment erasing to `Z`. -/
theorem absorb_timed_erases (S : QSimQ M σ E O EG OG d) (Z : QStratQ K ζ E O d)
    {ZT : QStratQ.Timed K ζ E O d}
    (pre : σ → E → QInstrT (Fin d × M) (σ × EG) fun _ => Fin d × M) (preCost : σ → E → ℕ)
    (post : σ → OG → QInstrT (Fin d × M) (σ × O) fun _ => Fin d × M) (postCost : σ → OG → ℕ)
    (hpre : ∀ s e, (pre s e).erase = S.pre s e) (hpost : ∀ s g, (post s g).erase = S.post s g)
    (hZ : ZT.Erases Z) :
    (QSimQ.absorb.timed S Z ZT.next ZT.nextCost pre preCost post postCost ZT.obs
      ZT.obsCost).Erases (S.absorb Z) := by
  subst hZ
  exact QSimQ.absorb.erase_timed S _ _ _ _ _ _ _ _ _ (fun _ => rfl) hpre hpost fun _ _ => rfl

variable [DecidableEq M]

/-- Absorption of a simulator with a private register as a costed pullback, from costed
simulator steps erasing to those of `S` whose `pre` steps take time at most `a` and whose
`post` steps take time at most `b`: the costed reduction is the derived costed absorption, the
constants are `a + 2` and `b + 2`, and the activation count is kept. -/
noncomputable def toQCostedPullbackQ (S : QSimQ M σ E O EG OG d)
    (pre : σ → E → QInstrT (Fin d × M) (σ × EG) fun _ => Fin d × M) (preCost : σ → E → ℕ)
    (post : σ → OG → QInstrT (Fin d × M) (σ × O) fun _ => Fin d × M) (postCost : σ → OG → ℕ)
    (hpre : ∀ s e, (pre s e).erase = S.pre s e) (hpost : ∀ s g, (post s g).erase = S.post s g)
    {a b : ℕ} (hpreT : ∀ s e, QInstrT.StepTimeBound (preCost s e, pre s e) a)
    (hpostT : ∀ s g, QInstrT.StepTimeBound (postCost s g, post s g) b) :
    QCostedPullbackQ EG OG E O d where
  toQEnvPullbackQ := S.toQEnvPullbackQ
  pullT Z ZT :=
    QSimQ.absorb.timed S Z ZT.next ZT.nextCost pre preCost post postCost ZT.obs ZT.obsCost
  nextC := a + 2
  obsC := b + 2
  roundsMul := 1
  roundsAdd := 0
  pullT_erases Z _ h := absorb_timed_erases S Z pre preCost post postCost hpre hpost h
  pullT_timeBound Z _ _ _ h :=
    (absorb_timeBound S Z pre preCost post postCost h hpreT hpostT).mono (by omega) (by omega)
  pull_rounds_le Z := by simp [toQEnvPullbackQ, absorb]

/-- Absorption of a simulator with a private register, the simulator register on the left of
the system register, as a costed pullback; costed reduction and constants as in
`toQCostedPullbackQ`. -/
noncomputable def toQCostedPullbackQL (S : QSimQ M σ E O EG OG d)
    (pre : σ → E → QInstrT (Fin d × M) (σ × EG) fun _ => Fin d × M) (preCost : σ → E → ℕ)
    (post : σ → OG → QInstrT (Fin d × M) (σ × O) fun _ => Fin d × M) (postCost : σ → OG → ℕ)
    (hpre : ∀ s e, (pre s e).erase = S.pre s e) (hpost : ∀ s g, (post s g).erase = S.post s g)
    {a b : ℕ} (hpreT : ∀ s e, QInstrT.StepTimeBound (preCost s e, pre s e) a)
    (hpostT : ∀ s g, QInstrT.StepTimeBound (postCost s g, post s g) b) :
    QCostedPullbackQ EG OG E O d where
  toQEnvPullbackQ := S.toQEnvPullbackQL
  pullT Z ZT :=
    QSimQ.absorb.timed S Z ZT.next ZT.nextCost pre preCost post postCost ZT.obs ZT.obsCost
  nextC := a + 2
  obsC := b + 2
  roundsMul := 1
  roundsAdd := 0
  pullT_erases Z _ h := absorb_timed_erases S Z pre preCost post postCost hpre hpost h
  pullT_timeBound Z _ _ _ h :=
    (absorb_timeBound S Z pre preCost post postCost h hpreT hpostT).mono (by omega) (by omega)
  pull_rounds_le Z := by simp [toQEnvPullbackQL, absorb]

end QSimQ

/-! ## The quantum cascade with time certificates -/

namespace QSys

variable {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
variable {τ υ E M O : Type} {d : ℕ}

/-- The cascade context with the hole on the left, `- ≫ Y`, as a costed pullback, from a costed
system `YT` erasing to `Y` with activations of time at most `s`: the events pass through at
step cost `0`, and the constants are `2` and `s + 2`. -/
noncomputable def cascadeLeft.toCosted (E : Type) (Y : QSys H' υ M O d)
    (YT : QSys.Timed H' υ M O d) (hE : YT.Erases Y) {s : ℕ} (hT : YT.TimeBound s) :
    QCostedPullbackQ E M E O d :=
  (asPostSim E Y).toQCostedPullbackQ (fun u e => QInstrT.ret _ _ _ (u, e)) (fun _ _ => 0)
    YT.step YT.stepCost (fun _ _ => QInstrT.erase_ret _) (fun u m => by subst hE; rfl)
    (fun _ _ => QInstrT.stepTimeBound_ret _ _) hT

/-- The cascade context with the hole on the right, `X ≫ -`, as a costed pullback, from a
costed system `XT` erasing to `X` with activations of time at most `s`: the outputs pass
through at step cost `0`, and the constants are `s + 2` and `2`. -/
noncomputable def cascadeRight.toCosted (O : Type) (X : QSys H τ E M d)
    (XT : QSys.Timed H τ E M d) (hE : XT.Erases X) {s : ℕ} (hT : XT.TimeBound s) :
    QCostedPullbackQ M O E O d :=
  (asPreSim O X).toQCostedPullbackQL XT.step XT.stepCost (fun t o => QInstrT.ret _ _ _ (t, o))
    (fun _ _ => 0) (fun t e => by subst hE; rfl) (fun _ _ => QInstrT.erase_ret _) hT
    (fun _ _ => QInstrT.stepTimeBound_ret _ _)

end QSys

/-- **Composition theorem for the quantum cascade with time certificates.** As
`QRealizesQB.cascade`; in addition, for costed systems `YT` of `Y` and `XT'` of `X'` with
activations of time at most `sY` and `sX`, the environment that absorbs `Y` and the environment
that absorbs `X'`, reduced from an environment of time `(n, o, q)`, have the derived costed
absorptions as costed forms, of time `(n + 2, o + (sY + 2), q)` and `(n + (sX + 2), o + 2, q)`. -/
theorem QRealizesQB.cascade_timed {H H' H₁ H₂ : Type} [Fintype H] [DecidableEq H] [Fintype H']
    [DecidableEq H'] [Fintype H₁] [DecidableEq H₁] [Fintype H₂] [DecidableEq H₂]
    {τ υ τ₁ υ₂ E M O : Type} {d : ℕ} {X : QSys H τ E M d} {X' : QSys H₁ τ₁ E M d}
    {Y : QSys H' υ M O d} {Y' : QSys H₂ υ₂ M O d}
    (YT : QSys.Timed H' υ M O d) (XT' : QSys.Timed H₁ τ₁ E M d) (hEY : YT.Erases Y)
    (hEX : XT'.Erases X') {sY sX : ℕ} (hTY : YT.TimeBound sY) (hTX : XT'.TimeBound sX)
    {bX : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ E M d → ℝ≥0∞}
    {bY : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) → QStratQ K ζ M O d → ℝ≥0∞}
    (hX : QRealizesQB X X' bX) (hY : QRealizesQB Y Y' bY) :
    QRealizesQB (X.cascade Y) (X'.cascade Y') (fun K _ _ ζ Z =>
        bX (K × H') (ζ × υ) ((QSys.asPostSim E Y).absorb Z) +
          bY (K × H₁) (ζ × τ₁) ((QSys.asPreSim O X').absorb Z)) ∧
      ∀ {K : Type} [Fintype K] [DecidableEq K] {ζ : Type} (Z : QStratQ K ζ E O d)
        (ZT : QStratQ.Timed K ζ E O d) {n o q : ℕ}, QEnvTimeBound Z ZT n o q →
          QEnvTimeBound ((QSys.asPostSim E Y).absorb Z)
              ((QSys.cascadeLeft.toCosted E Y YT hEY hTY).pullT Z ZT) (n + (0 + 2))
              (o + (sY + 2)) (1 * q + 0) ∧
            QEnvTimeBound ((QSys.asPreSim O X').absorb Z)
              ((QSys.cascadeRight.toCosted O X' XT' hEX hTX).pullT Z ZT) (n + (sX + 2))
              (o + (0 + 2)) (1 * q + 0) :=
  ⟨QRealizesQB.cascade hX hY,
    fun _ _ _ _ _ hT => ⟨(QSys.cascadeLeft.toCosted E Y YT hEY hTY).pull_envTimeBound hT,
      (QSys.cascadeRight.toCosted O X' XT' hEX hTX).pull_envTimeBound hT⟩⟩

end CatCrypt.Quantum.ReactiveUC
