/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCPullback
public import CatCryptCore.Crypto.UCPullbackTimed

/-!
# Costed environment pullbacks: the pullback law with time certificates

An environment `Z` has time `(n, o, q, tD)` (`EnvTimeBound Z ZT ZE n o q tD`) when it has a
costed strategy `ZT` (`Strat.Timed`) and a costed environment `ZE` (`UCConcrete.Env.Timed`)
erasing to it, each `next` activation of `ZT` costs at most `n` and each `obs` activation at
most `o`, its strategy makes at most `q` activations (`Z.input.rounds ≤ q`), and its
distinguisher costs at most `tD` on every state. These four numbers bound the whole run of `Z`:
against a system whose step costs at most `s`, the reset to the heap, the view and the
distinguisher cost at most `|heap| + q · (n + o + s + 9) + tD + 6` plus the cost of the
system (`EnvTimeBound.sysEnvTree_time`, from `sysEnvTree.timeBound_timed`).

A *costed pullback* `F : CostedPullback E O E' O'` is an environment pullback (`EnvPullback`,
`UCPullback.lean`) with costed forms `F.pullT` and `F.pullE` of its environment reduction on the
costed strategy and on the costed environment, and with constants `F.nextC`, `F.obsC`, `F.distC`,
`F.roundsMul`, `F.roundsAdd`, such that the reduced environment `F.pull Z` of an environment of
time `(n, o, q, tD)` has time
`(n + F.nextC, o + F.obsC, F.roundsMul · q + F.roundsAdd, tD + F.distC)`
(`CostedPullback.pull_envTimeBound`). Costed pullbacks compose (`CostedPullback.comp`): the
activation and distinguisher constants add and the maps of the activation count compose.

`RealizesTime X Y n o q tD b` is realization against the environments of time `(n, o, q, tD)`.
The time-graded pullback law (`CostedPullback.realizesTime_map`) maps a realization against the
environments of the reduced time to a realization of the images against the environments of
time `(n, o, q, tD)`. The costed pullback law (`CostedPullback.realizes_map`) and the composition
theorem for two holes (`CostedPullback.realizes_twoHole`) state, with the realization, the time
of each reduced environment.

Instances: the hybrid context (`Hybrid.toCostedPullback`), adversary absorption
(`AdvSys.toCostedPullback`), and either side of the cascade (`EnvPullback.seqLeft.toCosted`,
`EnvPullback.seqRight.toCosted`), with the cascade composition theorem `realizes_seq_timed`. Each
keeps the activation count (`roundsMul = 1`, `roundsAdd = 0`) and adds `1` to the
distinguisher (`Hybrid.Timed.reduceEnv_dist_le`); the costed reductions are the derived
`Hybrid.reduce.timed`, `Hybrid.reduceEnv.timed` and `Strat.absorb.timed`.

Search words: costed pullback, time certificate, environment reduction, composition theorem,
activation time, activation count, distinguisher time, adversary absorption, cascade.

## Main definitions

* `EnvTimeBound Z ZT ZE n o q tD`: the time of an environment.
* `CostedPullback E O E' O'`: costed environment pullbacks.
* `CostedPullback.comp`: composition.
* `RealizesTime X Y n o q tD b`: realization against the environments of time `(n, o, q, tD)`.
* `Hybrid.toCostedPullback`, `AdvSys.toCostedPullback`, `EnvPullback.seqLeft.toCosted`,
  `EnvPullback.seqRight.toCosted`: the instances.

## Main results

* `EnvTimeBound.sysEnvTree_time`: the time of the whole run of an environment.
* `CostedPullback.pull_envTimeBound`: the time of the reduced environment.
* `CostedPullback.realizes_map`: the costed pullback law.
* `CostedPullback.realizesTime_map`: the time-graded pullback law.
* `CostedPullback.realizes_twoHole`: the composition theorem for two holes with the time of each
  reduced environment.
* `realizes_seq_timed`: the cascade composition theorem with the time of each reduced
  environment.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-- A time bound of a costed strategy holds at larger bounds. -/
theorem Strat.Timed.TimeBound.mono {ζ E O : Type} {ZT : Strat.Timed ζ E O} {n o n' o' : ℕ}
    (h : ZT.TimeBound n o) (hn : n ≤ n') (ho : o ≤ o') : ZT.TimeBound n' o' :=
  ⟨fun z => (h.1 z).trans hn, fun z g => (h.2 z g).trans ho⟩

/-- The environment `Z` has time `(n, o, q, tD)`: the costed strategy `ZT` erases to the strategy
of `Z` and the costed environment `ZE` erases to `Z`; each `next` activation of `ZT` costs at
most `n` and each `obs` activation at most `o`; the strategy makes at most `q` activations; and
the distinguisher of `ZE` costs at most `tD` on every state. -/
structure EnvTimeBound {ζ E O : Type} (Z : Env (Strat ζ E O) ζ) (ZT : Strat.Timed ζ E O)
    (ZE : Env.Timed (Strat ζ E O) ζ) (n o q tD : ℕ) : Prop where
  /-- The costed strategy erases to the strategy of `Z`. -/
  strat_erases : ZT.Erases Z.input
  /-- The costed environment erases to `Z`. -/
  env_erases : ZE.Erases Z
  /-- The time of an activation. -/
  timeBound : ZT.TimeBound n o
  /-- The number of activations. -/
  rounds_le : Z.input.rounds ≤ q
  /-- The time of the distinguisher. -/
  dist_le : ∀ z, SPTree.Timed.stepTime (ZE.distCost z, ZE.dist z) ≤ tD

/-- **Time of the whole run of an environment.** For an environment of time `(n, o, q, tD)` and
a costed step of the system `S k` of time at most `s` at every round, the environment reduction
on `k` (the reset to the heap of `Z`, the view of `Z` against `S k` and the distinguisher) costs
at most `|heap| + q · (n + o + s + 9) + tD + SCost k + 6`. -/
theorem EnvTimeBound.sysEnvTree_time {K τ ζ E O : Type} {Z : Env (Strat ζ E O) ζ}
    {ZT : Strat.Timed ζ E O} {ZE : Env.Timed (Strat ζ E O) ζ} {n o q tD : ℕ}
    (h : EnvTimeBound Z ZT ZE n o q tD) (S : K → Sys τ E O) (SCost : K → ℕ)
    {step : K → τ → E → SPTree.Timed (τ × O)} {stepCost : K → τ → E → ℕ} (k : K)
    {InvS : ℕ → τ → Prop} {s : ℕ}
    (hS : SysRunBound (step k) (stepCost k) InvS (fun _ _ => True) (fun _ _ => True)
      (fun _ => s))
    (ht : InvS 0 (S k).init) :
    SPTree.Timed.stepTime (sysEnvTree.timed S SCost Z ZT.next ZT.nextCost step stepCost ZT.obs
        ZT.obsCost ZE.dist ZE.distCost k) ≤
      Z.heap.data.keys.card + q * (n + o + s + 9) + tD + SCost k + 6 := by
  have hZ : StratRunBound ZT.next ZT.nextCost ZT.obs ZT.obsCost (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) (fun _ => n) (fun _ => o) :=
    ⟨fun _ z _ => h.timeBound.1 z,
      fun _ _ _ => SPTree.Timed.allRet_of_forall (fun _ => ⟨trivial, trivial⟩) _,
      fun _ z g _ _ => h.timeBound.2 z g,
      fun _ _ _ _ _ => SPTree.Timed.allRet_of_forall (fun _ => trivial) _⟩
  have hT := sysEnvTree.timeBound_timed S SCost Z k hZ hS trivial ht
    (fun z _ => h.dist_le z)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hT
  have hq := h.rounds_le
  have : Z.input.rounds * (n + o) + Z.input.rounds * s + 9 * Z.input.rounds ≤
      q * (n + o + s + 9) := by
    nlinarith
  omega

/-- A costed environment pullback: an environment pullback with costed forms `pullT` and `pullE`
of its environment reduction, on the costed strategy and on the costed environment, which erase
to the reduced environment, add at most `nextC` to the time of a `next` activation, `obsC` to
the time of an `obs` activation and `distC` to the time of the distinguisher, and map an
activation count `r` to at most `roundsMul * r + roundsAdd`. -/
structure CostedPullback (E O E' O' : Type) extends EnvPullback E O E' O' where
  /-- The costed environment reduction, on the costed strategy of an environment. -/
  pullT : {ζ : Type} → Env (Strat ζ E' O') ζ → Strat.Timed ζ E' O' → Strat.Timed (Ctx ζ) E O
  /-- The costed environment reduction, on the costed environment (its distinguisher). -/
  pullE : {ζ : Type} → Env (Strat ζ E' O') ζ → Env.Timed (Strat ζ E' O') ζ →
    Env.Timed (Strat (Ctx ζ) E O) (Ctx ζ)
  /-- The time added to a `next` activation. -/
  nextC : ℕ
  /-- The time added to an `obs` activation. -/
  obsC : ℕ
  /-- The time added to the distinguisher. -/
  distC : ℕ
  /-- The factor of the activation count. -/
  roundsMul : ℕ
  /-- The activations added. -/
  roundsAdd : ℕ
  /-- Erasure of the costed reduction of the strategy. -/
  pullT_erases : ∀ {ζ : Type} (Z : Env (Strat ζ E' O') ζ) (ZT : Strat.Timed ζ E' O'),
    ZT.Erases Z.input → (pullT Z ZT).Erases (pull Z).input
  /-- Erasure of the costed reduction of the environment. -/
  pullE_erases : ∀ {ζ : Type} (Z : Env (Strat ζ E' O') ζ) (ZE : Env.Timed (Strat ζ E' O') ζ),
    ZE.Erases Z → (pullE Z ZE).Erases (pull Z)
  /-- Time of the costed reduction of the strategy. -/
  pullT_timeBound : ∀ {ζ : Type} (Z : Env (Strat ζ E' O') ζ) (ZT : Strat.Timed ζ E' O')
    {n o : ℕ}, ZT.TimeBound n o → (pullT Z ZT).TimeBound (n + nextC) (o + obsC)
  /-- Time of the distinguisher of the costed reduction of the environment. -/
  pullE_dist_le : ∀ {ζ : Type} (Z : Env (Strat ζ E' O') ζ) (ZE : Env.Timed (Strat ζ E' O') ζ)
    {tD : ℕ}, (∀ z, SPTree.Timed.stepTime (ZE.distCost z, ZE.dist z) ≤ tD) →
      ∀ w, SPTree.Timed.stepTime ((pullE Z ZE).distCost w, (pullE Z ZE).dist w) ≤ tD + distC
  /-- The activation count of the reduced environment. -/
  pull_rounds_le : ∀ {ζ : Type} (Z : Env (Strat ζ E' O') ζ),
    (pull Z).input.rounds ≤ roundsMul * Z.input.rounds + roundsAdd

/-- `X` realizes `Y` with bound `b` against every environment of time `(n, o, q, tD)`. -/
def RealizesTime {τ υ E O : Type} (X : Sys τ E O) (Y : Sys υ E O) (n o q tD : ℕ)
    (b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞) : Prop :=
  ∀ (ζ : Type) (Z : Env (Strat ζ E O) ζ) (ZT : Strat.Timed ζ E O)
    (ZE : Env.Timed (Strat ζ E O) ζ), EnvTimeBound Z ZT ZE n o q tD → adv X Y Z ≤ b ζ Z

/-- A realization is a realization against the environments of every time. -/
theorem Realizes.realizesTime {τ υ E O : Type} {X : Sys τ E O} {Y : Sys υ E O}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes X Y b) (n o q tD : ℕ) :
    RealizesTime X Y n o q tD b :=
  fun ζ Z _ _ _ => h ζ Z

namespace CostedPullback

variable {τ τ' υ υ' E O E₁ O₁ E₂ O₂ : Type}

/-- **Time of the reduced environment.** If `Z` has time `(n, o, q, tD)`, then `F.pull Z` has
time `(n + F.nextC, o + F.obsC, F.roundsMul * q + F.roundsAdd, tD + F.distC)` with the costed
reductions `F.pullT Z ZT` and `F.pullE Z ZE`. -/
theorem pull_envTimeBound (F : CostedPullback E O E₁ O₁) {ζ : Type}
    {Z : Env (Strat ζ E₁ O₁) ζ} {ZT : Strat.Timed ζ E₁ O₁} {ZE : Env.Timed (Strat ζ E₁ O₁) ζ}
    {n o q tD : ℕ} (h : EnvTimeBound Z ZT ZE n o q tD) :
    EnvTimeBound (F.pull Z) (F.pullT Z ZT) (F.pullE Z ZE) (n + F.nextC) (o + F.obsC)
      (F.roundsMul * q + F.roundsAdd) (tD + F.distC) where
  strat_erases := F.pullT_erases Z ZT h.strat_erases
  env_erases := F.pullE_erases Z ZE h.env_erases
  timeBound := F.pullT_timeBound Z ZT h.timeBound
  rounds_le := (F.pull_rounds_le Z).trans (by gcongr; exact h.rounds_le)
  dist_le := F.pullE_dist_le Z ZE h.dist_le

/-- **Composition of costed pullbacks**: the costed reductions of `G` followed by those of `F`;
the activation and distinguisher constants add, and the maps of the activation count compose. -/
def comp (F : CostedPullback E O E₁ O₁) (G : CostedPullback E₁ O₁ E₂ O₂) :
    CostedPullback E O E₂ O₂ where
  toEnvPullback := F.toEnvPullback.comp G.toEnvPullback
  pullT Z ZT := F.pullT (G.pull Z) (G.pullT Z ZT)
  pullE Z ZE := F.pullE (G.pull Z) (G.pullE Z ZE)
  nextC := G.nextC + F.nextC
  obsC := G.obsC + F.obsC
  distC := G.distC + F.distC
  roundsMul := F.roundsMul * G.roundsMul
  roundsAdd := F.roundsMul * G.roundsAdd + F.roundsAdd
  pullT_erases Z ZT h := F.pullT_erases _ _ (G.pullT_erases Z ZT h)
  pullE_erases Z ZE h := F.pullE_erases _ _ (G.pullE_erases Z ZE h)
  pullT_timeBound Z ZT n o h := by
    have := F.pullT_timeBound (G.pull Z) _ (G.pullT_timeBound Z ZT h)
    rw [Nat.add_assoc, Nat.add_assoc] at this
    exact this
  pullE_dist_le Z ZE tD h w := by
    have := F.pullE_dist_le (G.pull Z) _ (G.pullE_dist_le Z ZE h) w
    rw [Nat.add_assoc] at this
    exact this
  pull_rounds_le Z := by
    have h1 := F.pull_rounds_le (G.pull Z)
    have h2 := Nat.mul_le_mul_left F.roundsMul (G.pull_rounds_le Z)
    change (F.pull (G.pull Z)).input.rounds ≤ _
    rw [Nat.mul_add, ← Nat.mul_assoc] at h2
    omega

/-- **Costed pullback law.** If `X` realizes `Y` with bound `b`, both admissible, then `F.map X`
realizes `F.map Y` with bound `b` at the pulled-back environment, and the pulled-back
environment of an environment of time `(n, o, q, tD)` has time
`(n + F.nextC, o + F.obsC, F.roundsMul * q + F.roundsAdd, tD + F.distC)`. -/
theorem realizes_map (F : CostedPullback E O E₁ O₁) {X : Sys τ E O} {Y : Sys υ E O}
    (hX : F.Adm X) (hY : F.Adm Y) {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : Realizes X Y b) :
    Realizes (F.map X) (F.map Y) (fun ζ Z => b (F.Ctx ζ) (F.pull Z)) ∧
      ∀ {ζ : Type} (Z : Env (Strat ζ E₁ O₁) ζ) (ZT : Strat.Timed ζ E₁ O₁)
        (ZE : Env.Timed (Strat ζ E₁ O₁) ζ) {n o q tD : ℕ}, EnvTimeBound Z ZT ZE n o q tD →
          EnvTimeBound (F.pull Z) (F.pullT Z ZT) (F.pullE Z ZE) (n + F.nextC) (o + F.obsC)
            (F.roundsMul * q + F.roundsAdd) (tD + F.distC) :=
  ⟨F.toEnvPullback.realizes_map hX hY h, fun _ _ _ _ _ _ _ hT => F.pull_envTimeBound hT⟩

/-- **Time-graded pullback law.** If `X` realizes `Y` with bound `b` against the environments of
time `(n + F.nextC, o + F.obsC, F.roundsMul * q + F.roundsAdd, tD + F.distC)`, then `F.map X`
realizes `F.map Y` with bound `b` at the pulled-back environment against the environments of
time `(n, o, q, tD)`. -/
theorem realizesTime_map (F : CostedPullback E O E₁ O₁) {X : Sys τ E O} {Y : Sys υ E O}
    (hX : F.Adm X) (hY : F.Adm Y) {n o q tD : ℕ} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : RealizesTime X Y (n + F.nextC) (o + F.obsC) (F.roundsMul * q + F.roundsAdd)
      (tD + F.distC) b) :
    RealizesTime (F.map X) (F.map Y) n o q tD (fun ζ Z => b (F.Ctx ζ) (F.pull Z)) := by
  intro ζ Z ZT ZE hT
  rw [F.adv_map hX hY Z]
  exact h _ _ _ _ (F.pull_envTimeBound hT)

/-- The costed law for a composite: the realization is pulled back through `G` and then `F`,
and the composite reduction of an environment of time `(n, o, q, tD)` has the time given by
`F.comp G`. -/
theorem realizes_map_comp (F : CostedPullback E O E₁ O₁) (G : CostedPullback E₁ O₁ E₂ O₂)
    {X : Sys τ E O} {Y : Sys υ E O} (hX : F.Adm X) (hY : F.Adm Y)
    (hX' : G.Adm (F.map X)) (hY' : G.Adm (F.map Y))
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes X Y b) :
    Realizes (G.map (F.map X)) (G.map (F.map Y))
        (fun ζ Z => b (F.Ctx (G.Ctx ζ)) (F.pull (G.pull Z))) ∧
      ∀ {ζ : Type} (Z : Env (Strat ζ E₂ O₂) ζ) (ZT : Strat.Timed ζ E₂ O₂)
        (ZE : Env.Timed (Strat ζ E₂ O₂) ζ) {n o q tD : ℕ}, EnvTimeBound Z ZT ZE n o q tD →
          EnvTimeBound (F.pull (G.pull Z)) (F.pullT (G.pull Z) (G.pullT Z ZT))
            (F.pullE (G.pull Z) (G.pullE Z ZE)) (n + (F.comp G).nextC) (o + (F.comp G).obsC)
            ((F.comp G).roundsMul * q + (F.comp G).roundsAdd) (tD + (F.comp G).distC) :=
  (F.comp G).realizes_map ⟨hX, hX'⟩ ⟨hY, hY'⟩ h

/-- **Composition theorem for two holes with time certificates.** As
`EnvPullback.realizes_twoHole`; in addition, the reduced environment of each hole of an
environment of time `(n, o, q, tD)` has the time given by `F` for the first hole and by `G` for
the second. -/
theorem realizes_twoHole (F : CostedPullback E₁ O₁ E O) (G : CostedPullback E₂ O₂ E O)
    {X : Sys τ E₁ O₁} {X' : Sys τ' E₁ O₁} {Y : Sys υ E₂ O₂} {Y' : Sys υ' E₂ O₂}
    (hX : F.Adm X) (hX' : F.Adm X') (hY : G.Adm Y) (hY' : G.Adm Y')
    (hmid : ∀ (ζ : Type) (Z : Strat ζ E O), view (F.map X') Z = view (G.map Y) Z)
    {bX : (ζ : Type) → Env (Strat ζ E₁ O₁) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ E₂ O₂) ζ → ℝ≥0∞}
    (hXr : Realizes X X' bX) (hYr : Realizes Y Y' bY) :
    Realizes (F.map X) (G.map Y')
        (fun ζ Z => bX (F.Ctx ζ) (F.pull Z) + bY (G.Ctx ζ) (G.pull Z)) ∧
      ∀ {ζ : Type} (Z : Env (Strat ζ E O) ζ) (ZT : Strat.Timed ζ E O)
        (ZE : Env.Timed (Strat ζ E O) ζ) {n o q tD : ℕ}, EnvTimeBound Z ZT ZE n o q tD →
          EnvTimeBound (F.pull Z) (F.pullT Z ZT) (F.pullE Z ZE) (n + F.nextC) (o + F.obsC)
              (F.roundsMul * q + F.roundsAdd) (tD + F.distC) ∧
            EnvTimeBound (G.pull Z) (G.pullT Z ZT) (G.pullE Z ZE) (n + G.nextC) (o + G.obsC)
              (G.roundsMul * q + G.roundsAdd) (tD + G.distC) :=
  ⟨F.toEnvPullback.realizes_twoHole G.toEnvPullback hX hX' hY hY' hmid hXr hYr,
    fun _ _ _ _ _ _ _ hT => ⟨F.pull_envTimeBound hT, G.pull_envTimeBound hT⟩⟩

end CostedPullback

/-! ## Instances -/

namespace Hybrid

variable {σ ζ E O EG OG : Type}

/-- The costed reduction of an environment by a hybrid erases to the reduced environment. -/
theorem reduceEnv_timed_erases (π : Hybrid σ E O EG OG) {Z : Env (Strat ζ E O) ζ}
    {ZE : Env.Timed (Strat ζ E O) ζ} (h : ZE.Erases Z) :
    (Hybrid.reduceEnv.timed π Z ZE.dist ZE.distCost).Erases (π.reduceEnv Z) :=
  Hybrid.reduceEnv.erase_timed π Z _ _ fun _ => by rw [h]

/-- A hybrid with a costed hybrid machine `πT` erasing to it, whose steps `pre` and `post` cost
at most `a` and `c`, as a costed pullback: the costed reductions are `Hybrid.Timed.reduce` and
`Hybrid.reduceEnv.timed`, the constants `a + 2`, `c + 2` and `1`, and the activation count is
kept. -/
noncomputable def toCostedPullback (π : Hybrid σ E O EG OG) (πT : Hybrid.Timed σ E O EG OG)
    {a c : ℕ} (hE : πT.Erases π) (hT : πT.TimeBound a c) : CostedPullback EG OG E O where
  toEnvPullback := π.toEnvPullback
  pullT Z ZT := Hybrid.Timed.reduce π Z.input πT ZT
  pullE Z ZE := Hybrid.reduceEnv.timed π Z ZE.dist ZE.distCost
  nextC := a + 2
  obsC := c + 2
  distC := 1
  roundsMul := 1
  roundsAdd := 0
  pullT_erases Z ZT h := by
    change (Hybrid.Timed.reduce π Z.input πT ZT).Erases (π.toEnvPullback.pull Z).input
    rw [toEnvPullback_pull]
    exact Hybrid.Timed.reduce_erases hE h
  pullE_erases Z ZE h := by
    change (Hybrid.reduceEnv.timed π Z ZE.dist ZE.distCost).Erases (π.toEnvPullback.pull Z)
    rw [toEnvPullback_pull]
    exact reduceEnv_timed_erases π h
  pullT_timeBound Z ZT n o h :=
    (Hybrid.Timed.reduce_timeBound π Z.input hT h).mono (by omega) (by omega)
  pullE_dist_le Z ZE tD h w := Hybrid.Timed.reduceEnv_dist_le π Z ZE.dist ZE.distCost w (h w.1)
  pull_rounds_le Z := by
    rw [toEnvPullback_pull]
    simp [Hybrid.reduceEnv, Hybrid.reduce]

end Hybrid

namespace AdvSys

variable {α AI AP Lk Lk' P Oh : Type}

/-- Adversary absorption with a costed adversary (`act`, `out` with their costs, erasing to
those of `A`, of time at most `a` and `c`) as a costed pullback: the costed reductions are the
derived `Strat.absorb.timed` and `Hybrid.reduceEnv.timed` of `A.toHybrid`, the constants
`a + 4`, `c + 2` and `1`, and the activation count is kept. -/
noncomputable def toCostedPullback (A : AdvSys α AI AP Lk Lk')
    (act : α → AI → SPTree.Timed (α × AP)) (actCost : α → AI → ℕ)
    (out : α → Lk → SPTree.Timed (α × Lk')) (outCost : α → Lk → ℕ)
    (hact : ∀ s i, (act s i).erase.compile = A.act s i)
    (hout : ∀ s l, (out s l).erase.compile = A.out s l) {a c : ℕ}
    (ha : ∀ s i, SPTree.Timed.stepTime (actCost s i, act s i) ≤ a)
    (hc : ∀ s l, SPTree.Timed.stepTime (outCost s l, out s l) ≤ c) :
    CostedPullback (Event P AP) (Oh × Lk) (Event P AI) (Oh × Lk') where
  toEnvPullback := A.toEnvPullback
  pullT Z ZT := Strat.absorb.timed Z.input A ZT.next ZT.nextCost act actCost out outCost
    ZT.obs ZT.obsCost
  pullE Z ZE := Hybrid.reduceEnv.timed A.toHybrid Z ZE.dist ZE.distCost
  nextC := a + 4
  obsC := c + 2
  distC := 1
  roundsMul := 1
  roundsAdd := 0
  pullT_erases Z ZT h := by
    obtain ⟨_, _, hZ⟩ := h
    exact Strat.absorb.erase_timed Z.input A _ _ _ _ _ _ _ _ (fun _ => by rw [hZ]) hact hout
      (fun _ _ => by rw [hZ])
  pullE_erases Z ZE h := Hybrid.reduceEnv_timed_erases A.toHybrid h
  pullT_timeBound Z ZT n o h :=
    (Strat.absorb_timeBound Z.input A act actCost out outCost h ha hc).mono (by omega)
      (by omega)
  pullE_dist_le Z ZE tD h w :=
    Hybrid.Timed.reduceEnv_dist_le A.toHybrid Z ZE.dist ZE.distCost w (h w.1)
  pull_rounds_le Z := by
    simp [AdvSys.toEnvPullback, UCConcrete.Env.absorb, Hybrid.reduceEnv, Hybrid.reduce]

end AdvSys

/-! ## The cascade -/

namespace EnvPullback

variable {τ τ' υ υ' E O P : Type}

open Hybrid

/-- The left side of the cascade, `seqLeft Y hY`, as a costed pullback, from a costed hybrid
machine `πT` erasing to the context `seqCtxR Y hY` of `Y`, with steps of time at most `a` and
`c`: the costed reductions are those of the hybrid reduction by `seqCtxR Y hY`, the constants
`a + 2`, `c + 2` and `1`, and the activation count is kept. -/
noncomputable def seqLeft.toCosted (Y : Sys υ O P) (hY : ∀ u o, SPComp.NoFail (Y.step u o))
    (πT : Hybrid.Timed υ E P E O) {a c : ℕ} (hE : πT.Erases (seqCtxR Y hY))
    (hT : πT.TimeBound a c) : CostedPullback E O E P where
  toEnvPullback := seqLeft Y hY
  pullT Z ZT := Hybrid.Timed.reduce (seqCtxR Y hY) Z.input πT ZT
  pullE Z ZE := Hybrid.reduceEnv.timed (seqCtxR Y hY) Z ZE.dist ZE.distCost
  nextC := a + 2
  obsC := c + 2
  distC := 1
  roundsMul := 1
  roundsAdd := 0
  pullT_erases Z ZT h := Hybrid.Timed.reduce_erases hE h
  pullE_erases Z ZE h := Hybrid.reduceEnv_timed_erases _ h
  pullT_timeBound Z ZT n o h :=
    (Hybrid.Timed.reduce_timeBound _ Z.input hT h).mono (by omega) (by omega)
  pullE_dist_le Z ZE tD h w :=
    Hybrid.Timed.reduceEnv_dist_le (seqCtxR Y hY) Z ZE.dist ZE.distCost w (h w.1)
  pull_rounds_le Z := by
    simp [seqLeft, Hybrid.reduceEnv, Hybrid.reduce]

/-- The right side of the cascade, `seqRight X hX`, as a costed pullback, from a costed hybrid
machine `πT` erasing to the context `seqCtxL X hX` of `X`, with steps of time at most `a` and
`c`: the costed reductions are those of the hybrid reduction by `seqCtxL X hX`, the constants
`a + 2`, `c + 2` and `1`, and the activation count is kept. -/
noncomputable def seqRight.toCosted (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    (πT : Hybrid.Timed τ E P O P) {a c : ℕ} (hE : πT.Erases (seqCtxL X hX))
    (hT : πT.TimeBound a c) : CostedPullback O P E P where
  toEnvPullback := seqRight X hX
  pullT Z ZT := Hybrid.Timed.reduce (seqCtxL X hX) Z.input πT ZT
  pullE Z ZE := Hybrid.reduceEnv.timed (seqCtxL X hX) Z ZE.dist ZE.distCost
  nextC := a + 2
  obsC := c + 2
  distC := 1
  roundsMul := 1
  roundsAdd := 0
  pullT_erases Z ZT h := Hybrid.Timed.reduce_erases hE h
  pullE_erases Z ZE h := Hybrid.reduceEnv_timed_erases _ h
  pullT_timeBound Z ZT n o h :=
    (Hybrid.Timed.reduce_timeBound _ Z.input hT h).mono (by omega) (by omega)
  pullE_dist_le Z ZE tD h w :=
    Hybrid.Timed.reduceEnv_dist_le (seqCtxL X hX) Z ZE.dist ZE.distCost w (h w.1)
  pull_rounds_le Z := by
    simp [seqRight, Hybrid.reduceEnv, Hybrid.reduce]

end EnvPullback

open EnvPullback Hybrid in
/-- **Cascade composition theorem with time certificates.** As `realizes_seq`; in addition,
for costed hybrid machines `πR` of the context `seqCtxR Y hY` (steps of time at most `aR`, `cR`)
and `πL` of the context `seqCtxL X' hX'` (at most `aL`, `cL`), the reduced environment of each
component of an environment of time `(n, o, q, tD)` has the costed forms of the hybrid
reduction, with time `(n + aR + 2, o + cR + 2, q, tD + 1)` for `X` and
`(n + aL + 2, o + cL + 2, q, tD + 1)` for `Y`. -/
theorem realizes_seq_timed {τ τ' υ υ' E O P : Type} {X : Sys τ E O} {X' : Sys τ' E O}
    {Y : Sys υ O P} {Y' : Sys υ' O P}
    (hY : ∀ u o, SPComp.NoFail (Y.step u o)) (hX' : ∀ t e, SPComp.NoFail (X'.step t e))
    (πR : Hybrid.Timed υ E P E O) (πL : Hybrid.Timed τ' E P O P) {aR cR aL cL : ℕ}
    (hER : πR.Erases (seqCtxR Y hY)) (hTR : πR.TimeBound aR cR)
    (hEL : πL.Erases (seqCtxL X' hX')) (hTL : πL.TimeBound aL cL)
    {bX : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ O P) ζ → ℝ≥0∞}
    (hXr : Realizes X X' bX) (hYr : Realizes Y Y' bY) :
    Realizes (X.seq Y) (X'.seq Y')
        (fun ζ Z => bX (ζ × υ) ((seqCtxR (E := E) Y hY).reduceEnv Z) +
          bY (ζ × τ') ((seqCtxL (P := P) X' hX').reduceEnv Z)) ∧
      ∀ {ζ : Type} (Z : Env (Strat ζ E P) ζ) (ZT : Strat.Timed ζ E P)
        (ZE : Env.Timed (Strat ζ E P) ζ) {n o q tD : ℕ}, EnvTimeBound Z ZT ZE n o q tD →
          EnvTimeBound ((seqCtxR Y hY).reduceEnv Z)
              (Hybrid.Timed.reduce (seqCtxR Y hY) Z.input πR ZT)
              (Hybrid.reduceEnv.timed (seqCtxR Y hY) Z ZE.dist ZE.distCost) (n + (aR + 2))
              (o + (cR + 2)) (1 * q + 0) (tD + 1) ∧
            EnvTimeBound ((seqCtxL X' hX').reduceEnv Z)
              (Hybrid.Timed.reduce (seqCtxL X' hX') Z.input πL ZT)
              (Hybrid.reduceEnv.timed (seqCtxL X' hX') Z ZE.dist ZE.distCost) (n + (aL + 2))
              (o + (cL + 2)) (1 * q + 0) (tD + 1) :=
  (seqLeft.toCosted Y hY πR hER hTR).realizes_twoHole (seqRight.toCosted X' hX' πL hEL hTL)
    (X := X) (X' := X') (Y := Y) (Y' := Y') True.intro True.intro True.intro True.intro
    (fun _ _ => rfl) hXr hYr

end CatCrypt.Crypto.UCTransparent
