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

A *costed pullback* `F : CostedPullback E O E' O'` is an environment pullback
(`EnvPullback`, `UCPullback.lean`) together with a costed form `F.pullT` of its environment
reduction on costed strategies (`Strat.Timed`, `UCPullbackTimed.lean`) and two constants
`F.nextC`, `F.obsC`, such that

* (erasure) over a costed strategy that erases to the strategy of `Z`, the costed reduction
  erases to the strategy of `F.pull Z`;
* (time) if each `next` activation of the costed strategy costs at most `n` and each `obs`
  activation at most `o`, then those of the costed reduction cost at most `n + F.nextC` and
  `o + F.obsC`: `T(Z·C) ≤ T(Z) + T(C)`.

Costed pullbacks compose with the constants added (`CostedPullback.comp`). The costed pullback
law (`CostedPullback.realizes_map`) is the pullback law with the time certificate of the
reduced environment; its graded form (`CostedPullback.realizesTime_map`) maps a realization
against environments of activation time `(n + F.nextC, o + F.obsC)` to a realization of the
images against environments of activation time `(n, o)`. The composition theorem for two holes
(`CostedPullback.realizes_twoHole`) states the time of both reduced environments.

Instances: the hybrid context (`Hybrid.toCostedPullback`, constants from
`Hybrid.Timed.reduce_timeBound`) and adversary absorption (`AdvSys.toCostedPullback`, constants
from `Strat.absorb_timeBound`). The costed reductions are the derived `Hybrid.reduce.timed` and
`Strat.absorb.timed`.

Search words: costed pullback, time certificate, environment reduction, composition theorem,
activation time, time-bounded environment, adversary absorption.

## Main definitions

* `CostedPullback E O E' O'`: costed environment pullbacks.
* `CostedPullback.comp`: composition, constants added.
* `RealizesTime X Y n o b`: realization against environments with a costed strategy of
  activation time `(n, o)`.
* `Hybrid.toCostedPullback`, `AdvSys.toCostedPullback`: the instances.

## Main results

* `CostedPullback.realizes_map`: the costed pullback law.
* `CostedPullback.realizesTime_map`: the time-graded pullback law.
* `CostedPullback.realizes_twoHole`: the composition theorem for two holes with the time of each
  reduced environment.
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

/-- A costed environment pullback: an environment pullback with a costed form `pullT` of its
environment reduction on costed strategies, which erases to the strategy of the reduced
environment and adds at most `nextC` to the time of a `next` activation and `obsC` to the time
of an `obs` activation. -/
structure CostedPullback (E O E' O' : Type) extends EnvPullback E O E' O' where
  /-- The costed environment reduction, on the costed strategy of an environment. -/
  pullT : {ζ : Type} → Env (Strat ζ E' O') ζ → Strat.Timed ζ E' O' → Strat.Timed (Ctx ζ) E O
  /-- The time added to a `next` activation. -/
  nextC : ℕ
  /-- The time added to an `obs` activation. -/
  obsC : ℕ
  /-- Erasure of the costed reduction. -/
  pullT_erases : ∀ {ζ : Type} (Z : Env (Strat ζ E' O') ζ) (ZT : Strat.Timed ζ E' O'),
    ZT.Erases Z.input → (pullT Z ZT).Erases (pull Z).input
  /-- Time of the costed reduction. -/
  pullT_timeBound : ∀ {ζ : Type} (Z : Env (Strat ζ E' O') ζ) (ZT : Strat.Timed ζ E' O')
    {n o : ℕ}, ZT.TimeBound n o → (pullT Z ZT).TimeBound (n + nextC) (o + obsC)

/-- `X` realizes `Y` with bound `b` against every environment whose strategy has a costed form
with activation time at most `n` for `next` and `o` for `obs`. -/
def RealizesTime {τ υ E O : Type} (X : Sys τ E O) (Y : Sys υ E O) (n o : ℕ)
    (b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞) : Prop :=
  ∀ (ζ : Type) (Z : Env (Strat ζ E O) ζ) (ZT : Strat.Timed ζ E O),
    ZT.Erases Z.input → ZT.TimeBound n o → adv X Y Z ≤ b ζ Z

/-- A realization is a realization against environments of every activation time. -/
theorem Realizes.realizesTime {τ υ E O : Type} {X : Sys τ E O} {Y : Sys υ E O}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes X Y b) (n o : ℕ) :
    RealizesTime X Y n o b :=
  fun ζ Z _ _ _ => h ζ Z

namespace CostedPullback

variable {τ τ' υ υ' E O E₁ O₁ E₂ O₂ : Type}

/-- **Composition of costed pullbacks**: the costed reduction of `G` followed by that of `F`;
the constants add. -/
def comp (F : CostedPullback E O E₁ O₁) (G : CostedPullback E₁ O₁ E₂ O₂) :
    CostedPullback E O E₂ O₂ where
  toEnvPullback := F.toEnvPullback.comp G.toEnvPullback
  pullT Z ZT := F.pullT (G.pull Z) (G.pullT Z ZT)
  nextC := G.nextC + F.nextC
  obsC := G.obsC + F.obsC
  pullT_erases Z ZT h := F.pullT_erases _ _ (G.pullT_erases Z ZT h)
  pullT_timeBound Z ZT n o h := by
    have := F.pullT_timeBound (G.pull Z) _ (G.pullT_timeBound Z ZT h)
    rw [Nat.add_assoc, Nat.add_assoc] at this
    exact this

/-- **Costed pullback law.** If `X` realizes `Y` with bound `b`, both admissible, then `F.map X`
realizes `F.map Y` with bound `b` at the pulled-back environment, and the pulled-back
environment carries its time certificate: over a costed strategy of `Z` with activation time
`(n, o)`, the costed reduction erases to the strategy of `F.pull Z` and has activation time
`(n + F.nextC, o + F.obsC)`. -/
theorem realizes_map (F : CostedPullback E O E₁ O₁) {X : Sys τ E O} {Y : Sys υ E O}
    (hX : F.Adm X) (hY : F.Adm Y) {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : Realizes X Y b) :
    Realizes (F.map X) (F.map Y) (fun ζ Z => b (F.Ctx ζ) (F.pull Z)) ∧
      ∀ {ζ : Type} (Z : Env (Strat ζ E₁ O₁) ζ) (ZT : Strat.Timed ζ E₁ O₁) {n o : ℕ},
        ZT.Erases Z.input → ZT.TimeBound n o →
          (F.pullT Z ZT).Erases (F.pull Z).input ∧
            (F.pullT Z ZT).TimeBound (n + F.nextC) (o + F.obsC) :=
  ⟨F.toEnvPullback.realizes_map hX hY h,
    fun Z ZT _ _ hE hT => ⟨F.pullT_erases Z ZT hE, F.pullT_timeBound Z ZT hT⟩⟩

/-- **Time-graded pullback law.** If `X` realizes `Y` with bound `b` against environments of
activation time `(n + F.nextC, o + F.obsC)`, then `F.map X` realizes `F.map Y` with bound `b`
at the pulled-back environment against environments of activation time `(n, o)`. -/
theorem realizesTime_map (F : CostedPullback E O E₁ O₁) {X : Sys τ E O} {Y : Sys υ E O}
    (hX : F.Adm X) (hY : F.Adm Y) {n o : ℕ} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : RealizesTime X Y (n + F.nextC) (o + F.obsC) b) :
    RealizesTime (F.map X) (F.map Y) n o (fun ζ Z => b (F.Ctx ζ) (F.pull Z)) := by
  intro ζ Z ZT hE hT
  rw [F.adv_map hX hY Z]
  exact h _ _ _ (F.pullT_erases Z ZT hE) (F.pullT_timeBound Z ZT hT)

/-- The costed law for a composite: the realization is pulled back through `G` and then `F`,
and the composite reduction has activation time `(n + G.nextC + F.nextC, o + G.obsC + F.obsC)`
over a costed strategy of activation time `(n, o)`. -/
theorem realizes_map_comp (F : CostedPullback E O E₁ O₁) (G : CostedPullback E₁ O₁ E₂ O₂)
    {X : Sys τ E O} {Y : Sys υ E O} (hX : F.Adm X) (hY : F.Adm Y)
    (hX' : G.Adm (F.map X)) (hY' : G.Adm (F.map Y))
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes X Y b) :
    Realizes (G.map (F.map X)) (G.map (F.map Y))
        (fun ζ Z => b (F.Ctx (G.Ctx ζ)) (F.pull (G.pull Z))) ∧
      ∀ {ζ : Type} (Z : Env (Strat ζ E₂ O₂) ζ) (ZT : Strat.Timed ζ E₂ O₂) {n o : ℕ},
        ZT.Erases Z.input → ZT.TimeBound n o →
          (F.pullT (G.pull Z) (G.pullT Z ZT)).Erases (F.pull (G.pull Z)).input ∧
            (F.pullT (G.pull Z) (G.pullT Z ZT)).TimeBound (n + (G.nextC + F.nextC))
              (o + (G.obsC + F.obsC)) :=
  (F.comp G).realizes_map ⟨hX, hX'⟩ ⟨hY, hY'⟩ h

/-- **Composition theorem for two holes with time certificates.** As
`EnvPullback.realizes_twoHole`; in addition, over a costed strategy of `Z` with activation time
`(n, o)`, the reduced environment of each hole has a costed form erasing to it, of activation
time `(n + F.nextC, o + F.obsC)` for the first hole and `(n + G.nextC, o + G.obsC)` for the
second. -/
theorem realizes_twoHole (F : CostedPullback E₁ O₁ E O) (G : CostedPullback E₂ O₂ E O)
    {X : Sys τ E₁ O₁} {X' : Sys τ' E₁ O₁} {Y : Sys υ E₂ O₂} {Y' : Sys υ' E₂ O₂}
    (hX : F.Adm X) (hX' : F.Adm X') (hY : G.Adm Y) (hY' : G.Adm Y')
    (hmid : ∀ (ζ : Type) (Z : Strat ζ E O), view (F.map X') Z = view (G.map Y) Z)
    {bX : (ζ : Type) → Env (Strat ζ E₁ O₁) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ E₂ O₂) ζ → ℝ≥0∞}
    (hXr : Realizes X X' bX) (hYr : Realizes Y Y' bY) :
    Realizes (F.map X) (G.map Y')
        (fun ζ Z => bX (F.Ctx ζ) (F.pull Z) + bY (G.Ctx ζ) (G.pull Z)) ∧
      ∀ {ζ : Type} (Z : Env (Strat ζ E O) ζ) (ZT : Strat.Timed ζ E O) {n o : ℕ},
        ZT.Erases Z.input → ZT.TimeBound n o →
          ((F.pullT Z ZT).Erases (F.pull Z).input ∧
            (F.pullT Z ZT).TimeBound (n + F.nextC) (o + F.obsC)) ∧
          ((G.pullT Z ZT).Erases (G.pull Z).input ∧
            (G.pullT Z ZT).TimeBound (n + G.nextC) (o + G.obsC)) :=
  ⟨F.toEnvPullback.realizes_twoHole G.toEnvPullback hX hX' hY hY' hmid hXr hYr,
    fun Z ZT _ _ hE hT => ⟨⟨F.pullT_erases Z ZT hE, F.pullT_timeBound Z ZT hT⟩,
      ⟨G.pullT_erases Z ZT hE, G.pullT_timeBound Z ZT hT⟩⟩⟩

end CostedPullback

/-! ## Instances -/

namespace Hybrid

variable {σ E O EG OG : Type}

/-- A hybrid with a costed hybrid machine `πT` erasing to it, whose steps `pre` and `post` cost
at most `a` and `c`, as a costed pullback: the costed reduction is `Hybrid.Timed.reduce`, the
constants `a + 2` and `c + 2`. -/
noncomputable def toCostedPullback (π : Hybrid σ E O EG OG) (πT : Hybrid.Timed σ E O EG OG)
    {a c : ℕ} (hE : πT.Erases π) (hT : πT.TimeBound a c) : CostedPullback EG OG E O where
  toEnvPullback := π.toEnvPullback
  pullT Z ZT := Hybrid.Timed.reduce π Z.input πT ZT
  nextC := a + 2
  obsC := c + 2
  pullT_erases Z ZT h := by
    change (Hybrid.Timed.reduce π Z.input πT ZT).Erases (π.toEnvPullback.pull Z).input
    rw [toEnvPullback_pull]
    exact Hybrid.Timed.reduce_erases hE h
  pullT_timeBound Z ZT n o h :=
    (Hybrid.Timed.reduce_timeBound π Z.input hT h).mono (by omega) (by omega)

end Hybrid

namespace AdvSys

variable {α AI AP Lk Lk' P Oh : Type}

/-- Adversary absorption with a costed adversary (`act`, `out` with their costs, erasing to
those of `A`, of time at most `a` and `c`) as a costed pullback: the costed reduction is the
derived `Strat.absorb.timed`, the constants `a + 4` and `c + 2`. -/
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
  nextC := a + 4
  obsC := c + 2
  pullT_erases Z ZT h := by
    obtain ⟨_, _, hZ⟩ := h
    exact Strat.absorb.erase_timed Z.input A _ _ _ _ _ _ _ _ (fun _ => by rw [hZ]) hact hout
      (fun _ _ => by rw [hZ])
  pullT_timeBound Z ZT n o h :=
    (Strat.absorb_timeBound Z.input A act actCost out outCost h ha hc).mono (by omega)
      (by omega)

end AdvSys

end CatCrypt.Crypto.UCTransparent
