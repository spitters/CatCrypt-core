/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCOpen
public import CatCryptCore.Crypto.UCTransparentAdv
public import CatCryptCore.Crypto.UCCascade

/-!
# Environment pullbacks and the composition theorem

An *environment pullback* `F : EnvPullback E O E' O'` is a map `F.map` from systems with
interface `(E, O)` to systems with interface `(E', O')`, together with a map `F.pull` from
environments of the image interface to environments of the source interface (the environment
reduction, with state `F.Ctx ζ` over an environment with state `ζ`), such that for admissible
systems `X` and `Y`

  `adv (F.map X) (F.map Y) Z = adv X Y (F.pull Z)`.

**Pullback law** (`EnvPullback.realizes_map`): if `X` realizes `Y` with bound `b`, then
`F.map X` realizes `F.map Y` with bound `b ∘ F.pull`. Pullbacks compose (`EnvPullback.comp`,
`(G ∘ F).pull = F.pull ∘ G.pull`) with the identity (`EnvPullback.id`) as unit.

A context with one hole is a pullback: every open system (`Open.toEnvPullback`, through
`Open.reduceEnv` and `Open.adv_withSub`), hence every hybrid (`Hybrid.toEnvPullback`) and every
multi-call hybrid (`MultiHybrid.toEnvPullback`); either side of the cascade
(`EnvPullback.seqLeft`, `EnvPullback.seqRight`). Adversary absorption is a pullback
(`AdvSys.toEnvPullback`, through `Env.absorb` and `adv_attach`), and so is a change of
semantics that maps the advantage of an environment to the advantage of its reduction.

The composition theorem for a context with two holes is two pullbacks and `Realizes.trans`
(`EnvPullback.realizes_twoHole`); the cascade composition theorem `realizes_seq` is its instance
at `seqLeft` and `seqRight`. At bounds that do not depend on the environment the pullback
leaves the bound unchanged and the two-hole law adds the bounds
(`EnvPullback.realizes_map_const`, `EnvPullback.realizes_twoHole_const`).

## Main definitions

* `EnvPullback E O E' O'`: environment pullbacks.
* `EnvPullback.id`, `EnvPullback.comp`: identity and composition.
* `Open.toEnvPullback`, `Hybrid.toEnvPullback`, `MultiHybrid.toEnvPullback`,
  `AdvSys.toEnvPullback`, `EnvPullback.seqLeft`, `EnvPullback.seqRight`: the instances.

## Main results

* `EnvPullback.realizes_map`: the pullback law.
* `EnvPullback.realizes_map_comp`: the law for a composite.
* `EnvPullback.realizes_twoHole`: the composition theorem for two holes.
* `EnvPullback.realizes_map_const`, `EnvPullback.realizes_twoHole_const`: constant bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-- An environment pullback from systems with interface `(E, O)` to systems with interface
`(E', O')`: a map of systems, with state `St τ` over a system with state `τ`, and a map of
environments in the opposite direction, with state `Ctx ζ` over an environment with state `ζ`,
such that the advantage of `Z` between the images of two admissible systems is the advantage of
`pull Z` between the systems. -/
structure EnvPullback (E O E' O' : Type) : Type 1 where
  /-- The state of the image of a system with state `τ`. -/
  St : Type → Type
  /-- The map of systems. -/
  map : {τ : Type} → Sys τ E O → Sys (St τ) E' O'
  /-- The state of the pulled-back environment over an environment with state `ζ`. -/
  Ctx : Type → Type
  /-- The map of environments (the environment reduction). -/
  pull : {ζ : Type} → Env (Strat ζ E' O') ζ → Env (Strat (Ctx ζ) E O) (Ctx ζ)
  /-- The admissible systems. -/
  Adm : {τ : Type} → Sys τ E O → Prop
  /-- The advantage of `Z` between the images is the advantage of `pull Z`. -/
  adv_map : ∀ {τ υ ζ : Type} {X : Sys τ E O} {Y : Sys υ E O}, Adm X → Adm Y →
    ∀ Z : Env (Strat ζ E' O') ζ, adv (map X) (map Y) Z = adv X Y (pull Z)

namespace EnvPullback

variable {τ τ' υ υ' E O E₁ O₁ E₂ O₂ E₃ O₃ : Type}

/-- **Pullback law.** If `X` realizes `Y` with bound `b`, both admissible, then `F.map X`
realizes `F.map Y` with bound `b` at the pulled-back environment. -/
theorem realizes_map (F : EnvPullback E O E₁ O₁) {X : Sys τ E O} {Y : Sys υ E O}
    (hX : F.Adm X) (hY : F.Adm Y) {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : Realizes X Y b) :
    Realizes (F.map X) (F.map Y) (fun ζ Z => b (F.Ctx ζ) (F.pull Z)) := fun _ Z =>
  (F.adv_map hX hY Z).trans_le (h _ _)

/-- The pullback law at a bound that does not depend on the environment. -/
theorem realizes_map_const (F : EnvPullback E O E₁ O₁) {X : Sys τ E O} {Y : Sys υ E O}
    (hX : F.Adm X) (hY : F.Adm Y) {ε : ℝ≥0∞} (h : Realizes X Y (fun _ _ => ε)) :
    Realizes (F.map X) (F.map Y) (fun _ _ => ε) :=
  F.realizes_map hX hY h

/-- The identity pullback: systems and environments unchanged. -/
def id (E O : Type) : EnvPullback E O E O where
  St τ := τ
  map X := X
  Ctx ζ := ζ
  pull Z := Z
  Adm _ := True
  adv_map _ _ _ := rfl

/-- **Composition of pullbacks**: `G` after `F` on systems, `F.pull` after `G.pull` on
environments. -/
def comp (F : EnvPullback E O E₁ O₁) (G : EnvPullback E₁ O₁ E₂ O₂) :
    EnvPullback E O E₂ O₂ where
  St τ := G.St (F.St τ)
  map X := G.map (F.map X)
  Ctx ζ := F.Ctx (G.Ctx ζ)
  pull Z := F.pull (G.pull Z)
  Adm X := F.Adm X ∧ G.Adm (F.map X)
  adv_map hX hY Z := by rw [G.adv_map hX.2 hY.2, F.adv_map hX.1 hY.1]

/-- The identity is a left unit. -/
theorem id_comp (F : EnvPullback E O E₁ O₁) : (EnvPullback.id E O).comp F = F := by
  cases F
  simp only [comp, EnvPullback.id, true_and]

/-- The identity is a right unit. -/
theorem comp_id (F : EnvPullback E O E₁ O₁) : F.comp (EnvPullback.id E₁ O₁) = F := by
  cases F
  simp only [comp, EnvPullback.id, and_true]

/-- Associativity of composition. -/
theorem comp_assoc (F : EnvPullback E O E₁ O₁) (G : EnvPullback E₁ O₁ E₂ O₂)
    (H : EnvPullback E₂ O₂ E₃ O₃) : (F.comp G).comp H = F.comp (G.comp H) := by
  simp only [comp, and_assoc]

/-- **The law for a composite**: the realization is pulled back through `G.pull` and then
through `F.pull`. -/
theorem realizes_map_comp (F : EnvPullback E O E₁ O₁) (G : EnvPullback E₁ O₁ E₂ O₂)
    {X : Sys τ E O} {Y : Sys υ E O} (hX : F.Adm X) (hY : F.Adm Y)
    (hX' : G.Adm (F.map X)) (hY' : G.Adm (F.map Y))
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes X Y b) :
    Realizes (G.map (F.map X)) (G.map (F.map Y))
      (fun ζ Z => b (F.Ctx (G.Ctx ζ)) (F.pull (G.pull Z))) :=
  (F.comp G).realizes_map ⟨hX, hX'⟩ ⟨hY, hY'⟩ h

/-- **Composition theorem for two holes.** Let `F` fill the first hole and `G` the second, and
let `F.map X'` and `G.map Y` have the same views (the context with `X'` in the first hole and `Y`
in the second). If `X` realizes `X'` with bound `bX` and `Y` realizes `Y'` with bound `bY`, then
`F.map X` realizes `G.map Y'` with the sum of `bX` at `F.pull` and `bY` at `G.pull`. -/
theorem realizes_twoHole (F : EnvPullback E₁ O₁ E O) (G : EnvPullback E₂ O₂ E O)
    {X : Sys τ E₁ O₁} {X' : Sys τ' E₁ O₁} {Y : Sys υ E₂ O₂} {Y' : Sys υ' E₂ O₂}
    (hX : F.Adm X) (hX' : F.Adm X') (hY : G.Adm Y) (hY' : G.Adm Y')
    (hmid : ∀ (ζ : Type) (Z : Strat ζ E O), view (F.map X') Z = view (G.map Y) Z)
    {bX : (ζ : Type) → Env (Strat ζ E₁ O₁) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ E₂ O₂) ζ → ℝ≥0∞}
    (hXr : Realizes X X' bX) (hYr : Realizes Y Y' bY) :
    Realizes (F.map X) (G.map Y')
      (fun ζ Z => bX (F.Ctx ζ) (F.pull Z) + bY (G.Ctx ζ) (G.pull Z)) := by
  refine Realizes.trans (F.realizes_map hX hX' hXr) fun ζ => ?_
  rw [show (view (F.map X') : Strat ζ E O → SPComp ζ) = view (G.map Y) from funext (hmid ζ)]
  exact G.realizes_map hY hY' hYr ζ

/-- The composition theorem for two holes at bounds that do not depend on the environment: the
bounds add. -/
theorem realizes_twoHole_const (F : EnvPullback E₁ O₁ E O) (G : EnvPullback E₂ O₂ E O)
    {X : Sys τ E₁ O₁} {X' : Sys τ' E₁ O₁} {Y : Sys υ E₂ O₂} {Y' : Sys υ' E₂ O₂}
    (hX : F.Adm X) (hX' : F.Adm X') (hY : G.Adm Y) (hY' : G.Adm Y')
    (hmid : ∀ (ζ : Type) (Z : Strat ζ E O), view (F.map X') Z = view (G.map Y) Z)
    {ε δ : ℝ≥0∞} (hXr : Realizes X X' (fun _ _ => ε)) (hYr : Realizes Y Y' (fun _ _ => δ)) :
    Realizes (F.map X) (G.map Y') (fun _ _ => ε + δ) :=
  F.realizes_twoHole G hX hX' hY hY' hmid hXr hYr

end EnvPullback

/-! ## Contexts: open systems and hybrids -/

namespace Open

variable {E O EM OM EG OG : Type}

/-- An open system as an environment pullback: `withSub` on systems, `reduceEnv` on
environments. -/
noncomputable def toEnvPullback (P : Open E O EG OG) : EnvPullback EG OG E O where
  St := P.St
  map := P.withSub
  Ctx := P.Ctx
  pull := P.reduceEnv
  Adm := P.Adm
  adv_map hX hY Z := P.adv_withSub hX hY Z

/-- The pullback of a composite open system is the composite of the pullbacks. -/
theorem toEnvPullback_comp (P₁ : Open E O EM OM) (P₂ : Open EM OM EG OG) :
    (P₁.comp P₂).toEnvPullback = P₂.toEnvPullback.comp P₁.toEnvPullback := by
  simp only [toEnvPullback, EnvPullback.comp, EnvPullback.mk.injEq]
  exact ⟨rfl, HEq.rfl, rfl,
    heq_of_eq (funext fun _ => funext fun Z => reduceEnv_comp P₁ P₂ Z), rfl⟩

/-- The pullback of the identity open system is the identity pullback. -/
theorem toEnvPullback_id : (Open.id E O).toEnvPullback = EnvPullback.id E O := by
  simp only [toEnvPullback, EnvPullback.id, EnvPullback.mk.injEq]
  exact ⟨rfl, HEq.rfl, rfl, heq_of_eq (funext fun _ => funext fun Z => reduceEnv_id Z), rfl⟩

end Open

namespace Hybrid

variable {σ E O EG OG : Type}

/-- A hybrid as an environment pullback, through `Open.ofHybrid`. -/
noncomputable def toEnvPullback (π : Hybrid σ E O EG OG) : EnvPullback EG OG E O :=
  (Open.ofHybrid π).toEnvPullback

/-- The pulled-back environment of a hybrid is `π.reduceEnv`. -/
theorem toEnvPullback_pull {ζ : Type} (π : Hybrid σ E O EG OG) (Z : Env (Strat ζ E O) ζ) :
    π.toEnvPullback.pull Z = π.reduceEnv Z :=
  Open.reduceEnv_ofHybrid π Z

end Hybrid

namespace MultiHybrid

variable {σ E O EG OG : Type}

/-- A multi-call hybrid as an environment pullback, through `Open.ofMultiHybrid`; the admissible
subroutines are those idle at `idle`. -/
noncomputable def toEnvPullback (π : MultiHybrid σ E O EG OG) (idle : EG) :
    EnvPullback EG OG E O :=
  (Open.ofMultiHybrid π idle).toEnvPullback

/-- The pulled-back environment of a multi-call hybrid is `π.reduceEnv idle`. -/
theorem toEnvPullback_pull {ζ : Type} (π : MultiHybrid σ E O EG OG) (idle : EG)
    (Z : Env (Strat ζ E O) ζ) : (π.toEnvPullback idle).pull Z = π.reduceEnv idle Z :=
  Open.reduceEnv_ofMultiHybrid π idle Z

end MultiHybrid

/-! ## Adversary absorption -/

namespace AdvSys

variable {α AI AP Lk Lk' P Oh : Type}

/-- Attaching the adversary system `A` is an environment pullback: `Sys.attach` on systems,
`Env.absorb` on environments. -/
noncomputable def toEnvPullback (A : AdvSys α AI AP Lk Lk') :
    EnvPullback (Event P AP) (Oh × Lk) (Event P AI) (Oh × Lk') where
  St τ := α × τ
  map R := R.attach A
  Ctx ζ := ζ × α
  pull Z := Z.absorb A
  Adm _ := True
  adv_map _ _ Z := adv_attach _ _ A Z

end AdvSys

/-! ## The cascade -/

namespace EnvPullback

variable {τ τ' υ υ' E O P : Type}

open Hybrid

/-- The cascade with a lossless right component `Y` as a pullback in the left component: the
pulled-back environment runs `Y` after each answer. -/
noncomputable def seqLeft (Y : Sys υ O P) (hY : ∀ u o, SPComp.NoFail (Y.step u o)) :
    EnvPullback E O E P where
  St τ := τ × υ
  map X := X.seq Y
  Ctx ζ := ζ × υ
  pull Z := (seqCtxR Y hY).reduceEnv Z
  Adm _ := True
  adv_map {_ _ ζ} X X' _ _ Z := by
    have hv : ∀ {τ₀ : Type} (X₀ : Sys τ₀ E O),
        (view (X₀.seq Y) : Strat ζ E P → SPComp ζ) = view ((seqCtxR Y hY).withSub X₀) :=
      fun X₀ => funext (view_eq_of_stepMap _ _ Prod.swap rfl (seqCtxR_withSub_step Y hY X₀))
    unfold adv
    rw [hv X, hv X']
    exact Hybrid.adv_withSub (seqCtxR Y hY) X X' Z

/-- The cascade with a lossless left component `X` as a pullback in the right component: the
pulled-back environment runs `X` before each event. -/
noncomputable def seqRight (X : Sys τ E O) (hX : ∀ t e, SPComp.NoFail (X.step t e)) :
    EnvPullback O P E P where
  St υ := τ × υ
  map Y := X.seq Y
  Ctx ζ := ζ × τ
  pull Z := (seqCtxL X hX).reduceEnv Z
  Adm _ := True
  adv_map {_ _ _} Y Y' _ _ Z := by
    rw [← seqCtxL_withSub X hX Y, ← seqCtxL_withSub X hX Y']
    exact Hybrid.adv_withSub (seqCtxL X hX) Y Y' Z

/-- The cascade composition theorem `realizes_seq` is the two-hole law at `seqLeft` and
`seqRight`. -/
example {X : Sys τ E O} {X' : Sys τ' E O} {Y : Sys υ O P} {Y' : Sys υ' O P}
    (hY : ∀ u o, SPComp.NoFail (Y.step u o)) (hX' : ∀ t e, SPComp.NoFail (X'.step t e))
    {bX : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ O P) ζ → ℝ≥0∞}
    (hXr : Realizes X X' bX) (hYr : Realizes Y Y' bY) :
    Realizes (X.seq Y) (X'.seq Y')
      (fun ζ Z => bX (ζ × υ) ((seqCtxR (E := E) Y hY).reduceEnv Z) +
        bY (ζ × τ') ((seqCtxL (P := P) X' hX').reduceEnv Z)) :=
  (seqLeft Y hY).realizes_twoHole (seqRight X' hX') trivial trivial trivial trivial
    (fun _ _ => rfl) hXr hYr

end EnvPullback

/-! ## The existing context laws as instances of the pullback law -/

section Instances

variable {τ υ υ' σ E O EG OG α AI AP Lk Lk' P Oh : Type}

/-- `Open.realizes_withSub` is the pullback law at `Open.toEnvPullback`. -/
example (Q : Open E O EG OG) {X : Sys τ EG OG} {Y : Sys υ EG OG} (hX : Q.Adm X)
    (hY : Q.Adm Y) {b : (ζ : Type) → Env (Strat ζ EG OG) ζ → ℝ≥0∞} (h : Realizes X Y b) :
    Realizes (Q.withSub X) (Q.withSub Y) (fun ζ Z => b (Q.Ctx ζ) (Q.reduceEnv Z)) :=
  Q.toEnvPullback.realizes_map hX hY h

/-- `Hybrid.realizes_compose` is the pullback law at `Hybrid.toEnvPullback`, followed by
`Realizes.trans`. -/
example (π : Hybrid σ E O EG OG) (X : Sys τ EG OG) (Y : Sys υ EG OG) (I : Sys υ' E O)
    (b₁ : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞)
    (b₂ : (ζ : Type) → Env (Strat ζ EG OG) ζ → ℝ≥0∞)
    (h₁ : Realizes (π.withSub Y) I b₁) (h₂ : Realizes X Y b₂) :
    Realizes (π.withSub X) I (fun ζ Z => b₂ (ζ × σ) (π.reduceEnv Z) + b₁ ζ Z) := by
  have h := Realizes.trans (π.toEnvPullback.realizes_map trivial trivial h₂) h₁
  simp only [Hybrid.toEnvPullback_pull] at h
  exact h

/-- `MultiHybrid.realizes_compose` is the pullback law at `MultiHybrid.toEnvPullback`, followed
by `Realizes.trans`. -/
example (π : MultiHybrid σ E O EG OG) (idle : EG) (oX oY : OG)
    (X : Sys τ EG OG) (Y : Sys υ EG OG) (I : Sys υ' E O)
    (hX : MultiHybrid.IdleAt X idle oX) (hY : MultiHybrid.IdleAt Y idle oY)
    (b₁ : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞)
    (b₂ : (ζ : Type) → Env (Strat ζ EG OG) ζ → ℝ≥0∞)
    (h₁ : Realizes (π.withSub Y) I b₁) (h₂ : Realizes X Y b₂) :
    Realizes (π.withSub X) I
      (fun ζ Z => b₂ (MultiHybrid.RState σ ζ EG O) (π.reduceEnv idle Z) + b₁ ζ Z) := by
  have h := Realizes.trans
    ((π.toEnvPullback idle).realizes_map ⟨oX, hX⟩ ⟨oY, hY⟩ h₂) h₁
  simp only [MultiHybrid.toEnvPullback_pull] at h
  exact h

/-- `Realizes.attach` is the pullback law at `AdvSys.toEnvPullback`. -/
example {R : Sys τ (Event P AP) (Oh × Lk)} {I : Sys υ (Event P AP) (Oh × Lk)}
    {b : (ζ : Type) → Env (Strat ζ (Event P AP) (Oh × Lk)) ζ → ℝ≥0∞} (h : Realizes R I b)
    (A : AdvSys α AI AP Lk Lk') :
    Realizes (R.attach A) (I.attach A) (fun ζ Z => b (ζ × α) (Z.absorb A)) :=
  A.toEnvPullback.realizes_map trivial trivial h

end Instances

end CatCrypt.Crypto.UCTransparent
