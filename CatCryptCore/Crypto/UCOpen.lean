/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparentMulti

/-!
# Open systems with an environment reduction

An open system from the subroutine interface `(EG, OG)` to the outer interface `(E, O)`
(`Open E O EG OG`) is a transformer of subroutine systems together with the reduction of outer
environments to subroutine environments that explains it: running the transformed system
`withSub X` against `Z` is running `X` against the reduced environment `reduce Z`, followed by
the post-processing kernel `proj` on the final state of the reduced environment. The equation
holds for the admissible subroutines `Adm X`.

Multi-call hybrids (`Open.ofMultiHybrid`, admissible: idle at the idle event) and hybrids
(`Open.ofHybrid`, every subroutine admissible) are open systems, and so is a closed system over
the unit interface (`Open.closed`, its reduced environment runs the whole closed system in the
post-processing kernel). Open systems compose (`Open.comp`) with the identity (`Open.id`) as
unit, associatively.

## Main definitions

* `Open E O EG OG`: open systems with an environment reduction.
* `Open.reduceEnv`: the reduced `UCConcrete.Env`.
* `Open.ofMultiHybrid`, `Open.ofHybrid`, `Open.closed`, `Open.id`, `Open.comp`.

## Main results

* `Open.adv_withSub`: the advantage between `P.withSub X` and `P.withSub Y` is the advantage
  between `X` and `Y` at the reduced environment.
* `Open.realizes_withSub`, `Open.realizes_compose`: realization under an open system.
* `Open.comp_assoc`, `Open.id_comp`, `Open.comp_id`: the category laws.
* `MultiHybrid.idleAt_withSub`: a multi-call hybrid whose `start` answers the event `g` with
  the output `o` without a call is idle at `g` over every subroutine.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-- An open system from the subroutine interface `(EG, OG)` to the outer interface `(E, O)`: a
transformer of subroutine systems, with state `St τ` over a subroutine with state `τ`, and an
environment reduction with state `Ctx ζ` over an outer environment with state `ζ`, such that
the view of `Z` against `withSub X` is the view of `reduce Z` against `X` followed by `proj`,
for every admissible subroutine `X`. -/
structure Open (E O EG OG : Type) : Type 1 where
  /-- The state of the open system over a subroutine with state `τ`. -/
  St : Type → Type
  /-- The open system running with the subroutine system `X`. -/
  withSub : {τ : Type} → Sys τ EG OG → Sys (St τ) E O
  /-- The state of the reduced environment over an outer environment with state `ζ`. -/
  Ctx : Type → Type
  /-- The reduced environment. -/
  reduce : {ζ : Type} → Strat ζ E O → Strat (Ctx ζ) EG OG
  /-- The post-processing of the final state of the reduced environment. -/
  proj : {ζ : Type} → Ctx ζ → SPComp ζ
  /-- The admissible subroutine systems. -/
  Adm : {τ : Type} → Sys τ EG OG → Prop
  /-- The view of `Z` against `withSub X` is the view of `reduce Z` against `X`, followed by
  `proj`. -/
  view_withSub : ∀ {τ ζ : Type} (X : Sys τ EG OG) (Z : Strat ζ E O), Adm X →
    view (withSub X) Z = SPComp.bind (view X (reduce Z)) proj

namespace Open

variable {τ υ υ' ζ E O EM OM EG OG : Type}

/-- The reduced `UCConcrete.Env`: reduced strategy, same heap, and the distinguisher run after
the post-processing `proj`. -/
noncomputable def reduceEnv (P : Open E O EG OG) (Z : Env (Strat ζ E O) ζ) :
    Env (Strat (P.Ctx ζ) EG OG) (P.Ctx ζ) :=
  ⟨P.reduce Z.input, Z.heap, fun c => SPComp.bind (P.proj c) Z.dist⟩

/-- **Environment reduction**: the advantage of `Z` between `P.withSub X` and `P.withSub Y` is
the advantage of the reduced environment between `X` and `Y`, for admissible `X` and `Y`. -/
theorem adv_withSub (P : Open E O EG OG) {X : Sys τ EG OG} {Y : Sys υ EG OG}
    (hX : P.Adm X) (hY : P.Adm Y) (Z : Env (Strat ζ E O) ζ) :
    adv (P.withSub X) (P.withSub Y) Z = adv X Y (P.reduceEnv Z) := by
  rw [adv_eq, adv_eq, P.view_withSub X _ hX, P.view_withSub Y _ hY]
  simp only [reduceEnv, SPComp.bind_assoc]

/-- Realization under an open system: if `X` realizes `Y` with bound `b`, both admissible, then
`P.withSub X` realizes `P.withSub Y` with bound `b` at the reduced environment. -/
theorem realizes_withSub (P : Open E O EG OG) {X : Sys τ EG OG} {Y : Sys υ EG OG}
    (hX : P.Adm X) (hY : P.Adm Y) {b : (ζ : Type) → Env (Strat ζ EG OG) ζ → ℝ≥0∞}
    (h : Realizes X Y b) :
    Realizes (P.withSub X) (P.withSub Y) (fun ζ Z => b (P.Ctx ζ) (P.reduceEnv Z)) := by
  intro ζ Z
  have h' := P.adv_withSub hX hY Z
  unfold adv at h'
  rw [h']
  exact h _ _

/-- **Composition under an open system** (composition plumbing). If `P.withSub Y` realizes `I`
with bound `b₁` and `X` realizes `Y` with bound `b₂`, both admissible, then `P.withSub X`
realizes `I` with bound `b₂` at the reduced environment plus `b₁`. -/
theorem realizes_compose (P : Open E O EG OG) {X : Sys τ EG OG} {Y : Sys υ EG OG}
    {I : Sys υ' E O} (hX : P.Adm X) (hY : P.Adm Y)
    {b₁ : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    {b₂ : (ζ : Type) → Env (Strat ζ EG OG) ζ → ℝ≥0∞}
    (h₁ : Realizes (P.withSub Y) I b₁) (h₂ : Realizes X Y b₂) :
    Realizes (P.withSub X) I (fun ζ Z => b₂ (P.Ctx ζ) (P.reduceEnv Z) + b₁ ζ Z) :=
  Realizes.trans (P.realizes_withSub hX hY h₂) h₁

/-! ## Generators -/

/-- A multi-call hybrid as an open system: the reduced environment is `π.reduce idle`, and the
admissible subroutines are those idle at `idle`. -/
noncomputable def ofMultiHybrid {σ : Type} (π : MultiHybrid σ E O EG OG) (idle : EG) :
    Open E O EG OG where
  St τ := σ × τ
  withSub X := π.withSub X
  Ctx ζ := MultiHybrid.RState σ ζ EG O
  reduce Z := π.reduce idle Z
  proj c := SPComp.pure c.1
  Adm X := ∃ o, MultiHybrid.IdleAt X idle o
  view_withSub X Z := fun ⟨o, h⟩ => π.view_withSub idle o X h Z

/-- The reduced environment of `Open.ofMultiHybrid π idle` is `π.reduceEnv idle`. -/
theorem reduceEnv_ofMultiHybrid {σ : Type} (π : MultiHybrid σ E O EG OG) (idle : EG)
    (Z : Env (Strat ζ E O) ζ) : (ofMultiHybrid π idle).reduceEnv Z = π.reduceEnv idle Z := by
  simp only [reduceEnv, ofMultiHybrid, MultiHybrid.reduceEnv, SPComp.pure_bind]

/-- A hybrid as an open system: the reduced environment is `π.reduce`, and every subroutine is
admissible. -/
noncomputable def ofHybrid {σ : Type} (π : Hybrid σ E O EG OG) : Open E O EG OG where
  St τ := σ × τ
  withSub X := π.withSub X
  Ctx ζ := ζ × σ
  reduce Z := π.reduce Z
  proj c := SPComp.pure c.1
  Adm _ := True
  view_withSub X Z _ := π.view_withSub X Z

/-- The reduced environment of `Open.ofHybrid π` is `π.reduceEnv`. -/
theorem reduceEnv_ofHybrid {σ : Type} (π : Hybrid σ E O EG OG) (Z : Env (Strat ζ E O) ζ) :
    (ofHybrid π).reduceEnv Z = π.reduceEnv Z := by
  simp only [reduceEnv, ofHybrid, Hybrid.reduceEnv, SPComp.pure_bind]

/-- The strategy over the unit interface that holds the outer strategy `Z` as its state and
runs no activation. -/
noncomputable def holdStrat (Z : Strat ζ E O) : Strat (Strat ζ E O) Unit Unit where
  rounds := 0
  init := Z
  next c := SPComp.pure (c, ())
  obs c _ := SPComp.pure c
  next_noFail _ := SPComp.pure_noFail _
  obs_noFail _ _ := SPComp.pure_noFail _

/-- The view of the strategy `holdStrat Z` against every system is the point mass at `Z`. -/
theorem view_holdStrat (X : Sys τ Unit Unit) (Z : Strat ζ E O) :
    view X (holdStrat Z) = SPComp.pure Z := by
  simp [view, run, holdStrat, loop, SPComp.map]

/-- A closed system as an open system over the unit interface: it ignores its subroutine, and
its reduced environment holds the outer strategy and runs it against `C` in the
post-processing. Every subroutine is admissible. -/
noncomputable def closed (C : Sys τ E O) : Open E O Unit Unit where
  St _ := τ
  withSub _ := C
  Ctx ζ := Strat ζ E O
  reduce Z := holdStrat Z
  proj c := view C c
  Adm _ := True
  view_withSub X Z _ := by
    rw [view_holdStrat, SPComp.pure_bind]

/-! ## Identity and composition -/

/-- The identity open system: the subroutine itself, with the environment unchanged. -/
noncomputable def id (E O : Type) : Open E O E O where
  St τ := τ
  withSub X := X
  Ctx ζ := ζ
  reduce Z := Z
  proj c := SPComp.pure c
  Adm _ := True
  view_withSub _ _ _ := (SPComp.bind_pure _).symm

/-- **Composition of open systems**: `P₁` running with `P₂` running with the subroutine. The
reduced environment reduces through `P₁` and then through `P₂`, and the post-processing runs
that of `P₂` and then that of `P₁`. -/
noncomputable def comp (P₁ : Open E O EM OM) (P₂ : Open EM OM EG OG) : Open E O EG OG where
  St τ := P₁.St (P₂.St τ)
  withSub X := P₁.withSub (P₂.withSub X)
  Ctx ζ := P₂.Ctx (P₁.Ctx ζ)
  reduce Z := P₂.reduce (P₁.reduce Z)
  proj c := SPComp.bind (P₂.proj c) P₁.proj
  Adm X := P₂.Adm X ∧ P₁.Adm (P₂.withSub X)
  view_withSub X Z h := by
    rw [P₁.view_withSub _ Z h.2, P₂.view_withSub X _ h.1, SPComp.bind_assoc]

/-- The reduced environment of a composite is the reduction through `P₂` of the reduction
through `P₁`. -/
theorem reduceEnv_comp (P₁ : Open E O EM OM) (P₂ : Open EM OM EG OG)
    (Z : Env (Strat ζ E O) ζ) : (P₁.comp P₂).reduceEnv Z = P₂.reduceEnv (P₁.reduceEnv Z) := by
  simp only [reduceEnv, comp, SPComp.bind_assoc]

/-- The reduced environment of the identity is the environment itself. -/
theorem reduceEnv_id (Z : Env (Strat ζ E O) ζ) : (Open.id E O).reduceEnv Z = Z := by
  simp only [reduceEnv, Open.id, SPComp.pure_bind]

/-- Associativity of composition. -/
theorem comp_assoc {EN ON : Type} (P₁ : Open E O EM OM) (P₂ : Open EM OM EN ON)
    (P₃ : Open EN ON EG OG) : (P₁.comp P₂).comp P₃ = P₁.comp (P₂.comp P₃) := by
  simp only [comp, SPComp.bind_assoc, and_assoc]

/-- The identity is a left unit. -/
theorem id_comp (P : Open E O EG OG) : (Open.id E O).comp P = P := by
  cases P
  simp only [comp, Open.id, SPComp.bind_pure, and_true]

/-- The identity is a right unit. -/
theorem comp_id (P : Open E O EG OG) : P.comp (Open.id EG OG) = P := by
  cases P
  simp only [comp, Open.id, SPComp.pure_bind, true_and]

end Open

namespace MultiHybrid

variable {σ τ E O EG OG : Type}

/-- If `start` answers the event `g` with the output `o` from every state, without a call and
without a change of state, then `π.withSub X` is idle at `g` with output `o`, for every `X`. -/
theorem idleAt_withSub (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) {g : E} {o : O}
    (h : ∀ s, π.start s g = SPComp.pure (s, .inr o)) : IdleAt (π.withSub X) g o := by
  intro t
  cases hf : π.fuel <;> simp [withSub, h, drive, hf]

end MultiHybrid

end CatCrypt.Crypto.UCTransparent
