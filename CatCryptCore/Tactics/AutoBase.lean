/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoDispatchCore
public import CatCryptCore.Tactics.RepairAction

/-!
# The shapes of `catcrypt_auto` and its arms from the Lean core

Registrations with the registry of `CatCryptCore.Tactics.AutoDispatchCore`. They name
the constants of the game-proof theory by `Name` and import none of it, so the module
imports only `Lean` and the Lean-only modules of the dispatcher; a module of any level
that imports it, and the theory it states goals in, uses `catcrypt_auto`.

The module also defines `catcrypt_grind` and `catcrypt_grind [p₁, …]`: `grind`, with the
given parameters, with the scoped lemma set of namespace `CatCryptGrind` active. The
theory modules add their lemmas to that set beside their statements.

The module also brings into scope the grind repair code action of
`CatCryptCore.Tactics.RepairAction`, and registers `SPComp` as a program type of
`funext_unfold`.

Normalisation: a goal mentioning `>>=` is rewritten by
`simp only [CatCrypt.Core.SPComp.monad_bind_eq]`.

Shapes of the normalised stage, by decreasing priority:

| Shape | Detected head |
|---|---|
| `IsPure/NoFail side condition` | `SPComp.IsPure _`, `SPComp.NoFail _` |
| `relational rHoare judgment` | `rHoare _ _ _ _` |
| `distance inequality` | `_ ≤ _` over `ℝ≥0∞` or `ℝ` whose left side is a registered distance or a sum with one as summand, or that mentions a registered head, `prTrue` or `prEvent` |
| `advantage equality` | `_ = _` one of whose sides is an application of `AdvantageA` or `Advantage` |
| `monotonicity inequality` | `f a₁ … aₙ ≤ f b₁ … bₙ` or `<`, the same head on both sides; `Monotone f`, `Antitone f`, `StrictMono f`, `StrictAnti f` |
| `heap read after write` | `Heap.get (Heap.set _ _ _) _ = _`, either side |
| `SPComp equality` | `_ = _` over `SPComp _` |
| `heap read after write` | `=`, `≠` or `¬ _ = _` mentioning `Heap.set` |

Arms, each skipped when a constant it names is absent; an arm whose tactic, rule set or
attribute is absent from the environment fails and the next arm runs:

| Shape | Arm | Order |
|---|---|---|
| `*` | `exact t` | 10 |
| `*` | `apply t <;> (first \| assumption \| catcrypt_grind)` | 20 |
| `IsPure/NoFail side condition` | `aesop` over `CatCryptRel` | 10 |
| `relational rHoare judgment` | `aesop` over `CatCryptRel` | 10 |
| `distance inequality` | `gcongr <;> catcrypt_grind`; `catcrypt_grind`; `bound` (a quarter of the budget; skipped when a `∀`-quantified inequality is in context) | 30; 40; 50 |
| `monotonicity inequality` | `gcongr <;> catcrypt_grind` | 30 |
| `SPComp equality` | `catcrypt_grind` | 10 |
| `IsPure/NoFail side condition` | `solve_by_elim` over the `IsPure` combinators of `pure`, `sample`, `fail` and `SPComp.bind` | 90 |
| `IsPure/NoFail side condition` | `solve_by_elim` over the `NoFail` combinators of `pure`, `sample` and `SPComp.bind` | 91 |
| `heap read after write` | `grind [Heap.get_set_same, Heap.get_set_other, …]` | 10 |
| `monotonicity inequality` | `simp_all`; `grind` | 50; 60 |
| `other` | `simp_all`; `grind` | 20; 30 |
| `premises` | `solve_by_elim [p₁, …]` | 10 |
| `premises` | the forms of `AutoDispatch.PremiseForms.closeWith`, after the arms | — |
-/

public section

/-! ## The `catcrypt_grind` closer -/

namespace CatCryptGrind
end CatCryptGrind

namespace CatCrypt.Tactics

/-- `catcrypt_grind` runs `grind` with the scoped lemma set of `CatCryptGrind`
active. -/
macro "catcrypt_grind" : tactic => `(tactic| open CatCryptGrind in grind)

/-- `catcrypt_grind [p₁, …, pₙ]` runs `grind [p₁, …, pₙ]` with the scoped lemma
set of `CatCryptGrind` active. -/
macro "catcrypt_grind" " [" ps:Lean.Parser.Tactic.grindParam,* "]" : tactic =>
  `(tactic| open CatCryptGrind in grind [$ps,*])

end CatCrypt.Tactics

/-! ## Normalisation -/

catcrypt_auto_norm needs [CatCrypt.Core.SPComp.monad_bind_eq] when mentions [Bind.bind] :=
  "simp only [CatCrypt.Core.SPComp.monad_bind_eq]"

/-! ## Program types of `funext_unfold` -/

catcrypt_funext_type CatCrypt.Core.SPComp

/-! ## Shapes -/

catcrypt_auto_shape "IsPure/NoFail side condition" priority 100 :=
  any [app CatCrypt.Core.SPComp.IsPure, app CatCrypt.Crypto.SPComp.NoFail]

catcrypt_auto_shape "relational rHoare judgment" priority 100 :=
  app CatCrypt.Relational.rHoare

catcrypt_auto_shape "distance inequality" priority 90 :=
  distance [ENNReal, Real] mentioning [CatCrypt.Crypto.prTrue, CatCrypt.Unary.prEvent]

catcrypt_auto_shape "advantage equality" priority 85 :=
  any [arg Eq/3 at 1 (app CatCrypt.Crypto.AdvantageA), arg Eq/3 at 1 (app CatCrypt.Crypto.Advantage),
    arg Eq/3 at 2 (app CatCrypt.Crypto.AdvantageA), arg Eq/3 at 2 (app CatCrypt.Crypto.Advantage)]

catcrypt_auto_shape "monotonicity inequality" priority 80 :=
  any [same_head_sides LE.le, same_head_sides LT.lt, app Monotone, app Antitone,
    app StrictMono, app StrictAnti]

catcrypt_auto_shape "heap read after write" priority 70 :=
  any [arg Eq/3 at 1 (arg CatCrypt.Core.Heap.get/2 at 0 (app CatCrypt.Core.Heap.set/3)),
    arg Eq/3 at 2 (arg CatCrypt.Core.Heap.get/2 at 0 (app CatCrypt.Core.Heap.set/3))]

catcrypt_auto_shape "SPComp equality" priority 60 :=
  arg Eq/3 at 0 whnf (app CatCrypt.Core.SPComp)

catcrypt_auto_shape "heap read after write" priority 50 :=
  any [all [app Eq, mentions [CatCrypt.Core.Heap.set]],
    all [app Ne, mentions [CatCrypt.Core.Heap.set]],
    arg Not/1 at 0 (all [app Eq/3, mentions [CatCrypt.Core.Heap.set]])]

/-! ## Arms -/

catcrypt_auto_arm "*" order 10 := "exact %TERM"

catcrypt_auto_arm "IsPure/NoFail side condition" order 90
    needs [CatCrypt.Core.SPComp.bind_isPure, CatCrypt.Core.SPComp.pure_isPure,
      CatCrypt.Core.SPComp.sample_isPure, CatCrypt.Core.SPComp.fail_isPure] :=
  "solve_by_elim only [*, CatCrypt.Core.SPComp.bind_isPure, CatCrypt.Core.SPComp.pure_isPure, \
    CatCrypt.Core.SPComp.sample_isPure, CatCrypt.Core.SPComp.fail_isPure]"

catcrypt_auto_arm "IsPure/NoFail side condition" order 91
    needs [CatCrypt.Crypto.Assumptions.SPComp.bind_noFail, CatCrypt.Crypto.SPComp.pure_noFail,
      CatCrypt.Crypto.Assumptions.SPComp.sample_noFail] :=
  "solve_by_elim only [*, CatCrypt.Crypto.Assumptions.SPComp.bind_noFail, \
    CatCrypt.Crypto.SPComp.pure_noFail, CatCrypt.Crypto.Assumptions.SPComp.sample_noFail]"

catcrypt_auto_arm "heap read after write" order 10
    needs [CatCrypt.Core.Heap.get_set_same, CatCrypt.Core.Heap.get_set_other] :=
  "grind [CatCrypt.Core.Heap.get_set_same, CatCrypt.Core.Heap.get_set_other%GRIND_TAIL]"

catcrypt_auto_arm "monotonicity inequality" order 50 := "%SIMP_ALL"
catcrypt_auto_arm "monotonicity inequality" order 60 := "grind%GRIND"

catcrypt_auto_arm "other" order 20 := "%SIMP_ALL"
catcrypt_auto_arm "other" order 30 := "grind%GRIND"

catcrypt_auto_arm "premises" order 10 := "solve_by_elim%PREMISES"

/-! ## Arms over the `CatCryptRel` and `CatCryptGrind` sets -/

catcrypt_auto_arm "*" order 20 := "(apply %TERM <;> (first | assumption | catcrypt_grind))"

catcrypt_auto_arm "IsPure/NoFail side condition" order 10 :=
  "aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })%AESOP_ADD"

catcrypt_auto_arm "relational rHoare judgment" order 10 :=
  "aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })%AESOP_ADD"

catcrypt_auto_arm "distance inequality" order 30 := "(gcongr <;> catcrypt_grind%GRIND)"
catcrypt_auto_arm "distance inequality" order 40 := "catcrypt_grind%GRIND"
catcrypt_auto_arm "distance inequality" order 50 skip_forall_ineq budget_div 4 := "bound"

catcrypt_auto_arm "monotonicity inequality" order 30 := "(gcongr <;> catcrypt_grind%GRIND)"

catcrypt_auto_arm "SPComp equality" order 10 := "catcrypt_grind%GRIND"
