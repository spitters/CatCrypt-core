/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage

/-!
# Shallow module/functor SSP layer

An EasyCrypt-style *module* is a record of oracle procedures; a *functor*
(reduction) is a function on modules; module composition is `SPComp.bind`. All of
this is native to Lean — records and functions — and lives at the **shallow**
`SPComp` level, where the monad laws hold (via `SPComp.bind_assoc`) rather than
requiring the deep `RawCode` embedding.

The engine is the single composition lemma `advantageA_absorb`: absorbing a
reduction `R` into the adversary. It is the shallow analog of the deep
`DeepNomAdvantage_link`, proved once by shallow bind-associativity — with **no
deep-embedding assoc tax and no reifier**. A multi-hop game-hopping reduction is
then just `advantageA_absorb` (one hop = one component advantage) chained by the
existing `advantage_triangle`, replacing the per-hybrid `*_eq_*_bind` lemmas that
hand-rolled proofs carry.

## Main results
* `advantageA_absorb` — `AdvantageA (H₀ >>= R) (H₁ >>= R) A = AdvantageA H₀ H₁ (R · >>= A)`.
* `OracleModule` — a record of oracle procedures (the shallow module).
* `hybrid_bound₃` — a three-hop reduction bound assembled from `advantageA_absorb`
  + `advantage_triangle`, the reusable skeleton a KEM-DEM-style proof plugs into.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.ShallowModule

open CatCrypt.Core CatCrypt.Crypto
open scoped ENNReal

/-! ## The composition engine -/

/-- **Absorb a reduction into the adversary** (the shallow `DeepNomAdvantage_link`).

    If both games factor through a common reduction `R` after a component game
    `H₀`/`H₁`, then distinguishing them with adversary `A` is the same as
    distinguishing the components `H₀`/`H₁` with the adversary `R · >>= A`.
    Proved once, by shallow bind-associativity.

    NOTE (2026-07-17): this is the SSP "code-motion" lemma, and it is *definitionally
    the same* fact as the canonical `CatCryptCore.Relational.Rules.advantage_factorization`
    (identical statement + `simp [AdvantageA, SPComp.bind_assoc]` proof). The heavy
    protocols (TLS/MLS/Signal) use `advantage_factorization` (41×); `advantageA_absorb`
    is the shallow-module-layer twin, kept only for this module's `hybrid_bound₃`
    ergonomics. **New code should prefer `advantage_factorization`.** -/
theorem advantageA_absorb {α β : Type*} (H₀ H₁ : SPComp α) (R : α → SPComp β)
    (A : β → SPComp Bool) :
    AdvantageA (H₀.bind R) (H₁.bind R) A = AdvantageA H₀ H₁ (fun x => (R x).bind A) := by
  simp only [AdvantageA, SPComp.bind_assoc]

/-- Symmetric form: a reduction applied on the *left* of the adversary chain. -/
theorem advantageA_absorb_left {α β : Type*} (H₀ H₁ : SPComp α) (R : α → SPComp β)
    (A : β → SPComp Bool) :
    AdvantageA H₀ H₁ (fun x => (R x).bind A) = AdvantageA (H₀.bind R) (H₁.bind R) A :=
  (advantageA_absorb H₀ H₁ R A).symm

/-! ## The module record

A shallow oracle module bundles a game's oracle procedures. Games and
adversaries are modules; a reduction/functor is a function `OracleModule I → OracleModule J`.
Kept intentionally thin — the ergonomic wrapper over the `advantageA_absorb`
engine, not a new semantics. -/

/-- A shallow oracle module: for each operation `i : ι` of the interface, a
    procedure taking a `dom i` and producing an `SPComp (cod i)`. -/
structure OracleModule (ι : Type*) (dom cod : ι → Type*) where
  /-- The procedure implementing operation `i`. -/
  proc : (i : ι) → dom i → SPComp (cod i)

/-- A single-operation module is exactly a game `A → SPComp B` (EC's common case). -/
def OracleModule.ofGame {A B : Type*} (g : A → SPComp B) :
    OracleModule Unit (fun _ => A) (fun _ => B) where
  proc := fun _ => g

/-- Recover the game from a single-operation module. -/
def OracleModule.toGame {A B : Type*}
    (m : OracleModule Unit (fun _ => A) (fun _ => B)) : A → SPComp B :=
  m.proc ()

@[simp] theorem OracleModule.toGame_ofGame {A B : Type*} (g : A → SPComp B) :
    (OracleModule.ofGame g).toGame = g := rfl

/-! ## Reusable multi-hop skeleton

A game-hopping reduction with intermediate games `G₀ → G₁ → G₂ → G₃` bounds the
end-to-end advantage by the three per-hop advantages. Each hop that is a
reduction collapses to a component advantage via `advantageA_absorb`; the
assembly is the existing `advantage_triangle`. This skeleton is what a KEM-DEM
proof plugs its three hops into — no bespoke `*_eq_*_bind` lemmas. -/

/-- Three-hop advantage bound (triangle, twice). The reusable skeleton for a
    three-term game-hopping reduction (e.g. KEM-DEM: `KEM + DEM + KEM`). -/
theorem hybrid_bound₃ (G₀ G₁ G₂ G₃ : SPComp Bool) :
    Advantage G₀ G₃ ≤ Advantage G₀ G₁ + Advantage G₁ G₂ + Advantage G₂ G₃ := by
  calc Advantage G₀ G₃ ≤ Advantage G₀ G₁ + Advantage G₁ G₃ := advantage_triangle G₀ G₁ G₃
    _ ≤ Advantage G₀ G₁ + (Advantage G₁ G₂ + Advantage G₂ G₃) :=
        add_le_add le_rfl (advantage_triangle G₁ G₂ G₃)
    _ = Advantage G₀ G₁ + Advantage G₁ G₂ + Advantage G₂ G₃ := (add_assoc _ _ _).symm

/-- Adversary-level three-hop bound: the same skeleton at the `AdvantageA` level,
    so each hop can be discharged by `advantageA_absorb` down to a component. -/
theorem hybrid_boundA₃ {α : Type*} (G₀ G₁ G₂ G₃ : SPComp α) (A : α → SPComp Bool) :
    AdvantageA G₀ G₃ A ≤ AdvantageA G₀ G₁ A + AdvantageA G₁ G₂ A + AdvantageA G₂ G₃ A := by
  simpa only [AdvantageA] using hybrid_bound₃ (G₀.bind A) (G₁.bind A) (G₂.bind A) (G₃.bind A)

end CatCrypt.Crypto.ShallowModule
