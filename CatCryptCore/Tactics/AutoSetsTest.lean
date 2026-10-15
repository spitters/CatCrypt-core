/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoSets
public meta import CatCryptCore.Tactics.AutoSets
public import CatCryptCore.Crypto.HybridArgument

/-!
# Tests for the automation sets of `CatCryptCore.Tactics.AutoSets`

Each example states a goal shape that occurs in an existing proof and closes it
with one of the mechanisms of `CatCryptCore.Tactics.AutoSets`.
-/

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Relational CatCrypt.Crypto CatCrypt.Unary CatCrypt.Prob
open scoped ENNReal

namespace CatCrypt.Tactics.AutoSetsTest

/-! ## Scoped `grind` set -/

/-- Heap frame shape of `collFlag_preserved_by_set` (Examples/Cryptobox/PKEY.lean):
a write to another location preserves a read. Plain `grind` does not close it. -/
example (h₁ : Heap) (l l' : Location) (v : l.ty) (b : l'.ty) (hid : l.id ≠ l'.id)
    (hset : Heap.get h₁ l' = b) :
    Heap.get (h₁.set l v) l' = b := by
  fail_if_success grind
  catcrypt_grind

/-- Read-after-two-writes shape of `genOracle_instr_agree` (Examples/Cryptobox/PKEY.lean). -/
example (h : Heap) (l₁ l₂ l : Location) (v₁ : l₁.ty) (v₂ : l₂.ty) (v : l.ty)
    (h1 : l₁.id ≠ l.id) (h2 : l₂.id ≠ l.id) :
    (((h.set l v).set l₁ v₁).set l₂ v₂).get l = v := by
  catcrypt_grind

/-- Monad-law normalisation of an `SPComp` chain (the `sp_normalize` idiom). -/
example {α β : Type} (a : α) (c : SPComp β) (f : α → SPComp β) (hf : f a = c) :
    SPComp.bind (SPComp.bind (SPComp.pure a) f) SPComp.pure = c := by
  catcrypt_grind

/-- Advantage symmetry and reflexivity (as in `advantage_le_prBad_right`,
Unary/FailureEvent.lean). -/
example (G₀ G₁ : SPComp Bool) (ε : ℝ≥0∞) (h : Advantage G₀ G₁ = ε) :
    Advantage G₁ G₀ = ε ∧ Advantage G₁ G₁ = 0 := by
  catcrypt_grind

/-! ## Aesop rule set `CatCryptRel` -/

/-- A pure prefix followed by identical code on both sides: `rHoare_refl` after
monad-law normalisation. -/
example {α β : Type} (a : α) (c : α → SPComp β) :
    rHoare eqPre (SPComp.bind (SPComp.pure a) c) (c a) eqPost := by
  aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })

/-- Synchronised sampling (the shape closed by `rHoare_sample_same` in `ssprove_sim`). -/
example (Φ : RPre) :
    rHoare Φ (SPComp.sample Bool) (SPComp.sample Bool)
      (fun a₁ h₁ a₂ h₂ => Φ h₁ h₂ ∧ a₁ = a₂) := by
  aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })

/-! ## `gcongr` -/

/-- Monotonicity of `wpEF` in the postcondition and the error term
(the shape of `wpEF_mono`, Unary/ExpectationVCGen.lean). -/
example {α : Type} (c : SPComp α) (post post' : α → Heap → ℝ≥0∞) (e : ℝ≥0∞)
    (hpost : ∀ a h', post a h' ≤ post' a h') (h : Heap) :
    wpEF c post e h ≤ wpEF c post' (e + 1) h := by
  gcongr with a h'
  · exact hpost a h'
  · exact le_self_add

/-- Monotonicity of `prEvent` in the event. -/
example {α : Type} (d : SDistr (α × Heap)) (E : α → Heap → Prop) :
    prEvent d (fun a h => E a h ∧ True) ≤ prEvent d (fun a h => E a h ∨ False) := by
  gcongr with a h
  exact fun hE => Or.inl hE.1

/-- The per-hop step of `advantage_hybrid_uniform` (Crypto/HybridArgument.lean). -/
example {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool) (n : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, AdvantageA (G i) (G (i + 1)) A ≤ ε) :
    ∑ i ∈ Finset.range n, AdvantageA (G i) (G (i + 1)) A ≤ ∑ _i ∈ Finset.range n, ε := by
  gcongr with i
  exact hstep i

/-! ## `bound` -/

/-- A scaled success probability is at most the scale. -/
example (G : SPComp Bool) (h : Heap) (x : ℝ≥0∞) : prTrue G h * x ≤ 1 * x := by
  bound

/-! ## `ssprove_crypto_grind` -/

/-- Pure-prefix relational goal. -/
example {α β : Type} (a : α) (c : α → SPComp β) :
    rHoare eqPre (SPComp.bind (SPComp.pure a) c) (c a) eqPost := by
  ssprove_crypto_grind

/-- Synchronised read under an invariant that fixes the location (the shape of
`rHoare_get_sync`), with the side condition in the context. -/
example (Φ : RPre) (l : Location) (hS : ∀ h₁ h₂, Φ h₁ h₂ → h₁.get l = h₂.get l) :
    rHoare Φ (SPComp.get l) (SPComp.get l) (fun v₁ h₁ v₂ h₂ => Φ h₁ h₂ ∧ v₁ = v₂) := by
  ssprove_crypto_grind

/-- Identical sampling games (the example in the docstring of `ssprove_auto_ec`). -/
example (x : Bool) :
    rHoare eqPre (SPComp.bind (SPComp.sample Bool) (fun k => SPComp.pure (xor k x)))
      (SPComp.bind (SPComp.sample Bool) (fun k => SPComp.pure (xor k x))) eqPost := by
  ssprove_crypto_grind

/-- Heap goal of the `collFlag_preserved_by_set` shape. -/
example (h₁ : Heap) (l l' : Location) (v : l.ty) (b : l'.ty) (hid : l.id ≠ l'.id)
    (hset : Heap.get h₁ l' = b) :
    Heap.get (h₁.set l v) l' = b := by
  ssprove_crypto_grind

end CatCrypt.Tactics.AutoSetsTest
