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

/-! ## Additions from the closing-goal sweep -/

/-- Monotone step of the triangle chain in `elgamal_secure` (Examples/ElGamal.lean:256):
`add_le_add` with the `@[grind]` triangle inequality. -/
example (R0r R0i R1i R1r : SPComp Bool) :
    Advantage R0r R0i + Advantage R0i R1r ≤
      Advantage R0r R0i + (Advantage R0i R1i + Advantage R1i R1r) := by
  catcrypt_grind

/-- Zero case of `advantage_hybrid_dep` (Crypto/HybridArgument.lean:79). -/
example {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool) :
    AdvantageA (G 0) (G 0) A ≤ ∑ i ∈ Finset.range 0, AdvantageA (G i) (G (i + 1)) A := by
  catcrypt_grind

/-- Triangle step of `advantage_hybrid_dep` (Crypto/HybridArgument.lean:84). -/
example {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool) (k : ℕ) :
    AdvantageA (G 0) (G (k + 1)) A ≤
      AdvantageA (G 0) (G k) A + AdvantageA (G k) (G (k + 1)) A := by
  catcrypt_grind

/-- Two hop leaves of a game-hopping sum (the shape at KEMTLS/Reduction:161). -/
example (G₀ G₁ G₂ : SPComp Bool) (ε δ : ℝ≥0∞) (h₁ : Advantage G₀ G₁ ≤ ε)
    (h₂ : Advantage G₁ G₂ ≤ δ) :
    Advantage G₀ G₁ + Advantage G₁ G₂ ≤ ε + δ := by
  catcrypt_grind

/-- Synchronised sampling and reflexivity (the shape at Test/EasyCryptTacticTest:229). -/
example (Φ : RPre) :
    rHoare eqPre (SPComp.sample Bool) (SPComp.sample Bool) eqPost ∧
      rHoare Φ (SPComp.sample Bool) (SPComp.sample Bool)
        (fun a₁ h₁ a₂ h₂ => Φ h₁ h₂ ∧ a₁ = a₂) := by
  catcrypt_grind

/-- A fresh lazy evaluation against a direct sample (the shape at
Test/EasyCryptTacticTest:334). -/
example (lookup : ℕ → SPComp (Option Bool)) (store : ℕ → Bool → SPComp Unit) (k : ℕ)
    (h_fresh : lookup k = SPComp.pure none) (h_dead : ∀ v, store k v = SPComp.pure ()) :
    rHoare eqPre (CatCrypt.LazySampling.lazyEvalAbstract lookup store k)
      (SPComp.sample Bool) eqPost := by
  catcrypt_grind

/-- `IsPure` of a `do` block with a pair pattern (the shape at NoiseIK/Spec:105). -/
example (kg : SPComp (Bool × Bool)) (hkg : SPComp.IsPure kg) :
    SPComp.IsPure (do
      let ⟨a, b⟩ ← kg
      let x ← SPComp.sample Bool
      pure (xor a (xor b x))) := by
  aesop (rule_sets := [CatCryptRel])

/-- `NoFail` of a `do` block (the shape at IrisBridge/RatchetUCGrounding:140). -/
example (kg : SPComp (Bool × Bool)) (hkg : SPComp.NoFail kg) :
    SPComp.NoFail (do
      let ⟨a, b⟩ ← kg
      let x ← SPComp.sample Bool
      pure (xor a (xor b x))) := by
  aesop (rule_sets := [CatCryptRel])

/-- Division monotonicity with a cast from `ℕ` (the shape at OEKE/Reduction:292). -/
example (q₁ q₂ d : ℕ) (h : q₁ ≤ q₂) : (q₁ : ℝ≥0∞) / d ≤ (q₂ : ℝ≥0∞) / d := by
  bound

/-- Coefficient bounds `ε ≤ n * ε` (the shape at SPHINCSPlus/Reduction:247). -/
example (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (ε₁ ε₂ : ℝ≥0∞) :
    ε₁ + ε₂ ≤ (a : ℝ≥0∞) * ε₁ + (b : ℝ≥0∞) * ε₂ := by
  bound

/-! ## Termination of the relational drivers -/

/-- On a goal that `rHoare_refl` does not close and that the closing tactics
leave open, each driver fails within the default heartbeats. -/
example : True := by
  fail_if_success
    have : rHoare eqPre (SPComp.sample Bool) (SPComp.pure true) eqPost := by ssprove_auto_step
  fail_if_success
    have : rHoare eqPre (SPComp.sample Bool) (SPComp.pure true) eqPost := by ssprove_crypto_step
  fail_if_success
    have : rHoare eqPre (SPComp.sample Bool) (SPComp.pure true) eqPost := by ssprove_auto_ec
  fail_if_success
    have : rHoare eqPre (SPComp.sample Bool) (SPComp.pure true) eqPost := by ssprove_auto_ec!
  fail_if_success
    have : rHoare eqPre (SPComp.sample Bool) (SPComp.pure true) eqPost := by ssprove_crypto
  trivial

/-- Synchronised sampling with a constant continuation: closed by `ssprove_auto_ec`
after a `ssprove_sync` round. -/
example : rHoare eqPre (SPComp.bind (SPComp.sample Bool) (fun _ => SPComp.pure (42 : ℕ)))
    (SPComp.bind (SPComp.sample Bool) (fun _ => SPComp.pure (42 : ℕ))) eqPost := by
  ssprove_auto_ec

/-- A pure prefix against a constant: closed by `ssprove_crypto` through simplification. -/
example (x : Bool) :
    rHoare eqPre (SPComp.bind (SPComp.pure x) (fun k => SPComp.pure (xor k x)))
      (SPComp.pure false) eqPost := by
  ssprove_crypto

/-- Identical programs: closed by `ssprove_auto_ec!` through `rHoare_refl`. -/
example : rHoare eqPre (SPComp.bind (SPComp.sample Bool) (fun x => SPComp.pure x))
    (SPComp.bind (SPComp.sample Bool) (fun x => SPComp.pure x)) eqPost := by
  ssprove_auto_ec!

/-- `ssprove_crypto_step` passes over alternatives that succeed without progress
and closes the goal by `assumption`. -/
example (h : rHoare eqPre (SPComp.sample Bool) (SPComp.pure true) eqPost) :
    rHoare eqPre (SPComp.sample Bool) (SPComp.pure true) eqPost := by
  ssprove_crypto_step

end CatCrypt.Tactics.AutoSetsTest
