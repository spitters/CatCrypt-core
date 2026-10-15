/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoDispatch
public meta import CatCryptCore.Tactics.AutoDispatch

/-!
# Tests for `catcrypt_auto`

One example per shape of `CatCryptCore.Tactics.AutoDispatch`, a goal whose
shape is detected but whose arms fail, goals on which an arm exceeds its
heartbeat budget, and goals restated from game proofs: hop chains, hop leaves
whose lemma is passed as an argument, monotonicity goals, goals behind `set`,
heap disequalities under `some`, and the error on goals that stay open.
-/

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Relational CatCrypt.Crypto CatCrypt.Unary
open scoped ENNReal

namespace CatCrypt.Tactics.AutoDispatchTest

/-! ## One goal per shape -/

/-- Side condition in `do` form (the shape of `ik_real` in NoiseIK/Spec.lean). -/
example : SPComp.IsPure (do
    let a ← SPComp.sample Bool
    let b ← SPComp.sample Bool
    pure (a && b) : SPComp Bool) := by
  catcrypt_auto

/-- `NoFail` side condition in `>>=` form. -/
example {α β : Type} (a : α) (f : α → SPComp β) (hf : ∀ x, SPComp.NoFail (f x)) :
    SPComp.NoFail ((pure a : SPComp α) >>= f) := by
  catcrypt_auto

/-- A pure prefix followed by identical code on both sides. -/
example {α β : Type} (a : α) (c : α → SPComp β) :
    rHoare eqPre (SPComp.bind (SPComp.pure a) c) (c a) eqPost := by
  catcrypt_auto

/-- Two hop leaves of a triangle chain (the shape of KEMTLS/Reduction.lean:161). -/
example {α : Type} (G₀ G₁ G₂ : SPComp α) (A : α → SPComp Bool) (ε₁ ε₂ : ℝ≥0∞)
    (h₁ : AdvantageA G₀ G₁ A ≤ ε₁) (h₂ : AdvantageA G₁ G₂ A ≤ ε₂) :
    AdvantageA G₀ G₁ A + AdvantageA G₁ G₂ A ≤ ε₁ + ε₂ := by
  catcrypt_auto

/-- Read after a write to another location (Examples/Cryptobox/PKEY.lean:439). -/
example (h₁ : Heap) (l l' : Location) (v : l.ty) (b : l'.ty) (hid : l.id ≠ l'.id)
    (hset : Heap.get h₁ l' = b) :
    Heap.get (h₁.set l v) l' = b := by
  catcrypt_auto

/-- Monad-law normalisation of an `SPComp` chain. -/
example {α β : Type} (a : α) (c : SPComp β) (f : α → SPComp β) (hf : f a = c) :
    SPComp.bind (SPComp.bind (SPComp.pure a) f) SPComp.pure = c := by
  catcrypt_auto

/-- A goal of no registered shape. -/
example (n : ℕ) (h : n = 3) : n + 1 = 4 := by
  catcrypt_auto

/-! ## Failure within the budget -/

/-- The shape is detected and every arm fails on a false bound. -/
example (G₀ G₁ : SPComp Bool) : True := by
  fail_if_success have _ : Advantage G₀ G₁ ≤ 0 := by catcrypt_auto
  trivial

/-- `simp_all` rewrites `f n` to `f (n + 1)` without end and reaches the
recursion limit; the runtime exception is caught and `grind` closes the goal. -/
example (f : ℕ → ℕ) (_h : ∀ n, f n = f (n + 1)) (h₇ : f 0 = 7) : f 0 = 7 := by
  catcrypt_auto

-- Under a budget of one heartbeat unit the `aesop` arm exceeds it; the
-- heartbeat exception is caught and reported as the failure of the arm.
set_option catcrypt_auto.maxHeartbeats 1 in
example : True := by
  fail_if_success
    have _ : SPComp.NoFail ((pure true : SPComp Bool) >>= fun b => pure (!b)) := by catcrypt_auto
  trivial

/-! ## Suggestion -/

/-- `catcrypt_auto?` suggests the closing arm with its normalisation. -/
example {α β : Type} (a : α) (f : α → SPComp β) (hf : ∀ x, SPComp.NoFail (f x)) :
    SPComp.NoFail ((pure a : SPComp α) >>= f) := by
  catcrypt_auto?

/-- On a goal without `>>=` the suggestion has no `simp only` prefix (the goal of
Examples/Cryptobox/PKEY.lean:439). -/
example (h₁ : Heap) (l l' : Location) (v : l.ty) (b : l'.ty) (hid : l.id ≠ l'.id)
    (hset : Heap.get h₁ l' = b) : Heap.get (h₁.set l v) l' = b := by
  catcrypt_auto?

/-- The literal disequality of Examples/Cryptobox/PKEY.lean:472, without prefix. -/
example : (101 : ℕ) ≠ 103 := by
  catcrypt_auto?

/-! ## Hop chains -/

/-- The three-hop chain of Examples/PRF.lean:187 (`cascade_prf_bound`), with the
birthday term abstracted to `b`: the hop chain arm through `G 1` and `G 2`. -/
example {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool) (ε_prf b : ℝ≥0∞)
    (h01 : AdvantageA (G 0) (G 1) A ≤ ε_prf) (h12 : AdvantageA (G 1) (G 2) A ≤ b)
    (h23 : AdvantageA (G 2) (G 3) A ≤ ε_prf) :
    AdvantageA (G 0) (G 3) A ≤ 2 * ε_prf + b := by
  catcrypt_auto?

/-- A two-hop chain over `Advantage`. -/
example (G₀ G₁ G₂ : SPComp Bool) (ε : ℝ≥0∞) (h₁ : Advantage G₀ G₁ ≤ ε)
    (h₂ : Advantage G₁ G₂ ≤ ε) : Advantage G₀ G₂ ≤ 2 * ε := by
  catcrypt_auto?

/-- A hop assumption packaged in a structure, as `DDH_Advantage` and the KEMTLS
assumptions package theirs. -/
structure AdvHopAsm {α : Type} (G₀ G₁ : SPComp α) (ε : ℝ≥0∞) : Prop where
  bound : ∀ A, AdvantageA G₀ G₁ A ≤ ε

/-- The hop lemma of `AdvHopAsm`. -/
theorem advHop_of {α : Type} {G₀ G₁ : SPComp α} {ε : ℝ≥0∞} (h : AdvHopAsm G₀ G₁ ε)
    (A : α → SPComp Bool) : AdvantageA G₀ G₁ A ≤ ε :=
  h.bound A

/-- A chain of a `∀ A` hypothesis and a hop passed as argument (the shape of
SPHINCSPlus/Reduction.lean:243 before the triangle step). -/
example {α : Type} (G₀ G₁ G₂ : SPComp α) (ε₁ ε₂ : ℝ≥0∞) (hd : AdvHopAsm G₁ G₂ ε₂)
    (h₁ : ∀ A, AdvantageA G₀ G₁ A ≤ ε₁) (A : α → SPComp Bool) :
    AdvantageA G₀ G₂ A ≤ ε₁ + ε₂ := by
  catcrypt_auto? [advHop_of hd]

/-! ## Hop leaves and arguments -/

/-- An `sdist` hop assumption packaged in a structure (the KEMTLS assumptions). -/
structure SdistHopAsm (G₀ G₁ : Unit → SPComp Bool) (ε : ℝ≥0∞) : Prop where
  bound : sdist G₀ G₁ ≤ ε

/-- The hop lemma of `SdistHopAsm` (`kemtls_hop1` and its siblings). -/
theorem sdistHop_of {G₀ G₁ : Unit → SPComp Bool} {ε : ℝ≥0∞} (h : SdistHopAsm G₀ G₁ ε) :
    sdist G₀ G₁ ≤ ε :=
  h.bound

-- The leaves of KEMTLS/Reduction.lean:161 without their hop lemmas: every arm
-- fails with an error naming the shape.
/--
error: catcrypt_auto: goal shape advantage/sdist inequality; every arm failed
-/
#guard_msgs (substring := true) in
example (R H₁ H₂ I : Unit → SPComp Bool) (e₁ e₂ e₃ : ℝ≥0∞) (h₁ : SdistHopAsm R H₁ e₁)
    (h₂ : SdistHopAsm H₁ H₂ e₂) (h₃ : SdistHopAsm H₂ I e₃) :
    sdist R H₁ + (sdist H₁ H₂ + sdist H₂ I) ≤ e₁ + (e₂ + e₃) := by
  catcrypt_auto

/-- The same goal with the hop lemmas as arguments. -/
example (R H₁ H₂ I : Unit → SPComp Bool) (e₁ e₂ e₃ : ℝ≥0∞) (h₁ : SdistHopAsm R H₁ e₁)
    (h₂ : SdistHopAsm H₁ H₂ e₂) (h₃ : SdistHopAsm H₂ I e₃) :
    sdist R H₁ + (sdist H₁ H₂ + sdist H₂ I) ≤ e₁ + (e₂ + e₃) := by
  catcrypt_auto? [sdistHop_of h₁, sdistHop_of h₂, sdistHop_of h₃]

-- The leaf of OEKE/Reduction.lean:201 without its hop lemma: `bound` is skipped
-- because `_h_ic` is a `∀`-quantified inequality, and the error names the shape.
/--
error: catcrypt_auto: goal shape advantage/sdist inequality; every arm failed
-/
#guard_msgs (substring := true) in
example {α : Type} (R H I : SPComp α) (e : ℝ≥0∞) (hd : AdvHopAsm R H e)
    (_h_ic : ∀ A : α → SPComp Bool, AdvantageA H I A ≤ e) (A : α → SPComp Bool) :
    AdvantageA R H A + AdvantageA H I A ≤ e + AdvantageA H I A := by
  catcrypt_auto

/-- The same goal with the hop lemma as argument. -/
example {α : Type} (R H I : SPComp α) (e : ℝ≥0∞) (hd : AdvHopAsm R H e)
    (_h_ic : ∀ A : α → SPComp Bool, AdvantageA H I A ≤ e) (A : α → SPComp Bool) :
    AdvantageA R H A + AdvantageA H I A ≤ e + AdvantageA H I A := by
  catcrypt_auto? [advHop_of hd A]

/-- The triangle step of OEKE/Reduction.lean:205 with `advantageA_triangle` as
argument. -/
example {α : Type} (H₁ H₂ I : SPComp α) (e : ℝ≥0∞) (A : α → SPComp Bool) :
    e + AdvantageA H₁ I A ≤ e + (AdvantageA H₁ H₂ A + AdvantageA H₂ I A) := by
  catcrypt_auto? [advantageA_triangle]

/-- The triangle step of KEMTLS/Reduction.lean:159 with `sdist_triangle` as
argument. -/
example (R H₁ H₂ I : Unit → SPComp Bool) :
    sdist R H₁ + sdist H₁ I ≤ sdist R H₁ + (sdist H₁ H₂ + sdist H₂ I) := by
  catcrypt_auto? [sdist_triangle]

/-- An argument reaches the `aesop` arm as `(add unsafe hf)`. -/
example {α β : Type} (a : α) (f : α → SPComp β) (hf : ∀ x, SPComp.NoFail (f x)) :
    SPComp.NoFail ((pure a : SPComp α) >>= f) := by
  catcrypt_auto? [hf]

/-! ## Monotonicity, `set` variables and heap disequalities -/

/-- The monotonicity goal of MuSig2/Reduction.lean:70 (`nrs21_bound_mono`) after
`unfold`. -/
example (qH qS qo : ℕ) (x y : ℝ≥0∞) (hab : x ≤ y) :
    ((qH + qS + 1) ^ 2 : ℕ) / (qo : ℝ≥0∞) * x ≤
      ((qH + qS + 1) ^ 2 : ℕ) / (qo : ℝ≥0∞) * y := by
  catcrypt_auto?

/-- The monotonicity goal of OEKE/Reduction.lean:292 (`oeke_dict_bound_mono`)
after `unfold`. -/
example {q₁ q₂ : ℕ} (hle : q₁ ≤ q₂) (d : ℕ) :
    (q₁ : ℝ≥0∞) / (d : ℝ≥0∞) ≤ (q₂ : ℝ≥0∞) / (d : ℝ≥0∞) := by
  catcrypt_auto?

/-- The step of UOV/Reduction.lean:102, whose `prTrue` terms are hidden behind
`set` variables. -/
example (G H : SPComp Bool) :
    prTrue G Heap.empty ≤ absDiff (prTrue G Heap.empty) (prTrue H Heap.empty) +
      prTrue H Heap.empty := by
  set C := prTrue G Heap.empty
  set H₁ := prTrue H Heap.empty
  have h₁ : C - H₁ ≤ absDiff C H₁ := le_sup_left (b := H₁ - C)
  calc C ≤ C - H₁ + H₁ := le_tsub_add
    _ ≤ absDiff C H₁ + H₁ := by catcrypt_auto?

/-- The flag location of the test below. -/
abbrev testFlagLoc : Location := ⟨0, Bool⟩

/-- The heap disequality under `some` of Crypto/PRPPRFSwitching.lean:410. -/
example {α : Type} (a b : α) (h' : Heap)
    (hbad : ¬ (fun h : Heap => h.get testFlagLoc = true) h') :
    some (b, h') ≠ some (a, Heap.empty.set testFlagLoc true) := by
  catcrypt_auto?

end CatCrypt.Tactics.AutoDispatchTest
