/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoDispatch
public meta import CatCryptCore.Tactics.AutoDispatch
public meta import CatCryptCore.Tactics.AutoArms

/-!
# Tests for `catcrypt_auto`

One example per shape of `CatCryptCore.Tactics.AutoDispatch`, a goal whose
shape is detected but whose arms fail, goals on which an arm exceeds its
heartbeat budget, and goals restated from game proofs: hop chains, hop leaves
whose lemma is passed as an argument, monotonicity goals, goals behind `set`,
heap disequalities under `some`, and the error on goals that stay open. The arms
`hop_chain`, `sum_atoms_le` and `gcongr_unfold` are tested on a distance and a
definition registered in this module, and a goal over an unregistered distance
is shown to be of shape `other`. Equalities of advantages are closed by
`advantage_eq_nf` from their two game equalities, including games built from definitions
with an implicit type parameter and instance arguments, given by name as arguments.
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

/-- A three-hop chain (the earlier hypothesis form of `cascade_prf_bound`), with the
birthday term abstracted to `b`: the `hop_chain` arm through `G 1` and `G 2`. -/
example {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool) (ε_prf b : ℝ≥0∞)
    (h01 : AdvantageA (G 0) (G 1) A ≤ ε_prf) (h12 : AdvantageA (G 1) (G 2) A ≤ b)
    (h23 : AdvantageA (G 2) (G 3) A ≤ ε_prf) :
    AdvantageA (G 0) (G 3) A ≤ 2 * ε_prf + b := by
  catcrypt_auto?

/-- A two-hop chain over `Advantage`. -/
example (G₀ G₁ G₂ : SPComp Bool) (ε : ℝ≥0∞) (h₁ : Advantage G₀ G₁ ≤ ε)
    (h₂ : Advantage G₁ G₂ ≤ ε) : Advantage G₀ G₂ ≤ 2 * ε := by
  catcrypt_auto?

/-- A hop bound for a fixed adversary packaged in a structure. -/
structure AdvHopAsm {α : Type} (G₀ G₁ : SPComp α) (A : α → SPComp Bool) (ε : ℝ≥0∞) :
    Prop where
  bound : AdvantageA G₀ G₁ A ≤ ε

/-- The hop lemma of `AdvHopAsm`. -/
theorem advHop_of {α : Type} {G₀ G₁ : SPComp α} {A : α → SPComp Bool} {ε : ℝ≥0∞}
    (h : AdvHopAsm G₀ G₁ A ε) : AdvantageA G₀ G₁ A ≤ ε :=
  h.bound

/-- A chain of a hop hypothesis and a hop passed as argument (the shape of
SPHINCSPlus/Reduction.lean:243 before the triangle step, for a fixed adversary). -/
example {α : Type} (G₀ G₁ G₂ : SPComp α) (ε₁ ε₂ : ℝ≥0∞) (A : α → SPComp Bool)
    (hd : AdvHopAsm G₁ G₂ A ε₂) (h₁ : AdvantageA G₀ G₁ A ≤ ε₁) :
    AdvantageA G₀ G₂ A ≤ ε₁ + ε₂ := by
  catcrypt_auto? [advHop_of hd]

-- The residual of SPHINCSPlus/Reduction.lean:243: `hop_chain` reaches
-- `ε₁ + ε₂ ≤ h * ε₁ + l * ε₂`, which is outside the fragment of `sum_atoms_le`;
-- every arm fails with an error naming the shape and the residual.
/--
error: catcrypt_auto: goal shape distance inequality; every arm failed
-/
#guard_msgs (substring := true) in
example {α : Type} (G₀ G₁ G₂ : SPComp α) (A : α → SPComp Bool) (ε₁ ε₂ : ℝ≥0∞) (h l : ℕ)
    (_hh : 1 ≤ h) (_hl : 1 ≤ l) (h₁ : AdvantageA G₀ G₁ A ≤ ε₁)
    (h₂ : AdvantageA G₁ G₂ A ≤ ε₂) :
    AdvantageA G₀ G₂ A ≤ h * ε₁ + l * ε₂ := by
  catcrypt_auto?

-- A hop given only as a hypothesis quantified over the adversary is not
-- instantiated by `hop_chain`: with the per-adversary bound `f B` the
-- `hop_chain` arm fails and the suggestion is a later arm.
/--
info: Try this:
  [apply] catcrypt_grind
-/
#guard_msgs (substring := true) in
example {α : Type} (G₀ G₁ : SPComp α) (A : α → SPComp Bool)
    (f : (α → SPComp Bool) → ℝ≥0∞) (hB : ∀ B, AdvantageA G₀ G₁ B ≤ f B) :
    AdvantageA G₀ G₁ A ≤ f A := by
  catcrypt_auto?

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
error: catcrypt_auto: goal shape distance inequality; every arm failed
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
-- because `_h_q` is a `∀`-quantified inequality, and the error names the shape.
/--
error: catcrypt_auto: goal shape distance inequality; every arm failed
-/
#guard_msgs (substring := true) in
example {α : Type} (R H I : SPComp α) (e : ℝ≥0∞) (A : α → SPComp Bool)
    (hd : AdvHopAsm R H A e) (_h_q : ∀ n : ℕ, (n : ℝ≥0∞) * 0 ≤ e) :
    AdvantageA R H A + AdvantageA H I A ≤ e + AdvantageA H I A := by
  catcrypt_auto

/-- The same goal with the hop lemma as argument. -/
example {α : Type} (R H I : SPComp α) (e : ℝ≥0∞) (A : α → SPComp Bool)
    (hd : AdvHopAsm R H A e) (_h_q : ∀ n : ℕ, (n : ℝ≥0∞) * 0 ≤ e) :
    AdvantageA R H A + AdvantageA H I A ≤ e + AdvantageA H I A := by
  catcrypt_auto? [advHop_of hd]

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

/-! ## Arms over a registered test distance -/

/-- A pseudometric on `X` with values in `ℝ≥0∞`. -/
structure TestMetric (X : Type) where
  /-- The distance. -/
  d : X → X → ℝ≥0∞
  /-- Triangle inequality. -/
  tri : ∀ x y z, d x z ≤ d x y + d y z
  /-- Symmetry. -/
  symm : ∀ x y, d x y = d y x

/-- The triangle inequality of a `TestMetric`, stated on the distance. -/
@[hop_metric] theorem TestMetric.d_triangle {X : Type} (M : TestMetric X) (x y z : X) :
    M.d x z ≤ M.d x y + M.d y z := M.tri x y z

/-- The symmetry of a `TestMetric`, stated on the distance. -/
@[hop_metric] theorem TestMetric.d_symm {X : Type} (M : TestMetric X) (x y : X) :
    M.d x y = M.d y x := M.symm x y

/-- A distance-valued definition registered for unfolding. -/
@[hop_metric] noncomputable def testAdv {X : Type} (M : TestMetric X) (x y : X) : ℝ≥0∞ :=
  M.d x y

/-- A hop bound packaged in a structure. -/
structure TestHop {X : Type} (M : TestMetric X) (x y : X) (ε : ℝ≥0∞) : Prop where
  bound : M.d x y ≤ ε

/-- The hop lemma of `TestHop`. -/
theorem testHop_of {X : Type} {M : TestMetric X} {x y : X} {ε : ℝ≥0∞}
    (h : TestHop M x y ε) : M.d x y ≤ ε :=
  h.bound

-- The `hop_chain` arm, one hop used backwards through the registered symmetry.
/--
info: Try this:
  [apply] hop_chain
-/
#guard_msgs (substring := true) in
example {X : Type} (M : TestMetric X) (a b c : X) (e₁ e₂ : ℝ≥0∞)
    (h₁ : M.d a b ≤ e₁) (h₂ : M.d c b ≤ e₂) : M.d a c ≤ e₂ + e₁ := by
  catcrypt_auto?

-- The `hop_chain` arm with a hop passed as argument; the quantified argument
-- `M.tri` is not passed to `hop_chain`.
/--
info: Try this:
  [apply] hop_chain [testHop_of h₂]
-/
#guard_msgs (substring := true) in
example {X : Type} (M : TestMetric X) (a b c : X) (e₁ e₂ : ℝ≥0∞)
    (h₁ : M.d a b ≤ e₁) (h₂ : TestHop M b c e₂) : M.d a c ≤ 2 * e₁ + e₂ := by
  catcrypt_auto? [testHop_of h₂, M.tri]

-- The `hop_chain` arm on a registered definition, read by unfolding.
/--
info: Try this:
  [apply] hop_chain
-/
#guard_msgs (substring := true) in
example {X : Type} (M : TestMetric X) (a b c : X) (e₁ e₂ : ℝ≥0∞)
    (h₁ : testAdv M a b ≤ e₁) (h₂ : testAdv M b c = e₂) : testAdv M a c ≤ e₁ + e₂ := by
  catcrypt_auto?

-- The `sum_atoms_le` arm on a sum of distances.
/--
info: Try this:
  [apply] sum_atoms_le
-/
#guard_msgs (substring := true) in
example {X : Type} (M : TestMetric X) (a b c d : X) (e₁ e₂ f : ℝ≥0∞)
    (h₁ : M.d a b ≤ e₁) (h₂ : M.d c d ≤ e₂) : M.d a b + M.d c d ≤ e₂ + f + e₁ := by
  catcrypt_auto?

-- Without a path the error reports the failure of `hop_chain`.
/--
hop_chain: no chain of hop facts
-/
#guard_msgs (substring := true) in
example {X : Type} (M : TestMetric X) (a b c : X) (e₁ : ℝ≥0∞) (h₁ : M.d a b ≤ e₁) :
    M.d a c ≤ e₁ := by
  catcrypt_auto

/-- A distance whose triangle lemma is not registered. -/
noncomputable def unregDist {X : Type} (δ : X → X → ℝ≥0∞) (x y : X) : ℝ≥0∞ := δ x y

-- A goal over the unregistered `unregDist` is of shape `other`; no arm closes it.
/--
error: catcrypt_auto: goal shape other; every arm failed
-/
#guard_msgs (substring := true) in
example {X : Type} (δ : X → X → ℝ≥0∞) (a b c : X) (e₁ e₂ : ℝ≥0∞)
    (h₁ : unregDist δ a b ≤ e₁) (h₂ : unregDist δ b c ≤ e₂) :
    unregDist δ a c ≤ e₁ + e₂ := by
  catcrypt_auto

/-- A scaled bound `c * x`. -/
noncomputable def testScaled (c x : ℝ≥0∞) : ℝ≥0∞ := c * x

-- The `gcongr_unfold` arm on `Monotone`, with the definition as argument.
/--
info: Try this:
  [apply] gcongr_unfold [testScaled]
-/
#guard_msgs (substring := true) in
example (c : ℝ≥0∞) : Monotone (testScaled c) := by
  catcrypt_auto? [testScaled]

-- The `gcongr_unfold` arm on the same head on both sides.
/--
info: Try this:
  [apply] gcongr_unfold [testScaled]
-/
#guard_msgs (substring := true) in
example (c x y : ℝ≥0∞) (h : x ≤ y) : testScaled c x ≤ testScaled c y := by
  catcrypt_auto? [testScaled]

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

/-! ## Argument handling -/

-- A local hypothesis among the arguments does not reach `grind`, which rejects it
-- as a redundant parameter.
/--
info: Try this:
  [apply] grind [CatCrypt.Core.Heap.get_set_same, CatCrypt.Core.Heap.get_set_other]
-/
#guard_msgs (substring := true) in
example (h₁ : Heap) (l l' : Location) (v : l.ty) (b : l'.ty) (hid : l.id ≠ l'.id)
    (hset : Heap.get h₁ l' = b) : Heap.get (h₁.set l v) l' = b := by
  catcrypt_auto? [hset]

-- An applied hypothesis reaches `aesop` as one rule, in parentheses.
/--
(add unsafe (hf a))
-/
#guard_msgs (substring := true) in
example {α β : Type} (a : α) (f : α → SPComp β) (hf : ∀ x, SPComp.NoFail (f x)) :
    SPComp.NoFail ((pure a : SPComp α) >>= f) := by
  catcrypt_auto? [hf a]

-- A term with a hole is elaborated against the goal by `exact`.
/--
info: Try this:
  [apply] exact hPQ _ h
-/
#guard_msgs (substring := true) in
example (P Q : ℕ → Prop) (hPQ : ∀ n, P n → Q n) (h : P 3) : Q 3 := by
  catcrypt_auto? [hPQ _ h]

-- A lemma whose type class arguments stay stuck without an expected type is a
-- proof, passed to `simp_all` as a lemma argument.
/--
info: Try this:
  [apply] simp_all [mul_comm]
-/
#guard_msgs (substring := true) in
example (a b : ℕ) (h : a * b = 5) : b * a = 5 := by
  catcrypt_auto? [mul_comm]

/-- A game given as a definition. -/
noncomputable def testGame : SPComp Bool := do
  let a ← SPComp.sample Bool
  let b ← SPComp.sample Bool
  pure (a && b)

-- A definition among the arguments is unfolded, not added to `aesop`.
/--
info: Try this:
  [apply] (unfold CatCrypt.Tactics.AutoDispatchTest.testGame;
-/
#guard_msgs (substring := true) in
example : SPComp.IsPure testGame := by
  catcrypt_auto? [testGame]

/-! ## Unfolding -/

/-- A predicate given as a definition. -/
def testInv (x : ℕ) : Prop := x + 0 = x

-- The head of a goal of shape `other` is unfolded before the shape is read.
/--
info: Try this:
  [apply] (unfold CatCrypt.Tactics.AutoDispatchTest.testInv; simp_all)
-/
#guard_msgs (substring := true) in
example : testInv 3 := by
  catcrypt_auto?

-- The game under `IsPure` is unfolded once every arm fails on the folded goal.
/--
info: Try this:
  [apply] (unfold CatCrypt.Tactics.AutoDispatchTest.testGame;
-/
#guard_msgs (substring := true) in
example : SPComp.IsPure testGame := by
  catcrypt_auto?

/-! ## Sums of atoms outside the distance shape -/

-- `sum_atoms_le` runs on a `≤` goal of shape `other`.
/--
info: Try this:
  [apply] sum_atoms_le
-/
#guard_msgs (substring := true) in
example (c S r : ℝ≥0∞) : c * S ≤ r + c * S := by
  catcrypt_auto?

-- The hop chain of a hybrid argument whose bound is a sum over `range (k + 1)`
-- (Crypto/HybridArgument.lean:85): the residual is read after expanding the sum.
/--
info: Try this:
  [apply] hop_chain
-/
#guard_msgs (substring := true) in
example {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool) (ε : ℕ → ℝ≥0∞) (k : ℕ)
    (ih : AdvantageA (G 0) (G k) A ≤ ∑ i ∈ Finset.range k, ε i)
    (hk : AdvantageA (G k) (G (k + 1)) A ≤ ε k) :
    AdvantageA (G 0) (G (k + 1)) A ≤ ∑ i ∈ Finset.range (k + 1), ε i := by
  catcrypt_auto?

/-! ## `set` equations -/

-- `hm` and `_hn` rewrite into each other and `simp_all` reaches the maximum
-- recursion depth; the `simp_all` arm runs after `clear hm`.
/--
info: Try this:
  [apply] (clear hm; simp_all)
-/
#guard_msgs (substring := true) in
example (n : ℕ) (h : n = 3) : n + 1 = 4 := by
  set m := n + 1 with hm
  have _hn : n = m - 1 := by omega
  catcrypt_auto?

/-! ## Commutation of independent binds and sums in any order -/

/-- Abstract dependencies: a key generation with its `IsPure` field. -/
structure SwapDeps (K : Type) where
  /-- Key generation. -/
  keygen : SPComp (K × K)
  /-- Key generation does not touch the heap. -/
  keygen_isPure : SPComp.IsPure keygen

-- Two key generations and a sample exchanged around an adversary call.
/--
info: Try this:
  [apply] bind_swap_nf
-/
#guard_msgs (substring := true) in
example {K : Type} [Fintype K] [Nonempty K] (d : SwapDeps K) (adv : SPComp K)
    (A : K → K → K → K → SPComp Bool) :
    d.keygen.bind (fun ka => (SPComp.sample K).bind (fun s => adv.bind (fun x =>
      d.keygen.bind (fun kb => A ka.2 kb.2 s x)))) =
    adv.bind (fun x => d.keygen.bind (fun kb => (SPComp.sample K).bind (fun s =>
      d.keygen.bind (fun ka => A ka.2 kb.2 s x)))) := by
  catcrypt_auto?

-- A hypothesis bounding an atom by a sum whose summands appear in another order.
/--
info: Try this:
  [apply] sum_atoms_le
-/
#guard_msgs (substring := true) in
example (x y z : ℝ≥0∞) (h : x ≤ y + z) : x ≤ z + y := by
  catcrypt_auto?

/-- Advantage equality: the games are exchanged by `Advantage_sym` and equal up to the
order of independent bindings. -/
example {α β : Type} (p : SPComp α) (q : SPComp β) (k : α → β → SPComp Bool)
    (hp : SPComp.IsPure p) (G : SPComp Bool) :
    Advantage (p.bind fun a => q.bind fun b => k a b) G =
      Advantage G (q.bind fun b => p.bind fun a => k a b) := by
  catcrypt_auto

/-- Advantage equality with `AdvantageA` unfolded on one side. -/
example {α β : Type} (p : SPComp α) (q : SPComp β) (A : α × β → SPComp Bool)
    (hp : SPComp.IsPure p) (G : SPComp (α × β)) :
    AdvantageA (p.bind fun a => q.bind fun b => SPComp.pure (a, b)) G A =
      Advantage (q.bind fun b => p.bind fun a => A (a, b)) (G.bind A) := by
  advantage_eq_nf

/-- Advantage equality with an unused uniform sample removed (`lossless_sample`). -/
example {α : Type} [Fintype α] [Nonempty α] (q : SPComp Bool) (G : SPComp Bool) :
    Advantage ((SPComp.sample α).bind fun _ => q) G = Advantage q G := by
  advantage_eq_nf

/-- A game over a word type `W` given by an implicit parameter and instance arguments. -/
noncomputable def advReal {W : Type} [Fintype W] [Nonempty W] (p : SPComp W)
    (A : W → W → SPComp Bool) : SPComp Bool :=
  p.bind fun a => (SPComp.sample W).bind fun b => A a b

/-- The game `advReal` with its two bindings exchanged. -/
noncomputable def advSwap {W : Type} [Fintype W] [Nonempty W] (p : SPComp W)
    (A : W → W → SPComp Bool) : SPComp Bool :=
  (SPComp.sample W).bind fun b => p.bind fun a => A a b

/-- Advantage equality whose games use `advReal` and `advSwap` under a binder: the
definitions given as arguments are unfolded by name, without `(W := W)`. -/
example {W : Type} [Fintype W] [Nonempty W] (p q : SPComp W) (A : W → W → W → SPComp Bool)
    (G : SPComp Bool) :
    Advantage (q.bind fun x => advReal p (A x)) G =
      Advantage G (q.bind fun x => advSwap p (A x)) := by
  fail_if_success advantage_eq_nf
  advantage_eq_nf [advReal, advSwap]

end CatCrypt.Tactics.AutoDispatchTest
