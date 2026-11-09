/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveCsimp

/-!
# Tests for `derive_csimp`

One instance per stage on toy definitions: `eq` (a doubling, whose cost is registered as the
derived cost of its implementation), `guard` (a remainder below the modulus), `wrap`
(multiplication in `Fin 7` through `ℕ` with a decoding modulo `7`), `wrapR` (addition in `Fin 7`
through `Fin.val`), `transfer` followed by `eq`, `bounded` (the least `k` with `n ≤ k * k`, a
`noncomputable` definition with a computable caller) and `unique` (the value of a key in an
association list, with a computable caller; its cost derivation is refused and reported). Each
refusal of the command is checked by its message, and so are the warning on a caller compiled
before the replacement and the warning on an auxiliary axiom of `native_decide` in the
definition of the specification.
-/

public section

set_option autoImplicit false

namespace DeriveCsimpTest

open CatCrypt.Tactics.DeriveCsimp

/-! ## `eq` -/

/-- Specification of a doubling. -/
def specDouble (n : ℕ) : ℕ := n + n

/-- Implementation of the doubling. -/
def implDouble (n : ℕ) : ℕ := 2 * n

/-- The implementation computes the doubling. -/
theorem implDouble_eq (n : ℕ) : implDouble n = specDouble n := by
  unfold implDouble specDouble
  omega

derive_csimp specDouble via eq implDouble_eq

example : @specDouble = @specDouble.csimpImpl := specDouble_csimp

example : specDouble.timedCost = specDouble.csimpImpl.timedCost := rfl

/-! ## `guard` -/

/-- Specification of the remainder. -/
def modSpec (a b : ℕ) : ℕ := a % b

/-- The remainder computed by division. -/
theorem modSpec_sub (a b : ℕ) : a - b * (a / b) = modSpec a b := by
  unfold modSpec
  grind [Nat.mod_def]

derive_csimp modSpec via guard Nat.mod_eq_of_lt fallback modSpec_sub

example (a b : ℕ) : modSpec.csimpImpl a b = if a < b then a else a - b * (a / b) := rfl

/-! ## `wrap` -/

/-- Decoding of a natural number into `Fin 7`. -/
def dec7 (n : ℕ) : Fin 7 := ⟨n % 7, Nat.mod_lt _ (by decide)⟩

/-- Multiplication modulo `7` on `ℕ`. -/
def mul7 (x y : ℕ) : ℕ := x * y % 7

/-- `mul7` is a homomorphism along `dec7` on the numbers below `7`. -/
theorem mul7_hom (x y : ℕ) (_hx : x < 7) (_hy : y < 7) :
    dec7 (mul7 x y) = dec7 x * dec7 y := by
  apply Fin.ext
  simp [dec7, mul7, Fin.mul_def, Nat.mul_mod]

/-- The encoding of `Fin 7` lies below `7`. -/
theorem val_lt7 (a : Fin 7) : a.val < 7 := a.isLt

/-- `dec7` decodes the encoding. -/
theorem dec7_val (a : Fin 7) : dec7 a.val = a := by
  apply Fin.ext
  simp [dec7, Nat.mod_eq_of_lt a.isLt]

/-- Specification of multiplication in `Fin 7`. -/
def mulSpec (a b : Fin 7) : Fin 7 := a * b

derive_csimp mulSpec via wrap mul7_hom using val_lt7, dec7_val

example (a b : Fin 7) : mulSpec.csimpImpl a b = dec7 (mul7 a.val b.val) := rfl

/-! ## `wrapR` -/

/-- Specification of addition in `Fin 7`. -/
def addSpec (a b : Fin 7) : Fin 7 := a + b

derive_csimp addSpec via wrapR Fin.val_add using dec7_val

example (a b : Fin 7) : addSpec.csimpImpl a b = dec7 ((a.val + b.val) % 7) := rfl

/-! ## `transfer` followed by `eq` -/

/-- A doubling stated with a redundant `+ 0`. -/
def specDouble0 (n : ℕ) : ℕ := (n + 0) + (n + 0)

derive_csimp specDouble0 via transfer [Nat.add_zero], eq implDouble_eq

example (n : ℕ) : specDouble0.csimpImpl n = implDouble n := rfl

/-! ## `bounded` -/

/-- The least `k` with `n ≤ k * k`, decided classically. -/
noncomputable def leastSq (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, n ≤ k * k then Nat.find h else 0

/-- Every witness of `leastSq` is dominated by the witness `n`. -/
theorem leastSq_bound (n k : ℕ) (_ : n ≤ k * k) : ∃ j, j ≤ n ∧ n ≤ j * j :=
  ⟨n, le_refl n, Nat.le_mul_self n⟩

derive_csimp leastSq via bounded leastSq_bound

/-- A computable caller of the `noncomputable` `leastSq`. -/
def leastSqCaller (n : ℕ) : ℕ := leastSq n + 1

/-! ## `unique` -/

/-- The value of the key `k` in `L` when it is unique. -/
noncomputable def lookup (L : List (ℕ × ℕ)) (k : ℕ) : Option ℕ := by
  classical
  exact if h : ∃! v, (k, v) ∈ L then some h.exists.choose else none

/-- The values of `L` contain every value of `k`. -/
theorem lookup_mem (L : List (ℕ × ℕ)) (k v : ℕ) (h : (k, v) ∈ L) : v ∈ L.map Prod.snd :=
  List.mem_map.2 ⟨(k, v), h, rfl⟩

/--
info: derive_csimp DeriveCsimpTest.lookup: no cost registered; `derive_cost DeriveCsimpTest.lookup.csimpImpl` was refused: derive_timed: the cost `List.elem.timedCost` takes the cost of the method `BEq.beq` of the instance `instBEqProd`, which is not a field of a binder of the reduction, and the method is not priced (rule (k)):
  derive_timed: needs a registered primitive: `Bool.not` unfolds deeper than 16 definitions (option `derive_timed.maxDepth`)
-/
#guard_msgs in
derive_csimp lookup via unique lookup_mem

/-- A computable caller of the `noncomputable` `lookup`. -/
def lookupCaller (L : List (ℕ × ℕ)) (k : ℕ) : ℕ := (lookup L k).getD 0

/-! ## Refusals -/

/-- Specification for the refusals. -/
def modSpec2 (a b : ℕ) : ℕ := a % b

/--
error: derive_csimp DeriveCsimpTest.modSpec2: `Nat.mod_eq_of_lt` is conditional on `a <
  b` and no total encoding into it was found; supply `wrap Nat.mod_eq_of_lt using he, hd` with `he : ∀ a, D (e a)` and `hd : ∀ a, φ (e a) = a`, or `guard Nat.mod_eq_of_lt fallback R` with a decision procedure for the condition and a computable fallback `R : ∀ x, r x = DeriveCsimpTest.modSpec2 x`.
-/
#guard_msgs in
derive_csimp modSpec2 via eq Nat.mod_eq_of_lt

/-- Specification for the refusal of `wrapR` without a decoder. -/
def addSpec2 (a b : Fin 7) : Fin 7 := a + b

/--
error: derive_csimp DeriveCsimpTest.addSpec2: `Fin.val_add` gives an injective encoding but no decoder; supply `wrapR Fin.val_add using hd` with a computable `d` and `hd : ∀ a, d (enc a) = a`.
-/
#guard_msgs in
derive_csimp addSpec2 via wrapR Fin.val_add

/-- The unique witness of `p` in a type without decidable equality. -/
noncomputable def pick {α : Type} (p : α → Prop) (_L : List α) : Option α := by
  classical
  exact if h : ∃! a, p a then some h.exists.choose else none

/-- The witnesses of `p` lie in `L` (a hypothesis). -/
theorem pick_mem {α : Type} (p : α → Prop) (L : List α) (h : ∀ a, p a → a ∈ L) (a : α)
    (ha : p a) : a ∈ L := h a ha

/--
error: derive_csimp DeriveCsimpTest.pick: `DeriveCsimpTest.pick.csimpImpl` needs the instance `[DecidableEq
  α]` that `DeriveCsimpTest.pick` does not take; a csimp replacement keeps the type of `DeriveCsimpTest.pick` including its instance arguments. Install it at a monomorphic constant, or add the binder to `DeriveCsimpTest.pick`.
-/
#guard_msgs in
derive_csimp pick via unique pick_mem

/-- A classical constant used by a refused implementation. -/
noncomputable def classicalOne (n : ℕ) : ℕ := by
  classical
  exact if ∃ k, n < k then 1 else 0

/-- Specification of the refusal of a classical implementation. -/
def one (_n : ℕ) : ℕ := 1

/-- `classicalOne` is `1`. -/
theorem classicalOne_eq (n : ℕ) : classicalOne n = one n := by
  unfold classicalOne one
  simp [show ∃ k, n < k from ⟨n + 1, Nat.lt_succ_self n⟩]

/--
error: derive_csimp DeriveCsimpTest.one: `DeriveCsimpTest.one.csimpImpl` is not computable: `classicalOne
  _n` uses `DeriveCsimpTest.classicalOne` (noncomputable, no csimp, implemented_by or extern).
-/
#guard_msgs in
derive_csimp one via eq classicalOne_eq

/-- A choice of a witness that is not unique. -/
noncomputable def anyAbove (n : ℕ) : ℕ := (⟨n + 1, Nat.lt_succ_self n⟩ : ∃ k, n < k).choose

/--
error: derive_csimp DeriveCsimpTest.anyAbove: `DeriveCsimpTest.anyAbove` is defined by a choice whose witness is not determined (`Classical.choose` of a non-unique existential): no computable function provably equals it.
-/
#guard_msgs in
derive_csimp anyAbove via unique lookup_mem

/--
error: derive_csimp DeriveCsimpTest.leastSq: bounded: no bound given; prove `∀ x k, P x k → ∃ j ≤ b x, P x j` for a computable `b`.
-/
#guard_msgs in
derive_csimp leastSq via bounded

/-- An axiom outside the standard three. -/
axiom tripleAxiom : ∀ n : ℕ, 3 * n = n + n + n

/-- Specification of the refusal of an axiom. -/
def specTriple (n : ℕ) : ℕ := n + n + n

/--
error: derive_csimp DeriveCsimpTest.specTriple: the proof of `DeriveCsimpTest.specTriple_csimp` depends on the axiom `DeriveCsimpTest.tripleAxiom`; a csimp theorem is not recorded in the axioms of its callers, so it may use only `propext`, `Classical.choice` and `Quot.sound`.
-/
#guard_msgs in
derive_csimp specTriple via eq tripleAxiom

/-- A doubling whose definition carries a proof by the axiom `tripleAxiom`. -/
def specAxDouble (n : ℕ) : ℕ := (⟨n + n, tripleAxiom n⟩ : {_m : ℕ // 3 * n = n + n + n}).val

/--
error: derive_csimp DeriveCsimpTest.specAxDouble: the definition of `DeriveCsimpTest.specAxDouble` depends on the axiom `DeriveCsimpTest.tripleAxiom`, and so does the statement `@DeriveCsimpTest.specAxDouble = @DeriveCsimpTest.specAxDouble.csimpImpl` of `DeriveCsimpTest.specAxDouble_csimp`; a csimp theorem may use only `propext`, `Classical.choice` and `Quot.sound`.
-/
#guard_msgs in
derive_csimp specAxDouble via eq Nat.two_mul

/--
error: derive_csimp DeriveCsimpTest.modSpec2: guard: no fallback given; supply `guard Nat.mod_eq_of_lt fallback R` with a computable `r` and `R : ∀ x, r x = DeriveCsimpTest.modSpec2 x`.
-/
#guard_msgs in
derive_csimp modSpec2 via guard Nat.mod_eq_of_lt

/-! ## An auxiliary axiom of `native_decide` -/

set_option linter.style.native false in
/-- A doubling whose definition carries a proof by `native_decide`. -/
def specNdDouble (n : ℕ) : ℕ :=
  (⟨n + n, (by native_decide : 2 + 2 = 4)⟩ : {_m : ℕ // 2 + 2 = 4}).val

/--
warning: derive_csimp DeriveCsimpTest.specNdDouble: `DeriveCsimpTest.specNdDouble_csimp` depends on the axioms [_private.CatCryptCoreTest.Tactics.DeriveCsimpTest.0.DeriveCsimpTest.specNdDouble._native.native_decide.ax_1] of `native_decide`, which trust the compiled evaluation of a Boolean term; the axioms of compiled callers of `DeriveCsimpTest.specNdDouble` do not record them.
-/
#guard_msgs (warning, drop info) in
derive_csimp specNdDouble via eq Nat.two_mul

example : @specNdDouble = @specNdDouble.csimpImpl := specNdDouble_csimp

/-! ## Callers compiled before the replacement -/

/-- Specification with a caller compiled before the replacement. -/
def specQuad (n : ℕ) : ℕ := n + n + n + n

/-- A caller of `specQuad` compiled before the replacement. -/
def quadCaller (n : ℕ) : ℕ := specQuad n + 1

/-- The implementation of `specQuad`. -/
theorem quad_eq (n : ℕ) : 4 * n = specQuad n := by
  unfold specQuad
  omega

/--
warning: derive_csimp DeriveCsimpTest.specQuad: `DeriveCsimpTest.specQuad` has compiled callers earlier in this module ([DeriveCsimpTest.quadCaller]); they keep the code of `DeriveCsimpTest.specQuad`.
-/
#guard_msgs in
derive_csimp specQuad via eq quad_eq

end DeriveCsimpTest

end
