/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.StdCosts

/-!
# Tests for instance methods as cost companions

Rule (k) of `CatCryptCore.Tactics.DeriveTimed`: a callee whose cost takes the cost companion of a
method of its instance argument, called at an instance that is not a field of a binder, receives
the cost of that method as derived. The callees are fresh copies of `List.lookup` and `List.elem`
derived without a unit listing, so that their costs take the companion of `BEq.beq`; the costs
of `List.lookup` and `List.elem` registered in `CatCryptCore.Tactics.StdCosts` charge `BEq.beq`
one unit and take none.

* a lazily sampled table handler whose lookup is at a natural-number key (a global instance), at
  a key type with `deriving DecidableEq` (a structure, and a recursive type), and at a
  `[DecidableEq K]` binder, which receives the cost companion of its equality test;
* a reduction that simulates an adversary with the handler at a binder key, which passes its own
  companion, and at a natural-number key, where the decision procedure `instDecidableEqNat`
  passed for the binder of the handler is priced by its registered cost;
* a membership test in a condition priced under `derive_timed.priceProps`, at the same keys; and
  the membership `x ∈ l`, priced by the registered cost of `List.elem`, outside the class;
* the refusal of a `BEq` instance whose method is an opaque function.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedInstCostTest

open CatCrypt.Crypto

/-- A key of two fields with a derived decision of equality. -/
structure Key where
  n : ℕ
  b : Bool
  deriving DecidableEq

/-- A binary shape with a derived decision of equality by recursion. -/
inductive Shape where
  | leaf
  | node (l r : Shape)
  deriving DecidableEq

/-- The value recorded at the key `a` in the table (a copy of `List.lookup`). -/
def findKey {α β : Type} [BEq α] (a : α) : List (α × β) → Option β
  | [] => none
  | (k, v) :: r => if a == k then some v else findKey a r

derive_cost findKey

/-- The cost of the lookup takes the cost companion of the comparison of keys. -/
noncomputable example {α β : Type} [BEq α] (a : α) (l : List (α × β)) (beqCost : α → α → ℕ) : ℕ :=
  findKey.timedCost a l beqCost

/-- The lookup costs at most `k + 4` per entry and one more, for comparisons of cost at most
`k`. -/
theorem findKey.timedCost_le {α β : Type} [BEq α] (a : α) (l : List (α × β))
    (c : α → α → ℕ) {k : ℕ} (hc : ∀ x y, c x y ≤ k) :
    findKey.timedCost a l c ≤ (k + 4) * l.length + 1 := by
  induction l with
  | nil => simp [findKey.timedCost]
  | cons p l ih =>
    obtain ⟨k', v⟩ := p
    have := hc a k'
    simp only [findKey.timedCost, List.length_cons]
    split <;> nlinarith

/-! ### A lazily sampled table at three key types -/

/-- A lazily sampled table at natural-number keys: a recorded key returns its value, a new key
draws a uniform bit and records it. -/
noncomputable def lazyNat (t : List (ℕ × Bool)) (x : ℕ) :
    OracleAdv ℕ Bool (Bool × List (ℕ × Bool)) :=
  match findKey x t with
  | some v => .ret (v, t)
  | none => .rand (PMF.uniformFintype Bool) fun v => .ret (v, (x, v) :: t)

derive_timed lazyNat

example (t : List (ℕ × Bool)) (x : ℕ) : (lazyNat.timed t x).2.erase = lazyNat t x :=
  lazyNat.erase_timed t x

/-- A comparison of natural numbers is the method `decide (a = b)` of `instBEqOfDecidableEq`, its
decision `instDecidableEqNat a b` at its registered cost: two units in all. -/
example (t : List (ℕ × Bool)) (x : ℕ) :
    (lazyNat.timed t x).1 = 2 + findKey.timedCost x t (fun _ _ => 2) := by
  simp only [lazyNat.timed, OracleAdv.Timed.delay, instDecidableEqNat.timedCost_eq, Nat.add_zero]
  split <;> rfl

example (t : List (ℕ × Bool)) (x : ℕ) : (lazyNat.timed t x).1 ≤ 6 * t.length + 3 := by
  have := findKey.timedCost_le x t (fun _ _ => 2) (k := 2) (fun _ _ => le_rfl)
  rw [show (lazyNat.timed t x).1 = 2 + findKey.timedCost x t (fun _ _ => 2) by
    simp only [lazyNat.timed, OracleAdv.Timed.delay, instDecidableEqNat.timedCost_eq,
      Nat.add_zero]
    split <;> rfl]
  omega

/-- The same table at keys of a structure with a derived decision of equality. -/
noncomputable def lazyKey (t : List (Key × Bool)) (x : Key) :
    OracleAdv Key Bool (Bool × List (Key × Bool)) :=
  match findKey x t with
  | some v => .ret (v, t)
  | none => .rand (PMF.uniformFintype Bool) fun v => .ret (v, (x, v) :: t)

derive_timed lazyKey

example (t : List (Key × Bool)) (x : Key) : (lazyKey.timed t x).2.erase = lazyKey t x :=
  lazyKey.erase_timed t x

/-- The derived decision of `Key` decides its fields in turn, `ℕ` then `Bool`, each at its
registered cost: a comparison of keys costs at most eight units. -/
example (t : List (Key × Bool)) (x : Key) : (lazyKey.timed t x).1 ≤ 12 * t.length + 3 := by
  simp only [lazyKey.timed, OracleAdv.Timed.delay]
  split <;> simp only [Nat.add_zero] <;>
  · refine le_trans (Nat.add_le_add_left
      (findKey.timedCost_le x t _ (k := 8) fun a b => ?_) 2) (by omega)
    obtain ⟨n, b₁⟩ := a
    obtain ⟨m, b₂⟩ := b
    simp only [instDecidableEqNat.timedCost_eq, instDecidableEqBool.timedCost_eq]
    (try split) <;> (try split) <;> omega

/-- The same table at keys of a recursive type with a derived decision of equality. -/
noncomputable def lazyShape (t : List (Shape × Bool)) (x : Shape) :
    OracleAdv Shape Bool (Bool × List (Shape × Bool)) :=
  match findKey x t with
  | some v => .ret (v, t)
  | none => .rand (PMF.uniformFintype Bool) fun v => .ret (v, (x, v) :: t)

derive_timed lazyShape

example (t : List (Shape × Bool)) (x : Shape) :
    (lazyShape.timed t x).2.erase = lazyShape t x :=
  lazyShape.erase_timed t x

/-- The same table at keys of a `[DecidableEq K]` binder: the costed form takes the cost
companion `instCost` of the equality test after its binders. -/
noncomputable def lazyBind {K : Type} [DecidableEq K] (t : List (K × Bool)) (x : K) :
    OracleAdv K Bool (Bool × List (K × Bool)) :=
  match findKey x t with
  | some v => .ret (v, t)
  | none => .rand (PMF.uniformFintype Bool) fun v => .ret (v, (x, v) :: t)

derive_timed lazyBind

example {K : Type} [DecidableEq K] (t : List (K × Bool)) (x : K) (instCost : K → K → ℕ) :
    (lazyBind.timed t x instCost).2.erase = lazyBind t x :=
  lazyBind.erase_timed t x instCost

/-- A comparison of keys costs the companion of the binder plus two units. -/
example {K : Type} [DecidableEq K] (t : List (K × Bool)) (x : K) (instCost : K → K → ℕ) :
    (lazyBind.timed t x instCost).1 = 2 + findKey.timedCost x t (fun a b => 2 + instCost a b) := by
  simp only [lazyBind.timed, OracleAdv.Timed.delay]
  split <;> rfl

/-- A bound on the companion of the binder bounds the step cost of the handler. -/
example {K : Type} [DecidableEq K] (t : List (K × Bool)) (x : K) (instCost : K → K → ℕ)
    {k : ℕ} (hk : ∀ a b, instCost a b ≤ k) :
    (lazyBind.timed t x instCost).1 ≤ (k + 6) * t.length + 3 := by
  have := findKey.timedCost_le x t (fun a b => 2 + instCost a b) (k := k + 2)
    fun a b => by have := hk a b; omega
  simp only [lazyBind.timed, OracleAdv.Timed.delay]
  split <;> simp only [Nat.add_zero] <;> nlinarith

/-! ### Reductions over the handler -/

/-- The adversary `A` against the lazily sampled table at a binder key. -/
noncomputable def redBind {K : Type} [DecidableEq K] (A : OracleAdv K Bool Bool) :
    OracleAdv K Bool Bool :=
  (OracleAdv.simulate lazyBind A []).bind fun y => .ret y.1

derive_timed redBind

/-- The reduction passes its own companion for the binder of the handler. -/
example {K : Type} [DecidableEq K] (A : OracleAdv.Timed K Bool Bool) (instCost : K → K → ℕ) :
    (redBind.timed A instCost).2.erase = redBind A.erase :=
  redBind.erase_timed A instCost

/-- The adversary `A` against the lazily sampled table at natural-number keys, through the
handler generic in its key type. -/
noncomputable def redNat (A : OracleAdv ℕ Bool Bool) : OracleAdv ℕ Bool Bool :=
  (OracleAdv.simulate (lazyBind (K := ℕ)) A []).bind fun y => .ret y.1

derive_timed redNat

/-- The decision procedure `instDecidableEqNat` passed for the binder of the handler is priced
by its registered cost. -/
example (A : OracleAdv.Timed ℕ Bool Bool) :
    redNat.timed A = OracleAdv.Timed.delay
      (OracleAdv.Timed.simulate (fun t x => OracleAdv.Timed.delay 1
        (lazyBind.timed t x fun a b => 1 + instDecidableEqNat.timedCost a b)) A []).1
      ((OracleAdv.Timed.simulate (fun t x => OracleAdv.Timed.delay 1
        (lazyBind.timed t x fun a b => 1 + instDecidableEqNat.timedCost a b)) A []).2.bind
          fun y => (0, OracleAdv.Timed.ret y.1)) := rfl

example (A : OracleAdv.Timed ℕ Bool Bool) : (redNat.timed A).2.erase = redNat A.erase :=
  redNat.erase_timed A

/-! ### A membership test priced as a condition -/

/-- Membership of `a` in `l` by a `BEq` key (a copy of `List.elem`). -/
def memKey {α : Type} [BEq α] (a : α) : List α → Bool
  | [] => false
  | b :: l => a == b || memKey a l

derive_cost memKey

/-- `a` occurs in `l`; under `derive_timed.priceProps` the condition is priced by its body. -/
def Seen {α : Type} [BEq α] (a : α) (l : List α) : Prop := memKey a l = true

instance {α : Type} [BEq α] (a : α) (l : List α) : Decidable (Seen a l) :=
  inferInstanceAs (Decidable (memKey a l = true))

/-- A log of queries at natural-number keys: a key seen before is answered at once, a new key
is asked and logged. -/
def logNat (l : List ℕ) (x : ℕ) : OracleAdv ℕ Bool (Bool × List ℕ) :=
  if Seen x l then .ret (true, l) else .query x fun v => .ret (v, x :: l)

set_option derive_timed.priceProps true in
derive_timed logNat

example (l : List ℕ) (x : ℕ) : (logNat.timed l x).2.erase = logNat l x :=
  logNat.erase_timed l x

example (l : List ℕ) (x : ℕ) :
    (logNat.timed l x).1 =
      3 + memKey.timedCost x l (fun a b => 2 + instDecidableEqNat.timedCost a b) := by
  simp only [logNat.timed, OracleAdv.Timed.delay]
  split <;> rfl

/-- The same log at keys with a derived decision of equality. -/
def logKey (l : List Key) (x : Key) : OracleAdv Key Bool (Bool × List Key) :=
  if Seen x l then .ret (true, l) else .query x fun v => .ret (v, x :: l)

set_option derive_timed.priceProps true in
derive_timed logKey

example (l : List Key) (x : Key) : (logKey.timed l x).2.erase = logKey l x :=
  logKey.erase_timed l x

/-- The same log at keys of a `[DecidableEq K]` binder. -/
def logBind {K : Type} [DecidableEq K] (l : List K) (x : K) : OracleAdv K Bool (Bool × List K) :=
  if Seen x l then .ret (true, l) else .query x fun v => .ret (v, x :: l)

set_option derive_timed.priceProps true in
derive_timed logBind

example {K : Type} [DecidableEq K] (l : List K) (x : K) (instCost : K → K → ℕ) :
    (logBind.timed l x instCost).2.erase = logBind l x :=
  logBind.erase_timed l x instCost

example {K : Type} [DecidableEq K] (l : List K) (x : K) (instCost : K → K → ℕ) :
    (logBind.timed l x instCost).1 = 3 + memKey.timedCost x l (fun a b => 2 + instCost a b) := by
  simp only [logBind.timed, OracleAdv.Timed.delay]
  split <;> rfl

/-- The membership `x ∈ l` at a binder key, priced under `derive_timed.priceProps` by the
registered cost of `List.elem`, which charges each comparison one unit: outside the class, the
costed form takes no companion. -/
def logElemBind {K : Type} [DecidableEq K] (l : List K) (x : K) :
    OracleAdv K Bool (Bool × List K) :=
  if x ∈ l then .ret (true, l) else .query x fun v => .ret (v, x :: l)

set_option derive_timed.priceProps true in
derive_timed logElemBind

example {K : Type} [DecidableEq K] (l : List K) (x : K) :
    (logElemBind.timed l x).1 = 2 + List.elem.timedCost x l := by
  simp only [logElemBind.timed, OracleAdv.Timed.delay]
  split <;> rfl

/-! ### An instance whose method is not priced -/

/-- A tag. -/
structure Tag where
  n : ℕ

/-- An opaque comparison of tags. -/
opaque tagEq : Tag → Tag → Bool

instance : BEq Tag := ⟨tagEq⟩

/-- The table at keys compared by an opaque function. -/
noncomputable def lazyTag (t : List (Tag × Bool)) (x : Tag) :
    OracleAdv Tag Bool (Bool × List (Tag × Bool)) :=
  match findKey x t with
  | some v => .ret (v, t)
  | none => .rand (PMF.uniformFintype Bool) fun v => .ret (v, (x, v) :: t)

/--
error: derive_timed: the cost `CatCrypt.Tactics.DeriveTimedInstCostTest.findKey.timedCost`
takes the cost of the method `BEq.beq` of the instance `instBEqTag`, which is not a field of a
binder of the reduction, and the method is not priced (rule (k)):
  derive_timed: needs a registered primitive:
  `CatCrypt.Tactics.DeriveTimedInstCostTest.tagEq` has no definition to price and no registered
  cost `CatCrypt.Tactics.DeriveTimedInstCostTest.tagEq.timedCost`
-/
#guard_msgs (whitespace := lax) in
derive_timed lazyTag

end CatCrypt.Tactics.DeriveTimedInstCostTest
