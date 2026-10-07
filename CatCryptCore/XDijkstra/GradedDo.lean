/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Group.Defs

@[expose] public section
set_option autoImplicit false

/-!
# `GradedDo`: graded monads and a `do`-style notation for them

A graded monad over an additive monoid `G` is a family `M : G → Type u → Type v`
with a return at grade `0` and a bind that adds the grades (Katsumata, *Parametric
effect monads and semantics of effect systems*, POPL 2014; Orchard and Petricek,
*Embedding effect systems in Haskell*, Haskell 2014). Lean's `do` notation
elaborates to `Bind.bind` at one type constructor, so a block whose steps have
different grades is not a `do` block of any `Monad` instance. The notation `gdo`
of this module is a separate block notation that expands to `GradedMonad.gbind`,
as a rebindable or qualified `do` does in Haskell.

## The notation

A `gdo` block is a sequence of elements, one per line or separated by `;`.

* `let x ← e` binds the value of `e` in the rest of the block; `let x : τ ← e`
  states the type of `x`.
* `e`, not in the last position, runs `e` and discards its value, of any type.
* `let x := v` is a local definition.
* The last element is an expression `e`, the result of the block, or `return v`,
  which is `GradedMonad.gpure v`.

The expansion nests to the right: `gdo let x ← a; b; c` is
`gbind a fun x => gbind b fun _ => c`. For steps of grades `g₁, …, gₙ` the grade
of the block is therefore `g₁ + (g₂ + (… + gₙ))`, with last summand `0` when the
block ends in `return`. The grade is not normalised: the stated type of a block
names this sum, or the block is cast to another expression of the grade by an
operation of the family, such as a weakening along `≤`.

The notation has no `mut` variables, no `for` or `while` loops, no `if` without
`else`, no `try`, no pattern in a binder and no early `return`. A conditional or a
`match` is written as an expression whose branches have one common grade.

## Main definitions

* `GradedMonad`: the operations `gpure` and `gbind` of a graded monad.
* `LawfulGradedMonad`: the three monad laws, stated as heterogeneous equalities
  because the two sides have the grades `0 + g` and `g`, `g + 0` and `g`,
  `(g + h) + k` and `g + (h + k)`.
* `GradedMonad.gseq`: sequencing that discards the first value.
* The term notation `gdo`.

## Main results

* `GradedMonad.gseq_eq_gbind`: `gseq` is `gbind` at a constant continuation.
* `GradedMonad.gdo_let_arrow`, `GradedMonad.gdo_then`, `GradedMonad.gdo_return`:
  the expansion of each element of the notation, by `rfl`.
-/

namespace CatCrypt.XDijkstra

universe u v w

/-- A graded monad over the additive monoid `G`: a family of type constructors
indexed by a grade, with a return at grade `0` and a bind that adds the grades.
The class holds the operations only and is what the notation `gdo` expands to;
the laws are in `LawfulGradedMonad`. -/
class GradedMonad (G : Type w) [AddMonoid G] (M : G → Type u → Type v) where
  /-- Return a value, at grade `0`. -/
  gpure {α : Type u} : α → M 0 α
  /-- Run a computation of grade `g`, then the continuation, of grade `h` at every
  value, at its result. The grade is `g + h`. -/
  gbind {α β : Type u} {g h : G} : M g α → (α → M h β) → M (g + h) β

namespace GradedMonad

variable {G : Type w} [AddMonoid G] {M : G → Type u → Type v} [GradedMonad G M]

/-- Run `x`, discard its value, then run `y`. The grade is the sum of the two
grades. -/
def gseq {α β : Type u} {g h : G} (x : M g α) (y : M h β) : M (g + h) β :=
  gbind x fun _ => y

/-- `gseq` is `gbind` at a constant continuation. -/
theorem gseq_eq_gbind {α β : Type u} {g h : G} (x : M g α) (y : M h β) :
    gseq x y = gbind x fun _ => y := rfl

end GradedMonad

/-- The laws of a graded monad. The two sides of each law have types at grades
that are equal by a monoid law and not by reduction (`0 + g` and `g`, `g + 0` and
`g`, `(g + h) + k` and `g + (h + k)`), so each law is a heterogeneous equality. -/
class LawfulGradedMonad (G : Type w) [AddMonoid G] (M : G → Type u → Type v)
    [GradedMonad G M] : Prop where
  /-- Left identity: binding a returned value is applying the continuation. -/
  gpure_gbind {α β : Type u} {h : G} (a : α) (f : α → M h β) :
    HEq (GradedMonad.gbind (GradedMonad.gpure a) f) (f a)
  /-- Right identity: binding into the return is the computation. -/
  gbind_gpure {α : Type u} {g : G} (x : M g α) :
    HEq (GradedMonad.gbind x fun a => (GradedMonad.gpure a : M 0 α)) x
  /-- Associativity of bind. -/
  gbind_assoc {α β γ : Type u} {g h k : G} (x : M g α) (f : α → M h β) (c : β → M k γ) :
    HEq (GradedMonad.gbind (GradedMonad.gbind x f) c)
      (GradedMonad.gbind x fun a => GradedMonad.gbind (f a) c)

/-! ## The notation -/

/-- An element of a `gdo` block. -/
declare_syntax_cat gdoElem

/-- `let x ← e` binds the value of the graded computation `e` in the rest of the
block. -/
syntax (name := gdoLetArrow) "let " ident (" : " term)? " ← " term : gdoElem

/-- `let x := v` is a local definition in the rest of the block. -/
syntax (name := gdoLet) "let " ident (" : " term)? " := " term : gdoElem

/-- `return v` ends a block with `GradedMonad.gpure v`, at grade `0`. -/
syntax (name := gdoReturn) "return " term : gdoElem

/-- An expression: a step whose value is discarded, or the result of the block
when it is the last element. -/
syntax (name := gdoExpr) notFollowedBy("let") term : gdoElem

/-- `gdo` is block notation for a graded monad (`GradedMonad`). The elements are
`let x ← e`, `let x := v`, an expression `e`, and in the last position an
expression or `return v`; they are written one per line or separated by `;`. The
block expands to right-nested applications of `GradedMonad.gbind`, so its grade is
the sum `g₁ + (g₂ + (… + gₙ))` of the grades of its steps, with last summand `0`
after `return`. There are no `mut` variables, loops, `if` without `else`, patterns
in binders or early `return`. -/
syntax (name := gdoBlock) "gdo " many1Indent(gdoElem ";"?) : term

/-- The elements of a `gdo` block after the separators are removed; an
intermediate form of the expansion. -/
syntax (name := gdoElems) "gdo_elems% " gdoElem* : term

macro_rules
  | `(gdo $[$es:gdoElem $[;]?]*) => `(gdo_elems% $es*)

macro_rules
  | `(gdo_elems% return $v:term) => `(GradedMonad.gpure $v)
  | `(gdo_elems% $e:term) => `($e)
  | `(gdo_elems% let $x:ident ← $e:term $r:gdoElem $rs:gdoElem*) =>
    `(GradedMonad.gbind $e (fun $x => gdo_elems% $r $rs*))
  | `(gdo_elems% let $x:ident : $t:term ← $e:term $r:gdoElem $rs:gdoElem*) =>
    `(GradedMonad.gbind $e (fun ($x : $t) => gdo_elems% $r $rs*))
  | `(gdo_elems% let $x:ident := $v:term $r:gdoElem $rs:gdoElem*) =>
    `(let $x := $v; gdo_elems% $r $rs*)
  | `(gdo_elems% let $x:ident : $t:term := $v:term $r:gdoElem $rs:gdoElem*) =>
    `(let $x : $t := $v; gdo_elems% $r $rs*)
  | `(gdo_elems% return $_:term $r:gdoElem $_:gdoElem*) =>
    Lean.Macro.throwErrorAt r "`return` is the last element of a `gdo` block"
  | `(gdo_elems% $e:term $r:gdoElem $rs:gdoElem*) =>
    `(GradedMonad.gbind $e (fun _ => gdo_elems% $r $rs*))
  | `(gdo_elems% let $x:ident ← $_:term) =>
    Lean.Macro.throwErrorAt x "a `gdo` block ends in an expression or in `return`"
  | `(gdo_elems% let $x:ident : $_:term ← $_:term) =>
    Lean.Macro.throwErrorAt x "a `gdo` block ends in an expression or in `return`"
  | `(gdo_elems% let $x:ident := $_:term) =>
    Lean.Macro.throwErrorAt x "a `gdo` block ends in an expression or in `return`"
  | `(gdo_elems% let $x:ident : $_:term := $_:term) =>
    Lean.Macro.throwErrorAt x "a `gdo` block ends in an expression or in `return`"

namespace GradedMonad

variable {G : Type w} [AddMonoid G] {M : G → Type u → Type v} [GradedMonad G M]

/-- A block `let x ← e` followed by a result expands to `gbind`. -/
theorem gdo_let_arrow {α β : Type u} {g h : G} (x : M g α) (f : α → M h β) :
    (gdo
      let a ← x
      f a) = gbind x f := rfl

/-- A step followed by a result expands to `gbind` at a constant continuation,
which is `gseq`. -/
theorem gdo_then {α β : Type u} {g h : G} (x : M g α) (y : M h β) :
    (gdo
      x
      y) = gseq x y := rfl

/-- A block that ends in `return` has last summand `0` in its grade. -/
theorem gdo_return {α β : Type u} {g : G} (x : M g α) (f : α → β) :
    (gdo
      let a ← x
      let b := f a
      return b) = (gbind x fun a => gpure (f a) : M (g + 0) β) := rfl

end GradedMonad

end CatCrypt.XDijkstra
