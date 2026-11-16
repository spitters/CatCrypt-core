/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Rust.WP

/-!
# The `RustM` monad at the root namespace

`RustM` is the result monad of the Aeneas `Std` model vendored by hax-lean,
`Aeneas.Std.RustM`: a value (`.ok v`), a failure (`.fail e`) or divergence
(`.div`). This module gives it and its error type the root-level names `RustM`
and `Error`, as abbreviations, so that `UCMonad.RustMBridge` and `CTypeBridge`
state their results over the type that the extraction readings use.

`Error` has the two kinds `panic` and `undef` of `Aeneas.Std.Error`. The five
further kinds of the hax-lib error type (`assertionFailure`, `integerOverflow`,
`divisionByZero`, `arrayOutOfBounds`, `maximumSizeExceeded`) are absent: no
module of the workspace constructs or matches on them.

## What is provided

* `Error`, `RustM`: abbreviations of `Aeneas.Std.Error` and `Aeneas.Std.RustM`,
  with the constructors and `bind` exported under the root-level names. The
  monad and lawful-monad instances are those of hax-lean.
* `RustM.isOk`, `RustM.of_isOk`: the Boolean test `Aeneas.Std.ok?` and the
  extraction `Aeneas.Std.eval_global`.
* `RustM.IsOk`: the proposition that a computation is a value, with its
  introduction rules and `RustM.isOk_bind`.
* `RustM.extractPure`: the value of a computation, or `default`.
* `RustM.failure`: the panic that hax prints for an unimplemented feature.
-/

@[expose] public section

set_option autoImplicit false

/-- Error kinds of a failing Rust computation: `Aeneas.Std.Error`. -/
abbrev Error : Type := Aeneas.Std.Error

/-- The result monad of Rust computations, `Aeneas.Std.RustM`:
    * `.ok v`: completion with value `v`
    * `.fail e`: a runtime error
    * `.div`: divergence -/
abbrev RustM.{u} (α : Type u) : Type u := Aeneas.Std.RustM α

namespace Error

export Aeneas.Std.Error (panic undef)

end Error

namespace RustM

export Aeneas.Std.RustM (ok fail div)
export Aeneas.Std (bind)

/-- Is a `RustM` computation a value? This is `Aeneas.Std.ok?`. -/
abbrev isOk {α : Type} (x : RustM α) : Bool := Aeneas.Std.ok? x

/-- The value of a computation known to be one. This is `Aeneas.Std.eval_global`. -/
abbrev of_isOk {α : Type} (x : RustM α) (h : RustM.isOk x) : α := Aeneas.Std.eval_global x h

@[simp]
theorem ok_of_isOk {α : Type} (v : α) (h : isOk (ok v)) :
    of_isOk (ok v) h = v := rfl

/-- `IsOk x` witnesses that `x = .ok v` for some `v`. -/
def IsOk {α : Type} (x : RustM α) : Prop := ∃ v, x = .ok v

@[simp] theorem isOk_ok {α : Type} {v : α} : IsOk (.ok v) := ⟨v, rfl⟩
@[simp] theorem isOk_pure {α : Type} {a : α} : IsOk (pure a : RustM α) := ⟨a, rfl⟩

theorem not_isOk_fail {α : Type} {e : Error} : ¬ IsOk (.fail e : RustM α) := by
  intro ⟨_, h⟩; cases h

theorem not_isOk_div {α : Type} : ¬ IsOk (.div : RustM α) := by
  intro ⟨_, h⟩; cases h

theorem isOk_bind {α β : Type} {x : RustM α} {f : α → RustM β}
    (hx : IsOk x) (hf : ∀ v, IsOk (f v)) : IsOk (x >>= f) := by
  obtain ⟨v, rfl⟩ := hx
  exact hf v

/-- Extract the value from a successful computation, or return `default`. -/
def extractPure {α : Type} [Inhabited α] (x : RustM α) : α :=
  match x with
  | .ok v => v
  | _ => default

theorem extractPure_ok {α : Type} [Inhabited α] {x : RustM α} {v : α}
    (h : x = .ok v) : extractPure x = v := by
  subst h; rfl

theorem ok_extractPure {α : Type} [Inhabited α] (x : RustM α) (h : IsOk x) :
    x = .ok (extractPure x) := by
  obtain ⟨v, hv⟩ := h; subst hv; rfl

/-- Hax uses `failure` for unimplemented features. Maps to `RustM.fail .panic`. -/
def failure {α : Type} (_msg _label : String) : RustM α := .fail .panic

end RustM
