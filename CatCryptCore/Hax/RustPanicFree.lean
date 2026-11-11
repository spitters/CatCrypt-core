/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad.RustMBridge
public import HaxLean.RuntimeM
public import CatCryptCore.Tactics.AutoDispatchExt

/-!
# Panic freedom of `RustM` functions from `Std.WP` triples

The `Std.WP` interpretation of `RustM` (`HaxLean.RuntimeM`) sends a failure to the
exception postcondition. A triple whose exception postcondition is false therefore
excludes failure, and divergence satisfies no postcondition: the program is a value. This
module derives `UCMonad.RustMBridge.PanicFreeOn` and equations `f x = .ok v` from such
triples, so that `rust_vc`, which proves triples from the `@[spec]` guard triples of the
guarded runtime operations, proves panic freedom.

## Main results

* `RustPanicFree.eq_ok_of_triple`: from `Triple x P Q epost` with `epost` false and `P`,
  `x = .ok v` for a value `v` satisfying `Q`.
* `RustPanicFree.panicFreeOn_of_triple`: from `∀ x, ⦃pre x⦄ f x ⦃post x⦄`,
  `PanicFreeOn pre f`.
* `RustPanicFree.eq_ok_of_triple_eq`: from `⦃P⦄ x ⦃fun r => r = v⦄` and `P`, `x = .ok v`.

## Tactics

* `rust_panic_free` and `rust_panic_free [l₁, …]`: closes `PanicFreeOn pre f` by
  `panicFreeOn_of_triple` and `rust_vc`, and `x = .ok v` by `eq_ok_of_triple_eq` and
  `rust_vc`; the lemmas `lᵢ` go to `rust_vc`.
* The `catcrypt_auto` shapes `RustM panic freedom` (goals `PanicFreeOn pre f`) and
  `RustM value equation` (goals `x = .ok v` and `x = pure v` at `RustM`), each with the
  arm `rust_panic_free`.
-/

@[expose] public section

set_option autoImplicit false

namespace RustPanicFree

open UCMonad.RustMBridge (PanicFreeOn)
open _root_.Std.WP Lean.Order

/-- A triple with a false exception postcondition, at a state satisfying its
precondition, makes the program a value satisfying the postcondition. -/
theorem eq_ok_of_triple {α : Type} {x : Aeneas.Std.RustM α} {P : Prop} {Q : α → Prop}
    {epost : Aeneas.Std.Error → Prop} (h : Triple x P Q epost) (hE : ∀ e, ¬ epost e) (hP : P) :
    ∃ v, x = .ok v ∧ Q v := by
  have hw := h.le_wp hP
  cases x with
  | ok v => exact ⟨v, rfl, hw⟩
  | fail e => exact absurd hw (hE e)
  | div => exact hw.elim

/-- The exception postcondition `⊥` of the triple notation `⦃P⦄ x ⦃Q⦄` at `RustM` holds
at no error. -/
theorem bot_epost_false (e : Aeneas.Std.Error) :
    ¬ (Lean.Order.bot : Aeneas.Std.Error → Prop) e := by
  simp_all

/-- `PanicFreeOn pre f` from a triple `⦃pre x⦄ f x ⦃post x⦄` at every argument. -/
theorem panicFreeOn_of_triple {α β : Type} {pre : α → Prop} {f : α → Aeneas.Std.RustM β}
    (post : α → β → Prop) (h : ∀ x, ⦃ pre x ⦄ f x ⦃ post x ⦄) : PanicFreeOn pre f := by
  intro x hx
  obtain ⟨v, hv, _⟩ := eq_ok_of_triple (h x) bot_epost_false hx
  exact ⟨v, hv⟩

/-- `x = .ok v` from the triple `⦃P⦄ x ⦃fun r => r = v⦄` and `P`. -/
theorem eq_ok_of_triple_eq {α : Type} {x : Aeneas.Std.RustM α} {v : α} {P : Prop}
    (h : ⦃ P ⦄ x ⦃ fun r => r = v ⦄) (hP : P) : x = .ok v := by
  obtain ⟨w, hw, rfl⟩ := eq_ok_of_triple h bot_epost_false hP
  exact hw

end RustPanicFree

/-- `rust_panic_free` closes `PanicFreeOn pre f` by `panicFreeOn_of_triple` and `rust_vc`
at each argument, and an equation `x = .ok v` (or `x = pure v`) at `RustM` by
`eq_ok_of_triple_eq` at the precondition `True` and `rust_vc`, whose verification
conditions see the local hypotheses. `rust_panic_free [l₁, …]` passes the lemmas `lᵢ` to
`rust_vc`. -/
syntax (name := rustPanicFree) "rust_panic_free"
  (" [" withoutPosition((Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),*,?) "]")? : tactic

macro_rules
  | `(tactic| rust_panic_free) => `(tactic|
      open _root_.Std.WP Lean.Order in
      first
        | (refine RustPanicFree.panicFreeOn_of_triple (fun _ _ => True) (fun _ => ?_)
           rust_vc)
        | (refine RustPanicFree.eq_ok_of_triple_eq (P := True) ?_ trivial
           rust_vc))
  | `(tactic| rust_panic_free [$ts,*]) => `(tactic|
      open _root_.Std.WP Lean.Order in
      first
        | (refine RustPanicFree.panicFreeOn_of_triple (fun _ _ => True) (fun _ => ?_)
           rust_vc [$ts,*])
        | (refine RustPanicFree.eq_ok_of_triple_eq (P := True) ?_ trivial
           rust_vc [$ts,*]))

catcrypt_auto_shape "RustM panic freedom" direct priority 60 :=
  app UCMonad.RustMBridge.PanicFreeOn

catcrypt_auto_shape "RustM value equation" direct priority 55 :=
  all [arg Eq/3 at 0 whnf (app Aeneas.Std.RustM),
    arg Eq/3 at 2 (any [app Aeneas.Std.RustM.ok, app Pure.pure])]

catcrypt_auto_arm "RustM panic freedom" order 10 := "rust_panic_free"

catcrypt_auto_arm "RustM value equation" order 10 := "rust_panic_free"

namespace RustPanicFree.Examples

open UCMonad.RustMBridge (PanicFreeOn)
open Hax _root_.Std.WP Lean.Order

/-- `a[x + 1]` with a checked 64-bit increment: the two guarded operations `addM_w 64`
and `indexM`. -/
def incrIndex (p : Array Int × Int) : Aeneas.Std.RustM Int := do
  let j ← addM_w 64 p.2 1
  indexM p.1 j

/-- The precondition of `incrIndex`: the incremented index is in bounds and does not
overflow 64 bits. -/
def IncrIndexPre (p : Array Int × Int) : Prop :=
  0 ≤ p.2 ∧ p.2 + 1 < p.1.size ∧ p.2 + 1 < 2 ^ 64

/-- `incrIndex` is panic-free on its precondition, by `panicFreeOn_of_triple` and
`rust_vc`. -/
theorem incrIndex_panicFreeOn : PanicFreeOn IncrIndexPre incrIndex := by
  refine panicFreeOn_of_triple (fun _ _ => True) (fun p => ?_)
  unfold incrIndex IncrIndexPre
  rust_vc

/-- The same statement, by the tactic `rust_panic_free`. -/
example : PanicFreeOn IncrIndexPre incrIndex := by
  unfold IncrIndexPre
  rust_panic_free [incrIndex]

end RustPanicFree.Examples
