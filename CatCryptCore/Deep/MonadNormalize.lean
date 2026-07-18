/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.Eval

/-!
# Reflective normalization for the `RawCode` free monad

This file gives a *reflective normalizer* for the deep embedding `RawCode`, in
exactly the sense that `ring` normalizes commutative-ring expressions and
Mathlib's `monoidal` tactic normalizes monoidal-category coherence terms: we
compute a canonical normal form on the syntax tree and prove **once** that the
interpretation is invariant under normalization. Equalities that hold by the
monad laws then reduce to a single normal-form comparison.

The key observation is that `RawCode` *is already the reflected syntax tree* of
the free monad on the signature `{sample, get, put, fail, oracleCall, embed}` —
there is no need for a separate `MonExpr` reflection layer. We normalize
`RawCode` directly. The interpretation `RawCode.eval : RawCode α → SPComp α`
(`CatCryptCore/Deep/Eval.lean`) is a monad morphism into `SPComp`, and `SPComp`
is a **lawful** monad: `SPComp.bind_assoc`, `SPComp.pure_bind`, `SPComp.bind_pure`
hold as proved lemmas (`CatCryptCore/Core/Code.lean`). Those shallow laws are
what make the soundness lemma go through — even though the *same* laws are **not**
definitional on `RawCode` itself (its `Monad` instance is deliberately unlawful,
the associativity/unit tax that `sp_normalize_deep` currently pays by hand with
`simp`).

## Pipeline

* `RawCode.appendNF` — a "smart bind" that reassociates to the right and
  eliminates leading `ret` (left unit).
* `RawCode.normalize` — the resulting right-nested, pure-eliminated normal form.
* `RawCode.eval_appendNF`, `RawCode.eval_normalize` — the *one* soundness
  induction (the crux, analogous to `ring`'s soundness).
* `RawCode.eval_eq_of_normalize_eq` + the `mon_coherence` tactic — the reflective
  closer: an `a.eval = b.eval` goal is discharged by comparing normal forms.

## Intended use

`mon_coherence` is the reflective (ring / `monoidal`-coherence) analog for the
Kleisli bind of `SPComp`. It is intended to replace the simp-based
`sp_normalize_deep` as the leaf normalizer inside `pkg_coherence!`: instead of
paying the non-definitional-`bind_assoc` tax with a `simp` set on every leaf, the
normal form is computed once and the goal closes by a definitional comparison.

## References

* `ring` / `Mathlib.Tactic.Ring` — reflective normalization for commutative rings.
* `Mathlib.Tactic.CategoryTheory.Monoidal` — reflective coherence for monoidal
  categories.
-/

set_option autoImplicit false

namespace CatCrypt.Deep

open CatCrypt.Core

universe u

namespace RawCode

/-! ## Smart bind and normal form -/

/-- Smart bind on `RawCode`: append the continuation `k` to `c`, reassociating
    to the right and eliminating a leading `ret` (left unit).

    * `appendNF (.ret a) k = k a`                              (left unit / pure-elim)
    * `appendNF (.bind c k') k = .bind c (fun x => appendNF (k' x) k)` (reassociate right)
    * `appendNF op k = .bind op k` for an atomic op            (sample/get/put/fail/…)

    The recursion is structural under the bind continuation `k'` — this is the
    same shape as `RawCode.substOracle`, which recurses under its continuation. -/
def appendNF {α β : Type u} (c : RawCode α) (k : α → RawCode β) : RawCode β :=
  match c with
  | .ret a => k a
  | .bind c' k' => .bind c' (fun x => appendNF (k' x) k)
  | @RawCode.sample T fi ne => .bind (@RawCode.sample T fi ne) k
  | .get ℓ => .bind (.get ℓ) k
  | .put ℓ v => .bind (.put ℓ v) k
  | .fail => .bind .fail k
  | .oracleCall op dom codom x => .bind (.oracleCall op dom codom x) k
  | .embed c => .bind (.embed c) k

/-- Normalize a `RawCode` tree to right-nested, pure-eliminated normal form.

    Atomic constructors map to themselves; a `bind` is normalized recursively and
    then reassociated with `appendNF`. -/
def normalize {α : Type u} (c : RawCode α) : RawCode α :=
  match c with
  | .ret a => .ret a
  | .bind c' k => appendNF (normalize c') (fun x => normalize (k x))
  | @RawCode.sample T fi ne => @RawCode.sample T fi ne
  | .get ℓ => .get ℓ
  | .put ℓ v => .put ℓ v
  | .fail => .fail
  | .oracleCall op dom codom x => .oracleCall op dom codom x
  | .embed c => .embed c

/-! ## Soundness

The single soundness induction: `eval` is invariant under `appendNF`/`normalize`.
This is the crux, exactly analogous to `ring`'s soundness lemma. The proof uses
the *shallow* monad laws of `SPComp` (`pure_bind`, `bind_assoc`) — precisely the
laws that are **not** definitional on `RawCode`. -/

/-- `appendNF` computes the Kleisli bind of the interpretations:
    `(appendNF c k).eval = c.eval.bind (fun x => (k x).eval)`.

    Proof by induction on `c`, using `SPComp.pure_bind` (left-unit case) and
    `SPComp.bind_assoc` (reassociation case). -/
theorem eval_appendNF {α β : Type u} (c : RawCode α) (k : α → RawCode β) :
    (appendNF c k).eval = c.eval.bind (fun x => (k x).eval) := by
  induction c with
  | ret a => simp only [appendNF, eval_ret, SPComp.pure_bind]
  | bind c' k' _ ih_k' =>
    simp only [appendNF, eval_bind, ih_k']
    rw [SPComp.bind_assoc]
  | sample T => rfl
  | get ℓ => rfl
  | put ℓ v => rfl
  | fail => rfl
  | oracleCall op dom codom x => rfl
  | embed c => rfl

/-- **Soundness of `normalize`**: interpretation is invariant under normalization,
    `(normalize c).eval = c.eval`. Proof by induction on `c`, using `eval_appendNF`. -/
theorem eval_normalize {α : Type u} (c : RawCode α) :
    (normalize c).eval = c.eval := by
  induction c with
  | ret a => rfl
  | bind c' k ih_c' ih_k =>
    simp only [normalize, eval_appendNF, ih_c', ih_k, eval_bind]
  | sample T => rfl
  | get ℓ => rfl
  | put ℓ v => rfl
  | fail => rfl
  | oracleCall op dom codom x => rfl
  | embed c => rfl

/-! ## The reflective closer -/

/-- **Payoff**: if two `RawCode` trees have the same normal form, their
    interpretations are equal. Rewrite both sides through `eval_normalize`, then
    the syntactic hypothesis `h` finishes. -/
theorem eval_eq_of_normalize_eq {α : Type u} {a b : RawCode α}
    (h : normalize a = normalize b) : a.eval = b.eval := by
  rw [← eval_normalize a, ← eval_normalize b, h]

end RawCode

/-- Reflective closer for `SPComp`-level Kleisli-bind equalities. Closes a goal
    `a.eval = b.eval` by comparing the normal forms of the deep terms `a` and `b`:
    `exact RawCode.eval_eq_of_normalize_eq (by rfl)`.

    This is the ring / `monoidal`-coherence analog for the deep-embedding monad;
    it is meant to replace the simp-based `sp_normalize_deep` as the leaf
    normalizer inside `pkg_coherence!`. -/
macro "mon_coherence" : tactic =>
  `(tactic| exact CatCrypt.Deep.RawCode.eval_eq_of_normalize_eq (by rfl))

/-! ## Demonstration

Bind associativity / left-unit equalities at the `eval` level, each closed in a
single `mon_coherence` step. These would otherwise need several
`eval_bind`/`SPComp.bind_assoc` (i.e. `sp_normalize_deep`) simp steps. -/

namespace RawCodeMonNormalizeDemo

open RawCode

/-- Left unit at the `eval` level (`f`, `a` abstract). -/
example {α β : Type u} (a : α) (f : α → RawCode β) :
    (RawCode.bind (RawCode.ret a) f).eval = (f a).eval := by
  mon_coherence

/-- Single reassociation with a concrete leftmost leaf. -/
example {β γ : Type} (g : Bool → RawCode β) (h : β → RawCode γ) :
    (RawCode.bind (RawCode.bind (RawCode.sample Bool) g) h).eval
      = (RawCode.bind (RawCode.sample Bool) (fun x => RawCode.bind (g x) h)).eval := by
  mon_coherence

/-- Deep (triple) reassociation, left-nested to right-nested, closed in one step.
    A concrete spine (`sample`/`get`/`fail`) lets the normalizer reassociate fully. -/
example (ℓ : CatCrypt.Core.Location) :
    (RawCode.bind
        (RawCode.bind
          (RawCode.bind (RawCode.sample Bool) (fun _ => RawCode.get ℓ))
          (fun _ => RawCode.sample Bool))
        (fun _ => RawCode.fail (α := Nat))).eval
      = (RawCode.bind (RawCode.sample Bool)
          (fun x => RawCode.bind ((fun _ => RawCode.get ℓ) x)
            (fun y => RawCode.bind ((fun _ => RawCode.sample Bool) y)
              (fun _ => RawCode.fail (α := Nat))))).eval := by
  mon_coherence

/-- Reassociation threaded through a leading `ret` (left unit + associativity),
    combining pure-elimination and reassociation in one normal form. -/
example {γ : Type} (h : Bool → RawCode γ) :
    (RawCode.bind
        (RawCode.bind (RawCode.bind (RawCode.ret true) (fun _ => RawCode.sample Bool))
          (fun b => RawCode.ret b))
        h).eval
      = (RawCode.bind (RawCode.sample Bool) h).eval := by
  mon_coherence

end RawCodeMonNormalizeDemo

end CatCrypt.Deep
