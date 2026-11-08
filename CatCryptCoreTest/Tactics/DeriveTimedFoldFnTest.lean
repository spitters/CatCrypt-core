/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveTimed.Basic
public import CatCryptCore.Tactics.StdCosts
import CatCryptCore.Core.SPTree

/-!
# Tests for recursive function results and folds over functions in `derive_timed`

Fresh reductions whose state is a table updated by `Function.update`:

* a table counted by a structural recursion (`accAll`), read twice under a `let`
  (`lookTwice`): the recursion is charged once, through `accAll.timed`, which returns its cost
  with the costed table;
* the entries of tagged positions (`tagAll`, a recursion over a list with an accumulator updated
  at an `if`), read twice (`tagRed`);
* a table counted by a left fold (`foldTwice`) and one built by a right fold (`foldrTwice`):
  the fold of the costed step, priced by the registered cost of the fold at the costed table;
* a table defined by cases on its point (`tblTwice`), outside the class: each read is priced by
  the recursion at the point it reads.

Each erasure theorem and each derived cost or companion bound is pinned by an `example`.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedFoldFnTest

open CatCrypt.Core

/-- Every key of the list counted once more in the table. -/
def accAll (q : ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [] => q
  | x :: xs => accAll (Function.update q x (q x + 1)) xs

/-- The counted table read twice. -/
noncomputable def lookTwice (q : ℕ → ℕ) (l : List ℕ) (a b : ℕ) (D : ℕ → SPTree Bool) :
    SPTree Bool :=
  let g := accAll q l
  D (g a + g b)

derive_timed lookTwice

example (q qCost : ℕ → ℕ) (l : List ℕ) (a b : ℕ) (D : ℕ → SPTree.Timed Bool)
    (DCost : ℕ → ℕ) :
    (lookTwice.timed q qCost l a b D DCost).2.erase = lookTwice q l a b (fun n => (D n).erase) :=
  lookTwice.erase_timed q qCost l a b D DCost

/-- The recursion is charged once, at the `let`; each read costs one plus the companion of the
table the recursion returns. -/
example (q qCost : ℕ → ℕ) (l : List ℕ) (a b : ℕ) (D : ℕ → SPTree.Timed Bool)
    (DCost : ℕ → ℕ) :
    (lookTwice.timed q qCost l a b D DCost).1 =
      1 + (accAll.timed q qCost l).1 +
        (1 + (DCost (accAll q l a + accAll q l b) +
          (1 + (1 + (accAll.timed q qCost l).2.2 a + (1 + (accAll.timed q qCost l).2.2 b))))) :=
  rfl

/-- The companion of the table after the recursion exceeds that of the initial table by at most
three per key. -/
example (l : List ℕ) : ∀ (q qCost : ℕ → ℕ) (B : ℕ), (∀ y, qCost y ≤ B) →
    ∀ y, (accAll.timed q qCost l).2.2 y ≤ B + 3 * l.length := by
  induction l with
  | nil =>
    intro q qCost B h y
    simp only [accAll.timed.eq_1, List.length_nil]
    grind
  | cons x l ih =>
    intro q qCost B h y
    have hs : ∀ a, (2 + if _ : a = x then 0 else 1 + qCost a) ≤ B + 3 := fun a => by
      split <;> grind
    have := ih (Function.update q x (q x + 1)) _ (B + 3) hs y
    rw [accAll.timed.eq_2]
    grind

/-- The table counted by a left fold, read twice. -/
noncomputable def foldTwice (q : ℕ → ℕ) (l : List ℕ) (a b : ℕ) (D : ℕ → SPTree Bool) :
    SPTree Bool :=
  let g := l.foldl (fun g x => Function.update g x (g x + 1)) q
  D (g a + g b)

derive_timed foldTwice

example (q qCost : ℕ → ℕ) (l : List ℕ) (a b : ℕ) (D : ℕ → SPTree.Timed Bool)
    (DCost : ℕ → ℕ) :
    (foldTwice.timed q qCost l a b D DCost).2.erase = foldTwice q l a b (fun n => (D n).erase) :=
  foldTwice.erase_timed q qCost l a b D DCost

/-- The fold is charged once, at the `let`, by the registered cost of `List.foldl` at the costed
table; each read costs one plus the companion of the folded table. -/
example (q qCost : ℕ → ℕ) (l : List ℕ) (a b : ℕ) (D : ℕ → SPTree.Timed Bool)
    (DCost : ℕ → ℕ) :
    let f := fun (g : ℕ → ℕ) x => Function.update g x (g x + 1)
    let fHat := fun (gHat : (ℕ → ℕ) × (ℕ → ℕ)) x =>
      (Function.update gHat.1 x (gHat.1 x + 1), fun a => 2 + if _ : a = x then 0 else 1 + gHat.2 a)
    (foldTwice.timed q qCost l a b D DCost).1 =
      1 + List.foldl.timedCost fHat (fun gHat x => 2 + gHat.2 x) (q, qCost) l +
        (1 + (DCost (l.foldl f q a + l.foldl f q b) +
          (1 + (1 + (DeriveTimed.foldlHat f fHat (q, qCost) l).2 a +
            (1 + (DeriveTimed.foldlHat f fHat (q, qCost) l).2 b))))) :=
  rfl

/-- The companion of the folded table exceeds that of the initial table by at most three per
key (`foldlHat_snd_le`). -/
example (q qCost : ℕ → ℕ) (B : ℕ) (h : ∀ y, qCost y ≤ B) (l : List ℕ) (y : ℕ) :
    (DeriveTimed.foldlHat (fun (g : ℕ → ℕ) x => Function.update g x (g x + 1))
      (fun (gHat : (ℕ → ℕ) × (ℕ → ℕ)) x => (Function.update gHat.1 x (gHat.1 x + 1),
        fun a => 2 + if _ : a = x then 0 else 1 + gHat.2 a)) (q, qCost) l).2 y ≤
      B + 3 * l.length :=
  DeriveTimed.foldlHat_snd_le _ _
    (fun _ x M hM a => by
      change (2 + if _ : a = x then 0 else 1 + _) ≤ M + 3
      have := hM a
      split <;> grind) l (q, qCost) B h y

/-- The entries of the listed positions, an entry set at a tagged position only. -/
def tagAll (tag : ℕ → Bool) (msg : ℕ → ℕ) : List ℕ → (ℕ → Option ℕ) → ℕ → Option ℕ
  | [], acc => acc
  | i :: is, acc =>
    tagAll tag msg is (Function.update acc i (if tag i then some (msg i) else none))

/-- The tagged entries read at two positions. -/
noncomputable def tagRed (tag : ℕ → Bool) (msg : ℕ → ℕ) (l : List ℕ)
    (D : Option ℕ → SPTree Bool) : SPTree Bool :=
  let t := tagAll tag msg l (fun _ => none)
  D ((t 0).orElse fun _ => t 1)

derive_timed tagRed

example (tag : ℕ → Bool) (tagCost : ℕ → ℕ) (msg msgCost : ℕ → ℕ) (l : List ℕ)
    (D : Option ℕ → SPTree.Timed Bool) (DCost : Option ℕ → ℕ) :
    (tagRed.timed tag tagCost msg msgCost l D DCost).2.erase =
      tagRed tag msg l (fun o => (D o).erase) :=
  tagRed.erase_timed tag tagCost msg msgCost l D DCost

/-- The recursion is charged once, at the `let`, and the first read at its companion. -/
example (tag : ℕ → Bool) (tagCost : ℕ → ℕ) (msg msgCost : ℕ → ℕ) (l : List ℕ)
    (D : Option ℕ → SPTree.Timed Bool) (DCost : Option ℕ → ℕ) :
    (tagRed.timed tag tagCost msg msgCost l D DCost).1 =
      1 + (tagAll.timed tag tagCost msg msgCost l (fun _ => none) fun _ => 0).1 +
        (1 + (DCost ((tagAll tag msg l (fun _ => none) 0).orElse
            fun _ => tagAll tag msg l (fun _ => none) 1) +
          (1 + (1 + (tagAll.timed tag tagCost msg msgCost l (fun _ => none) fun _ => 0).2.2 0 +
            (1 + match tagAll tag msg l (fun _ => none) 0 with
              | some _ => 0
              | none =>
                1 + (1 + (tagAll.timed tag tagCost msg msgCost l (fun _ => none)
                  fun _ => 0).2.2 1)))))) := by
  simp only [tagRed.timed]
  split <;> simp only [*]

/-- The table of the listed keys built by a right fold, read twice. -/
noncomputable def foldrTwice (l : List ℕ) (a b : ℕ) (D : Option ℕ → SPTree Bool) :
    SPTree Bool :=
  let g := l.foldr (fun x g => Function.update g x (some x)) (fun _ => none)
  D ((g a).orElse fun _ => g b)

derive_timed foldrTwice

example (l : List ℕ) (a b : ℕ) (D : Option ℕ → SPTree.Timed Bool) (DCost : Option ℕ → ℕ) :
    (foldrTwice.timed l a b D DCost).2.erase = foldrTwice l a b (fun o => (D o).erase) :=
  foldrTwice.erase_timed l a b D DCost

/-- The companion of the table built by the right fold is at most three per key (the initial
table, a closure of constant results, has companion zero). -/
example (l : List ℕ) (y : ℕ) :
    (DeriveTimed.foldrHat (fun x (g : ℕ → Option ℕ) => Function.update g x (some x))
      (fun x (gHat : (ℕ → Option ℕ) × (ℕ → ℕ)) => (Function.update gHat.1 x (some x),
        fun a => 2 + if _ : a = x then 0 else 1 + gHat.2 a))
      (fun _ => none, fun _ => 0) l).2 y ≤ 3 * l.length := by
  have := DeriveTimed.foldrHat_snd_le (d := 3)
    (fun x (g : ℕ → Option ℕ) => Function.update g x (some x))
    (fun x (gHat : (ℕ → Option ℕ) × (ℕ → ℕ)) => (Function.update gHat.1 x (some x),
      fun a => 2 + if _ : a = x then 0 else 1 + gHat.2 a))
    (fun x _ M hM a => by
      change (2 + if _ : a = x then 0 else 1 + _) ≤ M + 3
      have := hM a
      split <;> grind) l (fun _ => none, fun _ => 0) 0 (fun _ => le_refl 0) y
  grind

/-- A table defined by cases on its point. -/
def tbl (k : ℕ) : ℕ → ℕ
  | 0 => k
  | n + 1 => tbl k n + 1

/-- The table read twice. -/
noncomputable def tblTwice (k a b : ℕ) (D : ℕ → SPTree Bool) : SPTree Bool :=
  let g := tbl k
  D (g a + g b)

derive_timed tblTwice

/-- Outside the class: `tbl k` is a partial application, whose recursion runs on the point, so
each read is priced by the cost of the recursion at the point it reads, and no costed value of
`tbl` is derived. -/
example (k a b : ℕ) (D : ℕ → SPTree.Timed Bool) (DCost : ℕ → ℕ) :
    (tblTwice.timed k a b D DCost).1 =
      1 + (DCost (tbl k a + tbl k b) +
        (1 + (1 + tbl.timedCost k a + (1 + tbl.timedCost k b)))) :=
  rfl

end CatCrypt.Tactics.DeriveTimedFoldFnTest

end
