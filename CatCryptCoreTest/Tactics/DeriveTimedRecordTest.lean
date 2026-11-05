/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.StdCosts
import CatCryptCore.Core.SPTree

/-!
# Tests for erasure through recursions over costed closures (rule (f))

Fresh recursions whose arguments or results hold functions, so that the cost companions change
along the recursion:

* `fillSeq`: a table filled in list order at a value sampled before the recursive call and an
  entry decided by an `if`, passed to the recursive call by `Function.update` (the companion of
  the recursive call is an expression of the incoming companion and of the `if`); its erasure is
  proved with the induction hypotheses quantified over the sampled value and rewritten with the
  case hypothesis of the `if`;
* `chainOut`: the outputs of a chain of steps, each holding a table, collected by `Fin.cons`
  after the recursive call; `snocOut`: tables collected by `Fin.snoc`;
* `storeStep`: a record with a carrier-type field (`Store.T`) given as a binder, whose function
  fields over the carrier are applied as field paths.

Each erasure theorem is pinned by an `example`.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedRecordTest

open CatCrypt.Core

/-- The entries of the listed positions, filled in list order with a sampled bit. -/
noncomputable def fillSeq (tag : ℕ → Bool) (msg : ℕ → ℕ) :
    List ℕ → (ℕ → Option ℕ × Option ℕ) → SPTree (ℕ → Option ℕ × Option ℕ)
  | [], acc => .ret acc
  | i :: is, acc => .sample Bool inferInstance inferInstance fun b =>
      fillSeq tag msg is
        (Function.update acc i (some (if b then 1 else 0), if tag i then some (msg i) else none))

/-- The filled table passed to a distinguisher. -/
noncomputable def fillRed (tag : ℕ → Bool) (msg : ℕ → ℕ) (l : List ℕ)
    (D : (ℕ → Option ℕ × Option ℕ) → SPTree Bool) : SPTree Bool :=
  (fillSeq tag msg l fun _ => (none, none)).bind D

derive_timed fillRed

example (tag : ℕ → Bool) (tagCost msg msgCost : ℕ → ℕ) (l : List ℕ)
    (acc : ℕ → Option ℕ × Option ℕ) (accCost : ℕ → ℕ) :
    ((fillSeq.timed tag tagCost msg msgCost l acc accCost).2.erase.bind fun y => .ret y.1) =
      fillSeq tag msg l acc :=
  fillSeq.erase_timed tag tagCost msg msgCost l acc accCost

example (tag : ℕ → Bool) (tagCost msg msgCost : ℕ → ℕ) (l : List ℕ)
    (D : (ℕ → Option ℕ × Option ℕ) → SPTree.Timed Bool)
    (DCost : (ℕ → Option ℕ × Option ℕ) → ℕ) :
    (fillRed.timed tag tagCost msg msgCost l D DCost).2.erase =
      fillRed tag msg l fun a => (D a).erase :=
  fillRed.erase_timed tag tagCost msg msgCost l D DCost

/-- The outputs of a chain of steps collected by `Fin.cons`, each output holding a table. -/
noncomputable def chainOut : (n : ℕ) → ℕ → SPTree (Fin n → (ℕ → ℕ) × ℕ)
  | 0, _ => .ret Fin.elim0
  | n + 1, s => .sample Bool inferInstance inferInstance fun b =>
      (chainOut n (s + 1)).bind fun rest =>
        .ret (Fin.cons (Function.update (fun _ => 0) s (if b then 1 else 0), s) rest)

/-- The chain after a first output `(h, s)`. -/
noncomputable def chainRed (n : ℕ) (s : ℕ) (D : (Fin (n + 1) → (ℕ → ℕ) × ℕ) → SPTree Bool)
    (h : ℕ → ℕ) : SPTree Bool :=
  (chainOut n s).bind fun rest => D (Fin.cons (h, s) rest)

derive_timed chainRed

example (n s : ℕ) :
    ((chainOut.timed n s).2.erase.bind fun y => .ret fun a => ((y.1 a).1.1, (y.1 a).2)) =
      chainOut n s :=
  chainOut.erase_timed n s

example (n s : ℕ) (D : (Fin (n + 1) → (ℕ → ℕ) × ℕ) → SPTree.Timed Bool)
    (DCost : (Fin (n + 1) → (ℕ → ℕ) × ℕ) → ℕ) (h hCost : ℕ → ℕ) :
    (chainRed.timed n s D DCost h hCost).2.erase = chainRed n s (fun a => (D a).erase) h :=
  chainRed.erase_timed n s D DCost h hCost

/-- Tables collected by `Fin.snoc` after the recursive call. -/
noncomputable def snocOut : (n : ℕ) → SPTree (Fin n → (ℕ → ℕ))
  | 0 => .ret Fin.elim0
  | n + 1 => (snocOut n).bind fun rest => .sample Bool inferInstance inferInstance fun b =>
      .ret (Fin.snoc rest (fun _ => if b then 1 else 0))

/-- The collected tables passed to a distinguisher. -/
noncomputable def snocRed (n : ℕ) (D : (Fin n → (ℕ → ℕ)) → SPTree Bool) : SPTree Bool :=
  (snocOut n).bind D

derive_timed snocRed

example (n : ℕ) : ((snocOut.timed n).2.erase.bind fun y => .ret y.1) = snocOut n :=
  snocOut.erase_timed n

/-- A store with a carrier type and functions over it. -/
structure Store where
  /-- The carrier. -/
  T : Type
  /-- Insert a key. -/
  ins : T → ℕ → T
  /-- Read at a key. -/
  get : T → ℕ → ℕ

/-- Insert a key and read at it. -/
noncomputable def storeStep (s : Store) (t : s.T) (x : ℕ) (D : ℕ → SPTree Bool) : SPTree Bool :=
  D (s.get (s.ins t x) x)

derive_timed storeStep

/-- The fields over the carrier are field paths of the binder `s`, priced by their companions
over `s.T`: one plus the companion of each field applied. -/
example (s : Store) (t : s.T) (x : ℕ) (D : ℕ → SPTree.Timed Bool) (DCost : ℕ → ℕ)
    (getCost insCost : s.T → ℕ → ℕ) :
    (storeStep.timed s t x D DCost getCost insCost).2.erase =
      storeStep s t x fun a => (D a).erase :=
  storeStep.erase_timed s t x D DCost getCost insCost

/-! ## Carrier records along computed records (rule (g))

A record `Loc` holding a store `st : Store` and a tree `tree : st.T` of its carrier has no
mirror (a field's type depends on another field). Its store's fields, applied through a record
computed from a binder, are priced by the binder's companions:

* `locRed1`: through a structure update in a non-recursive definition (`Loc.add`), by reduction
  to the binder's path `l.st`;
* `locRed2`: through a recursion that keeps the store (`Loc.addAll`), by the equation
  `(Loc.addAll l xs).st = l.st`, proved by functional induction, along which the companion is
  cast;
* `rebaseRed`: a recursion that replaces the store is refused.
-/

/-- A party: a store, an identity and a tree of the store's carrier. -/
structure Loc where
  /-- The store. -/
  st : Store
  /-- The identity. -/
  me : ℕ
  /-- The tree. -/
  tree : st.T

/-- Insert a key into the tree. -/
def Loc.add (l : Loc) (x : ℕ) : Loc := { l with tree := l.st.ins l.tree x }

/-- Insert the keys of a list in order. -/
def Loc.addAll (l : Loc) : List ℕ → Loc
  | [] => l
  | x :: xs => (l.add x).addAll xs

/-- Read the tree at a key. -/
def Loc.read (l : Loc) (x : ℕ) : ℕ := l.st.get l.tree x

/-- Insert a key and read. -/
noncomputable def locRed1 (l : Loc) (x : ℕ) (D : ℕ → SPTree Bool) : SPTree Bool :=
  D ((l.add x).read 0)

derive_timed locRed1

example (l : Loc) (x : ℕ) (D : ℕ → SPTree.Timed Bool) (DCost : ℕ → ℕ)
    (insCost getCost : l.st.T → ℕ → ℕ) :
    (locRed1.timed l x D DCost insCost getCost).2.erase = locRed1 l x fun a => (D a).erase :=
  locRed1.erase_timed l x D DCost insCost getCost

/-- The insertion and the read are priced by the companions of the binder's store. -/
example (l : Loc) (x : ℕ) (D : ℕ → SPTree.Timed Bool) (DCost : ℕ → ℕ)
    (insCost getCost : l.st.T → ℕ → ℕ) :
    (locRed1.timed l x D DCost insCost getCost).1 =
      1 + (DCost ((l.add x).read 0) +
        (1 + (2 + insCost l.tree x + (1 + getCost (l.add x).tree 0)))) :=
  rfl

/-- Insert the keys of a list into a fresh party of the store `st`, and read. -/
noncomputable def locRed2 (st : Store) (t : st.T) (xs : List ℕ) (D : ℕ → SPTree Bool) :
    SPTree Bool :=
  D ((Loc.addAll ⟨st, 0, t⟩ xs).read 0)

derive_timed locRed2

example (st : Store) (t : st.T) (xs : List ℕ) (D : ℕ → SPTree.Timed Bool) (DCost : ℕ → ℕ)
    (insCost getCost : st.T → ℕ → ℕ) :
    (locRed2.timed st t xs D DCost insCost getCost).2.erase =
      locRed2 st t xs fun a => (D a).erase :=
  locRed2.erase_timed st t xs D DCost insCost getCost

/-- The cost of the recursion takes the companion of the insertion of the store it keeps. -/
noncomputable example (l : Loc) (xs : List ℕ) (insCost : l.st.T → ℕ → ℕ) : ℕ :=
  Loc.addAll.timedCost l xs insCost

/-- Move to the store `s` at each key. -/
def Loc.rebase (s : Store) (t : s.T) (l : Loc) : List ℕ → Loc
  | [] => l
  | x :: xs => Loc.rebase s t ⟨s, x, s.ins t (l.st.get l.tree x)⟩ xs

/-- The rebased party read. -/
noncomputable def rebaseRed (s : Store) (t : s.T) (l : Loc) (xs : List ℕ)
    (D : ℕ → SPTree Bool) : SPTree Bool :=
  D ((Loc.rebase s t l xs).read 0)

/--
error: derive_timed: needs a registered primitive:
`CatCrypt.Tactics.DeriveTimedRecordTest.Loc.rebase` is recursive and has no registered cost
`CatCrypt.Tactics.DeriveTimedRecordTest.Loc.rebase.timedCost`, and `derive_cost
CatCrypt.Tactics.DeriveTimedRecordTest.Loc.rebase` fails:
  derive_cost: the recursive call `Loc.rebase s t { st := s, me := #1, tree := s.ins t (l.st.get
  l.tree #1) }
    #0` changes a structure whose applied fields are priced by cost companions
-/
#guard_msgs (whitespace := lax) in
derive_timed rebaseRed

end CatCrypt.Tactics.DeriveTimedRecordTest
