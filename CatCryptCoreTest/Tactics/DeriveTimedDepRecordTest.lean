/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Tests for erasure along computed companions under a node (rule (h))

`sealSeq` fills a table in list order. At each position it calls the computation `S.wrap` of a
record `S` (a tree binder of the derived tree, so the source's functional induction runs at the
call of the source in the goal) and passes the table updated at the value that the call returns
to the recursive call. The costed form passes the recursive call a companion computed from the
incoming one (`fun a => … + if a = i then 0 else 1 + accCost a`), under the binder of the node.
The erasure theorem is proved by functional induction on the source generalizing the
companions, with the induction hypothesis rewritten by the case hypothesis of the `if` on the
tag.

Each erasure theorem is pinned by an `example`. A carrier record read from an optional table
entry, outside the class of rule (g), is refused (`cellRed`, pinned by `#guard_msgs`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedDepRecordTest

open CatCrypt.Core

/-- A sealing scheme: seals, keys and a probabilistic sealing of a message. -/
structure Sealer (M : Type) where
  /-- The seals. -/
  Seal : Type
  /-- The keys. -/
  Key : Type
  /-- Seal a message. -/
  wrap : M → SPComp (Seal × Key)

/-- Seal `msg i` at every listed position `i`, recording the key where `tag i` holds. -/
noncomputable def sealSeq {M : Type} (S : Sealer M) (tag : ℕ → Bool) (msg : ℕ → M) :
    List ℕ → (ℕ → Option S.Seal × Option (M × S.Key)) →
      SPComp (ℕ → Option S.Seal × Option (M × S.Key))
  | [], acc => SPComp.pure acc
  | i :: is, acc => SPComp.bind (S.wrap (msg i)) fun co =>
      sealSeq S tag msg is
        (Function.update acc i (some co.1, if tag i then some (msg i, co.2) else none))

/-- Seal at every listed position, from the empty table. -/
noncomputable def sealAll {M : Type} (S : Sealer M) (tag : ℕ → Bool) (msg : ℕ → M)
    (l : List ℕ) : SPComp (ℕ → Option S.Seal × Option (M × S.Key)) :=
  sealSeq S tag msg l fun _ => (none, none)

derive_reduction sealAll

example {M : Type} (S : Sealer M) (tag : ℕ → Bool) (tagCost : ℕ → ℕ) (msg : ℕ → M)
    (msgCost : ℕ → ℕ) (l : List ℕ) (acc : ℕ → Option S.Seal × Option (M × S.Key))
    (accCost : ℕ → ℕ) (wrap : M → SPTree.Timed (S.Seal × S.Key)) (wrapCost : M → ℕ) :
    ((sealSeq.tree.timed S tag tagCost msg msgCost l acc accCost wrap wrapCost).2.erase.bind
        fun y => SPTree.ret y.1) =
      sealSeq.tree S tag msg l acc fun a => (wrap a).erase :=
  sealSeq.tree.erase_timed S tag tagCost msg msgCost l acc accCost wrap wrapCost

example {M : Type} (S : Sealer M) (tag : ℕ → Bool) (tagCost : ℕ → ℕ) (msg : ℕ → M)
    (msgCost : ℕ → ℕ) (l : List ℕ) (wrap : M → SPTree.Timed (S.Seal × S.Key))
    (wrapCost : M → ℕ) :
    ((sealAll.tree.timed S tag tagCost msg msgCost l wrap wrapCost).2.erase.bind
        fun y => SPTree.ret y.1) =
      sealAll.tree S tag msg l fun a => (wrap a).erase :=
  sealAll.tree.erase_timed S tag tagCost msg msgCost l wrap wrapCost

example {M : Type} (S : Sealer M) (tag : ℕ → Bool) (msg : ℕ → M) (l : List ℕ)
    (wrap : M → SPTree (S.Seal × S.Key)) (h : ∀ a, (wrap a).compile = S.wrap a) :
    (sealAll.tree S tag msg l wrap).compile = sealAll S tag msg l :=
  sealAll.compile_tree S tag msg l wrap h

/-! ## A carrier record read from a table (outside the class of rule (g))

`cellRed` reads a record `Cell` (a box with a carrier type and a value of its carrier) from an
optional table entry and applies the box's functions to the value. The record has no binder
path, so its function fields have no companion (rule (g) needs a binder path), and an optional
structure is a table (`hatTy?`). The refusal is pinned; the dependent mirror that would carry
the companions of the box's functions inside the entry is not implemented.
-/

/-- A box: a carrier with an insertion and a read. -/
structure Box where
  /-- The carrier. -/
  T : Type
  /-- Insert a key. -/
  put : T → ℕ → T
  /-- Read at a key. -/
  read : T → ℕ → ℕ

/-- A box and a value of its carrier. -/
structure Cell where
  /-- The box. -/
  bx : Box
  /-- The value. -/
  val : bx.T

/-- Read the entry of `p`, insert `x` into its value and read at `x`. -/
noncomputable def cellRed (tab : ℕ → Option Cell) (p x : ℕ) (D : ℕ → SPTree Bool) :
    SPTree Bool :=
  match tab p with
  | some c => D (c.bx.read (c.bx.put c.val x) x)
  | none => D 0

/--
error: derive_timed: a function bound in data: the field
`CatCrypt.Tactics.DeriveTimedDepRecordTest.Box.read` is applied in `c.bx.read
  (c.bx.put c.val x) x`
-/
#guard_msgs (whitespace := lax) in
derive_timed cellRed

end CatCrypt.Tactics.DeriveTimedDepRecordTest
