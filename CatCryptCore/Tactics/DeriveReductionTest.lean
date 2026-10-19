/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction

/-!
# Tests for `derive_reduction`

Reductions written in `do`-notation over `SPComp`, with adversaries as function binders. For
each, the command defines the computation tree `B.tree`, proves `B.compile_tree` and runs
`derive_timed B.tree`; the statements of the compile equation and of the erasure theorem are
pinned by `example`s. The shapes are a DDH-style reduction (a uniform sample, group
operations given as a binder, one adversary call), a reduction with two adversary calls and a
second adversary, a reduction with `match` and `if`, a reduction reading and writing a
location, and a reduction that calls a top-level `def` written in `do`-notation, with the
adversary named explicitly. The last test pins the refusal of an unpriced computation, a
field of a structure.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveReductionTest

open CatCrypt.Core

/-! ## A DDH-style reduction -/

/-- On a DDH triple `(gx, gy, gz)`, mask the message `m` with `gz` and a fresh uniform `r`,
call the adversary on the public key and the ciphertext, and return the negation of its
guess. The group operation is the binder `mul`. -/
noncomputable def ddhRed {G : Type} [Fintype G] [Nonempty G] (mul : G → G → G) (m : G)
    (A : G × G × G → SPComp Bool) (gx gy gz : G) : SPComp Bool := do
  let r ← SPComp.sample G
  let b ← A (gx, gy, mul m (mul gz r))
  return !b

derive_reduction ddhRed

example {G : Type} [Fintype G] [Nonempty G] (mul : G → G → G) (m : G)
    (A : G × G × G → SPTree Bool) (gx gy gz : G) :
    (ddhRed.tree mul m A gx gy gz).compile = ddhRed mul m (fun x => (A x).compile) gx gy gz :=
  ddhRed.compile_tree mul m A gx gy gz

example {G : Type} [Fintype G] [Nonempty G] (mul : G → G → G) (mulCost : G → G → ℕ) (m : G)
    (A : G × G × G → SPTree.Timed Bool) (ACost : G × G × G → ℕ) (gx gy gz : G) :
    (ddhRed.tree.timed mul mulCost m A ACost gx gy gz).2.erase =
      ddhRed.tree mul m (fun x => (A x).erase) gx gy gz :=
  ddhRed.tree.erase_timed mul mulCost m A ACost gx gy gz

/-! ## Two adversary calls and a second adversary -/

/-- Call `A` twice, the second time on the first answer, and pass the conjunction of the
answers to `B`. -/
noncomputable def twoCall (A : Bool → SPComp Bool) (B : Bool → ℕ → SPComp ℕ) : SPComp ℕ := do
  let x ← A true
  let y ← A x
  B (x && y) 3

derive_reduction twoCall

example (A : Bool → SPTree Bool) (B : Bool → ℕ → SPTree ℕ) :
    (twoCall.tree A B).compile = twoCall (fun x => (A x).compile) (fun x n => (B x n).compile) :=
  twoCall.compile_tree A B

/-! ## `match` and `if` -/

/-- Call the adversary on `n`; on an answer `some k` return `k` when `k < n` and fail
otherwise, on `none` return `0`. -/
noncomputable def branchRed (A : ℕ → SPComp (Option ℕ)) (n : ℕ) : SPComp ℕ := do
  let o ← A n
  match o with
  | some k => if k < n then return k else SPComp.fail
  | none => return 0

derive_reduction branchRed

example (A : ℕ → SPTree (Option ℕ)) (n : ℕ) :
    (branchRed.tree A n).compile = branchRed (fun x => (A x).compile) n :=
  branchRed.compile_tree A n

example (A : ℕ → SPTree.Timed (Option ℕ)) (ACost : ℕ → ℕ) (n : ℕ) :
    (branchRed.tree.timed A ACost n).2.erase = branchRed.tree (fun x => (A x).erase) n :=
  branchRed.tree.erase_timed A ACost n

/-! ## `get` and `set` -/

/-- Read the location `l`, write `upd` of the value back, and call the adversary on the old
value. -/
noncomputable def stateRed (l : Location) (upd : l.ty → l.ty) (A : l.ty → SPComp Bool) :
    SPComp Bool := do
  let v ← SPComp.get l
  SPComp.set l (upd v)
  A v

derive_reduction stateRed

example (l : Location) (upd : l.ty → l.ty) (A : l.ty → SPTree Bool) :
    (stateRed.tree l upd A).compile = stateRed l upd (fun x => (A x).compile) :=
  stateRed.compile_tree l upd A

/-! ## A called definition and an explicit adversary -/

/-- Mask `b` with a uniform bit and call the adversary. -/
noncomputable def maskThen (A : Bool → SPComp Bool) (b : Bool) : SPComp Bool := do
  let c ← SPComp.sample Bool
  A (xor b c)

/-- Post-process `w` with `post` and continue with `maskThen A`. Both `post` and `A` are
functions into `SPComp`, so both are adversaries. -/
noncomputable def postRed (post : Bool → SPComp Bool) (A : Bool → SPComp Bool) :
    Bool → SPComp Bool :=
  fun w => (post w).bind (maskThen A)

derive_reduction postRed (adv := post A)

example (post A : Bool → SPTree Bool) (w : Bool) :
    (postRed.tree post A w).compile =
      postRed (fun x => (post x).compile) (fun x => (A x).compile) w :=
  postRed.compile_tree post A w

/-! ## Refusal of an unpriced computation -/

/-- An adversary given as a structure. -/
structure GuessAdv where
  guess : Bool → SPComp Bool

/-- A reduction calling a field of a structure, which is not an adversary binder. -/
noncomputable def fieldRed (A : GuessAdv) (b : Bool) : SPComp Bool := A.guess b

/--
error: derive_reduction: unpriced computation: the subterm
  A.guess b
unfolds to
  A.1 b
which is not built from `pure`, `bind`, `sample`, `get`, `set`, `fail`, `if`, `match` or a call of an adversary
-/
#guard_msgs in
derive_reduction fieldRed

end CatCrypt.Tactics.DeriveReductionTest
