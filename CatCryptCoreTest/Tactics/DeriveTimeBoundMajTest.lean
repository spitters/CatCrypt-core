/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.OracleProgUseBound
import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimeBound.Basic
public import CatCryptCore.Core.CostMajorant
public import CatCryptCore.Crypto.OracleAdversaryPotential
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.ForMathlib.ListLength
public import CatCryptCore.Tactics.StdCosts

/-!
# Tests of time bounds in majorants of cost companions

Fresh costed trees and oracle programs, none taken from a protocol. With the option
`derive_time_bound.majorants`, a cost companion whose argument holds a list is bounded by a
monotone majorant `M` in the length of its last list argument (`CatCrypt.Core.CostMaj`), and the
time bound is a term in `M` at the bounds of those lengths:

* `scanL`: the companion at a list built from a sampled bit, `M (l.length + 1) + 2`;
* `twoChk`: a conditional, the companion at `l` and at `l ++ l`;
* `logChk`: a binder program whose queries are answered by a handler with records
  (`collectLog`), followed by the companion at the log: the majorant at the bound `q * 2` of the
  length of the log, from the use bound of the binder (the bound is monotone in the majorant).

A uniform bound is the constant majorant (`costMaj_const_iff`): `scanL_uniform` is the time
theorem at `M := fun _ => t`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBoundMajTest

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Container OracleProg

/-- Check the list `l` extended by a sampled bit. -/
noncomputable def scanL (chk : List Bool → Bool) (l : List Bool) : SPTree Bool :=
  SPTree.sample Bool inferInstance inferInstance fun x => SPTree.ret (chk (x :: l))

derive_timed scanL

set_option derive_time_bound.majorants true in
derive_time_bound scanL

example (chk : List Bool → Bool) (chkCost : List Bool → ℕ) (l : List Bool) {M : ℕ → ℕ}
    (hM : Monotone M) (h : ∀ a, chkCost a ≤ M a.length) :
    SPTree.Timed.stepTime (scanL.timed chk chkCost l) ≤ M (l.length + 1) + 2 :=
  scanL.timeBound_timed chk chkCost l hM h

/-- A uniform bound of the companion is its constant majorant. -/
theorem scanL_uniform (chk : List Bool → Bool) (chkCost : List Bool → ℕ) (l : List Bool) {t : ℕ}
    (ht : ∀ a, chkCost a ≤ t) : SPTree.Timed.stepTime (scanL.timed chk chkCost l) ≤ t + 2 :=
  have h := (costMaj_const_iff (s := List.length)).2 ht
  scanL.timeBound_timed chk chkCost l (M_chkCost := fun _ => t) h.1 h.2

/-- Two checks, the second at the list doubled. -/
noncomputable def twoChk (chk : ℕ → List Bool → Bool) (n : ℕ) (l : List Bool) : SPTree Bool :=
  if chk n l then SPTree.ret true else SPTree.ret (chk (n + 1) (l ++ l))

derive_timed twoChk

set_option derive_time_bound.majorants true in
derive_time_bound twoChk

example := @twoChk.timeBound_timed

/-- A handler program with records: one query on `i`, at step cost `1`, and the record
`[i, i]`. -/
def hrec (i : ℕ) : ℕ × Timed ℕ ℕ (ℕ × List ℕ) :=
  (0, .query i (fun _ => 1) fun o => .pure (o, [i, i]))

/-- The name of `logChk.timed`. -/
def logChk : Unit := ()

/-- The binder program `A x` with its queries answered by `hrec`, followed by a step whose cost is
the cost companion `logCost` at the collected records. -/
def logChk.timed (A : ℕ → Timed ℕ ℕ ℕ) (x : ℕ) (logCost : List ℕ → ℕ) : ℕ × Timed ℕ ℕ ℕ :=
  Timed.delay (1 + (Timed.collectLog hrec (A x)).1)
    ((Timed.collectLog hrec (A x)).2.bind fun al => (logCost al.2, .pure al.1))

set_option derive_time_bound.majorants true in
derive_time_bound +queries logChk

example := @logChk.timeBound_timed

end CatCrypt.Tactics.DeriveTimeBoundMajTest
