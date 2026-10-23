/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Crypto.UC
import CatCryptCore.Core.SPTree

/-!
# Test of the erasure of a callee headed by an imported matcher

The tree that `derive_reduction` builds for `chacha20UCReduction`: the block is stored in a sum,
and the sum is passed to an auxiliary definition whose body is the matcher of `mapSum` (the
match obtained by unfolding `mapSum`, a definition of another module), with the heap reset to a
fixed heap. The auxiliary definition is called at a discriminant built from `Sum.inl`, where its
erasure theorem does not apply and both matches are reduced at the constructor.

## Main results

* `o10Cha.erase_timed` — the erasure theorem, derived in a `module` file
* `o10Cha.timeBound` — the time of the costed form
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedMatcherTest

open CatCrypt.Core CatCrypt.Crypto

/-- A block: a function of a lane index. -/
abbrev O10Blk := Fin 2 → ℕ

-- The test reproduces the auxiliary definition that `derive_reduction` generates, which applies
-- the matcher of `mapSum` by name.
set_option linter.auxLemma false in
/-- The match of `mapSum SPTree.ret A` on the output channel, as the auxiliary definition
`B.tree.match_1` of `derive_reduction`: the matcher of `mapSum` at the top. -/
noncomputable def o10ChaSel (A : Unit → SPTree Bool) (x : O10Blk ⊕ Unit) :
    SPTree (O10Blk ⊕ Bool) :=
  @mapSum.match_1 O10Blk Unit (fun _ => SPTree (O10Blk ⊕ Bool)) x
    (fun a => (SPTree.ret a).bind fun b => SPTree.ret (Sum.inl b))
    (fun c => (A c).bind fun b => SPTree.ret (Sum.inr b))

/-- The block stored in a sum, matched by `o10ChaSel` and passed to a distinguisher, with
the heap reset to `h`. -/
noncomputable def o10Cha (A : Unit → SPTree Bool) (D : O10Blk ⊕ Bool → SPTree Bool) (h : Heap)
    (s : O10Blk) : SPTree Bool :=
  SPTree.load h ((SPTree.ret (Sum.inl s : O10Blk ⊕ Unit)).bind fun o =>
    (o10ChaSel A o).bind D)

derive_timed o10Cha

example (A : Unit → SPTree.Timed Bool) (ACost : Unit → ℕ)
    (D : O10Blk ⊕ Bool → SPTree.Timed Bool) (DCost : O10Blk ⊕ Bool → ℕ) (h : Heap)
    (s : O10Blk) (sCost : Fin 2 → ℕ) :
    (o10Cha.timed A ACost D DCost h s sCost).2.erase =
      o10Cha (fun u => (A u).erase) (fun o => (D o).erase) h s :=
  o10Cha.erase_timed A ACost D DCost h s sCost

/-- The costed form of `o10Cha` takes the reset of the heap, the match, the time of the
distinguisher and its cost. -/
theorem o10Cha.timeBound (A : Unit → SPTree.Timed Bool) (ACost : Unit → ℕ)
    (D : O10Blk ⊕ Bool → SPTree.Timed Bool) (DCost : O10Blk ⊕ Bool → ℕ) (h : Heap)
    (s : O10Blk) (sCost : Fin 2 → ℕ) {T d : ℕ} (hD : ∀ o, (D o).time ≤ T)
    (hd : ∀ o, DCost o ≤ d) :
    SPTree.Timed.stepTime (o10Cha.timed A ACost D DCost h s sCost) ≤
      h.data.keys.card + T + d + 4 := by
  have := hD (Sum.inl s)
  have := hd (Sum.inl s)
  simp only [o10Cha.timed, SPTree.Timed.stepTime, SPTree.Timed.time_load,
    SPTree.Timed.bind, o10ChaSel.timed]
  simp [SPTree.Timed.delay, SPTree.Timed.bind]
  omega

end CatCrypt.Tactics.DeriveTimedMatcherTest
