/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Schnorr
public import CatCryptCore.Crypto.PAKE.DHExtractKit

/-!
# Schnorr over a Diffie–Hellman group

A `DHGroup S W` (scalars a field `S`, group `W` in exponent form) with finite scalars and
decidable equality is a `GroupParam`: the generator is `pub 1`, the identity is `pub 0`, group
inversion is `Y ↦ Y^(−1)`, and the scalar operations are those of the field `S`. The Schnorr
Σ-protocol at this parameter has statements `W`, witnesses `S`, and relation `pub s = Y`.

## Main definitions

* `GroupParam.ofDHGroup G` — the group parameters of `G : DHGroup S W`

## Main results

* `schnorrSigma_ofDHGroup_rel` — the relation of Schnorr at `ofDHGroup G` is `G.pub s = Y`
* `schnorrSigma_ofDHGroup_specialSound`, `_complete`, `_uniqueResp`, `_perfectHVZK`,
  `_commitBound` — the properties of `schnorrSigma` at `ofDHGroup G`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.GroupParam

open CatCrypt.Crypto.PAKE.DHExtract

variable {S W : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]

/-- The group parameters of a Diffie–Hellman group `G`: carrier `W`, scalars `S`, generator
`pub 1`, identity `pub 0`, `exp = pub`, `groupExp = G.exp`, group operation `G.mul`, group
inverse `Y ↦ Y^(−1)`, and the field operations of `S`. -/
def ofDHGroup (G : DHGroup S W) : GroupParam :=
  letI : Fintype W := Fintype.ofEquiv S G.pub
  { G := W
    Scalar := S
    neG := ⟨G.pub 0⟩
    generator := G.pub 1
    identity := G.pub 0
    exp := G.pub
    groupExp := G.exp
    scalarAdd := (· + ·)
    scalarMul := (· * ·)
    scalarSub := (· - ·)
    scalarDiv := (· / ·)
    scalarNeg := (- ·)
    scalarZero := 0
    groupMul := G.mul
    groupInv := fun Y => G.exp Y (-1)
    scalarOne := 1
    exp_add := fun x y => (G.mul_pub x y).symm
    exp_zero := rfl
    div_mul_cancel := fun x y hy => div_mul_cancel₀ x hy
    groupExp_generator := fun x => by rw [G.exp_pub, one_mul]
    groupExp_exp := fun w e => G.exp_pub w e
    groupExp_one := fun h => by rw [G.exp_eq, mul_one, G.pub_dlog]
    groupExp_add := fun h a b => by
      simp only [G.exp_eq, G.mul_eq, DHGroup.dlog_pub, mul_add]
    scalarSub_ne_zero := fun a b hab => sub_ne_zero.mpr hab
    groupMul_identity := fun a => G.mul_pub_zero a
    identity_groupMul := fun a => G.pub_zero_mul a
    groupMul_inv := fun a => G.mul_exp_neg_one a
    inv_groupMul := fun a => by rw [G.mul_comm]; exact G.mul_exp_neg_one a
    groupMul_assoc := fun a b c => G.mul_assoc a b c
    groupExp_zero := fun h => by rw [G.exp_eq, mul_zero]
    scalarMul_one := fun a => mul_one a
    groupInv_groupExp := fun h e => by rw [G.exp_exp, mul_neg_one]
    scalarSub_eq := fun a b => sub_eq_add_neg a b
    scalarAdd_neg := fun a => add_neg_cancel a
    exp_surj := fun h => ⟨G.pub.symm h, G.pub.apply_symm_apply h⟩
    exp_inj := fun x y h => G.pub.injective h
    scalarAdd_comm := fun a b => add_comm a b
    scalarAdd_assoc := fun a b c => add_assoc a b c
    scalarMul_add := fun a b c => mul_add a b c
    scalarAdd_mul := fun a b c => add_mul a b c
    scalarMul_comm := fun a b => mul_comm a b
    scalarAdd_zero := fun a => add_zero a
    scalarZero_add := fun a => zero_add a
    scalarNeg_add := fun a => neg_add_cancel a
    scalarNeg_zero := neg_zero
    scalarNeg_add_distrib := fun a b => neg_add a b
    scalarMul_zero := fun a => mul_zero a
    scalarZero_mul := fun a => zero_mul a
    mul_div_cancel := fun a b hb => mul_div_cancel_right₀ a hb
    scalarMul_assoc := fun a b c => mul_assoc a b c }

end CatCrypt.Examples.GroupParam

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Crypto CatCrypt.Examples CatCrypt.Crypto.PAKE.DHExtract

variable {S W : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W] (G : DHGroup S W)

/-- The relation of Schnorr at `ofDHGroup G` is the key relation of the Diffie–Hellman group:
the statement `Y` has witness `s` iff `G.pub s = Y`. -/
theorem schnorrSigma_ofDHGroup_rel (Y : W) (s : S) :
    (schnorrSigma (GroupParam.ofDHGroup G)).rel Y s ↔ G.pub s = Y :=
  Iff.rfl

/-- Schnorr at `ofDHGroup G` is special sound. -/
theorem schnorrSigma_ofDHGroup_specialSound :
    (schnorrSigma (GroupParam.ofDHGroup G)).SpecialSound :=
  schnorrSigma_specialSound _

/-- Schnorr at `ofDHGroup G` is complete. -/
theorem schnorrSigma_ofDHGroup_complete :
    (schnorrSigma (GroupParam.ofDHGroup G)).Complete :=
  schnorrSigma_complete _

/-- Schnorr at `ofDHGroup G` has unique responses. -/
theorem schnorrSigma_ofDHGroup_uniqueResp :
    (schnorrSigma (GroupParam.ofDHGroup G)).UniqueResp :=
  schnorrSigma_uniqueResp _

/-- Schnorr at `ofDHGroup G` is perfect honest-verifier zero-knowledge. -/
theorem schnorrSigma_ofDHGroup_perfectHVZK :
    (schnorrSigma (GroupParam.ofDHGroup G)).PerfectHVZK :=
  schnorrSigma_perfectHVZK _

/-- Each commitment of Schnorr at `ofDHGroup G` has probability `1/|S|`. -/
theorem schnorrSigma_ofDHGroup_commitBound :
    (schnorrSigma (GroupParam.ofDHGroup G)).CommitBound (1 / Fintype.card S) :=
  schnorrSigma_commitBound _

end CatCrypt.Crypto.FiatShamirROM
