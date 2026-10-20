/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.ExtractedAlgebra

/-!
# Interpreting extracted pairing-based dependencies

A hax extraction of pairing-based code leaves the group arithmetic of three groups
`G₁`, `G₂`, `GT` and the pairing `e : G₁ → G₂ → GT` as fields of a `<X>Deps` class over
`Array Int`. Below is an interpretation of these operations on the decoded values of
`CatCryptCore.Crypto.ExtractedAlgebra`: the group of `AlgVal` is the tagged union
`PairGrp G₁ G₂ GT` of the three groups, exponentiation acts on each group by its own
exponentiation, and the pairing decodes a `G₁` and a `G₂` element and encodes their
pairing in `GT`.

Hash calls are interpreted by functions: a hash of a raw byte input (an identity) into
`G₁`, and a hash of a `GT` element into a byte vector, encoded as the raw byte array
`Codec.vecArray n` (the extracted code reads its bytes by index).

Each operation carries a simp lemma `op (enc x) (enc y) = enc (x ⋆ y)`. Bilinearity is
not part of the interface: `PairingInterp.BilinearLeft` and `BilinearRight` state it as
propositions that a consumer proves for its pairing or takes as named premises.

## Main definitions

* `PairGrp G₁ G₂ GT` — an element of one of the three groups
* `PairingInterp G₁ G₂ GT S` — generators, exponentiations, the pairing and the codec
* `PairingInterp.toAlgInterp` — the underlying `AlgInterp`
* operations `generator₁`, `generator₂`, `pow`, `pair`, `hashG1`, `hashGtBytes`
* `PairingInterp.BilinearLeft`, `PairingInterp.BilinearRight` — bilinearity in each
  argument

## Main results

* `pow_g1`, `pow_g2`, `pow_gt`, `pair_enc`, `hashG1_eq`, `hashGtBytes_gt` — the
  operations on encodings
* `toG₁_enc`, `toG₂_enc`, `toGT_enc` — decoding an encoded group element
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Extracted

/-- An element of one of the three groups of a pairing. -/
inductive PairGrp (G₁ G₂ GT : Type) where
  | g1 (x : G₁)
  | g2 (y : G₂)
  | gt (z : GT)

namespace PairGrp

variable {G₁ G₂ GT : Type}

/-- The default element `g1 1`, the decoded value outside the image of a codec. -/
instance [One G₁] : One (PairGrp G₁ G₂ GT) := ⟨.g1 1⟩

/-- The `G₁` element, `1` for the other groups. -/
def toG₁ [One G₁] : PairGrp G₁ G₂ GT → G₁
  | g1 x => x
  | _ => 1

/-- The `G₂` element, `1` for the other groups. -/
def toG₂ [One G₂] : PairGrp G₁ G₂ GT → G₂
  | g2 y => y
  | _ => 1

/-- The `GT` element, `1` for the other groups. -/
def toGT [One GT] : PairGrp G₁ G₂ GT → GT
  | gt z => z
  | _ => 1

@[simp] theorem toG₁_g1 [One G₁] (x : G₁) : (g1 x : PairGrp G₁ G₂ GT).toG₁ = x := rfl
@[simp] theorem toG₂_g2 [One G₂] (y : G₂) : (g2 y : PairGrp G₁ G₂ GT).toG₂ = y := rfl
@[simp] theorem toGT_gt [One GT] (z : GT) : (gt z : PairGrp G₁ G₂ GT).toGT = z := rfl

end PairGrp

/-- The decoded values of an extracted pairing computation: an element of one of the
    three groups or an exponent. -/
abbrev PairVal (G₁ G₂ GT S : Type) := AlgVal (PairGrp G₁ G₂ GT) S Unit Unit

/-- An interpretation of extracted pairing-based dependencies: generators `gen₁`, `gen₂`,
    exponentiations of the three groups by exponents `S`, the pairing `e` and the codec of
    decoded values. -/
structure PairingInterp (G₁ G₂ GT S : Type) where
  /-- The generator of `G₁`. -/
  gen₁ : G₁
  /-- The generator of `G₂`. -/
  gen₂ : G₂
  /-- Exponentiation in `G₁`. -/
  pow₁ : G₁ → S → G₁
  /-- Exponentiation in `G₂`. -/
  pow₂ : G₂ → S → G₂
  /-- Exponentiation in `GT`. -/
  powT : GT → S → GT
  /-- The pairing. -/
  e : G₁ → G₂ → GT
  /-- The codec of decoded values. -/
  codec : Codec (PairVal G₁ G₂ GT S) (Array Int)

namespace PairingInterp

variable {G₁ G₂ GT S : Type} (I : PairingInterp G₁ G₂ GT S)

/-- Exponentiation of a group element in its own group. -/
def gpow : PairGrp G₁ G₂ GT → S → PairGrp G₁ G₂ GT
  | .g1 x, s => .g1 (I.pow₁ x s)
  | .g2 y, s => .g2 (I.pow₂ y s)
  | .gt z, s => .gt (I.powT z s)

/-- The interpretation as an `AlgInterp` over the union of the three groups, with
    generator `gen₁`, the trivial ambient ring and no opaque data. -/
def toAlgInterp [One G₁] : AlgInterp (PairGrp G₁ G₂ GT) S Unit Unit where
  gen := .g1 I.gen₁
  gpow := I.gpow
  embed _ := ()
  proj _ := 1
  codec := I.codec

variable [One G₁]

/-- The encoding of a decoded value. -/
abbrev enc (v : PairVal G₁ G₂ GT S) : Array Int := I.toAlgInterp.enc v

/-- The decoded value of a carrier value. -/
abbrev val (a : Array Int) : PairVal G₁ G₂ GT S := I.toAlgInterp.val a

/-- The `G₁` element of a carrier value. -/
def toG₁ (a : Array Int) : G₁ := (I.toAlgInterp.toG (I.val a)).toG₁

/-- The `G₂` element of a carrier value. -/
def toG₂ [One G₂] (a : Array Int) : G₂ := (I.toAlgInterp.toG (I.val a)).toG₂

/-- The `GT` element of a carrier value. -/
def toGT [One GT] (a : Array Int) : GT := (I.toAlgInterp.toG (I.val a)).toGT

@[simp] theorem toG₁_enc (x : G₁) : I.toG₁ (I.enc (.grp (.g1 x))) = x := by
  simp [toG₁, enc, val]

@[simp] theorem toG₂_enc [One G₂] (y : G₂) : I.toG₂ (I.enc (.grp (.g2 y))) = y := by
  simp [toG₂, enc, val]

@[simp] theorem toGT_enc [One GT] (z : GT) : I.toGT (I.enc (.grp (.gt z))) = z := by
  simp [toGT, enc, val]

/-- The encoded generator of `G₁`. -/
def generator₁ : Array Int := I.enc (.grp (.g1 I.gen₁))

/-- The encoded generator of `G₂`. -/
def generator₂ : Array Int := I.enc (.grp (.g2 I.gen₂))

/-- Exponentiation of the group element of the base, in its own group. -/
def pow [Zero S] (a s : Array Int) : Array Int := I.toAlgInterp.pow a s

/-- The pairing of the `G₁` element of the first argument and the `G₂` element of the
    second. -/
def pair [One G₂] (a b : Array Int) : Array Int :=
  I.enc (.grp (.gt (I.e (I.toG₁ a) (I.toG₂ b))))

/-- A hash of a raw input into `G₁`, interpreted by the function `H`. -/
def hashG1 (H : Array Int → G₁) (a : Array Int) : Array Int := I.enc (.grp (.g1 (H a)))

/-- A hash of a `GT` element into `n` bytes, interpreted by the function `H` and encoded
    as the raw byte array. -/
def hashGtBytes [One GT] {n : ℕ} (H : GT → Vector UInt8 n) (a : Array Int) : Array Int :=
  (Codec.vecArray n).enc (H (I.toGT a))

@[simp] theorem generator₁_eq : I.generator₁ = I.enc (.grp (.g1 I.gen₁)) := rfl

@[simp] theorem generator₂_eq : I.generator₂ = I.enc (.grp (.g2 I.gen₂)) := rfl

section Pow

variable [Zero S]

@[simp] theorem pow_g1 (x : G₁) (s : S) :
    I.pow (I.enc (.grp (.g1 x))) (I.enc (.exp s)) = I.enc (.grp (.g1 (I.pow₁ x s))) := by
  simp [pow, enc, toAlgInterp, gpow]

@[simp] theorem pow_g2 (y : G₂) (s : S) :
    I.pow (I.enc (.grp (.g2 y))) (I.enc (.exp s)) = I.enc (.grp (.g2 (I.pow₂ y s))) := by
  simp [pow, enc, toAlgInterp, gpow]

@[simp] theorem pow_gt (z : GT) (s : S) :
    I.pow (I.enc (.grp (.gt z))) (I.enc (.exp s)) = I.enc (.grp (.gt (I.powT z s))) := by
  simp [pow, enc, toAlgInterp, gpow]

end Pow

@[simp] theorem pair_enc [One G₂] (x : G₁) (y : G₂) :
    I.pair (I.enc (.grp (.g1 x))) (I.enc (.grp (.g2 y))) = I.enc (.grp (.gt (I.e x y))) := by
  simp [pair]

@[simp] theorem hashG1_eq (H : Array Int → G₁) (a : Array Int) :
    I.hashG1 H a = I.enc (.grp (.g1 (H a))) := rfl

@[simp] theorem hashGtBytes_gt [One GT] {n : ℕ} (H : GT → Vector UInt8 n) (z : GT) :
    I.hashGtBytes H (I.enc (.grp (.gt z))) = (Codec.vecArray n).enc (H z) := by
  simp [hashGtBytes]

/-- Bilinearity in the first argument: `e (x^s) y = (e x y)^s`. -/
def BilinearLeft : Prop := ∀ x y s, I.e (I.pow₁ x s) y = I.powT (I.e x y) s

/-- Bilinearity in the second argument: `e x (y^s) = (e x y)^s`. -/
def BilinearRight : Prop := ∀ x y s, I.e x (I.pow₂ y s) = I.powT (I.e x y) s

end PairingInterp

end CatCrypt.Crypto.Extracted
