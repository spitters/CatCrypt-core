/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Fintype.EquivFin

/-!
# Interpreting extracted algebraic dependencies

A hax extraction leaves the algebra a crate calls as the fields of a `<X>Deps` class over
untyped carriers: `Array Int` (byte arrays) and `Vector UInt8 n`. Below are the
codecs between typed values and these carriers, and an interpretation of the untyped
operations through a group, its exponents and an ambient commutative ring.

A decoded value (`AlgVal`) is a group element, a ring element, an exponent or an opaque
datum, written on the carrier with a one-entry tag. The interpreted operations decode
their arguments, compute in the typed algebra and encode the result: group
multiplication of two group elements, ring multiplication otherwise (group elements
enter the ring through `embed`), exponentiation of the group element `proj`-ected from
the base, and addition and multiplication of exponents. Each operation carries a simp
lemma `op (enc x) (enc y) = enc (x ⋆ y)`, so a computation of an extracted function
under the interpretation reduces by `simp` to the typed computation.

## Main definitions

* `Codec α β` — an encoding `α → β` with a partial decoding, `dec (enc a) = some a`
* `Codec.ofEquiv`, `Codec.comp`, `Codec.fintypeNat`, `Codec.fintypeFin` — combinators
* `Codec.nat` — natural numbers as little-endian base-256 digit arrays in `Array Int`
* `Codec.vecArray` — `Vector UInt8 n` as an `Array Int` of byte values
* `Codec.finVec` — `Fin (256 ^ n)` as `Vector UInt8 n`
* `Codec.fintypeArray`, `Codec.fintypeVec` — any finite type into either carrier
* `Codec.fintypeEntry` — a finite type as one `Array Int` entry
* `AlgVal G S R K` — the decoded values; `AlgVal.codec` — the tagged codec
* `AlgInterp G S R K` — generator, exponentiation, `embed`/`proj` and the value codec;
  its operations `mul`, `add`, `sub`, `pow`, `generator`, `expAdd`, `expMul`, `hash1`,
  `hash2`, `const`

## Main results

* `Codec.enc_injective` — an encoding is injective
* `AlgInterp.val_enc` — decoding an encoded value returns it
* `AlgInterp.mul_grp_grp`, `mul_ring_grp`, `pow_grp`, `pow_ring`, `add_ring_grp`,
  `sub_ring_ring`, `expAdd_exp`, `expMul_exp`, `hash1_enc`, `hash2_enc` and the other
  operation lemmas
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Extracted

/-! ## Codecs -/

/-- An encoding of `α` into the carrier `β` with a partial decoding that inverts it. -/
structure Codec (α β : Type) where
  /-- The encoding. -/
  enc : α → β
  /-- The decoding; `none` on carrier values outside the image. -/
  dec : β → Option α
  dec_enc : ∀ a, dec (enc a) = some a

attribute [simp] Codec.dec_enc

namespace Codec

variable {α β γ : Type}

/-- An encoding is injective. -/
theorem enc_injective (c : Codec α β) : Function.Injective c.enc := fun a b h => by
  simpa using congrArg c.dec h

/-- The decoding with a default value on carrier values outside the image. -/
noncomputable def decD [Nonempty α] (c : Codec α β) (b : β) : α :=
  (c.dec b).getD (Classical.arbitrary α)

@[simp] theorem decD_enc [Nonempty α] (c : Codec α β) (a : α) : c.decD (c.enc a) = a := by
  simp [decD]

/-- The codec of an equivalence. -/
def ofEquiv (e : α ≃ β) : Codec α β where
  enc := e
  dec b := some (e.symm b)
  dec_enc a := by simp

/-- Encoding into `β` and then into `γ`. -/
def comp (c₁ : Codec α β) (c₂ : Codec β γ) : Codec α γ where
  enc a := c₂.enc (c₁.enc a)
  dec c := (c₂.dec c).bind c₁.dec
  dec_enc a := by simp

/-- A finite type as an initial segment of `ℕ`, through `Fintype.equivFin`. -/
noncomputable def fintypeNat (α : Type) [Fintype α] [DecidableEq α] : Codec α ℕ where
  enc a := (Fintype.equivFin α a : ℕ)
  dec n := if h : n < Fintype.card α then some ((Fintype.equivFin α).symm ⟨n, h⟩) else none
  dec_enc a := by simp

/-- A finite type of at most `m` elements in `Fin m`. -/
noncomputable def fintypeFin {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (h : Fintype.card α ≤ m) : Codec α (Fin m) where
  enc a := Fin.castLE h (Fintype.equivFin α a)
  dec i := (fintypeNat α).dec i
  dec_enc a := by simp [fintypeNat]

/-! ### The carriers `Array Int` and `Vector UInt8 n` -/

/-- Natural numbers as their little-endian base-256 digits in `Array Int`. -/
def nat : Codec ℕ (Array Int) where
  enc n := ((Nat.digits 256 n).map (fun d : ℕ => (d : Int))).toArray
  dec a := some (Nat.ofDigits 256 (a.toList.map Int.toNat))
  dec_enc n := by simp [Function.comp_def, Nat.ofDigits_digits]

/-- A byte vector as the `Array Int` of its byte values; decoding requires the length
    `n` and entries in `[0, 256)`. -/
def vecArray (n : ℕ) : Codec (Vector UInt8 n) (Array Int) where
  enc v := v.toArray.map fun b => (b.toNat : Int)
  dec a := if h : a.size = n then some ⟨a.map fun i => UInt8.ofNat i.toNat, by simp [h]⟩
    else none
  dec_enc v := by
    simp only [Array.size_map, Vector.size_toArray, dite_true, Option.some.injEq]
    ext i hi
    simp

/-- `UInt8` is `Fin 256`. -/
def uint8EquivFin : UInt8 ≃ Fin 256 where
  toFun b := b.toFin
  invFun i := UInt8.ofFin i
  left_inv b := by simp
  right_inv i := by simp

/-- A vector is the function of its entries. -/
def vectorEquivFun (α : Type) (n : ℕ) : Vector α n ≃ (Fin n → α) where
  toFun v i := v[i]
  invFun f := Vector.ofFn f
  left_inv v := by ext i hi; simp
  right_inv f := by funext i; simp

/-- `Fin (256 ^ n)` as `n` little-endian bytes. -/
def finVec (n : ℕ) : Codec (Fin (256 ^ n)) (Vector UInt8 n) :=
  ofEquiv (finFunctionFinEquiv.symm.trans
    ((Equiv.arrowCongr (Equiv.refl _) uint8EquivFin.symm).trans (vectorEquivFun UInt8 n).symm))

/-- A finite type in `Array Int`. -/
noncomputable def fintypeArray (α : Type) [Fintype α] [DecidableEq α] : Codec α (Array Int) :=
  (fintypeNat α).comp nat

/-- A finite type as one `Array Int` entry, its index in `Fintype.equivFin`. -/
noncomputable def fintypeEntry (α : Type) [Fintype α] [DecidableEq α] : Codec α (Array Int) where
  enc a := #[((fintypeNat α).enc a : Int)]
  dec v := match v.toList with
    | [i] => (fintypeNat α).dec i.toNat
    | _ => none
  dec_enc a := by simp

/-- A finite type of at most `256 ^ n` elements in `Vector UInt8 n`. -/
noncomputable def fintypeVec {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (h : Fintype.card α ≤ 256 ^ n) : Codec α (Vector UInt8 n) :=
  (fintypeFin h).comp (finVec n)

end Codec

/-! ## Decoded values -/

/-- A value of an extracted algebraic computation: a group element, an element of the
    ambient ring, an exponent, or an opaque datum (a hash output). -/
inductive AlgVal (G S R K : Type) where
  | grp (g : G)
  | ring (r : R)
  | exp (s : S)
  | dat (k : K)

namespace AlgVal

variable {G S R K : Type}

/-- The tagged codec: the tag `0`, `1`, `2`, `3` of the constructor followed by the
    encoding of the argument. -/
def codec (cG : Codec G (Array Int)) (cS : Codec S (Array Int)) (cR : Codec R (Array Int))
    (cK : Codec K (Array Int)) : Codec (AlgVal G S R K) (Array Int) where
  enc
    | grp g => #[0] ++ cG.enc g
    | ring r => #[1] ++ cR.enc r
    | exp s => #[2] ++ cS.enc s
    | dat k => #[3] ++ cK.enc k
  dec a := match a.toList with
    | [] => none
    | t :: rest =>
      if t = 0 then (cG.dec rest.toArray).map grp
      else if t = 1 then (cR.dec rest.toArray).map ring
      else if t = 2 then (cS.dec rest.toArray).map exp
      else if t = 3 then (cK.dec rest.toArray).map dat
      else none
  dec_enc v := by cases v <;> simp

/-- The exponent of a value, `0` for the other kinds. -/
def toS [Zero S] : AlgVal G S R K → S
  | exp s => s
  | _ => 0

/-- The datum of a value, an arbitrary element for the other kinds. -/
noncomputable def toK [Nonempty K] : AlgVal G S R K → K
  | dat k => k
  | _ => Classical.arbitrary K

@[simp] theorem toS_exp [Zero S] (s : S) : (exp s : AlgVal G S R K).toS = s := rfl
@[simp] theorem toK_dat [Nonempty K] (k : K) : (dat k : AlgVal G S R K).toK = k := rfl

end AlgVal

/-! ## The interpretation -/

/-- An interpretation of extracted algebraic dependencies: a group `G` with generator
    `gen` and exponentiation `gpow` by exponents `S`, an ambient commutative ring `R`
    with the inclusion `embed : G → R` and a left inverse `proj` on its image, opaque
    data `K`, and the codec of decoded values. -/
structure AlgInterp (G S R K : Type) where
  /-- The generator. -/
  gen : G
  /-- Exponentiation `gpow g s = g^s`. -/
  gpow : G → S → G
  /-- The inclusion of the group into the ring. -/
  embed : G → R
  /-- A left inverse of `embed` on its image. -/
  proj : R → G
  /-- The codec of decoded values. -/
  codec : Codec (AlgVal G S R K) (Array Int)

namespace AlgInterp

variable {G S R K : Type} (I : AlgInterp G S R K)

/-- The encoding of a decoded value. -/
def enc (v : AlgVal G S R K) : Array Int := I.codec.enc v

/-- The decoded value of a carrier value; `grp 1` outside the image of the codec. -/
def val [One G] (a : Array Int) : AlgVal G S R K := (I.codec.dec a).getD (.grp 1)

@[simp] theorem val_enc [One G] (v : AlgVal G S R K) : I.val (I.enc v) = v := by
  simp [val, enc]

/-- The group element of a value: `proj` of a ring element, `1` for the other kinds. -/
def toG [One G] : AlgVal G S R K → G
  | .grp g => g
  | .ring r => I.proj r
  | _ => 1

/-- The ring element of a value: `embed` of a group element, `0` for the other kinds. -/
def toR [Zero R] : AlgVal G S R K → R
  | .grp g => I.embed g
  | .ring r => r
  | _ => 0

@[simp] theorem toG_grp [One G] (g : G) : I.toG (.grp g) = g := rfl
@[simp] theorem toG_ring [One G] (r : R) : I.toG (.ring r) = I.proj r := rfl
@[simp] theorem toR_grp [Zero R] (g : G) : I.toR (.grp g) = I.embed g := rfl
@[simp] theorem toR_ring [Zero R] (r : R) : I.toR (.ring r) = r := rfl

/-- Multiplication: in the group when both arguments are group elements, in the ring
    otherwise. -/
def mul [One G] [Mul G] [Zero R] [Mul R] (a b : Array Int) : Array Int :=
  match I.val a, I.val b with
  | .grp x, .grp y => I.enc (.grp (x * y))
  | u, v => I.enc (.ring (I.toR u * I.toR v))

/-- Ring addition. -/
def add [One G] [Zero R] [Add R] (a b : Array Int) : Array Int :=
  I.enc (.ring (I.toR (I.val a) + I.toR (I.val b)))

/-- Ring subtraction. -/
def sub [One G] [Zero R] [Sub R] (a b : Array Int) : Array Int :=
  I.enc (.ring (I.toR (I.val a) - I.toR (I.val b)))

/-- Exponentiation of the group element of the base. -/
def pow [One G] [Zero S] (a e : Array Int) : Array Int :=
  I.enc (.grp (I.gpow (I.toG (I.val a)) (I.val e).toS))

/-- The encoded generator. -/
def generator : Array Int := I.enc (.grp I.gen)

/-- Exponent addition. -/
def expAdd [One G] [Zero S] [Add S] (a b : Array Int) : Array Int :=
  I.enc (.exp ((I.val a).toS + (I.val b).toS))

/-- Exponent multiplication. -/
def expMul [One G] [Zero S] [Mul S] (a b : Array Int) : Array Int :=
  I.enc (.exp ((I.val a).toS * (I.val b).toS))

/-- A one-input hash interpreted by a function on decoded values. -/
def hash1 [One G] (h : AlgVal G S R K → AlgVal G S R K) (a : Array Int) : Array Int :=
  I.enc (h (I.val a))

/-- A two-input hash interpreted by a function on decoded values. -/
def hash2 [One G] (h : AlgVal G S R K → AlgVal G S R K → AlgVal G S R K) (a b : Array Int) :
    Array Int :=
  I.enc (h (I.val a) (I.val b))

/-- A constant. -/
def const (v : AlgVal G S R K) : Array Int := I.enc v

section Ops

variable [One G]

@[simp] theorem hash1_enc (h : AlgVal G S R K → AlgVal G S R K) (v : AlgVal G S R K) :
    I.hash1 h (I.enc v) = I.enc (h v) := by
  simp [hash1]

@[simp] theorem hash2_enc (h : AlgVal G S R K → AlgVal G S R K → AlgVal G S R K)
    (v w : AlgVal G S R K) : I.hash2 h (I.enc v) (I.enc w) = I.enc (h v w) := by
  simp [hash2]

section Mul

variable [Mul G] [Zero R] [Mul R]

@[simp] theorem mul_grp_grp (x y : G) :
    I.mul (I.enc (.grp x)) (I.enc (.grp y)) = I.enc (.grp (x * y)) := by
  simp [mul]

@[simp] theorem mul_ring_grp (r : R) (y : G) :
    I.mul (I.enc (.ring r)) (I.enc (.grp y)) = I.enc (.ring (r * I.embed y)) := by
  simp [mul]

@[simp] theorem mul_grp_ring (x : G) (r : R) :
    I.mul (I.enc (.grp x)) (I.enc (.ring r)) = I.enc (.ring (I.embed x * r)) := by
  simp [mul]

@[simp] theorem mul_ring_ring (r t : R) :
    I.mul (I.enc (.ring r)) (I.enc (.ring t)) = I.enc (.ring (r * t)) := by
  simp [mul]

end Mul

section Add

variable [Zero R] [Add R]

@[simp] theorem add_ring_ring (r t : R) :
    I.add (I.enc (.ring r)) (I.enc (.ring t)) = I.enc (.ring (r + t)) := by
  simp [add]

@[simp] theorem add_ring_grp (r : R) (y : G) :
    I.add (I.enc (.ring r)) (I.enc (.grp y)) = I.enc (.ring (r + I.embed y)) := by
  simp [add]

@[simp] theorem add_grp_ring (x : G) (r : R) :
    I.add (I.enc (.grp x)) (I.enc (.ring r)) = I.enc (.ring (I.embed x + r)) := by
  simp [add]

end Add

@[simp] theorem sub_ring_ring [Zero R] [Sub R] (r t : R) :
    I.sub (I.enc (.ring r)) (I.enc (.ring t)) = I.enc (.ring (r - t)) := by
  simp [sub]

variable [Zero S]

@[simp] theorem pow_grp (x : G) (s : S) :
    I.pow (I.enc (.grp x)) (I.enc (.exp s)) = I.enc (.grp (I.gpow x s)) := by
  simp [pow]

@[simp] theorem pow_ring (r : R) (s : S) :
    I.pow (I.enc (.ring r)) (I.enc (.exp s)) = I.enc (.grp (I.gpow (I.proj r) s)) := by
  simp [pow]

@[simp] theorem expAdd_exp [Add S] (s t : S) :
    I.expAdd (I.enc (.exp s)) (I.enc (.exp t)) = I.enc (.exp (s + t)) := by
  simp [expAdd]

@[simp] theorem expMul_exp [Mul S] (s t : S) :
    I.expMul (I.enc (.exp s)) (I.enc (.exp t)) = I.enc (.exp (s * t)) := by
  simp [expMul]

end Ops

/-- A hash into the data `K` interpreted by the function `H` on the group element of its
    decoded input: the extracted form of a random-oracle query `H : G → K`. -/
def oracleHash [One G] (H : G → K) : Array Int → Array Int :=
  I.hash1 fun v => .dat (H (I.toG v))

@[simp] theorem oracleHash_grp [One G] (H : G → K) (g : G) :
    I.oracleHash H (I.enc (.grp g)) = I.enc (.dat (H g)) := by
  simp [oracleHash]

@[simp] theorem generator_eq : I.generator = I.enc (.grp I.gen) := rfl

@[simp] theorem const_eq (v : AlgVal G S R K) : I.const v = I.enc v := rfl

end AlgInterp

end CatCrypt.Crypto.Extracted
