/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.GroupExpNF
public meta import CatCryptCore.Tactics.GroupExpNF
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for `group_exp_nf`

Game equalities over a fresh group written for these tests. A group `G` with integer and
natural exponents bound by earlier samples (Diffie–Hellman shaped: the shared key computed
as `(g ^ a) ^ b`, `(g ^ b) ^ a` or `g ^ (a * b)`; products and inverses of powers of one
base). A fresh exponentiation `zexp` by `ZMod q` in a group of exponent `q`, with its fold
laws proved here and given as rules: a Diffie–Hellman key agreement against a DDH-style
game whose key generation and Diffie–Hellman operation are definitions unfolded by name,
and an ElGamal encryption against its DDH reduction. Negative cases that must not close:
an exponent identity that is false (`a * b` against `a + b`), bindings in another order,
and a cancellation that needs the commutativity of two bases.
-/

set_option autoImplicit false

@[expose] public section

open CatCrypt.Core

namespace CatCrypt.Tactic.GroupExpNFTest

/-! ## Integer and natural exponents -/

section IntExp

variable {G : Type} [Group G] (g : G)

/-- The key `(g ^ a) ^ b` of a Diffie–Hellman exchange equals `g ^ (b * a)`, with the
exponents sampled earlier in the chain. -/
example (n : ℕ) [NeZero n] (D : G → G → G → SPComp Bool) :
    (do let a ← SPComp.sample (Fin n); let b ← SPComp.sample (Fin n)
        D (g ^ (a : ℕ)) (g ^ (b : ℕ)) ((g ^ (a : ℕ)) ^ (b : ℕ)) : SPComp Bool) =
    (do let a ← SPComp.sample (Fin n); let b ← SPComp.sample (Fin n)
        D (g ^ (a : ℕ)) (g ^ (b : ℕ)) (g ^ ((b : ℕ) * (a : ℕ)))) := by
  group_exp_nf

/-- Alice's key `(g ^ b) ^ a` equals Bob's key `(g ^ a) ^ b`. -/
example (n : ℕ) [NeZero n] (D : G → G → G → SPComp Bool) :
    (do let a ← SPComp.sample (Fin n); let b ← SPComp.sample (Fin n)
        D (g ^ (a : ℤ)) (g ^ (b : ℤ)) ((g ^ (b : ℤ)) ^ (a : ℤ)) : SPComp Bool) =
    (do let a ← SPComp.sample (Fin n); let b ← SPComp.sample (Fin n)
        D (g ^ (a : ℤ)) (g ^ (b : ℤ)) ((g ^ (a : ℤ)) ^ (b : ℤ))) := by
  group_exp_nf

/-- A product of powers equals the power of the sum of the exponents, and a quotient the
power of the difference. -/
example (n : ℕ) [NeZero n] (D : G → G → SPComp Bool) :
    (do let a ← SPComp.sample (Fin n); let b ← SPComp.sample (Fin n)
        D (g ^ (a : ℤ) * g ^ (b : ℤ)) (g ^ (a : ℤ) * (g ^ (b : ℤ))⁻¹) : SPComp Bool) =
    (do let a ← SPComp.sample (Fin n); let b ← SPComp.sample (Fin n)
        D (g ^ ((a : ℤ) + b)) (g ^ ((a : ℤ) - b))) := by
  group_exp_nf

/-- A word of three factors with the base itself among them, in any association. -/
example (a b : ℕ) : g ^ a * (g * g ^ b) = (g ^ (b + 1)) * g ^ a := by
  group_exp_nf

/-- The negative case: `g ^ (a * b)` against `g ^ (a + b)` is not an identity. -/
example (n : ℕ) [NeZero n] (D : G → SPComp Bool)
    (h : (do let a ← SPComp.sample (Fin n); let b ← SPComp.sample (Fin n)
             D (g ^ ((a : ℕ) * (b : ℕ))) : SPComp Bool) =
        (do let a ← SPComp.sample (Fin n); let b ← SPComp.sample (Fin n)
            D (g ^ ((a : ℕ) + (b : ℕ))))) :
    (do let a ← SPComp.sample (Fin n); let b ← SPComp.sample (Fin n)
        D (g ^ ((a : ℕ) * (b : ℕ))) : SPComp Bool) =
        (do let a ← SPComp.sample (Fin n); let b ← SPComp.sample (Fin n)
            D (g ^ ((a : ℕ) + (b : ℕ)))) := by
  fail_if_success group_exp_nf
  exact h

/-- Bindings in another order are outside the fragment. -/
example (n : ℕ) [NeZero n] (D : G → G → SPComp Bool)
    (h : (do let a ← SPComp.sample (Fin n); let b ← SPComp.sample (Fin n)
             D (g ^ (a : ℕ)) (g ^ (b : ℕ)) : SPComp Bool) =
        (do let b ← SPComp.sample (Fin n); let a ← SPComp.sample (Fin n)
            D (g ^ (a : ℕ)) (g ^ (b : ℕ)))) :
    (do let a ← SPComp.sample (Fin n); let b ← SPComp.sample (Fin n)
        D (g ^ (a : ℕ)) (g ^ (b : ℕ)) : SPComp Bool) =
        (do let b ← SPComp.sample (Fin n); let a ← SPComp.sample (Fin n)
            D (g ^ (a : ℕ)) (g ^ (b : ℕ))) := by
  fail_if_success group_exp_nf
  exact h

/-- A cancellation that needs two bases to commute is outside the fragment. -/
example {H : Type} [CommGroup H] (x y : H) (a : ℤ)
    (h : x ^ a * y * x ^ (-a) = y) : x ^ a * y * x ^ (-a) = y := by
  fail_if_success group_exp_nf
  exact h

end IntExp

/-! ## A fresh exponentiation by `ZMod q` -/

section ZModExp

variable {G : Type} [Group G] {q : ℕ} [NeZero q]

/-- Exponentiation by `ZMod q` through the representative of the exponent. -/
def zexp (x : G) (a : ZMod q) : G := x ^ a.val

omit [NeZero q] in
/-- In a group of exponent `q`, a power depends on its exponent modulo `q`. -/
theorem pow_mod_of_pow_eq_one (hq : ∀ x : G, x ^ q = 1) (x : G) (n : ℕ) :
    x ^ n = x ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q]
  rw [pow_add, pow_mul, hq, one_pow, one_mul]

omit [NeZero q] in
/-- Fold law: an exponentiation of an exponentiation multiplies the exponents. -/
theorem zexp_zexp (hq : ∀ x : G, x ^ q = 1) (x : G) (a b : ZMod q) :
    zexp (zexp x a) b = zexp x (a * b) := by
  unfold zexp
  rw [← pow_mul, ZMod.val_mul, ← pow_mod_of_pow_eq_one hq]

/-- Fold law: a product of exponentiations of one base adds the exponents. -/
theorem zexp_mul_zexp (hq : ∀ x : G, x ^ q = 1) (x : G) (a b : ZMod q) :
    zexp x a * zexp x b = zexp x (a + b) := by
  unfold zexp
  rw [← pow_add, ZMod.val_add, ← pow_mod_of_pow_eq_one hq]

variable (q) (g : G)

/-- Key generation: sample `s`, publish `g ^ s`. -/
noncomputable def keygen : SPComp (ZMod q × G) := do
  let s ← SPComp.sample (ZMod q)
  pure (s, zexp g s)

/-- The Diffie–Hellman operation on a secret exponent and a public key. -/
def dh (s : ZMod q) (X : G) : G := zexp X s

/-- DDH-style real game: two key pairs, the shared key computed by `dh`. -/
noncomputable def realGame (A : G → G → G → SPComp Bool) : SPComp Bool := do
  let ⟨a, ga⟩ ← keygen q g
  let ⟨_, gb⟩ ← keygen q g
  A ga gb (dh q a gb)

/-- Diffie–Hellman key agreement: the key is `g ^ (b * a)`. -/
noncomputable def kaGame (A : G → G → G → SPComp Bool) : SPComp Bool := do
  let a ← SPComp.sample (ZMod q)
  let b ← SPComp.sample (ZMod q)
  A (zexp g a) (zexp g b) (zexp g (b * a))

/-- The key agreement is the DDH-style real game: the definitions are unfolded by name and
the leaf `zexp (zexp g b) a = zexp g (b * a)` closes by the fold law. -/
example (hq : ∀ x : G, x ^ q = 1) (A : G → G → G → SPComp Bool) :
    kaGame q g A = realGame q g A := by
  group_exp_nf [kaGame, realGame, keygen, dh, zexp_zexp hq]

/-- Without the fold law the leaf stays open. -/
example (A : G → G → G → SPComp Bool) (h : kaGame q g A = realGame q g A) :
    kaGame q g A = realGame q g A := by
  fail_if_success group_exp_nf [kaGame, realGame, keygen, dh]
  exact h

/-- Sums of exponents: `g ^ a * g ^ b` against `g ^ (b + a)`. -/
example (hq : ∀ x : G, x ^ q = 1) (A : G → G → SPComp Bool) :
    (do let a ← SPComp.sample (ZMod q); let b ← SPComp.sample (ZMod q)
        A (zexp g a * zexp g b) (zexp (zexp g a) (b + 1)) : SPComp Bool) =
    (do let a ← SPComp.sample (ZMod q); let b ← SPComp.sample (ZMod q)
        A (zexp g (b + a)) (zexp g a * zexp g (a * b))) := by
  group_exp_nf [zexp_zexp hq, zexp_mul_zexp hq]

/-- ElGamal encryption of `m` under `pk = g ^ sk` with randomness `r`. -/
noncomputable def elgEnc (pk : G) (m : G) : SPComp (G × G) := do
  let r ← SPComp.sample (ZMod q)
  pure (zexp g r, zexp pk r * m)

/-- The IND-CPA game for a fixed message: key generation, then encryption. -/
noncomputable def elgGame (m : G) (A : G → G × G → SPComp Bool) : SPComp Bool := do
  let ⟨_, pk⟩ ← keygen q g
  let c ← elgEnc q g pk m
  A pk c

/-- The DDH reduction for ElGamal: the DDH triple `(g ^ a, g ^ b, g ^ (a * b))` gives the
public key `g ^ a` and the ciphertext `(g ^ b, g ^ (a * b) * m)`. -/
noncomputable def elgDDH (m : G) (A : G → G × G → SPComp Bool) : SPComp Bool := do
  let a ← SPComp.sample (ZMod q)
  let b ← SPComp.sample (ZMod q)
  A (zexp g a) (zexp g b, zexp g (a * b) * m)

/-- ElGamal-shaped: the IND-CPA game is the DDH reduction on a real triple. -/
example (hq : ∀ x : G, x ^ q = 1) (m : G) (A : G → G × G → SPComp Bool) :
    elgGame q g m A = elgDDH q g m A := by
  group_exp_nf [elgGame, elgDDH, elgEnc, keygen, zexp_zexp hq]

/-- The negative case over `ZMod q`: the key `g ^ (a + b)` is not `g ^ (a * b)`. -/
example (_hq : ∀ x : G, x ^ q = 1) (A : G → G → G → SPComp Bool)
    (h : (do let a ← SPComp.sample (ZMod q); let b ← SPComp.sample (ZMod q)
             A (zexp g a) (zexp g b) (zexp g (a + b)) : SPComp Bool) = kaGame q g A) :
    (do let a ← SPComp.sample (ZMod q); let b ← SPComp.sample (ZMod q)
        A (zexp g a) (zexp g b) (zexp g (a + b)) : SPComp Bool) = kaGame q g A := by
  fail_if_success group_exp_nf [kaGame, zexp_zexp _hq, zexp_mul_zexp _hq]
  exact h

end ZModExp

end CatCrypt.Tactic.GroupExpNFTest
