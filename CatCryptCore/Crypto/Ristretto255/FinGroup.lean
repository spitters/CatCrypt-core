/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCryptCore.ForMathlib.Pocklington
public import CatCryptCore.ForMathlib.Pocklington
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# ristretto255 as a finite cyclic group

Port of `Commitments/theories/Ristretto255_finGroup.v` to Lean 4 + Mathlib.

ristretto255 is the quotient group `E/E[4]` where `E` is Edwards25519 and
`E[4]` is the order-4 subgroup.  The quotient is a prime-order cyclic group
of order
```
  l = 2^252 + 27742317777372353535851937790883648493
```
which is the scalar field order of Curve25519.

We model ristretto255 as `ZMod curve25519_l`, the cyclic group of order `l`.
This is justified because any cyclic group of prime order `l` is isomorphic
to `ZMod l`, and the SSProve security proofs only depend on the group being
cyclic of prime order with a known generator — the concrete representation
does not matter.

## Primality of `curve25519_l`

Primality is established via a chain of Pocklington certificates, mirroring
the strategy used in `fiat-crypto/src/Spec/Curve25519.v:prime_l` and the Coq
port in `Commitments/theories/Curve25519_primality.v`.

The chain factors `l - 1 = 2^2 · 3 · 11 · p_a · p_b` where
* `p_a = 198211423230930754013084525763697` (108-bit prime)
* `p_b = 276602624281642239937218680557139826668747` (138-bit prime)

For the top-level Pocklington check on `l` we only need `F = p_b`
(since `p_b > sqrt(l)`); this means only `p_b` requires a recursive
primality proof, not `p_a`.

The recursion on `p_b` continues via `p_b - 1 = 2 · 7 · p_c` where
`p_c = 19757330305831588566944191468367130476339` (134-bit prime),
and so on through ~10 levels down to small primes dispatched by `decide`.
-/

@[expose] public section

namespace CatCrypt.Crypto.Ristretto255

open Pocklington

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 10000

/-! ## The curve25519 group order `l` -/

/-- The order of the ristretto255 group and of the Curve25519 scalar field. -/
def curve25519_l : ℕ :=
  2 ^ 252 + 27742317777372353535851937790883648493

/-- Convenience numeric value. -/
lemma curve25519_l_eq : curve25519_l =
    7237005577332262213973186563042994240857116359379907606001950938285454250989 := by
  unfold curve25519_l
  decide

/-! ## Primality chain for `curve25519_l`

We build Pocklington primality certificates bottom-up.

The cases in each `PocklingtonWitness` constructor are dispatched by
nested `if`-on-equality, which keeps everything in `Type` (the
constructor returns data, not a proposition). -/

/-! ### Tier 0: small primes (dispatched by `decide`/`native_decide`) -/

lemma prime_17 : Nat.Prime 17 := by native_decide
lemma prime_67 : Nat.Prime 67 := by native_decide
lemma prime_113 : Nat.Prime 113 := by native_decide
lemma prime_269 : Nat.Prime 269 := by native_decide
lemma prime_307 : Nat.Prime 307 := by native_decide
lemma prime_1361 : Nat.Prime 1361 := by native_decide
lemma prime_2551 : Nat.Prime 2551 := by native_decide
lemma prime_2851 : Nat.Prime 2851 := by native_decide
lemma prime_2939 : Nat.Prime 2939 := by native_decide
lemma prime_3797 : Nat.Prime 3797 := by native_decide
lemma prime_5879 : Nat.Prime 5879 := by native_decide
lemma prime_531581 : Nat.Prime 531581 := by native_decide
lemma prime_1224481 : Nat.Prime 1224481 := by native_decide
lemma prime_292386187 : Nat.Prime 292386187 := by native_decide
lemma prime_213441916511 : Nat.Prime 213441916511 := by native_decide

/-! ### Helper: build a `PocklingtonWitness` from a witness base `a`.

Given `n`, `F`, `q` (prime, dividing `F`), and a base `a` for which
the `a^(n-1) = 1` and gcd conditions hold, package it up. The hypotheses
are `pow_eq_one` and `gcd_eq_one`, both `native_decide`-able. -/

/-! ### Tier 4: `1257559732178653` (51-bit) -/

set_option maxHeartbeats 400000 in
lemma prime_1257559732178653 : Nat.Prime 1257559732178653 := by
  refine pocklington 1257559732178653 (by decide) ?_
  refine
    { F := 1257559732178652
      R := 1
      hFR := by decide
      hCoprime := by decide
      hLarge := by decide
      witnesses := ?_ }
  intro q hq hqF
  haveI : NeZero (1257559732178653 : ℕ) := ⟨by decide⟩
  -- 1257559732178652 = 2^2 · 3 · 7 · 23 · 531581 · 1224481
  -- Decide which prime q is by checking membership in the (decidable) set of divisors.
  have hcases : q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 23 ∨ q = 531581 ∨ q = 1224481 := by
    have hFeq : (1257559732178652 : ℕ) =
        2^2 * 3 * 7 * 23 * 531581 * 1224481 := by decide
    rw [hFeq] at hqF
    have h1 := hq.dvd_mul.mp hqF
    rcases h1 with h | h
    · have h2 := hq.dvd_mul.mp h
      rcases h2 with h | h
      · have h3 := hq.dvd_mul.mp h
        rcases h3 with h | h
        · have h4 := hq.dvd_mul.mp h
          rcases h4 with h | h
          · have h5 := hq.dvd_mul.mp h
            rcases h5 with h | h
            · -- q ∣ 2^2
              left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
                (hq.dvd_of_dvd_pow h)
            · right; left;
              exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h
          · right; right; left;
            exact (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 7)).mp h
        · right; right; right; left;
          exact (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 23)).mp h
      · right; right; right; right; left;
        exact (Nat.prime_dvd_prime_iff_eq hq prime_531581).mp h
    · right; right; right; right; right;
      exact (Nat.prime_dvd_prime_iff_eq hq prime_1224481).mp h
  -- Now build the witness via `if` on q.
  classical
  by_cases h : q = 2
  · subst h
    exact { a := (2 : ZMod 1257559732178653), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 1257559732178653) ^ ((1257559732178653 - 1) / 2) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h2 : q = 3
  · subst h2
    exact { a := (2 : ZMod 1257559732178653), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 1257559732178653) ^ ((1257559732178653 - 1) / 3) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h3 : q = 7
  · subst h3
    exact { a := (2 : ZMod 1257559732178653), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 1257559732178653) ^ ((1257559732178653 - 1) / 7) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h4 : q = 23
  · subst h4
    exact { a := (2 : ZMod 1257559732178653), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 1257559732178653) ^ ((1257559732178653 - 1) / 23) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h5 : q = 531581
  · subst h5
    exact { a := (2 : ZMod 1257559732178653), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 1257559732178653) ^ ((1257559732178653 - 1) / 531581) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h6 : q = 1224481
  · subst h6
    exact { a := (2 : ZMod 1257559732178653), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 1257559732178653) ^ ((1257559732178653 - 1) / 1224481) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  -- All cases must be covered.
  exact absurd hcases (by tauto)

/-! ### Tier 5: `4434155615661930479` (62-bit) -/

set_option maxHeartbeats 400000 in
lemma prime_4434155615661930479 : Nat.Prime 4434155615661930479 := by
  refine pocklington 4434155615661930479 (by decide) ?_
  refine
    { F := 4434155615661930478
      R := 1
      hFR := by decide
      hCoprime := by decide
      hLarge := by decide
      witnesses := ?_ }
  intro q hq hqF
  haveI : NeZero (4434155615661930479 : ℕ) := ⟨by decide⟩
  have hcases : q = 2 ∨ q = 41 ∨ q = 43 ∨ q = 1257559732178653 := by
    have hFeq : (4434155615661930478 : ℕ) = 2 * 41 * 43 * 1257559732178653 := by decide
    rw [hFeq] at hqF
    rcases hq.dvd_mul.mp hqF with h | h
    · rcases hq.dvd_mul.mp h with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
        · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 41)).mp h
      · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 43)).mp h
    · right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq prime_1257559732178653).mp h
  classical
  by_cases h : q = 2
  · subst h
    exact { a := (17 : ZMod 4434155615661930479), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((17 : ZMod 4434155615661930479) ^ ((4434155615661930479 - 1) / 2) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h2 : q = 41
  · subst h2
    exact { a := (17 : ZMod 4434155615661930479), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((17 : ZMod 4434155615661930479) ^ ((4434155615661930479 - 1) / 41) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h3 : q = 43
  · subst h3
    exact { a := (17 : ZMod 4434155615661930479), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((17 : ZMod 4434155615661930479) ^ ((4434155615661930479 - 1) / 43) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h4 : q = 1257559732178653
  · subst h4
    exact { a := (17 : ZMod 4434155615661930479), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((17 : ZMod 4434155615661930479) ^
                      ((4434155615661930479 - 1) / 1257559732178653) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  exact absurd hcases (by tauto)

/-! ### Tier 6: `172054593956031949258510691` (88-bit) -/

set_option maxHeartbeats 800000 in
lemma prime_172054593956031949258510691 :
    Nat.Prime 172054593956031949258510691 := by
  refine pocklington 172054593956031949258510691 (by decide) ?_
  refine
    { F := 172054593956031949258510690
      R := 1
      hFR := by decide
      hCoprime := by decide
      hLarge := by decide
      witnesses := ?_ }
  intro q hq hqF
  haveI : NeZero (172054593956031949258510691 : ℕ) := ⟨by decide⟩
  have hcases : q = 2 ∨ q = 5 ∨ q = 1361 ∨ q = 2851 ∨ q = 4434155615661930479 := by
    have hFeq : (172054593956031949258510690 : ℕ) =
        2 * 5 * 1361 * 2851 * 4434155615661930479 := by decide
    rw [hFeq] at hqF
    rcases hq.dvd_mul.mp hqF with h | h
    · rcases hq.dvd_mul.mp h with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
          · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 5)).mp h
        · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq prime_1361).mp h
      · right; right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq prime_2851).mp h
    · right; right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq prime_4434155615661930479).mp h
  classical
  by_cases h : q = 2
  · subst h
    exact { a := (2 : ZMod 172054593956031949258510691), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 172054593956031949258510691) ^
                      ((172054593956031949258510691 - 1) / 2) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h2 : q = 5
  · subst h2
    exact { a := (2 : ZMod 172054593956031949258510691), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 172054593956031949258510691) ^
                      ((172054593956031949258510691 - 1) / 5) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h3 : q = 1361
  · subst h3
    exact { a := (2 : ZMod 172054593956031949258510691), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 172054593956031949258510691) ^
                      ((172054593956031949258510691 - 1) / 1361) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h4 : q = 2851
  · subst h4
    exact { a := (2 : ZMod 172054593956031949258510691), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 172054593956031949258510691) ^
                      ((172054593956031949258510691 - 1) / 2851) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h5 : q = 4434155615661930479
  · subst h5
    exact { a := (2 : ZMod 172054593956031949258510691), q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 172054593956031949258510691) ^
                      ((172054593956031949258510691 - 1) / 4434155615661930479) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  exact absurd hcases (by tauto)

/-! ### Tier 7: p1c = `19757330305831588566944191468367130476339` (134-bit) -/

set_option maxHeartbeats 1600000 in
lemma prime_p1c : Nat.Prime 19757330305831588566944191468367130476339 := by
  refine pocklington 19757330305831588566944191468367130476339 (by decide) ?_
  refine
    { F := 19757330305831588566944191468367130476338
      R := 1
      hFR := by decide
      hCoprime := by decide
      hLarge := by decide
      witnesses := ?_ }
  intro q hq hqF
  haveI : NeZero (19757330305831588566944191468367130476339 : ℕ) := ⟨by decide⟩
  have hcases : q = 2 ∨ q = 269 ∨ q = 213441916511 ∨ q = 172054593956031949258510691 := by
    have hFeq : (19757330305831588566944191468367130476338 : ℕ) =
        2 * 269 * 213441916511 * 172054593956031949258510691 := by decide
    rw [hFeq] at hqF
    rcases hq.dvd_mul.mp hqF with h | h
    · rcases hq.dvd_mul.mp h with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
        · right; left; exact (Nat.prime_dvd_prime_iff_eq hq prime_269).mp h
      · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq prime_213441916511).mp h
    · right; right; right;
      exact (Nat.prime_dvd_prime_iff_eq hq prime_172054593956031949258510691).mp h
  classical
  by_cases h : q = 2
  · subst h
    exact { a := (2 : ZMod 19757330305831588566944191468367130476339),
            q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 19757330305831588566944191468367130476339) ^
                      ((19757330305831588566944191468367130476339 - 1) / 2) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h2 : q = 269
  · subst h2
    exact { a := (2 : ZMod 19757330305831588566944191468367130476339),
            q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 19757330305831588566944191468367130476339) ^
                      ((19757330305831588566944191468367130476339 - 1) / 269) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h3 : q = 213441916511
  · subst h3
    exact { a := (2 : ZMod 19757330305831588566944191468367130476339),
            q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 19757330305831588566944191468367130476339) ^
                      ((19757330305831588566944191468367130476339 - 1) / 213441916511) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h4 : q = 172054593956031949258510691
  · subst h4
    exact { a := (2 : ZMod 19757330305831588566944191468367130476339),
            q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 19757330305831588566944191468367130476339) ^
                      ((19757330305831588566944191468367130476339 - 1) /
                        172054593956031949258510691) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  exact absurd hcases (by tauto)

/-! ### Tier 8: p2 = `276602624281642239937218680557139826668747` (138-bit) -/

set_option maxHeartbeats 1600000 in
lemma prime_p2 : Nat.Prime 276602624281642239937218680557139826668747 := by
  refine pocklington 276602624281642239937218680557139826668747 (by decide) ?_
  refine
    { F := 276602624281642239937218680557139826668746
      R := 1
      hFR := by decide
      hCoprime := by decide
      hLarge := by decide
      witnesses := ?_ }
  intro q hq hqF
  haveI : NeZero (276602624281642239937218680557139826668747 : ℕ) := ⟨by decide⟩
  have hcases : q = 2 ∨ q = 7 ∨ q = 19757330305831588566944191468367130476339 := by
    have hFeq : (276602624281642239937218680557139826668746 : ℕ) =
        2 * 7 * 19757330305831588566944191468367130476339 := by decide
    rw [hFeq] at hqF
    rcases hq.dvd_mul.mp hqF with h | h
    · rcases hq.dvd_mul.mp h with h | h
      · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
      · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 7)).mp h
    · right; right; exact (Nat.prime_dvd_prime_iff_eq hq prime_p1c).mp h
  classical
  by_cases h : q = 2
  · subst h
    exact { a := (2 : ZMod 276602624281642239937218680557139826668747),
            q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 276602624281642239937218680557139826668747) ^
                      ((276602624281642239937218680557139826668747 - 1) / 2) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h2 : q = 7
  · subst h2
    exact { a := (2 : ZMod 276602624281642239937218680557139826668747),
            q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 276602624281642239937218680557139826668747) ^
                      ((276602624281642239937218680557139826668747 - 1) / 7) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  by_cases h3 : q = 19757330305831588566944191468367130476339
  · subst h3
    exact { a := (2 : ZMod 276602624281642239937218680557139826668747),
            q_prime := hq, q_dvd_F := hqF,
            pow_eq_one := by native_decide,
            pow_sub_one_isUnit := by
              rw [← ZMod.natCast_zmod_val
                    ((2 : ZMod 276602624281642239937218680557139826668747) ^
                      ((276602624281642239937218680557139826668747 - 1) /
                        19757330305831588566944191468367130476339) - 1),
                  ZMod.isUnit_iff_coprime]; native_decide }
  exact absurd hcases (by tauto)

/-! ### Top tier: `curve25519_l` (253-bit)

For `l` we use `F = p2` (a single 138-bit prime) and
`R = (l - 1) / p2 = 26163907866482859529727157400808004`.
This satisfies `(F+1)^2 > l` since `p2 > sqrt(l)`. -/

set_option maxHeartbeats 1600000 in
lemma curve25519_l_prime : Nat.Prime curve25519_l := by
  rw [show curve25519_l =
      7237005577332262213973186563042994240857116359379907606001950938285454250989 from
      curve25519_l_eq]
  refine pocklington
    7237005577332262213973186563042994240857116359379907606001950938285454250989
    (by decide) ?_
  refine
    { F := 276602624281642239937218680557139826668747
      R := 26163907866482859529727157400808004
      hFR := by decide
      hCoprime := by decide
      hLarge := by decide
      witnesses := ?_ }
  intro q hq hqF
  -- F = p2 (a prime), so q must equal p2.
  have hqeq : q = 276602624281642239937218680557139826668747 :=
    (Nat.prime_dvd_prime_iff_eq hq prime_p2).mp hqF
  subst hqeq
  haveI : NeZero
      (7237005577332262213973186563042994240857116359379907606001950938285454250989 :
        ℕ) := ⟨by decide⟩
  exact
    { a := (2 :
              ZMod
                7237005577332262213973186563042994240857116359379907606001950938285454250989),
      q_prime := hq,
      q_dvd_F := hqF,
      pow_eq_one := by native_decide,
      pow_sub_one_isUnit := by
        rw [← ZMod.natCast_zmod_val
              ((2 :
                  ZMod 7237005577332262213973186563042994240857116359379907606001950938285454250989) ^
                ((7237005577332262213973186563042994240857116359379907606001950938285454250989 - 1) /
                  276602624281642239937218680557139826668747) - 1),
            ZMod.isUnit_iff_coprime]
        native_decide }

/-! ## Positivity and basic facts -/

lemma curve25519_l_pos : 0 < curve25519_l :=
  curve25519_l_prime.pos

lemma curve25519_l_gt_one : 1 < curve25519_l :=
  curve25519_l_prime.one_lt

instance : NeZero curve25519_l :=
  ⟨curve25519_l_pos.ne'⟩

instance : Fact (Nat.Prime curve25519_l) :=
  ⟨curve25519_l_prime⟩

/-! ## ristretto255 as `ZMod curve25519_l`

We model ristretto255 by the cyclic group of order `l = curve25519_l`.
Mathlib provides `ZMod n` with a `CommGroup`, `Fintype`, `DecidableEq`, and
`IsCyclic` structure for all `n`. -/

/-- The ristretto255 group type. -/
abbrev R255 : Type := ZMod curve25519_l

/-- The ristretto255 basepoint generator (the canonical generator `1` of the
additive cyclic group `ZMod l`). -/
def ristretto255_basepoint : R255 := 1

/-- The cardinality of ristretto255 equals `curve25519_l`. -/
lemma ristretto255_card : Fintype.card R255 = curve25519_l :=
  ZMod.card curve25519_l

end CatCrypt.Crypto.Ristretto255
