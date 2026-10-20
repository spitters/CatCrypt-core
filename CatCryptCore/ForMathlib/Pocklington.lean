/-
Copyright (c) 2026 SSProve-lean / CatCrypt.
Released under Apache 2.0 license as described in LICENSE.
-/

module

public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.Data.ZMod.Basic

/-!
# Pocklington primality test

Pocklington's theorem (a generalisation of Lucas–Pratt): suppose

* `n - 1 = F * R`,
* `gcd(F, R) = 1`,
* `n < (F + 1)^2`         (equivalently, `F + 1 > sqrt n`),
* for every prime `q ∣ F` there is `a_q : ZMod n` with
  - `a_q ^ (n - 1) = 1` and
  - `a_q ^ ((n - 1) / q) - 1` is a unit in `ZMod n`
    (equivalently, `gcd((a_q^((n-1)/q) - 1).val, n) = 1`).

Then `n` is prime.

The standard form of `hLarge` requires strict `n < (F+1)^2`. (With `≤`,
`n = 4`, `F = 1`, `R = 3` would vacuously satisfy all the witness conditions
yet `4` is composite, so the theorem fails.)

This file provides:

* `PocklingtonWitness`     — the witness data for one prime divisor `q ∣ F`.
* `PocklingtonCert n`      — the full primality certificate for `n`.
* `pocklington`            — the main theorem.
* `prime_257`              — a smoke test on the Fermat prime `n = 257`.
-/

@[expose] public section

namespace Pocklington

/-! ## Certificate datatype -/

/-- Per-prime witness for Pocklington's test.

For a base `a : ZMod n` and a prime `q ∣ F`, we record:
- `q_prime`            : `q` is prime,
- `q_dvd_F`            : `q ∣ F`,
- `pow_eq_one`         : `a ^ (n - 1) = 1` in `ZMod n`,
- `pow_sub_one_isUnit` : `a ^ ((n - 1) / q) - 1` is a unit in `ZMod n`.

The unit condition is equivalent to `Nat.gcd (a^((n-1)/q) - 1).val n = 1`
via `ZMod.isUnit_iff_coprime`. -/
structure PocklingtonWitness (n F q : ℕ) where
  a : ZMod n
  q_prime : Nat.Prime q
  q_dvd_F : q ∣ F
  pow_eq_one : a ^ (n - 1) = 1
  pow_sub_one_isUnit : IsUnit (a ^ ((n - 1) / q) - 1)

/-- A Pocklington primality certificate for `n`.

* `F`, `R`            : partial factorisation `n - 1 = F * R`,
* `hFR`               : `n - 1 = F * R`,
* `hCoprime`          : `Nat.Coprime F R`,
* `hLarge`            : `n < (F + 1)^2`,
* `witnesses`         : `PocklingtonWitness n F q` for every prime `q ∣ F`. -/
structure PocklingtonCert (n : ℕ) where
  F : ℕ
  R : ℕ
  hFR : n - 1 = F * R
  hCoprime : Nat.Coprime F R
  hLarge : n < (F + 1) ^ 2
  witnesses : ∀ q : ℕ, Nat.Prime q → q ∣ F → PocklingtonWitness n F q

/-! ## Order-theoretic lemma: from Lucas-style witnesses to prime-power
order divisibility. -/

/-- If `b^N = 1`, `b^(N/q) ≠ 1`, and `q` is a prime divisor of `N`, then the
`q`-part of `N` divides the order of `b`. -/
lemma factorization_dvd_orderOf
    {G : Type*} [Monoid G] {b : G} {N q : ℕ}
    (hN : 0 < N) (hq : Nat.Prime q) (hqN : q ∣ N)
    (hpow : b ^ N = 1) (hpow_div : b ^ (N / q) ≠ 1) :
    q ^ N.factorization q ∣ orderOf b := by
  -- d := orderOf b. d | N (from hpow). d ∤ N/q (from hpow_div).
  set d := orderOf b with hd
  have hdN : d ∣ N := orderOf_dvd_of_pow_eq_one hpow
  have hd_pos : 0 < d := by
    rw [hd]
    exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨N, hN, hpow⟩)
  have hd_ne_zero : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd_pos
  have hN_ne : N ≠ 0 := Nat.pos_iff_ne_zero.mp hN
  have hd_not_dvd : ¬ d ∣ N / q := by
    intro hdvd
    apply hpow_div
    exact (orderOf_dvd_iff_pow_eq_one).mp hdvd
  -- Use factorization to bound the q-part of d.
  -- d ∣ N gives d.factorization q ≤ N.factorization q.
  -- We claim d.factorization q ≥ N.factorization q, so equality.
  set k := N.factorization q with hk
  have hk_pos : 0 < k := hq.factorization_pos_of_dvd hN_ne hqN
  -- N = q^k * m with q ∤ m. Then N/q = q^(k-1) * m.
  have hqk_dvd_N : q ^ k ∣ N := Nat.ordProj_dvd _ _
  obtain ⟨m, hNm⟩ := hqk_dvd_N
  have hm_ne : m ≠ 0 := by
    rintro rfl; simp at hNm; exact hN_ne hNm
  have hq_not_dvd_m : ¬ q ∣ m := by
    intro hqm
    have : q ^ (k + 1) ∣ N := by
      rw [hNm, pow_succ]; exact mul_dvd_mul_left _ hqm
    have := (Nat.Prime.pow_dvd_iff_le_factorization hq hN_ne).mp this
    omega
  have hq_pos : 0 < q := hq.pos
  -- N/q = q^(k-1) * m.
  have hN_div_q : N / q = q ^ (k - 1) * m := by
    have hk_succ : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
    have : N = q * (q ^ (k - 1) * m) := by
      rw [hNm, ← mul_assoc, ← pow_succ', hk_succ]
    rw [this, Nat.mul_div_cancel_left _ hq_pos]
  -- Suppose for contradiction `q^k ∤ d`.
  by_contra hkj
  -- hkj : ¬ q ^ k ∣ d.
  -- So d.factorization q < k.
  have hj_lt : d.factorization q < k := by
    by_contra h
    push_neg at h
    apply hkj
    exact (Nat.Prime.pow_dvd_iff_le_factorization hq hd_ne_zero).mpr h
  -- Now show d ∣ N/q via factorization.
  have hd_dvd_div : d ∣ N / q := by
    rw [hN_div_q]
    -- d ∣ q^(k-1) * m iff d.factorization ≤ (q^(k-1) * m).factorization
    rw [← Nat.factorization_le_iff_dvd hd_ne_zero
          (by exact mul_ne_zero (pow_ne_zero _ hq.ne_zero) hm_ne)]
    intro p
    by_cases hpq : p = q
    · subst hpq
      rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hm_ne]
      simp [Finsupp.add_apply, Nat.factorization_pow,
        Nat.Prime.factorization_self hq,
        Nat.factorization_eq_zero_of_not_dvd hq_not_dvd_m]
      omega
    · -- p ≠ q. d ∣ N gives d.factorization p ≤ N.factorization p.
      have hd_le_N : d.factorization ≤ N.factorization :=
        (Nat.factorization_le_iff_dvd hd_ne_zero hN_ne).mpr hdN
      have hq_fact_p : q.factorization p = 0 := by
        rw [hq.factorization]
        simp [Ne.symm hpq]
      have hN_eq : N.factorization p = (q ^ (k - 1) * m).factorization p := by
        have hN_dec : N = q ^ k * m := hNm
        rw [hN_dec, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hm_ne,
            Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hm_ne]
        simp [Finsupp.add_apply, Nat.factorization_pow, hq_fact_p]
      rw [← hN_eq]
      exact hd_le_N p
  exact hd_not_dvd hd_dvd_div

/-! ## The main theorem -/

/-- **Pocklington's theorem.** If `n ≥ 2` admits a Pocklington certificate,
then `n` is prime. -/
theorem pocklington (n : ℕ) (hn : 2 ≤ n) (cert : PocklingtonCert n) : Nat.Prime n := by
  -- Set up: let p = minFac n; show p = n.
  set p := n.minFac with hp_def
  have hn_ne_one : n ≠ 1 := by omega
  have hn_pos : 0 < n := by omega
  have hn1_pos : 0 < n - 1 := by omega
  have hn1_ne : n - 1 ≠ 0 := Nat.pos_iff_ne_zero.mp hn1_pos
  have hp_prime : Nat.Prime p := Nat.minFac_prime hn_ne_one
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  have hp_dvd_n : p ∣ n := Nat.minFac_dvd n
  have hp_pos : 0 < p := hp_prime.pos
  -- Claim: F ∣ p - 1.
  have hFR := cert.hFR
  have hF_ne : cert.F ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hFR
    omega
  have hR_ne : cert.R ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hFR
    omega
  -- For each prime q | F: q^F.factorization q ∣ p - 1.
  have h_each : ∀ q, Nat.Prime q → q ∣ cert.F →
      q ^ cert.F.factorization q ∣ p - 1 := by
    intro q hq hqF
    -- The witness gives `q^(n-1).factorization q | orderOf (image of a in ZMod p)`.
    -- And by coprimality with R, (n-1).factorization q = F.factorization q.
    have w := cert.witnesses q hq hqF
    -- Image of a in ZMod p.
    set b : ZMod p := (ZMod.castHom hp_dvd_n (ZMod p)) w.a with hb
    have hb_pow : b ^ (n - 1) = 1 := by
      have hh := congrArg (ZMod.castHom hp_dvd_n (ZMod p)) w.pow_eq_one
      simpa only [map_pow, map_one] using hh
    have hb_pow_div : b ^ ((n - 1) / q) ≠ 1 := by
      intro hcontra
      -- The image of (a^((n-1)/q) - 1) is 0 mod p.
      have h0 :
          (ZMod.castHom hp_dvd_n (ZMod p)) (w.a ^ ((n - 1) / q) - 1) = 0 := by
        rw [map_sub, map_pow, map_one]
        rw [show (ZMod.castHom hp_dvd_n (ZMod p)) w.a = b from rfl, hcontra]
        ring
      rcases w.pow_sub_one_isUnit with ⟨u, hu⟩
      have hunit : IsUnit ((ZMod.castHom hp_dvd_n (ZMod p))
                            (w.a ^ ((n - 1) / q) - 1)) := by
        rw [← hu]; exact (Units.isUnit u).map _
      rw [h0] at hunit
      exact not_isUnit_zero hunit
    -- q | n-1 (from q | F | n-1).
    have hq_dvd_n1 : q ∣ n - 1 := by
      rw [cert.hFR]; exact dvd_mul_of_dvd_left hqF _
    -- Apply factorization_dvd_orderOf.
    have h_pow_dvd_ord : q ^ (n - 1).factorization q ∣ orderOf b :=
      factorization_dvd_orderOf hn1_pos hq hq_dvd_n1 hb_pow hb_pow_div
    -- (n-1).factorization q = F.factorization q.
    have hq_not_dvd_R : ¬ q ∣ cert.R := by
      intro hqR
      have hqgcd : q ∣ Nat.gcd cert.F cert.R := Nat.dvd_gcd hqF hqR
      rw [cert.hCoprime] at hqgcd
      exact hq.one_lt.ne' (Nat.eq_one_of_dvd_one hqgcd)
    have hfact_eq : (n - 1).factorization q = cert.F.factorization q := by
      rw [cert.hFR, Nat.factorization_mul hF_ne hR_ne]
      simp [Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hq_not_dvd_R]
    rw [hfact_eq] at h_pow_dvd_ord
    -- orderOf b | p - 1 (from Fermat).
    have hb_ne_zero : b ≠ 0 := by
      intro hb0
      have := hb_pow
      rw [hb0] at this
      -- 0^(n-1) = 0 ≠ 1 since n - 1 ≥ 1.
      rw [zero_pow hn1_ne] at this
      exact zero_ne_one this
    have h_ord_dvd_p_sub : orderOf b ∣ p - 1 :=
      ZMod.orderOf_dvd_card_sub_one hb_ne_zero
    exact h_pow_dvd_ord.trans h_ord_dvd_p_sub
  -- Now F ∣ p - 1.
  have hp_sub_one_pos : 0 < p - 1 := by
    have := hp_prime.one_lt; omega
  have hp1_ne : p - 1 ≠ 0 := Nat.pos_iff_ne_zero.mp hp_sub_one_pos
  have hF_dvd : cert.F ∣ p - 1 := by
    rw [← Nat.factorization_le_iff_dvd hF_ne hp1_ne]
    intro q
    -- If q is not prime, factorization is zero.
    by_cases hq : Nat.Prime q
    · by_cases hqF : q ∣ cert.F
      · -- Apply h_each to get q^F.fact q ∣ p - 1.
        have := h_each q hq hqF
        -- Translate to factorization.
        rw [Nat.Prime.pow_dvd_iff_le_factorization hq hp1_ne] at this
        exact this
      · -- q ∤ F, so F.factorization q = 0.
        rw [Nat.factorization_eq_zero_of_not_dvd hqF]
        simp
    · rw [Nat.factorization_eq_zero_of_not_prime _ hq]
      simp
  -- Hence p ≥ F + 1.
  have hF_le : cert.F + 1 ≤ p := by
    have := Nat.le_of_dvd hp_sub_one_pos hF_dvd
    omega
  -- Combine with hLarge: n < (F+1)^2 ≤ p^2.
  have hn_lt_p_sq : n < p ^ 2 := by
    calc n < (cert.F + 1) ^ 2 := cert.hLarge
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hF_le 2
  -- p ∣ n and p^2 > n force p = n.
  -- If p < n, then n = p * k with k ≥ 2 and k ≥ p (since p = minFac n),
  -- giving n ≥ p^2, contradiction.
  have hpn : p = n := by
    have hp_le_n : p ≤ n := Nat.minFac_le hn_pos
    rcases lt_or_eq_of_le hp_le_n with hlt | heq
    · exfalso
      -- p < n. n = p * (n/p), n/p ≥ 2, n/p ≥ p.
      have hp_lt_n : p < n := hlt
      have hk : n = p * (n / p) := (Nat.mul_div_cancel' hp_dvd_n).symm
      -- Since n > p ≥ 2 and p ∣ n, n/p ≥ 1; if n/p = 1, n = p contradicting p < n.
      have hk_ne_zero : n / p ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hk
        omega
      have hk_ne_one : n / p ≠ 1 := by
        intro h1
        rw [h1, mul_one] at hk
        omega
      -- (n/p) has its own minFac ≥ p (since p = minFac n).
      have hmf : Nat.Prime (n / p).minFac := Nat.minFac_prime hk_ne_one
      have h_dvd_n : (n / p).minFac ∣ n := by
        have hd : (n / p).minFac ∣ n / p := Nat.minFac_dvd _
        exact hd.trans ⟨p, by rw [mul_comm]; exact hk⟩
      have hp_le_mf : p ≤ (n / p).minFac := by
        show n.minFac ≤ (n / p).minFac
        exact Nat.minFac_le_of_dvd hmf.two_le h_dvd_n
      have hmf_le : (n / p).minFac ≤ n / p :=
        Nat.minFac_le (Nat.pos_iff_ne_zero.mpr hk_ne_zero)
      have hp_le_div : p ≤ n / p := hp_le_mf.trans hmf_le
      have h_pp_le : p * p ≤ p * (n / p) := Nat.mul_le_mul_left _ hp_le_div
      have h_pp_le_n : p * p ≤ n := by
        calc p * p ≤ p * (n / p) := h_pp_le
          _ = n := (Nat.mul_div_cancel' hp_dvd_n)
      have : p ^ 2 ≤ n := by grind
      omega
    · exact heq
  rw [← hpn]
  exact hp_prime

/-! ## Raw-data verifier (`native_decide` friendly) -/

/-- A flat, proof-free Pocklington witness for one prime divisor `q ∣ F`.
The `subPrime` field is a `Bool` flag the user sets via a recursive
sub-certificate; we only check the local arithmetic here. -/
structure RawWitness where
  q : ℕ
  a : ℕ
  subPrime : Bool
  deriving DecidableEq, Repr

/-- Flat, proof-free Pocklington certificate. -/
structure RawCert where
  n : ℕ
  F : ℕ
  R : ℕ
  witnesses : List RawWitness
  deriving Repr

/-- Bool-valued check: each `RawWitness` is a valid Pocklington witness for `n`,
  given that `q` is prime (recorded in `subPrime`).

  This is the predicate `native_decide` can dispatch quickly: it consists only
  of `Nat`/`ZMod` computations and `Bool` comparisons. -/
def RawWitness.check (n F : ℕ) (w : RawWitness) : Bool :=
  w.subPrime &&
  decide (Nat.Prime w.q) &&
  decide (w.q ∣ F) &&
  decide (((w.a : ZMod n) ^ (n - 1)) = 1) &&
  -- `IsUnit x` in `ZMod n` is equivalent to `Nat.gcd x.val n = 1`.
  decide (Nat.gcd ((w.a : ZMod n) ^ ((n - 1) / w.q) - 1).val n = 1)

/-- Bool-valued check that a `RawCert` is structurally a Pocklington certificate
  for `n`, modulo the user-supplied `subPrime` claims on each `q`.

  We additionally check that the union of `q`s in `witnesses` covers every
  prime divisor of `F`, by listing all primes ≤ `F` that divide `F` and
  comparing. (This is brute-force but works for small `F`; for the smoke test
  it is fine.) -/
def RawCert.verify (c : RawCert) : Bool :=
  decide (2 ≤ c.n) &&
  decide (c.n - 1 = c.F * c.R) &&
  decide (Nat.Coprime c.F c.R) &&
  decide (c.n < (c.F + 1) ^ 2) &&
  c.witnesses.all (RawWitness.check c.n c.F) &&
  -- Every prime ≤ F dividing F is covered by some witness.
  (List.range (c.F + 1)).all (fun q =>
    !decide (Nat.Prime q ∧ q ∣ c.F) ||
      c.witnesses.any (fun w => decide (w.q = q)))

/-! ## Smoke test -/

/-- Smoke test: `n = 257 = 2^8 + 1` is the Fermat prime `F_3`. -/
theorem prime_257 : Nat.Prime 257 := by norm_num

/-- A raw certificate for `257`, used to exercise `RawCert.verify`. -/
def rawCert_257 : RawCert :=
  { n := 257
    F := 256
    R := 1
    witnesses := [{ q := 2, a := 3, subPrime := true }] }

/-- The raw verifier closes on the certificate for `257`. -/
example : rawCert_257.verify = true := by native_decide

set_option maxRecDepth 4000 in
/-- A Pocklington certificate for `257`, exercising the certificate machinery
end-to-end. Here `n - 1 = 256 = 2^8`, so `F = 256`, `R = 1`. The only prime
divisor of `F` is `2`, and `a = 3` works:
- `3^256 ≡ 1 (mod 257)`
- `3^128 ≡ -1 (mod 257)`, so `3^128 - 1 ≡ -2 (mod 257)` is a unit. -/
def cert_257 : PocklingtonCert 257 where
  F := 256
  R := 1
  hFR := by decide
  hCoprime := by decide
  hLarge := by decide
  witnesses := fun q hq hqF => {
    a := (3 : ZMod 257)
    q_prime := by
      -- The only prime dividing 256 is 2.
      have hq2 : q = 2 := by
        have h256 : (256 : ℕ) = 2 ^ 8 := by decide
        rw [h256] at hqF
        exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
              (hq.dvd_of_dvd_pow hqF)
      rw [hq2]; exact Nat.prime_two
    q_dvd_F := hqF
    pow_eq_one := by
      -- a^(n-1) = a^256 doesn't depend on q.
      show (3 : ZMod 257) ^ (257 - 1) = 1
      decide
    pow_sub_one_isUnit := by
      have hq2 : q = 2 := by
        have h256 : (256 : ℕ) = 2 ^ 8 := by decide
        rw [h256] at hqF
        exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
              (hq.dvd_of_dvd_pow hqF)
      subst hq2
      -- (3^128 - 1 : ZMod 257) is a unit.
      show IsUnit ((3 : ZMod 257) ^ ((257 - 1) / 2) - 1)
      have h : (3 : ZMod 257) ^ ((257 - 1) / 2) - 1 = ((255 : ℕ) : ZMod 257) := by decide
      rw [h]
      exact (ZMod.isUnit_iff_coprime 255 257).mpr (by decide)
  }

/-- Smoke-test theorem: `257` is prime via the Pocklington certificate. -/
theorem prime_257_via_pocklington : Nat.Prime 257 :=
  pocklington 257 (by decide) cert_257

/-! ## Fast variant for 256-bit primes

`RawCert.verify` enumerates `List.range (F + 1)` to check that every prime
divisor of `F` is covered by a witness. For `F ≈ 2^256` this is infeasible.

`RawCertFast` replaces the enumeration with an explicit product check: each
witness records its prime `q` *together with* the multiplicity `e` of `q`
in `F`, and we verify `∏ qᵢ^eᵢ = F`. Since each `qᵢ` is asserted prime,
unique factorisation guarantees that every prime dividing `F` is some `qᵢ`.

The mod-exp check is left in terms of `(a : ZMod n) ^ (n - 1)`; in compiled
bytecode (`native_decide`) this uses Lean's fast `Nat.pow` on `Fin n`, so
no separate `powMod` helper is needed.

A `powMod` Nat-only mod-exp helper is also provided (with correctness lemma
`powMod_eq_pow_mod`) for callers that prefer to stay outside `ZMod`. -/

/-- Iterative-by-halving modular exponentiation, total over `Nat`.
`powMod m a k = a^k % m`. -/
def powMod (m a : ℕ) : ℕ → ℕ
  | 0     => 1 % m
  | n+1   =>
      let half := powMod m a ((n+1) / 2)
      let sq := (half * half) % m
      if (n+1) % 2 = 1 then (sq * a) % m else sq
decreasing_by
  exact Nat.div_lt_self (by omega) (by omega)

/-- Correctness of `powMod`: equals plain power mod `m`. -/
theorem powMod_eq_pow_mod (m a k : ℕ) : powMod m a k = (a ^ k) % m := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [powMod]
    | n+1 =>
      have h_half : ((n + 1) / 2 < n + 1) := Nat.div_lt_self (by omega) (by omega)
      have ih' := ih ((n + 1) / 2) h_half
      simp only [powMod]
      rw [ih']
      have hmd : (n + 1) % 2 + 2 * ((n + 1) / 2) = n + 1 := Nat.mod_add_div (n + 1) 2
      by_cases h : (n + 1) % 2 = 1
      · simp only [h, if_true]
        rw [show a ^ ((n + 1) / 2) % m * (a ^ ((n + 1) / 2) % m) % m
              = a ^ ((n + 1) / 2) * a ^ ((n + 1) / 2) % m from by rw [← Nat.mul_mod]]
        rw [show a ^ ((n + 1) / 2) * a ^ ((n + 1) / 2) % m * a % m
              = a ^ ((n + 1) / 2) * a ^ ((n + 1) / 2) * a % m from by
            rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]]
        congr 1
        rw [← pow_add, ← pow_succ]
        congr 1; omega
      · simp only [h, if_false]
        rw [show a ^ ((n + 1) / 2) % m * (a ^ ((n + 1) / 2) % m) % m
              = a ^ ((n + 1) / 2) * a ^ ((n + 1) / 2) % m from by rw [← Nat.mul_mod]]
        congr 1
        rw [← pow_add]
        congr 1; omega

/-- Smoke test: `powMod 257 3 256 = 1`. -/
example : powMod 257 3 256 = 1 := by native_decide

/-! ### `RawCertFast` ‑ proof-free certificate with explicit factorisation -/

/-- Per-prime witness for the fast variant: records both the prime `q` and
its multiplicity `e` in `F`. -/
structure RawWitnessFast where
  q : ℕ
  e : ℕ
  a : ℕ
  subPrime : Bool
  deriving DecidableEq, Repr

/-- Flat Pocklington certificate, fast variant. -/
structure RawCertFast where
  n : ℕ
  F : ℕ
  R : ℕ
  witnesses : List RawWitnessFast
  deriving Repr

/-- Local witness check (same arithmetic as `RawWitness.check`): `q` prime
(via `subPrime`), `q ∣ F`, `e ≥ 1`, `a^(n-1) = 1`, and the unit condition. -/
def RawWitnessFast.check (n F : ℕ) (w : RawWitnessFast) : Bool :=
  w.subPrime &&
  decide (Nat.Prime w.q) &&
  decide (w.q ∣ F) &&
  decide (1 ≤ w.e) &&
  decide (((w.a : ZMod n) ^ (n - 1)) = 1) &&
  decide (Nat.gcd ((w.a : ZMod n) ^ ((n - 1) / w.q) - 1).val n = 1)

/-- Product of `q^e` over the witnesses; must equal `F`. -/
def RawCertFast.factProd (ws : List RawWitnessFast) : ℕ :=
  (ws.map (fun w => w.q ^ w.e)).prod

/-- Bool-valued check that a `RawCertFast` is a Pocklington certificate.

Replaces the brute enumeration of `RawCert.verify` with an explicit product
check `∏ qᵢ^eᵢ = F`. -/
def RawCertFast.verify (c : RawCertFast) : Bool :=
  decide (2 ≤ c.n) &&
  decide (c.n - 1 = c.F * c.R) &&
  decide (Nat.Coprime c.F c.R) &&
  decide (c.n < (c.F + 1) ^ 2) &&
  decide (RawCertFast.factProd c.witnesses = c.F) &&
  c.witnesses.all (RawWitnessFast.check c.n c.F)

/-- If `F` is a product of prime-powers, every prime dividing `F` is one
of the bases. -/
lemma covers_of_factProd (ws : List RawWitnessFast)
    (hprime : ∀ w ∈ ws, Nat.Prime w.q) :
    ∀ q, Nat.Prime q → q ∣ (ws.map (fun w => w.q ^ w.e)).prod →
      ∃ w ∈ ws, q = w.q := by
  induction ws with
  | nil =>
      intro q hq hdvd
      simp at hdvd
      exact absurd hdvd hq.one_lt.ne'
  | cons w rest ih =>
      intro q hq hdvd
      simp at hdvd
      rcases hq.dvd_mul.mp hdvd with h1 | h2
      · have hwp : Nat.Prime w.q := hprime w List.mem_cons_self
        have hqdvd : q ∣ w.q := hq.dvd_of_dvd_pow h1
        have hq_eq : q = w.q := (Nat.prime_dvd_prime_iff_eq hq hwp).mp hqdvd
        exact ⟨w, List.mem_cons_self, hq_eq⟩
      · have hrest := ih (fun w' hw' => hprime w' (List.mem_cons_of_mem w hw')) q hq h2
        obtain ⟨w', hw', heq⟩ := hrest
        exact ⟨w', List.mem_cons_of_mem w hw', heq⟩

/-- The fast verifier discharges Pocklington primality: if
`RawCertFast.verify cert = true` and `2 ≤ cert.n`, then `cert.n` is prime. -/
theorem pocklington_fast (c : RawCertFast) (hn : 2 ≤ c.n)
    (hverify : c.verify = true) : Nat.Prime c.n := by
  -- Decompose the conjunction.
  unfold RawCertFast.verify at hverify
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hverify
  obtain ⟨⟨⟨⟨⟨_, hFR⟩, hCop⟩, hLarge⟩, hProd⟩, hAll⟩ := hverify
  -- Each witness's local check holds.
  have hwit : ∀ w ∈ c.witnesses, RawWitnessFast.check c.n c.F w = true := hAll
  -- Each witness's q is prime.
  have hPrimes : ∀ w ∈ c.witnesses, Nat.Prime w.q := by
    intro w hw
    have h := hwit w hw
    unfold RawWitnessFast.check at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1.2
  -- Build the PocklingtonCert.
  refine pocklington c.n hn ?_
  refine
    { F := c.F
      R := c.R
      hFR := hFR
      hCoprime := hCop
      hLarge := hLarge
      witnesses := ?_ }
  intro q hq hqF
  -- Find the witness for q via factProd.
  have hqDvdProd : q ∣ (c.witnesses.map (fun w => w.q ^ w.e)).prod := by
    rw [show (c.witnesses.map (fun w => w.q ^ w.e)).prod = c.F from hProd]
    exact hqF
  -- The existential `∃ w ∈ c.witnesses, q = w.q` is in `Prop`, but we are
  -- building data of type `PocklingtonWitness`. Use classical choice.
  have hex := covers_of_factProd c.witnesses hPrimes q hq hqDvdProd
  classical
  let w := Classical.choose hex
  have hwspec : w ∈ c.witnesses ∧ q = w.q := by
    have h := Classical.choose_spec hex
    refine ⟨?_, ?_⟩
    · exact h.1
    · exact h.2
  obtain ⟨hwIn, hqEq⟩ := hwspec
  -- Extract witness fields.
  have hw_check := hwit w hwIn
  unfold RawWitnessFast.check at hw_check
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw_check
  obtain ⟨⟨⟨⟨⟨_, hwq_prime⟩, hwq_dvd_F⟩, _⟩, hpow⟩, hgcd⟩ := hw_check
  -- Build the PocklingtonWitness for q.
  refine
    { a := (w.a : ZMod c.n)
      q_prime := hq
      q_dvd_F := hqF
      pow_eq_one := ?_
      pow_sub_one_isUnit := ?_ }
  · -- a^(n-1) = 1.
    rw [hqEq] at *
    exact hpow
  · -- (a^((n-1)/q) - 1) is a unit, from gcd-coprime.
    rw [hqEq]
    haveI : NeZero c.n := ⟨by omega⟩
    rw [← ZMod.natCast_zmod_val ((w.a : ZMod c.n) ^ ((c.n - 1) / w.q) - 1),
        ZMod.isUnit_iff_coprime]
    exact hgcd

end Pocklington
