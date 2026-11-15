/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Algebra.IsPrimePow

/-!
# The reduction of factoring to order finding

Shor's classical post-processing: for a unit `a` modulo `N` of even order `r` with
`a^{r/2} ≢ -1 (mod N)`, `gcd(a^{r/2} - 1, N)` is a nontrivial divisor of `N`, since
`N ∣ (a^{r/2} - 1)(a^{r/2} + 1)` while `N` divides neither factor. For `N` odd with at least
two distinct prime factors, at most half of the units are bad (odd order, or
`a^{r/2} = -1`): write `N = p^e M` with `p ∤ M`; through the Chinese remainder theorem a bad
unit has components of orders with equal `2`-adic valuation, and in the cyclic group
`(ZMod p^e)ˣ` of even order each value of the `2`-adic valuation of the order is taken by at
most half of the elements (Nielsen–Chuang, Theorem A4.13, the case of two factors).

## Main results

* `ShorReduction.one_lt_gcd_pow_half_sub_one` — `1 < gcd(a^{r/2} - 1, N) < N`.
* `ShorReduction.shorBad` — the units of odd order or with `u^{r/2} = -1`.
* `ShorReduction.two_mul_card_le_card_of_isCyclic` — in a finite cyclic group of even order,
  each value of the `2`-adic valuation of the order is taken by at most half of the elements.
* `ShorReduction.two_mul_card_shorBad_le` — `2 · #bad ≤ #(ZMod N)ˣ` for odd `N > 1` that is
  not a prime power.
* `ShorReduction.dvd_half_of_factorization_two_lt` — a divisor of `r` with smaller `2`-adic
  valuation than `r` divides `r / 2`.
* `ShorReduction.ordTwoVal_eq_of_bad_pair` — a pair whose order is odd or whose half-power is
  `(eG, eH)` with `eG, eH ≠ 1` has components of equal `2`-adic order valuation.
* `ShorReduction.two_mul_card_filter_ordTwoVal_eq_le` — in `G × H` with `G` cyclic of even
  order, at most half of the pairs have equal `2`-adic order valuations.
* `ShorReduction.exists_coprime_split_of_not_isPrimePow` — an odd `N > 1` that is not a prime
  power is `p ^ e * M` with `p` an odd prime and `M > 2` coprime to `p ^ e`.
* `ShorReduction.two_mul_card_shorBad_le_of_coprime` — the counting bound for `q * M` with
  `q`, `M > 2` coprime and `(ZMod q)ˣ` cyclic of even order.
-/

@[expose] public section

set_option autoImplicit false

open Finset

namespace ShorReduction

/-- If `a` has even order `r > 0` modulo `N` and `a^{r/2} ≢ -1`, then `gcd(a^{r/2} - 1, N)` is a
nontrivial divisor of `N`. -/
theorem one_lt_gcd_pow_half_sub_one {N a r : ℕ} (hr : orderOf (a : ZMod N) = r) (hr0 : 0 < r)
    (he : Even r) (hne : (a : ZMod N) ^ (r / 2) ≠ -1) :
    1 < Nat.gcd (a ^ (r / 2) - 1) N ∧ Nat.gcd (a ^ (r / 2) - 1) N < N := by
  have hr2 : 2 ≤ r := by obtain ⟨k, hk⟩ := he; omega
  have hx1 : (a : ZMod N) ^ (r / 2) ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hsq : (a : ZMod N) ^ (r / 2) * (a : ZMod N) ^ (r / 2) = 1 := by
    have h1 := pow_orderOf_eq_one (a : ZMod N)
    rw [hr] at h1
    have h2 : r / 2 + r / 2 = r := by obtain ⟨k, hk⟩ := he; omega
    rw [← pow_add, h2, h1]
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N
    · rcases mul_self_eq_one_iff.mp hsq with h | h
      · exact absurd h hx1
      · exact absurd h hne
    · exact absurd (Subsingleton.elim _ _) hx1
  · have : Fact (1 < N) := ⟨hN⟩
    have hcast : (((a ^ (r / 2) : ℕ)) : ZMod N) = (a : ZMod N) ^ (r / 2) := by push_cast; rfl
    have hx0 : 1 ≤ a ^ (r / 2) := by
      by_contra hx
      have h0 : a ^ (r / 2) = 0 := by omega
      rw [h0] at hcast
      rw [← hcast] at hsq
      simp at hsq
    have hdvd : N ∣ (a ^ (r / 2) - 1) * (a ^ (r / 2) + 1) := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast [Nat.cast_sub hx0]
      linear_combination hsq
    refine ⟨?_, ?_⟩
    · have hpos : 0 < Nat.gcd (a ^ (r / 2) - 1) N := Nat.gcd_pos_of_pos_right _ (by omega)
      by_contra hle
      have hg : Nat.gcd (a ^ (r / 2) - 1) N = 1 := by omega
      have hcop : Nat.Coprime N (a ^ (r / 2) - 1) := by
        rw [Nat.coprime_comm]; exact hg
      have h2 := hcop.dvd_of_dvd_mul_left hdvd
      rw [← ZMod.natCast_eq_zero_iff] at h2
      push_cast at h2
      exact hne (by linear_combination h2)
    · have hle : Nat.gcd (a ^ (r / 2) - 1) N ≤ N := Nat.gcd_le_right _ (by omega)
      by_contra hge
      have hg : Nat.gcd (a ^ (r / 2) - 1) N = N := by omega
      have h2 : N ∣ a ^ (r / 2) - 1 := by
        rw [← hg]; exact Nat.gcd_dvd_left _ _
      rw [← ZMod.natCast_eq_zero_iff] at h2
      push_cast [Nat.cast_sub hx0] at h2
      exact hx1 (by linear_combination h2)

/-- The `2`-adic valuation of the order of a group element. -/
noncomputable def ordTwoVal {G : Type*} [Monoid G] (x : G) : ℕ :=
  (orderOf x).factorization 2

/-- In a finite cyclic group of even order, each value of the `2`-adic valuation of the
order is taken by at most half of the elements. -/
theorem two_mul_card_le_card_of_isCyclic {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    [IsCyclic G] (hG : Even (Fintype.card G)) (d : ℕ) :
    2 * (univ.filter fun x : G => ordTwoVal x = d).card ≤ Fintype.card G := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hpow : ∀ x : G, ∃ i : ℕ, g ^ i = x := fun x =>
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg x))
  have hn0 : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hk : 1 ≤ (Fintype.card G).factorization 2 :=
    Nat.prime_two.factorization_pos_of_dvd hn0 (even_iff_two_dvd.mp hG)
  have key : ∀ i : ℕ, ordTwoVal (g ^ i) = (Fintype.card G).factorization 2 ↔ ¬ 2 ∣ i := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [pow_zero, ordTwoVal, orderOf_one, Nat.factorization_one, Finsupp.coe_zero,
        Pi.zero_apply, dvd_zero, not_true_eq_false, iff_false]
      omega
    · have h1 : orderOf (g ^ i) = Fintype.card G / Nat.gcd (Fintype.card G) i := by
        rw [orderOf_pow' _ hi.ne', hord]
      have h2 : ordTwoVal (g ^ i) = (Fintype.card G).factorization 2 -
          ((Fintype.card G).gcd i).factorization 2 := by
        unfold ordTwoVal
        rw [h1, Nat.factorization_div (Nat.gcd_dvd_left _ _)]
        rfl
      have hv : i.factorization 2 = 0 ↔ ¬ 2 ∣ i := by
        rw [Nat.factorization_eq_zero_iff]
        simp [hi.ne', Nat.prime_two]
      rw [h2, Nat.factorization_gcd hn0 hi.ne']
      simp only [Finsupp.inf_apply]
      omega
  have hflip : ∀ x : G, ordTwoVal x = (Fintype.card G).factorization 2 ↔
      ¬ ordTwoVal (x * g) = (Fintype.card G).factorization 2 := by
    intro x
    obtain ⟨i, rfl⟩ := hpow x
    rw [← pow_succ, key, key]
    omega
  have hAB : (univ.filter fun x : G => ordTwoVal x = (Fintype.card G).factorization 2).card ≤
      (univ.filter fun x : G => ¬ ordTwoVal x = (Fintype.card G).factorization 2).card :=
    card_le_card_of_injOn (· * g)
      (fun x hx => by
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
        exact (hflip x).mp hx)
      (fun x _ y _ h => mul_right_cancel h)
  have hBA : (univ.filter fun x : G => ¬ ordTwoVal x = (Fintype.card G).factorization 2).card ≤
      (univ.filter fun x : G => ordTwoVal x = (Fintype.card G).factorization 2).card :=
    card_le_card_of_injOn (· * g)
      (fun x hx => by
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
        have := hflip x
        tauto)
      (fun x _ y _ h => mul_right_cancel h)
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset G))
    (fun x : G => ordTwoVal x = (Fintype.card G).factorization 2)
  rw [card_univ] at hsum
  by_cases hd : d = (Fintype.card G).factorization 2
  · subst hd
    omega
  · have hsub : (univ.filter fun x : G => ordTwoVal x = d) ⊆
        (univ.filter fun x : G => ¬ ordTwoVal x = (Fintype.card G).factorization 2) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      omega
    have := card_le_card hsub
    omega

/-- A divisor `a` of `r` whose `2`-adic valuation is below that of `r` divides `r / 2`. -/
theorem dvd_half_of_factorization_two_lt {a r : ℕ} (ha : a ≠ 0) (hr : r ≠ 0) (hdvd : a ∣ r)
    (hlt : a.factorization 2 < r.factorization 2) : a ∣ r / 2 := by
  have h2 : 2 ∣ r := by
    by_contra h
    have := Nat.factorization_eq_zero_of_not_dvd h
    omega
  have hr2 : r / 2 ≠ 0 := by
    obtain ⟨k, hk⟩ := h2
    omega
  rw [← Nat.factorization_prime_le_iff_dvd ha hr2]
  intro p hp
  have hle : a.factorization p ≤ r.factorization p :=
    ((Nat.factorization_le_iff_dvd ha hr).mpr hdvd) p
  rw [Nat.factorization_div h2]
  by_cases hp2 : p = 2
  · subst hp2
    simp [Nat.prime_two.factorization]
    omega
  · simp [Nat.prime_two.factorization, Ne.symm hp2]
    omega

/-- If the components `x`, `y` of a pair of finite order have different `2`-adic valuations of their
orders, then the order of the pair is even and its half-power is not `(eG, eH)` for `eG`, `eH`
different from `1`. -/
theorem ordTwoVal_eq_of_bad_pair {G H : Type*} [Monoid G] [Monoid H] {x : G} {y : H}
    (hx : 0 < orderOf x) (hy : 0 < orderOf y) {eG : G} {eH : H} (hG : eG ≠ 1) (hH : eH ≠ 1)
    (hbad : Odd (orderOf (x, y)) ∨ (x, y) ^ (orderOf (x, y) / 2) = (eG, eH)) :
    ordTwoVal x = ordTwoVal y := by
  have hr : orderOf (x, y) = (orderOf x).lcm (orderOf y) := Prod.orderOf_mk
  have hr0 : (orderOf x).lcm (orderOf y) ≠ 0 := (Nat.lcm_pos hx hy).ne'
  have hv : ((orderOf x).lcm (orderOf y)).factorization 2 = max (ordTwoVal x) (ordTwoVal y) := by
    rw [Nat.factorization_lcm hx.ne' hy.ne']
    rfl
  rw [hr] at hbad
  rcases hbad with hodd | hpow
  · have h2x : ¬ 2 ∣ orderOf x := fun h =>
      (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h.trans (Nat.dvd_lcm_left _ _)))
    have h2y : ¬ 2 ∣ orderOf y := fun h =>
      (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h.trans (Nat.dvd_lcm_right _ _)))
    unfold ordTwoVal
    rw [Nat.factorization_eq_zero_of_not_dvd h2x, Nat.factorization_eq_zero_of_not_dvd h2y]
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hdvd := dvd_half_of_factorization_two_lt hx.ne' hr0 (Nat.dvd_lcm_left _ _)
        (by rw [hv]; exact lt_max_of_lt_right hlt)
      have h1 : x ^ ((orderOf x).lcm (orderOf y) / 2) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
      have h2 := congrArg Prod.fst hpow
      rw [Prod.pow_fst] at h2
      exact hG (h2.symm.trans h1)
    · have hdvd := dvd_half_of_factorization_two_lt hy.ne' hr0 (Nat.dvd_lcm_right _ _)
        (by rw [hv]; exact lt_max_of_lt_left hlt)
      have h1 : y ^ ((orderOf x).lcm (orderOf y) / 2) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
      have h2 := congrArg Prod.snd hpow
      rw [Prod.pow_snd] at h2
      exact hH (h2.symm.trans h1)

/-- The units `u` modulo `N` for which Shor's post-processing fails: odd order, or
`u^{r/2} = -1` for the order `r`. -/
noncomputable def shorBad (N : ℕ) [NeZero N] : Finset (ZMod N)ˣ :=
  univ.filter fun u => Odd (orderOf u) ∨ u ^ (orderOf u / 2) = -1

/-- In a product of a finite cyclic group `G` of even order and a finite monoid `H`, at most half
of the pairs have components with the same `2`-adic valuation of their orders. -/
theorem two_mul_card_filter_ordTwoVal_eq_le {G H : Type*} [Group G] [Fintype G] [DecidableEq G]
    [IsCyclic G] [Monoid H] [Fintype H] (hG : Even (Fintype.card G)) :
    2 * (univ.filter fun u : G × H => ordTwoVal u.1 = ordTwoVal u.2).card ≤
      Fintype.card G * Fintype.card H := by
  have h1 : (univ.filter fun u : G × H => ordTwoVal u.1 = ordTwoVal u.2).card =
      ∑ y : H, (univ.filter fun x : G => ordTwoVal x = ordTwoVal y).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    exact Finset.sum_congr rfl fun y _ => (Finset.card_filter _ _).symm
  calc 2 * (univ.filter fun u : G × H => ordTwoVal u.1 = ordTwoVal u.2).card
      = ∑ y : H, 2 * (univ.filter fun x : G => ordTwoVal x = ordTwoVal y).card := by
        rw [h1, Finset.mul_sum]
    _ ≤ ∑ _y : H, Fintype.card G :=
        Finset.sum_le_sum fun y _ => two_mul_card_le_card_of_isCyclic hG _
    _ = Fintype.card G * Fintype.card H := by simp [mul_comm]

/-- For coprime `q`, `M > 2` with `(ZMod q)ˣ` cyclic of even order, at most half of the units
modulo `q * M` are bad. -/
theorem two_mul_card_shorBad_le_of_coprime {q M : ℕ} [NeZero q] [NeZero M] (hcop : q.Coprime M)
    (hq : 2 < q) (hM : 2 < M) [IsCyclic (ZMod q)ˣ] (hev : Even (Fintype.card (ZMod q)ˣ)) :
    2 * (shorBad (q * M)).card ≤ Fintype.card (ZMod (q * M))ˣ := by
  let e : (ZMod (q * M))ˣ ≃* (ZMod q)ˣ × (ZMod M)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder hcop).toMulEquiv).trans MulEquiv.prodUnits
  have hcard : Fintype.card (ZMod (q * M))ˣ =
      Fintype.card (ZMod q)ˣ * Fintype.card (ZMod M)ˣ := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr e.toEquiv
  have hneg : e (-1) = (-1, -1) := by
    have h1 : ((Units.mapEquiv (ZMod.chineseRemainder hcop).toMulEquiv (-1) :
        (ZMod q × ZMod M)ˣ) : ZMod q × ZMod M) = (-1, -1) := by
      rw [Units.coe_mapEquiv]
      change ZMod.chineseRemainder hcop ((-1 : (ZMod (q * M))ˣ) : ZMod (q * M)) = (-1, -1)
      rw [Units.val_neg, Units.val_one, map_neg, map_one]
      rfl
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · exact (congrArg Prod.fst h1).trans (by simp)
    · exact (congrArg Prod.snd h1).trans (by simp)
  have : Fact (2 < q) := ⟨hq⟩
  have : Fact (2 < M) := ⟨hM⟩
  have hq1 : (-1 : (ZMod q)ˣ) ≠ 1 := fun h =>
    ZMod.neg_one_ne_one (by simpa using congrArg Units.val h)
  have hM1 : (-1 : (ZMod M)ˣ) ≠ 1 := fun h =>
    ZMod.neg_one_ne_one (by simpa using congrArg Units.val h)
  have hsub : (shorBad (q * M)).card ≤
      (univ.filter fun u : (ZMod q)ˣ × (ZMod M)ˣ => ordTwoVal u.1 = ordTwoVal u.2).card := by
    refine card_le_card_of_injOn e (fun u hu => ?_) (fun u _ v _ h => e.injective h)
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    simp only [shorBad, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu
    have hu' : Odd (orderOf (e u)) ∨ (e u) ^ (orderOf (e u) / 2) = (-1, -1) := by
      rw [MulEquiv.orderOf_eq]
      rcases hu with h | h
      · exact Or.inl h
      · right
        rw [← map_pow, h, hneg]
    exact ordTwoVal_eq_of_bad_pair (orderOf_pos _) (orderOf_pos _) hq1 hM1 hu'
  have := two_mul_card_filter_ordTwoVal_eq_le (G := (ZMod q)ˣ) (H := (ZMod M)ˣ) hev
  rw [hcard]
  omega

/-- An odd `N > 1` that is not a prime power is `p ^ e * M` with `p` an odd prime, `e > 0` and
`M > 2` coprime to `p ^ e`. -/
theorem exists_coprime_split_of_not_isPrimePow {N : ℕ} (hN : Odd N) (hpp : ¬ IsPrimePow N)
    (h1 : 1 < N) :
    ∃ p e M : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < e ∧ 2 < M ∧ (p ^ e).Coprime M ∧ N = p ^ e * M := by
  have hN0 : N ≠ 0 := by omega
  have hp : (N.minFac).Prime := Nat.minFac_prime (by omega)
  have hpN : N.minFac ∣ N := Nat.minFac_dvd N
  have he : 0 < N.factorization N.minFac := hp.factorization_pos_of_dvd hN0 hpN
  have hsplit : N.minFac ^ N.factorization N.minFac * (N / N.minFac ^ N.factorization N.minFac) =
      N := Nat.ordProj_mul_ordCompl_eq_self N N.minFac
  have hcop : N.minFac.Coprime (N / N.minFac ^ N.factorization N.minFac) :=
    Nat.coprime_ordCompl hp hN0
  have hMne1 : N / N.minFac ^ N.factorization N.minFac ≠ 1 := by
    intro hM
    apply hpp
    rw [isPrimePow_nat_iff]
    refine ⟨N.minFac, N.factorization N.minFac, hp, he, ?_⟩
    rw [hM, mul_one] at hsplit
    exact hsplit
  have hModd : Odd (N / N.minFac ^ N.factorization N.minFac) := by
    rw [← hsplit] at hN
    exact (Nat.odd_mul.mp hN).2
  have hp2 : N.minFac ≠ 2 := by
    intro h
    rw [h] at hpN
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr hpN)
  refine ⟨N.minFac, N.factorization N.minFac, N / N.minFac ^ N.factorization N.minFac, hp, hp2, he,
    ?_, hcop.pow_left _, hsplit.symm⟩
  obtain ⟨k, hk⟩ := hModd
  omega

/-- For odd `N > 1` that is not a prime power, at most half of the units modulo `N` are bad. -/
theorem two_mul_card_shorBad_le {N : ℕ} [NeZero N] (hN : Odd N) (hpp : ¬ IsPrimePow N)
    (h1 : 1 < N) : 2 * (shorBad N).card ≤ Fintype.card (ZMod N)ˣ := by
  obtain ⟨p, e, M, hp, hp2, he, hM, hcop, rfl⟩ := exists_coprime_split_of_not_isPrimePow hN hpp h1
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero M := ⟨by omega⟩
  have := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have hq : 2 < p ^ e := by
    have h2 := hp.two_le
    have h3 := Nat.le_self_pow he.ne' p
    omega
  have hev : Even (Fintype.card (ZMod (p ^ e))ˣ) := by
    rw [ZMod.card_units_eq_totient]
    exact Nat.totient_even hq
  exact two_mul_card_shorBad_le_of_coprime hcop hq hM hev

end ShorReduction
