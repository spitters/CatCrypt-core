/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.CompositePerTable
public import CatCryptCore.Quantum.QROM.HopResampleGood

/-!
# The key-from-ciphertext relabelling on a table resampled to good values

A value of the `G`-table is a key part and a coin part (`eKR`). The predicate
`kemBad pk sk` marks a value at a point `(m, hpk pk)` as bad when the coin part
does not decrypt back to `m`; it reads the coin part only. The resampling of a
uniform table to good values (`resampleTable`, law `tableMass`) therefore leaves
the key parts uniform and independent of the coins, and the key-from-ciphertext
relabelling `keyHop` of `Quantum/QROM/HopKeyFromCiphertext.lean` preserves the
resampled law on the tables whose ciphertext map is injective on the
public-key slice. With the challenge point `t = (m*, hpk pk)` exempted from the
resampling (`offPoint`), every message other than `m*` is good on the resampled
table, so the ciphertext map fails to be injective only when `m*` is bad; that
event has weight `δ* = |badVals t| / n`, the decryption-failure probability of
the single message `m*`.

## Main definitions

* `CoinOnly ε bad` — `bad` reads the coin part `(ε y).2` of a value only
* `setKeys ε κ g` — the table `g` with its key parts replaced by `κ`
* `keyExch ε` — the involution exchanging the key parts of a table with a key
  table
* `kemBad P hpk eG eKR pk sk` — the values at a slice point whose coin part
  does not decrypt back to the message of the point

## Main results

* `resampleAvg_eq_sum_tableMass` — the resampled table has the law `tableMass`
* `sum_tableMass_setKeys`, `resampleAvg_setKeys` — for a coin-only predicate the
  resampled law is unchanged when the key parts are redrawn uniformly
* `tableMass_keyHop` — `tableMass` is invariant under `keyHop`
* `sum_keyHop_weighted` — the relabelling `sum_keyHop` under a weight invariant
  under `keyHop`
* `absDiff_keyHop_le` — averaging a bounded function over `Hq` at the hopped
  table changes its weighted sum by at most the weight of the non-injective
  tables
* `sum_tableMass_not_sliceInj_le` — on the table resampled off the challenge
  point, that weight is at most `δ*`
* `absDiff_winSimJ_winHJ_resampled` — on the resampled table the simulated game
  and the hopped game differ by at most `δ*`, at every fixed rest of the input
* `absDiff_winSimJ_winHJ_triangle`, `absDiff_prWinKEMSimJ_prWinKEMHJ_le` — the
  triangle through the resampled table, per rest and averaged over the rest

## The triangle

The bound of `absDiff_prWinKEMSimJ_prWinKEMHJ_le` is the average over the rest of
the input of three terms: the distance between the uniform and the resampled
table for the simulated game, the same distance for the hopped game, and the
decryption-failure weight `restDelta r` of the challenge message. Its hypothesis `hcoin` states that every key pair in the support of
`keygen` has, for each message, a coin that decrypts correctly, so that the
resampling weight is a probability weight.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The key parts of a resampled table -/

section KeyParts

variable {m n : ℕ} {K R : Type} (ε : Fin n ≃ K × R)

/-- The predicate `bad` reads the coin part of a value only. -/
def CoinOnly (bad : Fin m → Fin n → Bool) : Prop :=
  ∀ x y y', (ε y).2 = (ε y').2 → bad x y = bad x y'

/-- The table `g` with its key parts replaced by `κ`, the coin parts kept. -/
def setKeys (κ : Fin m → K) (g : Fin m → Fin n) : Fin m → Fin n :=
  fun x => ε.symm (κ x, (ε (g x)).2)

/-- The exchange of the key parts of a table with a key table. -/
def keyExch (p : (Fin m → Fin n) × (Fin m → K)) : (Fin m → Fin n) × (Fin m → K) :=
  (setKeys ε p.2 p.1, fun x => (ε (p.1 x)).1)

theorem keyExch_involutive : Function.Involutive (keyExch ε (m := m)) := by
  rintro ⟨g, κ⟩
  refine Prod.ext (funext fun x => ?_) (funext fun x => ?_) <;> simp [keyExch, setKeys]

variable {ε} {bad : Fin m → Fin n → Bool}

theorem CoinOnly.offPoint (h : CoinOnly ε bad) (t : Fin m) : CoinOnly ε (offPoint bad t) := by
  intro x y y' hy
  simp only [QROM.offPoint, h x y y' hy]

theorem tableMass_eq_of_coins (h : CoinOnly ε bad) {g g' : Fin m → Fin n}
    (hc : ∀ x, (ε (g x)).2 = (ε (g' x)).2) : tableMass bad g = tableMass bad g' :=
  Finset.prod_congr rfl fun x _ => by simp only [goodMass, h x _ _ (hc x)]

theorem tableMass_setKeys (h : CoinOnly ε bad) (κ : Fin m → K) (g : Fin m → Fin n) :
    tableMass bad (setKeys ε κ g) = tableMass bad g :=
  tableMass_eq_of_coins h fun x => by simp [setKeys]

/-- The resampled table has the law `tableMass`. -/
theorem resampleAvg_eq_sum_tableMass [NeZero n] (hgood : ∀ x, ∃ y, bad x y = false)
    (f : (Fin m → Fin n) → ℝ≥0∞) :
    resampleAvg bad f = ∑ G : Fin m → Fin n, tableMass bad G * f G := by
  unfold resampleAvg pairMass resampleTable
  rw [sum_pi_fiber (fun x (p : Fin n × Fin n) => (n : ℝ≥0∞)⁻¹ * goodMass bad x p.2)
    (fun x (p : Fin n × Fin n) => if bad x p.1 then p.2 else p.1) f]
  refine Finset.sum_congr rfl fun G _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun x _ => ?_
  simpa only [mul_one] using sum_fiber_resample_one hgood x (G x)

variable [Fintype K]

/-- For a coin-only predicate the key parts of a `tableMass`-distributed table
are uniform and independent of the coin parts: redrawing them uniformly leaves
the law unchanged. -/
theorem sum_tableMass_setKeys (h : CoinOnly ε bad) (f : (Fin m → Fin n) → ℝ≥0∞) :
    ∑ g : Fin m → Fin n, ∑ κ : Fin m → K, tableMass bad g * f (setKeys ε κ g) =
      ∑ g : Fin m → Fin n, ∑ _κ : Fin m → K, tableMass bad g * f g := by
  rw [← Fintype.sum_prod_type' (f := fun g κ => tableMass bad g * f (setKeys ε κ g)),
    ← Fintype.sum_prod_type' (f := fun g (_ : Fin m → K) => tableMass bad g * f g)]
  refine Fintype.sum_equiv ((keyExch_involutive ε).toPerm _) _ _ fun p => ?_
  change _ = tableMass bad (setKeys ε p.2 p.1) * f (setKeys ε p.2 p.1)
  rw [tableMass_setKeys h]

/-- The resampled law factors as the resampled coin parts times uniform key
parts: averaging `f` over a uniform redraw of the key parts does not change its
resampled average. -/
theorem resampleAvg_setKeys [NeZero n] [Nonempty K] (h : CoinOnly ε bad)
    (hgood : ∀ x, ∃ y, bad x y = false) (f : (Fin m → Fin n) → ℝ≥0∞) :
    resampleAvg bad (fun g => ∑ κ : Fin m → K,
        (Fintype.card (Fin m → K) : ℝ≥0∞)⁻¹ * f (setKeys ε κ g)) = resampleAvg bad f := by
  set c : ℝ≥0∞ := (Fintype.card (Fin m → K) : ℝ≥0∞)⁻¹ with hc
  have hcsum : ∀ t : ℝ≥0∞, ∑ _κ : Fin m → K, c * t = t := by
    intro t
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hc,
      ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
      one_mul]
  rw [resampleAvg_eq_sum_tableMass hgood, resampleAvg_eq_sum_tableMass hgood]
  simp only [Finset.mul_sum]
  rw [sum_tableMass_setKeys h (fun g => c * f g)]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [mul_left_comm (tableMass bad g) c]
  exact hcsum _

end KeyParts

/-! ## The relabelling under a key-invariant weight -/

section Relabel

variable {m n : ℕ} {K R C : Type} (S : Fin m → Prop) [DecidablePred S] (e : Fin m → R → C)
  (ε : Fin n ≃ K × R)

theorem coins_keyHop (Hq : C → K) (g : Fin m → Fin n) (x : Fin m) :
    (ε (keyHop S e ε Hq g x)).2 = (ε (g x)).2 := by
  unfold keyHop
  split_ifs <;> simp

/-- `tableMass` of a coin-only predicate is invariant under `keyHop`. -/
theorem tableMass_keyHop {bad : Fin m → Fin n → Bool} (h : CoinOnly ε bad) (Hq : C → K)
    (g : Fin m → Fin n) : tableMass bad (keyHop S e ε Hq g) = tableMass bad g :=
  tableMass_eq_of_coins h (coins_keyHop S e ε Hq g)

variable [Fintype C] [DecidableEq C] [Fintype K]

open scoped Classical in
/-- The relabelling `sum_keyHop` under a weight on tables that is invariant under
`keyHop`. -/
theorem sum_keyHop_weighted (w : (Fin m → Fin n) → ℝ≥0∞)
    (hw : ∀ (Hq : C → K) g, w (keyHop S e ε Hq g) = w g)
    (F : (Fin m → Fin n) → (C → Option K) → ℝ≥0∞) :
    ∑ g : Fin m → Fin n, ∑ Hq : C → K, w g *
        (if SliceInj S e ε g then F (keyHop S e ε Hq g) (offImage S e ε g Hq) else 0) =
      ∑ g : Fin m → Fin n, ∑ Hq : C → K, w g *
        (if SliceInj S e ε g then F g (offImage S e ε g Hq) else 0) := by
  have h := sum_keyHop S e ε (fun g o => w g * F g o)
  simp only [hw] at h
  simpa only [mul_ite, mul_zero] using h

variable [Nonempty K]

open scoped Classical in
/-- The relabelling up to the non-injective tables: for a weight invariant under
`keyHop` and `Φ ≤ 1`, averaging `Φ` over a uniform `Hq` at the hopped table
changes the weighted sum by at most the weight of the tables whose ciphertext
map is not injective on the slice. -/
theorem absDiff_keyHop_le (w : (Fin m → Fin n) → ℝ≥0∞)
    (hw : ∀ (Hq : C → K) g, w (keyHop S e ε Hq g) = w g)
    (Φ : (Fin m → Fin n) → ℝ≥0∞) (hΦ : ∀ g, Φ g ≤ 1) :
    absDiff (∑ g : Fin m → Fin n, w g *
          ∑ Hq : C → K, (Fintype.card (C → K) : ℝ≥0∞)⁻¹ * Φ (keyHop S e ε Hq g))
        (∑ g : Fin m → Fin n, w g * Φ g) ≤
      ∑ g : Fin m → Fin n, w g * (if SliceInj S e ε g then 0 else 1) := by
  set κ : ℝ≥0∞ := (Fintype.card (C → K) : ℝ≥0∞)⁻¹ with hκ
  have hκsum : ∀ t : ℝ≥0∞, ∑ _Hq : C → K, κ * t = t := by
    intro t
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hκ,
      ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
      one_mul]
  have hsplit : ∀ (p : Prop) [Decidable p] (x : ℝ≥0∞),
      x = (if p then x else 0) + (if p then 0 else x) := by
    intro p _ x; split_ifs <;> simp
  set D := ∑ g : Fin m → Fin n, w g * (if SliceInj S e ε g then 0 else 1)
  set A0 := ∑ g : Fin m → Fin n, w g * (if SliceInj S e ε g then Φ g else 0)
  have hA := sum_keyHop_weighted S e ε w hw (fun g _ => κ * Φ g)
  have h1 : ∀ g : Fin m → Fin n,
      w g * (if SliceInj S e ε g then ∑ Hq : C → K, κ * Φ (keyHop S e ε Hq g) else 0) =
        ∑ Hq : C → K, w g * (if SliceInj S e ε g then κ * Φ (keyHop S e ε Hq g) else 0) := by
    intro g; split_ifs <;> simp [Finset.mul_sum]
  have h2 : ∀ g : Fin m → Fin n,
      ∑ Hq : C → K, w g * (if SliceInj S e ε g then κ * Φ g else 0) =
        w g * (if SliceInj S e ε g then Φ g else 0) := by
    intro g
    split_ifs
    · rw [← Finset.mul_sum, hκsum]
    · simp
  have hL : ∑ g : Fin m → Fin n, w g * ∑ Hq : C → K, κ * Φ (keyHop S e ε Hq g) =
      A0 + ∑ g : Fin m → Fin n, w g *
        (if SliceInj S e ε g then 0 else ∑ Hq : C → K, κ * Φ (keyHop S e ε Hq g)) := by
    calc ∑ g : Fin m → Fin n, w g * ∑ Hq : C → K, κ * Φ (keyHop S e ε Hq g)
        = ∑ g : Fin m → Fin n,
            (w g * (if SliceInj S e ε g then ∑ Hq : C → K, κ * Φ (keyHop S e ε Hq g) else 0) +
              w g * (if SliceInj S e ε g then 0
                else ∑ Hq : C → K, κ * Φ (keyHop S e ε Hq g))) :=
          Finset.sum_congr rfl fun g _ => by rw [← mul_add, ← hsplit]
      _ = _ := by
          rw [Finset.sum_add_distrib]
          congr 1
          simp only [h1]
          rw [hA]
          simp only [h2]
          rfl
  have hR : ∑ g : Fin m → Fin n, w g * Φ g =
      A0 + ∑ g : Fin m → Fin n, w g * (if SliceInj S e ε g then 0 else Φ g) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← mul_add, ← hsplit]
  have hB1 : ∑ g : Fin m → Fin n, w g *
      (if SliceInj S e ε g then 0 else ∑ Hq : C → K, κ * Φ (keyHop S e ε Hq g)) ≤ D := by
    refine Finset.sum_le_sum fun g _ => ?_
    split_ifs
    · simp
    · gcongr
      calc ∑ Hq : C → K, κ * Φ (keyHop S e ε Hq g) ≤ ∑ _Hq : C → K, κ * 1 :=
            Finset.sum_le_sum fun Hq _ => by gcongr; exact hΦ _
        _ = 1 := hκsum 1
  have hB2 : ∑ g : Fin m → Fin n, w g * (if SliceInj S e ε g then 0 else Φ g) ≤ D := by
    refine Finset.sum_le_sum fun g _ => ?_
    split_ifs
    · simp
    · gcongr; exact hΦ g
  rw [hL, hR]
  refine absDiff_le_iff.mpr ⟨?_, ?_⟩
  · calc _ ≤ A0 + D := add_le_add le_rfl hB1
      _ ≤ _ := by rw [add_assoc]; exact add_le_add le_rfl le_add_self
  · calc _ ≤ A0 + D := add_le_add le_rfl hB2
      _ ≤ _ := by rw [add_assoc]; exact add_le_add le_rfl le_add_self

end Relabel

/-! ## The bad predicate of the KEM game -/

section KEMBad

variable {m₁ n : ℕ} {PK SK M C R K Hash : Type} [DecidableEq Hash] [DecidableEq M]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eKR : (K × R) ≃ Fin n)

/-- A value `y` at a point `x = (m, h)` of the `G`-table is bad for the key pair
`(pk, sk)` when `h = hpk pk` and the ciphertext of `m` under the coin part of
`y` does not decrypt back to `m`. -/
def kemBad (pk : PK) (sk : SK) : Fin m₁ → Fin n → Bool := fun x y =>
  decide ((eG.symm x).2 = hpk pk) &&
    !decide (P.dec sk (P.enc pk (eG.symm x).1 (eKR.symm y).2) = some (eG.symm x).1)

theorem kemBad_coinOnly (pk : PK) (sk : SK) : CoinOnly eKR.symm (kemBad P hpk eG eKR pk sk) := by
  intro x y y' h
  simp only [kemBad, h]

theorem dec_of_kemBad_eq_false {pk : PK} {sk : SK} {x : Fin m₁} {y : Fin n}
    (hx : (eG.symm x).2 = hpk pk) (h : kemBad P hpk eG eKR pk sk x y = false) :
    P.dec sk (P.enc pk (eG.symm x).1 (eKR.symm y).2) = some (eG.symm x).1 := by
  simpa [kemBad, hx] using h

theorem kemBad_good [Nonempty K] {pk : PK} {sk : SK}
    (hcoin : ∀ m, ∃ r, P.dec sk (P.enc pk m r) = some m) :
    ∀ x, ∃ y, kemBad P hpk eG eKR pk sk x y = false := by
  intro x
  obtain ⟨r, hr⟩ := hcoin (eG.symm x).1
  exact ⟨eKR (Classical.arbitrary K, r), by simp [kemBad, hr]⟩

/-- The key pair `ks` has, for every message, a coin under which the ciphertext
decrypts back to the message. -/
def CoinGood (ks : PK × SK) : Prop :=
  ∀ m, ∃ r, P.dec ks.2 (P.enc ks.1 m r) = some m

/-- Under a key pair that is not `CoinGood`, every value at the point of the
`G`-table of a message without a correctly decrypting coin is bad, so a bound
`lam` on the bad-value fraction at every point is at least one. -/
theorem one_le_of_not_coinGood [NeZero n] {pk : PK} {sk : SK} (h : ¬ CoinGood P (pk, sk))
    (lam : ℝ≥0∞)
    (hlam : ∀ x, ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam) :
    1 ≤ lam := by
  simp only [CoinGood, not_forall, not_exists] at h
  obtain ⟨m, hm⟩ := h
  have hall : badVals (kemBad P hpk eG eKR pk sk) (eG (m, hpk pk)) = Finset.univ :=
    Finset.filter_true_of_mem fun y _ => by simp [kemBad, hm]
  have h1 := hlam (eG (m, hpk pk))
  rwa [hall, Finset.card_univ, Fintype.card_fin,
    ENNReal.div_self (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)] at h1

/-- A table that is good off the point `t` and good at `t` has a ciphertext map
injective on the public-key slice. -/
theorem sliceInj_of_kemBad (pk : PK) (sk : SK) (t : Fin m₁) (G : Fin m₁ → Fin n)
    (hG : ∀ x, offPoint (kemBad P hpk eG eKR pk sk) t x (G x) = false)
    (ht : kemBad P hpk eG eKR pk sk t (G t) = false) :
    SliceInj (kemSlice hpk eG pk) (kemEncAt P eG pk) eKR.symm G := by
  have hgx : ∀ x, kemBad P hpk eG eKR pk sk x (G x) = false := by
    intro x
    by_cases hx : x = t
    · subst hx; exact ht
    · rw [← offPoint_of_ne (bad := kemBad P hpk eG eKR pk sk) hx]; exact hG x
  have hdec : ∀ x, kemSlice hpk eG pk x →
      P.dec sk (coinCt (kemEncAt P eG pk) eKR.symm G x) = some (eG.symm x).1 :=
    fun x hx => dec_of_kemBad_eq_false P hpk eG eKR hx (hgx x)
  intro x y hx hy hxy
  have h1 : (eG.symm x).1 = (eG.symm y).1 :=
    Option.some_injective _ ((hdec x hx).symm.trans (hxy ▸ hdec y hy))
  exact eG.symm.injective (Prod.ext h1 (hx.trans hy.symm))

open scoped Classical in
/-- On the table resampled off the challenge point `t`, the tables whose
ciphertext map is not injective on the slice carry at most `δ* = |badVals t| / n`
of the weight. -/
theorem sum_tableMass_not_sliceInj_le [NeZero n] [Nonempty K] (pk : PK) (sk : SK) (t : Fin m₁)
    (hcoin : ∀ m, ∃ r, P.dec sk (P.enc pk m r) = some m) :
    ∑ G : Fin m₁ → Fin n, tableMass (offPoint (kemBad P hpk eG eKR pk sk) t) G *
        (if SliceInj (kemSlice hpk eG pk) (kemEncAt P eG pk) eKR.symm G then 0 else 1) ≤
      ((badVals (kemBad P hpk eG eKR pk sk) t).card : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ := by
  set bad := kemBad P hpk eG eKR pk sk
  have hgood : ∀ x, ∃ y, offPoint bad t x y = false :=
    offPoint_good t fun x _ => kemBad_good P hpk eG eKR hcoin x
  have hpt : ∀ G : Fin m₁ → Fin n, tableMass (offPoint bad t) G *
      (if SliceInj (kemSlice hpk eG pk) (kemEncAt P eG pk) eKR.symm G then 0 else 1) ≤
        tableMass (offPoint bad t) G * ∑ u ∈ badVals bad t, (if G t = u then 1 else 0) := by
    intro G
    by_cases hz : tableMass (offPoint bad t) G = 0
    · simp [hz]
    have hG : ∀ x, offPoint bad t x (G x) = false := by
      intro x
      have hx := Finset.prod_ne_zero_iff.mp hz x (Finset.mem_univ x)
      by_contra hb
      simp [goodMass, hb] at hx
    rw [Finset.sum_ite_eq]
    by_cases ht : bad t (G t) = true
    · have hm : G t ∈ badVals bad t := by simp [badVals, ht]
      rw [if_pos hm]
      gcongr
      split_ifs <;> simp
    · have ht' : bad t (G t) = false := by simpa using ht
      rw [if_pos (sliceInj_of_kemBad P hpk eG eKR pk sk t G hG ht')]
      simp
  refine (Finset.sum_le_sum fun G _ => hpt G).trans (le_of_eq ?_)
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hval : ∀ u, goodMass (offPoint bad t) t u = (n : ℝ≥0∞)⁻¹ := by
    intro u
    simp [goodMass, goodVals]
  simp only [sum_tableMass_eval hgood t, hval, Finset.sum_const, nsmul_eq_mul]

end KEMBad

/-! ## The hopped game on the resampled table -/

section Resampled

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

/-- The predicate `kemBad` at the key pair of the rest `r`, with the challenge
point `(m*, hpk pk)` exempted. -/
def restBad (r : KEMRest PK SK Z M K m₂ n) : Fin m₁ → Fin n → Bool :=
  offPoint (kemBad P hpk eG eKR r.1.1 r.1.2) (eG (r.2.2.1, hpk r.1.1))

/-- The decryption-failure weight `δ*` of the challenge message of the rest `r`:
the fraction of the values at `(m*, hpk pk)` whose coin part fails to decrypt. -/
def restDelta (r : KEMRest PK SK Z M K m₂ n) : ℝ≥0∞ :=
  ((badVals (kemBad P hpk eG eKR r.1.1 r.1.2) (eG (r.2.2.1, hpk r.1.1))).card : ℝ≥0∞) *
    (n : ℝ≥0∞)⁻¹

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [Nonempty R] [NeZero c] in
/-- On the table resampled off the challenge point, the simulated game and the
hopped game at a fixed rest differ by at most `δ*`. -/
theorem absDiff_winSimJ_winHJ_resampled (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (r : KEMRest PK SK Z M K m₂ n)
    (hcoin : ∀ m, ∃ ρ, P.dec r.1.2 (P.enc r.1.1 m ρ) = some m) :
    absDiff (resampleAvg (restBad P hpk eG eKR r) fun G =>
          winSimJ P hpk eG eJ eKR eC eKa A b (kemJoin r G))
        (resampleAvg (restBad P hpk eG eKR r) fun G =>
          winHJ P hpk eG eJ eKR eC eKa A b (kemJoin r G)) ≤
      restDelta P hpk eG eKR r := by
  have hgood : ∀ x, ∃ y, restBad P hpk eG eKR r x y = false :=
    offPoint_good _ fun x _ => kemBad_good P hpk eG eKR hcoin x
  rw [resampleAvg_eq_sum_tableMass hgood, resampleAvg_eq_sum_tableMass hgood, absDiff_comm]
  have hco : CoinOnly eKR.symm (restBad P hpk eG eKR r) :=
    (kemBad_coinOnly P hpk eG eKR r.1.1 r.1.2).offPoint _
  have hHJ : ∀ G, winHJ P hpk eG eJ eKR eC eKa A b (kemJoin r G) =
      ∑ Hq : C → K, (Fintype.card (C → K) : ℝ≥0∞)⁻¹ *
        winSimJ P hpk eG eJ eKR eC eKa A b
          (kemJoin r (keyHop (kemSlice hpk eG r.1.1) (kemEncAt P eG r.1.1) eKR.symm Hq G)) :=
    fun G => rfl
  simp only [hHJ]
  refine (absDiff_keyHop_le (kemSlice hpk eG r.1.1) (kemEncAt P eG r.1.1) eKR.symm
    (tableMass (restBad P hpk eG eKR r)) (fun Hq g => tableMass_keyHop _ _ _ hco Hq g)
    (fun G => winSimJ P hpk eG eJ eKR eC eKa A b (kemJoin r G))
    (fun G => winSimJ_le_one P hpk eG eJ eKR eC eKa A b _)).trans ?_
  exact sum_tableMass_not_sliceInj_le P hpk eG eKR r.1.1 r.1.2 _ hcoin

omit [Fintype PK] [Fintype SK] [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [Nonempty R] [NeZero c] in
/-- The triangle through the resampled table at a fixed rest: the distance
between the simulated and the hopped game over a uniform `G`-table is at most the
distance between the uniform and the resampled table in each game, plus `δ*`. -/
theorem absDiff_winSimJ_winHJ_triangle (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (r : KEMRest PK SK Z M K m₂ n)
    (hcoin : ∀ m, ∃ ρ, P.dec r.1.2 (P.enc r.1.1 m ρ) = some m) :
    absDiff (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
          winSimJ P hpk eG eJ eKR eC eKa A b (kemJoin r G))
        (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
          winHJ P hpk eG eJ eKR eC eKa A b (kemJoin r G)) ≤
      absDiff (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
          winSimJ P hpk eG eJ eKR eC eKa A b (kemJoin r G))
        (resampleAvg (restBad P hpk eG eKR r) fun G =>
          winSimJ P hpk eG eJ eKR eC eKa A b (kemJoin r G)) +
      absDiff (resampleAvg (restBad P hpk eG eKR r) fun G =>
          winHJ P hpk eG eJ eKR eC eKa A b (kemJoin r G))
        (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
          winHJ P hpk eG eJ eKR eC eKa A b (kemJoin r G)) +
      restDelta P hpk eG eKR r := by
  refine (absDiff_triangle _ (resampleAvg (restBad P hpk eG eKR r) fun G =>
    winSimJ P hpk eG eJ eKR eC eKa A b (kemJoin r G)) _).trans ?_
  refine (add_le_add le_rfl (absDiff_triangle _ (resampleAvg (restBad P hpk eG eKR r) fun G =>
    winHJ P hpk eG eJ eKR eC eKa A b (kemJoin r G)) _)).trans ?_
  have hmid := absDiff_winSimJ_winHJ_resampled P hpk eG eJ eKR eC eKa A b r hcoin
  calc _ ≤ _ + (restDelta P hpk eG eKR r + _) := add_le_add le_rfl (add_le_add hmid le_rfl)
    _ = _ := by ring

omit [Nonempty M] [Nonempty Z] [Nonempty R] [NeZero c] in
/-- The triangle averaged over the rest of the input: `prWinKEMSimJ` and
`prWinKEMHJ` differ by at most the `kemRestWeight`-average of the two outer
distances of `absDiff_winSimJ_winHJ_triangle` plus `δ*`. The coin hypothesis is
required at the key pairs in the support of `keygen`. -/
theorem absDiff_prWinKEMSimJ_prWinKEMHJ_le (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (hcoin : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ m, ∃ ρ, P.dec sk (P.enc pk m ρ) = some m) :
    absDiff (prWinKEMSimJ P hpk eG eJ eKR eC eKa A b) (prWinKEMHJ P hpk eG eJ eKR eC eKa A b) ≤
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
        (absDiff (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
              winSimJ P hpk eG eJ eKR eC eKa A b (kemJoin r G))
            (resampleAvg (restBad P hpk eG eKR r) fun G =>
              winSimJ P hpk eG eJ eKR eC eKa A b (kemJoin r G)) +
          absDiff (resampleAvg (restBad P hpk eG eKR r) fun G =>
              winHJ P hpk eG eJ eKR eC eKa A b (kemJoin r G))
            (∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ *
              winHJ P hpk eG eJ eKR eC eKa A b (kemJoin r G)) +
          restDelta P hpk eG eKR r) := by
  unfold prWinKEMSimJ
  rw [prWinKEMHJ_eq_sum_winHJ, sum_kemSample_kemJoin, sum_kemSample_kemJoin]
  refine (absDiff_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  refine (absDiff_mul_left_le _ _ _).trans ?_
  by_cases hk : P.keygen r.1 = 0
  · simp [kemRestWeight, hk]
  · gcongr
    exact absDiff_winSimJ_winHJ_triangle P hpk eG eJ eKR eC eKa A b r (hcoin r.1.1 r.1.2 hk)

end Resampled

end CatCrypt.Quantum.QROM
