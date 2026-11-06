/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.TVHops

/-!
# Bounded rejection sampling

`rejectLoop k μ f` draws `k` independent samples from `μ` and returns the first success of the
partial function `f`, or `none` when all `k` attempts fail. When an attempt succeeds with
probability at least `s`, with its value distributed as `s • ν`, and fails with probability at
least `r = 1 - s`, the loop is within `r^k` of `ν` in total variation distance. Replacing the
sampler `μ` by `μ'` moves the loop by at most `k * tvDist μ μ'`.

## Main definitions

* `firstSome` — the first success of a partial function along a finite sequence
* `rejectLoop` — the law of the first success among `k` independent attempts

## Main results

* `tvDist_le_one_sub_of_mul_le` — if `c • Q ≤ P` pointwise, then `tvDist P Q ≤ 1 - c`
* `firstSome_eq_some` — a first success is the success of an element of the sequence
* `firstSome_eq_none_iff` — the first success is `none` exactly when every value fails
* `firstSome_eq_map_firstSome` — the first success of a function that factors through `h`
* `rejectLoop_succ` — one attempt, then the loop of `k` attempts on failure
* `rejectLoop_bind_pure` — the loop over the image of a sampler
* `rejectLoop_apply_ge` — the loop puts mass at least `(1 - r^k) * ν y` on each success `y`
* `tvDist_rejectLoop_le` — `tvDist (rejectLoop k μ f) (ν.map some) ≤ r^k`
* `tvDist_rejectLoop_rejectLoop_le` — `tvDist (rejectLoop k μ f) (rejectLoop k μ' f) ≤
  k * tvDist μ μ'`
* `tvDist_uniform_bind_injective_le` — the image of a uniform distribution under an injection
  into `α` is within `(|α| - |β|) / |α|` of uniform on `α`
* `SDistr.apply_le_add_tvDist`, `apply_some_none_le_tvDist` — the mass of an outcome under two
  laws differs by at most their distance; a loop fails with probability at most its distance to
  a law of successes
* `tvDist_bind_le_of_eq_off`, `advantageA_sampleFrom_bind_le_of_eq_off` — continuations that
  agree off a set `bad` give distributions and games at distance at most the mass of `bad`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob CatCrypt.NonUniform
open scoped ENNReal

/-- The first success of `f` along a finite sequence, `none` when every value fails. -/
def firstSome {X Y : Type*} (f : X → Option Y) : {n : ℕ} → (Fin n → X) → Option Y
  | 0, _ => none
  | _ + 1, xs => (f (xs 0)).or (firstSome f (Fin.tail xs))

@[simp] theorem firstSome_zero {X Y : Type*} (f : X → Option Y) (xs : Fin 0 → X) :
    firstSome f xs = none := rfl

@[simp] theorem firstSome_cons {X Y : Type*} (f : X → Option Y) {n : ℕ} (x : X)
    (xs : Fin n → X) :
    firstSome f (Fin.cons x xs : Fin (n + 1) → X) = (f x).or (firstSome f xs) := by
  simp only [firstSome, Fin.cons_zero, Fin.tail_cons]

/-- A first success is a success of some element of the sequence. -/
theorem firstSome_eq_some {X Y : Type*} (f : X → Option Y) :
    ∀ {n : ℕ} (xs : Fin n → X) {y : Y}, firstSome f xs = some y → ∃ i, f (xs i) = some y
  | 0, _, _, h => by simp at h
  | _ + 1, xs, y, h => by
    simp only [firstSome] at h
    cases hx : f (xs 0) with
    | some z =>
      rw [hx, Option.some_or] at h
      exact ⟨0, hx.trans h⟩
    | none =>
      rw [hx, Option.none_or] at h
      obtain ⟨i, hi⟩ := firstSome_eq_some f (Fin.tail xs) h
      exact ⟨i.succ, hi⟩

/-- The first success is `none` exactly when every value fails. -/
theorem firstSome_eq_none_iff {X Y : Type*} (f : X → Option Y) :
    ∀ {n : ℕ} (xs : Fin n → X), firstSome f xs = none ↔ ∀ i, f (xs i) = none
  | 0, _ => by simp
  | _ + 1, xs => by
    simp only [firstSome, Option.or_eq_none_iff, firstSome_eq_none_iff f (Fin.tail xs),
      Fin.forall_fin_succ, Fin.tail]

/-- The first success of a function with the argument attached, forgetting the argument, is
the first success of the function. -/
theorem firstSome_map_snd {X Y : Type*} (g : X → Option Y) {n : ℕ} (xs : Fin n → X) :
    (firstSome (fun x => (g x).map fun r => (x, r)) xs).map Prod.snd = firstSome g xs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [firstSome]
    rw [← ih (Fin.tail xs)]
    cases g (xs 0) <;> simp

/-- A function that factors as `(f ∘ h).map m` has as first success the image under `m` of the
first success of `f` along the image of the sequence under `h`. -/
theorem firstSome_eq_map_firstSome {X Z Y W : Type*} {g : X → Option W} {f : Z → Option Y}
    {h : X → Z} {m : Y → W} (hg : ∀ x, g x = (f (h x)).map m) {n : ℕ} (xs : Fin n → X) :
    firstSome g xs = (firstSome f fun i => h (xs i)).map m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [firstSome]
    rw [ih (Fin.tail xs), hg]
    cases f (h (xs 0)) <;> rfl

/-- The law of the first success of `f` among `k` independent draws from `μ`. -/
noncomputable def rejectLoop {X Y : Type*} (k : ℕ) (μ : SDistr X) (f : X → Option Y) :
    SDistr (Option Y) :=
  (replicateFin k μ).bind fun xs => SDistr.pure (firstSome f xs)

/-- A sub-distribution of mass one gives no mass to failure. -/
theorem SDistr.apply_none_of_mass_one {α : Type*} {d : SDistr α} (hd : SDistr.mass d = 1) :
    d none = 0 :=
  Classical.byContradiction fun hne =>
    absurd hd (ne_of_lt (ENNReal.sub_lt_self (by norm_num) (by norm_num) hne))

/-- `absDiff a b ≤ ε` from the two one-sided bounds. -/
private theorem absDiff_le_of_le_add' {a b ε : ℝ≥0∞} (h₁ : a ≤ b + ε) (h₂ : b ≤ a + ε) :
    absDiff a b ≤ ε :=
  max_le (tsub_le_iff_right.2 (by rwa [add_comm])) (tsub_le_iff_right.2 (by rwa [add_comm]))

/-- An expectation of a test function bounded by `1` is at most `1`. -/
private theorem tsum_mul_le_one' {γ : Type*} (p : PMF γ) (f : γ → ℝ≥0∞) (hf : ∀ x, f x ≤ 1) :
    ∑' y, p y * f y ≤ 1 :=
  calc ∑' y, p y * f y ≤ ∑' y, p y := ENNReal.tsum_le_tsum fun y =>
        mul_le_of_le_one_right' (hf y)
    _ = 1 := p.tsum_coe

/-- If `c • Q ≤ P` pointwise, the expectations of a test function satisfy the same bound. -/
private theorem mul_tsum_le {α : Type*} (P Q : SDistr α) (c : ℝ≥0∞) (h : ∀ x, c * Q x ≤ P x)
    (f : Option α → ℝ≥0∞) : c * ∑' x, Q x * f x ≤ ∑' x, P x * f x := by
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun x => by rw [← mul_assoc]; exact mul_le_mul_left (h x) _

/-- **A pointwise lower bound gives a distance bound**: if `c * Q x ≤ P x` for every outcome,
then `tvDist P Q ≤ 1 - c`. -/
theorem tvDist_le_one_sub_of_mul_le {α : Type*} (P Q : SDistr α) (c : ℝ≥0∞) (hc : c ≤ 1)
    (h : ∀ x, c * Q x ≤ P x) : tvDist P Q ≤ 1 - c := by
  refine iSup₂_le fun f hf => ?_
  have hf' : ∀ x, 1 - f x ≤ 1 := fun _ => tsub_le_self
  have hsplit : ∀ R : SDistr α, ∑' x, R x * f x + ∑' x, R x * (1 - f x) = 1 := fun R => by
    rw [← ENNReal.tsum_add]
    conv_rhs => rw [← R.tsum_coe]
    exact tsum_congr fun x => by rw [← mul_add, add_tsub_cancel_of_le (hf x), mul_one]
  set a := ∑' x, P x * f x
  set b := ∑' x, Q x * f x
  set a' := ∑' x, P x * (1 - f x)
  set b' := ∑' x, Q x * (1 - f x)
  have hb : b ≤ 1 := tsum_mul_le_one' Q f hf
  have hcb : c * b ≤ a := mul_tsum_le P Q c h f
  have hcb' : c * b' ≤ a' := mul_tsum_le P Q c h _
  have hc1 : c + (1 - c) = 1 := add_tsub_cancel_of_le hc
  refine absDiff_le_of_le_add' ?_ ?_
  · have ha' : a' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (tsum_mul_le_one' P _ hf')
    refine (ENNReal.add_le_add_iff_right ha').1 ?_
    calc a + a' = 1 := hsplit P
      _ = c * (b + b') + (1 - c) := by rw [hsplit Q, mul_one, hc1]
      _ = c * b + (1 - c) + c * b' := by ring
      _ ≤ b + (1 - c) + a' := by
          gcongr
          exact mul_le_of_le_one_left' hc
  · calc b = (c + (1 - c)) * b := by rw [hc1, one_mul]
      _ = c * b + (1 - c) * b := add_mul _ _ _
      _ ≤ a + (1 - c) * 1 := by gcongr
      _ = a + (1 - c) := by rw [mul_one]

/-- The loop of `k + 1` attempts: one attempt, and the loop of `k` attempts on its failure. -/
theorem rejectLoop_succ {X Y : Type*} (k : ℕ) (μ : SDistr X) (f : X → Option Y) :
    rejectLoop (k + 1) μ f = μ.bind fun x =>
      (rejectLoop k μ f).bind fun o => SDistr.pure ((f x).or o) := by
  have hs : replicateFin (k + 1) μ =
      μ.bind fun a => (replicateFin k μ).bind fun g => SDistr.pure (Fin.cons a g) := rfl
  simp only [rejectLoop, hs, SDistr.bind_assoc, SDistr.pure_bind, firstSome_cons]

/-- The loop over the image of a sampler under `g` is the first success of `f ∘ g` among `k`
independent draws. -/
theorem rejectLoop_bind_pure {X Z Y : Type*} (k : ℕ) (μ : SDistr X) (g : X → Z)
    (f : Z → Option Y) :
    rejectLoop k (μ.bind fun x => SDistr.pure (g x)) f =
      (replicateFin k μ).bind fun xs => SDistr.pure (firstSome f fun i => g (xs i)) := by
  induction k with
  | zero =>
    have h0 : replicateFin 0 μ = SDistr.pure fun i => i.elim0 := rfl
    have h0' : replicateFin 0 (μ.bind fun x => SDistr.pure (g x)) =
      SDistr.pure fun i => i.elim0 := rfl
    rw [rejectLoop, h0, h0', SDistr.pure_bind, SDistr.pure_bind]
    rfl
  | succ k ih =>
    have hs : replicateFin (k + 1) μ =
        μ.bind fun a => (replicateFin k μ).bind fun t => SDistr.pure (Fin.cons a t) := rfl
    rw [rejectLoop_succ, ih, hs]
    simp only [SDistr.bind_assoc, SDistr.pure_bind]
    rfl

/-- The loop does not fail as a sub-distribution. -/
theorem mass_rejectLoop {X Y : Type*} (k : ℕ) {μ : SDistr X} (hμ : SDistr.mass μ = 1)
    (f : X → Option Y) : SDistr.mass (rejectLoop k μ f) = 1 :=
  mass_bind_of_mass_one (mass_replicateFin hμ) fun _ => SDistr.mass_pure _

/-- `1 - r^(k+1) ≤ s + r * (1 - r^k)` when `s + r = 1`. -/
private theorem one_sub_pow_succ_le {s r : ℝ≥0∞} (hsr : s + r = 1) (k : ℕ) :
    1 - r ^ (k + 1) ≤ s + r * (1 - r ^ k) := by
  have hr : r ≤ 1 := hsr ▸ le_add_self
  have hr' : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hr
  have hrk : r ^ (k + 1) ≤ r := by
    rw [pow_succ]; exact mul_le_of_le_one_left' (pow_le_one₀ zero_le hr)
  rw [ENNReal.mul_sub (fun _ _ => hr'), mul_one, ← pow_succ']
  conv_lhs => rw [← hsr]
  exact add_tsub_le_assoc

/-- **The loop puts mass at least `(1 - r^k) * ν y` on each success `y`**, when one attempt
succeeds with value `y` with probability at least `s * ν y` and fails with probability at
least `r`, `s + r = 1`. -/
theorem rejectLoop_apply_ge {X Y : Type*} (μ : SDistr X) (f : X → Option Y)
    (hμ : SDistr.mass μ = 1) (ν : SDistr Y) (s r : ℝ≥0∞) (hsr : s + r = 1)
    (hs : ∀ y, s * ν (some y) ≤ (μ.bind fun x => SDistr.pure (f x)) (some (some y)))
    (hr : r ≤ (μ.bind fun x => SDistr.pure (f x)) (some none)) (k : ℕ) (y : Y) :
    (1 - r ^ k) * ν (some y) ≤ rejectLoop k μ f (some (some y)) := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    set ρ := μ.bind fun x => SDistr.pure (f x)
    set L := rejectLoop k μ f
    have hL : SDistr.mass L = 1 := mass_rejectLoop k hμ f
    let K : Option Y → SDistr (Option Y) := fun o' => L.bind fun o => SDistr.pure (o'.or o)
    have hK : rejectLoop (k + 1) μ f = ρ.bind K := by
      rw [rejectLoop_succ, SDistr.bind_assoc]
      simp only [SDistr.pure_bind, K, L]
    have hKs : K (some y) = SDistr.pure (some y) := by
      simp only [K, Option.some_or]
      exact SDistr.bind_const_mass_one hL _
    have hKn : K none = L := by
      simp only [K, Option.none_or]
      exact SDistr.bind_pure L
    have hsum : ρ (some (some y)) * 1 + ρ (some none) * L (some (some y)) ≤
        (ρ.bind K) (some (some y)) := by
      rw [SDistr.bind, PMF.bind_apply]
      have hne : (some (some y) : Option (Option Y)) ≠ some none := by simp
      refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum {some (some y), some none})
      rw [Finset.sum_pair hne]
      simp only [hKs, hKn, SDistr.pure_apply_some, ite_true]
    rw [hK]
    refine le_trans ?_ hsum
    calc (1 - r ^ (k + 1)) * ν (some y)
        ≤ (s + r * (1 - r ^ k)) * ν (some y) := by gcongr; exact one_sub_pow_succ_le hsr k
      _ = s * ν (some y) * 1 + r * ((1 - r ^ k) * ν (some y)) := by ring
      _ ≤ ρ (some (some y)) * 1 + ρ (some none) * L (some (some y)) :=
          add_le_add (mul_le_mul' (hs y) le_rfl) (mul_le_mul' hr ih)

/-- The image of `ν` under `some` puts on `some (some y)` the mass of `y` and nothing on
`some none`. -/
private theorem bind_pure_some_apply {Y : Type*} (ν : SDistr Y) (y : Y) :
    (ν.bind fun y => SDistr.pure (some y)) (some (some y)) = ν (some y) := by
  classical
  rw [SDistr.bind, PMF.bind_apply, tsum_eq_single (some y)]
  · simp [SDistr.pure_apply_some]
  · intro o ho
    cases o with
    | none => simp [SDistr.fail_apply_some]
    | some y' =>
      have : y' ≠ y := fun h => ho (by rw [h])
      simp [SDistr.pure_apply_some, this]

private theorem bind_pure_some_apply_none {Y : Type*} (ν : SDistr Y) :
    (ν.bind fun y => SDistr.pure (some y)) (some none) = 0 := by
  classical
  rw [SDistr.bind, PMF.bind_apply]
  refine ENNReal.tsum_eq_zero.2 fun o => ?_
  cases o with
  | none => simp [SDistr.fail_apply_some]
  | some y' => simp [SDistr.pure_apply_some]

/-- The mass of an outcome is at most its mass under `Q` plus `tvDist P Q`. -/
theorem SDistr.apply_le_add_tvDist {α : Type*} (P Q : SDistr α) (x : Option α) :
    P x ≤ Q x + tvDist P Q := by
  classical
  have hf : ∀ y : Option α, (if y = x then 1 else 0 : ℝ≥0∞) ≤ 1 := fun y => by
    split_ifs <;> simp
  have h := le_iSup₂_of_le (f := fun (f : Option α → ℝ≥0∞) (_ : ∀ y, f y ≤ 1) =>
    absDiff (∑' y, P y * f y) (∑' y, Q y * f y)) (fun y => if y = x then 1 else 0) hf le_rfl
  simp only [mul_ite, mul_one, mul_zero, tsum_ite_eq] at h
  exact tsub_le_iff_left.1 ((le_max_left _ _).trans h)

/-- A law on `Option Y` puts on `none` at most its distance to the image of a law under
`some`. -/
theorem apply_some_none_le_tvDist {Y : Type*} (P : SDistr (Option Y)) (ν : SDistr Y) :
    P (some none) ≤ tvDist P (ν.bind fun y => SDistr.pure (some y)) := by
  have h := SDistr.apply_le_add_tvDist P (ν.bind fun y => SDistr.pure (some y)) (some none)
  rwa [bind_pure_some_apply_none, zero_add] at h

/-- **The bounded rejection loop is within `r^k` of the target law**: when one attempt
succeeds with value `y` with probability at least `s * ν y` and fails with probability at least
`r`, `s + r = 1`, the first success among `k` attempts is at total variation distance at most
`r^k` from `ν`. -/
theorem tvDist_rejectLoop_le {X Y : Type*} (μ : SDistr X) (f : X → Option Y)
    (hμ : SDistr.mass μ = 1) (ν : SDistr Y) (hν : SDistr.mass ν = 1) (s r : ℝ≥0∞)
    (hsr : s + r = 1)
    (hs : ∀ y, s * ν (some y) ≤ (μ.bind fun x => SDistr.pure (f x)) (some (some y)))
    (hr : r ≤ (μ.bind fun x => SDistr.pure (f x)) (some none)) (k : ℕ) :
    tvDist (rejectLoop k μ f) (ν.bind fun y => SDistr.pure (some y)) ≤ r ^ k := by
  have hr1 : r ≤ 1 := hsr ▸ le_add_self
  have hrk : r ^ k ≤ 1 := pow_le_one₀ zero_le hr1
  have hQ : SDistr.mass (ν.bind fun y => SDistr.pure (some y)) = 1 :=
    mass_bind_of_mass_one hν fun _ => SDistr.mass_pure _
  have h := tvDist_le_one_sub_of_mul_le (rejectLoop k μ f) (ν.bind fun y => SDistr.pure (some y))
    (1 - r ^ k) tsub_le_self ?_
  · rwa [ENNReal.sub_sub_cancel ENNReal.one_ne_top hrk] at h
  rintro (_ | _ | y)
  · rw [SDistr.apply_none_of_mass_one hQ, mul_zero]; exact zero_le
  · rw [bind_pure_some_apply_none, mul_zero]; exact zero_le
  · rw [bind_pure_some_apply]
    exact rejectLoop_apply_ge μ f hμ ν s r hsr hs hr k y

/-- **Changing the sampler of the loop**: `k` attempts at `μ` and at `μ'` are at total
variation distance at most `k * tvDist μ μ'`. -/
theorem tvDist_rejectLoop_rejectLoop_le {X Y : Type*} (k : ℕ) (μ μ' : SDistr X)
    (f : X → Option Y) :
    tvDist (rejectLoop k μ f) (rejectLoop k μ' f) ≤ k * tvDist μ μ' :=
  (tvDist_bind_le _ _ _).trans (tvDist_replicateFin_le k μ μ')

/-- **The uniform distribution on a subset**: the image of the uniform distribution on `β`
under an injection `e : β → α` is at total variation distance at most `(|α| - |β|) / |α|`
from the uniform distribution on `α`. -/
theorem tvDist_uniform_bind_injective_le {α β : Type} [Fintype α] [Fintype β] [Nonempty α]
    [Nonempty β] (e : β → α) (he : Function.Injective e) :
    tvDist ((SDistr.uniform β).bind fun b => SDistr.pure (e b)) (SDistr.uniform α) ≤
      ((Fintype.card α - Fintype.card β : ℕ) : ℝ≥0∞) / Fintype.card α := by
  classical
  set S := Finset.univ.image e
  have hle : Fintype.card β ≤ Fintype.card α := Fintype.card_le_of_injective e he
  have hS : S.card = Fintype.card β := by
    rw [Finset.card_image_of_injective _ he, Finset.card_univ]
  refine (tvDist_le_of_le_off _ _ {x | ∀ y, x = some y → y ∉ S} ?_).trans ?_
  · intro x hx
    simp only [Set.mem_ofPred_eq, not_forall, not_not] at hx
    obtain ⟨y, hxy, hy⟩ := hx
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hy
    rw [hxy, ← hq, SDistr.uniform_apply_some, SDistr.uniform_bind_pure_apply]
    have h1 : (Finset.univ.filter fun q' => e q' = e q).card = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨q, by ext q'; simp [he.eq_iff]⟩
    rw [h1, Nat.cast_one, one_mul]
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hle)
  · rw [SDistr.tsum_option_eq_add, Set.indicator_of_mem (by simp), SDistr.uniform_apply_none,
      zero_add, tsum_fintype]
    have h : ∀ y : α, Set.indicator {x | ∀ y, x = some y → y ∉ S}
        (SDistr.uniform α) (some y) =
        if y ∈ S then 0 else (Fintype.card α : ℝ≥0∞)⁻¹ := fun y => by
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_notMem (by simpa using hy), ite_eq_left_iff.mpr (fun h => absurd hy h)]
      · rw [Set.indicator_of_mem (by simpa using hy), ite_eq_right_iff.mpr (fun h => absurd h hy),
          SDistr.uniform_apply_some]
    simp only [h]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
      div_eq_mul_inv]
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff,
      Finset.inter_univ, Finset.card_univ, hS]

/-! ## Identical until a bad event -/

/-- The mass of `y` under the image of `d` by `g` is the mass of the preimage of `y`. -/
theorem SDistr.bind_pure_apply_eq_tsum_indicator {α β : Type*} (d : SDistr α) (g : α → β)
    (y : β) :
    (d.bind fun x => SDistr.pure (g x)) (some y) =
      ∑' x, {x | g x = y}.indicator (fun x => d (some x)) x := by
  classical
  rw [SDistr.bind, PMF.bind_apply, SDistr.tsum_option_eq_add]
  simp only [SDistr.fail_apply_some, mul_zero, zero_add, SDistr.pure_apply_some, mul_ite,
    mul_one, Set.indicator, Set.mem_ofPred_eq]

/-- **Identical until bad**: continuations that agree off a set `bad` give distributions at
total variation distance at most the mass of `bad`. -/
theorem tvDist_bind_le_of_eq_off {α β : Type*} (d : SDistr α) (K₁ K₂ : α → SDistr β)
    (bad : Set α) (h : ∀ a ∉ bad, K₁ a = K₂ a) :
    tvDist (d.bind K₁) (d.bind K₂) ≤ ∑' a, bad.indicator (fun a => d (some a)) a := by
  refine iSup₂_le fun f hf => ?_
  rw [SDistr.tsum_bind_mul, SDistr.tsum_bind_mul]
  have key : ∀ K K' : α → SDistr β, (∀ a ∉ bad, K a = K' a) →
      d none * f none + ∑' a, d (some a) * ∑' y, K a y * f y ≤
        d none * f none + ∑' a, d (some a) * ∑' y, K' a y * f y +
          ∑' a, bad.indicator (fun a => d (some a)) a := by
    intro K K' hK
    rw [add_assoc, ← ENNReal.tsum_add]
    refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun a => ?_)
    by_cases ha : a ∈ bad
    · rw [Set.indicator_of_mem ha]
      exact le_add_left (mul_le_of_le_one_right' (tsum_mul_le_one' (K a) f hf))
    · rw [hK a ha, Set.indicator_of_notMem ha, add_zero]
  exact absDiff_le_of_le_add' (key K₁ K₂ h) (key K₂ K₁ fun a ha => (h a ha).symm)

/-- **Identical until bad for games**: two games that draw from `μ` and continue identically
off a set `bad` have advantage at most the mass of `bad`. -/
theorem advantageA_sampleFrom_bind_le_of_eq_off {X V : Type} (μ : SDistr X)
    (k₁ k₂ : X → SPComp V) (bad : Set X) (h : ∀ x ∉ bad, k₁ x = k₂ x)
    (A : V → SPComp Bool) :
    AdvantageA ((sampleFrom μ).bind k₁) ((sampleFrom μ).bind k₂) A ≤
      ∑' x, bad.indicator (fun x => μ (some x)) x := by
  have hA : AdvantageA ((sampleFrom μ).bind k₁) ((sampleFrom μ).bind k₂) A =
      absDiff (prTrue (((sampleFrom μ).bind k₁).bind A) Heap.empty)
        (prTrue (((sampleFrom μ).bind k₂).bind A) Heap.empty) := rfl
  rw [hA]
  refine (absDiff_prTrue_bind_le_tvDist_gen _ _ A Heap.empty).trans ?_
  rw [sampleFrom_bind_apply, sampleFrom_bind_apply]
  exact tvDist_bind_le_of_eq_off μ _ _ bad fun x hx => by rw [h x hx]

end CatCrypt.Crypto
