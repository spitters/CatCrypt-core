/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLWE
public import CatCryptCore.Crypto.MLKEM.Sampler
public import CatCryptCore.Crypto.TV
public import Mathlib.Data.FinEnum

/-!
# The distribution of the XOF-expanded ML-KEM matrix

FIPS 203 K-PKE.KeyGen (Algorithm 13) expands the public matrix as
`Â[i, j] := SampleNTT(XOF(ρ, j, i))`, where `SampleNTT` (Algorithm 7,
`Sampler.sampleNTT`) rejection-samples 12-bit candidates `< 3329` from the XOF
byte stream. This file bounds the statistical distance between that matrix and
a uniform one when the XOF is a random oracle, and transfers the bound to the
module-LWE game.

## Main definitions

* `Stream m` — an XOF output of `m` three-byte groups (`3 m` bytes);
  FIPS 203 squeezes SHAKE-128 in 168-byte blocks, so `m = 56 · blocks`.
* `Fills`, `sampleOf` — the adequacy predicate and the output of Algorithm 7 on a
  stream.
* `fillProb`, `nonFillProb` — the probability that a uniform stream does or does
  not yield 256 accepted values.
* `prefixCount` — the number of streams whose accepted values start with a given
  list of a given length.
* `xofMatrix`, `xofMatrixDist` — the matrix of Algorithm 13 from a family of XOF
  outputs, and its distribution for a uniform family.
* `gameWith`, `advantageWith` — the module-LWE game of `MLWE.Game` with the matrix
  drawn from a given distribution; `gameSeed`, `advantageSeed` — the same game
  with the seed `ρ` given to the distinguisher.

## Main results

* `card_fills_sampleOf_eq`, `prob_fills_sampleOf_eq` — conditioned on filling, the
  output of Algorithm 7 on a uniform stream is uniform.
* `nonFillProb_eq` — `nonFillProb m = 1 - fillProb m`.
* `nonFillProb_le` — for `255 ≤ 2 m`,
  `nonFillProb m ≤ C(2 m, 255) · (767 / 4096) ^ (2 m - 255)`, a union bound over
  the positions of the rejected candidates.
* `sdist_xofMatrix_uniform_le` — the total-variation distance between the XOF
  matrix and a uniform `k × k` matrix is at most `k² · nonFillProb m`;
  `sdist_xofMatrix_uniform_le_choose` combines it with `nonFillProb_le`.
* `mlwe_advantage_xofMatrix_le` — for every distinguisher, the module-LWE
  advantage with the XOF matrix is within `2 k² · nonFillProb m` of
  `MLWE.advantage`; `mlwe_advantage_xofMatrix_seed_le` is the same bound for a
  distinguisher that also receives `ρ`.

## Scope

The XOF is modelled as a random oracle: the outputs on the `k²` distinct inputs
`(ρ, j, i)` are independent uniform streams, independent of `ρ`. The stream
length `m` (in three-byte groups) is a parameter, and the result holds for every
`m`; the non-fill probability is the quantity `nonFillProb m`, defined as a
probability over a uniform stream. The adversary's own XOF queries are not part
of this hop: the matrix is public, so an adversary can recompute it, and this hop
changes only the distribution of the challenger's matrix.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Prob
open scoped ENNReal

namespace CatCrypt.Crypto.MLKEM.XOFMatrix

/-! ## Distance from a pointwise minorant -/

/-- If `(1 - β) · Q ≤ P` pointwise, then every test function bounded by `1` has
`E_Q[f] ≤ E_P[f] + β` and `E_P[f] ≤ E_Q[f] + β`. -/
theorem tsum_le_add_of_minorant {X : Type*} (P Q : PMF X) (β : ℝ≥0∞)
    (hPQ : ∀ x, (1 - β) * Q x ≤ P x) (f : X → ℝ≥0∞) (hf : ∀ x, f x ≤ 1) :
    (∑' x, P x * f x ≤ (∑' x, Q x * f x) + β) ∧
      (∑' x, Q x * f x ≤ (∑' x, P x * f x) + β) := by
  have hle : ∀ R : PMF X, ∑' x, R x * f x ≤ 1 := fun R =>
    calc ∑' x, R x * f x ≤ ∑' x, R x :=
          ENNReal.tsum_le_tsum fun x => mul_le_of_le_one_right' (hf x)
      _ = 1 := R.tsum_coe
  by_cases hβ : β ≤ 1
  swap
  · have h1 : 1 ≤ β := le_of_lt (not_le.mp hβ)
    exact ⟨(hle P).trans (h1.trans le_add_self), (hle Q).trans (h1.trans le_add_self)⟩
  set c : ℝ≥0∞ := 1 - β with hc
  have hc1 : c ≤ 1 := tsub_le_self
  have hcβ : c + β = 1 := tsub_add_cancel_of_le hβ
  set r : X → ℝ≥0∞ := fun x => P x - c * Q x with hr
  have hPr : ∀ x, P x = r x + c * Q x := fun x => (tsub_add_cancel_of_le (hPQ x)).symm
  have hQf_le : ∑' x, Q x * f x ≤ 1 := by
    calc ∑' x, Q x * f x ≤ ∑' x, Q x :=
          ENNReal.tsum_le_tsum fun x => mul_le_of_le_one_right' (hf x)
      _ = 1 := Q.tsum_coe
  have hsumr : ∑' x, r x = β := by
    have h1 : ∑' x, r x + c = 1 := by
      calc ∑' x, r x + c = ∑' x, r x + c * ∑' x, Q x := by rw [Q.tsum_coe, mul_one]
        _ = ∑' x, (r x + c * Q x) := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        _ = ∑' x, P x := by simp only [← hPr]
        _ = 1 := P.tsum_coe
    have hcne : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc1
    calc ∑' x, r x = 1 - c := by rw [← h1, ENNReal.add_sub_cancel_right hcne]
      _ = β := by rw [← hcβ, ENNReal.add_sub_cancel_left hcne]
  have hPf : ∑' x, P x * f x = ∑' x, r x * f x + c * ∑' x, Q x * f x := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun x => ?_
    rw [hPr x, add_mul, mul_assoc]
  have hrf : ∑' x, r x * f x ≤ β := by
    calc ∑' x, r x * f x ≤ ∑' x, r x :=
          ENNReal.tsum_le_tsum fun x => mul_le_of_le_one_right' (hf x)
      _ = β := hsumr
  constructor
  · rw [hPf, add_comm (∑' x, Q x * f x)]
    exact add_le_add hrf (mul_le_of_le_one_left' hc1)
  · have hQ : ∑' x, Q x * f x = c * ∑' x, Q x * f x + β * ∑' x, Q x * f x := by
      rw [← add_mul, hcβ, one_mul]
    calc ∑' x, Q x * f x = c * ∑' x, Q x * f x + β * ∑' x, Q x * f x := hQ
      _ ≤ (∑' x, r x * f x + c * ∑' x, Q x * f x) + β := by
          gcongr
          · exact le_add_self
          · exact mul_le_of_le_one_right' hQf_le
      _ = (∑' x, P x * f x) + β := by rw [hPf]

/-! ## Counting accepted prefixes -/

/-- The prefix count after prepending one candidate: `e` rejecting candidates
keep the whole prefix, and exactly one accepting candidate matches its head. -/
def stepCount (e n : ℕ) (H : ℕ → ℕ) : ℕ → ℕ
  | 0 => n * H 0
  | k + 1 => H k + e * H (k + 1)

/-- One candidate step of the prefix count. `acc` maps a candidate to its
accepted value or to `none`; `e` candidates are rejected and each value is hit
by exactly one candidate. If the number of `ω` with `u` a prefix of `F ω`
depends only on `u.length` through `H`, then the same holds for the stream
`(acc d).toList ++ F ω` with the count `stepCount e (card C) H`. -/
theorem card_prefix_step {C Ω V : Type} [Fintype C] [Fintype Ω] [DecidableEq V]
    (acc : C → Option V) (e : ℕ)
    (he : (Finset.univ.filter fun d => acc d = none).card = e)
    (h1 : ∀ a, (Finset.univ.filter fun d => acc d = some a).card = 1)
    (F : Ω → List V) (H : ℕ → ℕ)
    (hF : ∀ u : List V, (Finset.univ.filter fun ω => u <+: F ω).card = H u.length)
    (u : List V) :
    (Finset.univ.filter fun p : C × Ω => u <+: (acc p.1).toList ++ F p.2).card =
      stepCount e (Fintype.card C) H u.length := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp only [← Finset.card_filter]
  cases u with
  | nil =>
    have h0 := hF []
    simp only [List.nil_prefix, Finset.filter_true, Finset.card_univ, List.length_nil] at h0 ⊢
    simp [stepCount, h0]
  | cons a u' =>
    have hterm : ∀ d : C,
        (Finset.univ.filter fun ω => a :: u' <+: (acc d).toList ++ F ω).card =
          (if acc d = none then H (u'.length + 1) else 0) +
            (if acc d = some a then H u'.length else 0) := by
      intro d
      cases hd : acc d with
      | none =>
        have := hF (a :: u')
        simp only [List.length_cons] at this
        simp only [Option.toList_none, List.nil_append, if_true, reduceCtorEq, if_false,
          add_zero]
        exact this
      | some b =>
        by_cases hb : b = a
        · subst hb
          simp [List.cons_prefix_cons, hF u']
        · have hne : (some b : Option V) ≠ some a := by simpa using hb
          simp [List.cons_prefix_cons, Ne.symm hb, hne]
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
      Finset.sum_const, smul_eq_mul, add_zero, he, h1, List.length_cons, stepCount]
    ring

/-! ## Byte groups and 12-bit candidates -/

open CatCrypt.Crypto.MLKEM.Sampler CatCrypt.Util

/-- A three-byte group of the XOF stream, the unit Algorithm 7 consumes. -/
abbrev Group : Type := UInt8 × UInt8 × UInt8

/-- The first 12-bit candidate of a group, `b0 + 256 * (b1 mod 16)`. -/
def cand1 (g : Group) : Fin 4096 :=
  ⟨g.1.toNat + 256 * (g.2.1.toNat % 16), by have := g.1.toNat_lt; omega⟩

/-- The second 12-bit candidate of a group, `(b1 div 16) + 16 * b2`. -/
def cand2 (g : Group) : Fin 4096 :=
  ⟨g.2.1.toNat / 16 + 16 * g.2.2.toNat, by
    have := g.2.1.toNat_lt; have := g.2.2.toNat_lt; omega⟩

/-- The candidate decoding of a group is a bijection onto pairs of 12-bit
values. -/
def groupEquiv : Group ≃ Fin 4096 × Fin 4096 where
  toFun g := (cand1 g, cand2 g)
  invFun d := (UInt8.ofNat (d.1.val % 256),
    UInt8.ofNat (d.1.val / 256 + 16 * (d.2.val % 16)), UInt8.ofNat (d.2.val / 16))
  left_inv g := by
    obtain ⟨b0, b1, b2⟩ := g
    have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt
    simp only [cand1, cand2, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> rw [UInt8.toNat_ofNat'] <;> omega
  right_inv d := by
    obtain ⟨⟨d1, h1⟩, ⟨d2, h2⟩⟩ := d
    simp only [cand1, cand2, UInt8.toNat_ofNat', Prod.mk.injEq, Fin.mk.injEq]
    omega

/-- The accepted value of a 12-bit candidate: `some d` in `Zq` when `d < 3329`,
`none` otherwise. -/
def accept (d : Fin 4096) : Option Zq :=
  if d.val < 3329 then some (Zq3329.fromNat d.val) else none

/-- Each value of `Zq` is accepted from exactly one candidate. -/
theorem card_accept_some (a : Zq) :
    (Finset.univ.filter fun d => accept d = some a).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨⟨a.val, by have := ZMod.val_lt a; omega⟩, ?_⟩
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    unfold accept at h
    by_cases hd : d.val < 3329
    · rw [if_pos hd] at h
      have h' := Option.some.inj h
      ext
      simp only [← h', Zq3329.fromNat, ZMod.val_natCast, Nat.mod_eq_of_lt hd]
    · rw [if_neg hd] at h
      exact absurd h (by simp)
  · rintro rfl
    simp [accept, ZMod.val_lt, Zq3329.fromNat]

/-- The number of rejected 12-bit candidates (`4096 - 3329`). -/
def rejectCount : ℕ := (Finset.univ.filter fun d => accept d = none).card

theorem rejectCount_eq : rejectCount = 767 := by
  have h : (Finset.univ.filter fun d : Fin 4096 => accept d = none) =
      Finset.univ.filter (fun d : Fin 4096 => ¬ d.val < 3329) := by
    ext d
    rw [Finset.mem_filter, Finset.mem_filter]
    unfold accept
    by_cases hd : d.val < 3329 <;> simp [hd]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 4096))) (fun d => d.val < 3329)
  rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at hsum
  rw [rejectCount, h]
  omega

/-- Algorithm 7 on a stream that starts with a full group: the accepted values of
the two candidates of the group, followed by the output on the rest. -/
theorem rejNTT_group (b0 b1 b2 : UInt8) (rest : List UInt8) :
    rejNTT (b0 :: b1 :: b2 :: rest) =
      (accept (cand1 (b0, b1, b2))).toList ++ (accept (cand2 (b0, b1, b2))).toList ++
        rejNTT rest := by
  simp only [rejNTT, accept, cand1, cand2, q]
  by_cases h1 : b0.toNat + 256 * (b1.toNat % 16) < 3329 <;>
    by_cases h2 : b1.toNat / 16 + 16 * b2.toNat < 3329 <;> simp [h1, h2]

/-! ## The XOF stream -/

/-- An XOF output of `m` three-byte groups (`3 * m` bytes). -/
abbrev Stream (m : ℕ) : Type := Fin m → Group

/-- The byte list of a stream, group by group. -/
def toBytes {m : ℕ} (s : Stream m) : List UInt8 :=
  (List.ofFn fun i => [(s i).1, (s i).2.1, (s i).2.2]).flatten

theorem toBytes_cons {m : ℕ} (g : Group) (s : Stream m) :
    toBytes (Fin.cons g s : Stream (m + 1)) = g.1 :: g.2.1 :: g.2.2 :: toBytes s := by
  simp [toBytes, List.ofFn_succ]

/-- The number of `m`-group streams whose accepted values start with a given
list of length `k`. -/
def prefixCount : ℕ → ℕ → ℕ
  | 0 => fun k => if k = 0 then 1 else 0
  | m + 1 => stepCount rejectCount 4096 (stepCount rejectCount 4096 (prefixCount m))

/-- The number of streams whose accepted values start with `u` depends only on
the length of `u`. -/
theorem card_prefix_rejNTT (m : ℕ) (u : List Zq) :
    (Finset.univ.filter fun s : Stream m => u <+: rejNTT (toBytes s)).card =
      prefixCount m u.length := by
  induction m generalizing u with
  | zero =>
    have hb : ∀ s : Stream 0, toBytes s = [] := fun s => by simp [toBytes]
    cases u with
    | nil => simp [prefixCount]
    | cons a u' => simp [prefixCount, hb, rejNTT]
  | succ m ih =>
    let E : Fin 4096 × (Fin 4096 × Stream m) ≃ Stream (m + 1) :=
      (Equiv.prodAssoc _ _ _).symm.trans
        ((Equiv.prodCongr groupEquiv.symm (Equiv.refl _)).trans (Fin.consEquiv fun _ => Group))
    have hE : ∀ p : Fin 4096 × (Fin 4096 × Stream m),
        rejNTT (toBytes (E p)) =
          (accept p.1).toList ++ ((accept p.2.1).toList ++ rejNTT (toBytes p.2.2)) := by
      rintro ⟨d1, d2, s⟩
      have hEp : E (d1, d2, s) = Fin.cons (groupEquiv.symm (d1, d2)) s := rfl
      rw [hEp, toBytes_cons]
      have h' : groupEquiv (groupEquiv.symm (d1, d2)) = (d1, d2) := groupEquiv.apply_symm_apply _
      generalize groupEquiv.symm (d1, d2) = g at h' ⊢
      obtain ⟨b0, b1, b2⟩ := g
      simp only [groupEquiv, Equiv.coe_fn_mk, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rw [rejNTT_group, List.append_assoc]
    have hcard := Finset.card_equiv E
      (s := Finset.univ.filter fun p => u <+: rejNTT (toBytes (E p)))
      (t := Finset.univ.filter fun s : Stream (m + 1) => u <+: rejNTT (toBytes s))
      (fun p => by simp)
    rw [← hcard]
    simp only [hE]
    have step1 := card_prefix_step accept rejectCount rfl card_accept_some
      (fun s : Stream m => rejNTT (toBytes s)) (prefixCount m) ih
    have step2 := card_prefix_step accept rejectCount rfl card_accept_some
      (fun p : Fin 4096 × Stream m => (accept p.1).toList ++ rejNTT (toBytes p.2)) _ step1 u
    simpa only [Fintype.card_fin, prefixCount] using step2

/-! ## Stage 1: one polynomial -/

/-- An NTT-domain polynomial, the output type of Algorithm 7. -/
abbrev Poly : Type := Fin 256 → Zq

/-- Algorithm 7 fills and outputs `p` exactly when the coefficients of `p` are a
prefix of the accepted values. -/
theorem fills_and_sampleNTT_iff (l : List UInt8) (p : Poly) :
    (SampleNTTFills l ∧ sampleNTT l = p) ↔ List.ofFn p <+: rejNTT l := by
  constructor
  · rintro ⟨hf, rfl⟩
    rw [List.prefix_iff_eq_take]
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_take]
      exact (Nat.min_eq_left hf).symm
    · intro i h1 h2
      simp only [List.length_ofFn] at h1
      rw [List.getElem_ofFn, List.getElem_take, sampleNTT_of_fills l hf ⟨i, h1⟩]
  · intro h
    have hlen : SampleNTTFills l := by
      have := h.length_le
      rw [List.length_ofFn] at this
      exact this
    refine ⟨hlen, funext fun i => ?_⟩
    rw [sampleNTT_of_fills l hlen i]
    have hi : i.val < (List.ofFn p).length := by rw [List.length_ofFn]; exact i.isLt
    rw [← h.getElem hi, List.getElem_ofFn]

/-- The polynomial Algorithm 7 reads from a stream. -/
def sampleOf {m : ℕ} (s : Stream m) : Poly := sampleNTT (toBytes s)

/-- The stream fills: Algorithm 7 accepts at least 256 values. -/
def Fills {m : ℕ} (s : Stream m) : Prop := SampleNTTFills (toBytes s)

instance {m : ℕ} (s : Stream m) : Decidable (Fills s) :=
  inferInstanceAs (Decidable (256 ≤ (rejNTT (toBytes s)).length))

/-- **Conditional uniformity (count form).** For every polynomial `p`, the
number of `m`-group streams that fill and yield `p` is `prefixCount m 256`, a
number independent of `p`. -/
theorem card_fills_sampleOf_eq (m : ℕ) (p : Poly) :
    (Finset.univ.filter fun s : Stream m => Fills s ∧ sampleOf s = p).card =
      prefixCount m 256 := by
  have h := card_prefix_rejNTT m (List.ofFn p)
  simp only [List.length_ofFn] at h
  rw [← h]
  refine Finset.card_bij (fun s _ => s) ?_ (fun _ _ _ _ h => h) ?_
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    exact ⟨hs.1, (fills_and_sampleNTT_iff _ p).mp hs.2⟩
  · intro s hs
    rw [Finset.mem_filter] at hs
    exact ⟨s, by rw [Finset.mem_filter]; exact ⟨hs.1, (fills_and_sampleNTT_iff _ p).mpr hs.2⟩, rfl⟩

/-- The number of filling streams is `|Poly| * prefixCount m 256`. -/
theorem card_fills_eq (m : ℕ) :
    (Finset.univ.filter fun s : Stream m => Fills s).card =
      Fintype.card Poly * prefixCount m 256 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := sampleOf) (t := Finset.univ) (by simp)]
  simp only [Finset.filter_filter, card_fills_sampleOf_eq, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]

/-! ## Probabilities under a uniform stream -/

/-- The image of the uniform distribution under `f`, evaluated at `y`, is the
fraction of inputs that `f` maps to `y`. -/
theorem bind_pure_uniform_apply {S Y : Type} [Fintype S] [Nonempty S] [DecidableEq Y]
    (f : S → Y) (y : Y) :
    ((SDistr.uniform S).bind fun s => SDistr.pure (f s)) (some y) =
      ((Finset.univ.filter fun s => f s = y).card : ℝ≥0∞) / Fintype.card S := by
  classical
  simp only [SDistr.bind, SDistr.uniform, PMF.bind_apply, PMF.map_apply, tsum_fintype]
  rw [Fintype.sum_option]
  simp
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv]

/-- The probability that a uniform `m`-group stream fills. -/
noncomputable def fillProb (m : ℕ) : ℝ≥0∞ :=
  ((Finset.univ.filter fun s : Stream m => Fills s).card : ℝ≥0∞) / Fintype.card (Stream m)

/-- The probability that a uniform `m`-group stream does not fill, the
statistical cost of one polynomial. -/
noncomputable def nonFillProb (m : ℕ) : ℝ≥0∞ :=
  ((Finset.univ.filter fun s : Stream m => ¬ Fills s).card : ℝ≥0∞) / Fintype.card (Stream m)

theorem nonFillProb_eq (m : ℕ) : nonFillProb m = 1 - fillProb m := by
  have hS : (Fintype.card (Stream m) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Stream m)).ne'
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Stream m))) (fun s => Fills s)
  have hfin : fillProb m ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hS
  refine ENNReal.eq_sub_of_add_eq hfin ?_
  rw [nonFillProb, fillProb, ENNReal.div_add_div_same, ← Nat.cast_add, add_comm, hsum,
    Finset.card_univ, ENNReal.div_self hS (ENNReal.natCast_ne_top _)]

theorem fillProb_eq (m : ℕ) :
    fillProb m =
      ((Fintype.card Poly : ℝ≥0∞) * prefixCount m 256) / Fintype.card (Stream m) := by
  rw [fillProb, card_fills_eq, Nat.cast_mul]

/-- **Stage 1, conditional uniformity.** For a uniform stream, the probability
of filling and yielding `p` is `fillProb m / |Poly|` for every `p`: conditioned on
filling, the output of Algorithm 7 is uniform. -/
theorem prob_fills_sampleOf_eq (m : ℕ) (p : Poly) :
    ((Finset.univ.filter fun s : Stream m => Fills s ∧ sampleOf s = p).card : ℝ≥0∞) /
        Fintype.card (Stream m) = fillProb m / Fintype.card Poly := by
  have hP : (Fintype.card Poly : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Poly)).ne'
  rw [card_fills_sampleOf_eq, fillProb_eq, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    mul_comm (Fintype.card Poly : ℝ≥0∞), mul_assoc, mul_assoc]
  congr 1
  rw [mul_left_comm, ENNReal.mul_inv_cancel hP (ENNReal.natCast_ne_top _), mul_one]

/-- Bernoulli's inequality in `ℝ≥0∞`: `1 - n δ ≤ (1 - δ) ^ n`. -/
theorem one_sub_mul_le_pow (δ : ℝ≥0∞) (n : ℕ) : 1 - n * δ ≤ (1 - δ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    set x := (1 - δ) ^ n with hx
    have hx1 : x ≤ 1 := pow_le_one₀ zero_le tsub_le_self
    have hxt : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx1
    rw [pow_succ, ← hx, ENNReal.mul_sub (fun _ _ => hxt), mul_one, Nat.cast_succ, add_mul,
      one_mul, tsub_add_eq_tsub_tsub]
    calc 1 - ↑n * δ - δ ≤ x - δ := tsub_le_tsub_right ih δ
      _ ≤ x - x * δ := tsub_le_tsub_left (mul_le_of_le_one_left' hx1) x

theorem fillProb_le_one (m : ℕ) : fillProb m ≤ 1 := by
  rw [fillProb]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul, ← Finset.card_univ]
  exact_mod_cast Finset.card_filter_le _ _

/-! ## A bound on the non-fill probability -/

/-- The count of short outputs after prepending one candidate: `e` rejecting
candidates keep the length, `a` accepting candidates add one. -/
def shortStep (e a : ℕ) (G : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | K + 1 => e * G (K + 1) + a * G K

/-- One candidate step of the count of outputs shorter than `K`. -/
theorem card_short_step {C Ω V : Type} [Fintype C] [Fintype Ω]
    (acc : C → Option V) (e a : ℕ)
    (he : (Finset.univ.filter fun d => acc d = none).card = e)
    (ha : (Finset.univ.filter fun d => ¬ acc d = none).card = a)
    (F : Ω → List V) (G : ℕ → ℕ)
    (hF : ∀ K, (Finset.univ.filter fun ω => (F ω).length < K).card = G K) (K : ℕ) :
    (Finset.univ.filter fun p : C × Ω => ((acc p.1).toList ++ F p.2).length < K).card =
      shortStep e a G K := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp only [← Finset.card_filter]
  cases K with
  | zero => simp [shortStep]
  | succ K =>
    have hterm : ∀ d : C,
        (Finset.univ.filter fun ω => ((acc d).toList ++ F ω).length < K + 1).card =
          (if acc d = none then G (K + 1) else 0) + (if ¬ acc d = none then G K else 0) := by
      intro d
      cases hd : acc d with
      | none =>
        simp only [Option.toList_none, List.nil_append, if_true, if_false, add_zero,
          not_true_eq_false]
        exact hF (K + 1)
      | some b =>
        simp only [Option.toList_some, List.singleton_append, List.length_cons,
          Nat.add_lt_add_iff_right, reduceCtorEq, if_false, zero_add, not_false_eq_true, if_true]
        exact hF K
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
      Finset.sum_const, smul_eq_mul, add_zero, he, ha, shortStep]

/-- The number of accepted 12-bit candidates. -/
theorem card_accept_ne_none :
    (Finset.univ.filter fun d : Fin 4096 => ¬ accept d = none).card = 3329 := by
  have h : (Finset.univ.filter fun d : Fin 4096 => ¬ accept d = none) =
      Finset.univ.filter (fun d : Fin 4096 => d.val < 3329) := by
    ext d
    rw [Finset.mem_filter, Finset.mem_filter]
    unfold accept
    by_cases hd : d.val < 3329 <;> simp [hd]
  rw [h, Fin.card_filter_val_lt]
  norm_num

/-- The number of `n`-candidate streams with fewer than `K` accepted values. -/
def shortCount : ℕ → ℕ → ℕ
  | 0 => fun K => if 0 < K then 1 else 0
  | n + 1 => shortStep 767 3329 (shortCount n)

/-- The number of streams with fewer than `K` accepted values is
`shortCount (2 m) K`. -/
theorem card_short_rejNTT (m K : ℕ) :
    (Finset.univ.filter fun s : Stream m => (rejNTT (toBytes s)).length < K).card =
      shortCount (2 * m) K := by
  induction m generalizing K with
  | zero =>
    have hb : ∀ s : Stream 0, toBytes s = [] := fun s => by simp [toBytes]
    cases K with
    | zero => simp [shortCount]
    | succ K => simp [shortCount, hb, rejNTT]
  | succ m ih =>
    let E : Fin 4096 × (Fin 4096 × Stream m) ≃ Stream (m + 1) :=
      (Equiv.prodAssoc _ _ _).symm.trans
        ((Equiv.prodCongr groupEquiv.symm (Equiv.refl _)).trans (Fin.consEquiv fun _ => Group))
    have hE : ∀ p : Fin 4096 × (Fin 4096 × Stream m),
        rejNTT (toBytes (E p)) =
          (accept p.1).toList ++ ((accept p.2.1).toList ++ rejNTT (toBytes p.2.2)) := by
      rintro ⟨d1, d2, s⟩
      have hEp : E (d1, d2, s) = Fin.cons (groupEquiv.symm (d1, d2)) s := rfl
      rw [hEp, toBytes_cons]
      have h' : groupEquiv (groupEquiv.symm (d1, d2)) = (d1, d2) := groupEquiv.apply_symm_apply _
      generalize groupEquiv.symm (d1, d2) = g at h' ⊢
      obtain ⟨b0, b1, b2⟩ := g
      simp only [groupEquiv, Equiv.coe_fn_mk, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rw [rejNTT_group, List.append_assoc]
    have hcard := Finset.card_equiv E
      (s := Finset.univ.filter fun p => (rejNTT (toBytes (E p))).length < K)
      (t := Finset.univ.filter fun s : Stream (m + 1) => (rejNTT (toBytes s)).length < K)
      (fun p => by simp)
    rw [← hcard]
    simp only [hE]
    have he : (Finset.univ.filter fun d : Fin 4096 => accept d = none).card = 767 :=
      rejectCount_eq
    have step1 := card_short_step accept 767 3329 he card_accept_ne_none
      (fun s : Stream m => rejNTT (toBytes s)) (shortCount (2 * m)) ih
    have step2 := card_short_step accept 767 3329 he card_accept_ne_none
      (fun p : Fin 4096 × Stream m => (accept p.1).toList ++ rejNTT (toBytes p.2)) _ step1 K
    rw [step2, show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    rfl

theorem shortCount_zero (n : ℕ) : shortCount n 0 = 0 := by
  cases n <;> rfl

theorem shortCount_le_pow (n K : ℕ) : shortCount n K ≤ 4096 ^ n := by
  induction n generalizing K with
  | zero => simp only [shortCount]; split_ifs <;> simp
  | succ n ih =>
    cases K with
    | zero => simp [shortCount, shortStep]
    | succ K =>
      show 767 * shortCount n (K + 1) + 3329 * shortCount n K ≤ 4096 ^ (n + 1)
      have h1 := ih (K + 1)
      have h2 := ih K
      rw [pow_succ]
      omega

/-- Union bound over the positions of `r` rejections: at most
`C(k + r, k) · 767 ^ r · 4096 ^ k` streams of `k + r` candidates accept at most
`k` values. -/
theorem shortCount_le_choose (k r : ℕ) :
    shortCount (k + r) (k + 1) ≤ (k + r).choose k * 767 ^ r * 4096 ^ k := by
  induction r generalizing k with
  | zero =>
    simpa using shortCount_le_pow k (k + 1)
  | succ r ihr =>
    induction k with
    | zero =>
      simp only [Nat.zero_add]
      show 767 * shortCount r 1 + 3329 * shortCount r 0 ≤ _
      have h := ihr 0
      simp only [Nat.zero_add, Nat.choose_zero_right, one_mul, pow_zero, mul_one] at h
      rw [shortCount_zero]
      simp only [Nat.choose_zero_right, one_mul, pow_zero, mul_one, mul_zero, add_zero,
        pow_succ]
      nlinarith
    | succ k ihk =>
      show 767 * shortCount (k + 1 + r) (k + 1 + 1) + 3329 * shortCount (k + 1 + r) (k + 1)
        ≤ _
      have h1 := ihr (k + 1)
      have h2 := ihk
      have hc : (k + 1 + (r + 1)).choose (k + 1) =
          (k + 1 + r).choose k + (k + 1 + r).choose (k + 1) := by
        rw [show k + 1 + (r + 1) = (k + 1 + r) + 1 by ring, Nat.choose_succ_succ]
      rw [show k + (r + 1) = k + 1 + r by ring] at h2
      rw [hc]
      set A := (k + 1 + r).choose k
      set B := (k + 1 + r).choose (k + 1)
      set x := shortCount (k + 1 + r) (k + 1 + 1)
      set y := shortCount (k + 1 + r) (k + 1)
      have hx : x ≤ B * 767 ^ r * 4096 ^ (k + 1) := h1
      have hy : y ≤ A * 767 ^ (r + 1) * 4096 ^ k := h2
      calc 767 * x + 3329 * y
          ≤ 767 * (B * 767 ^ r * 4096 ^ (k + 1)) + 3329 * (A * 767 ^ (r + 1) * 4096 ^ k) := by
            gcongr
        _ ≤ (A + B) * 767 ^ (r + 1) * 4096 ^ (k + 1) := by
            rw [pow_succ, pow_succ]
            nlinarith [Nat.zero_le (A * 767 ^ r * 4096 ^ k)]

/-- The count of non-filling streams. -/
theorem card_not_fills (m : ℕ) :
    (Finset.univ.filter fun s : Stream m => ¬ Fills s).card = shortCount (2 * m) 256 := by
  rw [← card_short_rejNTT]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fills, SampleNTTFills, not_le]

/-- **Non-fill bound.** For `255 ≤ 2 m`, a uniform stream of `m` groups
(`2 m` candidates) fails to yield 256 accepted values with probability at most
`C(2 m, 255) · (767 / 4096) ^ (2 m - 255)`. -/
theorem nonFillProb_le (m : ℕ) (hm : 255 ≤ 2 * m) :
    nonFillProb m ≤ ((2 * m).choose 255 : ℝ≥0∞) * (767 / 4096) ^ (2 * m - 255) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * m = 255 + r := ⟨2 * m - 255, by omega⟩
  have hcardS : Fintype.card (Stream m) = 4096 ^ (255 + r) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_congr groupEquiv, Fintype.card_prod,
      Fintype.card_fin, ← hr, pow_mul, sq]
  have hcount := shortCount_le_choose 255 r
  rw [nonFillProb, card_not_fills, hcardS, hr, Nat.add_sub_cancel_left]
  have hB0 : ((4096 : ℝ≥0∞) ^ 255) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hBt : ((4096 : ℝ≥0∞) ^ 255) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  calc (shortCount (255 + r) 256 : ℝ≥0∞) / ((4096 ^ (255 + r) : ℕ) : ℝ≥0∞)
      ≤ (((255 + r).choose 255 * 767 ^ r * 4096 ^ 255 : ℕ) : ℝ≥0∞) /
          ((4096 ^ (255 + r) : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = ((255 + r).choose 255 : ℝ≥0∞) * (767 / 4096) ^ r := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow,
          Nat.cast_ofNat, Nat.cast_ofNat, pow_add, mul_comm ((4096 : ℝ≥0∞) ^ 255) ((4096 : ℝ≥0∞) ^ r),
          ENNReal.mul_div_mul_right _ _ hB0 hBt, mul_div_assoc, div_eq_mul_inv, div_eq_mul_inv,
          mul_pow, ENNReal.inv_pow]

/-! ## Stage 2: the matrix -/

/-- The `k × k` family of XOF outputs: `H (j, i)` is the random-oracle output
on input `(ρ, j, i)`, a stream of `m` groups. -/
abbrev Family (k m : ℕ) : Type := Fin k × Fin k → Stream m

/-- A `k × k` matrix of NTT-domain polynomials. -/
abbrev Mat (k : ℕ) : Type := Fin k → Fin k → Poly

/-- Reindexing a family by `(j, i)` as a matrix entry `(i, j)`. -/
def matEquiv (k : ℕ) : (Fin k × Fin k → Poly) ≃ Mat k :=
  (Equiv.arrowCongr (Equiv.prodComm _ _) (Equiv.refl _)).trans (Equiv.curry _ _ _)

/-- FIPS 203 Algorithm 13, line 5: `Â[i, j] := SampleNTT(XOF(ρ, j, i))`, with
the XOF output on `(ρ, j, i)` given by `H (j, i)`. -/
def xofMatrix {k m : ℕ} (H : Family k m) : Mat k :=
  matEquiv k fun x => sampleOf (H x)

theorem xofMatrix_apply {k m : ℕ} (H : Family k m) (i j : Fin k) :
    xofMatrix H i j = sampleOf (H (j, i)) := rfl

/-- Independent coordinates: if every value `y` has exactly `g` preimages
satisfying `P`, then every `M : ι → Y` has at least `g ^ |ι|` coordinatewise
preimages. -/
theorem card_pi_filter_le {ι Ω Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    [DecidableEq Y] (f : Ω → Y) (P : Ω → Prop) [DecidablePred P] (g : ℕ)
    (hg : ∀ y, (Finset.univ.filter fun ω => P ω ∧ f ω = y).card = g) (M : ι → Y) :
    g ^ Fintype.card ι ≤ (Finset.univ.filter fun H : ι → Ω => ∀ x, f (H x) = M x).card := by
  calc g ^ Fintype.card ι
        = ∏ x : ι, (Finset.univ.filter fun ω => P ω ∧ f ω = M x).card := by
          simp only [hg, Finset.prod_const, Finset.card_univ]
    _ = (Fintype.piFinset fun x => Finset.univ.filter fun ω => P ω ∧ f ω = M x).card :=
          (Fintype.card_piFinset _).symm
    _ ≤ _ := by
          apply Finset.card_le_card
          intro H hH
          rw [Fintype.mem_piFinset] at hH
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, fun x => ?_⟩
          have hx := hH x
          rw [Finset.mem_filter] at hx
          exact hx.2.2

/-- `((P c) / S) ^ n · (P ^ n)⁻¹ = c ^ n / S ^ n` for `P ≠ 0, ⊤`. -/
theorem pow_div_mul_inv_pow (P c S : ℝ≥0∞) (hP0 : P ≠ 0) (hPt : P ≠ ⊤) (n : ℕ) :
    (P * c / S) ^ n * (P ^ n)⁻¹ = c ^ n / S ^ n := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_pow]
  simp only [ENNReal.inv_pow]
  rw [show P ^ n * c ^ n * S⁻¹ ^ n * P⁻¹ ^ n = c ^ n * S⁻¹ ^ n * (P * P⁻¹) ^ n by ring,
    ENNReal.mul_inv_cancel hP0 hPt, one_pow, mul_one]

/-- The distribution of `e (xofMatrix H)` for a uniform family `H`. -/
noncomputable def xofMatrixDistVia {k m : ℕ} {T : Type} (e : Mat k ≃ T) : SDistr T :=
  (SDistr.uniform (Family k m)).bind fun H => SDistr.pure (e (xofMatrix H))

/-- The distribution of `xofMatrix H` for a uniform family `H`: the matrix of
FIPS 203 K-PKE.KeyGen with the XOF modelled as a random oracle. -/
noncomputable def xofMatrixDist (k m : ℕ) : SDistr (Mat k) :=
  xofMatrixDistVia (m := m) (Equiv.refl (Mat k))

theorem card_family (k m : ℕ) :
    Fintype.card (Family k m) = Fintype.card (Stream m) ^ (k * k) := by
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]

theorem card_mat (k : ℕ) : Fintype.card (Mat k) = Fintype.card Poly ^ (k * k) := by
  rw [Fintype.card_fun (α := Fin k) (β := Fin k → Poly),
    Fintype.card_fun (α := Fin k) (β := Poly), Fintype.card_fin, ← pow_mul]

/-- **Stage 2, pointwise form.** The XOF matrix distribution dominates
`(1 - k² · nonFillProb m)` times the uniform distribution. -/
theorem xofMatrixDistVia_minorant {k m : ℕ} {T : Type} [Fintype T] [Nonempty T]
    (e : Mat k ≃ T) (A : T) :
    (1 - ((k * k : ℕ) : ℝ≥0∞) * nonFillProb m) * (SDistr.uniform T) (some A) ≤
      xofMatrixDistVia (m := m) e (some A) := by
  classical
  rw [xofMatrixDistVia, bind_pure_uniform_apply, SDistr.uniform_apply_some,
    Fintype.card_congr e.symm, card_mat, card_family]
  have hcount := card_pi_filter_le sampleOf Fills (prefixCount m 256)
    (card_fills_sampleOf_eq m) ((matEquiv k).symm (e.symm A))
  rw [Fintype.card_prod, Fintype.card_fin] at hcount
  have hsub : (prefixCount m 256) ^ (k * k) ≤
      (Finset.univ.filter fun H : Family k m => e (xofMatrix H) = A).card := by
    refine hcount.trans (Finset.card_le_card fun H hH => ?_)
    rw [Finset.mem_filter] at hH ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hH' : (fun x => sampleOf (H x)) = (matEquiv k).symm (e.symm A) := funext hH.2
    rw [xofMatrix, hH', Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hP0 : (Fintype.card Poly : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Poly)).ne'
  have hfill : 1 - nonFillProb m = fillProb m := by
    rw [nonFillProb_eq, ENNReal.sub_sub_cancel ENNReal.one_ne_top (fillProb_le_one m)]
  calc (1 - ((k * k : ℕ) : ℝ≥0∞) * nonFillProb m) * ((Fintype.card Poly ^ (k * k) : ℕ) : ℝ≥0∞)⁻¹
      ≤ fillProb m ^ (k * k) * ((Fintype.card Poly : ℝ≥0∞) ^ (k * k))⁻¹ := by
        rw [Nat.cast_pow, ← hfill]
        gcongr
        exact one_sub_mul_le_pow _ _
    _ = ((prefixCount m 256 : ℝ≥0∞)) ^ (k * k) / (Fintype.card (Stream m) : ℝ≥0∞) ^ (k * k) := by
        rw [fillProb_eq]
        exact pow_div_mul_inv_pow _ _ _ hP0 (ENNReal.natCast_ne_top _) _
    _ ≤ _ := by
        rw [Nat.cast_pow, div_eq_mul_inv, div_eq_mul_inv]
        gcongr
        exact_mod_cast hsub

/-- Pointwise domination extends from `some` to all of `Option`. -/
theorem minorant_option {α : Type} [Fintype α] [Nonempty α] (d : SDistr α) (β : ℝ≥0∞)
    (h : ∀ a, (1 - β) * SDistr.uniform α (some a) ≤ d (some a)) :
    ∀ x, (1 - β) * SDistr.uniform α x ≤ d x := by
  rintro (_ | a)
  · simp [SDistr.uniform_apply_none]
  · exact h a

/-- **Stage 2.** The total-variation distance between the XOF matrix and a
uniform matrix is at most `k² · nonFillProb m`. -/
theorem sdist_xofMatrix_uniform_le (k m : ℕ) :
    tvDist (xofMatrixDist k m) (SDistr.uniform (Mat k)) ≤
      ((k * k : ℕ) : ℝ≥0∞) * nonFillProb m := by
  refine iSup₂_le fun f hf => ?_
  have h := tsum_le_add_of_minorant (xofMatrixDist k m) (SDistr.uniform (Mat k)) _
    (minorant_option _ _ (xofMatrixDistVia_minorant (m := m) (Equiv.refl _))) f hf
  exact sup_le (tsub_le_iff_left.mpr h.1) (tsub_le_iff_left.mpr h.2)

/-- Stage 2 with the non-fill bound: for `255 ≤ 2 m`, the total-variation
distance between the XOF matrix and a uniform `k × k` matrix is at most
`k² · C(2 m, 255) · (767 / 4096) ^ (2 m - 255)`. -/
theorem sdist_xofMatrix_uniform_le_choose (k m : ℕ) (hm : 255 ≤ 2 * m) :
    tvDist (xofMatrixDist k m) (SDistr.uniform (Mat k)) ≤
      ((k * k : ℕ) : ℝ≥0∞) * (((2 * m).choose 255 : ℝ≥0∞) * (767 / 4096) ^ (2 * m - 255)) :=
  (sdist_xofMatrix_uniform_le k m).trans (by gcongr; exact nonFillProb_le m hm)

/-! ## Stage 3: transfer to the module-LWE game -/

/-- `prTrue` of a bind is the `d`-weighted average of `prTrue` of the
continuation. -/
theorem prTrue_bind {α : Type} (d : SDistr α) (K : α → SDistr Bool) :
    prTrue (d.bind K) = ∑' o, d o * Option.elim o 0 (fun a => prTrue (K a)) := by
  unfold prTrue SDistr.bind
  rw [PMF.bind_apply]
  refine tsum_congr fun o => ?_
  cases o with
  | none => simp [SDistr.fail_apply_some]
  | some a => rfl

/-- A continuation run on a distribution that dominates `(1 - β)` times the
uniform one outputs `true` with probability within `β` of the uniform run. -/
theorem prTrue_bind_close {α : Type} [Fintype α] [Nonempty α] (d : SDistr α) (β : ℝ≥0∞)
    (h : ∀ a, (1 - β) * SDistr.uniform α (some a) ≤ d (some a)) (K : α → SDistr Bool) :
    prTrue (d.bind K) ≤ prTrue ((SDistr.uniform α).bind K) + β ∧
      prTrue ((SDistr.uniform α).bind K) ≤ prTrue (d.bind K) + β := by
  rw [prTrue_bind, prTrue_bind]
  refine tsum_le_add_of_minorant d (SDistr.uniform α) β (minorant_option d β h) _ ?_
  rintro (_ | a)
  · exact zero_le_one
  · exact PMF.coe_le_one _ _

/-- Averaging preserves a pointwise additive bound. -/
theorem prTrue_bind_le_of_forall {α : Type} (d : SDistr α) (f g : α → SDistr Bool)
    (β : ℝ≥0∞) (h : ∀ a, prTrue (f a) ≤ prTrue (g a) + β) :
    prTrue (d.bind f) ≤ prTrue (d.bind g) + β := by
  rw [prTrue_bind, prTrue_bind]
  calc ∑' o, d o * Option.elim o 0 (fun a => prTrue (f a))
      ≤ ∑' o, (d o * Option.elim o 0 (fun a => prTrue (g a)) + d o * β) := by
        refine ENNReal.tsum_le_tsum fun o => ?_
        rw [← mul_add]
        gcongr
        cases o with
        | none => exact zero_le
        | some a => exact h a
    _ ≤ ∑' o, d o * Option.elim o 0 (fun a => prTrue (g a)) + β := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, d.tsum_coe, one_mul]

/-- `absDiff` moves by at most `2 β` when each argument moves by at most `β`. -/
theorem absDiff_le_of_close {a b a' b' β : ℝ≥0∞} (ha : a ≤ a' + β) (ha' : a' ≤ a + β)
    (hb : b ≤ b' + β) (hb' : b' ≤ b + β) : absDiff a b ≤ absDiff a' b' + 2 * β := by
  have h1 : a' ≤ absDiff a' b' + b' := le_tsub_add.trans (add_le_add le_sup_left le_rfl)
  have h2 : b' ≤ absDiff a' b' + a' := le_tsub_add.trans (add_le_add le_sup_right le_rfl)
  refine sup_le (tsub_le_iff_right.mpr ?_) (tsub_le_iff_right.mpr ?_)
  · calc a ≤ a' + β := ha
      _ ≤ absDiff a' b' + b' + β := add_le_add h1 le_rfl
      _ ≤ absDiff a' b' + (b + β) + β := by gcongr
      _ = absDiff a' b' + 2 * β + b := by ring
  · calc b ≤ b' + β := hb
      _ ≤ absDiff a' b' + a' + β := add_le_add h2 le_rfl
      _ ≤ absDiff a' b' + (a + β) + β := by gcongr
      _ = absDiff a' b' + 2 * β + a := by ring

/-- The module-LWE game of `MLWE.Game` with the matrix drawn from `dA`. -/
noncomputable def gameWith (P : MLWE.Params) (dA : SDistr P.Mat)
    (adv : P.Mat → P.Vec → SDistr Bool) (b : Bool) : SDistr Bool := do
  let A ← dA
  if b then do
    let u ← SDistr.uniform P.Vec
    adv A u
  else do
    let s ← P.dshort_vec
    let e ← P.dshort_vec
    let t := P.vec_add (P.mat_vec_mul A s) e
    adv A t

/-- With a uniform matrix, `gameWith` is `MLWE.Game`. -/
theorem gameWith_uniform (P : MLWE.Params) (adv : P.Mat → P.Vec → SDistr Bool) (b : Bool) :
    gameWith P (SDistr.uniform P.Mat) adv b = MLWE.Game P adv b := rfl

/-- The module-LWE advantage with the matrix drawn from `dA`. -/
noncomputable def advantageWith (P : MLWE.Params) (dA : SDistr P.Mat)
    (adv : P.Mat → P.Vec → SDistr Bool) : ℝ≥0∞ :=
  absDiff (prTrue (gameWith P dA adv false)) (prTrue (gameWith P dA adv true))

/-- **Matrix-distribution transfer.** If `dA` dominates `(1 - β)` times the
uniform matrix distribution, the module-LWE advantage of every distinguisher
with the matrix drawn from `dA` is within `2 β` of `MLWE.advantage`. -/
theorem advantageWith_le (P : MLWE.Params) (dA : SDistr P.Mat) (β : ℝ≥0∞)
    (h : ∀ A, (1 - β) * SDistr.uniform P.Mat (some A) ≤ dA (some A))
    (adv : P.Mat → P.Vec → SDistr Bool) :
    advantageWith P dA adv ≤ MLWE.advantage P adv + 2 * β := by
  have key : ∀ b, prTrue (gameWith P dA adv b) ≤ prTrue (MLWE.Game P adv b) + β ∧
      prTrue (MLWE.Game P adv b) ≤ prTrue (gameWith P dA adv b) + β := fun b =>
    prTrue_bind_close dA β h _
  exact absDiff_le_of_close (key false).1 (key false).2 (key true).1 (key true).2

/-- **Stage 3.** For every module-LWE parameter set whose matrix type is `Mat k`
up to an equivalence `e`, and every distinguisher, the advantage with the
matrix expanded from `k²` independent uniform XOF streams of `m` groups is
within `2 k² · nonFillProb m` of the uniform-matrix `MLWE.advantage`. -/
theorem mlwe_advantage_xofMatrix_le (P : MLWE.Params) (k m : ℕ) (e : Mat k ≃ P.Mat)
    (adv : P.Mat → P.Vec → SDistr Bool) :
    advantageWith P (xofMatrixDistVia (m := m) e) adv ≤
      MLWE.advantage P adv + 2 * (((k * k : ℕ) : ℝ≥0∞) * nonFillProb m) :=
  advantageWith_le P _ _ (xofMatrixDistVia_minorant e) adv

/-! ### A distinguisher that sees the seed -/

/-- The module-LWE game in which the distinguisher also receives a uniform seed
`ρ`, drawn independently of the matrix distribution `dA`. -/
noncomputable def gameSeed (P : MLWE.Params) (Seed : Type) [Fintype Seed] [Nonempty Seed]
    (dA : SDistr P.Mat) (adv : Seed → P.Mat → P.Vec → SDistr Bool) (b : Bool) :
    SDistr Bool :=
  (SDistr.uniform Seed).bind fun ρ => gameWith P dA (adv ρ) b

/-- The advantage in `gameSeed`. -/
noncomputable def advantageSeed (P : MLWE.Params) (Seed : Type) [Fintype Seed]
    [Nonempty Seed] (dA : SDistr P.Mat) (adv : Seed → P.Mat → P.Vec → SDistr Bool) :
    ℝ≥0∞ :=
  absDiff (prTrue (gameSeed P Seed dA adv false)) (prTrue (gameSeed P Seed dA adv true))

/-- With a uniform matrix, `gameSeed` is `MLWE.Game` for the distinguisher that
draws `ρ` itself. -/
theorem gameSeed_uniform (P : MLWE.Params) (Seed : Type) [Fintype Seed] [Nonempty Seed]
    (adv : Seed → P.Mat → P.Vec → SDistr Bool) (b : Bool) :
    gameSeed P Seed (SDistr.uniform P.Mat) adv b =
      MLWE.Game P (fun A t => (SDistr.uniform Seed).bind fun ρ => adv ρ A t) b := by
  cases b
  · show (SDistr.uniform Seed).bind (fun ρ => (SDistr.uniform P.Mat).bind fun A =>
        P.dshort_vec.bind fun s => P.dshort_vec.bind fun e =>
          adv ρ A (P.vec_add (P.mat_vec_mul A s) e)) =
      (SDistr.uniform P.Mat).bind fun A => P.dshort_vec.bind fun s =>
        P.dshort_vec.bind fun e => (SDistr.uniform Seed).bind fun ρ =>
          adv ρ A (P.vec_add (P.mat_vec_mul A s) e)
    rw [SDistr.bind_comm]
    congr 1; funext A
    rw [SDistr.bind_comm]
    congr 1; funext s
    rw [SDistr.bind_comm]
  · show (SDistr.uniform Seed).bind (fun ρ => (SDistr.uniform P.Mat).bind fun A =>
        (SDistr.uniform P.Vec).bind fun u => adv ρ A u) =
      (SDistr.uniform P.Mat).bind fun A => (SDistr.uniform P.Vec).bind fun u =>
        (SDistr.uniform Seed).bind fun ρ => adv ρ A u
    rw [SDistr.bind_comm]
    congr 1; funext A
    rw [SDistr.bind_comm]

/-- **Stage 3 with the seed.** A distinguisher that also receives the seed `ρ`
has, against the XOF-expanded matrix, advantage within `2 k² · nonFillProb m`
of the uniform-matrix `MLWE.advantage` of the distinguisher that draws `ρ`
itself. -/
theorem mlwe_advantage_xofMatrix_seed_le (P : MLWE.Params) (Seed : Type) [Fintype Seed]
    [Nonempty Seed] (k m : ℕ) (e : Mat k ≃ P.Mat)
    (adv : Seed → P.Mat → P.Vec → SDistr Bool) :
    advantageSeed P Seed (xofMatrixDistVia (m := m) e) adv ≤
      MLWE.advantage P (fun A t => (SDistr.uniform Seed).bind fun ρ => adv ρ A t) +
        2 * (((k * k : ℕ) : ℝ≥0∞) * nonFillProb m) := by
  have h := xofMatrixDistVia_minorant (m := m) e
  have key : ∀ b,
      prTrue (gameSeed P Seed (xofMatrixDistVia (m := m) e) adv b) ≤
          prTrue (gameSeed P Seed (SDistr.uniform P.Mat) adv b) +
            ((k * k : ℕ) : ℝ≥0∞) * nonFillProb m ∧
        prTrue (gameSeed P Seed (SDistr.uniform P.Mat) adv b) ≤
          prTrue (gameSeed P Seed (xofMatrixDistVia (m := m) e) adv b) +
            ((k * k : ℕ) : ℝ≥0∞) * nonFillProb m := fun b =>
    ⟨prTrue_bind_le_of_forall _ _ _ _ fun ρ => (prTrue_bind_close _ _ h _).1,
      prTrue_bind_le_of_forall _ _ _ _ fun ρ => (prTrue_bind_close _ _ h _).2⟩
  have hadv := absDiff_le_of_close (key false).1 (key false).2 (key true).1 (key true).2
  rw [advantageSeed]
  simp only [gameSeed_uniform] at hadv
  exact hadv

end CatCrypt.Crypto.MLKEM.XOFMatrix
