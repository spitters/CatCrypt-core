/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Constructions.ECBCPRFFlag
public import CatCryptCore.Crypto.Constructions.MACDomainExtension
public import CatCryptCore.Crypto.PRPPRFSwitching
public import CatCryptCore.Crypto.EagerLazyRF
public import CatCryptCore.Crypto.HashThenRF
public import CatCryptCore.Crypto.OracleSubst
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# ECBC-MAC is a PRF

ECBC-MAC over messages of at most `ℓ` blocks is `ecbc E iv ℓ (k₁, k₂) M =
E k₂ (cbc (E k₁) iv M)`. Against an adaptive adversary with at most `q` queries,
in the games of `CatCryptCore.Crypto.PRPPRFSwitching`, its PRF advantage is at most
the PRP advantages of `E` against two explicit reductions plus
`(q(q-1)/2 + qℓ(qℓ-1)/2 + 2(qℓ)²) / |B|` (Black–Rogaway 2000; Bellare–Kilian–Rogaway).

## Main definitions

* `ecbc` — ECBC-MAC on messages `Msg B ℓ` of at most `ℓ` blocks
* `ecbcOuterAdv E iv A` — samples `k₁` and queries its oracle at the CBC value
  of each message
* `ecbcInnerAdv iv A` — samples a function `f₂ : B → B`, computes the CBC chain of
  each message with its oracle and answers with `f₂`
* `cbc`, `cbcR`, `cbcIn` — CBC chains and chain inputs

## Main results

* `ecbc_prf_bound` — the PRF bound for ECBC-MAC
* `prob_not_injOn_cbc_le` — for a uniform `f : B → B` and a set `S` of messages
  of at most `ℓ` blocks, the CBC chain is injective on `S` except with probability
  `2(|S|ℓ)² / |B|`
* `uniform_prob_fresh_le` — a value of a uniform function at a point, from a set of
  at most `v` values, both independent of that value, has probability at most
  `v / |R|`

## Proof

Three hops. `E k₂` is replaced by a uniform `f₂` through `ecbcOuterAdv`, then `E k₁`
by a uniform `f₁` through `ecbcInnerAdv`, each costing a PRP advantage and a
switching term (`PRF_q_Advantage_le`). For the last hop, `f₂` is a lazy random
function queried at `cbc f₁ iv M`; it agrees with a lazy random function on
messages until two distinct queried messages have the same CBC value
(`HashThenRF.advantage_compose_le`). The collision probability over `f₁` for the final
message table is bounded by revealing the values of `f₁` along the tree of
prefixes of the queried messages, longest prefix last (`prob_not_good_le`): each
revealed value is fresh and must avoid at most `n + 1 + (children) · n` values,
where `n ≤ qℓ` is the number of nonempty prefixes.

The reduction `ecbcInnerAdv` samples the outer function eagerly; it is a valid
adversary in the information-theoretic games used here and makes at most `qℓ`
queries.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Constructions.ECBCPRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.HashThenRF (advantage_compose_le tsum_run_rfOracle_le)
open CatCrypt.Crypto.OracleAdv (QueryCollision)
open scoped ENNReal

/-! ## Resampling a single point -/

section Fresh

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]

/-- **Fresh point.** Let `X` be an event, `p` a point and `V` a set of at most `v`
values, none of which depends on the value of `f` at `p f` while `X` holds. Then
the uniform `f` satisfies `X` and takes a value in `V f` at `p f` with probability
at most `v / |R|`. -/
theorem uniform_prob_fresh_le (X : (D → R) → Prop) (p : (D → R) → D)
    (V : (D → R) → Finset R) (v : ℕ) (hV : ∀ f, X f → (V f).card ≤ v)
    (hinv : ∀ f, X f → ∀ r, X (Function.update f (p f) r) ∧
      p (Function.update f (p f) r) = p f ∧ V (Function.update f (p f) r) = V f) :
    (PMF.uniformFintype (D → R)).toOuterMeasure {f | X f ∧ f (p f) ∈ V f} ≤
      (v : ℝ≥0∞) / Fintype.card R := by
  classical
  rw [PMF.toOuterMeasure_uniformFintype_apply]
  set E : Finset (D → R) := Finset.univ.filter fun f => X f ∧ f (p f) ∈ V f with hE
  have hcardE : Fintype.card ↥{f : D → R | X f ∧ f (p f) ∈ V f} = E.card := by
    rw [hE, ← Fintype.card_subtype]
    rfl
  set T : Finset ((D → R) × R) := Finset.univ.filter fun x => X x.1 ∧ x.2 ∈ V x.1 with hT
  have hET : E.card * Fintype.card R ≤ T.card * 1 := by
    refine Finset.card_mul_le_card_mul (fun g x => Function.update x.1 (p x.1) x.2 = g) ?_ ?_
    · intro g hg
      simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      rw [← Finset.card_univ (α := R)]
      refine le_of_eq_of_le (Finset.card_image_of_injective _ (f := fun s =>
        (Function.update g (p g) s, g (p g))) ?_).symm (Finset.card_le_card ?_)
      · intro s s' h
        simpa using congrArg (fun x => x.1 (p g)) h
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨s, rfl⟩ := hx
        obtain ⟨hX', hp', hV'⟩ := hinv g hg.1 s
        simp only [Finset.bipartiteAbove, hT, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨hX', by rw [hV']; exact hg.2⟩, ?_⟩
        rw [hp']
        simp
    · intro x hx
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      simp only [Finset.bipartiteBelow, Finset.mem_filter] at ha hb
      exact ha.2.symm.trans hb.2
  have hTle : T.card ≤ Fintype.card (D → R) * v := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine (Finset.sum_le_card_nsmul _ _ v fun f _ => ?_).trans (by simp)
    by_cases hf : X f
    · refine (Finset.card_le_card_of_injOn Prod.snd (fun x hx => ?_) ?_).trans (hV f hf)
      · simp only [hT, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Finset.mem_coe]
        rw [← hx.2]; exact hx.1.2
      · intro x hx y hy h
        simp only [hT, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        exact Prod.ext (hx.2.trans hy.2.symm) h
    · refine (Finset.card_eq_zero.mpr ?_).le.trans (Nat.zero_le _)
      ext x
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_and]
      intro hx hx1; exact hf (hx1 ▸ hx.1)
  have hN0 : (Fintype.card R : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hF0 : (Fintype.card (D → R) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hnat : E.card * Fintype.card R ≤ v * Fintype.card (D → R) :=
    (hET.trans_eq (mul_one _)).trans (hTle.trans_eq (mul_comm _ _))
  rw [hcardE]
  calc (E.card : ℝ≥0∞) / Fintype.card (D → R)
      = (E.card * Fintype.card R : ℕ) / (Fintype.card R * Fintype.card (D → R) : ℕ) := by
        push_cast
        rw [mul_comm (Fintype.card R : ℝ≥0∞), ENNReal.mul_div_mul_right _ _ hN0
          (ENNReal.natCast_ne_top _)]
    _ ≤ (v * Fintype.card (D → R) : ℕ) / (Fintype.card R * Fintype.card (D → R) : ℕ) := by
        gcongr
    _ = (v : ℝ≥0∞) / Fintype.card R := by
        push_cast
        rw [ENNReal.mul_div_mul_right _ _ hF0 (ENNReal.natCast_ne_top _)]

end Fresh

/-! ## CBC chains -/

section CBC

variable {B : Type} [CryptoWord B]

/-- CBC chain of `f` from `iv` over the blocks of `M`: `sᵢ = f (sᵢ₋₁ ⊕ mᵢ)`. -/
def cbc (f : B → B) (iv : B) (M : List B) : B :=
  M.foldl (fun s m => f (CryptoWord.wxor s m)) iv

/-- CBC chain over a block list written last block first. -/
def cbcR (f : B → B) (iv : B) : List B → B
  | [] => iv
  | c :: r => f (CryptoWord.wxor (cbcR f iv r) c)

/-- The input to `f` at the last block of a block list written last block first. -/
def cbcIn (f : B → B) (iv : B) : List B → B
  | [] => iv
  | c :: r => CryptoWord.wxor (cbcR f iv r) c

theorem cbc_eq_cbcR (f : B → B) (iv : B) (M : List B) : cbc f iv M = cbcR f iv M.reverse := by
  induction M using List.reverseRecOn with
  | nil => rfl
  | append_singleton M c ih =>
    simp only [cbc, List.foldl_append, List.foldl_cons, List.foldl_nil, List.reverse_append,
      List.reverse_singleton, List.singleton_append, cbcR] at ih ⊢
    rw [ih]

theorem cbcR_cons (f : B → B) (iv c : B) (r : List B) :
    cbcR f iv (c :: r) = f (cbcIn f iv (c :: r)) := rfl

theorem raw_cbcmac_eq_cbc (E : MACDomainExtension.BlockCipherDef B) (k iv : B) (M : List B) :
    MACDomainExtension.raw_cbcmac E k iv M = cbc (E.enc k) iv M := by
  induction M generalizing iv with
  | nil => rfl
  | cons m M ih => simp only [MACDomainExtension.raw_cbcmac_cons, ih, cbc, List.foldl_cons]

/-! ### Collisions among CBC values of a tail-closed set -/

/-- Every element of `R` is nonempty and its tail is empty or in `R`. -/
def TailClosed (R : Finset (List B)) : Prop :=
  ∀ Q ∈ R, Q ≠ [] ∧ (Q.tail = [] ∨ Q.tail ∈ R)

/-- The elements of `NP` whose `f`-input is determined by the values on `R`. -/
def det (NP R : Finset (List B)) : Finset (List B) :=
  NP.filter fun Q => Q.tail ∈ insert [] R

/-- The children of `P` in `NP`. -/
def children (NP : Finset (List B)) (P : List B) : Finset (List B) :=
  NP.filter fun Q => Q.tail = P

/-- CBC values are injective on `R ∪ {[]}` and inputs are injective on `det NP R`. -/
def Good (iv : B) (NP R : Finset (List B)) (f : B → B) : Prop :=
  Set.InjOn (cbcR f iv) ↑(insert [] R) ∧ Set.InjOn (cbcIn f iv) ↑(det NP R)

/-- The values of `f` at the input of `P` that break `Good` when `P` is added to
`R`: the values already taken on `R ∪ {[]}`, and the values giving a child of `P`
an input already taken on `det NP R`. -/
def danger (iv : B) (NP R : Finset (List B)) (P : List B) (f : B → B) : Finset B :=
  (insert [] R).image (cbcR f iv) ∪ (children NP P).biUnion fun Q =>
    Finset.univ.filter fun y => CryptoWord.wxor y (Q.headD iv) ∈ (det NP R).image (cbcIn f iv)

theorem card_danger_le (iv : B) (NP R : Finset (List B)) (P : List B) (f : B → B) :
    (danger iv NP R P f).card ≤ (R.card + 1) + (children NP P).card * NP.card := by
  refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
  · exact Finset.card_image_le.trans (Finset.card_insert_le _ _)
  · refine Finset.card_biUnion_le.trans (Finset.sum_le_card_nsmul _ _ _ fun Q _ => ?_)
    refine (Finset.card_le_card_of_injOn (fun y => CryptoWord.wxor y (Q.headD iv))
      (fun y hy => Finset.mem_coe.mpr (Finset.mem_filter.mp hy).2)
      (fun y _ y' _ h => CryptoWord.wxor_right_injective _ h)).trans ?_
    exact Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _))

theorem mem_det_iff (NP R : Finset (List B)) (Q : List B) :
    Q ∈ det NP R ↔ Q ∈ NP ∧ (Q.tail = [] ∨ Q.tail ∈ R) := by
  simp [det]

/-- On `Good`, resampling `f` at the input of an element of `det NP R` outside `R`
changes no CBC value on `R ∪ {[]}`. -/
theorem cbcR_update_eq (iv : B) (NP R : Finset (List B)) (hR : R ⊆ NP) (hRc : TailClosed R)
    (P : List B) (hP : P ∈ det NP R) (hPR : P ∉ R) (f : B → B) (hG : Good iv NP R f) (y : B) :
    ∀ Q ∈ insert [] R, cbcR (Function.update f (cbcIn f iv P) y) iv Q = cbcR f iv Q := by
  intro Q hQ
  induction Q with
  | nil => rfl
  | cons c t ih =>
    have hQR : c :: t ∈ R := by simpa using hQ
    have ht : t ∈ insert [] R := by
      rcases (hRc _ hQR).2 with h | h
      · simp [show t = [] from h]
      · simp [show t ∈ R from h]
    have hQdet : c :: t ∈ det NP R := by
      rw [mem_det_iff]
      exact ⟨hR hQR, by simpa using (hRc _ hQR).2⟩
    have hne : cbcIn f iv (c :: t) ≠ cbcIn f iv P := by
      intro h
      exact hPR (hG.2 hQdet hP h ▸ hQR)
    simp only [cbcR]
    rw [ih ht, Function.update_of_ne]
    exact hne

theorem cbcIn_update_eq (iv : B) (NP R : Finset (List B)) (hR : R ⊆ NP) (hRc : TailClosed R)
    (hNP : TailClosed NP)
    (P : List B) (hP : P ∈ det NP R) (hPR : P ∉ R) (f : B → B) (hG : Good iv NP R f) (y : B) :
    ∀ Q ∈ det NP R, cbcIn (Function.update f (cbcIn f iv P) y) iv Q = cbcIn f iv Q := by
  intro Q hQ
  rw [mem_det_iff] at hQ
  match Q, hQ with
  | [], hQ => exact absurd rfl (hNP _ hQ.1).1
  | c :: t, hQ =>
    have ht : t ∈ insert [] R := by grind
    rw [cbcIn.eq_2, cbcIn.eq_2, cbcR_update_eq iv NP R hR hRc P hP hPR f hG y t ht]

theorem good_update (iv : B) (NP R : Finset (List B)) (hR : R ⊆ NP) (hRc : TailClosed R)
    (hNP : TailClosed NP)
    (P : List B) (hP : P ∈ det NP R) (hPR : P ∉ R) (f : B → B) (hG : Good iv NP R f) (y : B) :
    Good iv NP R (Function.update f (cbcIn f iv P) y) ∧
      cbcIn (Function.update f (cbcIn f iv P) y) iv P = cbcIn f iv P ∧
      danger iv NP R P (Function.update f (cbcIn f iv P) y) = danger iv NP R P f := by
  have hv := cbcR_update_eq iv NP R hR hRc P hP hPR f hG y
  have hi := cbcIn_update_eq iv NP R hR hRc hNP P hP hPR f hG y
  refine ⟨⟨hG.1.congr fun Q hQ => (hv Q hQ).symm, hG.2.congr fun Q hQ => (hi Q hQ).symm⟩,
    hi P hP, ?_⟩
  unfold danger
  rw [Finset.image_congr fun Q hQ => hv Q hQ, Finset.image_congr fun Q hQ => hi Q hQ]

/-- Adding `P ∈ det NP R` to `R` keeps `Good` unless `f` at the input of `P` lies in
the danger set. -/
theorem good_insert (iv : B) (NP R : Finset (List B)) (hNP : TailClosed NP)
    (P : List B) (hP : P ∈ det NP R) (hPR : P ∉ R) (f : B → B) (hG : Good iv NP R f)
    (hf : f (cbcIn f iv P) ∉ danger iv NP R P f) : Good iv NP (insert P R) f := by
  have hPne : P ≠ [] := (hNP _ (Finset.mem_filter.mp hP).1).1
  obtain ⟨c, t, rfl⟩ : ∃ c t, P = c :: t := List.exists_cons_of_ne_nil hPne
  simp only [danger, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_exists, not_and] at hf
  constructor
  · rw [Finset.insert_comm, Finset.coe_insert, Set.injOn_insert (by simpa using hPR)]
    refine ⟨hG.1, ?_⟩
    rintro ⟨Q, hQ, hQv⟩
    exact hf.1 Q hQ (by rw [hQv, cbcR_cons])
  · intro Q₁ hQ₁ Q₂ hQ₂ heq
    have hmem : ∀ Q ∈ det NP (insert (c :: t) R),
        Q ∈ det NP R ∨ (Q ∈ children NP (c :: t)) := by
      intro Q hQ
      simp only [det, children, Finset.mem_filter, Finset.mem_insert] at hQ ⊢
      rcases hQ.2 with h | h | h
      · exact Or.inl ⟨hQ.1, Or.inl h⟩
      · exact Or.inr ⟨hQ.1, h⟩
      · exact Or.inl ⟨hQ.1, Or.inr h⟩
    have hchild : ∀ Q ∈ children NP (c :: t), ∃ c', Q = c' :: c :: t := by
      intro Q hQ
      simp only [children, Finset.mem_filter] at hQ
      match Q, hQ with
      | [], hQ => exact absurd rfl (hNP _ hQ.1).1
      | c' :: t', hQ => exact ⟨c', by simp only [List.tail_cons] at hQ; rw [hQ.2]⟩
    have hcross : ∀ Q ∈ children NP (c :: t), ∀ Q' ∈ det NP R,
        cbcIn f iv Q ≠ cbcIn f iv Q' := by
      intro Q hQ Q' hQ' h
      obtain ⟨c', rfl⟩ := hchild Q hQ
      refine hf.2 _ hQ Q' hQ' ?_
      simp only [cbcIn, cbcR_cons, List.headD_cons] at h ⊢
      exact h.symm
    rcases hmem Q₁ hQ₁ with h₁ | h₁ <;> rcases hmem Q₂ hQ₂ with h₂ | h₂
    · exact hG.2 h₁ h₂ heq
    · exact absurd heq (fun h => hcross Q₂ h₂ Q₁ h₁ h.symm)
    · exact absurd heq (hcross Q₁ h₁ Q₂ h₂)
    · obtain ⟨c₁, rfl⟩ := hchild Q₁ h₁
      obtain ⟨c₂, rfl⟩ := hchild Q₂ h₂
      simp only [cbcIn] at heq
      rw [CryptoWord.wxor_left_injective _ heq]

theorem good_empty (iv : B) (NP : Finset (List B)) (hNP : TailClosed NP) (f : B → B) :
    Good iv NP ∅ f := by
  refine ⟨by simp, fun Q₁ hQ₁ Q₂ hQ₂ heq => ?_⟩
  simp only [Finset.mem_coe, mem_det_iff, Finset.notMem_empty, or_false] at hQ₁ hQ₂
  match Q₁, Q₂, hQ₁, hQ₂ with
  | [], _, h, _ => exact absurd rfl (hNP _ h.1).1
  | _, [], _, h => exact absurd rfl (hNP _ h.1).1
  | c₁ :: t₁, c₂ :: t₂, h₁, h₂ =>
    simp only [List.tail_cons] at h₁ h₂
    obtain ⟨-, rfl⟩ := h₁
    obtain ⟨-, rfl⟩ := h₂
    simp only [cbcIn, cbcR] at heq
    rw [CryptoWord.wxor_left_injective _ heq]

/-- The children counts of the elements of a tail-closed `NP` sum to at most `NP.card`. -/
theorem sum_card_children_le (NP : Finset (List B)) :
    ∑ P ∈ NP, (children NP P).card ≤ NP.card := by
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_card (Finset.biUnion_subset.mpr fun P _ => Finset.filter_subset _ _)
  · intro P _ P' _ hne
    refine Finset.disjoint_left.mpr fun Q hQ hQ' => hne ?_
    simp only [children, Finset.mem_filter] at hQ hQ'
    exact hQ.2.symm.trans hQ'.2

/-- For a tail-closed `R ⊆ NP` with `n` elements, `Good iv NP R` fails for a uniform
`f` with probability at most `(∑ k < n, (k + 1) + |NP| · ∑ P ∈ R, |children P|) / |B|`. -/
theorem prob_not_good_le (iv : B) (NP : Finset (List B)) (hNP : TailClosed NP) :
    ∀ (n : ℕ) (R : Finset (List B)), R.card = n → R ⊆ NP → TailClosed R →
      (PMF.uniformFintype (B → B)).toOuterMeasure {f | ¬ Good iv NP R f} ≤
        ((∑ k ∈ Finset.range n, (k + 1) + NP.card * ∑ P ∈ R, (children NP P).card : ℕ) :
          ℝ≥0∞) / Fintype.card B := by
  intro n
  induction n with
  | zero =>
    intro R hR _ _
    rw [Finset.card_eq_zero] at hR
    subst hR
    have h : {f : B → B | ¬ Good iv NP ∅ f} = ∅ :=
      Set.eq_empty_of_forall_notMem fun f hf => hf (good_empty iv NP hNP f)
    rw [h, MeasureTheory.measure_empty]
    exact zero_le
  | succ n ih =>
    intro R hcard hRNP hRc
    have hne : R.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨P, hPR, hPmax⟩ := Finset.exists_max_image R List.length hne
    have hlen : ∀ Q ∈ R, Q.length = Q.tail.length + 1 := by
      intro Q hQ
      cases Q with
      | nil => exact absurd rfl (hRc _ hQ).1
      | cons _ _ => simp
    have hR'card : (R.erase P).card = n := by rw [Finset.card_erase_of_mem hPR]; omega
    have hR'NP : R.erase P ⊆ NP := (Finset.erase_subset _ _).trans hRNP
    have hR'c : TailClosed (R.erase P) := by
      intro Q hQ
      have hQR := Finset.mem_of_mem_erase hQ
      refine ⟨(hRc Q hQR).1, ?_⟩
      rcases (hRc Q hQR).2 with h | h
      · exact Or.inl h
      · refine Or.inr (Finset.mem_erase.mpr ⟨fun hQP => ?_, h⟩)
        have h1 := hPmax Q hQR
        have h2 := hlen Q hQR
        rw [hQP] at h2
        omega
    have hPdet : P ∈ det NP (R.erase P) := by
      rw [mem_det_iff]
      refine ⟨hRNP hPR, ?_⟩
      rcases (hRc P hPR).2 with h | h
      · exact Or.inl h
      · refine Or.inr (Finset.mem_erase.mpr ⟨fun h' => ?_, h⟩)
        have h2 := hlen P hPR
        rw [h'] at h2
        omega
    have hPR' : P ∉ R.erase P := Finset.notMem_erase P R
    have hsub : {f : B → B | ¬ Good iv NP R f} ⊆ {f | ¬ Good iv NP (R.erase P) f} ∪
        {f | Good iv NP (R.erase P) f ∧ f (cbcIn f iv P) ∈ danger iv NP (R.erase P) P f} := by
      intro f hf
      by_cases hG : Good iv NP (R.erase P) f
      · refine Or.inr ⟨hG, ?_⟩
        by_contra hd
        have := good_insert iv NP (R.erase P) hNP P hPdet hPR' f hG hd
        rw [Finset.insert_erase hPR] at this
        exact hf this
      · exact Or.inl hG
    refine (MeasureTheory.measure_mono hsub).trans
      ((MeasureTheory.measure_union_le _ _).trans ?_)
    refine (add_le_add (ih _ hR'card hR'NP hR'c)
      (uniform_prob_fresh_le (Good iv NP (R.erase P)) (fun f => cbcIn f iv P)
        (danger iv NP (R.erase P) P) ((R.erase P).card + 1 + (children NP P).card * NP.card)
        (fun f _ => card_danger_le iv NP _ P f)
        (fun f hG r => good_update iv NP _ hR'NP hR'c hNP P hPdet hPR' f hG r))).trans ?_
    rw [ENNReal.div_add_div_same, ← Nat.cast_add]
    refine le_of_eq (congrArg (fun m : ℕ => (m : ℝ≥0∞) / Fintype.card B) ?_)
    rw [Finset.sum_range_succ, ← Finset.add_sum_erase R _ hPR, hR'card]
    ring

/-- **CBC collision bound.** For a set `S` of messages of at most `ℓ` blocks each,
the CBC chain of a uniform random function `f : B → B` from `iv` fails to be
injective on `S` with probability at most `2 (|S| ℓ)² / |B|`. -/
theorem prob_not_injOn_cbc_le (iv : B) (S : Finset (List B)) (ℓ : ℕ)
    (hS : ∀ M ∈ S, M.length ≤ ℓ) :
    (PMF.uniformFintype (B → B)).toOuterMeasure {f | ¬ Set.InjOn (cbc f iv) ↑S} ≤
      ((2 * (S.card * ℓ) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card B := by
  classical
  set NP : Finset (List B) :=
    (S.biUnion fun M => M.reverse.tails.toFinset).erase [] with hNPdef
  have hmemNP : ∀ Q, Q ∈ NP ↔ Q ≠ [] ∧ ∃ M ∈ S, Q <:+ M.reverse := by
    intro Q
    simp [hNPdef, List.mem_tails]
  have hNP : TailClosed NP := by
    intro Q hQ
    obtain ⟨hne, M, hM, hsuf⟩ := (hmemNP Q).mp hQ
    refine ⟨hne, ?_⟩
    by_cases ht : Q.tail = []
    · exact Or.inl ht
    · exact Or.inr ((hmemNP _).mpr ⟨ht, M, hM, (List.tail_suffix Q).trans hsuf⟩)
  have hcardNP : NP.card ≤ S.card * ℓ := by
    refine (Finset.card_le_card (t := S.biUnion fun M => M.reverse.tails.toFinset.erase [])
      ?_).trans ?_
    · intro Q hQ
      obtain ⟨hne, M, hM, hs⟩ := (hmemNP Q).mp hQ
      simp only [Finset.mem_biUnion, Finset.mem_erase, List.mem_toFinset, List.mem_tails]
      exact ⟨M, hM, hne, hs⟩
    · refine Finset.card_biUnion_le.trans (Finset.sum_le_card_nsmul _ _ _ fun M hM => ?_)
      rw [Finset.card_erase_of_mem (by simp [List.mem_tails])]
      have h1 := List.toFinset_card_le M.reverse.tails
      simp only [List.length_tails, List.length_reverse] at h1
      have h2 := hS M hM
      omega
  have hgood := prob_not_good_le iv NP hNP NP.card NP rfl subset_rfl hNP
  refine (MeasureTheory.measure_mono ?_).trans (hgood.trans ?_)
  · intro f hf hG
    apply hf
    intro M hM M' hM' heq
    rw [cbc_eq_cbcR, cbc_eq_cbcR] at heq
    have hmem : ∀ M ∈ S, M.reverse ∈ (↑(insert [] NP) : Set (List B)) := by grind
    exact List.reverse_injective (hG.1 (hmem M hM) (hmem M' hM') heq)
  · refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
    have h1 : ∑ k ∈ Finset.range NP.card, (k + 1) ≤ NP.card * NP.card := by
      refine (Finset.sum_le_card_nsmul _ _ NP.card fun k hk => ?_).trans (by simp)
      simp only [Finset.mem_range] at hk
      omega
    have h2 := sum_card_children_le NP
    calc ∑ k ∈ Finset.range NP.card, (k + 1) + NP.card * ∑ P ∈ NP, (children NP P).card
        ≤ NP.card * NP.card + NP.card * NP.card := add_le_add h1 (Nat.mul_le_mul_left _ h2)
      _ = 2 * NP.card ^ 2 := by ring
      _ ≤ 2 * (S.card * ℓ) ^ 2 := by gcongr

end CBC

/-! ## ECBC-MAC -/

section ECBC

variable {B K : Type} [CryptoWord B] [Fintype K] [Nonempty K]

/-- Messages of at most `ℓ` blocks. -/
abbrev Msg (B : Type) (ℓ : ℕ) : Type := {M : List B // M.length ≤ ℓ}

/-- ECBC-MAC over messages of at most `ℓ` blocks with the key pair `(k₁, k₂)`:
`E k₂ (cbc (E k₁) iv M)`. -/
def ecbc (E : K → B → B) (iv : B) (ℓ : ℕ) (k : K × K) (M : Msg B ℓ) : B :=
  E k.2 (cbc (E k.1) iv M.1)

theorem ecbc_eq_ecbc_eval (W : Type) [CryptoWord W] (E : MACDomainExtension.ECBCMAC W)
    (iv : W) (ℓ : ℕ) (k₁ k₂ : W) (M : Msg W ℓ) :
    ecbc E.cipher.enc iv ℓ (k₁, k₂) M = MACDomainExtension.ecbc_eval E k₁ k₂ iv M.1 := by
  simp [ecbc, MACDomainExtension.ecbc_eval, raw_cbcmac_eq_cbc]

/-- The adversary computing `g` of the CBC chain from `s` over `ms` by querying its
oracle at each chain input. -/
def cbcAdv (g : B → B) : B → List B → OracleAdv B B B
  | s, [] => .ret (g s)
  | s, m :: ms => .query (CryptoWord.wxor s m) fun r => cbcAdv g r ms

theorem run_keyed_cbcAdv {K' : Type} (F : K' → B → B) (k : K') (g : B → B) (s : B)
    (ms : List B) (u : Unit) :
    OracleAdv.run (keyedOracle F k) (cbcAdv g s ms) u = PMF.pure (g (cbc (F k) s ms), ()) := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih => simp only [cbcAdv, OracleAdv.run_query, keyedOracle, PMF.pure_bind, ih]; rfl

theorem isQueryBound_cbcAdv (g : B → B) (s : B) (ms : List B) :
    (cbcAdv g s ms).IsQueryBound ms.length := by
  induction ms generalizing s with
  | nil => trivial
  | cons m ms ih => exact fun r => ih r

/-- Reduction to the PRP security of the outer cipher: sample `k₁` and answer each
message query with one oracle query at its CBC value under `E k₁`. -/
noncomputable def ecbcOuterAdv (E : K → B → B) (iv : B) {ℓ : ℕ}
    (A : OracleAdv (Msg B ℓ) B Bool) : OracleAdv B B Bool :=
  .rand (PMF.uniformFintype K) fun k₁ => OracleAdv.mapQuery (fun M => cbc (E k₁) iv M.1) A

/-- Reduction to the PRP security of the inner cipher: sample a function `f₂` and
answer each message query `M` by computing the CBC chain of `M` with oracle queries
and applying `f₂`. -/
noncomputable def ecbcInnerAdv (iv : B) {ℓ : ℕ} (A : OracleAdv (Msg B ℓ) B Bool) :
    OracleAdv B B Bool :=
  .rand (PMF.uniformFintype (B → B)) fun f₂ =>
    OracleAdv.subst (fun M => cbcAdv f₂ iv M.1) A

theorem isQueryBound_ecbcOuterAdv (E : K → B → B) (iv : B) {ℓ q : ℕ}
    {A : OracleAdv (Msg B ℓ) B Bool} (hA : A.IsQueryBound q) :
    (ecbcOuterAdv E iv A).IsQueryBound q := by
  solve_by_elim [OracleAdv.isQueryBound_mapQuery]

theorem isQueryBound_ecbcInnerAdv (iv : B) {ℓ q : ℕ} {A : OracleAdv (Msg B ℓ) B Bool}
    (hA : A.IsQueryBound q) : (ecbcInnerAdv iv A).IsQueryBound (q * ℓ) :=
  fun f₂ => OracleAdv.isQueryBound_subst
    (fun M => (isQueryBound_cbcAdv f₂ iv M.1).mono M.2) hA

variable {ℓ : ℕ}

/-- The real game of ECBC is the real game of `E` against the outer reduction. -/
theorem realGame_ecbc_eq (E : K → B → B) (iv : B) (A : OracleAdv (Msg B ℓ) B Bool) :
    realGame (ecbc E iv ℓ) A = realGame E (ecbcOuterAdv E iv A) := by
  unfold realGame ecbcOuterAdv
  congr 1
  simp only [OracleAdv.run_rand, OracleAdv.run_mapQuery, PMF.map_bind]
  rw [PMF.uniform_prod_eq_bind, PMF.bind_comm (PMF.uniformFintype K), PMF.bind_bind]
  refine congrArg _ (funext fun k₁ => ?_)
  rw [PMF.bind_map]
  rfl

/-- The hybrid with the inner cipher `E k₁` and a uniform outer function `f₂`. -/
noncomputable def hybridOuter (E : K → B → B) (iv : B) (A : OracleAdv (Msg B ℓ) B Bool) :
    SPComp Bool :=
  liftPMF ((PMF.uniformFintype (B → B)).bind fun f₂ => (PMF.uniformFintype K).bind
    fun k₁ => (OracleAdv.run (fun _ M => PMF.pure (f₂ (cbc (E k₁) iv M.1), ())) A ()).map
      Prod.fst)

/-- The hybrid with uniform inner and outer functions `f₁` and `f₂`. -/
noncomputable def hybridBoth (iv : B) (A : OracleAdv (Msg B ℓ) B Bool) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype (B → B)).bind fun f₁ =>
    (OracleAdv.run (fun t M => rfOracle t (cbc f₁ iv M.1)) A []).map Prod.fst)

theorem rfGame_ecbcOuterAdv_eq (E : K → B → B) (iv : B) (A : OracleAdv (Msg B ℓ) B Bool) :
    rfGame (ecbcOuterAdv E iv A) = hybridOuter E iv A := by
  rw [← realGame_apply_eq_rfGame]
  unfold realGame hybridOuter ecbcOuterAdv
  simp only [OracleAdv.run_rand, OracleAdv.run_mapQuery, PMF.map_bind]
  rfl

theorem realGame_ecbcInnerAdv_eq (E : K → B → B) (iv : B) (A : OracleAdv (Msg B ℓ) B Bool) :
    realGame E (ecbcInnerAdv iv A) = hybridOuter E iv A := by
  unfold realGame hybridOuter ecbcInnerAdv
  congr 1
  simp only [OracleAdv.run_rand, OracleAdv.run_subst, run_keyed_cbcAdv, PMF.map_bind]
  rw [PMF.bind_comm]

theorem rfGame_ecbcInnerAdv_eq (iv : B) (A : OracleAdv (Msg B ℓ) B Bool) :
    rfGame (ecbcInnerAdv iv A) = hybridBoth iv A := by
  rw [← realGame_apply_eq_rfGame]
  unfold realGame hybridBoth ecbcInnerAdv
  congr 1
  refine congrArg _ (funext fun f₁ => ?_)
  simp only [OracleAdv.run_rand, OracleAdv.run_subst, run_keyed_cbcAdv, PMF.map_bind]
  have h := uniform_bind_run_keyed_map_fst
    (OracleAdv.mapQuery (fun M : Msg B ℓ => cbc f₁ iv M.1) A)
  simp only [OracleAdv.run_mapQuery] at h
  exact h

/-- The collision term: for a uniform `f₁`, the CBC chain is injective on the
queries of an adversary asking at most `q` queries except with probability
`2 (q ℓ)² / |B|`. -/
theorem advantage_hybridBoth_le (iv : B) (A : OracleAdv (Msg B ℓ) B Bool) (q : ℕ)
    (hA : A.IsQueryBound q) :
    Advantage (hybridBoth iv A) (rfGame A) ≤
      ((2 * (q * ℓ) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card B := by
  have hmono :
      Monotone fun m : ℕ => ((2 * (m * ℓ) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card B := by
    intro m m' hm
    simp only
    gcongr
  refine (advantage_compose_le (fun (f₁ : B → B) (M : Msg B ℓ) => cbc f₁ iv M.1) A).trans
    ((tsum_run_rfOracle_le (fun T => (PMF.uniformFintype (B → B)).toOuterMeasure
      {φ | QueryCollision (fun M : Msg B ℓ => cbc φ iv M.1) (T.map Prod.fst)}) _ hmono
      (fun T => ?_) A q hA []).trans_eq (by rw [List.length_nil, zero_add]))
  classical
  set S : Finset (List B) := (T.map fun p => p.1.1).toFinset
  have hScard : S.card ≤ T.length :=
    (List.toFinset_card_le _).trans (by simp)
  have hS : ∀ M ∈ S, M.length ≤ ℓ := by
    intro M hM
    simp only [S, List.mem_toFinset, List.mem_map] at hM
    obtain ⟨p, -, rfl⟩ := hM
    exact p.1.2
  refine (MeasureTheory.measure_mono fun f₁ hf => ?_).trans
    ((prob_not_injOn_cbc_le iv S ℓ hS).trans ?_)
  · obtain ⟨x, hx, y, hy, hne, hcoll⟩ := hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hy
    intro hinj
    refine hne (Subtype.ext (hinj ?_ ?_ hcoll))
    · grind [List.mem_toFinset]
    · grind [List.mem_toFinset]
  · gcongr

/-- **ECBC-MAC is a PRF** (Black–Rogaway). For a block cipher `E` and an adversary
asking at most `q` adaptive queries of at most `ℓ` blocks each, the PRF advantage
of ECBC-MAC is at most the PRP advantages of `E` against the outer reduction
`ecbcOuterAdv E iv A` (at most `q` queries) and the inner reduction
`ecbcInnerAdv iv A` (at most `q ℓ` queries) plus
`(q(q-1)/2 + qℓ(qℓ-1)/2 + 2(qℓ)²) / |B|`: two PRP/PRF switching terms and the
CBC collision term. -/
theorem ecbc_prf_bound (E : K → B → B) (iv : B) (A : OracleAdv (Msg B ℓ) B Bool) (q : ℕ)
    (hA : A.IsQueryBound q) :
    PRF_q_Advantage (ecbc E iv ℓ) A ≤
      PRP_q_Advantage E (ecbcOuterAdv E iv A) + PRP_q_Advantage E (ecbcInnerAdv iv A) +
        ((q * (q - 1) / 2 + q * ℓ * (q * ℓ - 1) / 2 + 2 * (q * ℓ) ^ 2 : ℕ) : ℝ≥0∞) /
          Fintype.card B := by
  have h₁ := PRF_q_Advantage_le E (ecbcOuterAdv E iv A) q (isQueryBound_ecbcOuterAdv E iv hA)
  have h₂ := PRF_q_Advantage_le E (ecbcInnerAdv iv A) (q * ℓ) (isQueryBound_ecbcInnerAdv iv hA)
  have h₃ := advantage_hybridBoth_le iv A q hA
  unfold PRF_q_Advantage at h₁ h₂ ⊢
  rw [rfGame_ecbcOuterAdv_eq] at h₁
  rw [realGame_ecbcInnerAdv_eq, rfGame_ecbcInnerAdv_eq] at h₂
  rw [realGame_ecbc_eq]
  calc Advantage (realGame E (ecbcOuterAdv E iv A)) (rfGame A)
      ≤ Advantage (realGame E (ecbcOuterAdv E iv A)) (hybridOuter E iv A) +
          (Advantage (hybridOuter E iv A) (hybridBoth iv A) +
            Advantage (hybridBoth iv A) (rfGame A)) :=
        (advantage_triangle _ _ _).trans (add_le_add le_rfl (advantage_triangle _ _ _))
    _ ≤ _ := by
        refine (add_le_add h₁ (add_le_add h₂ h₃)).trans_eq ?_
        simp only [Nat.cast_add, ENNReal.div_add_div_same.symm]
        ring

end ECBC

end CatCrypt.Crypto.Constructions.ECBCPRF
