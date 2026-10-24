/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SigmaProtocol.SurfaceDeps
public import Mathlib.Algebra.Polynomial.Roots
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# Sigma Protocol: batched verification and AND composition of the `sigma-proofs` extraction

`Extraction/SigmaProofs_haxpipe.lean` is the haxpipeT extraction of the crate
`sigma-proofs-hax`. This file states two further facts about it under the group
interpretation `groupSigmaProofsDeps E` of `SurfaceDeps.lean`, and so at
`defaultSigmaProofsDeps` (ristretto255).

## Main results

* `batch_accept_prob_le` — on a proof the per-equation verifier rejects, the batched verifier
  accepts with probability at most `(m - 1) / |Scalar|` over a uniform `ρ`
* `extAndSigma_eq` — the extracted AND composition of two branches is `linearSigma` of the
  core AND composition of the decoded branches

## Batched verification

`Instance_verifier_with_randomness` checks the `m` verification equations of an instance
with one multi-scalar multiplication: with the randomness `ρ`, it weights equation `j` by
`ρ ^ j` and accepts when the weighted product is the identity. For a commitment array `a`,
a challenge `c` and a response `z`, the defect `defect j` of equation `j` is the discrete
logarithm of `a[j] · image j ^ c · (map z j)⁻¹` for the decoded relation.

* `Instance_verifier_ok_iff_defect` — the per-equation verifier accepts exactly when `a` has
  `m` entries and every defect is zero
* `Instance_verifier_with_randomness_ok_iff` — the batched verifier accepts exactly when `a`
  has `m` entries and `∑ j, ρ ^ j · defect j = 0`
* `Instance_verifier_with_randomness_of_ok` — the batched verifier accepts, for every `ρ`,
  each proof that the per-equation verifier accepts
* `card_batch_accept_le` — for a proof that the per-equation verifier rejects, at most
  `m - 1` values of `ρ` make the batched verifier accept: the weighted sum is the value at
  `ρ` of a nonzero polynomial of degree at most `m - 1`; `batch_accept_prob_le` is the
  bound `(m - 1) / |Scalar|` on the probability over a uniform `ρ`

The statements assume that the element indices of the equations are below the number of
elements (`ElemsInRange`, check (4) of the extracted `validate`) and that the stored image
of each equation is the product `imageComb` of its image terms, which holds for an
instance built by `Instance_new` (`Instance_new_image`).

## AND composition

The extracted AND composition runs the prover, verifier and simulator of each branch of an
`AndInstance`. For two well-formed branches, `extAndSigma` is the Σ-protocol whose
components are the extracted AND functions on the encoded halves of a witness, nonce and
response, with decoded results.

* `extAndSigma_eq` — `extAndSigma` is `linearSigma` of the core AND composition
  `LinearRelation.and` of the decoded branches
* `extAnd_rel_iff` — a witness of the composition is a pair of witnesses of the branches
* `extAnd_complete`, `extAnd_specialSound`, `extAnd_perfectHVZK` — the extracted AND
  composition is complete, special sound and perfect HVZK
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SigmaProtocol.SurfaceDeps.BatchAnd

/-- A loop over `0, 1` is two steps. -/
theorem foldRange_two {α : Type} (init : α) (f : Int → α → α) :
    Hax.foldRange 0 2 init f = f 1 (f 0 init) := by
  rw [show (2 : Int) = ((1 + 1 : ℕ) : Int) by norm_num, Hax.foldRange_succ_cast,
    Hax.foldRange_succ_cast 0, Hax.foldRange_zero_cast]
  simp

/-! ### The extracted AND functions on two branches -/

section Generic

variable [SigmaProofs.SigmaProofsDeps]

theorem AndInstance_prover_commit_two (s₁ s₂ : SigmaProofs.Instance_T)
    (w₁ w₂ r₁ r₂ a₁ a₂ : Array (Array Int)) (st₁ st₂ : Array (Array Int) × Array (Array Int))
    (h₁ : SigmaProofs.Instance_prover_commit s₁ w₁ r₁ = .ok (a₁, st₁))
    (h₂ : SigmaProofs.Instance_prover_commit s₂ w₂ r₂ = .ok (a₂, st₂)) :
    SigmaProofs.AndInstance_prover_commit #[s₁, s₂] #[w₁, w₂] #[r₁, r₂] =
      .ok (#[a₁, a₂], #[st₁, st₂]) := by
  unfold SigmaProofs.AndInstance_prover_commit
  simp [SigmaProofs.«AndInstance.branches», SigmaProofs.«AndWitness.branches», Hax.array_len,
    Hax.bne, Hax.bor, Hax.deref, foldRange_two, Hax.index, h₁, h₂, Hax.push,
    SigmaProofs.AndCommitment, SigmaProofs.AndProverState]

theorem AndInstance_prover_response_two (s₁ s₂ : SigmaProofs.Instance_T)
    (st₁ st₂ : Array (Array Int) × Array (Array Int)) (c : Array Int) (z₁ z₂ : Array (Array Int))
    (h₁ : SigmaProofs.Instance_prover_response s₁ st₁ c = .ok z₁)
    (h₂ : SigmaProofs.Instance_prover_response s₂ st₂ c = .ok z₂) :
    SigmaProofs.AndInstance_prover_response #[s₁, s₂] #[st₁, st₂] c = .ok #[z₁, z₂] := by
  unfold SigmaProofs.AndInstance_prover_response
  simp [SigmaProofs.«AndInstance.branches», SigmaProofs.«AndProverState.branches», Hax.array_len,
    Hax.bne, foldRange_two, Hax.index, h₁, h₂, Hax.push, SigmaProofs.AndResponse]

theorem AndInstance_verifier_two_ok_iff (s₁ s₂ : SigmaProofs.Instance_T)
    (a₁ a₂ : Array (Array Int)) (c : Array Int) (z₁ z₂ : Array (Array Int)) :
    SigmaProofs.AndInstance_verifier #[s₁, s₂] #[a₁, a₂] c #[z₁, z₂] = .ok () ↔
      SigmaProofs.Instance_verifier s₁ a₁ c z₁ = .ok () ∧
        SigmaProofs.Instance_verifier s₂ a₂ c z₂ = .ok () := by
  unfold SigmaProofs.AndInstance_verifier
  cases h₁ : SigmaProofs.Instance_verifier s₁ a₁ c z₁ <;>
    cases h₂ : SigmaProofs.Instance_verifier s₂ a₂ c z₂ <;>
    simp [SigmaProofs.«AndInstance.branches», SigmaProofs.«AndCommitment.branches»,
      SigmaProofs.«AndResponse.branches», Hax.array_len, Hax.bne, Hax.bor, Hax.deref,
      foldRange_two, Hax.index, h₁, h₂]

theorem AndInstance_simulate_commitment_two (s₁ s₂ : SigmaProofs.Instance_T) (c : Array Int)
    (z₁ z₂ a₁ a₂ : Array (Array Int))
    (h₁ : SigmaProofs.Instance_simulate_commitment s₁ c z₁ = .ok a₁)
    (h₂ : SigmaProofs.Instance_simulate_commitment s₂ c z₂ = .ok a₂) :
    SigmaProofs.AndInstance_simulate_commitment #[s₁, s₂] c #[z₁, z₂] = .ok #[a₁, a₂] := by
  unfold SigmaProofs.AndInstance_simulate_commitment
  simp [SigmaProofs.«AndInstance.branches», SigmaProofs.«AndResponse.branches», Hax.array_len,
    Hax.bne, Hax.deref, foldRange_two, Hax.index, h₁, h₂, Hax.push, SigmaProofs.AndCommitment]

theorem AndInstance_simulate_response_two (s₁ s₂ : SigmaProofs.Instance_T)
    (z₁ z₂ z₁' z₂' : Array (Array Int))
    (h₁ : SigmaProofs.Instance_simulate_response s₁ z₁ = .ok z₁')
    (h₂ : SigmaProofs.Instance_simulate_response s₂ z₂ = .ok z₂') :
    SigmaProofs.AndInstance_simulate_response #[s₁, s₂] #[z₁, z₂] = .ok #[z₁', z₂'] := by
  unfold SigmaProofs.AndInstance_simulate_response
  simp [SigmaProofs.«AndInstance.branches», SigmaProofs.«AndResponse.branches», Hax.array_len,
    Hax.bne, Hax.deref, foldRange_two, Hax.index, h₁, h₂, Hax.push, SigmaProofs.AndResponse]

end Generic

/-! ### Array and loop facts -/

/-- The `if` returning `Ok ()` on a true condition accepts exactly when the condition holds. -/
theorem ite_ok_iff {ε : Type} (b : Bool) {d : Decidable (b = true)} (e : ε) :
    (@ite (Except ε Unit) (b = true) d (.ok ()) (.error e)) = .ok () ↔ b = true := by
  cases b <;> simp

theorem index_array_update {α : Type} [Inhabited α] (a : Array α) (e k : ℕ) (x : α)
    (he : e < a.size) (hk : k < a.size) :
    Hax.index (Hax.array_update a (e : Int) x) (k : Int) =
      if k = e then x else Hax.index a (k : Int) := by
  grind only [= Hax.index_of_size_eq_zero, = Hax.index_array_update_of_ne,
    = Hax.size_array_update_eq, = Hax.index_array_update_same]

/-- The `usize` cast of an index is the integer of `uidx`. -/
theorem castVal_eq_uidx (x : Int) : Hax.castVal_w Hax.usizeBits x = ((uidx x : ℕ) : Int) := by
  unfold uidx
  exact (Int.toNat_of_nonneg (Hax.mod2w_nonneg _ _)).symm

/-! ### The batched verifier -/

section Batch

open CatCrypt.Examples CatCrypt.Crypto.FiatShamirROM

attribute [local instance] GroupParam.scalarCommRing

variable {gp : GroupParam} (E : GroupEncoding gp)

theorem dotVal_update (sc bs : Array (Array Int)) (e : ℕ) (x : Array Int) (he : e < sc.size) :
    dotVal E (Hax.array_update sc (e : Int) x) bs =
      dotVal E sc bs + (E.decS x - E.decS (Hax.index sc (e : Int))) *
        gp.dlog (E.decG (Hax.index bs (e : Int))) := by
  unfold dotVal
  rw [Hax.size_array_update_eq]
  have hsplit : ∀ k ∈ Finset.range sc.size,
      E.decS (Hax.index (Hax.array_update sc (e : Int) x) (k : Int)) *
          gp.dlog (E.decG (Hax.index bs (k : Int))) =
        E.decS (Hax.index sc (k : Int)) * gp.dlog (E.decG (Hax.index bs (k : Int))) +
          if k = e then (E.decS x - E.decS (Hax.index sc (e : Int))) *
            gp.dlog (E.decG (Hax.index bs (e : Int))) else 0 := by
    intro k hk
    rw [index_array_update _ _ _ _ he (Finset.mem_range.mp hk)]
    split_ifs with hke
    · subst hke
      ring
    · ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp [he]

theorem dotVal_zero (N : ℕ) (bs : Array (Array Int)) :
    dotVal E (Array.ofFn fun _ : Fin N => E.encS gp.scalarZero) bs = 0 := by
  unfold dotVal
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Array.size_ofFn, Finset.mem_range] at hk
  rw [index_ofFn _ _ hk, E.decS_encS, GroupParam.scalarZero_eq_zero, zero_mul]

/-- The discrete logarithm of the image of an equation over the elements `els`: the sum of
`dlog els[e] · coefficient` over its image terms `(e, coefficient)`. -/
noncomputable def imgSum (els : Array (Array Int))
    (eq : (Array (Int × Array Int)) × (Array (Int × Int × Array Int))) : gp.Scalar :=
  ∑ k ∈ Finset.range eq.1.size,
    gp.dlog (E.decG (Hax.index els (Hax.castVal_w Hax.usizeBits (Hax.index eq.1 (k : Int)).1))) *
      E.decS (Hax.index eq.1 (k : Int)).2

/-- The discrete logarithm of row `z` of the map of an equation over the elements `els`:
the sum of `dlog els[e] · coefficient · z[s]` over its terms `(s, e, coefficient)`. -/
noncomputable def termSum {n : ℕ} (els : Array (Array Int))
    (eq : (Array (Int × Array Int)) × (Array (Int × Int × Array Int)))
    (z : Fin n → gp.Scalar) : gp.Scalar :=
  ∑ k ∈ Finset.range eq.2.size,
    gp.dlog (E.decG (Hax.index els (Hax.castVal_w Hax.usizeBits (Hax.index eq.2 (k : Int)).2.1))) *
      E.decS (Hax.index eq.2 (k : Int)).2.2 * vecGet z (uidx (Hax.index eq.2 (k : Int)).1)

/-- The indices of an equation are in range: element indices below `N`, scalar indices
below `n`. -/
def EqInRange (N n : ℕ) (eq : (Array (Int × Array Int)) × (Array (Int × Int × Array Int))) :
    Prop :=
  (∀ k : ℕ, k < eq.1.size → uidx (Hax.index eq.1 (k : Int)).1 < N) ∧
    (∀ k : ℕ, k < eq.2.size → uidx (Hax.index eq.2 (k : Int)).2.1 < N) ∧
    (∀ k : ℕ, k < eq.2.size → uidx (Hax.index eq.2 (k : Int)).1 < n)

/-- `Equation_accumulate_weights` with weight `p` adds `p · (c · imgSum − termSum)` to the
weighted sum `dotVal` of the weights. -/
theorem accumulate_weights_spec {n : ℕ} (els : Array (Array Int))
    (eq : (Array (Int × Array Int)) × (Array (Int × Int × Array Int))) (p c : gp.Scalar)
    (z : Fin n → gp.Scalar) (w : Array (Array Int)) (hw : w.size = els.size)
    (hr : EqInRange els.size n eq) :
    (@SigmaProofs.Equation_accumulate_weights (groupSigmaProofsDeps E) eq (E.encS p) (E.encS c)
        (encVec E z) w).size = els.size ∧
      dotVal E (@SigmaProofs.Equation_accumulate_weights (groupSigmaProofsDeps E) eq (E.encS p)
        (E.encS c) (encVec E z) w) els =
        dotVal E w els + p * (c * imgSum E els eq - termSum E els eq z) := by
  unfold SigmaProofs.Equation_accumulate_weights
  simp only [SigmaProofs.«Equation.image», SigmaProofs.«Equation.terms», Hax.array_len]
  obtain ⟨hi, ht, hs⟩ := hr
  have h1 := Hax.foldRange_induct (P := fun (i : Int) (acc : Array (Array Int)) =>
      acc.size = els.size ∧ dotVal E acc els = dotVal E w els + p * c *
        ∑ k ∈ Finset.range i.toNat,
          gp.dlog (E.decG (Hax.index els (Hax.castVal_w Hax.usizeBits
            (Hax.index eq.1 (k : Int)).1))) * E.decS (Hax.index eq.1 (k : Int)).2)
    (lo := 0) (hi := (eq.1.size : Int))
    (f := fun k acc => Hax.array_update acc (Hax.castVal_w Hax.usizeBits (Hax.index eq.1 k).1)
      (@SigmaProofs.SigmaProofsDeps.scalar_add (groupSigmaProofsDeps E)
        (Hax.index acc (Hax.castVal_w Hax.usizeBits (Hax.index eq.1 k).1))
        (@SigmaProofs.SigmaProofsDeps.scalar_mul (groupSigmaProofsDeps E)
          (@SigmaProofs.SigmaProofsDeps.scalar_mul (groupSigmaProofsDeps E) (E.encS p) (E.encS c))
          (Hax.index eq.1 k).2)))
    (init := w) (by omega) (by simp [hw]) (by
      intro i acc h0 hlt ⟨hsz, hv⟩
      have hi' := hi i.toNat (by omega)
      rw [Int.toNat_of_nonneg h0] at hi'
      refine ⟨by rw [Hax.size_array_update_eq, hsz], ?_⟩
      simp only [castVal_eq_uidx] at hv ⊢
      rw [dotVal_update _ _ _ _ _ (by omega), hv, show (i + 1).toNat = i.toNat + 1 by omega,
        Finset.sum_range_succ, Int.toNat_of_nonneg h0]
      simp only [groupSigmaProofsDeps_scalar_add, groupSigmaProofsDeps_scalar_mul, E.decS_encS,
        GroupParam.scalarAdd_eq_add, GroupParam.scalarMul_eq_mul]
      ring)
  obtain ⟨hsz1, hv1⟩ := h1
  generalize Hax.foldRange (0 : Int) (eq.1.size : Int) w _ = A at hsz1 hv1 ⊢
  have h2 := Hax.foldRange_induct (P := fun (i : Int) (acc : Array (Array Int)) =>
      acc.size = els.size ∧ dotVal E acc els = dotVal E A els - p *
        ∑ k ∈ Finset.range i.toNat,
          gp.dlog (E.decG (Hax.index els (Hax.castVal_w Hax.usizeBits
            (Hax.index eq.2 (k : Int)).2.1))) * E.decS (Hax.index eq.2 (k : Int)).2.2 *
              vecGet z (uidx (Hax.index eq.2 (k : Int)).1))
    (lo := 0) (hi := (eq.2.size : Int))
    (f := fun k acc => Hax.array_update acc (Hax.castVal_w Hax.usizeBits (Hax.index eq.2 k).2.1)
      (@SigmaProofs.SigmaProofsDeps.scalar_sub (groupSigmaProofsDeps E)
        (Hax.index acc (Hax.castVal_w Hax.usizeBits (Hax.index eq.2 k).2.1))
        (@SigmaProofs.SigmaProofsDeps.scalar_mul (groupSigmaProofsDeps E)
          (@SigmaProofs.SigmaProofsDeps.scalar_mul (groupSigmaProofsDeps E) (E.encS p)
            (Hax.index eq.2 k).2.2)
          (Hax.index (encVec E z) (Hax.castVal_w Hax.usizeBits (Hax.index eq.2 k).1)))))
    (init := A) (by omega) (by simp [hsz1]) (by
      intro i acc h0 hlt ⟨hsz, hv⟩
      have ht' := ht i.toNat (by omega)
      have hs' := hs i.toNat (by omega)
      rw [Int.toNat_of_nonneg h0] at ht' hs'
      refine ⟨by rw [Hax.size_array_update_eq, hsz], ?_⟩
      rw [encVec, index_castVal_ofFn _ _ hs']
      simp only [castVal_eq_uidx] at hv ⊢
      rw [dotVal_update _ _ _ _ _ (by omega), hv, show (i + 1).toNat = i.toNat + 1 by omega,
        Finset.sum_range_succ, Int.toNat_of_nonneg h0]
      simp only [groupSigmaProofsDeps_scalar_sub, groupSigmaProofsDeps_scalar_mul, E.decS_encS,
        GroupParam.scalarSub_eq_sub, GroupParam.scalarMul_eq_mul, vecGet, dite_eq_left hs']
      ring)
  refine ⟨h2.1, ?_⟩
  rw [h2.2, hv1]
  simp only [imgSum, termSum, Int.toNat_natCast]
  ring

/-- On an instance with `m ≠ 1` equations whose indices are in range, the extracted batched
verifier accepts exactly when `a` has `m` entries and
`∑ j, ρ ^ j · (dlog a[j] + c · imgSum j − termSum j) = 0`. -/
theorem verifier_with_randomness_ok_iff_sum {n m : ℕ} (inst : SigmaProofs.Instance_T)
    (hn : inst.2.2.2 = (n : Int)) (hm : inst.2.1.size = m) (hm1 : m ≠ 1)
    (hr : ∀ j : ℕ, j < m → EqInRange inst.1.size n (Hax.index inst.2.1 (j : Int)))
    (a : Array (Array Int)) (c ρ : gp.Scalar) (z : Fin n → gp.Scalar) :
    @SigmaProofs.Instance_verifier_with_randomness (groupSigmaProofsDeps E) inst a (E.encS c)
        (encVec E z) (E.encS ρ) = .ok () ↔
      a.size = m ∧ ∑ j ∈ Finset.range m, ρ ^ j * (gp.dlog (E.decG (Hax.index a (j : Int))) +
        c * imgSum E inst.1 (Hax.index inst.2.1 (j : Int)) -
          termSum E inst.1 (Hax.index inst.2.1 (j : Int)) z) = 0 := by
  unfold SigmaProofs.Instance_verifier_with_randomness
  by_cases ha : a.size = m
  · rw [ite_eq_right (by simp [SigmaProofs.«.equations», SigmaProofs.«Instance.num_scalars», Hax.array_len,
        Hax.bne, Hax.bor, ha, hm, hn]),
      ite_eq_right (by simp [SigmaProofs.«.equations», Hax.array_len, Hax.beq, hm]; omega), ite_ok_iff]
    simp only [SigmaProofs.«.equations», SigmaProofs.«.elements», Hax.array_len, Hax.deref, hm]
    rw [show Hax.foldRange (0 : Int) (inst.1.size : Int) (#[] : Array (Array Int))
        (fun _k weights => Hax.push weights
          (@SigmaProofs.SigmaProofsDeps.scalar_zero (groupSigmaProofsDeps E))) =
        Array.ofFn fun _ : Fin inst.1.size => E.encS gp.scalarZero from
      foldRange_push_ofFn _ _]
    have hR := Hax.foldRange_induct
      (P := fun (i : Int)
          (x : Array (Array Int) × Array (Array Int) × Array (Array Int) × Array Int) =>
        x.1.size = inst.1.size ∧ x.2.1.size = i.toNat ∧ x.2.2.1.size = i.toNat ∧
          x.2.2.2 = E.encS (ρ ^ i.toNat) ∧
          dotVal E x.1 inst.1 = ∑ j ∈ Finset.range i.toNat, ρ ^ j *
            (c * imgSum E inst.1 (Hax.index inst.2.1 (j : Int)) -
              termSum E inst.1 (Hax.index inst.2.1 (j : Int)) z) ∧
          dotVal E x.2.1 x.2.2.1 = ∑ j ∈ Finset.range i.toNat, ρ ^ j *
            gp.dlog (E.decG (Hax.index a (j : Int))))
      (lo := 0) (hi := (m : Int))
      (f := fun j x => (@SigmaProofs.Equation_accumulate_weights (groupSigmaProofsDeps E)
          (Hax.index inst.2.1 j) x.2.2.2 (E.encS c) (encVec E z) x.1,
        Hax.push x.2.1 x.2.2.2, Hax.push x.2.2.1 (Hax.index a j),
        @SigmaProofs.SigmaProofsDeps.scalar_mul (groupSigmaProofsDeps E) x.2.2.2 (E.encS ρ)))
      (init := (Array.ofFn fun _ : Fin inst.1.size => E.encS gp.scalarZero, #[], #[],
        @SigmaProofs.SigmaProofsDeps.scalar_one (groupSigmaProofsDeps E)))
      (by omega)
      (⟨by simp, rfl, rfl, by rw [groupSigmaProofsDeps_scalar_one, Int.toNat_zero, pow_zero]; rfl,
        by rw [dotVal_zero]; simp, by simp [dotVal]⟩) (by
        rintro i ⟨W, Sc, B, Pw⟩ h0 hlt ⟨h1, h2, h3, h4, h5, h6⟩
        simp only at h1 h2 h3 h4 h5 h6 ⊢
        subst h4
        have hr' := hr i.toNat (by omega)
        rw [Int.toNat_of_nonneg h0] at hr'
        obtain ⟨hw1, hw2⟩ := accumulate_weights_spec E inst.1 (Hax.index inst.2.1 i) (ρ ^ i.toNat) c
          z W h1 hr'
        have hi1 : (i + 1).toNat = i.toNat + 1 := by omega
        simp only [Hax.push]
        refine ⟨hw1, by simp [h2, hi1], by simp [h3, hi1], ?_, ?_, ?_⟩
        · simp only [groupSigmaProofsDeps_scalar_mul, E.decS_encS, GroupParam.scalarMul_eq_mul, hi1,
            pow_succ]
        · rw [hw2, h5, hi1, Finset.sum_range_succ, Int.toNat_of_nonneg h0]
        · rw [dotVal_push _ _ _ _ _ (h2.trans h3.symm), h6, hi1, Finset.sum_range_succ,
            Int.toNat_of_nonneg h0, E.decS_encS])
    generalize Hax.foldRange (0 : Int) (m : Int) _ _ = R at hR ⊢
    obtain ⟨hR1, hR2, hR3, -, hR5, hR6⟩ := hR
    simp only [Int.toNat_natCast] at hR2 hR3 hR5 hR6
    have hS := Hax.foldRange_induct
      (P := fun (k : Int) (y : Array (Array Int) × Array (Array Int)) =>
        y.1.size = m + k.toNat ∧ y.2.size = m + k.toNat ∧
          dotVal E y.1 y.2 = dotVal E R.2.1 R.2.2.1 + ∑ t ∈ Finset.range k.toNat,
            E.decS (Hax.index R.1 (t : Int)) * gp.dlog (E.decG (Hax.index inst.1 (t : Int))))
      (lo := 0) (hi := (inst.1.size : Int))
      (f := fun k y => (Hax.push y.1 (Hax.index R.1 k), Hax.push y.2 (Hax.index inst.1 k)))
      (init := (R.2.1, R.2.2.1)) (by omega) (by simp [hR2, hR3]) (by
        rintro k ⟨Sc, B⟩ h0 hlt ⟨h1, h2, h3⟩
        simp only at h1 h2 h3 ⊢
        have hk1 : (k + 1).toNat = k.toNat + 1 := by omega
        simp only [Hax.push]
        refine ⟨by simp [h1, hk1]; omega, by simp [h2, hk1]; omega, ?_⟩
        rw [dotVal_push _ _ _ _ _ (h1.trans h2.symm), h3, hk1, Finset.sum_range_succ,
          Int.toNat_of_nonneg h0, add_assoc])
    generalize Hax.foldRange (0 : Int) (inst.1.size : Int) _ _ = S at hS ⊢
    obtain ⟨-, -, hS3⟩ := hS
    have hsum : ∑ t ∈ Finset.range inst.1.size,
        E.decS (Hax.index R.1 (t : Int)) * gp.dlog (E.decG (Hax.index inst.1 (t : Int))) =
          dotVal E R.1 inst.1 := by
      rw [dotVal, hR1]
    rw [msm_vartime_eq, groupSigmaProofsDeps_group_eq, groupSigmaProofsDeps_identity, E.decG_encG,
      E.decG_encG, decide_eq_true_iff, ← gp.exp_zero, GroupParam.exp_inj_iff, hS3, hR6,
      Int.toNat_natCast, hsum, hR5, ← Finset.sum_add_distrib]
    simp only [ha, true_and, GroupParam.scalarZero_eq_zero]
    rw [Finset.sum_congr rfl fun (j : ℕ) _ => (by ring :
      ρ ^ j * gp.dlog (E.decG (Hax.index a (j : Int))) +
          ρ ^ j * (c * imgSum E inst.1 (Hax.index inst.2.1 (j : Int)) -
            termSum E inst.1 (Hax.index inst.2.1 (j : Int)) z) =
        ρ ^ j * (gp.dlog (E.decG (Hax.index a (j : Int))) +
          c * imgSum E inst.1 (Hax.index inst.2.1 (j : Int)) -
            termSum E inst.1 (Hax.index inst.2.1 (j : Int)) z))]
  · rw [ite_eq_left (by simp [SigmaProofs.«.equations», SigmaProofs.«Instance.num_scalars», Hax.array_len,
        Hax.bne, Hax.bor, ha, hm])]
    simp [ha]

/-! ### Defects of the decoded relation -/

/-- The element indices of the image terms and terms of the first `m` equations are below
the number of elements. -/
def ElemsInRange (m : ℕ) (inst : SigmaProofs.Instance_T) : Prop :=
  ∀ j : ℕ, j < m →
    (∀ k : ℕ, k < (Hax.index inst.2.1 (j : Int)).1.size →
      uidx (Hax.index (Hax.index inst.2.1 (j : Int)).1 (k : Int)).1 < inst.1.size) ∧
    (∀ k : ℕ, k < (Hax.index inst.2.1 (j : Int)).2.size →
      uidx (Hax.index (Hax.index inst.2.1 (j : Int)).2 (k : Int)).2.1 < inst.1.size)

/-- The defect of equation `i` for the commitment array `a`, the challenge `c` and the
response `z`: `dlog a[i] + c · dlog (image i) − dlog (map z i)` for the decoded relation. -/
noncomputable def defect {n m : ℕ} (inst : SigmaProofs.Instance_T) (a : Array (Array Int))
    (c : gp.Scalar) (z : Fin n → gp.Scalar) (i : Fin m) : gp.Scalar :=
  gp.dlog (E.decG (Hax.index a ((i : ℕ) : Int))) + c * gp.dlog ((decodeRel E n m inst).image i) -
    (decodeRel E n m inst).lin z i

theorem dlog_imageComb (els : Array (Array Int))
    (eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))) (j : ℕ) :
    gp.dlog (imageComb E els eqs j) = imgSum E els (Hax.index eqs (j : Int)) := by
  rw [imageComb, foldr_groupMul_eq_exp, GroupParam.dlog_exp, List.map_map, imgSum]
  simp only [Finset.sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply, GroupParam.groupExp_eq_exp, GroupParam.dlog_exp,
    GroupParam.scalarMul_eq_mul]

theorem lin_eq_termSum {n m : ℕ} (inst : SigmaProofs.Instance_T) (z : Fin n → gp.Scalar)
    (i : Fin m) :
    (decodeRel E n m inst).lin z i = termSum E inst.1 (Hax.index inst.2.1 ((i : ℕ) : Int)) z := by
  simp only [LinearRelation.lin, decodeRel, List.map_map]
  show List.sum _ = _
  simp only [termSum, Finset.sum, Finset.range_val, Multiset.range, Multiset.map_coe,
    Multiset.sum_coe]
  congr 1
  apply List.map_congr_left
  intro k hk
  change gp.scalarMul (gp.dlog ((decodeRel E n m inst).elem (m + (i : ℕ) * termBound inst + k)))
    (vecGet z (uidx (Hax.index (Hax.index inst.2.1 ((i : ℕ) : Int)).2 (k : Int)).1)) = _
  rw [decodeRel_elem_term E n m inst i k i.isLt (List.mem_range.mp hk), termElem,
    GroupParam.groupExp_eq_exp, GroupParam.dlog_exp]
  simp only [GroupParam.scalarMul_eq_mul]

variable {E}

/-- The extracted per-equation verifier accepts exactly when `a` has `m` entries and every
defect is zero. -/
theorem Instance_verifier_ok_iff_defect {n m : ℕ} {inst : SigmaProofs.Instance_T}
    (h : WellFormed E n m inst) (a : Array (Array Int)) (c : gp.Scalar) (z : Fin n → gp.Scalar) :
    @SigmaProofs.Instance_verifier (groupSigmaProofsDeps E) inst a (E.encS c) (encVec E z) =
        .ok () ↔
      a.size = m ∧ ∀ i : Fin m, defect E inst a c z i = 0 := by
  rw [Instance_verifier_ok_iff h]
  refine and_congr_right fun _ => ?_
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  have key : ∀ x y : gp.G, x = y ↔ gp.dlog x = gp.dlog y := fun x y =>
    ⟨congrArg _, fun hxy => by rw [← gp.exp_dlog x, hxy, gp.exp_dlog]⟩
  rw [key]
  simp only [decCom, LinearRelation.simCommit, defect, LinearRelation.map_eq_exp,
    GroupParam.groupExp_eq_exp, GroupParam.groupInv_eq_exp, GroupParam.groupMul_eq_exp,
    GroupParam.dlog_exp, GroupParam.scalarAdd_eq_add, GroupParam.scalarMul_eq_mul,
    GroupParam.scalarNeg_eq_neg]
  constructor <;> intro hd <;> linear_combination hd

/-- **Batched verification.** On a well-formed instance whose element indices are in range
and whose stored images are the products of their image terms, the extracted batched
verifier with randomness `ρ` accepts exactly when `a` has `m` entries and
`∑ i, ρ ^ i · defect i = 0`. -/
theorem Instance_verifier_with_randomness_ok_iff {n m : ℕ} {inst : SigmaProofs.Instance_T}
    (h : WellFormed E n m inst) (hel : ElemsInRange m inst)
    (himg : ∀ i : Fin m, (decodeRel E n m inst).image i = imageComb E inst.1 inst.2.1 i)
    (a : Array (Array Int)) (c ρ : gp.Scalar) (z : Fin n → gp.Scalar) :
    @SigmaProofs.Instance_verifier_with_randomness (groupSigmaProofsDeps E) inst a (E.encS c)
        (encVec E z) (E.encS ρ) = .ok () ↔
      a.size = m ∧ ∑ i : Fin m, ρ ^ (i : ℕ) * defect E inst a c z i = 0 := by
  by_cases hm1 : m = 1
  · subst hm1
    unfold SigmaProofs.Instance_verifier_with_randomness
    by_cases ha : a.size = 1
    · rw [ite_eq_right (by simp [SigmaProofs.«.equations», SigmaProofs.«Instance.num_scalars»,
          Hax.array_len, Hax.bne, Hax.bor, ha, h.1, h.2.1]),
        ite_eq_left (by simp [SigmaProofs.«.equations», Hax.array_len, Hax.beq, h.2.1]),
        Instance_verifier_ok_iff_defect h]
      simp [Fin.forall_fin_one]
    · rw [ite_eq_left (by simp [SigmaProofs.«.equations», SigmaProofs.«Instance.num_scalars»,
          Hax.array_len, Hax.bne, Hax.bor, ha, h.2.1])]
      simp [ha]
  · have hr : ∀ j : ℕ, j < m → EqInRange inst.1.size n (Hax.index inst.2.1 (j : Int)) :=
      fun j hj => ⟨(hel j hj).1, (hel j hj).2, (decodeRel_validate_iff E n m inst).mp h.2.2 j hj⟩
    rw [verifier_with_randomness_ok_iff_sum E inst h.1 h.2.1 hm1 hr a c ρ z]
    refine and_congr_right fun _ => ?_
    simp only [defect, himg, dlog_imageComb, lin_eq_termSum]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ρ ^ j * (gp.dlog (E.decG (Hax.index a (j : Int))) +
      c * imgSum E inst.1 (Hax.index inst.2.1 (j : Int)) -
        termSum E inst.1 (Hax.index inst.2.1 (j : Int)) z)) m]

/-- The batched verifier accepts, for every randomness, each proof that the per-equation
verifier accepts. -/
theorem Instance_verifier_with_randomness_of_ok {n m : ℕ} {inst : SigmaProofs.Instance_T}
    (h : WellFormed E n m inst) (hel : ElemsInRange m inst)
    (himg : ∀ i : Fin m, (decodeRel E n m inst).image i = imageComb E inst.1 inst.2.1 i)
    (a : Array (Array Int)) (c : gp.Scalar) (z : Fin n → gp.Scalar)
    (hok : @SigmaProofs.Instance_verifier (groupSigmaProofsDeps E) inst a (E.encS c)
      (encVec E z) = .ok ()) (ρ : gp.Scalar) :
    @SigmaProofs.Instance_verifier_with_randomness (groupSigmaProofsDeps E) inst a (E.encS c)
      (encVec E z) (E.encS ρ) = .ok () := by
  obtain ⟨ha, hd⟩ := (Instance_verifier_ok_iff_defect h a c z).mp hok
  exact (Instance_verifier_with_randomness_ok_iff h hel himg a c ρ z).mpr ⟨ha, by simp [hd]⟩

omit E in
/-- The scalars of `gp` have no zero divisors: a nonzero scalar `b` has the inverse
`scalarDiv 1 b`. -/
theorem scalar_noZeroDivisors : NoZeroDivisors gp.Scalar := ⟨fun {a b} hab => by
  by_cases hb : b = 0
  · exact Or.inr hb
  · left
    have hu := gp.div_mul_cancel gp.scalarOne b hb
    calc a = a * (gp.scalarDiv gp.scalarOne b * b) := by
          rw [GroupParam.scalarMul_eq_mul] at hu
          rw [hu]
          exact (mul_one a).symm
      _ = (a * b) * gp.scalarDiv gp.scalarOne b := by ring
      _ = 0 := by rw [hab, zero_mul]⟩

omit E in
/-- A sum `∑ j < m, ρ ^ j · d j` with a nonzero coefficient vanishes for at most `m − 1`
values of `ρ`: it is the value at `ρ` of a nonzero polynomial of degree at most `m − 1`. -/
theorem card_powerSum_roots_le (m : ℕ) (d : ℕ → gp.Scalar) (hd : ∃ j < m, d j ≠ 0) :
    (Finset.univ.filter fun ρ : gp.Scalar => ∑ j ∈ Finset.range m, ρ ^ j * d j = 0).card ≤
      m - 1 := by
  obtain ⟨j0, hj0, hd0⟩ := hd
  have : Nontrivial gp.Scalar := ⟨⟨d j0, 0, hd0⟩⟩
  have : NoZeroDivisors gp.Scalar := scalar_noZeroDivisors
  have : IsDomain gp.Scalar := NoZeroDivisors.to_isDomain _
  classical
  set P : Polynomial gp.Scalar := ∑ j ∈ Finset.range m, Polynomial.C (d j) * Polynomial.X ^ j
  have hP : P ≠ 0 := by
    intro h
    have := congrArg (fun q => Polynomial.coeff q j0) h
    simp [P, hj0] at this
    exact hd0 this
  have hdeg : P.natDegree ≤ m - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le (d j) j).trans (by simp at hj; omega)
  calc _ ≤ P.roots.toFinset.card := Finset.card_le_card fun ρ hρ => by
          simp only [Finset.mem_filter] at hρ
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def]
          simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_pow, Polynomial.eval_X]
          rw [← hρ.2]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ m - 1 := hdeg

open Classical in
/-- **Soundness of batching.** For a proof `(a, c, z)` that the extracted per-equation
verifier rejects, at most `m − 1` values of the randomness `ρ` make the extracted batched
verifier accept. -/
theorem card_batch_accept_le {n m : ℕ} {inst : SigmaProofs.Instance_T}
    (h : WellFormed E n m inst) (hel : ElemsInRange m inst)
    (himg : ∀ i : Fin m, (decodeRel E n m inst).image i = imageComb E inst.1 inst.2.1 i)
    (a : Array (Array Int)) (c : gp.Scalar) (z : Fin n → gp.Scalar)
    (hrej : @SigmaProofs.Instance_verifier (groupSigmaProofsDeps E) inst a (E.encS c)
      (encVec E z) ≠ .ok ()) :
    (Finset.univ.filter fun ρ : gp.Scalar =>
      @SigmaProofs.Instance_verifier_with_randomness (groupSigmaProofsDeps E) inst a (E.encS c)
        (encVec E z) (E.encS ρ) = .ok ()).card ≤ m - 1 := by
  by_cases ha : a.size = m
  · have hd : ∃ i : Fin m, defect E inst a c z i ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hrej ((Instance_verifier_ok_iff_defect h a c z).mpr ⟨ha, hcon⟩)
    obtain ⟨i0, hi0⟩ := hd
    let d : ℕ → gp.Scalar := fun j => if hj : j < m then defect E inst a c z ⟨j, hj⟩ else 0
    have hfilt : (Finset.univ.filter fun ρ : gp.Scalar =>
        @SigmaProofs.Instance_verifier_with_randomness (groupSigmaProofsDeps E) inst a (E.encS c)
          (encVec E z) (E.encS ρ) = .ok ()) =
        Finset.univ.filter fun ρ : gp.Scalar => ∑ j ∈ Finset.range m, ρ ^ j * d j = 0 := by
      ext ρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Instance_verifier_with_randomness_ok_iff h hel himg, ← Fin.sum_univ_eq_sum_range]
      simp [ha, d]
    rw [hfilt]
    exact card_powerSum_roots_le m d ⟨i0, i0.isLt, by simp [d, hi0]⟩
  · have hempty : (Finset.univ.filter fun ρ : gp.Scalar =>
        @SigmaProofs.Instance_verifier_with_randomness (groupSigmaProofsDeps E) inst a (E.encS c)
          (encVec E z) (E.encS ρ) = .ok ()) = ∅ := by
      ext ρ
      simp [Instance_verifier_with_randomness_ok_iff h hel himg, ha]
    simp [hempty]

open scoped ENNReal in
/-- **Soundness of batching, probability form.** For a proof that the extracted per-equation
verifier rejects, the batched verifier with a uniform randomness accepts with probability at
most `(m − 1) / |Scalar|`. -/
theorem batch_accept_prob_le {n m : ℕ} {inst : SigmaProofs.Instance_T}
    (h : WellFormed E n m inst) (hel : ElemsInRange m inst)
    (himg : ∀ i : Fin m, (decodeRel E n m inst).image i = imageComb E inst.1 inst.2.1 i)
    (a : Array (Array Int)) (c : gp.Scalar) (z : Fin n → gp.Scalar)
    (hrej : @SigmaProofs.Instance_verifier (groupSigmaProofsDeps E) inst a (E.encS c)
      (encVec E z) ≠ .ok ()) :
    (PMF.uniformFintype gp.Scalar).toOuterMeasure {ρ |
      @SigmaProofs.Instance_verifier_with_randomness (groupSigmaProofsDeps E) inst a (E.encS c)
        (encVec E z) (E.encS ρ) = .ok ()} ≤ ((m - 1 : ℕ) : ℝ≥0∞) / Fintype.card gp.Scalar := by
  classical
  rw [PMF.toOuterMeasure_uniformFintype_apply]
  gcongr
  rw [Fintype.card_ofFinset]
  refine le_trans (le_of_eq ?_) (card_batch_accept_le h hel himg a c z hrej)
  congr 1

end Batch

/-! ### The AND composition -/

section AndComposition

open CatCrypt.Examples CatCrypt.Crypto.FiatShamirROM

variable {gp : GroupParam} (E : GroupEncoding gp) {n₁ m₁ n₂ m₂ : ℕ}

/-- The statements of the two-branch extracted AND composition: pairs of well-formed
extracted instances. -/
abbrev ExtAndStmt (n₁ m₁ n₂ m₂ : ℕ) := ExtStmt E n₁ m₁ × ExtStmt E n₂ m₂

/-- The extracted `AndInstance` of a pair of branches. -/
def andInst (s : ExtAndStmt E n₁ m₁ n₂ m₂) : Array SigmaProofs.Instance_T := #[s.1.1, s.2.1]

/-- The core AND composition of the decoded branches. -/
def andRel (s : ExtAndStmt E n₁ m₁ n₂ m₂) : LinearRelation gp (n₁ + n₂) (m₁ + m₂) :=
  (decodeRel E n₁ m₁ s.1.1).and (decodeRel E n₂ m₂ s.2.1)

/-- The per-branch arrays of a concatenated scalar vector: the encodings of its halves. -/
def encVec₂ (v : Fin (n₁ + n₂) → gp.Scalar) : Array (Array (Array Int)) :=
  #[encVec E fun i => v (Fin.castAdd n₂ i), encVec E fun i => v (Fin.natAdd n₁ i)]

/-- The per-branch arrays of a concatenated commitment: the encodings of its halves. -/
def encCom₂ (a : Fin (m₁ + m₂) → gp.G) : Array (Array (Array Int)) :=
  #[encCom E fun i => a (Fin.castAdd m₂ i), encCom E fun i => a (Fin.natAdd m₁ i)]

/-- The concatenation of the decoded commitments of the two branches. -/
def decCom₂ (m₁ m₂ : ℕ) (a : Array (Array (Array Int))) : Fin (m₁ + m₂) → gp.G :=
  Fin.append (decCom E m₁ (Hax.index a 0)) (decCom E m₂ (Hax.index a 1))

/-- The concatenation of the decoded scalar vectors of the two branches. -/
def decVec₂ (n₁ n₂ : ℕ) (z : Array (Array (Array Int))) : Fin (n₁ + n₂) → gp.Scalar :=
  Fin.append (decVec E n₁ (Hax.index z 0)) (decVec E n₂ (Hax.index z 1))

/-- The Σ-protocol whose commitment, response, verifier and simulator are the extracted
`AndInstance_prover_commit`, `AndInstance_prover_response`, `AndInstance_verifier` and
`AndInstance_simulate_transcript` on the encoded halves of their arguments, with decoded
results. The extraction has no special-soundness extractor; the extractor is that of
`linearSigma`. -/
noncomputable def extAndSigma
    (gen : PMF (ExtAndStmt E n₁ m₁ n₂ m₂ × (Fin (n₁ + n₂) → gp.Scalar))) : Sigma where
  Stmt := ExtAndStmt E n₁ m₁ n₂ m₂
  Wit := Fin (n₁ + n₂) → gp.Scalar
  Com := Fin (m₁ + m₂) → gp.G
  Ch := gp.Scalar
  Resp := Fin (n₁ + n₂) → gp.Scalar
  Rand := Fin (n₁ + n₂) → gp.Scalar
  SimRand := Fin (n₁ + n₂) → gp.Scalar
  inhWit := ⟨fun _ => gp.scalarZero⟩
  rel s w := (andRel E s).Holds w
  gen := gen
  commit s w r :=
    match @SigmaProofs.AndInstance_prover_commit (groupSigmaProofsDeps E) (andInst E s)
        (encVec₂ E w) (encVec₂ E r) with
    | .ok (a, _) => decCom₂ E m₁ m₂ a
    | .error _ => fun _ => gp.identity
  respond s w r c :=
    match @SigmaProofs.AndInstance_prover_commit (groupSigmaProofsDeps E) (andInst E s)
        (encVec₂ E w) (encVec₂ E r) with
    | .ok (_, st) =>
      match @SigmaProofs.AndInstance_prover_response (groupSigmaProofsDeps E) (andInst E s) st
          (E.encS c) with
      | .ok z => decVec₂ E n₁ n₂ z
      | .error _ => fun _ => gp.scalarZero
    | .error _ => fun _ => gp.scalarZero
  verify s a c z :=
    match @SigmaProofs.AndInstance_verifier (groupSigmaProofsDeps E) (andInst E s) (encCom₂ E a)
        (E.encS c) (encVec₂ E z) with
    | .ok _ => true
    | .error _ => false
  simulate s c z :=
    match @SigmaProofs.AndInstance_simulate_transcript (groupSigmaProofsDeps E) (andInst E s)
        (encVec₂ E z) (E.encS c) with
    | .ok (a, _, z') => (decCom₂ E m₁ m₂ a, decVec₂ E n₁ n₂ z')
    | .error _ => (fun _ => gp.identity, z)
  extract _ _ c z c' z' j := gp.scalarDiv (gp.scalarSub (z j) (z' j)) (gp.scalarSub c c')

variable {E} {gen : PMF (ExtAndStmt E n₁ m₁ n₂ m₂ × (Fin (n₁ + n₂) → gp.Scalar))}

noncomputable instance : DecidableEq (extAndSigma E gen).Stmt := Classical.decEq _

theorem eq_append_iff {α : Type} {k l : ℕ} (a : Fin (k + l) → α) (A : Fin k → α)
    (B : Fin l → α) :
    a = Fin.append A B ↔ (fun i => a (Fin.castAdd l i)) = A ∧ (fun i => a (Fin.natAdd k i)) = B := by
  constructor
  · rintro rfl
    exact ⟨funext fun i => Fin.append_left A B i, funext fun i => Fin.append_right A B i⟩
  · rintro ⟨rfl, rfl⟩
    exact Fin.append_castAdd_natAdd.symm

theorem andRel_map (s : ExtAndStmt E n₁ m₁ n₂ m₂) (r : Fin (n₁ + n₂) → gp.Scalar) :
    (andRel E s).map r = Fin.append ((decodeRel E n₁ m₁ s.1.1).map fun i => r (Fin.castAdd n₂ i))
      ((decodeRel E n₂ m₂ s.2.1).map fun i => r (Fin.natAdd n₁ i)) := by
  conv_lhs => rw [← Fin.append_castAdd_natAdd (f := r)]
  exact LinearRelation.map_and s.1.2.2.2 _ _

theorem andRel_simCommit (s : ExtAndStmt E n₁ m₁ n₂ m₂) (c : gp.Scalar)
    (z : Fin (n₁ + n₂) → gp.Scalar) :
    (andRel E s).simCommit c z =
      Fin.append ((decodeRel E n₁ m₁ s.1.1).simCommit c fun i => z (Fin.castAdd n₂ i))
        ((decodeRel E n₂ m₂ s.2.1).simCommit c fun i => z (Fin.natAdd n₁ i)) := by
  funext i
  simp only [LinearRelation.simCommit, andRel_map]
  rw [andRel, LinearRelation.image_and s.1.2.2.2]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp only [Fin.append_left, Fin.append_right] <;> rfl

/-- A concatenated witness is a witness of the AND composition exactly when its halves are
witnesses of the branches. -/
theorem extAnd_rel_iff (s : ExtAndStmt E n₁ m₁ n₂ m₂) (w : Fin (n₁ + n₂) → gp.Scalar) :
    (andRel E s).Holds w ↔ (decodeRel E n₁ m₁ s.1.1).Holds (fun i => w (Fin.castAdd n₂ i)) ∧
      (decodeRel E n₂ m₂ s.2.1).Holds (fun i => w (Fin.natAdd n₁ i)) := by
  conv_lhs => rw [← Fin.append_castAdd_natAdd (f := w)]
  exact LinearRelation.holds_and_iff s.1.2.2.2 _ _

theorem andInst_prover_commit_eq (s : ExtAndStmt E n₁ m₁ n₂ m₂)
    (w r : Fin (n₁ + n₂) → gp.Scalar) :
    @SigmaProofs.AndInstance_prover_commit (groupSigmaProofsDeps E) (andInst E s) (encVec₂ E w)
        (encVec₂ E r) =
      .ok (#[encCom E ((decodeRel E n₁ m₁ s.1.1).map fun i => r (Fin.castAdd n₂ i)),
            encCom E ((decodeRel E n₂ m₂ s.2.1).map fun i => r (Fin.natAdd n₁ i))],
          #[(encVec E fun i => r (Fin.castAdd n₂ i), encVec E fun i => w (Fin.castAdd n₂ i)),
            (encVec E fun i => r (Fin.natAdd n₁ i), encVec E fun i => w (Fin.natAdd n₁ i))]) :=
  @AndInstance_prover_commit_two (groupSigmaProofsDeps E) _ _ _ _ _ _ _ _ _ _
    (Instance_prover_commit_eq s.1.2 _ _) (Instance_prover_commit_eq s.2.2 _ _)

theorem extAnd_commit (s : ExtAndStmt E n₁ m₁ n₂ m₂) (w r : Fin (n₁ + n₂) → gp.Scalar) :
    (extAndSigma E gen).commit s w r = (andRel E s).map r := by
  simp only [extAndSigma, andInst_prover_commit_eq, andRel_map]
  simp [decCom₂, Hax.index, decCom_encCom]

theorem extAnd_respond (s : ExtAndStmt E n₁ m₁ n₂ m₂) (w r : Fin (n₁ + n₂) → gp.Scalar)
    (c : gp.Scalar) :
    (extAndSigma E gen).respond s w r c = fun j => gp.scalarAdd (r j) (gp.scalarMul c (w j)) := by
  simp only [extAndSigma, andInst_prover_commit_eq]
  simp only [andInst]
  rw [@AndInstance_prover_response_two (groupSigmaProofsDeps E) _ _ _ _ _ _ _
    (Instance_prover_response_eq s.1.2 _ _ c) (Instance_prover_response_eq s.2.2 _ _ c)]
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [decVec₂, Hax.index, decVec_encVec]

theorem extAnd_verify_iff (s : ExtAndStmt E n₁ m₁ n₂ m₂) (a : Fin (m₁ + m₂) → gp.G)
    (c : gp.Scalar) (z : Fin (n₁ + n₂) → gp.Scalar) :
    (extAndSigma E gen).verify s a c z = true ↔ a = (andRel E s).simCommit c z := by
  have h₁ := Instance_verifier_ok_iff s.1.2 (encCom E fun i => a (Fin.castAdd m₂ i)) c
    (fun i => z (Fin.castAdd n₂ i))
  have h₂ := Instance_verifier_ok_iff s.2.2 (encCom E fun i => a (Fin.natAdd m₁ i)) c
    (fun i => z (Fin.natAdd n₁ i))
  rw [decCom_encCom] at h₁ h₂
  simp only [show ∀ (k : ℕ) (b : Fin k → gp.G), (encCom E b).size = k from fun k b => by
    simp [encCom], true_and] at h₁ h₂
  have hv := @AndInstance_verifier_two_ok_iff (groupSigmaProofsDeps E) s.1.1 s.2.1
    (encCom E fun i => a (Fin.castAdd m₂ i)) (encCom E fun i => a (Fin.natAdd m₁ i)) (E.encS c)
    (encVec E fun i => z (Fin.castAdd n₂ i)) (encVec E fun i => z (Fin.natAdd n₁ i))
  rw [h₁, h₂] at hv
  rw [andRel_simCommit, eq_append_iff, ← hv]
  simp only [extAndSigma, andInst, encCom₂, encVec₂]
  split <;> simp_all

theorem extAnd_simulate (s : ExtAndStmt E n₁ m₁ n₂ m₂) (c : gp.Scalar)
    (z : Fin (n₁ + n₂) → gp.Scalar) :
    (extAndSigma E gen).simulate s c z = ((andRel E s).simCommit c z, z) := by
  simp only [extAndSigma, andInst, encVec₂, SigmaProofs.AndInstance_simulate_transcript]
  rw [@AndInstance_simulate_response_two (groupSigmaProofsDeps E) _ _ _ _ _ _
    (Instance_simulate_response_eq s.1.2 _) (Instance_simulate_response_eq s.2.2 _)]
  simp only
  rw [@AndInstance_simulate_commitment_two (groupSigmaProofsDeps E) _ _ _ _ _ _ _
    (Instance_simulate_commitment_eq s.1.2 c _) (Instance_simulate_commitment_eq s.2.2 c _)]
  simp [andRel_simCommit, decCom₂, decVec₂, Hax.index, decCom_encCom, decVec_encVec,
    Fin.append_castAdd_natAdd]

/-- **The extracted AND composition is `linearSigma` of the core AND composition.** The
Σ-protocol of the extracted AND functions is the Σ-protocol `linearSigma` of the relations
`LinearRelation.and` of the decoded branches. -/
theorem extAndSigma_eq :
    extAndSigma E gen = linearSigma gp (n₁ + n₂) (m₁ + m₂) (andRel E) gen := by
  unfold extAndSigma linearSigma
  congr 1
  · funext s w r
    exact extAnd_commit (gen := gen) s w r
  · funext s w r c
    exact extAnd_respond (gen := gen) s w r c
  · funext s a c z
    exact Bool.eq_iff_iff.mpr ((extAnd_verify_iff (gen := gen) s a c z).trans
      (linearSigma_verify_iff (andRel E) gen s a c z).symm)
  · funext s c z
    exact extAnd_simulate (gen := gen) s c z

theorem extAnd_complete : (extAndSigma E gen).Complete :=
  extAndSigma_eq ▸ linearSigma_complete _ gen

theorem extAnd_specialSound : (extAndSigma E gen).SpecialSound :=
  extAndSigma_eq ▸ linearSigma_specialSound _ gen

theorem extAnd_perfectHVZK (hgen : ∀ s w, (s, w) ∈ gen.support → (andRel E s).Holds w) :
    (extAndSigma E gen).PerfectHVZK :=
  extAndSigma_eq ▸ linearSigma_perfectHVZK _ gen hgen

end AndComposition

end CatCrypt.Crypto.SigmaProtocol.SurfaceDeps.BatchAnd
