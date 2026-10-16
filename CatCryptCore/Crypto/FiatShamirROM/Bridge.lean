/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Game
public import CatCryptCore.Examples.Sigma

/-!
# Σ-protocols with explicit randomness as `Examples.Sigma` protocols

A `FiatShamirROM.Sigma` `P` gives two protocols of `CatCrypt.Examples.Sigma`.

* `Sigma.toSigmaProtocolS P` keeps the prover randomness as the prover state:
  the commitment step samples `r` and returns `(P.commit x w r, r)`, and the
  response step reads `r`.
* `Sigma.toSigmaProtocol P` is stateless with first message `P.Com`: the
  commitment step samples `r` and sends `P.commit x w r`; the response step on a
  commitment `a` samples `r'` uniformly from the fibre `{r' | P.commit x w r' = a}`
  and answers `P.respond x w r' e`. The pair `(a, z)` then has the distribution of
  `(P.commit x w r, P.respond x w r e)` for uniform `r`
  (`map_pair_eq_bind_fibreDist`).

The predicates of `Examples.Sigma` hold for `Sigma.toSigmaProtocol P` when their
counterparts hold for `P`.

## Main definitions

* `fibreDist c a` — the uniform distribution on the fibre of `c` over `a`
* `Sigma.toSigmaProtocolS`, `Sigma.toSigmaProtocol`

## Main results

* `bind_fibreDist` — sampling `c r` for uniform `r` and then a uniform element of
  its fibre is sampling uniformly
* `Sigma.completeness_toSigmaProtocol` — `Complete → Completeness`
* `Sigma.specialSoundness_toSigmaProtocol` — `SpecialSound → SpecialSoundness`
* `Sigma.shvzk_given_toSigmaProtocol` — `PerfectHVZK → SHVZK_given`, for a
  relation whose pairs are in the support of the generator
* `Sigma.specialSoundness_toSigmaProtocolS` — `SpecialSound` gives
  `SpecialSoundness` of the stateless protocol of `toSigmaProtocolS`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational
open CatCrypt.Examples.Sigma
open scoped ENNReal

/-! ## Uniform sampling over a fibre -/

section Fibre

variable {R A B : Type} [Fintype R] [Nonempty R] [DecidableEq A]

/-- The uniform distribution on the fibre `{r | c r = a}`, and the uniform
distribution on `R` when the fibre is empty. -/
noncomputable def fibreDist (c : R → A) (a : A) : PMF R :=
  if h : (Finset.univ.filter fun r => c r = a).Nonempty then PMF.uniformOfFinset _ h
  else PMF.uniformOfFintype R

/-- The image of the uniform distribution under `c` puts weight
`|c⁻¹(a)| / |R|` on `a`. -/
theorem map_uniformOfFintype_apply (c : R → A) (a : A) :
    ((PMF.uniformOfFintype R).map c) a =
      ((Finset.univ.filter fun r => c r = a).card : ℝ≥0∞) / Fintype.card R := by
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv]
  congr 3
  ext r
  simp [eq_comm]

/-- Sampling `c r` for uniform `r` and then a uniform element of the fibre over it
is uniform sampling. -/
theorem bind_fibreDist (c : R → A) :
    ((PMF.uniformOfFintype R).map c).bind (fibreDist c) = PMF.uniformOfFintype R := by
  ext r
  rw [PMF.bind_apply, tsum_eq_single (c r)]
  · have hne : (Finset.univ.filter fun r' => c r' = c r).Nonempty := ⟨r, by simp⟩
    rw [fibreDist, dif_pos hne,
      PMF.uniformOfFinset_apply_of_mem hne (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩),
      map_uniformOfFintype_apply, PMF.uniformOfFintype_apply]
    have h0 : ((Finset.univ.filter fun r' => c r' = c r).card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast hne.card_pos.ne'
    rw [div_eq_mul_inv, mul_comm _ (Fintype.card R : ℝ≥0∞)⁻¹, mul_assoc,
      ENNReal.mul_inv_cancel h0 (ENNReal.natCast_ne_top _), mul_one]
  · intro a ha
    by_cases hne : (Finset.univ.filter fun r' => c r' = a).Nonempty
    · rw [fibreDist, dif_pos hne,
        PMF.uniformOfFinset_apply_of_notMem hne (fun h => ha (Finset.mem_filter.mp h).2.symm),
        mul_zero]
    · have h0 : ((PMF.uniformOfFintype R).map c) a = 0 := by
        rw [map_uniformOfFintype_apply, Finset.not_nonempty_iff_eq_empty.mp hne]
        simp
      rw [h0, zero_mul]

/-- On a value `a` in the image of `c`, every element in the support of
`fibreDist c a` is mapped to `a`. -/
theorem eq_of_mem_support_fibreDist (c : R → A) {a : A}
    (ha : a ∈ ((PMF.uniformOfFintype R).map c).support) {r : R}
    (hr : r ∈ (fibreDist c a).support) : c r = a := by
  have hne : (Finset.univ.filter fun r' => c r' = a).Nonempty := by
    obtain ⟨r', -, hr'⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
    exact ⟨r', by simp [hr']⟩
  rw [fibreDist, dif_pos hne, PMF.mem_support_uniformOfFinset_iff] at hr
  exact (Finset.mem_filter.mp hr).2

/-- Two kernels that agree on the support of `p` give the same bind. -/
private theorem bind_congr_of_mem_support {α β : Type} (p : PMF α) {f g : α → PMF β}
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff p a).mpr ha, zero_mul, zero_mul]

/-- The joint distribution of `(c r, g r)` for uniform `r` is the image `a` of a
uniform `r` followed by `g` of a uniform element of the fibre over `a`. -/
theorem map_pair_eq_bind_fibreDist (c : R → A) (g : R → B) :
    (PMF.uniformOfFintype R).map (fun r => (c r, g r)) =
      ((PMF.uniformOfFintype R).map c).bind
        (fun a => ((fibreDist c a).map g).map fun z => (a, z)) := by
  conv_lhs => rw [← bind_fibreDist c]
  rw [PMF.map_bind]
  refine bind_congr_of_mem_support _ fun a ha => ?_
  rw [PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  refine bind_congr_of_mem_support _ fun r hr => ?_
  simp only [Function.comp_apply, eq_of_mem_support_fibreDist c ha hr]

end Fibre

/-! ## Heap-independent computations from distributions -/

section Lift

variable {α β : Type}

/-- Binding the heap-independent sampler of `p` is binding `p` at the current
heap. -/
theorem liftSDistr_map_some_bind (p : PMF α) (f : α → SPComp β) :
    SPComp.bind (liftSDistr (p.map some)) f = fun h => p.bind fun a => f a h := by
  funext h
  simp only [SPComp.bind, liftSDistr, SDistr.bind, PMF.bind_map, PMF.bind_bind,
    Function.comp_def, SDistr.pure, PMF.pure_bind]

/-- The heap-independent sampler of `p` returns only elements of the support of
`p`. -/
theorem pHoare_liftSDistr_map_some {P : CatCrypt.Unary.UPre} (p : PMF α) {Q : α → Prop}
    (hQ : ∀ a ∈ p.support, Q a) :
    CatCrypt.Unary.pHoare P (liftSDistr (p.map some)) (fun a _ => Q a) := by
  intro h₀ _ a h' hsupp
  simp only [liftSDistr, SDistr.bind, PMF.bind_map] at hsupp
  obtain ⟨b, hb, hb'⟩ := (PMF.mem_support_bind_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr hsupp)
  simp only [Function.comp_apply, SDistr.pure, PMF.mem_support_pure_iff, Option.some.injEq,
    Prod.mk.injEq] at hb'
  exact hb'.1 ▸ hQ b hb

/-- A heap-independent sampler is related to itself on equal outputs, from any
pair of heaps. -/
theorem rHoare_liftSDistr_self (d : SDistr α) :
    rHoare (fun _ _ => True) (liftSDistr d) (liftSDistr d) (fun a₁ _ a₂ _ => a₁ = a₂) := by
  intro h₁ h₂ _
  exact liftR_bind (liftR_refl d) fun a b hab => liftR_pure (by exact hab)

end Lift

/-! ## The two protocols -/

namespace Sigma

variable (P : Sigma)

/-- The `SigmaProtocolS` of `P` with the prover randomness as the prover state. -/
noncomputable def toSigmaProtocolS : SigmaProtocolS where
  Statement := P.Stmt
  Witness := P.Wit
  Message := P.Com
  Challenge := P.Ch
  Response := P.Resp
  PState := P.Rand
  relation := P.rel
  commit x w := liftSDistr ((PMF.uniformOfFintype P.Rand).map fun r => some (P.commit x w r, r))
  respond x w r _ e := SPComp.pure (P.respond x w r e)
  verify := P.verify
  simulate x e := liftSDistr ((PMF.uniformOfFintype P.SimRand).map fun s => some (P.simulate x e s))

/-- The response distribution of `toSigmaProtocol P` on the commitment `a`: the
response to `e` from a uniform element of the fibre of `P.commit x w` over `a`. -/
noncomputable def respondDist (x : P.Stmt) (w : P.Wit) (a : P.Com) (e : P.Ch) : PMF P.Resp :=
  (fibreDist (P.commit x w) a).map fun r => P.respond x w r e

/-- The stateless `SigmaProtocol` of `P` with first message `P.Com`: the response
step resamples the prover randomness from the fibre of the commitment. -/
noncomputable def toSigmaProtocol : SigmaProtocol where
  Statement := P.Stmt
  Witness := P.Wit
  Message := P.Com
  Challenge := P.Ch
  Response := P.Resp
  relation := P.rel
  commit x w := liftSDistr (((PMF.uniformOfFintype P.Rand).map (P.commit x w)).map some)
  respond x w a e := liftSDistr ((P.respondDist x w a e).map some)
  verify := P.verify
  simulate x e := liftSDistr (((PMF.uniformOfFintype P.SimRand).map (P.simulate x e)).map some)

/-- The honest run of `toSigmaProtocol P` with challenge `e` is the
heap-independent sampler of `(P.commit x w r, e, P.respond x w r e)` for uniform
`r`. -/
theorem realTranscriptGiven_toSigmaProtocol (x : P.Stmt) (w : P.Wit) (e : P.Ch) :
    realTranscriptGiven P.toSigmaProtocol x w e =
      liftSDistr ((((PMF.uniformOfFintype P.Rand).map
        (fun r => (P.commit x w r, P.respond x w r e))).map
          (fun p => (⟨p.1, e, p.2⟩ : Transcript P.toSigmaProtocol))).map some) := by
  rw [map_pair_eq_bind_fibreDist]
  unfold realTranscriptGiven
  simp only [SPComp.monad_bind_eq, SPComp.monad_pure_eq]
  funext h
  simp only [toSigmaProtocol, SPComp.bind, SPComp.pure, liftSDistr, SDistr.bind, SDistr.pure,
    respondDist, PMF.bind_map, PMF.map_bind, PMF.bind_bind, PMF.map_comp, Function.comp_def,
    PMF.pure_bind]

/-- The simulated run of `toSigmaProtocol P` with challenge `e` is the
heap-independent sampler of `(a, e, z)` for `(a, z) = P.simulate x e s` and uniform
`s`. -/
theorem simulatedTranscriptGiven_toSigmaProtocol (x : P.Stmt) (e : P.Ch) :
    simulatedTranscriptGiven P.toSigmaProtocol x e =
      liftSDistr ((((PMF.uniformOfFintype P.SimRand).map (P.simulate x e)).map
          (fun p => (⟨p.1, e, p.2⟩ : Transcript P.toSigmaProtocol))).map some) := by
  unfold simulatedTranscriptGiven
  simp only [SPComp.monad_bind_eq, SPComp.monad_pure_eq, toSigmaProtocol,
    liftSDistr_map_some_bind]
  funext h
  simp only [liftSDistr, SDistr.bind, PMF.bind_map, PMF.map_comp, Function.comp_def,
    SDistr.pure, SPComp.pure]

/-- `Complete` gives `Completeness` of `toSigmaProtocol P`. -/
theorem completeness_toSigmaProtocol (h : P.Complete) : Completeness P.toSigmaProtocol := by
  refine completeness_of_support _ fun x w e hrel => ?_
  refine pHoare_liftSDistr_map_some (P := fun _ => True) _ fun a ha => ?_
  refine pHoare_liftSDistr_map_some (P := fun _ => True) _ fun z hz => ?_
  obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
  have hc := eq_of_mem_support_fibreDist (P.commit x w) ha hr
  subst hc
  exact h x w hrel r e

/-- `SpecialSound` gives `SpecialSoundness` of `toSigmaProtocol P`, with the
extractor of `P`. -/
theorem specialSoundness_toSigmaProtocol (h : P.SpecialSound) :
    SpecialSoundness P.toSigmaProtocol :=
  ⟨fun x tt => P.extract x tt.message tt.challenge1 tt.response1 tt.challenge2 tt.response2,
    fun x tt => h x _ _ _ _ _ tt.accept1 tt.accept2 tt.diff⟩

/-- `PerfectHVZK` gives `SHVZK_given` of `toSigmaProtocol P` when every pair of the
relation is in the support of the generator. -/
theorem shvzk_given_toSigmaProtocol (h : P.PerfectHVZK)
    (hgen : ∀ x w, P.rel x w → (x, w) ∈ P.gen.support) :
    SHVZK_given P.toSigmaProtocol := by
  intro (x : P.Stmt) (w : P.Wit) (e : P.Ch) hrel
  rw [P.realTranscriptGiven_toSigmaProtocol x w e, P.simulatedTranscriptGiven_toSigmaProtocol x e,
    h x w (hgen x w hrel) e]
  exact rHoare_liftSDistr_self _

/-- `SpecialSound` gives `SpecialSoundness` of the stateless protocol of
`toSigmaProtocolS P`, whose first message carries the prover randomness. -/
theorem specialSoundness_toSigmaProtocolS (h : P.SpecialSound) :
    SpecialSoundness P.toSigmaProtocolS.toSigmaProtocol :=
  ⟨fun x tt => P.extract x tt.message.1 tt.challenge1 tt.response1 tt.challenge2 tt.response2,
    fun x tt => h x _ _ _ _ _ tt.accept1 tt.accept2 tt.diff⟩

end Sigma

end CatCrypt.Crypto.FiatShamirROM
