/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.CompressedSys
public import CatCryptCore.Quantum.QSysIndep
public import CatCryptCore.Crypto.UCMonad.CPCompUC

/-!
# Adaptive reprogramming of the compressed oracle at a fresh point

A signing attempt of a Fiat-Shamir signer draws a sample `ω` from a law `μ` and needs the
value of the random oracle at the point `pt ω`. The signer `signAtt` reads the compressed
oracle at `pt ω`; the programming signer `progAtt` draws a uniform value `v` and writes it at
`pt ω`. On a database whose entry `pt ω` is `⊥` both give a uniform value and the same state:
the read decompresses the entry to the uniform superposition and measures it, the write
decompresses, measures the old value and replaces it by `v` (`readAt_agree`). By gentle
substitution relative to the databases with at most `N` non-`⊥` entries, the two attempts are
within `2 √(N ε)` when every point is `pt ω` with probability at most `ε`
(`reprogram_fresh_le`, `sidistOn_signAtt_progAtt_le`); on an input of trace `π`, the
probability that the attempt is reached, the gap is at most `2 √(π N ε)`.

Signer programs `SignProg` have the operations `read`, `write` and `attempt`; the systems
`signSys` and `progSys` are the compressed challenger whose rounds run the signer program with
the attempts of `signAtt`, respectively `progAtt`. A potential `Φ` on the signer state bounds
the number of operations of the remaining rounds. The hybrid over the activations relative to
the weight of the database (`sidistOn_qloopQ_le_graded`), whose potential depends on the
number of remaining activations, gives `signToProg_le`: the acceptance probabilities of an
environment with `T` activations against the two systems differ by at most
`Φ s₀ · 2 √((T + Φ s₀) ε)`.

## Main definitions

* `ReactiveUC.reprogCost` — the cost `2 √(M ε)` of one reprogramming at weight `M`
* `signAtt`, `progAtt` — a signing attempt that reads, respectively programs, the oracle
* `SignProg`, `SignProg.exec`, `SignProg.ops` — signer programs with attempts
* `signSys`, `progSys` — the compressed challengers with the two kinds of attempts

## Main results

* `ReactiveUC.subst_sparse_on_le` — substitution at a sparse set, relative to a support, at an
  input of any trace at most `1`
* `readAt_agree` — reading and programming agree on the databases with the entry `⊥`
* `reprogram_fresh_le` — adaptive reprogramming at a fresh point, one attempt
* `ReactiveUC.sidistOn_qloopQ_le_graded` — the hybrid over activations with a graded invariant
  and a potential indexed by the remaining activations
* `ReactiveUC.absDiff_viewAcc_le_sidist` — acceptance probabilities and the diamond distance of
  the views
* `signToProg_le` — the reading and the programming challengers, summed over all attempts

## References

* [Barbosa, Barthe, Doczkal, Don, Fehr, Grégoire, Huang, Hülsing, Lee, Wu — Fixing and
  Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium, CRYPTO 2023, ePrint
  2023/246], Lemma 3
* cf. [Grilo, Hövelmanns, Hülsing, Majenz — Tight Adaptive Reprogramming in the QROM,
  ASIACRYPT 2021]
* [Zhandry — How to Record Quantum Queries, and Applications to Quantum
  Indifferentiability, CRYPTO 2019]
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal NNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.UnitaryChannel
open _root_.Quantum CatCrypt.Quantum.ReactiveUC
open CatCrypt.Quantum.OpenSystem (frameLeft frameLeft_bind frameLeft_pure)
open CatCrypt.Crypto.UCMonad.DiamondNorm
open UCMonad.QuantumUC

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

/-! ## Substitution at a sparse set relative to a support -/

section SparseOn

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] {α : Type}
variable {Ω : Type} [Fintype Ω]

open Classical in
/-- **Substitution at a sparse set, relative to a support.** Let `p ω` and `q ω` agree on the
inputs compressed by the projector onto the basis states outside `T ω`, and let each basis state
in `S` lie in `T ω` with probability at most `δ` when `ω` is drawn from `μ`. Then, on a positive
semidefinite input `ρ` of trace at most `1` supported on the states over `S`, the gap between
drawing `ω` and running `p ω`, and drawing `ω` and running `q ω`, is at most
`2 √(δ · tr ρ)`. -/
theorem subst_sparse_on_le (μ : Ω → ℝ≥0) (hμ : ∑ ω, μ ω = 1) (p q : Ω → SubInstrument A B α)
    (T : Ω → Set A)
    (hagree : ∀ ω a (M : Matrix A A ℂ), (p ω).branch a (projOff (T ω) * M * projOff (T ω)) =
      (q ω).branch a (projOff (T ω) * M * projOff (T ω)))
    (S : Set A) (δ : ℝ) (hδ : ∀ x ∈ S, ∑ ω, (μ ω : ℝ) * (if x ∈ T ω then 1 else 0) ≤ δ)
    (r : ℕ) {ρ : Matrix (A × Fin r) (A × Fin r) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (hS : SuppOn (Prod.fst ⁻¹' S) ρ) (ψ : α → QTest (B × Fin r)) :
    absDiff (accept (((sampleLaw μ hμ).bind p).frame (Fin r)) ψ ρ)
      (accept (((sampleLaw μ hμ).bind q).frame (Fin r)) ψ ρ) ≤
      ENNReal.ofReal (2 * √(δ * ρ.trace.re)) := by
  rw [SubInstrument.frame_bind, SubInstrument.frame_bind, sampleLaw_frame, accept_bind _ _ _ hρ,
    accept_bind _ _ _ hρ, accept_sampleLaw _ _ _ hρ, accept_sampleLaw _ _ _ hρ]
  have hdiag : ∀ x, 0 ≤ (ρ x x).re := fun x => (Complex.nonneg_iff.mp hρ.diag_nonneg).1
  have hout : ∀ x : A × Fin r, x.1 ∉ S → (ρ x x).re = 0 := fun x hx => by
    by_contra h
    exact hx (hS x x fun h0 => h (by simp [h0])).1
  set t : Ω → ℝ := fun ω => ((1 - kroneckerMap (· * ·) (projOff (T ω))
    (1 : Matrix (Fin r) (Fin r) ℂ)) * ρ).trace.re with ht
  have hgap : ∀ ω, absDiff ((QTest.comp ((p ω).frame (Fin r)) ψ).toFun ρ)
      ((QTest.comp ((q ω).frame (Fin r)) ψ).toFun ρ) ≤ ENNReal.ofReal (2 * √(t ω)) := fun ω =>
    gentle_subst_le (p ω) (q ω) (projOff (T ω)) (projOff_conjTranspose _) (projOff_mul_self _)
      (hagree ω) r hρ htr ψ
  have ht0 : ∀ ω, 0 ≤ t ω := fun ω => by
    simp only [ht, trace_one_sub_projOff_mul]
    exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hdiag x]
  have hsum : ∑ ω, (μ ω : ℝ) * t ω ≤ δ * ρ.trace.re := by
    calc ∑ ω, (μ ω : ℝ) * t ω
        = ∑ x, (∑ ω, (μ ω : ℝ) * (if x.1 ∈ T ω then 1 else 0)) * (ρ x x).re := by
          simp only [ht, trace_one_sub_projOff_mul, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun ω _ => by
            split_ifs <;> simp
      _ ≤ ∑ x, δ * (ρ x x).re := Finset.sum_le_sum fun x _ => by
          by_cases hx : x.1 ∈ S
          · exact mul_le_mul_of_nonneg_right (hδ x.1 hx) (hdiag x)
          · simp [hout x hx]
      _ = δ * ρ.trace.re := by
          rw [← Finset.mul_sum, Matrix.trace, Complex.re_sum]
          rfl
  have hjensen : ∑ ω, (μ ω : ℝ) * √(t ω) ≤ √(∑ ω, (μ ω : ℝ) * t ω) := by
    have h := Real.strictConcaveOn_sqrt.concaveOn.le_map_sum (t := Finset.univ)
      (w := fun ω => (μ ω : ℝ)) (p := t) (fun ω _ => (μ ω).2)
      (by rw [← NNReal.coe_sum, hμ, NNReal.coe_one]) (fun ω _ => ht0 ω)
    simpa only [smul_eq_mul] using h
  have hfinal : √(∑ ω, (μ ω : ℝ) * t ω) ≤ √(δ * ρ.trace.re) := Real.sqrt_le_sqrt hsum
  have h2 : ∑ ω, (μ ω : ℝ) * (2 * √(t ω)) = 2 * ∑ ω, (μ ω : ℝ) * √(t ω) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ω _ => by ring
  calc absDiff (∑ ω, (μ ω : ℝ≥0∞) * (QTest.comp ((p ω).frame (Fin r)) ψ).toFun ρ)
        (∑ ω, (μ ω : ℝ≥0∞) * (QTest.comp ((q ω).frame (Fin r)) ψ).toFun ρ)
      ≤ ∑ ω, (μ ω : ℝ≥0∞) * absDiff ((QTest.comp ((p ω).frame (Fin r)) ψ).toFun ρ)
          ((QTest.comp ((q ω).frame (Fin r)) ψ).toFun ρ) := by
        refine le_trans ?_ (Finset.sum_le_sum fun ω _ => absDiff_mul_le _ _ _ ENNReal.coe_ne_top)
        simpa only [tsum_fintype] using absDiff_tsum_le
          (fun ω => (μ ω : ℝ≥0∞) * (QTest.comp ((p ω).frame (Fin r)) ψ).toFun ρ)
          (fun ω => (μ ω : ℝ≥0∞) * (QTest.comp ((q ω).frame (Fin r)) ψ).toFun ρ)
    _ ≤ ∑ ω, (μ ω : ℝ≥0∞) * ENNReal.ofReal (2 * √(t ω)) :=
        Finset.sum_le_sum fun ω _ => by gcongr; exact hgap ω
    _ = ENNReal.ofReal (∑ ω, (μ ω : ℝ) * (2 * √(t ω))) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun ω _ => by positivity]
        refine Finset.sum_congr rfl fun ω _ => ?_
        clear ht; simp_all
    _ ≤ ENNReal.ofReal (2 * √(δ * ρ.trace.re)) :=
        ENNReal.ofReal_le_ofReal (by rw [h2]; linarith)

open Classical in
/-- **Substitution at a sparse set, relative distance.** Under the hypotheses of
`subst_sparse_on_le` with `0 ≤ δ`, the distance relative to `S` of drawing `ω` and running
`p ω`, and drawing `ω` and running `q ω`, is at most `2 √δ`. -/
theorem sidistOn_subst_sparse_le (μ : Ω → ℝ≥0) (hμ : ∑ ω, μ ω = 1)
    (p q : Ω → SubInstrument A B α) (T : Ω → Set A)
    (hagree : ∀ ω a (M : Matrix A A ℂ), (p ω).branch a (projOff (T ω) * M * projOff (T ω)) =
      (q ω).branch a (projOff (T ω) * M * projOff (T ω)))
    (S : Set A) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x ∈ S, ∑ ω, (μ ω : ℝ) * (if x ∈ T ω then 1 else 0) ≤ δ) :
    sidistOn S ((sampleLaw μ hμ).bind p) ((sampleLaw μ hμ).bind q) ≤
      ENNReal.ofReal (2 * √δ) :=
  iSup_le fun r => iSup_le fun _ => iSup_le fun hρ => iSup_le fun htr => iSup_le fun hS =>
    iSup_le fun ψ => (subst_sparse_on_le μ hμ p q T hagree S δ hδ r hρ htr hS ψ).trans
      (ENNReal.ofReal_le_ofReal (by gcongr; exact mul_le_of_le_one_right hδ0 htr))

end SparseOn

/-! ## Branches of composites -/

section Branch

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C] {α β : Type}

/-- A sequencing has a zero branch at `b` when, at every intermediate outcome, the first
branch or the continuation's branch at `b` is zero. -/
theorem bind_branch_eq_zero (p : SubInstrument A B α) (k : α → SubInstrument B C β) (b : β)
    (h : ∀ a, p.branch a = 0 ∨ (k a).branch b = 0) : (p.bind k).branch b = 0 := by
  refine LinearMap.ext fun ρ => ?_
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply, LinearMap.zero_apply]
  refine (tsum_congr fun a => ?_).trans tsum_zero
  rcases h a with h | h <;> simp [h]

/-- A nonzero branch of a sequencing passes through an intermediate outcome with nonzero
branches. -/
theorem exists_of_bind_branch_ne_zero (p : SubInstrument A B α) (k : α → SubInstrument B C β)
    (b : β) (h : (p.bind k).branch b ≠ 0) :
    ∃ a, p.branch a ≠ 0 ∧ (k a).branch b ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (bind_branch_eq_zero p k b fun a => by
    by_cases ha : p.branch a = 0
    · exact Or.inl ha
    · exact Or.inr (hc a ha))

/-- A nonzero branch of `pure a` is the branch at `a`. -/
theorem eq_of_pure_branch_ne_zero {a b : α}
    (h : (SubInstrument.pure a : SubInstrument A A α).branch b ≠ 0) : b = a := by
  by_contra hne
  exact h (SubInstrument.branch_pure_of_ne hne)

variable [DecidableEq A] {Ω : Type} [Fintype Ω]

/-- The branch of a classical law followed by `q` is the average of the branches of `q`. -/
theorem sampleLaw_bind_branch (μ : Ω → ℝ≥0) (hμ : ∑ ω, μ ω = 1) (q : Ω → SubInstrument A B β)
    (b : β) (ρ : Matrix A A ℂ) :
    ((sampleLaw μ hμ).bind q).branch b ρ = ∑ ω, (((μ ω : ℝ) : ℂ)) • (q ω).branch b ρ := by
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply, tsum_fintype]
  simp only [sampleLaw_branch, map_smul]

/-- A classical law maps every support to itself. -/
theorem sampleLaw_mapsSupp (μ : Ω → ℝ≥0) (hμ : ∑ ω, μ ω = 1) (S : Set A) :
    MapsSupp (sampleLaw μ hμ : SubInstrument A A Ω) S fun _ => S := by
  intro ω M hM
  rw [sampleLaw_branch]
  exact hM.smul _

/-- The branch of a Kraus measurement relabelled by `f` is the sum of the conjugations by the
operators of the outcomes that `f` sends to the branch. -/
theorem ofKraus_bind_pure_branch {ι : Type} [Fintype ι] [DecidableEq β] (K : ι → Matrix A A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (f : ι → β) (b : β) (ρ : Matrix A A ℂ) :
    ((SubInstrument.ofKraus K hK).bind fun i => SubInstrument.pure (f i)).branch b ρ =
      ∑ i, if f i = b then K i * ρ * (K i)ᴴ else 0 := by
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · subst h
    simp [DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply]
  · rw [SubInstrument.branch_pure_of_ne (Ne.symm h)]
    rfl

end Branch

/-! ## The hybrid with a graded invariant -/

section Graded

variable {H K : Type} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {τ ζ E O : Type} {d : ℕ}

omit [DecidableEq H] [DecidableEq K] in
/-- **Hybrid over activations with a graded invariant.** The invariant `Inv N` of the private
register is indexed by a level `N`; a step of `I` at the state `t` with event `e` maps the
support `Inv N` to `Inv (lvl N t e)`. Suppose that the distance of the steps relative to
`Inv N`, plus the supremum of `V k (lvl N t e) t'` over the states `t'` that a step of `I`
reaches with a nonzero branch, is at most `V (k + 1) N t`. Then the joint runs of `k`
activations from the state `t` are within `V k N t` relative to `Inv N`. -/
theorem sidistOn_qloopQ_le_graded (R I : QSys H τ E O d) (Z : QStratQ K ζ E O d)
    (Inv : ℕ → Set H) (lvl : ℕ → τ → E → ℕ)
    (hI : ∀ N t e, MapsSupp (I.step t e) (Prod.snd ⁻¹' Inv N)
      (fun _ => Prod.snd ⁻¹' Inv (lvl N t e)))
    (V : ℕ → ℕ → τ → ℝ≥0∞)
    (hV : ∀ k N t e, sidistOn (Prod.snd ⁻¹' Inv N) (R.step t e) (I.step t e) +
      ⨆ (p : τ × O) (_ : (I.step t e).branch p ≠ 0), V k (lvl N t e) p.1 ≤ V (k + 1) N t) :
    ∀ (k N : ℕ) (c : ζ × τ), sidistOn (Prod.fst ⁻¹' (Prod.snd ⁻¹' Inv N))
      (qloopQ R Z k c) (qloopQ I Z k c) ≤ V k N c.2 := by
  intro k
  induction k with
  | zero =>
    intro N c
    simp only [qloopQ, sidistOn_self]
    exact bot_le
  | succ k ih =>
    intro N c
    simp only [qloopQ]
    refine (sidistOn_bind_left_of_support _ _ _ (mapsSupp_envPlace H (Inv N) _)).trans
      (iSup₂_le fun a _ => ?_)
    refine (sidistOn_triangle _ _ (((I.step c.2 a.2).frame K).bind fun p =>
      (envPlace H (Z.obs a.1 p.2)).bind fun z => qloopQ R Z k (z, p.1)) _).trans ?_
    refine le_trans (add_le_add ((sidistOn_bind_right _ _ _ _).trans
      (sidistOn_frame _ _ _ K)) ?_) (hV k N c.2 a.2)
    refine (sidistOn_bind_left_of_support _ _ _ ((hI N c.2 a.2).frame K)).trans
      (iSup₂_le fun p hp => ?_)
    have hp' : (I.step c.2 a.2).branch p ≠ 0 := fun h0 =>
      hp (by rw [DSubInstrument.branch_frame_apply, h0, MatrixMap.amplify_zero])
    refine le_iSup₂_of_le p hp' ?_
    exact (sidistOn_bind_left_of_support _ _ _
      (mapsSupp_envPlace H (Inv (lvl N c.2 a.2)) _)).trans (iSup₂_le fun z _ => ih _ (z, p.1))

omit [DecidableEq K] in
/-- The views of an environment against `R` and against `I` are within `V Z.rounds N₀ R.init`,
under the hypotheses of `sidistOn_qloopQ_le_graded`, when the two systems start in the same
state and the same basis state of the private register, which lies in `Inv N₀`. -/
theorem sidist_qview_le_graded (R I : QSys H τ E O d) (Z : QStrat ζ E O d)
    (Inv : ℕ → Set H) (lvl : ℕ → τ → E → ℕ)
    (hI : ∀ N t e, MapsSupp (I.step t e) (Prod.snd ⁻¹' Inv N)
      (fun _ => Prod.snd ⁻¹' Inv (lvl N t e)))
    (V : ℕ → ℕ → τ → ℝ≥0∞)
    (hV : ∀ k N t e, sidistOn (Prod.snd ⁻¹' Inv N) (R.step t e) (I.step t e) +
      ⨆ (p : τ × O) (_ : (I.step t e).branch p ≠ 0), V k (lvl N t e) p.1 ≤ V (k + 1) N t)
    (hinit : R.init = I.init) (hreg : R.initReg = I.initReg) (N₀ : ℕ)
    (hmem : R.initReg ∈ Inv N₀) :
    sidist (qview R Z) (qview I Z) ≤ V Z.rounds N₀ R.init := by
  rw [← qviewQ_toQ, ← qviewQ_toQ]
  simp only [qviewQ, ← hinit, ← hreg]
  refine (sidist_le_sidistOn_univ _ _).trans ?_
  refine (sidistOn_bind_left_of_support _ _ _ (mapsSupp_appendBasis R.initReg _)).trans
    (iSup₂_le fun _ _ => ?_)
  refine (sidistOn_bind_left_of_support _ _ _ (mapsSupp_appendBasis Z.toQ.initReg _)).trans
    (iSup₂_le fun _ _ => ?_)
  refine (sidistOn_bind_right _ _ _ _).trans ?_
  refine (sidistOn_mono ?_ _ _).trans
    (sidistOn_qloopQ_le_graded R I Z.toQ Inv lvl hI V hV _ N₀ _)
  rintro x ⟨⟨-, hx⟩, -⟩
  change x.1.2 ∈ Inv N₀
  rw [hx]
  exact hmem

end Graded

/-! ## Acceptance probabilities and the distance of the views -/

section Accept

variable {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
variable {τ υ ζ E O : Type} {d : ℕ}

/-- The acceptance probabilities of an environment against two systems differ by at most the
diamond distance of its views. -/
theorem absDiff_viewAcc_le_sidist (R : QSys H τ E O d) (I : QSys H' υ E O d)
    (G : CatCrypt.Quantum.QROM.QStratAcc ζ E O d) :
    absDiff (CatCrypt.Quantum.QROM.viewAcc R G) (CatCrypt.Quantum.QROM.viewAcc I G) ≤
      sidist (qview R G.strat) (qview I G.strat) := by
  have h1 : absDiff (CatCrypt.Quantum.QROM.viewAcc R G) (CatCrypt.Quantum.QROM.viewAcc I G) ≤
      CatCrypt.Crypto.UCMonad.CPCompUC.cpSdist (fun _ : Unit => qview R G.strat)
        (fun _ => qview I G.strat) :=
    le_iSup_of_le G.post (le_iSup_of_le () (le_iSup_of_le G.init le_rfl))
  refine h1.trans ((CatCrypt.Crypto.UCMonad.CPCompUC.cpSdist_le_qdistDiamond _ _).trans ?_)
  exact (qdistDiamond_toQComp_le _ _).trans (iSup_le fun _ => le_rfl)

end Accept

/-- The cost `2 √(M ε)` of one reprogramming at a database of weight at most `M`, for a law
under which every point has probability at most `ε`. -/
def reprogCost (ε : ℝ≥0) (M : ℕ) : ℝ≥0∞ := ENNReal.ofReal (2 * √((M : ℝ) * ε))

/-- The cost of a reprogramming grows with the weight. -/
theorem reprogCost_mono (ε : ℝ≥0) {M M' : ℕ} (h : M ≤ M') : reprogCost ε M ≤ reprogCost ε M' := by
  unfold reprogCost
  gcongr

end CatCrypt.Quantum.ReactiveUC

namespace CatCrypt.Quantum.QROM

/-! ## Reading and programming at one point -/

section Agree

variable {m n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Operators on the entry `x` multiply entrywise on that entry. -/
theorem dbOp_update_mul (x : Fin m) (Z Z' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    dbOp m n (Function.update 1 x Z) * dbOp m n (Function.update 1 x Z') =
      dbOp m n (Function.update 1 x (Z * Z')) := by
  rw [dbOp_mul]
  congr 1
  funext x'
  by_cases hx : x' = x
  · subst hx; simp
  · simp [Function.update_of_ne hx]

omit [NeZero n] in
/-- A scalar on the entry `x` is a scalar of the database operator. -/
theorem dbOp_update_smul (x : Fin m) (s : ℂ) (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    dbOp m n (Function.update 1 x (s • Z)) = s • dbOp m n (Function.update 1 x Z) := by
  ext i j
  simp only [dbOp_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ x)]
  simp only [Function.update_self, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun x' hx' => by
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hx')]

/-- The operator `Dec |a⟩⟨⊥|` on the entry `x`, from the empty entry to the decompression of
the value `a`. -/
def freshOp (x : Fin m) (a : Fin (n + 1)) : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  dbOp m n (Function.update 1 x (decompEntry n * Matrix.single a (Fin.last n) 1))

/-- The operator `Dec |a⟩⟨b| Dec` on the entry `x`, restricted to the empty entry, is
`⟨b|Dec|⊥⟩ · Dec |a⟩⟨⊥|`. -/
theorem conj_single_mul_readP_last (x : Fin m) (a b : Fin (n + 1)) :
    decompDB m n * dbOp m n (Function.update 1 x (Matrix.single a b 1)) * decompDB m n *
        readP x (Fin.last n) = entryUniform n b • freshOp x a := by
  rw [decompDB_mul_dbOp_update_mul, readP, dbOp_update_mul, freshOp, ← dbOp_update_smul]
  congr 2
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.single a b 1),
    Matrix.single_mul_mul_single, decompEntry_apply_last, one_mul, mul_one, ← Matrix.mul_smul,
    Matrix.smul_single, smul_eq_mul, mul_one]

/-- The databases on the joint register whose entry `x` is not `⊥`. -/
def entrySet (d : ℕ) (x : Fin m) : Set (Fin d × Fin ((n + 1) ^ m)) :=
  {y | (dbIndex m n).symm y.2 x ≠ Fin.last n}

omit [NeZero n] in
/-- The projector onto the databases with the entry `x` equal to `⊥`. -/
theorem projOff_entrySet (d : ℕ) (x : Fin m) :
    projOff (entrySet (n := n) d x) = liftL (Fin d) (readP (n := n) x (Fin.last n)) := by
  ext y y'
  rw [liftL_apply, readP, dbOp_update_single_apply]
  simp only [projOff, entrySet, Matrix.diagonal_apply, Set.mem_ofPred_eq]
  have hset : ∀ k : Fin ((n + 1) ^ m), (dbIndex m n).symm k x = Fin.last n →
      dbSet k x (Fin.last n) = k := fun k hk => by
    simp only [dbSet, ← hk, Function.update_eq_self, Equiv.apply_symm_apply]
  obtain ⟨y1, y2⟩ := y
  obtain ⟨y1', y2'⟩ := y'
  by_cases hx : (dbIndex m n).symm y2' x = Fin.last n
  · have := hset y2' hx
    by_cases h1 : y1 = y1' <;> by_cases h2 : y2 = y2' <;> simp_all
  · by_cases h1 : y1 = y1' <;> by_cases h2 : y2 = y2' <;> simp_all

variable {Ω : Type}

/-- The uniform law on `Fin n`. -/
def unifLaw (n : ℕ) : Fin n → ℝ≥0 := fun _ => (n : ℝ≥0)⁻¹

theorem unifLaw_sum : ∑ v, unifLaw n v = 1 := by
  simp [unifLaw, NeZero.ne n]

/-- Reading the oracle at `x` in a signing attempt with sample `ω`: the read value is the
second outcome. -/
def readAt (d : ℕ) (x : Fin m) (ω : Ω) :
    SubInstrument (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) (Ω × Fin n) :=
  (frameLeft (readOp x) (Fin d)).bind fun c => SubInstrument.pure (ω, truncEntry n c)

/-- Programming the oracle at `x` in a signing attempt with sample `ω`: draw a uniform value
`v`, write it at `x`, return it. -/
def progAt (d : ℕ) (x : Fin m) (ω : Ω) :
    SubInstrument (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) (Ω × Fin n) :=
  (sampleLaw (unifLaw n) unifLaw_sum).bind fun v =>
    (frameLeft (writeOp x v) (Fin d)).bind fun _ => SubInstrument.pure (ω, v)

/-- The conjugation of `M` by the lifted operator `freshOp x a`. -/
def freshConj (d : ℕ) (x : Fin m) (a : Fin (n + 1))
    (M : Matrix (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) ℂ) :
    Matrix (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) ℂ :=
  liftL (Fin d) (freshOp x a) * M * (liftL (Fin d) (freshOp x a))ᴴ

omit [NeZero n] in
/-- Lifting commutes with scalars. -/
theorem liftL_smul {L X : Type} [DecidableEq L] (s : ℂ) (K : Matrix X X ℂ) :
    liftL L (s • K) = s • liftL L K := by
  ext x y
  simp only [liftL_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The conjugation by a scalar multiple. -/
theorem smul_mul_conjTranspose {X : Type} [Fintype X] (s : ℂ) (L M : Matrix X X ℂ) :
    (s • L) * M * (s • L)ᴴ = (s * star s) • (L * M * Lᴴ) := by
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The uniform superposition of an entry is a unit vector. -/
theorem entryUniform_sum_mul_star :
    ∑ u, entryUniform n u * star (entryUniform n u) = 1 := by
  simp only [entryUniform_mul_star, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.is_lt,
    ite_true, Fin.val_last, lt_irrefl, ite_false, Complex.ofReal_zero, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n))

/-- A read Kraus operator restricted to the empty entry. -/
theorem readK_mul_readP_last (x : Fin m) (c : Fin (n + 1)) :
    readK x c * readP x (Fin.last n) = entryUniform n c • freshOp x c :=
  conj_single_mul_readP_last x c c

/-- A write Kraus operator restricted to the empty entry. -/
theorem writeK_mul_readP_last (x : Fin m) (v : Fin n) (u : Fin (n + 1)) :
    writeK x v u * readP x (Fin.last n) = entryUniform n u • freshOp x v.castSucc :=
  conj_single_mul_readP_last x v.castSucc u

omit [NeZero n] in
/-- Conjugating an input compressed to the empty entry `x` by a lifted operator `K` is
conjugating the input by the lift of `K` restricted to the empty entry. -/
theorem liftL_conj_projOff (d : ℕ) (x : Fin m)
    (K : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ)
    (M : Matrix (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) ℂ) :
    liftL (Fin d) K * (projOff (entrySet d x) * M * projOff (entrySet d x)) *
        (liftL (Fin d) K)ᴴ =
      liftL (Fin d) (K * readP x (Fin.last n)) * M *
        (liftL (Fin d) (K * readP x (Fin.last n)))ᴴ := by
  have hPh := projOff_conjTranspose (entrySet (n := n) d x)
  rw [← liftL_mul, ← projOff_entrySet, conjTranspose_mul, hPh]
  simp only [Matrix.mul_assoc]

/-- On an input compressed to the empty entry `x`, the branch of `readAt` at `(ω', v)` is
`[ω' = ω] n⁻¹ · Dec|v⟩⟨⊥| M |⊥⟩⟨v|Dec`. -/
theorem readAt_branch_proj (d : ℕ) (x : Fin m) (ω : Ω) [DecidableEq Ω] (b : Ω × Fin n)
    (M : Matrix (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) ℂ) :
    (readAt d x ω).branch b (projOff (entrySet d x) * M * projOff (entrySet d x)) =
      if b.1 = ω then ((n : ℂ)⁻¹) • freshConj d x b.2.castSucc M else 0 := by
  rw [readAt, readOp, frameLeft_ofKraus, ofKraus_bind_pure_branch]
  simp only [liftL_conj_projOff, readK_mul_readP_last, liftL_smul, smul_mul_conjTranspose]
  rw [Fin.sum_univ_castSucc]
  obtain ⟨b1, b2⟩ := b
  simp only [truncEntry_castSucc, entryUniform_mul_star, Fin.val_castSucc, Fin.is_lt,
    Fin.val_last, lt_irrefl, ite_true, ite_false, Complex.ofReal_zero, zero_smul, ite_self,
    add_zero, Prod.mk.injEq]
  by_cases h : ω = b1 <;> simp [h, eq_comm, freshConj]

/-- On an input compressed to the empty entry `x`, the branch of `progAt` at `(ω', v)` is
`[ω' = ω] n⁻¹ · Dec|v⟩⟨⊥| M |⊥⟩⟨v|Dec`. -/
theorem progAt_branch_proj (d : ℕ) (x : Fin m) (ω : Ω) [DecidableEq Ω] (b : Ω × Fin n)
    (M : Matrix (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) ℂ) :
    (progAt d x ω).branch b (projOff (entrySet d x) * M * projOff (entrySet d x)) =
      if b.1 = ω then ((n : ℂ)⁻¹) • freshConj d x b.2.castSucc M else 0 := by
  rw [progAt, sampleLaw_bind_branch]
  simp only [writeOp, frameLeft_bind, frameLeft_pure, frameLeft_ofKraus,
    SubInstrument.bind_assoc, SubInstrument.pure_bind, ofKraus_bind_pure_branch,
    liftL_conj_projOff, writeK_mul_readP_last, liftL_smul, smul_mul_conjTranspose]
  obtain ⟨b1, b2⟩ := b
  simp only [Prod.mk.injEq]
  by_cases h : ω = b1
  · subst h
    simp only [true_and, ite_true]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_smul,
      entryUniform_sum_mul_star, one_smul, unifLaw, freshConj, NNReal.coe_inv,
      NNReal.coe_natCast, Complex.ofReal_inv, Complex.ofReal_natCast]
  · simp [h, Ne.symm h]

/-- **Reading and programming agree at an empty entry.** On the inputs compressed to the
databases with the entry `x` equal to `⊥`, reading `x` and writing a fresh uniform value at
`x` have the same branches. -/
theorem readAt_agree (d : ℕ) (x : Fin m) (ω : Ω) (b : Ω × Fin n)
    (M : Matrix (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) ℂ) :
    (readAt d x ω).branch b (projOff (entrySet d x) * M * projOff (entrySet d x)) =
      (progAt d x ω).branch b (projOff (entrySet d x) * M * projOff (entrySet d x)) := by
  classical
  rw [readAt_branch_proj, progAt_branch_proj]

variable [Fintype Ω]

/-- A signing attempt that reads the oracle at the point `pt ω` of a sample `ω` drawn
from `μ`. -/
def signAtt (d : ℕ) (μ : Ω → ℝ≥0) (hμ : ∑ ω, μ ω = 1) (pt : Ω → Fin m) :
    SubInstrument (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) (Ω × Fin n) :=
  (sampleLaw μ hμ).bind fun ω => readAt d (pt ω) ω

/-- A signing attempt that programs the oracle at the point `pt ω` of a sample `ω` drawn
from `μ` with a fresh uniform value. -/
def progAtt (d : ℕ) (μ : Ω → ℝ≥0) (hμ : ∑ ω, μ ω = 1) (pt : Ω → Fin m) :
    SubInstrument (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) (Ω × Fin n) :=
  (sampleLaw μ hμ).bind fun ω => progAt d (pt ω) ω

omit [NeZero n] in
open Classical in
/-- On a database with at most `N` non-`⊥` entries, the entry `pt ω` is not `⊥` with
probability at most `N ε`. -/
theorem sum_entrySet_le (d : ℕ) (μ : Ω → ℝ≥0) (pt : Ω → Fin m) (ε : ℝ≥0)
    (hε : ∀ z, ∑ ω, (μ ω : ℝ) * (if pt ω = z then 1 else 0) ≤ ε) (N : ℕ)
    (y : Fin d × Fin ((n + 1) ^ m)) (hy : y ∈ Prod.snd ⁻¹' dbLe m n N) :
    ∑ ω, (μ ω : ℝ) * (if y ∈ entrySet d (pt ω) then 1 else 0) ≤ N * ε := by
  set F := Finset.univ.filter fun z => (dbIndex m n).symm y.2 z ≠ Fin.last n with hF
  have hind : ∀ ω, (if y ∈ entrySet d (pt ω) then (1 : ℝ) else 0) =
      ∑ z ∈ F, if pt ω = z then 1 else 0 := fun ω => by
    rw [Finset.sum_ite_eq]
    by_cases h : (dbIndex m n).symm y.2 (pt ω) = Fin.last n <;> simp [entrySet, F, h]
  have hcard : (F.card : ℝ) ≤ N := by
    have : F.card = dbWeight (m := m) (n := n) y.2 := rfl
    rw [this]
    exact_mod_cast hy
  calc ∑ ω, (μ ω : ℝ) * (if y ∈ entrySet d (pt ω) then 1 else 0)
      = ∑ z ∈ F, ∑ ω, (μ ω : ℝ) * (if pt ω = z then 1 else 0) := by
        simp only [hind, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ _z ∈ F, (ε : ℝ) := Finset.sum_le_sum fun z _ => hε z
    _ = F.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * ε := by gcongr

/-- **Adaptive reprogramming at a fresh point** (after BBD+23 Lemma 3, with the factor `√(tr ρ)`
in place of the linear factor `tr ρ`). Let every point be `pt ω`
with probability at most `ε` when `ω` is drawn from `μ`. On a positive semidefinite input `ρ`
of trace at most `1` supported on the databases with at most `N` non-`⊥` entries, the gap
between the reading attempt and the programming attempt is at most `2 √(tr ρ · N ε)`; the
trace of `ρ` is the probability that the attempt is reached. -/
theorem reprogram_fresh_le (d : ℕ) (μ : Ω → ℝ≥0) (hμ : ∑ ω, μ ω = 1) (pt : Ω → Fin m)
    (ε : ℝ≥0) (hε : ∀ z, ∑ ω, (μ ω : ℝ) * (if pt ω = z then 1 else 0) ≤ ε) (N : ℕ) (r : ℕ)
    {ρ : Matrix ((Fin d × Fin ((n + 1) ^ m)) × Fin r) ((Fin d × Fin ((n + 1) ^ m)) × Fin r) ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (hS : SuppOn (Prod.fst ⁻¹' (Prod.snd ⁻¹' dbLe m n N)) ρ) (ψ : Ω × Fin n → QTest _) :
    absDiff (accept ((signAtt d μ hμ pt).frame (Fin r)) ψ ρ)
      (accept ((progAtt d μ hμ pt).frame (Fin r)) ψ ρ) ≤
      ENNReal.ofReal (2 * √(N * ε * ρ.trace.re)) := by
  classical
  exact subst_sparse_on_le μ hμ (fun ω => readAt d (pt ω) ω) (fun ω => progAt d (pt ω) ω)
    (fun ω => entrySet d (pt ω)) (fun ω => readAt_agree d (pt ω) ω) _ (N * ε)
    (fun y hy => sum_entrySet_le d μ pt ε hε N y hy) r hρ htr hS ψ

/-- **Adaptive reprogramming at a fresh point, relative distance.** Relative to the databases
with at most `N` non-`⊥` entries, the reading and the programming attempts are within
`2 √(N ε)`. -/
theorem sidistOn_signAtt_progAtt_le (d : ℕ) (μ : Ω → ℝ≥0) (hμ : ∑ ω, μ ω = 1)
    (pt : Ω → Fin m) (ε : ℝ≥0)
    (hε : ∀ z, ∑ ω, (μ ω : ℝ) * (if pt ω = z then 1 else 0) ≤ ε) (N : ℕ) :
    sidistOn (Prod.snd ⁻¹' dbLe m n N) (signAtt d μ hμ pt) (progAtt d μ hμ pt) ≤
      reprogCost ε N := by
  classical
  exact sidistOn_subst_sparse_le μ hμ (fun ω => readAt d (pt ω) ω) (fun ω => progAt d (pt ω) ω)
    (fun ω => entrySet d (pt ω)) (fun ω => readAt_agree d (pt ω) ω) _ (N * ε) (by positivity)
    (fun y hy => sum_entrySet_le d μ pt ε hε N y hy)

omit [Fintype Ω] in
/-- Reading adds at most one non-`⊥` entry. -/
theorem readAt_mapsSupp (d : ℕ) (x : Fin m) (ω : Ω) (N : ℕ) :
    MapsSupp (readAt d x ω) (Prod.snd ⁻¹' dbLe m n N)
      (fun _ => Prod.snd ⁻¹' dbLe m n (N + 1)) :=
  MapsSupp.bind' (readOp_mapsSupp x N) fun _ => mapsSupp_pure _ _

omit [Fintype Ω] in
/-- Programming adds at most one non-`⊥` entry. -/
theorem progAt_mapsSupp (d : ℕ) (x : Fin m) (ω : Ω) (N : ℕ) :
    MapsSupp (progAt d x ω) (Prod.snd ⁻¹' dbLe m n N)
      (fun _ => Prod.snd ⁻¹' dbLe m n (N + 1)) :=
  MapsSupp.bind' (sampleLaw_mapsSupp _ _ _) fun v =>
    MapsSupp.bind' (writeOp_mapsSupp x v N) fun _ => mapsSupp_pure _ _

/-- A reading attempt adds at most one non-`⊥` entry. -/
theorem signAtt_mapsSupp (d : ℕ) (μ : Ω → ℝ≥0) (hμ : ∑ ω, μ ω = 1) (pt : Ω → Fin m) (N : ℕ) :
    MapsSupp (signAtt d μ hμ pt) (Prod.snd ⁻¹' dbLe m n N)
      (fun _ => Prod.snd ⁻¹' dbLe m n (N + 1)) :=
  MapsSupp.bind' (sampleLaw_mapsSupp _ _ _) fun ω => readAt_mapsSupp d (pt ω) ω N

/-- A programming attempt adds at most one non-`⊥` entry. -/
theorem progAtt_mapsSupp (d : ℕ) (μ : Ω → ℝ≥0) (hμ : ∑ ω, μ ω = 1) (pt : Ω → Fin m) (N : ℕ) :
    MapsSupp (progAtt d μ hμ pt) (Prod.snd ⁻¹' dbLe m n N)
      (fun _ => Prod.snd ⁻¹' dbLe m n (N + 1)) :=
  MapsSupp.bind' (sampleLaw_mapsSupp _ _ _) fun ω => progAt_mapsSupp d (pt ω) ω N

end Agree

/-! ## Signer programs with attempts -/

/-- A signer program over the compressed oracle: `read x` and `write x v` as in `RWProg`, and
`attempt μ hμ pt k`, which draws a sample `ω` from the law `μ`, obtains a value `v` of the oracle
at the point `pt ω` and continues with `k ω v`. -/
inductive SignProg (m n : ℕ) (Ω : Type) [Fintype Ω] (α : Type) where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Read the oracle at `x`, continue with the value. -/
  | read (x : Fin m) (k : Fin n → SignProg m n Ω α)
  /-- Reprogram the oracle at `x` to `v`, continue. -/
  | write (x : Fin m) (v : Fin n) (k : SignProg m n Ω α)
  /-- Draw `ω` from `μ`, obtain a value at `pt ω`, continue with the sample and the value. -/
  | attempt (μ : Ω → ℝ≥0) (hμ : ∑ ω, μ ω = 1) (pt : Ω → Fin m)
      (k : Ω → Fin n → SignProg m n Ω α)

namespace SignProg

variable {m n : ℕ} {Ω : Type} [Fintype Ω] {α : Type}

/-- The largest number of operations on a path of the program. -/
def ops : SignProg m n Ω α → ℕ
  | ret _ => 0
  | read _ k => Finset.univ.sup (fun v => (k v).ops) + 1
  | write _ _ k => k.ops + 1
  | attempt _ _ _ k => Finset.univ.sup (fun p : Ω × Fin n => (k p.1 p.2).ops) + 1

/-- Every attempt of the program draws its point so that each point has probability at most
`ε`. -/
def Sparse (ε : ℝ≥0) : SignProg m n Ω α → Prop
  | ret _ => True
  | read _ k => ∀ v, (k v).Sparse ε
  | write _ _ k => k.Sparse ε
  | attempt μ _ pt k => (∀ z, ∑ ω, (μ ω : ℝ) * (if pt ω = z then 1 else 0) ≤ ε) ∧
      ∀ ω v, (k ω v).Sparse ε

/-- The program can return `b` on some path. -/
def Yields : SignProg m n Ω α → α → Prop
  | ret a, b => b = a
  | read _ k, b => ∃ v, (k v).Yields b
  | write _ _ k, b => k.Yields b
  | attempt _ _ _ k, b => ∃ ω v, (k ω v).Yields b

variable [NeZero n]

/-- The run of a program on the joint register: `read` and `write` are the operations of the
compressed oracle on the database register, and an attempt runs `att`. -/
def exec {d : ℕ} (att : (μ : Ω → ℝ≥0) → (∑ ω, μ ω = 1) → (Ω → Fin m) →
      SubInstrument (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) (Ω × Fin n)) :
    SignProg m n Ω α → SubInstrument (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) α
  | ret a => SubInstrument.pure a
  | read x k => (frameLeft (readOp x) (Fin d)).bind fun c => (k (truncEntry n c)).exec att
  | write x v k => (frameLeft (writeOp x v) (Fin d)).bind fun _ => k.exec att
  | attempt μ hμ pt k => (att μ hμ pt).bind fun r => (k r.1 r.2).exec att

/-- Every program returns some value on some path. -/
theorem exists_yields (p : SignProg m n Ω α) : ∃ a, p.Yields a := by
  induction p with
  | ret a => exact ⟨a, rfl⟩
  | read x k ih =>
    obtain ⟨a, h⟩ := ih 0
    exact ⟨a, 0, h⟩
  | write x v k ih => exact ih
  | attempt μ hμ pt k ih =>
    obtain ⟨ω, -⟩ : ∃ ω, μ ω ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hμ
    obtain ⟨a, h⟩ := ih ω 0
    exact ⟨a, ω, 0, h⟩

/-- A nonzero branch of the run of a program is at a value the program yields. -/
theorem yields_of_branch_ne_zero {d : ℕ}
    (att : (μ : Ω → ℝ≥0) → (∑ ω, μ ω = 1) → (Ω → Fin m) →
      SubInstrument (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) (Ω × Fin n))
    (p : SignProg m n Ω α) (a : α) (h : (p.exec att).branch a ≠ 0) : p.Yields a := by
  induction p with
  | ret b => exact eq_of_pure_branch_ne_zero h
  | read x k ih =>
    rw [exec] at h
    obtain ⟨c, -, hc⟩ := exists_of_bind_branch_ne_zero _ _ _ h
    exact ⟨_, ih _ hc⟩
  | write x v k ih =>
    rw [exec] at h
    obtain ⟨_, -, hc⟩ := exists_of_bind_branch_ne_zero _ _ _ h
    exact ih hc
  | attempt μ hμ pt k ih =>
    rw [exec] at h
    obtain ⟨r, -, hc⟩ := exists_of_bind_branch_ne_zero _ _ _ h
    exact ⟨r.1, r.2, ih _ _ hc⟩

/-- **Weight of a run.** If every attempt adds at most one non-`⊥` entry, the run of a program
adds at most its number of operations. -/
theorem exec_mapsSupp {d : ℕ}
    (att : (μ : Ω → ℝ≥0) → (∑ ω, μ ω = 1) → (Ω → Fin m) →
      SubInstrument (Fin d × Fin ((n + 1) ^ m)) (Fin d × Fin ((n + 1) ^ m)) (Ω × Fin n))
    (hatt : ∀ μ hμ pt N, MapsSupp (att μ hμ pt) (Prod.snd ⁻¹' dbLe m n N)
      (fun _ => Prod.snd ⁻¹' dbLe m n (N + 1)))
    (p : SignProg m n Ω α) (N : ℕ) :
    MapsSupp (p.exec att) (Prod.snd ⁻¹' dbLe m n N)
      (fun _ => Prod.snd ⁻¹' dbLe m n (N + p.ops)) := by
  induction p generalizing N with
  | ret a => exact mapsSupp_pure a _
  | read x k ih =>
    rw [exec]
    refine MapsSupp.bind' (readOp_mapsSupp x N) fun c =>
      MapsSupp.mono_right (ih (truncEntry n c) (N + 1)) fun _ =>
        Set.preimage_mono (dbLe_mono ?_)
    have := Finset.le_sup (f := fun v => (k v).ops) (Finset.mem_univ (truncEntry n c))
    simp only [ops]
    omega
  | write x v k ih =>
    rw [exec]
    refine MapsSupp.bind' (writeOp_mapsSupp x v N) fun _ =>
      MapsSupp.mono_right (ih (N + 1)) fun _ => Set.preimage_mono (dbLe_mono ?_)
    simp only [ops]
    omega
  | attempt μ hμ pt k ih =>
    rw [exec]
    refine MapsSupp.bind' (hatt μ hμ pt N) fun r =>
      MapsSupp.mono_right (ih r.1 r.2 (N + 1)) fun _ => Set.preimage_mono (dbLe_mono ?_)
    have := Finset.le_sup (f := fun p : Ω × Fin n => (k p.1 p.2).ops) (Finset.mem_univ r)
    simp only [ops]
    omega

/-- **Reprogramming in a signer program.** Relative to the databases with at most `N`
non-`⊥` entries, the runs of a sparse program with reading and with programming attempts are
within `ops · 2 √((N + ops) ε)`. -/
theorem exec_sidistOn_le (d : ℕ) (ε : ℝ≥0) (p : SignProg m n Ω α) (hp : p.Sparse ε) (N : ℕ) :
    sidistOn (Prod.snd ⁻¹' dbLe m n N) (p.exec (signAtt d)) (p.exec (progAtt d)) ≤
      p.ops * reprogCost ε (N + p.ops) := by
  induction p generalizing N with
  | ret a =>
    rw [exec, exec, sidistOn_self]
    exact bot_le
  | read x k ih =>
    rw [exec, exec]
    refine (sidistOn_bind_left_of_support _ _ _ (readOp_mapsSupp x N)).trans
      (iSup₂_le fun c _ => ?_)
    refine (ih _ (hp _) (N + 1)).trans ?_
    have := Finset.le_sup (f := fun v => (k v).ops) (Finset.mem_univ (truncEntry n c))
    exact mul_le_mul' (by simp only [ops]; exact_mod_cast (by omega))
      (reprogCost_mono ε (by simp only [ops]; omega))
  | write x v k ih =>
    rw [exec, exec]
    refine (sidistOn_bind_left_of_support _ _ _ (writeOp_mapsSupp x v N)).trans
      (iSup₂_le fun _ _ => ?_)
    refine (ih hp (N + 1)).trans ?_
    exact mul_le_mul' (by simp only [ops]; exact_mod_cast (by omega))
      (reprogCost_mono ε (by simp only [ops]; omega))
  | attempt μ hμ pt k ih =>
    rw [exec, exec]
    obtain ⟨hε, hk⟩ := hp
    have hops : (attempt μ hμ pt k).ops =
        Finset.univ.sup (fun p : Ω × Fin n => (k p.1 p.2).ops) + 1 := rfl
    rw [hops]
    refine (sidistOn_triangle _ _
      ((progAtt d μ hμ pt).bind fun r => (k r.1 r.2).exec (signAtt d)) _).trans ?_
    have h1 : sidistOn (Prod.snd ⁻¹' dbLe m n N)
        ((signAtt d μ hμ pt).bind fun r => (k r.1 r.2).exec (signAtt d))
        ((progAtt d μ hμ pt).bind fun r => (k r.1 r.2).exec (signAtt d)) ≤
        reprogCost ε (N + (Finset.univ.sup (fun p : Ω × Fin n => (k p.1 p.2).ops) + 1)) :=
      (sidistOn_bind_right _ _ _ _).trans ((sidistOn_signAtt_progAtt_le d μ hμ pt ε hε N).trans
        (reprogCost_mono ε (by omega)))
    have h2 : sidistOn (Prod.snd ⁻¹' dbLe m n N)
        ((progAtt d μ hμ pt).bind fun r => (k r.1 r.2).exec (signAtt d))
        ((progAtt d μ hμ pt).bind fun r => (k r.1 r.2).exec (progAtt d)) ≤
        (Finset.univ.sup (fun p : Ω × Fin n => (k p.1 p.2).ops) : ℕ) *
          reprogCost ε (N + (Finset.univ.sup (fun p : Ω × Fin n => (k p.1 p.2).ops) + 1)) := by
      refine (sidistOn_bind_left_of_support _ _ _ (progAtt_mapsSupp d μ hμ pt N)).trans
        (iSup₂_le fun r _ => ?_)
      refine (ih r.1 r.2 (hk r.1 r.2) (N + 1)).trans ?_
      have := Finset.le_sup (f := fun p : Ω × Fin n => (k p.1 p.2).ops) (Finset.mem_univ r)
      exact mul_le_mul' (by exact_mod_cast this) (reprogCost_mono ε (by omega))
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    push_cast
    ring

end SignProg

/-! ## The reading and the programming challengers -/

section Systems

variable {m n w c a : ℕ} [NeZero n] {σ ζ Ω : Type} [Fintype Ω]

/-- The step of a compressed challenger whose rounds run the signer program `sig s y` with the
attempts `att`: a query applies `cmpQuery`. -/
def signerStep (att : (μ : Ω → ℝ≥0) → (∑ ω, μ ω = 1) → (Ω → Fin m) →
      SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m))
        (Fin (m * n * w) × Fin ((n + 1) ^ m)) (Ω × Fin n))
    (sig : σ → Fin c → SignProg m n Ω (σ × Fin a)) (s : σ) :
    QROMEvent c → SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m))
      (Fin (m * n * w) × Fin ((n + 1) ^ m)) (σ × QROMOut a)
  | .query => (cmpQuery m n w).bind fun _ => SubInstrument.pure (s, .done)
  | .round y => ((sig s y).exec att).bind fun r => SubInstrument.pure (r.1, .answer r.2)

/-- **The reading challenger.** The compressed challenger whose signer reads the oracle in its
attempts. -/
def signSys (s₀ : σ) (sig : σ → Fin c → SignProg m n Ω (σ × Fin a)) :
    QSys (Fin ((n + 1) ^ m)) σ (QROMEvent c) (QROMOut a) (m * n * w) where
  init := s₀
  initReg := dbEmptyIdx m n
  step := signerStep (signAtt (m * n * w)) sig

/-- **The programming challenger.** The compressed challenger whose signer programs the oracle
with fresh uniform values in its attempts. -/
def progSys (s₀ : σ) (sig : σ → Fin c → SignProg m n Ω (σ × Fin a)) :
    QSys (Fin ((n + 1) ^ m)) σ (QROMEvent c) (QROMOut a) (m * n * w) where
  init := s₀
  initReg := dbEmptyIdx m n
  step := signerStep (progAtt (m * n * w)) sig

/-- The bound on the number of non-`⊥` entries after an event: a query adds one, a round adds
the number of operations of its signer program. -/
def stepLevel (sig : σ → Fin c → SignProg m n Ω (σ × Fin a)) : ℕ → σ → QROMEvent c → ℕ
  | N, _, .query => N + 1
  | N, s, .round y => N + (sig s y).ops

/-- The programming challenger raises the weight of the database to `stepLevel`. -/
theorem progSys_mapsSupp (s₀ : σ) (sig : σ → Fin c → SignProg m n Ω (σ × Fin a)) (N : ℕ)
    (s : σ) (e : QROMEvent c) :
    MapsSupp ((progSys (w := w) s₀ sig).step s e) (Prod.snd ⁻¹' dbLe m n N)
      (fun _ => Prod.snd ⁻¹' dbLe m n (stepLevel sig N s e)) := by
  cases e with
  | query => exact MapsSupp.bind' (cmpQuery_mapsSupp N) fun _ => mapsSupp_pure _ _
  | round y =>
    exact MapsSupp.bind' ((sig s y).exec_mapsSupp _ (progAtt_mapsSupp _) N) fun _ =>
      mapsSupp_pure _ _

/-- **Reading versus programming, summed over the attempts** (BBD+23, the hop from Sign to
Prog, charging every attempt of the signer and not the expected number of attempts).
Let every attempt of the signer draw its point so that each point has probability
at most `ε`, and let the potential `Φ` of the signer state bound the operations of the remaining
rounds: a round from `s` with `o` operations reaches only states `s'` with `o + Φ s' ≤ Φ s`.
Then the acceptance probabilities of an environment against the reading and the programming
challengers differ by at most `Φ s₀ · 2 √((T + Φ s₀) ε)`, for `T` the number of activations of
the environment. -/
theorem signToProg_le (s₀ : σ) (sig : σ → Fin c → SignProg m n Ω (σ × Fin a)) (ε : ℝ≥0)
    (hsp : ∀ s y, (sig s y).Sparse ε) (Φ : σ → ℕ)
    (hΦ : ∀ s y r, (sig s y).Yields r → (sig s y).ops + Φ r.1 ≤ Φ s)
    (G : QStratAcc ζ (QROMEvent c) (QROMOut a) (m * n * w)) :
    absDiff (viewAcc (signSys (w := w) s₀ sig) G) (viewAcc (progSys (w := w) s₀ sig) G) ≤
      Φ s₀ * reprogCost ε (G.strat.rounds + Φ s₀) := by
  refine (absDiff_viewAcc_le_sidist _ _ G).trans ?_
  have h := sidist_qview_le_graded (signSys (w := w) s₀ sig) (progSys s₀ sig) G.strat
    (dbLe m n) (stepLevel sig) (progSys_mapsSupp s₀ sig)
    (fun k N s => (Φ s : ℝ≥0∞) * reprogCost ε (N + k + Φ s)) ?_ rfl rfl 0
    (by change dbWeight (m := m) (n := n) (dbEmptyIdx m n) ≤ 0; rw [dbWeight_dbEmptyIdx])
  · refine h.trans (le_of_eq ?_)
    simp only [zero_add]
    rfl
  · intro k N s e
    cases e with
    | query =>
      change sidistOn _ ((cmpQuery m n w).bind _) ((cmpQuery m n w).bind _) + _ ≤ _
      rw [sidistOn_self, zero_add]
      refine iSup₂_le fun p hp => ?_
      obtain ⟨_, -, hp'⟩ := exists_of_bind_branch_ne_zero _ _ _ hp
      have hpe := eq_of_pure_branch_ne_zero hp'
      subst hpe
      exact mul_le_mul' le_rfl (reprogCost_mono ε (by simp only [stepLevel]; omega))
    | round y =>
      obtain ⟨r₀, hr₀⟩ := (sig s y).exists_yields
      have hle := hΦ s y r₀ hr₀
      change sidistOn _ (((sig s y).exec (signAtt _)).bind _)
        (((sig s y).exec (progAtt _)).bind _) + _ ≤ _
      have h1 : sidistOn (Prod.snd ⁻¹' dbLe m n N)
          (((sig s y).exec (signAtt (m * n * w))).bind
            fun r => SubInstrument.pure (r.1, QROMOut.answer r.2))
          (((sig s y).exec (progAtt (m * n * w))).bind
            fun r => SubInstrument.pure (r.1, QROMOut.answer r.2)) ≤
          (sig s y).ops * reprogCost ε (N + (k + 1) + Φ s) :=
        (sidistOn_bind_right _ _ _ _).trans ((SignProg.exec_sidistOn_le _ ε _ (hsp s y) N).trans
          (mul_le_mul' le_rfl (reprogCost_mono ε (by omega))))
      have h2 : ⨆ (p : σ × QROMOut a) (_ : ((progSys (w := w) s₀ sig).step s
            (.round y)).branch p ≠ 0),
            (Φ p.1 : ℝ≥0∞) * reprogCost ε (stepLevel sig N s (.round y) + k + Φ p.1) ≤
          ((Φ s - (sig s y).ops : ℕ) : ℝ≥0∞) * reprogCost ε (N + (k + 1) + Φ s) := by
        refine iSup₂_le fun p hp => ?_
        obtain ⟨r, hr, hp'⟩ := exists_of_bind_branch_ne_zero _ _ _ hp
        have hpe := eq_of_pure_branch_ne_zero hp'
        subst hpe
        have hy := hΦ s y r (SignProg.yields_of_branch_ne_zero _ _ _ hr)
        exact mul_le_mul' (by exact_mod_cast (by grind))
          (reprogCost_mono ε (by simp only [stepLevel]; omega))
      refine (add_le_add h1 h2).trans (le_of_eq ?_)
      rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' (by omega)]

end Systems

end CatCrypt.Quantum.QROM
