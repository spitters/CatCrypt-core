/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRealizesStep
public import QuantumFoundations.GentleMeasurement

/-!
# The distance of two subinstruments relative to an invariant

The diamond distance `sidist p q` maximises the gap of two subinstruments over all inputs.
`sidistOn S p q` maximises it over the inputs supported on a set `S` of basis states of the
input register (with an arbitrary reference register): a matrix is supported on `S` when each of
its nonzero entries has both indices in `S` (`SuppOn`). For a diagonal projector, such as the
projector onto the databases of weight at most `q` of the compressed oracle, the states fixed by
the projector are the states supported on a set.

A subinstrument maps the support `S` to `S' b` at the outcome `b` when each branch sends the
matrices supported on `S` to matrices supported on `S' b` (`MapsSupp`). Framing, relabelling,
appending a basis state and the placement of an environment operation keep this property. The
relative distance satisfies the rules of `sidist` for sequencing on the right, sequencing on the
left after a subinstrument that maps the support (`sidistOn_bind_left_of_support`) and framing.

A system preserves an invariant `Inv : τ → Set H` on its private register when each step at the
state `t` maps the support `Inv t` to `Inv t'` at the outcome with new state `t'`. The hybrid
over activations relative to the invariant (`sidistOn_qloopQ_le`) bounds the distance of the
joint runs from states supported on `Inv t` by a potential `V t` that bounds the relative distance
of the steps plus `V` at the states the ideal step reaches. The views are then within
`V R.init` when the initial basis state of the private register lies in `Inv R.init`
(`sidist_qviewQ_le_of_inv`).

**Gentle substitution.** If two subinstruments agree on the inputs compressed by a projector
`P`, they distinguish a state `ρ` of trace at most `1` with gap at most `2 √(tr((1 − P) ρ))`
(`gentle_subst_le`). The proof splits `ρ − PρP` into positive semidefinite parts whose traces
sum to its trace norm, and bounds the trace norm by the gentle measurement lemma
(`Quantum.GentleMeasurement.gentle_measurement`). A uniform bound `δ` on `tr((1 − P) ρ)` over
the states supported on `S` gives `sidistOn S p q ≤ 2 √δ` (`sidistOn_le_gentle`).

## Main definitions

* `ReactiveUC.SuppOn` — a matrix supported on a set of basis states
* `ReactiveUC.MapsSupp` — a subinstrument mapping one support to another
* `ReactiveUC.sidistOn` — the diamond distance over inputs supported on a set
* `ReactiveUC.QSys.Preserves` — a system preserving an invariant of its private register

## Main results

* `ReactiveUC.sidistOn_bind_left_of_support`, `ReactiveUC.sidistOn_bind_right`,
  `ReactiveUC.sidistOn_frame`
* `ReactiveUC.sidistOn_qloopQ_le` — the hybrid over activations relative to an invariant
* `ReactiveUC.sidist_qviewQ_le_of_inv` — the views from an initial state in the invariant
* `ReactiveUC.gentle_subst_le` — gentle substitution at one activation
* `ReactiveUC.sidistOn_le_gentle` — the relative distance of two steps that agree on the
  compressed inputs

## References

* [Barbosa, Barthe, Doczkal, Don, Fehr, Grégoire, Huang, Hülsing, Lee, Wu — Fixing and
  Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium, CRYPTO 2023, ePrint
  2023/246], Definition 2, Theorem 1 and Strategy 2
* [Winter — Coding Theorem and Strong Converse for Quantum Channels, 1999], gentle measurement
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum
open Matrix
open CatCrypt.Crypto.UCMonad.DiamondNorm
open UCMonad.QuantumUC
open scoped ENNReal NNReal ComplexOrder Kronecker

/-! ## Supports -/

section Support

variable {A B : Type} [Fintype A] [Fintype B] {α : Type}

/-- The matrix `M` is **supported on** the set `S` of basis states: each nonzero entry of `M`
has both indices in `S`. -/
def SuppOn {X : Type} (S : Set X) (M : Matrix X X ℂ) : Prop :=
  ∀ x y, M x y ≠ 0 → x ∈ S ∧ y ∈ S

/-- A scalar multiple of a matrix supported on `S` is supported on `S`. -/
theorem SuppOn.smul {X : Type} {S : Set X} {M : Matrix X X ℂ} (h : SuppOn S M) (c : ℂ) :
    SuppOn S (c • M) := fun x y hxy => h x y fun h0 => hxy (by simp [h0])

/-- A matrix supported on `S` is supported on every superset of `S`. -/
theorem SuppOn.mono {X : Type} {S S' : Set X} (hS : S ⊆ S') {M : Matrix X X ℂ}
    (h : SuppOn S M) : SuppOn S' M :=
  fun x y hxy => ⟨hS (h x y hxy).1, hS (h x y hxy).2⟩

/-- The subinstrument `s` **maps the support** `S` to `S' b` at each outcome `b`: the branch at
`b` sends the matrices supported on `S` to matrices supported on `S' b`. -/
def MapsSupp (s : SubInstrument A B α) (S : Set A) (S' : α → Set B) : Prop :=
  ∀ b (M : Matrix A A ℂ), SuppOn S M → SuppOn (S' b) (s.branch b M)

/-- Framing keeps the map of supports on the framed register. -/
theorem MapsSupp.frame {s : SubInstrument A B α} {S : Set A} {S' : α → Set B}
    (h : MapsSupp s S S') (R : Type) [Fintype R] :
    MapsSupp (s.frame R) (Prod.fst ⁻¹' S) (fun b => Prod.fst ⁻¹' S' b) := by
  intro b M hM x y hxy
  rw [DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply] at hxy
  exact h b _ (fun u v huv => hM (u, x.2) (v, y.2) huv) x.1 y.1 hxy

/-- A framed subinstrument keeps the support of the frame register. -/
theorem mapsSupp_frame_snd (s : SubInstrument A B α) {R : Type} [Fintype R] (T : Set R) :
    MapsSupp (s.frame R) (Prod.snd ⁻¹' T) (fun _ => Prod.snd ⁻¹' T) := by
  intro b M hM x y hxy
  rw [DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply] at hxy
  by_contra hc
  apply hxy
  have h0 : M.submatrix (·, x.2) (·, y.2) = 0 := by
    ext u v
    by_contra hne
    exact hc ⟨(hM _ _ hne).1, (hM _ _ hne).2⟩
  rw [h0, map_zero]
  rfl

/-- Relabelling transports the map of supports along the relabelling. -/
theorem MapsSupp.relabel {X Y : Type} [Fintype X] [Fintype Y] (e : X ≃ Y)
    {q : SubInstrument X X α} {S : Set X} {S' : α → Set X} (h : MapsSupp q S S') :
    MapsSupp (ReactiveUC.relabel e q) (e.symm ⁻¹' S) (fun b => e.symm ⁻¹' S' b) := by
  intro b M hM x y hxy
  rw [relabel_branch, reindexMap_apply] at hxy
  exact h b _ (fun u v huv => by simpa using hM (e u) (e v) huv) _ _ hxy

/-- An environment operation placed on the joint register keeps the support of the private
register. -/
theorem mapsSupp_envPlace {K : Type} [Fintype K] {d : ℕ} (H : Type) [Fintype H] (T : Set H)
    (w : SubInstrument (Fin d × K) (Fin d × K) α) :
    MapsSupp (envPlace H w) (Prod.fst ⁻¹' (Prod.snd ⁻¹' T))
      (fun _ => Prod.fst ⁻¹' (Prod.snd ⁻¹' T)) :=
  (mapsSupp_frame_snd w T).relabel (midSwap (Fin d) K H)

/-- Appending a basis state `k₀` maps the support `S` to the states over `S` with right factor
`k₀`. -/
theorem mapsSupp_appendBasis {K : Type} [Fintype K] [DecidableEq A] [DecidableEq K] (k₀ : K)
    (S : Set A) :
    MapsSupp (appendBasis k₀ : SubInstrument A (A × K) Unit) S
      (fun _ => {x | x.1 ∈ S ∧ x.2 = k₀}) := by
  intro b M hM x y hxy
  rw [appendBasis_branch_apply] at hxy
  split_ifs at hxy with hk
  · exact ⟨⟨(hM _ _ hxy).1, hk.1⟩, ⟨(hM _ _ hxy).2, hk.2⟩⟩
  · exact absurd rfl hxy

end Support

/-! ## The relative distance -/

section DistOn

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C] {α β : Type}

/-- The **diamond distance relative to** the set `S` of basis states of the input register: the
supremum, over reference registers `Fin r`, positive semidefinite inputs `ρ` on `A × Fin r` of
trace at most `1` supported on the states over `S`, and tests `ψ` on `B × Fin r`, of the gap
between the acceptances after `p ⊗ id` and after `q ⊗ id`. -/
def sidistOn (S : Set A) (p q : SubInstrument A B α) : ℝ≥0∞ :=
  ⨆ (r : ℕ) (ρ : Matrix (A × Fin r) (A × Fin r) ℂ) (_ : ρ.PosSemidef) (_ : ρ.trace.re ≤ 1)
    (_ : SuppOn (Prod.fst ⁻¹' S) ρ) (ψ : α → QTest (B × Fin r)),
    absDiff (accept (p.frame (Fin r)) ψ ρ) (accept (q.frame (Fin r)) ψ ρ)

/-- Each gap at an input supported on the states over `S` is at most the relative distance. -/
theorem le_sidistOn (S : Set A) (p q : SubInstrument A B α) (r : ℕ)
    {ρ : Matrix (A × Fin r) (A × Fin r) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (hS : SuppOn (Prod.fst ⁻¹' S) ρ) (ψ : α → QTest (B × Fin r)) :
    absDiff (accept (p.frame (Fin r)) ψ ρ) (accept (q.frame (Fin r)) ψ ρ) ≤ sidistOn S p q :=
  le_iSup_of_le r <| le_iSup_of_le ρ <| le_iSup_of_le hρ <| le_iSup_of_le htr <|
    le_iSup_of_le hS <| le_iSup_of_le ψ le_rfl

/-- The relative distance is at most the diamond distance. -/
theorem sidistOn_le_sidist (S : Set A) (p q : SubInstrument A B α) :
    sidistOn S p q ≤ sidist p q :=
  iSup_le fun r => iSup_le fun _ => iSup_le fun hρ => iSup_le fun htr => iSup_le fun _ =>
    iSup_le fun ψ => le_sidist p q r hρ htr ψ

/-- The diamond distance is the distance relative to the set of all basis states. -/
theorem sidist_le_sidistOn_univ (p q : SubInstrument A B α) :
    sidist p q ≤ sidistOn Set.univ p q :=
  iSup_le fun r => iSup_le fun _ => iSup_le fun hρ => iSup_le fun htr => iSup_le fun ψ =>
    le_sidistOn Set.univ p q r hρ htr (fun _ _ _ => ⟨trivial, trivial⟩) ψ

/-- The relative distance grows with the set. -/
theorem sidistOn_mono {S S' : Set A} (hS : S ⊆ S') (p q : SubInstrument A B α) :
    sidistOn S p q ≤ sidistOn S' p q :=
  iSup_le fun r => iSup_le fun _ => iSup_le fun hρ => iSup_le fun htr => iSup_le fun hsupp =>
    iSup_le fun ψ => le_sidistOn S' p q r hρ htr
      (hsupp.mono (Set.preimage_mono hS)) ψ

/-- The relative distance of a subinstrument to itself is `0`. -/
theorem sidistOn_self (S : Set A) (p : SubInstrument A B α) : sidistOn S p p = 0 := by
  simp [sidistOn, absDiff_self]

/-- Triangle inequality. -/
theorem sidistOn_triangle (S : Set A) (p q s : SubInstrument A B α) :
    sidistOn S p s ≤ sidistOn S p q + sidistOn S q s := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => iSup_le fun htr =>
    iSup_le fun hsupp => iSup_le fun ψ => ?_
  exact (absDiff_triangle _ _ _).trans
    (add_le_add (le_sidistOn S p q r hρ htr hsupp ψ) (le_sidistOn S q s r hρ htr hsupp ψ))

/-- On a positive semidefinite input of any trace supported on the states over `S`, the gap is
at most the trace times the relative distance. -/
theorem absDiff_accept_le_trace_mul_sidistOn (S : Set A) (p q : SubInstrument A B α) (r : ℕ)
    {σ : Matrix (A × Fin r) (A × Fin r) ℂ} (hσ : σ.PosSemidef)
    (hsupp : SuppOn (Prod.fst ⁻¹' S) σ) (ψ : α → QTest (B × Fin r)) :
    absDiff (accept (p.frame (Fin r)) ψ σ) (accept (q.frame (Fin r)) ψ σ) ≤
      ENNReal.ofReal σ.trace.re * sidistOn S p q := by
  have ht : 0 ≤ σ.trace.re := hσ.trace_re_nonneg
  rcases ht.eq_or_lt with h0 | hpos
  · have hσ0 : σ = 0 := hσ.trace_eq_zero_iff.mp
      (Complex.ext (by simpa using h0.symm) (trace_im_zero_of_psd hσ))
    subst hσ0
    simp only [accept, map_zero, QTest.map_zero, tsum_zero, absDiff_self]
    exact bot_le
  · set t := σ.trace.re
    set σ' : Matrix (A × Fin r) (A × Fin r) ℂ := ((t⁻¹ : ℝ) : ℂ) • σ
    have hσ' : σ'.PosSemidef :=
      hσ.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr ht))
    have htr' : σ'.trace.re ≤ 1 := by
      simp only [σ', Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      rw [inv_mul_cancel₀ hpos.ne']
    have hσeq : σ = (((t.toNNReal : ℝ≥0) : ℝ) : ℂ) • σ' := by
      simp only [σ', smul_smul, Real.coe_toNNReal _ ht, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]
    have hacc : ∀ P : SubInstrument A B α, accept (P.frame (Fin r)) ψ σ =
        (t.toNNReal : ℝ≥0∞) * accept (P.frame (Fin r)) ψ σ' := fun P => by
      rw [hσeq]
      exact (QTest.comp (P.frame (Fin r)) ψ).map_smul _ _ hσ'
    rw [hacc p, hacc q]
    exact (absDiff_mul_le _ _ _ ENNReal.coe_ne_top).trans
      (by gcongr <;> first | exact le_rfl | exact le_sidistOn S p q r hσ' htr' (hsupp.smul _) ψ)

/-- **Sequencing on the right.** A common continuation does not increase the relative
distance. -/
theorem sidistOn_bind_right (S : Set A) (p q : SubInstrument A B α)
    (k : α → SubInstrument B C β) :
    sidistOn S (p.bind k) (q.bind k) ≤ sidistOn S p q := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => iSup_le fun htr =>
    iSup_le fun hsupp => iSup_le fun ψ => ?_
  rw [SubInstrument.frame_bind, SubInstrument.frame_bind, accept_bind _ _ _ hρ,
    accept_bind _ _ _ hρ]
  exact le_sidistOn S p q r hρ htr hsupp _

/-- **Sequencing on the left, relative to a support.** After a common first subinstrument that
maps the support `S` to `S' b` at the outcome `b`, the relative distance is at most the
supremum, over the outcomes with a nonzero branch, of the distances of the continuations
relative to `S' b`. -/
theorem sidistOn_bind_left_of_support {S : Set A} {S' : β → Set B} (s : SubInstrument A B β)
    (k₁ k₂ : β → SubInstrument B C α) (hs : MapsSupp s S S') :
    sidistOn S (s.bind k₁) (s.bind k₂) ≤
      ⨆ (b : β) (_ : s.branch b ≠ 0), sidistOn (S' b) (k₁ b) (k₂ b) := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => iSup_le fun htr =>
    iSup_le fun hsupp => iSup_le fun ψ => ?_
  rw [SubInstrument.frame_bind, SubInstrument.frame_bind, accept_bind _ _ _ hρ,
    accept_bind _ _ _ hρ]
  set W := ⨆ (b : β) (_ : s.branch b ≠ 0), sidistOn (S' b) (k₁ b) (k₂ b)
  have hacc0 : ∀ P : SubInstrument B C α, accept (P.frame (Fin r)) ψ 0 = 0 := fun P =>
    (QTest.comp (P.frame (Fin r)) ψ).map_zero
  refine (absDiff_tsum_le _ _).trans ?_
  calc ∑' b, absDiff (accept ((k₁ b).frame (Fin r)) ψ ((s.frame (Fin r)).branch b ρ))
          (accept ((k₂ b).frame (Fin r)) ψ ((s.frame (Fin r)).branch b ρ))
      ≤ ∑' b, ENNReal.ofReal ((s.frame (Fin r)).branch b ρ).trace.re * W :=
        tsum_le_tsum fun b => by
          by_cases hb : s.branch b = 0
          · have h0 : (s.frame (Fin r)).branch b ρ = 0 := by
              rw [DSubInstrument.branch_frame_apply, hb, MatrixMap.amplify_zero]
              rfl
            rw [h0, hacc0, hacc0, absDiff_self]
            exact bot_le
          · exact (absDiff_accept_le_trace_mul_sidistOn (S' b) (k₁ b) (k₂ b) r
              ((s.frame (Fin r)).posSemidef_branch_apply b hρ)
              (hs.frame (Fin r) b ρ hsupp) ψ).trans
              (by gcongr; exact le_iSup_of_le b (le_iSup_of_le hb le_rfl))
    _ = (∑' b, ENNReal.ofReal ((s.frame (Fin r)).branch b ρ).trace.re) * W :=
        ENNReal.tsum_mul_right
    _ ≤ 1 * W := by
        gcongr
        exact (tsum_ofReal_trace_le _ hρ).trans (ENNReal.ofReal_le_one.mpr htr)
    _ = W := one_mul _

/-- **Framing.** Framing both subinstruments by a register does not increase the distance
relative to the states over `S`. -/
theorem sidistOn_frame (S : Set A) (p q : SubInstrument A B α) (K : Type) [Fintype K] :
    sidistOn (Prod.fst ⁻¹' S) (p.frame K) (q.frame K) ≤ sidistOn S p q := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => iSup_le fun htr =>
    iSup_le fun hsupp => iSup_le fun ψ => ?_
  let e : K × Fin r ≃ Fin (Fintype.card K * r) :=
    ((Fintype.equivFin K).prodCongr (Equiv.refl _)).trans finProdFinEquiv
  have h : ∀ P : SubInstrument A B α, accept ((P.frame K).frame (Fin r)) ψ ρ =
      accept (P.frame (Fin (Fintype.card K * r))) (fun a => (ψ a).reindex (assocEquiv B e).symm)
        (ρ.submatrix (assocEquiv A e).symm (assocEquiv A e).symm) := fun P =>
    tsum_congr fun a => by rw [frame_frame_branch P e]; rfl
  rw [h p, h q]
  refine le_sidistOn S p q _ (hρ.submatrix _) ?_ ?_ _
  · rwa [trace_submatrix_equiv]
  · intro x y hxy
    exact hsupp _ _ hxy

end DistOn

/-! ## The hybrid over activations relative to an invariant -/

section Hybrid

variable {H K : Type} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {τ ζ E O : Type} {d : ℕ}

/-- The system `I` **preserves** the invariant `Inv` of its private register: the step at the
state `t` maps the support `Inv t` to `Inv t'` at each outcome with new state `t'`. -/
def QSys.Preserves (I : QSys H τ E O d) (Inv : τ → Set H) : Prop :=
  ∀ t e, MapsSupp (I.step t e) (Prod.snd ⁻¹' Inv t) (fun p => Prod.snd ⁻¹' Inv p.1)

omit [DecidableEq H] [DecidableEq K] in
/-- **Hybrid over activations relative to an invariant.** Let `I` preserve `Inv`, and let `V t`
bound the distance of the steps of `R` and `I` at `t` relative to `Inv t` plus `V` at every
state that a step of `I` at `t` reaches with a nonzero branch. Then the joint runs of an
environment with `R` and with `I` from the state `t` are within `V t` relative to `Inv t`. -/
theorem sidistOn_qloopQ_le (R I : QSys H τ E O d) (Z : QStratQ K ζ E O d) (Inv : τ → Set H)
    (hI : I.Preserves Inv) (V : τ → ℝ≥0∞)
    (hV : ∀ t e, sidistOn (Prod.snd ⁻¹' Inv t) (R.step t e) (I.step t e) +
      ⨆ (p : τ × O) (_ : (I.step t e).branch p ≠ 0), V p.1 ≤ V t) :
    ∀ (n : ℕ) (c : ζ × τ), sidistOn (Prod.fst ⁻¹' (Prod.snd ⁻¹' Inv c.2))
      (qloopQ R Z n c) (qloopQ I Z n c) ≤ V c.2 := by
  intro n
  induction n with
  | zero =>
    intro c
    simp only [qloopQ, sidistOn_self]
    exact bot_le
  | succ n ih =>
    intro c
    simp only [qloopQ]
    refine (sidistOn_bind_left_of_support _ _ _ (mapsSupp_envPlace H (Inv c.2) _)).trans
      (iSup₂_le fun a _ => ?_)
    refine (sidistOn_triangle _ _ (((I.step c.2 a.2).frame K).bind fun p =>
      (envPlace H (Z.obs a.1 p.2)).bind fun z => qloopQ R Z n (z, p.1)) _).trans ?_
    refine le_trans (add_le_add ((sidistOn_bind_right _ _ _ _).trans
      (sidistOn_frame _ _ _ K)) ?_) (hV c.2 a.2)
    refine (sidistOn_bind_left_of_support _ _ _ ((hI c.2 a.2).frame K)).trans
      (iSup₂_le fun p hp => ?_)
    have hp' : (I.step c.2 a.2).branch p ≠ 0 := fun h0 =>
      hp (by rw [DSubInstrument.branch_frame_apply, h0, MatrixMap.amplify_zero])
    refine le_iSup₂_of_le p hp' ?_
    exact (sidistOn_bind_left_of_support _ _ _ (mapsSupp_envPlace H (Inv p.1) _)).trans
      (iSup₂_le fun z _ => ih (z, p.1))

/-- The views of an environment against `R` and against `I` are within `V R.init`, under the
hypotheses of `sidistOn_qloopQ_le`, when the two systems start in the same state and the same
basis state of the private register, and that basis state lies in `Inv R.init`. -/
theorem sidist_qviewQ_le_of_inv (R I : QSys H τ E O d) (Z : QStratQ K ζ E O d)
    (Inv : τ → Set H) (hI : I.Preserves Inv) (V : τ → ℝ≥0∞)
    (hinit : R.init = I.init) (hreg : R.initReg = I.initReg) (hmem : R.initReg ∈ Inv R.init)
    (hV : ∀ t e, sidistOn (Prod.snd ⁻¹' Inv t) (R.step t e) (I.step t e) +
      ⨆ (p : τ × O) (_ : (I.step t e).branch p ≠ 0), V p.1 ≤ V t) :
    sidist (qviewQ R Z) (qviewQ I Z) ≤ V R.init := by
  simp only [qviewQ, ← hinit, ← hreg]
  refine (sidist_le_sidistOn_univ _ _).trans ?_
  refine (sidistOn_bind_left_of_support _ _ _ (mapsSupp_appendBasis R.initReg _)).trans
    (iSup₂_le fun _ _ => ?_)
  refine (sidistOn_bind_left_of_support _ _ _ (mapsSupp_appendBasis Z.initReg _)).trans
    (iSup₂_le fun _ _ => ?_)
  refine (sidistOn_bind_right _ _ _ _).trans ?_
  refine (sidistOn_mono ?_ _ _).trans (sidistOn_qloopQ_le R I Z Inv hI V hV _ _)
  rintro x ⟨⟨-, hx⟩, -⟩
  change x.1.2 ∈ Inv R.init
  rw [hx]
  exact hmem

end Hybrid

/-! ## Gentle substitution -/

section Gentle

/-- **Jordan decomposition.** A Hermitian matrix is the difference of two positive semidefinite
matrices whose traces sum to its trace norm. -/
theorem exists_posSemidef_sub_eq_traceNormH {n : Type} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    ∃ P N : Matrix n n ℂ, P.PosSemidef ∧ N.PosSemidef ∧ X = P - N ∧
      P.trace.re + N.trace.re = traceNormH X hX := by
  set U : Matrix n n ℂ := (hX.eigenvectorUnitary : Matrix n n ℂ)
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hX.eigenvectorUnitary
  have hspec : X = U * diagonal (RCLike.ofReal ∘ hX.eigenvalues) * star U := by
    conv_lhs => rw [hX.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  have hpsd : ∀ f : n → ℝ, (∀ i, 0 ≤ f i) →
      (U * diagonal (fun i => ((f i : ℝ) : ℂ)) * star U).PosSemidef := fun f hf => by
    rw [star_eq_conjTranspose]
    exact (posSemidef_diagonal_iff.mpr fun i =>
      Complex.zero_le_real.mpr (hf i)).mul_mul_conjTranspose_same U
  have htr : ∀ f : n → ℂ, (U * diagonal f * star U).trace = ∑ i, f i := fun f => by
    rw [trace_mul_cycle, hUU, one_mul, trace_diagonal]
  refine ⟨U * diagonal (fun i => ((max (hX.eigenvalues i) 0 : ℝ) : ℂ)) * star U,
    U * diagonal (fun i => ((max (-hX.eigenvalues i) 0 : ℝ) : ℂ)) * star U,
    hpsd _ fun i => le_max_right _ _, hpsd _ fun i => le_max_right _ _, ?_, ?_⟩
  · rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    conv_lhs => rw [hspec]
    congr 2
    funext i
    simp only [← Complex.ofReal_sub, max_zero_sub_max_neg_zero_eq_self]
    rfl
  · rw [htr, htr, traceNormH, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Complex.ofReal_re]
    exact max_zero_add_max_neg_zero_eq_abs_self _

/-- A test is additive on positive semidefinite matrices. -/
theorem QTest.map_add {X : Type} [Fintype X] (φ : QTest X) {M N : Matrix X X ℂ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) : φ.toFun (M + N) = φ.toFun M + φ.toFun N := by
  have h := φ.map_tsum (fun b : Bool => if b then M else N)
    (fun b => by cases b <;> simpa) (hasSum_fintype _).summable
  simpa [tsum_bool, add_comm] using h

/-- Two tests that agree at `σ` differ at `ρ` by at most `tr P + tr N` when `ρ + N = σ + P`
with `P` and `N` positive semidefinite. -/
theorem absDiff_test_le_of_add_eq {X : Type} [Fintype X] (φ₁ φ₂ : QTest X)
    {ρ σ P N : Matrix X X ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hP : P.PosSemidef)
    (hN : N.PosSemidef) (h : ρ + N = σ + P) (heq : φ₁.toFun σ = φ₂.toFun σ) :
    absDiff (φ₁.toFun ρ) (φ₂.toFun ρ) ≤
      ENNReal.ofReal P.trace.re + ENNReal.ofReal N.trace.re := by
  have key : ∀ φ : QTest X, φ.toFun ρ + φ.toFun N = φ.toFun σ + φ.toFun P := fun φ => by
    rw [← φ.map_add hρ hN, ← φ.map_add hσ hP, h]
  have side : ∀ φ φ' : QTest X, φ.toFun σ = φ'.toFun σ →
      φ.toFun ρ ≤ φ'.toFun ρ + (ENNReal.ofReal P.trace.re + ENNReal.ofReal N.trace.re) :=
    fun φ φ' hφ => calc
      φ.toFun ρ ≤ φ.toFun ρ + φ.toFun N := le_add_right le_rfl
      _ = φ'.toFun σ + φ.toFun P := by rw [key φ, hφ]
      _ ≤ φ'.toFun σ + φ'.toFun P + ENNReal.ofReal P.trace.re := by
          rw [add_assoc]
          gcongr
          exact (φ.le_trace P hP).trans (le_add_left le_rfl)
      _ = φ'.toFun ρ + φ'.toFun N + ENNReal.ofReal P.trace.re := by rw [key φ']
      _ ≤ φ'.toFun ρ + ENNReal.ofReal N.trace.re + ENNReal.ofReal P.trace.re := by
          gcongr
          exact φ'.le_trace N hN
      _ = _ := by ring
  exact absDiff_le_iff.mpr ⟨side φ₁ φ₂ heq, side φ₂ φ₁ heq.symm⟩

/-- **Gentle decomposition** on `Fin N`. For a positive semidefinite `ρ` of trace at most `1`
and a projector `P`, `ρ + N = PρP + P'` with `P'`, `N` positive semidefinite and
`tr P' + tr N ≤ 2 √(tr((1 − P) ρ))`. -/
theorem exists_compress_decomp_fin {N : ℕ} (P : _root_.Quantum.GentleMeasurement.Projector (Fin N))
    {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1) :
    ∃ Pp Nn : Matrix (Fin N) (Fin N) ℂ, Pp.PosSemidef ∧ Nn.PosSemidef ∧
      ρ + Nn = P.val * ρ * P.val + Pp ∧
      Pp.trace.re + Nn.trace.re ≤ 2 * √(((1 - P.val) * ρ).trace.re) := by
  have hε : ∀ σ : Matrix (Fin N) (Fin N) ℂ, σ.PosSemidef → 0 ≤ ((1 - P.val) * σ).trace.re :=
    fun σ hσ => by
      rw [← P.trace_QρQ_eq]
      exact (P.QρQ_psd σ hσ).trace_re_nonneg
  have ht0 : 0 ≤ ρ.trace.re := hρ.trace_re_nonneg
  rcases ht0.eq_or_lt with h0 | hpos
  · have hρ0 : ρ = 0 := hρ.trace_eq_zero_iff.mp
      (Complex.ext (by simpa using h0.symm) (trace_im_zero_of_psd hρ))
    subst hρ0
    refine ⟨0, 0, PosSemidef.zero, PosSemidef.zero, by simp, ?_⟩
    simp only [trace_zero, Complex.zero_re, add_zero]
    positivity
  · set t := ρ.trace.re
    set ρ₁ : Matrix (Fin N) (Fin N) ℂ := ((t⁻¹ : ℝ) : ℂ) • ρ
    have hρ₁ : ρ₁.PosSemidef := hρ.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr ht0))
    have htr₁ : ρ₁.trace = 1 := by
      have him := trace_im_zero_of_psd hρ
      apply Complex.ext
      · simp [ρ₁, Matrix.trace_smul, t, inv_mul_cancel₀ hpos.ne']
      · simp [ρ₁, Matrix.trace_smul, him]
    have hρeq : ρ = ((t : ℝ) : ℂ) • ρ₁ := by
      simp only [ρ₁, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne',
        Complex.ofReal_one, one_smul]
    have hherm : (ρ₁ - P.val * ρ₁ * P.val).IsHermitian :=
      hρ₁.isHermitian.sub (P.PρP_psd ρ₁ hρ₁).isHermitian
    have hmeas : (P.val * ρ₁).trace.re ≥ 1 - ((1 - P.val) * ρ₁).trace.re := by
      have h : ((1 - P.val) * ρ₁).trace = ρ₁.trace - (P.val * ρ₁).trace := by
        rw [sub_mul, one_mul, trace_sub]
      rw [h, htr₁, Complex.sub_re, Complex.one_re]
      linarith
    have hgent := _root_.Quantum.GentleMeasurement.gentle_measurement P ρ₁ hρ₁ htr₁ _
      (hε ρ₁ hρ₁) hmeas hherm
    obtain ⟨Pp, Nn, hPp, hNn, hX, hsum⟩ := exists_posSemidef_sub_eq_traceNormH _ hherm
    have hc : (0 : ℂ) ≤ ((t : ℝ) : ℂ) := Complex.zero_le_real.mpr ht0
    refine ⟨((t : ℝ) : ℂ) • Pp, ((t : ℝ) : ℂ) • Nn, hPp.smul hc, hNn.smul hc, ?_, ?_⟩
    · have h1 : ρ₁ + Nn = P.val * ρ₁ * P.val + Pp := by
        rw [sub_eq_sub_iff_add_eq_add] at hX
        rw [hX, add_comm]
      rw [hρeq, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, ← smul_add, h1]
    · have hε₁ : ((1 - P.val) * ρ₁).trace.re = t⁻¹ * ((1 - P.val) * ρ).trace.re := by
        simp only [ρ₁, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      simp only [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      rw [← mul_add, hsum]
      rw [hε₁] at hgent
      have hreal : t * (2 * √(t⁻¹ * ((1 - P.val) * ρ).trace.re)) ≤
          2 * √(((1 - P.val) * ρ).trace.re) := by
        have he := hε ρ hρ
        generalize ((1 - P.val) * ρ).trace.re = ε at he ⊢
        have h1 : t * √(t⁻¹ * ε) ≤ √ε := by
          rw [Real.le_sqrt (by positivity), mul_pow,
            Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr ht0) he),
            show t ^ 2 * (t⁻¹ * ε) = t * ε by field_simp]
          · nlinarith
          · exact he
        linarith [mul_left_comm t 2 (√(t⁻¹ * ε))]
      exact (mul_le_mul_of_nonneg_left hgent ht0).trans hreal

/-- **Gentle decomposition.** For a positive semidefinite `ρ` of trace at most `1` and a
projector `P` on a finite register, `ρ + N = PρP + P'` with `P'`, `N` positive semidefinite and
`tr P' + tr N ≤ 2 √(tr((1 − P) ρ))`. -/
theorem exists_compress_decomp {X : Type} [Fintype X] [DecidableEq X] (P : Matrix X X ℂ)
    (hPh : Pᴴ = P) (hPP : P * P = P) {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace.re ≤ 1) :
    ∃ Pp Nn : Matrix X X ℂ, Pp.PosSemidef ∧ Nn.PosSemidef ∧ ρ + Nn = P * ρ * P + Pp ∧
      Pp.trace.re + Nn.trace.re ≤ 2 * √(((1 - P) * ρ).trace.re) := by
  set e := Fintype.equivFin X
  have hP'h : (P.submatrix e.symm e.symm)ᴴ = P.submatrix e.symm e.symm := by
    rw [conjTranspose_submatrix, hPh]
  have hP'P : P.submatrix e.symm e.symm * P.submatrix e.symm e.symm =
      P.submatrix e.symm e.symm := by
    rw [submatrix_mul_equiv, hPP]
  obtain ⟨Pp, Nn, hPp, hNn, hdec, hle⟩ := exists_compress_decomp_fin
    ⟨P.submatrix e.symm e.symm, hP'h, hP'P⟩ (ρ := ρ.submatrix e.symm e.symm) (hρ.submatrix _)
    (by rwa [trace_submatrix_equiv])
  refine ⟨Pp.submatrix e e, Nn.submatrix e e, hPp.submatrix _, hNn.submatrix _, ?_, ?_⟩
  · have h := congrArg (fun M => M.submatrix e e) hdec
    simpa [submatrix_mul_equiv, submatrix_add] using h
  · have h1 := trace_submatrix_equiv e.symm Pp
    have h2 := trace_submatrix_equiv e.symm Nn
    have h3 : (1 - P.submatrix e.symm e.symm) * ρ.submatrix e.symm e.symm =
        ((1 - P) * ρ).submatrix e.symm e.symm := by
      rw [sub_mul, sub_mul, one_mul, one_mul, submatrix_mul_equiv]
      rfl
    simp only [Equiv.symm_symm] at h1 h2
    rw [h1, h2]
    simpa only [h3, trace_submatrix_equiv] using hle

/-- Two tests that agree at `PρP` differ at `ρ` by at most `2 √(tr((1 − P) ρ))`. -/
theorem absDiff_test_le_gentle {X : Type} [Fintype X] [DecidableEq X] (P : Matrix X X ℂ)
    (hPh : Pᴴ = P) (hPP : P * P = P) (φ₁ φ₂ : QTest X) {ρ : Matrix X X ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (heq : φ₁.toFun (P * ρ * P) = φ₂.toFun (P * ρ * P)) :
    absDiff (φ₁.toFun ρ) (φ₂.toFun ρ) ≤ ENNReal.ofReal (2 * √(((1 - P) * ρ).trace.re)) := by
  obtain ⟨Pp, Nn, hPp, hNn, hdec, hle⟩ := exists_compress_decomp P hPh hPP hρ htr
  have hσ : (P * ρ * P).PosSemidef := by
    have h := hρ.conjTranspose_mul_mul_same P
    rwa [hPh] at h
  refine (absDiff_test_le_of_add_eq φ₁ φ₂ hρ hσ hPp hNn hdec heq).trans ?_
  rw [← ENNReal.ofReal_add hPp.trace_re_nonneg hNn.trace_re_nonneg]
  exact ENNReal.ofReal_le_ofReal hle

/-- The block at `(k, l)` of `(P ⊗ 1) M (P ⊗ 1)` is `P M_{kl} P`. -/
theorem kronecker_one_conj_submatrix {A : Type} [Fintype A] {r : ℕ} (P : Matrix A A ℂ)
    (M : Matrix (A × Fin r) (A × Fin r) ℂ) (k l : Fin r) :
    (kroneckerMap (· * ·) P (1 : Matrix (Fin r) (Fin r) ℂ) * M *
      kroneckerMap (· * ·) P (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix (·, k) (·, l) =
      P * M.submatrix (·, k) (·, l) * P := by
  ext u v
  simp [Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
    Finset.sum_mul]

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] {α : Type}

/-- **Gentle substitution.** Let the subinstruments `p` and `q` agree on the inputs compressed
by the projector `P`. Then, on a positive semidefinite input `ρ` of trace at most `1` with a
reference register, the gap between the acceptances after `p ⊗ id` and after `q ⊗ id` is at
most `2 √(tr((1 − P ⊗ 1) ρ))`. -/
theorem gentle_subst_le (p q : SubInstrument A B α) (P : Matrix A A ℂ) (hPh : Pᴴ = P)
    (hPP : P * P = P)
    (hagree : ∀ a (M : Matrix A A ℂ), p.branch a (P * M * P) = q.branch a (P * M * P))
    (r : ℕ) {ρ : Matrix (A × Fin r) (A × Fin r) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (ψ : α → QTest (B × Fin r)) :
    absDiff (accept (p.frame (Fin r)) ψ ρ) (accept (q.frame (Fin r)) ψ ρ) ≤
      ENNReal.ofReal (2 * √(((1 - kroneckerMap (· * ·) P (1 : Matrix (Fin r) (Fin r) ℂ)) *
        ρ).trace.re)) := by
  set Q := kroneckerMap (· * ·) P (1 : Matrix (Fin r) (Fin r) ℂ)
  have hPh' : Qᴴ = Q := by
    rw [Matrix.conjTranspose_kronecker, hPh, conjTranspose_one]
  have hPP' : Q * Q = Q := by
    rw [← mul_kronecker_mul, hPP, one_mul]
  refine absDiff_test_le_gentle _ hPh' hPP' (QTest.comp (p.frame (Fin r)) ψ)
    (QTest.comp (q.frame (Fin r)) ψ) hρ htr ?_
  change accept _ ψ _ = accept _ ψ _
  refine tsum_congr fun a => congrArg (ψ a).toFun ?_
  ext x y
  rw [DSubInstrument.branch_frame_apply, DSubInstrument.branch_frame_apply,
    MatrixMap.amplify_apply, MatrixMap.amplify_apply, kronecker_one_conj_submatrix, hagree]

/-- **Gentle substitution relative to a support.** If `p` and `q` agree on the inputs compressed
by the projector `P`, and every state of trace at most `1` supported on the states over `S`
gives `1 − P ⊗ 1` a trace of at most `δ`, then the distance of `p` and `q` relative to `S` is at
most `2 √δ`. -/
theorem sidistOn_le_gentle (S : Set A) (p q : SubInstrument A B α) (P : Matrix A A ℂ)
    (hPh : Pᴴ = P) (hPP : P * P = P)
    (hagree : ∀ a (M : Matrix A A ℂ), p.branch a (P * M * P) = q.branch a (P * M * P))
    (δ : ℝ) (hδ : ∀ (r : ℕ) (ρ : Matrix (A × Fin r) (A × Fin r) ℂ), ρ.PosSemidef →
      ρ.trace.re ≤ 1 → SuppOn (Prod.fst ⁻¹' S) ρ →
      ((1 - kroneckerMap (· * ·) P (1 : Matrix (Fin r) (Fin r) ℂ)) * ρ).trace.re ≤ δ) :
    sidistOn S p q ≤ ENNReal.ofReal (2 * √δ) :=
  iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => iSup_le fun htr => iSup_le fun hsupp =>
    iSup_le fun ψ => (gentle_subst_le p q P hPh hPP hagree r hρ htr ψ).trans
      (ENNReal.ofReal_le_ofReal (by gcongr; exact hδ r ρ hρ htr hsupp))

end Gentle

end CatCrypt.Quantum.ReactiveUC
