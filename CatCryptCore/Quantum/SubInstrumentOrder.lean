/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import QuantumFoundations.SubInstrument
public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Analysis.Matrix.Order
public import CatCryptCore.Quantum.CPInstrument

/-!
# Selinger's order on subinstruments

Subinstruments `Quantum.SubInstrument A B α` are ordered branchwise by complete positivity of the
difference: `I ≤ J` iff `J.branch a - I.branch a` is completely positive for every outcome `a`
(Selinger, *Towards a quantum programming language*, MSCS 2004, §3.3). This is a partial order,
and every increasing sequence has a least upper bound, the pointwise limit of its branches: the
subinstruments form an ω-complete partial order. Sequencing (`Quantum.SubInstrument.bind`) is
monotone and ω-continuous in each argument.

The supremum of a chain `c` is built from its increments: the first term, then the differences of
consecutive terms. The increments at all outcomes form one subinstrument with outcomes `α × ℕ`
(`Quantum.SubInstrument.chainIncrInstr`), and the supremum is its relabelling along `Prod.fst`.

## Main definitions

* `Quantum.SubInstrument.instPartialOrder`: Selinger's order
* `Quantum.SubInstrument.instOmegaCompletePartialOrder`: suprema of chains

## Main results

* `Quantum.MatrixMap.isCP_of_tendsto`: complete positivity is closed under pointwise limits
* `Quantum.SubInstrument.tendsto_branch_ωSup`: the branches of a chain converge to those of its
  supremum
* `Quantum.SubInstrument.bind_mono_left`, `Quantum.SubInstrument.bind_mono_right`: sequencing is
  monotone in each argument
* `Quantum.SubInstrument.ωSup_bind`, `Quantum.SubInstrument.bind_ωSup`: sequencing commutes with
  suprema of chains in each argument
* `Quantum.SubInstrument.posSemidef_sub_branch_of_le`: the order implies the Löwner order of the
  branches on positive semidefinite inputs
* `CatCrypt.Quantum.CPComp.qbind_mono_left`, `CatCrypt.Quantum.CPComp.ωSup_qbind` and their
  right-hand counterparts: the same statements for `CPComp.qbind`
* `CatCrypt.Quantum.CPComp.posSemidef_sub_toQComp_branch_of_le`: on `Unit`-valued instruments,
  Selinger's order implies the Löwner order of programs. The converse fails in general: a
  difference of completely positive maps can be positive without being completely positive.

The final section is the only part that uses `CatCryptCore.Quantum.CPInstrument`; the rest
depends on QuantumFoundations and Mathlib alone.
-/

@[expose] public section

set_option autoImplicit false

open scoped ComplexOrder Topology
open Filter OmegaCompletePartialOrder

noncomputable section

namespace Quantum

namespace MatrixMap

variable {A B : Type*}

/-- A pointwise limit of maps that are eventually completely positive is completely positive. -/
theorem isCP_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {Φ : ι → MatrixMap A B}
    {Ψ : MatrixMap A B} (hlim : ∀ ρ, Tendsto (fun i ↦ Φ i ρ) l (𝓝 (Ψ ρ)))
    (hΦ : ∀ᶠ i in l, (Φ i).IsCP) : Ψ.IsCP := by
  intro k ρ hρ
  have h : Tendsto (fun i ↦ (Φ i).amplify (Fin k) ρ) l (𝓝 (Ψ.amplify (Fin k) ρ)) :=
    tendsto_pi_nhds.mpr fun x ↦ tendsto_pi_nhds.mpr fun y ↦
      ((hlim _).apply_nhds x.1).apply_nhds y.1
  exact Matrix.posSemidef_is_closed.mem_of_tendsto h (hΦ.mono fun i hi ↦ hi k ρ hρ)

/-- A pointwise sum of completely positive maps is completely positive. -/
theorem isCP_of_hasSum {ι : Type*} {Φ : ι → MatrixMap A B} {Ψ : MatrixMap A B}
    (hΦ : ∀ i, (Φ i).IsCP) (h : ∀ ρ, HasSum (fun i ↦ Φ i ρ) (Ψ ρ)) : Ψ.IsCP :=
  isCP_of_tendsto (l := (SummationFilter.unconditional ι).filter)
    (Φ := fun s : Finset ι ↦ ∑ i ∈ s, Φ i)
    (fun ρ ↦ by
      have hρ := h ρ
      unfold HasSum at hρ
      simpa only [LinearMap.sum_apply] using hρ)
    (Eventually.of_forall fun s ↦ IsCP.sum s fun i _ ↦ hΦ i)

/-- Two maps whose differences in both directions are completely positive are equal. -/
theorem eq_of_isCP_sub [Finite A] {Φ Ψ : MatrixMap A B} (h₁ : (Ψ - Φ).IsCP) (h₂ : (Φ - Ψ).IsCP) :
    Φ = Ψ := by
  classical
  refine LinearMap.ext fun ρ ↦ ?_
  induction ρ using Matrix.induction_on_posSemidef with
  | posSemidef ρ hρ =>
    have e₁ := h₁.posSemidef hρ
    have e₂ := h₂.posSemidef hρ
    rw [LinearMap.sub_apply] at e₁ e₂
    open scoped MatrixOrder in
    exact le_antisymm (sub_nonneg.mp e₁.nonneg) (sub_nonneg.mp e₂.nonneg)
  | add M N hM hN => rw [map_add, map_add, hM, hN]
  | smul c M hM => rw [map_smul, map_smul, hM]

end MatrixMap

namespace SubInstrument

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] {α β : Type*}

/-! ## The order -/

/-- Selinger's order: `I ≤ J` iff `J.branch a - I.branch a` is completely positive for every
outcome `a`. -/
instance instPartialOrder : PartialOrder (SubInstrument A B α) where
  le I J := ∀ a, (J.branch a - I.branch a).IsCP
  le_refl I a := by
    rw [sub_self]
    exact MatrixMap.IsCP.zero
  le_trans I J K h₁ h₂ a := by
    have h := (h₂ a).add (h₁ a)
    rwa [sub_add_sub_cancel] at h
  le_antisymm I J h₁ h₂ :=
    DSubInstrument.ext (funext fun a ↦ MatrixMap.eq_of_isCP_sub (h₁ a) (h₂ a))

/-- Unfolding of Selinger's order. -/
theorem le_def {I J : SubInstrument A B α} : I ≤ J ↔ ∀ a, (J.branch a - I.branch a).IsCP :=
  Iff.rfl

/-- Selinger's order implies the Löwner order of the branches on positive semidefinite inputs. -/
theorem posSemidef_sub_branch_of_le {I J : SubInstrument A B α} (h : I ≤ J) (a : α)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) : (J.branch a ρ - I.branch a ρ).PosSemidef :=
  (h a).posSemidef hρ

/-! ## Increments of a sequence -/

/-- The increments of a sequence of subinstruments at outcome `a`: the branch of the first term,
then the differences of the branches of consecutive terms. -/
def chainIncr (c : ℕ → SubInstrument A B α) (a : α) : ℕ → MatrixMap A B
  | 0 => (c 0).branch a
  | n + 1 => (c (n + 1)).branch a - (c n).branch a

/-- The first `n + 1` increments sum to the branch of the `n`-th term. -/
theorem sum_range_chainIncr (c : ℕ → SubInstrument A B α) (a : α) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), chainIncr c a k = (c n).branch a := by
  induction n with
  | zero => simp [chainIncr]
  | succ n ih => rw [Finset.sum_range_succ, ih, chainIncr, add_sub_cancel]

/-- The increments of an increasing sequence are completely positive. -/
theorem isCP_chainIncr {c : ℕ → SubInstrument A B α} (hc : Monotone c) (a : α) (n : ℕ) :
    (chainIncr c a n).IsCP := by
  cases n with
  | zero => exact (c 0).isCP_branch a
  | succ n => exact hc n.le_succ a

/-- The increments of an increasing sequence at all outcomes form a completely positive family
with trace-nonincreasing partial sums. -/
theorem isCPTNIFamily_chainIncr {c : ℕ → SubInstrument A B α} (hc : Monotone c) :
    MatrixMap.IsCPTNIFamily fun x : α × ℕ ↦ chainIncr c x.1 x.2 where
  isCP x := isCP_chainIncr hc x.1 x.2
  sum_trace_re_le s ρ hρ := by
    classical
    obtain ⟨N, hN⟩ : ∃ N, ∀ x ∈ s, x.2 < N + 1 :=
      ⟨s.sup Prod.snd, fun x hx ↦ Nat.lt_succ_of_le (Finset.le_sup (f := Prod.snd) hx)⟩
    calc ∑ x ∈ s, (chainIncr c x.1 x.2 ρ).trace.re
        ≤ ∑ x ∈ s.image Prod.fst ×ˢ Finset.range (N + 1), (chainIncr c x.1 x.2 ρ).trace.re :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx ↦ Finset.mem_product.mpr
              ⟨Finset.mem_image_of_mem _ hx, Finset.mem_range.mpr (hN x hx)⟩)
            fun x _ _ ↦ ((isCP_chainIncr hc x.1 x.2).posSemidef hρ).trace_re_nonneg
      _ = ∑ a ∈ s.image Prod.fst, ∑ k ∈ Finset.range (N + 1), (chainIncr c a k ρ).trace.re :=
          Finset.sum_product _ _ _
      _ = ∑ a ∈ s.image Prod.fst, ((c N).branch a ρ).trace.re := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [← MatrixMap.trace_re_sum_apply, sum_range_chainIncr]
      _ ≤ ρ.trace.re := (c N).trace_le _ ρ hρ

/-- The increments of an increasing sequence at one outcome form a completely positive family
with trace-nonincreasing partial sums. -/
theorem isCPTNIFamily_chainIncr_apply {c : ℕ → SubInstrument A B α} (hc : Monotone c) (a : α) :
    MatrixMap.IsCPTNIFamily fun n : ℕ ↦ chainIncr c a n where
  isCP n := isCP_chainIncr hc a n
  sum_trace_re_le s ρ hρ := by
    classical
    simpa only [Finset.sum_map, Function.Embedding.coeFn_mk] using
      (isCPTNIFamily_chainIncr hc).sum_trace_re_le
        (s.map ⟨Prod.mk a, Prod.mk_right_injective a⟩) ρ hρ

/-- The increments of an increasing sequence are summable at every input. -/
theorem summable_chainIncr {c : ℕ → SubInstrument A B α} (hc : Monotone c) (a : α)
    (ρ : Matrix A A ℂ) : Summable fun n ↦ chainIncr c a n ρ :=
  (isCPTNIFamily_chainIncr_apply hc a).summable_apply ρ

/-- The increments of a chain, as one subinstrument with outcomes `α × ℕ`. -/
def chainIncrInstr (c : Chain (SubInstrument A B α)) : SubInstrument A B (α × ℕ) where
  branch x := chainIncr c x.1 x.2
  isCP_branch := (isCPTNIFamily_chainIncr (OrderHomClass.mono c)).isCP
  trace_le := (isCPTNIFamily_chainIncr (OrderHomClass.mono c)).sum_trace_re_le

/-! ## Suprema of chains -/

/-- The fibre of `Prod.fst` over `a` is a copy of `ℕ`. -/
def fstFiberEquiv (a : α) : ℕ ≃ (Prod.fst ⁻¹' {a} : Set (α × ℕ)) where
  toFun n := ⟨(a, n), rfl⟩
  invFun x := x.1.2
  left_inv _ := rfl
  right_inv := fun ⟨⟨b, n⟩, h⟩ ↦ by
    obtain rfl : b = a := h
    rfl

/-- The supremum of a chain: the relabelling of its increments along `Prod.fst`. -/
def chainSup (c : Chain (SubInstrument A B α)) : SubInstrument A B α :=
  (chainIncrInstr c).map Prod.fst

/-- The branch of the supremum of a chain is the sum of its increments. -/
theorem chainSup_branch_apply (c : Chain (SubInstrument A B α)) (a : α) (ρ : Matrix A A ℂ) :
    (chainSup c).branch a ρ = ∑' n, chainIncr c a n ρ := by
  rw [chainSup, branch_map_apply]
  exact ((fstFiberEquiv a).tsum_eq fun x ↦ (chainIncrInstr c).branch x ρ).symm

/-- The branches of a chain converge to those of its supremum. -/
theorem tendsto_branch_chainSup (c : Chain (SubInstrument A B α)) (a : α) (ρ : Matrix A A ℂ) :
    Tendsto (fun n ↦ (c n).branch a ρ) atTop (𝓝 ((chainSup c).branch a ρ)) := by
  rw [chainSup_branch_apply]
  have h := (summable_chainIncr (OrderHomClass.mono c) a ρ).hasSum.tendsto_sum_nat
  rw [← tendsto_add_atTop_iff_nat 1] at h
  exact Tendsto.congr (fun n ↦ by rw [← LinearMap.sum_apply, sum_range_chainIncr]) h

/-- Subinstruments form an ω-complete partial order under Selinger's order; the supremum of a
chain is the pointwise limit of its branches. -/
instance instOmegaCompletePartialOrder : OmegaCompletePartialOrder (SubInstrument A B α) where
  ωSup := chainSup
  le_ωSup c n a := MatrixMap.isCP_of_tendsto (l := atTop)
    (Φ := fun N ↦ (c N).branch a - (c n).branch a)
    (fun ρ ↦ by
      simpa only [LinearMap.sub_apply] using
        (tendsto_branch_chainSup c a ρ).sub_const ((c n).branch a ρ))
    ((eventually_ge_atTop n).mono fun _ hN ↦ c.monotone hN a)
  ωSup_le c J h a := MatrixMap.isCP_of_tendsto (l := atTop)
    (Φ := fun N ↦ J.branch a - (c N).branch a)
    (fun ρ ↦ by
      simpa only [LinearMap.sub_apply] using
        (tendsto_branch_chainSup c a ρ).const_sub (J.branch a ρ))
    (Eventually.of_forall fun N ↦ h N a)

/-- The branch of the supremum of a chain is the sum of its increments. -/
theorem ωSup_branch_apply (c : Chain (SubInstrument A B α)) (a : α) (ρ : Matrix A A ℂ) :
    (ωSup c).branch a ρ = ∑' n, chainIncr c a n ρ :=
  chainSup_branch_apply c a ρ

/-- The branches of a chain converge to those of its supremum. -/
theorem tendsto_branch_ωSup (c : Chain (SubInstrument A B α)) (a : α) (ρ : Matrix A A ℂ) :
    Tendsto (fun n ↦ (c n).branch a ρ) atTop (𝓝 ((ωSup c).branch a ρ)) :=
  tendsto_branch_chainSup c a ρ

/-! ## Sequencing -/

/-- The terms of the sum defining a branch of a composite are summable. -/
theorem summable_bind_apply (p : SubInstrument A B α) (k : α → SubInstrument B C β) (b : β)
    (ρ : Matrix A A ℂ) : Summable fun a ↦ (k a).branch b (p.branch a ρ) :=
  (p.isCPTNIFamily.comp_eval (fun a ↦ (k a).isCPTNIFamily) b).summable_apply ρ

/-- Sequencing is monotone in the first subinstrument. -/
theorem bind_mono_left {p p' : SubInstrument A B α} (h : p ≤ p') (k : α → SubInstrument B C β) :
    p.bind k ≤ p'.bind k := fun b ↦
  MatrixMap.isCP_of_hasSum (Φ := fun a ↦ (k a).branch b ∘ₗ (p'.branch a - p.branch a))
    (fun a ↦ ((k a).isCP_branch b).comp (h a)) fun ρ ↦ by
      rw [LinearMap.sub_apply, DSubInstrument.branch_bind_apply,
        DSubInstrument.branch_bind_apply]
      simpa only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub] using
        (summable_bind_apply p' k b ρ).hasSum.sub (summable_bind_apply p k b ρ).hasSum

/-- Sequencing is monotone in the continuation. -/
theorem bind_mono_right (p : SubInstrument A B α) {k k' : α → SubInstrument B C β}
    (h : k ≤ k') : p.bind k ≤ p.bind k' := fun b ↦
  MatrixMap.isCP_of_hasSum (Φ := fun a ↦ ((k' a).branch b - (k a).branch b) ∘ₗ p.branch a)
    (fun a ↦ (h a b).comp (p.isCP_branch a)) fun ρ ↦ by
      rw [LinearMap.sub_apply, DSubInstrument.branch_bind_apply,
        DSubInstrument.branch_bind_apply]
      simpa only [LinearMap.comp_apply, LinearMap.sub_apply] using
        (summable_bind_apply p k' b ρ).hasSum.sub (summable_bind_apply p k b ρ).hasSum

/-- The increments of a sequence followed by a fixed continuation. -/
theorem chainIncr_bind_left_apply (c : ℕ → SubInstrument A B α) (k : α → SubInstrument B C β)
    (b : β) (n : ℕ) (ρ : Matrix A A ℂ) :
    chainIncr (fun m ↦ (c m).bind k) b n ρ = ∑' a, (k a).branch b (chainIncr c a n ρ) := by
  cases n with
  | zero => exact DSubInstrument.branch_bind_apply _ _ b ρ
  | succ n =>
    simp only [chainIncr, LinearMap.sub_apply, DSubInstrument.branch_bind_apply, map_sub]
    exact ((summable_bind_apply _ k b ρ).tsum_sub (summable_bind_apply _ k b ρ)).symm

/-- The increments of a sequence of continuations after a fixed subinstrument. -/
theorem chainIncr_bind_right_apply (p : SubInstrument A B α)
    (c : ℕ → α → SubInstrument B C β) (b : β) (n : ℕ) (ρ : Matrix A A ℂ) :
    chainIncr (fun m ↦ p.bind (c m)) b n ρ =
      ∑' a, chainIncr (fun m ↦ c m a) b n (p.branch a ρ) := by
  cases n with
  | zero => exact DSubInstrument.branch_bind_apply _ _ b ρ
  | succ n =>
    simp only [chainIncr, LinearMap.sub_apply, DSubInstrument.branch_bind_apply]
    exact ((summable_bind_apply p _ b ρ).tsum_sub (summable_bind_apply p _ b ρ)).symm

/-- Sequencing after the supremum of a chain is the supremum of the sequenced chain. -/
theorem ωSup_bind (c : Chain (SubInstrument A B α)) (k : α → SubInstrument B C β) :
    (ωSup c).bind k = ωSup (c.map ⟨fun p ↦ p.bind k, fun _ _ h ↦ bind_mono_left h k⟩) := by
  refine DSubInstrument.ext (funext fun b ↦ LinearMap.ext fun ρ ↦ ?_)
  have hF : Summable (Function.uncurry fun a n ↦ (k a).branch b (chainIncr c a n ρ)) :=
    ((isCPTNIFamily_chainIncr (OrderHomClass.mono c)).comp (D := fun _ ↦ C)
      (Ψ := fun x ↦ (k x.1).branch b) (fun x ↦ (k x.1).isCP_branch b)
      fun x ↦ (k x.1).isCPTNIFamily.isTNI b).summable_apply ρ
  calc ((ωSup c).bind k).branch b ρ
      = ∑' a, (k a).branch b ((ωSup c).branch a ρ) := DSubInstrument.branch_bind_apply _ _ b ρ
    _ = ∑' a, ∑' n, (k a).branch b (chainIncr c a n ρ) := tsum_congr fun a ↦ by
        rw [ωSup_branch_apply, MatrixMap.map_tsum _ (summable_chainIncr (OrderHomClass.mono c) a ρ)]
    _ = ∑' n, ∑' a, (k a).branch b (chainIncr c a n ρ) := hF.tsum_comm.symm
    _ = ∑' n, chainIncr (fun m ↦ (c m).bind k) b n ρ :=
        tsum_congr fun n ↦ (chainIncr_bind_left_apply c k b n ρ).symm
    _ = _ := by rw [ωSup_branch_apply]; rfl

/-- Sequencing with the supremum of a chain of continuations is the supremum of the sequenced
chain. The order on continuations is the pointwise order. -/
theorem bind_ωSup (p : SubInstrument A B α) (c : Chain (α → SubInstrument B C β)) :
    p.bind (ωSup c) = ωSup (c.map ⟨fun k ↦ p.bind k, fun _ _ h ↦ bind_mono_right p h⟩) := by
  refine DSubInstrument.ext (funext fun b ↦ LinearMap.ext fun ρ ↦ ?_)
  have hc (a : α) : Monotone fun m ↦ c m a := fun _ _ h ↦ c.monotone h a
  have hF : Summable (Function.uncurry fun a n ↦
      chainIncr (fun m ↦ c m a) b n (p.branch a ρ)) :=
    (p.isCPTNIFamily.prod (Ψ := fun a n ↦ chainIncr (fun m ↦ c m a) b n)
      fun a ↦ isCPTNIFamily_chainIncr_apply (hc a) b).summable_apply ρ
  calc (p.bind (ωSup c)).branch b ρ
      = ∑' a, (ωSup c a).branch b (p.branch a ρ) := DSubInstrument.branch_bind_apply _ _ b ρ
    _ = ∑' a, ∑' n, chainIncr (fun m ↦ c m a) b n (p.branch a ρ) :=
        tsum_congr fun a ↦ ωSup_branch_apply (c.map (Pi.evalOrderHom a)) b _
    _ = ∑' n, ∑' a, chainIncr (fun m ↦ c m a) b n (p.branch a ρ) := hF.tsum_comm.symm
    _ = ∑' n, chainIncr (fun m ↦ p.bind (c m)) b n ρ :=
        tsum_congr fun n ↦ (chainIncr_bind_right_apply p c b n ρ).symm
    _ = _ := by rw [ωSup_branch_apply]; rfl

/-- Sequencing is ω-continuous in the first subinstrument. -/
theorem ωScottContinuous_bind_left (k : α → SubInstrument B C β) :
    ωScottContinuous fun p : SubInstrument A B α ↦ p.bind k :=
  ωScottContinuous.of_monotone_map_ωSup ⟨fun _ _ h ↦ bind_mono_left h k, fun c ↦ ωSup_bind c k⟩

/-- Sequencing is ω-continuous in the continuation. -/
theorem ωScottContinuous_bind_right (p : SubInstrument A B α) :
    ωScottContinuous fun k : α → SubInstrument B C β ↦ p.bind k :=
  ωScottContinuous.of_monotone_map_ωSup ⟨fun _ _ h ↦ bind_mono_right p h, fun c ↦ bind_ωSup p c⟩

end SubInstrument

end Quantum

/-! ## Completely positive instruments -/

namespace CatCrypt.Quantum.CPComp

variable {d : ℕ} {α β : Type}

/-- `qbind` is monotone in the first instrument. -/
theorem qbind_mono_left {C C' : CPComp d α} (h : C ≤ C') (f : α → CPComp d β) :
    C.qbind f ≤ C'.qbind f :=
  _root_.Quantum.SubInstrument.bind_mono_left h f

/-- `qbind` is monotone in the continuation. -/
theorem qbind_mono_right (C : CPComp d α) {f f' : α → CPComp d β} (h : f ≤ f') :
    C.qbind f ≤ C.qbind f' :=
  _root_.Quantum.SubInstrument.bind_mono_right C h

/-- `qbind` after the supremum of a chain is the supremum of the sequenced chain. -/
theorem ωSup_qbind (c : Chain (CPComp d α)) (f : α → CPComp d β) :
    (ωSup c).qbind f = ωSup (c.map ⟨fun C ↦ C.qbind f, fun _ _ h ↦ qbind_mono_left h f⟩) :=
  _root_.Quantum.SubInstrument.ωSup_bind c f

/-- `qbind` with the supremum of a chain of continuations is the supremum of the sequenced
chain. -/
theorem qbind_ωSup (C : CPComp d α) (c : Chain (α → CPComp d β)) :
    C.qbind (ωSup c) = ωSup (c.map ⟨fun f ↦ C.qbind f, fun _ _ h ↦ qbind_mono_right C h⟩) :=
  _root_.Quantum.SubInstrument.bind_ωSup C c

/-- `qbind` is ω-continuous in the first instrument. -/
theorem ωScottContinuous_qbind_left (f : α → CPComp d β) :
    ωScottContinuous fun C : CPComp d α ↦ C.qbind f :=
  _root_.Quantum.SubInstrument.ωScottContinuous_bind_left f

/-- `qbind` is ω-continuous in the continuation. -/
theorem ωScottContinuous_qbind_right (C : CPComp d α) :
    ωScottContinuous fun f : α → CPComp d β ↦ C.qbind f :=
  _root_.Quantum.SubInstrument.ωScottContinuous_bind_right C

/-- On `Unit`-valued instruments, Selinger's order implies the Löwner order of programs
(`LoewnerLE` of `CatCrypt.Quantum.Loop.While`, stated here by its definition): the difference of
the branches is positive semidefinite on positive semidefinite inputs. -/
theorem posSemidef_sub_toQComp_branch_of_le {C D : CPComp d Unit} (h : C ≤ D)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) :
    (D.toQComp.branch () ρ - C.toQComp.branch () ρ).PosSemidef :=
  _root_.Quantum.SubInstrument.posSemidef_sub_branch_of_le h () hρ

end CatCrypt.Quantum.CPComp
