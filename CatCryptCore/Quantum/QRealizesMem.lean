/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRealizes

/-!
# Simulators with a private quantum register

An extension of `CatCrypt.Quantum.ReactiveUC` in which environments and simulators hold
private quantum registers that persist across activations.

An environment `QStratQ K ζ E O d` acts on the interface register `Fin d` and its own memory
register `K`, prepared in a basis state and discarded at the end of the run. A simulator
`QSimQ M σ E O EG OG d` acts on `Fin d` and its own register `M`. Absorbing a simulator into
an environment (`QSimQ.absorb`) gives an environment with memory `K × M`; composing two
simulators (`QSimQ.comp`) tensors their registers. `QRealizesSimQ R I S ε` bounds the diamond
distance between the view of `R` and the view of `I` behind `S`, for environments with every
memory register.

Registers are moved between positions of a product by `relabel e q`, the subinstrument `q`
conjugated by the permutation of basis states `e`.

## Main definitions

* `ReactiveUC.relabel` — conjugation of a subinstrument by an equivalence of basis states
* `ReactiveUC.QStratQ`, `ReactiveUC.qloopQ`, `ReactiveUC.qviewQ`
* `ReactiveUC.QSimQ`, `QSimQ.absorb`, `QSimQ.id`, `QSimQ.comp`, `ReactiveUC.simViewQ`
* `ReactiveUC.QRealizesSimQ R I S ε`
* `QStrat.toQ`, `QSim.toQ` — the memoryless environments and simulators, with a trivial
  register

## Main results

* `ReactiveUC.qviewQ_iso` — the view is invariant under an equivalence of memory registers
  that intertwines the environment steps
* `ReactiveUC.QRealizesSimQ.refl` (`ε = 0`), `ReactiveUC.QRealizesSimQ.trans` (`ε₁ + ε₂`)
* `ReactiveUC.simViewQ_toQ` — the view behind `S.toQ` of `Z.toQ` is the view behind `S` of `Z`
* `ReactiveUC.QRealizesSimQ.toQSim` — realization behind `S.toQ` gives realization behind `S`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum
open Matrix
open CatCrypt.Crypto.UCMonad.DiamondNorm
open UCMonad.QuantumUC
open scoped ENNReal ComplexOrder

/-! ## Relabelling basis states -/

section Relabel

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C] {α β : Type}

/-- The map `Φ` conjugated by the relabelling `e` of basis states:
`ρ ↦ (Φ (ρ ∘ e)) ∘ e⁻¹`, entrywise. -/
def reindexMap (e : A ≃ B) (Φ : MatrixMap A A) : MatrixMap B B where
  toFun ρ := (Φ (ρ.submatrix e e)).submatrix e.symm e.symm
  map_add' ρ σ := by
    ext x y
    simp [Matrix.submatrix_add]
  map_smul' c ρ := by
    ext x y
    simp [Matrix.submatrix_smul]

omit [Fintype A] [Fintype B] in
/-- Unfolding lemma for `reindexMap`. -/
theorem reindexMap_apply (e : A ≃ B) (Φ : MatrixMap A A) (ρ : Matrix B B ℂ) :
    reindexMap e Φ ρ = (Φ (ρ.submatrix e e)).submatrix e.symm e.symm :=
  rfl

/-- Reindexing a matrix by an equivalence keeps its trace. -/
theorem trace_submatrix_equiv (e : A ≃ B) (X : Matrix A A ℂ) :
    (X.submatrix e.symm e.symm).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Fintype.sum_equiv e.symm _ _ fun _ => rfl

omit [Fintype A] [Fintype B] in
/-- A relabelled completely positive map is completely positive. -/
theorem isCP_reindexMap (e : A ≃ B) {Φ : MatrixMap A A} (hΦ : Φ.IsCP) :
    (reindexMap e Φ).IsCP := fun k ρ hρ => by
  have key : (reindexMap e Φ).amplify (Fin k) ρ =
      (Φ.amplify (Fin k) (ρ.submatrix (fun x : A × Fin k => (e x.1, x.2))
        (fun x : A × Fin k => (e x.1, x.2)))).submatrix
        (fun y : B × Fin k => (e.symm y.1, y.2)) (fun y : B × Fin k => (e.symm y.1, y.2)) :=
    rfl
  rw [key]
  exact (hΦ.amplify_posSemidef (hρ.submatrix _)).submatrix _

/-- The subinstrument `q` conjugated by the relabelling `e` of basis states. -/
def relabel (e : A ≃ B) (q : SubInstrument A A α) : SubInstrument B B α where
  branch b := reindexMap e (q.branch b)
  isCP_branch b := isCP_reindexMap e (q.isCP_branch b)
  trace_le s ρ hρ := by
    have h := q.trace_le s (ρ.submatrix e e) (hρ.submatrix _)
    calc ∑ i ∈ s, (reindexMap e (q.branch i) ρ).trace.re
        = ∑ i ∈ s, (q.branch i (ρ.submatrix e e)).trace.re :=
          Finset.sum_congr rfl fun i _ => by rw [reindexMap_apply, trace_submatrix_equiv]
      _ ≤ (ρ.submatrix e e).trace.re := h
      _ = ρ.trace.re := by
          have := trace_submatrix_equiv e.symm ρ
          rw [Equiv.symm_symm] at this
          rw [this]

/-- Unfolding lemma: the branches of `relabel e q` are the relabelled branches of `q`. -/
theorem relabel_branch (e : A ≃ B) (q : SubInstrument A A α) (b : α) :
    (relabel e q).branch b = reindexMap e (q.branch b) :=
  rfl

/-- Relabelling preserves `pure`. -/
theorem relabel_pure (e : A ≃ B) (a : α) :
    relabel e (SubInstrument.pure a : SubInstrument A A α) = SubInstrument.pure a := by
  refine DSubInstrument.ext <| funext fun j => LinearMap.ext fun ρ => ?_
  rw [relabel_branch, reindexMap_apply]
  obtain rfl | h := eq_or_ne j a
  · simp only [SubInstrument.branch_pure_self, LinearMap.id_apply, Matrix.submatrix_submatrix,
      Equiv.self_comp_symm, Matrix.submatrix_id_id]
  · simp only [SubInstrument.branch_pure_of_ne h, LinearMap.zero_apply]
    ext x y
    simp

/-- Relabelling preserves sequencing. -/
theorem relabel_bind (e : A ≃ B) (p : SubInstrument A A α) (k : α → SubInstrument A A β) :
    relabel e (p.bind k) = (relabel e p).bind fun a => relabel e (k a) := by
  refine DSubInstrument.ext <| funext fun c => LinearMap.ext fun ρ => ?_
  rw [relabel_branch, SubInstrument.bind, SubInstrument.bind, DSubInstrument.branch_bind_apply]
  ext x y
  rw [reindexMap_apply, DSubInstrument.branch_bind_apply]
  have h₁ : Summable fun i => (k i).branch c (p.branch i (ρ.submatrix e e)) :=
    (p.isCPTNIFamily.comp_eval (fun a => (k a).isCPTNIFamily) c).summable_apply _
  have h₂ : Summable fun i => (relabel e (k i)).branch c ((relabel e p).branch i ρ) :=
    ((relabel e p).isCPTNIFamily.comp_eval
      (fun a => (relabel e (k a)).isCPTNIFamily) c).summable_apply _
  rw [Matrix.submatrix_apply, Matrix.tsum_apply_apply h₁, Matrix.tsum_apply_apply h₂]
  refine tsum_congr fun i => ?_
  rw [relabel_branch, relabel_branch, reindexMap_apply, reindexMap_apply, Matrix.submatrix_apply,
    Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]

/-- Relabelling twice is relabelling along the composite. -/
theorem relabel_relabel (e : A ≃ B) (e' : B ≃ C) (q : SubInstrument A A α) :
    relabel e' (relabel e q) = relabel (e.trans e') q :=
  DSubInstrument.ext <| funext fun _ => LinearMap.ext fun _ => rfl

/-- Relabelling along the identity is the identity. -/
theorem relabel_refl (q : SubInstrument A A α) : relabel (Equiv.refl A) q = q :=
  DSubInstrument.ext <| funext fun _ => LinearMap.ext fun _ => rfl

/-- Framing commutes with relabelling. -/
theorem frame_relabel (e : A ≃ B) (q : SubInstrument A A α) (R : Type) [Fintype R] :
    (relabel e q).frame R = relabel (e.prodCongr (Equiv.refl R)) (q.frame R) :=
  DSubInstrument.ext <| funext fun _ => LinearMap.ext fun _ => rfl

/-- Framing twice is framing by the product, up to reassociation. -/
theorem frame_frame (q : SubInstrument A A α) (R S : Type) [Fintype R] [Fintype S] :
    (q.frame R).frame S = relabel (Equiv.prodAssoc A R S).symm (q.frame (R × S)) :=
  DSubInstrument.ext <| funext fun _ => LinearMap.ext fun _ => rfl

/-- Framing by the one-point register is relabelling. -/
theorem frame_unit (q : SubInstrument A A α) :
    q.frame Unit = relabel (Equiv.prodPUnit A).symm q :=
  DSubInstrument.ext <| funext fun _ => LinearMap.ext fun _ => rfl

/-- Framing by equivalent registers agrees up to relabelling. -/
theorem relabel_frame_congr {R S : Type} [Fintype R] [Fintype S] (f : R ≃ S)
    (q : SubInstrument A A α) :
    relabel ((Equiv.refl A).prodCongr f) (q.frame R) = q.frame S := by
  refine DSubInstrument.ext <| funext fun _ => LinearMap.ext fun ρ => ?_
  ext x y
  simp only [relabel_branch, reindexMap_apply, Matrix.submatrix_apply,
    DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply, Matrix.submatrix_submatrix]
  simp only [Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map,
    Equiv.refl_apply, Function.comp_def, Equiv.apply_symm_apply]

omit [Fintype B] in
/-- A relabelling that fixes every basis state is the identity. -/
theorem relabel_of_forall_eq (e : A ≃ A) (he : ∀ x, e x = x) (q : SubInstrument A A α) :
    relabel e q = q := by
  rw [show e = Equiv.refl A from Equiv.ext he, relabel_refl]

omit [Fintype C] in
/-- Framings by equivalent registers placed by compatible relabellings agree. -/
theorem relabel_frame_eq {R S : Type} [Fintype R] [Fintype S] (q : SubInstrument A A α)
    (e₁ : A × R ≃ B) (e₂ : A × S ≃ B) (f : R ≃ S) (h : ∀ a r, e₂ (a, f r) = e₁ (a, r)) :
    relabel e₁ (q.frame R) = relabel e₂ (q.frame S) := by
  rw [← relabel_frame_congr f q, relabel_relabel]
  congr 1
  exact Equiv.ext fun x => (h x.1 x.2).symm

/-- The equivalence `(A × K) × H ≃ (A × H) × K` exchanging the two right factors. -/
def midSwap (A K H : Type) : (A × K) × H ≃ (A × H) × K where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence `(A × C) × B ≃ A × (B × C)` that places a register `C` beside `A` to the
right of `B`. -/
def placeR (A B C : Type) : (A × C) × B ≃ A × (B × C) where
  toFun x := (x.1.1, (x.2, x.1.2))
  invFun x := ((x.1, x.2.2), x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

end Relabel

/-! ## Preparing and discarding a relabelled register -/

section Boundary

variable {A K K' C : Type} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
  [Fintype K'] [DecidableEq K'] [Fintype C] {β γ : Type}

/-- The branch of `appendBasis k₀` is `ρ ↦ ρ ⊗ |k₀⟩⟨k₀|`. -/
theorem appendBasis_branch_apply (k₀ : K) (ρ : Matrix A A ℂ) (x y : A × K) :
    (appendBasis k₀).branch () ρ x y = if x.2 = k₀ ∧ y.2 = k₀ then ρ x.1 y.1 else 0 := by
  rcases x with ⟨a, k⟩
  rcases y with ⟨a', k'⟩
  simp only [appendBasis, appendKraus, DSubInstrument.branch_ofKraus_apply,
    MatrixMap.conj_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Prod.ext_iff]
  by_cases h : k = k₀ <;> by_cases h' : k' = k₀ <;> simp [h, h']

/-- The branch of `discardRight` at `k` takes the block `(k, k)` of the right factor. -/
theorem discardRight_branch_apply (k : K) (ρ : Matrix (A × K) (A × K) ℂ) :
    (discardRight (A := A)).branch k ρ = ρ.submatrix (·, k) (·, k) := by
  ext a a'
  simp [discardRight, discardKraus, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Preparing a register in a basis state, running a relabelled subinstrument and discarding
the register is preparing the corresponding basis state, running the subinstrument and
discarding the register. -/
theorem appendBasis_relabel_discard (e : K ≃ K') (k₀ : K)
    (X : SubInstrument (A × K) (A × K) γ) (g : γ → SubInstrument A C β) :
    (appendBasis (e k₀)).bind (fun _ => (relabel ((Equiv.refl A).prodCongr e) X).bind
      fun c => discardRight.bind fun _ => g c) =
    (appendBasis k₀).bind (fun _ => X.bind fun c => discardRight.bind fun _ => g c) := by
  refine DSubInstrument.ext <| funext fun b => LinearMap.ext fun ρ => ?_
  have h₀ : ((appendBasis (e k₀)).branch () ρ).submatrix ((Equiv.refl A).prodCongr e)
      ((Equiv.refl A).prodCongr e) = (appendBasis k₀).branch () ρ := by
    ext x y
    simp only [Matrix.submatrix_apply, appendBasis_branch_apply, Equiv.prodCongr_apply,
      Prod.map, Equiv.refl_apply, e.apply_eq_iff_eq]
  have hd : ∀ (c : γ) (Y : Matrix (A × K) (A × K) ℂ),
      (discardRight.bind fun _ => g c).branch b
        (Y.submatrix ((Equiv.refl A).prodCongr e).symm ((Equiv.refl A).prodCongr e).symm) =
      (discardRight.bind fun _ => g c).branch b Y := by
    intro c Y
    rw [DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply, tsum_fintype,
      tsum_fintype]
    refine Fintype.sum_equiv e.symm _ _ fun k' => ?_
    rw [discardRight_branch_apply, discardRight_branch_apply]
    rfl
  rw [DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply]
  refine tsum_congr fun u => ?_
  cases u
  rw [DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply]
  refine tsum_congr fun c => ?_
  rw [relabel_branch, reindexMap_apply, h₀, hd]

/-- Preparing and discarding the one-point register around `X` is `X`. -/
theorem appendBasis_unit_discard (X : SubInstrument A A γ) (g : γ → SubInstrument A C β) :
    (appendBasis ()).bind (fun _ => (relabel (Equiv.prodPUnit A).symm X).bind
      fun c => discardRight.bind fun _ => g c) = X.bind g := by
  refine DSubInstrument.ext <| funext fun b => LinearMap.ext fun ρ => ?_
  have h₀ : ((appendBasis ()).branch () ρ).submatrix (Equiv.prodPUnit A).symm
      (Equiv.prodPUnit A).symm = ρ := by
    ext a a'
    simp [appendBasis_branch_apply]
  rw [DSubInstrument.branch_bind_apply, tsum_fintype, Fintype.sum_unique,
    DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply]
  refine tsum_congr fun c => ?_
  rw [DSubInstrument.branch_bind_apply, tsum_fintype, Fintype.sum_unique, relabel_branch,
    reindexMap_apply, h₀, discardRight_branch_apply]
  rfl

end Boundary

/-! ## Environments with a memory register -/

/-- An interactive quantum environment with internal state `ζ` and a private memory register
`K`, acting on the interface register `Fin d` and on `K`. The memory register is prepared in
the basis state `initReg` and kept across activations. -/
structure QStratQ (K : Type) [Fintype K] (ζ E O : Type) (d : ℕ) where
  /-- Number of activations. -/
  rounds : ℕ
  /-- Initial environment state. -/
  init : ζ
  /-- Initial basis state of the memory register. -/
  initReg : K
  /-- Choice of the next event. -/
  next : ζ → SubInstrument (Fin d × K) (Fin d × K) (ζ × E)
  /-- Observation of an output. -/
  obs : ζ → O → SubInstrument (Fin d × K) (Fin d × K) ζ

variable {H H' K K' : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
  [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
variable {τ υ ζ ζ₁ ζ₂ E O : Type} {d : ℕ}

/-- An operation of an environment with memory `K` placed on the joint register
`(Fin d × H) × K`. -/
def envPlace (H : Type) [Fintype H] {α : Type} (w : SubInstrument (Fin d × K) (Fin d × K) α) :
    SubInstrument ((Fin d × H) × K) ((Fin d × H) × K) α :=
  relabel (midSwap (Fin d) K H) (w.frame H)

omit [DecidableEq H] [DecidableEq K] in
/-- The joint run of the environment `Z` with memory `K` and the system `S` for `n` activations,
on the register `(Fin d × H) × K`. -/
def qloopQ (S : QSys H τ E O d) (Z : QStratQ K ζ E O d) :
    ℕ → ζ × τ → SubInstrument ((Fin d × H) × K) ((Fin d × H) × K) (ζ × τ)
  | 0, c => SubInstrument.pure c
  | n + 1, c =>
    (envPlace H (Z.next c.1)).bind fun a =>
      ((S.step c.2 a.2).frame K).bind fun p =>
        (envPlace H (Z.obs a.1 p.2)).bind fun z =>
          qloopQ S Z n (z, p.1)

/-- The view of the environment `Z` with memory `K` against `S`: prepare the private register
of `S` and the memory register of `Z` in their initial basis states, run `Z.rounds`
activations, discard both registers and return the final environment state. -/
def qviewQ (S : QSys H τ E O d) (Z : QStratQ K ζ E O d) : CPComp d ζ :=
  (appendBasis S.initReg).bind fun _ =>
    (appendBasis Z.initReg).bind fun _ =>
      (qloopQ S Z Z.rounds (Z.init, S.init)).bind fun c =>
        discardRight.bind fun _ => discardRight.bind fun _ => SubInstrument.pure c.1

omit [DecidableEq H] [DecidableEq K] [DecidableEq K'] in
/-- Relabelling the memory register commutes with placing an environment operation. -/
theorem relabel_envPlace {α : Type} (e : K ≃ K') (w : SubInstrument (Fin d × K) (Fin d × K) α) :
    relabel ((Equiv.refl (Fin d × H)).prodCongr e) (relabel (midSwap (Fin d) K H) (w.frame H)) =
      relabel (midSwap (Fin d) K' H) ((relabel ((Equiv.refl (Fin d)).prodCongr e) w).frame H) := by
  simp only [frame_relabel, relabel_relabel]
  rfl

omit [DecidableEq H] [DecidableEq K] [DecidableEq K'] in
/-- **Morphism of environments with memory.** An equivalence `e` of memory registers and a map
`f` of environment states that intertwine the steps of two environments intertwine their
joint runs. -/
theorem qloopQ_iso (S : QSys H τ E O d) (Z₁ : QStratQ K ζ₁ E O d) (Z₂ : QStratQ K' ζ₂ E O d)
    (e : K ≃ K') (f : ζ₁ → ζ₂)
    (hn : ∀ z, (relabel ((Equiv.refl (Fin d)).prodCongr e) (Z₁.next z)).bind
      (fun a => SubInstrument.pure (f a.1, a.2)) = Z₂.next (f z))
    (ho : ∀ z o, (relabel ((Equiv.refl (Fin d)).prodCongr e) (Z₁.obs z o)).bind
      (fun z' => SubInstrument.pure (f z')) = Z₂.obs (f z) o)
    (n : ℕ) (z : ζ₁) (t : τ) :
    (relabel ((Equiv.refl (Fin d × H)).prodCongr e) (qloopQ S Z₁ n (z, t))).bind
      (fun c => SubInstrument.pure (f c.1, c.2)) = qloopQ S Z₂ n (f z, t) := by
  induction n generalizing z t with
  | zero => simp only [qloopQ, relabel_pure, SubInstrument.pure_bind]
  | succ n ih =>
    simp only [qloopQ, envPlace, ← hn, ← ho, relabel_bind, relabel_envPlace,
      relabel_frame_congr, SubInstrument.frame_bind, SubInstrument.frame_pure, relabel_pure,
      SubInstrument.bind_assoc, SubInstrument.pure_bind, ← ih]

/-- The view is invariant under an equivalence of memory registers and a map of environment
states that intertwine the environment steps. -/
theorem qviewQ_iso (S : QSys H τ E O d) (Z₁ : QStratQ K ζ₁ E O d) (Z₂ : QStratQ K' ζ₂ E O d)
    (e : K ≃ K') (f : ζ₁ → ζ₂) (hr : Z₁.rounds = Z₂.rounds) (hi : f Z₁.init = Z₂.init)
    (hk : e Z₁.initReg = Z₂.initReg)
    (hn : ∀ z, (relabel ((Equiv.refl (Fin d)).prodCongr e) (Z₁.next z)).bind
      (fun a => SubInstrument.pure (f a.1, a.2)) = Z₂.next (f z))
    (ho : ∀ z o, (relabel ((Equiv.refl (Fin d)).prodCongr e) (Z₁.obs z o)).bind
      (fun z' => SubInstrument.pure (f z')) = Z₂.obs (f z) o) :
    (qviewQ S Z₁).bind (fun z => SubInstrument.pure (f z)) = qviewQ S Z₂ := by
  simp only [qviewQ, ← hr, ← hi, ← hk, ← qloopQ_iso S Z₁ Z₂ e f hn ho,
    SubInstrument.bind_assoc, SubInstrument.pure_bind, appendBasis_relabel_discard]

/-! ## Simulators with a private register -/

/-- A simulator with classical state `σ` and a private quantum register `M` between the real
interface (events `E`, outputs `O`) and the ideal interface (events `EG`, outputs `OG`). It
translates each real event to an ideal event and each ideal output to a real output, acting on
the environment register `Fin d` and on `M`. The register `M` is prepared in the basis state
`initReg` and kept across activations. -/
structure QSimQ (M : Type) [Fintype M] (σ E O EG OG : Type) (d : ℕ) where
  /-- Initial simulator state. -/
  init : σ
  /-- Initial basis state of the simulator register. -/
  initReg : M
  /-- Translation of a real event. -/
  pre : σ → E → SubInstrument (Fin d × M) (Fin d × M) (σ × EG)
  /-- Translation of an ideal output. -/
  post : σ → OG → SubInstrument (Fin d × M) (Fin d × M) (σ × O)

/-- An operation on `Fin d × B` placed on `Fin d × (B × C)`. -/
def placeLeft (B C : Type) [Fintype B] [Fintype C] {α : Type}
    (w : SubInstrument (Fin d × B) (Fin d × B) α) :
    SubInstrument (Fin d × (B × C)) (Fin d × (B × C)) α :=
  relabel (Equiv.prodAssoc (Fin d) B C) (w.frame C)

/-- An operation on `Fin d × C` placed on `Fin d × (B × C)`. -/
def placeRight (B C : Type) [Fintype B] [Fintype C] {α : Type}
    (s : SubInstrument (Fin d × C) (Fin d × C) α) :
    SubInstrument (Fin d × (B × C)) (Fin d × (B × C)) α :=
  relabel (placeR (Fin d) B C) (s.frame B)

namespace QSimQ

variable {M M₁ M₂ σ σ₁ σ₂ EM OM EG OG : Type} [Fintype M] [Fintype M₁] [Fintype M₂]

/-- The environment `Z` with the simulator `S` absorbed: an environment for the ideal
interface whose state pairs the state of `Z` with the simulator state and whose memory
register is the memory of `Z` beside the register of `S`. -/
def absorb (S : QSimQ M σ E O EG OG d) (Z : QStratQ K ζ E O d) :
    QStratQ (K × M) (ζ × σ) EG OG d where
  rounds := Z.rounds
  init := (Z.init, S.init)
  initReg := (Z.initReg, S.initReg)
  next c := (placeLeft K M (Z.next c.1)).bind fun a =>
    (placeRight K M (S.pre c.2 a.2)).bind fun b => SubInstrument.pure ((a.1, b.1), b.2)
  obs c og := (placeRight K M (S.post c.2 og)).bind fun b =>
    (placeLeft K M (Z.obs c.1 b.2)).bind fun z => SubInstrument.pure (z, b.1)

/-- The identity simulator, with the one-point register. -/
def id : QSimQ Unit Unit E O E O d where
  init := ()
  initReg := ()
  pre _ e := SubInstrument.pure ((), e)
  post _ o := SubInstrument.pure ((), o)

/-- The composite of a simulator `S₁` from the real to a middle interface and a simulator `S₂`
from the middle to the ideal interface; its register is the product of their registers. -/
def comp (S₁ : QSimQ M₁ σ₁ E O EM OM d) (S₂ : QSimQ M₂ σ₂ EM OM EG OG d) :
    QSimQ (M₁ × M₂) (σ₁ × σ₂) E O EG OG d where
  init := (S₁.init, S₂.init)
  initReg := (S₁.initReg, S₂.initReg)
  pre s e := (placeLeft M₁ M₂ (S₁.pre s.1 e)).bind fun a =>
    (placeRight M₁ M₂ (S₂.pre s.2 a.2)).bind fun b => SubInstrument.pure ((a.1, b.1), b.2)
  post s og := (placeRight M₁ M₂ (S₂.post s.2 og)).bind fun b =>
    (placeLeft M₁ M₂ (S₁.post s.1 b.2)).bind fun a => SubInstrument.pure ((a.1, b.1), a.2)

end QSimQ

variable {M M₁ M₂ σ σ₁ σ₂ EM OM EG OG : Type} [Fintype M] [DecidableEq M] [Fintype M₁]
  [DecidableEq M₁] [Fintype M₂] [DecidableEq M₂]

/-- The view of `Z` against the ideal system `I` behind the simulator `S`: the view of the
absorbed environment, projected to the state of `Z`. -/
def simViewQ (I : QSys H' υ EG OG d) (S : QSimQ M σ E O EG OG d) (Z : QStratQ K ζ E O d) :
    CPComp d ζ :=
  (qviewQ I (S.absorb Z)).bind fun c => SubInstrument.pure c.1

/-- `R` realizes `I` behind the simulator `S` with a private register at distance `ε`: for
every memory register `K` and environment state type `ζ`, the view map of `R` and the view
map of `I` behind `S` are within diamond distance `ε`. -/
def QRealizesSimQ (R : QSys H τ E O d) (I : QSys H' υ EG OG d) (S : QSimQ M σ E O EG OG d)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ζ : Type),
    QUCEmulatesDiamond ε (fun Z : QStratQ K ζ E O d => (qviewQ R Z).toQComp)
      (fun Z => (simViewQ I S Z).toQComp) (fun Z => CPComp.branch_cp (qviewQ R Z))
      (fun Z => CPComp.branch_cp (simViewQ I S Z))

/-- Behind the identity simulator the view is the view of the system. -/
theorem simViewQ_id (R : QSys H τ E O d) (Z : QStratQ K ζ E O d) :
    simViewQ R QSimQ.id Z = qviewQ R Z := by
  refine qviewQ_iso R (QSimQ.id.absorb Z) Z (Equiv.prodPUnit K) Prod.fst rfl rfl rfl
    (fun c => ?_) (fun c o => ?_)
  · simp only [QSimQ.absorb, QSimQ.id, placeLeft, placeRight, SubInstrument.frame_pure,
      relabel_pure, SubInstrument.pure_bind, relabel_bind, SubInstrument.bind_assoc,
      frame_unit, relabel_relabel]
    rw [relabel_of_forall_eq _ fun _ => rfl, SubInstrument.bind_pure]
  · simp only [QSimQ.absorb, QSimQ.id, placeLeft, placeRight, SubInstrument.frame_pure,
      relabel_pure, SubInstrument.pure_bind, relabel_bind, SubInstrument.bind_assoc,
      frame_unit, relabel_relabel]
    rw [relabel_of_forall_eq _ fun _ => rfl, SubInstrument.bind_pure]

/-- Behind a composite simulator the view is the view behind the second simulator of the
environment with the first simulator absorbed, projected to the state of `Z`. -/
theorem simViewQ_comp {τ' H'' : Type} [Fintype H''] [DecidableEq H'']
    (I : QSys H'' τ' EG OG d) (S₁ : QSimQ M₁ σ₁ E O EM OM d) (S₂ : QSimQ M₂ σ₂ EM OM EG OG d)
    (Z : QStratQ K ζ E O d) :
    simViewQ I (S₁.comp S₂) Z =
      (simViewQ I S₂ (S₁.absorb Z)).bind fun c => SubInstrument.pure c.1 := by
  have hZ : ∀ {α : Type} (w : SubInstrument (Fin d × K) (Fin d × K) α),
      relabel ((Equiv.refl (Fin d)).prodCongr (Equiv.prodAssoc K M₁ M₂).symm)
        (relabel (Equiv.prodAssoc (Fin d) K (M₁ × M₂)) (w.frame (M₁ × M₂))) =
      relabel (Equiv.prodAssoc (Fin d) (K × M₁) M₂)
        ((relabel (Equiv.prodAssoc (Fin d) K M₁) (w.frame M₁)).frame M₂) := by
    intro α w
    simp only [frame_relabel, frame_frame, relabel_relabel]
    rfl
  have hS₁ : ∀ {α : Type} (s : SubInstrument (Fin d × M₁) (Fin d × M₁) α),
      relabel ((Equiv.refl (Fin d)).prodCongr (Equiv.prodAssoc K M₁ M₂).symm)
        (relabel (placeR (Fin d) K (M₁ × M₂))
          ((relabel (Equiv.prodAssoc (Fin d) M₁ M₂) (s.frame M₂)).frame K)) =
      relabel (Equiv.prodAssoc (Fin d) (K × M₁) M₂)
        ((relabel (placeR (Fin d) K M₁) (s.frame K)).frame M₂) := by
    intro α s
    simp only [frame_relabel, frame_frame, relabel_relabel]
    exact relabel_frame_eq _ _ _ (Equiv.prodComm _ _) fun _ _ => rfl
  have hS₂ : ∀ {α : Type} (s : SubInstrument (Fin d × M₂) (Fin d × M₂) α),
      relabel ((Equiv.refl (Fin d)).prodCongr (Equiv.prodAssoc K M₁ M₂).symm)
        (relabel (placeR (Fin d) K (M₁ × M₂))
          ((relabel (placeR (Fin d) M₁ M₂) (s.frame M₁)).frame K)) =
      relabel (placeR (Fin d) (K × M₁) M₂) (s.frame (K × M₁)) := by
    intro α s
    simp only [frame_relabel, frame_frame, relabel_relabel]
    exact relabel_frame_eq _ _ _ (Equiv.prodComm _ _) fun _ _ => rfl
  rw [simViewQ, simViewQ, ← qviewQ_iso I ((S₁.comp S₂).absorb Z) (S₂.absorb (S₁.absorb Z))
    (Equiv.prodAssoc K M₁ M₂).symm (fun c => ((c.1, c.2.1), c.2.2)) rfl rfl rfl
    (fun c => by
      simp only [QSimQ.absorb, QSimQ.comp, placeLeft, placeRight, relabel_bind, relabel_pure,
        SubInstrument.frame_bind, SubInstrument.frame_pure, SubInstrument.bind_assoc,
        SubInstrument.pure_bind, hZ, hS₁, hS₂])
    (fun c o => by
      simp only [QSimQ.absorb, QSimQ.comp, placeLeft, placeRight, relabel_bind, relabel_pure,
        SubInstrument.frame_bind, SubInstrument.frame_pure, SubInstrument.bind_assoc,
        SubInstrument.pure_bind, hZ, hS₁, hS₂])]
  simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind]

/-- Every system realizes itself behind the identity simulator at distance `0`. -/
theorem QRealizesSimQ.refl (R : QSys H τ E O d) : QRealizesSimQ R R QSimQ.id 0 :=
  fun _ _ _ _ => quc_congr _ _
    (QUCEmulatesDiamond.refl 0 _ fun Z => CPComp.branch_cp (qviewQ R Z)) rfl
    (funext fun Z => by rw [simViewQ_id])

/-- Realization behind a simulator with a private register is transitive: the simulators
compose, their registers are tensored and the distances add. -/
theorem QRealizesSimQ.trans {τ' H'' : Type} [Fintype H''] [DecidableEq H'']
    {R : QSys H τ E O d} {M' : QSys H' υ EM OM d} {I : QSys H'' τ' EG OG d}
    {S₁ : QSimQ M₁ σ₁ E O EM OM d} {S₂ : QSimQ M₂ σ₂ EM OM EG OG d} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : QRealizesSimQ R M' S₁ ε₁) (h₂ : QRealizesSimQ M' I S₂ ε₂) :
    QRealizesSimQ R I (S₁.comp S₂) (ε₁ + ε₂) := by
  intro K _ _ ζ
  have hk : IsCPChannel fun c : ζ × σ₁ =>
      CPComp.toQComp (SubInstrument.pure c.1 : CPComp d ζ) :=
    fun c => CPComp.branch_cp _
  have h₂' := QUCEmulatesDiamond.comp_right _ hk
    (fun Z b => by beta_reduce; rw [← CPComp.toQComp_qbind]; exact CPComp.branch_cp _ b)
    (fun Z b => by beta_reduce; rw [← CPComp.toQComp_qbind]; exact CPComp.branch_cp _ b)
    (quc_precomp (h₂ (K × M₁) (ζ × σ₁)) (QSimQ.absorb S₁ (ζ := ζ) (K := K)))
  refine QUCEmulatesDiamond.trans (h₁ K ζ) (quc_congr _ _ h₂' ?_ ?_)
  · exact funext fun Z => (CPComp.toQComp_qbind _ _).symm
  · exact funext fun Z => by rw [simViewQ_comp]; exact (CPComp.toQComp_qbind _ _).symm

/-! ## Memoryless environments and simulators -/

/-- A memoryless environment as an environment with the one-point memory register. -/
def QStrat.toQ (Z : QStrat ζ E O d) : QStratQ Unit ζ E O d where
  rounds := Z.rounds
  init := Z.init
  initReg := ()
  next z := (Z.next z).frame Unit
  obs z o := (Z.obs z o).frame Unit

/-- Unfolding lemma: the event choice of `Z.toQ`. -/
theorem QStrat.toQ_next (Z : QStrat ζ E O d) (z : ζ) : Z.toQ.next z = (Z.next z).frame Unit :=
  rfl

/-- Unfolding lemma: the observation of `Z.toQ`. -/
theorem QStrat.toQ_obs (Z : QStrat ζ E O d) (z : ζ) (o : O) :
    Z.toQ.obs z o = (Z.obs z o).frame Unit :=
  rfl

/-- A simulator without a quantum register as a simulator with the one-point register. -/
def QSim.toQ (S : QSim σ E O EG OG d) : QSimQ Unit σ E O EG OG d where
  init := S.init
  initReg := ()
  pre s e := (S.pre s e).frame Unit
  post s o := (S.post s o).frame Unit

omit [DecidableEq H] in
/-- The run against a memoryless environment with the one-point memory register is the run
against the memoryless environment, placed beside the one-point register. -/
theorem qloopQ_toQ (S : QSys H τ E O d) (Z : QStrat ζ E O d) (n : ℕ) (c : ζ × τ) :
    qloopQ S Z.toQ n c = relabel (Equiv.prodPUnit (Fin d × H)).symm (qloop S Z n c) := by
  have hw : ∀ {α : Type} (w : CPComp d α),
      relabel (midSwap (Fin d) Unit H) ((relabel (Equiv.prodPUnit (Fin d)).symm w).frame H) =
        relabel (Equiv.prodPUnit (Fin d × H)).symm (w.frame H) := by
    intro α w
    simp only [frame_relabel, relabel_relabel]
    rfl
  induction n generalizing c with
  | zero => simp only [qloopQ, qloop, relabel_pure]
  | succ n ih =>
    simp only [qloopQ, qloop, envPlace, QStrat.toQ_next, QStrat.toQ_obs, frame_unit, hw,
      relabel_bind, ih]

/-- The view of a memoryless environment with the one-point memory register is its view. -/
theorem qviewQ_toQ (S : QSys H τ E O d) (Z : QStrat ζ E O d) : qviewQ S Z.toQ = qview S Z := by
  simp only [qviewQ, qview, qloopQ_toQ]
  simp only [QStrat.toQ, appendBasis_unit_discard]

/-- Behind `S.toQ` the view of `Z.toQ` is the view of `Z` behind `S`. -/
theorem simViewQ_toQ (I : QSys H' υ EG OG d) (S : QSim σ E O EG OG d) (Z : QStrat ζ E O d) :
    simViewQ I S.toQ Z.toQ = simView I S Z := by
  rw [simViewQ, simView, ← qviewQ_toQ, ← qviewQ_iso I (S.toQ.absorb Z.toQ) (S.absorb Z).toQ
    (Equiv.prodPUnit Unit) (fun c => c) rfl rfl rfl
    (fun c => by
      simp only [QSimQ.absorb, QSim.absorb, QSim.toQ, QStrat.toQ, placeLeft, placeRight,
        frame_unit, relabel_bind, relabel_pure, relabel_relabel, SubInstrument.bind_assoc,
        SubInstrument.pure_bind]
      rfl)
    (fun c o => by
      simp only [QSimQ.absorb, QSim.absorb, QSim.toQ, QStrat.toQ, placeLeft, placeRight,
        frame_unit, relabel_bind, relabel_pure, relabel_relabel, SubInstrument.bind_assoc,
        SubInstrument.pure_bind]
      rfl)]
  simp only [SubInstrument.bind_pure]

/-- Realization behind `S.toQ` against environments with every memory register gives
realization behind `S` against memoryless environments. -/
theorem QRealizesSimQ.toQSim {R : QSys H τ E O d} {I : QSys H' υ EG OG d}
    {S : QSim σ E O EG OG d} {ε : ℝ≥0∞} (h : QRealizesSimQ R I S.toQ ε) :
    QRealizesSim R I S ε := fun ζ =>
  quc_congr _ _ (quc_precomp (h Unit ζ) QStrat.toQ) (funext fun Z => by rw [qviewQ_toQ])
    (funext fun Z => by rw [simViewQ_toQ])

end CatCrypt.Quantum.ReactiveUC
