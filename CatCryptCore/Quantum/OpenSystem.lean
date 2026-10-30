/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

-- import all: unfolds `OpenProcessActivationEquiv` and `OpenProcess.activationLTS`
import all PolyFun.Interaction.Open.OpenProcess
public import PolyFun.Interaction.Open.OpenProcessModel
public import QuantumFoundations.SubInstrument

/-!
# Quantum open systems: the wiring structure

An open system is an `OpenProcess m Party Δ` of PolyFun: a state space, a step
protocol per state exposing the port boundary `Δ`, and a per-step sampler that
resolves every move of the step in the monad `m`. PolyFun's `openTheory Party m σ`
composes open processes by `map`, `par`, `wire` and `plug`, for every
`m : Type → Type` and every scheduler sampler `σ : m (ULift Bool)`; it is
`OpenTheory.IsLawful` with no assumption on `m`, and its monoidal, traced and
compact closed laws hold up to `OpenProcessActivationEquiv`.

Taking `m` to be the monad `Quantum.SubInstrument M M` of completely positive,
trace-nonincreasing subinstruments on a register with basis `M` gives quantum open
systems: each move of a step is drawn by a quantum instrument acting on the
register. `CPComp d` is the case `M = Fin d`. The probabilistic and the quantum
open systems therefore share one wiring structure, PolyFun's `OpenTheory`.
The tensor product of quantum data, which acts on the register, is a second
structure on the same category. A process on `M` is placed on the left factor of
`M × N` by framing each sampler (`SubInstrument.frame`, the amplification `Φ ⊗ id`
of QuantumFoundations), a process on `N` on the right factor by `frameLeft`
(`id ⊗ Φ`), and the tensor of two processes is the parallel composition of the
placed processes. The two structures are separate, as in Selinger's quantum
programming language QPL, where the sum structure carries the trace used for loops
and the tensor carries quantum data; they are related by the interchange laws below.

## Main definitions

* `OpenSystem.hoist φ p` — the open process `p` with every sampler transported
  along a family of maps `φ : ∀ X, m X → n X`
* `OpenSystem.QOpenProcess Party M Δ` — quantum open processes on the register `M`
* `OpenSystem.quantumOpenTheory Party M σ` — PolyFun's `openTheory` at the
  subinstrument monad, with scheduler `σ`
* `OpenSystem.frameLeft q L` — the subinstrument `q` on the right factor of `L × N`
* `OpenSystem.tensor σ P Q` — the tensor of quantum open processes on `M` and `N`,
  a quantum open process on `M × N`

## Main results

* `OpenSystem.hoist_par`, `OpenSystem.hoist_wire`, `OpenSystem.hoist_plug`,
  `OpenSystem.hoist_map` — composition in `openTheory` is natural in the sampling
  monad: transporting the samplers of a composite is composing the transported
  processes, with the transported scheduler
* `OpenSystem.samplePath_hoist` — along a monad morphism, sampling a transported
  sampler is transporting the sampled path
* `OpenSystem.activationEquiv_hoist_iff` — transport preserves and reflects
  activation equivalence
* `OpenSystem.quantumOpenTheory_isLawful` — quantum open systems form a lawful
  `OpenTheory`
* `OpenSystem.frameLeft_pure`, `OpenSystem.frameLeft_bind` — `frameLeft` is a monad
  morphism, as `SubInstrument.frame` is
* `OpenSystem.frame_bind_frameLeft_comm` — operations on the two factors commute on
  every joint state, entangled or not
* `OpenSystem.tensor_step_comm` — in a tensor, the two schedules of a step of each
  component give the same quantum operation
* `OpenSystem.frame_par`, `OpenSystem.frameLeft_par` — placing a parallel
  composition on a factor is the parallel composition of the placed processes
* `OpenSystem.traceRight_wire_frame` — the partial trace over the added factor
  commutes with each sampled step of a placed wiring

## References

* P. Selinger, *Towards a quantum programming language*, Mathematical Structures
  in Computer Science 14(4), 2004.
* PolyFun, `PolyFun.Interaction.Open.OpenTheory` and
  `PolyFun.Interaction.Open.OpenProcessModel`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w' w''

namespace CatCrypt.Quantum.OpenSystem

open Interaction Interaction.Open Concurrent

/-! ## Transport of samplers along a change of monad -/

section Hoist

variable {Party : Type u} {m : Type w → Type w'} {n : Type w → Type w''}

/-- The open process `p` with each per-step sampler transported along `φ`. The
state space and the step protocols are those of `p`. -/
def hoist (φ : TypeTree.Node.ContextHom (fun X => m X) (fun X => n X))
    {Δ : PortBoundary} (p : OpenProcess.{u, v, w, w'} m Party Δ) :
    OpenProcess.{u, v, w, w''} n Party Δ where
  Proc := p.Proc
  step := p.step
  stepSampler s := TypeTree.Decoration.map φ _ (p.stepSampler s)

/-- Transport forgets nothing of the structural process. -/
theorem toProcess_hoist (φ : TypeTree.Node.ContextHom (fun X => m X) (fun X => n X))
    {Δ : PortBoundary} (p : OpenProcess.{u, v, w, w'} m Party Δ) :
    (hoist φ p).toProcess = p.toProcess := rfl

/-- Transport along the identity is the identity. -/
theorem hoist_id {Δ : PortBoundary} (p : OpenProcess.{u, v, w, w'} m Party Δ) :
    hoist (TypeTree.Node.ContextHom.id (fun X => m X)) p = p := by
  cases p with | mk Proc step stepSampler =>
  simp only [hoist, TypeTree.Decoration.map_id]

/-- Transport along a composite is the composite of the transports. -/
theorem hoist_comp {k : Type w → Type w'}
    (ψ : TypeTree.Node.ContextHom (fun X => n X) (fun X => k X))
    (φ : TypeTree.Node.ContextHom (fun X => m X) (fun X => n X))
    {Δ : PortBoundary} (p : OpenProcess.{u, v, w, w'} m Party Δ) :
    hoist ψ (hoist φ p) = hoist (TypeTree.Node.ContextHom.comp ψ φ) p := by
  simp only [hoist, TypeTree.Decoration.map_comp]

/-- Transport commutes with boundary adaptation. -/
theorem hoist_mapBoundary (φ : TypeTree.Node.ContextHom (fun X => m X) (fun X => n X))
    {Δ₁ Δ₂ : PortBoundary} (f : PortBoundary.Hom Δ₁ Δ₂)
    (p : OpenProcess.{u, v, w, w'} m Party Δ₁) :
    hoist φ (p.mapBoundary f) = (hoist φ p).mapBoundary f := rfl

/-- Transporting an interleaving sampler transports the scheduler and both branch
samplers. -/
theorem map_sampler_interleave (φ : TypeTree.Node.ContextHom (fun X => m X) (fun X => n X))
    {spec₁ spec₂ : TypeTree.{w}} (σ : m (ULift.{w, 0} Bool))
    (S₁ : TypeTree.Sampler m spec₁) (S₂ : TypeTree.Sampler m spec₂) :
    TypeTree.Decoration.map φ _ (TypeTree.Sampler.interleave σ S₁ S₂) =
      TypeTree.Sampler.interleave (φ _ σ) (TypeTree.Decoration.map φ spec₁ S₁)
        (TypeTree.Decoration.map φ spec₂ S₂) := by
  rw [TypeTree.Sampler.interleave_eq, TypeTree.Sampler.interleave_eq]
  refine Prod.ext rfl (funext fun x => ?_)
  rcases x with ⟨_ | _⟩ <;> rfl

/-- Transport commutes with binary-choice interleaving; the scheduler sampler is
transported as well. -/
theorem hoist_interleave (φ : TypeTree.Node.ContextHom (fun X => m X) (fun X => n X))
    {Δ₁ Δ₂ Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (ctx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (σ : m (ULift.{w, 0} Bool)) :
    hoist φ (p₁.interleave p₂ f₁ f₂ ctx σ) =
      (hoist φ p₁).interleave (hoist φ p₂) f₁ f₂ ctx (φ _ σ) := by
  simp only [hoist, OpenProcess.interleave]
  congr 1
  funext s
  rcases s with ⟨s₁, s₂⟩
  exact map_sampler_interleave φ σ (p₁.stepSampler s₁) (p₂.stepSampler s₂)

end Hoist

/-! ## Naturality of the open theory in the sampling monad -/

section Naturality

variable (Party : Type u) {m : Type w → Type w'} {n : Type w → Type w''}
variable (φ : TypeTree.Node.ContextHom (fun X => m X) (fun X => n X))
variable (σ : m (ULift.{w, 0} Bool))

/-- Boundary adaptation in `openTheory` is natural in the sampling monad. -/
theorem hoist_map {Δ₁ Δ₂ : PortBoundary} (f : PortBoundary.Hom Δ₁ Δ₂)
    (p : OpenProcess.{u, v, w, w'} m Party Δ₁) :
    hoist φ ((openTheory.{u, v, w, w'} Party m σ).map f p) =
      (openTheory.{u, v, w, w''} Party n (φ _ σ)).map f (hoist φ p) := rfl

/-- Parallel composition in `openTheory` is natural in the sampling monad. -/
theorem hoist_par {Δ₁ Δ₂ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂) :
    hoist φ ((openTheory.{u, v, w, w'} Party m σ).par p₁ p₂) =
      (openTheory.{u, v, w, w''} Party n (φ _ σ)).par (hoist φ p₁) (hoist φ p₂) :=
  hoist_interleave φ p₁ p₂ _ _ _ σ

/-- Wiring in `openTheory` is natural in the sampling monad. -/
theorem hoist_wire {Δ₁ Γ Δ₂ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
    (p₂ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    hoist φ ((openTheory.{u, v, w, w'} Party m σ).wire p₁ p₂) =
      (openTheory.{u, v, w, w''} Party n (φ _ σ)).wire (hoist φ p₁) (hoist φ p₂) :=
  hoist_interleave φ p₁ p₂ _ _ _ σ

/-- Plugging in `openTheory` is natural in the sampling monad. -/
theorem hoist_plug {Δ : PortBoundary}
    (p : OpenProcess.{u, v, w, w'} m Party Δ)
    (k : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap Δ)) :
    hoist φ ((openTheory.{u, v, w, w'} Party m σ).plug p k) =
      (openTheory.{u, v, w, w''} Party n (φ _ σ)).plug (hoist φ p) (hoist φ k) :=
  hoist_interleave φ p k _ _ _ σ

end Naturality

/-! ## Sampling along a monad morphism -/

section Sample

variable {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] [Monad n]

/-- Along a family `φ` that preserves `pure` and `bind`, sampling a transported
sampler is transporting the sampled path. -/
theorem samplePath_hoist (φ : TypeTree.Node.ContextHom (fun X => m X) (fun X => n X))
    (hpure : ∀ {X : Type w} (x : X), φ X (pure x) = pure x)
    (hbind : ∀ {X Y : Type w} (c : m X) (f : X → m Y),
      φ Y (c >>= f) = φ X c >>= fun x => φ Y (f x)) :
    (spec : TypeTree.{w}) → (S : TypeTree.Sampler m spec) →
      TypeTree.samplePath spec (TypeTree.Decoration.map φ spec S) =
        φ _ (TypeTree.samplePath spec S)
  | .done, _ => by
    simp only [TypeTree.samplePath_done, hpure]
  | .node _ rest, ⟨samp, sampRest⟩ => by
    have hmap : TypeTree.Decoration.map φ (TypeTree.node _ rest) (samp, sampRest) =
        (φ _ samp, fun x => TypeTree.Decoration.map φ (rest x) (sampRest x)) := rfl
    rw [hmap, TypeTree.samplePath_node, TypeTree.samplePath_node, hbind]
    refine congrArg _ (funext fun x => ?_)
    rw [hbind, samplePath_hoist φ hpure hbind (rest x) (sampRest x)]
    exact congrArg _ (funext fun tr => (hpure _).symm)

end Sample

/-! ## Activation equivalence -/

/-- Transport of samplers preserves and reflects activation equivalence, which
compares the structural processes only. -/
theorem activationEquiv_hoist_iff {Party : Type u} {m : Type w → Type w'}
    {n : Type w → Type w''}
    (φ : TypeTree.Node.ContextHom (fun X => m X) (fun X => n X)) {Δ : PortBoundary}
    (p q : OpenProcess.{u, v, w, w'} m Party Δ) :
    OpenProcessActivationEquiv (hoist φ p) (hoist φ q) ↔ OpenProcessActivationEquiv p q :=
  Iff.rfl

/-! ## Quantum open systems -/

section Quantum

/-- Quantum open processes on the register with basis `M`: open processes whose
step samplers are completely positive, trace-nonincreasing subinstruments on `M`. -/
abbrev QOpenProcess (Party : Type u) (M : Type) [Fintype M] (Δ : PortBoundary) :=
  OpenProcess.{u, v, 0, 0} (Quantum.SubInstrument M M) Party Δ

/-- The open theory of quantum open processes on the register `M`, with scheduler
`σ`: PolyFun's `openTheory` at the subinstrument monad. -/
noncomputable abbrev quantumOpenTheory (Party : Type u) (M : Type) [Fintype M]
    (σ : Quantum.SubInstrument M M (ULift.{0, 0} Bool)) : OpenTheory :=
  openTheory.{u, v, 0, 0} Party (Quantum.SubInstrument M M) σ

variable (Party : Type u) (M : Type) [Fintype M] (σ : Quantum.SubInstrument M M (ULift Bool))

/-- Quantum open systems form a lawful open theory: `map` is functorial and `par`,
`wire`, `plug` are natural in boundary adaptation. -/
instance quantumOpenTheory_isLawful :
    OpenTheory.IsLawful (quantumOpenTheory.{u, v} Party M σ) :=
  inferInstanceAs (OpenTheory.IsLawful (openTheory.{u, v, 0, 0} Party _ σ))

/-- The quantum open theory has a monoidal unit. -/
instance quantumOpenTheory_hasUnit : OpenTheory.HasUnit (quantumOpenTheory.{u, v} Party M σ) :=
  inferInstanceAs (OpenTheory.HasUnit (openTheory.{u, v, 0, 0} Party _ σ))

/-- The quantum open theory has identity wires. -/
instance quantumOpenTheory_hasIdWire :
    OpenTheory.HasIdWire (quantumOpenTheory.{u, v} Party M σ) :=
  inferInstanceAs (OpenTheory.HasIdWire (openTheory.{u, v, 0, 0} Party _ σ))

end Quantum

/-! ## The tensor of quantum data -/

section TensorData

open _root_.Quantum
open scoped ComplexOrder

variable {M N L R S : Type} [Fintype M] [Fintype N] {α β : Type}

/-- A left amplification is a right amplification conjugated by the swap of the two
factors. -/
theorem amplifyLeft_apply_eq_swap (V : MatrixMap R S) (ρ : Matrix (L × R) (L × R) ℂ) :
    V.amplifyLeft L ρ =
      (V.amplify L (ρ.submatrix Prod.swap Prod.swap)).submatrix Prod.swap Prod.swap := rfl

/-- Reindexing a matrix on a product by the swap of the factors keeps its trace. -/
theorem trace_submatrix_swap [Fintype L] [Fintype R] (X : Matrix (L × R) (L × R) ℂ) :
    (X.submatrix Prod.swap Prod.swap).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Fintype.sum_equiv (Equiv.prodComm R L) _ _ fun _ => rfl

/-- A left amplification of a completely positive map is completely positive. -/
theorem isCP_amplifyLeft [Finite L] {V : MatrixMap R S} (hV : V.IsCP) : (V.amplifyLeft L).IsCP :=
  fun k ρ hρ => by
    have key : (V.amplifyLeft L).amplify (Fin k) ρ =
        (V.amplify (L × Fin k) (ρ.submatrix (fun x : R × (L × Fin k) => ((x.2.1, x.1), x.2.2))
          (fun x : R × (L × Fin k) => ((x.2.1, x.1), x.2.2)))).submatrix
          (fun y : (L × S) × Fin k => (y.1.2, (y.1.1, y.2)))
          (fun y : (L × S) × Fin k => (y.1.2, (y.1.1, y.2))) := rfl
    rw [key]
    exact (hV.amplify_posSemidef (hρ.submatrix _)).submatrix _

/-- The subinstrument `q` on the right factor of `L × N`, with the identity on the
left factor `L`: each branch is the left amplification `id_L ⊗ q_b`. -/
noncomputable def frameLeft (q : SubInstrument N N β) (L : Type) [Fintype L] :
    SubInstrument (L × N) (L × N) β where
  branch b := (q.branch b).amplifyLeft L
  isCP_branch b := isCP_amplifyLeft (q.isCP_branch b)
  trace_le s ρ hρ := by
    have h := (q.frame L).trace_le s (ρ.submatrix Prod.swap Prod.swap) (hρ.submatrix _)
    calc ∑ i ∈ s, ((q.branch i).amplifyLeft L ρ).trace.re
        = ∑ i ∈ s, ((q.frame L).branch i (ρ.submatrix Prod.swap Prod.swap)).trace.re :=
          Finset.sum_congr rfl fun i _ => by
            rw [amplifyLeft_apply_eq_swap, trace_submatrix_swap]; rfl
      _ ≤ (ρ.submatrix Prod.swap Prod.swap).trace.re := h
      _ = ρ.trace.re := by rw [trace_submatrix_swap]

/-- Unfolding lemma: the branches of `frameLeft q L` are the left amplifications of
the branches of `q`. -/
theorem frameLeft_branch [Fintype L] (q : SubInstrument N N β) (b : β) :
    (frameLeft q L).branch b = (q.branch b).amplifyLeft L := rfl

/-- `frameLeft` preserves `pure`. -/
theorem frameLeft_pure [Fintype L] (b : β) :
    frameLeft (SubInstrument.pure b : SubInstrument N N β) L = SubInstrument.pure b := by
  refine DSubInstrument.ext <| funext fun j => ?_
  rw [frameLeft_branch]
  obtain rfl | h := eq_or_ne j b
  · rw [SubInstrument.branch_pure_self, SubInstrument.branch_pure_self,
      MatrixMap.amplifyLeft_id]
  · rw [SubInstrument.branch_pure_of_ne h, SubInstrument.branch_pure_of_ne h,
      MatrixMap.amplifyLeft_zero]

/-- `frameLeft` preserves sequencing. -/
theorem frameLeft_bind [Fintype L] (p : SubInstrument N N α) (k : α → SubInstrument N N β) :
    frameLeft (p.bind k) L = (frameLeft p L).bind fun a => frameLeft (k a) L := by
  refine DSubInstrument.ext <| funext fun c => LinearMap.ext fun ρ => ?_
  rw [frameLeft_branch, SubInstrument.bind, SubInstrument.bind, DSubInstrument.branch_bind_apply]
  ext x y
  rw [MatrixMap.amplifyLeft_apply, DSubInstrument.branch_bind_apply]
  have h₁ : Summable fun i => (k i).branch c
      (p.branch i (ρ.submatrix (fun z => (x.1, z)) fun z => (y.1, z))) :=
    (p.isCPTNIFamily.comp_eval (fun a => (k a).isCPTNIFamily) c).summable_apply _
  have h₂ : Summable fun i => (frameLeft (k i) L).branch c ((frameLeft p L).branch i ρ) :=
    ((frameLeft p L).isCPTNIFamily.comp_eval
      (fun a => (frameLeft (k a) L).isCPTNIFamily) c).summable_apply _
  rw [Matrix.tsum_apply_apply h₁, Matrix.tsum_apply_apply h₂]
  rfl

/-- Pairing the outcome of `X` with a fixed first component `a'`: the branch at
`(a, b)` is the branch of `X` at `b` when `a' = a`, and zero otherwise. -/
theorem branch_bind_pure_pair_left {A : Type} [Fintype A] [DecidableEq α] (X : SubInstrument A A β)
    (a' a : α) (b : β) (σ : Matrix A A ℂ) :
    (X.bind fun b' => SubInstrument.pure (a', b')).branch (a, b) σ =
      if a' = a then X.branch b σ else 0 := by
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply]
  split_ifs with h
  · subst h
    rw [tsum_eq_single b fun b' hb' => by
      rw [SubInstrument.branch_pure_of_ne fun e => hb' (Prod.ext_iff.mp e).2.symm,
        LinearMap.zero_apply]]
    rw [SubInstrument.branch_pure_self, LinearMap.id_apply]
  · exact (tsum_congr fun b' => by
      rw [SubInstrument.branch_pure_of_ne fun e => h (Prod.ext_iff.mp e).1.symm,
        LinearMap.zero_apply]).trans tsum_zero

/-- Pairing the outcome of `X` with a fixed second component `b'`: the branch at
`(a, b)` is the branch of `X` at `a` when `b' = b`, and zero otherwise. -/
theorem branch_bind_pure_pair_right {A : Type} [Fintype A] [DecidableEq β] (X : SubInstrument A A α)
    (b' : β) (a : α) (b : β) (σ : Matrix A A ℂ) :
    (X.bind fun a' => SubInstrument.pure (a', b')).branch (a, b) σ =
      if b' = b then X.branch a σ else 0 := by
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply]
  split_ifs with h
  · subst h
    rw [tsum_eq_single a fun a' ha' => by
      rw [SubInstrument.branch_pure_of_ne fun e => ha' (Prod.ext_iff.mp e).1.symm,
        LinearMap.zero_apply]]
    rw [SubInstrument.branch_pure_self, LinearMap.id_apply]
  · exact (tsum_congr fun a' => by
      rw [SubInstrument.branch_pure_of_ne fun e => h (Prod.ext_iff.mp e).2.symm,
        LinearMap.zero_apply]).trans tsum_zero

/-- Local operations on the two factors commute: running `p` on `M` and then `q` on
`N` is running `q` on `N` and then `p` on `M`, for every joint state, entangled or
not. -/
theorem frame_bind_frameLeft_comm (p : SubInstrument M M α) (q : SubInstrument N N β) :
    (p.frame N).bind (fun a => (frameLeft q M).bind fun b => SubInstrument.pure (a, b)) =
      (frameLeft q M).bind (fun b => (p.frame N).bind fun a => SubInstrument.pure (a, b)) := by
  classical
  refine DSubInstrument.ext <| funext fun ab => LinearMap.ext fun ρ => ?_
  obtain ⟨a, b⟩ := ab
  have hL : ((p.frame N).bind fun a' =>
      (frameLeft q M).bind fun b' => SubInstrument.pure (a', b')).branch (a, b) ρ =
      (frameLeft q M).branch b ((p.frame N).branch a ρ) := by
    rw [SubInstrument.bind, DSubInstrument.branch_bind_apply]
    simp_rw [branch_bind_pure_pair_left]
    exact tsum_ite_eq a _
  have hR : ((frameLeft q M).bind fun b' =>
      (p.frame N).bind fun a' => SubInstrument.pure (a', b')).branch (a, b) ρ =
      (p.frame N).branch a ((frameLeft q M).branch b ρ) := by
    rw [SubInstrument.bind, DSubInstrument.branch_bind_apply]
    simp_rw [branch_bind_pure_pair_right]
    exact tsum_ite_eq b _
  rw [hL, hR]
  exact (LinearMap.congr_fun (MatrixMap.amplify_comp_amplifyLeft (p.branch a) (q.branch b))
    ρ).symm

end TensorData

/-! ## The tensor of quantum open processes -/

section TensorProcess

open _root_.Quantum

variable {Party : Type u} {M N : Type} [Fintype M] [Fintype N]

/-- Placing a subinstrument on `M` as the left factor of `M × N`. -/
noncomputable def frameHom (M N : Type) [Fintype M] [Fintype N] :
    TypeTree.Node.ContextHom (fun X => SubInstrument M M X)
      (fun X => SubInstrument (M × N) (M × N) X) :=
  fun _ p => p.frame N

/-- Placing a subinstrument on `N` as the right factor of `M × N`. -/
noncomputable def frameLeftHom (M N : Type) [Fintype M] [Fintype N] :
    TypeTree.Node.ContextHom (fun X => SubInstrument N N X)
      (fun X => SubInstrument (M × N) (M × N) X) :=
  fun _ q => frameLeft q M

/-- The tensor of a quantum open process `P` on the register `M` and a quantum open
process `Q` on the register `N`: their parallel composition in the quantum open
theory of `M × N`, with `P` acting on the left factor and `Q` on the right factor,
and scheduler `σ`. -/
noncomputable def tensor {Δ₁ Δ₂ : PortBoundary}
    (σ : SubInstrument (M × N) (M × N) (ULift Bool))
    (P : QOpenProcess.{u, v} Party M Δ₁) (Q : QOpenProcess.{u, v} Party N Δ₂) :
    QOpenProcess.{u, v} Party (M × N) (PortBoundary.tensor Δ₁ Δ₂) :=
  (quantumOpenTheory.{u, v} Party (M × N) σ).par (hoist (frameHom M N) P)
    (hoist (frameLeftHom M N) Q)

/-- Sampling a sampler placed on the left factor is placing the sampled path on the
left factor. -/
theorem samplePath_frame (spec : TypeTree.{0}) (S : TypeTree.Sampler (SubInstrument M M) spec) :
    TypeTree.samplePath spec (TypeTree.Decoration.map (frameHom M N) spec S) =
      (TypeTree.samplePath spec S).frame N :=
  samplePath_hoist (frameHom M N) (fun x => SubInstrument.frame_pure N x)
    (fun c f => SubInstrument.frame_bind N c f) spec S

/-- Sampling a sampler placed on the right factor is placing the sampled path on the
right factor. -/
theorem samplePath_frameLeft (spec : TypeTree.{0})
    (S : TypeTree.Sampler (SubInstrument N N) spec) :
    TypeTree.samplePath spec (TypeTree.Decoration.map (frameLeftHom M N) spec S) =
      frameLeft (TypeTree.samplePath spec S) M :=
  samplePath_hoist (frameLeftHom M N) (fun x => frameLeft_pure x)
    (fun c f => frameLeft_bind c f) spec S

/-- **Interchange of the two schedules.** In the tensor of `P` and `Q`, a step of `P`
followed by a step of `Q` and a step of `Q` followed by a step of `P` are the same
quantum operation on the joint register, entangled or not. -/
theorem tensor_step_comm {Δ₁ Δ₂ : PortBoundary}
    (P : QOpenProcess.{u, v} Party M Δ₁) (Q : QOpenProcess.{u, v} Party N Δ₂)
    (s₁ : P.Proc) (s₂ : Q.Proc) :
    (do
      let x ← TypeTree.samplePath _ ((hoist (frameHom M N) P).stepSampler s₁)
      let y ← TypeTree.samplePath _ ((hoist (frameLeftHom M N) Q).stepSampler s₂)
      pure (x, y)) =
    (do
      let y ← TypeTree.samplePath _ ((hoist (frameLeftHom M N) Q).stepSampler s₂)
      let x ← TypeTree.samplePath _ ((hoist (frameHom M N) P).stepSampler s₁)
      pure (x, y) : SubInstrument (M × N) (M × N) _) := by
  simp only [hoist, samplePath_frame, samplePath_frameLeft]
  exact frame_bind_frameLeft_comm _ _

/-- **Interchange of `par` and the tensor.** Placing a parallel composition on the
left factor of `M × N` is the parallel composition of the placed processes. -/
theorem frame_par (σ : SubInstrument M M (ULift Bool)) {Δ₁ Δ₂ : PortBoundary}
    (P₁ : QOpenProcess.{u, v} Party M Δ₁) (P₂ : QOpenProcess.{u, v} Party M Δ₂) :
    hoist (frameHom M N) ((quantumOpenTheory.{u, v} Party M σ).par P₁ P₂) =
      (quantumOpenTheory.{u, v} Party (M × N) (σ.frame N)).par (hoist (frameHom M N) P₁)
        (hoist (frameHom M N) P₂) :=
  hoist_par Party (frameHom M N) σ P₁ P₂

/-- Placing a parallel composition on the right factor of `M × N` is the parallel
composition of the placed processes. -/
theorem frameLeft_par (σ : SubInstrument N N (ULift Bool)) {Δ₁ Δ₂ : PortBoundary}
    (Q₁ : QOpenProcess.{u, v} Party N Δ₁) (Q₂ : QOpenProcess.{u, v} Party N Δ₂) :
    hoist (frameLeftHom M N) ((quantumOpenTheory.{u, v} Party N σ).par Q₁ Q₂) =
      (quantumOpenTheory.{u, v} Party (M × N) (frameLeft σ M)).par
        (hoist (frameLeftHom M N) Q₁) (hoist (frameLeftHom M N) Q₂) :=
  hoist_par Party (frameLeftHom M N) σ Q₁ Q₂

/-- Tracing out the right factor after a sampled path placed on the left factor is
running the sampled path after tracing out. -/
theorem traceRight_samplePath_frame (spec : TypeTree.{0})
    (S : TypeTree.Sampler (SubInstrument M M) spec) (tr : TypeTree.Path spec) :
    MatrixMap.traceRight M N ∘ₗ
        (TypeTree.samplePath spec (TypeTree.Decoration.map (frameHom M N) spec S)).branch tr =
      (TypeTree.samplePath spec S).branch tr ∘ₗ MatrixMap.traceRight M N := by
  rw [samplePath_frame]
  exact MatrixMap.traceRight_comp_amplify _

/-- **Wiring and the partial trace.** Place the wiring of `P₁` and `P₂` on the left
factor of `M × N`; by `hoist_wire` this is the wiring of the placed processes, with
the placed scheduler. Each sampled step of it, followed by the partial trace over
`N`, is the corresponding sampled step of the wiring on `M`, preceded by the partial
trace over `N`. -/
theorem traceRight_wire_frame (σ : SubInstrument M M (ULift Bool)) {Δ₁ Γ Δ₂ : PortBoundary}
    (P₁ : QOpenProcess.{u, v} Party M (PortBoundary.tensor Δ₁ Γ))
    (P₂ : QOpenProcess.{u, v} Party M (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (st : ((quantumOpenTheory.{u, v} Party M σ).wire P₁ P₂).Proc)
    (tr : TypeTree.Path (((quantumOpenTheory.{u, v} Party M σ).wire P₁ P₂).step st).tree) :
    MatrixMap.traceRight M N ∘ₗ (TypeTree.samplePath _
        ((hoist (frameHom M N) ((quantumOpenTheory.{u, v} Party M σ).wire P₁ P₂)).stepSampler
          st)).branch tr =
      (TypeTree.samplePath _
        (((quantumOpenTheory.{u, v} Party M σ).wire P₁ P₂).stepSampler st)).branch tr ∘ₗ
        MatrixMap.traceRight M N :=
  traceRight_samplePath_frame _ _ tr

end TensorProcess

end CatCrypt.Quantum.OpenSystem
