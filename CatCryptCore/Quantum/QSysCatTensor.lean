/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QSysCat
public import CatCryptCore.Quantum.QRealizesMem

/-!
# The tensor of quantum reactive systems on different registers

`QSysCat R` (`CatCryptCore.Quantum.QSysCat`) fixes the register `R`; its monoidal product `⊕`
is the parallel composition on the shared register. This module adds the product of systems on
different registers. The tensor of `S : QRSys M τ E O` and `T : QRSys N υ E' O'` is
`QRSys.parFramed S T : QRSys (M × N) (τ × υ) (E ⊕ E') (O ⊕ O')`: its boundaries are combined by
`⊕`, and an activation addressed to one side runs the step of that side framed by the identity
on the register of the other side (`SubInstrument.frame`, `OpenSystem.frameLeft`).

The tensor is assembled from two functors, `QSysCat.frameR M N : QSysCat M ⥤ QSysCat (M × N)`
and `QSysCat.frameL M N : QSysCat N ⥤ QSysCat (M × N)`, which are the identity on ports and
frame a system by the identity on the other register; `QSysCat.tensor f g` is the `⊕` of their
images. Both functors preserve `⊕` and the trace `loopbackω`: framing a system by the identity
on a register commutes with the unbounded loopback, which is Selinger's condition that
`A ⊗ (−)` is traced (Selinger, *Towards a quantum programming language*, 2004, §6.6). The proof
uses that framing is ω-continuous in Selinger's order (`ReactiveUC.frame_ωSup`).

A register equivalence `e : R ≃ R'` relabels systems along the conjugation `ReactiveUC.relabel`
of subinstruments by the permutation of basis states; this is the functor
`QSysCat.relabel e : QSysCat R ⥤ QSysCat R'`, functorial in `e`.

## Main definitions

* `Quantum.SubInstrument.ωSup_eq_of_tendsto`: a subinstrument whose branches are the limits of
  those of a chain is its supremum.
* `CatCrypt.Quantum.ReactiveUC.QRSys.relabel`: a system relabelled along a register equivalence.
* `CatCrypt.Quantum.ReactiveUC.QSysCat.frameR`, `QSysCat.frameL`: framing as functors.
* `CatCrypt.Quantum.ReactiveUC.QSysCat.relabel`: relabelling as a functor.
* `CatCrypt.Quantum.ReactiveUC.QSysCat.tensor`: the tensor of morphisms on different registers.

## Main results

* `QRSys.frameR_loopbackω`, `QRSys.frameL_loopbackω`: framing commutes with the trace.
* `QRSys.frameR_par`, `QRSys.frameL_par`: framing preserves `⊕`.
* `QRSys.StepMap.parFramed_seq`: interchange of the tensor with the cascade.
* `QRSys.StepMap.parFramed_par`: interchange of the tensor with `⊕`.
* `QRSys.StepMap.parFramed_distrib`: distributivity of the register `M` over `⊕`.
* `QSysCat.tensor_comp`, `QSysCat.tensor_id`, `QSysCat.tensor_tensorHom`,
  `QSysCat.frameR_map_trace`, `QSysCat.frameL_map_trace`, `QSysCat.tensor_distrib`: the same
  statements on morphisms.
* `QSysCat.relabel_refl_map`, `QSysCat.relabel_trans_map`: functoriality in the equivalence.
-/

@[expose] public section

set_option autoImplicit false

namespace Quantum.SubInstrument

open Filter Topology OmegaCompletePartialOrder

variable {A B : Type} [Fintype A] [Fintype B] {α : Type}

/-- A subinstrument whose branches are the pointwise limits of the branches of a chain is the
supremum of the chain. -/
theorem ωSup_eq_of_tendsto (c : Chain (SubInstrument A B α)) (X : SubInstrument A B α)
    (h : ∀ a ρ, Tendsto (fun n => (c n).branch a ρ) atTop (𝓝 (X.branch a ρ))) : ωSup c = X :=
  DSubInstrument.ext <| funext fun a => LinearMap.ext fun ρ =>
    tendsto_nhds_unique (tendsto_branch_ωSup c a ρ) (h a ρ)

end Quantum.SubInstrument

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum OmegaCompletePartialOrder Filter Topology

attribute [local simp] SubInstrument.bind_assoc SubInstrument.pure_bind SubInstrument.fail_bind
  SubInstrument.bind_fail

/-! ## Framing and relabelling are ω-continuous -/

section Continuity

variable {M N : Type} [Fintype M] [Fintype N] {α : Type}

/-- Framing on the right commutes with suprema of chains. -/
theorem frame_ωSup (c : Chain (SubInstrument M M α))
    (c' : Chain (SubInstrument (M × N) (M × N) α)) (hc : ∀ n, c' n = (c n).frame N) :
    ωSup c' = (ωSup c).frame N := by
  refine SubInstrument.ωSup_eq_of_tendsto _ _ fun a ρ => ?_
  have hf : (fun n => (c' n).branch a ρ) = fun n => ((c n).frame N).branch a ρ :=
    funext fun n => by rw [hc]
  rw [hf]
  exact tendsto_pi_nhds.2 fun x => tendsto_pi_nhds.2 fun y =>
    ((SubInstrument.tendsto_branch_ωSup c a _).apply_nhds x.1).apply_nhds y.1

/-- Framing on the left commutes with suprema of chains. -/
theorem frameLeft_ωSup (c : Chain (SubInstrument N N α))
    (c' : Chain (SubInstrument (M × N) (M × N) α)) (hc : ∀ n, c' n = OpenSystem.frameLeft (c n) M) :
    ωSup c' = OpenSystem.frameLeft (ωSup c) M := by
  refine SubInstrument.ωSup_eq_of_tendsto _ _ fun a ρ => ?_
  have hf : (fun n => (c' n).branch a ρ) = fun n => (OpenSystem.frameLeft (c n) M).branch a ρ :=
    funext fun n => by rw [hc]
  rw [hf]
  exact tendsto_pi_nhds.2 fun x => tendsto_pi_nhds.2 fun y =>
    ((SubInstrument.tendsto_branch_ωSup c a _).apply_nhds x.2).apply_nhds y.2

/-- Relabelling commutes with suprema of chains. -/
theorem relabel_ωSup (e : M ≃ N) (c : Chain (SubInstrument M M α))
    (c' : Chain (SubInstrument N N α)) (hc : ∀ n, c' n = relabel e (c n)) :
    ωSup c' = relabel e (ωSup c) := by
  refine SubInstrument.ωSup_eq_of_tendsto _ _ fun a ρ => ?_
  have hf : (fun n => (c' n).branch a ρ) = fun n => (relabel e (c n)).branch a ρ :=
    funext fun n => by rw [hc]
  rw [hf]
  exact tendsto_pi_nhds.2 fun x => tendsto_pi_nhds.2 fun y =>
    ((SubInstrument.tendsto_branch_ωSup c a _).apply_nhds (e.symm x)).apply_nhds (e.symm y)

/-- Framing on the left preserves the failing subinstrument. -/
theorem frameLeft_fail :
    OpenSystem.frameLeft (SubInstrument.fail : SubInstrument N N α) M = SubInstrument.fail :=
  DSubInstrument.ext <| funext fun _ => by
    rw [OpenSystem.frameLeft_branch]
    exact MatrixMap.amplifyLeft_zero

/-- Relabelling preserves the failing subinstrument. -/
theorem relabel_fail (e : M ≃ N) :
    relabel e (SubInstrument.fail : SubInstrument M M α) = SubInstrument.fail :=
  DSubInstrument.ext <| funext fun _ => LinearMap.ext fun _ => by
    ext x y
    rfl

end Continuity

namespace QRSys

variable {R R' R'' : Type} [Fintype R] [Fintype R'] [Fintype R'']
variable {M N : Type} [Fintype M] [Fintype N]
variable {τ υ τ' υ' τ₁ τ₂ υ₁ υ₂ E O P E' O' P' E₁ O₁ E₂ O₂ X : Type}

/-- Two systems with the same initial state and the same steps are equal. -/
theorem ext_step {S T : QRSys R τ E O} (h₁ : S.init = T.init)
    (h₂ : ∀ t e, S.step t e = T.step t e) : S = T := by
  obtain ⟨i, s⟩ := S
  obtain ⟨i', s'⟩ := T
  cases h₁
  congr 1
  funext t e
  exact h₂ t e

/-! ## Framing preserves the structure of `QSysCat` -/

/-- Framing on the right preserves stateless systems. -/
theorem frameR_ofFun (f : E → O) : (ofFun f : QRSys M Unit E O).frameR N = ofFun f :=
  ext_step rfl fun _ _ => SubInstrument.frame_pure N _

/-- Framing on the left preserves stateless systems. -/
theorem frameL_ofFun (f : E → O) : (ofFun f : QRSys N Unit E O).frameL M = ofFun f :=
  ext_step rfl fun _ _ => OpenSystem.frameLeft_pure _

/-- Framing on the right preserves the parallel composition. -/
theorem frameR_par (S : QRSys M τ E O) (T : QRSys M υ E' O') :
    (S.par T).frameR N = (S.frameR N).par (T.frameR N) := by
  refine ext_step rfl fun s e => ?_
  rcases e with e | e <;>
    simp only [frameR, par_step_inl, par_step_inr, SubInstrument.frame_bind,
      SubInstrument.frame_pure]

/-- Framing on the left preserves the parallel composition. -/
theorem frameL_par (S : QRSys N τ E O) (T : QRSys N υ E' O') :
    (S.par T).frameL M = (S.frameL M).par (T.frameL M) := by
  refine ext_step rfl fun s e => ?_
  rcases e with e | e <;>
    simp only [frameL, par_step_inl, par_step_inr, OpenSystem.frameLeft_bind,
      OpenSystem.frameLeft_pure]

/-! ## Framing commutes with the trace -/

/-- The activations failing on exhausted fuel of a system framed on the right are the framed
activations. -/
theorem fbRunFail_frameR (S : QRSys M τ (E ⊕ X) (O ⊕ X)) :
    ∀ (n : ℕ) (g : E ⊕ X) (t : τ),
      (S.frameR N).fbRunFail n g t = (S.fbRunFail n g t).frame N := by
  intro n
  induction n with
  | zero =>
    intro g t
    simp only [fbRunFail, frameR, SubInstrument.frame_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp
    · simp
  | succ n ih =>
    intro g t
    simp only [fbRunFail, frameR, SubInstrument.frame_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp
    · exact ih (.inr x) t'

/-- The activations failing on exhausted fuel of a system framed on the left are the framed
activations. -/
theorem fbRunFail_frameL (S : QRSys N τ (E ⊕ X) (O ⊕ X)) :
    ∀ (n : ℕ) (g : E ⊕ X) (t : τ),
      (S.frameL M).fbRunFail n g t = OpenSystem.frameLeft (S.fbRunFail n g t) M := by
  intro n
  induction n with
  | zero =>
    intro g t
    simp only [fbRunFail, frameL, OpenSystem.frameLeft_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp [OpenSystem.frameLeft_pure]
    · simp [frameLeft_fail]
  | succ n ih =>
    intro g t
    simp only [fbRunFail, frameL, OpenSystem.frameLeft_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp [OpenSystem.frameLeft_pure]
    · exact ih (.inr x) t'

/-- **Framing on the right is traced.** The unbounded loopback of `S` framed by the identity on
`N` is the framed unbounded loopback of `S`. -/
theorem frameR_loopbackω (S : QRSys M τ (E ⊕ X) (O ⊕ X)) :
    (S.frameR N).loopbackω = S.loopbackω.frameR N :=
  ext_step rfl fun t e => frame_ωSup _ _ fun n => fbRunFail_frameR S n (.inl e) t

/-- **Framing on the left is traced.** The unbounded loopback of `S` framed by the identity on
`M` is the framed unbounded loopback of `S`. -/
theorem frameL_loopbackω (S : QRSys N τ (E ⊕ X) (O ⊕ X)) :
    (S.frameL M).loopbackω = S.loopbackω.frameL M :=
  ext_step rfl fun t e => frameLeft_ωSup _ _ fun n => fbRunFail_frameL S n (.inl e) t

/-! ## Relabelling along a register equivalence -/

/-- The system `S` on the register `R` relabelled along `e : R ≃ R'`: each step is conjugated
by the permutation of basis states `e`. -/
noncomputable def relabel (e : R ≃ R') (S : QRSys R τ E O) : QRSys R' τ E O where
  init := S.init
  step t ev := ReactiveUC.relabel e (S.step t ev)

/-- Unfolding lemma of `relabel`: a step. -/
theorem relabel_step (e : R ≃ R') (S : QRSys R τ E O) (t : τ) (ev : E) :
    (S.relabel e).step t ev = ReactiveUC.relabel e (S.step t ev) :=
  rfl

/-- Relabelling preserves stateless systems. -/
theorem relabel_ofFun (e : R ≃ R') (f : E → O) : (ofFun f : QRSys R Unit E O).relabel e = ofFun f :=
  ext_step rfl fun _ _ => ReactiveUC.relabel_pure e _

/-- Relabelling commutes with the cascade. -/
theorem relabel_seq (e : R ≃ R') (S : QRSys R τ E O) (T : QRSys R υ O P) :
    (S.seq T).relabel e = (S.relabel e).seq (T.relabel e) :=
  ext_step rfl fun _ _ => by
    simp only [relabel_step, seq_step, ReactiveUC.relabel_bind, ReactiveUC.relabel_pure]

/-- Relabelling preserves the parallel composition. -/
theorem relabel_par (e : R ≃ R') (S : QRSys R τ E O) (T : QRSys R υ E' O') :
    (S.par T).relabel e = (S.relabel e).par (T.relabel e) := by
  refine ext_step rfl fun s ev => ?_
  rcases ev with ev | ev <;>
    simp only [relabel_step, par_step_inl, par_step_inr, ReactiveUC.relabel_bind,
      ReactiveUC.relabel_pure]

/-- Relabelling along the identity is the identity. -/
theorem relabel_refl (S : QRSys R τ E O) : S.relabel (Equiv.refl R) = S :=
  ext_step rfl fun _ _ => ReactiveUC.relabel_refl _

/-- Relabelling twice is relabelling along the composite equivalence. -/
theorem relabel_relabel (e : R ≃ R') (e' : R' ≃ R'') (S : QRSys R τ E O) :
    (S.relabel e).relabel e' = S.relabel (e.trans e') :=
  ext_step rfl fun _ _ => ReactiveUC.relabel_relabel e e' _

/-- A step map gives a step map of the relabelled systems. -/
theorem StepMap.relabel (e : R ≃ R') {S : QRSys R τ E O} {S' : QRSys R τ' E O} {f : τ → τ'}
    (h : StepMap S S' f) : StepMap (S.relabel e) (S'.relabel e) f where
  init_map := h.init_map
  step t ev := by
    simp only [relabel_step, ← h.step, ReactiveUC.relabel_bind, ReactiveUC.relabel_pure]

/-- The activations failing on exhausted fuel of a relabelled system are the relabelled
activations. -/
theorem fbRunFail_relabel (e : R ≃ R') (S : QRSys R τ (E ⊕ X) (O ⊕ X)) :
    ∀ (n : ℕ) (g : E ⊕ X) (t : τ),
      (S.relabel e).fbRunFail n g t = ReactiveUC.relabel e (S.fbRunFail n g t) := by
  intro n
  induction n with
  | zero =>
    intro g t
    simp only [fbRunFail, relabel_step, ReactiveUC.relabel_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp [ReactiveUC.relabel_pure]
    · simp [relabel_fail]
  | succ n ih =>
    intro g t
    simp only [fbRunFail, relabel_step, ReactiveUC.relabel_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp [ReactiveUC.relabel_pure]
    · simpa using ih (.inr x) t'

/-- **Relabelling is traced.** The unbounded loopback of a relabelled system is the relabelled
unbounded loopback. -/
theorem relabel_loopbackω (e : R ≃ R') (S : QRSys R τ (E ⊕ X) (O ⊕ X)) :
    (S.relabel e).loopbackω = S.loopbackω.relabel e :=
  ext_step rfl fun t ev => relabel_ωSup e _ _ fun n => fbRunFail_relabel e S n (.inl ev) t

/-! ## Interchange laws of the tensor -/

/-- **Interchange with the cascade.** The tensor of two cascades is the cascade of the tensors;
the state map exchanges the middle components. -/
theorem StepMap.parFramed_seq (S : QRSys M τ E O) (T : QRSys M υ O P) (S' : QRSys N τ' E' O')
    (T' : QRSys N υ' O' P') :
    StepMap ((S.seq T).parFramed (S'.seq T')) ((S.parFramed S').seq (T.parFramed T'))
      (fun s => ((s.1.1, s.2.1), (s.1.2, s.2.2))) := by
  rw [parFramed, frameR_seq, frameL_seq]
  exact StepMap.seq_par _ _ _ _

/-- **Interchange with `⊕`.** The tensor of two parallel compositions is the parallel
composition of the tensors, on ports exchanged by `Equiv.sumSumSumComm`. -/
theorem StepMap.parFramed_par (S₁ : QRSys M τ₁ E₁ O₁) (S₂ : QRSys M τ₂ E₂ O₂)
    (T₁ : QRSys N υ₁ E O) (T₂ : QRSys N υ₂ E' O') :
    StepMap (((S₁.par S₂).parFramed (T₁.par T₂)).seq (ofFun (Equiv.sumSumSumComm O₁ O₂ O O')))
      ((ofFun (Equiv.sumSumSumComm E₁ E₂ E E')).seq ((S₁.parFramed T₁).par (S₂.parFramed T₂)))
      (fun s => ((), ((s.1.1.1, s.1.2.1), (s.1.1.2, s.1.2.2)))) :=
  ⟨rfl, fun s ev => by
    rcases ev with (ev | ev) | (ev | ev) <;>
      simp [seq_step, parFramed, frameR_par, frameL_par]⟩

/-- The equivalence of ports `∅ ⊕ (B ⊕ C) ≃ (∅ ⊕ B) ⊕ (∅ ⊕ C)` of the distributivity of a
register over `⊕`. -/
def distribEmpty (B C : Type) : Empty ⊕ (B ⊕ C) ≃ (Empty ⊕ B) ⊕ (Empty ⊕ C) :=
  (Equiv.emptySum Empty (B ⊕ C)).trans
    (Equiv.sumCongr (Equiv.emptySum Empty B).symm (Equiv.emptySum Empty C).symm)

/-- **Distributivity.** The register `M`, as the stateless system on `M` without ports, tensored
with a parallel composition is the parallel composition of the tensors, on ports related by
`distribEmpty`. -/
theorem StepMap.parFramed_distrib (T₁ : QRSys N υ₁ E₁ O₁) (T₂ : QRSys N υ₂ E₂ O₂) :
    StepMap (((ofFun (id : Empty → Empty) : QRSys M Unit Empty Empty).parFramed (T₁.par T₂)).seq
        (ofFun (distribEmpty O₁ O₂)))
      ((ofFun (distribEmpty E₁ E₂)).seq
        (((ofFun (id : Empty → Empty) : QRSys M Unit Empty Empty).parFramed T₁).par
          ((ofFun (id : Empty → Empty) : QRSys M Unit Empty Empty).parFramed T₂)))
      (fun s => ((), ((s.1.1, s.1.2.1), (s.1.1, s.1.2.2)))) :=
  ⟨rfl, fun s ev => by
    rcases ev with ev | ev | ev
    · exact ev.elim
    · simp [seq_step, parFramed, frameL_par, distribEmpty]
    · simp [seq_step, parFramed, frameL_par, distribEmpty]⟩

/-! ## Bundled systems -/

/-- A bundled system framed on the right. -/
noncomputable def Obj.frameR (A : Obj M E O) (N : Type) [Fintype N] : Obj (M × N) E O :=
  ⟨A.St, A.sys.frameR N⟩

/-- A bundled system framed on the left. -/
noncomputable def Obj.frameL (A : Obj N E O) (M : Type) [Fintype M] : Obj (M × N) E O :=
  ⟨A.St, A.sys.frameL M⟩

/-- A bundled system relabelled along a register equivalence. -/
noncomputable def Obj.relabel (e : R ≃ R') (A : Obj R E O) : Obj R' E O :=
  ⟨A.St, A.sys.relabel e⟩

/-- Step equivalence is a congruence for framing on the right. -/
theorem StepEq.frameR {A A' : Obj M E O} (h : StepEq A A') :
    StepEq (A.frameR N) (A'.frameR N) :=
  StepEq.map (fun A => A.frameR N) (fun _ _ ⟨_, h⟩ => ⟨_, h.frameR⟩) h

/-- Step equivalence is a congruence for framing on the left. -/
theorem StepEq.frameL {A A' : Obj N E O} (h : StepEq A A') :
    StepEq (A.frameL M) (A'.frameL M) :=
  StepEq.map (fun A => A.frameL M) (fun _ _ ⟨_, h⟩ => ⟨_, h.frameL⟩) h

/-- Step equivalence is a congruence for relabelling. -/
theorem StepEq.relabel (e : R ≃ R') {A A' : Obj R E O} (h : StepEq A A') :
    StepEq (A.relabel e) (A'.relabel e) :=
  StepEq.map (fun A => A.relabel e) (fun _ _ ⟨_, h⟩ => ⟨_, h.relabel e⟩) h

end QRSys

/-! ## The functors and the tensor of morphisms -/

namespace QSysCat

open CategoryTheory MonoidalCategory

variable {R R' R'' : Type} [Fintype R] [Fintype R'] [Fintype R'']

/-- Framing by the identity on the register `N`: the functor `QSysCat M ⥤ QSysCat (M × N)`, the
identity on ports. -/
noncomputable def frameR (M N : Type) [Fintype M] [Fintype N] : QSysCat M ⥤ QSysCat (M × N) where
  obj X := ⟨X.P⟩
  map {X Y} f := Quotient.map (fun A : QRSys.Obj M X.P Y.P => A.frameR N)
    (fun _ _ h => QRSys.StepEq.frameR h) f
  map_id X := congrArg (fun S => (⟦⟨Unit, S⟩⟧ : (⟨X.P⟩ : QSysCat (M × N)) ⟶ ⟨X.P⟩))
    (QRSys.frameR_ofFun id)
  map_comp := by
    rintro _ _ _ ⟨A⟩ ⟨B⟩
    exact congrArg (fun S => (⟦⟨A.St × B.St, S⟩⟧ : (⟨_⟩ : QSysCat (M × N)) ⟶ ⟨_⟩))
      (QRSys.frameR_seq A.sys B.sys)

/-- Framing by the identity on the register `M`: the functor `QSysCat N ⥤ QSysCat (M × N)`, the
identity on ports. -/
noncomputable def frameL (M N : Type) [Fintype M] [Fintype N] : QSysCat N ⥤ QSysCat (M × N) where
  obj X := ⟨X.P⟩
  map {X Y} f := Quotient.map (fun A : QRSys.Obj N X.P Y.P => A.frameL M)
    (fun _ _ h => QRSys.StepEq.frameL h) f
  map_id X := congrArg (fun S => (⟦⟨Unit, S⟩⟧ : (⟨X.P⟩ : QSysCat (M × N)) ⟶ ⟨X.P⟩))
    (QRSys.frameL_ofFun id)
  map_comp := by
    rintro _ _ _ ⟨A⟩ ⟨B⟩
    exact congrArg (fun S => (⟦⟨A.St × B.St, S⟩⟧ : (⟨_⟩ : QSysCat (M × N)) ⟶ ⟨_⟩))
      (QRSys.frameL_seq A.sys B.sys)

/-- Relabelling along the register equivalence `e`: the functor `QSysCat R ⥤ QSysCat R'`, the
identity on ports. -/
noncomputable def relabel (e : R ≃ R') : QSysCat R ⥤ QSysCat R' where
  obj X := ⟨X.P⟩
  map {X Y} f := Quotient.map (fun A : QRSys.Obj R X.P Y.P => A.relabel e)
    (fun _ _ h => QRSys.StepEq.relabel e h) f
  map_id X := congrArg (fun S => (⟦⟨Unit, S⟩⟧ : (⟨X.P⟩ : QSysCat R') ⟶ ⟨X.P⟩))
    (QRSys.relabel_ofFun e id)
  map_comp := by
    rintro _ _ _ ⟨A⟩ ⟨B⟩
    exact congrArg (fun S => (⟦⟨A.St × B.St, S⟩⟧ : (⟨_⟩ : QSysCat R') ⟶ ⟨_⟩))
      (QRSys.relabel_seq e A.sys B.sys)

/-- Relabelling along the identity equivalence is the identity on morphisms. -/
theorem relabel_refl_map {X Y : QSysCat R} (f : X ⟶ Y) : (relabel (Equiv.refl R)).map f = f := by
  induction f using Quotient.inductionOn with
  | h A => exact congrArg (fun S => (⟦⟨A.St, S⟩⟧ : X ⟶ Y)) (QRSys.relabel_refl A.sys)

/-- Relabelling along a composite equivalence is relabelling along each in turn. -/
theorem relabel_trans_map (e : R ≃ R') (e' : R' ≃ R'') {X Y : QSysCat R} (f : X ⟶ Y) :
    (relabel (e.trans e')).map f = (relabel e').map ((relabel e).map f) := by
  induction f using Quotient.inductionOn with
  | h A =>
    exact congrArg (fun S => (⟦⟨A.St, S⟩⟧ : (⟨X.P⟩ : QSysCat R'') ⟶ ⟨Y.P⟩))
      (QRSys.relabel_relabel e e' A.sys).symm

/-- Relabelling preserves `⊕` of morphisms. -/
theorem relabel_map_tensorHom (e : R ≃ R') {X₁ Y₁ X₂ Y₂ : QSysCat R} (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (relabel e).map (tensorHom f g) = tensorHom ((relabel e).map f) ((relabel e).map g) := by
  induction f using Quotient.inductionOn with
  | h A =>
    induction g using Quotient.inductionOn with
    | h B =>
      exact congrArg (fun S => (⟦⟨A.St × B.St, S⟩⟧ :
        (⟨X₁.P ⊕ X₂.P⟩ : QSysCat R') ⟶ ⟨Y₁.P ⊕ Y₂.P⟩)) (QRSys.relabel_par e A.sys B.sys)

/-- Relabelling preserves the trace. -/
theorem relabel_map_trace (e : R ≃ R') (U : QSysCat R) {X Y : QSysCat R} (f : X ⊗ U ⟶ Y ⊗ U) :
    (relabel e).map (trace U f) =
      trace (X := (relabel e).obj X) (Y := (relabel e).obj Y) ((relabel e).obj U)
        ((relabel e).map f) := by
  induction f using Quotient.inductionOn with
  | h A =>
    exact congrArg (fun S => (⟦⟨A.St, S⟩⟧ : (⟨X.P⟩ : QSysCat R') ⟶ ⟨Y.P⟩))
      (QRSys.relabel_loopbackω e A.sys).symm

section Tensor

variable {M N : Type} [Fintype M] [Fintype N]

/-- Framing on the right preserves `⊕` of morphisms. -/
theorem frameR_map_tensorHom {X₁ Y₁ X₂ Y₂ : QSysCat M} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (frameR M N).map (tensorHom f g) =
      tensorHom ((frameR M N).map f) ((frameR M N).map g) := by
  induction f using Quotient.inductionOn with
  | h A =>
    induction g using Quotient.inductionOn with
    | h B =>
      exact congrArg (fun S => (⟦⟨A.St × B.St, S⟩⟧ :
        (⟨X₁.P ⊕ X₂.P⟩ : QSysCat (M × N)) ⟶ ⟨Y₁.P ⊕ Y₂.P⟩)) (QRSys.frameR_par A.sys B.sys)

/-- Framing on the left preserves `⊕` of morphisms. -/
theorem frameL_map_tensorHom {X₁ Y₁ X₂ Y₂ : QSysCat N} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (frameL M N).map (tensorHom f g) =
      tensorHom ((frameL M N).map f) ((frameL M N).map g) := by
  induction f using Quotient.inductionOn with
  | h A =>
    induction g using Quotient.inductionOn with
    | h B =>
      exact congrArg (fun S => (⟦⟨A.St × B.St, S⟩⟧ :
        (⟨X₁.P ⊕ X₂.P⟩ : QSysCat (M × N)) ⟶ ⟨Y₁.P ⊕ Y₂.P⟩)) (QRSys.frameL_par A.sys B.sys)

/-- **Framing on the right is traced** (Selinger's condition that `A ⊗ (−)` is traced). -/
theorem frameR_map_trace (U : QSysCat M) {X Y : QSysCat M} (f : X ⊗ U ⟶ Y ⊗ U) :
    (frameR M N).map (trace U f) =
      trace (X := (frameR M N).obj X) (Y := (frameR M N).obj Y) ((frameR M N).obj U)
        ((frameR M N).map f) := by
  induction f using Quotient.inductionOn with
  | h A =>
    exact congrArg (fun S => (⟦⟨A.St, S⟩⟧ : (⟨X.P⟩ : QSysCat (M × N)) ⟶ ⟨Y.P⟩))
      (QRSys.frameR_loopbackω A.sys).symm

/-- **Framing on the left is traced** (Selinger's condition that `(−) ⊗ A` is traced). -/
theorem frameL_map_trace (U : QSysCat N) {X Y : QSysCat N} (f : X ⊗ U ⟶ Y ⊗ U) :
    (frameL M N).map (trace U f) =
      trace (X := (frameL M N).obj X) (Y := (frameL M N).obj Y) ((frameL M N).obj U)
        ((frameL M N).map f) := by
  induction f using Quotient.inductionOn with
  | h A =>
    exact congrArg (fun S => (⟦⟨A.St, S⟩⟧ : (⟨X.P⟩ : QSysCat (M × N)) ⟶ ⟨Y.P⟩))
      (QRSys.frameL_loopbackω A.sys).symm

/-- The tensor of a morphism `f` on the register `M` and a morphism `g` on the register `N`: the
`⊕` in `QSysCat (M × N)` of `f` framed on the right and `g` framed on the left. -/
noncomputable def tensor {X₁ Y₁ : QSysCat M} {X₂ Y₂ : QSysCat N} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (⟨X₁.P ⊕ X₂.P⟩ : QSysCat (M × N)) ⟶ ⟨Y₁.P ⊕ Y₂.P⟩ :=
  tensorHom ((frameR M N).map f) ((frameL M N).map g)

/-- Unfolding lemma of `tensor` on classes of systems: the class of `QRSys.parFramed`. -/
theorem tensor_mk {X₁ Y₁ : QSysCat M} {X₂ Y₂ : QSysCat N} (A : QRSys.Obj M X₁.P Y₁.P)
    (B : QRSys.Obj N X₂.P Y₂.P) :
    tensor (⟦A⟧ : X₁ ⟶ Y₁) (⟦B⟧ : X₂ ⟶ Y₂) = ⟦⟨A.St × B.St, A.sys.parFramed B.sys⟩⟧ :=
  rfl

/-- **Interchange with the cascade.** -/
theorem tensor_comp {X₁ Y₁ Z₁ : QSysCat M} {X₂ Y₂ Z₂ : QSysCat N} (f₁ : X₁ ⟶ Y₁) (g₁ : Y₁ ⟶ Z₁)
    (f₂ : X₂ ⟶ Y₂) (g₂ : Y₂ ⟶ Z₂) :
    tensor (f₁ ≫ g₁) (f₂ ≫ g₂) = tensor f₁ f₂ ≫ tensor g₁ g₂ := by
  simp only [tensor, Functor.map_comp]
  exact (tensorHom_comp _ _ _ _).symm

/-- The tensor of identities is the identity. -/
theorem tensor_id (X₁ : QSysCat M) (X₂ : QSysCat N) :
    tensor (𝟙 X₁) (𝟙 X₂) = 𝟙 (⟨X₁.P ⊕ X₂.P⟩ : QSysCat (M × N)) := by
  change tensorHom ((frameR M N).map (𝟙 X₁)) ((frameL M N).map (𝟙 X₂)) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  change tensorHom (homOfFun id) (homOfFun id) = homOfFun id
  rw [homOfFun_tensorHom, Sum.map_id_id]

/-- **Interchange with `⊕`.** The tensor of two `⊕`s is the `⊕` of the tensors, on ports
exchanged by `Equiv.sumSumSumComm`. -/
theorem tensor_tensorHom {X₁ Y₁ X₂ Y₂ : QSysCat M} {X₃ Y₃ X₄ Y₄ : QSysCat N} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (g₁ : X₃ ⟶ Y₃) (g₂ : X₄ ⟶ Y₄) :
    tensor (tensorHom f₁ f₂) (tensorHom g₁ g₂) ≫
        homOfFun (Y := ⟨(Y₁.P ⊕ Y₃.P) ⊕ (Y₂.P ⊕ Y₄.P)⟩)
          (Equiv.sumSumSumComm Y₁.P Y₂.P Y₃.P Y₄.P) =
      homOfFun (X := ⟨(X₁.P ⊕ X₂.P) ⊕ (X₃.P ⊕ X₄.P)⟩)
          (Y := ⟨(X₁.P ⊕ X₃.P) ⊕ (X₂.P ⊕ X₄.P)⟩) (Equiv.sumSumSumComm X₁.P X₂.P X₃.P X₄.P) ≫
        tensorHom (X₁ := ⟨X₁.P ⊕ X₃.P⟩) (Y₁ := ⟨Y₁.P ⊕ Y₃.P⟩) (X₂ := ⟨X₂.P ⊕ X₄.P⟩)
          (Y₂ := ⟨Y₂.P ⊕ Y₄.P⟩) (tensor f₁ g₁) (tensor f₂ g₂) := by
  induction f₁ using Quotient.inductionOn with | h A₁ =>
  induction f₂ using Quotient.inductionOn with | h A₂ =>
  induction g₁ using Quotient.inductionOn with | h B₁ =>
  induction g₂ using Quotient.inductionOn with | h B₂ =>
  exact Quotient.sound (QRSys.StepMap.parFramed_par A₁.sys A₂.sys B₁.sys B₂.sys).stepEq

/-- The tensor with a trace on the left is the `⊕` of the framed trace and the framed second
morphism. -/
theorem tensor_trace_left (U : QSysCat M) {X Y : QSysCat M} {X₂ Y₂ : QSysCat N}
    (f : X ⊗ U ⟶ Y ⊗ U) (g : X₂ ⟶ Y₂) :
    tensor (trace U f) g =
      tensorHom (trace (X := (frameR M N).obj X) (Y := (frameR M N).obj Y) ((frameR M N).obj U)
        ((frameR M N).map f)) ((frameL M N).map g) := by
  rw [tensor, frameR_map_trace]

/-- **Distributivity.** For the register object `⟨Empty⟩` of `QSysCat M`, tensoring commutes
with `⊕` up to the port isomorphism `distribEmpty`. -/
theorem tensor_distrib {X₁ Y₁ X₂ Y₂ : QSysCat N} (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂) :
    tensor (𝟙 (⟨Empty⟩ : QSysCat M)) (tensorHom g₁ g₂) ≫
        homOfFun (Y := ⟨(Empty ⊕ Y₁.P) ⊕ (Empty ⊕ Y₂.P)⟩) (QRSys.distribEmpty Y₁.P Y₂.P) =
      homOfFun (X := ⟨Empty ⊕ (X₁.P ⊕ X₂.P)⟩) (Y := ⟨(Empty ⊕ X₁.P) ⊕ (Empty ⊕ X₂.P)⟩)
          (QRSys.distribEmpty X₁.P X₂.P) ≫
        tensorHom (X₁ := ⟨Empty ⊕ X₁.P⟩) (Y₁ := ⟨Empty ⊕ Y₁.P⟩) (X₂ := ⟨Empty ⊕ X₂.P⟩)
          (Y₂ := ⟨Empty ⊕ Y₂.P⟩) (tensor (𝟙 (⟨Empty⟩ : QSysCat M)) g₁)
          (tensor (𝟙 (⟨Empty⟩ : QSysCat M)) g₂) := by
  induction g₁ using Quotient.inductionOn with | h B₁ =>
  induction g₂ using Quotient.inductionOn with | h B₂ =>
  exact Quotient.sound (QRSys.StepMap.parFramed_distrib (M := M) B₁.sys B₂.sys).stepEq

end Tensor

end QSysCat

end CatCrypt.Quantum.ReactiveUC
