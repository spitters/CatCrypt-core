/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QSysCat
public import CatCryptCore.Quantum.ClassicalDiamondLift
public import CatCryptCore.Quantum.ClassicalEmbedGame
public import CatCryptCore.Crypto.UCLoopbackTraced
public import CatCryptCore.Crypto.Party.Prog

/-!
# The classical lift of reactive systems to quantum reactive systems

A sub-distribution `μ` on `α` is the diagonal subinstrument `SubInstrument.ofSDistr μ` on any
register `R`: its branch at `a` is the identity scaled by `μ(a)`. On `R = Fin d` it is the
embedding `classicalEmbed` of `CatCryptCore.Quantum.ClassicalEmbed` (`ofSDistr_eq_mk'`). The
lift preserves `pure`, `bind` and failure, is monotone for Selinger's order and sends the
supremum of a chain of sub-distributions to the supremum of the lifted chain.

A classical computation `c : SPComp α` is lifted through its run from the empty heap with the
final heap discarded (`heapFree c`). For a heap-independent computation (`SPComp.IsPure`) this
is the sub-distribution that the computation samples, and `heapFree` sends `bind` to `bind`.

The lift `liftSys S` of a classical reactive system `S : UCTransparent.Sys τ E O` is the quantum
reactive system on the register `R` with the same classical state whose step is the lift of
the classical step. It sends parallel composition to parallel composition and the forwarding
system to the forwarding system; for systems whose steps are heap-independent
(`Sys.HeapPure`) it sends the cascade to the cascade and the unbounded loopback to the
unbounded loopback. Step equivalence of classical systems, which allows an invariant on the
states, gives step equivalence of the lifts through the restriction of the lift to the
invariant (`stepEq_liftObj`).

The classical cascade shares the heap between its two systems, while the quantum cascade of
two lifts runs each on its own empty heap, so the cascade is preserved only for
heap-independent systems. The functor `liftFunctor : PSysCat ⥤ QSysCat R` is therefore defined
on `PSysCat`, the port types with heap-independent systems modulo classical step equivalence;
`PSysCat.toSysCat` is its inclusion in `SysCat`.

A party program `p : Party.Prog E O α` is lifted by `toQSys p = liftSys (toSys p)`. Its
quantum interpreter `qAct` runs each sample as the diagonal subinstrument of its
sub-distribution; on programs whose samples are heap-independent (`SamplesPure`) it is the step
of `toQSys p` (`qAct_eq_toQSys_step`).

## Transport of realizations

A classical realization at distance `0` lifts to equal quantum views against environments of
the classical-lift form (`qview_liftQSys_eq_of_realizes`), and hence to a quantum realization
at distance `0` against those environments. Transport at a positive distance needs more: a
statistical bound against quantum environments holds for classical protocols in Unruh's
quantum UC model (Unruh, Eurocrypt 2010), whose environments may keep quantum side
information, and a computational bound needs post-quantum reductions, whose adversaries are
quantum.

## Main definitions

* `Quantum.SubInstrument.ofSDistr`: a sub-distribution as a diagonal subinstrument.
* `ClassicalLiftSys.heapFree`, `ClassicalLiftSys.liftSys`, `Sys.HeapPure`.
* `ClassicalLiftSys.PSysCat`, `ClassicalLiftSys.liftFunctor`.
* `ClassicalLiftSys.toQSys`, `ClassicalLiftSys.qAct`, `ClassicalLiftSys.SamplesPure`.
* `ClassicalLiftSys.liftQSys`, `ClassicalLiftSys.liftStrat`.

## Main results

* `ofSDistr_pure`, `ofSDistr_fail`, `ofSDistr_bind`, `ofSDistr_mono`, `ofSDistr_ωSup`.
* `liftSys_ofFun`, `liftSys_par`, `liftSys_seq`, `liftSys_loopbackω`.
* `stepEq_liftObj`: classical step equivalence gives quantum step equivalence of the lifts.
* `liftFunctor_map_tensor`, `liftFunctor_map_trace`: the functor preserves `⊕` and the trace.
* `qAct_eq_toQSys_step`: the quantum interpreter of a party program is its lift.
* `qview_liftQSys_eq_of_realizes`: transport of a realization at distance `0`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Prob OmegaCompletePartialOrder
open scoped ENNReal ComplexOrder

namespace Quantum.SubInstrument

/-- The identity scaled by a nonnegative real is completely positive. -/
theorem isCP_ofReal_smul_id {R : Type} [Finite R] (r : ℝ) (hr : 0 ≤ r) :
    MatrixMap.IsCP (((r : ℂ)) • (LinearMap.id : MatrixMap R R)) := by
  classical
  have := Fintype.ofFinite R
  have h : ((r : ℂ)) • (LinearMap.id : MatrixMap R R) =
      MatrixMap.conj (((Real.sqrt r : ℝ) : ℂ) • (1 : Matrix R R ℂ)) := by
    ext ρ : 1
    simp [MatrixMap.conj_apply, smul_smul, Real.mul_self_sqrt hr]
  rw [h]
  exact MatrixMap.isCP_conj _

variable {R : Type} [Fintype R] {α β : Type}

/-- The weights of a sub-distribution over a finite set of values sum to at most `1`. -/
theorem sum_toReal_some_le_one (μ : SDistr α) (s : Finset α) :
    ∑ a ∈ s, (μ (some a)).toReal ≤ 1 := by
  rw [← ENNReal.toReal_sum fun a _ => PMF.apply_ne_top μ _]
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  calc ∑ a ∈ s, μ (some a) ≤ ∑' a, μ (some a) := ENNReal.sum_le_tsum s
    _ ≤ ∑' o, μ o := ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective α) μ
    _ = 1 := μ.tsum_coe

/-- The diagonal subinstrument of the sub-distribution `μ` on the register `R`: the branch at
`a` is the identity scaled by `μ(a)`. -/
noncomputable def ofSDistr (μ : SDistr α) : SubInstrument R R α where
  branch a := (((μ (some a)).toReal : ℂ)) • LinearMap.id
  isCP_branch a := isCP_ofReal_smul_id _ ENNReal.toReal_nonneg
  trace_le s ρ hρ := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Matrix.trace_smul, smul_eq_mul,
      Complex.re_ofReal_mul]
    rw [← Finset.sum_mul]
    exact mul_le_of_le_one_left (Complex.nonneg_iff.mp hρ.trace_nonneg).1
      (sum_toReal_some_le_one μ s)

/-- Unfolding lemma of `ofSDistr`: a branch. -/
@[simp] theorem ofSDistr_branch (μ : SDistr α) (a : α) :
    (ofSDistr μ : SubInstrument R R α).branch a = (((μ (some a)).toReal : ℂ)) • LinearMap.id :=
  rfl

/-- The lift of a point mass is `pure`. -/
theorem ofSDistr_pure (a : α) :
    (ofSDistr (SDistr.pure a) : SubInstrument R R α) = SubInstrument.pure a := by
  classical
  refine DSubInstrument.ext (funext fun a' => ?_)
  by_cases h : a' = a
  · subst h
    simp [SDistr.pure_apply_some]
  · simp [SDistr.pure_apply_some, Ne.symm h, SubInstrument.branch_pure_of_ne h]

/-- The lift of failure is failure. -/
theorem ofSDistr_fail :
    (ofSDistr (SDistr.fail : SDistr α) : SubInstrument R R α) = SubInstrument.fail := by
  refine DSubInstrument.ext (funext fun a => ?_)
  simp [SDistr.fail_apply_some]

/-- The weight of a value under `bind` sums over the values of the first sub-distribution. -/
theorem _root_.CatCrypt.Prob.SDistr.bind_apply_some' (μ : SDistr α) (f : α → SDistr β) (b : β) :
    (μ.bind f) (some b) = ∑' a, μ (some a) * f a (some b) := by
  simp only [SDistr.bind, PMF.bind_apply]
  exact SDistr.tsum_option_none_zero _ (by simp [SDistr.fail_apply_some])

/-- The lift sends `bind` to `bind`. -/
theorem ofSDistr_bind (μ : SDistr α) (f : α → SDistr β) :
    (ofSDistr (μ.bind f) : SubInstrument R R β) =
      (ofSDistr μ).bind fun a => ofSDistr (f a) := by
  refine DSubInstrument.ext (funext fun b => LinearMap.ext fun ρ => ?_)
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply]
  have hne : ∑' a, μ (some a) * f a (some b) ≠ ⊤ := by
    rw [← SDistr.bind_apply_some']
    exact PMF.apply_ne_top _ _
  have hs : Summable fun a => (μ (some a) * f a (some b)).toReal := ENNReal.summable_toReal hne
  have hterm : ∀ a, (ofSDistr (f a) : SubInstrument R R β).branch b
      ((ofSDistr μ : SubInstrument R R α).branch a ρ) =
        (((μ (some a) * f a (some b)).toReal : ℝ) : ℂ) • ρ := by
    intro a
    simp only [ofSDistr_branch, LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
      ENNReal.toReal_mul, Complex.ofReal_mul, mul_comm]
  simp only [hterm]
  rw [(Complex.summable_ofReal.mpr hs).tsum_smul_const, ← Complex.ofReal_tsum,
    ← ENNReal.tsum_toReal_eq fun a => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _), ← SDistr.bind_apply_some']
  rfl

/-- The lift is monotone for the pointwise order of sub-distributions and Selinger's order. -/
theorem ofSDistr_mono {μ ν : SDistr α} (h : μ ≤ ν) :
    (ofSDistr μ : SubInstrument R R α) ≤ ofSDistr ν := by
  intro a
  convert isCP_ofReal_smul_id (R := R) ((ν (some a)).toReal - (μ (some a)).toReal)
    (sub_nonneg.mpr (ENNReal.toReal_mono (PMF.apply_ne_top _ _) (SDistr.le_def.mp h a)))
    using 1
  ext ρ : 1
  simp [sub_smul]

/-- The lift as a monotone map. -/
noncomputable def ofSDistrHom : SDistr α →o SubInstrument R R α :=
  ⟨ofSDistr, fun _ _ h => ofSDistr_mono h⟩

/-- **Scott continuity.** The lift of the supremum of a chain of sub-distributions is the
supremum of the lifted chain in Selinger's order. -/
theorem ofSDistr_ωSup (c : Chain (SDistr α)) :
    (ofSDistr (ωSup c) : SubInstrument R R α) = ωSup (c.map ofSDistrHom) := by
  refine DSubInstrument.ext (funext fun a => LinearMap.ext fun ρ => ?_)
  refine tendsto_nhds_unique ?_ (tendsto_branch_ωSup (c.map ofSDistrHom) a ρ)
  have hmono : Monotone fun n => c n (some a) := fun m n hmn => SDistr.le_def.mp (c.monotone hmn) a
  have hlim : Filter.Tendsto (fun n => (c n (some a)).toReal) Filter.atTop
      (nhds ((ωSup c (some a)).toReal)) := by
    rw [SDistr.ωSup_apply_some]
    refine (ENNReal.tendsto_toReal ?_).comp (tendsto_atTop_iSup hmono)
    rw [← SDistr.ωSup_apply_some]
    exact PMF.apply_ne_top _ _
  exact ((Complex.continuous_ofReal.tendsto _).comp hlim).smul_const ρ

end Quantum.SubInstrument

namespace CatCrypt.Quantum

variable {d : ℕ} {α : Type}

/-- On the register `Fin d`, the diagonal subinstrument of `μ` is the embedding
`classicalEmbed μ`. -/
theorem ofSDistr_eq_mk' (μ : SDistr α) :
    (_root_.Quantum.SubInstrument.ofSDistr μ : CPComp d α) =
      CPComp.mk' (classicalEmbed μ) (ClassicalDiamondLift.classicalEmbed_isCPMap μ) :=
  _root_.Quantum.DSubInstrument.ext rfl

end CatCrypt.Quantum

/-- A reactive system is heap-independent when every step is a pure computation: it neither
reads nor writes the heap. -/
def CatCrypt.Crypto.UCTransparent.Sys.HeapPure {τ E O : Type}
    (S : CatCrypt.Crypto.UCTransparent.Sys τ E O) : Prop :=
  ∀ t e, CatCrypt.Core.SPComp.IsPure (S.step t e)

namespace CatCrypt.Quantum.ClassicalLiftSys

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Quantum.ReactiveUC
open _root_.Quantum (SubInstrument)
open _root_.Quantum.SubInstrument (ofSDistr ofSDistr_pure ofSDistr_fail ofSDistr_bind
  ofSDistr_ωSup ofSDistrHom)

/-! ## Computations run from the empty heap -/

section HeapFree

variable {α β : Type}

/-- The sub-distribution of results of `c` run from the empty heap, the final heap
discarded. -/
noncomputable def heapFree (c : SPComp α) : SDistr α :=
  (c Heap.empty).bind fun p => SDistr.pure p.1

/-- A computation that samples `μ` and leaves the heap unchanged runs from the empty heap to
`μ`. -/
theorem heapFree_eq_of_forall {c : SPComp α} {μ : SDistr α}
    (h : ∀ hp, c hp = μ.bind fun a => SDistr.pure (a, hp)) : heapFree c = μ := by
  rw [heapFree, h, SDistr.bind_assoc]
  simp only [SDistr.pure_bind]
  exact SDistr.bind_pure μ

/-- `heapFree` of `pure`. -/
theorem heapFree_pure (a : α) : heapFree (SPComp.pure a) = SDistr.pure a :=
  heapFree_eq_of_forall fun hp => (SDistr.pure_bind a fun a => SDistr.pure (a, hp)).symm

/-- `heapFree` of failure. -/
theorem heapFree_fail : heapFree (SPComp.fail : SPComp α) = SDistr.fail := by
  simp only [heapFree, SPComp.fail, SDistr.bind_fail]

/-- On a heap-independent first computation, `heapFree` sends `bind` to `bind`. -/
theorem heapFree_bind {c : SPComp α} (hc : SPComp.IsPure c) (f : α → SPComp β) :
    heapFree (c.bind f) = (heapFree c).bind fun a => heapFree (f a) := by
  obtain ⟨μ, hμ⟩ := hc
  rw [heapFree_eq_of_forall hμ]
  simp only [heapFree, SPComp.bind_def, hμ, SDistr.bind_assoc, SDistr.pure_bind]

/-- `heapFree` sends `map` to `map`. -/
theorem heapFree_map (f : α → β) (c : SPComp α) :
    heapFree (SPComp.map f c) = (heapFree c).bind fun a => SDistr.pure (f a) := by
  simp only [heapFree, SPComp.map, SPComp.bind_def, SPComp.pure_def, SDistr.bind_assoc,
    SDistr.pure_bind]

/-- `heapFree` is monotone. -/
theorem heapFree_mono {c c' : SPComp α} (h : c ≤ c') : heapFree c ≤ heapFree c' :=
  SDistr.bind_mono_left (h Heap.empty) _

/-- `heapFree` as a monotone map. -/
noncomputable def heapFreeHom : SPComp α →o SDistr α :=
  ⟨heapFree, fun _ _ h => heapFree_mono h⟩

/-- `heapFree` of the supremum of a chain is the supremum of `heapFree` of the chain. -/
theorem heapFree_ωSup (c : Chain (SPComp α)) : heapFree (ωSup c) = ωSup (c.map heapFreeHom) := by
  rw [heapFree, SPComp.ωSup_apply, SDistr.ωSup_bind]
  rfl

end HeapFree

/-! ## The lift of a reactive system -/

variable {R : Type} [Fintype R]
variable {τ υ E O E' O' P X : Type}

/-- The lift of the classical reactive system `S` to the register `R`: the same classical state,
and the step the diagonal subinstrument of the classical step run from the empty heap. -/
noncomputable def liftSys (S : Sys τ E O) : QRSys R τ E O where
  init := S.init
  step t e := ofSDistr (heapFree (S.step t e))

/-- Unfolding lemma of `liftSys`: a step. -/
theorem liftSys_step (S : Sys τ E O) (t : τ) (e : E) :
    (liftSys (R := R) S).step t e = ofSDistr (heapFree (S.step t e)) :=
  rfl

/-- The lift of the forwarding system of `f` is the forwarding system of `f`. -/
theorem liftSys_ofFun (f : E → O) : liftSys (R := R) (Sys.ofFun f) = QRSys.ofFun f := by
  change QRSys.mk _ _ = QRSys.mk _ _
  congr 1
  funext t e
  rw [Sys.ofFun, heapFree_pure, ofSDistr_pure]

/-- The lift of a parallel composition is the parallel composition of the lifts. -/
theorem liftSys_par (S : Sys τ E O) (T : Sys υ E' O') :
    liftSys (R := R) (S.par T) = (liftSys S).par (liftSys T) := by
  change QRSys.mk _ _ = QRSys.mk _ _
  congr 1
  funext s e
  rcases e with e | e
  · simp only [Sys.par_step_inl, heapFree_map, ofSDistr_bind, ofSDistr_pure]
    rfl
  · simp only [Sys.par_step_inr, heapFree_map, ofSDistr_bind, ofSDistr_pure]
    rfl

/-- The lift of the cascade of a heap-independent system `S` and a system `T` is the cascade of
the lifts. -/
theorem liftSys_seq {S : Sys τ E O} (hS : S.HeapPure) (T : Sys υ O P) :
    liftSys (R := R) (S.seq T) = (liftSys S).seq (liftSys T) := by
  change QRSys.mk _ _ = QRSys.mk _ _
  congr 1
  funext s e
  simp only [Sys.seq_step, heapFree_bind (hS _ _), heapFree_map, ofSDistr_bind, ofSDistr_pure]
  rfl

/-- On a heap-independent system, the lift of the activation failing on exhausted fuel is the
activation of the lift. -/
theorem liftSys_fbRunFail {S : Sys τ (E ⊕ X) (O ⊕ X)} (hS : S.HeapPure) (n : ℕ) :
    ∀ g t, ofSDistr (heapFree (S.fbRunFail n g t)) = (liftSys (R := R) S).fbRunFail n g t := by
  induction n with
  | zero =>
    intro g t
    rw [Sys.fbRunFail, QRSys.fbRunFail, heapFree_bind (hS t g), ofSDistr_bind, liftSys_step]
    congr 1
    funext q
    rcases q with ⟨t', o | x⟩
    · simp [heapFree_pure, ofSDistr_pure]
    · simp [heapFree_fail, ofSDistr_fail]
  | succ n ih =>
    intro g t
    rw [Sys.fbRunFail, QRSys.fbRunFail, heapFree_bind (hS t g), ofSDistr_bind, liftSys_step]
    congr 1
    funext q
    rcases q with ⟨t', o | x⟩
    · simp [heapFree_pure, ofSDistr_pure]
    · simpa using ih (.inr x) t'

/-- **The trace.** The lift of the unbounded loopback of a heap-independent system is the
unbounded loopback of the lift. -/
theorem liftSys_loopbackω {S : Sys τ (E ⊕ X) (O ⊕ X)} (hS : S.HeapPure) :
    liftSys (R := R) S.loopbackω = (liftSys S).loopbackω := by
  change QRSys.mk _ _ = QRSys.mk _ _
  congr 1
  funext t e
  change ofSDistr (heapFree (ωSup (S.fbChain (.inl e) t))) = ωSup ((liftSys S).fbChain (.inl e) t)
  rw [heapFree_ωSup, ofSDistr_ωSup]
  congr 1
  ext1
  funext n
  exact liftSys_fbRunFail hS n _ _

/-! ## Step equivalence -/

section Restrict

variable {α : Type} {Inv : τ → Prop}

/-- A value of positive weight in `heapFree c` is a possible outcome of `c`. -/
theorem isOutcome_of_heapFree_ne_zero {c : SPComp α} {a : α} (h : heapFree c (some a) ≠ 0) :
    IsOutcome c a := by
  classical
  rw [heapFree, SDistr.bind_apply_some'] at h
  obtain ⟨p, hp⟩ : ∃ p, (c Heap.empty) (some p) * SDistr.pure p.1 (some a) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (ENNReal.tsum_eq_zero.mpr hc)
  have h2 := right_ne_zero_of_mul hp
  rw [SDistr.pure_apply_some] at h2
  have hpa : p.1 = a := by
    by_contra hne
    simp [hne] at h2
  exact ⟨Heap.empty, p.2, by rw [← hpa]; exact left_ne_zero_of_mul hp⟩

open Classical in
/-- The sub-distribution `μ` on the states satisfying `Inv`: the outcomes outside `Inv` fail. -/
noncomputable def restrictD (Inv : τ → Prop) (μ : SDistr (τ × O)) : SDistr ({t // Inv t} × O) :=
  μ.bind fun q => if h : Inv q.1 then SDistr.pure (⟨q.1, h⟩, q.2) else SDistr.fail

/-- On a sub-distribution supported on `Inv`, the restriction followed by the inclusion is the
identity. -/
theorem restrictD_bind_val (μ : SDistr (τ × O)) (hμ : ∀ q, μ (some q) ≠ 0 → Inv q.1) :
    (restrictD Inv μ).bind (fun q => SDistr.pure (q.1.1, q.2)) = μ := by
  rw [restrictD, SDistr.bind_assoc]
  conv_rhs => rw [← SDistr.bind_pure μ]
  refine SDistr.bind_congr_support fun q hq => ?_
  simp [hμ q hq, SDistr.pure_bind]

/-- The lift of `S` on the states satisfying the invariant `Inv`. -/
noncomputable def liftRestrict (S : Sys τ E O) (Inv : τ → Prop) (h0 : Inv S.init) :
    QRSys R {t // Inv t} E O where
  init := ⟨S.init, h0⟩
  step t e := ofSDistr (restrictD Inv (heapFree (S.step t.1 e)))

/-- The inclusion of the invariant is a step map from the restricted lift to the lift. -/
theorem stepMap_liftRestrict_val {S : Sys τ E O} (h0 : Inv S.init)
    (hpres : ∀ t e, Inv t → ∀ q, IsOutcome (S.step t e) q → Inv q.1) :
    QRSys.StepMap (liftRestrict (R := R) S Inv h0) (liftSys S) Subtype.val where
  init_map := rfl
  step t e := by
    have key := congrArg (ofSDistr (R := R)) (restrictD_bind_val (Inv := Inv)
      (heapFree (S.step t.1 e)) fun q hq =>
        hpres t.1 e t.2 q (isOutcome_of_heapFree_ne_zero hq))
    rw [ofSDistr_bind] at key
    simp only [ofSDistr_pure] at key
    exact key

/-- A step map on an invariant gives a step map from the restricted lift to the lift of the
target. -/
theorem stepMap_liftRestrict {S : Sys τ E O} {S' : Sys υ E O} {f : τ → υ}
    (h : Sys.StepMapOn S S' Inv f) :
    QRSys.StepMap (liftRestrict (R := R) S Inv h.init_inv) (liftSys S') (f ∘ Subtype.val) where
  init_map := h.init_map
  step t e := by
    have hμ : ∀ q, heapFree (S.step t.1 e) (some q) ≠ 0 → Inv q.1 := fun q hq =>
      h.pres t.1 e t.2 q (isOutcome_of_heapFree_ne_zero hq)
    change (ofSDistr (restrictD Inv (heapFree (S.step t.1 e)))).bind _ =
      ofSDistr (heapFree (S'.step (f t.1) e))
    rw [← h.step t.1 e t.2, heapFree_map]
    conv_rhs => rw [← restrictD_bind_val _ hμ]
    rw [SDistr.bind_assoc]
    simp only [SDistr.pure_bind]
    rw [ofSDistr_bind]
    simp only [ofSDistr_pure]
    rfl

end Restrict

/-- The lift of a bundled system. -/
noncomputable def liftObj (A : SysObj E O) : QRSys.Obj R E O :=
  ⟨A.St, liftSys A.sys⟩

/-- Systems related by a step map on an invariant have step-equivalent lifts. -/
theorem stepEq_liftObj_of_stepRel {A B : SysObj E O} (h : Sys.StepRel A B) :
    QRSys.StepEq (liftObj (R := R) A) (liftObj B) := by
  obtain ⟨Inv, f, h⟩ := h
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (stepMap_liftRestrict_val (R := R) h.init_inv h.pres).stepEq)
    (stepMap_liftRestrict (R := R) h).stepEq

/-- **Step equivalence.** Step-equivalent classical systems have step-equivalent lifts. -/
theorem stepEq_liftObj {A B : SysObj E O} (h : Sys.StepEq A B) :
    QRSys.StepEq (liftObj (R := R) A) (liftObj B) := by
  induction h with
  | rel A B h => exact stepEq_liftObj_of_stepRel h
  | refl A => exact Relation.EqvGen.refl _
  | symm A B _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans A B C _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-! ## Heap independence -/

section HeapPure

/-- The supremum of a chain of heap-independent computations is heap-independent. -/
theorem isPure_ωSup {α : Type} (c : Chain (SPComp α)) (hc : ∀ n, SPComp.IsPure (c n)) :
    SPComp.IsPure (ωSup c) := by
  refine ⟨ωSup (c.map heapFreeHom), fun hp => ?_⟩
  rw [SPComp.ωSup_apply, SDistr.ωSup_bind]
  congr 1
  ext1
  funext n
  obtain ⟨μ, hμ⟩ := hc n
  change c n hp = (heapFree (c n)).bind _
  rw [heapFree_eq_of_forall hμ, hμ]

/-- The forwarding system is heap-independent. -/
theorem heapPure_ofFun (f : E → O) : (Sys.ofFun f).HeapPure := fun _ _ =>
  SPComp.pure_isPure _

/-- The cascade of heap-independent systems is heap-independent. -/
theorem heapPure_seq {S : Sys τ E O} {T : Sys υ O P} (hS : S.HeapPure) (hT : T.HeapPure) :
    (S.seq T).HeapPure := by
  intro s e
  rw [Sys.seq_step]
  refine SPComp.bind_isPure (hS _ _) fun _ => ?_
  unfold SPComp.map
  exact SPComp.bind_isPure (hT _ _) fun _ => SPComp.pure_isPure _

/-- The parallel composition of heap-independent systems is heap-independent. -/
theorem heapPure_par {S : Sys τ E O} {T : Sys υ E' O'} (hS : S.HeapPure) (hT : T.HeapPure) :
    (S.par T).HeapPure := by
  rintro s (e | e)
  · rw [Sys.par_step_inl]
    unfold SPComp.map
    exact SPComp.bind_isPure (hS _ _) fun _ => SPComp.pure_isPure _
  · rw [Sys.par_step_inr]
    unfold SPComp.map
    exact SPComp.bind_isPure (hT _ _) fun _ => SPComp.pure_isPure _

/-- The activations failing on exhausted fuel of a heap-independent system are
heap-independent. -/
theorem isPure_fbRunFail {S : Sys τ (E ⊕ X) (O ⊕ X)} (hS : S.HeapPure) (n : ℕ) :
    ∀ g t, SPComp.IsPure (S.fbRunFail n g t) := by
  induction n with
  | zero =>
    intro g t
    refine SPComp.bind_isPure (hS t g) fun q => ?_
    rcases q with ⟨t', o | x⟩
    · exact SPComp.pure_isPure _
    · exact SPComp.fail_isPure
  | succ n ih =>
    intro g t
    refine SPComp.bind_isPure (hS t g) fun q => ?_
    rcases q with ⟨t', o | x⟩
    · exact SPComp.pure_isPure _
    · exact ih _ _

/-- The unbounded loopback of a heap-independent system is heap-independent. -/
theorem heapPure_loopbackω {S : Sys τ (E ⊕ X) (O ⊕ X)} (hS : S.HeapPure) :
    S.loopbackω.HeapPure := fun t e =>
  isPure_ωSup (S.fbChain (.inl e) t) fun n => isPure_fbRunFail hS n _ _

end HeapPure

/-! ## The functor -/

/-- A bundled system with heap-independent steps. -/
abbrev PSysObj (E O : Type) : Type 1 := {A : SysObj E O // A.sys.HeapPure}

/-- Classical step equivalence on heap-independent systems. -/
instance PSysObj.stepSetoid (E O : Type) : Setoid (PSysObj E O) :=
  Setoid.comap Subtype.val (SysObj.stepSetoid E O)

/-- A type of ports of heap-independent classical systems. -/
structure PSysCat : Type 1 where
  /-- The ports. -/
  P : Type

open CategoryTheory

/-- The category of port types whose morphisms are heap-independent classical systems modulo
classical step equivalence; composition is the cascade. -/
noncomputable instance PSysCat.category : Category.{1} PSysCat where
  Hom X Y := Quotient (PSysObj.stepSetoid X.P Y.P)
  id X := ⟦⟨SysObj.idSys X.P, heapPure_ofFun id⟩⟧
  comp := Quotient.map₂ (fun A B => ⟨A.1.seq B.1, heapPure_seq A.2 B.2⟩)
    fun _ _ h₁ _ _ h₂ => Sys.StepEq.seq h₁ h₂
  id_comp := by
    rintro X Y ⟨A⟩
    exact Quotient.sound (Sys.StepEq.id_seq A.1)
  comp_id := by
    rintro X Y ⟨A⟩
    exact Quotient.sound (Sys.StepEq.seq_id A.1)
  assoc := by
    rintro W X Y Z ⟨A⟩ ⟨B⟩ ⟨C⟩
    exact Quotient.sound (Sys.StepEq.seq_assoc A.1 B.1 C.1)

/-- The inclusion of the heap-independent systems in `SysCat`. -/
noncomputable def PSysCat.toSysCat : PSysCat ⥤ SysCat where
  obj X := ⟨X.P⟩
  map f := Quotient.map Subtype.val (fun _ _ h => h) f
  map_id _ := rfl
  map_comp := by
    rintro X Y Z ⟨A⟩ ⟨B⟩
    rfl

variable (R) in
/-- **The lift functor.** A heap-independent classical system is sent to its lift on the
register `R`. -/
noncomputable def liftFunctor : PSysCat ⥤ QSysCat R where
  obj X := ⟨X.P⟩
  map f := Quotient.map (fun A => liftObj A.1) (fun _ _ h => stepEq_liftObj h) f
  map_id X := Quotient.sound (by
    change QRSys.StepEq ⟨Unit, liftSys (Sys.ofFun id)⟩ ⟨Unit, QRSys.ofFun id⟩
    rw [liftSys_ofFun]
    exact Relation.EqvGen.refl _)
  map_comp := by
    rintro X Y Z ⟨A⟩ ⟨B⟩
    exact Quotient.sound (by
      change QRSys.StepEq ⟨_, liftSys (A.1.sys.seq B.1.sys)⟩
        ⟨_, (liftSys A.1.sys).seq (liftSys B.1.sys)⟩
      rw [liftSys_seq A.2]
      exact Relation.EqvGen.refl _)

/-- The parallel composition of morphisms of `PSysCat`. -/
noncomputable def PSysCat.tensorHom {X₁ Y₁ X₂ Y₂ : PSysCat} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (⟨X₁.P ⊕ X₂.P⟩ : PSysCat) ⟶ ⟨Y₁.P ⊕ Y₂.P⟩ :=
  Quotient.map₂ (fun A B => ⟨A.1.par B.1, heapPure_par A.2 B.2⟩)
    (fun _ _ h₁ _ _ h₂ => Sys.StepEq.par h₁ h₂) f g

/-- **`⊕`.** The lift functor sends the parallel composition to the tensor product of
`QSysCat R`. -/
theorem liftFunctor_map_tensor {X₁ Y₁ X₂ Y₂ : PSysCat} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (liftFunctor R).map (PSysCat.tensorHom f g) =
      QSysCat.tensorHom ((liftFunctor R).map f) ((liftFunctor R).map g) := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rename_i A B
  exact Quotient.sound (by
    change QRSys.StepEq ⟨_, liftSys (A.1.sys.par B.1.sys)⟩
      ⟨_, (liftSys A.1.sys).par (liftSys B.1.sys)⟩
    rw [liftSys_par]
    exact Relation.EqvGen.refl _)

/-- The trace of `PSysCat`: the class of the unbounded loopback along `U`. -/
noncomputable def PSysCat.trace (U : PSysCat) {X Y : PSysCat}
    (f : (⟨X.P ⊕ U.P⟩ : PSysCat) ⟶ ⟨Y.P ⊕ U.P⟩) : X ⟶ Y :=
  Quotient.map (fun A => ⟨A.1.loopbackω, heapPure_loopbackω A.2⟩)
    (fun _ _ h => Sys.StepEq.loopbackω h) f

/-- **The trace.** The lift functor sends the unbounded loopback of `PSysCat` to the trace of
`QSysCat R`. -/
theorem liftFunctor_map_trace (U : PSysCat) {X Y : PSysCat}
    (f : (⟨X.P ⊕ U.P⟩ : PSysCat) ⟶ ⟨Y.P ⊕ U.P⟩) :
    (liftFunctor R).map (PSysCat.trace U f) =
      QSysCat.trace (X := ⟨X.P⟩) (Y := ⟨Y.P⟩) ⟨U.P⟩ ((liftFunctor R).map f) := by
  induction f using Quotient.inductionOn
  rename_i A
  exact Quotient.sound (by
    change QRSys.StepEq ⟨_, liftSys A.1.sys.loopbackω⟩ ⟨_, (liftSys A.1.sys).loopbackω⟩
    rw [liftSys_loopbackω A.2]
    exact Relation.EqvGen.refl _)

/-! ## Party programs -/

section Prog

open CatCrypt.Crypto.Party

variable {α γ : Type}

/-- The lift of the denotation of a party program. -/
noncomputable def toQSys (p : Prog E O α) : QRSys R (Prog E O α) E O :=
  liftSys (Prog.toSys p)

/-- The emit phase on the register `R`: a sample is the diagonal subinstrument of its
sub-distribution run from the empty heap. -/
noncomputable def qEmitK (s : O → Prog E O α → SubInstrument R R γ)
    (r : α → SubInstrument R R γ) : Prog E O α → SubInstrument R R γ
  | .ret a => r a
  | .recv _ => SubInstrument.fail
  | .send o p => s o p
  | .sampleN μ k => (ofSDistr (heapFree μ)).bind fun n => qEmitK s r (k n)
  | .fail => SubInstrument.fail

/-- The await phase on the register `R` on the event `e`: a sample is the diagonal
subinstrument of its sub-distribution run from the empty heap. -/
noncomputable def qAwaitK (e : E) (s : O → Prog E O α → SubInstrument R R γ)
    (rA rE : α → SubInstrument R R γ) : Prog E O α → SubInstrument R R γ
  | .ret a => rA a
  | .recv k => qEmitK s rE (k e)
  | .send _ _ => SubInstrument.fail
  | .sampleN μ k => (ofSDistr (heapFree μ)).bind fun n => qAwaitK e s rA rE (k n)
  | .fail => SubInstrument.fail

/-- The quantum interpreter of one activation of a program that halts on return. -/
noncomputable def qAct (p : Prog E O α) (e : E) : SubInstrument R R (Prog E O α × O) :=
  qAwaitK e (fun o q => SubInstrument.pure (q, o)) (fun _ => SubInstrument.fail)
    (fun _ => SubInstrument.fail) p

/-- Every sample of the program is heap-independent. -/
inductive SamplesPure : Prog E O α → Prop
  /-- A return. -/
  | ret (a : α) : SamplesPure (.ret a)
  /-- A receive whose continuations sample heap-independently. -/
  | recv (k : E → Prog E O α) (h : ∀ e, SamplesPure (k e)) : SamplesPure (.recv k)
  /-- A send whose continuation samples heap-independently. -/
  | send (o : O) (p : Prog E O α) (h : SamplesPure p) : SamplesPure (.send o p)
  /-- A heap-independent sample whose continuations sample heap-independently. -/
  | sampleN (μ : SPComp ℕ) (k : ℕ → Prog E O α) (hμ : SPComp.IsPure μ)
      (h : ∀ n, SamplesPure (k n)) : SamplesPure (.sampleN μ k)
  /-- A failure. -/
  | fail : SamplesPure .fail

/-- On a program whose samples are heap-independent, the quantum emit phase is the lift of the
classical emit phase. -/
theorem qEmitK_eq {s : O → Prog E O α → SubInstrument R R γ} {r : α → SubInstrument R R γ}
    {s' : O → Prog E O α → SPComp γ} {r' : α → SPComp γ}
    (hs : ∀ o q, SamplesPure q → s o q = ofSDistr (heapFree (s' o q)))
    (hr : ∀ a, r a = ofSDistr (heapFree (r' a))) {p : Prog E O α} (hp : SamplesPure p) :
    qEmitK s r p = ofSDistr (heapFree (Prog.emitK s' r' p)) := by
  induction hp with
  | ret a => exact hr a
  | recv k _ _ => simp only [qEmitK, Prog.emitK, heapFree_fail, ofSDistr_fail]
  | send o p hp _ => exact hs o p hp
  | sampleN μ k hμ _ ih =>
    simp only [qEmitK, Prog.emitK, heapFree_bind hμ, ofSDistr_bind, ih]
  | fail => simp only [qEmitK, Prog.emitK, heapFree_fail, ofSDistr_fail]

/-- On a program whose samples are heap-independent, the quantum await phase is the lift of the
classical await phase. -/
theorem qAwaitK_eq (e : E) {s : O → Prog E O α → SubInstrument R R γ}
    {rA rE : α → SubInstrument R R γ} {s' : O → Prog E O α → SPComp γ} {rA' rE' : α → SPComp γ}
    (hs : ∀ o q, SamplesPure q → s o q = ofSDistr (heapFree (s' o q)))
    (hrA : ∀ a, rA a = ofSDistr (heapFree (rA' a))) (hrE : ∀ a, rE a = ofSDistr (heapFree (rE' a)))
    {p : Prog E O α} (hp : SamplesPure p) :
    qAwaitK e s rA rE p = ofSDistr (heapFree (Prog.awaitK e s' rA' rE' p)) := by
  induction hp with
  | ret a => exact hrA a
  | recv k hk _ => exact qEmitK_eq hs hrE (hk e)
  | send o p _ _ => simp only [qAwaitK, Prog.awaitK, heapFree_fail, ofSDistr_fail]
  | sampleN μ k hμ _ ih =>
    simp only [qAwaitK, Prog.awaitK, heapFree_bind hμ, ofSDistr_bind, ih]
  | fail => simp only [qAwaitK, Prog.awaitK, heapFree_fail, ofSDistr_fail]

/-- **Party programs.** At a residual program whose samples are heap-independent, the quantum
interpreter, which runs each sample as the diagonal subinstrument of its sub-distribution, is
the step of the lift of the denotation. -/
theorem qAct_eq_toQSys_step (p t : Prog E O α) (e : E) (ht : SamplesPure t) :
    qAct (R := R) t e = (toQSys p).step t e := by
  change _ = ofSDistr (heapFree (Prog.awaitK e (fun o q => SPComp.pure (q, o))
    (fun _ => SPComp.fail) (fun _ => SPComp.fail) t))
  refine qAwaitK_eq e (fun o q _ => ?_) (fun _ => ?_) (fun _ => ?_) ht
  · rw [heapFree_pure, ofSDistr_pure]
  · rw [heapFree_fail, ofSDistr_fail]
  · rw [heapFree_fail, ofSDistr_fail]

end Prog

/-! ## Transport of realizations -/

section Transport

open CatCrypt.Crypto.UCMonad.DiamondNorm
open CatCrypt.Crypto (prTrue)
open CatCrypt.Crypto.UCConcrete (Env DistC)

variable {d : ℕ} {α ζ : Type}

/-- The lift of `S` to a quantum reactive system on `Fin d` with the trivial private
register. -/
noncomputable def liftQSys (S : Sys τ E O) : QSys Unit τ E O d where
  init := S.init
  initReg := ()
  step t e := ofSDistr (heapFree (S.step t e))

/-- The classical-lift form of an environment: each activation is the diagonal subinstrument
of the classical activation run from the empty heap. -/
noncomputable def liftStrat (Z : Strat ζ E O) : QStrat ζ E O d where
  rounds := Z.rounds
  init := Z.init
  next z := ofSDistr (heapFree (Z.next z))
  obs z o := ofSDistr (heapFree (Z.obs z o))

/-- The activations of the environment are heap-independent. -/
def StratPure (Z : Strat ζ E O) : Prop :=
  (∀ z, SPComp.IsPure (Z.next z)) ∧ ∀ z o, SPComp.IsPure (Z.obs z o)

/-- Framing a diagonal subinstrument by a register gives the diagonal subinstrument. -/
theorem frame_ofSDistr {A : Type} [Fintype A] (H : Type) [Fintype H] (μ : SDistr α) :
    (ofSDistr μ : SubInstrument A A α).frame H = ofSDistr μ := by
  refine _root_.Quantum.DSubInstrument.ext (funext fun a => LinearMap.ext fun ρ => ?_)
  ext x y
  simp

/-- The joint run of a lifted environment and a lifted system is the lift of the classical joint
run, its flag forgotten. -/
theorem qloop_liftQSys {S : Sys τ E O} (hS : S.HeapPure) {Z : Strat ζ E O} (hZ : StratPure Z)
    (b : Bool) (n : ℕ) : ∀ z t, qloop (liftQSys (d := d) S) (liftStrat Z) n (z, t) =
      (ofSDistr (heapFree (loop S (fun _ => false) Z n (z, t, b)))).bind
        fun c => SubInstrument.pure (c.1, c.2.1) := by
  induction n with
  | zero =>
    intro z t
    simp only [qloop, loop, heapFree_pure, ofSDistr_pure, SubInstrument.pure_bind]
  | succ n ih =>
    intro z t
    rw [qloop]
    simp only [ih]
    simp only [loop, liftQSys, liftStrat, heapFree_bind (hZ.1 _), heapFree_bind (hS _ _),
      heapFree_bind (hZ.2 _ _), ofSDistr_bind, frame_ofSDistr, SubInstrument.bind_assoc,
      Bool.or_false]

/-- The view of a lifted environment against a lifted system is determined by the classical
view from the empty heap. -/
theorem qview_liftQSys {S : Sys τ E O} (hS : S.HeapPure) {Z : Strat ζ E O} (hZ : StratPure Z) :
    qview (liftQSys (d := d) S) (liftStrat Z) = (appendBasis ()).bind fun _ =>
      (ofSDistr (heapFree (view S Z))).bind fun z =>
        discardRight.bind fun _ => SubInstrument.pure z := by
  unfold qview
  rw [qloop_liftQSys hS hZ false]
  simp only [view, run, heapFree_map, ofSDistr_bind, ofSDistr_pure, SubInstrument.bind_assoc,
    SubInstrument.pure_bind]
  rfl

/-- The acceptance probability from the empty heap is the weight of `true` in `heapFree`. -/
theorem prTrue_eq_heapFree (G : SPComp Bool) : prTrue G Heap.empty = heapFree G (some true) := by
  rw [prTrue, heapFree, SDistr.bind_apply_some']
  have key : ∀ g : SDistr (Bool × Heap),
      ∑' h, g (some (true, h)) = ∑' p, g (some p) * SDistr.pure p.1 (some true) := by
    intro g
    rw [ENNReal.tsum_prod', tsum_bool]
    simp [SDistr.pure_apply_some]
  exact key (G Heap.empty)

/-- The test of the value `z₀` accepts with the weight of `z₀` in `heapFree`. -/
theorem prTrue_bind_decide [DecidableEq α] (c : SPComp α) (z₀ : α) :
    prTrue (SPComp.bind c fun z => SPComp.pure (decide (z = z₀))) Heap.empty =
      heapFree c (some z₀) := by
  rw [prTrue_eq_heapFree]
  change heapFree (SPComp.map _ c) _ = _
  rw [heapFree_map, SDistr.bind_apply_some', tsum_eq_single z₀]
  · simp [SDistr.pure_apply_some]
  · intro z hz
    simp [hz, SDistr.pure_apply_some]

/-- A classical realization at distance `0` gives equal views from the empty heap. -/
theorem heapFree_view_eq_of_realizes {S : Sys τ E O} {I : Sys υ E O}
    (h : Realizes S I fun _ _ => 0) (Z : Strat ζ E O) :
    heapFree (view S Z) = heapFree (view I Z) := by
  classical
  refine SDistr.eq_of_some_eq fun z₀ => ?_
  have hg := h ζ ⟨Z, Heap.empty, fun z => SPComp.pure (decide (z = z₀))⟩
  simp only [Env.gap, CatCrypt.Crypto.absDiff, prTrue_bind_decide] at hg
  rw [max_le_iff] at hg
  exact le_antisymm (tsub_eq_zero_iff_le.mp (nonpos_iff_eq_zero.mp hg.1))
    (tsub_eq_zero_iff_le.mp (nonpos_iff_eq_zero.mp hg.2))

/-- **Transport at distance `0`.** A classical realization at distance `0` between
heap-independent systems gives equal quantum views against every environment of the
classical-lift form with heap-independent activations. -/
theorem qview_liftQSys_eq_of_realizes {S : Sys τ E O} {I : Sys υ E O} (hS : S.HeapPure)
    (hI : I.HeapPure) (h : Realizes S I fun _ _ => 0) (Z : Strat ζ E O) (hZ : StratPure Z) :
    qview (liftQSys (d := d) S) (liftStrat Z) = qview (liftQSys I) (liftStrat Z) := by
  rw [qview_liftQSys hS hZ, qview_liftQSys hI hZ, heapFree_view_eq_of_realizes h Z]

/-- **Quantum realization at distance `0`.** A classical realization at distance `0` between
heap-independent systems gives the quantum realization at distance `0` of their lifts, in the
diamond norm, against the environments of the classical-lift form with heap-independent
activations. -/
theorem quc_liftQSys_of_realizes {S : Sys τ E O} {I : Sys υ E O} (hS : S.HeapPure)
    (hI : I.HeapPure) (h : Realizes S I fun _ _ => 0) (ζ : Type) :
    QUCEmulatesDiamond 0
      (fun Z : {Z : Strat ζ E O // StratPure Z} =>
        (qview (liftQSys (d := d) S) (liftStrat Z.1)).toQComp)
      (fun Z => (qview (liftQSys I) (liftStrat Z.1)).toQComp)
      (fun Z => CPComp.branch_cp (qview (liftQSys S) (liftStrat Z.1)))
      (fun Z => CPComp.branch_cp (qview (liftQSys I) (liftStrat Z.1))) := by
  have key : ∀ (f g : {Z : Strat ζ E O // StratPure Z} → QComp d ζ) (hf : IsCPChannel f)
      (hg : IsCPChannel g), f = g → QUCEmulatesDiamond 0 f g hf hg := by
    rintro f g hf hg rfl
    exact QUCEmulatesDiamond.refl 0 f hf
  exact key _ _ _ _ (funext fun Z =>
    congrArg CPComp.toQComp (qview_liftQSys_eq_of_realizes hS hI h Z.1 Z.2))

end Transport

end CatCrypt.Quantum.ClassicalLiftSys
