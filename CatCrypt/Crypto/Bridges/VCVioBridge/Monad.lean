/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SDist
import CatCrypt.Prob.Support
import VCVio

/-!
# VCVio Bridge — Monad layer (Phase 1)

Probability-level and stateless monad-morphism bridge between VCVio and CatCrypt,
stated in `SDistr` / `SPComp` terms without any dependency on the `UCMonad`
typeclass. The UC-facing wrapping lives in the private `UCLift.lean` extension.

## Key insight

VCVio's `SPMF α = OptionT PMF = PMF (Option α)` is **definitionally**
CatCrypt's `SDistr α = PMF (Option α)`.

## Main definitions

* `toSDistr` / `fromSDistr` — Type isomorphism (definitional)
* `ProbComp.toSDistr` — Embed `ProbComp` into `SDistr` via `evalDist`
* `sdistrToSPComp` — State-independent lift from `SDistr` to `SPComp`
* `probCompLift` — `ProbComp → SPComp` monad morphism (composition of the two)

## Main results

* `sdistrToSPComp_pure` / `sdistrToSPComp_bind` — monad-morphism laws
* `sdistrToSPComp_isPure` — the lift produces heap-independent computations
* `probCompLift_pure` / `probCompLift_bind` — monad-morphism laws for `ProbComp`
* `probCompLift_isPure` — the ProbComp lift ignores the heap argument
-/

namespace CatCrypt.Crypto.VCVioBridge

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

/-! ## Type Isomorphism: SPMF ≅ SDistr (definitional) -/

/-- Convert VCVio's `SPMF` to CatCrypt's `SDistr`. -/
noncomputable def toSDistr {α : Type} (p : SPMF α) : SDistr α := p.toPMF

/-- Convert CatCrypt's `SDistr` to VCVio's `SPMF`. -/
noncomputable def fromSDistr {α : Type} (d : SDistr α) : SPMF α := SPMF.mk d

@[simp] theorem toSDistr_fromSDistr {α : Type} (d : SDistr α) :
    toSDistr (fromSDistr d) = d := rfl

@[simp] theorem fromSDistr_toSDistr {α : Type} (p : SPMF α) :
    fromSDistr (toSDistr p) = p := SPMF.mk_toPMF p

/-! ## SDistr ≡ SPMF alignment (bridge simp lemmas)

VCVio's `SPMF` and CatCrypt's `SDistr` are definitionally the same type —
both unfold to `PMF (Option α)`.  However, they carry independent monad
typeclass instances:

* `SPMF` inherits `AlternativeMonad`, `LawfulMonad`, `LawfulAlternative`,
  `LawfulMonadLift PMF SPMF` from the `OptionT PMF` structure.
* `SDistr` declares its own `Monad` and `LawfulMonad` instances directly
  via `SDistr.pure` / `SDistr.bind`.

The lemmas below bridge the two so VCVio's SPMF-level lemmas apply to
`SDistr` values after a single `simp [...]` normalization step, and
vice-versa.  Each lemma holds by `rfl` — the underlying operations are
already the same PMF computation; only the namespace annotations differ. -/

/-- `SDistr.pure` in SPMF-view. Named (not `@[simp]`) to avoid
    interference with CatCrypt's existing `SDistr.pure_bind` simp set. -/
theorem SDistr.pure_eq_SPMF {α : Type} (a : α) :
    (SDistr.pure a : SDistr α) = toSDistr (SPMF.mk (PMF.pure (some a))) := rfl

/-- `SDistr.fail` in SPMF-view. -/
theorem SDistr.fail_eq_SPMF {α : Type} :
    (SDistr.fail : SDistr α) = toSDistr (SPMF.mk (PMF.pure none)) := rfl

/-- `SDistr.uniform` in SPMF-view. -/
theorem SDistr.uniform_eq_SPMF {α : Type} [Fintype α] [Nonempty α] :
    SDistr.uniform α = toSDistr (SPMF.mk ((PMF.uniformOfFintype α).map some)) := rfl

/-- `SPMF.mk` commutes with `SDistr.pure` → `Pure.pure`. -/
theorem SPMF.mk_SDistr_pure {α : Type} (a : α) :
    SPMF.mk (SDistr.pure a) = (pure a : SPMF α) := rfl

/-- `SPMF.mk` commutes with `SDistr.fail` → `failure`. -/
theorem SPMF.mk_SDistr_fail {α : Type} :
    SPMF.mk (SDistr.fail : SDistr α) = failure :=
  SPMF.failure_eq_mk.symm

/-! ## ProbComp Embedding into SDistr -/

/-- Embed VCVio's `ProbComp` into `SDistr` via `evalDist`. -/
noncomputable def ProbComp.toSDistr {α : Type} (mx : ProbComp α) : SDistr α :=
  (evalDist mx).toPMF

/-! ## State-Independent Lift: SDistr → SPComp -/

/-- Lift `SDistr` to `SPComp` by ignoring the heap. -/
noncomputable def sdistrToSPComp {α : Type} (d : SDistr α) : SPComp α :=
  fun h => SDistr.bind d (fun a => SDistr.pure (a, h))

@[simp] theorem sdistrToSPComp_run {α : Type} (d : SDistr α) (h : Heap) :
    sdistrToSPComp d h = SDistr.bind d (fun a => SDistr.pure (a, h)) := rfl

/-- The state-independent lift preserves pure. -/
theorem sdistrToSPComp_pure {α : Type} (a : α) :
    sdistrToSPComp (SDistr.pure a) = SPComp.pure a := by
  funext h; simp [sdistrToSPComp, SDistr.pure_bind, SPComp.pure]

/-- The state-independent lift preserves bind. -/
theorem sdistrToSPComp_bind {α β : Type} (d : SDistr α) (f : α → SDistr β) :
    sdistrToSPComp (SDistr.bind d f) =
    SPComp.bind (sdistrToSPComp d) (fun a => sdistrToSPComp (f a)) := by
  funext h
  unfold sdistrToSPComp SPComp.bind
  simp only [SDistr.bind_assoc, SDistr.pure_bind]

/-- The state-independent lift produces `IsPure` computations. -/
theorem sdistrToSPComp_isPure {α : Type} (d : SDistr α) :
    SPComp.IsPure (sdistrToSPComp d) :=
  ⟨d, fun _ => rfl⟩

/-! ## ProbComp → SPComp monad morphism -/

/-- Full monad morphism `ProbComp → SPComp`: run the `ProbComp` to an `SDistr`,
    then lift to `SPComp` by ignoring the heap. This is the canonical stateless
    embedding used throughout the bridge. -/
noncomputable def probCompLift {α : Type} (mx : ProbComp α) : SPComp α :=
  sdistrToSPComp (ProbComp.toSDistr mx)

@[simp] theorem probCompLift_eq {α : Type} (mx : ProbComp α) :
    probCompLift mx = sdistrToSPComp (ProbComp.toSDistr mx) := rfl

/-- `probCompLift` preserves `pure`. -/
theorem probCompLift_pure {α : Type} (a : α) :
    probCompLift (pure a : ProbComp α) = SPComp.pure a := by
  unfold probCompLift ProbComp.toSDistr
  rw [evalDist_pure]
  show sdistrToSPComp (SDistr.pure a) = SPComp.pure a
  exact sdistrToSPComp_pure a

/-- `probCompLift` preserves `bind`. -/
theorem probCompLift_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) :
    probCompLift (mx >>= f) = SPComp.bind (probCompLift mx) (fun a => probCompLift (f a)) := by
  unfold probCompLift ProbComp.toSDistr
  rw [evalDist_bind]
  show sdistrToSPComp (SDistr.bind (evalDist mx).toPMF (fun a => (evalDist (f a)).toPMF)) = _
  rw [sdistrToSPComp_bind]

/-- The lift produces heap-independent (i.e. `IsPure`) computations. -/
theorem probCompLift_isPure {α : Type} (mx : ProbComp α) :
    SPComp.IsPure (probCompLift mx) :=
  sdistrToSPComp_isPure _

end CatCrypt.Crypto.VCVioBridge
