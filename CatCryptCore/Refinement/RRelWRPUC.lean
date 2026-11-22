/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.RRelWRPProb
public import CatCryptCore.Category.ProtBicatApprox
public import CatCryptCore.Crypto.UCConcrete
public import CatCryptCore.Crypto.UCMonad.SPCompInstance

/-!
# Game hops from refinement through couplings

At equal heaps and equal results, refinement of an ideal computation by a real computation up to
`ε` bounds the distinguishing advantage by `ε` in both directions. The judgement `RefinesUpTo`
states one inequality of expectations for every test bounded by `1` and every failure weight
bounded by `1`. A test at failure weight `0` gives one direction, and its complement at failure
weight `1` gives the other, since the two expectations sum to `1`. By completeness of couplings
for the statistical distance, the judgement is then equivalent to a coupling of grade `ε`.

`RefinesFamilyUpTo G F ε` is the premise class: for each input `x`, the real `G x` refines the
ideal `F x` up to `ε`. An instance is built from a coupling by
`RefinesFamilyUpTo.of_rHoareApprox`. It is a statement of statistical distance, so it applies to
information-theoretic steps; a computational step states its bound by a reduction in
`GameAdvBoundC`. From an instance, instance search gives `GameAdvBoundC` at the constant bound
`ε`, and with `PureGame` on both games `UCFromGameC`, the game hop: the emulation of the ideal
game by the real game with the identity simulator. For protocol objects, a simulator and an
instance give a 2-cell `ProtMorε`.

## Main definitions

* `RefinesFamilyUpTo G F ε`: a family of refinements up to `ε` at equal heaps and equal results.
* `UCMonad.ProtMorε.ofRefines`: the approximate 2-cell of a simulator and a refinement.

## Main results

* `RefinesUpTo.absDiff_prTrue_le`: one direction of refinement bounds both differences.
* `refinesUpTo_iff_rHoareApprox`: refinement up to `ε` is a coupling of grade `ε`.
* `RefinesFamilyUpTo.sdist_le`, `RefinesFamilyUpTo.advantageA_le`: the bounds of a family.
* `instGameAdvBoundCOfRefines`: the game bound by instance search, the premise of a game hop.
* `refines_heapConc_eqPre_refl`: exact refinement of a computation by itself.

## Search words

approximate coupling, refinement, game hop by instance search, statistical distance,
complement of a test, simulator, approximate 2-cell
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Refinement.WRP

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary CatCrypt.Crypto RefinementWP
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCDSL CatCrypt.Crypto.UCComposition
open scoped ENNReal

variable {ι α : Type}

/-! ## One direction of refinement bounds the distance -/

/-- At equal heaps and equal results, the concretization of a postcondition bounded by `1` is
    that postcondition. -/
theorem post_heapConc_eqPre_indRel_eq {q : α → Heap → ℝ≥0∞} (hq : ∀ x h, q x h ≤ 1) :
    (heapConc eqPre).post (indRel Eq) q = q := by
  funext x h
  refine le_antisymm ?_ (le_post_indRel ⟨rfl, rfl⟩ hq)
  rw [post_expectation_apply]
  refine iSup_le fun y => ?_
  by_cases hxy : x = y
  · subst hxy
    exact (min_le_right _ _).trans (iSup₂_le fun _ hs => hs ▸ le_rfl)
  · simp [indRel, hxy]

/-- The expectation of the complement of a test at failure weight `1` and the expectation of
    the test at failure weight `0` sum to `1`. -/
theorem wpEF_compl_add (c : SPComp α) {q : α → Heap → ℝ≥0∞} (hq : ∀ x h, q x h ≤ 1)
    (h : Heap) : wpEF c (fun x s => 1 - q x s) 1 h + wpEF c q 0 h = 1 := by
  rw [wpEF_eq_tsum_option, wpEF_eq_tsum_option, ← tsum_add]
  refine (tsum_congr fun o => ?_).trans (c h).tsum_coe
  cases o <;> simp [← mul_add, tsub_add_cancel_of_le, hq]

/-- The acceptance probability of a distinguisher after a computation is the expectation of
    its acceptance probability at failure weight `0`. -/
theorem prTrue_bind_eq_wpEF (c : SPComp α) (D : α → SPComp Bool) (h : Heap) :
    prTrue (SPComp.bind c D) h = wpEF c (fun x s => prTrue (D x) s) 0 h := by
  simp [prTrue_bind_weighted', wpEF, wpE_eq_tsum]

variable {c a : SPComp α} {ε : ℝ≥0∞}

/-- Refinement up to `ε` at equal heaps and equal results compares the expectations of every
    test and failure weight bounded by `1`. -/
theorem RefinesUpTo.wpEF_le_add
    (H : RefinesUpTo ε Lean.Order.top (heapConc eqPre) (fun e => e) c a (indRel Eq))
    {q : α → Heap → ℝ≥0∞} (hq : ∀ x h, q x h ≤ 1) {e : ℝ≥0∞} (he : e ≤ 1) (h : Heap) :
    wpEF a q e h ≤ wpEF c q e h + ε := by
  have h1 := refinesUpTo_top_iff.1 H q e hq he h
  rw [post_heapConc_eqPre_indRel_eq hq] at h1
  exact (le_iSup₂_of_le h rfl le_rfl).trans h1

/-- **One direction of refinement bounds both differences**: the reverse inequality is the
    given one at the complement of the test and failure weight `1`. -/
theorem RefinesUpTo.absDiff_prTrue_le
    (H : RefinesUpTo ε Lean.Order.top (heapConc eqPre) (fun e => e) c a (indRel Eq))
    (D : α → SPComp Bool) (h : Heap) :
    absDiff (prTrue (SPComp.bind c D) h) (prTrue (SPComp.bind a D) h) ≤ ε := by
  simp only [prTrue_bind_eq_wpEF]
  set q : α → Heap → ℝ≥0∞ := fun x s => prTrue (D x) s
  have hq : ∀ x s, q x s ≤ 1 := fun x s => prTrue_le_one (D x) s
  refine max_le (tsub_le_iff_left.2 ?_) (tsub_le_iff_left.2 (H.wpEF_le_add hq zero_le h))
  have hcompl := H.wpEF_le_add (q := fun x s => 1 - q x s) (fun _ _ => tsub_le_self) le_rfl h
  have hne : wpEF c (fun x s => 1 - q x s) 1 h ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (wpEF_le_one c (fun _ _ => tsub_le_self) le_rfl h)
  refine (ENNReal.add_le_add_iff_left hne).1 ?_
  calc wpEF c (fun x s => 1 - q x s) 1 h + wpEF c q 0 h
      = wpEF a (fun x s => 1 - q x s) 1 h + wpEF a q 0 h := by
        rw [wpEF_compl_add c hq, wpEF_compl_add a hq]
    _ ≤ wpEF c (fun x s => 1 - q x s) 1 h + ε + wpEF a q 0 h := by gcongr
    _ = wpEF c (fun x s => 1 - q x s) 1 h + (wpEF a q 0 h + ε) := by ring

/-- **Refinement up to `ε` at equal heaps and equal results is a coupling of grade `ε`.** -/
theorem refinesUpTo_iff_rHoareApprox :
    RefinesUpTo ε Lean.Order.top (heapConc eqPre) (fun e => e) c a (indRel Eq) ↔
      rHoareApprox ε eqPre c a (couplingPost eqPre Eq) :=
  ⟨fun H => rHoareApprox_of_forall_absDiff H.absDiff_prTrue_le,
    fun h => refinesUpTo_of_rHoareApprox h _⟩

/-! ## Families of refinements -/

/-- The real family `G` refines the ideal family `F` up to `ε`, pointwise in the input, at equal
    heaps and equal results. The premise is equivalent to a coupling of grade `ε` at each input
    (`refinesUpTo_iff_rHoareApprox`). -/
class RefinesFamilyUpTo (G F : ι → SPComp α) (ε : ℝ≥0∞) : Prop where
  /-- The refinement at each input. -/
  refines : ∀ x, RefinesUpTo ε Lean.Order.top (heapConc eqPre) (fun e => e) (G x) (F x) (indRel Eq)

variable {G F : ι → SPComp α}

/-- A pointwise coupling of grade `ε` gives a family of refinements up to `ε`. -/
theorem RefinesFamilyUpTo.of_rHoareApprox
    (h : ∀ x, rHoareApprox ε eqPre (G x) (F x) (couplingPost eqPre Eq)) :
    RefinesFamilyUpTo G F ε :=
  ⟨fun x => refinesUpTo_of_rHoareApprox (h x) _⟩

/-- A family of refinements up to `ε` is symmetric, as the statistical distance is. -/
theorem RefinesFamilyUpTo.symm (h : RefinesFamilyUpTo G F ε) : RefinesFamilyUpTo F G ε :=
  .of_rHoareApprox fun x => rHoareApprox_of_forall_absDiff fun D s =>
    (absDiff_comm _ _).trans_le ((h.refines x).absDiff_prTrue_le D s)

/-- A family of refinements up to `ε` has statistical distance at most `ε`. -/
theorem RefinesFamilyUpTo.sdist_le [h : RefinesFamilyUpTo G F ε] : sdist G F ≤ ε :=
  iSup_le fun D => iSup₂_le fun x s => (h.refines x).absDiff_prTrue_le D s

/-- A family of refinements up to `ε` bounds the advantage at each input by `ε`. -/
theorem RefinesFamilyUpTo.advantageA_le [h : RefinesFamilyUpTo G F ε] (x : ι)
    (D : α → SPComp Bool) : AdvantageA (G x) (F x) D ≤ ε :=
  rHoareApprox_advantageA (refinesUpTo_iff_rHoareApprox.1 (h.refines x)) D

/-- **The game bound of a refinement**: with `PureGame` on both games,
    `ucFromGameC_of_pure_adv` then gives `UCFromGameC`, a game hop with the identity
    simulator. -/
instance instGameAdvBoundCOfRefines [RefinesFamilyUpTo G F ε] :
    GameAdvBoundC G F (fun _ _ => ε) :=
  ⟨RefinesFamilyUpTo.advantageA_le⟩

end CatCrypt.Refinement.WRP

namespace UCMonad.ProtMorε

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Refinement.WRP
open scoped ENNReal

/-- **The approximate 2-cell of a simulator and a refinement**: the real protocol `Q.prot`
    refines `P.prot` followed by `sim` on the interface up to `ε`. The opposite orientation of
    the premise is `RefinesFamilyUpTo.symm`. -/
noncomputable def ofRefines {hon out : Type} {P Q : ProtObj SPComp hon out} {ε : ℝ≥0∞}
    (sim : P.iface → SPComp Q.iface)
    [h : RefinesFamilyUpTo Q.prot (fun x => P.prot x >>= UCMonadBase.ucMapSum pure sim) ε] :
    ProtMorε P Q ε where
  sim := sim
  dist := (sdist_sym _ _).trans_le h.sdist_le

end UCMonad.ProtMorε

namespace CatCrypt.Refinement.WRP

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Unary CatCrypt.Crypto RefinementWP
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCDSL CatCrypt.Crypto.UCComposition
open scoped ENNReal

/-! ## Instances of the hypotheses -/

/-- A computation is coupled with itself at grade `0`, at equal heaps and equal results. -/
theorem rHoareApprox_zero_eqPre_refl {α : Type} (c : SPComp α) :
    rHoareApprox 0 eqPre c c (couplingPost eqPre Eq) :=
  rHoareApprox_of_rHoare (rHoare_mono_post (rHoare_refl c) fun _ _ _ _ h => ⟨h.1, h.2⟩)

/-- A computation refines itself exactly at equal heaps and equal results, an instance of
    `refines_of_rHoareApprox_zero`. -/
theorem refines_heapConc_eqPre_refl {α : Type} (c : SPComp α) :
    Refines Lean.Order.top (heapConc eqPre) (fun e : ℝ≥0∞ => e) c c (retRel Eq) :=
  refines_of_rHoareApprox_zero (rHoareApprox_zero_eqPre_refl c)

end CatCrypt.Refinement.WRP
