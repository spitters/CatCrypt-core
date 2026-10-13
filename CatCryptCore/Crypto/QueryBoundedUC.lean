/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MonadCostModel
public import CatCryptCore.Crypto.CompUCEquivalence

/-!
# Query-bounded computational UC for `SPComp`

The trivial `UCMonadCompDist SPComp` instance (`UCAdmClass/SPCompInstance.lean`) uses
`adm = fun _ => True`, so its `ucCdist` collapses to `ucSdist` (the information-theoretic
reading). This file makes the computational distance **concrete** by pairing the genuine
query-bounded admissibility class `spTreeQueryAdm` (`MonadCostModel.lean`) with the
per-distinguisher decomposition of that same trivial instance.

## The query-bounded compdist

`queryBoundedCompDist : UCMonadCompDist SPComp` reuses the trivial instance's
per-distinguisher structure (`ucDistComp`, the metric fields, `ucSdist_eq_iSup_distComp`)
**verbatim** and swaps only the admissibility fields for `spTreeQueryAdm`'s. It is a `def`
(not an `instance`) to avoid a diamond with the already-registered trivial
`instance : UCMonadCompDist SPComp`. Its `adm` is *definitionally* `spTreeQueryAdm.adm`
(`queryBoundedCompDist_adm_iff`), i.e. "has a syntax-tree witness with uniformly bounded
query cost" — a genuine (non-trivial) class, not `True`.

## The equivalences at the query-bounded compdist

`dummy_completeness_cdist`, `ucEmulatesCdist_iff_dummy`, and
`ccConstructsCdist_iff_ucEmulatesCdist` are generic over `[UCMonadCompDist T]`; supplying
`queryBoundedCompDist` explicitly gives concrete `SPComp` statements in which the quantified
adversaries `A` range over **query-bounded** (`spTreeQueryAdm.adm`) arrows only. These are
`queryBounded_dummy_completeness_cdist`, `queryBounded_ucEmulatesCdist_iff_dummy`,
`queryBounded_ccConstructsCdist_iff_ucEmulatesCdist`.

## No separation for output differences

A strict `ucCdist queryBoundedCompDist f g < ucSdist f g` is **not** achievable via this
admissibility class, and the reason is structural: `ucCdist` restricts the distinguisher
`D`, but the query cost of `spTreeQueryAdm` bounds `D`'s *own* sampling/state operations,
not its ability to *threshold the received output*. Every "pure predicate test"
`fun b => SPComp.pure (p b)` has query cost `0`, hence is admissible
(`adm_pure_predicate`), and such tests already realise the statistical distance (the
received output is a sufficient statistic; thresholding it is optimal — the data-processing
inequality). On the canonical separating pair `Example.π` / `Example.F` we prove this
concretely: a query-`0` distinguisher achieves advantage `1`, so
`ucCdist queryBoundedCompDist π F = ucSdist π F = 1` (`ex_queryBounded_ucCdist_eq_one`,
`ex_queryBounded_no_separation`) — no gap.

A genuine `ucCdist < ucSdist` would need a pair whose *optimal* distinguisher has
**unbounded per-output-value query cost** (no uniformly bounded `SPTree` witness), together
with a query-complexity lower bound showing every uniformly-query-bounded `D` is strictly
worse. A computational gap in the
cryptographic sense requires restricting the distinguisher's *output post-processing*
(circuit size / PRG-style hardness), which `SPTree.queryCost` does not model; the size
model of `SizeBoundedUC.lean` does.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.QueryBoundedUC

open UCMonad
open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.CompUCEquivalence
open scoped ENNReal

/-! ## Section 1: The query-bounded compdist -/

/-- **The query-bounded per-distinguisher compdist on `SPComp`.**

    Everything except admissibility is inherited verbatim from the trivial
    `UCMonadCompDist SPComp` instance (`ucDistComp`, `ucSdist_eq_iSup_distComp`, the metric
    and structural fields); only the five `adm*` fields are swapped for `spTreeQueryAdm`'s
    query-bounded class. Kept a `def` (not `instance`) to avoid a diamond with the
    registered trivial instance. -/
@[reducible] noncomputable def queryBoundedCompDist : UCMonadCompDist SPComp :=
  { (inferInstance : UCMonadCompDist SPComp) with
    adm := spTreeQueryAdm.adm
    adm_pure := spTreeQueryAdm.adm_pure
    adm_bind := spTreeQueryAdm.adm_bind
    adm_mapSum := spTreeQueryAdm.adm_mapSum
    adm_precomp := spTreeQueryAdm.adm_precomp }

/-- The admissibility of `queryBoundedCompDist` is *definitionally* the query-bounded class
    `spTreeQueryAdm`: an arrow is admissible iff it has a syntax-tree family with uniformly
    bounded query cost. This is the non-triviality witness — it is not `fun _ => True`. -/
theorem queryBoundedCompDist_adm_iff {α β : Type} (f : α → SPComp β) :
    adm (self := queryBoundedCompDist.toUCAdmClass) f ↔
      ∃ (s : α → SPTree β),
        (∀ a, (s a).compile = f a) ∧ ∃ n, ∀ a, (s a).queryCost ≤ n :=
  Iff.rfl

/-- The `adm` field of `queryBoundedCompDist` equals `spTreeQueryAdm`'s on the nose. -/
theorem queryBoundedCompDist_adm_eq {α β : Type} (f : α → SPComp β) :
    adm (self := queryBoundedCompDist.toUCAdmClass) f
      = adm (self := spTreeQueryAdm) f := rfl

/-! ## Section 2: The equivalences at `queryBoundedCompDist`

Each statement below is the generic `CompUCEquivalence` theorem specialised to
`SPComp` with `queryBoundedCompDist` supplied explicitly. The `UCEmulatesCdist`/
`EmulatesDummyCdist` predicates unfold with `adm = spTreeQueryAdm.adm`, so the quantified
adversaries `A` are exactly the **query-bounded** arrows. -/

/-- **Query-bounded computational dummy-adversary completeness.** Emulation against the
    dummy adversary implies computational UC emulation against every **query-bounded**
    adversary and every environment view. -/
theorem queryBounded_dummy_completeness_cdist
    {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if))
    (h : @EmulatesDummyCdist SPComp queryBoundedCompDist ε hon out leak sim_if π F) :
    ∀ view : Type,
      @UCEmulatesCdist SPComp queryBoundedCompDist ε hon out leak sim_if view π F :=
  @dummy_completeness_cdist SPComp queryBoundedCompDist hon out leak sim_if ε π F h

/-- **Query-bounded computational dummy-adversary theorem** (equivalence over all views).
    The nontrivial direction is the absorption argument, which needs `adm A` — here
    `A` query-bounded — discharged through `spTreeQueryAdm.adm_mapSum spTreeQueryAdm.adm_pure`. -/
theorem queryBounded_ucEmulatesCdist_iff_dummy
    {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if)) :
    (∀ view : Type,
        @UCEmulatesCdist SPComp queryBoundedCompDist ε hon out leak sim_if view π F)
      ↔ @EmulatesDummyCdist SPComp queryBoundedCompDist ε hon out leak sim_if π F :=
  @ucEmulatesCdist_iff_dummy SPComp queryBoundedCompDist hon out leak sim_if ε π F

/-- **Query-bounded computational CC ⟺ UC.** A Maurer–Renner construction within `ε` in the
    query-bounded-distinguisher distance is exactly computational UC emulation within `ε`
    against every **query-bounded** adversary and every view. -/
theorem queryBounded_ccConstructsCdist_iff_ucEmulatesCdist
    {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if)) :
    @CCConstructsCdist SPComp queryBoundedCompDist ε hon out leak sim_if π F ↔
      ∀ view : Type,
        @UCEmulatesCdist SPComp queryBoundedCompDist ε hon out leak sim_if view π F :=
  @ccConstructsCdist_iff_ucEmulatesCdist SPComp queryBoundedCompDist hon out leak sim_if ε π F

/-! ## Section 3: The separation question

The query cost bounds the distinguisher's own operations, not its power to threshold the
received output. Pure predicate tests have query cost `0`, are therefore admissible, and
already saturate the statistical distance — so no strict separation arises. We prove this
concretely on the canonical separating pair. -/

/-- **Every pure predicate test is query-bounded-admissible** (query cost `0`). This is the
    structural obstruction to a distinguisher-side separation: the class that `ucCdist`
    ranges over already contains all output-thresholding distinguishers. -/
theorem adm_pure_predicate {β : Type} (p : β → Bool) :
    adm (self := queryBoundedCompDist.toUCAdmClass) (fun b => SPComp.pure (p b)) :=
  ⟨fun b => SPTree.ret (p b), fun _ => rfl, 0, fun _ => Nat.le_refl 0⟩

/-- The canonical separating distinguisher (reads the leaked bit off the `.inr` channel),
    written as a pure predicate test so it is manifestly query-bounded. -/
noncomputable def exD : (Unit ⊕ Bool) → SPComp Bool :=
  fun x => SPComp.pure (Sum.elim (fun _ => false) id x)

/-- `exD` is query-bounded-admissible. -/
theorem exD_adm : adm (self := queryBoundedCompDist.toUCAdmClass) exD :=
  adm_pure_predicate (Sum.elim (fun _ => false) id)

/-- The query-`0` distinguisher `exD` separates the real leak `true` from the ideal leak
    `false` with advantage `1`. -/
theorem exD_advantage_one :
    absDiff (prTrue (SPComp.bind (Example.π ()) exD) Heap.empty)
            (prTrue (SPComp.bind (Example.F ()) exD) Heap.empty) = 1 := by
  have h1 : SPComp.bind (Example.π ()) exD = SPComp.pure true := by
    simp [Example.π, exD, SPComp.pure_bind, Sum.elim_inr]
  have h2 : SPComp.bind (Example.F ()) exD = SPComp.pure false := by
    simp [Example.F, exD, SPComp.pure_bind, Sum.elim_inr]
  rw [h1, h2, ForkingLemma.prTrue_pure_bool, ForkingLemma.prTrue_pure_bool]
  simp [absDiff]

/-- The query-bounded computational distance on the canonical pair is at least `1`:
    the admissible query-`0` distinguisher `exD` already achieves advantage `1`. -/
theorem ex_queryBounded_ucCdist_ge_one :
    (1 : ℝ≥0∞) ≤
      @ucCdist SPComp queryBoundedCompDist Unit (Unit ⊕ Bool) Example.π Example.F := by
  refine le_iSup₂_of_le exD exD_adm ?_
  show (1 : ℝ≥0∞) ≤ ⨆ (a : Unit) (h₀ : Heap),
      absDiff (prTrue (SPComp.bind (Example.π a) exD) h₀)
              (prTrue (SPComp.bind (Example.F a) exD) h₀)
  exact le_iSup₂_of_le () Heap.empty (le_of_eq exD_advantage_one.symm)

/-- The statistical distance on the canonical pair is at most `1` (each per-distinguisher
    advantage is a difference of probabilities in `[0,1]`). -/
theorem ex_ucSdist_le_one :
    UCMonadMetric.ucSdist (self := queryBoundedCompDist.toUCMonadMetric)
        Example.π Example.F ≤ 1 := by
  show sdist Example.π Example.F ≤ 1
  refine iSup_le (fun D => iSup_le (fun a => iSup_le (fun h₀ => ?_)))
  simp only [absDiff]
  exact sup_le (le_trans tsub_le_self (prTrue_le_one _ _))
               (le_trans tsub_le_self (prTrue_le_one _ _))

/-- **No distinguisher-side separation on the canonical pair.** The query-bounded
    computational distance equals the statistical distance: both are `1`, and the value is
    realised by the query-`0` distinguisher `exD`. -/
theorem ex_queryBounded_no_separation :
    @ucCdist SPComp queryBoundedCompDist Unit (Unit ⊕ Bool) Example.π Example.F
      = UCMonadMetric.ucSdist (self := queryBoundedCompDist.toUCMonadMetric)
          Example.π Example.F :=
  le_antisymm
    (@ucCdist_le_ucSdist SPComp queryBoundedCompDist Unit (Unit ⊕ Bool)
      Example.π Example.F)
    (le_trans ex_ucSdist_le_one ex_queryBounded_ucCdist_ge_one)

/-- The query-bounded computational distance on the canonical pair is exactly `1`. -/
theorem ex_queryBounded_ucCdist_eq_one :
    @ucCdist SPComp queryBoundedCompDist Unit (Unit ⊕ Bool) Example.π Example.F = 1 :=
  le_antisymm
    (le_trans
      (@ucCdist_le_ucSdist SPComp queryBoundedCompDist Unit (Unit ⊕ Bool)
        Example.π Example.F)
      ex_ucSdist_le_one)
    ex_queryBounded_ucCdist_ge_one

end CatCrypt.Crypto.QueryBoundedUC
