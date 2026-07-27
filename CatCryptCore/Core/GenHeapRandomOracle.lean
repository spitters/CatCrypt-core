/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.GenHeap
import CatCryptCore.Relational.Rules

/-!
# Lazily-Sampled Random Oracle with a Heap-Resident Query Log

A random oracle whose query log lives in a single heap cell at a `GLocation`. The
log is an association list, so it grows by one entry per fresh query; its type
`List (D × R)` carries no `Fintype` instance and therefore cannot be the value type
of a `CatCrypt.Core.Location`.

Because the log is state rather than a threaded argument, the oracle has type
`SPComp R` — the type of any other stateful computation — so it can be composed
with, and handed to, an arbitrary `SPComp` adversary.

## Main definitions

* `logFind` — lookup in a query log
* `logLoc` — the heap cell holding the log
* `query` — the lazily-sampled oracle
* `program` — reprogram the oracle at one point

## Main results

* `query_apply_cached` — a repeated query is deterministic and leaves the log alone
* `query_apply_fresh` — a fresh query samples uniformly and appends one entry
* `query_answer_uniform` — the answer to a fresh query is uniform on `R`,
  whatever the log holds
* `query_consistent` — two successive queries on the same point agree
* `query_after_program` — a programmed point answers with the programmed value
* `preservesOutside_query` — the oracle writes only its own cell
* `msgLog_no_fintype` — the log type of a random oracle on arbitrary-length bit
  strings is not finite
-/

open scoped Classical

namespace CatCrypt.Core.RandomOracle

open CatCrypt.Prob CatCrypt.Relational

/-! ## Query logs -/

/-- Query log: an association list of query/response pairs. -/
abbrev Log (D R : Type) := List (D × R)

/-- Lookup in a query log; the leftmost entry for `x` wins. -/
def logFind {D R : Type} [DecidableEq D] (x : D) : Log D R → Option R
  | [] => none
  | (y, r) :: t => if y = x then some r else logFind x t

@[simp] theorem logFind_nil {D R : Type} [DecidableEq D] (x : D) :
    logFind x ([] : Log D R) = none := rfl

@[simp] theorem logFind_cons_self {D R : Type} [DecidableEq D] (x : D) (r : R) (T : Log D R) :
    logFind x ((x, r) :: T) = some r := by simp [logFind]

theorem logFind_cons_of_ne {D R : Type} [DecidableEq D] {x y : D} (hne : y ≠ x) (r : R)
    (T : Log D R) : logFind x ((y, r) :: T) = logFind x T := by simp [logFind, hne]

/-! ## The oracle -/

variable (D R : Type) [DecidableEq D] [Countable D] [Fintype R] [Nonempty R]

/-- Heap cell holding the random-oracle log. -/
@[reducible] def logLoc (id : Nat) : GLocation := { id := id, ty := Log D R }

/-- One oracle step, given the current log: return the cached answer, or sample a
fresh one and append it. -/
noncomputable def queryStep (id : Nat) (x : D) (T : Log D R) : SPComp R :=
  match logFind x T with
  | some r => SPComp.pure r
  | none =>
      SPComp.bind (SPComp.sample R) fun r =>
        SPComp.bind (SPComp.gset (logLoc D R id) ((x, r) :: T)) fun _ =>
          SPComp.pure r

/-- The lazily-sampled random oracle: read the log from the heap, answer, write back. -/
noncomputable def query (id : Nat) (x : D) : SPComp R :=
  SPComp.bind (SPComp.gget (logLoc D R id)) (queryStep D R id x)

theorem queryStep_of_cached {id : Nat} {x : D} {T : Log D R} {r : R}
    (hc : logFind x T = some r) : queryStep D R id x T = SPComp.pure r := by
  simp only [queryStep, hc]

theorem queryStep_of_fresh {id : Nat} {x : D} {T : Log D R} (hc : logFind x T = none) :
    queryStep D R id x T =
      SPComp.bind (SPComp.sample R) (fun r =>
        SPComp.bind (SPComp.gset (logLoc D R id) ((x, r) :: T)) fun _ => SPComp.pure r) := by
  simp only [queryStep, hc]

theorem query_apply (id : Nat) (x : D) (h : Heap) :
    query D R id x h = queryStep D R id x (h.gget (logLoc D R id)) h := by
  simp only [query, SPComp.bind, SPComp.gget, SDistr.pure_bind]

/-! ### A cached query is deterministic -/

/-- A query already in the log is answered from the log, leaving the heap untouched. -/
theorem query_apply_cached (id : Nat) (x : D) (h : Heap) (r : R)
    (hc : logFind x (h.gget (logLoc D R id)) = some r) :
    query D R id x h = SDistr.pure (r, h) := by
  simp only [query_apply, queryStep_of_cached D R hc, SPComp.pure]

/-! ### A fresh query samples uniformly -/

/-- A query absent from the log samples uniformly on `R` and appends one entry. -/
theorem query_apply_fresh (id : Nat) (x : D) (h : Heap)
    (hc : logFind x (h.gget (logLoc D R id)) = none) :
    query D R id x h =
      (SDistr.uniform R).bind (fun r =>
        SDistr.pure (r, h.gset (logLoc D R id) ((x, r) :: h.gget (logLoc D R id)))) := by
  simp only [query_apply, queryStep_of_fresh D R hc, SPComp.bind, SPComp.sample, SPComp.gset,
    SPComp.pure, SDistr.bind_assoc, SDistr.pure_bind]

/-- The answer to a fresh query is uniform on `R`, independently of the log contents.
This is the marginal of `query` on its result component. -/
theorem query_answer_uniform (id : Nat) (x : D) (h : Heap)
    (hc : logFind x (h.gget (logLoc D R id)) = none) :
    (query D R id x h).bind (fun p => SDistr.pure p.1) = SDistr.uniform R := by
  simp only [query_apply_fresh D R id x h hc, SDistr.bind_assoc, SDistr.pure_bind,
    SDistr.bind_pure]

/-- Every query is fresh on the empty heap, so the freshness hypothesis of
`query_answer_uniform` is satisfiable. -/
theorem query_empty_uniform (id : Nat) (x : D) :
    (query D R id x Heap.empty).bind (fun p => SDistr.pure p.1) = SDistr.uniform R :=
  query_answer_uniform D R id x Heap.empty (by rw [Heap.gget_empty]; rfl)

/-- Two heaps on which `x` is fresh give the same answer distribution: the marginal
does not depend on the log. -/
theorem query_answer_uniform_indep (id : Nat) (x : D) (h₁ h₂ : Heap)
    (hc₁ : logFind x (h₁.gget (logLoc D R id)) = none)
    (hc₂ : logFind x (h₂.gget (logLoc D R id)) = none) :
    (query D R id x h₁).bind (fun p => SDistr.pure p.1) =
      (query D R id x h₂).bind (fun p => SDistr.pure p.1) := by
  rw [query_answer_uniform D R id x h₁ hc₁, query_answer_uniform D R id x h₂ hc₂]

/-! ### The log makes the oracle consistent -/

omit [Nonempty R] in
/-- After a fresh query, the point is cached: the freshly written log answers `x`. -/
theorem logFind_after_fresh (id : Nat) (x : D) (r : R) (h : Heap) :
    logFind x ((h.gset (logLoc D R id) ((x, r) :: h.gget (logLoc D R id))).gget
      (logLoc D R id)) = some r := by
  simp only [Heap.gget_gset_same, logFind_cons_self]

/-- Querying the same point twice returns the same value. The second query reads the
entry the first one wrote, so this holds on every heap. -/
theorem query_consistent (id : Nat) (x : D) :
    SPComp.bind (query D R id x) (fun r₁ =>
      SPComp.bind (query D R id x) (fun r₂ => SPComp.pure (r₁, r₂))) =
    SPComp.bind (query D R id x) (fun r => SPComp.pure (r, r)) := by
  funext h
  simp only [SPComp.bind]
  cases hc : logFind x (h.gget (logLoc D R id)) with
  | some r =>
      rw [query_apply_cached D R id x h r hc, SDistr.pure_bind, SDistr.pure_bind,
        query_apply_cached D R id x h r hc, SDistr.pure_bind]
  | none =>
      rw [query_apply_fresh D R id x h hc, SDistr.bind_assoc, SDistr.bind_assoc]
      exact congrArg _ (funext fun r => by
        rw [SDistr.pure_bind, SDistr.pure_bind,
          query_apply_cached D R id x _ r (logFind_after_fresh D R id x r h), SDistr.pure_bind])

/-! ### Programming the oracle -/

/-- Reprogram the oracle at `x` to answer `r`. -/
noncomputable def program (id : Nat) (x : D) (r : R) : SPComp Unit :=
  SPComp.bind (SPComp.gget (logLoc D R id)) fun T =>
    SPComp.gset (logLoc D R id) ((x, r) :: T)

/-- A programmed point answers with the programmed value. -/
theorem query_after_program (id : Nat) (x : D) (r : R) :
    SPComp.bind (program D R id x r) (fun _ => query D R id x) =
    SPComp.bind (program D R id x r) (fun _ => SPComp.pure r) := by
  funext h
  simp only [SPComp.bind, program, SPComp.gget, SPComp.gset, SDistr.pure_bind,
    query_apply_cached D R id x _ r (logFind_after_fresh D R id x r h), SPComp.pure]

omit [Nonempty R] in
/-- Programming a point the oracle has not yet been asked about does not change the
answers already fixed at other points. -/
theorem logFind_program_of_ne (id : Nat) {x y : D} (hne : x ≠ y) (r : R) (h : Heap) :
    logFind y ((h.gset (logLoc D R id) ((x, r) :: h.gget (logLoc D R id))).gget
      (logLoc D R id)) = logFind y (h.gget (logLoc D R id)) := by
  simp only [Heap.gget_gset_same, logFind_cons_of_ne hne]

/-! ### Footprint -/

/-- Monotonicity of `PreservesOutside` in the footprint. -/
theorem preservesOutside_mono {α : Type} {c : SPComp α} {L L' : LocSet}
    (hc : PreservesOutside c L) (hsub : L ⊆ L') : PreservesOutside c L' :=
  fun h a h' hne id hnotin => hc h a h' hne id fun hmem => hnotin (hsub hmem)

/-- The oracle writes only its own cell. -/
theorem preservesOutside_query (id : Nat) (x : D) :
    PreservesOutside (query D R id x) {id} := by
  refine preservesOutside_mono
    (preservesOutside_bind (preservesOutside_gget (logLoc D R id)) (fun T => ?_))
    (by simp : (∅ : LocSet) ∪ {id} ⊆ {id})
  cases hc : logFind x T with
  | some r =>
      rw [queryStep_of_cached D R hc]
      exact preservesOutside_mono (preservesOutside_pure r) (Finset.empty_subset _)
  | none =>
      rw [queryStep_of_fresh D R hc]
      exact preservesOutside_mono
        (preservesOutside_bind (preservesOutside_sample R) fun r =>
          preservesOutside_mono
            (preservesOutside_bind (preservesOutside_gset (logLoc D R id) ((x, r) :: T))
              (fun _ => preservesOutside_pure r))
            (by simp : ({id} : LocSet) ∪ ∅ ⊆ {id}))
        (by simp : (∅ : LocSet) ∪ {id} ⊆ {id})

/-! ### pRHL

The judgment is `CatCrypt.Relational.rHoare` over the same two `Heap`s as for any
other computation, and the core frame rule applies to the oracle unchanged. -/

/-- The reprogramming step as a pRHL judgment: after programming `x` to `r`, the
oracle and the constant `r` are related on equal heaps. -/
theorem rHoare_query_after_program (id : Nat) (x : D) (r : R) :
    rHoare eqPre
      (SPComp.bind (program D R id x r) (fun _ => query D R id x))
      (SPComp.bind (program D R id x r) (fun _ => SPComp.pure r))
      eqPost := by
  rw [query_after_program D R id x r]
  exact rHoare_refl _

/-- The core frame rule applies to the oracle: an assertion about a finite-typed
location at a different id survives the oracle's step. -/
theorem rHoare_query_frame (id : Nat) (x : D) (l : Location) (v : l.ty) (hne : l.id ≠ id) :
    rHoare (eqPre ⋀ leftHas l v) (query D R id x) (query D R id x)
      (fun a h₁ b h₂ => eqPost a h₁ b h₂ ∧ leftHas l v h₁ h₂) :=
  r_frame_local (preservesOutside_query D R id x) (preservesOutside_query D R id x)
    (dependsOn_leftHas l v) (Finset.disjoint_singleton.mpr (Ne.symm hne)) (rHoare_refl _)

end CatCrypt.Core.RandomOracle

/-! ## The log type is outside the range of `Location`

A random oracle on arbitrary-length bit strings is the shape FDH and Fiat–Shamir
need. Neither its log type nor its domain is finite, so neither can be the value
type of a `CatCrypt.Core.Location`. -/

namespace CatCrypt.Core.RandomOracle

/-- For a finite query domain the *total* table `D → Option R` is itself finite, so a
bounded-domain oracle table is already a legal `Location` value type. The cases the
`Fintype` bound excludes are the log-shaped state and the unbounded query domain. -/
def boundedTableLoc (D R : Type) [Fintype D] [DecidableEq D] [Fintype R] (id : Nat) :
    Location := { id := id, ty := D → Option R }

/-- `BitVec w` is equivalent to `Fin (2 ^ w)`. This toolchain's Mathlib ships no
`Fintype (BitVec w)` instance. -/
local instance instFintypeBitVec (w : Nat) : Fintype (BitVec w) :=
  Fintype.ofEquiv (Fin (2 ^ w))
    { toFun := BitVec.ofFin, invFun := BitVec.toFin,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }

/-- Log of a random oracle from arbitrary-length bit strings to 256-bit digests. -/
abbrev MsgLog := Log (List Bool) (BitVec 256)

theorem msgLog_no_fintype : ¬ Nonempty (Fintype MsgLog) := fun ⟨_⟩ => not_finite MsgLog

theorem msgDomain_no_fintype : ¬ Nonempty (Fintype (List Bool)) :=
  fun ⟨_⟩ => not_finite (List Bool)

/-- The heap cell for that oracle's log. -/
@[reducible] def msgLogLoc (id : Nat) : GLocation := logLoc (List Bool) (BitVec 256) id

/-- The oracle on arbitrary-length bit strings. -/
noncomputable def msgQuery (id : Nat) (x : List Bool) : SPComp (BitVec 256) :=
  query (List Bool) (BitVec 256) id x

theorem msgQuery_consistent (id : Nat) (x : List Bool) :
    SPComp.bind (msgQuery id x) (fun r₁ =>
      SPComp.bind (msgQuery id x) (fun r₂ => SPComp.pure (r₁, r₂))) =
    SPComp.bind (msgQuery id x) (fun r => SPComp.pure (r, r)) :=
  query_consistent (List Bool) (BitVec 256) id x

end CatCrypt.Core.RandomOracle
