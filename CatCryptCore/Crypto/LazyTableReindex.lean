/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleSimulation

/-!
# Lazily sampled tables read through a re-indexing

A simulation of a random oracle `H : J → V` often stores the table of `H` in two lazily
sampled tables: points `q` with `sel q` are stored in a table `A : I → Option V` at the
re-indexed point `π q`, the other points in a table `B : J → Option V` at `q` itself. The
represented table of `H` is `reindexTable sel π A B`. When `π` is injective on the selected
points, a lazy read of `A` at `π j` (for a selected `j`) or of `B` at `j` (for an
unselected `j`) is a lazy read of the represented table at `j`, step by step; the run form
follows from `OracleAdv.run_map_state`. The FO transform with implicit rejection, the
DH-based KEM of HPKE and the ML-KEM proof instantiate it with the decryption, the DH and
the re-encryption selectors.

No eager table is involved: both sides sample lazily, and the re-indexing is a bijection of
lazy tables on the queried points, unlike the eager/lazy statements of `EagerLazyRF` and
`OracleLazyMulti`.

## Main definitions

* `lazyRead tab i set w g` — a lazy read of `tab` at `i` as a distribution over the answer,
  the state `set tab'` with the updated table and a ghost state `g`
* `reindexTable sel π A B` — the table read from `A` at `π q` on selected points and from
  `B` at `q` otherwise

## Main results

* `lazyRead_eq` — a lazy read is the random oracle on the table with the state mapped
* `roOracle_map_eq` — two lazy reads with equal values and related updates agree
* `reindexTable_update_left`, `reindexTable_update_left_of_forall`,
  `reindexTable_update_right` — storing in `A` or `B` stores in the represented table
* `lazyRead_map_reindex_left`, `lazyRead_map_reindex_right` — a lazy read of `A` at `π j`
  or of `B` at `j` is the random oracle on the represented table at `j`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

/-! ## Lazy reads with a ghost state -/

section LazyRead

variable {I V S G A : Type} [DecidableEq I] [Fintype V] [Nonempty V]

/-- Answer from the table `tab` at `i` with ghost state `g`, sampling and recording a
fresh value; `set` stores the table back into the state and `w` shapes the answer. -/
noncomputable def lazyRead (tab : I → Option V) (i : I) (set : (I → Option V) → S)
    (w : V → A) (g : G) : PMF (A × (S × G)) :=
  match tab i with
  | some v => PMF.pure (w v, (set tab, g))
  | none => (PMF.uniformFintype V).map fun v =>
      (w v, (set (Function.update tab i (some v)), g))

/-- A lazy read is the random oracle on the table, with the table stored back. -/
theorem lazyRead_eq (tab : I → Option V) (i : I) (set : (I → Option V) → S) (w : V → A)
    (g : G) : lazyRead tab i set w g = (roOracle tab i).map fun x => (w x.1, (set x.2, g)) := by
  unfold lazyRead roOracle
  cases tab i <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def]

theorem lazyRead_map_ghost {G' : Type} (φ : G → G') (tab : I → Option V) (i : I)
    (set : (I → Option V) → S) (w : V → A) (g : G) :
    (lazyRead tab i set w g).map (Prod.map id (Prod.map id φ)) = lazyRead tab i set w (φ g) := by
  unfold lazyRead; split <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def]

theorem lazyRead_map_const {G' : Type} (tab : I → Option V) (i : I) (set : (I → Option V) → S)
    (w : V → A) (g : G) (g' : G') :
    (lazyRead tab i set w g).map (fun y => (y.1, (y.2.1, g'))) = lazyRead tab i set w g' := by
  unfold lazyRead; split <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def]

theorem lazyRead_apply_ghost_ne (tab : I → Option V) (i : I) (set : (I → Option V) → S)
    (w : V → A) (g : G) (a : A) (s : S) (g' : G) (h : g ≠ g') :
    lazyRead tab i set w g (a, (s, g')) = 0 := by
  unfold lazyRead; split
  · simp [PMF.pure_apply, Ne.symm h]
  · rw [PMF.map_apply]; simp [Ne.symm h]

theorem mem_support_lazyRead_ghost {tab : I → Option V} {i : I} {set : (I → Option V) → S}
    {w : V → A} {g : G} {x : A × (S × G)} (hx : x ∈ (lazyRead tab i set w g).support) :
    x.2.2 = g := by
  by_contra h
  obtain ⟨a, s, g'⟩ := x
  exact (PMF.mem_support_iff _ _).mp hx (lazyRead_apply_ghost_ne _ _ _ _ _ _ _ _ (Ne.symm h))

/-- A lazy read leaves every function of the state that ignores the table unchanged. -/
theorem eq_of_mem_support_lazyRead {T : Type} (proj : S → T) {tab : I → Option V} {i : I}
    {set : (I → Option V) → S} (hset : ∀ t, proj (set t) = proj (set tab)) {w : V → A} {g : G}
    {x : A × (S × G)} (hx : x ∈ (lazyRead tab i set w g).support) :
    proj x.2.1 = proj (set tab) := by
  unfold lazyRead at hx; split at hx
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx; subst hx; rfl
  · simp only [PMF.support_map, Set.mem_image] at hx
    obtain ⟨v, _, rfl⟩ := hx
    exact hset _

end LazyRead

/-! ## Two lazy reads related by a map of states -/

/-- Two lazy reads with the same value and related updates give the same distribution
after mapping the state. -/
theorem roOracle_map_eq {I I' V S S' A : Type} [DecidableEq I] [DecidableEq I'] [Fintype V]
    [Nonempty V] (tab : I → Option V) (i : I) (tab' : I' → Option V) (i' : I')
    (F : V × (I → Option V) → A × S) (F' : V × (I' → Option V) → A × S') (φ : S → S')
    (hread : tab' i' = tab i) (h0 : ∀ v, Prod.map id φ (F (v, tab)) = F' (v, tab'))
    (h1 : ∀ v, Prod.map id φ (F (v, Function.update tab i (some v))) =
      F' (v, Function.update tab' i' (some v))) :
    ((roOracle tab i).map F).map (Prod.map id φ) = (roOracle tab' i').map F' := by
  unfold roOracle
  rw [hread]
  cases tab i with
  | some v => simp [PMF.pure_map, h0]
  | none =>
    simp only [PMF.map_comp, Function.comp_def]
    exact congrArg (fun F => PMF.map F _) (funext h1)

/-! ## The re-indexed table -/

section Reindex

variable {I J V : Type}

/-- The table read from `A` at `π q` when `sel q`, and from `B` at `q` otherwise. -/
def reindexTable (sel : J → Bool) (π : J → I) (A : I → Option V) (B : J → Option V) :
    J → Option V :=
  fun q => if sel q then A (π q) else B q

theorem reindexTable_of_sel {sel : J → Bool} {π : J → I} {A : I → Option V}
    {B : J → Option V} {q : J} (h : sel q = true) : reindexTable sel π A B q = A (π q) := by
  simp [reindexTable, h]

theorem reindexTable_of_not_sel {sel : J → Bool} {π : J → I} {A : I → Option V}
    {B : J → Option V} {q : J} (h : sel q = false) : reindexTable sel π A B q = B q := by
  simp [reindexTable, h]

variable [DecidableEq I] [DecidableEq J]

/-- Storing at `i` in `A` stores at `j` in the represented table, when `j` is the only
selected point over `i`. -/
theorem reindexTable_update_left (sel : J → Bool) (π : J → I) (A : I → Option V)
    (B : J → Option V) {i : I} {j : J} (hj : sel j = true) (hπ : π j = i)
    (hinj : ∀ q, sel q = true → π q = i → q = j) (v : Option V) :
    reindexTable sel π (Function.update A i v) B = Function.update (reindexTable sel π A B) j v := by
  funext q
  by_cases hq : q = j
  · subst hq; simp [reindexTable, hj, hπ]
  · rw [Function.update_of_ne hq]
    unfold reindexTable
    split_ifs with hs
    · exact Function.update_of_ne (fun h => hq (hinj q hs h)) _ _
    · rfl

omit [DecidableEq J] in
/-- Storing at `i` in `A` leaves the represented table unchanged, when no selected point
lies over `i`. -/
theorem reindexTable_update_left_of_forall (sel : J → Bool) (π : J → I) (A : I → Option V)
    (B : J → Option V) {i : I} (hi : ∀ q, sel q = true → π q ≠ i) (v : Option V) :
    reindexTable sel π (Function.update A i v) B = reindexTable sel π A B := by
  funext q
  unfold reindexTable
  split_ifs with hs
  · exact Function.update_of_ne (hi q hs) _ _
  · rfl

omit [DecidableEq I] in
/-- Storing at an unselected `j` in `B` stores at `j` in the represented table. -/
theorem reindexTable_update_right (sel : J → Bool) (π : J → I) (A : I → Option V)
    (B : J → Option V) {j : J} (hj : sel j = false) (v : Option V) :
    reindexTable sel π A (Function.update B j v) = Function.update (reindexTable sel π A B) j v := by
  funext q
  by_cases hq : q = j
  · subst hq; simp [reindexTable, hj]
  · rw [Function.update_of_ne hq]
    unfold reindexTable
    split_ifs
    · rfl
    · exact Function.update_of_ne hq _ _

variable [Fintype V] [Nonempty V] {S G W S' : Type}

/-- **Re-indexed lazy read, selected side.** When `π` is injective on the selected points
over `π j`, a lazy read of `A` at `π j` is the random oracle on the represented table at
`j`: mapping the state by `φ`, which reads the represented table from the stored `A`, turns
the read into `roOracle (reindexTable sel π A B) j` followed by `F`. -/
theorem lazyRead_map_reindex_left (sel : J → Bool) (π : J → I) (A : I → Option V)
    (B : J → Option V) {j : J} (hj : sel j = true)
    (hinj : ∀ q, sel q = true → π q = π j → q = j) (set : (I → Option V) → S) (w : V → W)
    (g : G) (φ : S × G → S') (F : V × (J → Option V) → W × S')
    (hφ : ∀ v t, (w v, φ (set t, g)) = F (v, reindexTable sel π t B)) :
    (lazyRead A (π j) set w g).map (Prod.map id φ) =
      (roOracle (reindexTable sel π A B) j).map F := by
  rw [lazyRead_eq]
  refine roOracle_map_eq _ _ _ _ _ _ _ (reindexTable_of_sel hj) (fun v => hφ v A) fun v => ?_
  rw [← reindexTable_update_left sel π A B hj rfl hinj]
  exact hφ v _

omit [DecidableEq I] in
/-- **Re-indexed lazy read, unselected side.** A lazy read of `B` at an unselected `j` is
the random oracle on the represented table at `j`. -/
theorem lazyRead_map_reindex_right (sel : J → Bool) (π : J → I) (A : I → Option V)
    (B : J → Option V) {j : J} (hj : sel j = false) (set : (J → Option V) → S) (w : V → W)
    (g : G) (φ : S × G → S') (F : V × (J → Option V) → W × S')
    (hφ : ∀ v t, (w v, φ (set t, g)) = F (v, reindexTable sel π A t)) :
    (lazyRead B j set w g).map (Prod.map id φ) =
      (roOracle (reindexTable sel π A B) j).map F := by
  rw [lazyRead_eq]
  refine roOracle_map_eq _ _ _ _ _ _ _ (reindexTable_of_not_sel hj) (fun v => hφ v B)
    fun v => ?_
  rw [← reindexTable_update_right sel π A B hj]
  exact hφ v _

end Reindex

end CatCrypt.Crypto
