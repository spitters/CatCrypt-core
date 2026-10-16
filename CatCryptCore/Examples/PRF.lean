/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SecurityDefs
public import CatCryptCore.Crypto.PRFAssumption
public import CatCryptCore.Crypto.SwitchingLemma
public import CatCryptCore.Crypto.MultiQueryPRF
public import CatCryptCore.Crypto.PRPPRFSwitching
public import CatCryptCore.Prob.BirthdayBound
public import CatCryptCore.Prob.XorBij
public import CatCryptCore.Examples.OneTimePad
public import CatCryptCore.Tactics
public import CatCryptCore.Tactics.AutoMetrics
public import CatCryptCore.ForMathlib.PMFSupport

/-!
# Bijection-Family PRF: Perfect Security

A pseudorandom function built from a *bijection family* has perfect security.
Following Rosulek, The Joy of Cryptography, §6 (pseudorandom functions).

For each input `x`, if the map `k ↦ eval k x` is a bijection from keys to
outputs, then over a uniform key the PRF output `eval k x` is itself uniform on
the output space and independent of `x`. Hence the PRF real game (keyed
evaluation) and the PRF ideal game (a fresh uniform output) are perfectly
indistinguishable: the PRF advantage of *every* adversary is exactly `0`.

## Overview

This mirrors the one-time-pad argument (`CatCrypt.Examples.OTP`): the security
proof is the bijection-coupling technique. `liftR_uniform_bij` couples the
uniform key with the uniform output through the bijection `bij x : Key ≃ Output`;
`liftR_bind`/`liftR_pure` push the coupling through the `sample`-then-`pure`
structure of the games; and `PRF_Adv_zero_of_rHoare` collapses the advantage to
`0`.

## Main definitions

* `BijPRFFamily` — a family of key→output bijections indexed by input.
* `BijPRFFamily.toPRFScheme` — the core `PRFScheme` it induces (`eval k x = bij x k`).

## Main results

* `cascade_prf_bound` — for the cascade `F k₂ (F k₁ x)` and every adaptive
  adversary `A` with at most `q` queries, the PRF advantage is at most the PRF
  advantages of two reductions against `F` plus `q(q-1)/2 / |D|`.
* `bijPRF_coupling` — the real and ideal PRF games couple with `eqPost`.
* `bijPRF_perfect` — a bijection-family PRF has perfect PRF security:
  `PRF_Adv B.toPRFScheme x A = 0` for every input `x` and adversary `A`.

## References

* [Rosulek, The Joy of Cryptography, §6 (pseudorandom functions)]
-/

@[expose] public section

namespace CatCrypt.Examples.PRF

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.SecurityDefs
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open CatCrypt.Relational

/-! ## Bijection-Family PRF -/

/-- A PRF given by a family of bijections `bij x : Key ≃ Output`, one per input.

For a uniform key, `bij x` maps the uniform key distribution onto the uniform
output distribution, which is the source of perfect security. -/
structure BijPRFFamily where
  /-- Key type -/
  Key : Type
  /-- Input (domain) type -/
  Input : Type
  /-- Output (range) type -/
  Output : Type
  [finKey : Fintype Key]
  [neKey : Nonempty Key]
  [finOutput : Fintype Output]
  [neOutput : Nonempty Output]
  /-- For each input, a bijection from keys to outputs -/
  bij : Input → (Key ≃ Output)

attribute [instance] BijPRFFamily.finKey BijPRFFamily.neKey
  BijPRFFamily.finOutput BijPRFFamily.neOutput

/-- The core `PRFScheme` induced by a bijection family: `eval k x = bij x k`. -/
def BijPRFFamily.toPRFScheme (B : BijPRFFamily) : PRFScheme where
  Key := B.Key
  Input := B.Input
  Output := B.Output
  eval := fun k x => B.bij x k

/-! ## Perfect PRF Security -/

/-- Coupling: for a bijection-family PRF the real and ideal games are
equidistributed.

Over a uniform key `k`, the real game returns `bij x k` while the ideal game
returns a fresh uniform output `r`; `liftR_uniform_bij (B.bij x)` couples them so
that `bij x k = r`, so the two games agree pointwise. -/
theorem bijPRF_coupling (B : BijPRFFamily) (x : B.Input) :
    rHoare eqPre
      (PRF_Real B.toPRFScheme x)
      (PRF_Ideal B.toPRFScheme)
      eqPost := by
  simp only [PRF_Real, PRF_Ideal, BijPRFFamily.toPRFScheme, SPComp.monad_bind_eq]
  ssprove_couple_bij (B.bij x)

/-- **A bijection-family PRF has perfect PRF security**: every adversary has PRF
advantage exactly `0`. -/
theorem bijPRF_perfect (B : BijPRFFamily) (x : B.Input)
    (A : B.toPRFScheme.Output → SPComp Bool) :
    PRF_Adv B.toPRFScheme x A = 0 :=
  PRF_Adv_zero_of_rHoare B.toPRFScheme x (bijPRF_coupling B x) A

/-! ## Example: the XOR PRF over `Bool`

`F(k, x) = k ⊕ x` is the bijection family `x ↦ boolXorBij x`; it is the PRF
counterpart of the one-time pad and inherits perfect security. -/

/-- The XOR PRF over `Bool` as a bijection family: `bij x = boolXorBij x`. -/
def boolXorPRF : BijPRFFamily where
  Key := Bool
  Input := Bool
  Output := Bool
  bij := boolXorBij

/-- The XOR PRF has perfect PRF security. -/
theorem boolXorPRF_perfect (x : Bool)
    (A : boolXorPRF.toPRFScheme.Output → SPComp Bool) :
    PRF_Adv boolXorPRF.toPRFScheme x A = 0 :=
  bijPRF_perfect boolXorPRF x A

/-! ## Cascade PRF: the reduction

The cascade of a keyed function `F : K → D → D` under two independent keys is
`cascade F (k₁, k₂) x = F k₂ (F k₁ x)`. For an adaptive adversary `A` asking at
most `q` queries, its PRF advantage is bounded by the PRF advantages of two
reductions against `F` and the PRP/PRF switching bound `q(q-1)/2 / |D|`.

### Main definitions

* `cascade F` — the cascade of `F` with itself
* `cascadeRedInner F A` — samples the outer key `k₂` and runs `A` with every
  answer mapped by `F k₂`
* `cascadeRedOuter A` — runs `A` with every query passed through an internally
  simulated lazy random injection

### Main results

* `cascade_prf_bound` — the bound on the PRF advantage against the cascade

The earlier statements `cascade_prf_bound`, `cascade_prf_bound_of_assumption`
and `cascade_prf_perfect` took the three hop bounds as hypotheses about an
arbitrary game sequence, with no cascade construction; they are replaced by the
statement of the same name below, in which the two PRF hops are the advantages
of the reductions `cascadeRedInner F A` and `cascadeRedOuter A` and the
switching hop is proved by `RF_RP_Advantage_le`.

### Proof

The games are
G₀ = `realGame (cascade F) A` = `realGame F (cascadeRedInner F A)`,
G₁ = `rfGame (cascadeRedInner F A)` (`F k₂` after a lazy random function),
G₂ = `rpGame (cascadeRedInner F A)` = `realGame F (cascadeRedOuter A)`
(`F k₂` after a lazy random injection), and
G₃ = `rfGame (cascadeRedOuter A)` = `rfGame A`. The hop G₁ → G₂ is the
switching lemma `RF_RP_Advantage_le`. The last equality states that a lazy
random function after a lazy random injection is a lazy random function; it is
proved through a joint lazy oracle `rfrpOracle` whose table maps onto the
table of the random function on every state, and onto the pair of tables of
the composite oracle on every state satisfying the invariant `RfrpInv`
(`run_map_state_of_inv`).
-/

section Cascade

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open scoped ENNReal

/-- The uniform distribution on a product is the product of the uniform
distributions. -/
theorem uniformOfFintype_prod {K : Type} [Fintype K] [Nonempty K] :
    PMF.uniformOfFintype (K × K) =
      (PMF.uniformOfFintype K).bind fun a => (PMF.uniformOfFintype K).map (a, ·) := by
  ext ⟨a, b⟩
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.map_apply, tsum_eq_single b]
    · simp [ENNReal.mul_inv]
    · intro y hy; simp [Ne.symm hy]
  · intro x hx
    rw [PMF.map_apply]
    simp [Ne.symm hx]

/-! ## Answer maps and the simulated random injection -/

section MapAns

variable {D R R' α : Type}

/-- `mapAns f A` asks the queries of `A` and passes `f r` to `A` for every
answer `r`. -/
def mapAns (f : R → R') : OracleAdv D R' α → OracleAdv D R α
  | .ret a => .ret a
  | .rand p k => .rand p fun b => mapAns f (k b)
  | .query d k => .query d fun r => mapAns f (k (f r))

/-- Running `mapAns f A` against `O` is running `A` against `O` with every answer
mapped by `f`. -/
theorem run_mapAns {S : Type} (f : R → R') (O : S → D → PMF (R × S))
    (A : OracleAdv D R' α) (s : S) :
    OracleAdv.run O (mapAns f A) s =
      OracleAdv.run (fun s d => (O s d).map (Prod.map f id)) A s := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih => simp only [mapAns, OracleAdv.run_rand, ih]
  | query d k ih =>
    simp only [mapAns, OracleAdv.run_query, ih, PMF.bind_map]
    rfl

/-- `mapAns f A` satisfies every query bound of `A`. -/
theorem isQueryBound_mapAns (f : R → R') {A : OracleAdv D R' α} {q : ℕ}
    (hA : A.IsQueryBound q) : (mapAns f A).IsQueryBound q := by
  induction A generalizing q with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b)
  | query d k ih =>
    cases q with
    | zero => exact hA.elim
    | succ q => exact fun r => ih (f r) (hA (f r))

end MapAns

/-- Running against `O` along a state invariant: if `I` holds initially, every
transition of `O` from a state satisfying `I` stays in `I`, and the state map
`f` commutes with one call of `O` from every state satisfying `I`, then `f`
commutes with the whole run. -/
theorem run_map_state_of_inv {D R α S S' : Type} (O : S → D → PMF (R × S))
    (O' : S' → D → PMF (R × S')) (f : S → S') (I : S → Prop)
    (hI : ∀ s d, I s → ∀ z ∈ (O s d).support, I z.2)
    (hO : ∀ s d, I s → (O s d).map (Prod.map id f) = O' (f s) d)
    (A : OracleAdv D R α) (s : S) (hs : I s) :
    (OracleAdv.run O A s).map (Prod.map id f) = OracleAdv.run O' A (f s) := by
  induction A generalizing s with
  | ret a => simp [PMF.pure_map]
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind]
    exact congrArg _ (funext fun b => ih b s hs)
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.map_bind,
      PMF.bind_congr_support _ _ _ (fun z hz => ih z.1 z.2 (hI s d hs z hz)), OracleAdv.run_query,
      ← hO s d hs, PMF.bind_map]
    rfl

/-! ## Lookup in association lists -/

section Lookup

variable {α β γ : Type} [DecidableEq α]

/-- Lookup commutes with a map of the values. -/
theorem lookup_map_snd (g : β → γ) (u : List (α × β)) (x : α) :
    List.lookup x (u.map fun e => (e.1, g e.2)) = (List.lookup x u).map g := by
  induction u with
  | nil => rfl
  | cons e u ih =>
    obtain ⟨a, b⟩ := e
    by_cases h : x = a
    · subst h; simp [List.lookup]
    · simp [List.lookup, beq_false_of_ne h, ih]

/-- A successful lookup returns a recorded entry. -/
theorem mem_of_lookup_eq_some {u : List (α × β)} {x : α} {b : β}
    (h : List.lookup x u = some b) : (x, b) ∈ u := by
  induction u with
  | nil => simp [List.lookup] at h
  | cons e u ih =>
    obtain ⟨a, c⟩ := e
    by_cases hx : x = a
    · subst hx; simp [List.lookup] at h; simp [h]
    · simp only [List.lookup, beq_false_of_ne hx] at h; exact List.mem_cons_of_mem _ (ih h)

/-- A failed lookup means the key is not recorded. -/
theorem not_mem_of_lookup_eq_none {u : List (α × β)} {x : α}
    (h : List.lookup x u = none) : x ∉ u.map Prod.fst := by
  induction u with
  | nil => simp
  | cons e u ih =>
    obtain ⟨a, c⟩ := e
    by_cases hx : x = a
    · subst hx; simp [List.lookup] at h
    · simp only [List.lookup, beq_false_of_ne hx] at h; simpa [hx] using ih h

/-- The lookup of an unrecorded key fails. -/
theorem lookup_eq_none_of_not_mem {u : List (α × β)} {x : α}
    (h : x ∉ u.map Prod.fst) : List.lookup x u = none := by
  induction u with
  | nil => rfl
  | cons e u ih =>
    obtain ⟨a, c⟩ := e
    have hx : x ≠ a := by rintro rfl; simp at h
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [List.lookup, beq_false_of_ne hx, ih h.2]

/-- With pairwise distinct keys, the lookup of a recorded key returns its
recorded value. -/
theorem lookup_eq_some_of_mem {u : List (α × β)} {x : α} {b : β}
    (hnd : (u.map Prod.fst).Nodup) (h : (x, b) ∈ u) : List.lookup x u = some b := by
  induction u with
  | nil => simp at h
  | cons e u ih =>
    obtain ⟨a, c⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with h | hmem
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [List.lookup]
    · have hx : x ≠ a := by
        intro hxa; subst hxa; exact hnd.1 (List.mem_map_of_mem (f := Prod.fst) hmem)
      simp [List.lookup, beq_false_of_ne hx, ih hnd.2 hmem]

end Lookup

/-! ## The cascade and its reductions -/

variable {K D : Type} [Fintype K] [Nonempty K] [Fintype D] [Nonempty D] [DecidableEq D]

/-- The cascade of a keyed function with itself under two independent keys:
`cascade F (k₁, k₂) x = F k₂ (F k₁ x)`. -/
def cascade (F : K → D → D) : K × K → D → D := fun kk x => F kk.2 (F kk.1 x)

/-- Reduction to the inner layer: sample the outer key `k₂` and run `A` with
every answer `y` replaced by `F k₂ y`. -/
noncomputable def cascadeRedInner (F : K → D → D) (A : OracleAdv D D Bool) :
    OracleAdv D D Bool :=
  .rand (PMF.uniformOfFintype K) fun k₂ => mapAns (F k₂) A

/-- `simRP t A` runs `A` against a lazily sampled random injection `π` with
table `t`, simulated inside the adversary, and replaces every query `x` of `A`
by the query `π x`. -/
noncomputable def simRP {α : Type} : List (D × D) → OracleAdv D D α → OracleAdv D D α
  | _, .ret a => .ret a
  | t, .rand p k => .rand p fun b => simRP t (k b)
  | t, .query x k =>
    match List.lookup x t with
    | some r => .query r fun y => simRP t (k y)
    | none => .rand (freshDist (usedAnswers t)) fun r => .query r fun y => simRP ((x, r) :: t) (k y)

/-- Reduction to the outer layer: run `A` with each of its queries passed
through an internally simulated lazy random injection. -/
noncomputable def cascadeRedOuter (A : OracleAdv D D Bool) : OracleAdv D D Bool :=
  simRP [] A

/-- The composite oracle: the query is first passed through the lazy random
injection (state `s.1`) and its image is then queried to `O` (state `s.2`). -/
noncomputable def compOracle {S : Type} (O : S → D → PMF (D × S)) (s : List (D × D) × S)
    (d : D) : PMF (D × (List (D × D) × S)) :=
  (rpOracle s.1 d).bind fun z => (O s.2 z.1).map fun w => (w.1, (z.2, w.2))

/-- Running the simulation `simRP t A` against `O` is running `A` against the
composite oracle, with the table of the simulated injection discarded. -/
theorem run_simRP {α S : Type} (O : S → D → PMF (D × S)) (A : OracleAdv D D α)
    (t : List (D × D)) (s : S) :
    OracleAdv.run O (simRP t A) s =
      (OracleAdv.run (compOracle O) A (t, s)).map (Prod.map id Prod.snd) := by
  induction A generalizing t s with
  | ret a => simp [simRP, PMF.pure_map]
  | rand p k ih => simp only [simRP, OracleAdv.run_rand, PMF.map_bind, ih]
  | query x k ih =>
    rcases h : List.lookup x t with _ | r
    · simp only [simRP, h, OracleAdv.run_rand, OracleAdv.run_query, compOracle, rpOracle,
        PMF.map_bind, PMF.bind_map, PMF.bind_bind, ih, Function.comp_apply]
    · simp only [simRP, h, OracleAdv.run_query, compOracle, rpOracle, PMF.pure_bind,
        PMF.map_bind, PMF.bind_map, ih]
      rfl

/-- `simRP t A` satisfies every query bound of `A`. -/
theorem isQueryBound_simRP {α : Type} {A : OracleAdv D D α} {q : ℕ} (hA : A.IsQueryBound q)
    (t : List (D × D)) : (simRP t A).IsQueryBound q := by
  induction A generalizing q t with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b) t
  | query x k ih =>
    cases q with
    | zero => exact hA.elim
    | succ q =>
      unfold simRP
      split
      · exact fun y => ih y (hA y) t
      · exact fun r y => ih y (hA y) _

/-! ## A random function composed with a random injection is a random function -/

/-- If the complement of `u` is nonempty, `freshDist u` samples outside `u`. -/
theorem not_mem_of_mem_support_freshDist {u : Finset D} (hu : uᶜ.Nonempty) {r : D}
    (hr : r ∈ (freshDist u).support) : r ∉ u := by
  unfold freshDist at hr
  rw [dif_pos hu, PMF.support_uniformOfFinset] at hr
  simpa using hr

/-- The joint lazy oracle for a random function composed with a random
injection. The table `u` records entries `(x, π x, ρ (π x))`: a recorded query
returns the third component; a fresh query samples `π x` without replacement
from the second components and `ρ (π x)` uniformly, and records the entry. -/
noncomputable def rfrpOracle (u : List (D × D × D)) (x : D) : PMF (D × List (D × D × D)) :=
  match List.lookup x u with
  | some r => PMF.pure (r.2, u)
  | none => (freshDist (usedAnswers (u.map fun e => (e.1, e.2.1)))).bind fun r₁ =>
      (PMF.uniformOfFintype D).map fun r₂ => (r₂, (x, r₁, r₂) :: u)

/-- Forgetting the middle components of the joint table gives the lazy random
function. -/
theorem rfrpOracle_map_rf (u : List (D × D × D)) (x : D) :
    (rfrpOracle u x).map (Prod.map id fun u => u.map fun e => (e.1, e.2.2)) =
      rfOracle (u.map fun e => (e.1, e.2.2)) x := by
  unfold rfrpOracle rfOracle
  rw [lookup_map_snd]
  rcases List.lookup x u with _ | r
  · simp only [Option.map_none, PMF.map_bind, PMF.map_comp]
    exact PMF.bind_const _
      (PMF.map (fun r => (r, (x, r) :: List.map (fun e => (e.1, e.2.2)) u))
        (PMF.uniformOfFintype D))
  · simp [PMF.pure_map]

/-- The invariant of the joint table: the queries and the images under the
random injection are pairwise distinct. -/
def RfrpInv (u : List (D × D × D)) : Prop :=
  (u.map Prod.fst).Nodup ∧ (u.map fun e => e.2.1).Nodup

omit [Fintype D] [Nonempty D] in
/-- The images of the random injection recorded in the joint table. -/
theorem usedAnswers_rfrp (u : List (D × D × D)) :
    usedAnswers (u.map fun e => (e.1, e.2.1)) = (u.map fun e => e.2.1).toFinset := by
  simp [usedAnswers, Function.comp_def]

omit [Nonempty D] in
/-- For a fresh query on a table satisfying the invariant, an unused image of
the random injection exists. -/
theorem compl_usedAnswers_nonempty {u : List (D × D × D)} (hu : RfrpInv u) {x : D}
    (hx : List.lookup x u = none) :
    (usedAnswers (u.map fun e => (e.1, e.2.1)))ᶜ.Nonempty := by
  have hnd : (x :: u.map Prod.fst).Nodup :=
    List.nodup_cons.mpr ⟨not_mem_of_lookup_eq_none hx, hu.1⟩
  have hlen : u.length + 1 ≤ Fintype.card D := by
    simpa using hnd.length_le_card
  have hcard : (usedAnswers (u.map fun e => (e.1, e.2.1))).card ≤ u.length :=
    (card_usedAnswers_le _).trans (by simp)
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at h
  rw [h, Finset.card_univ] at hcard
  omega

/-- `rfrpOracle` preserves the invariant `RfrpInv` on its support. -/
theorem rfrpOracle_inv (u : List (D × D × D)) (x : D) (hu : RfrpInv u) :
    ∀ z ∈ (rfrpOracle u x).support, RfrpInv z.2 := by
  intro z hz
  unfold rfrpOracle at hz
  rcases hx : List.lookup x u with _ | r
  · rw [hx] at hz
    obtain ⟨r₁, hr₁, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    rw [PMF.support_map] at hz
    obtain ⟨r₂, -, rfl⟩ := hz
    have hfr := not_mem_of_mem_support_freshDist (compl_usedAnswers_nonempty hu hx) hr₁
    rw [usedAnswers_rfrp, List.mem_toFinset] at hfr
    exact ⟨List.nodup_cons.mpr ⟨not_mem_of_lookup_eq_none hx, hu.1⟩,
      List.nodup_cons.mpr ⟨hfr, hu.2⟩⟩
  · rw [hx, PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hu

/-- On tables satisfying the invariant, splitting the joint table into the
table of the random injection and the table of the random function gives the
composite oracle. -/
theorem rfrpOracle_map_comp (u : List (D × D × D)) (x : D) (hu : RfrpInv u) :
    (rfrpOracle u x).map
        (Prod.map id fun u => (u.map fun e => (e.1, e.2.1), u.map Prod.snd)) =
      compOracle rfOracle (u.map fun e => (e.1, e.2.1), u.map Prod.snd) x := by
  unfold rfrpOracle compOracle rpOracle
  dsimp only
  rw [lookup_map_snd]
  rcases hx : List.lookup x u with _ | r
  · simp only [Option.map_none, PMF.map_bind, PMF.bind_map]
    refine PMF.bind_congr_support _ _ _ fun r₁ hr₁ => ?_
    have hfr := not_mem_of_mem_support_freshDist (compl_usedAnswers_nonempty hu hx) hr₁
    rw [usedAnswers_rfrp, List.mem_toFinset] at hfr
    have hl : List.lookup r₁ (u.map Prod.snd) = none :=
      lookup_eq_none_of_not_mem (by simpa [Function.comp_def] using hfr)
    simp only [Function.comp_apply, rfOracle, hl, PMF.map_comp]
    rfl
  · have hmem : (r.1, r.2) ∈ u.map Prod.snd :=
      List.mem_map.mpr ⟨(x, r), mem_of_lookup_eq_some hx, rfl⟩
    have hl : List.lookup r.1 (u.map Prod.snd) = some r.2 :=
      lookup_eq_some_of_mem (by simpa [Function.comp_def] using hu.2) hmem
    simp [PMF.pure_map, rfOracle, hl]

/-- A lazy random function composed with a lazy random injection has the
output distribution of a lazy random function. -/
theorem run_compOracle_rfOracle (A : OracleAdv D D Bool) :
    (OracleAdv.run (compOracle rfOracle) A ([], [])).map Prod.fst =
      (OracleAdv.run rfOracle A []).map Prod.fst := by
  have h₁ := OracleAdv.run_map_state rfrpOracle rfOracle _ rfrpOracle_map_rf A []
  have h₂ := run_map_state_of_inv rfrpOracle (compOracle rfOracle) _ RfrpInv rfrpOracle_inv
    rfrpOracle_map_comp A [] ⟨List.nodup_nil, List.nodup_nil⟩
  simp only [List.map_nil] at h₁ h₂
  rw [← h₁, ← h₂, PMF.map_comp, PMF.map_comp]
  rfl

/-! ## The game hops -/

omit [Fintype D] [Nonempty D] [DecidableEq D] in
/-- The real game of the cascade is the real game of `F` against the inner
reduction. -/
theorem realGame_cascade_eq (F : K → D → D) (A : OracleAdv D D Bool) :
    realGame (cascade F) A = realGame F (cascadeRedInner F A) := by
  unfold realGame cascadeRedInner
  congr 1
  rw [uniformOfFintype_prod, PMF.bind_bind]
  refine congrArg _ (funext fun k₁ => ?_)
  rw [OracleAdv.run_rand, PMF.bind_map, PMF.map_bind]
  refine congrArg _ (funext fun k₂ => ?_)
  rw [Function.comp_apply, run_mapAns]
  congr 2
  funext s d
  simp [keyedOracle, cascade, PMF.pure_map]

/-- The ideal PRP game of the inner reduction is the real game of `F` against
the outer reduction: both run `A` against `F k₂` composed with a lazy random
injection. -/
theorem rpGame_cascadeRedInner_eq (F : K → D → D) (A : OracleAdv D D Bool) :
    rpGame (cascadeRedInner F A) = realGame F (cascadeRedOuter A) := by
  unfold rpGame realGame cascadeRedInner cascadeRedOuter
  congr 1
  rw [OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun k => ?_)
  rw [run_mapAns, run_simRP, PMF.map_comp]
  have h := OracleAdv.run_map_state (compOracle (keyedOracle F k))
    (fun s d => (rpOracle s d).map (Prod.map (F k) id)) Prod.fst
    (fun s d => by
      simp only [compOracle, keyedOracle, PMF.map_bind, PMF.pure_map]
      rw [← PMF.bind_pure_comp]
      rfl) A ([], ())
  rw [← h, PMF.map_comp]
  rfl

/-- The ideal PRF game of the outer reduction is the ideal PRF game of `A`:
a lazy random function composed with a lazy random injection is a lazy random
function. -/
theorem rfGame_cascadeRedOuter_eq (A : OracleAdv D D Bool) :
    rfGame (cascadeRedOuter A) = rfGame A := by
  unfold rfGame cascadeRedOuter
  rw [run_simRP, PMF.map_comp, ← run_compOracle_rfOracle]
  rfl

omit [Fintype D] [Nonempty D] [DecidableEq D] in
/-- The inner reduction satisfies every query bound of `A`. -/
theorem isQueryBound_cascadeRedInner (F : K → D → D) {A : OracleAdv D D Bool} {q : ℕ}
    (hA : A.IsQueryBound q) : (cascadeRedInner F A).IsQueryBound q :=
  fun k₂ => isQueryBound_mapAns (F k₂) hA

/-- The outer reduction satisfies every query bound of `A`. -/
theorem isQueryBound_cascadeRedOuter {A : OracleAdv D D Bool} {q : ℕ}
    (hA : A.IsQueryBound q) : (cascadeRedOuter A).IsQueryBound q :=
  isQueryBound_simRP hA []

/-- **Security of the cascade.** For an adversary asking at most `q` adaptive
queries, the PRF advantage against the cascade `F k₂ ∘ F k₁` is at most the
PRF advantage of the inner reduction, plus the switching bound
`q(q-1)/2 / |D|`, plus the PRF advantage of the outer reduction. -/
theorem cascade_prf_bound (F : K → D → D) (A : OracleAdv D D Bool) (q : ℕ)
    (hA : A.IsQueryBound q) :
    PRF_q_Advantage (cascade F) A ≤
      PRF_q_Advantage F (cascadeRedInner F A) + ↑(q * (q - 1) / 2) / ↑(Fintype.card D)
        + PRF_q_Advantage F (cascadeRedOuter A) := by
  have hsw := RF_RP_Advantage_le (cascadeRedInner F A) q (isQueryBound_cascadeRedInner F hA)
  unfold PRF_q_Advantage RF_RP_Advantage at *
  rw [realGame_cascade_eq, ← rfGame_cascadeRedOuter_eq A]
  calc Advantage (realGame F (cascadeRedInner F A)) (rfGame (cascadeRedOuter A))
      ≤ Advantage (realGame F (cascadeRedInner F A)) (rfGame (cascadeRedInner F A)) +
          Advantage (rfGame (cascadeRedInner F A)) (rfGame (cascadeRedOuter A)) :=
        advantage_triangle _ _ _
    _ ≤ Advantage (realGame F (cascadeRedInner F A)) (rfGame (cascadeRedInner F A)) +
          (Advantage (rfGame (cascadeRedInner F A)) (rpGame (cascadeRedInner F A)) +
            Advantage (rpGame (cascadeRedInner F A)) (rfGame (cascadeRedOuter A))) :=
        add_le_add le_rfl (advantage_triangle _ _ _)
    _ ≤ _ := by
        rw [rpGame_cascadeRedInner_eq] at hsw ⊢
        rw [← add_assoc]
        exact add_le_add (add_le_add le_rfl hsw) le_rfl

end Cascade

open CatCrypt.Tactic

/-! ## Tactic showcase: the bijection-family PRF by `bind_vcgen`

For a bijection-family function the single-query PRF advantage is `0`. This is
proved by showing that the two single-query games are the *same* `SPComp`
distribution, using the
`bind_vcgen` run-to-completion tactic: it normalizes the monad structure and, via
the supplied change-of-variables bijection `B.bij x`, collapses `sample k; return
bij(x,k)` to a fresh uniform sample. -/

/-- The real and ideal single-query PRF games for a bijection family are the
*same* `SPComp` computation. Proved by `bind_vcgen using (B.bij x)`: the
change-of-variables through the bijection rewrites the keyed evaluation into a
plain uniform sample. -/
theorem bijPRF_game_eq (B : BijPRFFamily) (x : B.Input) :
    PRF_Real B.toPRFScheme x = PRF_Ideal B.toPRFScheme := by
  rw [← SPComp.bind_pure (PRF_Ideal B.toPRFScheme)]
  simp only [PRF_Real, PRF_Ideal, BijPRFFamily.toPRFScheme, SPComp.monad_bind_eq]
  bind_vcgen using (B.bij x)

/-- A bijection-family PRF has PRF advantage `0`, re-proved through the
`bind_vcgen` game-equality `bijPRF_game_eq` (an alternative to the relational
coupling of `bijPRF_perfect`). -/
theorem bijPRF_adv_zero_via_vcgen (B : BijPRFFamily) (x : B.Input)
    (A : B.toPRFScheme.Output → SPComp Bool) :
    PRF_Adv B.toPRFScheme x A = 0 := by
  simp_all [PRF_Adv, AdvantageA, bijPRF_game_eq, Advantage_self]

/-- A bijection-family base function satisfies the `PRFAssumption` with `ε = 0`,
witnessed by the `bind_vcgen` proof `bijPRF_adv_zero_via_vcgen`. -/
noncomputable def bijPRF_assumption (B : BijPRFFamily) : PRFAssumption B.toPRFScheme :=
  PRFAssumption.of_perfect B.toPRFScheme (bijPRF_adv_zero_via_vcgen B)

end CatCrypt.Examples.PRF
