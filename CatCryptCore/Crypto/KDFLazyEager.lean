/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCOracleGame
public import CatCryptCore.Crypto.PAKE.CPaceSquare
public import CatCryptCore.ForMathlib.PMFSupport

/-!
# Lazy and eager sampling of oracle states

A lazily sampling oracle `O` on states `S` and an eagerly sampling oracle `O'` on states `S'` are
related by a kernel `μ : S → PMF S'`, the distribution of the values that `O'` has drawn in
advance given the state of `O`. If one query to `O'` from a state drawn from `μ s` gives the
answer and the next state of `O` followed by a fresh draw from the kernel, every adversary has
the same output distribution against both oracles (`OracleAdv.run_map_fst_eq_of_kernel`). For
oracle games this gives equal acceptance probabilities (`KeyedGame.accept_eq_of_kernel`), and
for the systems of a protocol over the two games a realization at distance `0`
(`Realizes.ofKernel`).

For a key-derivation function sampled lazily into a table (`roAt`, the form of the key
derivation of the Diffie–Hellman squares), the draw of a fresh value at a query can be made
before the query: `roAt tb x` is a uniform key `k` followed by `roAtDrawn tb x k`, which answers
from the table and otherwise records `k` (`roAt_eq_map_roAtDrawn`). A key drawn in advance for
each pending session forms a pool (`drawPool`); consuming the key of one pending session leaves
a pool of the others (`drawPool_consume`). These are the step conditions of the kernel when a
session's key-derivation value is drawn eagerly at the start of the session and used at its
completion.

## Main definitions

* `roAtDrawn` — the key derivation with a value drawn in advance
* `drawPool` — independent uniform keys for a list of sessions

## Main results

* `OracleAdv.run_map_fst_eq_of_kernel`, `KeyedGame.accept_eq_of_kernel`, `Realizes.ofKernel`
* `roAt_eq_map_roAtDrawn`
* `drawPool_consume`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent
open scoped ENNReal

/-! ## Runs against oracles related by a kernel -/

/-- **Lazy and eager oracles.** Let `μ s` be the distribution of the state of `O'` given the state
`s` of `O`, for states satisfying `V`. If one query `d` to `O'` from a state drawn from `μ s` has
the joint distribution of the answer of `O` and a draw from the kernel at the next state of `O`,
and `O` keeps `V` on its support, then every adversary has the same output distribution against
`O` from `s` as against `O'` from a state drawn from `μ s`. -/
theorem OracleAdv.run_map_fst_eq_of_kernel {D R S S' α : Type} (O : S → D → PMF (R × S))
    (O' : S' → D → PMF (R × S')) (μ : S → PMF S') (V : S → Prop)
    (hstep : ∀ s d, V s → ((μ s).bind fun s' => O' s' d) =
      (O s d).bind fun x => (μ x.2).map fun s' => (x.1, s'))
    (hinv : ∀ s d, V s → ∀ x ∈ (O s d).support, V x.2)
    (B : OracleAdv D R α) (s : S) (hs : V s) :
    ((μ s).bind fun s' => (OracleAdv.run O' B s').map Prod.fst) =
      (OracleAdv.run O B s).map Prod.fst := by
  induction B generalizing s with
  | ret a => simp [PMF.pure_map]
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind]
    rw [PMF.bind_comm]
    exact PMF.bind_congr_support p _ _ fun b _ => ih b s hs
  | query d k ih =>
    simp only [OracleAdv.run_query, PMF.map_bind]
    rw [← PMF.bind_bind (μ s) (fun s' => O' s' d), hstep s d hs, PMF.bind_bind]
    refine PMF.bind_congr_support (O s d) _ _ fun x hx => ?_
    rw [PMF.bind_map]
    exact ih x.1 x.2 (hinv s d hs x hx)

/-- **Lazy and eager oracle games.** Two oracle games whose keys correspond along `κ`, whose
oracles at corresponding keys are related by the kernel `μ` on the invariant `V`, and whose
initial states correspond, accept every adversary with the same probability. -/
theorem KeyedGame.accept_eq_of_kernel {Q A : Type} (G G' : KeyedGame Q A) (κ : G.Key → G'.Key)
    (hkey : G'.keyDist = G.keyDist.map κ) (μ : G.State → PMF G'.State) (V : G.State → Prop)
    (hinit : μ G.init = PMF.pure G'.init) (hV : V G.init)
    (hstep : ∀ k s q, V s → ((μ s).bind fun s' => G'.oracle (κ k) s' q) =
      (G.oracle k s q).bind fun x => (μ x.2).map fun s' => (x.1, s'))
    (hinv : ∀ k s q, V s → ∀ x ∈ (G.oracle k s q).support, V x.2)
    (B : OracleAdv Q A Bool) : G.accept B = G'.accept B := by
  simp only [KeyedGame.accept, hkey, PMF.bind_map]
  congr 1
  refine PMF.bind_congr_support _ _ _ fun k _ => ?_
  have h := OracleAdv.run_map_fst_eq_of_kernel (G.oracle k) (G'.oracle (κ k)) μ V
    (fun s d hs => hstep k s d hs) (fun s d hs => hinv k s d hs) B G.init hV
  rw [hinit, PMF.pure_bind] at h
  exact h.symm

/-- **Lazy and eager systems.** The systems of a protocol over two oracle games related by a
kernel are at distance `0`. -/
theorem Realizes.ofKernel {τ E O Q A : Type} (P : OProt τ E O Q A) (G G' : KeyedGame Q A)
    (κ : G.Key → G'.Key) (hkey : G'.keyDist = G.keyDist.map κ) (μ : G.State → PMF G'.State)
    (V : G.State → Prop) (hinit : μ G.init = PMF.pure G'.init) (hV : V G.init)
    (hstep : ∀ k s q, V s → ((μ s).bind fun s' => G'.oracle (κ k) s' q) =
      (G.oracle k s q).bind fun x => (μ x.2).map fun s' => (x.1, s'))
    (hinv : ∀ k s q, V s → ∀ x ∈ (G.oracle k s q).support, V x.2) :
    Realizes (P.sys G) (P.sys G') fun _ _ => 0 := by
  intro _ Z
  refine le_of_eq ?_
  show adv (P.sys G) (P.sys G') Z = 0
  rw [P.adv_sys, KeyedGame.advantage,
    KeyedGame.accept_eq_of_kernel G G' κ hkey μ V hinit hV hstep hinv, absDiff_self]

/-! ## The key derivation with values drawn in advance -/

section Table

open CatCrypt.Crypto.PAKE.CPaceSquare (roAt)

variable {D K : Type} [DecidableEq D] [Fintype K] [Nonempty K]

/-- The key derivation at `x` with the value `k` drawn in advance: the recorded value when `x`
is in the table, and otherwise `k`, recorded. -/
def roAtDrawn (tb : List (D × K)) (x : D) (k : K) : K × List (D × K) :=
  match tb.lookup x with
  | some v => (v, tb)
  | none => (k, (x, k) :: tb)

/-- **A lazily sampled value is a value drawn in advance.** -/
theorem roAt_eq_map_roAtDrawn (tb : List (D × K)) (x : D) :
    roAt tb x = (PMF.uniformFintype K).map (roAtDrawn tb x) := by
  unfold roAt roAtDrawn
  cases tb.lookup x with
  | some v => exact (PMF.map_const _ _).symm
  | none => rfl

end Table

/-! ## Pools of keys drawn in advance -/

section Pool

variable {I K : Type} [DecidableEq I] [Fintype K] [Nonempty K]

/-- Independent uniform keys for the sessions of `l`, and no key elsewhere. -/
noncomputable def drawPool : List I → PMF (I → Option K)
  | [] => PMF.pure fun _ => none
  | i :: l => (PMF.uniformFintype K).bind fun k =>
      (drawPool l).map fun pool => Function.update pool i (some k)

omit [DecidableEq I] in
theorem map_congr_support {α β : Type} (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  simp only [PMF.map]
  exact PMF.bind_congr_support p _ _ fun a ha => by simp [h a ha]

/-- A pool has no key outside its sessions. -/
theorem drawPool_none (l : List I) :
    ∀ pool ∈ (drawPool (K := K) l).support, ∀ x, x ∉ l → pool x = none := by
  induction l with
  | nil =>
    intro pool hp x _
    rw [drawPool, PMF.mem_support_pure_iff] at hp
    rw [hp]
  | cons j l ih =>
    intro pool hp x hx
    rw [drawPool, PMF.mem_support_bind_iff] at hp
    obtain ⟨k, -, hp⟩ := hp
    rw [PMF.support_map] at hp
    obtain ⟨p, hp, rfl⟩ := hp
    rw [List.mem_cons, not_or] at hx
    dsimp only
    rw [Function.update_of_ne hx.1]
    exact ih p hp x hx.2

/-- **Consuming a key of the pool.** For a list of distinct sessions containing `i`, drawing the
pool and reading and removing the key of `i` is drawing a key and the pool of the other
sessions. -/
theorem drawPool_consume (l : List I) (hl : l.Nodup) (i : I) (hi : i ∈ l) :
    (drawPool (K := K) l).map (fun pool => (pool i, Function.update pool i none)) =
      (PMF.uniformFintype K).bind fun k =>
        (drawPool (l.erase i)).map fun pool => (some k, pool) := by
  induction l with
  | nil => exact absurd hi List.not_mem_nil
  | cons j l ih =>
    rw [List.nodup_cons] at hl
    by_cases hij : i = j
    · subst hij
      rw [List.erase_cons_head, drawPool, PMF.map_bind]
      refine congrArg _ (funext fun k => ?_)
      rw [PMF.map_comp]
      refine map_congr_support _ _ _ fun p hp => ?_
      have hpi : p i = none := drawPool_none l p hp i hl.1
      simp only [Function.comp_apply, Function.update_self, Function.update_idem, Prod.mk.injEq,
        true_and]
      exact Function.update_eq_self_iff.2 hpi.symm
    · have hi' : i ∈ l := (List.mem_cons.1 hi).resolve_left hij
      have e : ∀ k : K, (drawPool l).map ((fun pool => (pool i, Function.update pool i none)) ∘
          fun pool => Function.update pool j (some k)) =
          (PMF.uniformFintype K).bind fun k' =>
            (drawPool (l.erase i)).map fun p => (some k', Function.update p j (some k)) :=
          fun k => by
        have hf : ((fun pool => (pool i, Function.update pool i none)) ∘
            fun pool => Function.update pool j (some k)) =
            (fun q : Option K × (I → Option K) => (q.1, Function.update q.2 j (some k))) ∘
              (fun pool => (pool i, Function.update pool i none)) := funext fun p => by
          show (Function.update p j (some k) i,
              Function.update (Function.update p j (some k)) i none) =
            (p i, Function.update (Function.update p i none) j (some k))
          rw [Function.update_of_ne hij, Function.update_comm (Ne.symm hij)]
        rw [hf, ← PMF.map_comp, ih hl.2 hi', PMF.map_bind]
        simp only [PMF.map_comp, Function.comp_def]
      rw [List.erase_cons_tail (by simp [Ne.symm hij]), drawPool, PMF.map_bind]
      simp only [PMF.map_comp, e]
      rw [drawPool]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      exact PMF.bind_comm _ _ _

end Pool

end CatCrypt.Crypto
