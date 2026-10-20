/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Game
public import CatCryptCore.Crypto.PRPPRFPmfGame

/-!
# Fiat–Shamir in the random-oracle model: the verifier's values and the EUF-CMA game

Facts about the look-up in a random-oracle table, the values read by the verifier of a
Fiat–Shamir protocol, and its EUF-CMA game as a distinguishing game.

## Main results

* `lookupIn_mem` — a value found by `lookupIn` is an entry of the list
* `verifyVals_spec` — the values read by the verifier, each at the verifier's point after
  the values before it
* `advantageA_eufcmaGame_le` — a distinguisher on the EUF-CMA game against the game that
  always rejects has advantage at most the EUF-CMA advantage
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-- A value found by `lookupIn l k` is an entry `(k, c)` of `l`. -/
theorem lookupIn_mem {Kt C : Type} [DecidableEq Kt] {l : List (Kt × C)} {k : Kt} {c : C}
    (h : lookupIn l k = some c) : (k, c) ∈ l := by
  unfold lookupIn findKey at h
  cases hf : l.findIdx? (fun p => decide (p.1 = k)) with
  | none => simp [hf] at h
  | some i =>
    obtain ⟨hi, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    simp only [hf, Option.bind_some, List.getElem?_eq_getElem hi, Option.map_some,
      Option.some.injEq] at h
    simp only [decide_eq_true_eq] at hp
    rw [← hp, ← h]
    exact List.getElem_mem hi

/-- The values read by the verifier: `n` of them after `acc`, each the value of `look` at
the verifier's point after the values before it. -/
theorem verifyVals_spec {G : Protocol} (look : G.Key → Option G.Ch) (x : G.Stmt) (m : G.Msg)
    (σ : G.Sig) : ∀ (n : ℕ) (acc vs : List G.Ch), verifyVals look x m σ n acc = some vs →
      ∃ rest, vs = acc ++ rest ∧ rest.length = n ∧
        ∀ k (hk : k < rest.length), look (G.vkey x m σ (acc ++ rest.take k)) = some rest[k]
  | 0, acc, vs, h => ⟨[], by simpa [verifyVals] using h.symm, rfl, fun k hk => by simp at hk⟩
  | n + 1, acc, vs, h => by
    simp only [verifyVals, Option.bind_eq_some_iff] at h
    obtain ⟨e, he, hrest⟩ := h
    obtain ⟨rest, rfl, hlen, hlook⟩ := verifyVals_spec look x m σ n (acc ++ [e]) vs hrest
    refine ⟨e :: rest, by simp, by simp [hlen], fun k hk => ?_⟩
    cases k with
    | zero => simpa using he
    | succ k =>
      have := hlook k (by simp at hk; omega)
      simpa [List.take_succ_cons] using this

/-- A distinguisher on the EUF-CMA game of a Fiat–Shamir protocol against the game that
always rejects has advantage at most the EUF-CMA advantage. -/
theorem advantageA_eufcmaGame_le {G : Protocol} {qH qS : ℕ} (A : G.Adversary qH qS)
    (D : Bool → SPComp Bool) :
    AdvantageA (eufcmaGame A) (SPComp.pure false) D ≤ eufcmaAdvantage A := by
  refine (absDiff_bind_le_advantage (PRPPRF.pmfGame_isPure _) (SPComp.pure_isPure false)
    (PRPPRF.pmfGame_noFail _) (SPComp.pure_noFail false) D Heap.empty).trans ?_
  have h0 : prTrue (SPComp.pure false) Heap.empty = 0 := by
    unfold prTrue SPComp.pure SDistr.pure
    simp
  unfold Advantage
  rw [h0]
  simp [eufcmaAdvantage]
  exact le_rfl

end CatCrypt.Crypto.FiatShamirROM
