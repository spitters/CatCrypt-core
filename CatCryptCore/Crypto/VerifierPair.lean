/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.ForkingLemma
public import CatCryptCore.Crypto.UCConcrete

/-!
# Verifier Pairs That Differ Only on a Win Event

A real and an ideal verifier that read the outcome of one shared experiment
`exp : SPComp σ` and return the same decision except on states where the
adversary wins (`win : σ → Bool`) are indistinguishable up to the winning
probability: every distinguisher's advantage between `exp >>= real` and
`exp >>= ideal` is at most `prTrue (exp >>= fun s => pure (win s))`. This is
the search-game step of an unforgeability or binding argument, where the win
event is a forgery or a binding break and its probability is bounded by an
explicit reduction.

## Main results

* `prTrue_bind_le_prTrue_win_add` — two continuations of a shared prefix that
  agree off the win event: one side is at most the win probability plus the
  other side
* `absDiff_prTrue_bind_le_of_agree` — the same bound on the absolute difference
* `advantageA_le_prTrue_win` — the advantage of every distinguisher on the
  verifier pair is at most the win probability
* `gameAdvBoundC_of_agree` — the verifier pair as a `GameAdvBoundC`, from a
  bound on the win probability

## References

* Shoup — Sequences of Games, ePrint 2004/332, Lemma 1
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.VerifierPair

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {σ : Type}

/-- Two continuations `k₁`, `k₂` of a shared prefix `c` that agree on every
    state outside the win event: the `true`-probability of `c >>= k₁` is at
    most the win probability plus that of `c >>= k₂`. -/
theorem prTrue_bind_le_prTrue_win_add (c : SPComp σ) (k₁ k₂ : σ → SPComp Bool)
    (win : σ → Bool) (hagree : ∀ s, win s = false → k₁ s = k₂ s) (h₀ : Heap) :
    prTrue (c.bind k₁) h₀ ≤
      prTrue (c.bind fun s => SPComp.pure (win s)) h₀ + prTrue (c.bind k₂) h₀ := by
  refine ForkingLemma.prTrue_bind_le_add _ _ _ _ _ fun s h' => ?_
  cases hw : win s
  · rw [hagree s hw]; exact le_add_self
  · rw [ForkingLemma.prTrue_pure_bool, if_pos rfl]; exact le_add_right (prTrue_le_one _ _)

/-- Two continuations of a shared prefix that agree outside the win event
    differ in `true`-probability by at most the win probability. -/
theorem absDiff_prTrue_bind_le_of_agree (c : SPComp σ) (k₁ k₂ : σ → SPComp Bool)
    (win : σ → Bool) (hagree : ∀ s, win s = false → k₁ s = k₂ s) (h₀ : Heap) :
    absDiff (prTrue (c.bind k₁) h₀) (prTrue (c.bind k₂) h₀) ≤
      prTrue (c.bind fun s => SPComp.pure (win s)) h₀ :=
  sup_le (tsub_le_iff_right.mpr (prTrue_bind_le_prTrue_win_add c k₁ k₂ win hagree h₀))
    (tsub_le_iff_right.mpr (prTrue_bind_le_prTrue_win_add c k₂ k₁ win
      (fun s hs => (hagree s hs).symm) h₀))

/-- **Verifier pair, per distinguisher**: a real and an ideal verifier on the
    outcome of one experiment `exp` that agree outside the win event give every
    distinguisher `D` advantage at most the win probability. -/
theorem advantageA_le_prTrue_win (exp : SPComp σ) (real ideal win : σ → Bool)
    (hagree : ∀ s, win s = false → real s = ideal s) (D : Bool → SPComp Bool) :
    AdvantageA (exp.bind fun s => SPComp.pure (real s))
        (exp.bind fun s => SPComp.pure (ideal s)) D ≤
      prTrue (exp.bind fun s => SPComp.pure (win s)) Heap.empty := by
  simp only [AdvantageA, SPComp.bind_assoc, SPComp.pure_bind]
  exact absDiff_prTrue_bind_le_of_agree exp _ _ win (fun s hs => by rw [hagree s hs]) _

/-- The verifier pair as a concrete game bound: if the win probability on input
    `x` is at most `bound x D` for every distinguisher `D`, the pair satisfies
    `GameAdvBoundC` with `bound`. -/
theorem gameAdvBoundC_of_agree {hon : Type*} (exp : hon → SPComp σ)
    (real ideal win : hon → σ → Bool) (bound : hon → (Bool → SPComp Bool) → ℝ≥0∞)
    (hagree : ∀ x s, win x s = false → real x s = ideal x s)
    (hwin : ∀ x D, prTrue ((exp x).bind fun s => SPComp.pure (win x s)) Heap.empty ≤
      bound x D) :
    UCConcrete.GameAdvBoundC (fun x => (exp x).bind fun s => SPComp.pure (real x s))
      (fun x => (exp x).bind fun s => SPComp.pure (ideal x s)) bound :=
  ⟨fun x D => (advantageA_le_prTrue_win (exp x) (real x) (ideal x) (win x) (hagree x) D).trans
    (hwin x D)⟩

end CatCrypt.Crypto.VerifierPair
