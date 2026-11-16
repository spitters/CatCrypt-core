/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversary

/-!
# Runs of oracle adversaries through a state map on an invariant

A map `f` of oracle states that commutes with every call of the oracle `O` from the states
satisfying an invariant `Inv`, which every call from such a state keeps on its support,
commutes with every run of an adaptive oracle adversary from such a state. The form without an
invariant is `OracleAdv.run_map_state` of `CatCryptCore.Crypto.OracleAdversary`.

## Main results

* `OracleAdv.run_map_state_of_inv` — a state map commuting with the oracle calls from the
  states of an invariant commutes with the runs from those states
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

variable {S S' D R α : Type}

/-- **State maps under an invariant.** A map `f` of oracle states that commutes with every
oracle call from the states satisfying `Inv`, an invariant kept on the support of every call,
commutes with every run from such a state. -/
theorem run_map_state_of_inv (O : S → D → PMF (R × S)) (O' : S' → D → PMF (R × S'))
    (f : S → S') (Inv : S → Prop)
    (hInv : ∀ s d, Inv s → ∀ x ∈ (O s d).support, Inv x.2)
    (hO : ∀ s d, Inv s → (O s d).map (Prod.map id f) = O' (f s) d)
    (A : OracleAdv D R α) (s : S) (hs : Inv s) :
    (run O A s).map (Prod.map id f) = run O' A (f s) := by
  induction A generalizing s with
  | ret a => simp [PMF.pure_map]
  | rand p k ih =>
    simp only [run_rand, PMF.map_bind]
    exact congrArg _ (funext fun b => ih b s hs)
  | query d k ih =>
    simp only [run_query, PMF.map_bind]
    rw [← hO s d hs, PMF.bind_map]
    exact PMF.bind_congr_support _ _ _ fun x hx => ih x.1 x.2 (hInv s d hs x hx)

end CatCrypt.Crypto.OracleAdv
