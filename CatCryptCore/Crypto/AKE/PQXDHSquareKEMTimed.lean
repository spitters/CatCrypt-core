/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHSquareKEM
public import CatCryptCore.Crypto.AKE.X3DHSquareGDHTimed

/-!
# Running time of the KEM reduction of the PQXDH square

Draft.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.PQXDHSquareKEM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

derive_timed stepImplQ

derive_timed stepRedQ


section Generic

variable {σ E A V Q Ans Out : Type}

/-- **The time of `stepRedQ`.** Let `Inv i` hold of the states reached after `i` steps, with the
costs of the query decision, of the draw distribution and of a step from a state of `Inv i`
together at most `F i` (`F` monotone), and an extraction from a state of `Inv i` of cost at most
`Ext i`. Then a costed adversary `B` of time `T` with at most `q` queries gives a costed reduction
of time at most `T + q · (F q + 7) + Ext q + 1`. -/
theorem stepRedQ.timeBound_timed (need : σ → E → Option Q) (needCost : σ → E → ℕ)
    (μ : σ → E → PMF V) (μCost : σ → E → ℕ) (step : Option Ans → σ → E → V → σ × A)
    (stepCost : Option Ans → σ → E → V → ℕ) (ext : σ → Out) (extCost : σ → ℕ)
    (Inv : ℕ → σ → Prop) (F Ext : ℕ → ℕ) (hF : Monotone F)
    (hmono : ∀ i t, Inv i t → Inv (i + 1) t)
    (hstep : ∀ i t e oa r, Inv i t → Inv (i + 1) (step oa t e r).1)
    (hcost : ∀ i t e oa r, Inv i t → needCost t e + μCost t e + stepCost oa t e r ≤ F i)
    (hext : ∀ i t, Inv i t → extCost t ≤ Ext i)
    (B : OracleAdv.Timed E A Bool) {T q : ℕ} (hB : B.TimeBound T) (hq : B.erase.IsQueryBound q)
    (s₀ : σ) (h0 : Inv 0 s₀) :
    OracleAdv.Timed.StepTimeBound
      (stepRedQ.timed need needCost μ μCost step stepCost ext extCost B s₀)
      (T + q * (F q + 7) + (Ext q + 1)) := by
  unfold stepRedQ.timed
  generalize hI : (fun (t : σ) (e : E) => OracleAdv.Timed.delay 1
    (stepImplQ.timed need needCost μ μCost step stepCost t e)) = impl
  have himpl : ∀ i s d, Inv i s →
      OracleAdv.Timed.StepTimeBound (impl s d) (F i + 7) ∧
        OracleAdv.Timed.AllRet (fun y => Inv (i + 1) y.2) (impl s d).2 := by
    intro i s d hs
    subst hI
    obtain ⟨r₀, -⟩ := (μ s d).support_nonempty
    have h₀ := hcost i s d none r₀ hs
    simp only [stepImplQ.timed, OracleAdv.Timed.delay]
    cases hn : need s d with
    | some c =>
      dsimp only
      refine ⟨⟨?_, ?_, fun a => ⟨?_, ?_, fun r => ⟨?_, trivial⟩⟩⟩, fun a r => hstep i s d _ r hs⟩
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · have := hcost i s d (some a) r hs
        dsimp only; omega
    | none =>
      dsimp only
      refine ⟨⟨?_, ?_, fun r => ⟨?_, trivial⟩⟩, fun r => hstep i s d _ r hs⟩
      · dsimp only; omega
      · dsimp only; omega
      · have := hcost i s d none r hs
        dsimp only; omega
  have hsim := OracleAdv.Timed.timeBound_simulateHat_inv id id impl Inv (fun i => F i + 7) himpl
    hB hq 0 s₀ h0
  have hall := OracleAdv.Timed.allRet_simulateHat_inv id id impl Inv
    (fun i s d h => (himpl i s d h).2) hmono hq 0 s₀ h0
  unfold OracleAdv.Timed.simulateHat at hsim hall
  simp only [Nat.zero_add] at hsim hall
  have hsum : ∑ j ∈ Finset.range q, (F j + 7) ≤ q * (F q + 7) := by
    calc ∑ j ∈ Finset.range q, (F j + 7) ≤ ∑ _j ∈ Finset.range q, (F q + 7) :=
          Finset.sum_le_sum fun j hj => by
            have := hF (le_of_lt (Finset.mem_range.mp hj)); omega
      _ = q * (F q + 7) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hbind := OracleAdv.Timed.timeBound_bind_of_allRet (n := Ext q + 1)
    (f := fun p => (1 + extCost p.2, OracleAdv.Timed.ret (ext p.2))) hsim.2 hall
    fun y hy => ⟨by have := hext q y.2 hy; dsimp only; omega, trivial⟩
  refine (OracleAdv.Timed.stepTimeBound_delay hbind).mono ?_
  have := hsim.1
  omega

end Generic

end CatCrypt.Crypto.AKE.PQXDHSquareKEM
