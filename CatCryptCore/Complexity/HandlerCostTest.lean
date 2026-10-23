/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.HandlerCost
public import CatCryptCore.Quantum.QROM.PolyOracle

/-!
# Handler-cost bounds of the self-sampling quantum reductions

The costed mirrors of `qRedSamp` and `qRedPoly` over a gate set `GS`. The distinguisher `E` is
given by its costed mirror `E'`, one costed circuit per input and coins, of gate time at most
`TE` and classical set-up cost at most `cE₀`; the oracle `auxOracle` of the sampled tables is
answered by a handler word `v` of cost at most `h`, computed at classical cost at most `cv₀`.
The reduction makes no oracle call, and its time is at most
`cE₀ + cv₀ + TE + flatQ q k q * h`: the gates of the distinguisher, and the handler word at each
of its at most `flatQ q k q` calls. For `qRedPoly`, `cv₀` is `4 * auxDeg q k` coefficient
samples plus the cost `cw₀` of computing the handler word from the coefficients.

The costed mirrors here are written by hand as worked examples of the cost model of
`HandlerCost`; they are named `costed`, not `timed`, because the time certificates of these
reductions come from `derive_timed_structure` once it gives circuit-valued fields the rule
stated in `HandlerCost`.

## Main results

* `qRedSamp.erases_costed`, `qRedSamp.timeBound_costed` — `qRedSamp`
* `qRedPoly.erases_costed`, `qRedPoly.timeBound_costed` — `qRedPoly`, with the polynomial tables
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Complexity.HandlerCost.Test

open CatCrypt.Quantum.QROM CatCrypt.Crypto.MLKEM
open CatCrypt.Crypto.PKE.Games (Scheme)

section Samp

variable {m₁ m₂ n W q k c a : ℕ} {PK SK M C R K Hash Z ι X : Type}
  [DecidableEq Z] [Nonempty K] [DecidableEq C] [DecidableEq Hash]
  (S : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a) [NeZero n] [NeZero c]
  (key : X → PK)
  {ΩG ΩJ ΩH ΩT : Type} (ΦG : ΩG → Fin m₁ → Fin n) (ΦJ : ΩJ → Fin m₂ → Fin n)
  (ΦH : ΩH → C → K) (ΦT : ΩT → C → Fin n)
  (E : QAuxDist ι X (m₁ + m₂) n W q k c a C K)
  (GS : GateSet ((m₁ + m₂) * n * ancW c k W))
  (E' : ∀ (x : X) (s : ι × Z × ΩG × ΩJ × ΩH × ΩT),
    QAdv.Timed GS (E.stop x (ΦH s.2.2.2.2.1 (E.point x s.1)) s.1))
  (v : X → ι × Z × ΩG × ΩJ × ΩH × ΩT → List GS.G)

/-- The costed mirror of `qRedSamp`: the costed run of `E` with the handler word `v x s` in
place of each oracle call. -/
def qRedSamp.costed (x : X) (s : ι × Z × ΩG × ΩJ × ΩH × ΩT) : QAdv.Timed GS 0 :=
  (E' x s).absorb (v x s)

/-- The mirror erases to `qRedSamp` when `E'` erases to the runs of `E` and each handler word
implements the oracle unitary of the sampled tables. -/
theorem qRedSamp.erases_costed
    (hE : ∀ x s, (E' x s).Erases
      (auxRunAdv eC eKa E x (ΦH s.2.2.2.2.1 (E.point x s.1)) (ΦH s.2.2.2.2.1) s.1))
    (hv : ∀ x s, GS.eval (v x s) = oracleU (m₁ + m₂) n (ancW c k W)
      (auxOracle S hpk eG eJ eKR (key x) (ΦH s.2.2.2.2.1) (ΦG s.2.2.1) (ΦJ s.2.2.2.1)
        (ΦT s.2.2.2.2.2) s.2.1)) (x : X) (s : ι × Z × ΩG × ΩJ × ΩH × ΩT) :
    (qRedSamp.costed ΦH E GS E' v x s).Erases
      (qRedSamp S hpk eG eJ eKR eC eKa key ΦG ΦJ ΦH ΦT E x s) :=
  QAdv.Timed.erases_absorb (hE x s) _ (hv x s)

omit [DecidableEq Z] [Nonempty K] [DecidableEq C] [NeZero n] [NeZero c] in
/-- **Time of `qRedSamp`.** With set-up costs `cE x s ≤ cE₀` and `cv x s ≤ cv₀`, gate time of
`E'` at most `TE` and handler words of cost at most `h`, the reduction runs in at most
`cE₀ + cv₀ + TE + flatQ q k q * h`. -/
theorem qRedSamp.timeBound_costed (cE cv : X → ι × Z × ΩG × ΩJ × ΩH × ΩT → ℕ)
    {cE₀ cv₀ TE h : ℕ} (hcE : ∀ x s, cE x s ≤ cE₀) (hcv : ∀ x s, cv x s ≤ cv₀)
    (hE : ∀ x s, (E' x s).gateTime ≤ TE) (hv : ∀ x s, GS.cost (v x s) ≤ h)
    (x : X) (s : ι × Z × ΩG × ΩJ × ΩH × ΩT) :
    cE x s + cv x s + (qRedSamp.costed ΦH E GS E' v x s).time 0 ≤
      cE₀ + cv₀ + TE + flatQ q k q * h := by
  rw [qRedSamp.costed, QAdv.Timed.time_absorb]
  have h1 := Nat.mul_le_mul (E.stop x (ΦH s.2.2.2.2.1 (E.point x s.1)) s.1).isLt.le (hv x s)
  have := hcE x s
  have := hcv x s
  have := hE x s
  omega

end Samp

section Poly

variable {m₁ m₂ n W q k c a : ℕ} {SK C R K Hash Z ι X : Type}
  [Fintype Z] [DecidableEq Z] [Fintype K] [Nonempty K] [DecidableEq K] [Fintype C]
  [DecidableEq C] [DecidableEq Hash] [Fintype ι]
  (B : MLWE_PKE_Basic.Params) (S : Scheme (MLWE_PKE_Basic.PK B) SK B.PT C R)
  (hpk : MLWE_PKE_Basic.PK B → Hash) (eG : (B.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n] [NeZero c]
  (PG : PolyData (Fin m₁) (Fin n)) (PJ : PolyData (Fin m₂) (Fin n)) (PH : PolyData C K)
  (PT : PolyData C (Fin n)) (key : X → MLWE_PKE_Basic.PK B)
  (E : QAuxDist ι X (m₁ + m₂) n W q k c a C K)
  (GS : GateSet ((m₁ + m₂) * n * ancW c k W))
  (E' : ∀ (x : X) (s : ι × Z × (Fin (auxDeg q k) → PG.F) × (Fin (auxDeg q k) → PJ.F) ×
      (Fin (auxDeg q k) → PH.F) × (Fin (auxDeg q k) → PT.F)),
    QAdv.Timed GS (E.stop x (PH.table (auxDeg q k) s.2.2.2.2.1 (E.point x s.1)) s.1))
  (v : X → ι × Z × (Fin (auxDeg q k) → PG.F) × (Fin (auxDeg q k) → PJ.F) ×
      (Fin (auxDeg q k) → PH.F) × (Fin (auxDeg q k) → PT.F) → List GS.G)

omit [Fintype Z] [Fintype C] [Fintype ι] in
/-- The mirror of `qRedSamp` at the polynomial tables erases to `qRedPoly`. -/
theorem qRedPoly.erases_costed
    (hE : ∀ x s, (E' x s).Erases
      (auxRunAdv eC eKa E x (PH.table (auxDeg q k) s.2.2.2.2.1 (E.point x s.1))
        (PH.table (auxDeg q k) s.2.2.2.2.1) s.1))
    (hv : ∀ x s, GS.eval (v x s) = oracleU (m₁ + m₂) n (ancW c k W)
      (auxOracle S hpk eG eJ eKR (key x) (PH.table (auxDeg q k) s.2.2.2.2.1)
        (PG.table (auxDeg q k) s.2.2.1) (PJ.table (auxDeg q k) s.2.2.2.1)
        (PT.table (auxDeg q k) s.2.2.2.2.2) s.2.1)) (x : X)
    (s : ι × Z × (Fin (auxDeg q k) → PG.F) × (Fin (auxDeg q k) → PJ.F) ×
      (Fin (auxDeg q k) → PH.F) × (Fin (auxDeg q k) → PT.F)) :
    (qRedSamp.costed (PH.table (auxDeg q k)) E GS E' v x s).Erases
      (qRedPoly B S hpk eG eJ eKR eC eKa PG PJ PH PT key E x s) :=
  qRedSamp.erases_costed S hpk eG eJ eKR eC eKa key _ _ _ _ E GS E' v hE hv x s

omit [Fintype Z] [Fintype C] [Fintype ι] [DecidableEq Z] [Nonempty K] [DecidableEq C] [NeZero n]
  [NeZero c] in
/-- **Time of `qRedPoly`.** Drawing the `auxDeg q k` coefficients of each of the four tables
costs one unit per coefficient; with the handler word computed from the coefficients at cost
at most `cw₀` and of cost at most `h`, the reduction runs in at most
`cE₀ + 4 * auxDeg q k + cw₀ + TE + flatQ q k q * h`. -/
theorem qRedPoly.timeBound_costed
    (cE cw : X → ι × Z × (Fin (auxDeg q k) → PG.F) × (Fin (auxDeg q k) → PJ.F) ×
      (Fin (auxDeg q k) → PH.F) × (Fin (auxDeg q k) → PT.F) → ℕ)
    {cE₀ cw₀ TE h : ℕ} (hcE : ∀ x s, cE x s ≤ cE₀) (hcw : ∀ x s, cw x s ≤ cw₀)
    (hE : ∀ x s, (E' x s).gateTime ≤ TE) (hv : ∀ x s, GS.cost (v x s) ≤ h) (x : X)
    (s : ι × Z × (Fin (auxDeg q k) → PG.F) × (Fin (auxDeg q k) → PJ.F) ×
      (Fin (auxDeg q k) → PH.F) × (Fin (auxDeg q k) → PT.F)) :
    cE x s + (4 * auxDeg q k + cw x s) +
        (qRedSamp.costed (PH.table (auxDeg q k)) E GS E' v x s).time 0 ≤
      cE₀ + 4 * auxDeg q k + cw₀ + TE + flatQ q k q * h := by
  have := qRedSamp.timeBound_costed (PH.table (auxDeg q k)) E GS E' v cE
    (fun x s => 4 * auxDeg q k + cw x s) hcE (cv₀ := 4 * auxDeg q k + cw₀)
    (fun x s => Nat.add_le_add_left (hcw x s) _) hE hv x s
  omega

end Poly

end CatCrypt.Complexity.HandlerCost.Test
