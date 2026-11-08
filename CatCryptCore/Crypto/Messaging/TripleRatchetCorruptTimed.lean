/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.TripleRatchetCorrupt

/-!
# Running time of the reductions of the product CKA

Time certificates for the reductions `prodCorruptRed₁` and `prodCorruptRed₂` of
`CatCryptCore.Crypto.Messaging.TripleRatchetCorrupt`.

Each reduction is the oracle tree `R.tree` with the interaction of the product adversary as a
parameter; its costed form is derived by `derive_timed`, and `R.compile_tree` states that the
erased costed tree is the reduction at a costed interaction erasing to the adversary's. The
costed simulators `prodSimImpl₁.timed`, `prodSimImpl₂.timed` keep cost companions of the party
states and epoch counters of the component game they run themselves; each update adds at most
three units, so after `i` queries the companions are at most `1 + 3 i` (`prodCostInv`), the
invariant of `OracleAdv.Timed.timeBound_simulateHat_inv`. The `i`-th simulated query then costs
at most `3 s + v + 10 (1 + 3 i) + 60` (`prodQueryTime`), for sends of cost at most `s` and
receives of cost at most `v`. For an adversary of time `T` with at most `q` queries and call
cost at most `a`, each reduction has time at most `T + ∑_{j < q} prodQueryTime s v (1 + 3 j) +
a + 5`, a polynomial of degree two in `q`.

No module imports this file.

## Main results

* `prodSimImpl₁.timed_bound`, `prodSimImpl₂.timed_bound` — the time of a simulated query under
  the companion invariant
* `prodCorruptRed₁.tree`, `prodCorruptRed₁.compile_tree`, `prodCorruptRed₁.timeBound_timed` —
  the reduction to the first component
* `prodCorruptRed₂.tree`, `prodCorruptRed₂.compile_tree`, `prodCorruptRed₂.timeBound_timed` —
  the reduction to the second component
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions

variable {S₁ M₁ K₁ R₁ S₂ M₂ K₂ R₂ : Type}

/-- The time of a tree that draws `x` from `μ` at the step cost `c x` and then runs a
step-prefixed tree `S x` of time at most `B`, returning the first component of its output. -/
private theorem rand_cost_bind_fst {D R X Ŝ : Type} (μ : PMF X) (c : X → ℕ)
    (S : X → ℕ × OracleAdv.Timed D R (Bool × Ŝ)) {K B : ℕ} (hc : ∀ x, c x ≤ K)
    (hS : ∀ x, OracleAdv.Timed.StepTimeBound (S x) B) :
    OracleAdv.Timed.StepTimeBound (0, OracleAdv.Timed.rand μ
      (fun x => c x + (S x).1 + ((S x).2.bind fun r => (0, OracleAdv.Timed.ret r.1)).1)
      fun x => ((S x).2.bind fun r => (0, OracleAdv.Timed.ret r.1)).2) (K + B + 1) := by
  refine ⟨Nat.zero_le _, by dsimp only; omega, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hS x
  obtain ⟨h3, h4⟩ := OracleAdv.Timed.timeBound_bind (n := 0) h2
    (f := fun r => (0, OracleAdv.Timed.ret r.1)) fun _ => ⟨le_refl _, trivial⟩
  have := hc x
  refine ⟨by dsimp only; omega, h4.mono ?_⟩
  dsimp only; omega

section Red₁

variable [Fintype R₂] [Nonempty R₂]

/-- The oracle tree of the reduction `prodCorruptRed₁` at the challenge epoch `t` and the public
value `pub₁`, for the interaction `play` of the product adversary. -/
noncomputable def prodCorruptRed₁.tree (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₂ R₂]
    (initP₂ : PMF (M₂ × S₂ × S₂)) (ΔPCS : ℕ)
    (play : ℕ → M₁ × M₂ →
      OracleAdv CKAQuery (CKAAns (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂)) Bool)
    (t : ℕ) (pub₁ : M₁) : OracleAdv CKAQuery (CKAAns S₁ M₁ K₁ R₁) Bool :=
  prodCorruptTree₁ C₂ initP₂ ΔPCS play t pub₁

derive_timed prodCorruptRed₁.tree

/-- The bound `B` on the cost companions of a costed CKA game state: the companions of the
party states and of the epoch counters. -/
def prodCostInv {S M : Type} (B : ℕ)
    (ŝ : ((CKAParty → S) × (CKAParty → ℕ)) × ((CKAParty → ℕ) × (CKAParty → ℕ)) × M) : Prop :=
  (∀ p, ŝ.1.2 p ≤ B) ∧ ∀ p, ŝ.2.1.2 p ≤ B

/-- The time of a simulated query of a product reduction from a state with companions at most
`B`, with sends of cost at most `s` and receives of cost at most `v`. -/
def prodQueryTime (s v B : ℕ) : ℕ := 3 * s + v + 10 * B + 60

/-- **Time of a query of the simulator of `prodCorruptRed₁`.** From a costed state with
companions at most `1 + 3 i`, the costed simulator `prodSimImpl₁` answers in time at most
`prodQueryTime s v (1 + 3 i)` and returns states with companions at most `1 + 3 (i + 1)`. -/
theorem prodSimImpl₁.timed_bound (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₂ R₂] (ΔPCS t : ℕ)
    (sCost : S₂ → R₂ → ℕ) (vCost : S₂ → M₂ → ℕ) {s v : ℕ} (hs : ∀ x r, sCost x r ≤ s)
    (hv : ∀ x m, vCost x m ≤ v) (i : ℕ)
    (ŝ : ((CKAParty → S₂) × (CKAParty → ℕ)) × ((CKAParty → ℕ) × (CKAParty → ℕ)) × M₂)
    (q : CKAQuery) (hinv : prodCostInv (1 + 3 * i) ŝ) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay 1
        (prodSimImpl₁.timed (S₁ := S₁) (M₁ := M₁) (K₁ := K₁) (R₁ := R₁) (K₂ := K₂) C₂ ΔPCS t
          { st := ŝ.1.1, t := ŝ.2.1.1, msg := ŝ.2.2 } q sCost ŝ.1.2 vCost ŝ.2.1.2))
        (prodQueryTime s v (1 + 3 * i)) ∧
      OracleAdv.Timed.AllRet (fun y => prodCostInv (1 + 3 * (i + 1)) y.2)
        (prodSimImpl₁.timed (S₁ := S₁) (M₁ := M₁) (K₁ := K₁) (R₁ := R₁) (K₂ := K₂) C₂ ΔPCS t
          { st := ŝ.1.1, t := ŝ.2.1.1, msg := ŝ.2.2 } q sCost ŝ.1.2 vCost ŝ.2.1.2).2 := by
  obtain ⟨h1, h2⟩ := hinv
  unfold prodCostInv prodQueryTime
  cases q <;>
    simp only [prodSimImpl₁.timed, OracleAdv.Timed.delay,
      OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet] <;>
    repeat' (first | trivial | apply And.intro | intro _ | split |
      dsimp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound,
        OracleAdv.Timed.AllRet] | grind)

/-- The derived costed tree of `prodCorruptRed₁`, at a costed interaction `play` that erases to
the interaction of `A`, erases to the interaction of the reduction. -/
theorem prodCorruptRed₁.compile_tree (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₂ R₂]
    (initP₂ : PMF (M₂ × S₂ × S₂)) (ΔPCS : ℕ)
    (A : CKACorruptAdv (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂) Bool)
    (play : ℕ → M₁ × M₂ →
      OracleAdv.Timed CKAQuery (CKAAns (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂)) Bool)
    (playCost : ℕ → M₁ × M₂ → ℕ) (hplay : ∀ t g, (play t g).erase = A.play t g) (t : ℕ)
    (pub₁ : M₁) (sCost : S₂ → R₂ → ℕ) (vCost : S₂ → M₂ → ℕ) :
    (prodCorruptRed₁.tree.timed C₂ initP₂ ΔPCS play playCost t pub₁ sCost vCost).2.erase =
      (prodCorruptRed₁ C₂ initP₂ ΔPCS A).play t pub₁ := by
  rw [prodCorruptRed₁.tree.erase_timed]
  have h : (fun t g => (play t g).erase) = A.play := funext fun t => funext (hplay t)
  rw [h]
  rfl

/-- **Time of `prodCorruptRed₁`.** For a costed interaction of time at most `T`, at most `q`
queries and call cost at most `a`, sends of `C₂` of cost at most `s` and receives of cost at
most `v`, the derived costed tree of `prodCorruptRed₁` has time at most
`T + ∑_{j < q} (3 s + v + 10 (1 + 3 j) + 60) + a + 5`: one simulated query per query, whose
cost grows with the cost companions of the game state of `C₂`. -/
theorem prodCorruptRed₁.timeBound_timed (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₂ R₂]
    (initP₂ : PMF (M₂ × S₂ × S₂)) (ΔPCS : ℕ)
    (play : ℕ → M₁ × M₂ →
      OracleAdv.Timed CKAQuery (CKAAns (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂)) Bool)
    (playCost : ℕ → M₁ × M₂ → ℕ) (t : ℕ) (pub₁ : M₁) (sCost : S₂ → R₂ → ℕ)
    (vCost : S₂ → M₂ → ℕ) {T q a s v : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hs : ∀ x r, sCost x r ≤ s) (hv : ∀ x m, vCost x m ≤ v) :
    OracleAdv.Timed.StepTimeBound
      (prodCorruptRed₁.tree.timed C₂ initP₂ ΔPCS play playCost t pub₁ sCost vCost)
      (T + ∑ j ∈ Finset.range q, prodQueryTime s v (1 + 3 * j) + a + 5) := by
  unfold prodCorruptRed₁.tree.timed prodCorruptTree₁.timed
  dsimp only
  refine (OracleAdv.Timed.stepTimeBound_delay (rand_cost_bind_fst (K := 2 + a)
    (B := T + ∑ j ∈ Finset.range q, prodQueryTime s v (1 + 3 * j)) _ _ _
    (fun x => by have := ha t (pub₁, x.1); omega) fun i₂ => ?_)).mono (by omega)
  refine (OracleAdv.Timed.timeBound_simulateHat_inv _ _ _
    (fun i ŝ => prodCostInv (1 + 3 * i) ŝ) (fun i => prodQueryTime s v (1 + 3 * i))
    (fun i ŝ d h => prodSimImpl₁.timed_bound C₂ ΔPCS t sCost vCost hs hv i ŝ d h)
    (hA t _) (hq t _) 0 _ ?_).mono ?_
  · exact ⟨fun _ => by grind, fun _ => by grind⟩
  · simp only [Nat.zero_add, le_refl]

end Red₁

section Red₂

variable [Fintype R₁] [Nonempty R₁] [Fintype K₁] [Nonempty K₁]

/-- The oracle tree of the reduction `prodCorruptRed₂` at the challenge epoch `t` and the public
value `pub₂`, for the interaction `play` of the product adversary. -/
noncomputable def prodCorruptRed₂.tree (C₁ : CKADef S₁ M₁ K₁) [CKACoins C₁ R₁]
    (initP₁ : PMF (M₁ × S₁ × S₁)) (ΔPCS : ℕ)
    (play : ℕ → M₁ × M₂ →
      OracleAdv CKAQuery (CKAAns (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂)) Bool)
    (t : ℕ) (pub₂ : M₂) : OracleAdv CKAQuery (CKAAns S₂ M₂ K₂ R₂) Bool :=
  prodCorruptTree₂ C₁ initP₁ ΔPCS play t pub₂

derive_timed prodCorruptRed₂.tree

/-- **Time of a query of the simulator of `prodCorruptRed₂`.** From a costed state with
companions at most `1 + 3 i`, the costed simulator `prodSimImpl₂` answers in time at most
`prodQueryTime s v (1 + 3 i)` and returns states with companions at most `1 + 3 (i + 1)`. -/
theorem prodSimImpl₂.timed_bound (C₁ : CKADef S₁ M₁ K₁) [CKACoins C₁ R₁] (ΔPCS t : ℕ)
    (sCost : S₁ → R₁ → ℕ) (vCost : S₁ → M₁ → ℕ) {s v : ℕ} (hs : ∀ x r, sCost x r ≤ s)
    (hv : ∀ x m, vCost x m ≤ v) (i : ℕ)
    (ŝ : ((CKAParty → S₁) × (CKAParty → ℕ)) × ((CKAParty → ℕ) × (CKAParty → ℕ)) × M₁)
    (q : CKAQuery) (hinv : prodCostInv (1 + 3 * i) ŝ) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay 1
        (prodSimImpl₂.timed (S₂ := S₂) (M₂ := M₂) (K₂ := K₂) (R₂ := R₂) C₁ ΔPCS t
          { st := ŝ.1.1, t := ŝ.2.1.1, msg := ŝ.2.2 } q sCost ŝ.1.2 vCost ŝ.2.1.2))
        (prodQueryTime s v (1 + 3 * i)) ∧
      OracleAdv.Timed.AllRet (fun y => prodCostInv (1 + 3 * (i + 1)) y.2)
        (prodSimImpl₂.timed (S₂ := S₂) (M₂ := M₂) (K₂ := K₂) (R₂ := R₂) C₁ ΔPCS t
          { st := ŝ.1.1, t := ŝ.2.1.1, msg := ŝ.2.2 } q sCost ŝ.1.2 vCost ŝ.2.1.2).2 := by
  obtain ⟨h1, h2⟩ := hinv
  unfold prodCostInv prodQueryTime
  cases q <;>
    simp only [prodSimImpl₂.timed, OracleAdv.Timed.delay,
      OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet] <;>
    repeat' (first | trivial | apply And.intro | intro _ | split |
      dsimp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound,
        OracleAdv.Timed.AllRet] | grind)

/-- The derived costed tree of `prodCorruptRed₂`, at a costed interaction `play` that erases to
the interaction of `A`, erases to the interaction of the reduction. -/
theorem prodCorruptRed₂.compile_tree (C₁ : CKADef S₁ M₁ K₁) [CKACoins C₁ R₁]
    (initP₁ : PMF (M₁ × S₁ × S₁)) (ΔPCS : ℕ)
    (A : CKACorruptAdv (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂) Bool)
    (play : ℕ → M₁ × M₂ →
      OracleAdv.Timed CKAQuery (CKAAns (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂)) Bool)
    (playCost : ℕ → M₁ × M₂ → ℕ) (hplay : ∀ t g, (play t g).erase = A.play t g) (t : ℕ)
    (pub₂ : M₂) (sCost : S₁ → R₁ → ℕ) (vCost : S₁ → M₁ → ℕ) :
    (prodCorruptRed₂.tree.timed C₁ initP₁ ΔPCS play playCost t pub₂ sCost vCost).2.erase =
      (prodCorruptRed₂ C₁ initP₁ ΔPCS A).play t pub₂ := by
  rw [prodCorruptRed₂.tree.erase_timed]
  have h : (fun t g => (play t g).erase) = A.play := funext fun t => funext (hplay t)
  rw [h]
  rfl

/-- **Time of `prodCorruptRed₂`.** For a costed interaction of time at most `T`, at most `q`
queries and call cost at most `a`, sends of `C₁` of cost at most `s` and receives of cost at
most `v`, the derived costed tree of `prodCorruptRed₂` has time at most
`T + ∑_{j < q} (3 s + v + 10 (1 + 3 j) + 60) + a + 5`: one simulated query per query, whose
cost grows with the cost companions of the game state of `C₁`. -/
theorem prodCorruptRed₂.timeBound_timed (C₁ : CKADef S₁ M₁ K₁) [CKACoins C₁ R₁]
    (initP₁ : PMF (M₁ × S₁ × S₁)) (ΔPCS : ℕ)
    (play : ℕ → M₁ × M₂ →
      OracleAdv.Timed CKAQuery (CKAAns (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂)) Bool)
    (playCost : ℕ → M₁ × M₂ → ℕ) (t : ℕ) (pub₂ : M₂) (sCost : S₁ → R₁ → ℕ)
    (vCost : S₁ → M₁ → ℕ) {T q a s v : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hs : ∀ x r, sCost x r ≤ s) (hv : ∀ x m, vCost x m ≤ v) :
    OracleAdv.Timed.StepTimeBound
      (prodCorruptRed₂.tree.timed C₁ initP₁ ΔPCS play playCost t pub₂ sCost vCost)
      (T + ∑ j ∈ Finset.range q, prodQueryTime s v (1 + 3 * j) + a + 5) := by
  unfold prodCorruptRed₂.tree.timed prodCorruptTree₂.timed
  dsimp only
  refine (OracleAdv.Timed.stepTimeBound_delay (rand_cost_bind_fst (K := 2 + a)
    (B := T + ∑ j ∈ Finset.range q, prodQueryTime s v (1 + 3 * j)) _ _ _
    (fun x => by have := ha t (x.1, pub₂); omega) fun i₁ => ?_)).mono (by omega)
  refine (OracleAdv.Timed.timeBound_simulateHat_inv _ _ _
    (fun i ŝ => prodCostInv (1 + 3 * i) ŝ) (fun i => prodQueryTime s v (1 + 3 * i))
    (fun i ŝ d h => prodSimImpl₂.timed_bound C₁ ΔPCS t sCost vCost hs hv i ŝ d h)
    (hA t _) (hq t _) 0 _ ?_).mono ?_
  · exact ⟨fun _ => by grind, fun _ => by grind⟩
  · simp only [Nat.zero_add, le_refl]

end Red₂

end CatCrypt.Crypto.Messaging
