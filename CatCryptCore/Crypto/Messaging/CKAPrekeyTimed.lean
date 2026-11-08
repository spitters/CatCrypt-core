/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.CKAPrekey
import CatCryptCore.Tactics.DeriveTimed

/-!
# Running time of the DDH reduction of the CKA at a given pair

Time certificate of the DDH reduction `ckaCorruptDDHRedAt` of
`CatCryptCore.Crypto.Messaging.CKAPrekey`.

The reduction is the oracle tree `ckaCorruptDDHTreeAt` with the exponentiations and the
interaction of the adversary as parameters; its costed form, with the costs of the
exponentiations as parameters, is derived by `derive_timed`. The costed simulator
`ckaCorruptSimImplOf.timed` answers the `i`-th query in time at most `ckaSimQueryTime P X i`
under the companion invariant `ckaSimCostInv i` (`ckaCorruptSimImplOf.timed_bound`). For an
adversary of time `T` with at most `q` queries and call cost at most `a`, the reduction tree has
time at most `T + ∑_{j < q} ckaSimQueryTime P X j + a + 4`, a polynomial of degree two in `q`.

No module imports this file.

## Main results

* `ckaCorruptDDHTreeAt.timeBound_timed` — the time of the reduction tree
* `ckaCorruptDDHRedAt.tree`, `ckaCorruptDDHRedAt.compile_tree`,
  `ckaCorruptDDHRedAt.tree.timeBound_timed` — the reduction is the run of the erased costed
  tree, of time at most the bound above plus one
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCryptCore.Examples.CyclicGroupDDH

derive_timed ckaCorruptDDHTreeAt

/-- The time of a tree that draws `t` from `τ` at the step cost `c t`, and then runs a
step-prefixed tree `S t` of time at most `B` and returns the first component of its output. -/
private theorem timeBound_rand_bind {D R Ŝ α : Type} (τ : PMF ℕ) (c : ℕ → ℕ)
    (S : ℕ → ℕ × OracleAdv.Timed D R (α × Ŝ)) {K B : ℕ} (hc : ∀ t, c t ≤ K)
    (hS : ∀ t, OracleAdv.Timed.StepTimeBound (S t) B) :
    OracleAdv.Timed.StepTimeBound (0, OracleAdv.Timed.rand τ (fun t => c t + (S t).1 +
        ((S t).2.bind fun r => (0, OracleAdv.Timed.ret r.1)).1)
        fun t => ((S t).2.bind fun r => (0, OracleAdv.Timed.ret r.1)).2) (K + B + 2) := by
  refine ⟨Nat.zero_le _, by dsimp only; omega, fun t => ?_⟩
  obtain ⟨h1, h2⟩ := hS t
  obtain ⟨h3, h4⟩ := OracleAdv.Timed.timeBound_bind (n := 0) h2
    (f := fun r => (0, OracleAdv.Timed.ret r.1)) fun _ => ⟨le_refl _, trivial⟩
  have := hc t
  refine ⟨by dsimp only; omega, h4.mono ?_⟩
  dsimp only; omega

/-- **Time of the DDH reduction at a pair.** For an adversary whose costed trees have time at
most `T`, at most `q` queries and call cost at most `a`, and exponentiations of costs at most
`P` (of the generator) and `X` (of a group element), the costed reduction tree has time at most
`T + ∑_{j < q} (2 P + X + 21 j + 50) + a + 4`: the adversary and one simulated query per
query, whose cost grows with the closure layers of the simulator state. -/
theorem ckaCorruptDDHTreeAt.timeBound_timed {E Gr α : Type} [Fintype E] [Nonempty E]
    [Fintype Gr] [Nonempty Gr] (pow : E → Gr) (powCost : E → ℕ) (epow : Gr → E → Gr)
    (epowCost : Gr → E → ℕ) (ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → Gr → OracleAdv.Timed CKAQuery (CKAAns (Gr × E) Gr Gr E) α)
    (playCost : ℕ → Gr → ℕ) (i : Gr × (Gr × E) × (Gr × E)) (ga gb z : Gr) {T q a P X : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hP : ∀ x, powCost x ≤ P) (hX : ∀ g x, epowCost g x ≤ X) :
    OracleAdv.Timed.StepTimeBound
      (ckaCorruptDDHTreeAt.timed pow powCost epow epowCost ΔFS ΔPCS tStar play playCost i ga gb z)
      (T + ∑ j ∈ Finset.range q, ckaSimQueryTime P X j + a + 4) := by
  unfold ckaCorruptDDHTreeAt.timed
  refine (timeBound_rand_bind (K := a + 2)
    (B := T + ∑ j ∈ Finset.range q, ckaSimQueryTime P X j) _ _ _ ?_ ?_).mono (by omega)
  · intro t
    have := ha t i.1
    omega
  · intro t
    refine (OracleAdv.Timed.timeBound_simulateHat_inv _ _ _ ckaSimCostInv
      (ckaSimQueryTime P X)
      (fun n ŝ d h => ckaCorruptSimImplOf.timed_bound pow powCost epow epowCost ΔFS ΔPCS t ga gb z
          hP hX n _ d _ _ h.1 h.2) (hA t i.1) (hq t i.1) 0 _ ?_).mono ?_
    · exact ⟨fun p => le_refl _, fun p => Nat.zero_le _⟩
    · simp only [Nat.zero_add, le_refl]

/-- The oracle tree of the reduction `ckaCorruptDDHRedAt`: the tree `ckaCorruptDDHTreeAt` with
the exponentiations `pow` and `epow` as parameters, so that their costs are parameters of the
derived costed tree. -/
noncomputable def ckaCorruptDDHRedAt.tree {E Gr : Type} [Fintype E] [Nonempty E] [Fintype Gr]
    [Nonempty Gr] (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → Gr → OracleAdv CKAQuery (CKAAns (Gr × E) Gr Gr E) Bool)
    (i : Gr × (Gr × E) × (Gr × E)) (ga gb z : Gr) : OracleAdv Empty Unit Bool :=
  ckaCorruptDDHTreeAt pow epow ΔFS ΔPCS tStar play i ga gb z

derive_timed ckaCorruptDDHRedAt.tree

/-- **Time of `ckaCorruptDDHRedAt`.** The derived costed tree of `ckaCorruptDDHRedAt` has the
time bound of `ckaCorruptDDHTreeAt.timeBound_timed` plus one step:
`T + ∑_{j < q} ckaSimQueryTime P X j + a + 5`. -/
theorem ckaCorruptDDHRedAt.tree.timeBound_timed {E Gr : Type} [Fintype E] [Nonempty E]
    [Fintype Gr] [Nonempty Gr] (pow : E → Gr) (powCost : E → ℕ) (epow : Gr → E → Gr)
    (epowCost : Gr → E → ℕ) (ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → Gr → OracleAdv.Timed CKAQuery (CKAAns (Gr × E) Gr Gr E) Bool)
    (playCost : ℕ → Gr → ℕ) (i : Gr × (Gr × E) × (Gr × E)) (ga gb z : Gr) {T q a P X : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hP : ∀ x, powCost x ≤ P) (hX : ∀ g x, epowCost g x ≤ X) :
    OracleAdv.Timed.StepTimeBound
      (ckaCorruptDDHRedAt.tree.timed pow powCost epow epowCost ΔFS ΔPCS tStar play playCost i ga
        gb z)
      (T + ∑ j ∈ Finset.range q, ckaSimQueryTime P X j + a + 5) := by
  unfold ckaCorruptDDHRedAt.tree.timed
  exact (OracleAdv.Timed.stepTimeBound_delay (ckaCorruptDDHTreeAt.timeBound_timed pow powCost
    epow epowCost ΔFS ΔPCS tStar play playCost i ga gb z hA hq ha hP hX)).mono (by omega)

/-- **The reduction is the run of the erased costed tree.** At a costed interaction `play` that
erases to the interaction of `A`, the reduction `ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS A` is the
run of the erasure of the derived costed tree `ckaCorruptDDHRedAt.tree.timed` at the pair
`dhPairInit decE x₀`. -/
theorem ckaCorruptDDHRedAt.compile_tree {G : Type} [CG : CyclicGroup G] {Sk : Type}
    [Fintype Sk] [Nonempty Sk] [Inhabited Sk] (decE : Sk → CG.Exp) (x₀ : Sk) (ΔFS ΔPCS : ℕ)
    (A : CKACorruptAdv (G × Sk) G G Sk Bool) (powCost : Sk → ℕ) (epowCost : G → Sk → ℕ)
    (play : ℕ → G → OracleAdv.Timed CKAQuery (CKAAns (G × Sk) G G Sk) Bool)
    (playCost : ℕ → G → ℕ) (hplay : ∀ t g, (play t g).erase = A.play t g) (tr : G × G × G) :
    ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS A tr =
      liftPMF ((OracleAdv.run emptyOracle (ckaCorruptDDHRedAt.tree.timed
        (fun x => CG.pow (decE x)) powCost (fun h x => CyclicGroup.elemPow h (decE x)) epowCost
        ΔFS ΔPCS A.tStar play playCost (dhPairInit decE x₀) tr.1 tr.2.1 tr.2.2).2.erase
        ()).map Prod.fst) := by
  rw [ckaCorruptDDHRedAt.tree.erase_timed]
  have h : (fun t g => (play t g).erase) = A.play := funext fun t => funext (hplay t)
  rw [h]
  rfl

end CatCrypt.Crypto.Messaging
