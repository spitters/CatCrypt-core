/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.KEMCKACorrupt

/-!
# Running time of the KEM-CPA reduction of the KEM CKA

Time certificate of the KEM-CPA reduction `kemCorruptRed` of
`CatCryptCore.Crypto.Messaging.KEMCKACorrupt`.

The reduction is the oracle tree `kemCorruptTreeOf` with the key generation `kg`, the
encapsulation `en` and the interaction of the adversary as parameters; its costed form, with
the costs of `kg` and `en` as parameters, is derived by `derive_timed`, and
`kemCorruptTreeOf.erase_timed` states that the erased costed tree is the tree at the erased
interaction. The costed simulator `kemCorruptSimImplOf.timed` keeps cost companions of the party
states and epoch counters; each update adds one closure layer of cost at most `3`, so after `i`
queries the companions are within `ckaSimCostInv i`, the invariant of
`OracleAdv.Timed.timeBound_simulateHat_inv`. The `i`-th simulated query then costs at most
`6 G + 6 N + 24 i + 60` (`kemSimQueryTime`), for key generations of cost at most `G` and
encapsulations of cost at most `N`. For an adversary of time `T` with at most `q` queries and
call cost at most `a`, the reduction has time at most
`T + ∑_{j < q} kemSimQueryTime G N j + a + 6 G + 16`, a polynomial of degree two in `q`.

No module imports this file.

## Main results

* `kemCorruptSimImplOf.timed_bound` — the time of a simulated query under the companion
  invariant
* `kemCorruptTreeOf.timeBound_timed` — the time of the reduction tree
* `kemCorruptRed.tree`, `kemCorruptRed.compile_tree`, `kemCorruptRed.tree.timeBound_timed` —
  the reduction is the run of the erased costed tree, of time at most the bound above plus one
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
  CatCrypt.Examples.KEMDEM

derive_timed kemCorruptTreeOf


/-- The time of the `i`-th simulated query of the KEM-CPA reduction, with key generations of
cost at most `G` and encapsulations of cost at most `N`. -/
def kemSimQueryTime (G N i : ℕ) : ℕ := 6 * G + 6 * N + 24 * i + 60

section Time

variable {PK SK K E Rg Re : Type} [Fintype Rg] [Nonempty Rg] [Fintype Re] [Nonempty Re]
  [Fintype K] [Nonempty K]

/-- **Time of a simulated query of the KEM-CPA reduction.** From a costed state within the
bound `ckaSimCostInv i`, the costed simulator answers in time at most `kemSimQueryTime G N i`
and returns a costed state within the bound `ckaSimCostInv (i + 1)`. -/
theorem kemCorruptSimImplOf.timed_bound (kg : Rg → PK × SK) (kgCost : Rg → ℕ)
    (en : PK → Re → K × E) (enCost : PK → Re → ℕ) (ΔFS ΔPCS t : ℕ) (pk : PK) (ek : E) (kc : K)
    (ra : Re) (rb : Rg) {G N : ℕ} (hG : ∀ x, kgCost x ≤ G) (hN : ∀ p r, enCost p r ≤ N)
    (i : ℕ) (σ : CKAGameSt (PK × SK) (Option E × PK)) (q : CKAQuery)
    (stCost tCost : CKAParty → ℕ) (hS : ∀ p, stCost p ≤ 1 + 3 * i)
    (hT : ∀ p, tCost p ≤ 3 * i) :
    OracleAdv.Timed.StepTimeBound
        (OracleAdv.Timed.delay 1 (kemCorruptSimImplOf.timed kg kgCost en enCost ΔFS ΔPCS t
          pk ek kc ra rb σ q stCost tCost)) (kemSimQueryTime G N i) ∧
      OracleAdv.Timed.AllRet (fun y => ckaSimCostInv (i + 1) y.2)
        (kemCorruptSimImplOf.timed kg kgCost en enCost ΔFS ΔPCS t pk ek kc ra rb σ q stCost
          tCost).2 := by
  unfold ckaSimCostInv kemSimQueryTime
  cases q <;>
    simp only [kemCorruptSimImplOf.timed, OracleAdv.Timed.delay,
      OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet] <;>
    repeat' (first | trivial | apply And.intro | intro _ | split |
      dsimp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound,
        OracleAdv.Timed.AllRet] | grind)

end Time

/-- The time of a tree that draws `t` from `τ`, `x` from `μx`, `r` from `μr` and `b` from `μb`
at the step cost `c t x r b`, and then runs a step-prefixed tree `S t x r b` of time at most
`B` and returns the first component of its output. -/
private theorem timeBound_rand4_bind {D R X Y Z Ŝ α : Type} (τ : PMF ℕ) (μx : PMF X)
    (μr : PMF Y) (μb : PMF Z) (c : ℕ → X → Y → Z → ℕ)
    (S : ℕ → X → Y → Z → ℕ × OracleAdv.Timed D R (α × Ŝ)) {K B : ℕ}
    (hc : ∀ t x r b, c t x r b ≤ K) (hS : ∀ t x r b, OracleAdv.Timed.StepTimeBound (S t x r b) B) :
    OracleAdv.Timed.StepTimeBound (0, OracleAdv.Timed.rand τ (fun _ => 0) fun t =>
      OracleAdv.Timed.rand μx (fun _ => 0) fun x =>
        OracleAdv.Timed.rand μr (fun _ => 0) fun r =>
          OracleAdv.Timed.rand μb (fun b => c t x r b + (S t x r b).1 +
            ((S t x r b).2.bind fun r => (0, OracleAdv.Timed.ret r.1)).1)
            fun b => ((S t x r b).2.bind fun r => (0, OracleAdv.Timed.ret r.1)).2) (K + B + 4) := by
  refine ⟨Nat.zero_le _, by dsimp only; omega, fun t => ⟨Nat.zero_le _, by dsimp only; omega,
    fun x => ⟨Nat.zero_le _, by dsimp only; omega, fun r => ⟨Nat.zero_le _, by dsimp only; omega,
    fun b => ?_⟩⟩⟩⟩
  obtain ⟨h1, h2⟩ := hS t x r b
  obtain ⟨h3, h4⟩ := OracleAdv.Timed.timeBound_bind (n := 0) h2
    (f := fun r => (0, OracleAdv.Timed.ret r.1)) fun _ => ⟨le_refl _, trivial⟩
  have := hc t x r b
  refine ⟨by dsimp only; omega, h4.mono ?_⟩
  dsimp only; omega

/-- **Time of the KEM-CPA reduction.** For an adversary whose costed trees have time at most
`T`, at most `q` queries and call cost at most `a`, key generations of cost at most `G` and
encapsulations of cost at most `N`, the costed reduction tree has time at most
`T + ∑_{j < q} (6 G + 6 N + 24 j + 60) + a + 6 G + 16`: the adversary, one simulated query per
query, whose cost grows with the closure layers of the simulator state, and the setup of the
initial state. -/
theorem kemCorruptTreeOf.timeBound_timed {PK SK K E Rg Re α : Type} [Fintype Rg] [Nonempty Rg]
    [Fintype Re] [Nonempty Re] [Fintype K] [Nonempty K] (kg : Rg → PK × SK) (kgCost : Rg → ℕ)
    (en : PK → Re → K × E) (enCost : PK → Re → ℕ) (ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → Option E × PK →
      OracleAdv.Timed CKAQuery (CKAAns (PK × SK) (Option E × PK) K (Re × Rg)) α)
    (playCost : ℕ → Option E × PK → ℕ) (y : PK × E × K) {T q a G N : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hG : ∀ x, kgCost x ≤ G) (hN : ∀ p r, enCost p r ≤ N) :
    OracleAdv.Timed.StepTimeBound
      (kemCorruptTreeOf.timed kg kgCost en enCost ΔFS ΔPCS tStar play playCost y)
      (T + ∑ j ∈ Finset.range q, kemSimQueryTime G N j + a + 6 * G + 16) := by
  unfold kemCorruptTreeOf.timed
  refine (timeBound_rand4_bind (K := 12 + a + 6 * G)
    (B := T + ∑ j ∈ Finset.range q, kemSimQueryTime G N j) _ _ _ _ _ _ ?_ ?_).mono (by omega)
  · intro t x₀ ra rb
    have := ha t (none, y.1)
    have := ha t (none, (kg x₀).1)
    have := hG x₀
    split <;> omega
  · intro t x₀ ra rb
    refine (OracleAdv.Timed.timeBound_simulateHat_inv _ _ _ ckaSimCostInv
      (kemSimQueryTime G N)
      (fun i ŝ d h => kemCorruptSimImplOf.timed_bound kg kgCost en enCost ΔFS ΔPCS t y.1 y.2.1
        y.2.2 ra rb hG hN i _ d _ _ h.1 h.2) (hA t _) (hq t _) 0 _ ?_).mono ?_
    · exact ⟨fun p => le_refl _, fun p => Nat.zero_le _⟩
    · simp only [Nat.zero_add, le_refl]

/-- The oracle tree of the reduction `kemCorruptRed` for a Boolean adversary: the tree
`kemCorruptTreeOf` with the key generation `kg` and the encapsulation `en` as parameters, so
that their costs are parameters of the derived costed tree. -/
noncomputable def kemCorruptRed.tree {PK SK K E Rg Re : Type} [Fintype Rg] [Nonempty Rg]
    [Fintype Re] [Nonempty Re] [Fintype K] [Nonempty K] (kg : Rg → PK × SK)
    (en : PK → Re → K × E) (ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → Option E × PK →
      OracleAdv CKAQuery (CKAAns (PK × SK) (Option E × PK) K (Re × Rg)) Bool)
    (y : PK × E × K) : OracleAdv Empty Unit Bool :=
  kemCorruptTreeOf kg en ΔFS ΔPCS tStar play y

derive_timed kemCorruptRed.tree

/-- **The reduction is the run of the erased costed tree.** At a costed interaction `play` that
erases to the interaction of `A`, the KEM-CPA reduction `kemCorruptRed KEM ΔFS ΔPCS A` is the
run of the erasure of the derived costed tree `kemCorruptRed.tree.timed` at the algorithms of
the KEM. -/
theorem kemCorruptRed.compile_tree {PK SK K E Rg Re : Type} [Fintype Rg] [Nonempty Rg]
    [Fintype Re] [Nonempty Re] [Fintype K] [Nonempty K] (KEM : KEMScheme PK SK K E)
    [KEMCoins KEM Rg Re] (ΔFS ΔPCS : ℕ)
    (A : CKACorruptAdv (PK × SK) (Option E × PK) K (Re × Rg) Bool)
    (play : ℕ → Option E × PK →
      OracleAdv.Timed CKAQuery (CKAAns (PK × SK) (Option E × PK) K (Re × Rg)) Bool)
    (playCost : ℕ → Option E × PK → ℕ) (hplay : ∀ t g, (play t g).erase = A.play t g)
    (kgCost : Rg → ℕ) (enCost : PK → Re → ℕ) (y : PK × E × K) :
    kemCorruptRed KEM ΔFS ΔPCS A y =
      liftPMF ((OracleAdv.run emptyOracle
        (kemCorruptRed.tree.timed (KEMCoins.kgenR (KEM := KEM)) kgCost
          (KEMCoins.encapR (KEM := KEM)) enCost ΔFS ΔPCS A.tStar play playCost y).2.erase
        ()).map Prod.fst) := by
  rw [kemCorruptRed.tree.erase_timed]
  have h : (fun t g => (play t g).erase) = A.play := funext fun t => funext (hplay t)
  rw [h]
  rfl

/-- **Time of `kemCorruptRed`.** The derived costed tree of `kemCorruptRed` has the time bound
of `kemCorruptTreeOf.timeBound_timed` plus one step:
`T + ∑_{j < q} kemSimQueryTime G N j + a + 6 G + 17`. -/
theorem kemCorruptRed.tree.timeBound_timed {PK SK K E Rg Re : Type} [Fintype Rg] [Nonempty Rg]
    [Fintype Re] [Nonempty Re] [Fintype K] [Nonempty K] (kg : Rg → PK × SK) (kgCost : Rg → ℕ)
    (en : PK → Re → K × E) (enCost : PK → Re → ℕ) (ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → Option E × PK →
      OracleAdv.Timed CKAQuery (CKAAns (PK × SK) (Option E × PK) K (Re × Rg)) Bool)
    (playCost : ℕ → Option E × PK → ℕ) (y : PK × E × K) {T q a G N : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hG : ∀ x, kgCost x ≤ G) (hN : ∀ p r, enCost p r ≤ N) :
    OracleAdv.Timed.StepTimeBound
      (kemCorruptRed.tree.timed kg kgCost en enCost ΔFS ΔPCS tStar play playCost y)
      (T + ∑ j ∈ Finset.range q, kemSimQueryTime G N j + a + 6 * G + 17) := by
  unfold kemCorruptRed.tree.timed
  exact (OracleAdv.Timed.stepTimeBound_delay (kemCorruptTreeOf.timeBound_timed kg kgCost en
    enCost ΔFS ΔPCS tStar play playCost y hA hq ha hG hN)).mono (by omega)

end CatCrypt.Crypto.Messaging
