/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DillerNahm
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Logic.Function.Iterate

/-!
# Amortized cost as a Diller–Nahm morphism over a state object

A step over a state object `S` with a potential `Φ : S → ℕ` is a costed function with use counts
(`Clocked S S`) whose forward map is the update of the state and whose backward map demands, for a
data token of the next state, one data token of the state and `C (Φ s)` clock ticks: the demand
depends on the potential of the state (`Clocked.potential`, `Clocked.toDN_potential_false`).

The `q`-fold composite of a step (`Clocked.iter`) is the Diller–Nahm composite of its morphisms
(`Clocked.toDN_iter_succ`), and its cost is the sum `∑_{j < q} C (Φ (step^[j] s))` of the demands
along the states (`Clocked.iter_potential_cost`). When the potential grows by at most `g` a step
and `C` is monotone, each demand is at most the last, and the cost is at most
`q * C (Φ s + q * g)` (`Clocked.iter_potential_cost_le`): the amortized bound of Tarjan's
potential method (SIAM J. Algebraic Discrete Methods 6, 1985), at a cost of a step that is a
function of the potential.

The potential step `Clocked.potStep C g` is the step over the object of potentials `ℕ`, a state
of potential `n` going to `n + g`; it is the abstraction of a state object through a bound of its
potential. A costed simulation of an oracle adversary whose handler is simulated by the potential
step, from a state of potential at most `n`, a program of time at most `C n` and a state of
potential at most `n + g`, has the time of the adversary plus the cost of the `q`-fold composite
of the potential step (`OracleAdv.Timed.timeBound_simulateHat_amortized`,
`CatCryptCore/Crypto/OracleAdversaryPotential.lean`).

## Main definitions

* `Clocked.iter` — the `q`-fold composite of a step;
* `Clocked.potential` — the step over a state object whose demand is a function of the potential;
* `Clocked.potStep` — the step over the object of potentials.

## Main results

* `Clocked.toDN_iter_succ`, `Clocked.iter_uses` — the composite is a Diller–Nahm composite;
* `Clocked.toDN_potential_false` — the demand of a data token at a state is `C (Φ s)` clock ticks;
* `Clocked.iter_potential_cost`, `Clocked.iter_potential_cost_le` — the amortized cost;
* `Clocked.iter_potStep_cost`, `Clocked.iter_potStep_cost_le` — at the object of potentials.

## References

* R. E. Tarjan, *Amortized computational complexity*, SIAM J. Algebraic Discrete Methods 6
  (1985);
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018, §8.

Search words: amortized cost, potential, potential method, state object, Diller–Nahm, clock,
simulation, oracle handler.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container

namespace Clocked

variable {S : Type u}

/-- The `q`-fold composite of a step: `iter h 0` is the identity and `iter h (q + 1)` runs `h`
and then `iter h q`. -/
def iter (h : Clocked S S) : ℕ → Clocked S S
  | 0 => Clocked.id S
  | q + 1 => comp (iter h q) h

/-- The Diller–Nahm morphism of the `q + 1`-fold composite is the composite of the morphisms. -/
theorem toDN_iter_succ (h : Clocked S S) (q : ℕ) :
    toDN (h.iter (q + 1)) = DNLens.comp (toDN (h.iter q)) (toDN h) :=
  toDN_comp _ _

/-- The forward map of the `q`-fold composite is the `q`-fold iterate of the forward map. -/
theorem iter_fn (h : Clocked S S) (q : ℕ) (s : S) : (h.iter q).fn s = h.fn^[q] s := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih => exact ih (h.fn s)

/-- A step that uses its input once has a composite that uses its input once. -/
theorem iter_uses (h : Clocked S S) (hu : ∀ s, h.uses s = 1) (q : ℕ) (s : S) :
    (h.iter q).uses s = 1 := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih => change (h.iter q).uses (h.fn s) * h.uses s = 1; rw [ih, hu, one_mul]

/-- The cost of the composite of a step that uses its input once is the sum of the costs along
the states. -/
theorem iter_cost (h : Clocked S S) (hu : ∀ s, h.uses s = 1) (q : ℕ) (s : S) :
    (h.iter q).cost s = ∑ j ∈ Finset.range q, h.cost (h.fn^[j] s) := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih =>
    change (h.iter q).cost (h.fn s) + (h.iter q).uses (h.fn s) * h.cost s = _
    rw [ih, iter_uses h hu, one_mul, Finset.sum_range_succ', Function.iterate_zero_apply]
    simp only [Function.iterate_succ_apply]

/-- The step over a state object whose demand is a function of the potential: the state goes to
`step s`, used once, at `C (Φ s)` clock ticks. -/
def potential (Φ : S → ℕ) (C : ℕ → ℕ) (step : S → S) : Clocked S S where
  fn := step
  uses _ := 1
  cost s := C (Φ s)

/-- A data token of the next state demands one data token of the state and `C (Φ s)` clock
ticks. -/
theorem toDN_potential_false (Φ : S → ℕ) (C : ℕ → ℕ) (step : S → S) (s : S) :
    (toDN (potential Φ C step)).toFunB s false = {false} + C (Φ s) • {true} := by
  change 1 • ({false} : Multiset Bool) + C (Φ s) • {true} = _
  rw [one_nsmul]

/-- The cost of `q` steps is the sum of the demands at the potentials of the states. -/
theorem iter_potential_cost (Φ : S → ℕ) (C : ℕ → ℕ) (step : S → S) (q : ℕ) (s : S) :
    ((potential Φ C step).iter q).cost s = ∑ j ∈ Finset.range q, C (Φ (step^[j] s)) :=
  iter_cost _ (fun _ => rfl) q s

/-- **The amortized cost.** When the potential grows by at most `g` a step and the demand is
monotone in the potential, `q` steps cost at most `q` times the demand at the potential
`Φ s + q * g`. -/
theorem iter_potential_cost_le (Φ : S → ℕ) {C : ℕ → ℕ} (hC : Monotone C) (step : S → S)
    {g : ℕ} (hg : ∀ s, Φ (step s) ≤ Φ s + g) (q : ℕ) (s : S) :
    ((potential Φ C step).iter q).cost s ≤ q * C (Φ s + q * g) := by
  have hpot : ∀ j t, Φ (step^[j] t) ≤ Φ t + j * g := by
    intro j
    induction j with
    | zero => intro t; simp
    | succ j ih =>
      intro t
      rw [Function.iterate_succ_apply']
      have := hg (step^[j] t)
      have := ih t
      rw [Nat.succ_mul]
      omega
  rw [iter_potential_cost]
  have hle := Finset.sum_le_card_nsmul (Finset.range q) (fun j => C (Φ (step^[j] s)))
    (C (Φ s + q * g)) fun j hj => hC ((hpot j s).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Finset.mem_range.1 hj).le) _))
  simpa using hle

/-- The step over the object of potentials: a state of potential `n` goes to `n + g` at `C n`
clock ticks. -/
def potStep (C : ℕ → ℕ) (g : ℕ) : Clocked ℕ ℕ :=
  potential (fun n => n) C (· + g)

/-- The cost of `q` potential steps from `n` is `∑_{j < q} C (n + j * g)`. -/
theorem iter_potStep_cost (C : ℕ → ℕ) (g q n : ℕ) :
    ((potStep C g).iter q).cost n = ∑ j ∈ Finset.range q, C (n + j * g) := by
  have hj : ∀ j, (· + g)^[j] n = n + j * g := fun j => by
    induction j with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply', ih, Nat.succ_mul, Nat.add_assoc]
  rw [potStep, iter_potential_cost]
  exact Finset.sum_congr rfl fun j _ => congrArg C (hj j)

/-- `q` potential steps from `n` cost at most `q * C (n + q * g)`. -/
theorem iter_potStep_cost_le {C : ℕ → ℕ} (hC : Monotone C) (g q n : ℕ) :
    ((potStep C g).iter q).cost n ≤ q * C (n + q * g) :=
  iter_potential_cost_le (fun n => n) hC (· + g) (fun _ => le_rfl) q n

end Clocked

end CatCrypt.Container
