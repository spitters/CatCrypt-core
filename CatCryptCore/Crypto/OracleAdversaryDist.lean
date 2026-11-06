/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.Crypto.OracleSimulation

/-!
# The output distribution of an oracle tree without queries

An oracle tree over the empty interface, `OracleAdv Empty Empty α`, is a sampling program: its
nodes are `ret` and `rand`, and a `query` node has no query to ask. Its output distribution
`OracleAdv.dist A : PMF α` samples at each `rand` node and returns the leaf. It is the output of
a run of `A` against any oracle (`OracleAdv.run_map_fst_eq_dist`), so that a statement about the
run of the erasure of a costed tree over the empty interface under an arbitrary oracle is a
statement about `dist`.

A distribution written as a sampling program (`PMF.pure`, `PMF.bind`, `PMF.map`, uniform
sampling, the run of an oracle tree against a stateful oracle whose step is such a program) is
the output distribution of an oracle tree over the empty interface built node by node: the
lemmas `dist_*_of` below state this for each construct, and `derive_timed` assembles them into
the proof that the tree it reflects from such a distribution has that distribution
(`CatCryptCore.Tactics.DerivePMF`).

## Main definitions

* `OracleAdv.dist` — the output distribution of an oracle tree over the empty interface

## Main results

* `OracleAdv.dist_ret`, `OracleAdv.dist_rand`, `OracleAdv.dist_bind`, `OracleAdv.dist_simulate`
  — `dist` on the nodes, on sequencing and on simulation (a simulated adversary has the
  distribution of the run of the adversary against the oracle of the programs' distributions)
* `OracleAdv.run_map_fst_eq_dist` — over the empty interface, the output of a run against any
  oracle is `dist`
* `OracleAdv.dist_bind_of`, `dist_map_of`, `dist_sample_of`, `dist_simulate_of`, `dist_ite_of`,
  `dist_dite_of` — the reflection lemmas: a tree built from trees with the distributions of the
  parts has the distribution of the construct
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

namespace OracleAdv

variable {α β : Type}

/-- The output distribution of an oracle tree over the empty interface: sample at each `rand`
node and return the leaf; a `query` node asks a query of the empty type and is never reached. -/
noncomputable def dist : OracleAdv Empty Empty α → PMF α
  | ret a => PMF.pure a
  | rand p k => p.bind fun b => dist (k b)
  | query d _ => d.elim

@[simp] theorem dist_ret (a : α) : (ret a : OracleAdv Empty Empty α).dist = PMF.pure a := rfl

@[simp] theorem dist_rand {γ : Type} (p : PMF γ) (k : γ → OracleAdv Empty Empty α) :
    (rand p k).dist = p.bind fun b => (k b).dist := rfl

/-- The distribution of a sequencing is the sequencing of the distributions. -/
theorem dist_bind (A : OracleAdv Empty Empty α) (f : α → OracleAdv Empty Empty β) :
    (A.bind f).dist = A.dist.bind fun a => (f a).dist := by
  induction A with
  | ret a => simp [bind]
  | rand p k ih => simp only [bind, dist_rand, ih, PMF.bind_bind]
  | query d _ _ => exact d.elim

/-- **The distribution of a simulation.** An adversary whose queries are answered by programs
over the empty interface has the distribution of the run of the adversary against the oracle
that samples the program's distribution. -/
theorem dist_simulate {D R S : Type} (impl : S → D → OracleAdv Empty Empty (R × S))
    (A : OracleAdv D R α) (s : S) :
    (simulate impl A s).dist = run (fun s d => (impl s d).dist) A s := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih => simp only [simulate, dist_rand, run_rand, ih]
  | query d k ih => simp only [simulate, dist_bind, run_query, ih]

/-- Over the empty interface, the output of a run against any oracle is `dist`. -/
theorem run_map_fst_eq_dist {U : Type} (O : U → Empty → PMF (Empty × U))
    (A : OracleAdv Empty Empty α) (u : U) : (run O A u).map Prod.fst = A.dist := by
  induction A with
  | ret a => simp [PMF.pure_map]
  | rand p k ih => simp only [run_rand, PMF.map_bind, ih, dist_rand]
  | query d _ _ => exact d.elim

/-! ## Reflection lemmas -/

theorem dist_bind_of {t : OracleAdv Empty Empty α} {k : α → OracleAdv Empty Empty β}
    {p : PMF α} {f : α → PMF β} (hp : t.dist = p) (hf : ∀ a, (k a).dist = f a) :
    (t.bind k).dist = p.bind f := by
  rw [dist_bind, hp]
  exact congrArg _ (funext hf)

theorem dist_map_of {t : OracleAdv Empty Empty α} {p : PMF α} (f : α → β)
    (hp : t.dist = p) : (t.bind fun a => ret (f a)).dist = p.map f := by
  rw [dist_bind, hp]
  simp only [dist_ret]
  rfl

theorem dist_sample_of (p : PMF α) : (rand p ret : OracleAdv Empty Empty α).dist = p := by
  simp only [dist_rand, dist_ret, PMF.bind_pure]

theorem dist_simulate_of {D R S : Type} {impl : S → D → OracleAdv Empty Empty (R × S)}
    {O : S → D → PMF (R × S)} (hO : ∀ s d, (impl s d).dist = O s d) (A : OracleAdv D R α)
    (s : S) : (simulate impl A s).dist = run O A s := by
  rw [dist_simulate]
  exact congrArg (fun O' => run O' A s) (funext fun s => funext fun d => hO s d)

theorem dist_ite_of (c : Prop) [Decidable c] {t e : OracleAdv Empty Empty α} {p q : PMF α}
    (ht : t.dist = p) (he : e.dist = q) :
    (if c then t else e).dist = if c then p else q := by
  split <;> assumption

theorem dist_dite_of (c : Prop) [Decidable c] {t : c → OracleAdv Empty Empty α}
    {e : ¬c → OracleAdv Empty Empty α} {p : c → PMF α} {q : ¬c → PMF α}
    (ht : ∀ h, (t h).dist = p h) (he : ∀ h, (e h).dist = q h) :
    (if h : c then t h else e h).dist = if h : c then p h else q h := by
  split
  · exact ht _
  · exact he _

end OracleAdv

namespace OracleAdv.Timed

/-- Over the empty interface, the output of a run of an erased costed tree against any oracle is
the distribution of the erased tree. -/
theorem run_erase_map_fst_eq_dist {α U : Type} (O : U → Empty → PMF (Empty × U))
    (A : Timed Empty Empty α) (u : U) : (OracleAdv.run O A.erase u).map Prod.fst = A.erase.dist :=
  OracleAdv.run_map_fst_eq_dist O A.erase u

end OracleAdv.Timed

end CatCrypt.Crypto
