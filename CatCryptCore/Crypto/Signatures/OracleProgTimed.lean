/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.EUFCMA
public import CatCryptCore.Tactics.DeriveTimed

/-!
# Oracle programs with step costs, a tree kind of `derive_timed`

`OracleProg.Timed I O α` is the oracle program of `OracleProg I O α` in which every
continuation carries a step cost and every `lift` node carries a costed computation tree in
place of its computation: a node `query i c k` continues from the answer `o` with `k o`, and
`c o` is the cost of computing `k o` from `o`; a node `lift β t c k` runs the costed
computation tree `t : SPTree.Timed β` and continues from its result `b` with `k b`, at step
cost `c b`. Erasing the step costs, and compiling the erased computation trees
(`SPTree.compile`), gives the underlying program (`Timed.erase`).

The time bound `Timed.TimeBound p T` states that on every path of `p` the number of `query`
nodes, the times `SPTree.Timed.time t` of the computation trees of the `lift` nodes and the
step costs along the path add up to at most `T`. The time of a computation is that of its
costed tree, so a `lift` node is priced by the computation it runs.

A pair `(c, p) : ℕ × Timed I O α` is `p` preceded by `c` units of computation; its time bound
is `Timed.StepTimeBound`.

The kind `oracleProgKind` registers oracle programs in the table of tree kinds of
`CatCryptCore.Tactics.DeriveTimed`: nodes `pure` and `query`, the node `lift` whose
computation argument has the role `comp`, and the combinator `OracleProg.bind`.

## Main definitions

* `OracleProg.Timed I O α` — oracle programs with step costs and costed computation trees
* `OracleProg.Timed.erase`, `OracleProg.Timed.delay`, `OracleProg.Timed.bind`
* `OracleProg.Timed.TimeBound`, `OracleProg.Timed.StepTimeBound`
* `CatCrypt.Crypto.OracleProg.oracleProgKind` — the tree kind

## Main results

* `OracleProg.Timed.erase_bind` — erasure commutes with sequencing
* `OracleProg.Timed.timeBound_bind` — times add under sequencing
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core

namespace CatCrypt.Crypto

namespace OracleProg

/-- An oracle program with a step cost on every continuation and a costed computation tree at
every `lift` node. -/
inductive Timed (I O α : Type) : Type 1 where
  /-- Return the value. -/
  | pure (a : α) : Timed I O α
  /-- Query the oracle on `i` and continue, at step cost `c`, with `k`. -/
  | query (i : I) (c : O → ℕ) (k : O → Timed I O α) : Timed I O α
  /-- Run the costed computation tree `t` and continue, at step cost `c`, with `k`. -/
  | lift (β : Type) (t : SPTree.Timed β) (c : β → ℕ) (k : β → Timed I O α) : Timed I O α

namespace Timed

variable {I O α β : Type}

/-- The underlying oracle program: the step costs erased and the erased computation trees
compiled. -/
noncomputable def erase : Timed I O α → OracleProg I O α
  | pure a => .pure a
  | query i _ k => .query i fun o => erase (k o)
  | lift _ t _ k => .lift t.erase.compile fun b => erase (k b)

/-- `TimeBound p T`: on every path of `p`, the `query` nodes at one unit each, the times of the
computation trees of the `lift` nodes and the step costs of the continuations taken add up to
at most `T`. -/
def TimeBound : Timed I O α → ℕ → Prop
  | pure _, _ => True
  | query _ c k, n => 1 ≤ n ∧ ∀ o, c o ≤ n - 1 ∧ TimeBound (k o) (n - 1 - c o)
  | lift _ t c k, n => t.time ≤ n ∧ ∀ b, c b ≤ n - t.time ∧ TimeBound (k b) (n - t.time - c b)

/-- `StepTimeBound (c, p) T`: the step cost `c` followed by `p` takes time at most `T`. -/
def StepTimeBound (x : ℕ × Timed I O α) (n : ℕ) : Prop :=
  x.1 ≤ n ∧ x.2.TimeBound (n - x.1)

/-- The step cost `c` added in front of a step-prefixed program. -/
def delay (c : ℕ) (x : ℕ × Timed I O α) : ℕ × Timed I O α := (c + x.1, x.2)

theorem TimeBound.mono {p : Timed I O α} {m n : ℕ} (h : p.TimeBound m) (hmn : m ≤ n) :
    p.TimeBound n := by
  induction p generalizing m n with
  | pure a => trivial
  | query i c k ih =>
    exact ⟨h.1.trans hmn, fun o => ⟨(h.2 o).1.trans (by omega), ih o (h.2 o).2 (by omega)⟩⟩
  | lift β t c k ih =>
    exact ⟨h.1.trans hmn, fun b => ⟨(h.2 b).1.trans (by omega), ih b (h.2 b).2 (by omega)⟩⟩

theorem StepTimeBound.mono {x : ℕ × Timed I O α} {m n : ℕ} (h : StepTimeBound x m)
    (hmn : m ≤ n) : StepTimeBound x n :=
  ⟨h.1.trans hmn, h.2.mono (Nat.sub_le_sub_right hmn _)⟩

theorem stepTimeBound_delay {c : ℕ} {x : ℕ × Timed I O α} {n : ℕ}
    (h : StepTimeBound x n) : StepTimeBound (delay c x) (c + n) := by
  refine ⟨Nat.add_le_add_left h.1 c, ?_⟩
  have e : c + n - (c + x.1) = n - x.1 := by omega
  simpa only [delay, e] using h.2

/-- Run `p`, then continue with `f` on its output; the step cost of `f a` is added to the edge
into the leaf `pure a`, or precedes the result when `p` is `pure a`. -/
def bind : Timed I O α → (α → ℕ × Timed I O β) → ℕ × Timed I O β
  | pure a, f => f a
  | query i c k, f =>
    (0, query i (fun o => c o + (bind (k o) f).1) fun o => (bind (k o) f).2)
  | lift γ t c k, f =>
    (0, lift γ t (fun b => c b + (bind (k b) f).1) fun b => (bind (k b) f).2)

/-- Erasure commutes with sequencing. -/
theorem erase_bind (p : Timed I O α) (f : α → ℕ × Timed I O β) :
    (p.bind f).2.erase = p.erase.bind fun a => (f a).2.erase := by
  induction p with
  | pure a => rfl
  | query i c k ih => simp only [bind, erase, OracleProg.bind, ih]
  | lift γ t c k ih => simp only [bind, erase, OracleProg.bind, ih]

/-- Times add under sequencing. -/
theorem timeBound_bind {p : Timed I O α} {f : α → ℕ × Timed I O β} {m n : ℕ}
    (hp : p.TimeBound m) (hf : ∀ a, StepTimeBound (f a) n) :
    StepTimeBound (p.bind f) (m + n) := by
  induction p generalizing m with
  | pure a => exact (hf a).mono (Nat.le_add_left n m)
  | query i c k ih =>
    have h1 := hp.1
    refine ⟨Nat.zero_le _, ?_⟩
    simp only [bind, Nat.sub_zero]
    refine ⟨by omega, fun o => ?_⟩
    have h2 := (hp.2 o).1
    have h3 := (stepTimeBound_delay (c := c o) (ih o (hp.2 o).2)).mono
      (n := m + n - 1) (by omega)
    exact ⟨h3.1, h3.2⟩
  | lift γ t c k ih =>
    have h1 := hp.1
    refine ⟨Nat.zero_le _, ?_⟩
    simp only [bind, Nat.sub_zero]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hp.2 b).1
    have h3 := (stepTimeBound_delay (c := c b) (ih b (hp.2 b).2)).mono
      (n := m + n - t.time) (by omega)
    exact ⟨h3.1, h3.2⟩

/-- Erasure of a step-prefixed program commutes with `if`. -/
theorem erase_snd_ite (c : Prop) [Decidable c] (x y : ℕ × Timed I O α) :
    (if c then x else y).2.erase = if c then x.2.erase else y.2.erase := by
  split <;> rfl

/-- Erasure of a step-prefixed program commutes with a dependent `if`. -/
theorem erase_snd_dite (c : Prop) [Decidable c] (x : c → ℕ × Timed I O α)
    (y : ¬c → ℕ × Timed I O α) :
    (if h : c then x h else y h).2.erase = if h : c then (x h).2.erase else (y h).2.erase := by
  split <;> rfl

/-- Erasure of a costed oracle program commutes with an `if`. -/
theorem erase_ite (c : Prop) [Decidable c] (x y : Timed I O α) :
    (if c then x else y).erase = if c then x.erase else y.erase := by
  split <;> rfl

end Timed

open CatCrypt.Tactics.DeriveTimed in
/-- Oracle programs `OracleProg I O α`: `pure`, `query` and `lift` nodes, the computation of a
`lift` node priced by its costed computation tree, and the combinator `OracleProg.bind`. -/
meta def oracleProgKind : TreeKind where
  noun := "oracle program"
  tree := ``CatCrypt.Crypto.OracleProg
  nParams := 3
  timed := ``CatCrypt.Crypto.OracleProg.Timed
  erase := ``CatCrypt.Crypto.OracleProg.Timed.erase
  delay := ``CatCrypt.Crypto.OracleProg.Timed.delay
  nodes := #[
    ⟨``CatCrypt.Crypto.OracleProg.pure, ``CatCrypt.Crypto.OracleProg.Timed.pure, #[.data]⟩,
    ⟨``CatCrypt.Crypto.OracleProg.query, ``CatCrypt.Crypto.OracleProg.Timed.query,
      #[.data, .cont 1]⟩,
    ⟨``CatCrypt.Crypto.OracleProg.lift, ``CatCrypt.Crypto.OracleProg.Timed.lift,
      #[.keep, .comp, .cont 1]⟩]
  combinators := #[
    ⟨``CatCrypt.Crypto.OracleProg.bind, ``CatCrypt.Crypto.OracleProg.Timed.bind,
      #[.tree, .pairFn 1], true⟩]
  eraseLemmas := #[``CatCrypt.Crypto.OracleProg.Timed.erase,
    ``CatCrypt.Crypto.OracleProg.Timed.delay, ``CatCrypt.Crypto.OracleProg.Timed.erase_bind,
    ``CatCrypt.Crypto.OracleProg.Timed.erase_snd_ite,
    ``CatCrypt.Crypto.OracleProg.Timed.erase_snd_dite]
  hatLemmas := #[``CatCrypt.Crypto.OracleProg.bind, ``Prod.mk.eta, ``Sum.map_inl, ``Sum.map_inr,
    ``CatCrypt.Tactics.DeriveTimed.fst_ite, ``CatCrypt.Tactics.DeriveTimed.snd_ite,
    ``CatCrypt.Tactics.DeriveTimed.ite_prod_mk, ``CatCrypt.Crypto.OracleProg.Timed.erase_ite]
  stepTimeBound := some ``CatCrypt.Crypto.OracleProg.Timed.StepTimeBound

end OracleProg

end CatCrypt.Crypto

register_tree_kind CatCrypt.Crypto.OracleProg.oracleProgKind
