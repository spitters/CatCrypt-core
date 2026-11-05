/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.EUFCMA
public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveTimedStructure
public import CatCryptCore.Core.SPTreeTimedOps
public import CatCryptCore.Tactics.AutoTime

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
computation argument has the role `comp`, and the combinators `OracleProg.bind`,
`OracleProg.bindQueries` and `OracleProg.collectLog`, whose handler programs are step-prefixed
costed programs (role `pairFn`).

## Handlers

Replacing each query of a program by a handler program, and interpreting a program against an
oracle, cost the time of the program plus, per query, the time of the handler or oracle
(`stepTime_runWith_le` here; `timeBound_bindQueries` and `timeBound_collectLog`, with the query
count of the composite, in `CatCryptCore.Crypto.Signatures.OracleProgUseBound`, as instances of
the composition rule of use bounds). Prepending the records of a query to the records of the rest
costs `2 * l + 1` for records of length `l`, the registered cost of `List.append`.

The costed mirror `Signatures.EUFCMAAdversary.Timed` of EUF-CMA adversaries is derived here by
`derive_timed_structure`, so that the modules that derive reductions into
`EUFCMAAdversary` share it.

## Main definitions

* `OracleProg.Timed I O α` — oracle programs with step costs and costed computation trees
* `OracleProg.Timed.erase`, `OracleProg.Timed.delay`, `OracleProg.Timed.bind`
* `OracleProg.Timed.TimeBound`, `OracleProg.Timed.StepTimeBound`, `OracleProg.Timed.AllRet`
* `OracleProg.Timed.bindQueries`, `OracleProg.Timed.collectLog` — costed handler combinators
* `OracleProg.Timed.runWith` — the costed interpretation against a costed oracle
* `OracleProg.Timed.runWithTree` — the computation tree of the interpretation, registered with
  the costed form `runWith` as the interpreter `runWithInterp` of computation trees
* `CatCrypt.Crypto.OracleProg.oracleProgKind` — the tree kind
* `Signatures.EUFCMAAdversary.Timed` — the costed mirror of EUF-CMA adversaries

## Main results

* `OracleProg.Timed.erase_bind` — erasure commutes with sequencing
* `OracleProg.Timed.timeBound_bind` — times add under sequencing
* `OracleProg.Timed.erase_bindQueries`, `OracleProg.Timed.erase_collectLog`,
  `OracleProg.Timed.erase_runWith` — erasure of the handler combinators and the interpretation
* `OracleProg.Timed.erase_runWith_eq`, `OracleProg.Timed.compile_runWithTree` — the costed
  interpretation erases to `runWithTree`, which compiles to `OracleProg.runWith`
* `OracleProg.Timed.stepTime_runWith_le` — the cost law of the interpretation: time
  `T + q * (t + 2 * ℓ + 1)` for a program of time `T` with `q` queries against an oracle of time
  `t` with log entries of length at most `ℓ`
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

/-- `AllRet Q p`: `Q` holds at every leaf `pure a` of `p`. -/
def AllRet (Q : α → Prop) : Timed I O α → Prop
  | pure a => Q a
  | query _ _ k => ∀ o, AllRet Q (k o)
  | lift _ _ _ k => ∀ b, AllRet Q (k b)

/-- Times add under sequencing, with the continuation bounded at the leaves satisfying a leaf
invariant of the program. -/
theorem timeBound_bind_of_allRet {Q : α → Prop} {p : Timed I O α}
    {f : α → ℕ × Timed I O β} {m n : ℕ} (hp : p.TimeBound m) (hQ : p.AllRet Q)
    (hf : ∀ a, Q a → StepTimeBound (f a) n) : StepTimeBound (p.bind f) (m + n) := by
  induction p generalizing m with
  | pure a => exact (hf a hQ).mono (Nat.le_add_left n m)
  | query i c k ih =>
    have h1 := hp.1
    refine ⟨Nat.zero_le _, ?_⟩
    simp only [bind, Nat.sub_zero]
    refine ⟨by omega, fun o => ?_⟩
    have h2 := (hp.2 o).1
    have h3 := (stepTimeBound_delay (c := c o) (ih o (hp.2 o).2 (hQ o))).mono
      (n := m + n - 1) (by omega)
    exact ⟨h3.1, h3.2⟩
  | lift γ t c k ih =>
    have h1 := hp.1
    refine ⟨Nat.zero_le _, ?_⟩
    simp only [bind, Nat.sub_zero]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hp.2 b).1
    have h3 := (stepTimeBound_delay (c := c b) (ih b (hp.2 b).2 (hQ b))).mono
      (n := m + n - t.time) (by omega)
    exact ⟨h3.1, h3.2⟩

/-! ### Replacing queries by handler programs -/

section Handlers

variable {I' O' Q R L : Type}

/-- The costed form of `OracleProg.bindQueries`: each query `i` is replaced by the
step-prefixed handler program `h i`, followed by the step cost of the query's continuation. -/
def bindQueries (h : I → ℕ × Timed I' O' O) : Timed I O α → ℕ × Timed I' O' α
  | pure a => (0, pure a)
  | query i c k => delay (h i).1 ((h i).2.bind fun o => delay (c o) (bindQueries h (k o)))
  | lift γ t c k =>
    (0, lift γ t (fun b => c b + (bindQueries h (k b)).1) fun b => (bindQueries h (k b)).2)

/-- Erasure commutes with replacing queries by handler programs. -/
theorem erase_bindQueries (h : I → ℕ × Timed I' O' O) (p : Timed I O α) :
    (bindQueries h p).2.erase = OracleProg.bindQueries (fun i => (h i).2.erase) p.erase := by
  induction p with
  | pure a => rfl
  | query i c k ih =>
    simp only [bindQueries, delay, erase_bind, ih, erase, OracleProg.bindQueries]
  | lift γ t c k ih => simp only [bindQueries, erase, OracleProg.bindQueries, ih]

/-- The costed form of `OracleProg.collectLog`: each query `x` is replaced by the
step-prefixed handler program `h x`, and the records of the handler are prepended to the
records of the rest at the cost `2 * l + 1` of appending a list of length `l`, the registered
cost of `List.append`. -/
def collectLog (h : Q → ℕ × Timed I O (R × List L)) :
    Timed Q R α → ℕ × Timed I O (α × List L)
  | pure a => (0, pure (a, []))
  | query x c k => delay (h x).1 ((h x).2.bind fun rl =>
      delay (c rl.1) (delay (collectLog h (k rl.1)).1 ((collectLog h (k rl.1)).2.bind fun al =>
        (2 * rl.2.length + 1, pure (al.1, rl.2 ++ al.2)))))
  | lift γ t c k =>
    (0, lift γ t (fun b => c b + (collectLog h (k b)).1) fun b => (collectLog h (k b)).2)

/-- Erasure commutes with collecting the records of handler programs. -/
theorem erase_collectLog (h : Q → ℕ × Timed I O (R × List L)) (p : Timed Q R α) :
    (collectLog h p).2.erase = OracleProg.collectLog (fun x => (h x).2.erase) p.erase := by
  induction p with
  | pure a => rfl
  | query x c k ih =>
    simp only [collectLog, delay, erase_bind, ih, erase, OracleProg.collectLog]
  | lift γ t c k ih => simp only [collectLog, erase, OracleProg.collectLog, ih]

end Handlers

/-! ### Interpretation against an oracle -/

section Interpret

variable {L : Type}

/-- The costed form of `OracleProg.runWith`: each query `i` runs the step-prefixed costed
oracle `o i`, whose log entries are prepended to the entries of the rest at the cost
`2 * l + 1` of appending a list of length `l`, the registered cost of `List.append`; each
`lift` node runs its costed computation tree. -/
noncomputable def runWith (o : I → ℕ × SPTree.Timed (O × List L)) :
    Timed I O α → ℕ × SPTree.Timed (α × List L)
  | pure a => (0, .ret (a, []))
  | query i c k => SPTree.Timed.delay (o i).1 ((o i).2.bind fun ol =>
      SPTree.Timed.delay (c ol.1) (SPTree.Timed.delay (runWith o (k ol.1)).1
        ((runWith o (k ol.1)).2.bind fun al =>
          (2 * ol.2.length + 1, .ret (al.1, ol.2 ++ al.2)))))
  | lift _ t c k => t.bind fun b => SPTree.Timed.delay (c b) (runWith o (k b))

/-- The costed interpretation compiles to the interpretation of the erased program against the
compiled oracle. -/
theorem erase_runWith (o : I → ℕ × SPTree.Timed (O × List L)) (p : Timed I O α) :
    (runWith o p).2.erase.compile =
      OracleProg.runWith (fun i => (o i).2.erase.compile) p.erase := by
  induction p with
  | pure a =>
    simp only [runWith, SPTree.Timed.erase_ret, SPTree.compile_ret, erase,
      OracleProg.runWith_pure]
  | query i c k ih =>
    simp only [runWith, SPTree.Timed.delay, SPTree.Timed.erase_bind, SPTree.compile_bind, ih,
      SPTree.Timed.erase_ret, SPTree.compile_ret, erase, OracleProg.runWith]
  | lift β t c k ih =>
    simp only [runWith, SPTree.Timed.delay, SPTree.Timed.erase_bind, SPTree.compile_bind, ih,
      erase, OracleProg.runWith]

/-- **Cost of interpreting an oracle program.** A program of time `T` with at most `q` queries,
run against an oracle of time at most `t` per query whose log entries have length at most `ℓ`,
runs in time `T + q * (t + 2 * ℓ + 1)`. -/
theorem stepTime_runWith_le {o : I → ℕ × SPTree.Timed (O × List L)} {t ℓ : ℕ}
    (ho : ∀ i, SPTree.Timed.stepTime (o i) ≤ t)
    (hl : ∀ i, SPTree.Timed.AllRet (fun ol => ol.2.length ≤ ℓ) (o i).2)
    {p : Timed I O α} {T q : ℕ} (hp : p.TimeBound T)
    (hq : QueryCostLe (fun _ => 1) p.erase q) :
    SPTree.Timed.stepTime (runWith o p) ≤ T + q * (t + 2 * ℓ + 1) := by
  induction p generalizing T q with
  | pure a => simp [runWith, SPTree.Timed.stepTime, SPTree.Timed.time_ret]
  | query i c k ih =>
    obtain ⟨hT, hk⟩ := hp
    obtain ⟨hq1, hqk⟩ := hq
    simp only at hq1 hqk
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hb := SPTree.Timed.stepTime_bind_le_of_allRet (o i).2
      (fun ol => SPTree.Timed.delay (c ol.1) (SPTree.Timed.delay (runWith o (k ol.1)).1
        ((runWith o (k ol.1)).2.bind fun al =>
          (2 * ol.2.length + 1, .ret (al.1, ol.2 ++ al.2)))))
      (T - 1 + q' * (t + 2 * ℓ + 1) + (2 * ℓ + 1)) (hl i) fun ol hol => by
        have hc := (hk ol.1).1
        have hi := ih ol.1 (hk ol.1).2 (by simpa using hqk ol.1)
        have hg := SPTree.Timed.stepTime_bind_le (runWith o (k ol.1)).2
          (fun al => (2 * ol.2.length + 1, SPTree.Timed.ret (al.1, ol.2 ++ al.2)))
          (2 * ℓ + 1) fun _ => by
            simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
            omega
        simp only [SPTree.Timed.stepTime_delay]
        simp only [SPTree.Timed.stepTime] at hi hg ⊢
        omega
    have ho' := ho i
    simp only [runWith, SPTree.Timed.stepTime_delay]
    simp only [SPTree.Timed.stepTime] at hb ho' ⊢
    rw [Nat.succ_mul q']
    omega
  | lift β u c k ih =>
    have hu := hp.1
    have hb := SPTree.Timed.stepTime_bind_le u
      (fun b => SPTree.Timed.delay (c b) (runWith o (k b))) (T - u.time + q * (t + 2 * ℓ + 1))
      fun b => by
        have hc := (hp.2 b).1
        have hi := ih b (hp.2 b).2 (hq b)
        rw [SPTree.Timed.stepTime_delay]
        omega
    exact hb.trans (by omega)

/-- The computation tree of the interpretation of the costed program `p` against the oracle
`o` of computation trees: the tree of `OracleProg.runWith` with the step costs of `p` erased,
whose `lift` nodes run the erased computation trees of `p`. -/
noncomputable def runWithTree (o : I → SPTree (O × List L)) :
    Timed I O α → SPTree (α × List L)
  | pure a => .ret (a, [])
  | query i _ k => (o i).bind fun ol =>
      (runWithTree o (k ol.1)).bind fun al => .ret (al.1, ol.2 ++ al.2)
  | lift _ t _ k => t.erase.bind fun b => runWithTree o (k b)

/-- The costed interpretation erases to the tree of the interpretation against the erased
oracle. -/
theorem erase_runWith_eq (o : I → ℕ × SPTree.Timed (O × List L)) (p : Timed I O α) :
    (runWith o p).2.erase = runWithTree (fun i => (o i).2.erase) p := by
  induction p with
  | pure a => simp only [runWith, runWithTree, SPTree.Timed.erase_ret]
  | query i c k ih =>
    simp only [runWith, runWithTree, SPTree.Timed.delay, SPTree.Timed.erase_bind, ih,
      SPTree.Timed.erase_ret]
  | lift β t c k ih =>
    simp only [runWith, runWithTree, SPTree.Timed.delay, SPTree.Timed.erase_bind, ih]

/-- The tree of the interpretation compiles to the interpretation of the erased program against
the compiled oracle. -/
theorem compile_runWithTree (o : I → SPTree (O × List L)) (p : Timed I O α) :
    (runWithTree o p).compile = OracleProg.runWith (fun i => (o i).compile) p.erase := by
  induction p with
  | pure a => simp only [runWithTree, SPTree.compile_ret, erase, OracleProg.runWith_pure]
  | query i c k ih =>
    simp only [runWithTree, SPTree.compile_bind, ih, SPTree.compile_ret, erase,
      OracleProg.runWith]
  | lift β t c k ih =>
    simp only [runWithTree, SPTree.compile_bind, ih, erase, OracleProg.runWith]

end Interpret

end Timed

open CatCrypt.Tactics.DeriveTimed in
/-- Oracle programs `OracleProg I O α`: `pure`, `query` and `lift` nodes, the computation of a
`lift` node priced by its costed computation tree, and the combinators `OracleProg.bind`,
`OracleProg.bindQueries` and `OracleProg.collectLog`, the last two with a handler program per
query. -/
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
      #[.tree, .pairFn 1], true⟩,
    ⟨``CatCrypt.Crypto.OracleProg.bindQueries, ``CatCrypt.Crypto.OracleProg.Timed.bindQueries,
      #[.pairFn 1, .tree], true⟩,
    ⟨``CatCrypt.Crypto.OracleProg.collectLog, ``CatCrypt.Crypto.OracleProg.Timed.collectLog,
      #[.pairFn 1, .tree], true⟩]
  eraseLemmas := #[``CatCrypt.Crypto.OracleProg.Timed.erase,
    ``CatCrypt.Crypto.OracleProg.Timed.delay, ``CatCrypt.Crypto.OracleProg.Timed.erase_bind,
    ``CatCrypt.Crypto.OracleProg.Timed.erase_bindQueries,
    ``CatCrypt.Crypto.OracleProg.Timed.erase_collectLog,
    ``CatCrypt.Crypto.OracleProg.Timed.erase_snd_ite,
    ``CatCrypt.Crypto.OracleProg.Timed.erase_snd_dite]
  hatLemmas := #[``CatCrypt.Crypto.OracleProg.bind, ``Prod.mk.eta, ``Sum.map_inl, ``Sum.map_inr,
    ``CatCrypt.Tactics.DeriveTimed.fst_ite, ``CatCrypt.Tactics.DeriveTimed.snd_ite,
    ``CatCrypt.Tactics.DeriveTimed.ite_prod_mk, ``CatCrypt.Crypto.OracleProg.Timed.erase_ite]
  stepTimeBound := some ``CatCrypt.Crypto.OracleProg.Timed.StepTimeBound

open CatCrypt.Tactics.DeriveTimed in
/-- The interpretation of a costed oracle program against an oracle of computation trees, a
combinator of computation trees: the tree `Timed.runWithTree o p` has the costed form
`Timed.runWith o' p`, with the oracle `o` translated (role `pairFn`) and the costed program `p`
kept; it compiles to `OracleProg.runWith`, whose program is its second explicit argument. -/
meta def runWithInterp : Interp where
  tree := ``CatCrypt.Core.SPTree
  comb := ⟨``CatCrypt.Crypto.OracleProg.Timed.runWithTree,
    ``CatCrypt.Crypto.OracleProg.Timed.runWith, #[.pairFn 1, .keep], true⟩
  eraseLemmas := #[``CatCrypt.Crypto.OracleProg.Timed.erase_runWith_eq]
  source? := some ``CatCrypt.Crypto.OracleProg.runWith
  compileLemma? := some ``CatCrypt.Crypto.OracleProg.Timed.compile_runWithTree
  progArg := 1

end OracleProg

end CatCrypt.Crypto

register_tree_kind CatCrypt.Crypto.OracleProg.oracleProgKind

register_interpreter CatCrypt.Crypto.OracleProg.runWithInterp

/-! The costed mirror of EUF-CMA adversaries, whose field `run` is an oracle program. -/

derive_timed_structure CatCrypt.Crypto.Signatures.EUFCMAAdversary
