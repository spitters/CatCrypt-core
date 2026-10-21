/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.Core.SPTreeTimedOps
public import Lean

/-!
# Derived step costs of oracle-tree reductions

`derive_timed R` takes a reduction `R` whose result is an oracle tree `OracleAdv D R α` and
defines its costed form `R.timed`, whose result is a step-prefixed tree
`ℕ × OracleAdv.Timed D R α`, together with the erasure theorem `R.erase_timed`:
`(R.timed xs').2.erase = R xs`, where `xs` is obtained from `xs'` by erasing the costed
binders and dropping the cost companions. The theorem is proved by unfolding both sides and
rewriting with the erasure lemmas of `CatCryptCore.Crypto.OracleAdversaryTimed`, by
functional induction on `R.timed` when `R` is recursive, and is checked by the kernel.

## Tree kinds

The translation is driven by a table of tree kinds (`treeKinds`). An entry gives the tree type
and its costed type, their erasure and step prefix, the nodes and combinators with their costed
forms and the role of each argument (`ArgRole`), and the lemmas that prove the erasure theorems.
The table has two entries:

* oracle trees `OracleAdv D R α`, costed by `OracleAdv.Timed D R α`
  (`CatCryptCore.Crypto.OracleAdversaryTimed`);
* syntactic computation trees `SPTree α`, costed by `SPTree.Timed α`
  (`CatCryptCore.Core.SPTreeTimed`, `CatCryptCore.Core.SPTreeTimedOps`): the nodes `ret`,
  `sample`, `get`, `set` and `fail`, and the combinators `SPTree.bind` and `SPTree.map`.

Below, "tree" means a tree of a kind in the table, and the rules for oracle trees apply to
every kind.

## Binders

A binder of `R` is translated by its type:

* a type, a proposition or an instance is kept;
* first-order data is kept;
* an oracle tree `A : OracleAdv D R α` becomes `A : OracleAdv.Timed D R α`, erased by
  `A.erase`;
* a function into oracle trees `k : X → OracleAdv D R α` becomes `k : X → OracleAdv.Timed D R α`
  followed by its cost companion `kCost : X → ℕ`, the cost of computing the tree `k x` from
  `x`; it is erased by `fun x => (k x).erase`;
* any other function `f : X → Y` is kept and followed by its cost companion `fCost : X → ℕ`,
  the cost of evaluating `f x`;
* data holding functions (a pair with a function component, such as a simulation state with
  a table `ℕ → List (D × R)`) becomes its costed value (`hatTy?`), in which each function
  `X → Y` with a first-order domain is a costed closure `(X → Ŷ) × (X → ℕ)`: the function and
  its cost companion; it is erased by `ε`, which keeps the functions (`epsE`).

## Costed closures

A function value inside data, in a state component, in the result of a tree or received from
a tree is carried as a costed closure (the writer translation of function types, the case of
a first-order domain of the typed measures of Forster and Kunze):

* building a closure `fun x => e` costs nothing, and its companion is `fun x => cost(e)`;
* a partial application `g a₁ … aₖ` of a constant, or of a local function with a cost
  companion, evaluates its arguments when it is built, and its companion prices the call
  `g a₁ … aₖ x` with the arguments as values; a partial application of any other local
  function is a table; functions in the results of a closure are tables; so
  `Function.update f a v`, unfolded, has companion
  `fun x => 2 + (if x = a then 0 else 1 + fCost x)`;
* applying a costed closure `p` to `x` costs `1 + p.2 x` plus the cost of `x`;
* a function sampled by a `rand` or `sample` node, answered by a query, or returned by a tree
  binder (the adversary), is a table: its companion is zero (`ι`), so an application costs
  one; a tree binder keeps its plain costed type, and a tree argument of a callee whose
  binder takes the plain type is passed with its results erased (`ε`);
* a pair, an `if` and a call of a non-recursive definition holding functions are translated
  componentwise, by branch and by unfolding.

The costed tree of a reduction whose result holds functions has the costed result type, and
its erasure theorem is `(R.timed xs').2.erase.bind (fun y => ret (ε y)) = R xs`, with
`R.erase_timed_bind` for a continuation that depends on a result only through its erasure
(`OracleAdv.Timed.bind_hat`, `SPTree.Timed.bind_hat`). A simulation whose state holds
functions is translated to `OracleAdv.Timed.simulateHat ε ι`, the costed simulation with the
erasure and the lift of the state, so that the handler's companions thread through the state;
its erasure theorem `OracleAdv.Timed.erase_simulateHat_bind` holds when the erased handler
depends on the state only through its erasure, which the handler's erasure theorem gives.

A function-typed field `m` of a field path `s` (a binder of `R`, or a field of a field path:
`kit`, `kit.hkdf`), that is a field of a scheme structure without a registered cost
`m.timedCost` (not a class method), applied in the body or in a definition the
derivation unfolds, is a primitive of the scheme: its cost companion `mCost : X → ℕ`, the cost
of evaluating `s.m x`, is a further binder after the binders of `R`, one for each field and
path that the derivation prices. The fields are found by a first pass of the translation. A
recursive call of `R` passes the same structures. The paths are recorded as the definition
`R.timed.fieldPaths`, a function of the binders of `R`; a caller of `R` (also through a
partial application, eta-expanded) passes its companions for the paths at its arguments.

## Cost rules

Costs follow call-by-value evaluation:

* a call of a constant or of a local function costs one plus the callee's cost at its
  arguments plus the costs of its arguments; the callee's cost is its cost companion for a
  local function, its registered cost `f.timedCost` for a registered primitive, the cost of
  its unfolded body for a non-recursive definition, and the step cost of `f.timed` for a
  reduction;
* an arithmetic operation on `ℕ` or on `ZMod p` (a word for the fixed modulus), and an
  arithmetic, bitwise or comparison operation on a fixed-width word (`BitVec n`, `UInt8` to
  `UInt64`, `Fin n`), costs one plus its arguments;
* a function passed as a discriminant of a match (`Option.bind o f`) is priced, where the
  match binds it, by its companion; a `let` applied to arguments is zeta- and beta-reduced;
* a tree-valued field of a field path (`S.kem.encaps pk`, a program of a scheme) is a
  primitive: its tree runs at the unit cost of its nodes (`OracleAdv.Timed.ofAdv`) and its
  computation is priced by a cost companion indexed by the field's arguments;
* a method of an abstract algebraic structure, a method of an algebraic operation class
  (`+`, `*`, `-`, `^`, `•` of `[AddCommGroup M]` or `[Field F]`, `algebraicMethods`) or of
  `CryptoWord` whose instance is built from a local instance, costs one plus its arguments,
  as one call of the interface, and gets no cost companion; a method of any other class on a
  local instance (a primitive interface of a protocol) keeps its cost companion;
* `if` and `match` cost one, plus the costs of the condition or the discriminants, plus the
  cost of the branch taken;
* constructors, literals, numerals, casts, projections and variables cost nothing beyond
  their arguments (the parameters of a constructor's inductive type are not among them), and
  a closure costs nothing to build;
* a `rand` or `query` node costs its registered unit (`OracleAdv.Timed.TimeBound`); the
  distribution of a `rand` node is priced by the rules above, with the uniform and point
  distributions free, since sampling is included in the node's unit;
* a `sample`, `get` or `set` node of a computation tree costs its registered unit
  (`SPTree.Timed.time`), and the location and the value of a `get` or `set` node are priced by
  the rules above;
* `OracleAdv.bind`, `OracleAdv.simulate` and `OracleAdv.mapQuery` are translated to
  `OracleAdv.Timed.bind`, `OracleAdv.Timed.simulate` and `OracleAdv.Timed.mapQuery`, with the
  cost of the renaming `ren d` of a `mapQuery` charged per query; `SPTree.bind` and
  `SPTree.map` are translated to `SPTree.Timed.bind` and `SPTree.Timed.map`, with the cost of
  the function of a `map` charged per leaf;
* a match on an oracle-tree binder `A` of `R` (a definition by structural recursion over the
  adversary, a handler of its nodes) is translated to the case analysis
  `OracleAdv.Timed.casesOn` of its costed tree `A'`, at cost one: the continuation `k` of a
  `rand` or `query` node stands for the continuation of the costed node, with the node's step
  cost as its cost companion, so a recursive call on `k x` is a recursive call on the costed
  tree and `R.timed` is defined by structural recursion on `A'`; its time follows from
  `OracleAdv.Timed.timeBound_fold`;
* a `let` of first-order data is priced once: `let x := v; b` costs the cost of `v` plus the
  cost of `b`, in which `x` costs nothing; in a tree the `let` stays around the costed tree and
  the cost of `v` is charged in front; a `let` of a type, a proof, a function or a tree is
  substituted into its body;
* an unfolded definition binds its arguments in the same way, so that each argument is priced
  once per call, whether its parameter is used once, several times or not at all.

The binders of `R` are those of its type, which is reduced through type definitions: a
reduction whose declared type is an adversary type `W → W → W → SPComp Bool` under a name
takes the three binders of that type.

A recursive data function without a registered cost is priced by its cost derived on demand
with `derive_cost` (`deriveCostCore`), by its own recursion. A derived cost takes, after the
arguments, the cost companions of the field paths of its binders that its body applies
(`kit.hash`); a call passes the caller's companions for the same paths at the call's arguments.

A call `b` of which two projections `b.1`, `b.2` occur among the arguments of an unfolded
definition is bound by one `let` and priced once (`bindArgsShared`). Unfolding is bounded by
the option `derive_timed.maxDepth` (default 16) nested definitions.

A registered primitive `f` has a cost `f.timedCost`, a definition taking the arguments of
`f`, each function-typed argument followed by its cost companion, and returning `ℕ`; the
command `timed_cost f := e` defines it. A registered cost is a trusted statement about the
cost of `f`. A reduction whose costed form is written by hand is registered by defining
`R.timed` and `R.erase_timed` in the binder convention above.

A field `m` of a computed structure `g b₁ … bₖ`, where `g` is a field path (`kit.aead`) or a
local function with a cost companion, applied as `(g b₁ … bₖ).m x₁ … xₙ`, is priced as the
structure `g b₁ … bₖ` by the rules above, plus one, plus its cost companion
`g_mCost b₁ … bₖ x₁ … xₙ` (`aead_encCost iv k m`), a further binder after the binders of `R`
indexed by the arguments that compute the structure, plus the costs of the `xᵢ`.

Costed forms and costs are exposed definitions in a `module` file, so that importing modules
unfold them. A reduction valued in `PMF` is refused: a distribution has no cost structure.

Calls of reductions without a costed form are derived on demand. A derivation fails, with
the reason, on a function stored in data that is not a costed closure as above (a local
function without a cost companion, a function in a list or an option, a closure returned by
a recursive function), a
field of a structure that is neither a field path nor a field of a computed structure as
above, an opaque data function without a registered cost, a recursive data
function whose cost `derive_cost` does not derive (a class method on a local instance in its
body needs `derive_cost (unit := …)`), a `match` whose motive depends on its
discriminants, a match on an oracle tree that is not a binder, a recursive call that changes a
structure whose fields have cost companions, and a call of a reduction whose costed form
takes such companions.

## Attribution

The translation rules and the derivation on demand follow the instrumented translation of
the Ironwood project (`Zcash/Meta/Translate.lean`, `Instrument.lean`, `Efficient.lean`),
which is dual-licensed under the MIT and Apache-2.0 licences; the cost rules are those of
Isabelle's `time_fun` command.

## Main definitions

* `derive_timed R`, `derive_timed (suffix := s) R` — define `R.timed` (or `R.s`) and
  `R.erase_timed` (or `R.erase_s`)
* `timed_cost f := e` — register the cost `e` of the primitive `f`
* `treeKinds` — the table of tree kinds

## Main results

* `OracleAdv.Timed.timeBound_fold` — the time of a handler of the nodes of a costed tree:
  overhead `h` per unit of the tree's time and `r` at a leaf give time `(1 + h) * T + r`
* `OracleAdv.Timed.erase_simulateHat_bind` — erasure of a costed simulation whose state holds
  costed closures
* `OracleAdv.Timed.bind_hat`, `SPTree.Timed.bind_hat` — sequencing after a tree whose result
  holds costed closures
* `OracleAdv.Timed.timeBound_simulateHat_inv` — the time of a costed simulation under a state
  invariant indexed by the number of queries: `T + ∑_{j < q} t (i + j)`
-/

public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv.Timed

variable {D R α : Type}

/-- Erasure of a step-prefixed tree commutes with `if`. -/
theorem erase_snd_ite (c : Prop) [Decidable c] (x y : ℕ × Timed D R α) :
    (if c then x else y).2.erase = if c then x.2.erase else y.2.erase := by
  split <;> rfl

/-- Erasure of a step-prefixed tree commutes with a dependent `if`. -/
theorem erase_snd_dite (c : Prop) [Decidable c] (x : c → ℕ × Timed D R α)
    (y : ¬c → ℕ × Timed D R α) :
    (if h : c then x h else y h).2.erase = if h : c then (x h).2.erase else (y h).2.erase := by
  split <;> rfl

/-- **Time of a handler.** Let `H` interpret a costed tree from a state, with overhead at most
`h` per unit of the tree: at a `rand` or `query` node whose continuation has step cost `c`,
`H` takes time `M` whenever every continuation `k b` takes time `M - (1 + h) * (1 + c b)`
from every state; at a leaf it takes time `r`. Then an adversary of time `T` is handled in
time `(1 + h) * T + r`. A costed form that `derive_timed` derives by recursion over an oracle
tree is such an `H`, and `OracleAdv.Timed.simulate` and `subst` are its stateful and stateless
cases with the cost of each query in the handler (`timeBound_simulate`). -/
theorem timeBound_fold {S D' R' β : Type} (H : Timed D R α → S → ℕ × Timed D' R' β)
    {h r : ℕ} (hret : ∀ a s, StepTimeBound (H (ret a) s) r)
    (hrand : ∀ {γ : Type} (p : PMF γ) (c : γ → ℕ) (k : γ → Timed D R α) (s : S) (M : ℕ),
      1 + h ≤ M → (∀ b, (1 + h) * (1 + c b) ≤ M) →
      (∀ b s', StepTimeBound (H (k b) s') (M - (1 + h) * (1 + c b))) →
      StepTimeBound (H (rand p c k) s) M)
    (hquery : ∀ (d : D) (c : R → ℕ) (k : R → Timed D R α) (s : S) (M : ℕ),
      1 + h ≤ M → (∀ b, (1 + h) * (1 + c b) ≤ M) →
      (∀ b s', StepTimeBound (H (k b) s') (M - (1 + h) * (1 + c b))) →
      StepTimeBound (H (query d c k) s) M)
    {A : Timed D R α} {T : ℕ} (hA : A.TimeBound T) (s : S) :
    StepTimeBound (H A s) ((1 + h) * T + r) := by
  induction A generalizing T s with
  | ret a => exact (hret a s).mono (Nat.le_add_left r _)
  | rand p c k ih =>
    refine hrand p c k s _ ?_ (fun b => ?_) (fun b s' => (ih b (hA.2 b).2 s').mono ?_)
    · exact (Nat.le_mul_of_pos_right _ hA.1).trans (Nat.le_add_right _ _)
    · have := (hA.2 b).1; have := hA.1
      exact (Nat.mul_le_mul_left _ (by omega)).trans (Nat.le_add_right _ _)
    · have e : (1 + h) * T = (1 + h) * (1 + c b) + (1 + h) * (T - 1 - c b) := by
        rw [← Nat.mul_add]; congr 1; have := (hA.2 b).1; have := hA.1; omega
      omega
  | query d c k ih =>
    refine hquery d c k s _ ?_ (fun b => ?_) (fun b s' => (ih b (hA.2 b).2 s').mono ?_)
    · exact (Nat.le_mul_of_pos_right _ hA.1).trans (Nat.le_add_right _ _)
    · have := (hA.2 b).1; have := hA.1
      exact (Nat.mul_le_mul_left _ (by omega)).trans (Nat.le_add_right _ _)
    · have e : (1 + h) * T = (1 + h) * (1 + c b) + (1 + h) * (T - 1 - c b) := by
        rw [← Nat.mul_add]; congr 1; have := (hA.2 b).1; have := hA.1; omega
      omega

/-- An `if` between two pairs is the pair of the `if`s of their components. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.ite_prod_mk {β γ : Type _} (c : Prop) [Decidable c]
    (a b : β) (a' b' : γ) :
    (if c then (a, a') else (b, b')) = (if c then a else b, if c then a' else b') := by
  split <;> rfl

/-- The first component of an `if` between two pairs. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.fst_ite {β γ : Type _} (c : Prop) [Decidable c]
    (p q : β × γ) : (if c then p else q).1 = if c then p.1 else q.1 := by
  split <;> rfl

/-- The second component of an `if` between two pairs. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.snd_ite {β γ : Type _} (c : Prop) [Decidable c]
    (p q : β × γ) : (if c then p else q).2 = if c then p.2 else q.2 := by
  split <;> rfl

/-- The costed simulation of a handler whose state `Ŝ` carries costed closures: the
simulation `simulate impl A s`, with the erasure `ε : Ŝ → S` of the state and a lift
`ι : S → Ŝ` as parameters, which state its erasure theorem `erase_simulateHat_bind`. -/
def simulateHat {D' R' S Ŝ : Type} (_ε : Ŝ → S) (_ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ)) (A : Timed D R α) (s : Ŝ) :
    ℕ × Timed D' R' (α × Ŝ) :=
  simulate impl A s

/-- **Erasure of a costed simulation with costed closures in its state.** If the erased
handler depends on the state only through its erasure `ε` (`h`), and so does the
continuation `k` (`hk`), then the erased costed simulation followed by `k` is the
simulation of the erased handler from the erased state, followed by `k` on the lifted
state. -/
theorem erase_simulateHat_bind {D' R' S Ŝ β : Type} (ε : Ŝ → S) (ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ))
    (h : ∀ s d, (impl s d).2.erase.bind (fun y => .ret (y.1, ε y.2)) =
      (impl (ι (ε s)) d).2.erase.bind (fun y => .ret (y.1, ε y.2)))
    (A : Timed D R α) (s : Ŝ) (k : α × Ŝ → OracleAdv D' R' β)
    (hk : ∀ y, k y = k (y.1, ι (ε y.2))) :
    (simulateHat ε ι impl A s).2.erase.bind k =
      (OracleAdv.simulate (fun s d => (impl (ι s) d).2.erase.bind fun y => .ret (y.1, ε y.2))
        A.erase (ε s)).bind fun y => k (y.1, ι y.2) := by
  unfold simulateHat
  induction A generalizing s with
  | ret a => exact hk (a, s)
  | rand p c k' ih => simp only [simulate, erase, OracleAdv.simulate, OracleAdv.bind, ih]
  | query d c k' ih =>
    simp only [simulate, delay, erase, OracleAdv.simulate, erase_bind]
    rw [← h s d]
    simp only [OracleAdv.bind_assoc, OracleAdv.bind_ret, ih]

/-- An oracle tree followed by `ret` is the tree. -/
theorem bind_ret_eq (t : OracleAdv D R α) : t.bind (fun y => .ret y) = t := by
  induction t with
  | ret a => rfl
  | rand p k ih => simp only [OracleAdv.bind, ih]
  | query d k ih => simp only [OracleAdv.bind, ih]

/-- **Sequencing after a tree with costed closures in its result.** If `t` followed by the
erasure `ε` of its results is `t₀`, and the continuation `k` depends on a result only through
its erasure, then `t` followed by `k` is `t₀` followed by `k` on the lifted result. -/
theorem bind_hat {α' β : Type} (ε : α' → α) (ι : α → α') (t : OracleAdv D R α')
    (t₀ : OracleAdv D R α) (h : t.bind (fun y => .ret (ε y)) = t₀)
    (k : α' → OracleAdv D R β) (hk : ∀ y, k y = k (ι (ε y))) :
    t.bind k = t₀.bind fun y => k (ι y) := by
  subst h
  rw [OracleAdv.bind_assoc]
  exact congrArg t.bind (funext hk)

/-- `AllRet P A`: every leaf `ret a` of the costed tree `A` satisfies `P a`. -/
@[expose] def AllRet (P : α → Prop) : Timed D R α → Prop
  | ret a => P a
  | rand _ _ k => ∀ b, AllRet P (k b)
  | query _ _ k => ∀ r, AllRet P (k r)

/-- Times add under sequencing when the continuation is bounded on the leaves of the tree
only (`timeBound_bind`, with the continuation's bound required where `P` holds). -/
theorem timeBound_bind_of_allRet {β : Type} {P : α → Prop} {A : Timed D R α}
    {f : α → ℕ × Timed D R β} {m n : ℕ} (hA : A.TimeBound m) (hP : AllRet P A)
    (hf : ∀ a, P a → StepTimeBound (f a) n) : StepTimeBound (A.bind f) (m + n) := by
  induction A generalizing m with
  | ret a => exact (hf a hP).mono (Nat.le_add_left n m)
  | rand p c k ih =>
    have h1 := hA.1
    simp only [bind, stepTimeBound_zero, timeBound_rand_iff]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hA.2 b).1
    exact (stepTimeBound_delay (c := c b) (ih b (hA.2 b).2 (hP b))).mono (by omega)
  | query d c k ih =>
    have h1 := hA.1
    simp only [bind, stepTimeBound_zero, timeBound_query_iff]
    refine ⟨by omega, fun r => ?_⟩
    have h2 := (hA.2 r).1
    exact (stepTimeBound_delay (c := c r) (ih r (hA.2 r).2 (hP r))).mono (by omega)

/-- **Simulation time with a state invariant.** Let `Inv i` hold of the states reached
after `i` queries: a program of `impl` from a state with `Inv i` has time at most `t i` and
returns states with `Inv (i + 1)`. Then an adversary of time `T` with at most `q` queries,
simulated from a state with `Inv i`, has time at most `T + ∑_{j < q} t (i + j)`. A handler
whose state carries a table of costed closures, whose companions grow by a bounded amount per
query, has a per-query time `t j` that grows with `j`, which a single uniform bound
(`timeBound_simulate`) does not state. -/
theorem timeBound_simulateHat_inv {D' R' S Ŝ : Type} (ε : Ŝ → S) (ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ)) (Inv : ℕ → Ŝ → Prop) (t : ℕ → ℕ)
    (himpl : ∀ i s d, Inv i s →
      StepTimeBound (impl s d) (t i) ∧ AllRet (fun y => Inv (i + 1) y.2) (impl s d).2)
    {A : Timed D R α} {T q : ℕ} (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q)
    (i : ℕ) (s : Ŝ) (hs : Inv i s) :
    StepTimeBound (simulateHat ε ι impl A s) (T + ∑ j ∈ Finset.range q, t (i + j)) := by
  unfold simulateHat
  induction A generalizing T q i s with
  | ret a => exact ⟨Nat.zero_le _, trivial⟩
  | rand p c k ih =>
    have h1 := hA.1
    simp only [simulate, stepTimeBound_zero, timeBound_rand_iff]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hA.2 b).1
    exact (stepTimeBound_delay (c := c b) (ih b (hA.2 b).2 (hq b) i s hs)).mono (by omega)
  | query d c k ih =>
    cases q with
    | zero => exact (hq : False).elim
    | succ q =>
      have hsum : ∑ j ∈ Finset.range (q + 1), t (i + j) =
          ∑ j ∈ Finset.range q, t (i + 1 + j) + t i := by
        rw [Finset.sum_range_succ']
        simp only [Nat.add_zero]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_assoc, Nat.add_comm 1 j]
      rw [hsum]
      have hk : ∀ x : R × Ŝ, Inv (i + 1) x.2 →
          StepTimeBound (delay (c x.1) (simulate impl (k x.1) x.2))
            (T - 1 + ∑ j ∈ Finset.range q, t (i + 1 + j)) := fun x hx =>
        (stepTimeBound_delay (ih x.1 (hA.2 x.1).2 (hq x.1) (i + 1) x.2 hx)).mono
          (by have := (hA.2 x.1).1; omega)
      have hi := himpl i s d hs
      have h := stepTimeBound_delay (c := (impl s d).1)
        (timeBound_bind_of_allRet hi.1.2 hi.2 hk)
      exact h.mono (by have := hi.1.1; have := hA.1; omega)

end CatCrypt.Crypto.OracleAdv.Timed

namespace CatCrypt.Core.SPTree.Timed

/-- **Sequencing after a computation tree with costed closures in its result.** If `t`
followed by the erasure `ε` of its results is `t₀`, and the continuation `k` depends on a
result only through its erasure, then `t` followed by `k` is `t₀` followed by `k` on the
lifted result. -/
theorem bind_hat {α α' β : Type} (ε : α' → α) (ι : α → α') (t : SPTree α')
    (t₀ : SPTree α) (h : t.bind (fun y => .ret (ε y)) = t₀)
    (k : α' → SPTree β) (hk : ∀ y, k y = k (ι (ε y))) :
    t.bind k = t₀.bind fun y => k (ι y) := by
  subst h
  rw [SPTree.bind_assoc]
  exact congrArg t.bind (funext hk)

end CatCrypt.Core.SPTree.Timed

meta section

namespace CatCrypt.Tactics.DeriveTimed

open Lean Elab Meta Term Command

/-- How a binder of a reduction is translated. -/
inductive Kind where
  /-- A type, a proposition or an instance: kept. -/
  | static
  /-- First-order data: kept. -/
  | data
  /-- A function that is not into oracle trees: kept, with a cost companion. -/
  | fn
  /-- An oracle tree: replaced by a costed tree. -/
  | tree
  /-- A function into oracle trees: replaced by a function into costed trees, with a cost
  companion. -/
  | treeFn
  /-- Data holding functions (a pair with a function component): replaced by its costed
  value, in which each function is a costed closure. -/
  | hat
  deriving Inhabited, BEq, Repr

/-- The translation of a local of the reduction: its kind, its costed value (the costed tree
for `tree` and `treeFn`, the local itself otherwise) and its cost companion. -/
structure LocalInfo where
  kind : Kind
  value : Expr
  companion? : Option Expr := none
  deriving Inhabited

/-- The context of a translation: the translated locals, the reduction being derived with
the local that stands for its costed form, the suffix of costed forms, the unfolding
depth of data functions, the fields of local structures and instances, each applied to its
parameters and its structure, with their cost companions, the binders of the reduction, at
which field paths start, the reference collecting the field paths without a cost companion
(`fieldRec?`, in the first pass), and the data function whose cost is being derived, with the
local that stands for its cost (`selfCost?`). -/
structure Ctx where
  locals : FVarIdMap LocalInfo := {}
  self? : Option (Name × Expr) := none
  suffix : Name := `timed
  depth : Nat := 0
  visiting : NameSet := {}
  fields : Array (Expr × Expr) := #[]
  top : Array FVarId := #[]
  fieldRec? : Option (IO.Ref (Array Expr)) := none
  selfCost? : Option (Name × Expr) := none
  /-- The binders of kind `hat` with the erasures `ε x̂` of their costed values, substituted
  for them in the costed form. -/
  hatSubst : Array (Expr × Expr) := #[]
  /-- The costed form has the plain interface of the reduction: a binder holding functions
  takes its plain value, whose functions are tables (`ι`), and the result is erased to the
  plain type (`ε`). The tree of a field of a structure-valued reduction has this interface, the
  one its costed mirror takes. -/
  plain : Bool := false

/-- The maximal nesting of unfolded data definitions (option `derive_timed.maxDepth`). -/
register_option derive_timed.maxDepth : Nat := {
  defValue := 16
  descr := "the maximal nesting of data definitions that derive_timed, derive_cost and \
    derive_reduction unfold to price a call"
}

/-- The maximal nesting of unfolded data definitions: the option `derive_timed.maxDepth`. -/
def maxDepth : CoreM Nat := return derive_timed.maxDepth.get (← getOptions)

/-- Constants that cost nothing beyond their arguments. -/
def freeConstants : Array Name :=
  #[``OfNat.ofNat, ``Nat.cast, ``NatCast.natCast, ``Int.cast, ``IntCast.intCast, ``id,
    ``Eq.rec, ``Eq.ndrec, ``Eq.mp, ``Eq.mpr, ``cast, ``Subtype.val, ``Fin.val,
    ``PMF.uniformOfFintype, ``PMF.pure, ``Classical.arbitrary, ``Inhabited.default]

/-- Operations of unit cost on `ℕ`: a call costs one. -/
def natUnitOps : Array Name :=
  #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``Nat.succ, ``Nat.add,
    ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.pred, ``Nat.min, ``Nat.max, ``Min.min,
    ``Max.max]

/-- Arithmetic operations of unit cost on `ZMod p`, whose elements are words for the fixed
modulus `p`: a call costs one. -/
def zmodUnitOps : Array Name :=
  #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``Add.add, ``Sub.sub,
    ``Mul.mul, ``Div.div, ``Neg.neg, ``Inv.inv]

/-- Arithmetic, bitwise and comparison operations of unit cost on fixed-width words
(`BitVec n`, `UInt8`, `UInt16`, `UInt32`, `UInt64`, `Fin n`): a call costs one (word-RAM). -/
def wordUnitOps : Array Name :=
  #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``Add.add, ``Sub.sub,
    ``Mul.mul, ``Div.div, ``Mod.mod, ``Neg.neg, ``HAnd.hAnd, ``HOr.hOr, ``HXor.hXor,
    ``HShiftLeft.hShiftLeft, ``HShiftRight.hShiftRight, ``AndOp.and, ``OrOp.or, ``XorOp.xor,
    ``ShiftLeft.shiftLeft, ``ShiftRight.shiftRight, ``Complement.complement, ``BEq.beq,
    ``Max.max, ``Min.min]

/-- Whether the instance `inst` is built from a local instance: it mentions a local whose type
is a class (a section variable or a binder `[AddCommGroup M]`). -/
def builtFromLocalInstance (inst : Expr) : MetaM Bool := do
  let fvs := (collectFVars {} inst).fvarIds
  fvs.anyM fun fv => do
    let some d := (← getLCtx).find? fv | return false
    return (← isClass? d.type).isSome

/-- The methods of the algebraic operation classes: on a local instance (an abstract algebraic
structure) a call costs one unit, as one call of the interface. -/
def algebraicMethods : Array Name :=
  #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``HPow.hPow, ``HSMul.hSMul,
    ``HVAdd.hVAdd, ``Add.add, ``Sub.sub, ``Mul.mul, ``Div.div, ``Mod.mod, ``Neg.neg, ``Inv.inv,
    ``Pow.pow, ``SMul.smul, ``VAdd.vadd, ``Zero.zero, ``One.one, ``OfNat.ofNat]

/-- Whether the class method `c` is a unit operation on a local instance: a method of an
algebraic operation class, or a word operation of `CryptoWord`. The methods of other classes
(the primitive interfaces of a protocol, `WireGuardDependencies.aead_enc`) keep their cost
companions. -/
def isUnitMethod (c : Name) : Bool :=
  algebraicMethods.contains c || c.getPrefix == `CatCrypt.Crypto.CryptoWord

/-- Whether `t` is a fixed-width word type: `BitVec n`, `UInt8` to `UInt64` or `Fin n`. -/
def isWordType (t : Expr) : MetaM Bool := do
  let t ← whnfR t
  return t.isAppOfArity ``BitVec 1 || t.isAppOfArity ``Fin 1 || t.isConstOf ``UInt8 ||
    t.isConstOf ``UInt16 || t.isConstOf ``UInt32 || t.isConstOf ``UInt64

/-- The literal value of a numeral of type `ℕ`. -/
def natVal? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 0).isConstOf ``Nat then
      match e.getArg! 1 with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- The numeral `n : ℕ`. -/
def natE (n : Nat) : Expr := mkNatLit n

/-- `a + b` on `ℕ`, with zero summands dropped and leading numerals folded. -/
def add (a b : Expr) : Expr :=
  match natVal? a, natVal? b with
  | some 0, _ => b
  | _, some 0 => a
  | some m, some n => natE (m + n)
  | some m, none =>
    if b.isAppOfArity ``HAdd.hAdd 6 then
      match natVal? (b.getArg! 4) with
      | some n => mkNatAdd (natE (m + n)) (b.getArg! 5)
      | none => mkNatAdd a b
    else mkNatAdd a b
  | _, _ => mkNatAdd a b

/-- The sum of the costs `cs`. -/
def sum (cs : Array Expr) : Expr := cs.foldl add (natE 0)

/-- How an argument of a node or a combinator of a tree kind is translated. The roles of a
node or a combinator apply to the trailing arguments of its constant; the leading arguments
are the parameters of the tree type. -/
inductive ArgRole where
  /-- Kept, at no cost. -/
  | keep
  /-- Kept, with its cost charged. -/
  | data
  /-- A continuation with `n` binders: replaced by its step cost and its costed tree, both
  abstracted over the binders. -/
  | cont (n : Nat)
  /-- A tree: replaced by its costed tree, with its step cost charged in front. -/
  | tree
  /-- A function of `n` arguments into trees: replaced by a function into step-prefixed costed
  trees. -/
  | pairFn (n : Nat)
  /-- A data function of `n` arguments: kept and followed by its cost per call, `extra` plus the
  cost of evaluating it. -/
  | perCall (extra n : Nat)
  deriving Inhabited, BEq, Repr

/-- A node of a tree kind: the constructor `src` and the costed constructor `tgt`, which takes
the parameters of the costed tree type and the translated trailing arguments. -/
structure Node where
  src : Name
  tgt : Name
  roles : Array ArgRole
  deriving Inhabited

/-- A combinator of a tree kind: the constant `src` and its costed form `tgt`, which takes the
translated trailing arguments and returns a step-prefixed costed tree when `pair` holds and a
costed tree otherwise. -/
structure Comb where
  src : Name
  tgt : Name
  roles : Array ArgRole
  pair : Bool
  deriving Inhabited

/-- A kind of tree: the tree type `tree` with `nParams` parameters, its costed tree type `timed`
with the same parameters, the erasure `erase` and the step prefix `delay` of the costed type,
its nodes, its combinators, and the lemmas that prove the erasure theorems. -/
structure TreeKind where
  noun : String
  tree : Name
  nParams : Nat
  timed : Name
  erase : Name
  delay : Name
  nodes : Array Node
  combinators : Array Comb
  eraseLemmas : Array Name
  /-- The lemmas that push the erasure `ε` of a result holding functions to the leaves. -/
  hatLemmas : Array Name := #[]
  deriving Inhabited

/-- Oracle trees `OracleAdv D R α`: `ret`, `rand` and `query` nodes, and the combinators
`bind`, `simulate` and `mapQuery`. -/
def oracleKind : TreeKind where
  noun := "oracle tree"
  tree := ``CatCrypt.Crypto.OracleAdv
  nParams := 3
  timed := ``CatCrypt.Crypto.OracleAdv.Timed
  erase := ``CatCrypt.Crypto.OracleAdv.Timed.erase
  delay := ``CatCrypt.Crypto.OracleAdv.Timed.delay
  nodes := #[
    ⟨``CatCrypt.Crypto.OracleAdv.ret, ``CatCrypt.Crypto.OracleAdv.Timed.ret, #[.data]⟩,
    ⟨``CatCrypt.Crypto.OracleAdv.rand, ``CatCrypt.Crypto.OracleAdv.Timed.rand,
      #[.data, .cont 1]⟩,
    ⟨``CatCrypt.Crypto.OracleAdv.query, ``CatCrypt.Crypto.OracleAdv.Timed.query,
      #[.data, .cont 1]⟩]
  combinators := #[
    ⟨``CatCrypt.Crypto.OracleAdv.bind, ``CatCrypt.Crypto.OracleAdv.Timed.bind,
      #[.tree, .pairFn 1], true⟩,
    ⟨``CatCrypt.Crypto.OracleAdv.simulate, ``CatCrypt.Crypto.OracleAdv.Timed.simulate,
      #[.pairFn 2, .tree, .data], true⟩,
    ⟨``CatCrypt.Crypto.OracleAdv.mapQuery, ``CatCrypt.Crypto.OracleAdv.Timed.mapQuery,
      #[.perCall 1 1, .tree], false⟩]
  eraseLemmas := #[``CatCrypt.Crypto.OracleAdv.Timed.erase,
    ``CatCrypt.Crypto.OracleAdv.Timed.delay, ``CatCrypt.Crypto.OracleAdv.Timed.erase_bind,
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_simulate,
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_mapQuery,
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_snd_ite,
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_snd_dite,
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_ofAdv]
  hatLemmas := #[``CatCrypt.Crypto.OracleAdv.bind, ``CatCrypt.Crypto.OracleAdv.bind_assoc,
    ``CatCrypt.Crypto.OracleAdv.bind_ret,
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_simulateHat_bind, ``Prod.mk.eta,
    ``CatCrypt.Crypto.OracleAdv.Timed.bind_ret_eq,
    ``CatCrypt.Tactics.DeriveTimed.fst_ite, ``CatCrypt.Tactics.DeriveTimed.snd_ite,
    ``CatCrypt.Tactics.DeriveTimed.ite_prod_mk]

/-- Syntactic computation trees `SPTree α`: `ret`, `sample`, `get`, `set` and `fail` nodes, and
the combinators `SPTree.bind` and `SPTree.map`. -/
def spTreeKind : TreeKind where
  noun := "computation tree"
  tree := ``CatCrypt.Core.SPTree
  nParams := 1
  timed := ``CatCrypt.Core.SPTree.Timed
  erase := ``CatCrypt.Core.SPTree.Timed.erase
  delay := ``CatCrypt.Core.SPTree.Timed.delay
  nodes := #[
    ⟨``CatCrypt.Core.SPTree.ret, ``CatCrypt.Core.SPTree.Timed.ret, #[.data]⟩,
    ⟨``CatCrypt.Core.SPTree.sample, ``CatCrypt.Core.SPTree.Timed.sample,
      #[.keep, .keep, .keep, .cont 1]⟩,
    ⟨``CatCrypt.Core.SPTree.get, ``CatCrypt.Core.SPTree.Timed.get, #[.data, .cont 1]⟩,
    ⟨``CatCrypt.Core.SPTree.set, ``CatCrypt.Core.SPTree.Timed.set, #[.data, .data, .cont 0]⟩,
    ⟨``CatCrypt.Core.SPTree.fail, ``CatCrypt.Core.SPTree.Timed.fail, #[]⟩]
  combinators := #[
    ⟨``CatCrypt.Core.SPTree.bind, ``CatCrypt.Core.SPTree.Timed.bind, #[.tree, .pairFn 1], true⟩,
    ⟨``CatCrypt.Core.SPTree.map, ``CatCrypt.Core.SPTree.Timed.map, #[.perCall 0 1, .tree],
      true⟩]
  eraseLemmas := #[``CatCrypt.Core.SPTree.Timed.erase_ret,
    ``CatCrypt.Core.SPTree.Timed.erase_sample, ``CatCrypt.Core.SPTree.Timed.erase_get,
    ``CatCrypt.Core.SPTree.Timed.erase_set, ``CatCrypt.Core.SPTree.Timed.erase_fail,
    ``CatCrypt.Core.SPTree.Timed.delay, ``CatCrypt.Core.SPTree.Timed.erase_bind,
    ``CatCrypt.Core.SPTree.Timed.erase_map, ``CatCrypt.Core.SPTree.Timed.erase_snd_ite,
    ``CatCrypt.Core.SPTree.Timed.erase_snd_dite]
  hatLemmas := #[``CatCrypt.Core.SPTree.bind, ``CatCrypt.Core.SPTree.bind_assoc,
    ``CatCrypt.Core.SPTree.bind_ret_val, ``CatCrypt.Core.SPTree.bind_ret, ``Prod.mk.eta,
    ``CatCrypt.Tactics.DeriveTimed.fst_ite,
    ``CatCrypt.Tactics.DeriveTimed.snd_ite, ``CatCrypt.Tactics.DeriveTimed.ite_prod_mk]

/-- The table of tree kinds. -/
def treeKinds : Array TreeKind := #[oracleKind, spTreeKind]

/-- A tree type: its kind and its parameters. -/
structure TreeTy where
  kind : TreeKind
  params : Array Expr
  deriving Inhabited

/-- Whether `t` is the tree type of a kind in the table. -/
def treeTy? (t : Expr) : MetaM (Option TreeTy) := do
  let t ← whnfR (← instantiateMVars t)
  for k in treeKinds do
    if t.isAppOfArity k.tree k.nParams then return some ⟨k, t.getAppArgs⟩
  return none

namespace TreeTy

/-- The tree type. -/
def type (T : TreeTy) : Expr := mkAppN (mkConst T.kind.tree) T.params

/-- The costed tree type. -/
def timedType (T : TreeTy) : Expr := mkAppN (mkConst T.kind.timed) T.params

/-- The step-prefixed tree type `ℕ × T.timedType`. -/
def pairType (T : TreeTy) : Expr :=
  mkApp2 (mkConst ``Prod [Level.zero, Level.one]) (mkConst ``Nat) T.timedType

/-- The pair `(c, t)` of a step cost and a costed tree. -/
def mkPair (T : TreeTy) (c t : Expr) : Expr :=
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.one]) (mkConst ``Nat) T.timedType c t

/-- Whether `p` is an application of the step prefix `delay`. -/
def isDelay (T : TreeTy) (p : Expr) : Bool := p.isAppOfArity T.kind.delay (T.kind.nParams + 2)

/-- The step cost of a step-prefixed tree, reduced on a literal pair and on `delay`. -/
partial def fstOf (T : TreeTy) (p : Expr) : Expr :=
  if p.isAppOfArity ``Prod.mk 4 then p.getArg! 2
  else if T.isDelay p then
    add (p.getArg! T.kind.nParams) (T.fstOf (p.getArg! (T.kind.nParams + 1)))
  else mkApp3 (mkConst ``Prod.fst [Level.zero, Level.one]) (mkConst ``Nat) T.timedType p

/-- The costed tree of a step-prefixed tree, reduced on a literal pair and on `delay`. -/
partial def sndOf (T : TreeTy) (p : Expr) : Expr :=
  if p.isAppOfArity ``Prod.mk 4 then p.getArg! 3
  else if T.isDelay p then T.sndOf (p.getArg! (T.kind.nParams + 1))
  else mkApp3 (mkConst ``Prod.snd [Level.zero, Level.one]) (mkConst ``Nat) T.timedType p

/-- The step cost `c` in front of the step-prefixed tree `p`. -/
def delayE (T : TreeTy) (c p : Expr) : Expr :=
  if natVal? c == some 0 then p
  else if p.isAppOfArity ``Prod.mk 4 then T.mkPair (add c (p.getArg! 2)) (p.getArg! 3)
  else if T.isDelay p then
    mkAppN (mkConst T.kind.delay)
      (T.params ++ #[add c (p.getArg! T.kind.nParams), p.getArg! (T.kind.nParams + 1)])
  else mkAppN (mkConst T.kind.delay) (T.params ++ #[c, p])

/-- The erasure of the costed tree `v`. -/
def eraseE (T : TreeTy) (v : Expr) : Expr := mkAppN (mkConst T.kind.erase) (T.params.push v)

/-- The result type of the tree type. -/
def result (T : TreeTy) : Expr := T.params[T.params.size - 1]!

end TreeTy

/-- The costed type of a type `t` of data holding functions: a function `X → Y` with a
first-order domain becomes the costed closure `(X → Ŷ) × (X → ℕ)`, a pair the pair of the
costed types of its components; `none` when `t` holds no such function, whose costed type is
`t` itself. -/
partial def hatTy? (t : Expr) : MetaM (Option Expr) := do
  let t ← instantiateMVars t
  if ← isProp t then return none
  if ← isTypeFormerType t then return none
  if (← isClass? t).isSome then return none
  if (← treeTy? t).isSome then return none
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    let a := tw.getArg! 0
    let b := tw.getArg! 1
    let ha ← hatTy? a
    let hb ← hatTy? b
    if ha.isNone && hb.isNone then return none
    return some (← mkAppM ``Prod #[ha.getD a, hb.getD b])
  unless tw.isForall do return none
  forallTelescope tw fun ys body => do
    if body.hasAnyFVar fun f => ys.any (·.fvarId! == f) then return none
    for y in ys do
      let yt ← inferType y
      if ← isProp yt then return none
      if ← isTypeFormerType yt then return none
      if (← isClass? yt).isSome then return none
      if (← hatTy? yt).isSome then return none
      if (← treeTy? yt).isSome then return none
    if ← isProp body then return none
    if ← isTypeFormerType body then return none
    if (← treeTy? body).isSome then return none
    if ← isProp (← inferType body) then return none
    let hb ← hatTy? body
    let fnT ← mkForallFVars ys (hb.getD body)
    let cT ← mkForallFVars ys (mkConst ``Nat)
    return some (← mkAppM ``Prod #[fnT, cT])

/-- The erasure `ε v : t` of the costed value `v` of type `hatTy? t`: the function of each
costed closure. -/
partial def epsE (t v : Expr) : MetaM Expr := do
  let some _ ← hatTy? t | return v
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    let a ← epsE (tw.getArg! 0) (← mkAppM ``Prod.fst #[v])
    let b ← epsE (tw.getArg! 1) (← mkAppM ``Prod.snd #[v])
    return ← mkAppM ``Prod.mk #[a, b]
  let f ← mkAppM ``Prod.fst #[v]
  forallTelescope tw fun ys body => do
    if (← hatTy? body).isNone then return f
    mkLambdaFVars ys (← epsE body (mkAppN f ys))

/-- The lift `ι v : hatTy? t` of the value `v : t`: each function with the cost companion
zero. -/
partial def iotaE (t v : Expr) : MetaM Expr := do
  let some _ ← hatTy? t | return v
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    let a ← iotaE (tw.getArg! 0) (← mkAppM ``Prod.fst #[v])
    let b ← iotaE (tw.getArg! 1) (← mkAppM ``Prod.snd #[v])
    return ← mkAppM ``Prod.mk #[a, b]
  forallTelescope tw fun ys body => do
    let f ← mkLambdaFVars ys (← iotaE body (mkAppN v ys).headBeta)
    let c ← mkLambdaFVars ys (mkNatLit 0)
    mkAppM ``Prod.mk #[f, c]

/-- The erasure function `fun y => ε y` of the type `t`. -/
def epsFun (t : Expr) : MetaM Expr := do
  let some ht ← hatTy? t | throwError "derive_timed: internal: `{t}` holds no function"
  withLocalDeclD `y ht fun y => do mkLambdaFVars #[y] (← epsE t y)

/-- The lift function `fun y => ι y` of the type `t`. -/
def iotaFun (t : Expr) : MetaM Expr := do
  withLocalDeclD `y t fun y => do mkLambdaFVars #[y] (← iotaE t y)

/-- The tree type of `t` with its result type replaced by its costed type (`hatTy?`). -/
def treeTyH? (t : Expr) : MetaM (Option TreeTy) := do
  let some T ← treeTy? t | return none
  let some h ← hatTy? T.result | return some T
  return some { T with params := T.params.set! (T.params.size - 1) h }

/-- The kind of a binder of type `t`. -/
def classify (t : Expr) : MetaM Kind := do
  if ← isProp t then return .static
  if ← isTypeFormerType t then return .static
  if (← isClass? t).isSome then return .static
  forallTelescope (← whnfR t) fun ys b => do
    if (← treeTy? b).isSome then
      return if ys.isEmpty then .tree else .treeFn
    if ys.isEmpty then return if (← hatTy? b).isSome then .hat else .data
    return .fn

/-- Whether `e` is data: not a type, a proposition, a proof or an instance. -/
def isDataExpr (e : Expr) : MetaM Bool := do
  let t ← inferType e
  if ← isTypeFormerType t then return false
  if ← isProp t then return false
  if (← isClass? t).isSome then return false
  return true

/-- Whether `t` is a computation type `SPComp α`. -/
def isSPCompType (t : Expr) : MetaM Bool := do
  return (← whnfR t).isAppOfArity `CatCrypt.Core.SPComp 1

/-- Whether `let x : t := v` is kept as a `let`, so that the cost of `v` is charged once: `v`
is first-order data that is not a variable, a literal, a constant or a closure. Any other
`let` is substituted into its body. -/
def keepsLet (t v : Expr) : MetaM Bool := do
  match v.consumeMData with
  | .fvar _ | .lit _ | .const .. | .lam .. | .sort _ | .forallE .. => return false
  | _ => pure ()
  if ← isProp t then return false
  if ← isTypeFormerType t then return false
  if (← isClass? t).isSome then return false
  if ← isSPCompType t then return false
  if (← treeTy? t).isSome then return false
  if (← whnfR t).isForall then return false
  if (← hatTy? t).isSome then return false
  return true

/-- The binders of the type `t`, which is reduced at default transparency before each binder,
up to a computation type `SPComp α`, a tree type or a type that is not a function type: `k`
receives the binders and the remaining type. A binder introduced by a type definition (an
adversary type `W → W → W → SPComp Bool` under its name) is a binder of the result. -/
partial def withTypeBinders {β : Type} (t : Expr) (k : Array Expr → Expr → TermElabM β) :
    TermElabM β :=
  go t #[]
where
  go (t : Expr) (acc : Array Expr) : TermElabM β := do
    if ← isSPCompType t then return ← k acc t
    if (← treeTy? t).isSome then return ← k acc t
    match ← whnf t with
    | .forallE n d b bi => withLocalDecl n bi d fun x => go (b.instantiate1 x) (acc.push x)
    | _ => k acc t

/-- The body of the definition value `v` applied to `args`: an argument that `keepsLet` keeps
is bound by a `let` around the body, any other argument is substituted. -/
partial def bindArgs (v : Expr) (args : Array Expr) (i : Nat) : MetaM Expr := do
  if h : i < args.size then
    match v with
    | .lam n ty b _ =>
      let a := args[i]
      if ← keepsLet (← inferType a) a then
        return .letE n ty a (← bindArgs b args (i + 1)) false
      bindArgs (b.instantiate1 a) args (i + 1)
    | _ => return mkAppN v (args.extract i args.size)
  else return v

/-- The base `b` of a projection `b.1`, `b.2` of a pair. -/
def pairProjBase? (e : Expr) : Option Expr :=
  match e with
  | .proj ``Prod _ b => some b
  | _ =>
    if e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 then some e.appArg!
    else none

/-- The calls `b` of which at least two projections `b.1`, `b.2` occur in `args`: applications
of a constant without loose bound variables whose type is a pair of first-order data. -/
def sharedPairBases (args : Array Expr) : MetaM (Array Expr) := do
  let mut seen : Array Expr := #[]
  let mut shared : Array Expr := #[]
  for a in args do
    let bs : Array Expr := Id.run do
      let mut acc := #[]
      let mut todo := #[a]
      while h : todo.size > 0 do
        let s := todo.back
        todo := todo.pop
        if let some b := pairProjBase? s then acc := acc.push b
        match s with
        | .app f x => todo := todo.push f |>.push x
        | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
        | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
        | .mdata _ b | .proj _ _ b => todo := todo.push b
        | _ => pure ()
      return acc
    for b in bs do
      unless b.isApp && b.getAppFn.isConst && !b.hasLooseBVars do continue
      if seen.contains b then
        unless shared.contains b do shared := shared.push b
      else seen := seen.push b
  shared.filterM fun b => do
    let t ← whnfR (← inferType b)
    unless t.isAppOfArity ``Prod 2 do return false
    for c in t.getAppArgs do
      if (← whnfR c).isForall then return false
    keepsLet t b

/-- The body of the definition value `v` applied to `args`, as `bindArgs` gives it, with each
call `b` of which two projections `b.1`, `b.2` occur among the arguments bound once by a `let`
around it. -/
def bindArgsShared (v : Expr) (args : Array Expr) : MetaM Expr := do
  let bases ← sharedPairBases args
  let rec go (i : Nat) (args : Array Expr) : MetaM Expr := do
    if h : i < bases.size then
      let b := bases[i]
      withLetDecl (Name.mkSimple s!"shared{i}") (← inferType b) b fun r => do
        let args := args.map fun a => a.replace fun s => if s == b then some r else none
        mkLetFVars #[r] (← go (i + 1) args)
    else
      return (← bindArgs v args 0).headBeta
  go 0 args

/-- The cost companion type `X → ℕ` of a function of type `X → Y`. -/
def companionType (t : Expr) : MetaM Expr := do
  forallTelescope (← whnfR t) fun ys _ => mkForallFVars ys (mkConst ``Nat)

/-- The costed type of a binder of type `t` and kind `k`. -/
def costedType (t : Expr) : MetaM Expr := do
  forallTelescope (← whnfR t) fun ys b => do
    let some T ← treeTy? b | throwError "derive_timed: `{b}` is not a tree of a registered kind"
    mkForallFVars ys T.timedType

/-- The step-prefixed costed tree `p`, whose results have type `src`, with each result `y`
replaced by `f y`, a result of the tree type `T`: `p` followed by `fun y => (0, ret (f y))`,
at no cost. It lifts the results of a tree binder holding functions to costed closures of
companion zero (`ι`), and erases costed results for a callee whose tree binder takes the
plain type (`ε`). -/
def mapResultE (T : TreeTy) (p src : Expr) (f : Expr → MetaM Expr) : MetaM Expr := do
  let some bindC := T.kind.combinators.find? (·.src == T.kind.tree ++ `bind)
    | throwError "derive_timed: internal: the {T.kind.noun} kind has no bind"
  let lam ← withLocalDeclD `y src fun y => do
    let leaf := mkAppN (mkConst T.kind.nodes[0]!.tgt) (T.params.push (← f y))
    mkLambdaFVars #[y] (T.mkPair (natE 0) leaf)
  let p1 ← if p.isAppOfArity ``Prod.mk 4 then pure (p.getArg! 2) else mkAppM ``Prod.fst #[p]
  let p2 ← if p.isAppOfArity ``Prod.mk 4 then pure (p.getArg! 3) else mkAppM ``Prod.snd #[p]
  return T.delayE p1 (← mkAppM bindC.tgt #[p2, lam])

/-- The costed tree `p` of a binder of the plain tree type `raw`, lifted to the tree type `T`
whose results hold costed closures (`ι`); `p` when the two agree. -/
def liftBinderE (T raw : TreeTy) (p : Expr) : MetaM Expr := do
  if (← hatTy? raw.result).isNone then return p
  mapResultE T p raw.result (iotaE raw.result)

/-- The step-prefixed costed tree `p` of tree type `T`, erased to the plain tree type `raw` of
a callee's tree binder (`ε`); `p` when the two agree. -/
def lowerArgE (T raw : TreeTy) (p : Expr) : MetaM Expr := do
  if (← hatTy? raw.result).isNone then return p
  mapResultE raw p T.result (epsE raw.result)

/-- The erasure of the costed value `v` of a local of type `t` and kind `k`. -/
def erasure (k : Kind) (t v : Expr) : MetaM Expr := do
  match k with
  | .tree =>
    let some T ← treeTy? t | throwError "derive_timed: `{t}` is not a tree of a registered kind"
    return T.eraseE v
  | .treeFn =>
    forallTelescope (← whnfR t) fun ys b => do
      let some T ← treeTy? b
        | throwError "derive_timed: `{b}` is not a tree of a registered kind"
      mkLambdaFVars ys (T.eraseE (mkAppN v ys))
  | .hat => epsE t v
  | _ => return v

/-- The costed tree of the tree binder `e`, when `e` is one. -/
def treeLocal? (ctx : Ctx) (e : Expr) : Option Expr :=
  match e.consumeMData with
  | .fvar id =>
    match ctx.locals.get? id with
    | some { kind := .tree, value, .. } => some value
    | _ => none
  | _ => none

/-- Fail with the reason a derivation does not go through. -/
def fail {β : Type} (what : MessageData) : MetaM β :=
  throwError m!"derive_timed: {what}"

/-- Bind the translated binders of the locals `xs` and continue with the context, the
binders of the costed form and the arguments of the original. -/
partial def withBinders {β : Type} (ctx : Ctx) (xs : Array Expr)
    (k : Ctx → Array Expr → Array Expr → TermElabM β) : TermElabM β :=
  go 0 ctx #[] #[]
where
  go (i : Nat) (ctx : Ctx) (bs args : Array Expr) : TermElabM β := do
    if h : i < xs.size then
      let x := xs[i]
      let t ← inferType x
      let n := (← x.fvarId!.getUserName).eraseMacroScopes
      match ← classify t with
      | .static | .data => go (i + 1) ctx (bs.push x) (args.push x)
      | .hat => do
        if ctx.plain then
          -- The plain interface: the binder keeps its plain value, its functions tables.
          let v ← iotaE t x
          return ← go (i + 1) { ctx with locals := ctx.locals.insert x.fvarId! ⟨.hat, v, none⟩ }
            (bs.push x) (args.push x)
        let some ht ← hatTy? t | fail m!"internal: `{t}` holds no function"
        withLocalDeclD n ht fun v => do
          let e ← epsE t v
          go (i + 1) { ctx with locals := ctx.locals.insert x.fvarId! ⟨.hat, v, none⟩,
                                hatSubst := ctx.hatSubst.push (x, e) }
            (bs.push v) (args.push e)
      | .fn => do
        let ct ← companionType t
        withLocalDeclD (n.appendAfter "Cost") ct fun c =>
          go (i + 1) { ctx with locals := ctx.locals.insert x.fvarId! ⟨.fn, x, some c⟩ }
            (bs.push x |>.push c) (args.push x)
      | .tree => do
        let vt ← costedType t
        withLocalDeclD n vt fun v => do
          go (i + 1) { ctx with locals := ctx.locals.insert x.fvarId! ⟨.tree, v, none⟩ }
            (bs.push v) (args.push (← erasure .tree t v))
      | .treeFn => do
        let vt ← costedType t
        let ct ← companionType t
        withLocalDeclD n vt fun v =>
          withLocalDeclD (n.appendAfter "Cost") ct fun c => do
            go (i + 1) { ctx with locals := ctx.locals.insert x.fvarId! ⟨.treeFn, v, some c⟩ }
              (bs.push v |>.push c) (args.push (← erasure .treeFn t v))
    else k ctx bs args

/-- The leading binders of `f` applied to `n` fresh locals, with its body beta-reduced. -/
def withEta {β : Type} (f : Expr) (n : Nat) (k : Array Expr → Expr → TermElabM β) :
    TermElabM β := do
  forallBoundedTelescope (← whnfR (← inferType f)) n fun ys _ => do
    unless ys.size == n do fail m!"`{f}` takes fewer than {n} arguments"
    k ys (mkAppN f ys).headBeta

/-- The kinds of the binders of the function `f` at the arguments `args`. -/
def argKinds (f : Expr) (args : Array Expr) : MetaM (Array (Kind × Expr)) := do
  let mut ty ← inferType f
  let mut out := #[]
  for a in args do
    let .forallE _ bt body _ ← whnf ty | fail m!"`{f}` is applied to too many arguments"
    out := out.push (← classify bt, bt)
    ty := body.instantiate1 a
  return out

/-- The trailing arguments of `e` to which `roles` apply. -/
def trailing (e : Expr) (args : Array Expr) (roles : Array ArgRole) : MetaM (Array Expr) := do
  unless roles.size ≤ args.size do
    fail m!"`{e}` is applied to fewer arguments than its translation takes"
  return args.extract (args.size - roles.size) args.size

/-- The applied fields in `e` of local structures and instances without a registered cost:
each a projection applied to its parameters and a local, and to further arguments, without
loose bound variables. -/
partial def fieldPrefixes (e : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match e with
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      let mut acc := acc
      if let .const m _ := f then
        if let some info ← getProjectionFnInfo? m then
          if h : info.numParams + 1 < args.size then
            let p := mkAppN f (args.extract 0 (info.numParams + 1))
            if args[info.numParams].consumeMData.isFVar && !p.hasLooseBVars &&
                !(← getEnv).contains (m ++ `timedCost) && !acc.contains p then
              acc := acc.push p
      acc ← go f acc
      for a in args do acc ← go a acc
      return acc
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t acc)
    | .letE _ t v b _ => go b (← go v (← go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ s => go s acc
    | _ => return acc
  go e #[]

/-- The name of the cost companion of the field key `p`: `fCost` for a field `S.f ps s`, and
`g_fCost` for a field of a computed structure `fun xs => S.f ps (g xs)`. -/
def fieldCostName (p : Expr) : MetaM Name := do
  let last (e : Expr) : MetaM (Option String) := do
    match e.getAppFn with
    | .const m _ => return some (m.updatePrefix .anonymous).toString
    | .fvar id => return some (← id.getUserName).eraseMacroScopes.toString
    | _ => return none
  if p.isLambda then
    return ← lambdaTelescope p fun _ b => do
      let some fl ← last b | return `fieldCost
      let some gl ← last b.appArg! | return Name.mkSimple (fl ++ "Cost")
      return Name.mkSimple (gl ++ "_" ++ fl ++ "Cost")
  match ← last p with
  | some fl => return Name.mkSimple (fl ++ "Cost")
  | none => return `fieldCost

/-- Bind a cost companion for each applied field of `ps` and continue with the pairs of the
field and its companion. -/
def withFieldCosts {β : Type} (ps : Array Expr) (k : Array (Expr × Expr) → TermElabM β) :
    TermElabM β :=
  go 0 #[]
where
  go (i : Nat) (acc : Array (Expr × Expr)) : TermElabM β := do
    if h : i < ps.size then
      let p := ps[i]
      let n ← fieldCostName p
      withLocalDeclD n (← companionType (← inferType p)) fun cc =>
        go (i + 1) (acc.push (p, cc))
    else k acc

/-- The applications `m ps inst` in `e` of a method `m` of `units` to its parameters and a
local instance `inst`, without loose bound variables. -/
partial def unitPrefixes (units : Array Name) (e : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match e with
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      let mut acc := acc
      if let .const m _ := f then
        if units.contains m then
          if let some info ← getProjectionFnInfo? m then
            if h : info.numParams < args.size then
              let p := mkAppN f (args.extract 0 (info.numParams + 1))
              if args[info.numParams].consumeMData.isFVar && !p.hasLooseBVars &&
                  !acc.contains p then
                acc := acc.push p
      acc ← go f acc
      for a in args do acc ← go a acc
      return acc
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t acc)
    | .letE _ t v b _ => go b (← go v (← go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ s => go s acc
    | _ => return acc
  go e #[]

/-- Whether `s` is a field path: a binder of the reduction, or a field of a structure-valued
field path (`kit`, `kit.hkdf`, `P.dh`). -/
partial def isFieldPath (ctx : Ctx) (s : Expr) : MetaM Bool := do
  match s.consumeMData with
  | .fvar id => return ctx.top.contains id
  | .proj _ _ s' => isFieldPath ctx s'
  | s' =>
    let .const m _ := s'.getAppFn | return false
    let some info ← getProjectionFnInfo? m | return false
    unless s'.getAppNumArgs == info.numParams + 1 do return false
    isFieldPath ctx s'.appArg!

/-- The key of a field `S.f ps (g b₁ … bₘ) …` of a computed structure, applied to the arguments
`args` of the projection `f` with `np` parameters: the structure is computed by a field path `g`
of a binder (`kit.aead`) or a local function with a cost companion, applied to data `bᵢ`. The
key is `fun x₁ … xₘ => S.f ps (g x₁ … xₘ)`, returned with `b₁ … bₘ`. -/
def computedFieldKey? (ctx : Ctx) (f : Expr) (np : Nat) (args : Array Expr) :
    MetaM (Option (Expr × Array Expr)) := do
  let some s := args[np]? | return none
  let s := s.consumeMData
  let ps := args.extract 0 np
  if ps.any (·.hasLooseBVars) then return none
  let sargs := s.getAppArgs
  let some (gp, bs) ← (match s.getAppFn with
      | g@(.fvar id) => do
        match ctx.locals.get? id with
        | some { kind := .fn, companion? := some _, .. } => pure (some (g, sargs))
        | _ => pure none
      | g@(.const m _) => do
        let some gi ← getProjectionFnInfo? m | pure none
        if gi.fromClass then pure none
        else if h : gi.numParams + 1 < sargs.size then
          let gp := mkAppN g (sargs.extract 0 (gi.numParams + 1))
          if !gp.hasLooseBVars && (← isFieldPath ctx sargs[gi.numParams]) then
            pure (some (gp, sargs.extract (gi.numParams + 1) sargs.size))
          else pure none
        else pure none
      | _ => pure none : MetaM (Option (Expr × Array Expr))) | return none
  if bs.isEmpty then return none
  forallBoundedTelescope (← whnfR (← inferType gp)) bs.size fun xs _ => do
    unless xs.size == bs.size do return none
    return some (← mkLambdaFVars xs (mkAppN f (ps.push (mkAppN gp xs))), bs)

mutual

/-- The cost of evaluating the data term `e`. -/
partial def costOf (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let e := e.consumeMData.headBeta
  -- A `let` applied to arguments, `(let x := v; f) a`: zeta- and beta-reduced, so that `v` is
  -- priced at each use.
  if let .letE _ _ v b _ := e.getAppFn.consumeMData then
    unless e.getAppArgs.isEmpty do
      return ← costOf ctx (mkAppN (b.instantiate1 v) e.getAppArgs).headBeta
  unless ← isDataExpr e do return natE 0
  match e with
  | .fvar _ | .lit _ | .lam .. | .forallE .. | .sort _ => return natE 0
  | .proj _ _ s => costOf ctx s
  | .letE n t v b _ =>
    unless ← keepsLet t v do return ← costOf ctx (b.instantiate1 v)
    -- The value is priced once; the body with a local of cost zero in its place.
    let cv ← costOf ctx v
    withLetDecl n t v fun x => do
      let cb ← costOf ctx (b.instantiate1 x)
      return add cv (cb.replaceFVar x v)
  | .const .. | .app .. => costApp ctx e
  | _ => fail m!"the data term `{e}` is not supported"

/-- The costs of the data arguments among `args`. -/
partial def argsCost (ctx : Ctx) (args : Array Expr) : TermElabM Expr := do
  let mut cs := #[]
  for a in args do
    if ← isDataExpr a then cs := cs.push (← costOf ctx a)
  return sum cs

/-- The cost of a condition: the costs of the data arguments of the proposition. -/
partial def propCost (ctx : Ctx) (p : Expr) : TermElabM Expr := do
  let p := p.consumeMData
  if p.isAppOf ``Not then return ← propCost ctx p.appArg!
  if p.isAppOf ``And || p.isAppOf ``Or then
    return add (← propCost ctx (p.getArg! 0)) (← propCost ctx (p.getArg! 1))
  argsCost ctx p.getAppArgs

/-- The cost companion of the function-valued argument `a`. -/
partial def companionOf (ctx : Ctx) (a : Expr) : TermElabM Expr := do
  if let .fvar id := a.consumeMData then
    if let some { companion? := some c, .. } := ctx.locals.get? id then return c
  let t ← whnfR (← inferType a)
  forallTelescope t fun ys _ => do
    mkLambdaFVars ys (← costOf ctx (mkAppN a ys).headBeta)

/-- The costed value of a path `e` into a costed value: a local of kind `hat` (its costed
value), a local function with a cost companion (the costed closure of the two), a projection
of a path, or an application of a costed closure whose result holds functions. -/
partial def hatOf? (ctx : Ctx) (e : Expr) : TermElabM (Option Expr) := do
  let e := e.consumeMData
  match e with
  | .fvar id =>
    match ctx.locals.get? id with
    | some { kind := .hat, value, .. } => return some value
    | some { kind := .fn, value, companion? := some c } =>
      return some (← mkAppM ``Prod.mk #[value, c])
    | _ => return none
  | .proj ``Prod i s =>
    let some v ← hatOf? ctx s | return none
    return some (← projE (i == 0) v)
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if (f.isConstOf ``Prod.fst || f.isConstOf ``Prod.snd) && args.size == 3 then
      let some v ← hatOf? ctx args[2]! | return none
      return some (← projE (f.isConstOf ``Prod.fst) v)
    let some (c, rest, _) ← closureHead? ctx e | return none
    return some (← closureApp ctx c rest).2
  | _ => return none

/-- The projection `v.1` (or `v.2`) of a pair, reduced on a literal pair. -/
partial def projE (fst : Bool) (v : Expr) : MetaM Expr := do
  if v.isAppOfArity ``Prod.mk 4 then return v.getArg! (if fst then 2 else 3)
  mkAppM (if fst then ``Prod.fst else ``Prod.snd) #[v]

/-- The costed closure at the head of the application `e`, with the arguments applied to it
and the path that computes it: a local of kind `hat` applied, or a projection of a path
applied. -/
partial def closureHead? (ctx : Ctx) (e : Expr) :
    TermElabM (Option (Expr × Array Expr × Expr)) := do
  let f := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if args.isEmpty then return none
  match f with
  | .fvar id =>
    match ctx.locals.get? id with
    | some { kind := .hat, value, .. } => return some (value, args, f)
    | _ => return none
  | .proj ``Prod _ _ =>
    let some c ← hatOf? ctx f | return none
    return some (c, args, f)
  | .const n _ =>
    unless (n == ``Prod.fst || n == ``Prod.snd) && args.size > 3 do return none
    let q := mkAppN f (args.extract 0 3)
    let some c ← hatOf? ctx q | return none
    return some (c, args.extract 3 args.size, q)
  | _ => return none

/-- The application of the costed closure `c` to `args`: its cost, one plus the companion
at the arguments plus the costs of the arguments for each saturated application, and the
costed value of the result. -/
partial def closureApp (ctx : Ctx) (c : Expr) (args : Array Expr) :
    TermElabM (Expr × Expr) := do
  let mut cur := c
  let mut rest := args
  let mut cost := natE 0
  while !rest.isEmpty do
    let ct ← whnfR (← inferType cur)
    unless ct.isAppOfArity ``Prod 2 do
      fail m!"the costed closure `{cur}` is applied to more arguments than it takes"
    let k ← forallTelescope (← whnfR (ct.getArg! 1)) fun ys _ => pure ys.size
    unless k ≤ rest.size do
      fail m!"a costed closure is applied to {rest.size} arguments in a partial application"
    let now := rest.extract 0 k
    let comp := (mkAppN (← projE false cur) now).headBeta
    cost := add cost (add (natE 1) (add comp (← argsCost ctx now)))
    cur := (mkAppN (← projE true cur) now).headBeta
    rest := rest.extract k rest.size
  return (cost, cur)

/-- The cost and the costed value (`hatTy?`) of the data term `e`; for a term whose type
holds no function, its cost and `e`. A closure costs nothing to build and its companion is
the cost of its body; a partial application of a constant evaluates its arguments when it is
built; a pair, an `if` and a call of a definition are translated componentwise, by branch and
by unfolding. -/
partial def tv (ctx : Ctx) (e : Expr) : TermElabM (Expr × Expr) := do
  let e := e.consumeMData.headBeta
  let t ← inferType e
  let some ht ← hatTy? t | return (← costOf ctx e, e)
  if let some v ← hatOf? ctx e then return (← costOf ctx e, v)
  let tw ← whnfR t
  match e with
  | .letE n lt v b _ =>
    unless ← keepsLet lt v do return ← tv ctx (b.instantiate1 v)
    let cv ← costOf ctx v
    withLetDecl n lt v fun x => do
      let (cb, vb) ← tv ctx (b.instantiate1 x)
      return (add cv (cb.replaceFVar x v), vb.replaceFVar x v)
  | .lam .. =>
    let n ← forallTelescope tw fun ys _ => pure ys.size
    withEta e n fun ys b => do
      let (cb, vb) ← tv ctx b
      return (natE 0, ← mkAppM ``Prod.mk #[← mkLambdaFVars ys vb, ← mkLambdaFVars ys cb])
  | .app .. | .const .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.isConstOf ``Prod.mk && args.size == 4 then
      let (ca, va) ← tv ctx args[2]!
      let (cb, vb) ← tv ctx args[3]!
      return (add ca cb, ← mkAppM ``Prod.mk #[va, vb])
    if f.isConstOf ``ite && args.size == 5 then
      let (ca, va) ← tv ctx args[3]!
      let (cb, vb) ← tv ctx args[4]!
      let lvl ← getLevel ht
      return (add (natE 1) (add (← propCost ctx args[1]!)
          (mkApp5 (mkConst ``ite [Level.one]) (mkConst ``Nat) args[1]! args[2]! ca cb)),
        mkApp5 (mkConst ``ite [lvl]) ht args[1]! args[2]! va vb)
    if tw.isForall then
      -- A partial application of a constant or of a local function with a cost companion:
      -- the arguments are evaluated when the closure is built; the companion prices the call
      -- with them as values. A partial application of any other local function is a table,
      -- applied at unit cost.
      -- Functions in the closure's results are tables (`ι`).
      let cargs ← argsCost ctx args
      let val ← forallTelescope tw fun ys body => do
        if (← hatTy? body).isNone then return e
        mkLambdaFVars ys (← iotaE body (mkAppN e ys))
      match f with
      | .const _ _ => pure ()
      | .fvar id =>
        match ctx.locals.get? id with
        | some { kind := .fn, companion? := some _, .. } => pure ()
        | _ =>
          let z ← forallTelescope tw fun ys _ => mkLambdaFVars ys (natE 0)
          return (cargs, ← mkAppM ``Prod.mk #[val, z])
      | _ => fail m!"a function bound in data: the closure `{e}` is not a partial application \
          of a constant or a local function"
      let comp ← partialAppCompanion ctx e tw f args 0 #[] #[]
      return (cargs, ← mkAppM ``Prod.mk #[val, comp])
    let .const c lvls := f | fail m!"a function bound in data: the value `{e}` of type `{t}` \
      has no costed form"
    let env ← getEnv
    let some (.defnInfo dv) := env.find? c | fail m!"a function bound in data: the value `{e}` \
      of type `{t}` is not a definition to unfold"
    if (Structural.eqnInfoExt.find? env c).isSome || (WF.eqnInfoExt.find? env c).isSome then
      fail m!"a function bound in data: the recursive `{c}` returns functions"
    if ctx.depth ≥ (← maxDepth) then
      fail m!"needs a registered primitive: `{c}` unfolds too deep"
    unless lvls.length == dv.levelParams.length do fail m!"`{c}` does not unfold"
    let e' ← bindArgsShared (dv.value.instantiateLevelParams dv.levelParams lvls) args
    let (cb, vb) ← tv { ctx with depth := ctx.depth + 1 } e'
    let callCost := if ← isReducible c then natE 0 else natE 1
    return (add callCost cb, vb)
  | _ => fail m!"a function bound in data: the value `{e}` of type `{t}` has no costed form"

/-- The companion of the closure `e = f args` of type `tw`: the cost of `f args ys` at fresh
arguments `ys`, with each data argument that is not a variable, a literal or a closure
standing for its value at no cost. -/
partial def partialAppCompanion (ctx : Ctx) (e tw f : Expr) (args : Array Expr) (i : Nat)
    (vals : Array Expr) (zs : Array (Expr × Expr)) : TermElabM Expr := do
  if h : i < args.size then
    let a := args[i]
    if (← isDataExpr a) && (← keepsLet (← inferType a) a) then
      withLocalDeclD `v (← inferType a) fun z =>
        partialAppCompanion ctx e tw f args (i + 1) (vals.push z) (zs.push (z, a))
    else partialAppCompanion ctx e tw f args (i + 1) (vals.push a) zs
  else
    let c ← forallTelescope tw fun ys _ => do
      mkLambdaFVars ys (← costOf ctx (mkAppN (mkAppN f vals) ys))
    return c.replaceFVars (zs.map (·.1)) (zs.map (·.2))

/-- The arguments of a registered cost: each function-typed argument followed by its cost
companion. -/
partial def costArgs (ctx : Ctx) (f : Expr) (args : Array Expr) : TermElabM (Array Expr) := do
  let kinds ← argKinds f args
  let mut out := #[]
  for a in args, (k, _) in kinds do
    out := out.push a
    if k == .fn || k == .treeFn then out := out.push (← companionOf ctx a)
  return out

/-- The cost of the application `e` of a constant or a local. -/
partial def costApp (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let f := e.getAppFn
  let args := e.getAppArgs
  -- An application of a costed closure held in data.
  if let some (c, rest, hd) ← closureHead? ctx e then
    return add (← costOf ctx hd) (← closureApp ctx c rest).1
  match f with
  | .fvar id =>
    match ctx.locals.get? id with
    | some { kind := .fn, companion? := some c, .. } =>
      let arity ← forallTelescope (← whnfR (← inferType c)) fun ys _ => pure ys.size
      if args.size < arity then argsCost ctx args
      else if args.size == arity then
        return add (natE 1) (add (mkAppN c args) (← argsCost ctx args))
      else fail m!"the local function `{f}` is applied to more arguments than its companion takes"
    | some _ => fail m!"the oracle tree `{f}` occurs in a data position in `{e}`"
    | none =>
      if args.isEmpty then return natE 0
      fail m!"a function bound in data: the local `{f}` in `{e}` has no cost companion"
  | .const c _ => costConst ctx e c args
  | .proj S i s =>
    -- A field of a structure applied: priced as its projection function.
    let some info := getStructureInfo? (← getEnv) S
      | fail m!"the application `{e}` is headed by a projection of a non-structure"
    let some field := info.fieldNames[i]? | fail m!"the projection `{f}` has no field {i}"
    let pf ← mkAppM (S ++ field) #[s]
    costConst ctx (mkAppN pf args) (S ++ field) (pf.getAppArgs ++ args)
  | _ => fail m!"the application `{e}` is not headed by a constant or a local"

/-- The cost of an application of the constant `c`. -/
partial def costConst (ctx : Ctx) (e : Expr) (c : Name) (args : Array Expr) :
    TermElabM Expr := do
  let env ← getEnv
  let f := e.getAppFn
  if let some (.ctorInfo ci) := env.find? c then
    -- The parameters of the inductive type are not arguments of the call.
    return ← argsCost ctx (args.extract ci.numParams args.size)
  if freeConstants.contains c then
    return ← argsCost ctx args
  -- A partial application is a closure.
  let arity ← forallTelescope (← inferType f) fun ys _ => pure ys.size
  if args.size < arity then return ← argsCost ctx args
  if isCasesOnRecursor env c then
    return ← costCases ctx e c args
  -- A registered cost.
  let reg := c ++ `timedCost
  if let some (s, sc) := ctx.selfCost? then
    if s == c then
      return add (natE 1) (add (mkAppN sc (← costArgs ctx f args)) (← argsCost ctx args))
  if env.contains reg then
    let regArgs ← costArgs ctx f args
    let regE ← mkAppOptM reg (regArgs.map some)
    -- A derived cost that takes the cost companions of field paths of `c`'s binders: the
    -- caller passes its companions for the same paths at the arguments of the call.
    let extra ← forallTelescope (← inferType regE) fun ys _ => pure ys.size
    let mut fieldArgs := #[]
    if extra > 0 then
      for p in ← calleeFieldPaths c f.constLevels! args do
        if let some (_, cc) := ctx.fields.find? (·.1 == p) then
          fieldArgs := fieldArgs.push cc
        else if let some r := ctx.fieldRec? then
          if !p.hasLooseBVars && (p.isLambda || (← isFieldPath ctx p.appArg!)) then
            unless (← r.get).contains p do r.modify (·.push p)
          return add (natE 1) (← argsCost ctx args)
        else
          fail m!"the cost `{reg}` takes the cost of the field `{p}`, which is not a field of a \
            binder of the reduction"
      unless fieldArgs.size == extra do
        fail m!"the cost `{reg}` takes {extra} field costs at `{e}`, and {fieldArgs.size} were \
          found"
    return add (natE 1) (add (mkAppN regE fieldArgs) (← argsCost ctx args))
  if natUnitOps.contains c && args.size > 0 && (args[0]!).isConstOf ``Nat then
    return add (natE 1) (← argsCost ctx args)
  -- Arithmetic modulo `p`: one unit, a word operation for the fixed modulus.
  -- The test of the type is nested, so that `args[0]` is read only when it exists (a `←`
  -- inside a condition is run before the condition).
  if zmodUnitOps.contains c then
    if h : 0 < args.size then
      if (← whnfR args[0]).isAppOfArity `ZMod 1 then
        return add (natE 1) (← argsCost ctx args)
  -- Operations on fixed-width words: one unit.
  if wordUnitOps.contains c then
    if h : 0 < args.size then
      if ← isWordType args[0] then
        return add (natE 1) (← argsCost ctx args)
  -- A comparison of words decided at one unit: `decide (a < b)` is priced by the rule for
  -- `Decidable.decide` below.
  if c == ``Decidable.decide && args.size == 2 then
    return add (natE 1) (← propCost ctx args[0]!)
  if c == ``ite && args.size == 5 then
    return add (natE 1) (add (← propCost ctx args[1]!)
      (mkApp5 (mkConst ``ite [Level.one]) (mkConst ``Nat) args[1]! args[2]!
        (← costOf ctx args[3]!) (← costOf ctx args[4]!)))
  if c == ``dite && args.size == 5 then
    let ct ← withEta args[3]! 1 fun hs b => do mkLambdaFVars hs (← costOf ctx b)
    let ce ← withEta args[4]! 1 fun hs b => do mkLambdaFVars hs (← costOf ctx b)
    return add (natE 1) (add (← propCost ctx args[1]!)
      (mkApp5 (mkConst ``dite [Level.one]) (mkConst ``Nat) args[1]! args[2]! ct ce))
  if ← isMatcher c then
    return ← costMatch ctx e
  -- A structure projection.
  if let some info ← getProjectionFnInfo? c then
    -- A method of an abstract algebraic structure, an instance built from a local instance:
    -- one call of the interface, one unit.
    if info.fromClass && isUnitMethod c && args.size > info.numParams then
      if ← builtFromLocalInstance args[info.numParams]! then
        return add (natE 1) (← argsCost ctx (args.extract (info.numParams + 1) args.size))
    -- A field of a local structure or instance with a cost companion.
    if args.size > info.numParams + 1 then
      let p := mkAppN f (args.extract 0 (info.numParams + 1))
      let rest := args.extract (info.numParams + 1) args.size
      if let some (_, cc) := ctx.fields.find? (·.1 == p) then
        let arity ← forallTelescope (← whnfR (← inferType cc)) fun ys _ => pure ys.size
        unless rest.size == arity do
          fail m!"the field `{c}` is applied to {rest.size} arguments in `{e}`, and its cost \
            companion takes {arity}"
        return add (natE 1) (add (mkAppN cc rest) (← argsCost ctx rest))
      -- The first pass records the field paths that start at a binder of the reduction.
      if let some r := ctx.fieldRec? then
        if !p.hasLooseBVars && (← isFieldPath ctx args[info.numParams]!) then
          unless (← r.get).contains p do r.modify (·.push p)
          return add (natE 1) (← argsCost ctx rest)
      -- A field of a computed structure `g b₁ … bₘ`: the structure is priced by the rules
      -- above, the field by a companion indexed by `b₁ … bₘ` and the arguments of the field.
      if !info.fromClass then
        if let some (key, bs) ← computedFieldKey? ctx f info.numParams args then
          let s := args[info.numParams]!
          if let some (_, cc) := ctx.fields.find? (·.1 == key) then
            return add (natE 1) (add (mkAppN cc (bs ++ rest))
              (add (← costOf ctx s) (← argsCost ctx rest)))
          if let some r := ctx.fieldRec? then
            unless (← r.get).contains key do r.modify (·.push key)
            return add (natE 1) (add (← costOf ctx s) (← argsCost ctx rest))
    if info.fromClass then
      let inst := args[info.numParams]!
      -- A method of an abstract algebraic structure (an instance built from a local
      -- hypothesis) without a cost companion: a call of the abstract interface, at one unit.
      if inst.consumeMData.isFVar then
        return add (natE 1) (← argsCost ctx (args.extract (info.numParams + 1) args.size))
      let some e' ← unfoldProjInst? e
        | if inst.hasFVar then
            return add (natE 1) (← argsCost ctx (args.extract (info.numParams + 1) args.size))
          fail m!"needs a registered primitive: the class method `{c}` does not unfold"
      if ctx.depth ≥ (← maxDepth) then
        fail m!"needs a registered primitive: `{c}` unfolds too deep"
      return ← costOf { ctx with depth := ctx.depth + 1 } e'
    if args.size > info.numParams + 1 then
      fail m!"a function bound in data: the field `{c}` is applied in `{e}`"
    return ← argsCost ctx args
  -- A definition, unfolded.
  let some info := env.find? c | fail m!"unknown constant `{c}`"
  if (Structural.eqnInfoExt.find? env c).isSome || (WF.eqnInfoExt.find? env c).isSome then
    -- A recursive data function: its cost is derived by its recursion, then the call is priced
    -- by it.
    try
      deriveCostCore #[] c
    catch ex =>
      fail m!"needs a registered primitive: `{c}` is recursive and has no registered cost \
        `{reg}`, and `derive_cost {c}` fails:{indentD ex.toMessageData}"
    return ← costConst ctx e c args
  let .defnInfo dv := info
    | fail m!"needs a registered primitive: `{c}` has no definition to price and no registered \
        cost `{reg}`"
  let depthLimit ← maxDepth
  if ctx.depth ≥ depthLimit then
    fail m!"needs a registered primitive: `{c}` unfolds deeper than {depthLimit} definitions \
      (option `derive_timed.maxDepth`)"
  -- The arguments are bound by `let`s around the body, so that each is priced once.
  let lvls := f.constLevels!
  unless lvls.length == dv.levelParams.length do
    fail m!"needs a registered primitive: `{c}` does not unfold"
  let e' ← bindArgsShared (dv.value.instantiateLevelParams dv.levelParams lvls) args
  if (e'.find? fun s => s.isConstOf ``WellFounded.fix || s.isAppOf ``Nat.rec
      || s.isAppOf ``List.rec).isSome then
    fail m!"needs a registered primitive: `{c}` unfolds to a recursor"
  -- An abbreviation is notation: unfolded without the cost of a call.
  let callCost := if ← isReducible c then natE 0 else natE 1
  return add callCost (← costOf { ctx with depth := ctx.depth + 1 } e')

/-- The cost of a data-valued `casesOn` of an inductive type without indices: one, the major
premise, and the branch taken. -/
partial def costCases (ctx : Ctx) (e : Expr) (c : Name) (args : Array Expr) :
    TermElabM Expr := do
  let some (.inductInfo iv) := (← getEnv).find? c.getPrefix
    | fail m!"`{c}` is not the case analysis of an inductive type"
  unless iv.numIndices == 0 do fail m!"the case analysis `{e}` is over an indexed family"
  let arity := iv.numParams + 2 + iv.numCtors
  unless args.size == arity do
    fail m!"the case analysis `{e}` has a motive that depends on further arguments"
  let major := args[iv.numParams + 1]!
  let motive ← withLocalDeclD `x (← inferType major) fun x => mkLambdaFVars #[x] (mkConst ``Nat)
  let mut minors := #[]
  for i in [0:iv.numCtors] do
    let ctor ← getConstInfoCtor iv.ctors[i]!
    let minor := args[iv.numParams + 2 + i]!
    minors := minors.push (← withEta minor ctor.numFields fun fs b => do
      mkLambdaFVars fs (← costOf ctx b))
  let levels := match e.getAppFn.constLevels! with
    | _ :: ls => Level.one :: ls
    | [] => []
  let cases := mkAppN (mkConst c levels)
    (args[0:iv.numParams].toArray ++ #[motive, major] ++ minors)
  return add (natE 1) (add (← costOf ctx major) cases)

/-- The matcher application `e` with its discriminants and alternatives prepared for a
translation with result type `resultType`: the translated discriminants replaced by their
erasures, and each alternative translated by `alt` in the context in which its fields stand
for the translated discriminants they bind. Returns the new application and the cost of the
data discriminants. -/
partial def mapMatch (ctx : Ctx) (e resultType : Expr)
    (alt : Ctx → Expr → TermElabM Expr) : TermElabM (Expr × Expr) := do
  let some app ← matchMatcherApp? e | fail m!"`{e}` is not a matcher application"
  unless app.remaining.isEmpty do
    fail m!"the match `{e}` has a motive that depends on its discriminants"
  let mut discrs := #[]
  let mut trDiscrs : Array (Expr × LocalInfo) := #[]
  let mut cost := natE 0
  for d in app.discrs do
    if let some Td ← treeTy? (← inferType d) then
      fail m!"a recursion over an {Td.kind.noun}: a match on the {Td.kind.noun} `{d}`; register \
        a costed form written by hand"
    match d.consumeMData with
    | .fvar id =>
      match ctx.locals.get? id with
      | some info =>
        let dt ← inferType d
        if info.kind == .fn then discrs := discrs.push d
        else discrs := discrs.push (← erasure info.kind dt info.value)
        trDiscrs := trDiscrs.push (dt, info)
      | none => discrs := discrs.push d
    | _ =>
      discrs := discrs.push d
      cost := add cost (← costOf ctx d)
      -- A function passed as a discriminant (`Option.bind o f` matches on `f`): the field
      -- that binds it is a local function with the companion of the function.
      let dt ← inferType d
      if (← isDataExpr d) && (← whnfR dt).isForall && (← treeTy? dt).isNone then
        trDiscrs := trDiscrs.push (dt, ⟨.fn, d, some (← companionOf ctx d)⟩)
  let motive ← lambdaTelescope app.motive fun xs _ => mkLambdaFVars xs resultType
  let lvl ← getLevel resultType
  let levels := match app.uElimPos? with
    | some i => app.matcherLevels.set! i lvl
    | none => app.matcherLevels
  let matcherType ← instantiateForall
    (← inferType (mkConst app.matcherName levels.toList)) (app.params ++ #[motive] ++ discrs)
  let mut alts := #[]
  let mut ty := matcherType
  for a in app.alts do
    let .forallE _ aty body _ ← whnf ty | fail m!"the match `{e}` has an unexpected type"
    let n ← forallTelescope aty fun ys _ => pure ys.size
    let a' ← lambdaBoundedTelescope a n fun fs b => do
      let mut ctx' := ctx
      for fv in fs do
        let ft ← inferType fv
        let mut found : Option LocalInfo := none
        for (dt, info) in trDiscrs do
          if ← isDefEq ft dt then
            if found.isSome then
              fail m!"the match `{e}` binds two translated discriminants of type `{ft}`"
            found := some info
        if let some info := found then
          ctx' := { ctx' with locals := ctx'.locals.insert fv.fvarId! info }
      mkLambdaFVars fs (← alt ctx' b)
    alts := alts.push a'
    ty := body.instantiate1 a'
  let e' := mkAppN (mkConst app.matcherName levels.toList)
    (app.params ++ #[motive] ++ discrs ++ alts)
  return (e', cost)

/-- The cost of a data-valued match: one, the discriminants, and the branch taken. -/
partial def costMatch (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let (e', cd) ← mapMatch ctx e (mkConst ``Nat) costOf
  return add (natE 1) (add cd e')

/-- The translation of the oracle tree `e`: a step-prefixed costed tree whose erasure is `e`
with the translated locals erased. -/
partial def tr (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let e := e.consumeMData.headBeta
  -- A `let` applied to arguments, `(let x := v; f) a`: zeta- and beta-reduced, so that `v` is
  -- priced at each use.
  if let .letE _ _ v b _ := e.getAppFn.consumeMData then
    unless e.getAppArgs.isEmpty do
      return ← tr ctx (mkAppN (b.instantiate1 v) e.getAppArgs).headBeta
  let some T ← treeTyH? (← inferType e)
    | fail m!"`{e}` is not a tree of a registered kind"
  match e with
  | .letE n t v b _ =>
    unless ← keepsLet t v do return ← tr ctx (b.instantiate1 v)
    -- The value is priced once, in front; the costed tree keeps the `let`.
    let cv ← costOf ctx v
    withLetDecl n t v fun x => do
      let p ← tr ctx (b.instantiate1 x)
      let body := (T.sndOf p).abstract #[x]
      return T.mkPair (add cv ((T.fstOf p).replaceFVar x v)) (.letE n t v body false)
  | .fvar id =>
    match ctx.locals.get? id with
    | some { kind := .tree, value, .. } =>
      let some raw ← treeTy? (← inferType e) | fail m!"`{e}` is not a tree"
      liftBinderE T raw (raw.mkPair (natE 0) value)
    | _ => fail m!"a function bound in data: the {T.kind.noun} `{e}` has no costed form"
  | .app .. | .const .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .fvar id =>
      match ctx.locals.get? id with
      | some { kind := .treeFn, value, companion? := some c } =>
        let some raw ← treeTy? (← inferType e) | fail m!"`{e}` is not a tree"
        liftBinderE T raw (raw.mkPair (add (natE 1) (add (mkAppN c args) (← argsCost ctx args)))
          (mkAppN value args))
      | _ => fail m!"a function bound in data: the local `{f}` in `{e}` has no costed form"
    | .const c _ => trConst ctx e c args T
    | .proj S i s =>
      -- A field of a structure applied: translated as its projection function.
      let some sinfo := getStructureInfo? (← getEnv) S
        | fail m!"the {T.kind.noun} `{e}` is headed by a projection of a non-structure"
      let some field := sinfo.fieldNames[i]? | fail m!"the projection `{f}` has no field {i}"
      let pf ← mkAppM (S ++ field) #[s]
      tr ctx (mkAppN pf args)
    | _ => fail m!"the {T.kind.noun} `{e}` is not headed by a constant or a local"
  | _ => fail m!"the {T.kind.noun} `{e}` is not supported"

/-- The translation of a continuation `a` with `n` binders: its step cost and its costed tree,
both abstracted over the binders. -/
partial def trCont (ctx : Ctx) (a : Expr) (n : Nat) : TermElabM (Expr × Expr) := do
  if n == 0 then
    let some Ta ← treeTyH? (← inferType a) | fail m!"`{a}` is not a tree of a registered kind"
    let p ← tr ctx a
    return (Ta.fstOf p, Ta.sndOf p)
  withEta a n fun ys b => do
    let some Tb ← treeTyH? (← inferType b) | fail m!"`{b}` is not a tree of a registered kind"
    -- A sampled or received value holding functions: each function is a table, applied at
    -- unit cost (`ι`).
    let mut ctx := ctx
    for y in ys do
      let yt ← inferType y
      if (← hatTy? yt).isSome then
        ctx := { ctx with locals := ctx.locals.insert y.fvarId! ⟨.hat, ← iotaE yt y, none⟩ }
    let p ← tr ctx b
    return (← mkLambdaFVars ys (Tb.fstOf p), ← mkLambdaFVars ys (Tb.sndOf p))

/-- The translation of a function `a` of `m` arguments into trees, whose arguments are results
of costed trees: a binder holding functions stands for its costed value `x̂`, and `ε x̂` for
the binder in the costed tree. -/
partial def trPairFn (ctx : Ctx) (a : Expr) (m : Nat) : TermElabM Expr :=
  withEta a m fun ys b => do
    let rec go (i : Nat) (ctx : Ctx) (bs : Array Expr) (subst : Array (Expr × Expr)) :
        TermElabM Expr := do
      if h : i < ys.size then
        let y := ys[i]
        let yt ← inferType y
        match ← hatTy? yt with
        | some ht =>
          withLocalDeclD (← y.fvarId!.getUserName) ht fun v => do
            go (i + 1) { ctx with locals := ctx.locals.insert y.fvarId! ⟨.hat, v, none⟩ }
              (bs.push v) (subst.push (y, ← epsE yt v))
        | none => go (i + 1) ctx (bs.push y) subst
      else
        let p ← tr ctx b
        mkLambdaFVars bs (p.replaceFVars (subst.map (·.1)) (subst.map (·.2)))
    go 0 ctx #[] #[]

/-- The translation of a node: the costed constructor applied to the translated arguments, with
the costs of the data arguments as its step cost. The continuations are translated first. -/
partial def trNode (ctx : Ctx) (e : Expr) (nd : Node) (args : Array Expr) (T : TreeTy) :
    TermElabM Expr := do
  let xs ← trailing e args nd.roles
  let mut conts : Array (Option (Expr × Expr)) := Array.replicate xs.size none
  for h : i in [0:xs.size] do
    if let .cont m := nd.roles[i]! then
      conts := conts.set! i (some (← trCont ctx xs[i] m))
  let mut outs := #[]
  let mut cost := natE 0
  for h : i in [0:xs.size] do
    match nd.roles[i]!, conts[i]! with
    | .cont _, some (cs, ks) => outs := outs.push cs |>.push ks
    | .data, _ =>
      let (c, v) ← tv ctx xs[i]
      outs := outs.push v
      cost := add cost c
    | _, _ => outs := outs.push xs[i]
  let node ← mkAppM' (mkAppN (mkConst nd.tgt) T.params) outs
  return T.mkPair cost node

/-- The translation of a combinator: its costed form applied to the translated arguments, with
the step costs of the tree arguments and the costs of the data arguments in front. The tree
arguments are translated first. -/
partial def trComb (ctx : Ctx) (e : Expr) (cb : Comb) (args : Array Expr) (T : TreeTy) :
    TermElabM Expr := do
  let xs ← trailing e args cb.roles
  let mut trees : Array Expr := Array.replicate xs.size (natE 0)
  let mut treeCost := natE 0
  for h : i in [0:xs.size] do
    if cb.roles[i]! == .tree then
      let some Ta ← treeTyH? (← inferType xs[i]) | fail m!"`{e}` has an unexpected type"
      let p ← tr ctx xs[i]
      trees := trees.set! i (Ta.sndOf p)
      treeCost := add treeCost (Ta.fstOf p)
  let mut outs := #[]
  let mut dataCost := natE 0
  for h : i in [0:xs.size] do
    let a := xs[i]
    match cb.roles[i]! with
    | .tree => outs := outs.push trees[i]!
    | .pairFn m => outs := outs.push (← trPairFn ctx a m)
    | .perCall extra m =>
      if (← hatTy? (← inferType e)).isSome ||
          (← xs.anyM fun x => do
            match ← treeTy? (← inferType x) with
            | some Tx => return (← hatTy? Tx.result).isSome
            | none => return false) then
        fail m!"a function bound in data: the result of a tree in `{e}` holds functions"
      let t ← withEta a m fun ys b => do mkLambdaFVars ys (add (natE extra) (← costOf ctx b))
      outs := outs.push a |>.push t
    | .data =>
      let (c, v) ← tv ctx a
      outs := outs.push v
      dataCost := add dataCost c
    | .keep | .cont _ => outs := outs.push a
  -- A simulation whose state holds functions: its costed form carries the erasure and the
  -- lift of the state, which state its erasure theorem.
  if cb.src == ``CatCrypt.Crypto.OracleAdv.simulate then
    let st ← inferType xs[xs.size - 1]!
    if (← hatTy? st).isSome then
      let r ← mkAppM ``CatCrypt.Crypto.OracleAdv.Timed.simulateHat
        (#[← epsFun st, ← iotaFun st] ++ outs)
      return T.delayE (add treeCost dataCost) r
  let r ← mkAppM cb.tgt outs
  let r := if cb.pair then r else T.mkPair (natE 0) r
  return T.delayE (add treeCost dataCost) r

/-- The translation of a tree headed by the constant `c`. -/
partial def trConst (ctx : Ctx) (e : Expr) (c : Name) (args : Array Expr) (T : TreeTy) :
    TermElabM Expr := do
  let n := args.size
  if let some nd := T.kind.nodes.find? (·.src == c) then
    return ← trNode ctx e nd args T
  if let some cb := T.kind.combinators.find? (·.src == c) then
    return ← trComb ctx e cb args T
  if c == ``ite && n == 5 then
    let pt ← tr ctx args[3]!
    let pe ← tr ctx args[4]!
    let i := mkApp5 (mkConst ``ite [Level.succ Level.one]) T.pairType args[1]! args[2]! pt pe
    return T.delayE (add (natE 1) (← propCost ctx args[1]!)) i
  if c == ``dite && n == 5 then
    let pt ← withEta args[3]! 1 fun hs b => do mkLambdaFVars hs (← tr ctx b)
    let pe ← withEta args[4]! 1 fun hs b => do mkLambdaFVars hs (← tr ctx b)
    let i := mkApp5 (mkConst ``dite [Level.succ Level.one]) T.pairType args[1]! args[2]! pt pe
    return T.delayE (add (natE 1) (← propCost ctx args[1]!)) i
  if ← isMatcher c then
    -- A match on an oracle-tree binder is translated as its case analysis.
    if let some app ← matchMatcherApp? e then
      if app.discrs.any fun d => (treeLocal? ctx d).isSome then
        let some e' ← delta? e | fail m!"the match `{e}` does not unfold"
        return ← tr ctx (← Core.betaReduce e')
    let (e', cd) ← mapMatch ctx e T.pairType tr
    return T.delayE (add (natE 1) cd) e'
  if c == ``CatCrypt.Crypto.OracleAdv.casesOn then
    return ← trTreeCases ctx e args T
  -- A tree-valued field of a field path (`S.kem.encaps pk`, a program of a scheme structure):
  -- a primitive, whose oracle tree runs at the unit cost of its nodes and whose computation
  -- is priced by its cost companion, indexed by the arguments of the field.
  if let some info ← getProjectionFnInfo? c then
    if !info.fromClass && args.size > info.numParams &&
        T.kind.tree == ``CatCrypt.Crypto.OracleAdv then
      let p := mkAppN e.getAppFn (args.extract 0 (info.numParams + 1))
      let rest := args.extract (info.numParams + 1) args.size
      if !p.hasLooseBVars && (← isFieldPath ctx args[info.numParams]!) then
        let leaf ← mkAppM ``CatCrypt.Crypto.OracleAdv.Timed.ofAdv #[e]
        if let some (_, cc) := ctx.fields.find? (·.1 == p) then
          return T.mkPair (add (natE 1) (add (mkAppN cc rest) (← argsCost ctx rest))) leaf
        if let some r := ctx.fieldRec? then
          unless (← r.get).contains p do r.modify (·.push p)
          return T.mkPair (add (natE 1) (← argsCost ctx rest)) leaf
  -- A call of a reduction.
  let target ← match ctx.self? with
    | some (self, rec) => if self == c then pure rec else ensureTimed ctx c e.getAppFn
    | none => ensureTimed ctx c e.getAppFn
  callTimed ctx e target args T

/-- The case analysis `OracleAdv.casesOn A ret rand query` of an oracle-tree binder `A` with
costed form `A'`, translated as the case analysis `OracleAdv.Timed.casesOn A'` of the costed
tree (a handler of the nodes of `A`, `T.Timed` having the constructors of `T`): the
continuation `k` of a `rand` or `query` node of `A` stands for the continuation `k'` of the
costed node, with the node's step cost `c` as its cost companion. The case analysis costs one.
A recursive call on `k x` is a recursive call on `k' x`, so a reduction defined by structural
recursion on `A` gets a costed form defined by structural recursion on `A'`. -/
partial def trTreeCases (ctx : Ctx) (e : Expr) (args : Array Expr) (T : TreeTy) :
    TermElabM Expr := do
  unless args.size == 8 do
    fail m!"the case analysis `{e}` has a motive that depends on further arguments"
  let major := args[4]!
  let some A' := treeLocal? ctx major
    | fail m!"a case analysis of the oracle tree `{major}`, which is not a binder"
  let some Tm ← treeTy? (← inferType major) | fail m!"`{major}` is not an oracle tree"
  let motive ← withLocalDeclD `x Tm.timedType fun x => mkLambdaFVars #[x] T.pairType
  let cases := mkAppN (mkConst ``CatCrypt.Crypto.OracleAdv.Timed.casesOn [← getLevel T.pairType])
    (Tm.params ++ #[motive, A'])
  let minorTys ← forallBoundedTelescope (← inferType cases) (some 3) fun ms _ =>
    ms.mapM fun m => inferType m
  unless minorTys.size == 3 do fail m!"internal: unexpected type of `{cases}`"
  -- The `ret` alternative.
  let altRet ← withEta args[5]! 1 fun ys b => do
    mkLambdaFVars ys (T.delayE (natE 1) (← tr ctx b))
  -- A node alternative: the target fields end with the step cost `c` and the continuation
  -- `k'`; the source alternative takes the fields before `c` and the continuation `k`.
  let node (minor : Expr) (ty : Expr) : TermElabM Expr :=
    forallTelescope ty fun fs _ => do
      let c := fs[fs.size - 2]!
      let k' := fs[fs.size - 1]!
      let kTy ← forallTelescope (← inferType k') fun ys _ => mkForallFVars ys Tm.type
      withLocalDeclD `k kTy fun k => do
        let srcFields := (fs.extract 0 (fs.size - 2)).push k
        let b ← Core.betaReduce (mkAppN minor srcFields)
        let ctx' := { ctx with locals := ctx.locals.insert k.fvarId! ⟨.treeFn, k', some c⟩ }
        let p ← tr ctx' b
        let p := p.replaceFVar k (← erasure .treeFn kTy k')
        mkLambdaFVars fs (T.delayE (natE 1) p)
  let altRand ← node args[6]! minorTys[1]!
  let altQuery ← node args[7]! minorTys[2]!
  -- The unit of the case analysis is charged in each alternative, so that the case analysis
  -- heads the costed form and Lean derives its equations.
  return mkAppN cases #[altRet, altRand, altQuery]

/-- The costed form of the reduction `c` at the universe levels of `f`: registered, or
derived now. -/
partial def ensureTimed (ctx : Ctx) (c : Name) (f : Expr) : TermElabM Expr := do
  let name := c ++ ctx.suffix
  unless (← getEnv).contains name do
    if ctx.visiting.contains c then
      fail m!"`{c}` is reached again while its costed form is derived (mutual recursion)"
    try
      -- The callee is derived in its own context: the locals, fields, substitutions and the
      -- plain interface of the caller are not the callee's.
      deriveTimed { suffix := ctx.suffix, visiting := ctx.visiting.insert c } c
    catch ex =>
      throwError m!"derive_timed: while deriving the costed form of the callee `{c}`:\n\
        {ex.toMessageData}"
  return mkConst name f.constLevels!

/-- A call of the reduction whose costed form is `target`: one plus the step cost of the
costed call plus the costs of the arguments. -/
partial def callTimed (ctx : Ctx) (e target : Expr) (args : Array Expr) (T : TreeTy) :
    TermElabM Expr := do
  let kinds ← argKinds e.getAppFn args
  let mut out := #[]
  let mut cost := natE 0
  for a in args, (k, _) in kinds do
    match k with
    | .static => out := out.push a
    | .data =>
      out := out.push a
      cost := add cost (← costOf ctx a)
    | .hat =>
      let (c, v) ← tv ctx a
      out := out.push v
      cost := add cost c
    | .fn =>
      out := out.push a |>.push (← companionOf ctx a)
      cost := add cost (← costOf ctx a)
    | .tree =>
      let some Ta ← treeTyH? (← inferType a)
        | fail m!"`{a}` is not a tree of a registered kind"
      let some raw ← treeTy? (← inferType a) | fail m!"`{a}` is not a tree"
      let p ← lowerArgE Ta raw (← tr ctx a)
      out := out.push (raw.sndOf p)
      cost := add cost (raw.fstOf p)
    | .treeFn =>
      match a.consumeMData with
      | .fvar id =>
        match ctx.locals.get? id with
        | some { kind := .treeFn, value, companion? := some c } =>
          out := out.push value |>.push c
        | _ => fail m!"a function bound in data: `{a}` has no costed form"
      | _ =>
        let arity ← forallTelescope (← whnfR (← inferType a)) fun ys _ => pure ys.size
        let (v, c) ← withEta a arity fun ys b => do
          let some Tb ← treeTyH? (← inferType b)
            | fail m!"`{b}` is not a tree of a registered kind"
          let some raw ← treeTy? (← inferType b) | fail m!"`{b}` is not a tree"
          let p ← lowerArgE Tb raw (← tr ctx b)
          return (← mkLambdaFVars ys (raw.sndOf p), ← mkLambdaFVars ys (raw.fstOf p))
        out := out.push v |>.push c
  let arity ← forallTelescope (← inferType target) fun ys _ => pure ys.size
  -- The costed form of the callee takes the cost companions of field paths of its binders
  -- (`R.timed.fieldPaths`): the caller passes its companions for the same paths at the
  -- arguments of the call.
  if out.size < arity then
    if let .const tname tlvls := target then
      let fpName := tname ++ `fieldPaths
      if (← getEnv).contains fpName then
        let some fp ← unfoldDefinition? (mkAppN (mkConst fpName tlvls) args)
          | fail m!"internal: `{fpName}` does not unfold"
        let mut tup := fp.headBeta
        let mut paths := #[]
        while tup.isAppOfArity ``PProd.mk 4 do
          paths := paths.push (tup.getArg! 2)
          tup := (tup.getArg! 3).headBeta
        for p in paths do
          if let some (_, cc) := ctx.fields.find? (·.1 == p) then
            out := out.push cc
          else if let some r := ctx.fieldRec? then
            unless (← r.get).contains p do r.modify (·.push p)
            out := out.push (← mkFreshExprMVar (← companionType (← inferType p)))
          else
            fail m!"the costed form of the callee `{e.getAppFn}` takes the cost of the field \
              `{p}`, which is not a field of a binder of the caller"
  unless out.size == arity do
    fail m!"the costed form of the callee `{e.getAppFn}` takes the costs of fields of local \
      structures or instances; register its costed form at the call"
  return T.delayE (add (natE 1) cost) (mkAppN target out)

/-- Derive and add the costed form `c.timed` and the erasure theorem `c.erase_timed` of the
reduction `c`. -/
partial def deriveTimed (ctx : Ctx) (c : Name) : TermElabM Unit := do
  let env ← getEnv
  let some info := env.find? c | fail m!"unknown constant `{c}`"
  let timedName := c ++ ctx.suffix
  let eraseName := c ++ (Name.mkSimple ("erase_" ++ ctx.suffix.toString))
  if env.contains timedName then fail m!"`{timedName}` already exists"
  let levels := info.levelParams.map mkLevelParam
  let recursive := (Structural.eqnInfoExt.find? env c).isSome || (WF.eqnInfoExt.find? env c).isSome
  let body ← match Structural.eqnInfoExt.find? env c, WF.eqnInfoExt.find? env c, info with
    | some i, _, _ => pure i.value
    | _, some i, _ => pure i.value
    | _, _, .defnInfo d => pure d.value
    | _, _, _ => fail m!"`{c}` has no definition to translate; register `{timedName}`"
  let type := info.type
  -- Eta-expand to all binders of the type, through type definitions.
  let value ← lambdaTelescope body fun xs b => do
    withTypeBinders (← instantiateForall type xs) fun ys _ =>
      mkLambdaFVars (xs ++ ys) (mkAppN b ys).headBeta
  -- A distribution is not a program: a reduction valued in `PMF` has no cost structure.
  let resultPMF ← lambdaTelescope value fun _ b => do
    return (← whnfR (← inferType b)).isAppOf ``PMF
  if resultPMF then
    fail m!"no cost structure: `{c}` is valued in `PMF`, a distribution without a program; \
      write it as an oracle tree or a computation tree (`SPComp`) to derive its time"
  -- A tree binder whose results hold functions: its results are lifted to costed closures.
  let binderHat ← lambdaTelescope value fun xs _ => xs.anyM fun x => do
    forallTelescope (← whnfR (← inferType x)) fun _ b => do
      match ← treeTy? b with
      | some T => return (← hatTy? T.result).isSome
      | none => return false
  -- The tree of a field `f` of a structure-valued reduction `R` (named `R.f.tree`) has the
  -- plain interface that the costed mirror of the structure takes.
  let fieldTree : TermElabM Bool :=
    match c with
    | .str (.str P f) "tree" =>
      match env.find? P with
      | some pinfo => forallTelescope pinfo.type fun _ r => do
          match (← whnfR r).getAppFn with
          | .const S _ =>
            pure (isStructure env S && (getStructureFields env S).contains (Name.mkSimple f))
          | _ => pure false
      | none => pure false
    | _ => pure false
  let plain ← if ctx.plain then pure true else fieldTree
  let ctx := { ctx with plain }
  -- A plain interface around data holding functions: the erasure lemmas of costed closures.
  let plainHat ← if !plain then pure false else lambdaTelescope value fun xs b => do
    if ← xs.anyM fun x => do return (← hatTy? (← inferType x)).isSome then return true
    let some rawT ← treeTy? (← inferType b) | return false
    return (← hatTy? rawT.result).isSome
  let (tType, tValue, eType, nBinders, hatted, fp?) ← lambdaTelescope value fun xs b => do
    let some T ← treeTyH? (← inferType b)
      | fail m!"the result of `{c}` is not a tree of a registered kind"
    let some rawT ← treeTy? (← inferType b) | fail m!"internal: the result of `{c}`"
    -- The tree type of the costed form: the plain one for the plain interface.
    let To := if plain then rawT else T
    let ctx := { ctx with top := xs.map (·.fvarId!) }
    -- The field paths applied in the body, and those reached through unfolded definitions,
    -- recorded by a first pass.
    let direct ← fieldPrefixes b
    let reached ← withBinders ctx xs fun ctx bs _ => do
      let r ← IO.mkRef (#[] : Array Expr)
      withLocalDeclD `rec (← mkForallFVars bs T.pairType) fun recF => do
        try discard <| tr { ctx with self? := some (c, recF), fieldRec? := some r } b
        catch _ => pure ()
      r.get
    let cands := reached.foldl (fun acc p => if acc.contains p then acc else acc.push p) direct
    -- Methods of an abstract structure (a local instance) cost one unit: no companion.
    let cands ← cands.filterM fun p => do
      let .const pc _ := p.getAppFn | return true
      let some pinfo ← getProjectionFnInfo? pc | return true
      unless pinfo.fromClass && isUnitMethod pc do return true
      let some inst := p.getAppArgs[pinfo.numParams]? | return true
      return !(← builtFromLocalInstance inst)
    withBinders ctx xs fun ctx bs args => do
      withFieldCosts cands fun fcs => do
        -- The costed form with the cost companions of the fields `fs` after the binders `bs`;
        -- a recursive call passes the same companions.
        let build (fs : Array (Expr × Expr)) : TermElabM (Expr × Expr × Expr) := do
          let recType ← mkForallFVars bs To.pairType
          withLocalDeclD `rec recType fun recF => do
            let ctx := { ctx with self? := some (c, recF), fields := fs }
            let p ← tr ctx b
            let p := p.replaceFVars (ctx.hatSubst.map (·.1)) (ctx.hatSubst.map (·.2))
            let p ← if plain then lowerArgE T rawT p else pure p
            let cs := fs.map (·.2)
            let p ← if cs.isEmpty then pure (p.replaceFVar recF (mkConst timedName levels))
              else
                let self ← mkLambdaFVars bs (mkAppN (mkConst timedName levels) (bs ++ cs))
                Core.betaReduce (p.replaceFVar recF self)
            if p.containsFVar recF.fvarId! then fail m!"internal: the recursive call escaped"
            return (← mkForallFVars (bs ++ cs) To.pairType, ← mkLambdaFVars (bs ++ cs) p, p)
        -- Only the fields priced by the translation receive a cost companion.
        let used ← if fcs.isEmpty then pure #[] else do
          let (_, _, v) ← build fcs
          pure (fcs.filter fun (_, cc) => v.containsFVar cc.fvarId!)
        if recursive && !used.isEmpty then
          let fixed := (List.range xs.size).filter fun i =>
            used.any fun (p, _) => p.containsFVar xs[i]!.fvarId!
          let need := fixed.foldl (fun m i => max m (i + 1)) 0
          let bad := b.find? fun s => s.isAppOf c && s.getAppNumArgs ≥ need &&
            fixed.any fun i => s.getArg! i != xs[i]!
          if let some s := bad then
            fail m!"the recursive call `{s}` changes a structure or instance whose applied \
              fields are priced by cost companions"
        let (tType, tValue, _) ← build used
        let bs := bs ++ used.map (·.2)
        for x in xs do
          if tValue.containsFVar x.fvarId! && !(bs.contains x) then
            fail m!"the binder `{x}` of `{c}` occurs in a type of the costed form"
        let call := mkAppN (mkConst timedName levels) bs
        let lhs := To.eraseE (To.sndOf call)
        -- A result holding functions: the erased costed tree followed by `ε`.
        let hatted := !plain && (← hatTy? rawT.result).isSome
        let lhs ← if !hatted then pure lhs else do
          let lam ← withLocalDeclD `y T.result fun y => do
            let r := mkAppN (mkConst T.kind.nodes[0]!.src) (rawT.params.push
              (← epsE rawT.result y))
            mkLambdaFVars #[y] r
          mkAppM (T.kind.tree ++ `bind) #[lhs, lam]
        let rhs := mkAppN (mkConst c levels) args
        let eType ← mkForallFVars bs (← mkEq lhs rhs)
        let explicit ← bs.mapM fun b => return (← b.fvarId!.getBinderInfo).isExplicit
        -- The field paths whose cost companions the costed form takes, as a function of the
        -- binders of `c`: a caller passes its companions for them (`callTimed`).
        let fp? ← if used.isEmpty then pure none else do
          let mut tup : Expr := mkConst ``PUnit.unit [Level.one]
          for (p, _) in used.reverse do
            tup ← mkAppM ``PProd.mk #[p, tup]
          pure (some (← mkLambdaFVars xs tup))
        return (tType, tValue, eType, explicit, hatted, fp?)
  addTimedDef timedName info.levelParams tType tValue
  if let some fp := fp? then
    addTimedDef (timedName ++ `fieldPaths) info.levelParams (← inferType fp) fp
  -- The erasure theorem.
  let callees := collectTimed (← getEnv) ctx.suffix tValue timedName
  -- The erasure lemmas of the tree kinds whose costed trees occur in the costed form.
  let used := tType.getUsedConstants ++ tValue.getUsedConstants
  let kindLemmas := (treeKinds.filter fun k => used.contains k.timed).flatMap (·.eraseLemmas)
  -- A costed form by recursion over an oracle tree has a case analysis as its only equation,
  -- which `fun_induction` unfolds; as a simp lemma it would loop.
  let treeRec := tValue.getUsedConstants.contains ``CatCrypt.Crypto.OracleAdv.Timed.casesOn
  -- Costed closures in a result or in a simulation state: the lemmas that push `ε` to the
  -- leaves and the erasure of a simulation with a costed state.
  let hatLemmas : Array Name :=
    if hatted || binderHat || plainHat || used.contains ``CatCrypt.Crypto.OracleAdv.Timed.simulateHat ||
        callees.any (fun n => n.toString.endsWith "_bind") then
      (treeKinds.filter fun k => used.contains k.timed).flatMap (·.hatLemmas)
    else #[]
  let simpLemmas : Array Name :=
    (if treeRec then #[c] else #[timedName, c]) ++ kindLemmas ++ hatLemmas ++ callees
  let ids : Array (TSyntax `ident) := (Array.range nBinders.size).map fun i =>
    mkIdent (Name.mkSimple s!"x{i}")
  let explicitIds := (ids.zip nBinders).filterMap fun (i, e) => if e then some i else none
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    simpLemmas.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  -- The side conditions of `erase_simulateHat_bind` are equations under binders, discharged
  -- by the same lemmas.
  let close ← if hatLemmas.isEmpty then
      `(tactic| ((try simp only [$lemmas,*, *]) <;> (try (repeat' split)) <;>
        (try simp only [$lemmas,*, *]) <;> (try rfl)))
    else
      `(tactic| ((try simp (disch := (intros; simp only [$lemmas,*])) only [$lemmas,*, *]) <;>
        (try (repeat' split)) <;>
        (try simp (disch := (intros; simp only [$lemmas,*])) only [$lemmas,*, *]) <;>
        (try rfl)))
  let tac ← if recursive then
      `(tactic| (intro $ids*; fun_induction $(mkIdent timedName):ident $explicitIds* <;> $close))
    else if treeRec then
      `(tactic| (intro $ids*; $close))
    else
      -- A costed form whose body is a match on a binder has its equations split by case:
      -- `unfold` rewrites it at a variable.
      `(tactic| (intro $ids*; (try unfold $(mkIdent timedName):ident); $close))
  let proof ← Term.withoutErrToSorry do
    let mv ← mkFreshExprMVar eType
    let rem ← Tactic.run mv.mvarId! (Tactic.evalTactic tac)
    unless rem.isEmpty do
      fail m!"the erasure theorem `{eraseName}` is not closed by unfolding and the erasure \
        lemmas; goals left:{indentD (MessageData.joinSep (rem.map (.ofGoal ·)) "\n")}"
    instantiateMVars mv
  if proof.hasSorry || proof.hasMVar then
    fail m!"the erasure theorem `{eraseName}` is not proved"
  let thm : TheoremVal :=
    { name := eraseName, levelParams := info.levelParams, type := eType, value := proof }
  addDecl (Declaration.thmDecl thm)
  -- A result holding functions: the erasure theorem for the costed tree followed by a
  -- continuation that depends on a result only through its erasure.
  if hatted then
    let levels := info.levelParams.map mkLevelParam
    let (bType, bValue) ← forallTelescope eType fun bs eq => do
      let some (_, lhs, rhs) := eq.eq? | fail m!"internal: `{eraseName}` is not an equation"
      let some T ← treeTy? (← inferType rhs) | fail m!"internal: the result of `{c}`"
      let E := lhs.getArg! (lhs.getAppNumArgs - 2)
      let εF ← epsFun T.result
      let ιF ← iotaFun T.result
      let some ht ← hatTy? T.result | fail m!"internal: the result of `{c}`"
      withLocalDeclD `β (mkSort Level.one) fun β => do
        let treeOf (a : Expr) : Expr := mkAppN (mkConst T.kind.tree)
          (T.params.set! (T.params.size - 1) a)
        withLocalDeclD `k (← mkArrow ht (treeOf β)) fun k => do
          let hkTy ← withLocalDeclD `y ht fun y => do
            mkForallFVars #[y] (← mkEq (mkApp k y)
              (mkApp k (mkApp ιF (mkApp εF y)).headBeta.headBeta))
          withLocalDeclD `hk hkTy fun hk => do
            let bindHat := if T.kind.tree == ``CatCrypt.Core.SPTree then
                ``CatCrypt.Core.SPTree.Timed.bind_hat
              else ``CatCrypt.Crypto.OracleAdv.Timed.bind_hat
            let pf ← mkAppM bindHat #[εF, ιF, E, rhs,
              mkAppN (mkConst eraseName levels) bs, k, hk]
            let ty ← inferType pf
            return (← mkForallFVars (bs ++ #[β, k, hk]) ty,
              ← mkLambdaFVars (bs ++ #[β, k, hk]) pf)
    let bindThm : TheoremVal :=
      { name := eraseName.appendAfter "_bind", levelParams := info.levelParams,
        type := bType, value := bValue }
    addDecl (Declaration.thmDecl bindThm)

/-- The callees of `v` with a costed form `n.suffix` other than `self`, as their erasure
theorems, with the erasure theorems `R.erase_timed_bind` of the callees whose results hold
functions. -/
partial def collectTimed (env : Environment) (suffix : Name) (v : Expr) (self : Name) :
    Array Name :=
  let eraseSuffix := Name.mkSimple ("erase_" ++ suffix.toString)
  v.getUsedConstants.foldl (init := #[]) fun acc n =>
    match n with
    | .str p s =>
      if n != self && s == suffix.toString then
        let thm := p ++ eraseSuffix
        let acc := if env.contains thm && !acc.contains thm then acc.push thm else acc
        let thmB := thm.appendAfter "_bind"
        if env.contains thmB && !acc.contains thmB then acc.push thmB else acc
      else acc
    | _ => acc

/-- Add the definition `name`, settling its recursion as a `def`'s. In a `module` file the
definition is exposed, so that importing modules unfold costed forms and costs. -/
partial def addTimedDef (name : Name) (levelParams : List Name) (type value : Expr) :
    TermElabM Unit := do
  let saved := (← getThe Core.State).messages
  modifyThe Core.State fun s => { s with messages := {} }
  let outcome ← try
      withExporting (isExporting := (← getEnv).header.isModule) <| addPreDefinitions ({}, {}) #[{
        ref := .missing, kind := .def, levelParams,
        modifiers := { computeKind := .noncomputable }, declName := name,
        binders := .missing, type, value, termination := .none }]
      pure none
    catch ex => pure (some ex.toMessageData)
  let msgs := (← getThe Core.State).messages
  modifyThe Core.State fun s => { s with messages := saved }
  let failure := match outcome with
    | some m => some m
    | none =>
      if msgs.hasErrors then
        some (MessageData.joinSep (msgs.toList.filterMap fun (m : Message) =>
          if m.severity == MessageSeverity.error then some m.data else none) "\n")
      else none
  if let some why := failure then
    fail m!"`{name}` could not be defined: {why}"

/-- Price `b` in `ctx` with each prefix of `ps` standing for a local function whose cost
companion is zero, so that each call of a listed method costs one plus its arguments. -/
partial def costWithUnits (ctx : Ctx) (ps : Array Expr) (b : Expr) : TermElabM Expr := do
  let rec go (i : Nat) (ctx : Ctx) (b : Expr) (us : Array (Expr × Expr)) : TermElabM Expr := do
    if h : i < ps.size then
      let p := ps[i]
      let t ← inferType p
      withLocalDeclD `unitMethod t fun u => do
        let zero ← forallTelescope (← whnfR t) fun ys _ => mkLambdaFVars ys (mkNatLit 0)
        let ctx := { ctx with locals := ctx.locals.insert u.fvarId! ⟨.fn, u, some zero⟩ }
        go (i + 1) ctx (b.replace fun s => if s == p then some u else none) (us.push (u, p))
    else
      let c ← costOf ctx b
      let c := us.foldl (fun c (u, p) => c.replaceFVar u p) c
      return (← Core.betaReduce c)
  go 0 ctx b #[]

/-- Derive and add the cost `c.timedCost` of the data function `c` (the command `derive_cost`
of `CatCryptCore.Tactics.DeriveCost`), charging the class methods `units` on local instances
one unit. The body priced is the one Lean keeps for the equation lemmas of `c`, in which a
recursive call is an application of `c`; it is priced by the cost being defined, so the cost
is defined by the recursion of `c`. -/
partial def deriveCostCore (units : Array Name) (c : Name) : TermElabM Unit := do
  let env ← getEnv
  let some info := env.find? c | throwError "derive_cost: unknown constant `{c}`"
  let costName := c ++ `timedCost
  if env.contains costName then throwError "derive_cost: `{costName}` already exists"
  let levels := info.levelParams.map mkLevelParam
  let value ← costValue c info
  let (cType, cValue) ← lambdaTelescope value fun xs b => do
    if (← treeTyH? (← inferType b)).isSome then
      throwError "derive_cost: the result of `{c}` is a tree; use `derive_timed`"
    for x in xs do
      if (← classify (← inferType x)) matches .tree | .treeFn then
        throwError "derive_cost: the binder `{x}` of `{c}` is a tree; use `derive_timed`"
    let paths ← recordFieldPaths units c xs b
    withBinders { top := xs.map (·.fvarId!) } xs fun ctx bs _ => do
      withFieldCosts paths fun fcs => do
        let cs := fcs.map (·.2)
        -- A recursive call passes the structures whose fields have cost companions unchanged.
        if !cs.isEmpty && ((Structural.eqnInfoExt.find? env c).isSome ||
            (WF.eqnInfoExt.find? env c).isSome) then
          let fixed := (List.range xs.size).filter fun i =>
            paths.any fun p => p.containsFVar xs[i]!.fvarId!
          let need := fixed.foldl (fun m i => max m (i + 1)) 0
          let bad := b.find? fun s => s.isAppOf c && s.getAppNumArgs ≥ need &&
            fixed.any fun i => s.getArg! i != xs[i]!
          if let some s := bad then
            throwError "derive_cost: the recursive call `{s}` changes a structure whose applied \
              fields are priced by cost companions"
        let cType ← mkForallFVars (bs ++ cs) (mkConst ``Nat)
        let ps ← unitPrefixes units b
        withLocalDeclD `rec (← mkForallFVars bs (mkConst ``Nat)) fun recF => do
          let cost ← costWithUnits { ctx with selfCost? := some (c, recF), fields := fcs } ps b
          let cost ← instantiateMVars cost
          if cost.hasMVar then
            throwError "derive_cost: the cost of `{c}` has unassigned universes"
          let self ← mkLambdaFVars bs (mkAppN (mkConst costName levels) (bs ++ cs))
          let cost ← Core.betaReduce (cost.replaceFVar recF self)
          return (cType, ← mkLambdaFVars (bs ++ cs) cost)
  addTimedDef costName info.levelParams cType cValue

/-- The value of the data function `c` that `derive_cost` prices: the body of its equation
lemmas, eta-expanded to all binders of its type through type definitions. -/
partial def costValue (c : Name) (info : ConstantInfo) : TermElabM Expr := do
  let env ← getEnv
  let body ← match Structural.eqnInfoExt.find? env c, WF.eqnInfoExt.find? env c, info with
    | some i, _, _ => pure i.value
    | _, some i, _ => pure i.value
    | _, _, .defnInfo d => pure d.value
    | _, _, _ => throwError "derive_cost: `{c}` has no definition to price"
  lambdaTelescope body fun xs b => do
    withTypeBinders (← instantiateForall info.type xs) fun ys _ =>
      mkLambdaFVars (xs ++ ys) (mkAppN b ys).headBeta

/-- The field paths of the binders `xs` of the data function `c` with body `b` that its cost
prices, in the order in which a pricing pass reaches them: the fields whose cost companions
the derived cost `c.timedCost` takes after its binders. -/
partial def recordFieldPaths (units : Array Name) (c : Name) (xs : Array Expr) (b : Expr) :
    TermElabM (Array Expr) := do
  withBinders { top := xs.map (·.fvarId!) } xs fun ctx bs _ => do
    let r ← IO.mkRef (#[] : Array Expr)
    let ps ← unitPrefixes units b
    withLocalDeclD `rec (← mkForallFVars bs (mkConst ``Nat)) fun recF => do
      try discard <| costWithUnits { ctx with selfCost? := some (c, recF), fieldRec? := some r } ps b
      catch _ => pure ()
    r.get

/-- The field paths whose cost companions the derived cost of the data function `c` takes,
instantiated at the arguments `args` of a call of `c` at the universe levels `lvls`. -/
partial def calleeFieldPaths (c : Name) (lvls : List Level) (args : Array Expr) :
    TermElabM (Array Expr) := do
  let some info := (← getEnv).find? c | return #[]
  let value := (← costValue c info).instantiateLevelParams info.levelParams lvls
  lambdaTelescope value fun xs b => do
    unless xs.size == args.size do
      fail m!"the cost of `{c}` takes the costs of fields, and `{c}` is applied to \
        {args.size} of its {xs.size} arguments"
    let ps ← recordFieldPaths #[] c xs b
    return ps.map (·.replaceFVars xs args)

end

/-- `derive_timed R` defines the costed form `R.timed` of the reduction `R` and proves its
erasure theorem `R.erase_timed`; `derive_timed (suffix := s) R` names them `R.s` and
`R.erase_s`. -/
syntax (name := deriveTimedCmd) "derive_timed " ("(" &"suffix" " := " ident ") ")? ident :
  command

@[command_elab deriveTimedCmd]
def elabDeriveTimed : CommandElab := fun stx => do
  let suffix := match stx[1].getOptional? with
    | some s => s[3].getId
    | none => `timed
  let id := stx[2]
  liftTermElabM do
    let c ← realizeGlobalConstNoOverloadWithInfo id
    deriveTimed { suffix } c

/-- `timed_cost f := e` registers `e` as the cost of the primitive `f`: it defines
`f.timedCost := e`, which takes the arguments of `f`, each function-typed argument followed
by its cost companion. A registered cost is a trusted statement about the cost of `f`. -/
syntax (name := timedCostCmd) "timed_cost " ident " := " term : command

@[command_elab timedCostCmd]
def elabTimedCost : CommandElab := fun stx => do
  let c ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let e : TSyntax `term := ⟨stx[3]⟩
  elabCommand (← `(@[expose] noncomputable def $(mkIdent (`_root_ ++ c ++ `timedCost)) := $e))

end CatCrypt.Tactics.DeriveTimed

end
