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
  `sample`, `get`, `set`, `fail` and the heap reset `load`, and the combinators `SPTree.bind`
  and `SPTree.map`.

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
* data holding functions (a pair or a sum with a function component, such as a simulation
  state with a table `ℕ → List (D × R)`) becomes its costed value (`hatTy?`), in which each
  function `X → Y` with a first-order domain is a costed closure `(X → Ŷ) × (X → ℕ)`: the
  function and its cost companion; it is erased by `ε`, which keeps the functions (`epsE`);
* a structure holding functions is kept, and its function fields applied in the body are
  field paths (below).

## Functions stored in data and in state fields

A function stored in data, in a component of a sum or in a field of a state structure carries
its cost companion with it, as the costed closure of the function and its companion; the
companion is built where the function is created and read where the function is applied
(the convention of `OracleAdv.Timed.simulateHat` for a simulation state):

* the costed type of a sum `A ⊕ B` is `Â ⊕ B̂`, erased and lifted componentwise by `Sum.map`;
* a structure `S` whose fields are data of types independent of the other fields, one of
  which holds functions, has as costed value its mirror (`mirrorStruct?`, `mirrorType`): the
  tuple `ĥ₀ × (ĥ₁ × … × ĥₙ₋₁)` of the costed values of its fields; `ε` applies the constructor
  to the erased components, `ι` lifts each field;
* a constructor application `S.mk a₁ … aₙ` or `Sum.inl a` is translated componentwise; a
  field `s.f` of such a structure is the component of the costed value of `s`, and a
  function field applied, `s.f x`, costs one plus the companion of that component at `x`
  (`costConst`); a `let` of a structure stays a `let`, and its costed value is that of its
  value;
* a field of a pattern of a match on a discriminant with a costed value (the block `a` of
  `| .inl a`, a field of `| ⟨f, g⟩`) keeps its function and reads its companion from the
  discriminant's costed value (`patternHats`, `refillE`): a component of a pair or a mirror,
  or, under `Sum.inl`/`Sum.inr`, the component selected by `Sum.elim`;
* the result of a call of a function binder holding functions (`st a : S`), a local without
  a costed value, and a function under any other constructor (`Option`, `List`) hold tables
  (`ι`), as the functions received from a tree do.

A binder of the reduction whose type is such a structure keeps the convention of field paths
(below), so that a scheme or a kit passed as a binder has the cost companions of its applied
fields as further binders; a binder whose type is a sum holding functions is a costed value.

A field path whose value is used as data holding functions (the input `Z.input : Unit × S` of an
environment binder `Z : Env (Unit × S) β`, with `S` a state structure with function fields,
passed on as a state) is a data path: the shortest such prefix `p : t` of a path, below a
binder without a costed value, has as costed value `refillE t p p̂` (`pathHat?`), whose
functions are those of `p` and whose cost companions are read from a further binder
`p̂ : hatTy? t` after the binders of `R` (named `inputHat`, recorded with the field paths), so
that its erasure reduces to `p`. A path below it (`Z.input.2`) has the component of that costed
value, and a function field applied below it (`Z.input.2.f x`) is the costed closure of the
component, applied, in place of a field path with its own companion.

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
  match binds it, by its companion; a `let` applied to arguments has the application pushed
  into its body, `(let x := v; f) a ⇝ let x := v; f a`, so that `v` is priced once;
* a tree-valued field of a field path (`S.kem.encaps pk`, a program of a scheme) is a
  primitive: its tree runs at the unit cost of its nodes (`OracleAdv.Timed.ofAdv`) and its
  computation is priced by a cost companion indexed by the field's arguments;
* a method of an abstract algebraic structure, a method of an algebraic operation class
  (`+`, `*`, `-`, `^`, `•` of `[AddCommGroup M]` or `[Field F]`, `algebraicMethods`) or of
  `CryptoWord` whose instance is built from a local instance, costs one plus its arguments,
  as one call of the interface, and gets no cost companion; a method of any other class on a
  local instance (a primitive interface of a protocol) keeps its cost companion;
* `if` and `match` cost one, plus the costs of the condition or the discriminants, plus the
  cost of the branch taken; a match of a tree whose motive depends on its discriminants
  (`SPTree (Fin n → X)` on `n`) has the costed tree type at each discriminant as its motive;
* constructors, literals, numerals, casts, projections and variables cost nothing beyond
  their arguments (the parameters of a constructor's inductive type are not among them), and
  a closure costs nothing to build;
* an elimination from an empty type (`Fin.elim0`, `False.elim`, `absurd`) is never evaluated
  and costs nothing;
* a function field applied to arguments, of a structure that reduces to a constructor
  application (a constant structure `xorEnc`, or a `let` bound to one), costs the structure
  plus the field's value at the arguments, priced as an unfolded definition;
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
  the cost of `v` is charged in front; a `let` of a structure value stays a `let`, and a
  field applied through it is priced as a field of a structure that reduces to a constructor;
  a `let` of a type, a proof, a function, a tree or a field path of a local (`kit.hkdf`,
  which costs nothing) is substituted into its body;
* an unfolded definition binds its arguments in the same way, so that each argument is priced
  once per call, whether its parameter is used once, several times or not at all.

The binders of `R` are those of its type, which is reduced through type definitions: a
reduction whose declared type is an adversary type `W → W → W → SPComp Bool` under a name
takes the three binders of that type.

The erasure theorem of a definition by well-founded recursion is proved by functional induction
on its costed form, with the definition unfolded once by `unfold` (its unconditional equation
loops as a simp lemma) and the induction hypotheses, conditional on the hypothesis of the
case of an `if`, discharged by `assumption`.

The erasure theorem of a recursion whose result holds functions (`SPTree (Fin n → X)`) is
proved by induction with each induction hypothesis
`(R.timed ys).2.erase.bind (fun y => ret (ε y)) = R ys` used from right to left
(`rewriteRecHyps`), so that the recursive call becomes the erased costed call followed by `ε`.

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
function without a cost companion applied, a function in a list or an option), a field of a
structure that is neither a field path, nor a field of a computed structure, nor a field of a
structure with a mirror, nor a field of a structure value as below, an opaque data function without a registered cost, an operation on a quotient type
(`Finset`, `Multiset`, `Quot`) without a registered cost (the costs of `Finset.sum`,
`Finset.prod`, `Finset.univ`, `Finset.range` and `Finset.erase` are registered in
`CatCryptCore.Tactics.StdCosts`), a recursive data
function whose cost `derive_cost` does not derive (a class method on a local instance in its
body needs `derive_cost (unit := …)`), a `match` whose motive depends on its
discriminants, a match on an oracle tree that is not a binder, a recursive call that changes a
structure whose fields have cost companions, and a call of a reduction whose costed form
takes such companions.

## States, generic callees and recursion

A leaf of a handler that returns its incoming state, or a structure update of it, keeps the cost
companions of the unchanged function fields of the state (`iotaPathE`), and the costed form
takes those companions after its binders. A call of a non-recursive tree-valued definition
generic in its state type, at a state holding functions, is unfolded and translated in the
caller's context (`unfoldsGenericCall`). A call of a registered costed form generic in the
result type of a tree argument, at a result type holding functions, passes the costed tree and
instantiates the type parameter at its costed type; the erasure theorem uses the naturality
lemma `c.bind_ret : (c X).bind (fun y => .ret (f y)) = c (X.bind fun y => .ret (f y))` of the
callee, without which the call is refused. A recursive data function whose result holds
functions gets a costed value `c.timed` by its recursion, with the erasure theorem
`c.erase_timed : ε (c.timed xs) = c (ε xs)`, proved by functional induction, and one projection
lemma `c.erase_timed_<i>` per component (`deriveHatValue`). The members of a mutual block are
priced together (`deriveCostBlock`): their costs take the cost companions of the fields that the
block applies, shared by all members and passed through the recursive calls. A function field
of a structure value given as a constructor application or by a `let` is priced through that
value (`isValueField`).

The erasure proof unfolds the data definitions whose bodies are headed by a case analysis (a
matcher, `if` or dependent `if`; `isCaseHead`). After the `if` closer it runs a stage with the
bind lemmas of `if`, of dependent `if` (`OracleAdv.ite_bind`, `SPTree.dite_bind`) and of the
matchers of the costed form (`matchBindLemma`), first without the discharger, then with it. A
costed form whose value uses a declaration private to the module is not exposed, since its
equation lemmas could not be stated in the exported environment.

## Attribution

The translation rules and the derivation on demand follow the instrumented translation of
the Ironwood project (`Zcash/Meta/Translate.lean`, `Instrument.lean`, `Efficient.lean`),
which is dual-licensed under the MIT and Apache-2.0 licences. Those rules follow the
translation of Isabelle's `time_fun` command and in addition charge one unit for each call of a
non-recursive function and for each decision of `if` and `match`; `derive_timed` also charges
one unit for each arithmetic operation (`CatCryptCore/Crypto/ConcreteSecurity.md`, §4).

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
* `OracleAdv.Timed.allRet_bind`, `OracleAdv.Timed.allRet_mono` — leaves of a sequencing, and
  monotonicity of `AllRet`
* `OracleAdv.Timed.allRet_simulateHat_inv` — the final state of a costed simulation satisfies
  the state invariant at index `i + q`
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

/-- Erasure of a costed oracle tree commutes with an `if`. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.erase_ite_oracle {D R α : Type} (c : Prop)
    [Decidable c] (x y : Timed D R α) :
    (if c then x else y).erase = if c then x.erase else y.erase := by
  split <;> rfl

/-- The recursor of `Bool` at a constant motive is the `if` on its major premise. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.boolRec_eq_ite {α : Sort _} (f t : α) (b : Bool) :
    Bool.rec (motive := fun _ => α) f t b = if b = true then t else f := by
  cases b <;> rfl

/-- Erasure of a costed computation tree commutes with an `if`. -/
theorem _root_.CatCrypt.Tactics.DeriveTimed.erase_ite_spTree {α : Type} (c : Prop)
    [Decidable c] (x y : CatCrypt.Core.SPTree.Timed α) :
    (if c then x else y).erase = if c then x.erase else y.erase := by
  split <;> rfl

/-- The costed simulation of a handler whose state `Ŝ` carries costed closures: the
simulation `simulate impl A s`, with the erasure `ε : Ŝ → S` of the state and a lift
`ι : S → Ŝ` as parameters, which state its erasure theorem `erase_simulateHat_bind`. -/
@[expose] def simulateHat {D' R' S Ŝ : Type} (_ε : Ŝ → S) (_ι : S → Ŝ)
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

/-- Every leaf of a sequencing satisfies `P` when every leaf `a` of the first tree satisfies
`Q` and the continuation at such an `a` has all its leaves in `P`. -/
theorem allRet_bind {β : Type} {Q : α → Prop} {P : β → Prop} {A : Timed D R α}
    {f : α → ℕ × Timed D R β} (hA : AllRet Q A) (hf : ∀ a, Q a → AllRet P (f a).2) :
    AllRet P (A.bind f).2 := by
  induction A with
  | ret a => exact hf a hA
  | rand p c k ih => exact fun b => ih b (hA b)
  | query d c k ih => exact fun r => ih r (hA r)

/-- `AllRet` is monotone in its predicate. -/
theorem allRet_mono {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) {A : Timed D R α}
    (h : AllRet P A) : AllRet Q A := by
  induction A with
  | ret a => exact hPQ a h
  | rand p c k ih => exact fun b => ih b (h b)
  | query d c k ih => exact fun r => ih r (h r)

/-- **Final state of a simulation under a state invariant.** With `Inv` monotone in its
index and every program of `impl` from a state with `Inv i` returning states with
`Inv (i + 1)`, a simulation of an adversary with at most `q` queries from a state with
`Inv i` returns states with `Inv (i + q)`. -/
theorem allRet_simulateHat_inv {D' R' S Ŝ : Type} (ε : Ŝ → S) (ι : S → Ŝ)
    (impl : Ŝ → D → ℕ × Timed D' R' (R × Ŝ)) (Inv : ℕ → Ŝ → Prop)
    (himpl : ∀ i s d, Inv i s → AllRet (fun y => Inv (i + 1) y.2) (impl s d).2)
    (hmono : ∀ i s, Inv i s → Inv (i + 1) s)
    {A : Timed D R α} {q : ℕ} (hq : A.erase.IsQueryBound q) (i : ℕ) (s : Ŝ) (hs : Inv i s) :
    AllRet (fun y => Inv (i + q) y.2) (simulateHat ε ι impl A s).2 := by
  unfold simulateHat
  induction A generalizing q i s with
  | ret a =>
    show Inv (i + q) s
    clear hq
    induction q with
    | zero => exact hs
    | succ q ih => exact hmono _ _ ih
  | rand p c k ih => exact fun b => ih b (hq b) i s hs
  | query d c k ih =>
    cases q with
    | zero => exact (hq : False).elim
    | succ q =>
      refine allRet_bind (himpl i s d hs) fun x hx => ?_
      have h := ih x.1 (hq x.1) (i + 1) x.2 hx
      rwa [show i + 1 + q = i + (q + 1) by omega] at h

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

namespace CatCrypt.Crypto.OracleAdv

/-- The bind of an `if` is the `if` of the binds. -/
theorem ite_bind {D R α β : Type} (c : Prop) [Decidable c] (t e : OracleAdv D R α)
    (f : α → OracleAdv D R β) :
    (if c then t else e).bind f = if c then t.bind f else e.bind f := by
  split <;> rfl

/-- The bind of a dependent `if` is the dependent `if` of the binds. -/
theorem dite_bind {D R α β : Type} (c : Prop) [Decidable c] (t : c → OracleAdv D R α)
    (e : ¬c → OracleAdv D R α) (f : α → OracleAdv D R β) :
    (if h : c then t h else e h).bind f = if h : c then (t h).bind f else (e h).bind f := by
  split <;> rfl

end CatCrypt.Crypto.OracleAdv

namespace CatCrypt.Core.SPTree

/-- The bind of an `if` is the `if` of the binds. -/
theorem ite_bind {α β : Type} (c : Prop) [Decidable c] (t e : SPTree α) (f : α → SPTree β) :
    (if c then t else e).bind f = if c then t.bind f else e.bind f := by
  split <;> rfl

/-- The bind of a dependent `if` is the dependent `if` of the binds. -/
theorem dite_bind {α β : Type} (c : Prop) [Decidable c] (t : c → SPTree α) (e : ¬c → SPTree α)
    (f : α → SPTree β) :
    (if h : c then t h else e h).bind f = if h : c then (t h).bind f else (e h).bind f := by
  split <;> rfl

end CatCrypt.Core.SPTree

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
(`fieldRec?`, in the first pass), and the data functions whose costs are being derived (the
members of a mutual block), each with the local that stands for its cost (`selfCosts`). -/
structure Ctx where
  locals : FVarIdMap LocalInfo := {}
  self? : Option (Name × Expr) := none
  suffix : Name := `timed
  depth : Nat := 0
  visiting : NameSet := {}
  fields : Array (Expr × Expr) := #[]
  top : Array FVarId := #[]
  fieldRec? : Option (IO.Ref (Array Expr)) := none
  selfCosts : Array (Name × Expr) := #[]
  /-- The binders of kind `hat` with the erasures `ε x̂` of their costed values, substituted
  for them in the costed form. -/
  hatSubst : Array (Expr × Expr) := #[]
  /-- The costed form has the plain interface of the reduction: a binder holding functions
  takes its plain value, whose functions are tables (`ι`), and the result is erased to the
  plain type (`ε`). The tree of a field of a structure-valued reduction has this interface, the
  one its costed mirror takes. -/
  plain : Bool := false
  /-- The data definitions unfolded in the costed value whose body is a match: unfolded by the
  erasure theorem, so that the hypotheses of its case split rewrite their discriminants. -/
  unfolded? : Option (IO.Ref (Array Name)) := none
  /-- The naturality lemmas `c.bind_ret` of the registered callees `c` called at a costed
  instance of the type parameter that is the result type of a tree argument (`callTimed`):
  rewriting lemmas of the erasure theorem. -/
  natural? : Option (IO.Ref (Array Name)) := none
  /-- The recursive data function whose costed value is being derived, with the local that
  stands for its costed value (`deriveHatValue`). -/
  selfHat? : Option (Name × Expr) := none

/-- The maximal nesting of unfolded data definitions (option `derive_timed.maxDepth`). -/
register_option derive_timed.maxDepth : Nat := {
  defValue := 16
  descr := "the maximal nesting of data definitions that derive_timed, derive_cost and \
    derive_reduction unfold to price a call"
}

/-- Whether the constant `n` is a case analysis: a matcher, `ite` or `dite`. A data definition
whose body is headed by one is unfolded by the erasure theorem, so that its cases meet the
cases of the costed value. -/
def isCaseHead (env : Environment) (n : Name) : Bool :=
  isMatcherCore env n || n == ``ite || n == ``dite

/-- The body of the `let` telescope `e`: a definition `let c := v; match c.f with …` is headed by
its match. -/
partial def letBody (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ _ b _ => letBody b
  | e' => e'

/-- The maximal nesting of unfolded data definitions: the option `derive_timed.maxDepth`, read
by its name, so that a command of this module runs before the option's initializer has (the
tests of the module). -/
def maxDepth : CoreM Nat := return (← getOptions).get `derive_timed.maxDepth (16 : Nat)

/-- Constants that cost nothing beyond their arguments. -/
def freeConstants : Array Name :=
  #[``OfNat.ofNat, ``Nat.cast, ``NatCast.natCast, ``Int.cast, ``IntCast.intCast, ``id,
    ``Eq.rec, ``Eq.ndrec, ``Eq.mp, ``Eq.mpr, ``cast, ``Subtype.val, ``Fin.val,
    ``PMF.uniformFintype, ``PMF.pure, ``Classical.arbitrary, ``Inhabited.default,
    ``Fin.elim0, ``False.elim, ``absurd, ``Empty.elim, ``PEmpty.elim]

/-- The namespaces of the operations on quotient types (`Finset`, `Multiset`, `Quot`,
`Quotient`), which are priced by a registered cost and never unfolded. -/
def quotientLibs : Array Name := #[`Finset, `Multiset, `Quot, `Quotient]

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
    ``Sum.map_inl, ``Sum.map_inr,
    ``CatCrypt.Crypto.OracleAdv.Timed.bind_ret_eq,
    ``CatCrypt.Tactics.DeriveTimed.fst_ite, ``CatCrypt.Tactics.DeriveTimed.snd_ite,
    ``CatCrypt.Tactics.DeriveTimed.ite_prod_mk, ``CatCrypt.Tactics.DeriveTimed.erase_ite_oracle]

/-- Syntactic computation trees `SPTree α`: `ret`, `sample`, `get`, `set`, `fail` and `load`
nodes, and the combinators `SPTree.bind` and `SPTree.map`. -/
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
    ⟨``CatCrypt.Core.SPTree.fail, ``CatCrypt.Core.SPTree.Timed.fail, #[]⟩,
    ⟨``CatCrypt.Core.SPTree.load, ``CatCrypt.Core.SPTree.Timed.load, #[.data, .cont 0]⟩]
  combinators := #[
    ⟨``CatCrypt.Core.SPTree.bind, ``CatCrypt.Core.SPTree.Timed.bind, #[.tree, .pairFn 1], true⟩,
    ⟨``CatCrypt.Core.SPTree.map, ``CatCrypt.Core.SPTree.Timed.map, #[.perCall 0 1, .tree],
      true⟩]
  eraseLemmas := #[``CatCrypt.Core.SPTree.Timed.erase_ret,
    ``CatCrypt.Core.SPTree.Timed.erase_sample, ``CatCrypt.Core.SPTree.Timed.erase_get,
    ``CatCrypt.Core.SPTree.Timed.erase_set, ``CatCrypt.Core.SPTree.Timed.erase_fail,
    ``CatCrypt.Core.SPTree.Timed.erase_load,
    ``CatCrypt.Core.SPTree.Timed.delay, ``CatCrypt.Core.SPTree.Timed.erase_bind,
    ``CatCrypt.Core.SPTree.Timed.erase_map, ``CatCrypt.Core.SPTree.Timed.erase_snd_ite,
    ``CatCrypt.Core.SPTree.Timed.erase_snd_dite]
  hatLemmas := #[``CatCrypt.Core.SPTree.bind, ``CatCrypt.Core.SPTree.bind_assoc,
    ``CatCrypt.Core.SPTree.bind_ret_val, ``CatCrypt.Core.SPTree.bind_ret, ``Prod.mk.eta,
    ``Sum.map_inl, ``Sum.map_inr,
    ``CatCrypt.Tactics.DeriveTimed.fst_ite,
    ``CatCrypt.Tactics.DeriveTimed.snd_ite, ``CatCrypt.Tactics.DeriveTimed.ite_prod_mk,
    ``CatCrypt.Tactics.DeriveTimed.erase_ite_spTree]

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

/-- A structure whose costed value is a mirror: its name, constructor, universe levels and
parameters at a type, the projections and the types of its fields. -/
structure MirrorStruct where
  struct : Name
  ctor : Name
  levels : List Level
  params : Array Expr
  projs : Array Name
  fieldTypes : Array Expr

/-- The structure `S ps` of the type `tw` (in weak head normal form), when its costed value is
a mirror: a structure that is not a class nor `Prod`, with at least one field, whose fields
are data of types that do not depend on the other fields. -/
def mirrorStruct? (tw : Expr) : MetaM (Option MirrorStruct) := do
  let .const S lvls := tw.getAppFn | return none
  if S == ``Prod || S == ``Sum then return none
  let env ← getEnv
  unless isStructure env S do return none
  if isClass env S then return none
  let some (.inductInfo ii) := env.find? S | return none
  unless ii.numIndices == 0 && tw.getAppNumArgs == ii.numParams do return none
  let [ctor] := ii.ctors | return none
  let fields := getStructureFields env S
  if fields.isEmpty then return none
  let some (.ctorInfo ci) := env.find? ctor | return none
  let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams lvls)
    tw.getAppArgs
  forallTelescope cty fun fs _ => do
    unless fs.size == fields.size do return none
    let mut tys := #[]
    for f in fs do
      let ft ← inferType f
      if ft.hasAnyFVar fun x => fs.any (·.fvarId! == x) then return none
      if ← isProp ft then return none
      if ← isTypeFormerType ft then return none
      if (← isClass? ft).isSome then return none
      tys := tys.push ft
    return some { struct := S, ctor, levels := lvls, params := tw.getAppArgs,
                  projs := fields.map (S ++ ·), fieldTypes := tys }

/-- The mirror type `h₀ × (h₁ × … × hₙ₋₁)` of the costed field types `hs` (`h₀` for one
field). -/
def mirrorType (hs : Array Expr) : MetaM Expr := do
  let some last := hs.back? | throwError "derive_timed: internal: a mirror of no field"
  hs.pop.foldrM (fun h acc => mkAppM ``Prod #[h, acc]) last

/-- The mirror tuple of the costed field values `vs`. -/
def mirrorMk (vs : Array Expr) : MetaM Expr := do
  let some last := vs.back? | throwError "derive_timed: internal: a mirror of no field"
  vs.pop.foldrM (fun v acc => mkAppM ``Prod.mk #[v, acc]) last

/-- The component `i` of the mirror tuple `v` of `n` fields, reduced on a literal tuple. -/
def mirrorProj (n i : Nat) (v : Expr) : MetaM Expr := do
  let proj (fst : Bool) (v : Expr) : MetaM Expr := do
    if v.isAppOfArity ``Prod.mk 4 then return v.getArg! (if fst then 2 else 3)
    mkAppM (if fst then ``Prod.fst else ``Prod.snd) #[v]
  let mut cur := v
  for _ in [0:i] do cur ← proj false cur
  if i + 1 < n then proj true cur else return cur

/-- The costed type of a type `t` of data holding functions: a function `X → Y` with a
first-order domain becomes the costed closure `(X → Ŷ) × (X → ℕ)`, a pair the pair of the
costed types of its components; `none` when `t` holds no such function, whose costed type is
`t` itself. With `mirror := false` a structure is not mirrored: the result is `none` for a
type whose functions are all in fields of structures. -/
partial def hatTy? (t : Expr) (seen : List Name := []) (mirror : Bool := true) :
    MetaM (Option Expr) := do
  let t ← instantiateMVars t
  if ← isProp t then return none
  if ← isTypeFormerType t then return none
  if (← isClass? t).isSome then return none
  if (← treeTy? t).isSome then return none
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    let a := tw.getArg! 0
    let b := tw.getArg! 1
    let ha ← hatTy? a seen mirror
    let hb ← hatTy? b seen mirror
    if ha.isNone && hb.isNone then return none
    return some (← mkAppM ``Prod #[ha.getD a, hb.getD b])
  if tw.isAppOfArity ``Sum 2 then
    let a := tw.getArg! 0
    let b := tw.getArg! 1
    let ha ← hatTy? a seen mirror
    let hb ← hatTy? b seen mirror
    if ha.isNone && hb.isNone then return none
    return some (← mkAppM ``Sum #[ha.getD a, hb.getD b])
  if let some m ← mirrorStruct? tw then
    if seen.contains m.struct || !mirror then return none
    let hs ← m.fieldTypes.mapM (hatTy? · (m.struct :: seen))
    if hs.all (·.isNone) then return none
    return some (← mirrorType ((m.fieldTypes.zip hs).map fun (f, h) => h.getD f))
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

/-- `Sum.map` of `f` at the components of the sum `a ⊕ b` applied to `v`: with `f = epsE` from
the costed sum to `a ⊕ b`, with `f = iotaE` from `a ⊕ b` to the costed sum. -/
def sumMapE (a b v : Expr) (f : Expr → Expr → MetaM Expr) : MetaM Expr := do
  let vt ← whnfR (← inferType v)
  let side (i : Nat) (c : Expr) : MetaM Expr := do
    withLocalDeclD `x (vt.getArg! i) fun x => do mkLambdaFVars #[x] (← f c x)
  mkAppM ``Sum.map #[← side 0 a, ← side 1 b, v]

/-- The erasure `ε v : t` of the costed value `v` of type `hatTy? t`: the function of each
costed closure. -/
partial def epsE (t v : Expr) : MetaM Expr := do
  let some _ ← hatTy? t | return v
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    let a ← epsE (tw.getArg! 0) (← mkAppM ``Prod.fst #[v])
    let b ← epsE (tw.getArg! 1) (← mkAppM ``Prod.snd #[v])
    return ← mkAppM ``Prod.mk #[a, b]
  if tw.isAppOfArity ``Sum 2 then
    return ← sumMapE (tw.getArg! 0) (tw.getArg! 1) v epsE
  if let some m ← mirrorStruct? tw then
    let n := m.fieldTypes.size
    let mut fs := #[]
    for i in [0:n] do
      fs := fs.push (← epsE m.fieldTypes[i]! (← mirrorProj n i v))
    return mkAppN (mkConst m.ctor m.levels) (m.params ++ fs)
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
  if tw.isAppOfArity ``Sum 2 then
    return ← sumMapE (tw.getArg! 0) (tw.getArg! 1) v iotaE
  if let some m ← mirrorStruct? tw then
    let mut fs := #[]
    for i in [0:m.fieldTypes.size] do
      let pf := mkAppN (mkConst m.projs[i]! m.levels) (m.params.push v)
      fs := fs.push (← iotaE m.fieldTypes[i]! pf)
    return ← mirrorMk fs
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

/-- The components of the erasure `ε v : t` of the costed value `v` (`epsE`), each with the
component of `x : t` at the same position: the pairs `(vᵢ, xᵢ)` such that `ε v = x` gives
`vᵢ = xᵢ` by projections. A component is a first-order field (`vᵢ` a projection of `v`) or a
function whose results hold no function (`vᵢ` the function of a costed closure); the
components inside a sum or inside the results of a function are left out. -/
partial def epsLeaves (t v x : Expr) : MetaM (Array (Expr × Expr)) := do
  let some _ ← hatTy? t | return #[(v, x)]
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    let a ← epsLeaves (tw.getArg! 0) (← mkAppM ``Prod.fst #[v]) (← mkAppM ``Prod.fst #[x])
    let b ← epsLeaves (tw.getArg! 1) (← mkAppM ``Prod.snd #[v]) (← mkAppM ``Prod.snd #[x])
    return a ++ b
  if tw.isAppOfArity ``Sum 2 then return #[]
  if let some m ← mirrorStruct? tw then
    let n := m.fieldTypes.size
    let mut out := #[]
    for i in [0:n] do
      let xi := mkAppN (mkConst m.projs[i]! m.levels) (m.params.push x)
      out := out ++ (← epsLeaves m.fieldTypes[i]! (← mirrorProj n i v) xi)
    return out
  forallTelescope tw fun _ body => do
    if (← hatTy? body).isSome then return #[]
    return #[(← mkAppM ``Prod.fst #[v], x)]

/-- The costed value of `x : t` with its functions from `x` and their cost companions from the
costed value `c : hatTy? t`; its erasure reduces to `x` by projections. A sum inside `t` is
lifted by `ι`. -/
partial def refillE (t x c : Expr) : MetaM Expr := do
  let some _ ← hatTy? t | return x
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    let a ← refillE (tw.getArg! 0) (← mkAppM ``Prod.fst #[x]) (← mkAppM ``Prod.fst #[c])
    let b ← refillE (tw.getArg! 1) (← mkAppM ``Prod.snd #[x]) (← mkAppM ``Prod.snd #[c])
    return ← mkAppM ``Prod.mk #[a, b]
  if tw.isAppOfArity ``Sum 2 then return ← iotaE t x
  if let some m ← mirrorStruct? tw then
    let n := m.fieldTypes.size
    let mut fs := #[]
    for i in [0:n] do
      let pf := mkAppN (mkConst m.projs[i]! m.levels) (m.params.push x)
      fs := fs.push (← refillE m.fieldTypes[i]! pf (← mirrorProj n i c))
    return ← mirrorMk fs
  let comp ← mkAppM ``Prod.snd #[c]
  let fn ← mkAppM ``Prod.fst #[c]
  let f ← forallTelescope tw fun ys body => do
    if (← hatTy? body).isNone then return x
    mkLambdaFVars ys (← refillE body (mkAppN x ys).headBeta (mkAppN fn ys).headBeta)
  mkAppM ``Prod.mk #[f, comp]

/-- The fields of the pattern `p` of a discriminant with costed value `v`, each with the
costed value of its position in `v`: a field is the whole value, a component of a pair or of
a structure with a mirror is the component, and the component of `Sum.inl`/`Sum.inr` is read
by `Sum.elim`, with `ι` of the pattern in the other case. A field under any other constructor
is not found. -/
partial def patternHats (p v : Expr) : MetaM (Array (Expr × Expr)) := do
  let p := p.consumeMData
  if p.isFVar then return #[(p, v)]
  let args := p.getAppArgs
  let .const c _ := p.getAppFn | return #[]
  if c == ``Prod.mk && args.size == 4 then
    return (← patternHats args[2]! (← mkAppM ``Prod.fst #[v])) ++
      (← patternHats args[3]! (← mkAppM ``Prod.snd #[v]))
  if (c == ``Sum.inl || c == ``Sum.inr) && args.size == 3 then
    let vt ← whnfR (← inferType v)
    unless vt.isAppOfArity ``Sum 2 do return #[]
    let left := c == ``Sum.inl
    let pt := if left then args[0]! else args[1]!
    let dflt ← iotaE pt args[2]!
    let get ← withLocalDeclD `z (vt.getArg! (if left then 0 else 1)) fun z =>
      mkLambdaFVars #[z] z
    let other ← withLocalDeclD `z (vt.getArg! (if left then 1 else 0)) fun z =>
      mkLambdaFVars #[z] dflt
    let comp ← if left then mkAppM ``Sum.elim #[get, other, v]
      else mkAppM ``Sum.elim #[other, get, v]
    return ← patternHats args[2]! comp
  let some m ← mirrorStruct? (← whnfR (← inferType p)) | return #[]
  unless c == m.ctor && args.size == m.params.size + m.fieldTypes.size do return #[]
  let mut out := #[]
  for i in [0:m.fieldTypes.size] do
    out := out ++ (← patternHats args[m.params.size + i]! (← mirrorProj m.fieldTypes.size i v))
  return out

/-- The patterns of the alternative `i` of the match `app`, one for each discriminant, over the
fields `fs` of the alternative. -/
def altPatterns (app : MatcherApp) (i : Nat) (fs : Array Expr) : MetaM (Option (Array Expr)) := do
  let mty ← instantiateForall
    (← inferType (mkConst app.matcherName app.matcherLevels.toList)) app.params
  forallBoundedTelescope mty (some 1) fun _ rest => do
    let rest ← instantiateForall rest app.discrs
    forallBoundedTelescope rest (some app.alts.size) fun as _ => do
      let some a := as[i]? | return none
      forallBoundedTelescope (← inferType a) (some fs.size) fun gs body => do
        unless gs.size == fs.size do return none
        let pats := body.getAppArgs
        unless pats.size == app.discrs.size do return none
        return some (pats.map (·.replaceFVars gs fs))

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
    -- A structure binder keeps the convention of field paths: its function fields applied
    -- are priced by cost companions after the binders. So does a binder whose functions are
    -- all in fields of structures (a pair `R × W` of two structures).
    if ys.isEmpty && (← mirrorStruct? b).isSome then return .data
    if ys.isEmpty then
      return if (← hatTy? b (mirror := false)).isSome then .hat else .data
    return .fn

/-- Whether `e` is data: not a type, a proposition, a proof or an instance. -/
def isDataExpr (e : Expr) : MetaM Bool := do
  let t ← inferType e
  if ← isTypeFormerType t then return false
  if ← isProp t then return false
  if (← isClass? t).isSome then return false
  return true

/-- The recursor of `Bool` at a constant motive applied to its two minor premises and its
major premise, `Bool.rec f t b`, as the `if` on the major premise `if b = true then t else f`
(`boolRec_eq_ite`); `none` for any other expression. -/
def boolRecIte? (e : Expr) : MetaM (Option Expr) := do
  unless e.isAppOfArity ``Bool.rec 4 do return none
  let args := e.getAppArgs
  let .lam _ _ body _ := args[0]! | return none
  if body.hasLooseBVars then return none
  let some u := e.getAppFn.constLevels!.head? | return none
  let c ← mkEq args[3]! (mkConst ``Bool.true)
  let inst := mkApp2 (mkConst ``instDecidableEqBool) args[3]! (mkConst ``Bool.true)
  return some (mkApp5 (mkConst ``ite [u]) body c inst args[2]! args[1]!)

/-- Whether `t` is a computation type `SPComp α`. -/
def isSPCompType (t : Expr) : MetaM Bool := do
  return (← whnfR t).isAppOfArity `CatCrypt.Core.SPComp 1

/-- Whether `v` is a projection path of a local: a local, or a structure projection of a
projection path (`kit.hkdf`, `Z.input.1`). -/
partial def isLocalProjPath (v : Expr) : MetaM Bool := do
  match v.consumeMData with
  | .fvar _ => return true
  | .proj _ _ s => isLocalProjPath s
  | v' =>
    let .const m _ := v'.getAppFn | return false
    let some info ← getProjectionFnInfo? m | return false
    unless v'.getAppNumArgs == info.numParams + 1 do return false
    isLocalProjPath v'.appArg!

/-- Whether `let x : t := v` is kept as a `let`, so that the cost of `v` is charged once: `v`
is first-order data that is not a variable, a literal, a constant, a closure or a projection
path of a local. Any other `let` is substituted into its body. -/
def keepsLet (t v : Expr) : MetaM Bool := do
  match v.consumeMData with
  | .fvar _ | .lit _ | .const .. | .lam .. | .sort _ | .forallE .. => return false
  | _ => pure ()
  -- A field path of a local (`kit.hkdf`) costs nothing: substituted, so that the fields
  -- applied through it are fields of a field path.
  if ← isLocalProjPath v then return false
  if ← isProp t then return false
  if ← isTypeFormerType t then return false
  if (← isClass? t).isSome then return false
  if ← isSPCompType t then return false
  if (← treeTy? t).isSome then return false
  if (← whnfR t).isForall then return false
  -- A structure value stays a `let`; its costed value is read through the `let` (`tv`).
  if (← mirrorStruct? (← whnfR t)).isSome then return true
  if (← hatTy? t).isSome then return false
  return true

/-- A `let` applied to arguments with the application pushed into its body,
`(let x := v; f) a ⇝ let x := v; f a` (beta-reduced, through nested `let`s), so that the
`let` is priced once by the rule for `let`. Any other term is returned unchanged. -/
partial def pushLetApp (e : Expr) : Expr :=
  let args := e.getAppArgs
  if args.isEmpty then e else
  match e.getAppFn.consumeMData with
  | .letE n t v b nd =>
    let args' := args.map (·.liftLooseBVars 0 1)
    .letE n t v (pushLetApp (mkAppN b args').headBeta) nd
  | _ => e

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

/-- The erasure lemma of the tree kind `k` for the matcher `M` (`erase_snd_ite` for a
`match`): for every instance of the parameters, discriminants and alternatives,
`(M ps (fun _ => ℕ × k.timed ts) ds alts).2.erase = M ps (fun _ => k.tree ts) ds
  (fun fs => (alts fs).2.erase)`,
proved by case analysis on the discriminants. Its name is `M.erase_snd_<kind>`; it is added
once per matcher and kind. Returns `none` when `M` does not eliminate into an arbitrary
universe or the case analysis does not close the equation. -/
def matchEraseLemma (k : TreeKind) (M : Name) : TermElabM (Option Name) := do
  let name := M ++ Name.mkSimple ("erase_snd_" ++ k.noun.replace " " "_")
  if (← getEnv).contains name then return some name
  let some mi ← getMatcherInfo? M | return none
  let some uPos := mi.uElimPos? | return none
  let cinfo ← getConstInfo M
  let lps := cinfo.levelParams
  let stmt? ← forallTelescope (← inferType (mkConst k.tree)) fun tps _ => do
    let T1 ← mkAppM ``Prod #[mkConst ``Nat, mkAppN (mkConst k.timed) tps]
    let T2 := mkAppN (mkConst k.tree) tps
    let lvls := lps.map mkLevelParam
    let M1 := Lean.mkConst M (lvls.set uPos (← getLevel T1))
    let M2 := Lean.mkConst M (lvls.set uPos (← getLevel T2))
    let ty1 ← inferType M1
    forallBoundedTelescope ty1 mi.numParams fun ps rest => do
      let .forallE _ motTy _ _ := rest | return none
      let mot1 ← forallTelescope motTy fun xs _ => mkLambdaFVars xs T1
      let mot2 ← forallTelescope motTy fun xs _ => mkLambdaFVars xs T2
      let rest1 ← instantiateForall ty1 (ps.push mot1)
      forallBoundedTelescope rest1 mi.numDiscrs fun ds rest2 => do
        forallBoundedTelescope rest2 mi.numAlts fun alts _ => do
          let erase (v : Expr) : MetaM Expr := do
            return mkAppN (mkConst k.erase) (tps.push (← mkAppM ``Prod.snd #[v]))
          let lhs ← erase (mkAppN M1 (ps ++ #[mot1] ++ ds ++ alts))
          let alts2 ← alts.mapM fun a => do
            forallTelescope (← inferType a) fun fs _ => do
              mkLambdaFVars fs (← erase (mkAppN a fs))
          let rhs := mkAppN M2 (ps ++ #[mot2] ++ ds ++ alts2)
          let eq ← mkEq lhs rhs
          return some (← Core.betaReduce (← mkForallFVars (tps ++ ps ++ ds ++ alts) eq))
  let some stmt := stmt? | return none
  let s ← saveState
  try
    let mv ← mkFreshExprMVar stmt
    let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic|
      (intros; split <;> (try rfl) <;> (split <;> first | rfl | (exfalso; simp_all))))))
    unless gs.isEmpty do
      s.restore
      return none
    let proof ← instantiateMVars mv
    if proof.hasSorry || proof.hasMVar then
      s.restore
      return none
    let thm : TheoremVal :=
      { name := name, levelParams := lps.eraseIdx uPos, type := stmt, value := proof }
    addDecl (Declaration.thmDecl thm)
    return some name
  catch _ =>
    s.restore
    return none

/-- The bind of the tree kind `k`: its combinator named `bind`. -/
def kindBind? (k : TreeKind) : Option Name :=
  (k.combinators.find? fun cb => match cb.src with
    | .str _ "bind" => true
    | _ => false).map (·.src)

/-- The bind lemma `M.bind_<kind>` of the matcher `M` for trees of kind `k`: the bind of a match
whose alternatives are trees is the match of the binds of the alternatives, stated at every
continuation `f`. It is generated and proved by case analysis on its first use, and is `none`
when the matcher has no universe parameter for its motive or the proof fails. -/
def matchBindLemma (k : TreeKind) (M : Name) : TermElabM (Option Name) := do
  let name := M ++ Name.mkSimple ("bind_" ++ k.noun.replace " " "_")
  if (← getEnv).contains name then return some name
  let some bindC := kindBind? k | return none
  let some mi ← getMatcherInfo? M | return none
  let some uPos := mi.uElimPos? | return none
  let cinfo ← getConstInfo M
  let lps := cinfo.levelParams
  let stmt? ← forallTelescope (← inferType (mkConst k.tree)) fun tps _ => do
    let some α := tps.back? | return none
    withLocalDeclD `β (← inferType α) fun β => do
      let T1 := mkAppN (mkConst k.tree) tps
      let T2 := mkAppN (mkConst k.tree) (tps.pop.push β)
      withLocalDeclD `f (← mkArrow α T2) fun f => do
        let lvls := lps.map mkLevelParam
        let M1 := Lean.mkConst M (lvls.set uPos (← getLevel T1))
        let M2 := Lean.mkConst M (lvls.set uPos (← getLevel T2))
        let ty1 ← inferType M1
        forallBoundedTelescope ty1 mi.numParams fun ps rest => do
          let .forallE _ motTy _ _ := rest | return none
          let mot1 ← forallTelescope motTy fun xs _ => mkLambdaFVars xs T1
          let mot2 ← forallTelescope motTy fun xs _ => mkLambdaFVars xs T2
          let rest1 ← instantiateForall ty1 (ps.push mot1)
          forallBoundedTelescope rest1 mi.numDiscrs fun ds rest2 => do
            forallBoundedTelescope rest2 mi.numAlts fun alts _ => do
              let lhs ← mkAppM bindC #[mkAppN M1 (ps ++ #[mot1] ++ ds ++ alts), f]
              let alts2 ← alts.mapM fun a => do
                forallTelescope (← inferType a) fun fs _ => do
                  mkLambdaFVars fs (← mkAppM bindC #[mkAppN a fs, f])
              let rhs := mkAppN M2 (ps ++ #[mot2] ++ ds ++ alts2)
              let eq ← mkEq lhs rhs
              return some (← Core.betaReduce
                (← mkForallFVars (tps ++ #[β, f] ++ ps ++ ds ++ alts) eq))
  let some stmt := stmt? | return none
  let s ← saveState
  try
    let mv ← mkFreshExprMVar stmt
    let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic|
      (intros; split <;> (try rfl) <;> (split <;> first | rfl | (exfalso; simp_all))))))
    unless gs.isEmpty do
      s.restore
      return none
    let proof ← instantiateMVars mv
    if proof.hasSorry || proof.hasMVar then
      s.restore
      return none
    let thm : TheoremVal :=
      { name := name, levelParams := lps.eraseIdx uPos, type := stmt, value := proof }
    addDecl (Declaration.thmDecl thm)
    return some name
  catch _ =>
    s.restore
    return none

/-- Whether the call `e` of the tree-valued definition `c` is unfolded rather than translated
to a call of a costed form: `c` is a non-recursive definition that is not a matcher, the result
type of the tree at the call holds functions (`hatTy?`), and the result type of the tree in the
declared type of `c` does not (a callee generic in its state type, called at a state holding
functions). -/
def unfoldsGenericCall (c : Name) (e : Expr) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo dv) := env.find? c | return false
  if (Structural.eqnInfoExt.find? env c).isSome || (WF.eqnInfoExt.find? env c).isSome then
    return false
  if isMatcherCore env c then return false
  let some Tc ← treeTy? (← inferType e) | return false
  if (← hatTy? Tc.result).isNone then return false
  forallTelescope dv.type fun _ b => do
    let some Tg ← treeTy? b | return false
    return (← hatTy? Tg.result).isNone

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
  if let .proj S i _ := p then
    -- A data path: the costed value of the field, `inputHat` for `Z.input`.
    if let some info := getStructureInfo? (← getEnv) S then
      if let some fl := info.fieldNames[i]? then
        return Name.mkSimple (fl.toString ++ "Hat")
    return `fieldHat
  match ← last p with
  | some fl => return Name.mkSimple (fl ++ "Cost")
  | none => return `fieldCost

/-- Whether a value of type `t` is data holding functions that is not itself a function: its
costed value (`hatTy?`) is a tuple that contains costed closures. -/
def holdsFnData (t : Expr) : MetaM Bool := do
  if (← whnfR t).isForall then return false
  return (← hatTy? t).isSome

/-- Whether the field path `p` is a data path: a primitive projection whose type holds
functions and is not a function. -/
def isDataPath (p : Expr) : MetaM Bool := do
  unless p.isProj do return false
  holdsFnData (← inferType p)

/-- The type of the companion of the field path `p`: the costed type `hatTy? t` of a data path
of type `t`, and the cost companion type `X → ℕ` of a function field of type `X → Y`. -/
def pathCompanionType (p : Expr) : MetaM Expr := do
  let t ← inferType p
  if ← isDataPath p then
    let some ht ← hatTy? t | fail m!"internal: `{t}` holds no function"
    return ht
  companionType t

/-- Bind a companion for each field path of `ps` (`pathCompanionType`: a cost companion of an
applied field, the costed value of a data path) and continue with the pairs of the path and
its companion. -/
def withFieldCosts {β : Type} (ps : Array Expr) (k : Array (Expr × Expr) → TermElabM β) :
    TermElabM β :=
  go 0 #[]
where
  go (i : Nat) (acc : Array (Expr × Expr)) : TermElabM β := do
    if h : i < ps.size then
      let p := ps[i]
      let n ← fieldCostName p
      withLocalDeclD n (← pathCompanionType p) fun cc =>
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

/-- The equations among the conjuncts of the proof `pf` of `ty`. -/
partial def conjEqns (pf ty : Expr) : MetaM (Array Expr) := do
  -- At default transparency, so that a match of the hypothesis on a constructor reduces.
  let ty ← whnf (← instantiateMVars ty)
  if ty.isAppOfArity ``And 2 then
    return (← conjEqns (mkApp3 (mkConst ``And.left) (ty.getArg! 0) (ty.getArg! 1) pf)
        (ty.getArg! 0)) ++
      (← conjEqns (mkApp3 (mkConst ``And.right) (ty.getArg! 0) (ty.getArg! 1) pf) (ty.getArg! 1))
  if ty.isAppOfArity ``Eq 3 then return #[pf]
  return #[]

/-- Rewrite the goal `g` from right to left with each hypothesis (or conjunct of one) that is
an equation whose right side is a call of `c`: the induction hypotheses of an erasure theorem
`… = c ys`. -/
def rewriteRecHyps (c : Name) (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  let mut used : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    for pf in ← conjEqns d.toExpr d.type do
      let some (ty, lhs, rhs) := (← instantiateMVars (← inferType pf)).eq? | continue
      unless rhs.isAppOf c do continue
      let gt ← instantiateMVars (← g.getType)
      unless (gt.find? (· == rhs)).isSome do continue
      -- The occurrences of `rhs` replaced by `lhs`, by congruence with the motive that
      -- abstracts them.
      let motive ← withLocalDeclD `z ty fun z => do
        mkLambdaFVars #[z] (gt.replace fun s => if s == rhs then some z else none)
      unless ← isTypeCorrect motive do continue
      let gNew := (mkApp motive lhs).headBeta
      g ← g.replaceTargetEq gNew (← mkEqSymm (← mkCongrArg motive pf))
      used := used.push d.fvarId
  -- A used hypothesis is cleared, so that a later `simp [*]` does not rewrite back.
  for h in used do g ← g.tryClear h
  return g

/-- The step of the projection `e = s.i` of the structure `S`, a primitive projection or a
projection function (not a class method) applied to its parameters and to `s`: `(S, i, s)`. -/
def projStep? (e : Expr) : MetaM (Option (Name × Nat × Expr)) := do
  match e.consumeMData with
  | .proj S i s => return some (S, i, s)
  | e' =>
    let .const m _ := e'.getAppFn | return none
    let some info ← getProjectionFnInfo? m | return none
    if info.fromClass then return none
    unless e'.getAppNumArgs == info.numParams + 1 do return none
    return some (m.getPrefix, info.i, e'.appArg!)

/-- The projection path `e` with each step written as a primitive projection: the key of a
data path in `Ctx.fields`. -/
partial def canonPath (e : Expr) : MetaM Expr := do
  match ← projStep? e with
  | some (S, i, s) => return .proj S i (← canonPath s)
  | none => return e.consumeMData

/-- The start of the projection path `e`: the term whose projections it takes. -/
partial def pathRoot (e : Expr) : MetaM Expr := do
  match ← projStep? e with
  | some (_, _, s) => pathRoot s
  | none => return e.consumeMData

/-- The component `i` of the costed value `v` of a structure `s` of the structure `S`: a
component of a pair, or of the mirror tuple of a structure holding functions. -/
def projHat? (S : Name) (i : Nat) (s v : Expr) : MetaM (Option Expr) := do
  if S == ``Prod then
    if v.isAppOfArity ``Prod.mk 4 then return some (v.getArg! (if i == 0 then 2 else 3))
    return some (← mkAppM (if i == 0 then ``Prod.fst else ``Prod.snd) #[v])
  let some m ← mirrorStruct? (← whnfR (← inferType s)) | return none
  unless m.struct == S do return none
  return some (← mirrorProj m.fieldTypes.size i v)

/-- The costed value of the projection path `e` below a binder of the reduction that has no
costed value of its own (a structure binder with the convention of field paths, such as an
environment `Z`). The shortest prefix `p` of `e` that is data holding functions and not a
function (the data path `Z.input` of `Z : Env (Unit × S) β`) has as costed value
`refillE t p p̂`, whose functions are those of `p` and whose cost companions are read from the
binder `p̂ : hatTy? t` after the binders of the reduction (`Ctx.fields`, keyed by
`canonPath p`); the costed value of `e` is its component. With `record`, in the first pass, a
data path without a binder is recorded (`fieldRec?`), with its functions as tables (`ι`). -/
partial def pathHat? (ctx : Ctx) (e : Expr) (record : Bool) : MetaM (Option Expr) := do
  let some (S, i, s) ← projStep? e | return none
  let s := s.consumeMData
  if !s.isFVar then
    if let some sv ← pathHat? ctx s record then
      return ← projHat? S i s sv
  -- `s` is a path that holds no function in its prefixes: `e` is a data path when `s` starts
  -- at a binder of the reduction without a costed value.
  unless ← isFieldPath ctx s do return none
  if let .fvar id ← pathRoot s then
    if (ctx.locals.get? id).isSome then return none
  let t ← inferType e
  unless ← holdsFnData t do return none
  let key ← canonPath e
  if let some (_, cc) := ctx.fields.find? (·.1 == key) then
    return some (← refillE t key cc)
  if record then
    if let some r := ctx.fieldRec? then
      unless (← r.get).contains key do r.modify (·.push key)
      return some (← iotaE t key)
  return none

/-- The costed value of the field path `v : t` (a binder of the reduction holding functions
without a costed value of its own, such as a handler state, or a field of one): `ι v`, except
that a function field `S.f v` with a cost companion `cc` (`Ctx.fields`) is the costed closure
`(fun ys => v.f ys, cc)`, and a data path with a costed value (`pathHat?`) is that value. With
a reference `fieldRec?` (the first pass), a function field without a companion is recorded, so
that the second pass gives it one. -/
partial def iotaPathE (ctx : Ctx) (t v : Expr) : TermElabM Expr := do
  let some _ ← hatTy? t | return v
  let tw ← whnfR t
  if tw.isForall then
    let found? ← match ctx.fields.find? (·.1 == v) with
      | some (_, cc) => pure (some cc)
      | none => do
        let key ← canonPath v
        pure ((ctx.fields.find? fun (p, _) => p == key).map (·.2))
    let some cc := found?
      | if let some r := ctx.fieldRec? then
          if !v.hasLooseBVars && v.getAppFn.isConst && (← isFieldPath ctx v) then
            unless (← r.get).contains v do r.modify (·.push v)
        return ← iotaE t v
    let f ← forallTelescope tw fun ys body => do
      mkLambdaFVars ys (← iotaE body (mkAppN v ys).headBeta)
    return ← mkAppM ``Prod.mk #[f, cc]
  if let some h ← pathHat? ctx v (record := true) then return h
  if tw.isAppOfArity ``Prod 2 then
    let a ← iotaPathE ctx (tw.getArg! 0) (← mkAppM ``Prod.fst #[v])
    let b ← iotaPathE ctx (tw.getArg! 1) (← mkAppM ``Prod.snd #[v])
    return ← mkAppM ``Prod.mk #[a, b]
  if let some m ← mirrorStruct? tw then
    let mut fs := #[]
    for i in [0:m.fieldTypes.size] do
      let pf := mkAppN (mkConst m.projs[i]! m.levels) (m.params.push v)
      fs := fs.push (← iotaPathE ctx m.fieldTypes[i]! pf)
    return ← mirrorMk fs
  iotaE t v

/-- Whether `p` is a function field `S.f ps s` of a structure value: `s` is not a field path of
the binders of the reduction, and `s`, or the value of the `let` that binds it, is a
constructor application up to reducible unfolding. The cost companion of such a field is the
cost of the field applied, read through the structure's value (`companionOf`). A field of a
structure computed by a definition, `(kit.aead iv).enc`, keeps its own cost companion (the rule
for computed structures), since unfolding the definition would price its whole body. -/
def isValueField (ctx : Ctx) (p : Expr) : MetaM Bool := do
  if p.hasLooseBVars then return false
  unless (← whnfR (← inferType p)).isForall do return false
  let .const m _ := p.getAppFn | return false
  let some info ← getProjectionFnInfo? m | return false
  if info.fromClass then return false
  unless p.getAppNumArgs == info.numParams + 1 do return false
  let s := p.appArg!.consumeMData
  if ← isFieldPath ctx s then return false
  let sv ← match s with
    | .fvar id => do
      match ← id.getValue? with
      | some v => pure v
      | none => pure s
    | _ => pure s
  return (← isConstructorApp? (← whnfR sv)).isSome

/-- The projection path `e` with its step to the structure argument `s` replaced by `s'`. -/
def replaceProjArg (e s' : Expr) : Expr :=
  match e.consumeMData with
  | .proj S j _ => .proj S j s'
  | e' => mkApp e'.appFn! s'

/-- The structure term `s` with every projection of a constructor application reduced, from the
innermost structure argument out: `{ cfg := s.cfg, … }.cfg` is `s.cfg`. -/
partial def reduceStructArg (s : Expr) : MetaM Expr := do
  let some (_, i, s₀) ← projStep? s | return s
  let s₀' ← reduceStructArg s₀
  if let some v ← projectCore? (← whnfR s₀') i then
    return ← reduceStructArg v
  if s₀' == s₀.consumeMData then return s
  return replaceProjArg s s₀'

/-- The field `S.f s` with its structure argument reduced by `reduceStructArg`:
`{ cfg := s.cfg, … }.cfg.env` is `s.cfg.env`. The outermost projection is kept, so that a field
of a constructor application (`Corr.leaks ⟨f, g⟩`) stays a field of a structure value. -/
def reduceFieldArg (e : Expr) : MetaM Expr := do
  if e.hasLooseBVars then return e
  let some (_, _, s) ← projStep? e | return e
  let s' ← reduceStructArg s
  if s' == s.consumeMData then return e
  return replaceProjArg e s'

/-- The key of the field path `p = S.f ps s` of a callee at a structure `s` computed by a
definition: `s`, or the value of the `let` that binds it, is an application `g as bs` of a
definition `g` that is not a projection, whose value is not a constructor application up to
reducible unfolding, where `as` are the leading implicit and instance arguments of `g` and `bs`
the remaining arguments, none empty. The key is `fun xs => S.f ps (g as xs)`, returned with
`bs`; the caller passes the cost companion of the key applied to `bs`, as for a field of a
computed structure (`computedFieldKey?`). -/
def computedPathKey? (ctx : Ctx) (p : Expr) : MetaM (Option (Expr × Array Expr)) := do
  if p.hasLooseBVars || p.isLambda then return none
  let some (_, _, s₀) ← projStep? p | return none
  let mut s := s₀.consumeMData
  if ← isFieldPath ctx s then return none
  -- The value of the `let` that binds the structure, through nested `let`s.
  for _ in [0:8] do
    let .fvar id := s | break
    let some v ← id.getValue? | break
    s := v.consumeMData
  if (← isConstructorApp? (← whnfR s)).isSome then return none
  let .const g lvls := s.getAppFn | return none
  let some (.defnInfo _) := (← getEnv).find? g | return none
  if (← getProjectionFnInfo? g).isSome then return none
  let sargs := s.getAppArgs
  let k ← forallTelescope (← inferType (mkConst g lvls)) fun ys _ => do
    let mut k := 0
    for y in ys do
      if (← y.fvarId!.getBinderInfo).isExplicit then break
      k := k + 1
    return k
  if k ≥ sargs.size then return none
  let gp := mkAppN (mkConst g lvls) (sargs.extract 0 k)
  let bs := sargs.extract k sargs.size
  if gp.hasLooseBVars then return none
  forallBoundedTelescope (← whnfR (← inferType gp)) bs.size fun xs _ => do
    unless xs.size == bs.size do return none
    let key ← mkLambdaFVars xs (replaceProjArg p (mkAppN gp xs))
    unless ← isTypeCorrect key do return none
    return some (key, bs)

/-- The cost `if c then a else b`, which is `a` when the two branch costs are the same term. -/
def iteNatE (c inst a b : Expr) : Expr :=
  if a == b then a else mkApp5 (mkConst ``ite [Level.one]) (mkConst ``Nat) c inst a b

/-- The common cost of the alternatives of the match `e`, when every alternative is a constant
function of its pattern variables and all have the same value. -/
def constAlts? (e : Expr) : MetaM (Option Expr) := do
  let some app ← matchMatcherApp? e | return none
  let mut v? : Option Expr := none
  for alt in app.alts do
    let b? ← lambdaTelescope alt fun xs b => pure <|
      if b.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then none else some b
    let some b := b? | return none
    match v? with
    | none => v? := some b
    | some v => unless v == b do return none
  return v?

/-- Close the goal `g` by rewriting it from right to left with a case hypothesis `d = C as`
(a constructor application, as `split` introduces) and `rfl`: the structure
`{ cur := k + 1, env := s.cfg.env }` that the hypothesis `s.cfg.cur = k + 1` produced from the
eta expansion of `s.cfg` becomes that eta expansion again, which `rfl` closes. Each case
hypothesis is tried alone; the goal is unchanged when none closes it. -/
def closeByCaseHypsRev (g : MVarId) : MetaM Bool := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, _, rhs) := (← instantiateMVars d.type).eq? | continue
    unless (← isConstructorApp? rhs).isSome do continue
    let s ← saveState
    try
      let r ← g.rewrite (← g.getType) (← mkEqSymm d.toExpr)
      unless r.mvarIds.isEmpty do throwError "side goals"
      let g' ← g.replaceTargetEq r.eNew r.eqProof
      g'.refl
      return true
    catch _ => s.restore
  return false

mutual

/-- The cost of evaluating the data term `e`. -/
partial def costOf (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let e := pushLetApp e.consumeMData.headBeta
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
of a path, an application of a costed closure whose result holds functions, or a projection
path of a binder below a data path (`pathHat?`, which records the data path with `record`). -/
partial def hatOf? (ctx : Ctx) (e : Expr) (record : Bool := false) :
    TermElabM (Option Expr) := do
  let e := e.consumeMData
  if let some v ← pathHat? ctx e record then return some v
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
costed value of the result. A partial application (fewer arguments than the companion takes)
costs its arguments and is the costed closure of the remaining arguments. -/
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
    if rest.size < k then
      -- A partial application: the costed closure of the remaining arguments, whose function
      -- and companion are those of `cur` at the arguments given, evaluated when it is built.
      let fn ← projE true cur
      let cp ← projE false cur
      let r ← forallBoundedTelescope (← whnfR (← inferType (mkAppN fn rest)))
        (some (k - rest.size)) fun zs _ => do
          let f ← mkLambdaFVars zs (mkAppN (mkAppN fn rest) zs).headBeta
          let c ← mkLambdaFVars zs (mkAppN (mkAppN cp rest) zs).headBeta
          mkAppM ``Prod.mk #[f, c]
      return (add cost (← argsCost ctx rest), r)
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
  let e := pushLetApp e.consumeMData.headBeta
  let t ← inferType e
  let some ht ← hatTy? t | return (← costOf ctx e, e)
  if let some v ← hatOf? ctx e (record := true) then return (← costOf ctx e, v)
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
  | .fvar id =>
    -- A `let` of a structure: its costed value is that of the value, whose cost the `let`
    -- charged. A binder of the reduction (a structure with the convention of field paths)
    -- keeps the cost companions of its function fields (`iotaPathE`). Any other local holding
    -- functions without a costed value is a table (`ι`).
    if let some v ← id.getValue? then return (natE 0, (← tv ctx v).2)
    if ← isFieldPath ctx e then return (natE 0, ← iotaPathE ctx t e)
    return (natE 0, ← iotaE t e)
  | .proj S i s =>
    -- A component of a pair holding functions: the component of its costed value.
    if S == ``Prod then
      let (cs, vs) ← tv ctx s
      return (cs, ← projE (i == 0) vs)
    let some m ← mirrorStruct? (← whnfR (← inferType s))
      | fail m!"a function bound in data: the projection `{e}` has no costed form"
    unless m.struct == S do fail m!"internal: the projection `{e}`"
    let (cs, vs) ← tv ctx s
    return (cs, ← mirrorProj m.fieldTypes.size i vs)
  | .app .. | .const .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    -- A sum holding functions: the costed value of the component.
    if (f.isConstOf ``Sum.inl || f.isConstOf ``Sum.inr) && args.size == 3 then
      let (ca, va) ← tv ctx args[2]!
      let ha := (← hatTy? args[0]!).getD args[0]!
      let hb := (← hatTy? args[1]!).getD args[1]!
      let .const n lvls := f | fail m!"internal: `{e}`"
      let lvls' ← [ha, hb].mapM fun x => (getDecLevel x : MetaM Level)
      unless lvls.length == 2 do fail m!"internal: `{e}`"
      return (ca, mkAppN (mkConst n lvls') #[ha, hb, va])
    if let .const fc _ := f then
      if let some m ← mirrorStruct? tw then
        -- A structure holding functions built by its constructor: the mirror tuple of the
        -- costed values of its fields.
        if fc == m.ctor && args.size == m.params.size + m.fieldTypes.size then
          let mut cs := #[]
          let mut vs := #[]
          for a in args.extract m.params.size args.size do
            let (c, v) ← tv ctx a
            cs := cs.push c
            vs := vs.push v
          return (sum cs, ← mirrorMk vs)
      -- A field of a structure holding functions: the component of its costed value.
      if let some info ← getProjectionFnInfo? fc then
        if !info.fromClass && args.size == info.numParams + 1 then
          let s := args[info.numParams]!
          if let some m ← mirrorStruct? (← whnfR (← inferType s)) then
            if let some i := m.projs.idxOf? fc then
              let (cs, vs) ← tv ctx s
              return (cs, ← mirrorProj m.fieldTypes.size i vs)
    -- A call of a local function with a cost companion whose result holds functions: the
    -- functions of the result are tables (`ι`).
    if let .fvar id := f then
      if let some { kind := .fn, companion? := some _, .. } := ctx.locals.get? id then
        unless tw.isForall do return (← costOf ctx e, ← iotaE t e)
    if f.isConstOf ``Prod.mk && args.size == 4 then
      let (ca, va) ← tv ctx args[2]!
      let (cb, vb) ← tv ctx args[3]!
      return (add ca cb, ← mkAppM ``Prod.mk #[va, vb])
    if let some e' ← boolRecIte? e then return ← tv ctx e'
    if f.isConstOf ``ite && args.size == 5 then
      let (ca, va) ← tv ctx args[3]!
      let (cb, vb) ← tv ctx args[4]!
      let lvl ← getLevel ht
      return (add (natE 1) (add (← propCost ctx args[1]!)
          (iteNatE args[1]! args[2]! ca cb)),
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
    let env ← getEnv
    -- A match whose matcher is compiled to a recursor, a `casesOn` or a sparse `casesOn` (a
    -- match with a wildcard arm, whose catch-all alternative is one branch shared by the
    -- constructors it covers; a definition by cases unfolds to its matcher): the match of the
    -- costed values of the branches, priced as a data-valued match. A matcher compiled to `if`s
    -- on decidable equalities is unfolded below.
    if let some app ← matchMatcherApp? e then
      let byRec := match env.find? app.matcherName with
        | some (.defnInfo mi) => (mi.value.find? fun s => match s with
            | .const n _ => isCasesOnLike env n || isRecCore env n
            | _ => false).isSome
        | _ => false
      if byRec then
        let (v, _) ← mapMatch ctx e ht (fun ctx b => return (← tv ctx b).2)
          (some fun _ => pure ht)
        return (← costMatch ctx e, v)
    let .const c lvls := f | fail m!"a function bound in data: the value `{e}` of type `{t}` \
      has no costed form"
    let some (.defnInfo dv) := env.find? c | fail m!"a function bound in data: the value `{e}` \
      of type `{t}` is not a definition to unfold"
    if (Structural.eqnInfoExt.find? env c).isSome || (WF.eqnInfoExt.find? env c).isSome then
      -- A recursive data function whose result holds functions: the call of its costed value
      -- `c.timed`, derived by its recursion (`deriveHatValue`), at the costed values of the
      -- arguments, priced by the cost of `c`. A recursive call in the derivation of `c.timed`
      -- is a call of the local standing for it; its cost is not used.
      let selfCall := ctx.selfHat?.any (·.1 == c)
      let target ← match ctx.selfHat? with
        | some (self, rec) => if self == c then pure rec else ensureHat ctx c f
        | none => ensureHat ctx c f
      let out ← hatArgs ctx f args
      let arity ← forallTelescope (← inferType target) fun ys _ => pure ys.size
      unless out.size == arity do
        fail m!"the recursive `{c}` returns functions and is applied to {args.size} arguments, \
          not to all binders of its costed value"
      let cost ← if selfCall then pure (natE 0) else costOf ctx e
      return (cost, mkAppN target out)
    if ctx.depth ≥ (← maxDepth) then
      fail m!"needs a registered primitive: `{c}` unfolds too deep"
    unless lvls.length == dv.levelParams.length do fail m!"`{c}` does not unfold"
    let e' ← bindArgsShared (dv.value.instantiateLevelParams dv.levelParams lvls) args
    if let some r := ctx.unfolded? then
      unless isMatcherCore env c do
        let headed ← lambdaTelescope dv.value fun _ b =>
          pure (isCaseHead env (letBody b).getAppFn.constName)
        if headed then r.modify fun a => if a.contains c then a else a.push c
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
      else
        let now := args.extract 0 arity
        let call := add (natE 1) (add (mkAppN c now) (← argsCost ctx now))
        if args.size == arity then return call
        -- A result that is a function under a non-reducible name (`SPComp α`, a function of
        -- the heap): the result is a table, and its application to the remaining arguments
        -- costs one plus their costs.
        let rest := args.extract arity args.size
        return add call (add (natE 1) (← argsCost ctx rest))
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
  if let some (_, sc) := ctx.selfCosts.find? (·.1 == c) then
    return add (natE 1) (add (mkAppN sc (← costArgs ctx f args)) (← argsCost ctx args))
  if env.contains reg then
    let regArgs ← costArgs ctx f args
    let regE ← mkAppOptM reg (regArgs.map some)
    -- A derived cost that takes the cost companions of field paths of `c`'s binders: the
    -- caller passes its companions for the same paths at the arguments of the call.
    let extra ← forallTelescope (← inferType regE) fun ys _ => pure ys.size
    let mut fieldArgs := #[]
    if extra > 0 then
      -- In the first pass, every path without a companion is recorded before the call is
      -- priced without its field costs.
      let mut missing := false
      for p in ← calleeFieldPaths c f.constLevels! args do
        let p ← reduceFieldArg p
        -- The key of a field of a structure computed by a definition, for a path that is not a
        -- field path of the binders (those keep their own companions).
        let ck? ← if p.isLambda || (p.isApp && (← isFieldPath ctx p.appArg!)) then pure none
          else computedPathKey? ctx p
        if let some (_, cc) := ctx.fields.find? (·.1 == p) then
          fieldArgs := fieldArgs.push cc
        else if let some (_, cc) := ctx.fields.find? (·.1 == (← canonPath p)) then
          fieldArgs := fieldArgs.push cc
        else if ← isValueField ctx p then
          -- A field of a structure value: priced at the structure's value.
          fieldArgs := fieldArgs.push (← companionOf ctx p)
        else if let some (key, bs) := ck? then
          -- A field of a structure computed by a definition: the companion of the key,
          -- applied to the arguments that compute the structure.
          if let some (_, cc) := ctx.fields.find? (·.1 == key) then
            fieldArgs := fieldArgs.push (mkAppN cc bs)
          else if let some r := ctx.fieldRec? then
            unless (← r.get).contains key do r.modify (·.push key)
            missing := true
          else
            fail m!"the cost `{reg}` takes the cost of the field `{p}`, whose key `{key}` has \
              no cost companion"
        else if let some r := ctx.fieldRec? then
          if !p.hasLooseBVars && (p.isLambda || (← isFieldPath ctx p.appArg!)) then
            unless (← r.get).contains p do r.modify (·.push p)
          missing := true
        else
          fail m!"the cost `{reg}` takes the cost of the field `{p}`, which is not a field of a \
            binder of the reduction"
      if missing then return add (natE 1) (← argsCost ctx args)
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
  if let some e' ← boolRecIte? e then return ← costOf ctx e'
  if c == ``ite && args.size == 5 then
    return add (natE 1) (add (← propCost ctx args[1]!)
      (iteNatE args[1]! args[2]! (← costOf ctx args[3]!) (← costOf ctx args[4]!)))
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
      -- A field below a projection of a constructor application (`{ cfg := s.cfg, … }.cfg.env`):
      -- the structure is priced, and the field is priced at the reduced path (`s.cfg.env`).
      if !info.fromClass then
        let p' ← reduceFieldArg p
        if p' != p then
          return add (← costOf ctx args[info.numParams]!) (← costOf ctx (mkAppN p' rest))
      -- A function field of a structure below a data path with a binder (`Z.input.2.f x`):
      -- the costed closure of the field in the costed value of the data path, applied.
      if !info.fromClass then
        let s := args[info.numParams]!
        if let some sv ← pathHat? ctx s false then
          if let some m ← mirrorStruct? (← whnfR (← inferType s)) then
            if let some i := m.projs.idxOf? c then
              if (← hatTy? m.fieldTypes[i]!).isSome then
                let comp ← mirrorProj m.fieldTypes.size i sv
                return add (← costOf ctx s) (← closureApp ctx comp rest).1
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
      -- A field of a structure that reduces to a constructor application (a constant
      -- structure, or a `let` bound to one): the structure is priced, and the field's value
      -- applied to the arguments is priced as unfolded.
      let s := args[info.numParams]!
      let rest := args.extract (info.numParams + 1) args.size
      let sv ← match s.consumeMData with
        | .fvar id => do
          match ← id.getValue? with
          | some v => pure v
          | none => pure s
        | _ => pure s
      let sw ← whnf sv
      if let some cv ← isConstructorApp? sw then
        if let some v := sw.getAppArgs[cv.numParams + info.i]? then
          if ctx.depth ≥ (← maxDepth) then
            fail m!"needs a registered primitive: `{c}` unfolds too deep"
          return add (← costOf ctx s)
            (← costOf { ctx with depth := ctx.depth + 1 } (mkAppN v rest).headBeta)
      -- A function field of a structure holding functions: the costed closure of the field
      -- in the costed value of the structure, applied.
      if let some m ← mirrorStruct? (← whnfR (← inferType s)) then
        if let some i := m.projs.idxOf? c then
          if (← hatTy? m.fieldTypes[i]!).isSome then
            let (cs, vs) ← tv ctx s
            let comp ← mirrorProj m.fieldTypes.size i vs
            return add cs (← closureApp ctx comp rest).1
      fail m!"a function bound in data: the field `{c}` is applied in `{e}`"
    return ← argsCost ctx args
  -- An operation on finite sets or multisets is defined through a quotient, whose internals
  -- have no cost: it is priced by its registered cost (`CatCryptCore.Tactics.StdCosts`).
  if quotientLibs.contains c.getRoot then
    fail m!"needs a registered primitive: `{c}` is an operation on a quotient type (`Finset`, \
      `Multiset`) without a registered cost `{reg}`; the costs of `Finset.sum`, `Finset.prod`, \
      `Finset.univ`, `Finset.range` and `Finset.erase` are registered in \
      `CatCryptCore.Tactics.StdCosts`, which the module must import"
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
for the translated discriminants they bind. A motive whose body depends on the discriminants
(a result type `SPTree (Fin n → X)` of a match on `n`) is translated by `motiveRes?` at its
body. Returns the new application and the cost of the data discriminants. -/
partial def mapMatch (ctx : Ctx) (e resultType : Expr)
    (alt : Ctx → Expr → TermElabM Expr)
    (motiveRes? : Option (Expr → TermElabM Expr) := none) : TermElabM (Expr × Expr) := do
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
  let motive ← lambdaTelescope app.motive fun xs body => do
    if xs.any (fun x => body.containsFVar x.fvarId!) then
      match motiveRes? with
      | some f => mkLambdaFVars xs (← f body)
      | none => fail m!"the match `{e}` has a motive that depends on its discriminants"
    else mkLambdaFVars xs resultType
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
      -- A field of a pattern of a discriminant with a costed value (a block in a sum, a
      -- function field of a state): its costed value keeps the field's functions and reads
      -- their cost companions from the discriminant's costed value.
      if let some pats ← altPatterns app alts.size fs then
        for d in app.discrs, p in pats do
          let .fvar id := d.consumeMData | continue
          let some { kind := .hat, value := v, .. } := ctx.locals.get? id | continue
          for (fv, c) in ← patternHats p v do
            unless fs.contains fv && (ctx'.locals.get? fv.fvarId!).isNone do continue
            let ft ← inferType fv
            if (← hatTy? ft).isNone then continue
            ctx' := { ctx' with
              locals := ctx'.locals.insert fv.fvarId! ⟨.hat, ← refillE ft fv c, none⟩ }
      mkLambdaFVars fs (← alt ctx' b)
    alts := alts.push a'
    ty := body.instantiate1 a'
  let e' := mkAppN (mkConst app.matcherName levels.toList)
    (app.params ++ #[motive] ++ discrs ++ alts)
  return (e', cost)

/-- The cost of a data-valued match: one, the discriminants, and the branch taken. -/
partial def costMatch (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let (e', cd) ← mapMatch ctx e (mkConst ``Nat) costOf (some fun _ => pure (mkConst ``Nat))
  return add (natE 1) (add cd ((← constAlts? e').getD e'))

/-- The translation of the oracle tree `e`: a step-prefixed costed tree whose erasure is `e`
with the translated locals erased. -/
partial def tr (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let e := pushLetApp e.consumeMData.headBeta
  let some T ← treeTyH? (← inferType e)
    | fail m!"`{e}` is not a tree of a registered kind"
  match e with
  | .letE n t v b _ =>
    unless ← keepsLet t v do return ← tr ctx (b.instantiate1 v)
    if let some ht ← hatTy? t then
      -- A `let` of a value holding functions (a state structure): its costed value is bound by
      -- a second `let` and shared by every use, in the step cost and in the costed tree. A
      -- value without a costed form (a field that is a function into an untimed computation)
      -- is priced by the rule below, which prices only the fields the body uses.
      let s ← saveState
      let recs ← ctx.fieldRec?.mapM (·.get)
      let unf ← ctx.unfolded?.mapM (·.get)
      let tvd? ← try some <$> tv ctx v catch _ => do
        s.restore
        if let (some r, some a) := (ctx.fieldRec?, recs) then r.set a
        if let (some r, some a) := (ctx.unfolded?, unf) then r.set a
        pure none
      if let some (cv, vh) := tvd? then
        return ← withLetDecl n t v fun x => withLetDecl (n.appendAfter "Hat") ht vh fun xh => do
          let ctx' := { ctx with locals := ctx.locals.insert x.fvarId! ⟨.hat, xh, none⟩ }
          let p ← tr ctx' (b.instantiate1 x)
          return T.mkPair (add cv (← mkLetFVars #[x, xh] (T.fstOf p)))
            (← mkLetFVars #[x, xh] (T.sndOf p))
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
  if let some e' ← boolRecIte? e then return ← tr ctx e'
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
    -- A dependent motive `fun n => SPTree (τ n)`: the costed tree type at each `n`, of the
    -- interface of `T` (costed results or the plain one).
    let hatted := match ← treeTyH? (← inferType e) with
      | some Th => Th.pairType == T.pairType
      | none => false
    let motiveRes (body : Expr) : TermElabM Expr := do
      let some Tb ← (if hatted then treeTyH? body else treeTy? body)
        | fail m!"the match `{e}` has a motive whose body `{body}` is not a tree"
      return Tb.pairType
    let (e', cd) ← mapMatch ctx e T.pairType tr (some motiveRes)
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
  -- A non-recursive callee generic in its state type, called at a state holding functions: its
  -- body is translated in the caller's context, where the state has its costed value, and the
  -- erasure theorem unfolds it.
  if ctx.self?.all (·.1 != c) && (← unfoldsGenericCall c e) then
    if ctx.depth ≥ (← maxDepth) then
      fail m!"needs a registered costed form: `{c}` unfolds too deep"
    let some e' ← delta? e | fail m!"the call `{e}` does not unfold"
    if let some r := ctx.unfolded? then
      r.modify fun a => if a.contains c then a else a.push c
    return ← tr { ctx with depth := ctx.depth + 1 } (← Core.betaReduce e')
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

/-- The costed value `c.timed` of the recursive data function `c` whose result holds functions,
at the universe levels of `f`: registered, or derived now (`deriveHatValue`). -/
partial def ensureHat (ctx : Ctx) (c : Name) (f : Expr) : TermElabM Expr := do
  let name := c ++ ctx.suffix
  unless (← getEnv).contains name do
    if ctx.visiting.contains c then
      fail m!"`{c}` is reached again while its costed value is derived (mutual recursion)"
    try
      deriveHatValue { suffix := ctx.suffix, visiting := ctx.visiting.insert c } c
    catch ex =>
      throwError m!"derive_timed: while deriving the costed value of the recursive data \
        function `{c}`:\n{ex.toMessageData}"
  return mkConst name f.constLevels!

/-- The arguments of the costed value of the data function `f` at the arguments `args` of a
call, by the binder kinds of `f` (`withBinders`): data as it is, data holding functions as its
costed value (`tv`), a function followed by the cost companion of its costed closure. -/
partial def hatArgs (ctx : Ctx) (f : Expr) (args : Array Expr) : TermElabM (Array Expr) := do
  let kinds ← argKinds f args
  let mut out := #[]
  for i in [0:args.size] do
    let a := args[i]!
    match kinds[i]!.1 with
    | .static | .data => out := out.push a
    | .hat => out := out.push (← tv ctx a).2
    | .fn =>
      let comp ← if (← hatTy? (← inferType a)).isSome then
          projE false (← tv ctx a).2
        else companionOf ctx a
      out := out.push a |>.push comp
    | .tree | .treeFn => fail m!"the data function `{f}` takes the tree `{a}`"
  return out

/-- Derive and add the costed value `c.timed` of the recursive data function `c` whose result
type `t` holds functions, and its erasure theorem `c.erase_timed : ε (c.timed xs) = c (ε xs)`
with the projection lemmas `c.erase_timed_<i>`, one for each component of the erasure
(`epsLeaves`). The binders are those of a costed form (`withBinders`); the body is the one Lean
keeps for the equation lemmas of `c`, translated by `tv` with a recursive call standing for a
call of `c.timed`, so that `c.timed` is defined by the recursion of `c`. The erasure theorem is
proved by functional induction on `c.timed`. -/
partial def deriveHatValue (ctx : Ctx) (c : Name) : TermElabM Unit := do
  let env ← getEnv
  let some info := env.find? c | fail m!"unknown constant `{c}`"
  let name := c ++ ctx.suffix
  let eraseName := c ++ Name.mkSimple ("erase_" ++ ctx.suffix.toString)
  if env.contains name then fail m!"`{name}` already exists"
  let levels := info.levelParams.map mkLevelParam
  let value ← costValue c info
  let (hType, hValue) ← lambdaTelescope value fun xs b => do
    let rt ← inferType b
    let some hrt ← hatTy? rt | fail m!"internal: the result of `{c}` holds no function"
    for x in xs do
      if (← classify (← inferType x)) matches .tree | .treeFn then
        fail m!"the recursive data function `{c}` takes the tree `{x}`"
    withBinders { ctx with top := xs.map (·.fvarId!) } xs fun ctx bs _ => do
      withLocalDeclD `rec (← mkForallFVars bs hrt) fun recF => do
        let (_, v) ← tv { ctx with selfHat? := some (c, recF) } b
        let v := v.replaceFVars (ctx.hatSubst.map (·.1)) (ctx.hatSubst.map (·.2))
        let self ← mkLambdaFVars bs (mkAppN (mkConst name levels) bs)
        let v ← instantiateMVars (← Core.betaReduce (v.replaceFVar recF self))
        if v.hasMVar then fail m!"the costed value of `{c}` has unassigned metavariables"
        if v.containsFVar recF.fvarId! then fail m!"internal: the recursive call escaped"
        for x in xs do
          if v.containsFVar x.fvarId! && !(bs.contains x) then
            fail m!"the binder `{x}` of `{c}` occurs in the costed value"
        return (← mkForallFVars bs hrt, ← mkLambdaFVars bs v)
  addTimedDef name info.levelParams hType hValue
  -- The statement of the erasure theorem and of its projection lemmas, over the binders of the
  -- costed value bound again.
  let (eType, explicit, leaves) ← lambdaTelescope value fun xs b => do
    let rt ← inferType b
    withBinders { ctx with top := xs.map (·.fvarId!) } xs fun _ bs args => do
      let call := mkAppN (mkConst name levels) bs
      let rhs := mkAppN (mkConst c levels) args
      let eq ← mkEq (← epsE rt call) rhs
      let explicit ← bs.mapM fun b => return (← b.fvarId!.getBinderInfo).isExplicit
      let leaves ← (← epsLeaves rt call rhs).mapM fun (l, r) => do
        withLocalDeclD `z rt fun z => do
          let r' ← kabstract r rhs
          return (← mkForallFVars bs (← mkEq l (r'.instantiate1 rhs)),
            ← mkLambdaFVars bs (← mkLambdaFVars #[z] (r'.instantiate1 z)))
      return (← mkForallFVars bs eq, explicit, leaves)
  -- The erasure theorem, by functional induction on the costed value.
  let envNow ← getEnv
  let wfC := (WF.eqnInfoExt.find? envNow c).isSome
  let callees := collectTimed envNow ctx.suffix hValue name
  let simpLemmas : Array Name := (if wfC then #[] else #[name, c]) ++ callees ++
    (if hValue.getUsedConstants.contains ``ite then
      #[``CatCrypt.Tactics.DeriveTimed.boolRec_eq_ite] else #[])
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    simpLemmas.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let ids : Array (TSyntax `ident) := (Array.range explicit.size).map fun i =>
    mkIdent (Name.mkSimple s!"x{i}")
  let explicitIds := (ids.zip explicit).filterMap fun (i, e) => if e then some i else none
  let intros ← if ids.isEmpty then `(tactic| skip) else `(tactic| intro $ids*)
  let close ← `(tactic| ((try simp only [$lemmas,*, *]) <;> (try (repeat' split)) <;>
    (try simp only [$lemmas,*, *]) <;> (try rfl)))
  let tac ← if wfC then
      `(tactic| ($intros; fun_induction $(mkIdent name):ident $explicitIds* <;>
        (try unfold $(mkIdent c):ident) <;> (try unfold $(mkIdent name):ident) <;>
        (try simp (disch := assumption) only [$lemmas,*, *]) <;> $close))
    else
      `(tactic| ($intros; fun_induction $(mkIdent name):ident $explicitIds* <;> $close))
  let proof ← Term.withoutErrToSorry do
    let mv ← mkFreshExprMVar eType
    let rem ← Tactic.run mv.mvarId! (Tactic.evalTactic tac)
    unless rem.isEmpty do
      fail m!"the erasure theorem `{eraseName}` is not closed by functional induction and \
        unfolding; goals left:{indentD (MessageData.joinSep (rem.map (.ofGoal ·)) "\n")}"
    instantiateMVars mv
  if proof.hasSorry || proof.hasMVar then
    fail m!"the erasure theorem `{eraseName}` is not proved"
  addDecl (Declaration.thmDecl
    { name := eraseName, levelParams := info.levelParams, type := eType, value := proof })
  -- The projection lemmas: each component of the erasure theorem, by congruence.
  for h : i in [0:leaves.size] do
    let (ty, proj) := leaves[i]
    let pf ← forallTelescope ty fun bs _ => do
      let hb := mkAppN (mkConst eraseName levels) bs
      let p ← mkCongrArg (mkAppN proj bs).headBeta hb
      mkLambdaFVars bs (← mkExpectedTypeHint p (← instantiateForall ty bs))
    addDecl (Declaration.thmDecl
      { name := eraseName.appendAfter s!"_{i}", levelParams := info.levelParams, type := ty,
        value := pf })

/-- The cost companion of the field path `p` of a local holding functions (a simulation state
of kind `hat`, such as the state of a handler under `simulateHat`): the companion of the
costed closure that the costed value of the local holds at the field; `none` when `p` mentions
no such local or its costed value is not a costed closure. -/
partial def hatFieldCompanion? (ctx : Ctx) (p : Expr) : TermElabM (Option Expr) := do
  let isHat (id : FVarId) : Bool := match ctx.locals.get? id with
    | some { kind := .hat, .. } => true
    | _ => false
  unless p.hasAnyFVar isHat do return none
  let (_, v) ← tv ctx p
  unless (← whnfR (← inferType v)).isAppOfArity ``Prod 2 do return none
  return some (← mkAppM ``Prod.snd #[v])

/-- The pairs `(i, j)` of binders of the function `f`, among its first `n`, such that the
binder `i` is a tree whose result type is the binder `j`, a type parameter that is also the
result type of the tree after the `n` binders (a callee generic in the result type of a tree
argument and of its own result). -/
partial def genericTreeArgs (f : Expr) (n : Nat) : MetaM (Array (Nat × Nat)) := do
  forallBoundedTelescope (← inferType f) (some n) fun xs b => do
    let some Tb ← treeTy? b | return #[]
    let mut out := #[]
    for i in [0:xs.size] do
      let some Tx ← treeTy? (← inferType xs[i]!) | continue
      let r := Tx.result
      unless r.isFVar && Tb.result == r do continue
      let some j := xs.findIdx? (· == r) | continue
      out := out.push (i, j)
    return out

/-- A call of the reduction whose costed form is `target`: one plus the step cost of the
costed call plus the costs of the arguments.

A tree argument whose raw result type is a type parameter `α` of a registered callee `c`
(`genericTreeArgs`) and holds functions is passed as the costed tree, with its results costed,
and `α` is instantiated with their costed type: the call's result has the costed type of the
caller's state. The erasure theorem moves the erasure of the results inside `c` by the
naturality lemma `c.bind_ret`, recorded in `ctx.natural?`; a callee without it is refused. -/
partial def callTimed (ctx : Ctx) (e target : Expr) (args : Array Expr) (T : TreeTy) :
    TermElabM Expr := do
  let kinds ← argKinds e.getAppFn args
  let generic ← genericTreeArgs e.getAppFn args.size
  let mut out := #[]
  let mut cost := natE 0
  -- The positions in `out` of the static arguments, and the costed instances of the type
  -- parameters of the generic rule.
  let mut staticPos : Array (Nat × Nat) := #[]
  let mut instAt : Array (Nat × Expr) := #[]
  for i in [0:args.size] do
    let a := args[i]!
    let k := kinds[i]!.1
    match k with
    | .static =>
      staticPos := staticPos.push (i, out.size)
      out := out.push a
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
      let gen? := generic.find? (·.1 == i)
      if let (some (_, j), some _) := (gen?, ← hatTy? raw.result) then
        let .const cn _ := e.getAppFn
          | fail m!"internal: the generic callee `{e.getAppFn}` is not a constant"
        let lem := cn ++ `bind_ret
        unless (← getEnv).contains lem do
          fail m!"the callee `{cn}` is generic in the result type of its tree argument `{a}`, \
            called at a result type holding functions: its costed form takes the costed \
            results, which needs the naturality lemma `{lem}`, \
            `(c X).bind (fun y => .ret (f y)) = c (X.bind fun y => .ret (f y))`"
        if let some r := ctx.natural? then
          r.modify fun ns => if ns.contains lem then ns else ns.push lem
        let p ← tr ctx a
        instAt := instAt.push (j, Ta.result)
        out := out.push (Ta.sndOf p)
        cost := add cost (Ta.fstOf p)
      else
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
  for (j, h) in instAt do
    let some (_, pos) := staticPos.find? (·.1 == j)
      | fail m!"internal: the type parameter of the generic callee `{e.getAppFn}` is not static"
    out := out.set! pos h
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
          let p ← reduceFieldArg p
          if let some (_, cc) := ctx.fields.find? (·.1 == p) then
            out := out.push cc
          else if let some (_, cc) := ctx.fields.find? (·.1 == (← canonPath p)) then
            out := out.push cc
          else if let some cc ← hatFieldCompanion? ctx p then
            out := out.push cc
          else if ← isValueField ctx p then
            -- A field of a structure value: priced at the structure's value.
            out := out.push (← companionOf ctx p)
          else if let some r := ctx.fieldRec? then
            unless (← r.get).contains p do r.modify (·.push p)
            out := out.push (← mkFreshExprMVar (← pathCompanionType p))
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
  let unfoldedRef ← IO.mkRef (#[] : Array Name)
  let naturalRef ← IO.mkRef (#[] : Array Name)
  let ctx := { ctx with plain, unfolded? := some unfoldedRef, natural? := some naturalRef }
  -- A plain interface around data holding functions: the erasure lemmas of costed closures.
  let plainHat ← if !plain then pure false else lambdaTelescope value fun xs b => do
    if ← xs.anyM fun x => do return (← hatTy? (← inferType x)).isSome then return true
    let some rawT ← treeTy? (← inferType b) | return false
    return (← hatTy? rawT.result).isSome
  let (tType, tValue, eType, nBinders, hatted, dataHat, fp?) ←
      lambdaTelescope value fun xs b => do
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
        -- A failed first pass leaves no declarations behind: a callee whose costed form was
        -- added before its erasure theorem failed is derived again, and fails, in the second.
        let s ← saveState
        try discard <| tr { ctx with self? := some (c, recF), fieldRec? := some r } b
        catch _ => s.restore
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
        -- A data path with a costed value: its costed closures flow through the trees.
        let dataHat ← used.anyM fun (p, _) => isDataPath p
        return (tType, tValue, eType, explicit, hatted, dataHat, fp?)
  addTimedDef timedName info.levelParams tType tValue
  if let some fp := fp? then
    addTimedDef (timedName ++ `fieldPaths) info.levelParams (← inferType fp) fp
  -- The erasure theorem.
  let callees := collectTimed (← getEnv) ctx.suffix tValue timedName
  -- The erasure lemmas of the tree kinds whose costed trees occur in the costed form.
  let used := tType.getUsedConstants ++ tValue.getUsedConstants
  let kindLemmas := (treeKinds.filter fun k => used.contains k.timed).flatMap (·.eraseLemmas)
  -- The naturality lemmas `c.bind_ret` of registered callees called at a costed instance of
  -- their type parameter (`callTimed`), oriented left to right: the erasure of the results
  -- moves inside the callee, onto the erasure theorem of its tree argument.
  let naturalLemmas ← naturalRef.get
  -- A costed form by recursion over an oracle tree has a case analysis as its only equation,
  -- which `fun_induction` unfolds; as a simp lemma it would loop.
  let treeRec := tValue.getUsedConstants.contains ``CatCrypt.Crypto.OracleAdv.Timed.casesOn
  -- Costed closures in a result or in a simulation state: the lemmas that push `ε` to the
  -- leaves and the erasure of a simulation with a costed state.
  let hatLemmas : Array Name :=
    if hatted || binderHat || plainHat || dataHat || used.contains ``CatCrypt.Crypto.OracleAdv.Timed.simulateHat ||
        callees.any (fun n => n.toString.endsWith "_bind") || !naturalLemmas.isEmpty then
      (treeKinds.filter fun k => used.contains k.timed).flatMap (·.hatLemmas)
    else #[]
  -- A definition by well-founded recursion has an unconditional equation, which loops as a
  -- simp lemma: it is unfolded once by `unfold`, and `fun_induction` unfolds its costed form.
  let envNow ← getEnv
  let wf (n : Name) : Bool := (WF.eqnInfoExt.find? envNow n).isSome
  let wfC := wf c
  -- A `match` in a tree position under a binder (a continuation `fun o => match o with …`),
  -- where `split` does not reach: the erasure lemma of its matcher.
  let mut matchLemmas : Array Name := #[]
  for m in tValue.getUsedConstants.filter (isMatcherCore envNow ·) do
    for k in treeKinds.filter fun k => used.contains k.timed do
      if let some n ← matchEraseLemma k m then matchLemmas := matchLemmas.push n
  let unfoldedDefs := (← unfoldedRef.get).filter (fun n => n != c)
  let simpLemmas : Array Name :=
    ((if treeRec then #[c] else #[timedName, c]).filter (!wf ·)) ++ kindLemmas ++ hatLemmas ++
      matchLemmas ++ callees ++ naturalLemmas ++ unfoldedDefs ++
      (if used.contains ``ite then #[``CatCrypt.Tactics.DeriveTimed.boolRec_eq_ite] else #[])
  let ids : Array (TSyntax `ident) := (Array.range nBinders.size).map fun i =>
    mkIdent (Name.mkSimple s!"x{i}")
  let explicitIds := (ids.zip nBinders).filterMap fun (i, e) => if e then some i else none
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    simpLemmas.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  -- The side conditions of `erase_simulateHat_bind` are equations under binders, discharged
  -- by the same lemmas. `simp` with a discharger traverses a shared costed value once per
  -- occurrence, so a non-recursive costed form is closed first without the discharger (then by
  -- the `if` closer below), and with it only when goals remain.
  let mkClose (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (disch : Bool) :
      TermElabM (TSyntax `tactic) :=
    if hatLemmas.isEmpty || !disch then
      `(tactic| ((try simp only [$lemmas,*, *]) <;> (try (repeat' split)) <;>
        (try simp only [$lemmas,*, *]) <;> (try rfl)))
    else
      `(tactic| ((try simp (disch := (intros; simp only [$lemmas,*])) only [$lemmas,*, *]) <;>
        (try (repeat' split)) <;>
        (try simp (disch := (intros; simp only [$lemmas,*])) only [$lemmas,*, *]) <;>
        (try rfl)))
  let close ← mkClose lemmas recursive
  let closeDisch ← mkClose lemmas true
  -- A callee whose body is a match (an auxiliary definition `B.tree.match_i` of
  -- `derive_reduction`) called at a discriminant built from a constructor, where its erasure
  -- theorem does not close the goal: the callee and its costed form are unfolded, the
  -- discriminants are reduced by the lemmas of `Sum.map` and `Sum.elim` at a constructor, and
  -- `simp` reduces both matches at the constructor. In a `module` file `rfl` does not unfold the
  -- matcher of an imported definition, so that the two matches are not reduced by `rfl` alone.
  let mut matchDefs : Array Name := #[]
  for n in tValue.getUsedConstants do
    let .str p s := n | continue
    unless n != timedName && s == ctx.suffix.toString && !matchDefs.contains p do continue
    let some (.defnInfo dv) := envNow.find? p | continue
    let headed ← lambdaTelescope dv.value fun _ b =>
      pure (isMatcherCore envNow b.getAppFn.constName)
    if headed then matchDefs := matchDefs ++ #[p, n]
  let closeMatch? ← if matchDefs.isEmpty then pure none else do
    let extra := matchDefs ++ #[``Sum.map_inl, ``Sum.map_inr, ``Sum.elim_inl, ``Sum.elim_inr]
    let more : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      extra.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    pure (some (← mkClose (lemmas ++ more) true))
  -- `intro` without names introduces one binder: a reduction without binders introduces none.
  let intros ← if ids.isEmpty then `(tactic| skip) else `(tactic| intro $ids*)
  let tac ← if recursive && wfC then
      -- The induction hypotheses of a recursion through `if` are conditional on the case's
      -- hypothesis, discharged by `assumption`.
      `(tactic| ($intros; fun_induction $(mkIdent timedName):ident $explicitIds* <;>
        (try unfold $(mkIdent c):ident) <;>
        (try simp (disch := assumption) only [$lemmas,*, *]) <;> $close))
    else if recursive then
      `(tactic| ($intros; fun_induction $(mkIdent timedName):ident $explicitIds* <;> $close))
    else if treeRec then
      `(tactic| ($intros; $close))
    else
      -- A costed form whose body is a match on a binder has its equations split by case:
      -- `unfold` rewrites it at a variable.
      `(tactic| ($intros; (try unfold $(mkIdent timedName):ident); $close))
  -- An `if` in a continuation between costed values whose erasure the other side reads through
  -- functions applied to the `if` (`(if a then s.corrupt u else s).isCorrupted u`): the
  -- projections are pushed through the `if` (`fst_ite`, `snd_ite`) before any
  -- case split, both sides are decomposed by congruence under the binders of the continuations
  -- (`congr!`), and the `if`s, now on variables, are split by their conditions.
  let iteNames := #[``fst_ite, ``snd_ite].filter (!hatLemmas.contains ·)
  let iteLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    iteNames.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let allIte := lemmas ++ iteLemmas
  let closeIte ← `(tactic| ((try simp only [$allIte,*, *]) <;> (try congr!) <;>
    (try split_ifs) <;> (try rfl)))
  let tacIte? : Option (TSyntax `tactic) ← if recursive || treeRec then pure none else
    some <$> `(tactic| ($intros; (try unfold $(mkIdent timedName):ident); $closeIte))
  -- The closer with the discharger, for a non-recursive costed form left open by the others.
  let tacDisch? : Option (TSyntax `tactic) ← if recursive || hatLemmas.isEmpty then pure none
    else if treeRec then some <$> `(tactic| ($intros; $closeDisch))
    else some <$> `(tactic| ($intros; (try unfold $(mkIdent timedName):ident); $closeDisch))
  -- A bind of an `if` or a match under a binder (an `if` under the binder of a `query` node
  -- whose branches rebuild a state holding functions, followed by the erasure `ε` of the
  -- result): the bind lemmas of `if`, dependent `if` and the matchers of both sides push the
  -- bind into the branches. The stage runs without the discharger, then with it.
  let usedKinds := treeKinds.filter fun k => used.contains k.timed
  let mut bindNames : Array Name := #[]
  for k in usedKinds do
    if k.tree == ``CatCrypt.Crypto.OracleAdv then
      bindNames := bindNames ++ #[``CatCrypt.Crypto.OracleAdv.ite_bind,
        ``CatCrypt.Crypto.OracleAdv.dite_bind]
    if k.tree == ``CatCrypt.Core.SPTree then
      bindNames := bindNames ++ #[``CatCrypt.Core.SPTree.ite_bind,
        ``CatCrypt.Core.SPTree.dite_bind]
  let bodyConsts := match info with
    | .defnInfo dv => dv.value.getUsedConstants
    | _ => #[]
  for m in (tValue.getUsedConstants ++ bodyConsts).filter (isMatcherCore envNow ·) do
    for k in usedKinds do
      if let some n ← matchBindLemma k m then
        unless bindNames.contains n do bindNames := bindNames.push n
  let bindLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    bindNames.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let allBind := allIte ++ bindLemmas
  let closeBind ← `(tactic| ((try simp only [$allBind,*, *]) <;> (try (repeat' split)) <;>
    (try split_ifs) <;> (try simp only [$allBind,*, *]) <;> (try rfl)))
  -- With the discharger, the erasure theorems `R.erase_timed_bind` of callees are left out when
  -- `R.erase_timed` is present: in a side condition of `erase_simulateHat_bind` the handler's
  -- result is followed by `ε`, which `R.erase_timed` matches, while `R.erase_timed_bind` leaves
  -- the round trip `ι ∘ ε` of the state, a structure eta-expanded field by field.
  let plainNames := simpLemmas.filter fun n =>
    !(callees.contains n && n.toString.endsWith "_bind" &&
      callees.any (·.toString ++ "_bind" == n.toString))
  let plainLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    plainNames.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let allPlain := plainLemmas ++ iteLemmas ++ bindLemmas
  let closeBindDisch ← `(tactic|
    ((try simp (disch := (intros; simp only [$allPlain,*])) only [$allPlain,*, *]) <;>
      (try (repeat' split)) <;> (try split_ifs) <;>
      (try simp (disch := (intros; simp only [$allPlain,*])) only [$allPlain,*, *]) <;>
      (try rfl)))
  let tacBind? : Option (TSyntax `tactic) ← if recursive || bindNames.isEmpty then pure none
    else if treeRec then some <$> `(tactic| ($intros; $closeBind))
    else some <$> `(tactic| ($intros; (try unfold $(mkIdent timedName):ident); $closeBind))
  let tacBindDisch? : Option (TSyntax `tactic) ←
    if recursive || bindNames.isEmpty || hatLemmas.isEmpty then pure none
    else if treeRec then some <$> `(tactic| ($intros; $closeBindDisch))
    else some <$> `(tactic| ($intros; (try unfold $(mkIdent timedName):ident); $closeBindDisch))
  let proof ← Term.withoutErrToSorry do
    let mv ← mkFreshExprMVar eType
    let rem ← if recursive && hatted then do
        -- A recursion whose result holds functions: the induction hypothesis
        -- `(R.timed ys).2.erase.bind (fun y => ret (ε y)) = R ys` is used from right to left,
        -- so that the recursive call of `R` becomes the erased costed call followed by `ε`,
        -- which the continuation's lemmas (`bind_assoc`, `bind_ret`) absorb.
        let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic|
          ($intros; fun_induction $(mkIdent timedName):ident $explicitIds* <;>
            (try unfold $(mkIdent c):ident) <;>
            (try simp only [$lemmas,*]) <;> (try (repeat' split))))))
        let mut rem := []
        for g in gs do
          let g ← rewriteRecHyps c g
          rem := rem ++ (← Tactic.run g (Tactic.evalTactic close))
        pure rem
      else Tactic.run mv.mvarId! (Tactic.evalTactic tac)
    let rem ← match closeMatch? with
      | some closeMatch => rem.flatMapM fun g => Tactic.run g (Tactic.evalTactic closeMatch)
      | none => pure rem
    let (mv, rem) ← match rem, tacIte? with
      | _ :: _, some tacIte => do
        let mv' ← mkFreshExprMVar eType
        let rem' ← Tactic.run mv'.mvarId! (Tactic.evalTactic tacIte)
        pure (if rem'.isEmpty then (mv', rem') else (mv, rem))
      | _, _ => pure (mv, rem)
    let (mv, rem) ← match rem, tacBind? with
      | _ :: _, some tacBind => do
        let mv' ← mkFreshExprMVar eType
        let rem' ← Tactic.run mv'.mvarId! (Tactic.evalTactic tacBind)
        pure (if rem'.isEmpty then (mv', rem') else (mv, rem))
      | _, _ => pure (mv, rem)
    let (mv, rem) ← match rem, tacBindDisch? with
      | _ :: _, some tacBindDisch => do
        let mv' ← mkFreshExprMVar eType
        let rem' ← Tactic.run mv'.mvarId! (Tactic.evalTactic tacBindDisch)
        pure (if rem'.isEmpty then (mv', rem') else (mv, rem))
      | _, _ => pure (mv, rem)
    let (mv, rem) ← match rem, tacDisch? with
      | _ :: _, some tacDisch => do
        let mv' ← mkFreshExprMVar eType
        let rem' ← Tactic.run mv'.mvarId! (Tactic.evalTactic tacDisch)
        let rem' ← match closeMatch? with
          | some closeMatch => rem'.flatMapM fun g => Tactic.run g (Tactic.evalTactic closeMatch)
          | none => pure rem'
        pure (if rem'.isEmpty then (mv', rem') else (mv, rem))
      | _, _ => pure (mv, rem)
    -- A goal left with a structure rebuilt from the projections of a state, one of which a case
    -- hypothesis rewrote (`{ cur := k + 1, env := s.cfg.env } = s.cfg` with `s.cfg.cur = k + 1`).
    let rem ← rem.filterM fun g => return !(← closeByCaseHypsRev g)
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
        let acc := if env.contains thmB && !acc.contains thmB then acc.push thmB else acc
        -- The projection lemmas `thm_<i>` of the costed value of a recursive data function.
        let projs := (List.range 64).map (fun i => thm.appendAfter s!"_{i}")
          |>.takeWhile env.contains
        projs.foldl (fun acc n => if acc.contains n then acc else acc.push n) acc
      else acc
    | _ => acc

/-- Add the definition `name`, settling its recursion as a `def`'s (`addTimedDefs`). -/
partial def addTimedDef (name : Name) (levelParams : List Name) (type value : Expr) :
    TermElabM Unit :=
  addTimedDefs levelParams #[(name, type, value)]

/-- Add the definitions `defs`, each a name, a type and a value, as one mutual block, settling
its recursion as a `mutual` block of `def`s'. In a `module` file the definitions are exposed,
so that importing modules unfold costed forms and costs, unless a value uses a declaration
private to the module (the matcher of a definition that is not exposed): the equation lemmas
of an exposed definition are stated in the exported environment, where that declaration is
unknown. -/
partial def addTimedDefs (levelParams : List Name) (defs : Array (Name × Expr × Expr)) :
    TermElabM Unit := do
  let name := defs[0]!.1
  let saved := (← getThe Core.State).messages
  modifyThe Core.State fun s => { s with messages := {} }
  let expose := (← getEnv).header.isModule &&
    !defs.any fun (_, _, value) => value.getUsedConstants.any isPrivateName
  let outcome ← try
      withExporting (isExporting := expose) <| addPreDefinitions ({}, {}) <|
        defs.map fun (declName, type, value) => {
          ref := .missing, kind := .def, levelParams,
          modifiers := { computeKind := .noncomputable }, declName,
          binders := .missing, type, value, termination := .none }
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
  -- A member of a mutual block: the costs of the block are derived together.
  let block := mutualBlock env c
  if block.size > 1 then return ← deriveCostBlock units c block
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
          let cost ← costWithUnits { ctx with selfCosts := #[(c, recF)], fields := fcs } ps b
          let cost ← instantiateMVars cost
          if cost.hasMVar then
            throwError "derive_cost: the cost of `{c}` has unassigned universes"
          let self ← mkLambdaFVars bs (mkAppN (mkConst costName levels) (bs ++ cs))
          let cost ← Core.betaReduce (cost.replaceFVar recF self)
          return (cType, ← mkLambdaFVars (bs ++ cs) cost)
  addTimedDef costName info.levelParams cType cValue

/-- The members of the mutual block of the recursive function `c`, in the order of the block:
`#[c]` for a function outside a mutual block. -/
partial def mutualBlock (env : Environment) (c : Name) : Array Name :=
  let names := match Structural.eqnInfoExt.find? env c, WF.eqnInfoExt.find? env c with
    | some i, _ => i.declNames
    | _, some i => i.declNames
    | _, _ => #[]
  if names.contains c then names else #[c]

/-- Derive and add the costs `g.timedCost` of the members `g` of the mutual block `block` of the
data function `c` as one mutual definition, charging the class methods `units` on local
instances one unit. A call of a member is priced by the member's cost being defined, so the
costs are defined by the recursion of the block. Each cost takes, after the costed binders of its
member, the cost companions of the field paths of the block (`blockFieldPaths`), and a call of a
member passes the same companions. -/
partial def deriveCostBlock (units : Array Name) (c : Name) (block : Array Name) :
    TermElabM Unit := do
  let env ← getEnv
  let some cInfo := env.find? c | throwError "derive_cost: unknown constant `{c}`"
  let levels := cInfo.levelParams.map mkLevelParam
  for g in block do
    if env.contains (g ++ `timedCost) then
      throwError "derive_cost: `{g ++ `timedCost}` already exists"
  let members ← blockMembers c block
  let (shared, k) ← blockFieldPaths units c members
  let defs ← withLocalDeclsDND (members.map fun (_, _, t) => (`rec, t)) fun recFs => do
    let selfCosts := block.zip recFs
    members.mapM fun (g, value, _) => lambdaTelescope value fun xs b => do
      let pre := xs.extract 0 k
      let paths := shared.map (·.instantiateRev pre)
      for p in paths do
        try Meta.check p
        catch ex =>
          throwError "derive_cost: the field path `{p}` of the mutual block of `{c}` is not a \
            path of the binders of `{g}`:{indentD ex.toMessageData}"
      -- A call of a member passes the binders that the field paths mention unchanged.
      unless paths.isEmpty do
        let fixed := (List.range k).filter fun i =>
          paths.any fun p => p.containsFVar xs[i]!.fvarId!
        let need := fixed.foldl (fun m i => max m (i + 1)) 0
        let bad := b.find? fun s => block.any (s.isAppOf ·) && s.getAppNumArgs ≥ need &&
          fixed.any fun i => s.getArg! i != xs[i]!
        if let some s := bad then
          throwError "derive_cost: the call `{s}` in the mutual block of `{c}` changes a \
            structure whose applied fields are priced by cost companions"
      withBinders { top := xs.map (·.fvarId!) } xs fun ctx bs _ => do
        withFieldCosts paths fun fcs => do
          let cs := fcs.map (·.2)
          let cost ← costWithUnits { ctx with selfCosts, fields := fcs }
            (← unitPrefixes units b) b
          let cost ← instantiateMVars cost
          if cost.hasMVar then
            throwError "derive_cost: the cost of `{g}` has unassigned universes"
          -- Each local standing for the cost of a member is that member's cost at the same
          -- companions.
          let selfs ← (block.zip recFs).mapM fun (g', r) => do
            forallTelescope (← inferType r) fun ys _ =>
              mkLambdaFVars ys (mkAppN (mkConst (g' ++ `timedCost) levels) (ys ++ cs))
          let cost ← Core.betaReduce (cost.replaceFVars recFs selfs)
          return (g ++ `timedCost, ← mkForallFVars (bs ++ cs) (mkConst ``Nat),
            ← mkLambdaFVars (bs ++ cs) cost)
  addTimedDefs cInfo.levelParams defs

/-- The members `g` of the mutual block `block` of the data function `c`, each with the value
that `derive_cost` prices and the type of its cost without the costs of fields. -/
partial def blockMembers (c : Name) (block : Array Name) :
    TermElabM (Array (Name × Expr × Expr)) := do
  let env ← getEnv
  let some cInfo := env.find? c | throwError "derive_cost: unknown constant `{c}`"
  let mut members : Array (Name × Expr × Expr) := #[]
  for g in block do
    let some info := env.find? g
      | throwError "derive_cost: unknown constant `{g}` in the mutual block of `{c}`"
    unless info.levelParams == cInfo.levelParams do
      throwError "derive_cost: the members `{c}` and `{g}` of a mutual block have different \
        universe parameters"
    let value ← costValue g info
    let cType ← lambdaTelescope value fun xs b => do
      if (← treeTyH? (← inferType b)).isSome then
        throwError "derive_cost: the result of `{g}` is a tree; use `derive_timed`"
      for x in xs do
        if (← classify (← inferType x)) matches .tree | .treeFn then
          throwError "derive_cost: the binder `{x}` of `{g}` is a tree; use `derive_timed`"
      withBinders { top := xs.map (·.fvarId!) } xs fun _ bs _ =>
        mkForallFVars bs (mkConst ``Nat)
    members := members.push (g, value, cType)
  return members

/-- The field paths whose cost companions the costs of the members `members` of the mutual
block of `c` take: the field paths of every member, in the order in which pricing passes reach
them, each abstracted over the first `k` binders of its member, where `k` is the least number of
binders of a member; returned with `k`. A path that mentions a later binder is refused. -/
partial def blockFieldPaths (units : Array Name) (c : Name)
    (members : Array (Name × Expr × Expr)) : TermElabM (Array Expr × Nat) := do
  let k := members.foldl (fun m (_, v, _) => min m v.getNumHeadLambdas)
    (members[0]?.map (·.2.1.getNumHeadLambdas) |>.getD 0)
  withLocalDeclsDND (members.map fun (_, _, t) => (`rec, t)) fun recFs => do
    let selfCosts := (members.map (·.1)).zip recFs
    let mut shared : Array Expr := #[]
    for (g, value, _) in members do
      let ps ← lambdaTelescope value fun xs b => do
        let paths ← recordFieldPaths units g xs b selfCosts
        let pre := xs.extract 0 k
        paths.mapM fun p => do
          let a := p.abstract pre
          if xs.any fun x => a.containsFVar x.fvarId! then
            throwError "derive_cost: `{g}`, in the mutual block of `{c}`, applies the field \
              `{p}` of a binder after the first {k} binders, which all members share"
          return a
      for a in ps do
        unless shared.contains a do shared := shared.push a
    return (shared, k)

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
partial def recordFieldPaths (units : Array Name) (c : Name) (xs : Array Expr) (b : Expr)
    (others : Array (Name × Expr) := #[]) : TermElabM (Array Expr) := do
  withBinders { top := xs.map (·.fvarId!) } xs fun ctx bs _ => do
    let r ← IO.mkRef (#[] : Array Expr)
    let ps ← unitPrefixes units b
    withLocalDeclD `rec (← mkForallFVars bs (mkConst ``Nat)) fun recF => do
      try
        discard <| costWithUnits
          { ctx with selfCosts := #[(c, recF)] ++ others, fieldRec? := some r } ps b
      catch _ => pure ()
    r.get

/-- The field paths whose cost companions the derived cost of the data function `c` takes,
instantiated at the arguments `args` of a call of `c` at the universe levels `lvls`. -/
partial def calleeFieldPaths (c : Name) (lvls : List Level) (args : Array Expr) :
    TermElabM (Array Expr) := do
  let some info := (← getEnv).find? c | return #[]
  -- A member of a mutual block: the field paths shared by the block.
  let block := mutualBlock (← getEnv) c
  if block.size > 1 then
    let (shared, k) ← blockFieldPaths #[] c (← blockMembers c block)
    if shared.isEmpty then return #[]
    unless k ≤ args.size do
      fail m!"the cost of `{c}` takes the costs of fields, and `{c}` is applied to \
        {args.size} of the {k} arguments that its field paths take"
    return shared.map fun a =>
      (a.instantiateLevelParams info.levelParams lvls).instantiateRev (args.extract 0 k)
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
  -- The optional group `(suffix := s)` is a node of five children when present.
  let suffix := if stx[1].getNumArgs == 5 then stx[1][3].getId else `timed
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

