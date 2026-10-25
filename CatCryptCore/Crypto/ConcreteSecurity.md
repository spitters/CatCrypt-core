# Concrete security and the cost of reductions

CatCrypt states security concretely: a theorem bounds the advantage of every adversary by the
advantages of explicit reductions plus a statistical term, and the efficiency of each reduction
is a separate statement about its running time. The complexity measures of the library serve
the purposes of §3; their results and relation to the literature are in [Complexity.md](Complexity.md).

## 1. The convention

A computational security theorem has the form

```
for every adversary A,   Adv_protocol(A) ≤ Σᵢ Adv_primᵢ(Bᵢ A) + ε_stat
```

where each reduction `Bᵢ` is a definition in the same file, `Adv_primᵢ` is the advantage in the
game of a primitive, and `ε_stat` is an information-theoretic term, a number or a function of
the query bounds of `A`. This is the form of the code-based game proofs of CertiCrypt and
EasyCrypt [BGZ09, BGHZ11] and of concrete security after Bellare and Rogaway [BR06]. For
example, `cascade_prf_bound` ([Examples/PRF.lean](../Examples/PRF.lean)) bounds the PRF
advantage of the cascade against an oracle adversary `A` with `A.IsQueryBound q` by the PRF
advantages of `cascadeRedInner F A` and `cascadeRedOuter A` plus `q(q−1)/2 / |D|`.

A Lean adversary is an arbitrary function, and the theorem holds for every one. Its content for
an efficient `A` comes from two further facts: the time theorem of `Bᵢ` bounds the running time
of `Bᵢ A` by that of `A` (§2), and the assumption on the primitive bounds `Adv_primᵢ` at
efficient adversaries. The assumption stays
outside the theorem. Two forms are excluded. A hypothesis `∀ A, Adv_prim(A) ≤ ε` on a
computational game, under any name (a class, a structure field, an assumed reduction `∃ B`),
fails for every primitive when `A` ranges over unbounded functions, since exhaustive search
breaks it. A bound `⨆ A, Adv_prim(B A)` replaces the adversary at hand by the strongest one.

UC statements are made for each adversary and environment. `UCEmulatesCSim spec π F sim bound`
([UCConcrete.lean](UCConcrete.lean)) states that for every adversary `A` and environment `Z`
(an input, an initial heap and a distinguisher) the gap between the real run with `A` and the
ideal run with the simulator `sim A` is at most `bound A Z`, for instance `DDH_Advantage (B A Z)`
for an explicit reduction `B`. Transitivity, subroutine and parallel composition are
`UCEmulatesCSim.trans`, `UCEmulatesCSim_compile` and `UCEmulatesCSim_par`; `UCFromGameC` turns
a concrete game bound into concrete UC emulation. The numeric `UCEmulates ε` ([UC.lean](UC.lean))
bounds the statistical distance over all distinguishers and serves information-theoretic
protocols; `UCEmulatesC_const_iff` identifies it with `UCEmulatesC` at a constant bound.
Asymptotic statements (`IsNegligible`, `UCEmulatesNegl`, `isNegligible_poly_mul`) are
in [ConcreteReductions.lean](ConcreteReductions.lean).

## 2. Efficiency of reductions

For each reduction the statement to certify is

```
time(Bᵢ A) ≤ k · time(A) + q · t + c
```

where `q` is the number of oracle queries of `A`, `t` the cost of answering one, `k` the number
of runs of `A` inside `Bᵢ` (one for a black-box reduction, more under rewinding) and `c` the
remaining work of `Bᵢ`. The cost logic of EasyCrypt [BBGKS21] proved statements of this form,
with the adversary an abstract module whose cost is a parameter, until its removal in 2024
(§4). In CatCrypt a
reduction `R` is certified by a costed form and two theorems checked by the kernel.

1. Costed mirrors. The oracle trees `OracleAdv` ([OracleAdversary.lean](OracleAdversary.lean))
   and the syntax trees `SPTree` ([SPTree.lean](../Core/SPTree.lean)) have mirrors
   `OracleAdv.Timed` ([OracleAdversaryTimed.lean](OracleAdversaryTimed.lean)) and `SPTree.Timed`
   ([SPTreeTimed.lean](../Core/SPTreeTimed.lean)) with the same constructors, in which each
   sampling and query node also carries the cost of computing the next node. `erase` sends a
   mirror to the plain tree; `TimeBound` sums node and step costs along every path. Its laws
   are the time analogues of `isQueryBound_bind` and `isQueryBound_simulate`
   ([OracleSimulation.lean](OracleSimulation.lean)): `timeBound_bind`, and `timeBound_simulate`,
   by which `OracleAdv.simulate impl A` has time at most `T_A + q_A · t_impl`. `compileTimed`
   sends a costed syntax tree to `CostComp` with expected cost at most its time
   (`ecost_compileTimed_le_time`).
2. The adversary as a costed witness. A time theorem quantifies over costed adversaries whose
   erasure is `A` and whose time is at most `T`, as §1 quantifies over `A` with
   `A.IsQueryBound q`.
3. The certificate. The costed form `R.timed` takes costed adversaries in place of the
   adversaries of `R` and returns a costed tree preceded by a step cost. The erasure theorem
   `R.erase_timed` states `(R.timed A').2.erase = R A'.erase`; its variant `R.run_erase_timed`
   states that the erased costed form has the output distribution of `R` under every oracle.
   The time theorem `R.timeBound_timed` bounds the time of the costed form by
   `k · T + q · t + c` when `A'` has time at most `T` and its erasure at most `q` queries.

Five certified reductions and their time theorems:

| Time theorem | Reduction | Time at most | Costed form |
|---|---|---|---|
| [`hashRed.timeBound_timed`](HashThenRF.lean) | hash-then-PRF to the PRF | `1 + T + q · (2 + t₀)` | `derive_timed` |
| [`iknpCRRed.timeBound_timed`](OTExtension/IKNP.lean) | IKNP OT extension to the correlation-robust hash | `T₁ + Ts + ts + T + a + tv + 3` | `derive_reduction` |
| [`ckaDDHRed.timeBound_timed`](Messaging/CKA.lean) | Diffie–Hellman CKA to DDH | `T + a + tv + 4` | `derive_reduction` |
| [`cdhReduction.timeBound_timed`](PAKE/DHPAKE.lean) | Diffie–Hellman PAKE to CDH | `T + (tH + 1) · qH + tOut + 3` | by hand |
| [`mkHybRed.timeBound_timed`](MultiKeyPRF.lean) | multi-key PRF to the PRF, hybrid `j` over the keys | `T + q · c` | by hand |

Here `T` is the time of the adversary, `q` and `qH` its numbers of queries and `a` the cost of a
call to it. The IKNP reduction runs the two parts of the adversary, of times `T₁` and `T`, and a
simulator of the base-OT view of time `Ts` and call cost `ts`. The costs of primitives are `t₀`
for the hash, `tH` for answering a hash query, `tv` for the view map, which computes the group
elements of the CKA transcript, and `c` for the bookkeeping of each query of the multi-key
reduction (the rank of its index, the table lookup and the state update).

`derive_timed R` ([DeriveTimed.lean](../Tactics/DeriveTimed.lean)) defines `R.timed` and proves
`R.erase_timed` for a reduction whose result is an oracle tree or an `SPTree`. A binder that is
a tree, or a function into trees, becomes its costed mirror, and each function-typed binder,
adversary or primitive, is followed by a cost companion `fCost`, the cost of evaluating it at
its arguments. The step costs are derived from the reduction's code by the rules of
call-by-value evaluation: a call costs one plus the callee's cost at its arguments; `if` and
`match` cost one plus the branch taken; constructors, literals, projections and variables are
free; a `let` of the reduction's body is priced once, and so is an argument of a definition the
tool unfolds, whether the bound variable is used once, several times or not at all; `rand`,
`query`, `sample`, `get` and `set` nodes cost one unit, as in `SPTree.queryCost`. A value computed
inside a helper whose cost is registered or derived separately is priced at each call of the
helper. A call `b` of which two projections `b.1`, `b.2` occur among the arguments of an
unfolded definition is evaluated once and shared. A field of a structure binder (`kit.hash`)
has one cost companion, whether it is applied in the body, inside an unfolded helper or inside
a recursive helper whose cost `derive_cost` derives; that cost takes the companions of the fields
it applies, and each call passes them. A field of a computed structure, `(kit.aead iv).enc k m`,
is priced as the computation of the structure `kit.aead iv` by these rules, plus one, plus a cost
companion `aead_encCost iv k m` indexed by the arguments that compute the structure and the
arguments of the field.
A function value inside data, a table of a simulation state, a function in a result or a
closure received from a tree, is carried as a costed closure `(X → Y) × (X → ℕ)`, the function
with its cost companion (the writer translation of function types, the first-order case of the
typed measures of Forster and Kunze). Building a closure is free and its companion is the cost
of its body; a partial application evaluates its arguments when it is built; applying a costed
closure costs one plus its companion at the argument; a sampled function is a table, applied at
unit cost. `Function.update f a v` is priced from its definition, with companion
`fun x => 2 + (if x = a then 0 else 1 + fCost x)`, so the companion of a table records the
updates that built it. A simulation whose state holds functions is translated to
`OracleAdv.Timed.simulateHat`, whose state carries the companions from query to query; its
erasure theorem `erase_simulateHat_bind` needs only the erasure theorem of the handler. A
reduction whose result holds functions has the erasure theorem
`(R.timed xs').2.erase.bind (fun y => ret (ε y)) = R xs`, `ε` keeping the functions.
A reduction defined by structural recursion over its adversary, a handler of the adversary's
nodes such as `prfMacRedAux` and `mapAns`, gets a costed form by the same recursion over the
costed mirror: the continuation of a node of the adversary stands for the continuation of the
costed node, with the node's step cost as its cost companion, and the case analysis of a node
costs one. Its time follows from `OracleAdv.Timed.timeBound_fold`: when the handler's overhead
is at most `h` per unit of the adversary's time and `r` at a leaf, a handled adversary of time
`T` takes time `(1 + h) · T + r`. `OracleAdv.simulate` and `OracleAdv.subst` are the stateful
and stateless handlers whose overhead is the cost of answering a query, and `timeBound_simulate`
is their time law; the PRF-to-MAC reduction and the inner cascade reduction take time
`4 · T + 6` and `(6 + e) · T + 3`, with `e` a bound on the cost of the keyed function
([PRFMACTimed.lean](../Examples/PRFMACTimed.lean), [PRFTimed.lean](../Examples/PRFTimed.lean)).
The rules for calls, decisions, constructors and variables are those of [Hop26]. They follow the
translation of Isabelle's `time_fun` [Nip25, HOL-Time] and in addition charge one unit for each
call of a non-recursive function and for each decision of `if` and `match`; `derive_timed` also
charges one unit for each arithmetic operation, which `time_fun` counts as free. The two
conventions differ by a constant per call and per decision, which changes the constants `k` and
`c` of `k · T + q · t + c` (§4). A primitive without a body to price takes the cost registered
for it with `timed_cost f := e`.

`derive_reduction R` ([DeriveReduction.lean](../Tactics/DeriveReduction.lean)) takes a reduction
into `SPComp`, written in `do`-notation or with the constructors of `SPComp`. It reflects the
body into a tree `R.tree`, in which each adversary and each primitive (a field of a scheme
structure or a method of a class, such as `D.keygen` or `kit.enc`) is a binder, proves the
compile equation `R.compile_tree`, `(R.tree …).compile = R …`, by a term the kernel checks, and
runs `derive_timed R.tree`. At 2026-10-20 it derives the costed forms of 79 of the 112
reductions of its evaluation set.

A multi-stage adversary is a structure whose fields are its stages (trees or computations), a
state type and proof fields such as query bounds. `derive_timed_structure S`
([DeriveTimedStructure.lean](../Tactics/DeriveTimedStructure.lean)) defines its costed mirror
`S.Timed`: proof fields dropped, each stage a costed stage followed by its cost companion; the
erasure relation `S.Timed.Erases`, under which proof fields are stated about the erased stages;
and `S.Timed.TimeBound`, one bound per stage on the cost of computing the stage plus its run.
The stages run separately, so their bounds are not added. A reduction whose result is such a
structure is derived by `derive_reduction` field by field: `R.timed : … → S.Timed …` and
`R.erase_timed : … → (R.timed …).Erases (R …)`. A stage of a structure binder
(`A.choose`, `B.guess`) is a primitive of the reduction with a costed binder and a hypothesis
relating its erasure to the field.

A derived step cost follows from the code of the reduction by these rules. A costed form written
by hand carries step costs chosen by its author, which the kernel checks only through the
erasure theorem: that theorem determines the reduction and leaves the step costs unconstrained.

Scheme primitives and the adversary enter as cost parameters, as abstract modules do in the
cost logic of [BBGKS21]: the hash of `hashRed` through its cost companion, bounded by `t₀`; the
group exponentiations of `ckaDDHRed` through the cost of the view map, bounded by `tv`; the
adversary through its time `T`. An extractor chosen by `Classical.choose` has no code to price,
and its cost is a parameter: `logExtractor.timeBound_timed`
([FiatShamirROM/MPCitH.lean](FiatShamirROM/MPCitH.lean)) gives the extractor of the MPC-in-the-head
signature time `tExt`.

The kernel checks the erasure theorem, so an error in a step cost can misstate a running time
but cannot change the reduction whose advantage §1 bounds. The trusted base of a derived time
theorem is the rule set of `derive_timed` and the costs registered with `timed_cost`. The
asymptotic statements of §1 bound advantages; for a family of reductions indexed by the
security parameter, the time theorem at each index bounds the running time.

Three checks in the continuous integration of the CatCrypt repository read the Lean sources,
without loading Lean, and keep counts that may fall and never rise.

- Reductions without a certificate. A definition named as a reduction, inverter or extractor
  whose type is a computation or an adversary is certified when the sources of the two
  repositories hold its costed form, its erasure theorem and a time theorem, or its tree, its
  compile equation and a time theorem for the costed tree. At 2026-10-20 the CatCrypt
  repository has 22 certified and 358 uncertified reductions and CatCrypt-core 44 and 51.
- Reductions with exponential code. A reduction that draws a whole random function
  (`PMF.uniformOfFintype (X → Y)`) or computes the measurement distribution of a quantum
  adversary's state runs in time exponential in the bit length of `X` or of the adversary's
  register. The count over the CatCrypt repository is 0. A reduction that needs a random
  function samples it lazily, a fresh value for each new query, and its proof uses a lemma
  equating the lazy and the eager table: in [EagerLazyRF.lean](EagerLazyRF.lean),
  `SIVNonce.uniform_bind_run_simOracle_keyed` equates eager and lazy sampling behind a
  simulation, and `SIVNonce.lazyRF.timeBound_timed` bounds the time of the lazy sampler by the
  time of the adversary.
- Hand-written costed forms. The costed forms `R.timed` defined by hand, counted across the two
  repositories, number 110 at 2026-10-20.

## 3. What the complexity measures are for

Query bounds of adversaries. `OracleAdv.IsQueryBound A q` states that every path of `A` asks at
most `q` queries; `IsQueryBoundBy cost` weights each query; `QueryCostLe` states the same for
`OracleProg` trees ([Signatures/EUFCMA.lean](Signatures/EUFCMA.lean)). These are the hypotheses of
the statistical terms of §1, such as `q(q−1)/2 / |D|` above or `q / |T|` for guessing a tag in
`T`, and `isQueryBound_simulate` carries them through a reduction.

Expected cost of extractors. `CostComp` and `ecost` ([ExpectedCost.lean](../Unary/ExpectedCost.lean))
give the expected value of the charges a program accumulates; `ecost_bind_le` is the tower
law, and `ecost_retryN_le_div` bounds a loop retrying an attempt of expected cost `C` and
success probability `p` by `C / p`. A rewinding extractor is bounded with these two quantities, and the per-attempt cost is a
parameter; a time theorem of §2 for the prover makes it a function of the prover's running time.

Admissibility classes and computational UC. `UCAdmClass` ([UCAdmClass.lean](UCAdmClass.lean))
is a predicate on Kleisli arrows closed under `pure`, composition, coproducts and precomposition
with functions (`adm_pure`, `adm_bind`, `adm_mapSum`, `adm_precomp`); `ucCdist` is the distance
over admissible distinguishers. A `MonadCostModel` ([MonadCostModel.lean](MonadCostModel.lean)),
a cost on Kleisli arrows zero on `pure` and subadditive under composition, induces a class. On
`SPComp` the instances are the query class `spTreeQueryAdm`, the size class `spTreeSizeAdm`
([SizeBoundedUC.lean](SizeBoundedUC.lean)) and the shape class of `ct_spComp`
([CTAdmClass.lean](CTAdmClass.lean)). Over them are stated the levels `UCEmulatesL2` and
`UCEmulatesL3` ([UCLevels.lean](UCLevels.lean)) and `UCEmulatesCdist`
([CompUCEquivalence.lean](CompUCEquivalence.lean)), with transitivity, the implications between
levels and dummy-adversary completeness ([QueryBoundedUC.lean](QueryBoundedUC.lean)).

These classes bound the operations of a syntax-tree witness: the query class the `sample`,
`get` and `set` nodes on the worst path (`SPTree.queryCost`), the size class all nodes summed
over branches (`SPTree.size`), the shape class the sequence of operations, the same for every
input. The value in a `ret` node, a value written by `set` and the computation inside a
continuation carry no charge (`queryCost (ret a) = 0`, `size (ret a) = 1`). Every class
therefore contains every pure test `pure ∘ p`, by `adm_pure` and `adm_precomp`
(`adm_pure_predicate`, `adm_pure_predicate_size`). For a generator `G : S → Y` with
`|S| < |Y|`, the range test `p y = decide (∃ s, G s = y)` distinguishes `G` on a uniform seed
from the uniform distribution on `Y` with advantage at least `1 − |S|/|Y|`, so `ucCdist` of this
pair is at least that much in every class on `SPComp`. Computational indistinguishability is
carried by the convention of §1; the classes serve statements about queries, size and shape and
the structure of computational UC.

## 4. Relation to other cost analyses

A time certificate of §2 consists of a costed form whose step costs are derived from the code of
the reduction, an erasure theorem checked by the kernel, and a time theorem. The paragraphs below
compare it with the closest related work in the cost model, in what is derived, checked and
trusted, and in how adversaries enter.

EasyCrypt's cost logic [BBGKS21] attaches complexity restrictions to module signatures:
`compl[intr : k, x₁.f₁ : k₁, …]` bounds the time of a procedure, excluding calls to its functor
parameters, by `k`, and its number of calls to each parameter procedure `xᵢ.fᵢ` by `kᵢ` (§3.2).
Typing a module against a restriction generates an obligation, discharged in a Hoare logic for
cost whose judgements `E ⊢ {φ} s {ψ | t}` record in `t` the concrete time and the number of calls
of each abstract procedure (Defs. 4.1, 4.2). Operators are costed by rules, some supplied by the
user, and a variable costs one (§4.1, App. E). The abstract-call rule Abs (Fig. 6) charges a call
of an abstract procedure `x.f` one unit in the entry `x.f` and, for the `k`-th call it makes to a
parameter procedure `xᵢ.fᵢ`, a bound `tᵢₖ`, under an invariant indexed by the call counts. The statement
shape is that of §2: the time of a reduction is its own cost plus, for each oracle or adversary
procedure, the number of calls times the cost of a call, with the cost of the adversary a
parameter; an abstract module with a restriction plays the role of the costed adversaries `A'`
with erasure `A`, time at most `T` and `q` queries. In EasyCrypt the cost is a property of the
program, proved interactively in a logic whose soundness (Theorem 4.1, relative to a
denotational semantics that takes the worst case over final memories) is a metatheorem; the
implementation of the logic and the operator costs are trusted. In CatCrypt the costs are
annotations on a second definition `R.timed`, `derive_timed` derives them together with the
erasure theorem, and the kernel checks that theorem and the time theorem; the trusted base is
the rule set and the `timed_cost` registrations, and the program logic of the advantage bounds
carries no costs. Rule Abs bounds each call of a parameter procedure separately, and
`timeBound_simulate` uses one bound `t_impl` for every query. The example of [BBGKS21, §2]
concludes with an existential over inverters in a complexity class (Theorem 2.1); a time theorem
of CatCrypt bounds the named reduction `R`. For UC, [BBGKS21] puts cost restrictions into the
module types of simulators and environments, and transitivity yields the sequential composition
of the two simulators with the corresponding cost (§5, Lemma 5.1, Theorem 5.2).
`UCEmulatesCSim` takes an explicit simulator map `sim`, and the time of `sim A` is the subject of
a separate time theorem. EasyCrypt removed the cost logic on 2024-03-29 [EC24]; the commit
message states that it "does not implement what is needed, and is then barely used" and that
"its implementation is invasive and duplicates some internal mechanisms".

Hopwood's `assert_efficient` [Hop26, Ironwood] rejects a definition that is `unsafe`, `partial`
or `noncomputable` and derives a cost function `f.cost` with the binders of `f`: a call costs one
plus the callee's cost at its arguments, a recursive call one plus `f.cost`, `if` and `match` one
plus the branch taken; constructors, literals, projections and local variables are free; a
callee without a cost function gets one derived on demand; a primitive (an axiom, an opaque
definition, a recursor, `Nat` arithmetic) takes a cost registered with `efficient_cost`; and
each function-typed binder is followed by a cost companion. The same pull request adds an
instrumented translation: the class `Costed` gives each type a costed form, the costed form of a
function pairs it with an instrumented version, a Kleisli arrow of the writer monad `Nat × -`,
and `f.inst` is defined term by term. `derive_timed` takes its translation rules and its
derivation on demand from this code. The two share the rules for calls, decisions, constructors
and variables, one cost companion after each function binder and one for each applied field of a
structure binder, registered costs for primitives, and the description of the trusted base as
the rules plus the registered costs; in both, a bound on the derived cost is an ordinary theorem.
For a computable data function `f`, `derive_cost f` ([DeriveCost.lean](../Tactics/DeriveCost.lean))
prices the body that Lean keeps for the equation lemmas of `f`, which is the body that [Hop26]
prices. In [Ironwood] the relation between the instrumented and the original program is a
predicate `Consistent`, whose documentation states that it cannot exclude an instrumented
function that reports too little cost, and at the cited head no theorem relates `f.inst` to `f`.
For a reduction, that relation is the erasure theorem `(R.timed xs').2.erase = R xs`, which
`derive_timed` proves and the kernel checks. Most reductions of §1 are `noncomputable` functions
into `SPComp`, which `assert_efficient` rejects before deriving a cost; `derive_reduction`
reflects such a reduction into an `SPTree` with a kernel-checked compile equation and derives the
costs of the tree, whose sampling, query and state nodes cost one unit each. In [Ironwood] the
adversary is a function parameter priced by its companion. In CatCrypt it is a costed tree whose
time `T` bounds every path, and a handler defined by recursion over the adversary's nodes is
translated to recursion over the costed tree, with time `(1 + h) · T + r` by
`OracleAdv.Timed.timeBound_fold`. The costed form of a function in [Ironwood] is higher-order and
dependent, and containers have costed forms (`List (WithCosts α)` for `List α`); the costed
closures of `derive_timed` have first-order domains, and a function inside a list or an option is
refused.

Isabelle's `time_fun` [HOL-Time] defines a step-counting function `T_f` from the defining
equations of `f` by the translation of [Nip25, §1.5]: an equation `f p₁ … pₙ = e` gives
`T_f p₁ … pₙ = T⟦e⟧ + 1`; a call `f e₁ … eₙ` costs the costs of its arguments plus
`T_f e₁ … eₙ`; variables, constructors and the predefined operations on booleans and numbers
cost 0 (`time_fun_0`); `if` and `case` cost the condition plus the branch taken; `let` charges
its bound term once; and the `+ 1` is dropped for a non-recursive function. A functional
argument is passed as a pair of the function and its time function (`T_foldl`), and a function
defined in a locale takes a time function `T_f` for each locale parameter `f` it uses. The costed
closure `(f, fCost)` of §2 is the pair of `T_foldl`, the cost companions of function binders are
the time functions of locale parameters, and the `let` rule of §2 is that of §1.5. `derive_timed`
in addition charges one unit for each call of a non-recursive function, for each decision of
`if` and `match`, and for each arithmetic operation on `ℕ`, `ZMod p` and fixed-width words. By
[Nip25, §1.5.2], which follows Sands in counting only non-primitive calls, the two conventions
differ by a constant per call and per decision: the order of growth of the time function is the
same, and the constants `k` and `c` of a bound `k · T + q · t + c` differ. `time_fun` refuses
partial application, which `derive_timed` prices by evaluating the arguments when the partial
application is built. `time_fun` defines `T_f` alone, and its manual states that the framework
"is not verified" and that "there is no underlying formal model"; the correspondence of `T_f`
with `f` rests on the translation. `derive_timed` defines a mirror of `R` whose erasure theorem
the kernel checks, which confines the trust to the step costs. The option `equations` of
`time_fun` derives `T_f` from proved equations in place of the definition. The same option for
`derive_timed` would price a program provably equal to `R`, with the erasure theorem stated
relative to those equations, and would give costed forms to definitions whose Lean body is not
the intended algorithm.

Danner, Licata and Ramyaa [DLR15] translate a call-by-value λ-calculus with inductive types into
a complexity language by a monadic translation into the writer monad `C × −` (§3.2). The
potential of a function maps argument potentials to a cost and a result potential,
`⟨⟨σ → τ⟩⟩ = ⟨⟨σ⟩⟩ → C × ⟨⟨τ⟩⟩`; an abstraction is free, an application costs one plus the costs
of the function, of the argument and of the body, and `let` charges its bound term once
(Fig. 5). Potentials may then be abstracted to sizes (§§4–5). The costed closure of §2 is the
first-order case of this translation without size abstraction: when the potential of a value is
the value, the potential of a function with first-order domain and codomain has type
`X → C × Y`, isomorphic to `(X → Y) × (X → ℕ)`, and the application rule of Fig. 5 is that of a
costed closure. The translation replaces a function by its potential; the costed closure keeps
the function beside its companion, so that erasure is a projection. The bounding theorem of
[DLR15] (Theorem 5.7) states for every well-typed term that its operational cost is at most the
cost component of its translation and that its value is bounded by the potential component; it
is proved once for the language, by logical relations. CatCrypt proves the value component, at
the identity size abstraction, as the erasure theorem of each reduction; Lean has no operational
cost semantics of its terms against which a cost component could be proved. [DLR15] admits
higher-order potentials and has no probabilistic or oracle constructs.

calf [NSGH22] is a dependent type theory with one effect, `step^c(M)`, which incurs cost `c`
before `M`, and a proposition `¶_E`, the extensional phase, under which cost is trivial; by
noninterference every function from an intensional to an extensional type is constant
(§§1.1–1.3). A cost bound is a refinement defined in the theory, such as
`hasCost(A, e, c) ≔ Σ a : A. e = step^c(ret(a))` (§1.4). The cost model is chosen for each
algorithm by placing `step` by hand, counting for instance comparisons for sorting or `mod`
operations for Euclid's algorithm (§§3.2, 4), and a recurrence is written by hand and related to
the program by proving the bound. Both calf and CatCrypt separate behaviour from cost and
guarantee that cost annotations leave behaviour unchanged: the extensional equality
`◯(insertionSort = mergeSort)` of calf corresponds to two costed forms with different step costs
and the same erasure. A calf program is written in the cost-aware language, and noninterference
holds for every program by the type theory and its model (§5). A CatCrypt reduction is a plain
Lean definition, `R.timed` a second definition, and the separation is the erasure theorem,
proved for each reduction. The step costs of a derived costed form follow the fixed rules of
`derive_timed`; those of a hand-written costed form are chosen by its author, as the placement of
`step` is in calf, and in both cases the agreement of the costs with an intended cost model is
not part of what is proved. Cost is the only effect of [NSGH22]; the costed trees of CatCrypt
carry sampling, queries and state.

Forster and Kunze [FK19] extract Coq functions of simple polymorphic types to the weak
call-by-value λ-calculus L, whose time is its number of β-steps; for decision functions, L and Turing machines
simulate each other with polynomial overhead in time and constant-factor overhead in space
[FKR20, Theorem 2], so L is a reasonable machine model. Correctness of the extraction is a
logical relation, and its time-indexed form uses complexity measures
`C(A → B) = A → C_A → ℕ × C_B`, with `C_A = 1` for an encodable `A`: the measure of `map` takes
`f` and the measure of `f` (§3.2). An instance `computableTime f τ` is proved by tactics that
count β-steps and leave the recurrence inequalities that the user-supplied measure `τ` must
satisfy (§5.4). At first-order arguments the measure is the cost companion of §2:
`C(X → Y) = X → 1 → ℕ × 1 ≅ X → ℕ` for encodable `X` and `Y`. In [FK19] the measure is chosen by
the user and checked against the β-steps of L, and nothing beyond Coq is trusted; `derive_timed`
computes the measure from its rules, and no machine model checks it. The deep language D of
CatCrypt ([Complexity/D](../Complexity/D/README.md)) counts β-steps as L does and has a
certifying reflection `reflect_d` after [FK19]; a relation `TimedSim E K n x t` from a costed
tree `x` to a D evaluation tree `t`, with `E` relating the leaves, gives
`t.cost ≤ n + K · stepTime x` (`TimedSim.cost_le`, [Link.lean](../Complexity/D/Link.lean)). The
theorem relating the two cost models would be a `computableTime` instance whose measure is the
one `derive_timed` computes: for a reduction `R` with costed form `R.timed` and reflection
`R.d`, the relation `TimedSim E K n (R.timed xs').2 t` for the evaluation tree `t` of `R.d`,
proved construct by construct in the manner of §5.4 of [FK19]. A time theorem
`k · T + q · t + c` would then give a time bound in D, and through it the `TimeReduction` and
`polyTime_transfer` of [Complexity.md](Complexity.md). That theorem needs operands of bounded
width, or companions that charge bit length, since `derive_timed` charges one unit for an
operation on `ℕ` and D charges its bit length; a reflection that covers recursion over the
adversary's tree, recursive helpers and structures with function fields, where `reflect_d` has
`foldl` and `iter` as its only recursion; and, for the chain from D to Turing machines, a
simulation of the primitive steps of D in L, which [FKR20] does not provide. A query node of D
is matched with a branching of the costed tree over the oracle's answers (`TimedSim.query`),
since D charges the maximum over them.

FCF [PM15, FCF] parametrises asymptotic security definitions by an admissibility predicate on
families of adversaries (§3.7). The cost of a Gallina function is an assumed relation
`FunctionCostModel := ∀ A B, (A → B) → nat → Prop`, with closure properties collected in a
class: identity and constants cost 0, composition adds, extensionally equal functions have equal
costs, and a conditional costs its condition plus both branches. `oc_cost` gives an oracle
computation a cost as a function of the cost of the oracle, and the paper states that "the cost
model for Gallina functions is axiomatic". VCVio [VCVio] instruments oracle computations with
an additive cost per query and proves once, for this uniform instrumentation, that it does not
change the output distribution (`fst_map_costDist`). In its ElGamal example the instrumented
reduction places `addTell` by hand at each query site and takes its own overhead as a parameter
`intrinsic`, and a theorem states that the pathwise cost is `intrinsic` plus one use of each
adversary procedure.
FCF's cost of running against an oracle and VCVio's count of interface uses agree with the query
part `T_A + q_A · t_impl` of `timeBound_simulate`. The cost of the code of the reduction itself
is an assumed relation invariant under extensional equality in FCF, so that it belongs to a
function as a mathematical object, and a free parameter in VCVio; `derive_timed` derives it from
the code of `R`, and the erasure theorem fixes the code that was priced. FCF's function costs are
constants over all arguments; the cost companions of §2 are functions of the arguments, and the
worst case is taken in the time theorem. VCVio proves its erasure property once because the
instrumentation is a uniform handler; CatCrypt proves the erasure theorem for each reduction
because a meta-program inserts the step costs into the code of each.

Implicit computational complexity characterises a complexity class by a restriction of the
language whose typable programs are closed under composition, as safe recursion [BC92] does for
the polynomial-time functions; Atkey [Atk24] surveys these characterisations and extends them to
dependent types. The `UCAdmClass` laws of §3 take this closure under composition as their model:
the admissible arrows form a wide subcategory of the Kleisli category. Through `adm_precomp`,
which admits precomposition with every function, the laws also admit every pure test, so a class
satisfying them bounds the effectful operations of an arrow and leaves its pure computation free.
The running time of that pure computation in a reduction is what the derived costs of §2 certify.

## References

- [Atk24] R. Atkey. Polynomial time and dependent types. POPL 2024.
- [BBGKS21] M. Barbosa, G. Barthe, B. Grégoire, A. Koutsos, P.-Y. Strub. Mechanized proofs of adversarial complexity and application to universal composability. CCS 2021, pp. 2541–2563. doi:10.1145/3460120.3484548. Full version: HAL hal-03469015.
- [BC92] S. Bellantoni, S. Cook. A new recursion-theoretic characterization of the polytime functions. Computational Complexity 2, 1992.
- [BGHZ11] G. Barthe, B. Grégoire, S. Heraud, S. Zanella-Béguelin. Computer-aided security proofs for the working cryptographer. CRYPTO 2011.
- [BGZ09] G. Barthe, B. Grégoire, S. Zanella-Béguelin. Formal certification of code-based cryptographic proofs. POPL 2009.
- [BR06] M. Bellare, P. Rogaway. The security of triple encryption and a framework for code-based game-playing proofs. EUROCRYPT 2006.
- [DLR15] N. Danner, D. R. Licata, R. Ramyaa. Denotational cost semantics for functional languages with inductive types. ICFP 2015, pp. 140–151. doi:10.1145/2784731.2784749. Long version: arXiv:1506.01949.
- [EC24] The EasyCrypt development team. EasyCrypt commit 41c2667f7fa794d0145ea30d42cc77285c1270d7: removal of the cost logic, 2024-03-29. https://github.com/EasyCrypt/easycrypt/commit/41c2667f7fa794d0145ea30d42cc77285c1270d7.
- [FCF] A. Petcher. FCF: The Foundational Cryptography Framework. https://github.com/adampetcher/fcf, files `src/FCF/WC_PolyTime.v` and `src/FCF/Admissibility.v`.
- [FK19] Y. Forster, F. Kunze. A certifying extraction with time bounds from Coq to call-by-value lambda calculus. ITP 2019, LIPIcs 141, 17:1–17:19. doi:10.4230/LIPIcs.ITP.2019.17.
- [FKR20] Y. Forster, F. Kunze, M. Roth. The weak call-by-value λ-calculus is reasonable for both time and space. Proc. ACM Program. Lang. 4(POPL), 2020. doi:10.1145/3371095. arXiv:1902.07515.
- [HOL-Time] J. Stahl, T. Nipkow. Theories `Time_Commands`, `Time_Functions` and `Time_Manual`. Isabelle2026, HOL-Library. https://isabelle.in.tum.de/library/HOL/HOL-Library/Time_Manual.html.
- [Hop26] D.-E. Hopwood. Are the reductions efficient? An `efficient` keyword for Lean. Talk, October 2026; implementation in the zcash/ironwood repository.
- [Ironwood] D.-E. Hopwood. meta: efficient def and assert_efficient (prototype). zcash/ironwood pull request 228, head 6b83c6f893fb3e26b6f11198c342020cb7d52ad8, 2026. https://github.com/zcash/ironwood/pull/228.
- [Nip25] T. Nipkow (ed.). Functional Data Structures and Algorithms: A Proof Assistant Approach. ACM Books, 2025. doi:10.1145/3731369. Chapter 1 by T. Nipkow.
- [NSGH22] Y. Niu, J. Sterling, H. Grodin, R. Harper. A cost-aware logical framework. Proc. ACM Program. Lang. 6(POPL), 2022. doi:10.1145/3498670. arXiv:2107.04663.
- [PM15] A. Petcher, G. Morrisett. The Foundational Cryptography Framework. POST 2015, LNCS, pp. 53–72. doi:10.1007/978-3-662-46666-7_4. arXiv:1410.3735.
- [VCVio] VCVio contributors. VCVio: a framework for oracle computations and cryptographic proofs in Lean. https://github.com/Verified-zkEVM/VCVio, commit 96754a37e739.
