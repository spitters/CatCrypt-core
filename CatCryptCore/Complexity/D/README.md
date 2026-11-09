# D: a deep call-by-value language with intrinsic cost

D is a typed call-by-value λ-calculus embedded in Lean, whose terms carry their own cost.
A Lean function carries no cost of its own, so a time measure on `SPComp` arrows collapses to
query cost (`spTreeTimeCost_eq_spTreeQueryCost` in `XDijkstra/XTimedMonad.lean`). In D the
cost of a program is the number of evaluation steps of its term.

The cost model follows the weak call-by-value λ-calculus L of Forster and Kunze:

* Y. Forster, F. Kunze. *A certifying extraction with time bounds from Coq to call-by-value
  λ-calculus*. ITP 2019, LIPIcs 141. doi:10.4230/LIPIcs.ITP.2019.17
* Y. Forster, F. Kunze, M. Roth. *The weak call-by-value λ-calculus is reasonable for both
  time and space*. POPL 2020, PACMPL 4. doi:10.1145/3371095

In L, time is the number of β-steps, and the second paper shows that this measure is
polynomially related to Turing-machine time. D counts β-steps in the same way and adds
branches and effect nodes (`sample`, `get`, `set`, `query`, as in `SPTree.queryCost`) at one
step each, and primitive operations at the cost `Prim.cost`.

## Cost of primitive operations

Operations on `Bool` and on fixed-width words cost one step (the word-RAM convention for a
fixed word width). Operations on `ℕ` are charged by the bit length `Nat.size` of their
arguments (logarithmic cost):

| Operation | Cost |
| --- | --- |
| `natAdd`, `natSub`, `natEq`, `natLt` | `max (size x) (size y) + 1` |
| `natMul`, `natDiv`, `natMod` | `size x * size y + 1` (schoolbook) |
| `Bool` and word operations | `1` |

The shifts `wshl` and `wshr` take a natural-number amount and cost one step: an amount of at
least the word width gives the zero word, so only amounts below the word width are
meaningful. The evaluator places `p.cost v` ticks for a primitive operation `p` at the
argument `v`, so `CTree.cost` remains the number of ticks and effect nodes.

Unit cost on unbounded integers is too strong a model. A unit-cost RAM with multiplication
decides in polynomial time every problem in PSPACE:

* J. Hartmanis, J. Simon. *On the power of multiplication in random access machines*. 15th
  Annual Symposium on Switching and Automata Theory (SWAT 1974), IEEE, 13–23.

Under the logarithmic cost criterion, where an operation costs the bit lengths of its
operands, RAM time and Turing-machine time are polynomially related:

* S. A. Cook, R. A. Reckhow. *Time bounded random access machines*. JCSS 7(4), 1973, 354–375.

D charges `ℕ` operations under this criterion. That a primitive step of D is simulated in L by
a number of β-steps polynomial in its cost, which would place D's cost among the reasonable
time measures of Forster, Kunze and Roth, is not proved here.

## Modules

| Module | Content |
| --- | --- |
| `Tree` | `FTy` (finite ground types), `CTree` (effect trees with a `tick` node), `CTree.cost` (worst case over the branches), `CTree.run` (meaning in `SPComp`), `CTree.Rel` (relational lifting) |
| `Syntax` | `Ty`, `Val`, de Bruijn `Var`, `Env`, `Prim`, the intrinsically typed terms `Tm Γ τ`, `Tm.compose`; the module docstring maps each construct of hax-lean's `TExpr` to D |
| `Semantics` | the interpreter `Tm.interp`, the evaluator `Tm.eval` (a tick at every step), the denotation `Tm.den` / `Tm.denote`, the logical relation `ValRel` and the adequacy theorems |
| `Cost` | `Tm.cost` and its compositionality lemmas |
| `Examples` | a list sum by `foldl`, a function applied twice, a sampler |
| `TimeAdm` | time admissibility of `SPComp` arrows by closed D-terms, its graded laws, the time-bounded distance `ucCdistTime` |
| `DNHered` | the hereditary Diller–Nahm object `Ty.dnH` of a type, the Dialectica predicate `Ty.simPred` of a value, and the soundness `Tm.dnH_sound` of the morphism of a pure term at a first-order variable |
| `DNHeredFull` | the object `Ty.hatH` with call demands at function types, the translation `Tm.dtH` with `Tm.dtH_forget`, `Sim.arr_iff_dnSoundH` at every argument type and `Tm.dnHH_sound` |
| `OpenTree` | the open costed tree `Tm.dtO` with the calls of function variables as operations, `Tm.wpFold_dtC_eq_liftM_dtO`, `Tm.cost_le_of_useBound` and `Tm.useBound_liftM_substHandler_clocked` |
| `PriceSound` | the gluing of the Diller–Nahm category along `CTree`: `PriceSound`, `KeepsTokens`, `PriceObj`, `Sim.arr_iff_priceSound` and `Tm.priceHom` |
| `PriceTransfer` | transport of price-soundness along a change of implementation (`CTree.SimLE`, `DNLens.PriceSound.impl`) and along a square of specifications (`DNLens.PriceSound.spec`, `DNLens.KeepsTokens.of_dnSquare`), and of morphisms of the gluing along both (`PriceObj.transport`, `PriceHom.transport`) |
| `RGraphInterp` | the abstraction theorem of D with cost: a base relation on the finite ground types extends to every type (`Ty.relB`), and a term that respects it gives related values at equal cost (`Tm.eval_lift`, `Tm.abstraction_cost`); D in the reflexive-graph model (`Tm.rg_abstraction`) and in the polynomial model over it (`Ty.polyC_pos_rel_iff`) |
| `FreeNI` | non-interference with timing as a free theorem: equal cost, and equal trees at a public result type, for environments that agree on the public variables (`Tm.cost_eq_of_secret`, `Tm.free_noninterference`) |
| `GenericGroup` | generic group algorithms: results on two representations of the group correspond under a homomorphism or an isomorphism at equal cost (`hom_free`, `iso_free`, `hom_commute`, `iso_commute`), and square-and-multiply exponentiation (`powT_eval`, `powT_commute`) |

## Reflection of Lean definitions

The command `reflect_d f` (module `Reflect`, tests in `ReflectTest`) is a certifying extraction
of a Lean definition `f` into D, after Forster and Kunze (ITP 2019), who extract Coq functions
to L with MetaCoq and certify each extraction by a generated correctness relation. It defines
the D-term `f.d : Tm Γ τ`, whose context `Γ` holds the parameters of `f`, and proves the
denotation theorem `f.d_den`: `f.d.den ρ = .ret (f x₁ … xₙ)` when `f` returns data, and
`f.d.denote O ρ = f x₁ … xₙ` for every oracle `O` when `f` returns `SPComp α`. The certificate
is a derivation of the judgements `Den` and `DenM`, one lemma per construct, assembled by the
command and checked by the kernel; the cost of `f.d` is then `Tm.cost`, so a bound on it is a
time bound for `f` in D's model. A parameter `A : α → β` or an adversary `A : α → SPComp β` is
a D function value with the hypothesis that it computes `A`; an `Option` value is represented
as a sum with `Unit` (`optEnc`). The fragment is: `ℕ`, `Bool`, `Unit`, `BitVec w` for a numeral
`w`, products, sums and lists; λ-terms, application, `let`, literals, the operations of `Prim`
and the decisions of `=`, `≠`, `<`, `≤`, `∧`, `∨`, `¬`; pairs and projections; `if`, `bif` and
matches on `Bool`, `Option`, `Sum`, pairs and lists (non-recursive, as `lcase`); `List.foldl`
as `foldl` and `Nat.iterate` as `iter`; `pure`, `bind`, `SPComp.sample` of a finite ground
type, `SPComp.get` and `SPComp.set` at a location `FTy.loc f n`. A constant outside the Lean,
Std and Mathlib libraries is unfolded; a Lean inductive type is `mu` of its signature and a
structural recursion over it the eliminator `fold` (section "Inductive types"); any other
recursive definition, a type without representation and any other constant are refused with a
message naming them.

## What is proved

* The evaluator and the denotation give related trees in related environments
  (`Tm.interp_rel`, the fundamental lemma of the logical relation `ValRel`). At first-order
  types the evaluator with its ticks erased is the denotation (`Tm.eval_erase`), and both have
  the same meaning in `SPComp` (`Tm.run_eval`).
* The cost of a bind is at most the cost of the tree plus a bound on the continuation at its
  leaves (`CTree.cost_bind_le`); a sample costs one plus the maximum over its branches
  (`CTree.cost_bind_sample`, `Tm.cost_letE_sample`).
* An application costs the function, the argument, one β-step and the body
  (`Tm.cost_app_le`, `Tm.cost_app_lam`); a `letE` costs its bound term once
  (`Tm.cost_letE_le`, `Tm.cost_letE_ret`); variables cost nothing (`Tm.cost_var`); a
  primitive operation costs its argument and `Prim.cost` at the argument's value
  (`Tm.cost_prim`, `Tm.cost_prim_le`).
* The sum of a list `l` by `foldl` costs at most `length l * (size (sum l) + 2)`
  (`Examples.sumBody_cost_le`); on words, a function applied twice to the successor costs
  exactly six steps (`Examples.twice_succW_cost`).
* `foldl` and `iter` cost at most the number of iterations times one plus the cost of one
  application (`foldT_cost_le`, `iterT_cost_le`).
* Precomposition of function terms adds the costs (`Tm.cost_compose_le`,
  `Tm.allRet_compose`, `Tm.cost_app_compose_le`).

## Time admissibility

The module `TimeAdm` charges the time of a distinguisher in the cost model of Forster and
Kunze cited above. A Kleisli arrow `f : Val a → SPComp (Val b)` on first-order types is
admissible at time `n` (`TimeAdm`) when a closed D-term evaluates to a closure whose
application to every input costs at most `n` steps and means `f`. The laws of `UCAdmClass`
hold in graded form: `pure` at time 1, bind at the sum of the times plus 3, the coproduct at
the maximum of the times plus 2, and precomposition only by a function that a closed D-term
computes, at the sum of the two times plus 3; precomposition by an arbitrary Lean function is
not admissible at any constant time. `ucCdistTime` is the computational distance over the
distinguishers admissible at time `t`, a pseudometric with the composition bounds that these
laws give. In the query, size and shape classes a pure test is free, and step time on `SPComp`
equals query cost; the time class charges the range test of a generator at about the number of
seeds times the cost of the generator. Its coproduct realizer uses renaming and weakening of
terms (`Tm.rename`, `Tm.weaken`, defined in `Syntax`; `Tm.interp_rename`, `Tm.eval_weaken`, in
`Semantics`). Its relation to the other classes is in
`CatCryptCore/Crypto/Complexity.md`, section "Time over the deep language D".

The module `Asymptotic` grades this class by a security parameter. A family of arrows is
polynomial-time (`PolyTimeFam`) when its member at `n` is admissible at time `p n` for a
polynomially bounded `p`; asymptotic security (`AsymSecure`) and asymptotic computational
indistinguishability (`UCTimeNegl`, `ucCdistTime` negligible at every polynomial time) quantify
over these families only. The transfer theorem `polyTime_transfer` and its corollary
`asymSecure_of_reduction` take a concrete reduction through time reductions of polynomially
bounded time and derive asymptotic security; `TimeRealizer.ofBody` turns the term of a
`reflect_d` extraction into a realizer, used in the instance `addTwo_asymSecure`. Details:
`CatCryptCore/Crypto/Complexity.md`, section "Asymptotic security over D".

## Relation to hax-lean's typed IR

The typed IR `TExpr` of hax-lean, the input of the CatCrypt compiler's front, embeds into D
on the fragment the front accepts: literals, variables, `let`, sequencing, pairs and their
projections, conditionals, binary operations implemented by D primitives, assignments, and
counted loops `forFold` whose state is the set of names the compiler carries through the
loop. The embedding preserves meaning against the control-flow semantics `Hax.denote'`, and
the cost in D of the embedded term is at most the number of evaluation steps of the source
under that semantics (factor 1, constant 0), with loop tests and increments charged at
their bit length. The module is `CatCrypt.Complexity.TExprToD` in the CatCrypt development
repository, where the compiler's loop analysis is available. This is a simulation between
two concrete measures, of the kind Forster, Kunze and Roth prove between L and Turing
machines.

## Design

Terms are intrinsically typed and scoped (`Tm : List Ty → Ty → Type`). A function value is a
Lean function `Val a → CTree (Val b)` into costed trees, so the evaluator is a definitional
interpreter: it is defined by structural recursion on the term, and a closure is produced
only by evaluating a `lam`.

Recursion is structural: `foldl` over lists, `iter` over `ℕ`, the constructor match
`lcase`, and the eliminator `fold` of the inductive types `mu S`. There is no general fixed point, so every term denotes a total function and neither
the evaluator nor the denotation needs fuel. A Lean definition by structural recursion on a
list or a natural number is reflected through these schemes; a definition by well-founded
recursion needs a bound on its recursion depth, which becomes the count of an `iter`.

Unlike L, which encodes data by Scott encodings and counts their β-steps, D has native
products, sums, lists and primitive operations; a constructor or a projection costs nothing
and a branch costs one step, the convention of `derive_timed`.

## Dependent products and sums

`Ty.pi f B` and `Ty.sig f B` are the dependent product and sum of a family `B : f.den → Ty` over
a finite ground index `f` (`FTy`), so that a type computed from a finite datum, such as a record
whose field types depend on a tag or a table of types `beta : Fin n → Type`, is a code of D.
The index ranges over `f.den`, defined before `Ty`: an index over the values of a type of D
would make `Ty` and `Val` an inductive-recursive pair, which Lean's kernel does not provide.
`Val`, `ValRel`, `Ty.hat` and `Sim` are defined by recursion on the code: a dependent function
of the values of the family, a dependent pair of an index and a value, and the translated
values are the table of the translated components and the dependent pair of translated
values.

* `ptab ts`: a table, its components evaluated in the order of `tabT` (`tabDep`); it costs the
  sum of its components and nothing of its own. `papp t j`: the component at a static index,
  free.
* `spair j x`: a pair at a static index, free; `scase s ks`: the branch of the index of a pair,
  one step plus the branch.
* `fcase i ks`: the branch at the value of a finite ground value, one step plus the branch. A
  read of a table at a computed index is `fcase i fun j => papp t j`: one step, the read of a
  tabulated function of `derive_timed` (rule (m)).

The charges of `Tm.dt` are the same, a table charged the sum of the charges of its pure
components (`tabCost`, `tabCost_add`); the soundness theorem `Tm.dtC_timedSim` covers the five
constructs (`tabDep_stepN` for the table), and with it `Tm.cost_le_dt`, `Tm.dt_run` and
`Tm.dt_erase`. Test: `CatCryptCoreTest/Complexity/D/PiSigTest.lean`.

## Stores

A store `Ty.store f a` is the dependent product over a finite ground index `f` at the constant
family `a`: its values are the tables `f.den → Val a`. It is read and written at a computed
index by two primitive operations of one step each, `Prim.sget` and `Prim.sset` (the write is
`Function.update` at the decision of equality of the source); a finite ground table
`FTy.tab (n + 1) r` has the same two operations, `Prim.tget` and `Prim.tset`. As primitives they
enter the evaluator, `Tm.dtC` and the soundness theorem `Tm.dtC_timedSim` through the existing
case of primitive operations (`Prim.unitCost`), and `Prim.fo` covers them by the field `ha` of
first-order values of a store.

`reflect_d` represents a function type `X → Y` at a component of a product, a sum or a list,
with `X` a finite ground type and `Y` first-order data that `Ty.foB` accepts and that is not a
table of a finite ground type, as `Ty.store`; it reflects `t i` and `Function.update t i v` on a
store or a table as these operations, and refuses a function parameter written by
`Function.update`.

The unit charge is the word-RAM convention at an index of `log N` bits for a table of `N`
entries. A program of D with `k` store operations on stores of `N` entries is simulated on a
pointer machine or a Turing machine by a balanced tree per store at `O(log N)` steps per
operation times the size of an entry, and a store used after it was written costs no more with
path copying (Driscoll, Sarnak, Sleator, Tarjan, *Making data structures persistent*, JCSS
38(1), 1989); this simulation is not proved here.

`derive_timed` charges a write to table data `Function.update t i v` one unit plus
`Function.update.timedCost` and its arguments, and a table read one unit plus its argument;
a table under a name that does not unfold at reducible transparency is such data, and
`link_timed` links it by `DSim.prim`. A table held in the state at a type with a costed form is
a costed closure for `derive_timed` (the write's companion is the read of the definition), which
D does not represent. Tests: `CatCryptCoreTest/Complexity/D/StoreTest.lean`,
`CatCryptCoreTest/Tactics/LinkTimedStoreTest.lean`.

## Indexed inductive families

`Ty.imu f S i` is the inductive family over a finite ground index `f` of the indexed signatures
`S : f.den → ISig f`, at the index `i`: a further constructor of an indexed signature names, at
each recursive position, the index of the child there. Its values are the indexed W-type `IW` of
the constructors with their fields. The index ranges over `f.den`, a type defined before `Ty`: an
index over the values of a type of D would make `Ty` and `Val` an inductive-recursive pair. A
static index needs no family: a type computed by recursion on a parameter is a code of D.

* `icon`: the node at its index, its children a table whose component at a position is at the
  index that position names; free.
* `ifold`: the eliminator at a motive family `c : f.den → Ty`, from a value at `i` to `c i`, the
  step functions a table over the indices; a step receives the field, the table of the children
  and the table of the recursive results, closures on `unit` at the types of the motive at the
  indices of the children; one step per node visited plus the step there, as `fold`.

`ValRel` and `Sim` at `imu` are the lifting `IWLift` over the indexed W-type and
`Ty.hat (imu f S i)` the indexed W-type of the translated fields; the charges of `Tm.dt` price
`icon` at nothing (`conHatI`) and `ifold` as `fold` (`foldHatI`), and the soundness theorem
`Tm.dtC_timedSim` covers both (`conAtI_sim`, `foldIW_sim`). Test:
`CatCryptCoreTest/Complexity/D/IMuTest.lean` (binary trees of bounded depth, an eliminator at a
constant motive and one into a motive family whose type changes with the depth).

## Inductive types

`Ty.mu S` is the polynomial inductive type of a signature `S : Sig`: a list of constructors,
each with a field type and recursive positions that are none or indexed by a finite ground
type, the first constructor without recursive position. Its values are the W-type whose shapes
are a constructor `c : S.Ctor` with a value of its field (`S.Fld c`) and whose positions are
those of the constructor (`S.Pos c`). A field may hold functions: the logical relation `ValRel`
and the relation `Sim` of the translation are, at `mu S`, the lifting `WLift` over the W-type
(two nodes of one constructor with related fields and related children), and the translated
values `Ty.hat (mu S)` are the W-type of the translated fields (`Sig.hatF`). Lists (kept as the
type `list` of their own), binary trees, oracle trees with answers in a finite ground type and
strategies with challenges in a finite ground type are instances.

* `con`: a node from the argument of its constructor; the children of a constructor with
  positions `some f` are a table, a value of the dependent product `pi f fun _ => mu S`, whose
  components are evaluated where the table is built (`ptab`): a constructor costs nothing, as
  `derive_timed` charges a constructor.
* `fold`: the eliminator at a constant motive, a paramorphism with one step function per
  constructor, which receives the field, the children and the recursive results; one step per
  node it visits plus the step function there, the recursive results evaluated when the step
  applies them, as a call of a structural recursion costs one plus its body. A case analysis
  is the `fold` that applies no recursive result.

The charges of `Tm.dt` (`TranslateDt`) price `con` at nothing (`conHat`) and `fold` by one plus
the step at the root and one plus the step at a child per application of its result
(`foldHat`); the soundness theorem `Tm.dtC_timedSim`
covers both, by induction on the signature and on the value (`conAt_sim`, `foldW_sim`). The
judgements of `Reflect` have the rules `Den.con`, `Den.fold` (the eliminator denotes a recursion
`F` when its steps denote `F` at every node whose recursive results are the values of `F` at its
children), `Den.foldEnc` (the eliminator over the encoded values of a Lean type, by induction on
that type), `Den.foldApp` (at a function motive) and `CEq.fold`; `TimedLink` has the construct
rules `DSim.con` and `DSim.fold` (the eliminator against the cost of a structural recursion, one
per call plus the body). `reflect_d` reads the case analyses written with `casesOn` and with the
recursors of `Bool`, `Option`, `Sum` and pairs, and maps a Lean inductive type `T` to
`mu T.dSig` with the encoding `T.dEnc` generated by `T.rec`: a constructor is `con`, a match on a
value of `T` and a structural recursion over `T` are `fold`, a recursive call on a child the
application of the recursive results at its position, and a recursion whose other arguments
change the eliminator at a function motive (module docstring of `Reflect`, "Inductive types and
structural recursion"). `link_timed` links the fold of a structural recursion to the costed form
of `derive_timed`, whose companion `f.timedCost` is defined by the same recursion
(`TimedLink.DSim.foldEnc`, the node condition the equation of the companion at each
constructor). Tests: `CatCryptCoreTest/Complexity/D/MuTest.lean`, `ReflectRecTest.lean`,
`ReflectIndTest.lean`, `CatCryptCoreTest/Tactics/LinkTimedFoldTest.lean`.

## The interpretation in the Diller–Nahm category

`DillerNahm` relates the charges of `Tm.dtC` to the Diller–Nahm category of containers
(`CatCryptCore/Container/DillerNahm.lean`; Moss and von Glehn, *Dialectica models of type theory*,
LICS 2018, §8).

* The substitution theorem `Tm.dtC_subst`: a certified callee `g : Tm (a :: Γ) b` of the
  fragment, effectful or not, substituted for the function variable of `t` is simulated by the
  charges of `t` at the entry `calleeEntry cc g η` of the callee, each call charged the charge of
  the call and the cost of the callee at its argument (`Tm.dtC_call_calleeEntry`); it is the
  soundness theorem of `t` at that entry, related to the closure of `g` by the soundness theorem
  of `g`. `Tm.cost_subst_le` and `Tm.dtC_subst_letE` (the β-redex) follow.
* The functor of the pure fragment: a type is the container `Ty.dn τ = clockPos τ.hat` (a data
  token and a clock tick at each translated value), a pure term in the context of one more
  variable its costed closure `Tm.costedC` and the Diller–Nahm morphism `Tm.dnC`, whose backward
  map sends a data token to its demand. The variable is the identity (`Tm.dnC_var`), and the
  composite by substitution `Tm.letComp s t` is the composite of the morphisms with the clock tick
  of the β-step between them (`Tm.dnC_letComp`, with `Tm.dtC_rename`). `Tm.dnC_bounds` is the
  soundness theorem at the abstraction: the evaluation is a leaf after at most the ticks of the
  demand.
* `reflect_d` reflects a call of a callee with a certificate `c.d_timedSim` as the closure of
  `c.d` renamed into the caller's context (`Ren.liftN`), and `link_timed` applies the certificate
  at the call (`TSim.certCall`), without walking the body of the callee again. Test:
  `CatCryptCoreTest/Tactics/LinkTimedCertTest.lean`.

* The hereditary object (`DNHered`). A type `τ` is the container `Ty.dnH τ` with the translated
  values `τ.hat` as shapes. At a function type its positions at a costed closure are a clock
  tick and the call tokens `⟨u, z⟩`, an argument with a position of the result (Pédrot, LICS
  2014). `Ty.simPred τ v` is the Dialectica predicate of a value `v`, and `Sim` is this predicate
  at every position (`Ty.sim_iff_forall_simPred`). `Sim` at a function type with a first-order
  argument is the soundness of the morphism of the application (`Sim.arr_iff_dnSound`), and the
  morphism `Tm.dnH` of a pure term of the fragment is sound (`Tm.dnH_sound`).
* Call demands (`DNHeredFull`). In `Ty.hatH` a function type has as shapes a Diller–Nahm morphism
  of the hereditary objects together with a cost at each argument, so that a shape records the
  call demand. `Tm.dtH` is the costed tree of lifted values, and `Tm.dtC` is its image under
  `Ty.forget` (`Tm.dtH_forget`). `Sim.arr_iff_dnSoundH` states the equivalence at every argument
  type, and `Tm.dnHH_sound` the soundness of the morphism of an abstraction, whose body demands
  of an argument of function type no call token. Soundness is for the pure fragment.
* Open trees (`OpenTree`). `Tm.dtO` keeps the calls of the function variables of a context as
  operations of the tree. The closed tree is the open tree interpreted by the entries of the
  variables (`Tm.wpFold_dtC_eq_liftM_dtO`), and substitution of a callee is the interpretation of
  the call tokens by a handler. `Tm.cost_le_of_useBound` bounds the cost of every evaluation by
  the allowance, the base cost and the sum of the uses times the times of the entries, and
  `Tm.useBound_liftM_substHandler_clocked` gives the use vector of `Clocked.comp` for the
  substitution of a callee.
* Price-soundness (`PriceSound`). `DNLens.PriceSound` bounds a closure `g : X' → CTree Y'` by a
  Diller–Nahm morphism of clock objects at relations on the arguments and results, in the sense of
  Danner, Licata and Ramyaa. `PriceObj` with the morphisms `PriceHom`, which keep tokens
  (`DNLens.KeepsTokens`), is the gluing of the Diller–Nahm category along the Kleisli category of
  `CTree`. `Sim` at a function type is price-soundness of the costed closure
  (`Sim.arr_iff_priceSound`), and a pure term of the fragment in related environments is a
  morphism (`Tm.priceHom`).

## The types of D in the polynomial model

`PolyModel` places the types of D in the polynomial model of type theory (von Glehn;
`CatCryptCore/Container/`). The codes with their values form a universe in the sense of Awodey's
natural models (`univPoly Val`), and so do the codes with their translated values
(`univPoly Ty.hat`). `pi f B` and `sig f B` are the Π- and Σ-codes of that universe at the finite
ground codes (`piStr`, `sigStr`, and `piStrHat`, `sigStrHat` for the translation), `mu S` and
`imu f S i` its W-codes (`wStr`, `iwStr`): the values of `mu S` are Mathlib's W-type of the
container `Sig.den S` (a `PFunctor`) and those of `imu f S i` the indexed W-type
`Container.IPW` of the indexed container `ISig.cont S` (PolyFun's `IPFunctor`). A function type
translates to the costed function `Container.Costed` of the Diller–Nahm model. The logical
relations `ValRel` and `Sim` at inductive types are the relators `Container.WLift`,
`Container.IWLift` of the W-types (`CatCryptCore/Container/WTypes.lean`, with the maps of fields
`Container.wmapF`, `Container.iwmapF`), and `Sim` at a function type is the bound of the
evaluation by the demand of the Diller–Nahm morphism of the costed function
(`Sim.arr_iff_demand`).

## Relations on base types and the abstraction theorem

`RGraphInterp` extends a relation on the values of the finite ground types to every type of D.
The relation at a function type is the exact lifting `CTree.Lift` of trees: related trees have the
same effect nodes and ticks at related leaves, hence equal cost. A term that respects the base
relation (`Tm.RespB`) sends related environments to related results at equal cost (`Tm.eval_lift`,
`Tm.abstraction_cost`). Over a reflexive graph with a base relation over each edge, the types of D
are types of the reflexive-graph model and a respecting term is a term of it, at which the
abstraction theorem of the model holds (`Tm.rg_abstraction`); the positions of a computation in the
polynomial model over it are its ticks (`Ty.polyC_pos_rel_iff`).

`FreeNI` takes the relation that is total at the secret types and equality elsewhere. A respecting
term has equal cost on two environments that differ only in the secret (`Tm.cost_eq_of_secret`),
and equal trees at a public result type (`Tm.free_noninterference`). `GenericGroup` takes the graph
of a homomorphism of the group operations. A respecting term gives related results at equal cost on
the operations of two representations (`hom_free`, `iso_free`), and a term of one input and one
output commutes with the homomorphism (`hom_commute`, `iso_commute`). Square-and-multiply
exponentiation `powT` is such a term; it is evaluated in `n · (m + 4) + w · (m + 1)` steps for `n`
bits of weight `w` and multiplication cost `m` (`powT_eval`, `powT_commute`).
