# Refinement: the relational weakest precondition

`CatCryptCore/Refinement/` relates two programs through their weakest
preconditions. It observes a program as a monotone predicate transformer, as
Lean's `Std.Do` does, and a refinement states that every weakest-precondition fact of
an abstract program carries over to a concrete one. The judgment is the
refinement weakest precondition `rwp` of Sebastian Graf's
[sgraf812/ascent](https://github.com/sgraf812/ascent), stated as Mathlib's
arrow relation `Relator.LiftFun`. The namespace is `CatCrypt.Refinement`.

## The judgment

An assertion map `γ : AssnRel ps ps'` sends abstract assertions to concrete ones;
it is monotone and preserves existentials. Together with a relation `R` on values
and a relation `RE` on exception postconditions it induces a relation `γ.Rel` on
assertions, and the refinement of a transformer `wa` by a transformer `wc` is

```
RRelPT γ RE R wa wc := ((R ⇒ γ.Rel) ⇒ (RE ⇒ γ.Rel)) wa wc
```

that is, related postconditions give related preconditions. For two programs with
`WP` instances, `RRel γ RE R a c` is `RRelPT` at `wp⟦a⟧` and `wp⟦c⟧`. Because
`RRelPT` takes transformers, not monads, one side can be a deeply embedded
language with its own weakest precondition and the other a monadic program.

`RRelPT.closed_form` identifies the judgment with the closed form of `rwp`:
`γ (wa Q E) ⊢ wc (post R γ Q) E'`, where `post R γ Q` is the least concrete
postcondition related to `Q`.

## Results

| Statement | Lean |
|---|---|
| A refinement carries a triple of the abstract program to a triple of the concrete one. | [`RRelPT.transport`](RRel.lean), [`RRel.transport`](RRel.lean) |
| Refinements compose, with relational couplings of values and exceptions, for assertion maps that preserve existentials. | [`RRelPT.trans`](RRel.lean), [`RRel.trans`](RRel.lean) |
| The refinement is the closed-form `rwp` inequality. | [`RRelPT.closed_form`](RRel.lean), [`RRel.closed_form`](RRel.lean) |
| `pure`, `bind`, `if` and `Functor.map` preserve refinement, between two different monads. | [`RRel.pure`](RRel.lean), [`RRel.bind`](RRel.lean), [`RRel.ite`](RRel.lean), [`RRel.map_left`](RRel.lean), [`RRel.map_right`](RRel.lean) |
| Two `for` loops over lists, ranges or `Std.Rco` are related by a relational invariant indexed by the iteration. | [`RRel.forIn_list_inv`](RRelLoop.lean), [`RRel.forIn_range_inv`](RRelLoop.lean), [`RRel.forIn_rco_inv`](RRelLoop.lean) |
| Two `while` loops are related by a relational invariant and a variant on pairs of states. | [`RRel.repeatM`](RRelLoop.lean), [`RRel.loop`](RRelLoop.lean) |
| A refinement follows from one check at the strongest postcondition of the abstract side, and conversely for conjunctive transformers. | [`sp`](RRelLoop.lean), [`RRelPT.of_sp`](RRelLoop.lean), [`RRelPT.iff_sp`](RRelLoop.lean) |
| A guarded abstract update refined by the weakest precondition of a step relation is a forward simulation, total or partial. | [`rrelPT_optProg_wpRel_iff`](Programs.lean), [`rrelPT_optProg_wpRelP_iff`](Programs.lean), [`corresRel_iff_rrelPT`](Programs.lean) |
| Guarded refinements weaken, sequence over composed steps and compose with a refinement of the concrete side. | [`GuardedRRelPT.weaken`](Programs.lean), [`GuardedRRelPT.seq`](Programs.lean), [`guardedRRelPT_trans`](Programs.lean) |

The module provides the assertion maps identity, composition, purification of a
pure-shaped side, a state relation (`ofStateRel`) and a relation between concrete
states (`ofRel`); `ofRel_comp_ofStateRel_γ` computes their composite.

## The correspondence judgments of the ascent

The ascent of the CatCrypt compiler relates a program to a shallow function by a
family of correspondence judgments, one for each semantics: the source language
of the extraction, `LowCT`, the `RustM` monad, and the x86, RISC-V and
instruction-set machines. Each judgment is equivalent to an instance of
`RRelPT`, and `RRelPT.trans` composes correspondences across semantics.

| Judgment | Instance |
|---|---|
| Source expressions, argument lists and functions, with early exit (`Corres`, `CorresArgs`, `FnCorres`, `FnCorresX`, `CorresX`, `CorresG`) | [`corres_iff_rrelPT`](https://github.com/spitters/catcrypt-compiler/blob/master/HaxAscent/Ascent/CorresRRel.lean), [`fnCorres_iff_rrelPT`](https://github.com/spitters/catcrypt-compiler/blob/master/HaxAscent/Ascent/FnCorresRRel.lean) |
| Refinement of a partial semantics by a function (`RefinesO`, `RefinesP`) | [`refinesO_iff_rrelPT`](https://github.com/spitters/catcrypt-compiler/blob/master/HaxAscent/Ascent/FnCorresRRel.lean) |
| `RustM` programs and step machines (`CorresM`, `StepTriple`) | [`corresM_iff_rrelPT`](https://github.com/spitters/catcrypt-compiler/blob/master/HaxAscent/Calculus/CorresMCore.lean) |
| x86 blocks (`CorresJ`) | [`corresJ_iff_rrel`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/Ascent/CorresJRRel.lean) |
| `LowCT`, RISC-V, instruction-set, leaf-oracle, exception-valued and loop judgments | [`CorresMachineRRel`](https://github.com/spitters/catcrypt-compiler/blob/master/CatCrypt/Crypto/SecureCompilation/Ascent/CorresMachineRRel.lean) |
| A fuel simulation between two source programs is a refinement, and `corres_of_fuelSim` follows by composition | [`rrelPT_wpAT_of_sim`](https://github.com/spitters/catcrypt-compiler/blob/master/HaxAscent/Ascent/CorresRRel.lean) |

The source-level judgment `Corres` is in turn the weakest precondition of the
eventual run of the source semantics, with one postcondition for plain values and
one for control flow. The rules of `Corres` for sequencing, `let`, conditionals
and counted loops follow from that weakest precondition and mention no fuel.

## Relation to `sgraf812/ascent` and to Trocq

`RRelPT` states `rwp` as a relation between transformers, which gives three
additions to the upstream formulation. The two sides may be different monads, or a
monad and a deep embedding. Composition holds for relational couplings of values
and exceptions, given an assertion map that preserves existentials. Relational invariants, with a variant on pairs of states,
relate two loops.

The value relation `R` and the arrow relation are the parametricity relations of
Trocq: ParamTransfer's `R_arrow` is `Relator.LiftFun`, and in the compiler
`RRelParam` shows that ParamTransfer's Kleisli relations `RComp` and `RCompOk`
are the instances of `RRel` at the identity assertion map and at purification,
and lifts a `Param` on values to a `Param` on computations of two monads
(`Param.rrel`).
