# Tactics: game-proof automation

This registry lists the automation for game-based proofs in this directory and
in [`../XDijkstra/`](../XDijkstra/). Tactics are in the namespace
`CatCrypt.Tactics` unless their module states another.

The modules [`AutoSetsDecl.lean`](AutoSetsDecl.lean),
[`AutoSets.lean`](AutoSets.lean), [`AutoRules.lean`](AutoRules.lean),
[`AutoHopRegistry.lean`](AutoHopRegistry.lean),
[`AutoDispatchCore.lean`](AutoDispatchCore.lean), [`AutoBase.lean`](AutoBase.lean),
[`AutoDispatch.lean`](AutoDispatch.lean),
[`AutoDispatchExt.lean`](AutoDispatchExt.lean), [`AutoArms.lean`](AutoArms.lean),
[`AutoMetrics.lean`](AutoMetrics.lean) and [`AutoPremises.lean`](AutoPremises.lean)
are leaves: the aggregate module `CatCryptCore.Tactics` does not import them, and a
proof that uses them imports them itself.

The dispatcher `catcrypt_auto` is in `AutoDispatchCore`, with its registry of shapes,
arms and normalisation steps (`catcrypt_auto_shape`, `catcrypt_auto_arm`,
`catcrypt_auto_norm`). `AutoDispatchCore` imports only `Lean`, `AutoHopRegistry` (the
`@[hop_metric]` attribute) and `AutoPremises`, all three Lean-only; `AutoBase`
registers by `Name` the shapes of the game-proof goals and the arms that use only Lean
tactics, without importing the theory. A module at any level, including the modules
that `AutoSets` imports (`Core/Code`, `Crypto/Advantage`, the XDijkstra files), uses
`catcrypt_auto` by importing `CatCryptCore.Tactics.AutoBase`
([`AutoBaseTest.lean`](AutoBaseTest.lean) prints its import closure). The other arms
are registered beside the tactics they call: `AutoArms` (`hop_chain`, `sum_atoms_le`,
`gcongr_unfold`, `gcongr`), `AutoSets` (`aesop` over `CatCryptRel`, `catcrypt_grind`,
`ssprove_crypto`, `bound`), `AutoDispatch` (`bind_swap_nf`, `bind_vcgen`) and `AutoDispatchExt` (the
XDijkstra and zero-advantage shapes and arms). A proof that uses every arm imports
`CatCryptCore.Tactics.AutoDispatchExt`: it imports `AutoDispatch`, which imports
`AutoBase`, `AutoSets` (which imports `AutoSetsDecl`) and `AutoMetrics` (which imports
`AutoArms`). No module of that chain imports `AutoRules`; a proof that needs its two
rules in `CatCryptRel` (`rHoare_false`, `ssprove_nofail`) imports
`CatCryptCore.Tactics.AutoRules` as well. Each module has its tests in the module of
the same name with the suffix `Test`.

## Leaf goals

At a leaf goal of a game proof, run `catcrypt_auto?` and replace it by the call
it suggests. When every arm fails, the error names the goal shape and the first
line of each arm's error; the shape selects the family in the registry below.
When the goal needs a hop lemma, a triangle lemma or a definition that is not in
context, pass it: `catcrypt_auto? [t₁, …, tₙ]` (terms, e.g. `kemtls_hop1 P ε h`,
`advantageA_triangle`, a definition name). Each term is elaborated as one term
and goes to the arms by its kind: a local hypothesis to `simp_all` and `aesop`
(never to `grind`, which uses the local context and rejects it as a redundant
parameter); a definition to `grind`, `catcrypt_grind`, `simp_all`,
`gcongr_unfold` and the unfolding pass (never to `aesop`); a term with a hole
`_`, a term whose type is not a proposition, or a term that needs the goal to
elaborate to the arms `exact t` and `apply t` only, tried first; any other proof
to `grind`, `catcrypt_grind` and `simp_all` as a lemma argument, to `aesop` as
`(add unsafe (t))`, and to `hop_chain` when it is not `∀`-quantified. The
suggestion keeps them.

## Registry

| Family | Tactic or set | Module | What it does |
|---|---|---|---|
| Dispatch | `catcrypt_auto`, `catcrypt_auto [t₁, …]` | [`AutoDispatchCore.lean`](AutoDispatchCore.lean); registrations in [`AutoBase.lean`](AutoBase.lean), [`AutoArms.lean`](AutoArms.lean), [`AutoSets.lean`](AutoSets.lean), [`AutoDispatch.lean`](AutoDispatch.lean), [`AutoDispatchExt.lean`](AutoDispatchExt.lean) | Reads the shape of the main goal and runs the arms registered for that shape (next section) in order, each under its own heartbeat budget, with the terms `tᵢ` passed to the arms. Closes the goal or fails. |
| Dispatch | `catcrypt_auto?`, `catcrypt_auto? [t₁, …]` | [`AutoDispatchCore.lean`](AutoDispatchCore.lean) | Behaves as `catcrypt_auto` and adds a "Try this" suggestion with the closing arm and its arguments, preceded by the normalisation and `unfold` steps that changed the goal. |
| Dispatch | `catcrypt_auto_shape`, `catcrypt_auto_arm`, `catcrypt_auto_norm` | [`AutoDispatchCore.lean`](AutoDispatchCore.lean) | Register a shape (a matcher on head constants given by `Name`, a stage and a priority), an arm (tactic text with argument placeholders, an order, constants it needs) or a normalisation step. Registrations of imported modules are merged. |
| Dispatch | `#import_closure_roots M` | [`AutoDispatchCore.lean`](AutoDispatchCore.lean) | Prints the root packages of the import closure of the module `M` and its modules outside `Init`, `Std` and `Lean`. |
| Distances | `hop_chain`, `hop_chain [h₁, …]` | [`AutoArms.lean`](AutoArms.lean) | Proves `d x y ≤ e` for a distance `d` registered with `@[hop_metric]`: a breadth-first path of hop facts `d u v ≤ b` (or `= b`) from `x` to `y` among the unquantified hypotheses and the arguments, each usable backwards when a symmetry lemma is registered, composed by the triangle lemma; the residual sum goes to `sum_atoms_le`. |
| Distances | `hop_chain!`, `hop_chain! [h₁, …]` | [`AutoArms.lean`](AutoArms.lean) | `hop_chain` with hop endpoints identified up to definitional equality at default transparency (games that agree after unfolding), and the head definitions of the bound `e` unfolded when the residual is not closed (a bound defined as the sum of the hop bounds). |
| Case splits | `bool_cases` | [`AutoArms.lean`](AutoArms.lean) | Splits the goal in at most three rounds (at most eight goals) by `cases` on local Boolean variables of the goal or a hypothesis, else `by_cases` on the proposition of a `decide` or `if` subterm; fails when there is none. |
| Unfolding | `eqn_unfold` | [`AutoEqnUnfold.lean`](AutoEqnUnfold.lean) | Rewrites, in the goal and the hypotheses, each application of a workspace definition by pattern matching whose argument at a pattern position of one of its equation lemmas has a constructor at its head, by those equation lemmas (`simp only`, two rounds); fails when there is none. An arm of the shape `other` of `catcrypt_auto` (`AutoArms`). |
| Distances | `@[hop_metric]` | [`AutoHopRegistry.lean`](AutoHopRegistry.lean) (imports only `Lean`); standard registrations in [`AutoMetrics.lean`](AutoMetrics.lean) | Registers a triangle lemma, a symmetry lemma, an equation `D … = d …` or a definition to unfold. `AutoMetrics` registers `sdist`, `Advantage` and `AdvantageA`; an advantage- or probability-valued definition of a proof becomes a distance by `@[hop_metric]` on it. |
| Distances | `sum_atoms_le` | [`AutoArms.lean`](AutoArms.lean) | Decides `Σ aᵢ ≤ Σ bⱼ` for ℕ-weighted sums of atoms in a canonically ordered semiring (`ℝ≥0∞`), matching each left atom to a right atom equal to it or bounding it by a hypothesis `a ≤ b`. |
| Time bounds | `time_bound`; simp set `time_bound_simps` | [`AutoTime.lean`](AutoTime.lean) | Proves `SPTree.Timed.stepTime x ≤ B`, `t.time ≤ B`, `OracleAdv.Timed.StepTimeBound x n` and `A.TimeBound n` node by node with a path cost `P` (`P + stepTime x ≤ B`, `StepTimeBound x (B - P)`): pairs, `delay`, nodes, binds pushed into nodes or (after a tree that is not a node) charged with its time, `if` and `match` split, non-recursive definitions with visible bodies unfolded; other subtrees bounded by local hypotheses or, below the goal's head, by `N.timeBound_timed`/`N.timeBound`; an arithmetic leaf first by substitution (`closeBySubst`: each summand replaced by a hypothesis bound in the variables of the right side, products in `ring_nf` normal form by `addRingFacts`, `omega` with the hypotheses cleared); an equation `e = c + y.1` of a summand rule by `omega` with the hypotheses cleared (`closeEqAC`); otherwise arithmetic leaves by `omega`, then `linarith`, with the instances of hypotheses `∀ x, f x ≤ b` at the subterms `f a` and, for a registered cost that mentions variables absent from the bound, its bound free of them (`addCostFacts`, `boundFree?`), and `l.length * c ≤ n * c` for a product of a length with an invariant `l.length ≤ n` (`addProductFacts`); `linarith` and `nlinarith` each under `arithHeartbeats`, so a leaf they cannot close falls through to the next rule; a bind assumes the length invariants of `AutoTime.lengthInvs` (structure included). `time_bound_simps` holds unfolding equations of definitions whose bodies are not visible. Arm of the direct shape `time bound` (priority 120) of `catcrypt_auto`. |
| Costed forms | `derive_timed R`, `derive_timed_structure S`, `derive_reduction R`, `derive_erases_hat S`; `register_tree_kind k` | [`DeriveTimed.lean`](DeriveTimed.lean), [`DeriveTimedStructure.lean`](DeriveTimedStructure.lean), [`DeriveReduction.lean`](DeriveReduction.lean); tests of a registered tree kind in [`DeriveTimedTreeKindTest.lean`](DeriveTimedTreeKindTest.lean) | Define the costed form `R.timed` of a reduction with its erasure theorem, and the costed mirror `S.Timed` of a structure with its time bound. The tree types are an open table (`treeKinds`): the built-in kinds `OracleAdv` and `SPTree`, followed by the kinds `k : TreeKind` registered by `register_tree_kind k` in the module of the tree type or above it (oracle programs, [`OracleProgTimed.lean`](../Crypto/Signatures/OracleProgTimed.lean)). A node argument of role `comp` (a computation `SPTree.compile t`) is priced by the costed tree of `t`; a computation without a tree is refused. A kind names the time bound of its step-prefixed costed trees (`stepTimeBound`), read by `S.Timed.TimeBound`. A fully applied non-recursive definition whose result is a function (a state update `Function.update E a v` under `if`) is unfolded, so its values are priced once at construction and a read is a lookup (`unfoldFnCall?`). A condition costs its data arguments and its `Decidable` instance is not read; under `set_option derive_timed.priceProps true` it is also priced by what decides it: `x ∈ l` as `List.elem`, `l₁ = l₂` and `l₁ ≠ l₂` on lists as `List.beq`, a definition valued in `Prop` as one plus its unfolded body (list costs in [`StdCosts.lean`](StdCosts.lean)). Set the option when a guard of the reduction tests list membership, list equality or a `Prop`-valued definition and the certificate is to charge that test. |
| Query bounds | `query_fold`, `query_fold [names]`; attribute `@[query_fold]` | [`QueryFold.lean`](QueryFold.lean), imported with [`OracleProfile`](../Crypto/OracleProfile.lean); tests in [`QueryFoldTest.lean`](../../CatCryptCoreTest/Tactics/QueryFoldTest.lean) | The fold-based tactic for query bounds. Proves `A.IsQueryBoundBy c n`, `A.IsQueryBound n`, `IsQueryBound₂`, `MayOnlyCall S A` and `IsQueryProfile` by rewriting to the budget-passing fold `OracleAdv.Within` with `simp`, so a sequential composition needs no estimate of the budget of its first part. A tree with no equation of the fold enters by a known bound: a hypothesis, a theorem with the attribute, a listed name, or a theorem for `simulate` and `subst`; a premise of a known bound is a goal of the same procedure, and a choice is undone when a premise fails. An attributed or listed equation, equivalence or definition is a rewrite law. Use it at those goals; an induction stays with the user, and the tactic reports the goal it reached at a recursive definition applied to a variable without a known bound. |
| Query bounds | `query_bound`, `query_bound [names]`, `query_bound only [names]` | [`QueryBound.lean`](QueryBound.lean), imported with [`OracleQueryVec`](../Crypto/OracleQueryVec.lean); tests in [`QueryBoundTest.lean`](../../CatCryptCoreTest/Tactics/QueryBoundTest.lean) | Proves `A.IsQueryBoundBy c n`, `A.IsQueryBound n`, `MayOnlyCall S A` and `IsQueryBound₂ A h q` by structural recursion on the tree `A`: a query subtracts its charge from the budget, `A.bind f` takes the budget of `A` from a syntactic estimator that the proof checks, a branch is split, and a simulation or substitution takes the known bounds of `A` at the charge given by the budgets of its programs. Known bounds come from the local context, the listed names, the proposition fields of a structure at a projection head, and theorems named `Ns.isQueryBound_f`, `Ns.isQueryBoundBy_f`, `Ns.isQueryBound₂_f` or `Ns.f.isQueryBound` for a head `Ns.f` (`only` leaves out this family). Use it where known bounds follow that naming and need no attribute. It fails with a named error at a recursive definition applied to a variable and at an adversary variable with no known bound. |
| Time bounds | `derive_time_bound N` | [`DeriveTimeBound.lean`](DeriveTimeBound.lean) | Derives `N.timeBound_timed`; a continuation that reads a bound value is bounded at the length invariants of the tree it follows (`AutoTime.lengthInvs`): those of local hypotheses and of theorems `N.allRet_length`, and, for a tree whose structure is visible (a callee inlined by `derive_reduction`), those derived through its `sample`/`get`/`set`/`load` nodes, binds and `ret` leaves. A registered cost without a closed form free of the bound value is bounded by `AutoTime.boundFree?` (premise `∀ x y, fCost x y ≤ ?k` of its `_le` lemma by the bound of the companion at fresh arguments; `↑(i : Fin n)` by `n`; lengths of `List.ofFn`/`map`/`zip` by their equations); failing that, in a strict mode free of every value bound inside the continuation (`withStrict`). |
| Monotonicity | `gcongr_unfold`, `gcongr_unfold [d₁, …]` | [`AutoArms.lean`](AutoArms.lean) | Introduces the binders of `Monotone f`-like goals, unfolds `dᵢ`, runs `gcongr` and closes the side goals by `assumption`, `positivity` or `norm_num`. |
| Party programs | `party_derive`, `party_derive [t₁, …]`, `party_derive!` | [`PartyDerive.lean`](PartyDerive.lean) (imports `Party.Call`, `Party.Derived`, `Party.Timed`); tests in [`PartyDeriveTest.lean`](PartyDeriveTest.lean) | Proves the side conditions of a concrete party program by descent over its term: `Prog.Samples p c`, `ProgE.Ports Pe Po p`, `ProgE.ViewRel V Eq p p` for a program without receives and sends, `ProgE.Bound w p t P`, and `∃ t, ProgE.Bound w p t P` with the bound read off the program. Applies the rule of the head constructor, splits a head `match` or `if`, unfolds a head definition; the terms `tᵢ` close subgoals and unfold in the predicate leaves. At a time bound, a subprogram with head `c` is bounded by a hypothesis or by the theorem `c_bound` when the descent succeeds with it (`party_derive!` unfolds instead). |
| Fixed points | `loop_rw`, `loop_rw [h₁, …]`; simp set `loop_simps` | [`LoopRewrite.lean`](LoopRewrite.lean); set declared in [`LoopRewriteAttr.lean`](LoopRewriteAttr.lean); dynamic-circuit equations in dev `CatCrypt/Quantum/DynCircuitLoopRw.lean` | Loop rewriting with the trace laws as directed steps, on any traced symmetric monoidal category, `SysCat` and `QSysCat R` (unbounded loopback `loopbackω`): tightening moves pre- and post-processing outside the trace, sliding moves a wire morphism from the entry to the exit, vanishing removes a unit wire, a tensor wire or an unused wire (`trace U (f ▷ U) = f`), yanking replaces the trace of the symmetry by the identity, and `loopbackω_step`, `fbRunω_inl` unroll the first activation. Adds the associativity and unit laws of composition and the rules `hᵢ`; for the dynamic-circuit loop `whileBit`, its unrolling on a register and its morphism as a trace. |
| Wiring | `port_coherence`, `port_coherence [h₁, …]`; `port_simp`, `port_ext`, `port_cases` | [`PortCoherence.lean`](PortCoherence.lean) | Monoidal coherence and port plumbing: `monoidal` on any monoidal category (`SysCat`, `QSysCat R`, their Int constructions, the party category `Party.Diag g`; no registration needed), else `port_simp` rewrites composites of `homOfFun`, `isoOfEquiv`, structure maps, whiskerings and `mkHom` in `SysCat`, `QSysCat R` and their Int constructions to one `homOfFun` (or `mkHom` of two), unfolding the definitions `hᵢ`, and `port_ext` closes the equality by `funext` and case analysis on sums, dependent pairs and `Empty`. Closes the boundary laws `bMap_id`, `bMap_comp`, `bMu_bMap`, `bMu_assoc`, `bMu_comm`, unit laws and `swapRight_eq_homOfFun`; goals with a trace (`cup_cap_zigzag`) need `trace_homOfFun` first. |
| Fixed points | `scott_induction`, `scott_induction e`, `scott_induction using thm`; `scott_admissible` | [`ScottInduction.lean`](ScottInduction.lean); theorems in [`../ForMathlib/Order/ScottInduction.lean`](../ForMathlib/Order/ScottInduction.lean) | Scott induction (fixed-point induction): abstracts from the goal a least fixed point `f.lfp` (`OrderHom.lfp_scott_induction`), a supremum of iterates `ωSup (iterateChain f x h)` or the unbounded loopback activation `S.fbRunω` of a quantum reactive system (`QRSys.fbRunω_scott_induction`), or the term `e`, into the predicate `P`, and leaves the continuity side conditions, `P` at the start, and the step `P x → P (f x)`. The admissibility of `P` (`OmegaCompletePartialOrder.Admissible`, closure under ω-suprema of chains) is closed by `scott_admissible` for `True`, conjunctions, `∀`, bounds `x ≤ b`, and inequalities and equations between maps `fun_prop` proves ω-Scott-continuous; otherwise it is left as a goal. |
| Transport | `transport_along P`, `transport_along P using K`; `transport_rel`, `transport_bias` | [`TransportAlong.lean`](TransportAlong.lean); theorems in [`../Crypto/UCTransport.lean`](../Crypto/UCTransport.lean) | Reduces a goal about the images of systems under an observation-preserving map `P : ObsPreserving F G` to the same goal about the source systems: `RealizesSim`, `Realizes` (maps of `envSetting`, such as `compiledObsPreserving`), `QRealizes` (a family of maps of `qSetting`), `EmulatesΩ`, and an equation `B.obs X' (G K) = B.obs Y' (G K)`, which becomes `∀ K, A.obs X K = A.obs Y K` (the test `K` given by `using K` when unification does not find it). The relation goals `F X X'` are closed by `transport_rel` (a hypothesis, the cases of `compiledRel`, the graph of a function, composites from `ObsPreserving.comp`, right component first); the bias condition on the map of observations by `transport_bias`, else left as the first goal. The file states the classical lift `liftQSys`/`liftStrat` as the map `liftObsPreserving` from `pureSetting` to `qSetting`. |
| Sets | `CatCryptRel` | [`AutoSetsDecl.lean`](AutoSetsDecl.lean) (declaration), [`AutoSets.lean`](AutoSets.lean), [`AutoRules.lean`](AutoRules.lean) | Aesop rule set. Safe `apply`: the `IsPure` and `NoFail` combinators for `pure`, `sample` and bind, in `SPComp.bind` and `>>=` form, and `rHoare_false`. Unsafe `apply`: `rHoare_ret_same`, `rHoare_refl`, `rHoare_sample_same`, `rHoare_fail` (70%); the synchronised and one-sided `get`/`set` rules, `rHoare_ite`, `rHoare_if` (50%). Unsafe tactic rule: `ssprove_nofail` (60%). Normalisation `simp`: the `SPComp` monad laws, `SPComp.monad_bind_eq`, `SPComp.monad_pure_eq`. Called as `aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })`. |
| Sets | `CatCryptGrind` | [`AutoSets.lean`](AutoSets.lean) | Scoped `grind` set, active where the namespace `CatCryptGrind` is open. Equations: the `SPComp` monad laws, `Heap.get_set_same`, `Heap.get_set_other`, `Advantage_sym`, `Advantage_self`, the unfolding of `AdvantageA`, `Finset.sum_range_zero`, `Finset.sum_range_succ`, `lazyEval_fresh_eq_sample`. Facts: `add_le_add`, `rHoare_refl`, `rHoare_sample_same`. |
| Sets | `catcrypt_grind`, `catcrypt_grind [p₁, …]` | [`AutoSets.lean`](AutoSets.lean) | `grind`, with the given `grind` parameters, and `CatCryptGrind` open. |
| Sets | `@[gcongr]` | [`AutoSets.lean`](AutoSets.lean) | `wpE_mono`, `wpEF_mono` (monotonicity of the expectation transformers in the postcondition and the error term) and `prEvent_mono` (monotonicity in the event). |
| Sets | `@[bound]` | [`AutoSets.lean`](AutoSets.lean) | `prTrue_le_one`, `ENNReal.div_le_div_right`, `natCast_le_natCast_of_le` (the cast `ℕ → ℝ≥0∞` is monotone) and `le_natCast_mul_of_one_le` (`ε ≤ n * ε` for `1 ≤ n`). |
| Closers | `ssprove_crypto_close` | [`AutoSets.lean`](AutoSets.lean) | The first of `simp_all` (when it closes the goal), `catcrypt_grind` and `aesop` over `CatCryptRel` that closes the goal; fails otherwise. |
| Closers | `ssprove_crypto_grind` | [`AutoSets.lean`](AutoSets.lean) | `ssprove_crypto_close`; otherwise `ssprove_crypto`; otherwise `ssprove_code_simpl`, the rounds of `ssprove_auto_repeat` and `ssprove_crypto_close` on each remaining goal. Fails when a goal stays open. |
| Relational drivers | `ssprove_auto_step` | [`Auto.lean`](Auto.lean) | One round: the first of a WP step, `ssprove_sync`, `ssprove_rcondt`, `ssprove_rcondf`, a one-sided sample, `ssprove_dead_code` and `assumption` that changes the goal list. Fails when none does. |
| Relational drivers | `ssprove_auto_repeat` | [`Auto.lean`](Auto.lean) | `ssprove_auto_step` until it fails, no goal is left or 64 rounds have run. Always succeeds. |
| Relational drivers | `ssprove_auto_ec`, `ssprove_auto_ec!` | [`Auto.lean`](Auto.lean) | `ssprove_code_simpl`, `ssprove_auto_repeat`, then a closing tactic on every goal; closes the goal or fails. The `!` form tries `rHoare_refl` first. |
| Relational drivers | `ssprove_crypto`, `ssprove_crypto_step` | [`CryptoAuto.lean`](CryptoAuto.lean) | `ssprove_crypto` is `ssprove_auto_ec!`; `ssprove_crypto_step` is one round of `ssprove_auto_step`. |
| Relational drivers | `prob_to_rHoare` | [`CryptoAuto.lean`](CryptoAuto.lean) | Reduces `∀ A, AdvantageA G₀ G₁ A = 0` to `rHoare eqPre G₀ G₁ eqPost` through `advantage_zero_of_rHoare` and closes the judgment with `ssprove_crypto`. |
| Simulation | `ssprove_sim`, `ssprove_sim?`, `ssprove_sim_eq`, `ssprove_sim_auto`, `ssprove_sim_bij f`, `ssprove_rspec`, `ssprove_reorder` | [`Sim.lean`](Sim.lean) | Structural bisimulation after EasyCrypt's `sim`: normalise both programs, match the heads and apply the `@[rspec]` rule of the pair. `ssprove_sim?` suggests the script of the steps that fired; `ssprove_reorder` commutes mismatched heads. |
| Simulation | `ssprove_try_bij f`, `ssprove_couple_bij f`, `ssprove_try_bij₂` | [`Sim.lean`](Sim.lean), [`TryBij2.lean`](TryBij2.lean) | Coupling of a uniform sample along a bijection; `ssprove_couple_bij` closes the continuation with `ssprove_sim_auto`; `ssprove_try_bij₂` couples the inner of two nested samples. |
| Game equality | `bind_swap_nf [h, …]` | [`BindSwap.lean`](BindSwap.lean) | Closes an `SPComp` equality whose sides differ by the order of independent `IsPure` binds: normalises both sides, moves each head binding of one side to the front of the other (`isPure_bind_comm_left`/`_right`) and removes it; `IsPure` side conditions from the combinators, hypotheses, structure fields and the arguments. When that fails, removes unused bindings (discard facts, or `isPure_bind_discard` for `IsPure` mass-one computations) and rewrites by two-binding chain facts (`∀ f, c₁ >>= fun p => c₂ >>= fun q => f p q t = … f p q t'`, e.g. `DHComm`, `deps.dh_keygen_comm`); equations given as arguments close the leaves by `simp only`; then splits each `sample (A × B)` into the samples of its components (`SPComp.sample_prod_eq`) and retries. A definition named as an argument is unfolded by name (no `(W := W)` for implicit type or instance parameters); a theorem named as an argument is used with its arguments quantified. First arm of `catcrypt_auto` on game equalities. |
| Advantage equality | `advantage_eq_nf [h, …]` | [`BindSwap.lean`](BindSwap.lean) | Closes `a = b` with both sides unfolding at the head to `Advantage X Y` (`AdvantageA`, `DDH_Advantage`, …) from the game equalities `X = X'`, `Y = Y'` (or crossed, with `Advantage_sym`), each by unfolding the game definitions at its heads and the definitions named as arguments, and `bind_swap_nf`. Arm of `catcrypt_auto` for the shape `advantage equality`. |
| Game equality | `bind_vcgen`, `bind_vcgen using e` | [`BindVcgen.lean`](BindVcgen.lean) | Normalises and peels matching `SPComp.bind` layers until stuck; `using e` applies the change of variables `SPComp.sample_bind_equiv e` to a sample residual. |
| Game equality | `bind_vcgen_sum` | [`BindVcgenSum.lean`](BindVcgenSum.lean) | `bind_vcgen` with the `mapSum` reassociations of `Sum`-typed views. |
| Game equality | `bind_align` | [`BindAlign.lean`](BindAlign.lean) | Peels matching bind layers from both sides of an equality and leaves the pointwise residual. |
| Game equality | `group_exp_nf [r₁, …]`, `group_exp_norm [r₁, …]` | [`GroupExpNF.lean`](GroupExpNF.lean) | Unfolds the rules `rᵢ` and the monad laws, folds the group expressions into powers of their bases (`ℕ` and `ℤ` exponents built in, other exponentiations by their fold laws given as rules), brings the exponents to `ring_nf` normal form, peels the aligned layers by `bind_align` and closes each leaf by the same normal form; fails when a leaf remains. `group_exp_norm` is the normalisation alone. |
| Game equality | `sp_normalize` | [`SPNormalize.lean`](SPNormalize.lean) | `simp only` with the `SPComp` monad laws. |
| Game equality | `pkg_coherence`, `pkg_coherence!`, `pkg_coherence_lite`, `sum_cases` | [`PkgCoherence.lean`](PkgCoherence.lean), [`PkgCoherenceBang.lean`](PkgCoherenceBang.lean), [`SumCases.lean`](SumCases.lean) | Structural equalities of package handlers (composition, associator, unitor, braiding); `pkg_coherence!` adds `sp_normalize_deep` on the leaves; `sum_cases` splits every `Sum` in the context. |
| Rule steps: synchronous | `ssprove_sync`, `ssprove_sync_eq`, `ssprove_sync_bij f`, `ssprove_sync_ret`, `ssprove_sync_sample`, `ssprove_rnd_lhs`, `ssprove_rnd_rhs` | [`Sync.lean`](Sync.lean) | The synchronous rule for matching heads (`sample`, `get`, `set`, `pure`), under heap equality, or along a bijection; a sample on one side. |
| Rule steps: structural | `ssprove_bind`, `ssprove_conseq`, `ssprove_call spec` | [`Sync.lean`](Sync.lean), [`Call.lean`](Call.lean) | The bind rule, the consequence rule, and a known specification applied to the head bind. |
| Rule steps: contraction and swap | `ssprove_contract_get_lhs`, `ssprove_contract_put_lhs`, `ssprove_contract_put_get_lhs` and their `_rhs` forms, `ssprove_swap_lhs`, `ssprove_swap_rhs`, `ssprove_swap_samples_lhs n`, `ssprove_swap_samples_rhs n` | [`Sync.lean`](Sync.lean) | Remove a repeated `get` or `set` on one side; commute independent operations on one side. |
| Rule steps: contraction and swap | `ssprove_swap_binds_deep`, `ssprove_swap_at n` | [`BindMatch.lean`](BindMatch.lean) | Commute two binds with `IsPure` heads at the first depth where the rewrite applies (up to 5), or at depth `n`. |
| Rule steps: WP and SP | `ssprove_wp`, `ssprove_wp_step`, `ssprove_sp`, `ssprove_sp_step` | [`WP.lean`](WP.lean), [`SP.lean`](SP.lean) | Deterministic suffixes backwards into the postcondition, deterministic prefixes forwards into the precondition. |
| Rule steps: conditionals | `ssprove_rcondt`, `ssprove_rcondf` | [`Conditional.lean`](Conditional.lean) | Resolve a branch whose condition the precondition fixes. |
| Rule steps: procedures | `ssprove_proc [defs]`, `ssprove_proc_lhs [defs]`, `ssprove_proc_rhs [defs]` | [`Proc.lean`](Proc.lean) | Unfold game and oracle definitions on both sides or on one, then normalise. |
| Rule steps: code | `ssprove_code_simpl`, `ssprove_distr_simp`, `ssprove_valid`, `ssprove_rnd e` | [`Basic.lean`](Basic.lean) | Normalise code (bind association, pure inlining, dead code, contraction); normalise sub-distribution terms; close `ValidCode` goals; a sampling step along a bijection `e`. |
| Rule steps: ProofFrog | `ssprove_dead_code`, `ssprove_dead_sample_lhs`, `ssprove_dead_sample_rhs`, `ssprove_copy_propagate`, `ssprove_unreachable`, `ssprove_canonicalize`, `ssprove_contract_all`, `ssprove_inline_lhs`, `ssprove_inline_rhs`, `ssprove_auto_pf` | [`ProofFrog.lean`](ProofFrog.lean) | Game simplifications after ProofFrog: dead code, copy propagation, an unsatisfiable precondition, canonical bind structure, contraction on both sides, inlining; `ssprove_auto_pf` applies all of them. |
| Rule steps: invariants | `ssprove_invariant`, `ssprove_restore` | [`Invariant.lean`](Invariant.lean) | Close `IsInvariant` goals from the standard invariant lemmas; re-establish `syncsAt`, `rem_lhs`, `rem_rhs` or an invariant after writes. The consequence rules `rHoare_restore_lhs_conseq` and `rHoare_restore_rhs_conseq` of [`Restore.lean`](Restore.lean) unwrap `set_lhs`/`set_rhs` preconditions. |
| Rule steps: invariants | `ssprove_remember_lhs`, `ssprove_remember_rhs`, `ssprove_remind_lhs`, `ssprove_remind_rhs`, `ssprove_forget` | [`Remember.lean`](Remember.lean) | Record the value of a `get` in the precondition, use it at a later `get` of the same location, and drop it. |
| Rule steps: side conditions | `ssprove_vc`, `ssprove_ispure`, `ssprove_ispure_syn`, `ssprove_nofail`, `ssprove_phoare` | [`VC.lean`](VC.lean) | `ssprove_vc` dispatches on the head: `IsPure` by reification to `RawCode` (`ssprove_ispure_syn`) and then the combinator cascade; `NoFail` by `mvcgen`; `pHoare` through `pHoare_iff_triple` and `mvcgen`. |
| Advantage | `ssprove_triangle G₀ gs Gₙ`, `adv_game_hop [G₁, …]` | [`Triangle.lean`](Triangle.lean) | The triangle inequality over a chain of games, as a hypothesis, or as one subgoal per hop on `AdvantageA G₀ Gₙ A ≤ ε₁ + … + εₙ`. |
| Advantage | `ssprove_upto bad` | [`UpToBad.lean`](UpToBad.lean) | The up-to-bad lemma with the bad event `bad`, chosen by the goal shape. |
| Advantage | `ssprove_eager`, `ssprove_lazy_unfold` | [`LazySampling.lean`](LazySampling.lean) | Rewrite lazy evaluation to eager sampling; unfold `lazyEvalAbstract`. |
| Advantage | `le_of_sum`, `congr_funext` | [`LeOfSum.lean`](LeOfSum.lean) | `x ≤ a + b + …` by `le_self_add` and `le_add_self`; the congruence cases of an induction over binds. |
| XDijkstra | `xmvcgen`, `xmvcgen_ctl`, `xmvcgen!` | [`XMvcgen.lean`](../XDijkstra/XMvcgen.lean), [`XMvcgenControl.lean`](../XDijkstra/XMvcgenControl.lean), [`XMvcgenReg.lean`](../XDijkstra/XMvcgenReg.lean) | One `simp only` call that unfolds `XTriple` and `XPT` (and `XRelTriple`, except in `xmvcgen_ctl`) and computes the weakest precondition, from a fixed lemma list, from the list and the `xspec` set (control flow `xite`, `xphi`, `xfor`), or from the `xspec` set alone. |
| XDijkstra | `relmvcgen`, `relmvcgen_ctl` | [`XRelMvcgen.lean`](../XDijkstra/Rel/XRelMvcgen.lean), [`XRelMvcgenControl.lean`](../XDijkstra/Rel/XRelMvcgenControl.lean) | Coupling composition backwards along binds (`relBind_spec`, `relSpec_seq`), and in `relmvcgen_ctl` also through shared-condition branches and bounded loops (`relSpec_ite`, `relSpec_forN`). Leaves the per-hop coupling leaves; the grade is carried in the type index. |
| XDijkstra | `relmvcgen!`, `relmvcgen!?` | [`XCombinedAutomation.lean`](../XDijkstra/Rel/XCombinedAutomation.lean) | `relmvcgen_ctl`, then the grade-0 base coupling (`xrelQ0_pure`) and the arithmetic grade conditions. `relmvcgen!?` also tries `assumption` and `grind` on each leaf, so a chain whose hops are hypotheses closes. |
| XDijkstra | `advmvcgen`, `advmvcgen_dep` | [`XAdvantageHybrid.lean`](../XDijkstra/XAdvantageHybrid.lean) | On `AdvantageA (G 0) (G n) A ≤ budget`, apply `advChain_uniform_le` (one per-hop bound) or `advChain_triangle_le` (per-hop bounds `ε i`), leaving the per-hop leaf and the arithmetic condition. |
| XDijkstra | `advmvcgen!`, `advmvcgen_dep!`, `advmvcgen!?` | [`XCombinedAutomation.lean`](../XDijkstra/Rel/XCombinedAutomation.lean) | Discharge the arithmetic condition (with a budget bound `[h]` when given) and leave the per-hop leaf. `advmvcgen!?` also tries `assumption` and `grind`, so a hybrid whose per-hop bound is a hypothesis closes. |

## Arms of `catcrypt_auto`

The shapes of the direct stage (registered in `AutoDispatchExt`) are read on the
goal as stated, and the one of highest priority runs its arms first. When none
matches, or all its arms fail, the normalised stage runs: the goal containing
`>>=` is rewritten by `simp only [SPComp.monad_bind_eq]` (a step registered in
`AutoBase` with `catcrypt_auto_norm`), keeping the rewrite only when it changes the
goal, and the head of the goal is read with its `set`/`let` variables replaced by
their values and, failing a match, the head of its `whnfR`. The error of a goal
that stays open names the shape of the normalised stage and its failed arms, then
the failures of the unfolding pass and the premise stage, then those of the direct
stage. The table gives the arms in order, with the module registering each.

| Shape | Detected head | Arms, in order | Module |
|---|---|---|---|
| coupling (direct) | `XRelTripleQ0 …`, `RelSpecTriple …` | `relmvcgen!?` | `AutoDispatchExt` |
| hybrid advantage (direct) | `AdvantageA _ _ _ ≤ _` | `advmvcgen!?`; `advmvcgen_dep` with the leaf cascade of `advmvcgen!?` | `AutoDispatchExt` |
| zero advantage (direct) | `AdvantageA _ _ _ = 0`, possibly under `∀ A` | `prob_to_rHoare`; `advantage_zero_of_rHoare` with `catcrypt_auto` on the `rHoare` premise | `AutoDispatchExt` |
| extended triple (direct) | mentions `XTriple`, `XPT` or `XRelTriple` | `xmvcgen!`, then `omega`, `le_rfl`, `assumption`, `simp_all` or `grind` on each residual | `AutoDispatchExt` |
| side condition | `SPComp.IsPure _`, `SPComp.NoFail _` | `aesop` over `CatCryptRel`; `solve_by_elim` over the `IsPure` combinators; the same over the `NoFail` combinators | `AutoSets`; `AutoBase` |
| relational | `rHoare _ _ _ _` | `aesop` over `CatCryptRel`; `ssprove_crypto`; `ssprove_crypto_grind` | `AutoSets` |
| distance inequality | `_ ≤ _` over `ℝ≥0∞` or `ℝ` whose left side is a registered distance (after unfolding `@[hop_metric]` definitions, else after `whnfR`) or a sum with one as summand, or that mentions a registered head, `prTrue` or `prEvent` | `hop_chain`; `hop_chain!`; `sum_atoms_le`; `gcongr <;> catcrypt_grind`; `catcrypt_grind`; `bound` (a quarter of the budget; skipped when a `∀`-quantified inequality is in context) | `AutoArms`; `AutoSets` |
| monotonicity | `f a₁ … aₙ ≤ f b₁ … bₙ` or `<`, the same head on both sides; `Monotone f`, `Antitone f`, `StrictMono f`, `StrictAnti f` | `gcongr_unfold`; `gcongr`; `gcongr <;> catcrypt_grind`; `sum_atoms_le` (on `≤`); `simp_all`; `grind` | `AutoArms`; `AutoSets`; `AutoBase` |
| heap read | `Heap.get (Heap.set _ _ _) _ = _`, either side; `=`, `≠` or `¬ _ = _` mentioning `Heap.set` | `grind [Heap.get_set_same, Heap.get_set_other]` | `AutoBase` |
| game equality | `_ = _` over `SPComp _` | `catcrypt_grind`; `bool_cases` then `rfl`, `decide` or `simp_all` on each case; `bind_vcgen` | `AutoSets`; `AutoArms`; `AutoDispatch` |
| other | anything else | `sum_atoms_le` (on `≤`); `simp_all`; `bool_cases` then `rfl`, `decide` or `simp_all` on each case; `grind` | `AutoArms`; `AutoBase` |
| premises | (premise stage) | `solve_by_elim [p₁, …]` with the premises of `AutoPremises` | `AutoBase` |

The shapes are matched by constant `Name`, so `AutoBase` registers them without
importing the theory; an arm whose constants (`needs`) are absent or whose tactic
does not parse at the call site is skipped, and the error says so. When the arms
and the unfolding pass fail, the premise stage restores the normalised goal and runs
the `premises` arms with the candidates of `AutoPremises.premises` from the theorems
of the current file and the fields of local hypotheses.

Four rules hold across the shapes of the normalised stage.

- Arguments are sorted by kind as stated under "Leaf goals"; the `exact t` and
  `apply t` arms of non-proof terms run before the arms of the shape.
- Unfolding: a goal of shape `other` whose head is a definition is unfolded
  before the shape is read. When every arm fails, the unfolding pass unfolds the
  first definition head on each branch of the goal's explicit arguments (down to
  depth 3) and the definition arguments that occur in the goal, and the arms of
  the new shape run. A definition is unfolded when it is non-recursive, of
  regular reducibility, not an instance, projection or matcher, not from the
  Lean core, Mathlib, Batteries, Aesop or Qq, not a shape head, registered head
  or probability constant, and not an operation on the representation of its
  type (its value is not a `fun` beyond the binders of its declared type, which
  keeps `SPComp.bind` and `SPComp.pure` folded). The suggestion records each
  `unfold` step.
- `sum_atoms_le` runs on every `≤` goal of the distance, monotonicity and `other`
  shapes; it reads a goal outside its fragment again after expanding sums over
  `Finset.range (n + 1)` and reducing conditionals on `false = true` and
  `true = false`. `hop_chain` closes its residual the same way.
- Every `simp_all` arm runs after `clear` of the equations of `set x := e with h`:
  such an equation rewrites `x` back into `e`, and beside a hypothesis that
  states a subterm of `e` in terms of `x` the two rewrite into each other until
  the maximum recursion depth.

The `hop_chain` arm applies to every distance registered with `@[hop_metric]`;
its failure (no path, an unregistered left side, a residual outside the fragment
of `sum_atoms_le`) is reported in the error of `catcrypt_auto`. A `∀`-quantified
hypothesis, such as `∀ A, AdvantageA G H A ≤ ε`, is not instantiated and is no
hop; a hop for the goal's adversary is passed as an argument (`h A`, or a
reduction lemma applied to `A`). A file-local advantage or probability
definition is read as a distance once it, or its defining equation, carries
`@[hop_metric]`.

An arm succeeds only when it closes the goal, logs no error, and assigns the
goal a proof term without `sorry`. A nested `by` block that fails inside an arm
(for example `exact le_of_eq (by ring)` under `first`) logs its error and admits
its goal instead of throwing; such an arm is rejected, and its messages are
undone with it. Error recovery is off inside an
arm, so a `<;>` branch reports its first error. Each arm runs under
`catcrypt_auto.maxHeartbeats` heartbeats (default 20000, in the unit of
`maxHeartbeats`), counted from its start. An arm that fails, leaves a goal open
or exhausts its budget is undone and the next arm runs; the exhausted budget is
a runtime exception, which `try` and `first` do not catch and `catcrypt_auto`
does. Each arm also runs under `catcrypt_auto.maxMillis` milliseconds (default 5000),
and the whole run under `catcrypt_auto.totalMillis` (default 30000; `0` disables either
budget): a watcher sets the cancellation token of `Core.Context` at the deadline, the
interrupt is caught as the failure "exceeded the time budget of N ms", and once the
total budget is spent the remaining arms are not run. The steps between arms run under
the heartbeat budget of one arm and the time left. An arm's error is reported through
`elideMessage`, which drops goals and trace children before formatting.

## Adding automation

- Tag a new lemma at its definition: `@[gcongr]`, `@[bound]`, or
  `@[aesop … (rule_sets := [CatCryptRel])]`. The last needs an import of
  `CatCryptCore.Tactics.AutoSetsDecl`, which imports only Aesop. A lemma enters
  `CatCryptGrind` by `attribute [scoped grind =] name` (or `grind .`) inside
  `namespace CatCryptGrind`, after its declaration.
- Tag an existing lemma that many modules import in
  [`AutoSets.lean`](AutoSets.lean), never in its defining module: an attribute
  there changes that module and recompiles every module that imports it. A
  registration that needs an import `AutoSets` does not have goes in a new leaf
  module beside it, as [`AutoRules.lean`](AutoRules.lean) does for
  `ssprove_nofail`.
- An Aesop tactic rule takes a tactic without arguments; a rule step with
  arguments (`ssprove_sync_bij f`, `ssprove_swap_at n …`) cannot be one.
- A new shape or arm of `catcrypt_auto` is a `catcrypt_auto_shape` or
  `catcrypt_auto_arm` command (syntax in
  [`AutoDispatchCore.lean`](AutoDispatchCore.lean)) in the module that defines the
  tactic it calls, or in a leaf beside it that imports that module and
  `AutoDispatchCore`; a shape names its head constants by `Name` and needs no import
  of their module. The registration takes effect where the registering module is
  imported. `AutoDispatchCore` itself declares the registry and cannot use it (an
  `initialize` extension is not available in its own module).
- Each registration or arm comes with a test in the matching `Test` module that
  closes a goal of the shape it is for.
- `CatCryptGrind` holds no location constants (`grind` fails on location-id
  disequalities when they are given and closes them when they are not), no
  protocol definitions (they belong in the call, `grind [defs]`) and no lemma
  about `ZMod` (a `grind only [ZMod.natCast_self]` proof of a bind-chain
  equality over `ZMod p` passes elaboration and is rejected by the kernel).

## Pitfalls

- `ℝ≥0∞` is not an ordered ring, so the linear arithmetic of `grind` does not
  run on advantage sums. A bound `a + b ≤ ε₁ + ε₂` closes by `gcongr` followed
  by the hop lemmas, or by `grind` with `add_le_add` (in `CatCryptGrind`). A
  transitivity step through an unnamed middle game is found by neither; state
  the triangle step.
- The `IsPure`/`NoFail` combinators of `SPComp` are stated for `SPComp.bind`.
  A `do` goal needs `simp only [SPComp.monad_bind_eq]` first, or the `>>=` forms
  `SPComp.bindOp_isPure` and `SPComp.bindOp_noFail` of `CatCryptRel`.
- `CatCryptRel` normalises `>>=` to `SPComp.bind`, so the contraction lemmas,
  stated for `>>=`, are not in it.
