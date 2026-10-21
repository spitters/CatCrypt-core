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
| Distances | `@[hop_metric]` | [`AutoHopRegistry.lean`](AutoHopRegistry.lean) (imports only `Lean`); standard registrations in [`AutoMetrics.lean`](AutoMetrics.lean) | Registers a triangle lemma, a symmetry lemma, an equation `D … = d …` or a definition to unfold. `AutoMetrics` registers `sdist`, `Advantage` and `AdvantageA`; an advantage- or probability-valued definition of a proof becomes a distance by `@[hop_metric]` on it. |
| Distances | `sum_atoms_le` | [`AutoArms.lean`](AutoArms.lean) | Decides `Σ aᵢ ≤ Σ bⱼ` for ℕ-weighted sums of atoms in a canonically ordered semiring (`ℝ≥0∞`), matching each left atom to a right atom equal to it or bounding it by a hypothesis `a ≤ b`. |
| Time bounds | `time_bound`; simp set `time_bound_simps` | [`AutoTime.lean`](AutoTime.lean) | Proves `SPTree.Timed.stepTime x ≤ B`, `t.time ≤ B`, `OracleAdv.Timed.StepTimeBound x n` and `A.TimeBound n` node by node with a path cost `P` (`P + stepTime x ≤ B`, `StepTimeBound x (B - P)`): pairs, `delay`, nodes, binds pushed into nodes or (after a tree that is not a node) charged with its time, `if` and `match` split, non-recursive definitions with visible bodies unfolded; other subtrees bounded by local hypotheses or, below the goal's head, by `N.timeBound_timed`/`N.timeBound`; arithmetic leaves by `omega`, then `linarith`, with the instances of hypotheses `∀ x, f x ≤ b` at the subterms `f a`. `time_bound_simps` holds unfolding equations of definitions whose bodies are not visible. Arm of the direct shape `time bound` (priority 120) of `catcrypt_auto`. |
| Monotonicity | `gcongr_unfold`, `gcongr_unfold [d₁, …]` | [`AutoArms.lean`](AutoArms.lean) | Introduces the binders of `Monotone f`-like goals, unfolds `dᵢ`, runs `gcongr` and closes the side goals by `assumption`, `positivity` or `norm_num`. |
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
