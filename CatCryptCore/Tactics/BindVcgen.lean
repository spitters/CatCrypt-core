/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCryptCore.Tactics.BindAlign
public import CatCryptCore.Tactics.BindAlign
public meta import CatCryptCore.Core.Code
public import CatCryptCore.Core.Code

/-!
# `bind_vcgen` — run-to-completion for `SPComp`-*equality* goals

Distributional-equivalence proofs commonly have the shape

```
  SPComp.bind X (fun a => … pure (…)) = SPComp.bind Y (fun b => … pure (…))
```

i.e. an equality of two `SPComp.bind` chains, *not* a refinement. The proof is
always the same run-to-completion loop: repeatedly **normalize** (flatten
`bind_assoc`, fire `pure_bind`) and **peel** (`bind_align`) matching layers,
commuting a pure sample past an independent bind where needed, until the two
chains coincide up to a single change-of-variables residual — which the caller
supplies via a bijection.

## Attribution

The run-to-completion relational-VC-gen design is borrowed from **VCVio**'s
`rvcgen` (Devon Tuma, *VCVio: Verified Cryptography in Lean via Oracle Effects
and Handlers*, ePrint 2026/899) and **Loom** (`verse-lab/loom`). Those drive a
*refinement* (approximate-coupling / arWP) judgement to completion; `bind_vcgen`
is the `SPComp`-*equality* analogue — the exact-coupling, ε = 0 case, where the
two sides are provably the same distribution rather than ε-close. The `using`
clause mirrors `rvcstep using`: the caller hands in the change-of-variables
`Equiv` that the mechanical loop cannot guess.

## What is automated vs. supplied

`bind_vcgen` fully automates the *mechanical* part shared by every such proof:

* `spcomp_normalize` — a `simp only` over the monad rewrite set
  (`monad_bind_eq`, `bind_assoc`, `pure_bind`, `map`). Unfolding `SPComp.map`
  lets `bind_assoc` fuse a `map`-of-`bind` into the inner bind. It fails cleanly
  when it makes no progress, so it is safe inside `first`/`repeat`.
* `bind_step` (from `BindAlign`) — peels one matching `SPComp.bind` (head-strict
  `congrArg` + `funext`). Stops at the first head mismatch.

The loop `repeat (first | rfl | spcomp_normalize | bind_step)` runs these to a
fixpoint, closing goals that are pure reassociation / `pure`-elimination /
matching-prefix peeling, and otherwise reducing the goal to the residual equality.

The crux step is **caller-supplied**, because it needs data the loop cannot
synthesize:

* **change of variables** — `bind_vcgen using e` rewrites the `sample`-residual
  `bind (sample α) f = bind (sample β) g` by `SPComp.sample_bind_equiv e`
  (targeting the RHS only, via `refine Eq.trans ?_ (…)`, which pins the change
  to the right-hand `sample`), then peels again, leaving the pointwise
  `f a = g (e a)` obligation (discharged from `e.left_inv`).

## Change of variables found from the context

`bij_cov [t₁, …]` proves an `SPComp` equality by a change of variables through a
bijection at a uniform sample. The candidate bijections are the terms of type `α ≃ β` or
`Function.Bijective f` (read as `Equiv.ofBijective f h`) among the local hypotheses, the
fields of structure-typed local hypotheses and the arguments `tᵢ`; the leading explicit
binders of a candidate are instantiated by local variables of their type and its instance
binders by instance synthesis. A candidate is kept when both `α` and `β` are sampled in the
goal (definitional equality at default transparency, so that a field of a structure
instance such as `B.toScheme.Key` matches `B.Key`). For each kept candidate `e` and for
`e.symm`, on the goal and on its symmetric form, a side that is a bare `SPComp.sample β` is
read as `SPComp.bind (SPComp.sample β) pure` and `bind_vcgen using e` runs; when this
leaves goals, `bind_vcgen` first peels the common prefix of the two chains and
`bind_vcgen using e` runs on each residual. The procedure fails without running any tactic
when the goal is not an `SPComp` equality, has no sample, or no candidate matches the
sampled types.

The module registers with `catcrypt_auto` (`CatCryptCore.Tactics.AutoDispatchCore`) the
arms `bind_vcgen` and `bij_cov` of the shape `SPComp equality`, at orders 20 and 21.
-/

public section

meta section

namespace CatCrypt.Tactic

open Lean Elab Tactic

/-- Normalize an `SPComp` bind-chain: rewrite `>>=` to `SPComp.bind`, flatten
    `bind_assoc`, fire `pure_bind`, and unfold `SPComp.map` (so `bind_assoc` can
    fuse a `map`-of-`bind` into its inner bind).

    Uses `simp only`, so it **fails cleanly when it makes no progress** — this
    makes it safe as an alternative inside `first`/`repeat`. -/
syntax "spcomp_normalize" : tactic
macro_rules
  | `(tactic| spcomp_normalize) => `(tactic|
      -- The rewrite set is fixed and generic, so not every lemma fires on every
      -- goal; silence the `unusedSimpArgs` linter at the call site.
      set_option linter.unusedSimpArgs false in
      simp only [CatCrypt.Core.SPComp.monad_bind_eq, CatCrypt.Core.SPComp.bind_assoc,
                 CatCrypt.Core.SPComp.pure_bind, CatCrypt.Core.SPComp.map])

/-- Run-to-completion driver for `SPComp`-*equality* goals.

    `bind_vcgen` repeatedly normalizes (`spcomp_normalize`) and peels matching
    `SPComp.bind` layers (`bind_step`) until it is stuck — closing the goal
    outright when the two bind-chains coincide, or leaving the residual
    (a leaf equality / a `sample`-change-of-variables) for the caller.

    `bind_vcgen using e` additionally applies the change-of-variables
    `SPComp.sample_bind_equiv e` to the `sample`-residual (rewriting the RHS
    only), then peels again — leaving the pointwise `f a = g (e a)` obligation,
    which follows from `e.left_inv`.

    See the module docstring for the VCVio/Loom attribution and the precise
    "automated vs. supplied" split. -/
syntax "bind_vcgen" (" using " term)? : tactic
macro_rules
  | `(tactic| bind_vcgen) => `(tactic|
      repeat (first | rfl | spcomp_normalize | bind_step))
  | `(tactic| bind_vcgen using $e) => `(tactic|
      (try spcomp_normalize);
      (try (refine Eq.trans ?_ (CatCrypt.Core.SPComp.sample_bind_equiv $e _)));
      (repeat (first | rfl | spcomp_normalize | bind_step)))

namespace GameTransform

open Meta

/-- The types `α` of the uniform samples `SPComp.sample α` occurring in `e`. -/
partial def sampleTypes (e : Expr) (out : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``CatCrypt.Core.SPComp.sample 3 then
    let α := e.getArg! 0
    if out.contains α then out else out.push α
  else
    match e with
    | .app f a => sampleTypes a (sampleTypes f out)
    | .lam _ d b _ | .forallE _ d b _ => sampleTypes b (sampleTypes d out)
    | .letE _ t v b _ => sampleTypes b (sampleTypes v (sampleTypes t out))
    | .mdata _ b => sampleTypes b out
    | .proj _ _ b => sampleTypes b out
    | _ => out

/-- `e` is an `SPComp` equality: its type is `@Eq (SPComp α) l r`. -/
def spcompEq? (t : Expr) : Option (Expr × Expr) := do
  let some (ty, l, r) := t.eq? | none
  guard (ty.isAppOf ``CatCrypt.Core.SPComp)
  return (l, r)

/-- The maximal number of local variables tried for one binder of a candidate. -/
def maxPerBinder : Nat := 3

/-- The maximal number of candidate bijections kept. -/
def maxCandidates : Nat := 8

/-- The local variables (not implementation details) whose type is `d` up to reducible
definitional equality, at most `maxPerBinder` of them, most recent first. -/
def localsOfType (d : Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  for decl in (← getLCtx).decls.toArray.reverse do
    let some decl := decl | continue
    if decl.isImplementationDetail then continue
    if out.size ≥ maxPerBinder then break
    if ← withReducible (isDefEq decl.type d) then out := out.push decl.toExpr
  return out

/-- The instances of the term `t : ty` whose leading binders are instantiated (explicit and
implicit ones by local variables of their type, instance ones by synthesis), up to `fuel`
binders, ending in a type `α ≃ β` or `Function.Bijective f`; each is returned as an
equivalence. -/
partial def equivInstances (t ty : Expr) (fuel : Nat) : MetaM (Array Expr) := do
  let ty ← whnfR (← instantiateMVars ty)
  if ty.isAppOfArity ``Equiv 2 then return #[t]
  if ty.isAppOfArity ``Function.Bijective 3 then
    match ← observing? (mkAppM ``Equiv.ofBijective #[ty.getArg! 2, t]) with
    | some e => return #[e]
    | none => return #[]
  let .forallE _ d b bi := ty | return #[]
  if fuel == 0 then return #[]
  if bi.isInstImplicit then
    let some i ← observing? (synthInstance d) | return #[]
    return ← equivInstances (mkApp t i) (b.instantiate1 i) (fuel - 1)
  let mut out := #[]
  for v in ← localsOfType d do
    out := out ++ (← equivInstances (mkApp t v) (b.instantiate1 v) (fuel - 1))
  return out

/-- The type `T` mentions `Equiv` or `Function.Bijective`. -/
def mentionsBij (T : Expr) : Bool :=
  (T.find? fun e => e.isConstOf ``Equiv || e.isConstOf ``Function.Bijective).isSome

/-- The candidate bijections: the instances (`equivInstances`) of the terms `extra`, of
the local hypotheses and of the fields of structure-typed local hypotheses. -/
def candidates (extra : Array Expr) : MetaM (Array Expr) := do
  let mut srcs : Array Expr := extra
  for h in ← getLocalHyps do
    let decl ← h.fvarId!.getDecl
    if decl.isImplementationDetail || decl.binderInfo.isInstImplicit then continue
    let ty ← instantiateMVars decl.type
    if mentionsBij ty then srcs := srcs.push h
    let tyR ← whnfR ty
    let some sName := tyR.getAppFn.constName? | continue
    let env ← getEnv
    unless isStructure env sName do continue
    for f in getStructureFieldsFlattened env sName (includeSubobjectFields := false) do
      let some p ← observing? (mkProjection h f) | continue
      let some pty ← observing? (inferType p) | continue
      if mentionsBij pty then srcs := srcs.push p
  let mut out := #[]
  for s in srcs do
    out := out ++ (← equivInstances s (← inferType s) 4)
  return out

/-- The type `e` is definitionally equal to a member of `ts` (default transparency, so that
a field of a structure instance such as `B.toScheme.Key` matches `B.Key`). -/
def memDefEq (e : Expr) (ts : Array Expr) : MetaM Bool :=
  ts.anyM fun t => isDefEq e t

/-- The candidate bijections whose domain and codomain are both sampled in `goal`. -/
def matchingCandidates (goal : Expr) (extra : Array Expr) : MetaM (Array Expr) := do
  let tys := sampleTypes goal
  if tys.isEmpty then return #[]
  let mut out := #[]
  for c in ← candidates extra do
    if out.size ≥ maxCandidates then break
    let cty ← whnfR (← inferType c)
    unless cty.isAppOfArity ``Equiv 2 do continue
    if (← memDefEq (cty.getArg! 0) tys) && (← memDefEq (cty.getArg! 1) tys) then
      out := out.push c
  return out

/-- Elaborate the arguments of `bij_cov [t₁, …]`. -/
def elabArgs (stx : Syntax) : TacticM (Array Expr) := do
  let ts : Array Syntax := if stx[1].isNone then #[] else stx[1][1].getSepArgs
  withMainContext <| ts.mapM fun t => Term.withoutErrToSorry (elabTerm t none)

/-- Run `tac` on the main goal; keep the result when it closes every goal, else restore
the state and return `false`. -/
def closes (tac : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try
    tac
    if (← getUnsolvedGoals).isEmpty then return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

/-- `bij_cov [t₁, …]` proves an `SPComp` equality by a change of variables through a
bijection at a uniform sample, the bijection being taken from the local hypotheses, the
fields of structure-typed hypotheses and the arguments (see the module docstring). -/
syntax (name := bijCovStx) "bij_cov" (" [" term,* "]")? : tactic

/-- The elaborator of `bij_cov`. -/
@[tactic bijCovStx] def evalBijCov : Tactic := fun stx => do
  let extra ← elabArgs stx
  let g ← getMainGoal
  let cands ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some _ := spcompEq? t | throwError "bij_cov: the goal is not an SPComp equality"
    let cs ← matchingCandidates t extra
    if cs.isEmpty then
      throwError "bij_cov: no bijection between the sampled types of the goal"
    return cs
  for c in cands do
    for e in #[c, ← g.withContext (mkAppM ``Equiv.symm #[c])] do
      let cod ← g.withContext do return (← whnfR (← inferType e)).getArg! 1
      let es ← g.withContext (Term.exprToSyntax e)
      let cs ← g.withContext (Term.exprToSyntax cod)
      for flip in [false, true] do
        let run (peel : Bool) : TacticM Unit := do
          if flip then evalTactic (← `(tactic| symm))
          evalTactic (← `(tactic|
            try rw [← CatCrypt.Core.SPComp.bind_pure (CatCrypt.Core.SPComp.sample $cs)]))
          if peel then
            evalTactic (← `(tactic| bind_vcgen))
            evalTactic (← `(tactic| all_goals bind_vcgen using $es))
          else
            evalTactic (← `(tactic| bind_vcgen using $es))
        if ← closes (run false) then return
        if ← closes (run true) then return
  throwError "bij_cov: no candidate bijection closes the goal ({cands.size} tried)"

end GameTransform

end CatCrypt.Tactic

end

/-! ## Arm of `catcrypt_auto` -/

catcrypt_auto_arm "SPComp equality" order 20 := "bind_vcgen"
catcrypt_auto_arm "SPComp equality" order 21 := "bij_cov%GRIND"
