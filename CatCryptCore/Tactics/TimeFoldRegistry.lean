/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# The registry of costed tree kinds read by the fold rule

The fold rule of `derive_time_bound` (`CatCrypt.Tactics.DeriveTimeBound.foldBound`) bounds the
charge fold `wpFold (OpSpec.chargeUnder c allows) x (fun _ => 0)` of a program `x` of a free monad
`FreeM P α`. A costed tree kind enters the rule through its image in such a free monad: a
translation `toFreeMT` of its costed trees, a translation `stepToFreeMT` of its step-prefixed
costed trees, and the equivalences between its time-bound predicates and bounds on the charge
folds of these images. `register_time_fold k` adds the record `k : FoldKind`, a constant, to the
table read by the rule. The record is kept apart from the tree kinds of `register_tree_kind`
because the modules that translate a kind into a free monad import the module that registers
the kind.

Each field names a constant of the environment:

* `timed` — the head of the costed tree type, for instance `SPTree.Timed`;
* `sig`, `charge`, `allows` — the signature of the image, the charge of a position (a function
  into `ℕ`, possibly of parameters of the tree) and the answer relation (`none`: every answer);
* `toFreeMT`, `stepToFreeMT` — the images; the node equations of `toFreeMT` are its equation
  lemmas;
* `timeBoundIff` — `∀ t n, P t n ↔ wpFold Φ (toFreeMT t) (fun _ => 0) ≤ n`, the time-bound
  predicate `P` of a costed tree; its left side states the hypothesis of a binder tree;
* `stepTimeBoundIff` — the same for the step time bound of a step-prefixed tree; its left side
  states the time theorem of a costed tree of the kind;
* `hypIffs` — further equivalences or implications `P t n → fold ≤ n`, read at the conclusions
  of the time theorems of callees and at hypotheses;
* `concls` — implications `fold ≤ n → P t n`, read at goals;
* `stepFold` — the charge fold of `stepToFreeMT x` is `x.1` plus the charge fold of
  `toFreeMT x.2` (under every answer relation admitting the tick answers);
* `bind`, `bindFold` — the bind of the kind and the equation of the charge fold of
  `stepToFreeMT (A.bind f)` with the charge fold of `(toFreeMT A).bind (stepToFreeMT ∘ f)`;
* `allRet` — the leaf invariant `AllRet Q t` of the kind, read at the conclusions of callees,
  and `allRetFold`, its implication to the demonic fold of `toFreeMT t` under `allows`;
* `timeLe` — `(t.time : ℕ∞) ≤ wpFold (OpSpec.charge c) (toFreeMT t) (fun _ => 0)`, for a kind
  whose trees occur as charges of positions of another kind (the computation node of an oracle
  program charges the time of its costed tree);
* `laws` — the combinator laws: theorems concluding a bound on the charge fold of the image of a
  combinator application from bounds on the charge folds of the images of its arguments.

## Main definitions

* `FoldKind` — the record of a kind
* `foldKindExt`, `register_time_fold k` — the registry
* `foldKinds` — the registered records
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.TimeFold

open Lean Elab Command

meta section

/-- The record of a costed tree kind read by the fold rule; see the module docstring. -/
structure FoldKind where
  /-- The head of the costed tree type. -/
  timed : Name
  /-- The signature of the images. -/
  sig : Name
  /-- The charge of a position, into `ℕ`. -/
  charge : Name
  /-- The answer relation; `none` admits every answer. -/
  allows : Option Name := none
  /-- The image of a costed tree. -/
  toFreeMT : Name
  /-- The image of a step-prefixed costed tree. -/
  stepToFreeMT : Name
  /-- `P t n ↔ wpFold Φ (toFreeMT t) (fun _ => 0) ≤ n`. -/
  timeBoundIff : Name
  /-- `Q x n ↔ wpFold Φ (stepToFreeMT x) (fun _ => 0) ≤ n`. -/
  stepTimeBoundIff : Name
  /-- Further equivalences or implications from a time-bound predicate to a fold bound. -/
  hypIffs : Array Name := #[]
  /-- Implications from a fold bound to a time-bound predicate, read at goals. -/
  concls : Array Name := #[]
  /-- The fold of `stepToFreeMT x` is `x.1` plus the fold of `toFreeMT x.2`. -/
  stepFold : Option Name := none
  /-- The bind of the kind. -/
  bind : Option Name := none
  /-- The fold equation of `stepToFreeMT (A.bind f)`. -/
  bindFold : Option Name := none
  /-- The leaf invariant `AllRet Q t` of the kind. -/
  allRet : Option Name := none
  /-- `AllRet Q t → wpFold (OpSpec.demonicUnder allows) (toFreeMT t) Q`. -/
  allRetFold : Option Name := none
  /-- `(t.time : ℕ∞) ≤ wpFold (OpSpec.charge c) (toFreeMT t) (fun _ => 0)`. -/
  timeLe : Option Name := none
  /-- The combinator laws. -/
  laws : Array Name := #[]
  deriving Inhabited, Repr

/-- The records registered by `register_time_fold`, the records of imported modules first. -/
initialize foldKindExt : SimplePersistentEnvExtension FoldKind (Array FoldKind) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- The registered records. -/
def foldKinds : CoreM (Array FoldKind) :=
  return foldKindExt.getState (← getEnv)

/-- The record whose costed tree type has the head `n`. -/
def foldKindOf? (n : Name) : CoreM (Option FoldKind) :=
  return (← foldKinds).find? (·.timed == n)

/-- The record of the constant `n`, evaluated. -/
unsafe def evalFoldKindUnsafe (n : Name) : CoreM FoldKind := do
  ofExcept <| (← getEnv).evalConstCheck FoldKind (← getOptions) ``FoldKind n

@[implemented_by evalFoldKindUnsafe]
opaque evalFoldKind (n : Name) : CoreM FoldKind

/-- `register_time_fold k` adds the record `k : FoldKind`, a constant, to the registry of the
fold rule for the modules that import the current one. Every name of the record must be a
constant of the environment. -/
syntax (name := registerTimeFoldCmd) "register_time_fold " ident : command

@[command_elab registerTimeFoldCmd]
def elabRegisterTimeFold : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload stx[1]
  let k ← liftCoreM <| evalFoldKind n
  if (← liftCoreM foldKinds).any (·.timed == k.timed) then
    throwError "register_time_fold: the tree type `{k.timed}` already has a record"
  let names := #[k.timed, k.sig, k.charge, k.toFreeMT, k.stepToFreeMT, k.timeBoundIff,
      k.stepTimeBoundIff] ++ k.hypIffs ++ k.concls ++ k.laws ++
    ([k.allows, k.stepFold, k.bind, k.bindFold, k.allRet, k.allRetFold, k.timeLe].filterMap id)
  for c in names do
    unless (← getEnv).contains c do
      throwError "register_time_fold: `{c}` is not a constant"
  modifyEnv (foldKindExt.addEntry · k)

end

end CatCrypt.Tactics.TimeFold
