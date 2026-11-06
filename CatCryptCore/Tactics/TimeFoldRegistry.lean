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
  `allRetFold`, its implication to the demonic fold of `toFreeMT t` under `allows`, and
  `allRetBind`, the invariant of a bind from the invariant of every continuation (the
  leaf-length rule of `derive_time_bound`);
* `timeLe` — `(t.time : ℕ∞) ≤ wpFold (OpSpec.charge c) (toFreeMT t) (fun _ => 0)`, for a kind
  whose trees occur as charges of positions of another kind (the computation node of an oracle
  program charges the time of its costed tree);
* `laws` — the combinator laws: theorems concluding a bound on the charge fold of the image of a
  combinator application from bounds on the charge folds of the images of its arguments;
* `stepFolds`, `bindFolds` — the equations of `stepFold` and `bindFold` at the further charges
  of the components of a vector charge;
* `useCharge`, `useJoin`, `useStepIff` — a vector charge of the kind: its constant `C`, the
  theorem concluding the use bound `UseBound (C cost) allows x v` of a program from bounds on the
  charge folds of its components (its premises, in the order of the components), and the
  equivalence of the use bound of a step-prefixed image with a statement (the time bound and the
  query count of an oracle program). The readings of a use bound as its component folds are
  among `hypIffs`, the component laws of a combinator among `laws`.

A kind registered again with the same tree type, signature, charge and images refines its record:
the modules that import the second registration read the second record. The vector charge of
oracle programs is registered in this way by the module that defines it, above the module that
registers the kind.

## Main definitions

* `FoldKind` — the record of a kind
* `foldKindExt`, `register_time_fold k` — the registry
* `FoldKind.refines` — a registration refining an earlier one
* `foldKinds` — the registered records, each refined record at its last refinement
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
  /-- `(∀ a, AllRet Q (f a).2) → AllRet Q (A.bind f).2`, read by the leaf-length rule. -/
  allRetBind : Option Name := none
  /-- `(t.time : ℕ∞) ≤ wpFold (OpSpec.charge c) (toFreeMT t) (fun _ => 0)`. -/
  timeLe : Option Name := none
  /-- The combinator laws. -/
  laws : Array Name := #[]
  /-- The equations of `stepFold` at the further component charges of a vector charge. -/
  stepFolds : Array Name := #[]
  /-- The equations of `bindFold` at the further component charges of a vector charge. -/
  bindFolds : Array Name := #[]
  /-- The constant `C` of the vector charge `C cost` of the kind. -/
  useCharge : Option Name := none
  /-- The use bound `UseBound (C cost) allows x v` from the bounds of its component folds. -/
  useJoin : Option Name := none
  /-- The use bound of a step-prefixed image as a statement. -/
  useStepIff : Option Name := none
  deriving Inhabited, Repr

/-- The records registered by `register_time_fold`, the records of imported modules first. -/
initialize foldKindExt : SimplePersistentEnvExtension FoldKind (Array FoldKind) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- Whether `k` refines `k₀`: the same tree type, signature, charge and images. -/
def FoldKind.refines (k k₀ : FoldKind) : Bool :=
  k.timed == k₀.timed && k.sig == k₀.sig && k.charge == k₀.charge &&
    k.toFreeMT == k₀.toFreeMT && k.stepToFreeMT == k₀.stepToFreeMT

/-- The registered records, a refined record replaced by its last refinement. -/
def foldKinds : CoreM (Array FoldKind) :=
  return (foldKindExt.getState (← getEnv)).foldl (init := #[]) fun acc k =>
    match acc.findIdx? (·.timed == k.timed) with
    | some i => acc.set! i k
    | none => acc.push k

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
  if let some k₀ := (← liftCoreM foldKinds).find? (·.timed == k.timed) then
    unless k.refines k₀ do
      throwError "register_time_fold: the tree type `{k.timed}` already has a record with \
        another signature, charge or image"
  let names := #[k.timed, k.sig, k.charge, k.toFreeMT, k.stepToFreeMT, k.timeBoundIff,
      k.stepTimeBoundIff] ++ k.hypIffs ++ k.concls ++ k.laws ++ k.stepFolds ++ k.bindFolds ++
    ([k.allows, k.stepFold, k.bind, k.bindFold, k.allRet, k.allRetFold, k.allRetBind, k.timeLe,
      k.useCharge, k.useJoin, k.useStepIff].filterMap id)
  for c in names do
    unless (← getEnv).contains c do
      throwError "register_time_fold: `{c}` is not a constant"
  modifyEnv (foldKindExt.addEntry · k)

end

end CatCrypt.Tactics.TimeFold
