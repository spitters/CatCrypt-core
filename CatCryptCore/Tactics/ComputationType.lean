/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# Computation types

A computation type is a type family `M` whose values `M β` are computations rather than data:
a family tagged `@[computation_type]`, or a family that is not an inductive type, is not `Id`,
is not a quotient and has a `Monad` instance (`StateT σ m`, `ReaderT ρ m`, `OptionT m`, `PMF`).
An inductive family or a quotient with a `Monad` instance (`Option`, `List`, `Except ε`,
`Multiset`) holds data and is a computation type only when tagged. The costed derivations (`derive_timed_structure`, `derive_reduction`)
price a computation only through a registered costed kind, and refuse a field or a data
function whose codomain is a computation type of no such kind. An attribute is usable only in
modules importing the one that declares it, so the declaration is a module of its own.

## Main definitions

* `@[computation_type]` — the tag of a computation type that the `Monad` test does not find
* `isComputationType b` — whether the type `b` is an application of a computation type
-/

public section

meta section

namespace CatCrypt.Tactics.ComputationType

open Lean Meta

/-- The tag `@[computation_type]` of a type family whose values are computations: an inductive
family with a `Monad` instance (`QComp`), or a family without one. -/
initialize computationTypeAttr : TagAttribute ←
  registerTagAttribute `computation_type
    "a type family whose values are computations, priced only through a registered costed kind"

/-- Whether the type `b`, as written, is an application `M a₁ ⋯ aₖ` of a computation type `M`:
a constant tagged `@[computation_type]`, or a constant other than `Id` that is not an inductive
type, whose application does not unfold to a quotient (`Multiset`), and for which
`Monad (M a₁ ⋯ aₖ₋₁)` has an instance. -/
def isComputationType (b : Expr) : MetaM Bool := do
  let b ← instantiateMVars b
  let .const h _ := b.getAppFn | return false
  let env ← getEnv
  if computationTypeAttr.hasTag env h then return true
  if h == ``Id || !b.isApp then return false
  if let some (.inductInfo _) := env.find? h then return false
  if (← whnf b).isAppOf ``Quot then return false
  try
    let inst ← mkAppM ``Monad #[b.appFn!]
    return (← synthInstance? inst).isSome
  catch _ => return false

end CatCrypt.Tactics.ComputationType

end

end
