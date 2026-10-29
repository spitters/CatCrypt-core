/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveCost

/-!
# Tests of `derive_cost`: a callee's field path of a pair binder

`tick` takes a state `s : Cf × List ℕ` whose first component holds a function; its derived cost
takes the cost companion of the data path `s.1`, a primitive projection of the pair binder `s`.
`dec` calls `tick` at its own binder `s`: the cost of `dec` takes the companion of `s.1` and
passes it to `tick.timedCost`. No module imports this file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedProjPathTest

/-- A configuration: an environment, a current position and a stack of positions. -/
structure Cf where
  /-- The environment. -/
  env : ℕ → Option ℕ
  /-- The current position. -/
  cur : ℕ
  /-- The positions left. -/
  ks : List ℕ

/-- The configuration past the finished positions `0`. -/
def popAux : ℕ → List ℕ → (ℕ → Option ℕ) → Cf
  | 0, k :: ks, ρ => popAux k ks ρ
  | s, ks, ρ => ⟨ρ, s, ks⟩

/-- The configuration `c` past its finished positions. -/
def Cf.pop (c : Cf) : Cf := popAux c.cur c.ks c.env

/-- A step of the state `s`: the configuration past its finished positions, a binding at a
nonzero position, and the value read at it. -/
def tick (s : Cf × List ℕ) : (Cf × List ℕ) × ℕ :=
  let c := s.1.pop
  match c.cur with
  | 0 => ((c, s.2), 0)
  | n+1 => (({ c with env := fun x => if x = n then some n else c.env x }, s.2.tail),
      (c.env n).getD 0)

/-- A step on an event: a tick, or a push onto the queue of the state. -/
def dec (s : Cf × List ℕ) : Bool → (Cf × List ℕ) × ℕ
  | true => tick s
  | false => ((s.1, 0 :: s.2), 0)

derive_cost popAux
derive_cost tick
derive_cost dec

/-- The cost of `dec` takes the companion of the environment and the costed value of `s.1`. -/
noncomputable example (s : Cf × List ℕ) (b : Bool) (envCost : ℕ → ℕ)
    (fstHat : ((ℕ → Option ℕ) × (ℕ → ℕ)) × ℕ × List ℕ) : ℕ :=
  dec.timedCost s b envCost fstHat

end CatCrypt.Tactics.DeriveTimedProjPathTest
