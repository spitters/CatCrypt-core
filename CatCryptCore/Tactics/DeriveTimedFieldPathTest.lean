/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveCost
public import CatCryptCore.Tactics.StdCosts

/-!
# Tests of field paths, deduplication costs and rebuilt states under `derive_timed`

* a callee cost taking the companions of two fields of a binder, all recorded in the first pass
  (`pendL`, `redL`);
* a field of a projection of a constructor application, priced at the reduced path (`resumeB`,
  `redB`);
* the registered costs of `List.toFinset` and `Multiset.toFinset` (`ksM`, `ksL`);
* a simulator state rebuilt from projections that a case hypothesis rewrote (`startR`), and a
  callee whose body is a `let` followed by a match (`tickR`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedFieldPathTest

open CatCrypt.Crypto

/-- A local language with two function fields. -/
structure LL where
  /-- Evaluation. -/
  eval : ℕ → ℕ
  /-- The truth value of a value. -/
  toBool : ℕ → Bool

/-- A step that reads both fields of the language. -/
def stepL (l : LL) (n : ℕ) : Bool := l.toBool (l.eval n)

derive_cost stepL

/-- A caller of `stepL`. -/
def pendL (l : LL) (n : ℕ) : Bool := stepL l (n + 1)

/-- A reduction calling `stepL`. -/
def redL {D R : Type} (l : LL) (n : ℕ) : OracleAdv D R Bool := .ret (stepL l n)

derive_cost pendL
derive_timed redL

/-- A configuration with an environment. -/
structure Cfg where
  /-- The environment. -/
  env : ℕ → ℕ

/-- A state holding a configuration. -/
structure HSt where
  /-- The configuration. -/
  cfg : Cfg
  /-- The pending work. -/
  pend : ℕ

/-- A function reading the environment of a configuration. -/
def useEnv (c : Cfg) (n : ℕ) : ℕ := c.env n

derive_cost useEnv

/-- A call of `useEnv` at a field of a constructor application. -/
def resumeB (s : HSt) (n : ℕ) : ℕ := useEnv ({ cfg := s.cfg, pend := 0 } : HSt).cfg n

/-- A reduction calling `useEnv` at a field of a constructor application. -/
def redB {D R : Type} (s : HSt) (n : ℕ) : OracleAdv D R ℕ :=
  .ret (useEnv ({ cfg := s.cfg, pend := 0 } : HSt).cfg n)

derive_cost resumeB
derive_timed redB

/-- The keys of a multiset. -/
def ksM (s : Multiset ℕ) : Finset ℕ := s.toFinset

/-- The present keys of a list. -/
def ksL (l : List (Option ℕ)) : Finset ℕ := (l.filterMap id).toFinset

derive_cost ksM
derive_cost ksL

example (s : Multiset ℕ) : ksM.timedCost s = 1 + Multiset.toFinset.timedCost ℕ s := rfl

/-- An update of a queue table at one index. -/
def upd (q : ℕ → List ℕ) (h : ℕ) (v : List ℕ) : ℕ → List ℕ :=
  fun y => if y = h then v else q y

/-- Pending work of a simulator. -/
inductive Pd where
  | idle
  | evt (e : ℕ)
  | bind (x : ℕ) (w : Option ℕ)

/-- A configuration with a statement and an environment. -/
structure Cf where
  /-- The statement. -/
  cur : ℕ
  /-- The environment. -/
  env : ℕ → Option ℕ

/-- A simulator state over `Cf`. -/
structure St where
  /-- The configuration. -/
  cfg : Cf
  /-- Whether the simulator has started. -/
  started : Bool
  /-- The input queues. -/
  iq : ℕ → List ℕ
  /-- The pending work. -/
  pend : Pd

/-- A step on the statement of the configuration. -/
def tick (s : St) : St × (ℕ ⊕ Option ℕ) :=
  match s.cfg.cur with
  | 0 => ({ s with cfg := { s.cfg with cur := 1 } }, .inr none)
  | k + 1 =>
      ({ s with
          iq := upd s.iq k (s.iq k).tail
          pend := .bind k none }, .inl k)

/-- The start of an activation. -/
def stt (s : St) : St × (ℕ ⊕ Option ℕ) :=
  if s.started then tick s else ({ s with started := true }, .inl 0)

/-- The start of an activation as an oracle tree. -/
def startR {D R : Type} (s : St) : OracleAdv D R (St × (ℕ ⊕ Option ℕ)) := .ret (stt s)

derive_timed startR

/-- A configuration with continuations. -/
structure Cg where
  /-- The statement. -/
  cur : ℕ
  /-- The continuations. -/
  konts : List ℕ
  /-- The environment. -/
  env : ℕ → Option ℕ

/-- The configuration past its finished statements. -/
def popAux : ℕ → List ℕ → (ℕ → Option ℕ) → Cg
  | 0, k :: ks, ρ => popAux k ks ρ
  | s, ks, ρ => ⟨s, ks, ρ⟩

/-- The configuration `c` past its finished statements. -/
def Cg.pop (c : Cg) : Cg := popAux c.cur c.konts c.env

/-- A simulator state over `Cg`. -/
structure St2 where
  /-- The configuration. -/
  cfg : Cg
  /-- The input queues. -/
  iq : ℕ → List ℕ
  /-- The pending work. -/
  pend : Pd

/-- A step whose body is a `let` followed by a match. -/
def tick2 (s : St2) : St2 × (ℕ ⊕ Option ℕ) :=
  let c := s.cfg.pop
  match c.cur with
  | 0 => ({ s with cfg := c }, .inr none)
  | k + 1 =>
      ({ s with
          cfg := { c with cur := k }
          iq := upd s.iq k (s.iq k).tail
          pend := .bind k none }, .inl k)

/-- The step `tick2` as an oracle tree. -/
def tickR {D R : Type} (s : St2) : OracleAdv D R (St2 × (ℕ ⊕ Option ℕ)) := .ret (tick2 s)

derive_timed tickR

end CatCrypt.Tactics.DeriveTimedFieldPathTest
