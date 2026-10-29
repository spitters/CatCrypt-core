/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.AutoTime

/-!
# Tests for the recursive data functions of `derive_timed`

A miniature of a choreography simulator: a configuration `Cfg` holds an environment and a label
map (functions) and a list of continuations, each with the environment and labels it restores.

* `Cfg.popAux`: the configuration after its finished branches, by structural recursion over the
  list of continuations; its result holds functions.
* `hImpl`: a handler whose state is a configuration, which calls `Cfg.popAux` and matches on the
  statement of its result.
* `red`: the simulation of `hImpl`; `derive_timed` derives the costed value
  `Cfg.popAux.timed` and its erasure theorem on the way.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedRecFnTest

open CatCrypt.Crypto

/-- The statements of the miniature. -/
inductive Stmt where
  | skip
  | set (x v : ℕ) (k : Stmt)
  | ask (x : ℕ) (k : Stmt)

/-- A configuration: the statement, the continuations with the environments and labels they
restore, the environment, the labels and the last answer. -/
structure Cfg where
  /-- The statement being run. -/
  cur : Stmt
  /-- The continuations, innermost first. -/
  konts : List ((ℕ → Option ℕ) × (ℕ → Option Bool) × Stmt)
  /-- The environment. -/
  env : ℕ → Option ℕ
  /-- The labels. -/
  lab : ℕ → Option Bool
  /-- The last answer. -/
  got : Option ℕ

/-- The configuration after its finished branches. -/
def Cfg.popAux (got : Option ℕ) :
    Stmt → List ((ℕ → Option ℕ) × (ℕ → Option Bool) × Stmt) → (ℕ → Option ℕ) →
      (ℕ → Option Bool) → Cfg
  | .skip, (ρ, lb, k) :: ks, _, _ => Cfg.popAux got k ks ρ lb
  | s, ks, ρ, lb => ⟨s, ks, ρ, lb, got⟩

/-- The configuration `c` after its finished branches. -/
def Cfg.pop (c : Cfg) : Cfg := Cfg.popAux c.got c.cur c.konts c.env c.lab

/-- A step of the configuration at the query `q`. -/
noncomputable def hImpl (st : Cfg) (q : ℕ) : OracleAdv ℕ Bool (Option ℕ × Cfg) :=
  let c := st.pop
  match c.cur with
  | .skip => .ret (none, c)
  | .set x v k => .ret (c.env x, { c with cur := k, env := Function.update c.env x (some v) })
  | .ask x k => .query (q + x) fun b =>
      .ret (c.env q, { c with cur := k, lab := Function.update c.lab x (some b) })

/-- The simulation of `hImpl` from a configuration with one continuation. -/
noncomputable def red (A : OracleAdv ℕ (Option ℕ) Bool) : OracleAdv ℕ Bool Bool :=
  (OracleAdv.simulate hImpl A
    ⟨.skip, [(fun _ => none, fun _ => none, .ask 0 .skip)], fun _ => none, fun _ => none,
      none⟩).bind fun x => .ret x.1

derive_timed red

example (A : OracleAdv.Timed ℕ (Option ℕ) Bool) : (red.timed A).2.erase = red A.erase :=
  red.erase_timed A

example (got : Option ℕ) (s : Stmt) (ks : List ((ℕ → Option ℕ) × (ℕ → Option Bool) × Stmt))
    (ρ : ℕ → Option ℕ) (ρc : ℕ → ℕ) (lb : ℕ → Option Bool) (lbc : ℕ → ℕ) :
    (Cfg.popAux.timed got s ks ρ ρc lb lbc).2.2.1.1 = (Cfg.popAux got s ks ρ lb).env :=
  Cfg.popAux.erase_timed_2 got s ks ρ ρc lb lbc

end CatCrypt.Tactics.DeriveTimedRecFnTest
