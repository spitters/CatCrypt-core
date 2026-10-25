/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.AutoTime

/-!
# Tests for the rule of `derive_timed` for registered callees generic in their result type

* `relab`: a structurally recursive relabelling of oracle adversaries, generic in the result
  type, with the hand-registered costed form `relab.timed`, its erasure theorem
  `relab.erase_timed` and the naturality lemma `relab.bind_ret`.
* `red`: a simulation whose handler `rImpl` runs `relab` on a handler `hImpl` whose state
  holds a function (a lazily sampled table) and rebuilds the state; `derive_timed` passes
  the costed tree to `relab.timed` at the costed state. The definitions are not exposed, so
  that the matcher of `rImpl`, which `rImpl.timed` reuses, is private to this module.

## Main results

* `relab.bind_ret` — `(relab X).bind (fun y => .ret (f y)) = relab (X.bind fun y => .ret (f y))`
* `relab.erase_timed` — `(relab.timed A).2.erase = relab A.erase`
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedGenericTest

open CatCrypt.Crypto

/-- A simulation state with a table holding functions. -/
structure St where
  /-- The lazily sampled table. -/
  tab : ℕ → Option (Fin 4)
  /-- The query found, if any. -/
  found : Option ℕ

/-- The lazily sampled table at `c`. -/
noncomputable def lazyT (st : St) (c : ℕ) : OracleAdv ℕ Bool (Fin 4 × St) :=
  match st.tab c with
  | some k => .ret (k, st)
  | none => .rand (PMF.uniformFintype (Fin 4)) fun k =>
      .ret (k, { st with tab := Function.update st.tab c (some k) })

/-- A handler with an `if` under the binder of a query node. -/
noncomputable def hImpl (st : St) (q : ℕ) : OracleAdv ℕ Bool (Fin 4 × St) :=
  .query q fun b =>
    if b then (if q = 0 then .ret (0, { st with found := some q }) else lazyT st q)
    else lazyT st (q + 1)

/-- Each query `q` asked as `.inr q`, each answer read back through `Sum.elim`. -/
noncomputable def relab {α : Type} : OracleAdv ℕ Bool α → OracleAdv (Unit ⊕ ℕ) (Unit ⊕ Bool) α
  | .ret a => .ret a
  | .rand p k => .rand p fun b => relab (k b)
  | .query q k => .query (.inr q) fun a => relab (k (a.elim (fun _ => false) id))

/-- The relabelling of a costed adversary: one unit per query for reading the answer back. -/
noncomputable def relabT {α : Type} :
    OracleAdv.Timed ℕ Bool α → OracleAdv.Timed (Unit ⊕ ℕ) (Unit ⊕ Bool) α
  | .ret a => .ret a
  | .rand p c k => .rand p c fun b => relabT (k b)
  | .query q c k => .query (.inr q) (fun a => c (a.elim (fun _ => false) id) + 1) fun a =>
      relabT (k (a.elim (fun _ => false) id))

/-- The costed form of `relab`. -/
noncomputable def relab.timed {α : Type} (A : OracleAdv.Timed ℕ Bool α) :
    ℕ × OracleAdv.Timed (Unit ⊕ ℕ) (Unit ⊕ Bool) α :=
  (0, relabT A)

/-- Erasing the step costs of `relab.timed A` gives `relab` of the erased adversary. -/
theorem relab.erase_timed {α : Type} (A : OracleAdv.Timed ℕ Bool α) :
    (relab.timed A).2.erase = relab A.erase := by
  induction A with
  | ret a => rfl
  | rand p c k ih =>
    simp only [relab.timed, relabT, OracleAdv.Timed.erase, relab] at ih ⊢; simp only [ih]
  | query q c k ih =>
    simp only [relab.timed, relabT, OracleAdv.Timed.erase, relab] at ih ⊢; simp only [ih]

/-- `relab` commutes with a bind into `ret`. -/
theorem relab.bind_ret {α β : Type} (X : OracleAdv ℕ Bool α) (f : α → β) :
    (relab X).bind (fun y => .ret (f y)) = relab (X.bind fun y => .ret (f y)) := by
  induction X with
  | ret a => rfl
  | rand p k ih => simp only [relab, OracleAdv.bind, ih]
  | query q k ih => simp only [relab, OracleAdv.bind, ih]

/-- The handler `hImpl` behind `relab`, with a direct query on the left summand. -/
noncomputable def rImpl (st : St) : Unit ⊕ ℕ → OracleAdv (Unit ⊕ ℕ) (Unit ⊕ Bool) (Fin 4 × St)
  | .inl _ => .query (.inl ()) fun _ => .ret (0, st)
  | .inr q => relab (hImpl st q)

/-- The simulation of `rImpl`. -/
noncomputable def red (A : OracleAdv (Unit ⊕ ℕ) (Fin 4) Bool) :
    OracleAdv (Unit ⊕ ℕ) (Unit ⊕ Bool) (Option ℕ) :=
  (OracleAdv.simulate rImpl A ⟨fun _ => none, none⟩).bind fun x => .ret x.2.found

derive_timed hImpl

example (x0 : St) (q : ℕ) (x2 : ℕ → ℕ) :
    ((relab.timed (hImpl.timed x0 q x2).2).2.erase.bind fun y =>
      OracleAdv.ret (y.1, ({ tab := y.2.1.1, found := y.2.2 } : St))) = relab (hImpl x0 q) := by
  simp only [relab.erase_timed, relab.bind_ret, hImpl.erase_timed]

example (x0 : St) (q : ℕ) (x2 : ℕ → ℕ) :
    ((OracleAdv.Timed.delay 1 (OracleAdv.Timed.delay (2 + (hImpl.timed x0 q x2).1)
      (relab.timed (hImpl.timed x0 q x2).2))).2.erase.bind fun y =>
      OracleAdv.ret (y.1, ({ tab := y.2.1.1, found := y.2.2 } : St))) = rImpl x0 (Sum.inr q) := by
  simp only [rImpl, OracleAdv.Timed.delay, relab.erase_timed, relab.bind_ret, hImpl.erase_timed]

derive_timed red

example (A : OracleAdv.Timed (Unit ⊕ ℕ) (Fin 4) Bool) : (red.timed A).2.erase = red A.erase :=
  red.erase_timed A

end CatCrypt.Tactics.DeriveTimedGenericTest
