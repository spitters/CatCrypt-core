/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.PassFramework

/-!
# No-Op Elimination Pass

Remove instructions that have no effect on program state:
1. Assignments to `Lnone` with pure expressions (Pconst, Pbool, Parr_init)
2. These are common artifacts of inlining and earlier transformations.

## Main definitions

* `nopElimInstr` — Classify an instruction as removable or not
* `nopElimCmd` — Remove no-op instructions from a command
* `translate_lnone_const_noop` — Key lemma: Lnone+const translates to a semantic no-op

## Proof technique

The key insight: `translateWriteLVal sid (.Lnone _ _) _ = .ret ⟨()⟩` for ANY value.
Combined with a pure expression (Pconst/Pbool/Parr_init), the entire instruction
evaluates to `SPComp.pure ⟨()⟩`, which is the identity under `SPComp.bind`.
-/

namespace CatCrypt.Crypto.Jasmin

open CatCrypt.Deep (RawCode eval_bind eval_ret)
open CatCrypt.Core (SPComp)

set_option autoImplicit false

/-! ## Pass Definition -/

/-- Test if an instruction is a no-op (pure expression assigned to Lnone). -/
def isNopInstr : InstrR → Bool
  | .Cassgn (.Lnone _ _) _ _ (.Pconst _) => true
  | .Cassgn (.Lnone _ _) _ _ (.Pbool _) => true
  | .Cassgn (.Lnone _ _) _ _ (.Parr_init _) => true
  | _ => false

/-- Remove no-op instructions from a command. -/
def nopElimCmd (cmd : Cmd) : Cmd :=
  cmd.filter (fun i => !isNopInstr i)

noncomputable section

/-! ## Key Lemma: Lnone + pure expression is a semantic no-op -/

/-- `translateWriteLVal` to `Lnone` always returns `ret ⟨()⟩`. -/
theorem translateWriteLVal_Lnone (sid : ScopeId) (info : VarInfo)
    (ty : SType) (tv : TypedValue) :
    translateWriteLVal sid (.Lnone info ty) tv = .ret ⟨()⟩ := rfl

/-- Translating a `Cassgn (Lnone ..) _ _ (Pconst z)` is a semantic no-op:
    its eval is `SPComp.pure ⟨()⟩`. -/
theorem translate_cassgn_lnone_const_eval (env : TransEnv) (sid : ScopeId)
    (fuel : Nat) (info : VarInfo) (lty : SType) (tag : AssgnTag)
    (ty : SType) (z : Int) :
    (translateInstrR env sid fuel
      (.Cassgn (.Lnone info lty) tag ty (.Pconst z))).code.eval =
    SPComp.pure ⟨()⟩ := by
  simp [translateInstrR, translatePExpr, translateWriteLVal, eval_bind,
        eval_ret, SPComp.pure_bind, coerceValue]

/-- Same for `Pbool`. -/
theorem translate_cassgn_lnone_bool_eval (env : TransEnv) (sid : ScopeId)
    (fuel : Nat) (info : VarInfo) (lty : SType) (tag : AssgnTag)
    (ty : SType) (b : Bool) :
    (translateInstrR env sid fuel
      (.Cassgn (.Lnone info lty) tag ty (.Pbool b))).code.eval =
    SPComp.pure ⟨()⟩ := by
  simp [translateInstrR, translatePExpr, translateWriteLVal, eval_bind,
        eval_ret, SPComp.pure_bind, coerceValue]

/-- Same for `Parr_init`. -/
theorem translate_cassgn_lnone_arrinit_eval (env : TransEnv) (sid : ScopeId)
    (fuel : Nat) (info : VarInfo) (lty : SType) (tag : AssgnTag)
    (ty : SType) (n : Nat) :
    (translateInstrR env sid fuel
      (.Cassgn (.Lnone info lty) tag ty (.Parr_init n))).code.eval =
    SPComp.pure ⟨()⟩ := by
  simp [translateInstrR, translatePExpr, translateWriteLVal, eval_bind,
        eval_ret, SPComp.pure_bind, coerceValue]

/-- A no-op instruction (as classified by `isNopInstr`) translates to
    `SPComp.pure ⟨()⟩` and leaves the scope ID unchanged. -/
theorem isNopInstr_eval (env : TransEnv) (sid : ScopeId) (fuel : Nat)
    (i : InstrR) (h : isNopInstr i = true) :
    (translateInstrR env sid fuel i).code.eval = SPComp.pure ⟨()⟩ ∧
    (translateInstrR env sid fuel i).newSid = sid := by
  cases i with
  | Cassgn lv tag ty e =>
    cases lv with
    | Lnone info lty =>
      cases e with
      | Pconst z =>
        exact ⟨translate_cassgn_lnone_const_eval env sid fuel info lty tag ty z,
               by simp [translateInstrR]⟩
      | Pbool b =>
        exact ⟨translate_cassgn_lnone_bool_eval env sid fuel info lty tag ty b,
               by simp [translateInstrR]⟩
      | Parr_init n =>
        exact ⟨translate_cassgn_lnone_arrinit_eval env sid fuel info lty tag ty n,
               by simp [translateInstrR]⟩
      | _ => simp [isNopInstr] at h
    | _ => simp [isNopInstr] at h
  | _ => simp [isNopInstr] at h

/-! ## Command-Level Correctness

The full proof uses:
1. `isNopInstr_eval`: nop instructions evaluate to `SPComp.pure ⟨()⟩`
2. `SPComp.pure_bind`: `bind (pure x) f = f x`
3. `translateCmd_fuel_step`: fuel monotonicity when fuel ≥ fuelBound
4. Induction on the command list -/

/-- Nop elimination on a cons: drop nop, keep non-nop. -/
private theorem nopElimCmd_cons_nop (i : InstrR) (is : Cmd) (h : isNopInstr i = true) :
    nopElimCmd (i :: is) = nopElimCmd is := by
  simp [nopElimCmd, List.filter, h]

private theorem nopElimCmd_cons_keep (i : InstrR) (is : Cmd) (h : isNopInstr i = false) :
    nopElimCmd (i :: is) = i :: nopElimCmd is := by
  simp [nopElimCmd, List.filter, h]

/-- No-op elimination preserves command semantics when fuel is sufficient.
    Proved by induction on `cmd` using fuel monotonicity
    (`translateCmd_fuel_step`) to bridge the fuel gap when removing a nop. -/
theorem nopElimCmd_correct_sufficient_fuel :
    ∀ env sid fuel cmd,
      fuel ≥ fuelBoundCmd cmd →
      (translateCmd env (nopElimCmd cmd) sid fuel).code.eval =
      (translateCmd env cmd sid fuel).code.eval := by
  intro env sid fuel cmd hfuel
  induction cmd generalizing sid fuel with
  | nil => rfl
  | cons i is ih =>
    -- fuel ≥ fuelBoundCmd (i :: is) = 1 + max (fuelBoundInstr i) (fuelBoundCmd is)
    -- So fuel ≥ 2, write fuel = n + 1
    have hfuel_pos : fuel ≥ 1 := le_trans (fuelBoundCmd_pos (i :: is)) hfuel
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    have hn_is : n ≥ fuelBoundCmd is := by
      have := Nat.le_max_right (fuelBoundInstr i) (fuelBoundCmd is)
      simp only [fuelBoundCmd_cons] at hfuel; linarith
    by_cases hnop : isNopInstr i = true
    · -- Nop case: remove i, use fuel step for the gap
      rw [nopElimCmd_cons_nop i is hnop]
      rw [translateCmd_cons_eval]
      obtain ⟨hi_eval, hi_sid⟩ := isNopInstr_eval env sid n i hnop
      rw [hi_eval, hi_sid, SPComp.pure_bind]
      -- IH: nopElimCmd is at fuel n+1 = is at fuel n+1
      rw [ih sid (n + 1) (by linarith)]
      -- Fuel step: is at fuel n+1 = is at fuel n
      exact translateCmd_fuel_step env is sid n hn_is
    · -- Keep case: same instruction, IH on tail
      simp only [Bool.not_eq_true] at hnop
      rw [nopElimCmd_cons_keep i is hnop]
      rw [translateCmd_cons_eval, translateCmd_cons_eval]
      congr 1; funext _
      exact ih _ n (by linarith)

end

end CatCrypt.Crypto.Jasmin
