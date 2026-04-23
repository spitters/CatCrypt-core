/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminTranslate
import CatCrypt.Deep.Eval

/-!
# Jasmin Compiler Pass Framework

Framework for defining and composing semantics-preserving compiler passes
on Jasmin programs. Pass correctness is stated as preservation of `RawCode.eval`,
bridging the deep → shallow embedding.

## Main definitions

* `RawCode.semEquiv` — Semantic equivalence of RawCode programs (via eval)
* `ExprPassCorrect` — Correctness predicate for expression-level passes
* `CmdPassCorrect` — Correctness predicate for command-level passes
* `mapInstrExprs` — Apply an expression transform across an instruction
* `mapCmdExprs` — Apply an expression transform across a command

## References

* Jasmin 2025 paper (arXiv 2511.11292): compiler pass correctness via ITree semantics
* "The Last Yard" (CPP 2024): Jasmin → CatCrypt bridge
-/

namespace CatCrypt.Crypto.Jasmin

open CatCrypt.Deep (RawCode eval_bind eval_ret eval_sample eval_fail)
open CatCrypt.Core (SPComp)

set_option autoImplicit false

noncomputable section

/-! ## Semantic Equivalence -/

/-- Two RawCode programs are semantically equivalent when they evaluate
    to the same SPComp computation. -/
def RawCode.semEquiv {α : Type*} (c₁ c₂ : RawCode α) : Prop := c₁.eval = c₂.eval

/-! ## Pass Correctness Predicates -/

/-- An expression pass is correct when it preserves the eval of the
    translated expression for all scope IDs. -/
def ExprPassCorrect (pass : PExpr → PExpr) : Prop :=
  ∀ sid e, (translatePExpr sid (pass e)).eval = (translatePExpr sid e).eval

/-- A command pass is correct when it preserves the eval of the translated
    code for all environments, scope IDs, and fuel values.
    The `newSid` may differ (scoping changes are allowed). -/
def CmdPassCorrect (pass : Cmd → Cmd) : Prop :=
  ∀ env sid fuel cmd,
    (translateCmd env (pass cmd) sid fuel).code.eval =
    (translateCmd env cmd sid fuel).code.eval

/-- A program pass is correct when it preserves the eval of the translated
    entry function for all programs, entry points, arguments, and fuel. -/
def ProgPassCorrect (pass : JasminProg → JasminProg) : Prop :=
  ∀ prog entryFn args fuel,
    (translateProg (pass prog) entryFn args fuel).map RawCode.eval =
    (translateProg prog entryFn args fuel).map RawCode.eval

/-! ## Pass Composition -/

/-- Composing two correct expression passes yields a correct pass. -/
theorem exprPassCorrect_comp {p₁ p₂ : PExpr → PExpr}
    (h₁ : ExprPassCorrect p₁) (h₂ : ExprPassCorrect p₂) :
    ExprPassCorrect (p₁ ∘ p₂) := by
  intro sid e
  simp only [Function.comp]
  rw [h₁, h₂]

/-- The identity pass is correct. -/
theorem exprPassCorrect_id : ExprPassCorrect id := by
  intro sid e; rfl

end

/-! ## Expression Mapping

Apply an expression transform to all sub-expressions in instructions
and commands. Only transforms RHS expressions, not l-value index expressions. -/

/-- Apply an expression transform to all sub-expressions in an instruction. -/
def mapInstrExprs (f : PExpr → PExpr) : InstrR → InstrR
  | .Cassgn lv tag ty e => .Cassgn lv tag ty (f e)
  | .Copn lvs tag op es => .Copn lvs tag op (es.map f)
  | .Cif cond th el =>
    .Cif (f cond) (th.map (mapInstrExprs f)) (el.map (mapInstrExprs f))
  | .Cfor v range body =>
    .Cfor v range (body.map (mapInstrExprs f))
  | .Cwhile cb cond ca =>
    .Cwhile (cb.map (mapInstrExprs f)) (f cond) (ca.map (mapInstrExprs f))
  | .Ccall ii lvs fn args =>
    .Ccall ii lvs fn (args.map f)

/-- Apply an expression transform to all sub-expressions in a command. -/
def mapCmdExprs (f : PExpr → PExpr) (cmd : Cmd) : Cmd :=
  cmd.map (mapInstrExprs f)

/-! ## Fuel Bounds

Minimum fuel needed for `translateCmd`/`translateInstrR` to fully execute
without hitting the fuel=0 fail case in any nested command. -/

/-- Minimum fuel for `translateInstrR` (accounts for nested `translateCmd` calls). -/
def fuelBoundInstr : InstrR → Nat
  | .Cif _ t e => max (fuelBoundList t) (fuelBoundList e)
  | .Cfor _ _ body => fuelBoundList body
  | _ => 0  -- Cassgn, Copn, Cwhile, Ccall: no recursive translateCmd calls
where
  /-- Minimum fuel for `translateCmd` on an instruction list. -/
  fuelBoundList : List InstrR → Nat
    | [] => 1
    | i :: is => 1 + max (fuelBoundInstr i) (fuelBoundList is)

/-- Minimum fuel for `translateCmd`. -/
def fuelBoundCmd (cmd : Cmd) : Nat := fuelBoundInstr.fuelBoundList cmd

theorem fuelBoundInstr_fuelBoundList (cmd : Cmd) :
    fuelBoundInstr.fuelBoundList cmd = fuelBoundCmd cmd := rfl
@[simp] theorem fuelBoundCmd_nil : fuelBoundCmd ([] : Cmd) = 1 := rfl
@[simp] theorem fuelBoundCmd_cons (i : InstrR) (is : Cmd) :
    fuelBoundCmd (i :: is) = 1 + max (fuelBoundInstr i) (fuelBoundCmd is) := rfl

theorem fuelBoundCmd_pos (cmd : Cmd) : fuelBoundCmd cmd ≥ 1 := by
  cases cmd with
  | nil => exact le_refl _
  | cons _ _ => simp [fuelBoundCmd]; exact Nat.le_add_right 1 _

noncomputable section

/-! ## Lifting Lemmas -/

/-- If `pass` preserves expression eval, then `translatePExprAll` with
    mapped expressions has the same eval. -/
theorem translatePExprAll_map (pass : PExpr → PExpr)
    (h : ExprPassCorrect pass) (sid : ScopeId) :
    ∀ es, (translatePExprAll sid (es.map pass)).eval =
          (translatePExprAll sid es).eval := by
  intro es
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map, translatePExprAll, eval_bind, eval_ret, h sid e, ih]

/-! ### Expression pass lifting — proved by joint fuel induction

The proof uses induction on fuel, proving cmd-level and instr-level correctness
simultaneously. At each fuel level:
- cmd correctness at fuel n+1 follows from instr + cmd correctness at fuel n
- instr correctness at fuel n+1 follows from cmd correctness at fuel n+1
  (because `translateInstrR` calls `translateCmd` at the same fuel)

The `translateForLoop` case requires an auxiliary induction on the index list. -/

/-- Auxiliary: `translateForLoop` preserves eval under expression mapping,
    given that `translateCmd` preserves eval at the same fuel level. -/
private theorem translateForLoop_map_eval (pass : PExpr → PExpr)
    (h : ExprPassCorrect pass) (fuel : Nat)
    (hcmd_eval : ∀ env cmd sid,
      (translateCmd env (cmd.map (mapInstrExprs pass)) sid fuel).code.eval =
      (translateCmd env cmd sid fuel).code.eval) :
    ∀ env sid v indices body,
      (translateForLoop env sid v indices (body.map (mapInstrExprs pass)) fuel).eval =
      (translateForLoop env sid v indices body fuel).eval := by
  intro env sid v indices body
  induction indices with
  | nil => simp only [translateForLoop.eq_def]
  | cons i rest ih =>
    conv_lhs => rw [translateForLoop.eq_def]
    conv_rhs => rw [translateForLoop.eq_def]
    simp only [eval_bind, hcmd_eval, ih]

/-- One-step unfolding of `translateCmd` at cons: eval becomes a bind. -/
theorem translateCmd_cons_eval (env : TransEnv) (i : InstrR) (is : Cmd)
    (sid : ScopeId) (n : Nat) :
    (translateCmd env (i :: is) sid (n + 1)).code.eval =
    SPComp.bind (translateInstrR env sid n i).code.eval
    (fun _ => (translateCmd env is (translateInstrR env sid n i).newSid n).code.eval) := by
  rw [translateCmd.eq_def]; dsimp only; simp only [eval_bind]

/-- One-step unfolding of `translateCmd` at cons: newSid propagates through. -/
theorem translateCmd_cons_newSid (env : TransEnv) (i : InstrR) (is : Cmd)
    (sid : ScopeId) (n : Nat) :
    (translateCmd env (i :: is) sid (n + 1)).newSid =
    (translateCmd env is (translateInstrR env sid n i).newSid n).newSid := by
  rw [translateCmd.eq_def]

/-- Joint fuel induction: an expression pass lifts to both cmd and instr levels.
    Returns `(cmd_correct ∧ cmd_newSid, instr_correct ∧ instr_newSid)`. -/
private theorem exprPass_lifting_joint (pass : PExpr → PExpr) (h : ExprPassCorrect pass) :
    ∀ fuel,
      (∀ env cmd sid,
        (translateCmd env (cmd.map (mapInstrExprs pass)) sid fuel).code.eval =
        (translateCmd env cmd sid fuel).code.eval ∧
        (translateCmd env (cmd.map (mapInstrExprs pass)) sid fuel).newSid =
        (translateCmd env cmd sid fuel).newSid) ∧
      (∀ env sid i,
        (translateInstrR env sid fuel (mapInstrExprs pass i)).code.eval =
        (translateInstrR env sid fuel i).code.eval ∧
        (translateInstrR env sid fuel (mapInstrExprs pass i)).newSid =
        (translateInstrR env sid fuel i).newSid) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · -- CmdLifts 0: translateCmd at fuel 0 always returns { sid, .fail }
      intro env cmd sid
      simp only [translateCmd.eq_def]
      exact ⟨trivial, trivial⟩
    · -- InstrLifts 0
      intro env sid i
      cases i with
      | Cassgn lv tag ty e =>
        simp only [mapInstrExprs, translateInstrR.eq_def, eval_bind, h sid e]
        exact ⟨trivial, trivial⟩
      | Copn lvs tag op es =>
        simp only [mapInstrExprs, translateInstrR.eq_def, eval_bind,
                   translatePExprAll_map pass h sid]
        exact ⟨trivial, trivial⟩
      | Cif cond th el =>
        simp only [mapInstrExprs, translateInstrR.eq_def, translateCmd.eq_def,
                   eval_bind, h sid cond]
        exact ⟨trivial, trivial⟩
      | Cfor v range body =>
        simp only [mapInstrExprs, translateInstrR.eq_def]
        exact ⟨translateForLoop_map_eval pass h 0
          (fun env cmd sid => by simp [translateCmd.eq_def]) env sid v.var
          (loopRange range) body, trivial⟩
      | Cwhile cb cond ca =>
        simp only [mapInstrExprs, translateInstrR.eq_def]
        exact ⟨trivial, trivial⟩
      | Ccall ii lvs fn args =>
        simp only [mapInstrExprs, translateInstrR.eq_def, eval_bind,
                   translatePExprAll_map pass h sid]
        exact ⟨trivial, trivial⟩
  | succ n ih =>
    obtain ⟨ih_cmd, ih_instr⟩ := ih
    -- Step 1: cmd correctness at n+1 (from instr + cmd at n)
    have cmd_succ : ∀ env cmd sid,
        (translateCmd env (cmd.map (mapInstrExprs pass)) sid (n + 1)).code.eval =
        (translateCmd env cmd sid (n + 1)).code.eval ∧
        (translateCmd env (cmd.map (mapInstrExprs pass)) sid (n + 1)).newSid =
        (translateCmd env cmd sid (n + 1)).newSid := by
      intro env cmd sid
      cases cmd with
      | nil =>
        simp only [List.map_nil, translateCmd.eq_def]
        exact ⟨trivial, trivial⟩
      | cons i is =>
        simp only [List.map_cons]
        obtain ⟨hi_eval, hi_sid⟩ := ih_instr env sid i
        constructor
        · rw [translateCmd_cons_eval, translateCmd_cons_eval, hi_sid, hi_eval]
          congr 1; funext _
          exact (ih_cmd env is (translateInstrR env sid n i).newSid).1
        · rw [translateCmd_cons_newSid, translateCmd_cons_newSid, hi_sid]
          exact (ih_cmd env is (translateInstrR env sid n i).newSid).2
    -- Step 2: instr correctness at n+1 (from cmd at n+1)
    refine ⟨cmd_succ, fun env sid i => ?_⟩
    cases i with
    | Cassgn lv tag ty e =>
      simp only [mapInstrExprs, translateInstrR.eq_def, eval_bind, h sid e]
      exact ⟨trivial, trivial⟩
    | Copn lvs tag op es =>
      simp only [mapInstrExprs, translateInstrR.eq_def, eval_bind,
                 translatePExprAll_map pass h sid]
      exact ⟨trivial, trivial⟩
    | Cif cond th el =>
      simp only [mapInstrExprs, translateInstrR.eq_def]
      obtain ⟨h_then_eval, h_then_sid⟩ := cmd_succ env th sid
      rw [h_then_sid]
      obtain ⟨h_else_eval, h_else_sid⟩ :=
        cmd_succ env el (translateCmd env th sid (n + 1)).newSid
      refine ⟨?_, h_else_sid⟩
      simp only [eval_bind, h sid cond]
      congr 1; funext ⟨ty, val⟩
      cases ty with
      | sbool => cases val <;> simp only [h_then_eval, h_else_eval]
      | sint => exact h_then_eval
      | sarr => exact h_then_eval
      | sword => exact h_then_eval
    | Cfor v range body =>
      simp only [mapInstrExprs, translateInstrR.eq_def]
      exact ⟨translateForLoop_map_eval pass h (n + 1)
        (fun env cmd sid => (cmd_succ env cmd sid).1) env sid v.var
        (loopRange range) body, trivial⟩
    | Cwhile cb cond ca =>
      simp only [mapInstrExprs, translateInstrR.eq_def]
      exact ⟨trivial, trivial⟩
    | Ccall ii lvs fn args =>
      simp only [mapInstrExprs, translateInstrR.eq_def, eval_bind,
                 translatePExprAll_map pass h sid]
      exact ⟨trivial, trivial⟩

/-- An expression pass lifts to instruction-level correctness.
    Proved by joint fuel induction with `exprPass_lifts_to_cmd`. -/
theorem exprPass_lifts_to_instr (pass : PExpr → PExpr) (h : ExprPassCorrect pass) :
    ∀ env sid fuel i,
      (translateInstrR env sid fuel (mapInstrExprs pass i)).code.eval =
      (translateInstrR env sid fuel i).code.eval :=
  fun env sid fuel i => ((exprPass_lifting_joint pass h fuel).2 env sid i).1

/-- An expression pass lifts to command-level correctness.
    Proved by joint fuel induction with `exprPass_lifts_to_instr`. -/
theorem exprPass_lifts_to_cmd (pass : PExpr → PExpr) (h : ExprPassCorrect pass) :
    CmdPassCorrect (mapCmdExprs pass) := by
  intro env sid fuel cmd
  exact ((exprPass_lifting_joint pass h fuel).1 env cmd sid).1

/-! ## Fuel Monotonicity

When fuel exceeds `fuelBoundCmd`, the result of `translateCmd` is stable:
increasing fuel by 1 does not change `.code.eval` or `.newSid`.

The proof follows the same joint fuel induction as the expression pass lifting:
1. cmd_step(n+1) from P(n)
2. instr_step(n+1) from cmd_step(n+1) -/

/-- Auxiliary: `translateForLoop` is stable under fuel increase. -/
private theorem translateForLoop_fuel_step (fuel : Nat)
    (hcmd : ∀ env cmd sid, fuelBoundCmd cmd ≤ fuel →
      (translateCmd env cmd sid (fuel + 1)).code.eval =
      (translateCmd env cmd sid fuel).code.eval ∧
      (translateCmd env cmd sid (fuel + 1)).newSid =
      (translateCmd env cmd sid fuel).newSid) :
    ∀ env sid v indices body,
      fuelBoundCmd body ≤ fuel →
      (translateForLoop env sid v indices body (fuel + 1)).eval =
      (translateForLoop env sid v indices body fuel).eval := by
  intro env sid v indices body hbound
  induction indices with
  | nil => simp only [translateForLoop.eq_def]
  | cons i rest ih =>
    conv_lhs => rw [translateForLoop.eq_def]
    conv_rhs => rw [translateForLoop.eq_def]
    obtain ⟨heval, hsid⟩ := hcmd env body sid hbound
    simp only [eval_bind, heval, ih]

/-- Joint fuel step: `translateCmd` and `translateInstrR` are unchanged when
    fuel increases beyond `fuelBound`. -/
private theorem fuel_step_joint :
    ∀ fuel,
      (∀ env cmd sid, fuelBoundCmd cmd ≤ fuel →
        (translateCmd env cmd sid (fuel + 1)).code.eval =
        (translateCmd env cmd sid fuel).code.eval ∧
        (translateCmd env cmd sid (fuel + 1)).newSid =
        (translateCmd env cmd sid fuel).newSid) ∧
      (∀ env sid i, fuelBoundInstr i ≤ fuel →
        (translateInstrR env sid (fuel + 1) i).code.eval =
        (translateInstrR env sid fuel i).code.eval ∧
        (translateInstrR env sid (fuel + 1) i).newSid =
        (translateInstrR env sid fuel i).newSid) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · -- cmd: fuelBoundCmd cmd ≤ 0, impossible since fuelBoundCmd ≥ 1
      intro env cmd sid h
      exact absurd (fuelBoundCmd_pos cmd) (by omega)
    · -- instr at fuel 0: only cases with fuelBoundInstr = 0
      intro env sid i h
      cases i with
      | Cassgn => simp only [translateInstrR.eq_def]; exact ⟨trivial, trivial⟩
      | Copn => simp only [translateInstrR.eq_def]; exact ⟨trivial, trivial⟩
      | Cif _ th el =>
        have := fuelBoundCmd_pos th
        simp only [fuelBoundInstr, fuelBoundInstr_fuelBoundList] at h
        exact absurd (le_trans (Nat.le_max_left ..) h) (by omega)
      | Cfor _ _ body =>
        have := fuelBoundCmd_pos body
        simp only [fuelBoundInstr, fuelBoundInstr_fuelBoundList] at h
        exact absurd h (by omega)
      | Cwhile => simp only [translateInstrR.eq_def]; exact ⟨trivial, trivial⟩
      | Ccall => simp only [translateInstrR.eq_def]; exact ⟨trivial, trivial⟩
  | succ n ih =>
    obtain ⟨ih_cmd, ih_instr⟩ := ih
    -- Step 1: cmd_step(n+1) from P(n)
    have cmd_step : ∀ env cmd sid, fuelBoundCmd cmd ≤ n + 1 →
        (translateCmd env cmd sid (n + 2)).code.eval =
        (translateCmd env cmd sid (n + 1)).code.eval ∧
        (translateCmd env cmd sid (n + 2)).newSid =
        (translateCmd env cmd sid (n + 1)).newSid := by
      intro env cmd sid hbound
      cases cmd with
      | nil =>
        simp only [translateCmd.eq_def]
        exact ⟨trivial, trivial⟩
      | cons i is =>
        have hi_bound : fuelBoundInstr i ≤ n := by
          have := Nat.le_max_left (fuelBoundInstr i) (fuelBoundCmd is)
          simp only [fuelBoundCmd_cons] at hbound; linarith
        have his_bound : fuelBoundCmd is ≤ n := by
          have := Nat.le_max_right (fuelBoundInstr i) (fuelBoundCmd is)
          simp only [fuelBoundCmd_cons] at hbound; linarith
        obtain ⟨hi_eval, hi_sid⟩ := ih_instr env sid i hi_bound
        constructor
        · rw [translateCmd_cons_eval, translateCmd_cons_eval, hi_sid, hi_eval]
          congr 1; funext _
          exact (ih_cmd env is (translateInstrR env sid n i).newSid his_bound).1
        · rw [translateCmd_cons_newSid, translateCmd_cons_newSid, hi_sid]
          exact (ih_cmd env is (translateInstrR env sid n i).newSid his_bound).2
    -- Step 2: instr_step(n+1) from cmd_step(n+1)
    refine ⟨cmd_step, fun env sid i h => ?_⟩
    cases i with
    | Cassgn => simp only [translateInstrR.eq_def]; exact ⟨trivial, trivial⟩
    | Copn => simp only [translateInstrR.eq_def]; exact ⟨trivial, trivial⟩
    | Cif cond th el =>
      simp only [translateInstrR.eq_def]
      have hth : fuelBoundCmd th ≤ n + 1 := by
        have := Nat.le_max_left (fuelBoundCmd th) (fuelBoundCmd el)
        simp only [fuelBoundInstr, fuelBoundInstr_fuelBoundList] at h; linarith
      have hel : fuelBoundCmd el ≤ n + 1 := by
        have := Nat.le_max_right (fuelBoundCmd th) (fuelBoundCmd el)
        simp only [fuelBoundInstr, fuelBoundInstr_fuelBoundList] at h; linarith
      obtain ⟨h_then_eval, h_then_sid⟩ := cmd_step env th sid hth
      rw [h_then_sid]
      obtain ⟨h_else_eval, h_else_sid⟩ :=
        cmd_step env el (translateCmd env th sid (n + 1)).newSid hel
      refine ⟨?_, h_else_sid⟩
      simp only [eval_bind]
      congr 1; funext ⟨ty, val⟩
      cases ty with
      | sbool => cases val <;> simp only [h_then_eval, h_else_eval]
      | sint => exact h_then_eval
      | sarr => exact h_then_eval
      | sword => exact h_then_eval
    | Cfor v range body =>
      simp only [translateInstrR.eq_def]
      have hbody : fuelBoundCmd body ≤ n + 1 := by
        simp only [fuelBoundInstr, fuelBoundInstr_fuelBoundList] at h; exact h
      exact ⟨translateForLoop_fuel_step (n + 1)
        (fun env cmd sid hb => cmd_step env cmd sid hb) env sid v.var
        (loopRange range) body hbody, trivial⟩
    | Cwhile => simp only [translateInstrR.eq_def]; exact ⟨trivial, trivial⟩
    | Ccall => simp only [translateInstrR.eq_def]; exact ⟨trivial, trivial⟩

/-- `translateCmd` is stable when fuel increases beyond `fuelBoundCmd`. -/
theorem translateCmd_fuel_step (env : TransEnv) (cmd : Cmd) (sid : ScopeId)
    (fuel : Nat) (h : fuel ≥ fuelBoundCmd cmd) :
    (translateCmd env cmd sid (fuel + 1)).code.eval =
    (translateCmd env cmd sid fuel).code.eval :=
  ((fuel_step_joint fuel).1 env cmd sid h).1

/-- `translateCmd` newSid is stable when fuel increases beyond `fuelBoundCmd`. -/
theorem translateCmd_fuel_step_newSid (env : TransEnv) (cmd : Cmd) (sid : ScopeId)
    (fuel : Nat) (h : fuel ≥ fuelBoundCmd cmd) :
    (translateCmd env cmd sid (fuel + 1)).newSid =
    (translateCmd env cmd sid fuel).newSid :=
  ((fuel_step_joint fuel).1 env cmd sid h).2

end

end CatCrypt.Crypto.Jasmin
