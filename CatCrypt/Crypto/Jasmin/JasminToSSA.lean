/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CryptoSSA
import CatCrypt.Crypto.Jasmin.JasminAST

/-!
# General Jasmin → CryptoSSA Translation with Correctness Proof

Constructive translation from SSA-compatible Jasmin commands to CryptoSSA
programs, with a proved correctness theorem that the CryptoSSA denotation
computes the same function as the Jasmin assignments.

## Architecture

```
Jasmin SSA commands (sequence of x := op(a, b))
  → translateMonoCmd → CProg Γ (.sword n)
  → CProg.denote V = SPComp.pure (pureEvalMonoCmd env retVar cmd)
```

## Supported Fragment

- **Assignments**: `x := op(a, b)` for binary word ops (xor, and, or, add, sub, mul)
- **Assignments**: `x := op(a)` for unary word ops (not)
- **Shifts**: `x := a << k`, `x := a >> k` for constant shift amounts
- **Copies**: `x := y` (alias in VarMap, no let-binding)
- **Constants**: `x := c` (bvConst)
- **Return**: look up the return variable

## Key Theorem

`translateMonoCmd_correct`: For SSA-compatible commands with `BitVec n` variables,
the CryptoSSA translation computes the same function as the pure evaluation.

**0 axioms**, **0 sorries**.
-/

namespace CatCrypt.Crypto.Jasmin.ToSSA

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open scoped ENNReal

set_option autoImplicit false

noncomputable section

/-! ## Section 1: Monomorphic Variable Maps -/

/-- Monomorphic variable map: maps Jasmin `Var` to CryptoSSA De Bruijn indices. -/
def MonoVarMap (Γ : Ctx) (n : Nat) := Var → Option (CVar Γ (.sword n))

def MonoVarMap.empty {n : Nat} : MonoVarMap ([] : Ctx) n := fun _ => none

/-- Extend with a new binding at `.here`; shift existing bindings. -/
def MonoVarMap.extend {Γ : Ctx} {n : Nat} (m : MonoVarMap Γ n) (v : Var) :
    MonoVarMap (CryptoTy.sword n :: Γ) n :=
  fun w => if w = v then some .here else (m w).map .there

/-! ## Section 2: Agreement Relation -/

/-- The simulation invariant: tracked variable values agree. -/
def monoAgrees {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) (V : HVec Γ) (env : Var → BitVec n) : Prop :=
  ∀ (v : Var) (cv : CVar Γ (.sword n)),
    m v = some cv → cv.lookup V = env v

/-- Agreement is preserved when extending with a new variable. -/
theorem monoAgrees_extend {Γ : Ctx} {n : Nat}
    {m : MonoVarMap Γ n} {V : HVec Γ} {env : Var → BitVec n}
    (h : monoAgrees m V env) (v : Var) (val : BitVec n) :
    monoAgrees (m.extend v) (HVec.cons val V)
      (fun w => if w = v then val else env w) := by
  intro w cv h_lookup
  simp only [MonoVarMap.extend] at h_lookup
  split at h_lookup
  · rename_i h_eq; subst h_eq
    cases h_lookup; simp [CVar.lookup]
  · rename_i h_neq
    simp only [Option.map] at h_lookup
    split at h_lookup
    · rename_i cv' h_eq; cases h_lookup
      simp [CVar.lookup, h_neq, h w cv' h_eq]
    · exact absurd h_lookup (by simp)

/-! ## Section 3: Pure Evaluation (Reference Semantics) -/

/-- Pure evaluation of a Jasmin expression in the word fragment. -/
def pureEvalMonoExpr (n : Nat) (env : Var → BitVec n) : PExpr → BitVec n
  | .Pvar gv => env gv.gv.var
  | .Pconst z => BitVec.ofInt n z
  | .Papp2 (.Olxor _) (.Pvar x) (.Pvar y) => env x.gv.var ^^^ env y.gv.var
  | .Papp2 (.Oland _) (.Pvar x) (.Pvar y) => env x.gv.var &&& env y.gv.var
  | .Papp2 (.Olor _) (.Pvar x) (.Pvar y) => env x.gv.var ||| env y.gv.var
  | .Papp2 (.Oadd _) (.Pvar x) (.Pvar y) => env x.gv.var + env y.gv.var
  | .Papp2 (.Osub _) (.Pvar x) (.Pvar y) => env x.gv.var - env y.gv.var
  | .Papp2 (.Omul _) (.Pvar x) (.Pvar y) => env x.gv.var * env y.gv.var
  | .Papp1 (.Olnot _) (.Pvar x) => ~~~(env x.gv.var)
  | .Papp2 (.Olsl _) (.Pvar x) (.Pconst k) => env x.gv.var <<< k.toNat
  | .Papp2 (.Olsr _) (.Pvar x) (.Pconst k) => BitVec.ushiftRight (env x.gv.var) k.toNat
  | _ => 0

/-- Pure evaluation of an SSA-compatible command sequence. -/
def pureEvalMonoCmd (n : Nat) (env : Var → BitVec n) (retVar : Var) :
    List InstrR → BitVec n
  | [] => env retVar
  | .Cassgn (.Lvar x) _ _ e :: rest =>
    pureEvalMonoCmd n
      (fun w => if w = x.var then pureEvalMonoExpr n env e else env w)
      retVar rest
  | _ :: rest => pureEvalMonoCmd n env retVar rest

/-! ## Section 4: Expression Translation -/

/-- Translate a binary op on two variables to a CExpr. -/
def translateBinOp {Γ : Ctx} {n : Nat}
    (cvx cvy : CVar Γ (.sword n)) : SOp2 → Option (CExpr Γ (.sword n))
  | .Olxor _ => some (.bvXor cvx cvy)
  | .Oland _ => some (.bvAnd cvx cvy)
  | .Olor _ => some (.bvOr cvx cvy)
  | .Oadd _ => some (.bvAdd cvx cvy)
  | .Osub _ => some (.bvSub cvx cvy)
  | .Omul _ => some (.bvMul cvx cvy)
  | _ => none

/-- Translate a Jasmin expression to a CryptoSSA `CExpr`. -/
def translateMonoExpr {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) : PExpr → Option (CExpr Γ (.sword n))
  | .Pconst z => some (.bvConst (BitVec.ofInt n z))
  | .Papp2 op (.Pvar x) (.Pvar y) =>
    match m x.gv.var, m y.gv.var with
    | some cvx, some cvy => translateBinOp cvx cvy op
    | _, _ => none
  | .Papp1 (.Olnot _) (.Pvar x) =>
    match m x.gv.var with
    | some cvx => some (.bvNot cvx)
    | none => none
  | .Papp2 (.Olsl _) (.Pvar x) (.Pconst k) =>
    match m x.gv.var with
    | some cvx => some (.bvShiftL cvx k.toNat)
    | none => none
  | .Papp2 (.Olsr _) (.Pvar x) (.Pconst k) =>
    match m x.gv.var with
    | some cvx => some (.bvShiftR cvx k.toNat)
    | none => none
  | _ => none

/-! ## Section 5: Command Translation -/

/-- Translate SSA-compatible Jasmin commands to CryptoSSA.

    Uses two-level matching: first on list structure, then on instruction. -/
def translateMonoCmd {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) (retVar : Var) :
    List InstrR → Option (CProg Γ (.sword n))
  | [] =>
    match m retVar with
    | some cv => some (.ret cv)
    | none => none
  | .Cassgn (.Lvar x) _ _ (.Pvar gv) :: rest =>
    match m gv.gv.var with
    | some cv =>
      translateMonoCmd (fun w => if w = x.var then some cv else m w) retVar rest
    | none => none
  | .Cassgn (.Lvar x) _ _ e :: rest =>
    match translateMonoExpr m e with
    | some cexpr =>
      match translateMonoCmd (m.extend x.var) retVar rest with
      | some body => some (.letBind cexpr body)
      | none => none
    | none => none
  | _ :: _ => none

/-! ## Section 6: Expression Correctness -/

private theorem translateBinOp_correct {Γ : Ctx} {n : Nat}
    {cvx cvy : CVar Γ (.sword n)} {V : HVec Γ} {op : SOp2}
    {cexpr : CExpr Γ (.sword n)}
    (h_trans : translateBinOp cvx cvy op = some cexpr)
    (vx vy : BitVec n)
    (hx : cvx.lookup V = vx) (hy : cvy.lookup V = vy) :
    cexpr.denote V = SPComp.pure (
      match op with
      | .Olxor _ => vx ^^^ vy
      | .Oland _ => vx &&& vy
      | .Olor _ => vx ||| vy
      | .Oadd _ => vx + vy
      | .Osub _ => vx - vy
      | .Omul _ => vx * vy
      | _ => 0) := by
  cases op <;> simp [translateBinOp] at h_trans
  all_goals (subst h_trans; simp [CExpr.denote, hx, hy])

theorem translateMonoExpr_correct {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) (V : HVec Γ) (env : Var → BitVec n)
    (h_agrees : monoAgrees m V env) (e : PExpr) (cexpr : CExpr Γ (.sword n))
    (h_trans : translateMonoExpr m e = some cexpr) :
    cexpr.denote V = SPComp.pure (pureEvalMonoExpr n env e) := by
  cases e with
  | Pconst z =>
    simp [translateMonoExpr] at h_trans; subst h_trans
    simp [CExpr.denote, pureEvalMonoExpr]
  | Papp2 op e1 e2 =>
    cases e1 with
    | Pvar x =>
      cases e2 with
      | Pvar y =>
        simp only [translateMonoExpr] at h_trans
        match h_mx : m x.gv.var with
        | some cvx =>
          match h_my : m y.gv.var with
          | some cvy =>
            simp [h_mx, h_my] at h_trans
            have h_bin := translateBinOp_correct h_trans
              (env x.gv.var) (env y.gv.var)
              (h_agrees x.gv.var cvx h_mx) (h_agrees y.gv.var cvy h_my)
            rw [h_bin]; congr 1
            simp [pureEvalMonoExpr]
            cases op <;> rfl
          | none => simp [h_mx, h_my] at h_trans
        | none => simp [h_mx] at h_trans
      | Pconst k =>
        cases op with
        | Olsl ws =>
          simp only [translateMonoExpr] at h_trans
          match h_mx : m x.gv.var with
          | some cvx =>
            simp [h_mx] at h_trans; subst h_trans
            simp [CExpr.denote, pureEvalMonoExpr, h_agrees x.gv.var cvx h_mx]
          | none => simp [h_mx] at h_trans
        | Olsr ws =>
          simp only [translateMonoExpr] at h_trans
          match h_mx : m x.gv.var with
          | some cvx =>
            simp [h_mx] at h_trans; subst h_trans
            simp [CExpr.denote, pureEvalMonoExpr, h_agrees x.gv.var cvx h_mx]
          | none => simp [h_mx] at h_trans
        | _ => simp [translateMonoExpr] at h_trans
      | _ => simp [translateMonoExpr] at h_trans
    | _ => simp [translateMonoExpr] at h_trans
  | Papp1 op arg =>
    cases op with
    | Olnot ws =>
      cases arg with
      | Pvar x =>
        simp only [translateMonoExpr] at h_trans
        match h_mx : m x.gv.var with
        | some cvx =>
          simp [h_mx] at h_trans; subst h_trans
          simp [CExpr.denote, pureEvalMonoExpr, h_agrees x.gv.var cvx h_mx]
        | none => simp [h_mx] at h_trans
      | _ => simp [translateMonoExpr] at h_trans
    | _ => simp [translateMonoExpr] at h_trans
  | _ => simp [translateMonoExpr] at h_trans

/-! ## Section 7: Command Correctness -/

/-- Helper: `translateMonoCmd` returns `none` for unsupported instructions. -/
private theorem translateMonoCmd_unsupported {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) (retVar : Var) (instr : InstrR) (rest : List InstrR)
    (h : ∀ lv tag ty e, instr ≠ .Cassgn lv tag ty e) :
    translateMonoCmd m retVar (instr :: rest) = none := by
  cases instr with
  | Cassgn lv tag ty e => exact absurd rfl (h lv tag ty e)
  | Copn _ _ _ _ => rfl
  | Cif _ _ _ => rfl
  | Cfor _ _ _ => rfl
  | Cwhile _ _ _ => rfl
  | Ccall _ _ _ _ => rfl

/-- **Command translation correctness**: The CryptoSSA denotation of the
    translated program equals `SPComp.pure` of the pure evaluation. -/
theorem translateMonoCmd_correct {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) (V : HVec Γ) (env : Var → BitVec n)
    (retVar : Var) (cmd : List InstrR) (prog : CProg Γ (.sword n))
    (h_agrees : monoAgrees m V env)
    (h_trans : translateMonoCmd m retVar cmd = some prog) :
    prog.denote V = SPComp.pure (pureEvalMonoCmd n env retVar cmd) := by
  induction cmd generalizing Γ m V env prog with
  | nil =>
    simp only [translateMonoCmd] at h_trans
    split at h_trans
    · rename_i cv h_ret; cases h_trans
      simp [CProg.denote, pureEvalMonoCmd, h_agrees retVar cv h_ret]
    · exact absurd h_trans (by simp)
  | cons instr rest ih =>
    cases instr with
    | Cassgn lv tag ty e =>
      cases lv with
      | Lvar x =>
        cases e with
        | Pvar gv =>
          -- Copy case
          simp only [translateMonoCmd] at h_trans
          split at h_trans
          · rename_i cv h_src
            have h_agrees' : monoAgrees
                (fun w => if w = x.var then some cv else m w) V
                (fun w => if w = x.var then env gv.gv.var else env w) := by
              intro w cv' h_lookup
              by_cases hw : w = x.var
              · subst hw; simp at h_lookup ⊢; cases h_lookup
                exact h_agrees gv.gv.var cv h_src
              · simp [hw] at h_lookup ⊢
                exact h_agrees w cv' h_lookup
            simp only [pureEvalMonoCmd, pureEvalMonoExpr]
            exact ih _ V _ _ h_agrees' h_trans
          · exact absurd h_trans (by simp)
        | _ =>
          -- Operation/constant case
          simp only [translateMonoCmd] at h_trans
          split at h_trans
          · rename_i cexpr h_expr
            split at h_trans
            · rename_i body h_body; cases h_trans
              simp only [CProg.denote]
              have h_ec := translateMonoExpr_correct m V env h_agrees _ cexpr h_expr
              rw [h_ec, SPComp.pure_bind]
              simp only [pureEvalMonoCmd, pureEvalMonoExpr]
              exact ih _ (.cons _ V) _ _ (monoAgrees_extend h_agrees x.var _) h_body
            · exact absurd h_trans (by simp)
          · exact absurd h_trans (by simp)
      | Lnone _ _ | Lmem _ _ _ | Laset _ _ _ _ | Lasub _ _ _ _ _ =>
        simp [translateMonoCmd] at h_trans
    | Copn _ _ _ _ | Cif _ _ _ | Cfor _ _ _ | Cwhile _ _ _ | Ccall _ _ _ _ =>
      simp [translateMonoCmd] at h_trans

/-! ## Section 8: Function-Level Wrappers -/

def translateMonoFun (inputVar retVar : Var) (n : Nat) (body : List InstrR) :
    Option (CProg [.sword n] (.sword n)) :=
  translateMonoCmd (MonoVarMap.extend MonoVarMap.empty inputVar) retVar body

def translateMonoFun2 (input1 input2 retVar : Var) (n : Nat) (body : List InstrR) :
    Option (CProg [.sword n, .sword n] (.sword n)) :=
  let m0 : MonoVarMap [.sword n] n := MonoVarMap.extend MonoVarMap.empty input2
  let m1 : MonoVarMap [.sword n, .sword n] n := m0.extend input1
  translateMonoCmd m1 retVar body

/-! ## Section 9: Function-Level Correctness -/

theorem translateMonoFun_correct (inputVar retVar : Var) (n : Nat)
    (body : List InstrR) (prog : CProg [.sword n] (.sword n))
    (h_trans : translateMonoFun inputVar retVar n body = some prog) :
    ∀ (a : BitVec n),
    prog.denote (.cons a .nil) =
    SPComp.pure (pureEvalMonoCmd n
      (fun w => if w = inputVar then a else 0)
      retVar body) := by
  intro a
  refine translateMonoCmd_correct _ (.cons a .nil)
    (fun w => if w = inputVar then a else 0) retVar body prog ?_ h_trans
  intro v cv h_lookup
  simp only [MonoVarMap.extend, MonoVarMap.empty] at h_lookup
  split at h_lookup
  · rename_i h_eq; simp at h_lookup; cases h_lookup; simp [CVar.lookup, h_eq]
  · simp at h_lookup

theorem translateMonoFun2_correct (input1 input2 retVar : Var) (n : Nat)
    (body : List InstrR) (prog : CProg [.sword n, .sword n] (.sword n))
    (h_ne : input1 ≠ input2)
    (h_trans : translateMonoFun2 input1 input2 retVar n body = some prog) :
    ∀ (a b : BitVec n),
    prog.denote (.cons a (.cons b .nil)) =
    SPComp.pure (pureEvalMonoCmd n
      (fun w => if w = input1 then a else if w = input2 then b else 0)
      retVar body) := by
  intro a b
  refine translateMonoCmd_correct _ (.cons a (.cons b .nil))
    (fun w => if w = input1 then a else if w = input2 then b else 0)
    retVar body prog ?_ h_trans
  intro v cv h_lookup
  simp only [MonoVarMap.extend, MonoVarMap.empty] at h_lookup
  split at h_lookup
  · rename_i h_eq; simp at h_lookup; cases h_lookup; simp [CVar.lookup, h_eq]
  · rename_i h_ne1
    simp only [Option.map] at h_lookup
    split at h_lookup
    · rename_i cv' h_inner; cases h_lookup
      split at h_inner
      · rename_i h_eq2; simp at h_inner; cases h_inner
        simp [CVar.lookup, h_eq2, (Ne.symm h_ne : input2 ≠ input1)]
      · simp at h_inner
    · exact absurd h_lookup (by simp)

def translateMonoFun4 (i1 i2 i3 i4 retVar : Var) (n : Nat) (body : List InstrR) :
    Option (CProg [.sword n, .sword n, .sword n, .sword n] (.sword n)) :=
  let m0 : MonoVarMap [.sword n] n := MonoVarMap.extend MonoVarMap.empty i4
  let m1 : MonoVarMap [.sword n, .sword n] n := m0.extend i3
  let m2 : MonoVarMap [.sword n, .sword n, .sword n] n := m1.extend i2
  let m3 : MonoVarMap [.sword n, .sword n, .sword n, .sword n] n := m2.extend i1
  translateMonoCmd m3 retVar body

theorem translateMonoFun4_correct (i1 i2 i3 i4 retVar : Var) (n : Nat)
    (h_ne12 : i1 ≠ i2) (h_ne13 : i1 ≠ i3) (h_ne14 : i1 ≠ i4)
    (h_ne23 : i2 ≠ i3) (h_ne24 : i2 ≠ i4) (h_ne34 : i3 ≠ i4)
    (body : List InstrR) (prog : CProg [.sword n, .sword n, .sword n, .sword n] (.sword n))
    (h_trans : translateMonoFun4 i1 i2 i3 i4 retVar n body = some prog) :
    ∀ (a b c d : BitVec n),
    prog.denote (.cons a (.cons b (.cons c (.cons d .nil)))) =
    SPComp.pure (pureEvalMonoCmd n
      (fun w => if w = i1 then a else if w = i2 then b
                else if w = i3 then c else if w = i4 then d else 0)
      retVar body) := by
  intro a b c d
  refine translateMonoCmd_correct _ (.cons a (.cons b (.cons c (.cons d .nil))))
    (fun w => if w = i1 then a else if w = i2 then b
              else if w = i3 then c else if w = i4 then d else 0)
    retVar body prog ?_ h_trans
  intro v cv h_lookup
  simp only [MonoVarMap.extend, MonoVarMap.empty, Option.map] at h_lookup
  split_ifs at h_lookup <;> simp at h_lookup <;> cases h_lookup <;>
    simp_all [CVar.lookup, Ne.symm h_ne12, Ne.symm h_ne13, Ne.symm h_ne14,
              Ne.symm h_ne23, Ne.symm h_ne24, Ne.symm h_ne34]

/-! ## Section 10: General Correctness Theorem -/

/-- **General Jasmin→CryptoSSA correctness**: For SSA-compatible commands with
    `BitVec n` variables, the CryptoSSA translation is semantics-preserving.

    This replaces `jasminToCProg_correct` from `JasminSSABridge.lean`. -/
theorem jasminSSA_correct {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) (retVar : Var) (cmd : List InstrR)
    (prog : CProg Γ (.sword n))
    (h_trans : translateMonoCmd m retVar cmd = some prog) :
    ∀ (V : HVec Γ) (env : Var → BitVec n),
    monoAgrees m V env →
    prog.denote V = SPComp.pure (pureEvalMonoCmd n env retVar cmd) :=
  fun V env h => translateMonoCmd_correct m V env retVar cmd prog h h_trans

/-! ## Section 11: Dead Code Elimination Correctness -/

/-- Variables read by an expression in the monomorphic fragment. -/
def monoExprVars : PExpr → List Var
  | .Pvar gv => [gv.gv.var]
  | .Papp2 _ (.Pvar x) (.Pvar y) => [x.gv.var, y.gv.var]
  | .Papp2 _ (.Pvar x) (.Pconst _) => [x.gv.var]
  | .Papp1 _ (.Pvar x) => [x.gv.var]
  | _ => []

/-- Variables that matter for computing `pureEvalMonoCmd`: variables read by instructions
    or the return variable itself. Computed backwards from the return. -/
def monoCmdLiveVars (retVar : Var) : List InstrR → List Var
  | [] => [retVar]
  | .Cassgn (.Lvar x) _ _ e :: rest =>
    let liveRest := monoCmdLiveVars retVar rest
    if x.var ∈ liveRest then
      (liveRest.filter (fun v => !decide (v = x.var))) ++ monoExprVars e
    else
      liveRest
  | _ :: rest => monoCmdLiveVars retVar rest

/-- If two environments agree on the variables read by an expression,
    `pureEvalMonoExpr` gives the same result. -/
theorem pureEvalMonoExpr_irrelevant {n : Nat}
    (env₁ env₂ : Var → BitVec n) (e : PExpr)
    (h : ∀ w ∈ monoExprVars e, env₁ w = env₂ w) :
    pureEvalMonoExpr n env₁ e = pureEvalMonoExpr n env₂ e := by
  cases e with
  | Pvar gv =>
    simp [pureEvalMonoExpr, monoExprVars] at h ⊢; exact h
  | Papp2 op e1 e2 =>
    cases e1 with
    | Pvar x =>
      cases e2 with
      | Pvar y =>
        simp [monoExprVars] at h
        obtain ⟨hx, hy⟩ := h
        cases op <;> simp [pureEvalMonoExpr, hx, hy]
      | Pconst k =>
        simp [monoExprVars] at h
        cases op <;> simp [pureEvalMonoExpr, h]
      | _ => simp [pureEvalMonoExpr]
    | _ => simp [pureEvalMonoExpr]
  | Papp1 op arg =>
    cases arg with
    | Pvar x =>
      simp [monoExprVars] at h
      cases op <;> simp [pureEvalMonoExpr, h]
    | _ => simp [pureEvalMonoExpr]
  | _ => simp [pureEvalMonoExpr]

/-- If two environments agree on the live variables of a command,
    `pureEvalMonoCmd` gives the same result. -/
theorem pureEvalMonoCmd_irrelevant {n : Nat}
    (env₁ env₂ : Var → BitVec n) (retVar : Var) (cmd : List InstrR)
    (h : ∀ w ∈ monoCmdLiveVars retVar cmd, env₁ w = env₂ w) :
    pureEvalMonoCmd n env₁ retVar cmd = pureEvalMonoCmd n env₂ retVar cmd := by
  induction cmd generalizing env₁ env₂ with
  | nil =>
    simp [pureEvalMonoCmd, monoCmdLiveVars] at h ⊢
    exact h
  | cons instr rest ih =>
    cases instr with
    | Cassgn lv tag ty e =>
      cases lv with
      | Lvar x =>
        simp only [pureEvalMonoCmd]
        apply ih
        intro w hw
        simp only [monoCmdLiveVars] at h
        by_cases hx_live : x.var ∈ monoCmdLiveVars retVar rest
        · simp [hx_live] at h
          by_cases hw_eq : w = x.var
          · subst hw_eq; simp
            apply pureEvalMonoExpr_irrelevant
            intro v hv; exact h v (Or.inr hv)
          · simp [hw_eq]
            exact h w (Or.inl ⟨hw, hw_eq⟩)
        · simp [hx_live] at h
          by_cases hw_eq : w = x.var
          · subst hw_eq; exact absurd hw hx_live
          · simp [hw_eq]; exact h w hw
      | _ => simp only [pureEvalMonoCmd]; exact ih _ _ (by simp [monoCmdLiveVars] at h ⊢; exact h)
    | _ => simp only [pureEvalMonoCmd]; exact ih _ _ (by simp [monoCmdLiveVars] at h ⊢; exact h)

/-- A dead assignment (to a variable not live in the rest) can be removed. -/
theorem pureEvalMonoCmd_dead_elim {n : Nat}
    (env : Var → BitVec n) (retVar : Var) (x : VarI) (tag : AssgnTag)
    (ty : SType) (e : PExpr) (rest : List InstrR)
    (h_dead : x.var ∉ monoCmdLiveVars retVar rest) :
    pureEvalMonoCmd n env retVar (.Cassgn (.Lvar x) tag ty e :: rest) =
    pureEvalMonoCmd n env retVar rest := by
  simp only [pureEvalMonoCmd]
  apply pureEvalMonoCmd_irrelevant
  intro w hw
  by_cases hw_eq : w = x.var
  · subst hw_eq; exact absurd hw h_dead
  · simp [hw_eq]

/-- Simple dead code elimination: remove assignments to variables not read later.
    Checks liveness against the original (pre-DCE) rest for straightforward correctness. -/
def simpleDCE (retVar : Var) : List InstrR → List InstrR
  | [] => []
  | .Cassgn (.Lvar x) tag ty e :: rest =>
    if x.var ∈ monoCmdLiveVars retVar rest then
      .Cassgn (.Lvar x) tag ty e :: simpleDCE retVar rest
    else
      simpleDCE retVar rest
  | instr :: rest => instr :: simpleDCE retVar rest

/-- **DCE correctness**: `simpleDCE` preserves `pureEvalMonoCmd`. -/
theorem simpleDCE_correct {n : Nat}
    (env : Var → BitVec n) (retVar : Var) (cmd : List InstrR) :
    pureEvalMonoCmd n env retVar (simpleDCE retVar cmd) =
    pureEvalMonoCmd n env retVar cmd := by
  induction cmd generalizing env with
  | nil => rfl
  | cons instr rest ih =>
    cases instr with
    | Cassgn lv tag ty e =>
      cases lv with
      | Lvar x =>
        simp only [simpleDCE]
        by_cases h_live : x.var ∈ monoCmdLiveVars retVar rest
        · simp [h_live, pureEvalMonoCmd, ih]
        · simp [h_live]
          rw [ih]
          exact (pureEvalMonoCmd_dead_elim env retVar x tag ty e _ h_live).symm
      | _ => simp [simpleDCE, pureEvalMonoCmd, ih]
    | _ => simp [simpleDCE, pureEvalMonoCmd, ih]

end

end CatCrypt.Crypto.Jasmin.ToSSA
