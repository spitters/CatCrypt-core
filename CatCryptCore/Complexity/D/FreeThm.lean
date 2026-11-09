/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.RespB
public import CatCryptCore.Complexity.D.FreeNI
public import CatCryptCore.Complexity.D.GenericGroup
public import CatCryptCore.Complexity.D.Reflect

/-!
# The command `free_theorem`

`free_theorem name binders for t at shape arg` adds the theorem `name`: the free theorem of the
term `t` of D in the given shape, a corollary of the abstraction theorem with cost
(`Tm.abstraction_cost`). The respect of the base relation of the shape by `t` (`Tm.RespB`) is
proved by the tactic `resp_b`. The binders are those of the theorem; the shape adds its own
binders after them. `t` is a term of type `Tm Γ τ`; `for reflect_d f` first reflects the
definition `f` into D (`reflect_d`) and takes `t := f.d`.

The shapes:

* `noninterference hs`, for `hs : Sec s` and `t : Tm (.base s :: Γ) τ`: non-interference with
  equal cost, the statement of `Tm.free_noninterference` at `t`, with the binders
  `(ρ : Env Γ) (k k' : s.den)`. The public context (`∀ σ ∈ Γ, σ.Pub Sec`) is proved from the
  constructors of `Ty.Pub` and the binders.
* `noninterference a₁ … aₘ`, for `t : Tm (X₁ :: … :: Xₘ :: Γ) τ` and each `aᵢ` either a proof
  `hsᵢ : Sec sᵢ`, for a secret variable of type `Xᵢ = .base sᵢ`, or `_`, for a public variable:
  non-interference with equal cost for several secret variables at any positions of the first
  `m`, the statement of `Tm.noninterference_of_rel` at the two environments, with the binders
  `(ρ : Env Γ)` (absent when `Γ` is empty), `(kᵢ kᵢ' : sᵢ.den)` per secret position and
  `(pᵢ : Val Xᵢ)` per public position, in the order of the context. The two runs take `kᵢ` and
  `kᵢ'` at the secret positions and the same `pᵢ` and `ρ` elsewhere; the conclusion is equal cost,
  and equal trees when `τ.Pub Sec`. The public positions and `Γ` are proved public as above. With
  one argument that is a proof this is the shape `noninterference hs`.
* `noninterference_ops h a₁ … aₘ`, for `h : EnvRelB (BRel.secret Sec) ρ δ` with `ρ δ : Env Γ`,
  `m ≥ 0`, and `aᵢ` as above: the same statement with the environments `ρ` and `δ` of `h` in
  place of one public environment `ρ`, for a context `Γ` that is not public, such as an
  environment of operations whose cost does not depend on their secret arguments; the binders
  are those of the positions.
* `hom_commute hφ`, for `hφ : M.IsHom N φ` of group operations at `g`
  (`GenericGroup.GrpOps.IsHom`) and `t : Tm (P₁ :: … :: Pₙ :: el g :: homCtx g) τ`: commutation
  with the homomorphism at equal cost, the statement of `GenericGroup.hom_commute`, with the
  binders `(c : OpCost) (x : g.den)` and one binder `pᵢ : Val Pᵢ` per public input. On the input
  `φ x` over `N` the run gives the image under `φ` of the run on `x` over `M` when `τ` is
  `el g`, and results related by `Ty.relB (homRel g φ) τ` otherwise.
* `iso_commute hφ hinj hg`, for `hφ` as above, `hinj : Function.Injective φ`,
  `hg : FTy.bool ≠ g` and `t : Tm (P₁ :: … :: Pₙ :: el g :: isoCtx g) τ`, a term over the group
  operations and the equality test of group elements: the shape `hom_commute` with the
  environments `isoEnv₁` and their relation `GenericGroup.isoEnv_rel`, the statement of
  `GenericGroup.iso_commute`.
* `rep_independence h`, for `h : EnvRelB (homRel g φ) ρ δ` of two environments of operations
  `ρ δ : Env Δ` and `t : Tm (P₁ :: … :: Pₙ :: el g :: Δ) τ` or `t : Tm Δ τ`: representation
  independence at equal cost, the statement of `rep_independence_input` of the development's
  `Bridges/Transfer/RepIndependence`, with the binders `(x : g.den)` and `pᵢ : Val Pᵢ`.

A public input `pᵢ` is related to itself at the graph of `φ` when its type is built without the
group (`homRel_refl_of_pub`, with `Ty.Pub (· = g) Pᵢ` proved from the constructors of `Ty.Pub`
and the binders). `using [t₁, …, tₙ]` adds the terms `tᵢ` to `resp_b` and to these proofs.
The command fails with the first error of the proof: an obligation `resp_b` does not close, or a
context or an input it does not prove public.

## Main results

* `Tm.homRel_commute` — a term with a result at `g` that respects the graph of `φ` commutes with
  `φ` at equal cost, in environments related by the graph;
* `Ty.Pub.relB_iff_of` — identity extension at the public types for every base relation that is
  equality away from the secret types;
* `homRel_refl_of_pub` — a value of a type built without the group is related to itself by the
  graph of `φ`;
* `Tm.noninterference_of_rel` — non-interference with timing in two environments related by the
  relation of the secret types;
* `Ty.pub_nil`, `Ty.pub_cons` — public contexts;
* `free_theorem` — the command.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open GenericGroup (homRel homRel_self)

/-- A term whose result is an element of `g` and that respects the graph of `φ` commutes with
`φ`: in environments related by the graph, the result of the second run is the image under `φ`
of the result of the first, through the same effects and at equal cost. -/
theorem Tm.homRel_commute {g : FTy} {φ : g.den → g.den} {Γ : List Ty} (t : Tm Γ (.base g))
    (ht : t.RespB (homRel g φ)) {ρ δ : Env Γ} (h : EnvRelB (homRel g φ) ρ δ) :
    CTree.Lift (fun a b => φ a = b) (t.eval ρ) (t.eval δ) ∧
      (t.eval ρ).cost = (t.eval δ).cost := by
  have h' := t.abstraction_cost ht h
  exact ⟨CTree.Lift.mono (fun _ _ hab => homRel_self.1 hab) h'.1, h'.2⟩

/-- Identity extension at the public types of a base relation that is equality at the finite
ground types that are not secret. -/
theorem Ty.Pub.relB_iff_of {R : BRel} {Sec : FTy → Prop}
    (hR : ∀ f, ¬ Sec f → ∀ a b, R f a b ↔ a = b) {τ : Ty} (hτ : τ.Pub Sec) :
    ∀ u v : Val τ, Ty.relB R τ u v ↔ u = v := by
  induction hτ with
  | base hf => exact hR _ hf
  | nat => intro u v; exact Iff.rfl
  | prod _ _ iha ihb =>
    intro u v
    change Ty.relB _ _ u.1 v.1 ∧ Ty.relB _ _ u.2 v.2 ↔ u = v
    rw [iha, ihb]
    exact Prod.ext_iff.symm
  | @sum a b _ _ iha ihb =>
    intro u v
    change Val a ⊕ Val b at u v
    change Sum.LiftRel (Ty.relB _ a) (Ty.relB _ b) u v ↔ u = v
    constructor
    · rintro (⟨hx⟩ | ⟨hy⟩)
      · exact congrArg Sum.inl ((iha _ _).1 hx)
      · exact congrArg Sum.inr ((ihb _ _).1 hy)
    · rintro rfl
      cases u with
      | inl x => exact .inl ((iha x x).2 rfl)
      | inr y => exact .inr ((ihb y y).2 rfl)
  | @list a _ iha =>
    intro u v
    change List.Forall₂ (Ty.relB _ a) u v ↔ u = v
    have hab : Ty.relB R a = (· = ·) :=
      funext fun x => funext fun y => propext (iha x y)
    rw [hab, List.forall₂_eq_eq_eq]
    exact Iff.rfl
  | @pi f B _ ih =>
    intro u v
    change (j : f.den) → Val (B j) at u v
    change (∀ j, Ty.relB _ (B j) (u j) (v j)) ↔ u = v
    rw [funext_iff]
    exact forall_congr' fun j => ih j (u j) (v j)
  | @sig f B _ ih =>
    intro u v
    change (j : f.den) × Val (B j) at u v
    obtain ⟨i, x⟩ := u
    obtain ⟨j, y⟩ := v
    change (∃ e : i = j, Ty.relB _ (B j) (e ▸ x) y) ↔ _
    constructor
    · rintro ⟨rfl, hxy⟩
      rw [(ih i x y).1 hxy]
    · intro he
      obtain ⟨rfl, hx⟩ := Sigma.mk.inj_iff.1 he
      cases hx
      exact ⟨rfl, (ih i x x).2 rfl⟩

/-- A value of a type built without the group `g` is related to itself by the graph of `φ`. -/
theorem homRel_refl_of_pub {g : FTy} {φ : g.den → g.den} {τ : Ty} (hτ : τ.Pub (· = g))
    (u : Val τ) : Ty.relB (homRel g φ) τ u u :=
  (Ty.Pub.relB_iff_of (fun _ hf _ _ => GenericGroup.homRel_of_ne hf) hτ u u).2 rfl

/-- Non-interference with timing in two environments related by the relation of the secret
types: equal cost, and equal trees when the result type is public. -/
theorem Tm.noninterference_of_rel {Sec : FTy → Prop} {Γ : List Ty} {τ : Ty} (t : Tm Γ τ)
    (ht : t.RespB (BRel.secret Sec)) {ρ δ : Env Γ} (h : EnvRelB (BRel.secret Sec) ρ δ) :
    (t.eval ρ).cost = (t.eval δ).cost ∧ (τ.Pub Sec → t.eval ρ = t.eval δ) :=
  ⟨t.cost_eq_of_secret ht h, fun hτ => t.eval_eq_of_pub hτ ht h⟩

/-- The empty context is public. -/
theorem Ty.pub_nil {Sec : FTy → Prop} : ∀ σ ∈ ([] : List Ty), σ.Pub Sec := by
  simp

/-- A context is public when its first type and the rest are. -/
theorem Ty.pub_cons {Sec : FTy → Prop} {a : Ty} {Γ : List Ty} (ha : a.Pub Sec)
    (h : ∀ σ ∈ Γ, σ.Pub Sec) : ∀ σ ∈ a :: Γ, σ.Pub Sec := by
  grind

namespace FreeThm

/-- `free_theorem name binders for t at shape arg` adds the theorem `name`, the free theorem of
the term `t` of D in the shape `noninterference hs`, `noninterference a₁ … aₘ` (each `aᵢ` a
proof of secrecy or `_`), `noninterference_ops h a₁ … aₘ`, `hom_commute hφ`,
`iso_commute hφ hinj hg` or `rep_independence h`, with the respect of the base relation proved
by `resp_b`. `for reflect_d f` reflects `f` first and takes `f.d`; `using [t₁, …, tₙ]` adds
lemmas to `resp_b`. -/
syntax (name := freeTheorem) (docComment)? "free_theorem " ident (ppSpace bracketedBinder)*
  " for " ("reflect_d ")? term " at " ident (ppSpace term:max)+ (" using " "[" term,* "]")? :
  command

meta section

open Lean Meta Elab Term Command

/-- The elements of a list literal `[a₁, …, aₙ]` of `Ty`, with the suffix after each. -/
partial def listElems (l : Expr) : MetaM (Array Expr × Array Expr) := do
  let l ← whnfR (← instantiateMVars l)
  if l.isAppOfArity ``List.cons 3 then
    let (es, ts) ← listElems (l.getArg! 2)
    return (#[l.getArg! 1] ++ es, #[l.getArg! 2] ++ ts)
  else if l.isAppOfArity ``List.nil 1 then
    return (#[], #[])
  else
    throwError "free_theorem: the context{indentExpr l}\nis not a list of types"

/-- Introduces the local declarations `decls` and runs `k`; returns the result of `k`, a
statement and its proof, abstracted over the declarations. -/
def withBinders (decls : Array (Name × Expr)) (k : Array Expr → TermElabM (Expr × Expr)) :
    TermElabM (Expr × Expr) :=
  withLocalDeclsDND decls fun ys => do
    let (ty, pf) ← k ys
    return (← mkForallFVars ys ty, ← mkLambdaFVars ys pf)

/-- Elaborates the proof `pf` and returns its type and the proof. -/
def elabProof (pf : Term) : TermElabM (Expr × Expr) := withoutErrToSorry do
  let e ← elabTerm pf none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← instantiateMVars (← inferType e)
  return (ty, e)

/-- The lemmas of `resp_b` at a relation of the secret types. -/
def niLemmas : Array Name :=
  #[``Prim.respB_of_pub, ``BRel.secret_eq, ``Ty.Pub.base, ``Ty.Pub.nat, ``Ty.Pub.prod,
    ``Ty.Pub.sum, ``Ty.Pub.list]

/-- The lemmas of `resp_b` at the graph of a map of a group. -/
def homLemmas : Array Name := #[``GenericGroup.homRel_of_ne, ``GenericGroup.homRel_self]

/-- The `resp_b` call with the lemmas `ls` and the extra terms `extra`. -/
def respBTac (ls : Array Name) (extra : Array Term) : TermElabM Term := do
  let ts : Array Term := ls.map mkCIdent ++ extra
  `(by resp_b [$ts,*])

/-- The proof of a goal `τ.Pub Sec` from the constructors of `Ty.Pub`, the hypotheses and the
extra terms `extra`. -/
def pubTac (extra : Array Term) : TermElabM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  let ts : Array Term := #[``Ty.Pub.base, ``Ty.Pub.nat, ``Ty.Pub.prod, ``Ty.Pub.sum,
    ``Ty.Pub.list, ``Ty.Pub.pi, ``Ty.Pub.sig].map mkCIdent ++ extra
  let rules ← ts.mapM fun p => `(Lean.Parser.Tactic.SolveByElim.arg| $p:term)
  `(Lean.Parser.Tactic.tacticSeq| solve_by_elim (maxDepth := 64) [$rules,*])

/-- The shape `noninterference hs`. -/
def shapeNI (t : Expr) (Γ : Expr) (hs : Term) (extra : Array Term) :
    TermElabM (Expr × Expr) := do
  let (es, ts) ← listElems Γ
  let some s0 := es[0]? | throwError "free_theorem: the context of the term is empty"
  let s0 ← whnfR s0
  unless s0.isAppOfArity ``Ty.base 1 do
    throwError "free_theorem: the innermost variable{indentExpr s0}\nis not of a finite type"
  let s := s0.getArg! 0
  let rest := ts[0]!
  withBinders #[(`ρ, mkApp (mkConst ``Env) rest), (`k, mkApp (mkConst ``FTy.den) s),
      (`k', mkApp (mkConst ``FTy.den) s)] fun ys => do
    let tS ← exprToSyntax t
    let ρ ← exprToSyntax ys[0]!
    let k ← exprToSyntax ys[1]!
    let k' ← exprToSyntax ys[2]!
    let ht ← respBTac niLemmas extra
    let pubT ← pubTac extra
    let nil := mkCIdent ``Ty.pub_nil
    let cons := mkCIdent ``Ty.pub_cons
    let hΓ ← `(by
      repeat' (first | exact $nil | refine $cons ?_ ?_)
      all_goals first
        | $pubT
        | fail "free_theorem: no constructor of `Ty.Pub` proves that the context is public")
    elabProof (← `($(mkCIdent ``Tm.free_noninterference) $hs $tS $ht $hΓ $ρ $k $k'))

/-- The shape `noninterference a₁ … aₘ` with `m > 1` or a public position: the variable `i` of
the context is secret when `aᵢ` is a proof `hs : Sec s` and public when `aᵢ` is `_`. With
`base := some h`, for `h : EnvRelB (BRel.secret Sec) ρ δ`, the shape
`noninterference_ops h a₁ … aₘ`:
the rest of the context takes the environments `ρ` and `δ` of `h` instead of one public
environment. -/
def shapeNIs (t Γ : Expr) (args : Array Term) (extra : Array Term)
    (base : Option Term := none) : TermElabM (Expr × Expr) := do
  let (es, ts) ← listElems Γ
  let m := args.size
  if es.size < m then
    throwError "free_theorem: the context of the term has fewer than {m} variables"
  let rest := if m = 0 then Γ else ts[m - 1]!
  -- For each position: `none` when public, `some (proof, s)` when secret.
  let mut secrets : Array (Option (Term × Expr)) := #[]
  let mut sec? : Option Expr := none
  -- The environments of the rest of the context and their relation, from `base`.
  let mut baseEnvs : Option (Term × Term) := none
  if let some h := base then
    let hE ← elabTerm h none
    synthesizeSyntheticMVarsNoPostponing
    let hT := (← instantiateMVars (← inferType hE)).consumeMData
    unless hT.isAppOfArity ``EnvRelB 4 do
      throwError "free_theorem: noninterference_ops expects related environments, not{
        indentExpr hT}"
    let R := (← whnfR (← instantiateMVars (hT.getArg! 0))).consumeMData
    unless R.isAppOfArity ``BRel.secret 1 do
      throwError "free_theorem: the relation{indentExpr R}\nis not `BRel.secret Sec`"
    unless ← isDefEq (hT.getArg! 1) rest do
      throwError "free_theorem: the environments of{indentExpr hT}\nare not of the context{
        indentExpr rest}"
    sec? := some (R.getArg! 0)
    baseEnvs := some (← exprToSyntax (hT.getArg! 2), ← exprToSyntax (hT.getArg! 3))
  let restNil := baseEnvs.isSome || (← whnfR rest).isAppOfArity ``List.nil 1
  for i in [0:m] do
    let a := args[i]!
    if a.raw.isOfKind ``Lean.Parser.Term.hole then
      secrets := secrets.push none
    else
      let si ← whnfR es[i]!
      unless si.isAppOfArity ``Ty.base 1 do
        throwError "free_theorem: the secret variable {i + 1}{indentExpr si}\nis not of a \
          finite type"
      let s := si.getArg! 0
      let hE ← elabTerm a none
      synthesizeSyntheticMVarsNoPostponing
      let hT ← instantiateMVars (← inferType hE)
      let .app Sec s' := hT.consumeMData | throwError "free_theorem: the proof of secrecy of \
        variable {i + 1} has type{indentExpr hT}\nnot `Sec s`"
      unless ← isDefEq s s' do
        throwError "free_theorem: the proof of secrecy of variable {i + 1} is about{
          indentExpr s'}\nnot{indentExpr s}"
      if let some Sec0 := sec? then
        unless ← isDefEq Sec Sec0 do
          throwError "free_theorem: the proofs of secrecy name different sets of secret types"
      else sec? := some Sec
      secrets := secrets.push (some (a, s))
  let some Sec := sec? | throwError "free_theorem: noninterference needs a secret variable"
  let mut decls : Array (Name × Expr) :=
    if restNil then #[] else #[(`ρ, mkApp (mkConst ``Env) rest)]
  for i in [0:m] do
    match secrets[i]! with
    | none => decls := decls.push (Name.mkSimple s!"p{i + 1}", mkApp (mkConst ``Val) es[i]!)
    | some (_, s) =>
      decls := decls.push (Name.mkSimple s!"k{i + 1}", mkApp (mkConst ``FTy.den) s)
      decls := decls.push (Name.mkSimple s!"k{i + 1}'", mkApp (mkConst ``FTy.den) s)
  withBinders decls fun ys => do
    let SecS ← exprToSyntax Sec
    let restS ← exprToSyntax rest
    let pubT ← pubTac extra
    let nil := mkCIdent ``Ty.pub_nil
    let cons := mkCIdent ``Ty.pub_cons
    let hΓ ← `((by
      repeat' (first | exact $nil | refine $cons ?_ ?_)
      all_goals first
        | $pubT
        | fail "free_theorem: no constructor of `Ty.Pub` proves that the context is public" :
        ∀ σ ∈ $restS, Ty.Pub $SecS σ))
    let (ρ0 : Term) ← if restNil then `($(mkCIdent ``Env.nil)) else exprToSyntax ys[0]!
    let (ρ1, δ1) := baseEnvs.getD (ρ0, ρ0)
    let mut ρ := ρ1
    let mut δ := δ1
    let mut rel ← match base with
      | some h => pure h
      | none => `($(mkCIdent ``EnvRelB.refl_of_pub) (Sec := $SecS) $hΓ $ρ0)
    -- The binders of position `i` start at `idx[i]`.
    let mut idx : Array Nat := #[]
    let mut n := if restNil then 0 else 1
    for i in [0:m] do
      idx := idx.push n
      n := n + (if secrets[i]!.isSome then 2 else 1)
    for j in [0:m] do
      let i := m - 1 - j
      let X ← exprToSyntax es[i]!
      match secrets[i]! with
      | none =>
        let p ← exprToSyntax ys[idx[i]!]!
        ρ ← `($(mkCIdent ``Env.cons) (τ := $X) $p $ρ)
        δ ← `($(mkCIdent ``Env.cons) (τ := $X) $p $δ)
        let hX ← `((by first
          | $pubT
          | fail "free_theorem: no constructor of `Ty.Pub` proves that the input is public" :
          Ty.Pub $SecS $X))
        rel ← `($(mkCIdent ``EnvRelB.cons) (τ := $X) (u := $p) (v := $p) $rel
          (($(mkCIdent ``Ty.Pub.relB_iff) $hX $p $p).2 rfl))
      | some (hs, _) =>
        let k ← exprToSyntax ys[idx[i]!]!
        let k' ← exprToSyntax ys[idx[i]! + 1]!
        ρ ← `($(mkCIdent ``Env.cons) (τ := $X) $k $ρ)
        δ ← `($(mkCIdent ``Env.cons) (τ := $X) $k' $δ)
        rel ← `($(mkCIdent ``EnvRelB.cons) (τ := $X) (u := $k) (v := $k') $rel
          (Or.inl $hs))
    let tS ← exprToSyntax t
    let ht ← respBTac niLemmas extra
    elabProof (← `($(mkCIdent ``Tm.noninterference_of_rel) (Sec := $SecS) $tS $ht
      (ρ := $ρ) (δ := $δ) $rel))

/-- The proof that a public input `p : Val P` is related to itself. -/
def inputRelTac (extra : Array Term) : TermElabM Term := do
  `($(mkCIdent ``homRel_refl_of_pub) (by first
    | $(← pubTac extra)
    | fail "free_theorem: no constructor of `Ty.Pub` proves that the input avoids the group") _)

/-- The common part of the shapes `hom_commute` and `rep_independence`: the inputs
`P₁ … Pₙ` in front of the variable `el g` and the context `Δ` of operations. `env x` gives the
two environments of `el g :: Δ` and their relation for the input `x`. -/
def shapeGraph (t τ : Expr) (Γ g Δ : Expr) (extra : Array Term) (pre : Array (Name × Expr))
    (env : Array Expr → Option Expr → TermElabM (Term × Term × Term)) :
    TermElabM (Expr × Expr) := do
  let (es, ts) ← listElems Γ
  let (dElems, _) ← listElems Δ
  let n := es.size
  let m := dElems.size
  let gTy := mkApp (mkConst ``Ty.base) g
  let hasX := n > m
  let k := if hasX then n - m - 1 else 0
  if n < m then throwError "free_theorem: the context of the term is shorter than{indentExpr Δ}"
  if hasX then
    unless ← isDefEq es[k]! gTy do
      throwError "free_theorem: the variable after the inputs is not of type{indentExpr gTy}"
    unless ← isDefEq ts[k]! Δ do
      throwError "free_theorem: the context of the term does not end with{indentExpr Δ}"
  else
    unless ← isDefEq Γ Δ do
      throwError "free_theorem: the context of the term is not{indentExpr Δ}"
  let xDecl : Array (Name × Expr) :=
    if hasX then #[(`x, mkApp (mkConst ``FTy.den) g)] else #[]
  let inputs : Array (Name × Expr) := (List.range k).reverse.toArray.map fun i =>
    (Name.mkSimple s!"p{i + 1}", mkApp (mkConst ``Val) es[i]!)
  withBinders (pre ++ xDecl ++ inputs) fun ys => do
    let preVs := ys.extract 0 pre.size
    let x? := if hasX then some ys[pre.size]! else none
    let (ρ0, δ0, rel0) ← env preVs x?
    let mut ρ := ρ0
    let mut δ := δ0
    let mut rel := rel0
    for j in [0:k] do
      let i := k - 1 - j
      let p ← exprToSyntax ys[pre.size + xDecl.size + j]!
      let P ← exprToSyntax es[i]!
      ρ ← `($(mkCIdent ``Env.cons) (τ := $P) $p $ρ)
      δ ← `($(mkCIdent ``Env.cons) (τ := $P) $p $δ)
      rel ← `($(mkCIdent ``EnvRelB.cons) (τ := $P) (u := $p) (v := $p) $rel
        $(← inputRelTac extra))
    let tS ← exprToSyntax t
    let ht ← respBTac homLemmas extra
    let thm := if ← isDefEq τ gTy then ``Tm.homRel_commute else ``Tm.abstraction_cost
    elabProof (← `($(mkCIdent thm) $tS $ht (ρ := $ρ) (δ := $δ) $rel))

/-- The shape `hom_commute hφ`, and with `iso := some (hinj, hg)` the shape
`iso_commute hφ hinj hg` over the group operations and the equality test. -/
def shapeHom (t τ Γ : Expr) (hφ : Term) (extra : Array Term)
    (iso : Option (Term × Term) := none) : TermElabM (Expr × Expr) := do
  let hE ← elabTerm hφ none
  synthesizeSyntheticMVarsNoPostponing
  let hT ← whnfR (← instantiateMVars (← inferType hE))
  unless hT.isAppOfArity ``GenericGroup.GrpOps.IsHom 5 do
    throwError "free_theorem: hom_commute expects a homomorphism of group operations, not{
      indentExpr hT}"
  let X ← whnfR (hT.getArg! 0)
  unless X.isAppOfArity ``FTy.den 1 do
    throwError "free_theorem: the carrier{indentExpr X}\nis not a finite ground type"
  let g := X.getArg! 0
  let M := hT.getArg! 2
  let N := hT.getArg! 3
  let φ := hT.getArg! 4
  let Δ := mkApp (mkConst (if iso.isSome then ``GenericGroup.isoCtx else ``GenericGroup.homCtx)) g
  shapeGraph t τ Γ g Δ extra #[(`c, mkConst ``GenericGroup.OpCost)] fun pre x? => do
    let some x := x? | throwError "free_theorem: {if iso.isSome then "iso_commute" else
      "hom_commute"} needs an input element"
    let c ← exprToSyntax pre[0]!
    let xS ← exprToSyntax x
    let gS ← exprToSyntax g
    let MS ← exprToSyntax M
    let NS ← exprToSyntax N
    let φS ← exprToSyntax φ
    let (envF, relΔ) ← match iso with
      | none => pure (mkCIdent ``GenericGroup.homEnv₁,
          ← `($(mkCIdent ``GenericGroup.homEnv_rel) $hφ $c))
      | some (hinj, hg) => pure (mkCIdent ``GenericGroup.isoEnv₁,
          ← `($(mkCIdent ``GenericGroup.isoEnv_rel) $hφ $hinj $hg $c))
    let ρ ← `($envF $gS $MS $c $xS)
    let δ ← `($envF $gS $NS $c ($φS $xS))
    let rel ← `($(mkCIdent ``EnvRelB.cons) $relΔ
      (τ := $(mkCIdent ``Ty.base) $gS) (u := $xS) (v := $φS $xS)
      ($(mkCIdent ``GenericGroup.homRel_self).2 rfl))
    return (ρ, δ, rel)

/-- The shape `rep_independence h`. -/
def shapeRep (t τ Γ : Expr) (h : Term) (extra : Array Term) : TermElabM (Expr × Expr) := do
  let hE ← elabTerm h none
  synthesizeSyntheticMVarsNoPostponing
  let hT ← instantiateMVars (← inferType hE)
  let hT := hT.consumeMData
  unless hT.isAppOfArity ``EnvRelB 4 do
    throwError "free_theorem: rep_independence expects related environments, not{
      indentExpr hT}"
  let R := (← instantiateMVars (hT.getArg! 0)).consumeMData
  unless R.isAppOfArity ``GenericGroup.homRel 2 do
    throwError "free_theorem: the relation{indentExpr R}\nis not the graph `homRel g φ`"
  let g := R.getArg! 0
  let φ := R.getArg! 1
  let Δ := hT.getArg! 1
  let ρΔ ← exprToSyntax (hT.getArg! 2)
  let δΔ ← exprToSyntax (hT.getArg! 3)
  shapeGraph t τ Γ g Δ extra #[] fun _ x? => do
    match x? with
    | none => return (ρΔ, δΔ, h)
    | some x =>
      let xS ← exprToSyntax x
      let gS ← exprToSyntax g
      let φS ← exprToSyntax φ
      let τg ← `($(mkCIdent ``Ty.base) $gS)
      let ρ ← `($(mkCIdent ``Env.cons) (τ := $τg) $xS $ρΔ)
      let δ ← `($(mkCIdent ``Env.cons) (τ := $τg) ($φS $xS) $δΔ)
      let rel ← `($(mkCIdent ``EnvRelB.cons) $h (τ := $τg) (u := $xS) (v := $φS $xS)
        ($(mkCIdent ``GenericGroup.homRel_self).2 rfl))
      return (ρ, δ, rel)

/-- The elaborator of `free_theorem`. -/
@[command_elab freeTheorem] def elabFreeTheorem : CommandElab := fun stx => do
  let doc? := stx[0].getOptional?
  let nameStx := stx[2]
  let bs : Array Syntax := stx[3].getArgs
  let reflect := !stx[5].isNone
  let shape := stx[8].getId
  let args : Array Term := stx[9].getArgs.map (⟨·⟩)
  let arg : Term := args[0]!
  let nArgs (k : Nat) : CommandElabM Unit := do
    unless args.size = k do
      throwErrorAt stx[8] "free_theorem: the shape `{shape}` takes {k} argument(s)"
  let extra : Array Term :=
    if stx[10].isNone then #[] else stx[10][0][2].getSepArgs.map (⟨·⟩)
  match shape with
  | `hom_commute | `rep_independence => nArgs 1
  | `iso_commute => nArgs 3
  | _ => pure ()
  let tStx : Term ← if reflect then do
      unless stx[6].isIdent do
        throwErrorAt stx[6] "free_theorem: reflect_d expects the name of a definition"
      elabCommand (← `(reflect_d $(⟨stx[6]⟩):ident))
      let c ← liftCoreM <| realizeGlobalConstNoOverload stx[6]
      pure (mkCIdent (c ++ `d))
    else pure ⟨stx[6]⟩
  let (declName, _) ← mkDeclName (← getCurrNamespace) {} nameStx.getId
  let (type, value) ← liftTermElabM do
    elabBinders (bs.map fun b => (⟨b⟩ : TSyntax ``Parser.Term.bracketedBinder)) fun xs => do
      let t ← elabTerm tStx none
      synthesizeSyntheticMVarsNoPostponing
      let t ← instantiateMVars t
      let tT ← whnfR (← instantiateMVars (← inferType t))
      unless tT.isAppOfArity ``Tm 2 do
        throwErrorAt stx[6] "free_theorem: the term has type{indentExpr tT}\nnot `Tm Γ τ`"
      let Γ := tT.getArg! 0
      let τ := tT.getArg! 1
      let (ty, pf) ← match shape with
        | `noninterference =>
          if args.size = 1 && !arg.raw.isOfKind ``Lean.Parser.Term.hole then
            shapeNI t Γ arg extra
          else shapeNIs t Γ args extra
        | `noninterference_ops => shapeNIs t Γ (args.extract 1 args.size) extra (some arg)
        | `hom_commute => shapeHom t τ Γ arg extra
        | `iso_commute => shapeHom t τ Γ arg extra (some (args[1]!, args[2]!))
        | `rep_independence => shapeRep t τ Γ arg extra
        | _ => throwErrorAt stx[8] "free_theorem: unknown shape `{shape}`; the shapes are \
            `noninterference`, `noninterference_ops`, `hom_commute`, `iso_commute` and \
            `rep_independence`"
      let ty ← instantiateMVars (← mkForallFVars xs ty)
      let pf ← instantiateMVars (← mkLambdaFVars xs pf)
      if ty.hasMVar || pf.hasMVar then
        throwError "free_theorem: the statement or the proof has unassigned metavariables"
      return (ty, pf)
  let lps := (collectLevelParams (collectLevelParams {} type) value).params.toList
  liftCoreM <| addDecl <| .thmDecl { name := declName, levelParams := lps, type, value }
  if let some doc := doc? then
    liftTermElabM <| addDocString declName (binders := mkNullNode bs)
      (⟨doc⟩ : TSyntax ``Parser.Command.docComment)
  liftTermElabM <| addTermInfo' nameStx (mkConst declName (lps.map Level.param))
    (isBinder := true)

end

end FreeThm

end CatCrypt.Complexity.D
