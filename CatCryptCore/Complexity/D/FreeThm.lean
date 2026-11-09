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
* `hom_commute hφ`, for `hφ : M.IsHom N φ` of group operations at `g`
  (`GenericGroup.GrpOps.IsHom`) and `t : Tm (P₁ :: … :: Pₙ :: el g :: homCtx g) τ`: commutation
  with the homomorphism at equal cost, the statement of `GenericGroup.hom_commute`, with the
  binders `(c : OpCost) (x : g.den)` and one binder `pᵢ : Val Pᵢ` per public input. On the input
  `φ x` over `N` the run gives the image under `φ` of the run on `x` over `M` when `τ` is
  `el g`, and results related by `Ty.relB (homRel g φ) τ` otherwise.
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

/-- The empty context is public. -/
theorem Ty.pub_nil {Sec : FTy → Prop} : ∀ σ ∈ ([] : List Ty), σ.Pub Sec := by
  simp

/-- A context is public when its first type and the rest are. -/
theorem Ty.pub_cons {Sec : FTy → Prop} {a : Ty} {Γ : List Ty} (ha : a.Pub Sec)
    (h : ∀ σ ∈ Γ, σ.Pub Sec) : ∀ σ ∈ a :: Γ, σ.Pub Sec := by
  grind

namespace FreeThm

/-- `free_theorem name binders for t at shape arg` adds the theorem `name`, the free theorem of
the term `t` of D in the shape `noninterference hs`, `hom_commute hφ` or `rep_independence h`,
with the respect of the base relation proved by `resp_b`. `for reflect_d f` reflects `f` first
and takes `f.d`; `using [t₁, …, tₙ]` adds lemmas to `resp_b`. -/
syntax (name := freeTheorem) (docComment)? "free_theorem " ident (ppSpace bracketedBinder)*
  " for " ("reflect_d ")? term " at " ident term:max (" using " "[" term,* "]")? : command

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

/-- The shape `hom_commute hφ`. -/
def shapeHom (t τ Γ : Expr) (hφ : Term) (extra : Array Term) : TermElabM (Expr × Expr) := do
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
  let Δ := mkApp (mkConst ``GenericGroup.homCtx) g
  shapeGraph t τ Γ g Δ extra #[(`c, mkConst ``GenericGroup.OpCost)] fun pre x? => do
    let some x := x? | throwError "free_theorem: hom_commute needs an input element"
    let c ← exprToSyntax pre[0]!
    let xS ← exprToSyntax x
    let gS ← exprToSyntax g
    let MS ← exprToSyntax M
    let NS ← exprToSyntax N
    let φS ← exprToSyntax φ
    let ρ ← `($(mkCIdent ``GenericGroup.homEnv₁) $gS $MS $c $xS)
    let δ ← `($(mkCIdent ``GenericGroup.homEnv₁) $gS $NS $c ($φS $xS))
    let rel ← `($(mkCIdent ``EnvRelB.cons) ($(mkCIdent ``GenericGroup.homEnv_rel) $hφ $c)
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
  let arg : Term := ⟨stx[9]⟩
  let extra : Array Term :=
    if stx[10].isNone then #[] else stx[10][0][2].getSepArgs.map (⟨·⟩)
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
        | `noninterference => shapeNI t Γ arg extra
        | `hom_commute => shapeHom t τ Γ arg extra
        | `rep_independence => shapeRep t τ Γ arg extra
        | _ => throwErrorAt stx[8] "free_theorem: unknown shape `{shape}`; the shapes are \
            `noninterference`, `hom_commute` and `rep_independence`"
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
