/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.DillerNahm
public import CatCryptCore.Container.DNCert

/-!
# Open costed trees of D-terms

The costed tree `Tm.dtC` of a D-term is closed: a call of a function variable splices the entry
of the variable into the tree. The open costed tree `Tm.dtO` of a term keeps the calls of the
function variables of a context `Γ₀` as operations: it is a tree of `FreeM (SPSigT + CallSig Γ₀)`,
whose operations are those of a costed tree (`SPSigT`, with the step costs as tick nodes) and the
call tokens `CallSig Γ₀`, a function variable of `Γ₀` at a translated argument, answered by a
translated value of its codomain. A call token is the element `(u, data token)` of the position
type `Σ u : a.hat, Q.B (p u)` of the function space of the Diller–Nahm model, the backward
component of a term at a function variable in Pédrot's functional Dialectica interpretation.

The closed tree is the open tree interpreted by the handler that runs the entry of each function
variable at its argument (`Tm.wpFold_dtC_eq_liftM_dtO`), an equation of the charge folds: the
costed bind of `Tm.dtC` merges the step cost of a continuation into the edge before it, which
the fold does not see. Substitution of callees for the function variables is thus interpretation
of the call tokens by a handler (Plotkin and Pretnar), and the composition law of use bounds
under a handler (`useBound_liftM`) applies to D-terms:

* `Tm.cost_le_of_useBound`: a use bound of the open tree, read at a resource map of the call
  tokens, and time bounds of the entries bound the cost of every evaluation, `allowance + base
  cost + Σ uses · time`, the form `T_R + Σ q_i · T_i` of a reduction certificate;
* `Tm.useBound_liftM_substHandler_clocked`: substituting, at every call token, an open callee
  with the use vector of a costed function `f` into a term with the use vector of `g` gives the
  use vector of `Clocked.comp g f` (uses `n₂ * n₁`, cost `c₂ + n₂ * c₁`).

## Main definitions

* `CallSig`, `OSig`: the call tokens of the function variables of `Γ₀`, and the operations of an
  open costed tree
* `Ty.hatO`, `EnvO`, `EnvO.ofEnvHat`: open entries, a function variable an open tree at each
  argument, and the open environment of a translated one, its function variables as call tokens
* `Tm.dtO`: the open costed tree of a term
* `EnvHat.callImpl`: the handler of the call tokens by the entries of a translated environment
* `substHandler`: the handler that runs an open callee at each call token

## Main results

* `Tm.dtC_congr`: the costed tree of a pure term of the fragment reads only the entries of the
  variables that are not of function type
* `Tm.wpFold_dtC_eq_liftM_dtO`: the closed tree is the open tree interpreted by the entries
* `Tm.cost_le_of_useBound`: the cost of a D-term from a use bound of its open tree
* `Tm.useBound_liftM_substHandler_clocked`: `Clocked.comp` as substitution of a callee

## References

* P.-M. Pédrot, *A functional functional interpretation*, LICS 2014;
* G. Plotkin, M. Pretnar, *Handlers of algebraic effects*, ESOP 2009;
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core CatCrypt.Container PFunctor PFunctor.FreeM
open CatCrypt.Core.SPTree (SPSigT tickCost)
open CatCrypt.Core.SPTree.Timed (toFreeMT stepToFreeMT)
open scoped BigOperators

/-! ## Call tokens and open entries -/

/-- The call tokens of the function variables of `Γ₀`: a function variable with a translated
argument, answered by a translated value of its codomain. -/
def CallSig (Γ₀ : List Ty) : PFunctor.{1, 0} :=
  ⟨ULift.{1} (Σ ab : Ty × Ty, Var Γ₀ (.arr ab.1 ab.2) × ab.1.hat), fun c => c.down.1.2.hat⟩

/-- The operations of an open costed tree: those of a costed tree and the call tokens of `Γ₀`. -/
abbrev OSig (Γ₀ : List Ty) : PFunctor.{1, 0} := SPSigT + CallSig Γ₀

/-- The call token of the function variable `y` at the argument `u`. -/
def callO {Γ₀ : List Ty} {a b : Ty} (y : Var Γ₀ (.arr a b)) (u : a.hat) :
    FreeM (OSig Γ₀) b.hat :=
  FreeM.lift (P := OSig Γ₀) (Sum.inr ⟨⟨(a, b), y, u⟩⟩)

/-- A step-prefixed costed tree as an open tree without call tokens. -/
def embO {Γ₀ : List Ty} {α : Type} (x : ℕ × SPTree.Timed α) : FreeM (OSig Γ₀) α :=
  (stepToFreeMT x).mapLens Lens.inl

/-- The tick `c` in front of an open tree. -/
def delayO {Γ₀ : List Ty} {α : Type} (c : ℕ) (X : FreeM (OSig Γ₀) α) : FreeM (OSig Γ₀) α :=
  FreeM.liftBind (P := OSig Γ₀) (Sum.inl (Sum.inr c)) fun _ => X

/-- The open entries: a variable of function type is an open tree at each argument, a variable
of any other type a translated entry. -/
def Ty.hatO (Γ₀ : List Ty) : Ty → Type 1
  | .base f => Ty.hatE (.base f)
  | .nat => Ty.hatE .nat
  | .prod a b => Ty.hatE (.prod a b)
  | .sum a b => Ty.hatE (.sum a b)
  | .arr a b => Ty.hat a → FreeM (OSig Γ₀) (Ty.hat b)
  | .list a => Ty.hatE (.list a)
  | .mu S => Ty.hatE (.mu S)
  | .pi f B => Ty.hatE (.pi f B)
  | .sig f B => Ty.hatE (.sig f B)
  | .imu f S i => Ty.hatE (.imu f S i)

/-- The closed entry of an open entry: the entry itself at a type other than a function type,
the failing tree at a function type. -/
noncomputable def Ty.closeO {Γ₀ : List Ty} : (τ : Ty) → τ.hatO Γ₀ → τ.hatE
  | .base _, v => v
  | .nat, v => v
  | .prod _ _, v => v
  | .sum _ _, v => v
  | .arr _ _, _ => fun _ => (0, .fail)
  | .list _, v => v
  | .mu _, v => v
  | .pi _ _, v => v
  | .sig _ _, v => v
  | .imu _ _ _, v => v

/-- A translated value as an open entry: a pure costed closure is the open tree of its value
behind its cost. -/
noncomputable def Ty.ofHatO {Γ₀ : List Ty} : (τ : Ty) → τ.hat → τ.hatO Γ₀
  | .base f, u => Ty.ofHat (.base f) u
  | .nat, u => Ty.ofHat .nat u
  | .prod a b, u => Ty.ofHat (.prod a b) u
  | .sum a b, u => Ty.ofHat (.sum a b) u
  | .arr _ _, p => fun u => embO (p.2 u, .ret (p.1 u))
  | .list a, u => Ty.ofHat (.list a) u
  | .mu S, u => Ty.ofHat (.mu S) u
  | .pi f B, u => Ty.ofHat (.pi f B) u
  | .sig f B, u => Ty.ofHat (.sig f B) u
  | .imu f S i, u => Ty.ofHat (.imu f S i) u

/-- The open entry of a variable `y` of `Γ₀` with the translated entry `v`: the call tokens of
`y` at a function type, `v` at any other type. -/
def Ty.entryO {Γ₀ : List Ty} : (τ : Ty) → Var Γ₀ τ → τ.hatE → τ.hatO Γ₀
  | .base _, _, v => v
  | .nat, _, v => v
  | .prod _ _, _, v => v
  | .sum _ _, _, v => v
  | .arr _ _, y, _ => fun u => callO y u
  | .list _, _, v => v
  | .mu _, _, v => v
  | .pi _ _, _, v => v
  | .sig _ _, _, v => v
  | .imu _ _ _, _, v => v

/-- At a type other than a function type, a translated value read back from its open entry is
its entry. -/
theorem Ty.ofHat_eq_closeO_ofHatO {Γ₀ : List Ty} {σ : Ty} (h : σ.isArr = false) (u : σ.hat) :
    σ.ofHat u = σ.closeO (σ.ofHatO (Γ₀ := Γ₀) u) := by
  cases σ <;> first | rfl | simp [Ty.isArr] at h

/-- Open environments of the context `Δ`, with call tokens of `Γ₀`. -/
def EnvO (Γ₀ Δ : List Ty) : Type 1 := (τ : Ty) → Var Δ τ → τ.hatO Γ₀

/-- The open environment of a translated environment: its entries at the variables that are not
of function type, the call tokens at the function variables. -/
def EnvO.ofEnvHat {Γ₀ : List Ty} (η : EnvHat Γ₀) : EnvO Γ₀ Γ₀ :=
  fun τ y => τ.entryO y (η τ y)

/-- Extend an open environment by a translated value for the innermost variable. -/
noncomputable def EnvO.cons {Γ₀ Δ : List Ty} {σ : Ty} (u : σ.hat) (e : EnvO Γ₀ Δ) :
    EnvO Γ₀ (σ :: Δ) :=
  fun _ x => match x with
    | .here => σ.ofHatO u
    | .there y => e _ y

/-- The closed environment of an open one: the entries at the variables that are not of function
type, the failing tree at the function variables. -/
noncomputable def EnvO.close {Γ₀ Δ : List Ty} (e : EnvO Γ₀ Δ) : EnvHat Δ :=
  fun τ x => τ.closeO (e τ x)

/-- The handler of the call tokens of `Γ₀` by the entries of `η`: the step-prefixed tick tree of
the entry of the variable at the argument. -/
noncomputable def EnvHat.callImpl {Γ₀ : List Ty} (η : EnvHat Γ₀) :
    (c : (CallSig Γ₀).A) → FreeM SPSigT ((CallSig Γ₀).B c) :=
  fun c => stepToFreeMT (η _ c.down.2.1 c.down.2.2)

/-- Two translated environments agree at the variables that are not of function type. -/
def EnvHat.AgreeData {Δ : List Ty} (η η' : EnvHat Δ) : Prop :=
  ∀ τ (x : Var Δ τ), τ.isArr = false → η τ x = η' τ x

/-- Agreement at the variables that are not of function type is kept by an extension. -/
theorem EnvHat.AgreeData.cons {Δ : List Ty} {σ : Ty} {η η' : EnvHat Δ} (h : η.AgreeData η')
    (u : σ.hat) : (η.cons u).AgreeData (η'.cons u) := by
  intro τ x hx
  cases x with
  | here => rfl
  | there y => exact h _ y hx

/-! ## Charge folds of interpreted open trees -/

section OEq

variable {Γ₀ : List Ty}

/-- A tree of `SPSigT` and a step-prefixed costed tree have equal charge folds at every
postcondition, the answers read under `allows`. -/
def OEq (allows : (a : SPSigT.A) → SPSigT.B a → Prop) {α : Type} (X : FreeM SPSigT α)
    (x : ℕ × SPTree.Timed α) : Prop :=
  ∀ post : α → ℕ∞,
    wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows) X post =
      wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows) (stepToFreeMT x) post

variable {allows : (a : SPSigT.A) → SPSigT.B a → Prop}

/-- An open tree without call tokens, interpreted by a call handler, is its tick tree. -/
theorem liftM_callHandler_embO {α : Type}
    (impl : (c : (CallSig Γ₀).A) → FreeM SPSigT ((CallSig Γ₀).B c)) (x : ℕ × SPTree.Timed α) :
    (embO (Γ₀ := Γ₀) x).liftM (callHandler impl) = stepToFreeMT x := by
  unfold embO callHandler
  rw [Handler.liftM_sum_mapLens_inl]
  exact FreeM.liftM_lift_eq_self _

/-- An open tree without call tokens has the charge folds of its costed tree. -/
theorem oeq_embO {α : Type} (impl : (c : (CallSig Γ₀).A) → FreeM SPSigT ((CallSig Γ₀).B c))
    (x : ℕ × SPTree.Timed α) :
    OEq allows ((embO (Γ₀ := Γ₀) x).liftM (callHandler impl)) x := by
  intro post
  rw [liftM_callHandler_embO]

/-- The charge fold of a costed bind is the charge fold of the step-prefixed tree followed by the
charge folds of the continuation. -/
theorem wpFold_stepToFreeMT_bindT (hA : ∀ n, allows (.inr n) PUnit.unit) {α β : Type}
    (x : ℕ × SPTree.Timed α) (f : α → ℕ × SPTree.Timed β) (post : β → ℕ∞) :
    wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (stepToFreeMT (bindT x f)) post =
      wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows) (stepToFreeMT x)
        fun a => wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
          (stepToFreeMT (f a)) post := by
  have hb := SPTree.Timed.wpFold_stepToFreeMT_bind allows hA x.2 f post
  rw [SPTree.Timed.wpFold_chargeUnder_stepToFreeMT allows hA, wpFold_bind'] at hb
  rw [SPTree.Timed.wpFold_chargeUnder_stepToFreeMT allows hA,
    SPTree.Timed.wpFold_chargeUnder_stepToFreeMT allows hA]
  simp only [bindT, SPTree.Timed.delay, Nat.cast_add, add_assoc, hb]
  rfl

/-- The bind of open trees, interpreted, has the charge folds of the costed bind. -/
theorem oeq_bindO (hA : ∀ n, allows (.inr n) PUnit.unit)
    (impl : (c : (CallSig Γ₀).A) → FreeM SPSigT ((CallSig Γ₀).B c)) {α β : Type}
    {X : FreeM (OSig Γ₀) α} {x : ℕ × SPTree.Timed α} {F : α → FreeM (OSig Γ₀) β}
    {f : α → ℕ × SPTree.Timed β} (hX : OEq allows (X.liftM (callHandler impl)) x)
    (hF : ∀ a, OEq allows ((F a).liftM (callHandler impl)) (f a)) :
    OEq allows ((X.bind F).liftM (callHandler impl)) (bindT x f) := by
  intro post
  rw [show (X.bind F).liftM (callHandler impl) =
      (X.liftM (callHandler impl)).bind fun a => (F a).liftM (callHandler impl) from
      PFunctor.FreeM.liftM_bind (interp := callHandler impl) X F, wpFold_bind',
    wpFold_stepToFreeMT_bindT hA, ← hX]
  congr 1
  funext a
  exact hF a post

/-- A tick in front of an open tree, interpreted, has the charge folds of the step cost in front
of the costed tree. -/
theorem oeq_delayO (hA : ∀ n, allows (.inr n) PUnit.unit)
    (impl : (c : (CallSig Γ₀).A) → FreeM SPSigT ((CallSig Γ₀).B c)) {α : Type}
    {X : FreeM (OSig Γ₀) α} {x : ℕ × SPTree.Timed α} (c : ℕ)
    (hX : OEq allows (X.liftM (callHandler impl)) x) :
    OEq allows ((delayO c X).liftM (callHandler impl)) (SPTree.Timed.delay c x) := by
  intro post
  have h1 : (delayO c X).liftM (callHandler impl) =
      FreeM.liftBind (P := SPSigT) (Sum.inr c) fun _ => X.liftM (callHandler impl) := rfl
  rw [h1, wpFold_chargeUnder_liftBind_const _ allows _ (hA c), hX,
    SPTree.Timed.wpFold_chargeUnder_stepToFreeMT allows hA,
    SPTree.Timed.wpFold_chargeUnder_stepToFreeMT allows hA]
  simp only [SPTree.Timed.delay, Nat.cast_add, add_assoc, tickCost]

/-- An open environment related to a translated one: the same entries at the variables that are
not of function type, and at each function variable and argument an open tree whose
interpretation has the charge folds of the entry. -/
structure EnvORel (allows : (a : SPSigT.A) → SPSigT.B a → Prop)
    (impl : (c : (CallSig Γ₀).A) → FreeM SPSigT ((CallSig Γ₀).B c)) {Δ : List Ty}
    (e : EnvO Γ₀ Δ) (η : EnvHat Δ) : Prop where
  data : ∀ τ (x : Var Δ τ), τ.isArr = false → η τ x = e.close τ x
  call : ∀ a b (x : Var Δ (.arr a b)) (u : a.hat),
    OEq allows ((e _ x u).liftM (callHandler impl)) (η _ x u)

/-- Related environments stay related when extended by the same translated value. -/
theorem EnvORel.cons {impl : (c : (CallSig Γ₀).A) → FreeM SPSigT ((CallSig Γ₀).B c)}
    {Δ : List Ty} {σ : Ty} {e : EnvO Γ₀ Δ} {η : EnvHat Δ} (h : EnvORel allows impl e η)
    (u : σ.hat) : EnvORel allows impl (e.cons u) (η.cons u) where
  data τ x hx := by
    cases x with
    | here => exact Ty.ofHat_eq_closeO_ofHatO hx u
    | there y => exact h.data _ y hx
  call a b x v := by
    cases x with
    | here => exact oeq_embO impl _
    | there y => exact h.call _ _ y v

/-- The open environment of a translated environment is related to it at the handler of the call
tokens by its entries. -/
theorem EnvORel.ofEnvHat (η : EnvHat Γ₀) : EnvORel allows η.callImpl (EnvO.ofEnvHat η) η where
  data τ x hx := by cases τ <;> first | rfl | simp [Ty.isArr] at hx
  call a b x v := by
    intro post
    change wpFold _ ((callO x v).liftM _) post = _
    exact congrArg (fun X => wpFold _ X post)
      (PFunctor.FreeM.liftM_lift (callHandler η.callImpl) _)

end OEq

/-! ## The open costed tree -/

namespace Tm

/-- The open costed tree of a term: `Tm.dtC` with the costed bind read as the bind of `FreeM`,
step costs as tick nodes, and a call of a function variable as its open entry behind `cc a`
ticks. An abstraction and a tabulation, whose bodies in the fragment call no function variable,
are the closed trees at the closed environment. -/
noncomputable def dtO (cc : Ty → ℕ) {Γ₀ : List Ty} :
    {Δ : List Ty} → {τ : Ty} → Tm Δ τ → EnvO Γ₀ Δ → FreeM (OSig Γ₀) τ.hat
  | _, τ, .var x, e => embO (τ.read (e.close τ x))
  | _, _, .lam body, e => embO ((Tm.lam body).dtC cc e.close)
  | _, _, .app (a := a) f x, e =>
    match f.headVar? with
    | some y => (x.dtO cc e).bind fun u => delayO (cc a) (e _ y u)
    | none => (f.dtO cc e).bind fun p => (x.dtO cc e).bind fun u => embO (1 + p.2 u, .ret (p.1 u))
  | _, _, .letE e' b, e => (e'.dtO cc e).bind fun u => b.dtO cc (e.cons u)
  | _, _, .seq e' b, e => (e'.dtO cc e).bind fun _ => b.dtO cc e
  | _, _, .natLit n, _ => embO (0, .ret n)
  | _, _, .lit _ v, _ => embO (0, .ret v)
  | _, _, .prim p x, e => (x.dtO cc e).bind fun u => embO (1, .ret (p.applyHat u))
  | _, _, .pair x y, e =>
    (x.dtO cc e).bind fun u => (y.dtO cc e).bind fun w => embO (0, .ret (u, w))
  | _, _, .fst p, e => (p.dtO cc e).bind fun u => embO (0, .ret u.1)
  | _, _, .snd p, e => (p.dtO cc e).bind fun u => embO (0, .ret u.2)
  | _, _, .inl (a := a) (b := b) x, e =>
    (x.dtO cc e).bind fun u => embO (0, .ret (Sum.inl u : a.hat ⊕ b.hat))
  | _, _, .inr (a := a) (b := b) x, e =>
    (x.dtO cc e).bind fun u => embO (0, .ret (Sum.inr u : a.hat ⊕ b.hat))
  | _, _, .case (a := a) (b := b) s l r, e =>
    (s.dtO cc e).bind fun (u : a.hat ⊕ b.hat) =>
      delayO 1 (Sum.elim (fun x => l.dtO cc (e.cons x)) (fun y => r.dtO cc (e.cons y)) u)
  | _, _, .ite c t f, e =>
    (c.dtO cc e).bind fun (b : Bool) => delayO 1 (bif b then t.dtO cc e else f.dtO cc e)
  | _, _, .nil (a := a), _ => embO (0, .ret ([] : List a.hat))
  | _, _, .cons (a := a) x xs, e =>
    (x.dtO cc e).bind fun u => (xs.dtO cc e).bind fun (l : List a.hat) => embO (0, .ret (u :: l))
  | _, _, .lcase (a := a) xs n c, e =>
    (xs.dtO cc e).bind fun (l : List a.hat) => delayO 1
      (match l with
        | [] => n.dtO cc e
        | x :: l' => c.dtO cc ((e.cons (σ := .list a) l').cons x))
  | _, _, .foldl (a := a) (c := c) f i xs, e =>
    (f.dtO cc e).bind fun (p : Ty.hat (.arr (.prod c a) c)) => (i.dtO cc e).bind fun acc =>
      (xs.dtO cc e).bind fun (l : List a.hat) =>
        embO (List.foldl.timedCost (fun x y => p.1 (x, y)) (fun x y => p.2 (x, y)) acc l,
          .ret (List.foldl (fun x y => p.1 (x, y)) acc l))
  | _, _, .iter (c := c) n f i, e =>
    (n.dtO cc e).bind fun (k : ℕ) => (f.dtO cc e).bind fun (p : Ty.hat (.arr c c)) =>
      (i.dtO cc e).bind fun acc => embO (iterCost p acc k, .ret (p.1^[k] acc))
  | _, _, .sample f, _ =>
    embO (0, .sample f.den (FTy.instFintype f) (FTy.instNonempty f) (fun _ => 0) fun v => .ret v)
  | _, _, .get n f, _ => embO (0, .get (f.loc n) (fun _ => 0) fun v => .ret v)
  | _, _, .set n f x, e => (x.dtO cc e).bind fun u => embO (0, .set (f.loc n) u 0 (.ret ()))
  | _, _, .query _ r x, e => (x.dtO cc e).bind fun _ =>
    embO (0, .sample r.den (FTy.instFintype r) (FTy.instNonempty r) (fun _ => 0) fun v => .ret v)
  | _, _, .fail, _ => embO (0, .fail)
  | _, _, .con (S := S) x, e => (x.dtO cc e).bind fun u =>
    embO (0, .ret (conHat S (fun a k => (WType.mk a k : Ty.hat (.mu S))) u))
  | _, _, .fold g x, e => (g.dtO cc e).bind fun p => (x.dtO cc e).bind fun w =>
    embO (1 + (foldHat p w).2, .ret (foldHat p w).1)
  | _, _, .icon (f := f) (S := S) (i := i) x, e => (x.dtO cc e).bind fun u =>
    embO (0, .ret (conHatI (X := fun j => .imu f S j) (S i)
      (fun a k => (Container.IPW.mk i a k : Ty.hat (.imu f S i))) u))
  | _, _, .ifold (c := c) g x, e => (g.dtO cc e).bind fun p => (x.dtO cc e).bind fun w =>
    embO (1 + (foldHatI (c := c) p w).2, .ret (foldHatI (c := c) p w).1)
  | _, _, .ptab ts, e => embO ((Tm.ptab ts).dtC cc e.close)
  | _, _, .papp (B := B) t j, e =>
    (t.dtO cc e).bind fun (u : (j : _) → (B j).hat) => embO (0, .ret (u j))
  | _, _, .spair (f := f) (B := B) j x, e =>
    (x.dtO cc e).bind fun u => embO (0, .ret (⟨j, u⟩ : (j : f.den) × (B j).hat))
  | _, _, .scase (f := f) (B := B) s ks, e =>
    (s.dtO cc e).bind fun (u : (j : f.den) × (B j).hat) =>
      delayO 1 ((ks u.1).dtO cc (e.cons u.2))
  | _, _, .fcase (f := f) i ks, e =>
    (i.dtO cc e).bind fun (j : f.den) => delayO 1 ((ks j).dtO cc e)

/-! ## Pure terms read only the data entries -/

/-- The costed tree of a pure term of the fragment reads only the entries of the variables that
are not of function type. -/
theorem dtC_congr (cc : Ty → ℕ) {Δ : List Ty} {τ : Ty} (t : Tm Δ τ) :
    t.InDtFrag → t.Pure → ∀ {η η' : EnvHat Δ}, η.AgreeData η' → t.dtC cc η = t.dtC cc η' := by
  induction t with
  | var x => intro _ hp η η' h; exact congrArg (Ty.read _) (h _ x hp)
  | lam body ih =>
    intro ht _ η η' h
    have hb : ∀ u, body.dtC cc (η.cons u) = body.dtC cc (η'.cons u) :=
      fun u => ih ht.1 ht.2 (h.cons u)
    simp only [dtC, hb]
  | app f x ihf ihx =>
    intro ht hp η η' h
    have hf : f.InDtFrag := by simpa [hp.1] using ht.1
    simp only [dtC, hp.1, ihf hf hp.2.1 h, ihx ht.2 hp.2.2 h]
  | letE e b ihe ihb =>
    intro ht hp η η' h
    have hb : ∀ u, b.dtC cc (η.cons u) = b.dtC cc (η'.cons u) :=
      fun u => ihb ht.2 hp.2 (h.cons u)
    simp only [dtC, ihe ht.1 hp.1 h, hb]
  | seq e b ihe ihb =>
    intro ht hp η η' h
    simp only [dtC, ihe ht.1 hp.1 h, ihb ht.2 hp.2 h]
  | natLit n => intro _ _ η η' _; rfl
  | lit f v => intro _ _ η η' _; rfl
  | prim p x ih => intro ht hp η η' h; simp only [dtC, ih ht.2 hp h]
  | pair x y ihx ihy => intro ht hp η η' h; simp only [dtC, ihx ht.1 hp.1 h, ihy ht.2 hp.2 h]
  | fst p ih => intro ht hp η η' h; simp only [dtC, ih ht hp h]
  | snd p ih => intro ht hp η η' h; simp only [dtC, ih ht hp h]
  | inl x ih => intro ht hp η η' h; simp only [dtC, ih ht hp h]
  | inr x ih => intro ht hp η η' h; simp only [dtC, ih ht hp h]
  | case s l r ihs ihl ihr =>
    intro ht hp η η' h
    have hl : ∀ u, l.dtC cc (η.cons u) = l.dtC cc (η'.cons u) :=
      fun u => ihl ht.2.1 hp.2.1 (h.cons u)
    have hr : ∀ u, r.dtC cc (η.cons u) = r.dtC cc (η'.cons u) :=
      fun u => ihr ht.2.2 hp.2.2 (h.cons u)
    simp only [dtC, ihs ht.1 hp.1 h, hl, hr]
  | ite c t e ihc iht ihe =>
    intro ht hp η η' h
    simp only [dtC, ihc ht.1 hp.1 h, iht ht.2.1 hp.2.1 h, ihe ht.2.2 hp.2.2 h]
  | nil => intro _ _ η η' _; rfl
  | cons x xs ihx ihxs =>
    intro ht hp η η' h; simp only [dtC, ihx ht.1 hp.1 h, ihxs ht.2 hp.2 h]
  | lcase xs n c ihxs ihn ihc =>
    intro ht hp η η' h
    have hc : ∀ x l', c.dtC cc ((η.cons l').cons x) = c.dtC cc ((η'.cons l').cons x) :=
      fun x l' => ihc ht.2.2 hp.2.2 ((h.cons l').cons x)
    simp only [dtC, ihxs ht.1 hp.1 h, ihn ht.2.1 hp.2.1 h]
    congr 1
    funext l
    cases l with
    | nil => rfl
    | cons x l' => exact congrArg _ (hc x l')
  | foldl f i xs ihf ihi ihxs =>
    intro ht hp η η' h
    simp only [dtC, ihf ht.1 hp.1 h, ihi ht.2.1 hp.2.1 h, ihxs ht.2.2 hp.2.2 h]
  | iter n f i ihn ihf ihi =>
    intro ht hp η η' h
    simp only [dtC, ihn ht.1 hp.1 h, ihf ht.2.1 hp.2.1 h, ihi ht.2.2 hp.2.2 h]
  | sample f => intro _ hp; exact hp.elim
  | get n f => intro _ hp; exact hp.elim
  | set n f x _ => intro _ hp; exact hp.elim
  | query d r x _ => intro _ hp; exact hp.elim
  | fail => intro _ hp; exact hp.elim
  | con x ih => intro ht hp η η' h; simp only [dtC, ih ht hp h]
  | fold g x ihg ihx => intro ht hp η η' h; simp only [dtC, ihg ht.1 hp.1 h, ihx ht.2 hp.2 h]
  | icon x ih => intro ht hp η η' h; simp only [dtC, ih ht hp h]
  | ifold g x ihg ihx => intro ht hp η η' h; simp only [dtC, ihg ht.1 hp.1 h, ihx ht.2 hp.2 h]
  | ptab ts ih =>
    intro ht hp η η' h
    have hts : ∀ j, (ts j).dtC cc η = (ts j).dtC cc η' := fun j => ih j (ht j).1 (hp j) h
    simp only [dtC, hts]
  | papp t j ih => intro ht hp η η' h; simp only [dtC, ih ht hp h]
  | spair j x ih => intro ht hp η η' h; simp only [dtC, ih ht hp h]
  | scase s ks ihs ihks =>
    intro ht hp η η' h
    have hks : ∀ j u, (ks j).dtC cc (η.cons u) = (ks j).dtC cc (η'.cons u) :=
      fun j u => ihks j (ht.2 j) (hp.2 j) (h.cons u)
    simp only [dtC, ihs ht.1 hp.1 h, hks]
  | fcase i ks ihi ihks =>
    intro ht hp η η' h
    have hks : ∀ j, (ks j).dtC cc η = (ks j).dtC cc η' := fun j => ihks j (ht.2 j) (hp.2 j) h
    simp only [dtC, ihi ht.1 hp.1 h, hks]

/-! ## Interpretation of the call tokens -/

variable {Γ₀ : List Ty} {allows : (a : SPSigT.A) → SPSigT.B a → Prop}

/-- In related environments, the open tree of a term of the fragment, interpreted by the call
handler, has the charge folds of its closed tree. -/
theorem dtO_oeq (cc : Ty → ℕ) (hA : ∀ n, allows (.inr n) PUnit.unit)
    (impl : (c : (CallSig Γ₀).A) → FreeM SPSigT ((CallSig Γ₀).B c)) {Δ : List Ty} {τ : Ty}
    (t : Tm Δ τ) : t.InDtFrag → ∀ {e : EnvO Γ₀ Δ} {η : EnvHat Δ}, EnvORel allows impl e η →
      OEq allows ((t.dtO cc e).liftM (callHandler impl)) (t.dtC cc η) := by
  induction t with
  | @var _ τ x =>
    intro ht e η h
    change OEq allows ((embO (τ.read (e.close τ x))).liftM _) (τ.read (η τ x))
    rw [h.data _ x ht]
    exact oeq_embO impl _
  | lam body _ =>
    intro ht e η h
    change OEq allows ((embO ((Tm.lam body).dtC cc e.close)).liftM _) ((Tm.lam body).dtC cc η)
    rw [dtC_congr cc (Tm.lam body) ht trivial (η' := e.close) fun τ x hx => h.data τ x hx]
    exact oeq_embO impl _
  | app f x ihf ihx =>
    intro ht e η h
    cases hv : f.headVar? with
    | some y =>
      obtain rfl := eq_var_of_headVar? hv
      exact oeq_bindO hA impl (ihx ht.2 h) fun u => oeq_delayO hA impl _ (h.call _ _ y u)
    | none =>
      have hf : f.InDtFrag := by simpa [hv] using ht.1
      simp only [dtO, dtC, hv]
      exact oeq_bindO hA impl (ihf hf h) fun _ =>
        oeq_bindO hA impl (ihx ht.2 h) fun _ => oeq_embO impl _
  | letE e' b ihe ihb =>
    intro ht e η h
    exact oeq_bindO hA impl (ihe ht.1 h) fun u => ihb ht.2 (h.cons u)
  | seq e' b ihe ihb =>
    intro ht e η h
    exact oeq_bindO hA impl (ihe ht.1 h) fun _ => ihb ht.2 h
  | natLit n => intro _ e η _; exact oeq_embO impl _
  | lit f v => intro _ e η _; exact oeq_embO impl _
  | prim p x ih =>
    intro ht e η h
    exact oeq_bindO hA impl (ih ht.2 h) fun _ => oeq_embO impl _
  | pair x y ihx ihy =>
    intro ht e η h
    exact oeq_bindO hA impl (ihx ht.1 h) fun _ =>
      oeq_bindO hA impl (ihy ht.2 h) fun _ => oeq_embO impl _
  | fst p ih => intro ht e η h; exact oeq_bindO hA impl (ih ht h) fun _ => oeq_embO impl _
  | snd p ih => intro ht e η h; exact oeq_bindO hA impl (ih ht h) fun _ => oeq_embO impl _
  | inl x ih => intro ht e η h; exact oeq_bindO hA impl (ih ht h) fun _ => oeq_embO impl _
  | inr x ih => intro ht e η h; exact oeq_bindO hA impl (ih ht h) fun _ => oeq_embO impl _
  | case s l r ihs ihl ihr =>
    intro ht e η h
    refine oeq_bindO hA impl (ihs ht.1 h) fun u => oeq_delayO hA impl 1 ?_
    cases u with
    | inl x => exact ihl ht.2.1 (h.cons x)
    | inr y => exact ihr ht.2.2 (h.cons y)
  | ite c t f ihc iht ihf =>
    intro ht e η h
    refine oeq_bindO hA impl (ihc ht.1 h) fun b => oeq_delayO hA impl 1 ?_
    cases b with
    | false => exact ihf ht.2.2 h
    | true => exact iht ht.2.1 h
  | nil => intro _ e η _; exact oeq_embO impl _
  | cons x xs ihx ihxs =>
    intro ht e η h
    exact oeq_bindO hA impl (ihx ht.1 h) fun _ =>
      oeq_bindO hA impl (ihxs ht.2 h) fun _ => oeq_embO impl _
  | lcase xs n c ihxs ihn ihc =>
    intro ht e η h
    refine oeq_bindO hA impl (ihxs ht.1 h) fun l => oeq_delayO hA impl 1 ?_
    cases l with
    | nil => exact ihn ht.2.1 h
    | cons x l' => exact ihc ht.2.2 ((h.cons (σ := .list _) l').cons x)
  | foldl f i xs ihf ihi ihxs =>
    intro ht e η h
    exact oeq_bindO hA impl (ihf ht.1 h) fun _ => oeq_bindO hA impl (ihi ht.2.1 h) fun _ =>
      oeq_bindO hA impl (ihxs ht.2.2 h) fun _ => oeq_embO impl _
  | iter n f i ihn ihf ihi =>
    intro ht e η h
    exact oeq_bindO hA impl (ihn ht.1 h) fun _ => oeq_bindO hA impl (ihf ht.2.1 h) fun _ =>
      oeq_bindO hA impl (ihi ht.2.2 h) fun _ => oeq_embO impl _
  | sample f => intro _ e η _; exact oeq_embO impl _
  | get n f => intro _ e η _; exact oeq_embO impl _
  | set n f x ih => intro ht e η h; exact oeq_bindO hA impl (ih ht h) fun _ => oeq_embO impl _
  | query d r x ih => intro ht e η h; exact oeq_bindO hA impl (ih ht h) fun _ => oeq_embO impl _
  | fail => intro _ e η _; exact oeq_embO impl _
  | con x ih => intro ht e η h; exact oeq_bindO hA impl (ih ht h) fun _ => oeq_embO impl _
  | fold g x ihg ihx =>
    intro ht e η h
    exact oeq_bindO hA impl (ihg ht.1 h) fun _ =>
      oeq_bindO hA impl (ihx ht.2 h) fun _ => oeq_embO impl _
  | icon x ih => intro ht e η h; exact oeq_bindO hA impl (ih ht h) fun _ => oeq_embO impl _
  | ifold g x ihg ihx =>
    intro ht e η h
    exact oeq_bindO hA impl (ihg ht.1 h) fun _ =>
      oeq_bindO hA impl (ihx ht.2 h) fun _ => oeq_embO impl _
  | ptab ts _ =>
    intro ht e η h
    change OEq allows ((embO ((Tm.ptab ts).dtC cc e.close)).liftM _) ((Tm.ptab ts).dtC cc η)
    rw [dtC_congr cc (Tm.ptab ts) ht (fun j => (ht j).2) (η' := e.close)
      fun τ x hx => h.data τ x hx]
    exact oeq_embO impl _
  | papp t j ih => intro ht e η h; exact oeq_bindO hA impl (ih ht h) fun _ => oeq_embO impl _
  | spair j x ih => intro ht e η h; exact oeq_bindO hA impl (ih ht h) fun _ => oeq_embO impl _
  | scase s ks ihs ihks =>
    intro ht e η h
    exact oeq_bindO hA impl (ihs ht.1 h) fun u =>
      oeq_delayO hA impl 1 (ihks u.1 (ht.2 u.1) (h.cons u.2))
  | fcase i ks ihi ihks =>
    intro ht e η h
    exact oeq_bindO hA impl (ihi ht.1 h) fun j => oeq_delayO hA impl 1 (ihks j (ht.2 j) h)

/-- **The interpretation theorem.** The closed costed tree of a term of the fragment has the
charge folds of its open tree with the call tokens interpreted by the entries of the function
variables, at every postcondition and every reading of the answers that admits the ticks. -/
theorem wpFold_dtC_eq_liftM_dtO (cc : Ty → ℕ) {τ : Ty} (t : Tm Γ₀ τ) (ht : t.InDtFrag)
    (η : EnvHat Γ₀) (hA : ∀ n, allows (.inr n) PUnit.unit) (post : τ.hat → ℕ∞) :
    wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (stepToFreeMT (t.dtC cc η)) post =
      wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        ((t.dtO cc (EnvO.ofEnvHat η)).liftM (callHandler η.callImpl)) post :=
  (dtO_oeq cc hA η.callImpl t ht (EnvORel.ofEnvHat η) post).symm

/-- **The use bound of a D-term.** A use bound `u` of the open tree of a term of the fragment, at
the resource map `ρc` of its call tokens, and bounds `T` on the charge folds of the entries of
the function variables bound the cost of its evaluation in related environments: the allowance,
the tick component of the use bound, and per resource its use count times its time bound. -/
theorem cost_le_of_useBound (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) {τ : Ty} (t : Tm Γ₀ τ)
    (ht : t.InDtFrag) {κ : Type} [Fintype κ] [DecidableEq κ] (ρc : (CallSig Γ₀).A → κ)
    {η : EnvHat Γ₀} {ρ : Env Γ₀} (hρ : SimEnv η ρ) (u : Option κ → ℕ) (T : κ → ℕ)
    (hu : UseBound (openCharge tickCost ρc) (openAllows fun _ _ => True)
      (t.dtO cc (EnvO.ofEnvHat η)) fun j => u j)
    (hT : ∀ c, wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) fun _ _ => True)
      (η.callImpl c) (fun _ => 0) ≤ T (ρc c)) :
    (t.eval ρ).cost ≤ t.allowC cc + (u none + ∑ i, u (some i) * T i) := by
  have h1 := (dtC_timedSim cc hcc t ht hρ).cost_le
  have h2 : SPTree.Timed.stepTime (t.dtC cc η) ≤ u none + ∑ i, u (some i) * T i := by
    refine SPTree.Timed.stepTime_le_of_wpFold_le _ _ ?_
    rw [← OpSpec.chargeUnder_true,
      wpFold_dtC_eq_liftM_dtO cc t ht η (allows := fun _ _ => True) (fun _ => trivial)]
    refine (wpFold_liftM_callHandler_le tickCost ρc (fun _ _ => True) hu η.callImpl
      (fun i => T i) hT).trans ?_
    push_cast
    simp [mul_comm]
  omega

end Tm

/-! ## Substitution of callees and `Clocked.comp` -/

section Subst

variable {Γ₀ : List Ty}

/-- The substitution handler: an operation of a costed tree is kept, a call token `c` runs the
open tree `impl c` of a callee. -/
def substHandler (impl : (c : (CallSig Γ₀).A) → FreeM (OSig Γ₀) ((CallSig Γ₀).B c)) :
    Handler (FreeM (OSig Γ₀)) (OSig Γ₀) :=
  Handler.sum (fun a => FreeM.lift (P := OSig Γ₀) (Sum.inl a)) impl

/-- The clocked charge of an open tree: an operation of a costed tree charges its ticks at the
clock (`true`), a call token one use (`false`). -/
def clockCharge : (OSig Γ₀).A → Bool → ℕ∞
  | .inl a => Pi.single true (tickCost a : ℕ∞)
  | .inr _ => Pi.single false 1

/-- **`Clocked.comp` as substitution.** If the open tree `x` (for instance `t.dtO cc e`) uses
its call tokens `g.uses` times at cost `g.cost` at `f.fn a₀`, and the open callee substituted at
every call token has the use vector of `f` at `a₀`, then the substituted tree has the use vector
of `Clocked.comp g f` at `a₀`: uses `n₂ * n₁`, cost `c₂ + n₂ * c₁`. -/
theorem useBound_liftM_substHandler_clocked {X Y Z : Type*} {α : Type}
    (x : FreeM (OSig Γ₀) α)
    (impl : (c : (CallSig Γ₀).A) → FreeM (OSig Γ₀) ((CallSig Γ₀).B c))
    (g : Clocked Y Z) (f : Clocked X Y) (a₀ : X)
    (hx : UseBound clockCharge (fun _ _ => True) x (g.useVec (f.fn a₀)))
    (himpl : ∀ c, UseBound clockCharge (fun _ _ => True) (impl c) (f.useVec a₀)) :
    UseBound clockCharge (fun _ _ => True) (x.liftM (substHandler impl))
      ((Clocked.comp g f).useVec a₀) := by
  refine useBound_liftM_clocked g f a₀ hx ?_ fun _ =>
    FreeM.wpFold_demonicUnder_true _ _
  rintro (a | c)
  · change wpFold _ (FreeM.lift (P := OSig Γ₀) (Sum.inl a)) (fun _ => 0) ≤ _
    rw [wpFold_lift, OpSpec.chargeUnder_apply]
    refine le_of_eq ?_
    funext b
    cases b <;> simp [clockCharge, Clocked.callDemand]
  · refine (himpl c).trans (le_of_eq ?_)
    funext b
    cases b <;> simp [clockCharge, Clocked.callDemand]

end Subst

end CatCrypt.Complexity.D
