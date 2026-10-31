/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Nat.Notation

/-!
# The party language, parametric in its effect

A party with input events `E` and outputs `O` is a first-order program tree
`Party.ProgE Op E O α` over the effect signature `Op`: it returns, waits for the next activation
(`recv`), emits the output of the current activation (`send`), performs an effect operation
`q : Op` and continues with its outcome (`opN`), or fails. Outcomes are codes in `ℕ`, so the
tree lives in `Type` whatever the effect. Programs form a lawful monad.

The party language has two instances. The classical language `Party.Prog E O` is the instance at
sampling, `Op = SPComp ℕ`; the quantum language `Party.QProg R E O` is the instance at the
subinstruments `Op = SubInstrument R R ℕ` on the register `R`. Both are abbreviations of
`ProgE`, so every definition and theorem of this module applies to both.

A program is interpreted in a monad `M` with failure through a handler `Handler Op M`, which runs
an effect operation as a computation of `M` on codes. An activation on the event `e` runs the
residual program in two phases: in the await phase (`ProgE.awaitK`) it performs the operations
up to the next `recv` and feeds it `e`; in the emit phase (`ProgE.emitK`) it performs the
operations up to the next `send o` and stops there with the output `o`. Both phases commute with
`bind` (`ProgE.emitK_bind`, `ProgE.awaitK_bind`). The classical interpretation is the handler in
`SPComp`, the quantum one the handler in `SubInstrument R R`; the classical lift of a classical
program to the register `R` is its interpretation through the quantum handler precomposed with
the diagonal subinstrument of a sample (`Handler.comap`). A map of effect signatures acts on
programs (`ProgE.mapOp`), and interpreting the mapped program is interpreting the program through
the precomposed handler (`ProgE.emitK_mapOp`, `ProgE.awaitK_mapOp`).

The parallel composition `ProgE.par p q` waits for an event and runs one activation of the
program on its side. For a lawful handler its activation is the activation of that side
(`ProgE.act_par_inl`, `ProgE.act_par_inr`).

## Main definitions

* `Party.ProgE Op E O α`: party programs over the effect `Op`, with `Monad (ProgE Op E O)`.
* `Party.Handler Op M`, `Party.Handler.comap`, `Party.Handler.Lawful`.
* `Party.ProgE.emitK`, `Party.ProgE.awaitK`, `Party.ProgE.stepWith`, `Party.ProgE.act`.
* `Party.ProgE.mapOp`: the action of a map of effect signatures.
* `Party.ProgE.Child`, `Party.ProgE.par`: the immediate-subprogram relation and the parallel
  composition.

## Main results

* `Party.ProgE.emitK_bind`, `Party.ProgE.awaitK_bind`: the phases respect `bind`.
* `Party.ProgE.mapOp_bind`, `Party.ProgE.emitK_mapOp`, `Party.ProgE.awaitK_mapOp`,
  `Party.ProgE.act_mapOp`: interpreting a mapped program.
* `Party.ProgE.act_par_inl`, `Party.ProgE.act_par_inr`: activations of the parallel composition.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

/-- Programs of a party over the effect signature `Op`, with input events `E` and outputs `O`,
returning `α`. -/
inductive ProgE (Op : Type) (E O : Type) (α : Type) : Type where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Wait for the next activation and continue with its event. -/
  | recv (k : E → ProgE Op E O α)
  /-- Emit `o` as the output of the current activation and continue. -/
  | send (o : O) (k : ProgE Op E O α)
  /-- Perform the effect operation `q` and continue with its outcome code. -/
  | opN (q : Op) (k : ℕ → ProgE Op E O α)
  /-- Failure. -/
  | fail

/-- An interpretation of the effect signature `Op` in the monad `M` with failure: `run q` is the
computation of the operation `q` on outcome codes. -/
structure Handler (Op : Type) (M : Type → Type) : Type 1 where
  /-- The return of `M`. -/
  pure : {γ : Type} → γ → M γ
  /-- The sequencing of `M`. -/
  bind : {β γ : Type} → M β → (β → M γ) → M γ
  /-- The failure of `M`. -/
  fail : {γ : Type} → M γ
  /-- The computation of an effect operation. -/
  run : Op → M ℕ

namespace Handler

variable {Op Op' : Type} {M : Type → Type}

/-- The handler `H` precomposed with the map of effect signatures `f`. -/
def comap (H : Handler Op M) (f : Op' → Op) : Handler Op' M where
  pure := H.pure
  bind := H.bind
  fail := H.fail
  run q := H.run (f q)

/-- A lawful handler: `pure` is a left unit of `bind`, `bind` is associative and failure is a
left zero. -/
structure Lawful (H : Handler Op M) : Prop where
  /-- `pure` is a left unit. -/
  pure_bind : ∀ {β γ : Type} (a : β) (f : β → M γ), H.bind (H.pure a) f = f a
  /-- `bind` is associative. -/
  bind_assoc : ∀ {β γ δ : Type} (c : M β) (f : β → M γ) (g : γ → M δ),
    H.bind (H.bind c f) g = H.bind c fun b => H.bind (f b) g
  /-- Failure is a left zero. -/
  fail_bind : ∀ {β γ : Type} (f : β → M γ), H.bind H.fail f = H.fail

end Handler

namespace ProgE

variable {Op Op' : Type} {M : Type → Type} {E O E' O' α β γ σ : Type}

/-- Sequential composition of programs. -/
def bind : ProgE Op E O α → (α → ProgE Op E O β) → ProgE Op E O β
  | .ret a, f => f a
  | .recv k, f => .recv fun e => (k e).bind f
  | .send o p, f => .send o (p.bind f)
  | .opN q k, f => .opN q fun n => (k n).bind f
  | .fail, _ => .fail

instance : Monad (ProgE Op E O) where
  pure := .ret
  bind := bind

/-- Unfolding lemma of the monad instance: `pure` is `ProgE.ret`. -/
@[simp] theorem pure_eq (a : α) : (pure a : ProgE Op E O α) = .ret a := rfl

/-- Unfolding lemma of the monad instance: `>>=` is `ProgE.bind`. -/
@[simp] theorem bind_eq (p : ProgE Op E O α) (f : α → ProgE Op E O β) : p >>= f = p.bind f :=
  rfl

/-- Unfolding lemma of the monad instance: `<$>` is `ProgE.bind` followed by a return. -/
@[simp] theorem map_eq (f : α → β) (p : ProgE Op E O α) :
    f <$> p = p.bind fun a => .ret (f a) := rfl

/-- `bind` returning its argument is the identity. -/
theorem bind_ret (p : ProgE Op E O α) : p.bind .ret = p := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [bind, ih]
  | send o p ih => simp only [bind, ih]
  | opN q k ih => simp only [bind, ih]
  | fail => rfl

/-- `bind` is associative. -/
theorem bind_assoc (p : ProgE Op E O α) (f : α → ProgE Op E O β) (g : β → ProgE Op E O γ) :
    (p.bind f).bind g = p.bind fun a => (f a).bind g := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [bind, ih]
  | send o p ih => simp only [bind, ih]
  | opN q k ih => simp only [bind, ih]
  | fail => rfl

instance : LawfulMonad (ProgE Op E O) := LawfulMonad.mk'
  (id_map := fun p => bind_ret p)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun p f g => bind_assoc p f g)

/-- Wait for the next activation and return its event. -/
def recvE : ProgE Op E O E := .recv .ret

/-- Emit `o` as the output of the current activation. -/
def sendE (o : O) : ProgE Op E O Unit := .send o (.ret ())

/-- The returned state, or `d` at a program that is not a return. -/
def retOr (d : σ) : ProgE Op E O σ → σ
  | .ret s => s
  | _ => d

/-! ## Activations -/

/-- The emit phase through the handler `H`: perform the operations up to the next `send o` and
continue with `s o` at the rest; a return continues with `r`; a `recv` or a failure fails. -/
def emitK (H : Handler Op M) (s : O → ProgE Op E O α → M γ) (r : α → M γ) :
    ProgE Op E O α → M γ
  | .ret a => r a
  | .recv _ => H.fail
  | .send o p => s o p
  | .opN q k => H.bind (H.run q) fun n => emitK H s r (k n)
  | .fail => H.fail

/-- The await phase through the handler `H` on the event `e`: perform the operations up to the
next `recv`, feed it `e` and continue in the emit phase with `s` and `rE`; a return continues
with `rA`; a `send` or a failure fails. -/
def awaitK (H : Handler Op M) (e : E) (s : O → ProgE Op E O α → M γ) (rA rE : α → M γ) :
    ProgE Op E O α → M γ
  | .ret a => rA a
  | .recv k => emitK H s rE (k e)
  | .send _ _ => H.fail
  | .opN q k => H.bind (H.run q) fun n => awaitK H e s rA rE (k n)
  | .fail => H.fail

/-- The emit phase commutes with `bind`: a return of `p` continues with the emit phase of
`f`. -/
theorem emitK_bind (H : Handler Op M) (s : O → ProgE Op E O β → M γ) (r : β → M γ)
    (p : ProgE Op E O α) (f : α → ProgE Op E O β) :
    emitK H s r (p.bind f) =
      emitK H (fun o q => s o (q.bind f)) (fun a => emitK H s r (f a)) p := by
  induction p with
  | ret a => rfl
  | recv k ih => rfl
  | send o p ih => rfl
  | opN q k ih => simp only [bind, emitK, ih]
  | fail => rfl

/-- The await phase commutes with `bind`: a return of `p` in the await phase continues with the
await phase of `f`, and in the emit phase with the emit phase of `f`. -/
theorem awaitK_bind (H : Handler Op M) (e : E) (s : O → ProgE Op E O β → M γ)
    (rA rE : β → M γ) (p : ProgE Op E O α) (f : α → ProgE Op E O β) :
    awaitK H e s rA rE (p.bind f) =
      awaitK H e (fun o q => s o (q.bind f)) (fun a => awaitK H e s rA rE (f a))
        (fun a => emitK H s rE (f a)) p := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [bind, awaitK, emitK_bind]
  | send o p ih => rfl
  | opN q k ih => simp only [bind, awaitK, ih]
  | fail => rfl

/-- One activation of the program `p` on the event `e` through the handler `H` that continues
with `restart a e` when `p` returns `a` in the await phase: the residual program after the
activation's `send`, and the output. -/
def stepWith (H : Handler Op M) (restart : α → E → M (ProgE Op E O α × O)) (p : ProgE Op E O α)
    (e : E) : M (ProgE Op E O α × O) :=
  awaitK H e (fun o q => H.pure (q, o)) (fun a => restart a e) (fun _ => H.fail) p

/-- One activation of a program that halts on return: an activation after the return fails. -/
def act (H : Handler Op M) (p : ProgE Op E O α) (e : E) : M (ProgE Op E O α × O) :=
  stepWith H (fun _ _ => H.fail) p e

/-- Unfolding lemma of `act`: a receive followed by a send is one step. -/
theorem act_recv_send (H : Handler Op M) (g : E → O) (p : E → ProgE Op E O α) (e : E) :
    act H (.recv fun e => .send (g e) (p e)) e = H.pure (p e, g e) := rfl

/-- For a lawful handler, a continuation after the emit phase moves into its continuations. -/
theorem bind_emitK (H : Handler Op M) (hH : H.Lawful) (s : O → ProgE Op E O α → M γ)
    (r : α → M γ) (g : γ → M β) (p : ProgE Op E O α) :
    H.bind (emitK H s r p) g =
      emitK H (fun o q => H.bind (s o q) g) (fun a => H.bind (r a) g) p := by
  induction p with
  | opN q k ih => simp only [emitK, hH.bind_assoc, ih]
  | _ => simp only [emitK, hH.fail_bind]

/-- For a lawful handler, a continuation after the await phase moves into its
continuations. -/
theorem bind_awaitK (H : Handler Op M) (hH : H.Lawful) (e : E)
    (s : O → ProgE Op E O α → M γ) (rA rE : α → M γ) (g : γ → M β) (p : ProgE Op E O α) :
    H.bind (awaitK H e s rA rE p) g =
      awaitK H e (fun o q => H.bind (s o q) g) (fun a => H.bind (rA a) g)
        (fun a => H.bind (rE a) g) p := by
  induction p with
  | recv k => exact bind_emitK H hH s rE g (k e)
  | opN q k ih => simp only [awaitK, hH.bind_assoc, ih]
  | _ => simp only [awaitK, hH.fail_bind]

/-- The lawfulness of `H` is that of `H.comap f`. -/
theorem _root_.CatCrypt.Crypto.Party.Handler.Lawful.comap {H : Handler Op' M} (hH : H.Lawful)
    (f : Op → Op') : (H.comap f).Lawful :=
  ⟨hH.pure_bind, hH.bind_assoc, hH.fail_bind⟩

/-! ## Maps of effect signatures -/

/-- The program `p` with each effect operation `q` replaced by `f q`. -/
def mapOp (f : Op → Op') : ProgE Op E O α → ProgE Op' E O α
  | .ret a => .ret a
  | .recv k => .recv fun e => mapOp f (k e)
  | .send o p => .send o (mapOp f p)
  | .opN q k => .opN (f q) fun n => mapOp f (k n)
  | .fail => .fail

/-- A map of effect signatures is a monad morphism. -/
theorem mapOp_bind (f : Op → Op') (p : ProgE Op E O α) (g : α → ProgE Op E O β) :
    mapOp f (p.bind g) = (mapOp f p).bind fun a => mapOp f (g a) := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [bind, mapOp, ih]
  | send o p ih => simp only [bind, mapOp, ih]
  | opN q k ih => simp only [bind, mapOp, ih]
  | fail => rfl

/-- The emit phase of a mapped program is the emit phase through the precomposed handler. -/
theorem emitK_mapOp (H : Handler Op' M) (f : Op → Op') (s : O → ProgE Op' E O α → M γ)
    (r : α → M γ) (p : ProgE Op E O α) :
    emitK H s r (mapOp f p) = emitK (H.comap f) (fun o q => s o (mapOp f q)) r p := by
  induction p with
  | ret a => rfl
  | recv k ih => rfl
  | send o p ih => rfl
  | opN q k ih => simp only [mapOp, emitK, ih, Handler.comap]
  | fail => rfl

/-- The await phase of a mapped program is the await phase through the precomposed handler. -/
theorem awaitK_mapOp (H : Handler Op' M) (f : Op → Op') (e : E)
    (s : O → ProgE Op' E O α → M γ) (rA rE : α → M γ) (p : ProgE Op E O α) :
    awaitK H e s rA rE (mapOp f p) =
      awaitK (H.comap f) e (fun o q => s o (mapOp f q)) rA rE p := by
  induction p with
  | ret a => rfl
  | recv k ih => exact emitK_mapOp H f s rE (k e)
  | send o p ih => rfl
  | opN q k ih => simp only [mapOp, awaitK, ih, Handler.comap]
  | fail => rfl

/-- An activation of a mapped program is the activation through the precomposed handler, its
residual mapped. -/
theorem act_mapOp (H : Handler Op' M) (hH : H.Lawful) (f : Op → Op') (p : ProgE Op E O α)
    (e : E) :
    act H (mapOp f p) e =
      H.bind (act (H.comap f) p e) fun x => H.pure (mapOp f x.1, x.2) := by
  simp only [act, stepWith, awaitK_mapOp]
  refine Eq.trans ?_ (bind_awaitK (H.comap f) (hH.comap f) e _ _ _ _ p).symm
  simp only [Handler.comap, hH.pure_bind, hH.fail_bind]

/-! ## The immediate-subprogram relation -/

/-- `Child c p`: `c` is an immediate subprogram of `p`, a continuation after one operation. -/
inductive Child : ProgE Op E O α → ProgE Op E O α → Prop where
  /-- The continuation of a receive at an event. -/
  | recv (k : E → ProgE Op E O α) (e : E) : Child (k e) (.recv k)
  /-- The continuation of a send. -/
  | send (o : O) (p : ProgE Op E O α) : Child p (.send o p)
  /-- The continuation of an effect operation at an outcome code. -/
  | opN (q : Op) (k : ℕ → ProgE Op E O α) (n : ℕ) : Child (k n) (.opN q k)

/-- The immediate-subprogram relation is well founded. -/
theorem child_wf : WellFounded (@Child Op E O α) := by
  refine ⟨fun p => ?_⟩
  induction p with
  | ret a => exact ⟨_, fun y h => nomatch h⟩
  | recv k ih => exact ⟨_, fun y h => by cases h; exact ih _⟩
  | send o p ih => exact ⟨_, fun y h => by cases h; exact ih⟩
  | opN q k ih => exact ⟨_, fun y h => by cases h; exact ih _⟩
  | fail => exact ⟨_, fun y h => nomatch h⟩

/-- Programs ordered by the immediate-subprogram relation. -/
instance instWellFoundedRelation : WellFoundedRelation (ProgE Op E O α) :=
  ⟨Child, child_wf⟩

/-! ## Parallel composition -/

mutual

/-- **Parallel composition.** Wait for an event and run one activation of the program on its
side; the program on the other side is unchanged. -/
def par (p : ProgE Op E O α) (q : ProgE Op E' O' β) : ProgE Op (E ⊕ E') (O ⊕ O') Empty :=
  .recv fun e => match e with
    | .inl e₁ => parAwL e₁ p q
    | .inr e₂ => parAwR e₂ p q
  termination_by (p, q, 2)
  decreasing_by
    all_goals exact Prod.Lex.right _ (Prod.Lex.right _ (by decide))

/-- The await phase of the left program on the event `e`. -/
def parAwL (e : E) (p : ProgE Op E O α) (q : ProgE Op E' O' β) :
    ProgE Op (E ⊕ E') (O ⊕ O') Empty :=
  match p with
  | .recv k => parEmL (k e) q
  | .opN c k => .opN c fun n => parAwL e (k n) q
  | .ret _ => .fail
  | .send _ _ => .fail
  | .fail => .fail
  termination_by (p, q, 1)
  decreasing_by
    · exact Prod.Lex.left _ _ (Child.recv _ _)
    · exact Prod.Lex.left _ _ (Child.opN _ _ _)

/-- The emit phase of the left program. -/
def parEmL (p : ProgE Op E O α) (q : ProgE Op E' O' β) : ProgE Op (E ⊕ E') (O ⊕ O') Empty :=
  match p with
  | .send o r => .send (.inl o) (par r q)
  | .opN c k => .opN c fun n => parEmL (k n) q
  | .ret _ => .fail
  | .recv _ => .fail
  | .fail => .fail
  termination_by (p, q, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (Child.send _ _)
    · exact Prod.Lex.left _ _ (Child.opN _ _ _)

/-- The await phase of the right program on the event `e`. -/
def parAwR (e : E') (p : ProgE Op E O α) (q : ProgE Op E' O' β) :
    ProgE Op (E ⊕ E') (O ⊕ O') Empty :=
  match q with
  | .recv k => parEmR p (k e)
  | .opN c k => .opN c fun n => parAwR e p (k n)
  | .ret _ => .fail
  | .send _ _ => .fail
  | .fail => .fail
  termination_by (p, q, 1)
  decreasing_by
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (Child.recv _ _))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (Child.opN _ _ _))

/-- The emit phase of the right program. -/
def parEmR (p : ProgE Op E O α) (q : ProgE Op E' O' β) : ProgE Op (E ⊕ E') (O ⊕ O') Empty :=
  match q with
  | .send o r => .send (.inr o) (par p r)
  | .opN c k => .opN c fun n => parEmR p (k n)
  | .ret _ => .fail
  | .recv _ => .fail
  | .fail => .fail
  termination_by (p, q, 0)
  decreasing_by
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (Child.send _ _))
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (Child.opN _ _ _))

end

section Par

variable (H : Handler Op M) (hH : H.Lawful)
include hH

/-- The emit phase of `parEmL p q` is the emit phase of `p`, its residual composed with `q` and
its output tagged `inl`. -/
theorem emitK_parEmL (q : ProgE Op E' O' β) (p : ProgE Op E O α) :
    emitK H (fun o r => H.pure (r, o)) (fun _ => H.fail) (parEmL p q) =
      H.bind (emitK H (fun o r => H.pure (r, o)) (fun _ => H.fail) p)
        fun x => H.pure (par x.1 q, Sum.inl x.2) := by
  induction p with
  | opN c k ih => simp only [parEmL, emitK, ih, hH.bind_assoc]
  | _ => simp [parEmL, emitK, hH.pure_bind, hH.fail_bind]

/-- The emit phase of `parEmR p q` is the emit phase of `q`, `p` composed with its residual and
its output tagged `inr`. -/
theorem emitK_parEmR (p : ProgE Op E O α) (q : ProgE Op E' O' β) :
    emitK H (fun o r => H.pure (r, o)) (fun _ => H.fail) (parEmR p q) =
      H.bind (emitK H (fun o r => H.pure (r, o)) (fun _ => H.fail) q)
        fun x => H.pure (par p x.1, Sum.inr x.2) := by
  induction q with
  | opN c k ih => simp only [parEmR, emitK, ih, hH.bind_assoc]
  | _ => simp [parEmR, emitK, hH.pure_bind, hH.fail_bind]

/-- The emit phase of `parAwL e p q` is the activation of `p` on `e`. -/
theorem emitK_parAwL (e : E) (q : ProgE Op E' O' β) (p : ProgE Op E O α) :
    emitK H (fun o r => H.pure (r, o)) (fun _ => H.fail) (parAwL e p q) =
      H.bind (act H p e) fun x => H.pure (par x.1 q, Sum.inl x.2) := by
  induction p with
  | recv k => simp only [parAwL, act, stepWith, awaitK, emitK_parEmL H hH]
  | opN c k ih =>
    simp only [act, stepWith] at ih
    simp only [parAwL, emitK, act, stepWith, awaitK, ih, hH.bind_assoc]
  | _ => simp [parAwL, emitK, act, stepWith, awaitK, hH.fail_bind]

/-- The emit phase of `parAwR e p q` is the activation of `q` on `e`. -/
theorem emitK_parAwR (e : E') (p : ProgE Op E O α) (q : ProgE Op E' O' β) :
    emitK H (fun o r => H.pure (r, o)) (fun _ => H.fail) (parAwR e p q) =
      H.bind (act H q e) fun x => H.pure (par p x.1, Sum.inr x.2) := by
  induction q with
  | recv k => simp only [parAwR, act, stepWith, awaitK, emitK_parEmR H hH]
  | opN c k ih =>
    simp only [act, stepWith] at ih
    simp only [parAwR, emitK, act, stepWith, awaitK, ih, hH.bind_assoc]
  | _ => simp [parAwR, emitK, act, stepWith, awaitK, hH.fail_bind]

/-- An activation of `par p q` on a left event is the activation of `p`. -/
theorem act_par_inl (p : ProgE Op E O α) (q : ProgE Op E' O' β) (e : E) :
    act H (par p q) (.inl e) = H.bind (act H p e) fun x => H.pure (par x.1 q, Sum.inl x.2) := by
  rw [par]
  exact emitK_parAwL H hH e q p

/-- An activation of `par p q` on a right event is the activation of `q`. -/
theorem act_par_inr (p : ProgE Op E O α) (q : ProgE Op E' O' β) (e : E') :
    act H (par p q) (.inr e) = H.bind (act H q e) fun x => H.pure (par p x.1, Sum.inr x.2) := by
  rw [par]
  exact emitK_parAwR H hH e p q

end Par

end ProgE

end CatCrypt.Crypto.Party
