/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Cost
public import CatCryptCore.Core.SPTree
public import Lean

/-!
# Reflection of Lean definitions into D

The command `reflect_d f` reflects a Lean definition `f` whose body lies in the fragment of D
into a D-term `f.d : Tm Γ τ` and proves the denotation theorem `f.d_den`, stating that the
denotation of `f.d` is `f`. The context `Γ` holds the parameters of `f`, the last parameter
innermost. This is the certifying extraction of Forster and Kunze (*A certifying extraction
with time bounds from Coq to call-by-value λ-calculus*, ITP 2019) for D: they extract Coq
functions to L with MetaCoq and certify the extraction by a generated correctness relation;
here the certificate is the denotation theorem, and the cost of `f.d` is `Tm.cost`.

## The denotation theorem

For parameters `x₁ … xₙ`, the environment is `ρ = Env.nil.cons v₁ … .cons vₙ`, where `vᵢ` is
`xᵢ` for a parameter of a data type and `optEnc xᵢ` for an `Option` parameter. A parameter
`A : α → β` is represented by a D function value `g : Val (.arr a b)` with the hypothesis
`∀ v, g v = .ret (A v)`; a parameter `A : α → SPComp β` (an adversary) by `g` with the
hypothesis `∀ v, (g v).run O = A v` at the oracle `O` of the theorem, and a parameter
`A : α → SPTree β` (a tree primitive or adversary) with `∀ v, (g v).run O = (A v).compile`.
A curried parameter `A : α₁ → … → αₙ → β` is a D function on the right-nested tuple of its
arguments, applied when all `n` arguments are present (a partial application is refused); a
computation parameter without arguments (`SPComp β`, `SPTree β`) is a D function on `unit`,
applied to `()`. A parameter the body does not mention is a binder of the theorems only.
The theorem states

* `f.d.den ρ = .ret (f x₁ … xₙ)` when `f` returns data (`.ret (optEnc (f …))` for `Option`);
* `f.d.denote O ρ = f x₁ … xₙ` when `f` returns `SPComp α`, and
  `f.d.denote O ρ = (f x₁ … xₙ).compile` when `f` returns `SPTree α`.

It is proved by a derivation of the judgements `Den t ρ v` (the denotation of `t` in `ρ` is
the leaf `v`) and `DenM O t ρ c` (the meaning of `t` in `SPComp`, the oracle answered by `O`,
is `c`), one lemma per construct of D, assembled by the command and checked by the kernel. A
tree node is reflected as the D construct of its `SPComp` operation (`DenM.treeSample`,
`DenM.treeBind`, …).

## Static parameters

A parameter `M : Type` is represented by a finite ground type: `f.d` and the theorems take
`MF : FTy` in its place and state `f` at `M := MF.den`; the instance parameters of `f` are
then found by instance search at that representation. A parameter `n : ℕ` that occurs in the
type of a later parameter or of the result (a modulus `Fin (n + 1)`) is a parameter of `f.d`.

## The cost theorem

When every construct of the body is in the costed fragment (all of the above except λ-terms
applied in the body, matches on sums and lists, `foldl`, `iter` and `Option` constructors),
the command also proves `f.d_cost`: `f.d.cost ρ = c` for data and `f.d.cost ρ ≤ B` for a
computation, `c` and `B` expressions in the parameters. A data function parameter `A` takes a
cost function `ACost : Val a → ℕ` with `∀ v, g v = stepN CTree.tick (ACost v) (.ret (A v))`;
a computation parameter a bound `ACost : ℕ` with `∀ v, (g v).cost ≤ ACost`. The derivation uses
the judgements `CEq t ρ c v` (evaluation in exactly `c` steps to `v`) and `CLe t ρ B`; after a
sample or a read over a finite ground type the bound of the continuation is maximised over the
values (`CLe.letESup`).

## The fragment

Types: `ℕ`, `Bool`, `Unit`, `BitVec w` for a numeral `w`, `Fin m` and `ZMod m` for a modulus
`m` that is a positive numeral or of the form `n + 1`, products, sums and lists of these;
`Option α` as `α`'s sum with `Unit`, at the parameters, the result and the scrutinees of
matches; functions as parameters, `let`-bound values and arguments of λ-terms.

Terms: variables, `fun`, application, `let`, numerals and the literals `true`, `false`, `()`
and `BitVec.ofNat w n`; the operations `+ - * / %` on `ℕ`, `+ - * &&& ||| ^^^ ~~~ <<< >>>` on
words, `+ - *` and numerals on `Fin m` and `ZMod m`, `&&`, `||`, `!`, `^^` on `Bool`,
`BitVec.ofNat`, `BitVec.toNat`, `BitVec.setWidth`, `Fin.val`, `ZMod.val` and the cast of a
natural number into `Fin m` or `ZMod m`; `decide` of `=`, `≠`, `<`, `≤`, `∧`, `∨`, `¬` over
these (`=`, `≠` and `<` on residues); pairs and projections; `Sum.inl`,
`Sum.inr`, `some`, `none`, `[]`, `::`, `id`; `if`, `bif`, `Option.elim`, `Sum.elim` and
matches on `Bool`, `Option`, `Sum`, `List` (non-recursive, as `lcase`) and pairs; `List.foldl`
as `foldl` and `Nat.iterate` as `iter`; in `SPComp`, `pure`, `bind` (and `do`), `SPComp.fail`,
`SPComp.sample` of a finite ground type,
`SPComp.get` and `SPComp.set` at a location `FTy.loc f n`, and the application of a parameter;
in `SPTree`, `ret`, `sample` of a finite ground type, `get`, `set`, `fail`, `SPTree.bind`, `if`
and the application of a parameter.
A constant outside the Lean, Std and Mathlib libraries is unfolded. Any other construct is
refused with a message naming it.

## Main definitions

* `Den`, `DenM`: the judgements; `optEnc`: the representation of `Option`.
* `CEq`, `CLe`: the cost judgements.
* `reflect_d f`: the command.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.Reflect

open CatCrypt.Core

/-- The representation of `Option α` in D: `none` is the left unit, `some x` the right `x`. -/
def optEnc {α : Type} : Option α → Unit ⊕ α
  | none => .inl ()
  | some x => .inr x

/-- The denotation of `t` in `ρ` is the leaf `v`. -/
def Den {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) (ρ : Env Γ) (v : Val τ) : Prop :=
  t.den ρ = .ret v

/-- The meaning of `t` in `ρ`, the oracle answered by `O`, is `c`. -/
def DenM (O : CTree.Oracle) {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) (ρ : Env Γ)
    (c : SPComp (Val τ)) : Prop :=
  t.denote O ρ = c

/-- The evaluation of `t` in `ρ` takes `c` steps and returns `v` without effects. -/
def CEq {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) (ρ : Env Γ) (c : ℕ) (v : Val τ) : Prop :=
  t.eval ρ = stepN CTree.tick c (.ret v)

/-- The evaluation of `t` in `ρ` costs at most `B` steps. -/
def CLe {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) (ρ : Env Γ) (B : ℕ) : Prop :=
  (t.eval ρ).cost ≤ B

namespace Den

variable {Γ : List Ty} {ρ : Env Γ}

/-- `Den` at a variable, an unfolding of `Tm.den`. -/
theorem var {τ : Ty} (x : Var Γ τ) (ρ : Env Γ) : Den (.var x) ρ (ρ τ x) := rfl

/-- `Den` at a numeral, an unfolding of `Tm.den`. -/
theorem natLit (n : ℕ) (ρ : Env Γ) : Den (.natLit n) ρ n := rfl

/-- `Den` at a literal, an unfolding of `Tm.den`. -/
theorem lit (f : FTy) (v : f.den) (ρ : Env Γ) : Den (.lit f v) ρ v := rfl

/-- `Den` at a λ-term, an unfolding of `Tm.den`: its value is the closure. -/
theorem lam {a b : Ty} (t : Tm (a :: Γ) b) (ρ : Env Γ) :
    Den (.lam t) ρ (fun v => t.den (ρ.cons v)) := rfl

theorem app {a b : Ty} {f : Tm Γ (.arr a b)} {x : Tm Γ a} {F : Val (.arr a b)} {v : Val a}
    {w : Val b} (hf : Den f ρ F) (hx : Den x ρ v) (h : F v = .ret w) : Den (.app f x) ρ w := by
  show (f.den ρ).bind (fun g => (x.den ρ).bind fun v => g v) = _
  rw [hf, CTree.bind_ret, hx, CTree.bind_ret]
  exact h

theorem letE {a b : Ty} {e : Tm Γ a} {t : Tm (a :: Γ) b} {u : Val a} {w : Val b}
    (he : Den e ρ u) (ht : Den t (ρ.cons u) w) : Den (.letE e t) ρ w := by
  show (e.den ρ).bind (fun v => t.den (ρ.cons v)) = _
  rw [he, CTree.bind_ret]
  exact ht

theorem prim {a b : Ty} (p : Prim a b) {x : Tm Γ a} {v : Val a} (h : Den x ρ v) :
    Den (.prim p x) ρ (p.apply v) := by
  show (x.den ρ).bind (fun v => stepN (fun t => t) (p.cost v) (.ret (p.apply v))) = _
  rw [h, CTree.bind_ret, stepN_id]

theorem pair {a b : Ty} {x : Tm Γ a} {y : Tm Γ b} {u : Val a} {v : Val b}
    (hx : Den x ρ u) (hy : Den y ρ v) : Den (.pair x y) ρ ((u, v) : Val a × Val b) := by
  show (x.den ρ).bind (fun u => (y.den ρ).bind fun v => .ret ((u, v) : Val a × Val b)) = _
  rw [hx, CTree.bind_ret, hy]; rfl

theorem fst {a b : Ty} {p : Tm Γ (.prod a b)} {v : Val a × Val b} (h : Den p ρ v) :
    Den (.fst p) ρ v.1 := by
  show (p.den ρ).bind (fun (v : Val a × Val b) => .ret v.1) = _
  rw [h]; rfl

theorem snd {a b : Ty} {p : Tm Γ (.prod a b)} {v : Val a × Val b} (h : Den p ρ v) :
    Den (.snd p) ρ v.2 := by
  show (p.den ρ).bind (fun (v : Val a × Val b) => .ret v.2) = _
  rw [h]; rfl

theorem inl {a b : Ty} {x : Tm Γ a} {v : Val a} (h : Den x ρ v) :
    Den (.inl (b := b) x) ρ (Sum.inl v : Val a ⊕ Val b) := by
  show (x.den ρ).bind (fun v => .ret (Sum.inl v : Val a ⊕ Val b)) = _
  rw [h]; rfl

theorem inr {a b : Ty} {x : Tm Γ b} {v : Val b} (h : Den x ρ v) :
    Den (.inr (a := a) x) ρ (Sum.inr v : Val a ⊕ Val b) := by
  show (x.den ρ).bind (fun v => .ret (Sum.inr v : Val a ⊕ Val b)) = _
  rw [h]; rfl

/-- `Den` at the empty list, an unfolding of `Tm.den`. -/
theorem nil {a : Ty} (ρ : Env Γ) : Den (.nil (a := a)) ρ ([] : List (Val a)) := rfl

theorem cons {a : Ty} {x : Tm Γ a} {xs : Tm Γ (.list a)} {v : Val a} {l : List (Val a)}
    (hx : Den x ρ v) (hxs : Den xs ρ l) : Den (.cons x xs) ρ (v :: l) := by
  show (x.den ρ).bind (fun v => (xs.den ρ).bind fun (l : List (Val a)) => .ret (v :: l)) = _
  rw [hx, CTree.bind_ret, hxs]; rfl

theorem case {a b c : Ty} {β : Type} (E : β → Val c) {s : Tm Γ (.sum a b)}
    {l : Tm (a :: Γ) c} {r : Tm (b :: Γ) c} {v : Val a ⊕ Val b} {L : Val a → β}
    {R : Val b → β} (hs : Den s ρ v) (hl : ∀ x, Den l (ρ.cons x) (E (L x)))
    (hr : ∀ y, Den r (ρ.cons y) (E (R y))) :
    Den (.case s l r) ρ (E (Sum.casesOn (motive := fun _ => β) v L R)) := by
  show (s.den ρ).bind (fun (v : Val a ⊕ Val b) =>
    Sum.elim (fun x => l.den (ρ.cons x)) (fun y => r.den (ρ.cons y)) v) = _
  rw [hs]
  cases v with
  | inl x => exact hl x
  | inr y => exact hr y

theorem caseOpt {a c : Ty} {β : Type} (E : β → Val c) {s : Tm Γ (.sum .unit a)}
    {l : Tm (.unit :: Γ) c} {r : Tm (a :: Γ) c} {o : Option (Val a)} {N : β}
    {S : Val a → β} (hs : Den s ρ (optEnc o)) (hl : Den l (ρ.cons (τ := .unit) ()) (E N))
    (hr : ∀ y, Den r (ρ.cons y) (E (S y))) :
    Den (.case s l r) ρ (E (Option.casesOn (motive := fun _ => β) o N S)) := by
  show (s.den ρ).bind (fun (v : Unit ⊕ Val a) =>
    Sum.elim (fun x => l.den (ρ.cons (τ := .unit) x)) (fun y => r.den (ρ.cons y)) v) = _
  rw [hs]
  cases o with
  | none => exact hl
  | some y => exact hr y

theorem cond {c : Ty} {β : Type} (E : β → Val c) {b : Tm Γ .bool} {t e : Tm Γ c}
    {v : Bool} {x y : β} (hb : Den b ρ v) (ht : Den t ρ (E x)) (he : Den e ρ (E y)) :
    Den (.ite b t e) ρ (E (Bool.casesOn (motive := fun _ => β) v y x)) := by
  show (b.den ρ).bind (fun (v : Bool) => bif v then t.den ρ else e.den ρ) = _
  rw [hb]
  cases v
  · exact he
  · exact ht

theorem ite {c : Ty} {β : Type} (E : β → Val c) {P : Prop} [Decidable P] {b : Tm Γ .bool}
    {t e : Tm Γ c} {x y : β} (hb : Den b ρ (decide P)) (ht : Den t ρ (E x))
    (he : Den e ρ (E y)) : Den (.ite b t e) ρ (E (if P then x else y)) := by
  show (b.den ρ).bind (fun (v : Bool) => bif v then t.den ρ else e.den ρ) = _
  rw [hb]
  by_cases hP : P
  · rw [decide_eq_true hP, ite_eq_left hP]; exact ht
  · rw [decide_eq_false hP, ite_eq_right hP]; exact he

theorem lcase {a c : Ty} {β : Type} (E : β → Val c) {xs : Tm Γ (.list a)} {n : Tm Γ c}
    {k : Tm (a :: .list a :: Γ) c} {l : List (Val a)} {N : β} {C : Val a → List (Val a) → β}
    (hl : Den xs ρ l) (hn : Den n ρ (E N))
    (hk : ∀ x xs', Den k ((ρ.cons (τ := .list a) xs').cons x) (E (C x xs'))) :
    Den (.lcase xs n k) ρ (E (List.casesOn (motive := fun _ => β) l N C)) := by
  show (xs.den ρ).bind (fun (l : List (Val a)) =>
    listCase l (n.den ρ) fun x l' => k.den ((ρ.cons (τ := .list a) l').cons x)) = _
  rw [hl]
  cases l with
  | nil => exact hn
  | cons x xs' => exact hk x xs'

theorem foldT_id {a c : Ty} {F : Val (.arr (.prod c a) c)} {H : Val c → Val a → Val c}
    (hs : ∀ p : Val c × Val a, F p = .ret (H p.1 p.2)) (l : List (Val a)) :
    ∀ acc, foldT (fun t => t) F acc l = .ret (List.foldl H acc l) := by
  induction l with
  | nil => intro acc; rfl
  | cons x xs ih =>
    intro acc
    show (F (acc, x)).bind (fun acc' => foldT (fun t => t) F acc' xs) = _
    rw [hs (acc, x), CTree.bind_ret]
    exact ih _

theorem foldl {a c : Ty} {f : Tm Γ (.arr (.prod c a) c)} {i : Tm Γ c} {xs : Tm Γ (.list a)}
    {F : Val (.arr (.prod c a) c)} {H : Val c → Val a → Val c} {acc : Val c}
    {l : List (Val a)} (hf : Den f ρ F) (hs : ∀ p : Val c × Val a, F p = .ret (H p.1 p.2))
    (hi : Den i ρ acc) (hl : Den xs ρ l) : Den (.foldl f i xs) ρ (List.foldl H acc l) := by
  show (f.den ρ).bind (fun g => (i.den ρ).bind fun acc =>
    (xs.den ρ).bind fun l => foldT (fun t => t) g acc l) = _
  rw [hf, CTree.bind_ret, hi, CTree.bind_ret, hl]
  exact foldT_id hs l acc

theorem iterT_id {c : Ty} {F : Val (.arr c c)} {H : Val c → Val c}
    (hs : ∀ v, F v = .ret (H v)) (k : ℕ) : ∀ acc, iterT (fun t => t) F acc k =
      .ret (Nat.iterate H k acc) := by
  induction k with
  | zero => intro acc; rfl
  | succ k ih =>
    intro acc
    show (F acc).bind (fun acc' => iterT (fun t => t) F acc' k) = _
    rw [hs acc, CTree.bind_ret]
    exact ih _

theorem iter {c : Ty} {n : Tm Γ .nat} {f : Tm Γ (.arr c c)} {i : Tm Γ c} {k : ℕ}
    {F : Val (.arr c c)} {H : Val c → Val c} {acc : Val c} (hn : Den n ρ k) (hf : Den f ρ F)
    (hs : ∀ v, F v = .ret (H v)) (hi : Den i ρ acc) :
    Den (.iter n f i) ρ (Nat.iterate H k acc) := by
  show (n.den ρ).bind (fun (k : ℕ) => (f.den ρ).bind fun g =>
    (i.den ρ).bind fun acc => iterT (fun t => t) g acc k) = _
  rw [hn, hf]
  show (i.den ρ).bind (fun acc => iterT (fun t => t) F acc k) = _
  rw [hi]
  exact iterT_id hs k acc

/-! ### Decisions of propositions -/

theorem natLe {x : Tm Γ (.prod .nat .nat)} {m n : ℕ} (h : Den x ρ ((n, m) : ℕ × ℕ)) :
    Den (.prim .bnot (.prim .natLt x)) ρ (decide (m ≤ n)) := by
  have h' := Den.prim Prim.bnot (Den.prim Prim.natLt h)
  refine h'.trans ?_
  have e : (!decide (n < m)) = decide (m ≤ n) := by simp only [← decide_not, Nat.not_lt]
  exact congrArg (CTree.ret (α := Bool)) e

theorem natNe {x : Tm Γ (.prod .nat .nat)} {m n : ℕ} (h : Den x ρ ((m, n) : ℕ × ℕ)) :
    Den (.prim .bnot (.prim .natEq x)) ρ (decide (m ≠ n)) := by
  have h' := Den.prim Prim.bnot (Den.prim Prim.natEq h)
  refine h'.trans ?_
  show CTree.ret (!decide (m = n)) = CTree.ret (decide (m ≠ n))
  rw [decide_not]

theorem wordNe {w : ℕ} {x : Tm Γ (.prod (.word w) (.word w))} {m n : BitVec w}
    (h : Den x ρ ((m, n) : BitVec w × BitVec w)) :
    Den (.prim .bnot (.prim (.weq w) x)) ρ (decide (m ≠ n)) := by
  have h' := Den.prim Prim.bnot (Den.prim (Prim.weq w) h)
  refine h'.trans ?_
  show CTree.ret (!decide (m = n)) = CTree.ret (decide (m ≠ n))
  rw [decide_not]

theorem finNe {k : ℕ} {x : Tm Γ (.prod (.fin k) (.fin k))} {m n : Fin (k + 1)}
    (h : Den x ρ ((m, n) : Fin (k + 1) × Fin (k + 1))) :
    Den (.prim .bnot (.prim (.finEq k) x)) ρ (decide (m ≠ n)) := by
  have h' := Den.prim Prim.bnot (Den.prim (Prim.finEq k) h)
  refine h'.trans ?_
  show CTree.ret (!decide (m = n)) = CTree.ret (decide (m ≠ n))
  rw [decide_not]

theorem decAnd {x y : Tm Γ .bool} {P Q : Prop} [Decidable P] [Decidable Q]
    (hx : Den x ρ (decide P)) (hy : Den y ρ (decide Q)) :
    Den (.prim .band (.pair x y)) ρ (decide (P ∧ Q)) := by
  refine (Den.prim Prim.band (Den.pair hx hy)).trans ?_
  show CTree.ret (decide P && decide Q) = CTree.ret (decide (P ∧ Q))
  rw [Bool.decide_and]

theorem decOr {x y : Tm Γ .bool} {P Q : Prop} [Decidable P] [Decidable Q]
    (hx : Den x ρ (decide P)) (hy : Den y ρ (decide Q)) :
    Den (.prim .bor (.pair x y)) ρ (decide (P ∨ Q)) := by
  refine (Den.prim Prim.bor (Den.pair hx hy)).trans ?_
  show CTree.ret (decide P || decide Q) = CTree.ret (decide (P ∨ Q))
  rw [Bool.decide_or]

theorem decNot {x : Tm Γ .bool} {P : Prop} [Decidable P] (hx : Den x ρ (decide P)) :
    Den (.prim .bnot x) ρ (decide ¬P) := by
  refine (Den.prim Prim.bnot hx).trans ?_
  show CTree.ret (!decide P) = CTree.ret (decide ¬P)
  rw [decide_not]

theorem decBool {x : Tm Γ .bool} {b : Bool} (hx : Den x ρ b) : Den x ρ (decide (b = true)) := by
  have e : decide (b = true) = b := by simp
  show x.den ρ = CTree.ret (α := Bool) (decide (b = true))
  rw [e]; exact hx

end Den

namespace DenM

variable {O : CTree.Oracle} {Γ : List Ty} {ρ : Env Γ}

theorem pure {τ : Ty} {t : Tm Γ τ} {v : Val τ} (h : Den t ρ v) :
    DenM O t ρ (SPComp.pure v) := by
  show (t.den ρ).run O = _
  rw [h]
  rfl

theorem letE {a b : Ty} {e : Tm Γ a} {t : Tm (a :: Γ) b} {c : SPComp (Val a)}
    {k : Val a → SPComp (Val b)} (he : DenM O e ρ c) (ht : ∀ v, DenM O t (ρ.cons v) (k v)) :
    DenM O (.letE e t) ρ (SPComp.bind c k) := by
  show ((e.den ρ).bind fun v => t.den (ρ.cons v)).run O = _
  rw [CTree.run_bind]
  rw [show (e.den ρ).run O = c from he]
  exact congrArg _ (funext fun v => ht v)

theorem letEPure {a b : Ty} {e : Tm Γ a} {t : Tm (a :: Γ) b} {u : Val a}
    {c : SPComp (Val b)} (he : Den e ρ u) (ht : DenM O t (ρ.cons u) c) :
    DenM O (.letE e t) ρ c := by
  show ((e.den ρ).bind fun v => t.den (ρ.cons v)).run O = _
  rw [he, CTree.bind_ret]
  exact ht

theorem sample (f : FTy) (ρ : Env Γ) [i : Fintype f.den] [j : Nonempty f.den] :
    DenM O (.sample f) ρ (@SPComp.sample f.den i j) := by
  show SPComp.bind (@SPComp.sample f.den (FTy.instFintype f) _) (fun x => SPComp.pure x) = _
  rw [SPComp.bind_pure, Subsingleton.elim (FTy.instFintype f) i]

theorem fail {τ : Ty} (ρ : Env Γ) : DenM O (Tm.fail : Tm Γ τ) ρ SPComp.fail := rfl

theorem get (n : ℕ) (f : FTy) (ρ : Env Γ) : DenM O (.get n f) ρ (SPComp.get (f.loc n)) := by
  show SPComp.bind (SPComp.get (f.loc n)) (fun x => SPComp.pure x) = _
  rw [SPComp.bind_pure]

theorem set (n : ℕ) (f : FTy) {x : Tm Γ (.base f)} {v : f.den} (h : Den x ρ v) :
    DenM O (.set n f x) ρ (SPComp.set (f.loc n) v) := by
  show ((x.den ρ).bind fun v => CTree.set n f v (.ret (() : Unit))).run O = _
  rw [h]
  show SPComp.bind (SPComp.set (f.loc n) v) (fun _ => SPComp.pure ()) = _
  conv_rhs => rw [← SPComp.bind_pure (SPComp.set (f.loc n) v)]

theorem app {a b : Ty} {f : Tm Γ (.arr a b)} {x : Tm Γ a} {F : Val (.arr a b)} {v : Val a}
    {c : SPComp (Val b)} (hf : Den f ρ F) (hx : Den x ρ v) (h : (F v).run O = c) :
    DenM O (.app f x) ρ c := by
  show ((f.den ρ).bind (fun g => (x.den ρ).bind fun v => g v)).run O = _
  rw [hf, CTree.bind_ret, hx, CTree.bind_ret]
  exact h

theorem ite {c : Ty} {P : Prop} [Decidable P] {b : Tm Γ .bool} {t e : Tm Γ c}
    {x y : SPComp (Val c)} (hb : Den b ρ (decide P)) (ht : DenM O t ρ x) (he : DenM O e ρ y) :
    DenM O (.ite b t e) ρ (if P then x else y) := by
  show ((b.den ρ).bind (fun (v : Bool) => bif v then t.den ρ else e.den ρ)).run O = _
  rw [hb]
  by_cases hP : P
  · rw [decide_eq_true hP, ite_eq_left hP]; exact ht
  · rw [decide_eq_false hP, ite_eq_right hP]; exact he

theorem cond {c : Ty} {b : Tm Γ .bool} {t e : Tm Γ c} {v : Bool} {x y : SPComp (Val c)}
    (hb : Den b ρ v) (ht : DenM O t ρ x) (he : DenM O e ρ y) :
    DenM O (.ite b t e) ρ (Bool.casesOn (motive := fun _ => SPComp (Val c)) v y x) := by
  show ((b.den ρ).bind (fun (v : Bool) => bif v then t.den ρ else e.den ρ)).run O = _
  rw [hb]
  cases v
  · exact he
  · exact ht

theorem caseOpt {a c : Ty} {s : Tm Γ (.sum .unit a)} {l : Tm (.unit :: Γ) c}
    {r : Tm (a :: Γ) c} {o : Option (Val a)} {N : SPComp (Val c)}
    {S : Val a → SPComp (Val c)} (hs : Den s ρ (optEnc o))
    (hl : DenM O l (ρ.cons (τ := .unit) ()) N) (hr : ∀ y, DenM O r (ρ.cons y) (S y)) :
    DenM O (.case s l r) ρ (Option.casesOn (motive := fun _ => SPComp (Val c)) o N S) := by
  show ((s.den ρ).bind (fun (v : Unit ⊕ Val a) =>
    Sum.elim (fun x => l.den (ρ.cons (τ := .unit) x)) (fun y => r.den (ρ.cons y)) v)).run O = _
  rw [hs]
  cases o with
  | none => exact hl
  | some y => exact hr y

theorem case {a b c : Ty} {s : Tm Γ (.sum a b)} {l : Tm (a :: Γ) c} {r : Tm (b :: Γ) c}
    {v : Val a ⊕ Val b} {L : Val a → SPComp (Val c)} {R : Val b → SPComp (Val c)}
    (hs : Den s ρ v) (hl : ∀ x, DenM O l (ρ.cons x) (L x))
    (hr : ∀ y, DenM O r (ρ.cons y) (R y)) :
    DenM O (.case s l r) ρ (Sum.casesOn (motive := fun _ => SPComp (Val c)) v L R) := by
  show ((s.den ρ).bind (fun (v : Val a ⊕ Val b) =>
    Sum.elim (fun x => l.den (ρ.cons x)) (fun y => r.den (ρ.cons y)) v)).run O = _
  rw [hs]
  cases v with
  | inl x => exact hl x
  | inr y => exact hr y

/-! ### Computation trees

The meaning of a reflected `SPTree` is its compilation. A tree node is reflected as the D
construct of the corresponding `SPComp` operation; the compilation of `sample`, `get`, `set`,
`ret` and `fail` unfolds to that operation, and `SPTree.compile_bind` relates a tree bind to
the bind of the compilations. -/

theorem treeRet {τ : Ty} {t : Tm Γ τ} {v : Val τ} (h : Den t ρ v) :
    DenM O t ρ (SPTree.ret v).compile :=
  pure h

theorem treeFail {τ : Ty} (ρ : Env Γ) :
    DenM O (Tm.fail : Tm Γ τ) ρ (SPTree.fail : SPTree (Val τ)).compile :=
  rfl

theorem treeSample {b : Ty} (f : FTy) [i : Fintype f.den] [j : Nonempty f.den]
    {t : Tm (.base f :: Γ) b} {k : f.den → SPTree (Val b)}
    (ht : ∀ x, DenM O t (ρ.cons (τ := .base f) x) (k x).compile) :
    DenM O (.letE (.sample f) t) ρ (SPTree.sample f.den i j k).compile :=
  letE (sample f ρ) ht

theorem treeGet {b : Ty} (n : ℕ) (f : FTy) {t : Tm (.base f :: Γ) b}
    {k : (f.loc n).ty → SPTree (Val b)}
    (ht : ∀ x : f.den, DenM O t (ρ.cons (τ := .base f) x) (k x).compile) :
    DenM O (.letE (.get n f) t) ρ (SPTree.get (f.loc n) k).compile :=
  letE (get n f ρ) ht

theorem treeSet {b : Ty} (n : ℕ) (f : FTy) {x : Tm Γ (.base f)} {v : f.den}
    {t : Tm (.unit :: Γ) b} {T : SPTree (Val b)} (h : Den x ρ v)
    (ht : ∀ u : Unit, DenM O t (ρ.cons (τ := .unit) u) T.compile) :
    DenM O (.letE (.set n f x) t) ρ (SPTree.set (f.loc n) v T).compile :=
  letE (set n f h) ht

theorem treeBind {a b : Ty} {e : Tm Γ a} {t : Tm (a :: Γ) b} {T : SPTree (Val a)}
    {F : Val a → SPTree (Val b)} (he : DenM O e ρ T.compile)
    (ht : ∀ v, DenM O t (ρ.cons v) (F v).compile) :
    DenM O (.letE e t) ρ (T.bind F).compile := by
  rw [SPTree.compile_bind]
  exact letE he ht

theorem treeIte {c : Ty} {P : Prop} [Decidable P] {b : Tm Γ .bool} {t e : Tm Γ c}
    {x y : SPTree (Val c)} (hb : Den b ρ (decide P)) (ht : DenM O t ρ x.compile)
    (he : DenM O e ρ y.compile) : DenM O (.ite b t e) ρ (if P then x else y).compile := by
  rw [apply_ite SPTree.compile]
  exact ite hb ht he

end DenM

/-! ### Cost judgements

`CEq t ρ c v`: the evaluation takes exactly `c` steps to the value `v`; `CLe t ρ B`: it costs
at most `B`. A function parameter `g` of the reflected definition is costed by a hypothesis
`g v = stepN CTree.tick (cg v) (.ret (F v))` (a data function) or `(g v).cost ≤ k` (a
computation). -/

theorem stepN_tick_add {α : Type} (m k : ℕ) (t : CTree α) :
    stepN CTree.tick m (stepN CTree.tick k t) = stepN CTree.tick (m + k) t := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => rw [Nat.add_right_comm]; exact congrArg CTree.tick ih

theorem stepN_tick_succ {α : Type} (n : ℕ) (t : CTree α) :
    stepN CTree.tick n (.tick t) = stepN CTree.tick (n + 1) t :=
  stepN_tick_add n 1 t

theorem stepN_ret_bind {α β : Type} (n : ℕ) (a : α) (g : α → CTree β) :
    (stepN CTree.tick n (.ret a)).bind g = stepN CTree.tick n (g a) := by
  rw [stepN_tick_bind]; rfl

namespace CEq

variable {Γ : List Ty} {ρ : Env Γ}

theorem cost_eq {τ : Ty} {t : Tm Γ τ} {c : ℕ} {v : Val τ} (h : CEq t ρ c v) :
    t.cost ρ = c := by
  rw [Tm.cost, h, cost_stepN_tick, CTree.cost_ret, Nat.add_zero]

theorem var {τ : Ty} (x : Var Γ τ) (ρ : Env Γ) : CEq (.var x) ρ 0 (ρ τ x) := rfl

theorem natLit (n : ℕ) (ρ : Env Γ) : CEq (.natLit n) ρ 0 n := rfl

theorem lit (f : FTy) (v : f.den) (ρ : Env Γ) : CEq (.lit f v) ρ 0 v := rfl

theorem prim {a b : Ty} (p : Prim a b) {x : Tm Γ a} {c : ℕ} {v : Val a} (h : CEq x ρ c v) :
    CEq (.prim p x) ρ (c + p.cost v) (p.apply v) := by
  rw [CEq, Tm.eval_prim, h, stepN_ret_bind, stepN_tick_add]

theorem pair {a b : Ty} {x : Tm Γ a} {y : Tm Γ b} {c d : ℕ} {u : Val a} {v : Val b}
    (hx : CEq x ρ c u) (hy : CEq y ρ d v) :
    CEq (.pair x y) ρ (c + d) ((u, v) : Val a × Val b) := by
  show ((x.eval ρ).bind fun u => (y.eval ρ).bind fun v => .ret ((u, v) : Val a × Val b)) = _
  rw [hx, stepN_ret_bind, hy, stepN_ret_bind, stepN_tick_add]
  rfl

theorem fst {a b : Ty} {p : Tm Γ (.prod a b)} {c : ℕ} {v : Val a × Val b}
    (h : CEq p ρ c v) : CEq (.fst p) ρ c v.1 := by
  show ((p.eval ρ).bind fun (v : Val a × Val b) => .ret v.1) = _
  rw [h]
  exact stepN_ret_bind c v _

theorem snd {a b : Ty} {p : Tm Γ (.prod a b)} {c : ℕ} {v : Val a × Val b}
    (h : CEq p ρ c v) : CEq (.snd p) ρ c v.2 := by
  show ((p.eval ρ).bind fun (v : Val a × Val b) => .ret v.2) = _
  rw [h]
  exact stepN_ret_bind c v _

theorem app {a b : Ty} {f : Tm Γ (.arr a b)} {x : Tm Γ a} {cf cx k : ℕ} {F : Val (.arr a b)}
    {v : Val a} {w : Val b} (hf : CEq f ρ cf F) (hx : CEq x ρ cx v)
    (h : F v = stepN CTree.tick k (.ret w)) : CEq (.app f x) ρ (cf + cx + (k + 1)) w := by
  rw [CEq, Tm.eval_app, hf, stepN_ret_bind, hx, stepN_ret_bind]
  show stepN CTree.tick cf (stepN CTree.tick cx (CTree.tick (F v))) = _
  rw [h, stepN_tick_succ, stepN_tick_add, stepN_tick_add]
  congr 1
  omega

theorem letE {a b : Ty} {e : Tm Γ a} {t : Tm (a :: Γ) b} {ce ct : ℕ} {u : Val a} {w : Val b}
    (he : CEq e ρ ce u) (ht : CEq t (ρ.cons u) ct w) : CEq (.letE e t) ρ (ce + (ct + 1)) w := by
  rw [CEq, Tm.eval_letE, he, stepN_ret_bind]
  show stepN CTree.tick ce (CTree.tick (t.eval (ρ.cons u))) = _
  rw [ht, stepN_tick_succ, stepN_tick_add]
  congr 1
  omega

theorem ite {c : Ty} {β : Type} (E : β → Val c) {P : Prop} [Decidable P] {b : Tm Γ .bool}
    {t e : Tm Γ c} {cb ct ce : ℕ} {x y : β} (hb : CEq b ρ cb (decide P))
    (ht : CEq t ρ ct (E x)) (he : CEq e ρ ce (E y)) :
    CEq (.ite b t e) ρ (cb + ((if P then ct else ce) + 1)) (E (if P then x else y)) := by
  show ((b.eval ρ).bind (fun (v : Bool) => CTree.tick (bif v then t.eval ρ else e.eval ρ))) = _
  rw [hb]
  refine (stepN_ret_bind cb (decide P) _).trans ?_
  by_cases hP : P
  · have hc : (bif decide P then t.eval ρ else e.eval ρ) = t.eval ρ := by simp [hP]
    show stepN CTree.tick cb (CTree.tick (bif decide P then t.eval ρ else e.eval ρ)) = _
    rw [hc, ht, stepN_tick_succ, stepN_tick_add, ite_eq_left hP, ite_eq_left hP]
    congr 1
    omega
  · have hc : (bif decide P then t.eval ρ else e.eval ρ) = e.eval ρ := by simp [hP]
    show stepN CTree.tick cb (CTree.tick (bif decide P then t.eval ρ else e.eval ρ)) = _
    rw [hc, he, stepN_tick_succ, stepN_tick_add, ite_eq_right hP, ite_eq_right hP]
    congr 1
    omega

theorem natLe {x : Tm Γ (.prod .nat .nat)} {c : ℕ} {m n : ℕ} (h : CEq x ρ c ((n, m) : ℕ × ℕ)) :
    CEq (.prim .bnot (.prim .natLt x)) ρ (c + (max n.size m.size + 1) + 1)
      (decide (m ≤ n)) := by
  have h' := prim Prim.bnot (prim Prim.natLt h)
  have e : (!decide (n < m)) = decide (m ≤ n) := by simp only [← decide_not, Nat.not_lt]
  exact e ▸ h'

theorem natNe {x : Tm Γ (.prod .nat .nat)} {c : ℕ} {m n : ℕ} (h : CEq x ρ c ((m, n) : ℕ × ℕ)) :
    CEq (.prim .bnot (.prim .natEq x)) ρ (c + (max m.size n.size + 1) + 1)
      (decide (m ≠ n)) := by
  have h' := prim Prim.bnot (prim Prim.natEq h)
  have e : (!decide (m = n)) = decide (m ≠ n) := by rw [decide_not]
  exact e ▸ h'

theorem wordNe {w : ℕ} {x : Tm Γ (.prod (.word w) (.word w))} {c : ℕ} {m n : BitVec w}
    (h : CEq x ρ c ((m, n) : BitVec w × BitVec w)) :
    CEq (.prim .bnot (.prim (.weq w) x)) ρ (c + 1 + 1) (decide (m ≠ n)) := by
  have h' := prim Prim.bnot (prim (Prim.weq w) h)
  have e : (!decide (m = n)) = decide (m ≠ n) := by rw [decide_not]
  exact e ▸ h'

theorem finNe {k : ℕ} {x : Tm Γ (.prod (.fin k) (.fin k))} {c : ℕ} {m n : Fin (k + 1)}
    (h : CEq x ρ c ((m, n) : Fin (k + 1) × Fin (k + 1))) :
    CEq (.prim .bnot (.prim (.finEq k) x)) ρ (c + ((k + 1).size + 1) + 1)
      (decide (m ≠ n)) := by
  have h' := prim Prim.bnot (prim (Prim.finEq k) h)
  have e : (!decide (m = n)) = decide (m ≠ n) := by rw [decide_not]
  exact e ▸ h'

theorem decAnd {x y : Tm Γ .bool} {c d : ℕ} {P Q : Prop} [Decidable P] [Decidable Q]
    (hx : CEq x ρ c (decide P)) (hy : CEq y ρ d (decide Q)) :
    CEq (.prim .band (.pair x y)) ρ (c + d + 1) (decide (P ∧ Q)) := by
  have h' := prim Prim.band (pair hx hy)
  have e : (decide P && decide Q) = decide (P ∧ Q) := by rw [Bool.decide_and]
  exact e ▸ h'

theorem decOr {x y : Tm Γ .bool} {c d : ℕ} {P Q : Prop} [Decidable P] [Decidable Q]
    (hx : CEq x ρ c (decide P)) (hy : CEq y ρ d (decide Q)) :
    CEq (.prim .bor (.pair x y)) ρ (c + d + 1) (decide (P ∨ Q)) := by
  have h' := prim Prim.bor (pair hx hy)
  have e : (decide P || decide Q) = decide (P ∨ Q) := by rw [Bool.decide_or]
  exact e ▸ h'

theorem decNot {x : Tm Γ .bool} {c : ℕ} {P : Prop} [Decidable P] (hx : CEq x ρ c (decide P)) :
    CEq (.prim .bnot x) ρ (c + 1) (decide ¬P) := by
  have h' := prim Prim.bnot hx
  have e : (!decide P) = decide ¬P := by rw [decide_not]
  exact e ▸ h'

theorem decBool {x : Tm Γ .bool} {c : ℕ} {b : Bool} (hx : CEq x ρ c b) :
    CEq x ρ c (decide (b = true)) := by
  have e : b = decide (b = true) := by simp
  exact e ▸ hx

end CEq

namespace CLe

variable {Γ : List Ty} {ρ : Env Γ}

theorem cost_le {τ : Ty} {t : Tm Γ τ} {B : ℕ} (h : CLe t ρ B) : t.cost ρ ≤ B := h

theorem ofEq {τ : Ty} {t : Tm Γ τ} {c : ℕ} {v : Val τ} (h : CEq t ρ c v) : CLe t ρ c :=
  (CEq.cost_eq h).le

theorem fail {τ : Ty} (ρ : Env Γ) : CLe (Tm.fail : Tm Γ τ) ρ 0 := le_refl _

theorem letEPure {a b : Ty} {e : Tm Γ a} {t : Tm (a :: Γ) b} {ce B : ℕ} {u : Val a}
    (he : CEq e ρ ce u) (ht : CLe t (ρ.cons u) B) : CLe (.letE e t) ρ (ce + (B + 1)) := by
  show ((e.eval ρ).bind fun v => CTree.tick (t.eval (ρ.cons v))).cost ≤ _
  rw [he, stepN_tick_bind, CTree.bind_ret, cost_stepN_tick, CTree.cost_tick]
  have : (t.eval (ρ.cons u)).cost ≤ B := ht
  omega

theorem letE {a b : Ty} {e : Tm Γ a} {t : Tm (a :: Γ) b} {Be Bt : ℕ} (he : CLe e ρ Be)
    (ht : ∀ v, CLe t (ρ.cons v) Bt) : CLe (.letE e t) ρ (Be + (1 + Bt)) :=
  (Tm.cost_letE_le e t ρ Bt (CTree.AllRet.of_forall ht _)).trans
    (Nat.add_le_add_right he _)

theorem letESup {f : FTy} {b : Ty} {e : Tm Γ (.base f)} {t : Tm (.base f :: Γ) b} {Be : ℕ}
    {Bt : f.den → ℕ} (he : CLe e ρ Be) (ht : ∀ v, CLe t (ρ.cons (τ := .base f) v) (Bt v)) :
    CLe (.letE e t) ρ (Be + (1 + Finset.univ.sup Bt)) :=
  (Tm.cost_letE_le e t ρ (Finset.univ.sup Bt) (CTree.AllRet.of_forall (fun v =>
    (ht v).trans (Finset.le_sup (f := Bt) (Finset.mem_univ (α := f.den) v))) _)).trans
    (Nat.add_le_add_right he _)

theorem sample (f : FTy) (ρ : Env Γ) : CLe (.sample f) ρ 1 := by
  show 1 + Finset.univ.sup (fun x : f.den => (CTree.ret x : CTree f.den).cost) ≤ 1
  simp

theorem get (n : ℕ) (f : FTy) (ρ : Env Γ) : CLe (.get n f) ρ 1 := by
  show 1 + Finset.univ.sup (fun x : f.den => (CTree.ret x : CTree f.den).cost) ≤ 1
  simp

theorem set (n : ℕ) (f : FTy) {x : Tm Γ (.base f)} {c : ℕ} {v : f.den} (h : CEq x ρ c v) :
    CLe (.set n f x) ρ (c + 1) := by
  show ((x.eval ρ).bind fun v => CTree.set n f v (.ret (() : Unit))).cost ≤ _
  rw [h]
  refine (congrArg CTree.cost (stepN_ret_bind c v _)).trans_le ?_
  rw [cost_stepN_tick]
  show c + (1 + 0) ≤ c + 1
  omega

theorem app {a b : Ty} {f : Tm Γ (.arr a b)} {x : Tm Γ a} {cf cx k : ℕ} {F : Val (.arr a b)}
    {v : Val a} (hf : CEq f ρ cf F) (hx : CEq x ρ cx v) (h : (F v).cost ≤ k) :
    CLe (.app f x) ρ (cf + cx + (k + 1)) := by
  show ((f.eval ρ).bind fun g => (x.eval ρ).bind fun v => CTree.tick (g v)).cost ≤ _
  rw [hf, stepN_ret_bind, hx, stepN_ret_bind, cost_stepN_tick, cost_stepN_tick]
  show cf + (cx + (1 + (F v).cost)) ≤ _
  omega

theorem ite {c : Ty} {P : Prop} [Decidable P] {b : Tm Γ .bool} {t e : Tm Γ c} {cb Bt Be : ℕ}
    (hb : CEq b ρ cb (decide P)) (ht : CLe t ρ Bt) (he : CLe e ρ Be) :
    CLe (.ite b t e) ρ (cb + ((if P then Bt else Be) + 1)) := by
  show ((b.eval ρ).bind (fun (v : Bool) => CTree.tick (bif v then t.eval ρ else e.eval ρ))).cost
    ≤ _
  rw [hb]
  refine (congrArg CTree.cost (stepN_ret_bind cb (decide P) _)).trans_le ?_
  rw [cost_stepN_tick]
  show cb + (1 + (bif decide P then t.eval ρ else e.eval ρ).cost) ≤ _
  by_cases hP : P
  · have hc : (bif decide P then t.eval ρ else e.eval ρ) = t.eval ρ := by simp [hP]
    have : (t.eval ρ).cost ≤ Bt := ht
    rw [hc, ite_eq_left hP]
    omega
  · have hc : (bif decide P then t.eval ρ else e.eval ρ) = e.eval ρ := by simp [hP]
    have : (e.eval ρ).cost ≤ Be := he
    rw [hc, ite_eq_right hP]
    omega

theorem mono {τ : Ty} {t : Tm Γ τ} {B B' : ℕ} (h : CLe t ρ B) (hB : B ≤ B') : CLe t ρ B' :=
  le_trans h hB

end CLe

end CatCrypt.Complexity.D.Reflect

meta section

namespace CatCrypt.Complexity.D.Reflect.Impl

open Lean Elab Meta Command CatCrypt.Core

/-- How a function-typed value is applied: a closure of a λ-term of the source, with the index
of its context and whether its body is in `SPComp`, or a parameter `g` with its hypothesis
`h` for the denotation theorem and `hc` for the cost theorem, applied to the tuple of its
`arity` arguments (`arity = 0`: applied to `()`; `arity ≥ 2`: a curried source function,
uncurried in D). -/
inductive Fn where
  | clo (lam : Expr) (ctxId : Nat) (eff : Bool)
  | param (g h hc : Expr) (eff : Bool) (arity : Nat)
  deriving Inhabited

/-- A source variable: its de Bruijn level in D, the projections applied to it, the D type of
the variable at that level, its source value, its D value and how it is applied. -/
structure Entry where
  fvar : FVarId
  level : Nat
  path : List Bool
  baseTy : Expr
  val : Expr
  dval : Expr
  fn : Option Fn := none
  deriving Inhabited

/-- A translation context: the source variables, the D context (innermost first), the
environment and the oracle of the denotation theorem. -/
structure Ctx where
  entries : List Entry := []
  tys : List Expr := []
  rho : Expr
  oracle : Expr := default
  deriving Inhabited

/-- A translated subterm: the D-term, its type, its derivation, its source value, its D value
and, when the construct is in the costed fragment, its cost derivation (`CEq` for a pure
term, `CLe` for a computation). -/
structure Res where
  tm : Expr
  ty : Expr
  pf : Expr
  val : Expr
  dv : Expr
  fn : Option Fn := none
  cpf : Option Expr := none
  deriving Inhabited

/-- The translation monad: the flag selects translation without derivations; the state holds
the contexts of closures. -/
abbrev M := ReaderT Bool (StateRefT (Array Ctx) MetaM)

def fail {α : Type} (msg : MessageData) : M α := throwError m!"reflect_d: {msg}"

def synMode : M Bool := read

def ifPf (k : M Expr) : M Expr := do
  if ← synMode then return mkConst ``True.intro else k

/-- A cost derivation from the cost derivations `xs` of the subterms, or none when one of them
is missing or the lemma does not apply. -/
def costPf (xs : Array (Option Expr)) (k : Array Expr → M Expr) : M (Option Expr) := do
  if ← synMode then return none
  let some ys := xs.mapM id | return none
  try return some (← k ys) catch _ => return none

/-- The bound of a cost derivation: `c` of `CEq t ρ c v`, `B` of `CLe t ρ B`. -/
def costOf (pf : Expr) : MetaM Expr := do
  let T ← instantiateMVars (← inferType pf)
  return T.getArg! 4

/-- A lemma of `DenM` applied at the oracle of the context. -/
def denMApp (ctx : Ctx) (n : Name) (args : Array Expr) : MetaM Expr := do
  mkAppM' (← mkAppOptM n #[some ctx.oracle]) args

/-! ### D types -/

def tyC (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst (``Ty ++ n)) args

def tyBase (f : Expr) : Expr := tyC `base #[f]

def tyNat : Expr := mkConst ``Ty.nat

def tyUnit : Expr := tyBase (mkConst ``FTy.unit)

def tyBool : Expr := tyBase (mkConst ``FTy.bool)

def tyWord (w : Expr) : Expr := tyBase (mkApp (mkConst ``FTy.word) w)

def valE (τ : Expr) : Expr := mkApp (mkConst ``Val) τ

def gammaE (tys : List Expr) : Expr :=
  tys.foldr (fun t acc => mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Ty) t acc)
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Ty))

def tyArgs2 (n : Name) (t : Expr) : Option (Expr × Expr) :=
  if t.isAppOfArity (``Ty ++ n) 2 then some (t.appFn!.appArg!, t.appArg!) else none

/-- The argument of `SPComp`, if `T` is an `SPComp` type. -/
def spcompArg? (T : Expr) : MetaM (Option Expr) := do
  let T ← whnfR T
  if T.isAppOfArity ``SPComp 1 then return some T.appArg! else return none

/-- The word width of `BitVec w`, or `none` for `ℕ`. -/
def numKind (T : Expr) : MetaM (Option (Option Expr)) := do
  let T ← whnf T
  if T.isConstOf ``Nat then return some none
  if T.isAppOfArity ``BitVec 1 then return some (some T.appArg!)
  return none

/-- The predecessor `n` of a modulus `m = n + 1`, given as `n + 1`, `Nat.succ n` or a positive
numeral. -/
def modPred (m : Expr) : MetaM Expr := do
  let m := m.consumeMData
  if m.isAppOfArity ``HAdd.hAdd 6 then
    if (← evalNat m.appArg!) == some 1 then return m.appFn!.appArg!
  if m.isAppOfArity ``Nat.succ 1 then return m.appArg!
  if m.hasFVar then throwError "reflect_d: the modulus `{m}` depends on a variable"
  match ← evalNat m with
  | some (v + 1) => return mkNatLit v
  | _ => throwError "reflect_d: the modulus `{m}` is not a positive numeral or `n + 1`"

/-- For `Fin m` or `ZMod m` with `m = n + 1`, the predecessor `n`: the type is
`FTy.den (.fin n)`. -/
def finMod? (T : Expr) : MetaM (Option Expr) := do
  let T := T.consumeMData
  if T.isAppOfArity `ZMod 1 then return some (← modPred T.appArg!)
  let T ← whnf T
  if T.isAppOfArity ``Fin 1 then return some (← modPred T.appArg!)
  return none

/-- The type of the leaves of an `SPTree`, or `none`. -/
def treeArg? (T : Expr) : MetaM (Option Expr) := do
  let T ← whnfR T
  if T.isAppOfArity ``SPTree 1 then return some T.appArg! else return none

/-- The finite ground type of `T`. -/
def ftyOf (T : Expr) : MetaM Expr := do
  if let some n ← finMod? T then return mkApp (mkConst ``FTy.fin) n
  if T.consumeMData.isAppOfArity ``FTy.den 1 then return T.consumeMData.appArg!
  let T ← whnf T
  if T.isAppOfArity ``FTy.den 1 then return T.appArg!
  if T.isConstOf ``Bool then return mkConst ``FTy.bool
  if T.isConstOf ``PUnit then return mkConst ``FTy.unit
  if T.isAppOfArity ``BitVec 1 then
    let w := T.appArg!
    if w.hasFVar then throwError "reflect_d: the width of `{T}` depends on a variable"
    return mkApp (mkConst ``FTy.word) w
  throwError "reflect_d: `{T}` is not a finite ground type (Bool, Unit, BitVec w, Fin m, ZMod m)"

/-- The D type of a source type; the flag marks `Option`, represented by `optEnc`. -/
partial def tyOf (T : Expr) : MetaM (Expr × Bool) := do
  if let some γ ← spcompArg? T then
    throwError "reflect_d: the computation type `SPComp {γ}` occurs inside a data type"
  if let some γ ← treeArg? T then
    throwError "reflect_d: the computation type `SPTree {γ}` occurs inside a data type"
  if let some n ← finMod? T then return (tyBase (mkApp (mkConst ``FTy.fin) n), false)
  if T.consumeMData.isAppOfArity ``FTy.den 1 then return (tyBase T.consumeMData.appArg!, false)
  let T ← whnf T
  match T with
  | .forallE _ a b _ =>
    if b.hasLooseBVars then throwError "reflect_d: the dependent function type `{T}`"
    let (ta, _) ← tyFO a
    let tb ← match ← spcompArg? b with
      | some γ => pure (← tyFO γ).1
      | none => match ← treeArg? b with
        | some γ => pure (← tyFO γ).1
        | none => pure (← tyOf b).1
    return (tyC `arr #[ta, tb], false)
  | _ =>
  let args := T.getAppArgs
  match T.getAppFn.constName?, args.size with
  | some ``FTy.den, 1 => return (tyBase args[0]!, false)
  | some ``Nat, 0 => return (tyNat, false)
  | some ``Bool, 0 => return (tyBool, false)
  | some ``PUnit, 0 => return (tyUnit, false)
  | some ``BitVec, 1 => return (tyBase (← ftyOf T), false)
  | some ``Prod, 2 => return (tyC `prod #[(← tyFO args[0]!).1, (← tyFO args[1]!).1], false)
  | some ``Sum, 2 => return (tyC `sum #[(← tyFO args[0]!).1, (← tyFO args[1]!).1], false)
  | some ``List, 1 => return (tyC `list #[(← tyFO args[0]!).1], false)
  | some ``Option, 1 => return (tyC `sum #[tyUnit, (← tyFO args[0]!).1], true)
  | _, _ => throwError "reflect_d: the type `{T}` has no representation in D"
where
  /-- A type represented by itself: no `Option` occurs in it. -/
  tyFO (T : Expr) : MetaM (Expr × Bool) := do
    let r ← tyOf T
    if r.2 then throwError "reflect_d: `Option` inside the type `{T}`"
    return r

/-- The D value of a source value of type `T`. -/
def encode (T v : Expr) : MetaM Expr := do
  let T ← whnf T
  if T.isAppOfArity ``Option 1 then return mkApp2 (mkConst ``optEnc) T.appArg! v
  return v

/-! ### Contexts and terms -/

def Ctx.depth (ctx : Ctx) : Nat := ctx.tys.length

def Ctx.gamma (ctx : Ctx) : Expr := gammaE ctx.tys

/-- Substitute the source values of the variables of the context. -/
def Ctx.subst (ctx : Ctx) (e : Expr) : Expr :=
  e.replaceFVars (ctx.entries.map (mkFVar ·.fvar)).toArray (ctx.entries.map (·.val)).toArray

/-- Push a D binder of type `τ` with D value `v`. -/
def Ctx.bind (ctx : Ctx) (τ v : Expr) : Ctx :=
  { ctx with tys := τ :: ctx.tys,
             rho := mkAppN (mkConst ``Env.cons) #[ctx.gamma, τ, v, ctx.rho] }

def Ctx.push (ctx : Ctx) (en : Entry) : Ctx := { ctx with entries := en :: ctx.entries }

def mkVarE : List Expr → Nat → Expr × Expr
  | τ :: Γ, 0 => (mkApp2 (mkConst ``Var.here) (gammaE Γ) τ, τ)
  | σ :: Γ, k + 1 =>
    let (x, τ) := mkVarE Γ k
    (mkApp4 (mkConst ``Var.there) (gammaE Γ) σ τ x, τ)
  | [], _ => (default, default)

def denE (Γ τ tm ρ v : Expr) : Expr := mkAppN (mkConst ``Den) #[Γ, τ, tm, ρ, v]

def denME (O Γ τ tm ρ c : Expr) : Expr := mkAppN (mkConst ``DenM) #[O, Γ, τ, tm, ρ, c]

/-- Close a pure node: the source value, the D value and the derivation with its type. -/
def finish (ctx : Ctx) (e tm ty pf : Expr) (fn : Option Fn := none)
    (cpf : Option Expr := none) : M Res := do
  let val := ctx.subst e
  if ← synMode then return { tm, ty, pf, val, dv := val, fn }
  if fn.isSome then
    return { tm, ty, pf, val, dv := (← inferType pf).appArg!, fn, cpf }
  let dv ← encode (← inferType val) val
  return { tm, ty, pf := ← mkExpectedTypeHint pf (denE ctx.gamma ty tm ctx.rho dv), val, dv,
           cpf }

/-- Close an effectful node. -/
def finishM (ctx : Ctx) (e tm ty pf : Expr) (cpf : Option Expr := none) : M Res := do
  let val := ctx.subst e
  if ← synMode then return { tm, ty, pf, val, dv := val }
  return { tm, ty, pf := ← mkExpectedTypeHint pf (denME ctx.oracle ctx.gamma ty tm ctx.rho val),
           val, dv := val, cpf }

/-- Close a tree node: its meaning is the compilation of the source tree. -/
def finishT (ctx : Ctx) (e tm ty pf : Expr) (cpf : Option Expr := none) : M Res := do
  let val ← mkAppM ``SPTree.compile #[ctx.subst e]
  if ← synMode then return { tm, ty, pf, val, dv := val }
  return { tm, ty, pf := ← mkExpectedTypeHint pf (denME ctx.oracle ctx.gamma ty tm ctx.rho val),
           val, dv := val, cpf }

def refVar (ctx : Ctx) (en : Entry) : M Res := do
  let Γ := ctx.gamma
  let (x, τ) := mkVarE ctx.tys (ctx.depth - 1 - en.level)
  let mut tm := mkApp3 (mkConst ``Tm.var) Γ τ x
  let mut ty := τ
  let mut pf ← ifPf (mkAppM ``Den.var #[x, ctx.rho])
  let mut cpf ← costPf #[] fun _ => mkAppM ``CEq.var #[x, ctx.rho]
  for snd in en.path do
    let some (a, b) := tyArgs2 `prod ty | fail m!"a projection of a variable of type {ty}"
    tm := mkAppN (mkConst (if snd then ``Tm.snd else ``Tm.fst)) #[Γ, a, b, tm]
    pf ← ifPf (mkAppM (if snd then ``Den.snd else ``Den.fst) #[pf])
    cpf ← costPf #[cpf] fun ys => mkAppM (if snd then ``CEq.snd else ``CEq.fst) ys
    ty := if snd then b else a
  if ← synMode then return { tm, ty, pf, val := en.val, dv := en.dval, fn := en.fn }
  return { tm, ty, val := en.val, dv := en.dval, fn := en.fn, cpf,
           pf := ← mkExpectedTypeHint pf (denE Γ ty tm ctx.rho en.dval) }

/-- A constant whose definition is unfolded: one outside the Lean, Std and Mathlib
libraries. -/
def unfoldable (c : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo _) := env.find? c | return false
  if isInstanceCore env c then return false
  match env.getModuleIdxFor? c with
  | none => return true
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    let root := m.getRoot
    return !([`Init, `Std, `Lean, `Mathlib, `Batteries, `Qq, `Aesop].contains root)

/-- `e` as a λ-term of at least `n` binders, by η-expansion. -/
def etaN (ctx : Ctx) (e : Expr) (n : Nat) : MetaM Expr := do
  let rec count : Expr → Nat
    | .lam _ _ b _ => count b + 1
    | _ => 0
  if count e ≥ n then return e
  let T ← whnf (← inferType (ctx.subst e))
  forallBoundedTelescope T (some n) fun xs _ => do
    let body := mkAppN e xs
    mkLambdaFVars xs body

/-- The application `e` of the constant `c` with its definition unfolded and β-reduced at the
head. A definition by recursion (through `brecOn`, a recursor or well-founded recursion) is
refused. -/
def deltaApp (c : Name) (e : Expr) : M Expr := do
  let .const _ lvls := e.getAppFn.consumeMData | fail m!"the term `{e}`"
  let info ← getConstInfo c
  unless info.hasValue do fail m!"the constant `{c}` has no definition to unfold"
  let v ← instantiateValueLevelParams info lvls
  let recursive := v.find? fun s => match s.constName? with
    | some n => n.isStr && (n.getString! == "brecOn" || n.getString! == "rec" ||
        n == ``WellFounded.fix)
    | none => false
  if recursive.isSome then
    fail m!"the recursive definition `{c}` (use List.foldl or Nat.iterate)"
  return v.beta e.getAppArgs

def isNumeral (e : Expr) : Bool :=
  !e.hasFVar && (e.isRawNatLit || e.isAppOfArity ``OfNat.ofNat 3)

mutual

/-- Translate a pure source term. -/
partial def goP (ctx : Ctx) (e : Expr) : M Res := do
  let e := e.consumeMData
  let Γ := ctx.gamma
  match e with
  | .fvar fv =>
    match ctx.entries.find? (·.fvar == fv) with
    | some en => refVar ctx en
    | none => fail m!"the free variable `{e}`"
  | .letE n _ v b _ =>
    let rv ← goP ctx v
    let y ← mkFreshFVarId
    let ctx' := (ctx.bind rv.ty rv.dv).push
      { fvar := y, level := ctx.depth, path := [], baseTy := rv.ty, val := rv.val,
        dval := rv.dv, fn := rv.fn }
    let rb ← goP ctx' (b.instantiate1 (mkFVar y))
    let tm := mkAppN (mkConst ``Tm.letE) #[Γ, rv.ty, rb.ty, rv.tm, rb.tm]
    let pf ← ifPf (mkAppM ``Den.letE #[rv.pf, rb.pf])
    let cpf ← costPf #[rv.cpf, rb.cpf] fun ys => mkAppM ``CEq.letE ys
    let _ := n
    finish ctx e tm rb.ty pf rb.fn cpf
  | .lam .. => goLam ctx e
  | .proj ``Prod i s =>
    let rs ← goP ctx s
    let some (a, b) := tyArgs2 `prod rs.ty | fail m!"the projection `{e}`"
    let tm := mkAppN (mkConst (if i == 0 then ``Tm.fst else ``Tm.snd)) #[Γ, a, b, rs.tm]
    let pf ← ifPf (mkAppM (if i == 0 then ``Den.fst else ``Den.snd) #[rs.pf])
    let cpf ← costPf #[rs.cpf] fun ys => mkAppM (if i == 0 then ``CEq.fst else ``CEq.snd) ys
    finish ctx e tm (if i == 0 then a else b) pf none cpf
  | .lit (.natVal _) =>
    finish ctx e (mkApp2 (mkConst ``Tm.natLit) Γ e) tyNat
      (← ifPf (mkAppM ``Den.natLit #[e, ctx.rho])) none
      (← costPf #[] fun _ => mkAppM ``CEq.natLit #[e, ctx.rho])
  | _ =>
    let fn := e.getAppFn.consumeMData
    let args := e.getAppArgs
    match fn with
    | .const c _ => goConst ctx e c args
    | .fvar _ | .lam .. | .letE .. | .mdata .. =>
      if args.isEmpty then fail m!"the term `{e}`"
      applyAll ctx e fn args false
    | _ => fail m!"the term `{e}`"

/-- A λ-term: a closure. -/
partial def goLam (ctx : Ctx) (e : Expr) : M Res := do
  let .lam n T body bi := e | fail m!"the term `{e}`"
  let Γ := ctx.gamma
  let T' := ctx.subst T
  let (a, _) ← tyOf T'
  let eff ← withLocalDecl n bi T' fun y => do
    return (← spcompArg? (← inferType (ctx.subst (body.instantiate1 y)))).isSome
  let rb ← withLocalDecl n bi T' fun y =>
    withReader (fun _ => true) do
      let ctx' := (ctx.bind a y).push
        { fvar := y.fvarId!, level := ctx.depth, path := [], baseTy := a, val := y, dval := y }
      if eff then goM ctx' (body.instantiate1 y) else goP ctx' (body.instantiate1 y)
  let tm := mkAppN (mkConst ``Tm.lam) #[Γ, a, rb.ty, rb.tm]
  let id ← modifyGet fun s => (s.size, s.push ctx)
  let pf ← ifPf (mkAppM ``Den.lam #[rb.tm, ctx.rho])
  finish ctx e tm (tyC `arr #[a, rb.ty]) pf (some (.clo e id eff))

/-- The translation of the arguments `args` of a parameter as one D argument: `()` for none,
the argument for one, the right-nested tuple for several. -/
partial def argsRes (ctx : Ctx) (args : Array Expr) : M Res := do
  let Γ := ctx.gamma
  if args.isEmpty then
    let u := Lean.mkConst ``PUnit.unit [Level.one]
    let f := mkConst ``FTy.unit
    return { tm := mkApp3 (mkConst ``Tm.lit) Γ f u, ty := tyUnit,
             pf := ← ifPf (mkAppM ``Den.lit #[f, u, ctx.rho]), val := u, dv := u,
             cpf := ← costPf #[] fun _ => mkAppM ``CEq.lit #[f, u, ctx.rho] }
  let mut acc ← goP ctx args.back!
  for i in (List.range (args.size - 1)).reverse do
    let r ← goP ctx args[i]!
    let synth ← synMode
    acc := { tm := mkAppN (mkConst ``Tm.pair) #[Γ, r.ty, acc.ty, r.tm, acc.tm],
             ty := tyC `prod #[r.ty, acc.ty],
             pf := ← ifPf (mkAppM ``Den.pair #[r.pf, acc.pf]),
             val := ← if synth then pure default else mkAppM ``Prod.mk #[r.val, acc.val],
             dv := ← if synth then pure default else mkAppM ``Prod.mk #[r.dv, acc.dv],
             cpf := ← costPf #[r.cpf, acc.cpf] fun ys => mkAppM ``CEq.pair ys }
  return acc

/-- The application of the function `fn` to `args`: a parameter of arity `n` takes its `n`
arguments at once, as a tuple (`()` for `n = 0`); in an `SPComp` or `SPTree` position
(`eff`) the last application is a computation. -/
partial def applyAll (ctx : Ctx) (e fn : Expr) (args : Array Expr) (eff : Bool) : M Res := do
  let mut r ← goP ctx fn
  let mut i := 0
  let mut done := false
  for _ in [0:args.size + 1] do
    if done then break
    let n := match r.fn with
      | some (.param _ _ _ _ n) => n
      | _ => 1
    if i + n > args.size then
      if i == args.size then break
      fail m!"the partial application `{e}` of a parameter"
    let srcs := args.extract i (i + n)
    let ra ← if n == 1 then goP ctx args[i]! else argsRes ctx srcs
    let last := i + n == args.size
    r ← if last && eff then applyMR ctx r ra srcs else applyPR ctx r ra srcs
    i := i + n
    if last then
      done := true
  if eff && !done then fail m!"the computation `{e}`"
  if i != args.size then fail m!"the application `{e}`"
  return r

/-- Apply a translated function to a source argument, in a pure position. -/
partial def applyP (ctx : Ctx) (rf : Res) (arg : Expr) : M Res := do
  applyPR ctx rf (← goP ctx arg) #[arg]

/-- Apply a translated function to the translated argument `ra` of the source arguments
`srcs`, in a pure position. -/
partial def applyPR (ctx : Ctx) (rf : Res) (ra : Res) (srcs : Array Expr) : M Res := do
  let some (a, b) := tyArgs2 `arr rf.ty | fail m!"an application of a non-function"
  let tm := mkAppN (mkConst ``Tm.app) #[ctx.gamma, a, b, rf.tm, ra.tm]
  if ← synMode then return { tm, ty := b, pf := mkConst ``True.intro, val := default,
                             dv := default }
  match rf.fn with
  | some (.clo (.lam _ _ body _) id false) =>
    let c0 := (← get)[id]!
    let y ← mkFreshFVarId
    let c0' := (c0.bind a ra.dv).push
      { fvar := y, level := c0.depth, path := [], baseTy := a, val := ra.val, dval := ra.dv,
        fn := ra.fn }
    let rb ← goP c0' (body.instantiate1 (mkFVar y))
    let pf ← mkAppM ``Den.app #[rf.pf, ra.pf, rb.pf]
    return { tm, ty := b, pf, val := rb.val, dv := rb.dv, fn := rb.fn }
  | some (.param _ h hc false n) =>
    unless n == srcs.size do fail m!"the partial application of the parameter `{rf.val}`"
    let pf ← mkAppM ``Den.app #[rf.pf, ra.pf, mkApp h ra.dv]
    let val := if n == 1 then mkApp rf.val ra.val else mkAppN rf.val (srcs.map ctx.subst)
    let cpf ← costPf #[rf.cpf, ra.cpf] fun ys => mkAppM ``CEq.app #[ys[0]!, ys[1]!, mkApp hc ra.dv]
    return { tm, ty := b, pf := ← mkExpectedTypeHint pf (denE ctx.gamma b tm ctx.rho val),
             val, dv := val, cpf }
  | _ => fail m!"an application of `{rf.val}`, whose body is not known or is in SPComp"

/-- Apply a translated function to a source argument, in an `SPComp` position. -/
partial def applyM (ctx : Ctx) (rf : Res) (arg : Expr) : M Res := do
  applyMR ctx rf (← goP ctx arg) #[arg]

/-- Apply a translated function to the translated argument `ra` of the source arguments
`srcs`, in an `SPComp` position. -/
partial def applyMR (ctx : Ctx) (rf : Res) (ra : Res) (srcs : Array Expr) : M Res := do
  let some (a, b) := tyArgs2 `arr rf.ty | fail m!"an application of a non-function"
  let tm := mkAppN (mkConst ``Tm.app) #[ctx.gamma, a, b, rf.tm, ra.tm]
  if ← synMode then return { tm, ty := b, pf := mkConst ``True.intro, val := default,
                             dv := default }
  match rf.fn with
  | some (.clo (.lam _ _ body _) id true) =>
    let c0 := (← get)[id]!
    let y ← mkFreshFVarId
    let c0' := (c0.bind a ra.dv).push
      { fvar := y, level := c0.depth, path := [], baseTy := a, val := ra.val, dval := ra.dv,
        fn := ra.fn }
    let rb ← goM c0' (body.instantiate1 (mkFVar y))
    let pf ← denMApp ctx ``DenM.app #[rf.pf, ra.pf, rb.pf]
    return { tm, ty := b, pf, val := rb.val, dv := rb.dv }
  | some (.param _ h hc true n) =>
    unless n == srcs.size do fail m!"the partial application of the parameter `{rf.val}`"
    let pf ← denMApp ctx ``DenM.app #[rf.pf, ra.pf, mkApp h ra.dv]
    let val0 := if n == 1 then mkApp rf.val ra.val else mkAppN rf.val (srcs.map ctx.subst)
    let val ← if (← treeArg? (← inferType val0)).isSome then mkAppM ``SPTree.compile #[val0]
      else pure val0
    let cpf ← costPf #[rf.cpf, ra.cpf] fun ys => mkAppM ``CLe.app #[ys[0]!, ys[1]!, mkApp hc ra.dv]
    return { tm, ty := b,
             pf := ← mkExpectedTypeHint pf (denME ctx.oracle ctx.gamma b tm ctx.rho val),
             val, dv := val, cpf }
  | _ => fail m!"an application of `{rf.val}` in SPComp, whose body is not known"

/-- The result type and representation of a branching node of source type `T`:
`(c, β, E)`. -/
partial def branchRep (T : Expr) : M (Expr × Expr × Expr) := do
  let (c, isOpt) ← tyOf T
  if isOpt then
    let T ← whnf T
    let α := T.appArg!
    return (c, mkApp (mkConst ``Option [Level.zero]) α, mkApp (mkConst ``optEnc) α)
  return (c, valE c, .lam `v (valE c) (.bvar 0) .default)

/-- A generic binder of source type `T` with name `n`, as a declared variable. -/
partial def withGeneric {α : Type} (ctx : Ctx) (n : Name) (T : Expr) (path : List Bool)
    (level : Nat) (baseTy : Expr) (k : Expr → Entry → M α) : M α := do
  let T := ctx.subst T
  discard <| tyOf T
  withLocalDeclD n T fun x => k x
    { fvar := x.fvarId!, level, path, baseTy, val := x, dval := x }

/-- Translate the condition `P` of an `if` to a Boolean term denoting `decide P`. -/
partial def goDecide (ctx : Ctx) (P : Expr) : M Res := do
  let P := P.consumeMData
  let Γ := ctx.gamma
  let Ps := ctx.subst P
  let fin (tm : Expr) (pf : Expr) (cpf : Option Expr) : M Res := do
    if ← synMode then return { tm, ty := tyBool, pf, val := default, dv := default }
    let d ← mkDecide Ps
    return { tm, ty := tyBool, pf := ← mkExpectedTypeHint pf (denE Γ tyBool tm ctx.rho d),
             val := d, dv := d, cpf }
  let primB (p : Expr) (inTy : Expr) (x : Res) : Expr :=
    mkAppN (mkConst ``Tm.prim) #[Γ, inTy, tyBool, p, x.tm]
  let pairR (x y : Res) : M (Expr × Expr × Expr × Option Expr) := do
    let ty := tyC `prod #[x.ty, y.ty]
    let tm := mkAppN (mkConst ``Tm.pair) #[Γ, x.ty, y.ty, x.tm, y.tm]
    let pf ← ifPf (mkAppM ``Den.pair #[x.pf, y.pf])
    let cpf ← costPf #[x.cpf, y.cpf] fun ys => mkAppM ``CEq.pair ys
    return (ty, tm, pf, cpf)
  let primC (p : Expr) (c : Option Expr) : M (Option Expr) :=
    costPf #[c] fun ys => mkAppM ``CEq.prim #[p, ys[0]!]
  let args := P.getAppArgs
  match P.getAppFn.constName?, args.size with
  | some ``Eq, 3 =>
    let T := args[0]!
    if (← whnf (ctx.subst T)).isConstOf ``Bool && args[2]!.consumeMData.isConstOf ``Bool.true then
      let r ← goP ctx args[1]!
      return ← fin r.tm (← ifPf (mkAppM ``Den.decBool #[r.pf]))
        (← costPf #[r.cpf] fun ys => mkAppM ``CEq.decBool ys)
    if let some n ← finMod? (ctx.subst T) then
      let (pty, ptm, ppf, pc) ← pairR (← goP ctx args[1]!) (← goP ctx args[2]!)
      let p := mkApp (mkConst ``Prim.finEq) n
      let tm := mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, p, ptm]
      return ← fin tm (← ifPf (mkAppM ``Den.prim #[p, ppf])) (← primC p pc)
    let some k ← numKind (ctx.subst T) | fail m!"the equality `{P}` at a type without a primitive"
    let (pty, ptm, ppf, pc) ← pairR (← goP ctx args[1]!) (← goP ctx args[2]!)
    let p := match k with | none => mkConst ``Prim.natEq | some w => mkApp (mkConst ``Prim.weq) w
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, p, ptm]
    fin tm (← ifPf (mkAppM ``Den.prim #[p, ppf])) (← primC p pc)
  | some ``Ne, 3 =>
    if let some n ← finMod? (ctx.subst args[0]!) then
      let (pty, ptm, ppf, pc) ← pairR (← goP ctx args[1]!) (← goP ctx args[2]!)
      let tm := mkAppN (mkConst ``Tm.prim) #[Γ, tyBool, tyBool, mkConst ``Prim.bnot,
        mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, mkApp (mkConst ``Prim.finEq) n, ptm]]
      return ← fin tm (← ifPf (mkAppM ``Den.finNe #[ppf]))
        (← costPf #[pc] fun ys => mkAppM ``CEq.finNe ys)
    let some k ← numKind (ctx.subst args[0]!) | fail m!"the disequality `{P}`"
    let (pty, ptm, ppf, pc) ← pairR (← goP ctx args[1]!) (← goP ctx args[2]!)
    let p := match k with | none => mkConst ``Prim.natEq | some w => mkApp (mkConst ``Prim.weq) w
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, tyBool, tyBool, mkConst ``Prim.bnot,
      mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, p, ptm]]
    fin tm (← ifPf (mkAppM (if k.isNone then ``Den.natNe else ``Den.wordNe) #[ppf]))
      (← costPf #[pc] fun ys => mkAppM (if k.isNone then ``CEq.natNe else ``CEq.wordNe) ys)
  | some ``LT.lt, 4 =>
    if let some n ← finMod? (ctx.subst args[0]!) then
      let (pty, ptm, ppf, pc) ← pairR (← goP ctx args[2]!) (← goP ctx args[3]!)
      let p := mkApp (mkConst ``Prim.finLt) n
      let tm := mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, p, ptm]
      return ← fin tm (← ifPf (mkAppM ``Den.prim #[p, ppf])) (← primC p pc)
    let some none ← numKind (ctx.subst args[0]!) | fail m!"the comparison `{P}` (only on ℕ)"
    let (pty, ptm, ppf, pc) ← pairR (← goP ctx args[2]!) (← goP ctx args[3]!)
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, mkConst ``Prim.natLt, ptm]
    fin tm (← ifPf (mkAppM ``Den.prim #[mkConst ``Prim.natLt, ppf]))
      (← primC (mkConst ``Prim.natLt) pc)
  | some ``LE.le, 4 =>
    let some none ← numKind (ctx.subst args[0]!) | fail m!"the comparison `{P}` (only on ℕ)"
    let (pty, ptm, ppf, pc) ← pairR (← goP ctx args[3]!) (← goP ctx args[2]!)
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, tyBool, tyBool, mkConst ``Prim.bnot,
      mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, mkConst ``Prim.natLt, ptm]]
    fin tm (← ifPf (mkAppM ``Den.natLe #[ppf])) (← costPf #[pc] fun ys => mkAppM ``CEq.natLe ys)
  | some ``And, 2 =>
    let x ← goDecide ctx args[0]!
    let y ← goDecide ctx args[1]!
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, tyC `prod #[tyBool, tyBool], tyBool,
      mkConst ``Prim.band, mkAppN (mkConst ``Tm.pair) #[Γ, tyBool, tyBool, x.tm, y.tm]]
    fin tm (← ifPf (mkAppM ``Den.decAnd #[x.pf, y.pf]))
      (← costPf #[x.cpf, y.cpf] fun ys => mkAppM ``CEq.decAnd ys)
  | some ``Or, 2 =>
    let x ← goDecide ctx args[0]!
    let y ← goDecide ctx args[1]!
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, tyC `prod #[tyBool, tyBool], tyBool,
      mkConst ``Prim.bor, mkAppN (mkConst ``Tm.pair) #[Γ, tyBool, tyBool, x.tm, y.tm]]
    fin tm (← ifPf (mkAppM ``Den.decOr #[x.pf, y.pf]))
      (← costPf #[x.cpf, y.cpf] fun ys => mkAppM ``CEq.decOr ys)
  | some ``Not, 1 =>
    let x ← goDecide ctx args[0]!
    fin (primB (mkConst ``Prim.bnot) tyBool x) (← ifPf (mkAppM ``Den.decNot #[x.pf]))
      (← costPf #[x.cpf] fun ys => mkAppM ``CEq.decNot ys)
  | _, _ => fail m!"the proposition `{P}` in a condition"

/-- A primitive operation applied to the translations of `xs` (paired when two). -/
partial def goPrim (ctx : Ctx) (e p inTy outTy : Expr) (xs : Array Expr) : M Res := do
  let Γ := ctx.gamma
  let rs ← xs.mapM (goP ctx)
  let (atm, apf, acpf) ← if h : rs.size = 2 then do
      let x := rs[0]; let y := rs[1]
      pure (mkAppN (mkConst ``Tm.pair) #[Γ, x.ty, y.ty, x.tm, y.tm],
        ← ifPf (mkAppM ``Den.pair #[x.pf, y.pf]),
        ← costPf #[x.cpf, y.cpf] fun ys => mkAppM ``CEq.pair ys)
    else pure (rs[0]!.tm, rs[0]!.pf, rs[0]!.cpf)
  let tm := mkAppN (mkConst ``Tm.prim) #[Γ, inTy, outTy, p, atm]
  finish ctx e tm outTy (← ifPf (mkAppM ``Den.prim #[p, apf])) none
    (← costPf #[acpf] fun ys => mkAppM ``CEq.prim #[p, ys[0]!])

/-- A binary arithmetic operation of source type `T`. -/
partial def goArith (ctx : Ctx) (e T : Expr) (nat : Option Name) (word : Option Name)
    (a b : Expr) : M Res := do
  if let some n ← finMod? (ctx.subst T) then
    let p ← match nat with
      | some ``Prim.natAdd => pure ``Prim.finAdd
      | some ``Prim.natSub => pure ``Prim.finSub
      | some ``Prim.natMul => pure ``Prim.finMul
      | _ => fail m!"the operation `{e}` at type `{T}`"
    let ty := tyBase (mkApp (mkConst ``FTy.fin) n)
    return ← goPrim ctx e (mkApp (mkConst p) n) (tyC `prod #[ty, ty]) ty #[a, b]
  let some k ← numKind (ctx.subst T) | fail m!"the operation `{e}` at type `{T}`"
  match k, nat, word with
  | none, some n, _ =>
    goPrim ctx e (mkConst n) (tyC `prod #[tyNat, tyNat]) tyNat #[a, b]
  | some w, _, some n =>
    goPrim ctx e (mkApp (mkConst n) w) (tyC `prod #[tyWord w, tyWord w]) (tyWord w) #[a, b]
  | _, _, _ => fail m!"the operation `{e}` at type `{T}`"

/-- Constants: literals, primitive operations, constructors, recursion schemes, branches. -/
partial def goConst (ctx : Ctx) (e : Expr) (c : Name) (args : Array Expr) : M Res := do
  let Γ := ctx.gamma
  let lit (f : Expr) : M Res := do
    if e.hasAnyFVar (fun fv => ctx.entries.any (·.fvar == fv)) then
      fail m!"the literal `{e}` depends on a variable"
    finish ctx e (mkApp3 (mkConst ``Tm.lit) Γ f e) (tyBase f)
      (← ifPf (mkAppM ``Den.lit #[f, e, ctx.rho])) none
      (← costPf #[] fun _ => mkAppM ``CEq.lit #[f, e, ctx.rho])
  match c, args.size with
  | ``OfNat.ofNat, 3 =>
    if let some n ← finMod? (ctx.subst args[0]!) then
      return ← lit (mkApp (mkConst ``FTy.fin) n)
    match ← numKind (ctx.subst args[0]!) with
    | some none =>
      finish ctx e (mkApp2 (mkConst ``Tm.natLit) Γ e) tyNat
        (← ifPf (mkAppM ``Den.natLit #[e, ctx.rho])) none
        (← costPf #[] fun _ => mkAppM ``CEq.natLit #[e, ctx.rho])
    | some (some w) => lit (mkApp (mkConst ``FTy.word) w)
    | none => fail m!"the numeral `{e}`"
  | ``BitVec.ofNat, 2 =>
    let w := args[0]!
    if isNumeral args[1]!.consumeMData then lit (mkApp (mkConst ``FTy.word) w)
    else goPrim ctx e (mkApp (mkConst ``Prim.wofNat) w) tyNat (tyWord w) #[args[1]!]
  | ``Bool.true, 0 | ``Bool.false, 0 => lit (mkConst ``FTy.bool)
  | ``PUnit.unit, 0 | ``Unit.unit, 0 => lit (mkConst ``FTy.unit)
  | ``HAdd.hAdd, 6 => goArith ctx e args[0]! (some ``Prim.natAdd) (some ``Prim.wadd) args[4]! args[5]!
  | ``HSub.hSub, 6 => goArith ctx e args[0]! (some ``Prim.natSub) (some ``Prim.wsub) args[4]! args[5]!
  | ``HMul.hMul, 6 => goArith ctx e args[0]! (some ``Prim.natMul) (some ``Prim.wmul) args[4]! args[5]!
  | ``HDiv.hDiv, 6 => goArith ctx e args[0]! (some ``Prim.natDiv) none args[4]! args[5]!
  | ``HMod.hMod, 6 => goArith ctx e args[0]! (some ``Prim.natMod) none args[4]! args[5]!
  | ``HAnd.hAnd, 6 => goArith ctx e args[0]! none (some ``Prim.wand) args[4]! args[5]!
  | ``HOr.hOr, 6 => goArith ctx e args[0]! none (some ``Prim.wor) args[4]! args[5]!
  | ``HXor.hXor, 6 => goArith ctx e args[0]! none (some ``Prim.wxor) args[4]! args[5]!
  | ``HShiftLeft.hShiftLeft, 6 | ``HShiftRight.hShiftRight, 6 =>
    let some (some w) ← numKind (ctx.subst args[0]!) | fail m!"the shift `{e}`"
    let some none ← numKind (ctx.subst args[1]!) | fail m!"the shift `{e}` by a non-ℕ amount"
    let p := mkApp (mkConst (if c == ``HShiftLeft.hShiftLeft then ``Prim.wshl else ``Prim.wshr)) w
    goPrim ctx e p (tyC `prod #[tyWord w, tyNat]) (tyWord w) #[args[4]!, args[5]!]
  | ``Complement.complement, 3 =>
    let some (some w) ← numKind (ctx.subst args[0]!) | fail m!"the complement `{e}`"
    goPrim ctx e (mkApp (mkConst ``Prim.wnot) w) (tyWord w) (tyWord w) #[args[2]!]
  | ``and, 2 => goPrim ctx e (mkConst ``Prim.band) (tyC `prod #[tyBool, tyBool]) tyBool args
  | ``or, 2 => goPrim ctx e (mkConst ``Prim.bor) (tyC `prod #[tyBool, tyBool]) tyBool args
  | ``xor, 2 =>
    goPrim ctx e (mkConst ``Prim.bxor) (tyC `prod #[tyBool, tyBool]) tyBool args
  | ``not, 1 => goPrim ctx e (mkConst ``Prim.bnot) tyBool tyBool args
  | ``BitVec.toNat, 2 =>
    let w := args[0]!
    goPrim ctx e (mkApp (mkConst ``Prim.wtoNat) w) (tyWord w) tyNat #[args[1]!]
  | ``BitVec.setWidth, 3 =>
    let w := args[0]!; let v := args[1]!
    if v.hasFVar then fail m!"the width of `{e}` depends on a variable"
    goPrim ctx e (mkApp2 (mkConst ``Prim.wcast) w v) (tyWord w) (tyWord v) #[args[2]!]
  | ``Fin.val, 2 =>
    let n ← modPred (ctx.subst args[0]!)
    goPrim ctx e (mkApp (mkConst ``Prim.finToNat) n) (tyBase (mkApp (mkConst ``FTy.fin) n))
      tyNat #[args[1]!]
  | `ZMod.val, 2 =>
    let n ← modPred (ctx.subst args[0]!)
    goPrim ctx e (mkApp (mkConst ``Prim.finToNat) n) (tyBase (mkApp (mkConst ``FTy.fin) n))
      tyNat #[args[1]!]
  | ``Nat.cast, 3 =>
    let some n ← finMod? (ctx.subst args[0]!) | fail m!"the cast `{e}`"
    goPrim ctx e (mkApp (mkConst ``Prim.finOfNat) n) tyNat
      (tyBase (mkApp (mkConst ``FTy.fin) n)) #[args[2]!]
  | ``Decidable.decide, 2 =>
    let r ← goDecide ctx args[0]!
    finish ctx e r.tm tyBool r.pf none r.cpf
  | ``Prod.mk, 4 =>
    let x ← goP ctx args[2]!
    let y ← goP ctx args[3]!
    finish ctx e (mkAppN (mkConst ``Tm.pair) #[Γ, x.ty, y.ty, x.tm, y.tm])
      (tyC `prod #[x.ty, y.ty]) (← ifPf (mkAppM ``Den.pair #[x.pf, y.pf])) none
      (← costPf #[x.cpf, y.cpf] fun ys => mkAppM ``CEq.pair ys)
  | ``Prod.fst, 3 | ``Prod.snd, 3 =>
    let rs ← goP ctx args[2]!
    let some (a, b) := tyArgs2 `prod rs.ty | fail m!"the projection `{e}`"
    let fst := c == ``Prod.fst
    finish ctx e (mkAppN (mkConst (if fst then ``Tm.fst else ``Tm.snd)) #[Γ, a, b, rs.tm])
      (if fst then a else b) (← ifPf (mkAppM (if fst then ``Den.fst else ``Den.snd) #[rs.pf]))
      none (← costPf #[rs.cpf] fun ys => mkAppM (if fst then ``CEq.fst else ``CEq.snd) ys)
  | ``Sum.inl, 3 =>
    let (b, _) ← tyOf (ctx.subst args[1]!)
    let x ← goP ctx args[2]!
    finish ctx e (mkAppN (mkConst ``Tm.inl) #[Γ, x.ty, b, x.tm]) (tyC `sum #[x.ty, b])
      (← ifPf (mkAppOptM ``Den.inl #[none, none, none, b, none, none, x.pf]))
  | ``Sum.inr, 3 =>
    let (a, _) ← tyOf (ctx.subst args[0]!)
    let x ← goP ctx args[2]!
    finish ctx e (mkAppN (mkConst ``Tm.inr) #[Γ, a, x.ty, x.tm]) (tyC `sum #[a, x.ty])
      (← ifPf (mkAppOptM ``Den.inr #[none, none, a, none, none, none, x.pf]))
  | ``Option.some, 2 =>
    let x ← goP ctx args[1]!
    finish ctx e (mkAppN (mkConst ``Tm.inr) #[Γ, tyUnit, x.ty, x.tm]) (tyC `sum #[tyUnit, x.ty])
      (← ifPf (mkAppOptM ``Den.inr #[none, none, tyUnit, none, none, none, x.pf]))
  | ``Option.none, 1 =>
    let (a, _) ← tyOf (ctx.subst args[0]!)
    let u := Lean.mkConst ``PUnit.unit [Level.one]
    let utm := mkApp3 (mkConst ``Tm.lit) Γ (mkConst ``FTy.unit) u
    let upf ← ifPf (mkAppM ``Den.lit #[mkConst ``FTy.unit, u, ctx.rho])
    finish ctx e (mkAppN (mkConst ``Tm.inl) #[Γ, tyUnit, a, utm]) (tyC `sum #[tyUnit, a])
      (← ifPf (mkAppOptM ``Den.inl #[none, none, tyUnit, a, none, none, upf]))
  | ``List.nil, 1 =>
    let (a, _) ← tyOf (ctx.subst args[0]!)
    finish ctx e (mkApp2 (mkConst ``Tm.nil) Γ a) (tyC `list #[a])
      (← ifPf (mkAppOptM ``Den.nil #[none, a, ctx.rho]))
  | ``List.cons, 3 =>
    let x ← goP ctx args[1]!
    let xs ← goP ctx args[2]!
    finish ctx e (mkAppN (mkConst ``Tm.cons) #[Γ, x.ty, x.tm, xs.tm]) xs.ty
      (← ifPf (mkAppM ``Den.cons #[x.pf, xs.pf]))
  | ``List.foldl, 5 => goFoldl ctx e args[0]! args[1]! args[2]! args[3]! args[4]!
  | ``Nat.iterate, 4 => goIter ctx e args[0]! args[1]! args[2]! args[3]!
  | ``ite, 5 =>
    let (cTy, β, E) ← branchRep (ctx.subst args[0]!)
    let rc ← goDecide ctx args[1]!
    let rt ← goP ctx args[3]!
    let re ← goP ctx args[4]!
    let P := ctx.subst args[1]!; let inst := ctx.subst args[2]!
    let tm := mkAppN (mkConst ``Tm.ite) #[Γ, cTy, rc.tm, rt.tm, re.tm]
    let pf ← ifPf do
      let hb ← mkExpectedTypeHint rc.pf
        (denE Γ tyBool rc.tm ctx.rho (mkApp2 (mkConst ``Decidable.decide) P inst))
      return mkAppN (mkConst ``Den.ite) #[Γ, ctx.rho, cTy, β, E, P, inst, rc.tm, rt.tm, re.tm,
        rt.val, re.val, hb, rt.pf, re.pf]
    let cpf ← costPf #[rc.cpf, rt.cpf, re.cpf] fun ys =>
      mkAppOptM ``CEq.ite #[none, none, none, β, E, P, inst, none, none, none, none, none, none,
        rt.val, re.val, ys[0]!, ys[1]!, ys[2]!]
    finish ctx e tm cTy pf none cpf
  | ``cond, 4 => goCond ctx e args[0]! args[1]! args[2]! args[3]!
  | ``Bool.casesOn, 4 =>
    goCond ctx e (← inferType (ctx.subst e)) args[1]! args[3]!.headBeta args[2]!.headBeta
  | ``Option.casesOn, 5 => goCaseOpt ctx e args[0]! args[2]! args[3]!.headBeta args[4]!
  | ``Sum.casesOn, 6 => goCaseSum ctx e args[0]! args[1]! args[3]! args[4]! args[5]!
  | ``List.casesOn, 5 => goLcase ctx e args[0]! args[2]! args[3]!.headBeta args[4]!
  | ``Prod.casesOn, 5 => goProdCase ctx e args[3]! args[4]! false
  | ``Sum.elim, 6 => goCaseSum ctx e args[0]! args[1]! args[5]! args[3]! args[4]!
  | ``Option.elim, 5 => goCaseOpt ctx e args[0]! args[2]! args[3]! args[4]!
  | ``id, 2 =>
    let r ← goP ctx args[1]!
    finish ctx e r.tm r.ty r.pf r.fn r.cpf
  | _, _ =>
    if (← isMatcher c) || (← unfoldable c) then goP ctx (← deltaApp c e)
    else if c.isStr && (c.getString! == "brecOn" || c.getString! == "rec") then
      fail m!"the recursion `{c}` (use List.foldl or Nat.iterate)"
    else fail m!"the constant `{c}` in `{e}`"

partial def goCond (ctx : Ctx) (e T b t f : Expr) : M Res := do
  let Γ := ctx.gamma
  let (cTy, β, E) ← branchRep (ctx.subst T)
  let rb ← goP ctx b
  let rt ← goP ctx t
  let rf ← goP ctx f
  let tm := mkAppN (mkConst ``Tm.ite) #[Γ, cTy, rb.tm, rt.tm, rf.tm]
  let pf ← ifPf (return mkAppN (mkConst ``Den.cond) #[Γ, ctx.rho, cTy, β, E, rb.tm, rt.tm,
    rf.tm, rb.val, rt.val, rf.val, rb.pf, rt.pf, rf.pf])
  finish ctx e tm cTy pf

/-- The branch of a constructor with `n` fields, as a λ-term of `n` binders. -/
partial def goCaseOpt (ctx : Ctx) (e α o nb sb : Expr) : M Res := do
  let Γ := ctx.gamma
  let (cTy, β, E) ← branchRep (← inferType (ctx.subst e))
  let (aTy, _) ← tyOf (ctx.subst α)
  let ro ← goP ctx o
  let u := Lean.mkConst ``PUnit.unit [Level.one]
  let dummy ← mkFreshFVarId
  let ctxN := (ctx.bind tyUnit u).push
    { fvar := dummy, level := ctx.depth, path := [], baseTy := tyUnit, val := u, dval := u }
  let rn ← goP ctxN nb
  let sb ← etaN ctx sb 1
  let .lam n T body _ := sb | fail m!"the branch `{sb}`"
  let (rs, hr, S) ← withGeneric ctx n T [] ctx.depth aTy fun x en => do
    let rs ← goP ((ctx.bind aTy x).push en) (body.instantiate1 x)
    return (rs, ← ifPf (mkLambdaFVars #[x] rs.pf), ← mkLambdaFVars #[x] rs.val)
  let tm := mkAppN (mkConst ``Tm.case) #[Γ, tyUnit, aTy, cTy, ro.tm, rn.tm, rs.tm]
  let pf ← ifPf (return mkAppN (mkConst ``Den.caseOpt) #[Γ, ctx.rho, aTy, cTy, β, E, ro.tm,
    rn.tm, rs.tm, ro.val, rn.val, S, ro.pf, rn.pf, hr])
  finish ctx e tm cTy pf

partial def goCaseSum (ctx : Ctx) (e α β' s lb rb : Expr) : M Res := do
  let Γ := ctx.gamma
  let (cTy, β, E) ← branchRep (← inferType (ctx.subst e))
  let (aTy, _) ← tyOf (ctx.subst α)
  let (bTy, _) ← tyOf (ctx.subst β')
  let rs ← goP ctx s
  let branch (br : Expr) (ty : Expr) : M (Res × Expr × Expr) := do
    let br ← etaN ctx br 1
    let .lam n T body _ := br | fail m!"the branch `{br}`"
    withGeneric ctx n T [] ctx.depth ty fun x en => do
      let r ← goP ((ctx.bind ty x).push en) (body.instantiate1 x)
      return (r, ← ifPf (mkLambdaFVars #[x] r.pf), ← mkLambdaFVars #[x] r.val)
  let (rl, hl, L) ← branch lb aTy
  let (rr, hr, R) ← branch rb bTy
  let tm := mkAppN (mkConst ``Tm.case) #[Γ, aTy, bTy, cTy, rs.tm, rl.tm, rr.tm]
  let pf ← ifPf (return mkAppN (mkConst ``Den.case) #[Γ, ctx.rho, aTy, bTy, cTy, β, E, rs.tm,
    rl.tm, rr.tm, rs.val, L, R, rs.pf, hl, hr])
  finish ctx e tm cTy pf

partial def goLcase (ctx : Ctx) (e α l nb cb : Expr) : M Res := do
  let Γ := ctx.gamma
  let (cTy, β, E) ← branchRep (← inferType (ctx.subst e))
  let (aTy, _) ← tyOf (ctx.subst α)
  let lTy := tyC `list #[aTy]
  let rl ← goP ctx l
  let rn ← goP ctx nb
  let cb ← etaN ctx cb 2
  let .lam n1 T1 (.lam n2 T2 body _) _ := cb | fail m!"the branch `{cb}`"
  let (rc, hk, C) ← withGeneric ctx n1 T1 [] (ctx.depth + 1) aTy fun x enx => do
    withGeneric ctx n2 (T2.instantiate1 x) [] ctx.depth lTy fun xs enxs => do
      let ctx' := ((ctx.bind lTy xs).bind aTy x).push enxs |>.push enx
      let rc ← goP ctx' (body.instantiate #[xs, x])
      return (rc, ← ifPf (mkLambdaFVars #[x, xs] rc.pf), ← mkLambdaFVars #[x, xs] rc.val)
  let tm := mkAppN (mkConst ``Tm.lcase) #[Γ, aTy, cTy, rl.tm, rn.tm, rc.tm]
  let pf ← ifPf (return mkAppN (mkConst ``Den.lcase) #[Γ, ctx.rho, aTy, cTy, β, E, rl.tm, rn.tm,
    rc.tm, rl.val, rn.val, C, rl.pf, rn.pf, hk])
  finish ctx e tm cTy pf

/-- A match on a pair: projections of a variable, or a `letE` of the scrutinee. -/
partial def goProdCase (ctx : Ctx) (e p k : Expr) (eff : Bool) : M Res := do
  let Γ := ctx.gamma
  let k ← etaN ctx k 2
  let .lam _ _ (.lam _ _ body _) _ := k | fail m!"the match `{k}`"
  let fa ← mkFreshFVarId
  let fb ← mkFreshFVarId
  let body := body.instantiate #[mkFVar fb, mkFVar fa]
  let pv := p.consumeMData
  if let .fvar fv := pv then
    if let some en := ctx.entries.find? (·.fvar == fv) then
      if en.fn.isNone then
        let va ← mkAppM ``Prod.fst #[en.val]
        let vb ← mkAppM ``Prod.snd #[en.val]
        let ea : Entry := { en with fvar := fa, path := en.path ++ [false], val := va }
        let eb : Entry := { en with fvar := fb, path := en.path ++ [true], val := vb }
        let ctx' := (ctx.push { ea with dval := va }).push { eb with dval := vb }
        let r ← if eff then goM ctx' body else goP ctx' body
        if eff then return ← finishM ctx e r.tm r.ty r.pf
        return ← finish ctx e r.tm r.ty r.pf
  let rp ← goP ctx p
  let va ← mkAppM ``Prod.fst #[rp.val]
  let vb ← mkAppM ``Prod.snd #[rp.val]
  let base := { fvar := fa, level := ctx.depth, path := [false], baseTy := rp.ty, val := va,
                dval := va : Entry }
  let ctx' := ((ctx.bind rp.ty rp.dv).push base).push
    { base with fvar := fb, path := [true], val := vb, dval := vb }
  let r ← if eff then goM ctx' body else goP ctx' body
  let tm := mkAppN (mkConst ``Tm.letE) #[Γ, rp.ty, r.ty, rp.tm, r.tm]
  if eff then
    finishM ctx e tm r.ty (← ifPf (denMApp ctx ``DenM.letEPure #[rp.pf, r.pf]))
      (← costPf #[rp.cpf, r.cpf] fun ys => mkAppM ``CLe.letEPure ys)
  else
    finish ctx e tm r.ty (← ifPf (mkAppM ``Den.letE #[rp.pf, r.pf])) none
      (← costPf #[rp.cpf, r.cpf] fun ys => mkAppM ``CEq.letE ys)

/-- `List.foldl f i l` as `foldl`. -/
partial def goFoldl (ctx : Ctx) (e α β' f i l : Expr) : M Res := do
  let Γ := ctx.gamma
  let (cTy, _) ← tyOf (ctx.subst α)
  let (aTy, _) ← tyOf (ctx.subst β')
  let pTy := tyC `prod #[cTy, aTy]
  let f ← etaN ctx f 2
  let .lam _ T1 (.lam _ _ body _) _ := f | fail m!"the step function `{f}`"
  let fa ← mkFreshFVarId
  let fx ← mkFreshFVarId
  let body := body.instantiate #[mkFVar fx, mkFVar fa]
  let pT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (ctx.subst T1) (ctx.subst β')
  let step (syn : Bool) : M (Res × Expr) := withReader (fun s => s || syn) do
    withLocalDeclD `p pT fun p => do
      let va ← mkAppM ``Prod.fst #[p]
      let vb ← mkAppM ``Prod.snd #[p]
      let ea : Entry :=
        { fvar := fa, level := ctx.depth, path := [false], baseTy := pTy, val := va, dval := va }
      let eb : Entry :=
        { fvar := fx, level := ctx.depth, path := [true], baseTy := pTy, val := vb, dval := vb }
      let ctx' := ((ctx.bind pTy p).push ea).push eb
      let r ← goP ctx' body
      return (r, ← ifPf (mkLambdaFVars #[p] r.pf))
  let (rb, _) ← step true
  let tmF := mkAppN (mkConst ``Tm.lam) #[Γ, pTy, cTy, rb.tm]
  let ri ← goP ctx i
  let rl ← goP ctx l
  let tm := mkAppN (mkConst ``Tm.foldl) #[Γ, aTy, cTy, tmF, ri.tm, rl.tm]
  let pf ← ifPf do
    let (_, hs) ← step false
    let hf ← mkAppM ``Den.lam #[rb.tm, ctx.rho]
    let F := (← inferType hf).appArg!
    return mkAppN (mkConst ``Den.foldl) #[Γ, ctx.rho, aTy, cTy, tmF, ri.tm, rl.tm, F,
      ctx.subst f, ri.dv, rl.dv, hf, hs, ri.pf, rl.pf]
  finish ctx e tm cTy pf

/-- `Nat.iterate f n a` as `iter`. -/
partial def goIter (ctx : Ctx) (e α f n a : Expr) : M Res := do
  let Γ := ctx.gamma
  let (cTy, _) ← tyOf (ctx.subst α)
  let f ← etaN ctx f 1
  let .lam nm T body _ := f | fail m!"the iterated function `{f}`"
  let step (syn : Bool) : M (Res × Expr) := withReader (fun s => s || syn) do
    withGeneric ctx nm T [] ctx.depth cTy fun x en => do
      let r ← goP ((ctx.bind cTy x).push en) (body.instantiate1 x)
      return (r, ← ifPf (mkLambdaFVars #[x] r.pf))
  let (rb, _) ← step true
  let tmF := mkAppN (mkConst ``Tm.lam) #[Γ, cTy, cTy, rb.tm]
  let rn ← goP ctx n
  let ra ← goP ctx a
  let tm := mkAppN (mkConst ``Tm.iter) #[Γ, cTy, rn.tm, tmF, ra.tm]
  let pf ← ifPf do
    let (_, hs) ← step false
    let hf ← mkAppM ``Den.lam #[rb.tm, ctx.rho]
    let F := (← inferType hf).appArg!
    return mkAppN (mkConst ``Den.iter) #[Γ, ctx.rho, cTy, rn.tm, tmF, ra.tm, rn.dv, F,
      ctx.subst f, ra.dv, rn.pf, hf, hs, ra.pf]
  finish ctx e tm cTy pf

/-- Translate a source term of type `SPComp α`. -/
partial def goM (ctx : Ctx) (e : Expr) : M Res := do
  let e := e.consumeMData
  let Γ := ctx.gamma
  match e with
  | .letE _ _ v b _ =>
    let rv ← goP ctx v
    let y ← mkFreshFVarId
    let ctx' := (ctx.bind rv.ty rv.dv).push
      { fvar := y, level := ctx.depth, path := [], baseTy := rv.ty, val := rv.val,
        dval := rv.dv, fn := rv.fn }
    let rb ← goM ctx' (b.instantiate1 (mkFVar y))
    let tm := mkAppN (mkConst ``Tm.letE) #[Γ, rv.ty, rb.ty, rv.tm, rb.tm]
    finishM ctx e tm rb.ty (← ifPf (denMApp ctx ``DenM.letEPure #[rv.pf, rb.pf]))
      (← costPf #[rv.cpf, rb.cpf] fun ys => mkAppM ``CLe.letEPure ys)
  | _ =>
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  match fn with
  | .const c _ =>
    match c, args.size with
    | ``Bind.bind, 6 => goBind ctx e args[4]! args[5]!
    | ``SPComp.bind, 4 => goBind ctx e args[2]! args[3]!
    | ``Pure.pure, 4 | ``SPComp.pure, 2 =>
      let r ← goP ctx args.back!
      finishM ctx e r.tm r.ty (← ifPf (denMApp ctx ``DenM.pure #[r.pf]))
        (← costPf #[r.cpf] fun ys => mkAppM ``CLe.ofEq ys)
    | ``SPComp.sample, 3 =>
      let f ← ftyOf (ctx.subst args[0]!)
      let tm := mkApp2 (mkConst ``Tm.sample) Γ f
      finishM ctx e tm (tyBase f) (← ifPf (mkAppOptM ``DenM.sample
        #[ctx.oracle, none, f, ctx.rho, ctx.subst args[1]!, ctx.subst args[2]!]))
        (← costPf #[] fun _ => mkAppM ``CLe.sample #[f, ctx.rho])
    | ``SPComp.fail, 1 =>
      let (τ, _) ← tyOf (ctx.subst args[0]!)
      finishM ctx e (mkApp2 (mkConst ``Tm.fail) Γ τ) τ
        (← ifPf (mkAppOptM ``DenM.fail #[ctx.oracle, none, τ, ctx.rho]))
        (← costPf #[] fun _ => mkAppOptM ``CLe.fail #[none, τ, ctx.rho])
    | ``SPComp.get, 1 =>
      let (n, f) ← location (ctx.subst args[0]!)
      finishM ctx e (mkApp3 (mkConst ``Tm.get) Γ n f) (tyBase f)
        (← ifPf (denMApp ctx ``DenM.get #[n, f, ctx.rho]))
        (← costPf #[] fun _ => mkAppM ``CLe.get #[n, f, ctx.rho])
    | ``SPComp.set, 2 =>
      let (n, f) ← location (ctx.subst args[0]!)
      let rv ← goP ctx args[1]!
      finishM ctx e (mkAppN (mkConst ``Tm.set) #[Γ, n, f, rv.tm]) tyUnit
        (← ifPf (denMApp ctx ``DenM.set #[n, f, rv.pf]))
        (← costPf #[rv.cpf] fun ys => mkAppM ``CLe.set #[n, f, ys[0]!])
    | ``ite, 5 =>
      let rc ← goDecide ctx args[1]!
      let rt ← goM ctx args[3]!
      let re ← goM ctx args[4]!
      let P := ctx.subst args[1]!; let inst := ctx.subst args[2]!
      let tm := mkAppN (mkConst ``Tm.ite) #[Γ, rt.ty, rc.tm, rt.tm, re.tm]
      let pf ← ifPf do
        let hb ← mkExpectedTypeHint rc.pf
          (denE Γ tyBool rc.tm ctx.rho (mkApp2 (mkConst ``Decidable.decide) P inst))
        mkAppOptM ``DenM.ite #[ctx.oracle, none, none, none, P, inst, none, none, none, none,
          none, hb, rt.pf, re.pf]
      finishM ctx e tm rt.ty pf (← iteCost P inst rc rt re)
    | ``cond, 4 => goCondM ctx e args[1]! args[2]! args[3]!
    | ``Bool.casesOn, 4 => goCondM ctx e args[1]! args[3]!.headBeta args[2]!.headBeta
    | ``Option.casesOn, 5 =>
      let (aTy, _) ← tyOf (ctx.subst args[0]!)
      let ro ← goP ctx args[2]!
      let u := Lean.mkConst ``PUnit.unit [Level.one]
      let dummy ← mkFreshFVarId
      let eu : Entry :=
        { fvar := dummy, level := ctx.depth, path := [], baseTy := tyUnit, val := u, dval := u }
      let rn ← goM ((ctx.bind tyUnit u).push eu) args[3]!.headBeta
      let sb ← etaN ctx args[4]! 1
      let .lam n T body _ := sb | fail m!"the branch `{sb}`"
      let (rs, hr, S) ← withGeneric ctx n T [] ctx.depth aTy fun x en => do
        let rs ← goM ((ctx.bind aTy x).push en) (body.instantiate1 x)
        return (rs, ← ifPf (mkLambdaFVars #[x] rs.pf), ← mkLambdaFVars #[x] rs.val)
      let tm := mkAppN (mkConst ``Tm.case) #[Γ, tyUnit, aTy, rn.ty, ro.tm, rn.tm, rs.tm]
      finishM ctx e tm rn.ty (← ifPf (return mkAppN (mkConst ``DenM.caseOpt) #[ctx.oracle, Γ,
        ctx.rho, aTy, rn.ty, ro.tm, rn.tm, rs.tm, ro.val, rn.val, S, ro.pf, rn.pf, hr]))
    | ``Prod.casesOn, 5 => goProdCase ctx e args[3]! args[4]! true
    | _, _ =>
      if (← isMatcher c) || (← unfoldable c) then goM ctx (← deltaApp c e)
      else fail m!"the computation `{e}` (head `{c}`)"
  | .fvar _ | .lam .. =>
    let rm ← applyAll ctx e fn args true
    if ← synMode then return rm
    finishM ctx e rm.tm rm.ty rm.pf rm.cpf
  | _ => fail m!"the computation `{e}`"

partial def goCondM (ctx : Ctx) (e b t f : Expr) : M Res := do
  let Γ := ctx.gamma
  let rb ← goP ctx b
  let rt ← goM ctx t
  let rf ← goM ctx f
  let tm := mkAppN (mkConst ``Tm.ite) #[Γ, rt.ty, rb.tm, rt.tm, rf.tm]
  finishM ctx e tm rt.ty (← ifPf (return mkAppN (mkConst ``DenM.cond) #[ctx.oracle, Γ, ctx.rho,
    rt.ty, rb.tm, rt.tm, rf.tm, rb.val, rt.val, rf.val, rb.pf, rt.pf, rf.pf]))

/-- The cost derivation of a continuation under the binder `x`, and whether its bound
depends on `x`. -/
partial def contCost (x : Expr) (cpf : Option Expr) : M (Option Expr × Bool) := do
  match cpf with
  | some p =>
    let dep := (← costOf p).containsFVar x.fvarId!
    return (← costPf #[cpf] fun ys => mkLambdaFVars #[x] ys[0]!, dep)
  | none => return (none, false)

/-- The cost of a `letE` of a computation of D type `ty` followed by a continuation: the
continuation's bound is uniform, or a maximum over a finite ground type. -/
partial def bindCost (rc hk : Option Expr) (dep : Bool) (ty : Expr) : M (Option Expr) :=
  costPf #[rc, hk] fun ys => do
    if !dep then mkAppM ``CLe.letE ys
    else if ty.isAppOfArity ``Ty.base 1 then mkAppM ``CLe.letESup ys
    else throwError "the cost of the continuation depends on a value of an infinite type"

/-- The cost of a conditional on `decide P` over two computations. -/
partial def iteCost (P inst : Expr) (rc rt re : Res) : M (Option Expr) :=
  costPf #[rc.cpf, rt.cpf, re.cpf] fun ys =>
    mkAppOptM ``CLe.ite #[none, none, none, P, inst, none, none, none, none, none, none,
      ys[0]!, ys[1]!, ys[2]!]

/-- `bind c k` as `letE`. -/
partial def goBind (ctx : Ctx) (e c k : Expr) : M Res := do
  let Γ := ctx.gamma
  let rc ← goM ctx c
  let k ← etaN ctx k 1
  let .lam n T body _ := k | fail m!"the continuation `{k}`"
  let (rb, hk, K, hkc, dep) ← withGeneric ctx n T [] ctx.depth rc.ty fun x en => do
    let rb ← goM ((ctx.bind rc.ty x).push en) (body.instantiate1 x)
    let (hkc, dep) ← contCost x rb.cpf
    return (rb, ← ifPf (mkLambdaFVars #[x] rb.pf), ← mkLambdaFVars #[x] rb.val, hkc, dep)
  let tm := mkAppN (mkConst ``Tm.letE) #[Γ, rc.ty, rb.ty, rc.tm, rb.tm]
  finishM ctx e tm rb.ty (← ifPf (return mkAppN (mkConst ``DenM.letE) #[ctx.oracle, Γ, ctx.rho,
    rc.ty, rb.ty, rc.tm, rb.tm, rc.val, K, rc.pf, hk])) (← bindCost rc.cpf hkc dep rc.ty)

/-- A continuation `k` of a tree node with a binder of D type `ty`, translated as a tree. -/
partial def treeCont (ctx : Ctx) (k ty : Expr) : M (Res × Expr × Option Expr × Bool) := do
  let k ← etaN ctx k 1
  let .lam n T body _ := k | fail m!"the continuation `{k}`"
  withGeneric ctx n T [] ctx.depth ty fun x en => do
    let rb ← goT ((ctx.bind ty x).push en) (body.instantiate1 x)
    let (hkc, dep) ← contCost x rb.cpf
    return (rb, ← ifPf (mkLambdaFVars #[x] rb.pf), hkc, dep)

/-- A computation tree (`SPTree`): its meaning is its compilation (`DenM.tree*`). -/
partial def goT (ctx : Ctx) (e : Expr) : M Res := do
  let e := e.consumeMData
  let Γ := ctx.gamma
  match e with
  | .letE _ _ v b _ =>
    let rv ← goP ctx v
    let y ← mkFreshFVarId
    let ctx' := (ctx.bind rv.ty rv.dv).push
      { fvar := y, level := ctx.depth, path := [], baseTy := rv.ty, val := rv.val,
        dval := rv.dv, fn := rv.fn }
    let rb ← goT ctx' (b.instantiate1 (mkFVar y))
    let tm := mkAppN (mkConst ``Tm.letE) #[Γ, rv.ty, rb.ty, rv.tm, rb.tm]
    finishT ctx e tm rb.ty (← ifPf (denMApp ctx ``DenM.letEPure #[rv.pf, rb.pf]))
      (← costPf #[rv.cpf, rb.cpf] fun ys => mkAppM ``CLe.letEPure ys)
  | _ =>
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  match fn with
  | .const c _ =>
    match c, args.size with
    | ``SPTree.ret, 2 =>
      let r ← goP ctx args[1]!
      finishT ctx e r.tm r.ty (← ifPf (denMApp ctx ``DenM.treeRet #[r.pf]))
        (← costPf #[r.cpf] fun ys => mkAppM ``CLe.ofEq ys)
    | ``SPTree.fail, 1 =>
      let (τ, _) ← tyOf (ctx.subst args[0]!)
      finishT ctx e (mkApp2 (mkConst ``Tm.fail) Γ τ) τ
        (← ifPf (mkAppOptM ``DenM.treeFail #[ctx.oracle, none, τ, ctx.rho]))
        (← costPf #[] fun _ => mkAppOptM ``CLe.fail #[none, τ, ctx.rho])
    | ``SPTree.sample, 5 =>
      let f ← ftyOf (ctx.subst args[1]!)
      let ty := tyBase f
      let (rb, hk, hkc, dep) ← treeCont ctx args[4]! ty
      let tm := mkAppN (mkConst ``Tm.letE) #[Γ, ty, rb.ty, mkApp2 (mkConst ``Tm.sample) Γ f,
        rb.tm]
      let pf ← ifPf (mkAppOptM ``DenM.treeSample #[ctx.oracle, none, none, none, f,
        ctx.subst args[2]!, ctx.subst args[3]!, none, none, hk])
      let sc ← costPf #[] fun _ => mkAppM ``CLe.sample #[f, ctx.rho]
      finishT ctx e tm rb.ty pf (← bindCost sc hkc dep ty)
    | ``SPTree.get, 3 =>
      let (n, f) ← location (ctx.subst args[1]!)
      let ty := tyBase f
      let (rb, hk, hkc, dep) ← treeCont ctx args[2]! ty
      let tm := mkAppN (mkConst ``Tm.letE) #[Γ, ty, rb.ty, mkApp3 (mkConst ``Tm.get) Γ n f,
        rb.tm]
      let pf ← ifPf (mkAppOptM ``DenM.treeGet #[ctx.oracle, none, none, none, n, f, none,
        none, hk])
      let gc ← costPf #[] fun _ => mkAppM ``CLe.get #[n, f, ctx.rho]
      finishT ctx e tm rb.ty pf (← bindCost gc hkc dep ty)
    | ``SPTree.set, 4 =>
      let (n, f) ← location (ctx.subst args[1]!)
      let rv ← goP ctx args[2]!
      let unitT := mkConst ``Unit
      let (rb, hk, hkc, dep) ← withGeneric ctx `u unitT [] ctx.depth tyUnit fun x en => do
        let rb ← goT ((ctx.bind tyUnit x).push en) args[3]!
        let (hkc, dep) ← contCost x rb.cpf
        return (rb, ← ifPf (mkLambdaFVars #[x] rb.pf), hkc, dep)
      let tm := mkAppN (mkConst ``Tm.letE) #[Γ, tyUnit, rb.ty,
        mkAppN (mkConst ``Tm.set) #[Γ, n, f, rv.tm], rb.tm]
      let pf ← ifPf (mkAppOptM ``DenM.treeSet #[ctx.oracle, none, none, none, n, f, none, none,
        none, none, rv.pf, hk])
      let sc ← costPf #[rv.cpf] fun ys => mkAppM ``CLe.set #[n, f, ys[0]!]
      finishT ctx e tm rb.ty pf (← bindCost sc hkc dep tyUnit)
    | ``SPTree.bind, 4 =>
      let rc ← goT ctx args[2]!
      let (rb, hk, hkc, dep) ← treeCont ctx args[3]! rc.ty
      let tm := mkAppN (mkConst ``Tm.letE) #[Γ, rc.ty, rb.ty, rc.tm, rb.tm]
      let pf ← ifPf (denMApp ctx ``DenM.treeBind #[rc.pf, hk])
      finishT ctx e tm rb.ty pf (← bindCost rc.cpf hkc dep rc.ty)
    | ``ite, 5 =>
      let rc ← goDecide ctx args[1]!
      let rt ← goT ctx args[3]!
      let re ← goT ctx args[4]!
      let P := ctx.subst args[1]!; let inst := ctx.subst args[2]!
      let tm := mkAppN (mkConst ``Tm.ite) #[Γ, rt.ty, rc.tm, rt.tm, re.tm]
      let pf ← ifPf do
        let hb ← mkExpectedTypeHint rc.pf
          (denE Γ tyBool rc.tm ctx.rho (mkApp2 (mkConst ``Decidable.decide) P inst))
        mkAppOptM ``DenM.treeIte #[ctx.oracle, none, none, none, P, inst, none, none, none,
          none, none, hb, rt.pf, re.pf]
      finishT ctx e tm rt.ty pf (← iteCost P inst rc rt re)
    | _, _ =>
      if (← isMatcher c) || (← unfoldable c) then goT ctx (← deltaApp c e)
      else fail m!"the tree `{e}` (head `{c}`)"
  | .fvar _ | .lam .. =>
    let rm ← applyAll ctx e fn args true
    if ← synMode then return rm
    finishT ctx e rm.tm rm.ty rm.pf rm.cpf
  | _ => fail m!"the tree `{e}`"

/-- The identifier and finite ground type of a location `FTy.loc f n`. -/
partial def location (l : Expr) : M (Expr × Expr) := do
  if l.isAppOfArity ``FTy.loc 2 then return (l.appArg!, l.appFn!.appArg!)
  let l' ← whnf l
  unless l'.isAppOfArity ``Location.mk 4 do fail m!"the location `{l}`"
  let n := l'.getArg! 0
  let f ← ftyOf (l'.getArg! 1)
  if n.hasFVar then fail m!"the location `{l}` depends on a variable"
  unless ← isDefEq l (mkApp2 (mkConst ``FTy.loc) f n) do
    fail m!"the location `{l}` is not `FTy.loc {f} {n}`"
  return (n, f)

end

/-- The D type of the tuple of arguments of types `τs`: `unit` for none, the right-nested
product otherwise. -/
def tupleTy : List Expr → Expr
  | [] => tyUnit
  | [τ] => τ
  | τ :: τs => tyC `prod #[τ, tupleTy τs]

/-- The components of a value `v` of `tupleTy τs`. -/
def tupleProjs : List Expr → Expr → Array Expr
  | [], _ => #[]
  | [_], v => #[v]
  | τ :: τs, v =>
    let r := tupleTy τs
    #[mkApp3 (mkConst ``Prod.fst [Level.zero, Level.zero]) (valE τ) (valE r) v] ++
      tupleProjs τs (mkApp3 (mkConst ``Prod.snd [Level.zero, Level.zero]) (valE τ) (valE r) v)

/-- The arguments and the final codomain of a curried function type; a computation type
(`SPComp`, `SPTree`) is a codomain. -/
partial def funShape (T : Expr) : MetaM (Array Expr × Expr) := do
  if (← spcompArg? T).isSome || (← treeArg? T).isSome then return (#[], T)
  match ← whnf T with
  | .forallE _ a b _ =>
    if b.hasLooseBVars then throwError "reflect_d: the dependent function type `{T}`"
    let (ds, c) ← funShape b
    return (#[a] ++ ds, c)
  | _ => return (#[], T)

/-- The parameters of the reflected definition: the static parameters (a type parameter,
represented by a finite ground type `f` as `FTy.den f`, and a parameter occurring in a later
type), the cost parameters of the function parameters, the binders of the denotation and of the
cost theorem, the arguments of the definition, and the D context and environment. -/
structure Params where
  statics : Array Expr := #[]
  costStatics : Array Expr := #[]
  dBinders : Array Expr := #[]
  cBinders : Array Expr := #[]
  args : Array Expr := #[]
  entries : List Entry := []
  tys : List Expr := []
  rho : Expr
  /-- For each binder, whether the body or a later binder type mentions it. -/
  used : Array Bool := #[]

/-- Reflect the definition `c`: define `c.d`, prove `c.d_den` and, when every construct is in
the costed fragment, `c.d_cost`. -/
def reflect (c : Name) : Term.TermElabM Unit := do
  let info ← getConstInfoDefn c
  unless info.levelParams.isEmpty do
    throwError "reflect_d: `{c}` has universe parameters"
  withLocalDeclD `O (mkConst ``CTree.Oracle) fun O => do
    let rec params : Nat → Expr → Params → (Params → Expr → MetaM Unit) → MetaM Unit
      | 0, _, _, _ => throwError "reflect_d: `{c}` has too many parameters"
      | fuel + 1, ty, ps, k => do
      let ty ← if ty.isForall then pure ty
        else if (← spcompArg? ty).isSome || (← treeArg? ty).isSome then pure ty
        else whnf ty
      let .forallE n T b bi := ty | k ps ty
      if T.isSort then
        unless T == mkSort Level.one do
          throwError "reflect_d: the type parameter `{n}` of `{c}` is not in `Type`"
        withLocalDeclD (n.appendAfter "F") (mkConst ``FTy) fun f => do
          let a := mkApp (mkConst ``FTy.den) f
          let ps' := { ps with statics := ps.statics.push f, args := ps.args.push a }
          params fuel (b.instantiate1 a) ps' k
      else if bi.isInstImplicit then
        let some inst ← synthInstance? T
          | throwError "reflect_d: no instance `{T}` at the representation of the parameters"
        params fuel (b.instantiate1 inst) { ps with args := ps.args.push inst } k
      else if b.hasLooseBVar 0 || !bi.isExplicit then
        unless (← isDefEq T (mkConst ``Nat)) || (← isDefEq T (mkConst ``FTy)) do
          throwError "reflect_d: the parameter `{n}` of `{c}` occurs in a type and is not a \
            natural number or a finite ground type"
        withLocalDeclD n T fun s => do
          let ps' := { ps with statics := ps.statics.push s, args := ps.args.push s }
          params fuel (b.instantiate1 s) ps' k
      else if !(ps.used.getD ps.args.size true) then
        withLocalDeclD n T fun x =>
          params fuel (b.instantiate1 x)
            { ps with dBinders := ps.dBinders.push x, cBinders := ps.cBinders.push x,
                      args := ps.args.push x } k
      else
        withLocalDeclD n T fun x => do
          let i := ps.tys.length
          let gam := gammaE ps.tys
          let (doms, cod) ← funShape T
          let tree := (← treeArg? cod).isSome
          let eff := (← spcompArg? cod).isSome || tree
          let fnParam := !doms.isEmpty || eff
          let dτs ← if fnParam then doms.mapM fun d => return (← tyOf d).1 else pure #[]
          let (τ, isOpt) ← if fnParam then do
              let a := tupleTy dτs.toList
              let some γ ← (do if let some γ ← spcompArg? cod then return some γ
                                else treeArg? cod) | pure (tyC `arr #[a, (← tyOf cod).1], false)
              pure (tyC `arr #[a, (← tyOf γ).1], false)
            else tyOf T
          if let some (a, bt) := (if fnParam then tyArgs2 `arr τ else none) then
            let nArgs := doms.size
            let srcApp (v : Expr) : Expr := mkAppN x (tupleProjs dτs.toList v)
            let _ := a
            withLocalDeclD `g (valE τ) fun g => do
              let hT ← withLocalDeclD `v (valE a) fun v => do
                if eff then
                  let rhs ← if tree then mkAppM ``SPTree.compile #[srcApp v]
                    else pure (srcApp v)
                  mkForallFVars #[v] (← mkEq (mkApp3 (mkConst ``CTree.run) (valE bt) O
                    (mkApp g v)) rhs)
                else
                  mkForallFVars #[v] (← mkEq (mkApp g v) (mkApp2 (mkConst ``CTree.ret)
                    (valE bt) (srcApp v)))
              let csT ← if eff then pure (mkConst ``Nat)
                else mkArrow (valE a) (mkConst ``Nat)
              withLocalDeclD (n.appendAfter "Cost") csT fun cs => do
                let hcT ← withLocalDeclD `v (valE a) fun v => do
                  if eff then
                    mkForallFVars #[v] (← mkAppM ``LE.le
                      #[mkApp2 (mkConst ``CTree.cost) (valE bt) (mkApp g v), cs])
                  else
                    mkForallFVars #[v] (← mkEq (mkApp g v) (← mkAppM ``stepN
                      #[mkConst ``CTree.tick, mkApp cs v,
                        mkApp2 (mkConst ``CTree.ret) (valE bt) (srcApp v)]))
                withLocalDeclD `hA hT fun hA => withLocalDeclD `hC hcT fun hC => do
                  let en : Entry := { fvar := x.fvarId!, level := i, path := [], baseTy := τ,
                                      val := x, dval := g,
                                      fn := some (.param g hA hC eff nArgs) }
                  params fuel (b.instantiate1 x)
                    { ps with costStatics := ps.costStatics.push cs,
                              dBinders := ps.dBinders ++ #[x, g, hA],
                              cBinders := ps.cBinders ++ #[x, g, hC],
                              args := ps.args.push x, entries := en :: ps.entries,
                              tys := τ :: ps.tys,
                              rho := mkAppN (mkConst ``Env.cons) #[gam, τ, g, ps.rho] } k
          else
            let v ← if isOpt then encode T x else pure x
            let en : Entry :=
              { fvar := x.fvarId!, level := i, path := [], baseTy := τ, val := x, dval := v }
            params fuel (b.instantiate1 x)
              { ps with dBinders := ps.dBinders.push x, cBinders := ps.cBinders.push x,
                        args := ps.args.push x, entries := en :: ps.entries,
                        tys := τ :: ps.tys,
                        rho := mkAppN (mkConst ``Env.cons) #[gam, τ, v, ps.rho] } k
    let used ← lambdaTelescope info.value fun xs body => do
      let mut us : Array Bool := #[]
      for h : j in [0:xs.size] do
        let fv := xs[j].fvarId!
        let mut u := body.containsFVar fv
        for k in [j+1:xs.size] do
          if (← inferType xs[k]!).containsFVar fv then u := true
        us := us.push u
      return us
    params 1024 info.type { rho := mkConst ``Env.nil, used } fun ps bodyT => do
      let body := info.value.beta ps.args
      let ctx : Ctx := { entries := ps.entries, tys := ps.tys, rho := ps.rho, oracle := O }
      let tree := (← treeArg? bodyT).isSome
      let eff := (← spcompArg? bodyT).isSome
      let go := if tree then goT ctx body else if eff then goM ctx body else goP ctx body
      let (res, _) ← (go.run false).run #[]
      if res.fn.isSome then throwError "reflect_d: `{c}` returns a function"
      if res.tm.hasAnyFVar (fun fv => !ps.statics.any (·.fvarId! == fv)) then
        throwError "reflect_d: the D-term of `{c}` depends on a parameter (a width or a literal)"
      let Γ := ctx.gamma
      let τ := res.ty
      let dName := c ++ `d
      let dType ← mkForallFVars ps.statics (mkApp2 (mkConst ``Tm) Γ τ)
      let dVal ← mkLambdaFVars ps.statics res.tm
      let dv : DefinitionVal :=
        { name := dName, levelParams := [], type := ← instantiateMVars dType,
          value := ← instantiateMVars dVal, hints := .regular 0, safety := .safe }
      addDecl (.defnDecl dv)
      addDocStringCore dName s!"The D-term of `{c}`, reflected by `reflect_d`."
      let dC := mkAppN (mkConst dName) ps.statics
      let fx := mkAppN (mkConst c) ps.args
      let (stmt, pre) ← if tree || eff then do
          let lhs := mkAppN (mkConst ``Tm.denote) #[Γ, τ, O, dC, ctx.rho]
          let rhs ← if tree then mkAppM ``SPTree.compile #[fx] else pure fx
          pure (← mkEq lhs rhs, #[O])
        else do
          let lhs := mkAppN (mkConst ``Tm.den) #[Γ, τ, dC, ctx.rho]
          let rhs := mkApp2 (mkConst ``CTree.ret) (valE τ) (← encode bodyT fx)
          pure (← mkEq lhs rhs, #[])
      let pf ← mkExpectedTypeHint res.pf stmt
      let binders := ps.statics ++ pre ++ ps.dBinders
      let type ← instantiateMVars (← mkForallFVars binders stmt)
      let value ← instantiateMVars (← mkLambdaFVars binders pf)
      let thmName := c ++ `d_den
      try
        addDecl <| .thmDecl { name := thmName, levelParams := [], type, value }
      catch ex =>
        throwError "reflect_d: the denotation theorem of `{c}` does not check: \
          {ex.toMessageData}"
      addDocStringCore thmName s!"The denotation of `{c}.d` is `{c}`, proved by `reflect_d`."
      let some cp := res.cpf | return
      if cp.containsFVar O.fvarId! then return
      let B ← costOf cp
      let lhs := mkAppN (mkConst ``Tm.cost) #[Γ, τ, dC, ctx.rho]
      let (cstmt, cpf) ← if tree || eff then do
          pure (← mkAppM ``LE.le #[lhs, B], ← mkAppM ``CLe.cost_le #[cp])
        else
          pure (← mkEq lhs B, ← mkAppM ``CEq.cost_eq #[cp])
      let cbinders := ps.statics ++ ps.costStatics ++ ps.cBinders
      let ctype ← instantiateMVars (← mkForallFVars cbinders cstmt)
      let cvalue ← instantiateMVars (← mkLambdaFVars cbinders
        (← mkExpectedTypeHint cpf cstmt))
      let costName := c ++ `d_cost
      try
        addDecl <| .thmDecl { name := costName, levelParams := [], type := ctype,
                              value := cvalue }
      catch ex =>
        throwError "reflect_d: the cost theorem of `{c}` does not check: {ex.toMessageData}"
      addDocStringCore costName
        s!"The cost of `{c}.d`, from the cost hypotheses of its function parameters, proved by \
          `reflect_d`."

end CatCrypt.Complexity.D.Reflect.Impl

namespace CatCrypt.Complexity.D.Reflect

open Lean Elab Command

/-- `reflect_d f` reflects the definition `f` into D: it defines the D-term `f.d` and proves
the denotation theorem `f.d_den`. -/
syntax (name := reflectDCmd) "reflect_d " ident : command

@[command_elab reflectDCmd]
def elabReflectD : CommandElab := fun stx => do
  liftTermElabM do
    let c ← realizeGlobalConstNoOverloadWithInfo stx[1]
    Impl.reflect c

end CatCrypt.Complexity.D.Reflect

end
