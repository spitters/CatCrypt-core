/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Cost
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
hypothesis `∀ v O, (g v).run O = A v`. The theorem states

* `f.d.den ρ = .ret (f x₁ … xₙ)` when `f` returns data (`.ret (optEnc (f …))` for `Option`);
* `f.d.denote O ρ = f x₁ … xₙ` for every oracle `O` when `f` returns `SPComp α`.

It is proved by a derivation of the judgements `Den t ρ v` (the denotation of `t` in `ρ` is
the leaf `v`) and `DenM t ρ c` (the meaning of `t` in `SPComp` is `c`), one lemma per
construct of D, assembled by the command and checked by the kernel.

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
`SPComp.get` and `SPComp.set` at a location `FTy.loc f n`, and the application of a parameter.
A constant outside the Lean, Std and Mathlib libraries is unfolded. Any other construct is
refused with a message naming it.

## Main definitions

* `Den`, `DenM`: the judgements; `optEnc`: the representation of `Option`.
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

/-- The meaning of `t` in `ρ` is `c`, for every oracle. -/
def DenM {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) (ρ : Env Γ) (c : SPComp (Val τ)) : Prop :=
  ∀ O, t.denote O ρ = c

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
  · rw [decide_eq_true hP, if_pos hP]; exact ht
  · rw [decide_eq_false hP, if_neg hP]; exact he

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

variable {Γ : List Ty} {ρ : Env Γ}

theorem pure {τ : Ty} {t : Tm Γ τ} {v : Val τ} (h : Den t ρ v) :
    DenM t ρ (SPComp.pure v) := by
  intro O
  show (t.den ρ).run O = _
  rw [h]
  rfl

theorem letE {a b : Ty} {e : Tm Γ a} {t : Tm (a :: Γ) b} {c : SPComp (Val a)}
    {k : Val a → SPComp (Val b)} (he : DenM e ρ c) (ht : ∀ v, DenM t (ρ.cons v) (k v)) :
    DenM (.letE e t) ρ (SPComp.bind c k) := by
  intro O
  show ((e.den ρ).bind fun v => t.den (ρ.cons v)).run O = _
  rw [CTree.run_bind]
  rw [show (e.den ρ).run O = c from he O]
  exact congrArg _ (funext fun v => ht v O)

theorem letEPure {a b : Ty} {e : Tm Γ a} {t : Tm (a :: Γ) b} {u : Val a}
    {c : SPComp (Val b)} (he : Den e ρ u) (ht : DenM t (ρ.cons u) c) :
    DenM (.letE e t) ρ c := by
  intro O
  show ((e.den ρ).bind fun v => t.den (ρ.cons v)).run O = _
  rw [he, CTree.bind_ret]
  exact ht O

theorem sample (f : FTy) (ρ : Env Γ) [i : Fintype f.den] [j : Nonempty f.den] :
    DenM (.sample f) ρ (@SPComp.sample f.den i j) := by
  intro O
  show SPComp.bind (@SPComp.sample f.den (FTy.instFintype f) _) (fun x => SPComp.pure x) = _
  rw [SPComp.bind_pure, Subsingleton.elim (FTy.instFintype f) i]

theorem fail {τ : Ty} (ρ : Env Γ) : DenM (Tm.fail : Tm Γ τ) ρ SPComp.fail := fun _ => rfl

theorem get (n : ℕ) (f : FTy) (ρ : Env Γ) : DenM (.get n f) ρ (SPComp.get (f.loc n)) := by
  intro O
  show SPComp.bind (SPComp.get (f.loc n)) (fun x => SPComp.pure x) = _
  rw [SPComp.bind_pure]

theorem set (n : ℕ) (f : FTy) {x : Tm Γ (.base f)} {v : f.den} (h : Den x ρ v) :
    DenM (.set n f x) ρ (SPComp.set (f.loc n) v) := by
  intro O
  show ((x.den ρ).bind fun v => CTree.set n f v (.ret (() : Unit))).run O = _
  rw [h]
  show SPComp.bind (SPComp.set (f.loc n) v) (fun _ => SPComp.pure ()) = _
  conv_rhs => rw [← SPComp.bind_pure (SPComp.set (f.loc n) v)]

theorem app {a b : Ty} {f : Tm Γ (.arr a b)} {x : Tm Γ a} {F : Val (.arr a b)} {v : Val a}
    {c : SPComp (Val b)} (hf : Den f ρ F) (hx : Den x ρ v) (h : ∀ O, (F v).run O = c) :
    DenM (.app f x) ρ c := by
  intro O
  show ((f.den ρ).bind (fun g => (x.den ρ).bind fun v => g v)).run O = _
  rw [hf, CTree.bind_ret, hx, CTree.bind_ret]
  exact h O

theorem ite {c : Ty} {P : Prop} [Decidable P] {b : Tm Γ .bool} {t e : Tm Γ c}
    {x y : SPComp (Val c)} (hb : Den b ρ (decide P)) (ht : DenM t ρ x) (he : DenM e ρ y) :
    DenM (.ite b t e) ρ (if P then x else y) := by
  intro O
  show ((b.den ρ).bind (fun (v : Bool) => bif v then t.den ρ else e.den ρ)).run O = _
  rw [hb]
  by_cases hP : P
  · rw [decide_eq_true hP, if_pos hP]; exact ht O
  · rw [decide_eq_false hP, if_neg hP]; exact he O

theorem cond {c : Ty} {b : Tm Γ .bool} {t e : Tm Γ c} {v : Bool} {x y : SPComp (Val c)}
    (hb : Den b ρ v) (ht : DenM t ρ x) (he : DenM e ρ y) :
    DenM (.ite b t e) ρ (Bool.casesOn (motive := fun _ => SPComp (Val c)) v y x) := by
  intro O
  show ((b.den ρ).bind (fun (v : Bool) => bif v then t.den ρ else e.den ρ)).run O = _
  rw [hb]
  cases v
  · exact he O
  · exact ht O

theorem caseOpt {a c : Ty} {s : Tm Γ (.sum .unit a)} {l : Tm (.unit :: Γ) c}
    {r : Tm (a :: Γ) c} {o : Option (Val a)} {N : SPComp (Val c)}
    {S : Val a → SPComp (Val c)} (hs : Den s ρ (optEnc o))
    (hl : DenM l (ρ.cons (τ := .unit) ()) N) (hr : ∀ y, DenM r (ρ.cons y) (S y)) :
    DenM (.case s l r) ρ (Option.casesOn (motive := fun _ => SPComp (Val c)) o N S) := by
  intro O
  show ((s.den ρ).bind (fun (v : Unit ⊕ Val a) =>
    Sum.elim (fun x => l.den (ρ.cons (τ := .unit) x)) (fun y => r.den (ρ.cons y)) v)).run O = _
  rw [hs]
  cases o with
  | none => exact hl O
  | some y => exact hr y O

theorem case {a b c : Ty} {s : Tm Γ (.sum a b)} {l : Tm (a :: Γ) c} {r : Tm (b :: Γ) c}
    {v : Val a ⊕ Val b} {L : Val a → SPComp (Val c)} {R : Val b → SPComp (Val c)}
    (hs : Den s ρ v) (hl : ∀ x, DenM l (ρ.cons x) (L x)) (hr : ∀ y, DenM r (ρ.cons y) (R y)) :
    DenM (.case s l r) ρ (Sum.casesOn (motive := fun _ => SPComp (Val c)) v L R) := by
  intro O
  show ((s.den ρ).bind (fun (v : Val a ⊕ Val b) =>
    Sum.elim (fun x => l.den (ρ.cons x)) (fun y => r.den (ρ.cons y)) v)).run O = _
  rw [hs]
  cases v with
  | inl x => exact hl x O
  | inr y => exact hr y O

end DenM

end CatCrypt.Complexity.D.Reflect

meta section

namespace CatCrypt.Complexity.D.Reflect.Impl

open Lean Elab Meta Command CatCrypt.Core

/-- How a function-typed value is applied: a closure of a λ-term of the source, with the index
of its context and whether its body is in `SPComp`, or a parameter `g` with its hypothesis
`h`. -/
inductive Fn where
  | clo (lam : Expr) (ctxId : Nat) (eff : Bool)
  | param (g h : Expr) (eff : Bool)
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

/-- A translation context: the source variables, the D context (innermost first) and the
environment. -/
structure Ctx where
  entries : List Entry := []
  tys : List Expr := []
  rho : Expr
  deriving Inhabited

/-- A translated subterm: the D-term, its type, its derivation, its source value and its D
value. -/
structure Res where
  tm : Expr
  ty : Expr
  pf : Expr
  val : Expr
  dv : Expr
  fn : Option Fn := none
  deriving Inhabited

/-- The translation monad: the flag selects translation without derivations; the state holds
the contexts of closures. -/
abbrev M := ReaderT Bool (StateRefT (Array Ctx) MetaM)

def fail {α : Type} (msg : MessageData) : M α := throwError m!"reflect_d: {msg}"

def synMode : M Bool := read

def ifPf (k : M Expr) : M Expr := do
  if ← synMode then return mkConst ``True.intro else k

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
  if m.hasFVar then throwError "reflect_d: the modulus `{m}` depends on a variable"
  if m.isAppOfArity ``HAdd.hAdd 6 then
    if (← evalNat m.appArg!) == some 1 then return m.appFn!.appArg!
  if m.isAppOfArity ``Nat.succ 1 then return m.appArg!
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

/-- The finite ground type of `T`. -/
def ftyOf (T : Expr) : MetaM Expr := do
  if let some n ← finMod? T then return mkApp (mkConst ``FTy.fin) n
  let T ← whnf T
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
  if let some n ← finMod? T then return (tyBase (mkApp (mkConst ``FTy.fin) n), false)
  let T ← whnf T
  match T with
  | .forallE _ a b _ =>
    if b.hasLooseBVars then throwError "reflect_d: the dependent function type `{T}`"
    let (ta, _) ← tyFO a
    let tb ← match ← spcompArg? b with
      | some γ => pure (← tyFO γ).1
      | none => pure (← tyOf b).1
    return (tyC `arr #[ta, tb], false)
  | _ =>
  let args := T.getAppArgs
  match T.getAppFn.constName?, args.size with
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

def denME (Γ τ tm ρ c : Expr) : Expr := mkAppN (mkConst ``DenM) #[Γ, τ, tm, ρ, c]

/-- Close a pure node: the source value, the D value and the derivation with its type. -/
def finish (ctx : Ctx) (e tm ty pf : Expr) (fn : Option Fn := none) : M Res := do
  let val := ctx.subst e
  if ← synMode then return { tm, ty, pf, val, dv := val, fn }
  if fn.isSome then
    return { tm, ty, pf, val, dv := (← inferType pf).appArg!, fn }
  let dv ← encode (← inferType val) val
  return { tm, ty, pf := ← mkExpectedTypeHint pf (denE ctx.gamma ty tm ctx.rho dv), val, dv }

/-- Close an effectful node. -/
def finishM (ctx : Ctx) (e tm ty pf : Expr) : M Res := do
  let val := ctx.subst e
  if ← synMode then return { tm, ty, pf, val, dv := val }
  return { tm, ty, pf := ← mkExpectedTypeHint pf (denME ctx.gamma ty tm ctx.rho val), val,
           dv := val }

def refVar (ctx : Ctx) (en : Entry) : M Res := do
  let Γ := ctx.gamma
  let (x, τ) := mkVarE ctx.tys (ctx.depth - 1 - en.level)
  let mut tm := mkApp3 (mkConst ``Tm.var) Γ τ x
  let mut ty := τ
  let mut pf ← ifPf (mkAppM ``Den.var #[x, ctx.rho])
  for snd in en.path do
    let some (a, b) := tyArgs2 `prod ty | fail m!"a projection of a variable of type {ty}"
    tm := mkAppN (mkConst (if snd then ``Tm.snd else ``Tm.fst)) #[Γ, a, b, tm]
    pf ← ifPf (mkAppM (if snd then ``Den.snd else ``Den.fst) #[pf])
    ty := if snd then b else a
  if ← synMode then return { tm, ty, pf, val := en.val, dv := en.dval, fn := en.fn }
  return { tm, ty, val := en.val, dv := en.dval, fn := en.fn,
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
    let _ := n
    finish ctx e tm rb.ty pf rb.fn
  | .lam .. => goLam ctx e
  | .proj ``Prod i s =>
    let rs ← goP ctx s
    let some (a, b) := tyArgs2 `prod rs.ty | fail m!"the projection `{e}`"
    let tm := mkAppN (mkConst (if i == 0 then ``Tm.fst else ``Tm.snd)) #[Γ, a, b, rs.tm]
    let pf ← ifPf (mkAppM (if i == 0 then ``Den.fst else ``Den.snd) #[rs.pf])
    finish ctx e tm (if i == 0 then a else b) pf
  | .lit (.natVal _) =>
    finish ctx e (mkApp2 (mkConst ``Tm.natLit) Γ e) tyNat
      (← ifPf (mkAppM ``Den.natLit #[e, ctx.rho]))
  | _ =>
    let fn := e.getAppFn.consumeMData
    let args := e.getAppArgs
    match fn with
    | .const c _ => goConst ctx e c args
    | .fvar _ | .lam .. | .letE .. | .mdata .. =>
      if args.isEmpty then fail m!"the term `{e}`"
      let mut r ← goP ctx fn
      for a in args do
        r ← applyP ctx r a
      return r
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

/-- Apply a translated function to a source argument, in a pure position. -/
partial def applyP (ctx : Ctx) (rf : Res) (arg : Expr) : M Res := do
  let some (a, b) := tyArgs2 `arr rf.ty | fail m!"an application of a non-function"
  let ra ← goP ctx arg
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
  | some (.param _ h false) =>
    let pf ← mkAppM ``Den.app #[rf.pf, ra.pf, mkApp h ra.dv]
    let val := mkApp rf.val ra.val
    return { tm, ty := b, pf := ← mkExpectedTypeHint pf (denE ctx.gamma b tm ctx.rho val),
             val, dv := val }
  | _ => fail m!"an application of `{rf.val}`, whose body is not known or is in SPComp"

/-- Apply a translated function to a source argument, in an `SPComp` position. -/
partial def applyM (ctx : Ctx) (rf : Res) (arg : Expr) : M Res := do
  let some (a, b) := tyArgs2 `arr rf.ty | fail m!"an application of a non-function"
  let ra ← goP ctx arg
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
    let pf ← mkAppM ``DenM.app #[rf.pf, ra.pf, rb.pf]
    return { tm, ty := b, pf, val := rb.val, dv := rb.dv }
  | some (.param _ h true) =>
    let pf ← mkAppM ``DenM.app #[rf.pf, ra.pf, mkApp h ra.dv]
    let val := mkApp rf.val ra.val
    return { tm, ty := b, pf := ← mkExpectedTypeHint pf (denME ctx.gamma b tm ctx.rho val),
             val, dv := val }
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
  let fin (tm : Expr) (pf : Expr) : M Res := do
    if ← synMode then return { tm, ty := tyBool, pf, val := default, dv := default }
    let d ← mkDecide Ps
    return { tm, ty := tyBool, pf := ← mkExpectedTypeHint pf (denE Γ tyBool tm ctx.rho d),
             val := d, dv := d }
  let primB (p : Expr) (inTy : Expr) (x : Res) : Expr :=
    mkAppN (mkConst ``Tm.prim) #[Γ, inTy, tyBool, p, x.tm]
  let pairR (x y : Res) : M (Expr × Expr × Expr) := do
    let ty := tyC `prod #[x.ty, y.ty]
    let tm := mkAppN (mkConst ``Tm.pair) #[Γ, x.ty, y.ty, x.tm, y.tm]
    let pf ← ifPf (mkAppM ``Den.pair #[x.pf, y.pf])
    return (ty, tm, pf)
  let args := P.getAppArgs
  match P.getAppFn.constName?, args.size with
  | some ``Eq, 3 =>
    let T := args[0]!
    if (← whnf (ctx.subst T)).isConstOf ``Bool && args[2]!.consumeMData.isConstOf ``Bool.true then
      let r ← goP ctx args[1]!
      return ← fin r.tm (← ifPf (mkAppM ``Den.decBool #[r.pf]))
    if let some n ← finMod? (ctx.subst T) then
      let (pty, ptm, ppf) ← pairR (← goP ctx args[1]!) (← goP ctx args[2]!)
      let p := mkApp (mkConst ``Prim.finEq) n
      let tm := mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, p, ptm]
      return ← fin tm (← ifPf (mkAppM ``Den.prim #[p, ppf]))
    let some k ← numKind (ctx.subst T) | fail m!"the equality `{P}` at a type without a primitive"
    let (pty, ptm, ppf) ← pairR (← goP ctx args[1]!) (← goP ctx args[2]!)
    let p := match k with | none => mkConst ``Prim.natEq | some w => mkApp (mkConst ``Prim.weq) w
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, p, ptm]
    fin tm (← ifPf (mkAppM ``Den.prim #[p, ppf]))
  | some ``Ne, 3 =>
    if let some n ← finMod? (ctx.subst args[0]!) then
      let (pty, ptm, ppf) ← pairR (← goP ctx args[1]!) (← goP ctx args[2]!)
      let tm := mkAppN (mkConst ``Tm.prim) #[Γ, tyBool, tyBool, mkConst ``Prim.bnot,
        mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, mkApp (mkConst ``Prim.finEq) n, ptm]]
      return ← fin tm (← ifPf (mkAppM ``Den.finNe #[ppf]))
    let some k ← numKind (ctx.subst args[0]!) | fail m!"the disequality `{P}`"
    let (pty, ptm, ppf) ← pairR (← goP ctx args[1]!) (← goP ctx args[2]!)
    let p := match k with | none => mkConst ``Prim.natEq | some w => mkApp (mkConst ``Prim.weq) w
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, tyBool, tyBool, mkConst ``Prim.bnot,
      mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, p, ptm]]
    fin tm (← ifPf (mkAppM (if k.isNone then ``Den.natNe else ``Den.wordNe) #[ppf]))
  | some ``LT.lt, 4 =>
    if let some n ← finMod? (ctx.subst args[0]!) then
      let (pty, ptm, ppf) ← pairR (← goP ctx args[2]!) (← goP ctx args[3]!)
      let p := mkApp (mkConst ``Prim.finLt) n
      let tm := mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, p, ptm]
      return ← fin tm (← ifPf (mkAppM ``Den.prim #[p, ppf]))
    let some none ← numKind (ctx.subst args[0]!) | fail m!"the comparison `{P}` (only on ℕ)"
    let (pty, ptm, ppf) ← pairR (← goP ctx args[2]!) (← goP ctx args[3]!)
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, mkConst ``Prim.natLt, ptm]
    fin tm (← ifPf (mkAppM ``Den.prim #[mkConst ``Prim.natLt, ppf]))
  | some ``LE.le, 4 =>
    let some none ← numKind (ctx.subst args[0]!) | fail m!"the comparison `{P}` (only on ℕ)"
    let (pty, ptm, ppf) ← pairR (← goP ctx args[3]!) (← goP ctx args[2]!)
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, tyBool, tyBool, mkConst ``Prim.bnot,
      mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, mkConst ``Prim.natLt, ptm]]
    fin tm (← ifPf (mkAppM ``Den.natLe #[ppf]))
  | some ``And, 2 =>
    let x ← goDecide ctx args[0]!
    let y ← goDecide ctx args[1]!
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, tyC `prod #[tyBool, tyBool], tyBool,
      mkConst ``Prim.band, mkAppN (mkConst ``Tm.pair) #[Γ, tyBool, tyBool, x.tm, y.tm]]
    fin tm (← ifPf (mkAppM ``Den.decAnd #[x.pf, y.pf]))
  | some ``Or, 2 =>
    let x ← goDecide ctx args[0]!
    let y ← goDecide ctx args[1]!
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, tyC `prod #[tyBool, tyBool], tyBool,
      mkConst ``Prim.bor, mkAppN (mkConst ``Tm.pair) #[Γ, tyBool, tyBool, x.tm, y.tm]]
    fin tm (← ifPf (mkAppM ``Den.decOr #[x.pf, y.pf]))
  | some ``Not, 1 =>
    let x ← goDecide ctx args[0]!
    fin (primB (mkConst ``Prim.bnot) tyBool x) (← ifPf (mkAppM ``Den.decNot #[x.pf]))
  | _, _ => fail m!"the proposition `{P}` in a condition"

/-- A primitive operation applied to the translations of `xs` (paired when two). -/
partial def goPrim (ctx : Ctx) (e p inTy outTy : Expr) (xs : Array Expr) : M Res := do
  let Γ := ctx.gamma
  let rs ← xs.mapM (goP ctx)
  let (atm, apf) ← if h : rs.size = 2 then do
      let x := rs[0]; let y := rs[1]
      pure (mkAppN (mkConst ``Tm.pair) #[Γ, x.ty, y.ty, x.tm, y.tm],
        ← ifPf (mkAppM ``Den.pair #[x.pf, y.pf]))
    else pure (rs[0]!.tm, rs[0]!.pf)
  let tm := mkAppN (mkConst ``Tm.prim) #[Γ, inTy, outTy, p, atm]
  finish ctx e tm outTy (← ifPf (mkAppM ``Den.prim #[p, apf]))

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
    if e.hasFVar then fail m!"the literal `{e}` depends on a variable"
    finish ctx e (mkApp3 (mkConst ``Tm.lit) Γ f e) (tyBase f)
      (← ifPf (mkAppM ``Den.lit #[f, e, ctx.rho]))
  match c, args.size with
  | ``OfNat.ofNat, 3 =>
    if let some n ← finMod? (ctx.subst args[0]!) then
      return ← lit (mkApp (mkConst ``FTy.fin) n)
    match ← numKind (ctx.subst args[0]!) with
    | some none =>
      finish ctx e (mkApp2 (mkConst ``Tm.natLit) Γ e) tyNat
        (← ifPf (mkAppM ``Den.natLit #[e, ctx.rho]))
    | some (some w) => lit (mkApp (mkConst ``FTy.word) w)
    | none => fail m!"the numeral `{e}`"
  | ``BitVec.ofNat, 2 =>
    let w := args[0]!
    if isNumeral args[1]!.consumeMData then lit (mkApp (mkConst ``FTy.word) w)
    else goPrim ctx e (mkApp (mkConst ``Prim.wofNat) w) tyNat (tyWord w) #[args[1]!]
  | ``Bool.true, 0 | ``Bool.false, 0 => lit (mkConst ``FTy.bool)
  | ``PUnit.unit, 0 => lit (mkConst ``FTy.unit)
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
    finish ctx e r.tm tyBool r.pf
  | ``Prod.mk, 4 =>
    let x ← goP ctx args[2]!
    let y ← goP ctx args[3]!
    finish ctx e (mkAppN (mkConst ``Tm.pair) #[Γ, x.ty, y.ty, x.tm, y.tm])
      (tyC `prod #[x.ty, y.ty]) (← ifPf (mkAppM ``Den.pair #[x.pf, y.pf]))
  | ``Prod.fst, 3 | ``Prod.snd, 3 =>
    let rs ← goP ctx args[2]!
    let some (a, b) := tyArgs2 `prod rs.ty | fail m!"the projection `{e}`"
    let fst := c == ``Prod.fst
    finish ctx e (mkAppN (mkConst (if fst then ``Tm.fst else ``Tm.snd)) #[Γ, a, b, rs.tm])
      (if fst then a else b) (← ifPf (mkAppM (if fst then ``Den.fst else ``Den.snd) #[rs.pf]))
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
    finish ctx e tm cTy pf
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
    finish ctx e r.tm r.ty r.pf r.fn
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
    finishM ctx e tm r.ty (← ifPf (mkAppM ``DenM.letEPure #[rp.pf, r.pf]))
  else
    finish ctx e tm r.ty (← ifPf (mkAppM ``Den.letE #[rp.pf, r.pf]))

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
    finishM ctx e tm rb.ty (← ifPf (mkAppM ``DenM.letEPure #[rv.pf, rb.pf]))
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
      finishM ctx e r.tm r.ty (← ifPf (mkAppM ``DenM.pure #[r.pf]))
    | ``SPComp.sample, 3 =>
      let f ← ftyOf (ctx.subst args[0]!)
      let tm := mkApp2 (mkConst ``Tm.sample) Γ f
      finishM ctx e tm (tyBase f) (← ifPf (mkAppOptM ``DenM.sample
        #[none, f, ctx.rho, ctx.subst args[1]!, ctx.subst args[2]!]))
    | ``SPComp.fail, 1 =>
      let (τ, _) ← tyOf (ctx.subst args[0]!)
      finishM ctx e (mkApp2 (mkConst ``Tm.fail) Γ τ) τ
        (← ifPf (mkAppOptM ``DenM.fail #[none, τ, ctx.rho]))
    | ``SPComp.get, 1 =>
      let (n, f) ← location (ctx.subst args[0]!)
      finishM ctx e (mkApp3 (mkConst ``Tm.get) Γ n f) (tyBase f)
        (← ifPf (mkAppM ``DenM.get #[n, f, ctx.rho]))
    | ``SPComp.set, 2 =>
      let (n, f) ← location (ctx.subst args[0]!)
      let rv ← goP ctx args[1]!
      finishM ctx e (mkAppN (mkConst ``Tm.set) #[Γ, n, f, rv.tm]) tyUnit
        (← ifPf (mkAppM ``DenM.set #[n, f, rv.pf]))
    | ``ite, 5 =>
      let rc ← goDecide ctx args[1]!
      let rt ← goM ctx args[3]!
      let re ← goM ctx args[4]!
      let P := ctx.subst args[1]!; let inst := ctx.subst args[2]!
      let tm := mkAppN (mkConst ``Tm.ite) #[Γ, rt.ty, rc.tm, rt.tm, re.tm]
      let pf ← ifPf do
        let hb ← mkExpectedTypeHint rc.pf
          (denE Γ tyBool rc.tm ctx.rho (mkApp2 (mkConst ``Decidable.decide) P inst))
        mkAppOptM ``DenM.ite #[none, none, none, P, inst, none, none, none, none, none, hb,
          rt.pf, re.pf]
      finishM ctx e tm rt.ty pf
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
      finishM ctx e tm rn.ty (← ifPf (return mkAppN (mkConst ``DenM.caseOpt) #[Γ, ctx.rho,
        aTy, rn.ty, ro.tm, rn.tm, rs.tm, ro.val, rn.val, S, ro.pf, rn.pf, hr]))
    | ``Prod.casesOn, 5 => goProdCase ctx e args[3]! args[4]! true
    | _, _ =>
      if (← isMatcher c) || (← unfoldable c) then goM ctx (← deltaApp c e)
      else fail m!"the computation `{e}` (head `{c}`)"
  | .fvar _ | .lam .. =>
    if args.isEmpty then fail m!"the computation `{e}`"
    let mut r ← goP ctx fn
    for a in args.pop do
      r ← applyP ctx r a
    let rm ← applyM ctx r args.back!
    if ← synMode then return rm
    finishM ctx e rm.tm rm.ty rm.pf
  | _ => fail m!"the computation `{e}`"

partial def goCondM (ctx : Ctx) (e b t f : Expr) : M Res := do
  let Γ := ctx.gamma
  let rb ← goP ctx b
  let rt ← goM ctx t
  let rf ← goM ctx f
  let tm := mkAppN (mkConst ``Tm.ite) #[Γ, rt.ty, rb.tm, rt.tm, rf.tm]
  finishM ctx e tm rt.ty (← ifPf (return mkAppN (mkConst ``DenM.cond) #[Γ, ctx.rho, rt.ty,
    rb.tm, rt.tm, rf.tm, rb.val, rt.val, rf.val, rb.pf, rt.pf, rf.pf]))

/-- `bind c k` as `letE`. -/
partial def goBind (ctx : Ctx) (e c k : Expr) : M Res := do
  let Γ := ctx.gamma
  let rc ← goM ctx c
  let k ← etaN ctx k 1
  let .lam n T body _ := k | fail m!"the continuation `{k}`"
  let (rb, hk, K) ← withGeneric ctx n T [] ctx.depth rc.ty fun x en => do
    let rb ← goM ((ctx.bind rc.ty x).push en) (body.instantiate1 x)
    return (rb, ← ifPf (mkLambdaFVars #[x] rb.pf), ← mkLambdaFVars #[x] rb.val)
  let tm := mkAppN (mkConst ``Tm.letE) #[Γ, rc.ty, rb.ty, rc.tm, rb.tm]
  finishM ctx e tm rb.ty (← ifPf (return mkAppN (mkConst ``DenM.letE) #[Γ, ctx.rho, rc.ty,
    rb.ty, rc.tm, rb.tm, rc.val, K, rc.pf, hk]))

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

/-- The parameters of the reflected definition, with their D types and values. -/
structure Params where
  binders : Array Expr := #[]
  entries : List Entry := []
  tys : List Expr := []
  rho : Expr

/-- Reflect the definition `c`: define `c.d` and prove `c.d_den`. -/
def reflect (c : Name) : Term.TermElabM Unit := do
  let info ← getConstInfoDefn c
  unless info.levelParams.isEmpty do
    throwError "reflect_d: `{c}` has universe parameters"
  lambdaTelescope info.value fun xs body => do
    let rec params (i : Nat) (ps : Params) (k : Params → MetaM Unit) : MetaM Unit := do
      if h : i < xs.size then
        let x := xs[i]
        unless (← x.fvarId!.getBinderInfo).isExplicit do
          throwError "reflect_d: the implicit parameter `{x}` of `{c}`"
        let T ← inferType x
        let (τ, isOpt) ← tyOf T
        let gam := gammaE ps.tys
        if let some (a, b) := tyArgs2 `arr τ then
          let T ← whnf T
          let .forallE _ _ cod _ := T | throwError "reflect_d: the parameter `{x}`"
          let eff := (← spcompArg? cod).isSome
          withLocalDeclD `g (valE τ) fun g => do
            let hT ← withLocalDeclD `v (valE a) fun v => do
              if eff then
                withLocalDeclD `O (mkConst ``CTree.Oracle) fun O => do
                  mkForallFVars #[v, O] (← mkEq (mkApp3 (mkConst ``CTree.run) (valE b) O
                    (mkApp g v)) (mkApp x v))
              else
                mkForallFVars #[v] (← mkEq (mkApp g v) (mkApp2 (mkConst ``CTree.ret)
                  (valE b) (mkApp x v)))
            withLocalDeclD `hA hT fun hA => do
              let en : Entry := { fvar := x.fvarId!, level := i, path := [], baseTy := τ,
                                  val := x, dval := g, fn := some (.param g hA eff) }
              let ps' : Params := { binders := ps.binders ++ #[x, g, hA],
                                    entries := en :: ps.entries, tys := τ :: ps.tys,
                                    rho := mkAppN (mkConst ``Env.cons) #[gam, τ, g, ps.rho] }
              params (i + 1) ps' k
        else
          let v ← if isOpt then encode T x else pure x
          let en : Entry :=
            { fvar := x.fvarId!, level := i, path := [], baseTy := τ, val := x, dval := v }
          let ps' : Params := { binders := ps.binders.push x, entries := en :: ps.entries,
                                tys := τ :: ps.tys,
                                rho := mkAppN (mkConst ``Env.cons) #[gam, τ, v, ps.rho] }
          params (i + 1) ps' k
      else k ps
    params 0 { rho := mkConst ``Env.nil } fun ps => do
      let ctx : Ctx := { entries := ps.entries, tys := ps.tys, rho := ps.rho }
      let bodyT ← inferType body
      let eff := (← spcompArg? bodyT).isSome
      let (res, _) ← ((if eff then goM ctx body else goP ctx body).run false).run #[]
      if res.fn.isSome then throwError "reflect_d: `{c}` returns a function"
      if res.tm.hasFVar then
        throwError "reflect_d: the D-term of `{c}` depends on a parameter (a width or a literal)"
      let Γ := ctx.gamma
      let τ := res.ty
      let dName := c ++ `d
      let dv : DefinitionVal :=
        { name := dName, levelParams := [], type := mkApp2 (mkConst ``Tm) Γ τ,
          value := res.tm, hints := .regular 0, safety := .safe }
      addDecl (.defnDecl dv)
      addDocStringCore dName s!"The D-term of `{c}`, reflected by `reflect_d`."
      let dC := mkConst dName
      let fx := mkAppN (mkConst c) xs
      let (stmt, pf) ← if eff then
          withLocalDeclD `O (mkConst ``CTree.Oracle) fun O => do
            let lhs := mkAppN (mkConst ``Tm.denote) #[Γ, τ, O, dC, ctx.rho]
            let stmt ← mkForallFVars #[O] (← mkEq lhs fx)
            return (stmt, ← mkExpectedTypeHint res.pf stmt)
        else do
          let lhs := mkAppN (mkConst ``Tm.den) #[Γ, τ, dC, ctx.rho]
          let rhs := mkApp2 (mkConst ``CTree.ret) (valE τ) (← encode bodyT fx)
          let stmt ← mkEq lhs rhs
          pure (stmt, ← mkExpectedTypeHint res.pf stmt)
      let type ← instantiateMVars (← mkForallFVars ps.binders stmt)
      let value ← instantiateMVars (← mkLambdaFVars ps.binders pf)
      let thmName := c ++ `d_den
      try
        addDecl <| .thmDecl { name := thmName, levelParams := [], type, value }
      catch ex =>
        throwError "reflect_d: the denotation theorem of `{c}` does not check: \
          {ex.toMessageData}"
      addDocStringCore thmName s!"The denotation of `{c}.d` is `{c}`, proved by `reflect_d`."

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
