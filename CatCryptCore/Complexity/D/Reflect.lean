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
applied to `()`. A parameter the body does not mention is a binder of the theorems only, and
so is a proof parameter (`hf : ∀ o, NoFail (f o)`); a parameter that only the types of proof
parameters mention counts as not mentioned.
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
then found by instance search at that representation. An instance parameter that instance search
does not find there (`CryptoWord MF.den`, `DecidableEq MF.den`, a group class) is a binder of
the theorems, and its methods are parameters of D: each class method applied in the body, or in
a definition the translation unfolds, to static parameters and such an instance (`wxor`,
`mul`, `gen`) is a D value at the innermost end of the context, a function `g` with the
hypothesis `∀ v, g v = .ret (m v)` (and a cost function, as for a data function parameter) or a
datum; an equality `a = b` or `a ≠ b` at `MF.den` is decided by the method
`fun a b => decide (a = b)` of the instance of `DecidableEq MF.den`. A parameter `n : ℕ` that
occurs in the type of a later parameter or of the result (a modulus `Fin (n + 1)`) is a
parameter of `f.d`.

A record parameter (a structure in `Type` without a representation in D, as a scheme
`S : Scheme PK SK M C R` or a CRS) is a binder of the theorems, and its fields applied in the
body are methods as above (`S.enc`, a datum `crs.trapdoor`); a field that is a program
(`S.coins : K → SPComp M`) is a D function with the hypothesis of a computation parameter. A
record or an instance parameter of a structure with a field that is a type (an associated type:
`CyclicGroup.Exp G`, `gp.Scalar` of `gp : GroupParam`) is unbundled: the theorems state `f` at
the constructor applied to its fields, a type field is a finite ground type `EF : FTy` at
`EF.den` (a parameter of `f.d`), and every other field (data, an instance, a proof) is a binder
of the theorems. A record value is the constructor applied to its fields up to structure eta, so
the theorems apply to every record whose type fields are finite ground types.

## The cost theorem

When every construct of the body is in the costed fragment (all of the above except λ-terms
applied to functions in the body, matches on sums and lists, `foldl`, `iter` and `Option` constructors),
the command also proves `f.d_cost`: `f.d.cost ρ = c` for data and `f.d.cost ρ ≤ B` for a
computation, `c` and `B` expressions in the parameters. A data function parameter `A` takes a
cost function `ACost : Val a → ℕ` with `∀ v, g v = stepN CTree.tick (ACost v) (.ret (A v))`;
a computation parameter a bound `ACost : ℕ` with `∀ v, (g v).cost ≤ ACost`. The derivation uses
the judgements `CEq t ρ c v` (evaluation in exactly `c` steps to `v`) and `CLe t ρ B`; after a
sample or a read over a finite ground type the bound of the continuation is maximised over the
values (`CLe.letESup`).

## The fragment

Types: `ℕ`, `Bool`, `Unit`, `BitVec w` for a numeral `w`, `Fin m` and `ZMod m` for a modulus
`m` that is a positive numeral or of the form `n + 1`, tables `Fin q → R` of a finite ground
type `R` (the finite ground type `FTy.tab q f`), products, sums and lists of these;
`Option α` as `α`'s sum with `Unit`, and a Lean inductive type `T` as `mu T.dSig` (below), at
the parameters, the result, the scrutinees of matches and the fields of an inductive type;
functions as parameters, `let`-bound values and arguments of λ-terms.

Terms: variables, `fun`, application (a λ-term applied to a datum is the `let` of the
datum), `let`, numerals and the literals `true`, `false`, `()`
and `BitVec.ofNat w n`; the operations `+ - * / %` on `ℕ`, `+ - * &&& ||| ^^^ ~~~ <<< >>>` on
words, `+ - *` and numerals on `Fin m` and `ZMod m`, `&&`, `||`, `!`, `^^` on `Bool`,
`BitVec.ofNat`, `BitVec.toNat`, `BitVec.setWidth`, `Fin.val`, `ZMod.val` and the cast of a
natural number into `Fin m` or `ZMod m`; `decide` of `=`, `≠`, `<`, `≤`, `∧`, `∨`, `¬` over
these (`=`, `≠` and `<` on residues); pairs and projections; `Sum.inl`,
`Sum.inr`, `some`, `none`, `[]`, `::`, `id`; `if`, `bif`, `Option.elim`, `Sum.elim` and
matches on `Bool`, `Option`, `Sum`, `List` (non-recursive, as `lcase`) and pairs, also written
as the case analyses `casesOn` and, for `Bool`, `Option`, `Sum` and pairs, as the recursors
`rec` at a constant motive; `List.foldl`
as `foldl` and `Nat.iterate` as `iter`; in `SPComp`, `pure`, `bind` (and `do`), `SPComp.fail`,
`SPComp.sample` of a finite ground type,
`SPComp.get` and `SPComp.set` at a location `FTy.loc f n`, and the application of a parameter;
in `SPTree`, `ret`, `sample` of a finite ground type, `get`, `set`, `fail`, `SPTree.bind`, `if`
and the application of a parameter.
A constant outside the Lean, Std and Mathlib libraries is unfolded. Any other construct is
refused with a message naming it.

## Inductive types and structural recursion

The class: an inductive type `T` outside the Lean, Std and Mathlib libraries, not a structure,
without indices, universe parameters, mutual or nested occurrences, with a constructor without
recursive argument, whose type parameters are finite ground types. Its signature `T.dSig` lists
the constructors, one without recursive argument first and the others in their order; the
fields of a constructor (its arguments that are not recursive) are the product of their D
types; its recursive arguments are one family of children, indexed by `unit` (one child),
`bool` (two: the first at `false`) or `fin (n - 1)` (`n ≥ 3`, read by `pick`), or a function
`k : R → T` indexed by the finite ground type of `R`. The command defines `T.dSig`, the proof
`T.dSig_fo` that its fields are first-order, and the encoding `T.dEnc : T → Val (mu T.dSig)` by
`T.rec`: a constructor is the node (`Sig.node`) of its encoded fields and the table of the
encodings of its children. A value of `T` in a parameter, a result or a field is its encoding,
as an `Option` is `optEnc`; a type parameter `α` of `T` is a finite ground type `αF` of these
definitions (`T.dEnc αF : T αF.den → …`).

The rules:

* a constructor applied to its arguments is `con` of the injection of the tuple of its fields
  and the table `ptab` of its children (`Den.con`, `Den.ptab`);
* a case analysis `T.casesOn` at a constant motive (a `match` on a value of `T`) is the
  eliminator `fold` whose step at each constructor is its alternative; its derivation is
  `Den.foldEnc` with the case analysis of the scrutinee at the motive
  `fun t => foldW gv (T.dEnc t) = .ret (E (… t …))`, each alternative's derivation at the node of
  the constructor;
* a structural recursion `f` over `T` (the body Lean keeps for its equations,
  `Structural.eqnInfoExt`, a match on the recursion argument) is the same eliminator, whose steps
  receive the recursive results: a recursive call `f ys (kid j)` on the child at position `j`,
  at the other arguments `ys` unchanged, is the application of the recursive results at `j`
  (`app (snd (snd v)) (lit j)`, a call `f ys (k e)` on a function of children at `e`), and its
  derivation is the induction hypothesis of `T.rec` at the child (`Den.app`);
* a recursion whose arguments `zs` other than the recursion argument change in its recursive
  calls (an accumulator) is the eliminator at the motive `arr Y c`, `Y` the tuple of the changing
  arguments, applied to their initial values: each step is a closure of `Y`, a recursive call
  the recursive result at the child applied to the tuple of its new arguments (`Den.foldApp`,
  `Den.app2`, the induction at the motive quantified over the changing arguments).

A recursion over a type outside the class (`List`, `ℕ`), a mutual recursion, a recursive call
on a value that is not a child and a match on the recursion argument with nested patterns are
refused with messages naming them; a field holding a function is refused (`Sig.FO`). The cost
theorem is not derived for the constructs `con` and `fold`.

## Main definitions

* `Den`, `DenM`: the judgements; `optEnc`: the representation of `Option`.
* `pick`: the child at a position of `fin (n - 1)`.
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

/-- The element at `n` of the list `x :: xs`, its last element beyond its length: the child at a
position of `fin (n - 1)` of a constructor with `n ≥ 3` recursive arguments. -/
def pick {X : Type} : X → List X → ℕ → X
  | x, [], _ => x
  | x, _ :: _, 0 => x
  | _, y :: ys, n + 1 => pick y ys n

/-- Elements related pairwise are related at every position. -/
theorem pick_rel {X Y : Type} (Q : X → Y → Prop) {x : X} {y : Y} {xs : List X} {ys : List Y}
    (h : Q x y) (hs : List.Forall₂ Q xs ys) : ∀ n, Q (pick x xs n) (pick y ys n) := by
  induction hs generalizing x y with
  | nil => intro n; exact h
  | cons hab _ ih =>
    intro n
    cases n with
    | zero => exact h
    | succ n => exact ih hab n

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

/-- `Den` at a constructor: the node its constructor builds from the denotation of the
argument, the children of a constructor with positions being the table in the argument. -/
theorem con {S : Sig} (hS : S.FO) {x : Tm Γ (S.conTy (.mu S))} {v : Val (S.conTy (.mu S))}
    (hx : Den x ρ v) :
    Den (.con hS x) ρ (conAt (X := .mu S) S (fun a k => (WType.mk a k : Val (.mu S))) v) := by
  show (x.den ρ).bind (fun v =>
    .ret (conAt (X := .mu S) S (fun a k => (WType.mk a k : Val (.mu S))) v)) = _
  rw [hx, CTree.bind_ret]

/-- `Den` at the eliminator, by induction on the value: when the step functions denote the
recursion `F` at every node whose recursive results are the values of `F` at its children, the
eliminator denotes `F` at the value. -/
theorem fold {S : Sig} {c : Ty} (hS : S.FO) {g : Tm Γ (S.stepsTy (.mu S) c)} {x : Tm Γ (.mu S)}
    {gv : Val (S.stepsTy (.mu S) c)} {w : Val (.mu S)} (hg : Den g ρ gv) (hx : Den x ρ w)
    {F : WType (Sig.den S).2 → Val c}
    (hF : ∀ a kids, stepAt S gv a kids (fun j => .ret (F (kids j))) = .ret (F ⟨a, kids⟩)) :
    Den (.fold hS g x) ρ (F w) := by
  have key : ∀ w : WType (Sig.den S).2, foldW gv w = .ret (F w) := by
    intro w
    induction w with
    | mk a kids ih =>
      show stepAt S gv a kids (fun j => foldW gv (kids j)) = _
      rw [show (fun j => foldW gv (kids j)) = fun j => CTree.ret (F (kids j)) from funext ih]
      exact hF a kids
  show (g.den ρ).bind (fun gv => (x.den ρ).bind fun w => foldW gv w) = _
  rw [hg, CTree.bind_ret, hx, CTree.bind_ret]
  exact key w

/-- `Den` at the eliminator over the encoded values of a type `T`: when the eliminator at the
encoding `enc t` of every `t : T` is the leaf `F t` (a statement proved by induction on `t`), the
eliminator at the encoding of `t` denotes `F t`. -/
theorem foldEnc {S : Sig} {c : Ty} (hS : S.FO) {g : Tm Γ (S.stepsTy (.mu S) c)}
    {x : Tm Γ (.mu S)} {gv : Val (S.stepsTy (.mu S) c)} {T : Type} {enc : T → Val (.mu S)}
    {F : T → Val c} {t : T} (hg : Den g ρ gv) (hx : Den x ρ (enc t))
    (hF : ∀ t, foldW gv (enc t) = .ret (F t)) : Den (.fold hS g x) ρ (F t) := by
  show (g.den ρ).bind (fun gv => (x.den ρ).bind fun w => foldW gv w) = _
  rw [hg, CTree.bind_ret, hx, CTree.bind_ret]
  exact hF t

/-- `Den` at the eliminator at a function motive applied to an argument: the eliminator at the
value `w` is a leaf whose function, applied to the value of the argument, is the leaf `v`. -/
theorem foldApp {S : Sig} {a b : Ty} (hS : S.FO) {g : Tm Γ (S.stepsTy (.mu S) (.arr a b))}
    {x : Tm Γ (.mu S)} {z : Tm Γ a} {gv : Val (S.stepsTy (.mu S) (.arr a b))} {w : Val (.mu S)}
    {u : Val a} {v : Val b} (hg : Den g ρ gv) (hx : Den x ρ w) (hz : Den z ρ u)
    (h : (foldW gv w).bind (fun G => G u) = .ret v) : Den (.app (.fold hS g x) z) ρ v := by
  show (((g.den ρ).bind fun gv => (x.den ρ).bind fun w => foldW gv w)).bind
    (fun G => (z.den ρ).bind fun u => G u) = _
  rw [hg, CTree.bind_ret, hx, CTree.bind_ret, hz]
  exact h

/-- `Den` at a function applied to two arguments, the first application a tree whose leaf is
applied to the second. -/
theorem app2 {a y b : Ty} {f : Tm Γ (.arr a (.arr y b))} {x : Tm Γ a} {z : Tm Γ y}
    {F : Val (.arr a (.arr y b))} {v : Val a} {u : Val y} {w : Val b} (hf : Den f ρ F)
    (hx : Den x ρ v) (hz : Den z ρ u) (h : (F v).bind (fun G => G u) = .ret w) :
    Den (.app (.app f x) z) ρ w := by
  show (((f.den ρ).bind fun g => (x.den ρ).bind fun v => g v)).bind
    (fun G => (z.den ρ).bind fun u => G u) = _
  rw [hf, CTree.bind_ret, hx, CTree.bind_ret, hz]
  exact h

/-- `Den` at a table: the dependent function of the values of its components. -/
theorem ptab {f : FTy} {B : f.den → Ty} {ts : (j : f.den) → Tm Γ (B j)}
    {v : (j : f.den) → Val (B j)} (h : ∀ j, Den (ts j) ρ (v j)) : Den (.ptab ts) ρ v := by
  show tabDep f (fun j => Val.default (B j)) (fun j => (ts j).den ρ) = _
  rw [show (fun j => (ts j).den ρ) = fun j => CTree.ret (v j) from funext h]
  exact tabDep_ret f _ v

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

/-- `CEq` at the eliminator, by induction on the value: when at every node whose recursive
results are leaves of the values of `F` after `C` ticks at the children the step is a leaf of
`F` after `C` ticks at the node, the eliminator costs the step functions, the argument, one
step and `C` at the value. -/
theorem fold {S : Sig} {c : Ty} (hS : S.FO) {g : Tm Γ (S.stepsTy (.mu S) c)} {x : Tm Γ (.mu S)}
    {cg cx : ℕ} {gv : Val (S.stepsTy (.mu S) c)} {w : Val (.mu S)} (hg : CEq g ρ cg gv)
    (hx : CEq x ρ cx w) {F : WType (Sig.den S).2 → Val c} {C : WType (Sig.den S).2 → ℕ}
    (hF : ∀ a kids (rec : (Sig.den S).2 a → CTree (Val c)),
      (∀ j, rec j = stepN CTree.tick (C (kids j)) (.ret (F (kids j)))) →
        stepAt S gv a kids rec = stepN CTree.tick (C ⟨a, kids⟩) (.ret (F ⟨a, kids⟩))) :
    CEq (.fold hS g x) ρ (cg + (cx + (C w + 1))) (F w) := by
  have key : ∀ w : WType (Sig.den S).2,
      foldW gv w = stepN CTree.tick (C w) (.ret (F w)) := by
    intro w
    induction w with
    | mk a kids ih => exact hF a kids _ ih
  show (g.eval ρ).bind (fun gv => (x.eval ρ).bind fun w => CTree.tick (foldW gv w)) = _
  rw [hg, stepN_ret_bind, hx, stepN_ret_bind, key w]
  show stepN CTree.tick cg (stepN CTree.tick cx (stepN CTree.tick (C w + 1) (.ret (F w)))) = _
  rw [stepN_tick_add, stepN_tick_add, Nat.add_assoc]

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

/-- The arguments of a structural recursion that change in its recursive calls (an accumulator):
their positions, source types, D types and encodings. -/
structure AccInfo where
  chg : Array Nat := #[]
  srcTys : Array Expr := #[]
  tys : Array Expr := #[]
  encs : Array (Option Expr) := #[]
  deriving Inhabited

/-- A structural recursion over a represented inductive type: the recursive constant, its
universe levels, its arguments (in the source, substituted), the position of the recursion
argument and the changing arguments. -/
structure RecFrame where
  fn : Name
  levels : List Level
  args : Array Expr
  pos : Nat
  acc : AccInfo := {}
  deriving Inhabited

/-- A child of the node of the enclosing recursion: its variable, whether it is a function into
the children, its position (a literal, for a child), the induction hypothesis at it (in the
derivation), the recursion and the entry of the recursive results. -/
structure Kid where
  fvar : FVarId
  fnChild : Bool
  pos : Expr
  posTy : Expr
  ih : Expr
  frame : RecFrame
  recEntry : Entry
  deriving Inhabited

/-- A translation context: the source variables, the D context (innermost first), the
environment and the oracle of the denotation theorem. -/
structure Ctx where
  entries : List Entry := []
  tys : List Expr := []
  rho : Expr
  oracle : Expr := default
  /-- The class method terms, each with the variable that stands for it. -/
  methods : List (Expr × Expr) := []
  /-- The types with an equality method, each with the variable of that method. -/
  eqMethods : List (Expr × Expr) := []
  /-- The children of the node of the enclosing structural recursion, whose recursive calls are
  the applications of its recursive results. -/
  kids : List Kid := []
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

/-- The finite ground type `f` of `T = FTy.den f`, up to the projections of a constructor (a
field of an unbundled record, `GP.G ⟨FTy.den f, …⟩`). -/
partial def ftyDen? (T : Expr) : MetaM (Option Expr) := do
  let T := T.consumeMData
  if T.isAppOfArity ``FTy.den 1 then return some T.appArg!
  let T ← whnfCore T
  if T.isAppOfArity ``FTy.den 1 then return some T.appArg!
  let .const c _ := T.getAppFn | return none
  unless (← getProjectionFnInfo? c).isSome do return none
  let some T' ← unfoldDefinition? T | return none
  let T'' ← whnfCore T'
  if T''.isProj then return none
  ftyDen? T''

/-- The size `q` and the entry type `R` of a table type `T = Fin q → R`. -/
def tabTy? (T : Expr) : MetaM (Option (Expr × Expr)) := do
  let .forallE _ a b _ ← whnf T | return none
  if b.hasLooseBVars then return none
  let a ← whnfR a
  unless a.isAppOfArity ``Fin 1 do return none
  return some (a.appArg!, b)

/-- The finite ground type of `T`; a table `Fin q → R` is `FTy.tab q f` for `R = FTy.den f`. -/
partial def ftyOf (T : Expr) : MetaM Expr := do
  if let some n ← finMod? T then return mkApp (mkConst ``FTy.fin) n
  if let some f ← ftyDen? T then return f
  let T ← whnf T
  if T.isAppOfArity ``FTy.den 1 then return T.appArg!
  if let some (q, r) ← tabTy? T then return mkApp2 (mkConst ``FTy.tab) q (← ftyOf r)
  if T.isConstOf ``Bool then return mkConst ``FTy.bool
  if T.isConstOf ``PUnit then return mkConst ``FTy.unit
  if T.isAppOfArity ``BitVec 1 then
    let w := T.appArg!
    if w.hasFVar then throwError "reflect_d: the width of `{T}` depends on a variable"
    return mkApp (mkConst ``FTy.word) w
  throwError "reflect_d: `{T}` is not a finite ground type (Bool, Unit, BitVec w, Fin m, ZMod m, \
    Fin q → R)"

/-! ### Inductive types of the source

A Lean inductive type `T` without indices, outside the Lean, Std and Mathlib libraries and not a
structure, is represented by `mu S` for its signature `T.dSig` (`IndRep`): its constructors,
one without recursive argument first and the others in their order; the fields of a
constructor (its arguments that are not recursive) as the product of their D types; its
recursive arguments as one family of children, indexed by `unit` (one child), `bool` (two:
`false` the first, `true` the second) or `fin (n - 1)` (`n ≥ 3`, `pick`), or a function
`k : R → T` into the type indexed by the finite ground type of `R`. A value is represented by
its encoding `T.dEnc : T → Val (mu T.dSig)`, defined by `T.rec` as the node (`Sig.node`) of the
encoded fields and the encodings of the children; `T.dSig_fo` is the first-order signature. A
type parameter of `T` is a finite ground type `αF` of these definitions, at `αF.den`. -/

/-- The recursive arguments of a constructor: none, `n ≥ 1` arguments of the type, or one
function `R → T` into the type, whose positions are the finite ground type `f` of `R`. -/
inductive RecShape where
  | noKids
  | direct (n : Nat)
  | fn (f : Expr)
  deriving Inhabited

/-- The finite ground type of the positions of a constructor with recursive arguments. -/
def RecShape.fty? : RecShape → Option Expr
  | .noKids => none
  | .direct 1 => some (mkConst ``FTy.unit)
  | .direct 2 => some (mkConst ``FTy.bool)
  | .direct n => some (mkApp (mkConst ``FTy.fin) (mkNatLit (n - 1)))
  | .fn f => some f

/-- A constructor of a represented inductive type, at given parameters. -/
structure CtorRep where
  name : Name
  /-- Its index among the constructors of the type. -/
  declIdx : Nat
  /-- The number of its arguments after the parameters. -/
  arity : Nat
  /-- The positions of its fields among its arguments. -/
  fields : Array Nat
  /-- The D types of the fields. -/
  fieldTys : Array Expr
  /-- The encodings of the fields (`none`: a field represented by itself). -/
  fieldEnc : Array (Option Expr)
  /-- The positions of its recursive arguments among its arguments. -/
  recs : Array Nat
  shape : RecShape
  deriving Inhabited

/-- A Lean inductive type represented by `mu T.dSig`. -/
structure IndRep where
  ind : Name
  /-- The parameters of the type in the source. -/
  params : Array Expr
  /-- The arguments of `T.dSig`, `T.dSig_fo` and `T.dEnc`: the finite ground type of a type
  parameter, any other parameter itself. -/
  dArgs : Array Expr
  /-- The constructors in the order of the signature. -/
  ctors : Array CtorRep
  deriving Inhabited

def IndRep.sig (r : IndRep) : Expr := mkAppN (mkConst (r.ind ++ `dSig)) r.dArgs

def IndRep.fo (r : IndRep) : Expr := mkAppN (mkConst (r.ind ++ `dSig_fo)) r.dArgs

def IndRep.enc (r : IndRep) : Expr := mkAppN (mkConst (r.ind ++ `dEnc)) r.dArgs

def IndRep.ty (r : IndRep) : Expr := tyC `mu #[r.sig]

/-- The source type `T ps`. -/
def IndRep.srcTy (r : IndRep) : Expr := mkAppN (mkConst r.ind) r.params

/-- The D type of the fields of a constructor: `unit` for none, the right-nested product. -/
def fieldTupleTy : List Expr → Expr
  | [] => tyUnit
  | [τ] => τ
  | τ :: τs => tyC `prod #[τ, fieldTupleTy τs]

/-- The value of the fields `vs` of D types `τs`, right-nested. -/
def fieldTupleVal : List Expr → List Expr → Expr
  | [], _ => Lean.mkConst ``PUnit.unit [Level.one]
  | [v], _ => v
  | v :: vs, τ :: τs =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (valE τ) (valE (fieldTupleTy τs)) v (fieldTupleVal vs τs)
  | _, _ => default

/-- The paths of the fields in their tuple. -/
def fieldPaths : Nat → List (List Bool)
  | 0 => []
  | 1 => [[]]
  | n + 1 => [false] :: (fieldPaths n).map (true :: ·)

def CtorRep.fieldTy (c : CtorRep) : Expr := fieldTupleTy c.fieldTys.toList

/-- The positions `k : Option FTy` of a constructor. -/
def CtorRep.posE (c : CtorRep) : Expr :=
  match c.shape.fty? with
  | none => mkApp (mkConst ``Option.none [0]) (mkConst ``FTy)
  | some f => mkApp2 (mkConst ``Option.some [0]) (mkConst ``FTy) f

/-- The prefixes `S₀, …, S_{m-1}` of the signature of the constructors `cs` (written out). -/
def sigPrefixes (cs : Array CtorRep) : Array Expr := Id.run do
  let mut out := #[]
  for h : i in [0:cs.size] do
    let c := cs[i]
    if i == 0 then out := out.push (mkApp (mkConst ``Sig.base) c.fieldTy)
    else out := out.push (mkApp3 (mkConst ``Sig.ext) out[i - 1]! c.fieldTy c.posE)
  return out

/-- The table of the children `vs` of a constructor of shape `sh`, of element type `V` (a Lean
type): constant at `unit`, `cond` at `bool`, `pick` at `fin (n - 1)`, the function itself for a
function into the type. -/
def kidTable (sh : RecShape) (V : Expr) (vs : Array Expr) : MetaM Expr := do
  match sh with
  | .direct 1 =>
    return Expr.lam `_ (mkApp (mkConst ``FTy.den) (mkConst ``FTy.unit)) vs[0]! .default
  | .direct 2 =>
    return Expr.lam `b (mkConst ``Bool)
      (mkApp4 (mkConst ``cond [Level.one]) V (.bvar 0) vs[1]! vs[0]!) .default
  | .direct n =>
    let l ← mkListLit V (vs.extract 1 vs.size).toList
    let dom := mkApp (mkConst ``FTy.den) (mkApp (mkConst ``FTy.fin) (mkNatLit (n - 1)))
    let b := mkApp4 (mkConst ``pick) V vs[0]! l (mkApp2 (mkConst ``Fin.val) (mkNatLit n) (.bvar 0))
    return Expr.lam `i dom b .default
  | .fn _ => return vs[0]!
  | .noKids => return default

/-- A proof that the D type `τ` is first-order. -/
partial def foPf (τ : Expr) : MetaM Expr := do
  let args := τ.getAppArgs
  match τ.getAppFn.constName?, args.size with
  | some ``Ty.base, 1 | some ``Ty.nat, 0 => return mkConst ``True.intro
  | some ``Ty.prod, 2 | some ``Ty.sum, 2 =>
    return mkApp4 (mkConst ``And.intro) (mkApp (mkConst ``Ty.FO) args[0]!)
      (mkApp (mkConst ``Ty.FO) args[1]!) (← foPf args[0]!) (← foPf args[1]!)
  | some ``Ty.list, 1 => foPf args[0]!
  | some ``Ty.mu, 1 =>
    let S := args[0]!
    let .const sn _ := S.getAppFn | throwError "reflect_d: the signature `{S}` is not generated"
    let some I := (match sn with | .str I "dSig" => some I | _ => none)
      | throwError "reflect_d: the signature `{S}` is not generated"
    return mkAppN (mkConst (I ++ `dSig_fo)) S.getAppArgs
  | some ``Ty.arr, 2 =>
    throwError "reflect_d: a field of an inductive type holds a function (`{τ}`); the signatures \
      of D have first-order fields"
  | _, _ => throwError "reflect_d: the D type `{τ}` of a field"

/-- A proof that the signature of the constructors `cs` is first-order. -/
def sigFoPf (cs : Array CtorRep) : MetaM Expr := do
  let pre := sigPrefixes cs
  let mut pf ← foPf cs[0]!.fieldTy
  for i in [1:cs.size] do
    let c := cs[i]!
    pf := mkApp4 (mkConst ``And.intro) (mkApp (mkConst ``Sig.FO) pre[i - 1]!)
      (mkApp (mkConst ``Ty.FO) c.fieldTy) pf (← foPf c.fieldTy)
  return pf

/-- Whether the constant `c` is declared in the Lean, Std or Mathlib libraries. -/
def libraryConst (c : Name) : MetaM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? c with
  | none => return false
  | some idx =>
    let root := env.header.moduleNames[idx.toNat]!.getRoot
    return [`Init, `Std, `Lean, `Mathlib, `Batteries, `Qq, `Aesop].contains root

/-- Add a definition, exposed in a `module` file so that importing modules unfold it. -/
def addExposedDef (name : Name) (type value : Expr) (doc : String) : MetaM Unit := do
  let dv : DefinitionVal :=
    { name, levelParams := [], type := ← instantiateMVars type,
      value := ← instantiateMVars value, hints := .regular 0, safety := .safe }
  withExporting (isExporting := (← getEnv).header.isModule) <| addDecl (.defnDecl dv)
  addDocStringCore name doc

/-- The injection of the argument `v` of the constructor `j` (in the order of the signature) into
the sum over the constructors, at the value level. -/
def injVal (cs : Array CtorRep) (pre : Array Expr) (X : Expr) (j : Nat) (v : Expr) : Expr :=
  go (cs.size - 1) v
where
  go : Nat → Expr → Expr
    | 0, v => v
    | l + 1, v =>
      let c := cs[l + 1]!
      let L := valE (mkApp2 (mkConst ``Sig.conTy) pre[l]! X)
      let R := valE (mkApp3 (mkConst ``Sig.kidTy) c.fieldTy c.posE X)
      if j == l + 1 then mkApp3 (mkConst ``Sum.inr [0, 0]) L R v
      else mkApp3 (mkConst ``Sum.inl [0, 0]) L R (go l v)

mutual

/-- The D type of a source type; the flag marks an encoded type: `Option`, represented by
`optEnc`, or an inductive type `T`, represented by `T.dEnc`. -/
partial def tyOf (T : Expr) : MetaM (Expr × Bool) := do
  if let some γ ← spcompArg? T then
    throwError "reflect_d: the computation type `SPComp {γ}` occurs inside a data type"
  if let some γ ← treeArg? T then
    throwError "reflect_d: the computation type `SPTree {γ}` occurs inside a data type"
  if let some n ← finMod? T then return (tyBase (mkApp (mkConst ``FTy.fin) n), false)
  if let some f ← ftyDen? T then return (tyBase f, false)
  if (← tabTy? T).isSome then
    if let some f ← observing? (ftyOf T) then return (tyBase f, false)
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
  | _, _ =>
    if let some r ← indRep? T then return (r.ty, true)
    throwError "reflect_d: the type `{T}` has no representation in D"
where
  /-- A type represented by itself: no encoded type occurs in it. -/
  tyFO (T : Expr) : MetaM (Expr × Bool) := do
    let r ← tyOf T
    if r.2 then
      throwError "reflect_d: the encoded type (`Option` or an inductive type) inside the type \
        `{T}`; it is represented only as a parameter, a result, a field or a scrutinee"
    return r

/-- The encoding of the values of the source type `T` when it is encoded (`Option` or an
inductive type): the function from `T` to the values of its D type. -/
partial def encoder? (T : Expr) : MetaM (Option Expr) := do
  let T ← whnf T
  if T.isAppOfArity ``Option 1 then return some (mkApp (mkConst ``optEnc) T.appArg!)
  if let some r ← indRep? T then return some r.enc
  return none

/-- The constructors of the inductive type `I` at the parameters `params`, in the order of its
signature. -/
partial def ctorReps (I : Name) (params : Array Expr) : MetaM (Array CtorRep) := do
  let ind ← getConstInfoInduct I
  let selfTy := mkAppN (mkConst I) params
  let isSelf (A : Expr) : Bool := A.getAppFn.isConstOf I
  let mut reps : Array CtorRep := #[]
  for h : k in [0:ind.ctors.length] do
    let cn := ind.ctors[k]!
    let cinfo ← getConstInfoCtor cn
    let rep ← forallTelescope (← instantiateForall cinfo.type params) fun xs _ => do
      let mut fields := #[]
      let mut fieldTys := #[]
      let mut fieldEnc := #[]
      let mut recs := #[]
      let mut fnPos : Option Expr := none
      for h : i in [0:xs.size] do
        let A ← whnf (← inferType xs[i])
        if A.hasAnyFVar (fun fv => xs.any (·.fvarId! == fv)) then
          throwError "reflect_d: the field `{xs[i]}` of the constructor `{cn}` has a type \
            depending on another field"
        if isSelf A then
          unless A == selfTy do
            throwError "reflect_d: the constructor `{cn}` has a child at other parameters"
          recs := recs.push i
        else if A.find? (fun s => s.isConstOf I) |>.isSome then
          let some (R, B) := (match A with
              | .forallE _ R B _ => if B.hasLooseBVars then none else some (R, B)
              | _ => none)
            | throwError "reflect_d: the argument `{xs[i]}` of the constructor `{cn}` holds the \
                type `{I}` other than as a child or a function into children (a nested \
                inductive type)"
          unless (← whnf B) == selfTy do
            throwError "reflect_d: the argument `{xs[i]}` of the constructor `{cn}` is a \
              function into `{B}` (a nested inductive type)"
          if fnPos.isSome then
            throwError "reflect_d: the constructor `{cn}` has two functions into children; the \
              positions of a constructor are one family"
          fnPos := some (← ftyOf R)
          recs := recs.push i
        else
          let (τ, encd) ← tyOf A
          fields := fields.push i
          fieldTys := fieldTys.push τ
          fieldEnc := fieldEnc.push (← if encd then encoder? A else pure none)
      let shape ← match fnPos with
        | some f =>
          if recs.size != 1 then
            throwError "reflect_d: the constructor `{cn}` has children and a function into \
              children; the positions of a constructor are one family"
          pure (RecShape.fn f)
        | none => pure (if recs.isEmpty then RecShape.noKids else RecShape.direct recs.size)
      return { name := cn, declIdx := k, arity := xs.size, fields, fieldTys, fieldEnc, recs,
               shape : CtorRep }
    reps := reps.push rep
  let some first := reps.findIdx? (fun c => match c.shape with | .noKids => true | _ => false)
    | throwError "reflect_d: the inductive type `{I}` has no constructor without a recursive \
        argument; the first constructor of a signature of D has none"
  return #[reps[first]!] ++ (reps.eraseIdx! first)

/-- Under binders for the parameters of `I` (a finite ground type `αF` for a type parameter, read
at `αF.den`), `k dbs srcs` with the binders and the parameters in the source. -/
partial def withDParams {α : Type} (fuel : Nat) (ty : Expr) (dbs srcs : Array Expr)
    (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  if fuel == 0 then return ← k dbs srcs
  let ty ← whnf ty
  let .forallE n T b _ := ty | k dbs srcs
  if T.isSort then
    unless T == mkSort Level.one do
      throwError "reflect_d: the type parameter `{n}` of an inductive type is not in `Type`"
    withLocalDeclD (n.appendAfter "F") (mkConst ``FTy) fun f => do
      let a := mkApp (mkConst ``FTy.den) f
      withDParams (fuel - 1) (b.instantiate1 a) (dbs.push f) (srcs.push a) k
  else
    withLocalDeclD n T fun x => withDParams (fuel - 1) (b.instantiate1 x) (dbs.push x) (srcs.push x) k

/-- Define `I.dSig`, `I.dSig_fo` and `I.dEnc` when they do not exist. -/
partial def ensureIndDecls (I : Name) : MetaM Unit := do
  if (← getEnv).contains (I ++ `dEnc) then return
  let ind ← getConstInfoInduct I
  withDParams ind.numParams ind.type #[] #[] fun dbs srcs => do
    let cs ← ctorReps I srcs
    let pre := sigPrefixes cs
    addExposedDef (I ++ `dSig) (← mkForallFVars dbs (mkConst ``Sig)) (← mkLambdaFVars dbs pre.back!)
      s!"The signature of D of the inductive type `{I}`, generated by `reflect_d`."
    let r : IndRep := { ind := I, params := srcs, dArgs := dbs, ctors := cs }
    let foT := mkApp (mkConst ``Sig.FO) r.sig
    let foV ← mkExpectedTypeHint (← sigFoPf cs) foT
    let foName := I ++ `dSig_fo
    let foType ← mkForallFVars dbs foT
    let foValue ← mkLambdaFVars dbs foV
    let foDecl : TheoremVal := { name := foName, levelParams := [], type := foType, value := foValue }
    withExporting (isExporting := (← getEnv).header.isModule) <| addDecl (.thmDecl foDecl)
    let X := r.ty
    let selfTy := r.srcTy
    let motive ← withLocalDeclD `t selfTy fun t => mkLambdaFVars #[t] (valE X)
    let recC := mkAppN (mkConst (I ++ `rec) [Level.one]) (srcs.push motive)
    let minorTys ← forallBoundedTelescope (← inferType recC) ind.numCtors fun ms _ =>
      ms.mapM inferType
    let mut minors := Array.replicate ind.numCtors (default : Expr)
    for h : j in [0:cs.size] do
      let c := cs[j]
      let m ← forallTelescope minorTys[c.declIdx]! fun xs _ => do
        let args := xs.extract 0 c.arity
        let ihs := xs.extract c.arity xs.size
        let fvals ← (c.fields.zip c.fieldEnc).mapM fun (i, en) => do
          match en with
          | some f => return mkApp f args[i]!
          | none => return args[i]!
        let fv := fieldTupleVal fvals.toList c.fieldTys.toList
        let payload ← match c.shape.fty? with
          | none => pure fv
          | some f => do
            let tab ← kidTable c.shape (valE X) ihs
            let piTy := mkApp2 (mkConst ``Ty.pi) f (.lam `_ (mkApp (mkConst ``FTy.den) f) X .default)
            pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (valE c.fieldTy) (valE piTy) fv tab
        mkLambdaFVars xs (mkApp2 (mkConst ``Sig.node) r.sig (injVal cs pre X j payload))
      minors := minors.set! c.declIdx m
    let encT ← mkForallFVars dbs (← mkArrow selfTy (valE X))
    let encV ← mkLambdaFVars dbs (← withLocalDeclD `t selfTy fun t =>
      mkLambdaFVars #[t] (mkApp (mkAppN recC minors) t))
    addExposedDef (I ++ `dEnc) encT encV
      s!"The encoding of the values of `{I}` as values of D, generated by `reflect_d`."

/-- The representation of the source type `T` when it is an inductive type of the class above. -/
partial def indRep? (T : Expr) : MetaM (Option IndRep) := do
  let T ← whnf T
  let .const I lvls := T.getAppFn | return none
  let env ← getEnv
  let some (.inductInfo ind) := env.find? I | return none
  if isStructure env I || (← libraryConst I) then return none
  unless lvls.isEmpty && ind.numIndices == 0 && ind.all.length == 1 && ind.numNested == 0 do
    throwError "reflect_d: the inductive type `{T}` is not represented in D (universe \
      parameters, indices, a mutual or a nested inductive type)"
  let params := T.getAppArgs
  unless params.size == ind.numParams do return none
  ensureIndDecls I
  let dArgs ← forallBoundedTelescope ind.type ind.numParams fun ps _ =>
    (ps.zip params).mapM fun (p, a) => do
      if (← inferType p).isSort then ftyOf a else pure a
  return some { ind := I, params, dArgs, ctors := ← ctorReps I params }

end

/-- The D value of a source value of type `T`. -/
def encode (T v : Expr) : MetaM Expr := do
  if let some f ← encoder? T then return mkApp f v
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

/-- The variable of the equality method of the type `T`, if `T` has one. -/
def eqMethod? (ctx : Ctx) (T : Expr) : MetaM (Option Expr) := do
  for (T', x) in ctx.eqMethods do
    if ← isDefEq T T' then return some x
  return none

/-- The method term of the context that is a prefix of the application of `fn` to `args`: the
variable that stands for it and the remaining arguments. -/
def methodMatch? (ctx : Ctx) (fn : Expr) (args : Array Expr) : Option (Expr × Array Expr) :=
  ctx.methods.findSome? fun (t, x) =>
    let k := t.getAppNumArgs
    if fn == t.getAppFn && k ≤ args.size && mkAppN fn (args.extract 0 k) == t then
      some (x, args.extract k args.size)
    else none

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
    if let some (x, rest) := methodMatch? ctx fn args then
      if rest.isEmpty then return ← goP ctx x
      return ← applyAll ctx e x rest false
    match fn with
    | .const c _ => goConst ctx e c args
    | .lam n T body _ =>
      -- A λ-term applied to a datum (not a function) is a `let` of the datum.
      if !args.isEmpty && !(← whnf (ctx.subst T)).isForall then
        let rest := args.extract 1 args.size
        return ← goP ctx (.letE n T args[0]! (mkAppN body (rest.map (·.liftLooseBVars 0 1)))
          false)
      applyAll ctx e fn args false
    | .fvar _ | .letE .. | .mdata .. =>
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
    let val := (if n == 1 then mkApp rf.val ra.val
      else mkAppN rf.val (srcs.map ctx.subst)).headBeta
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
  let (c, isEnc) ← tyOf T
  if isEnc then
    let some E ← encoder? T | fail m!"internal: the encoding of `{T}`"
    return (c, T, E)
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
    if let some xm ← eqMethod? ctx (ctx.subst T) then
      let r ← applyAll ctx (mkApp2 xm args[1]! args[2]!) xm #[args[1]!, args[2]!] false
      return ← fin r.tm r.pf r.cpf
    let some k ← numKind (ctx.subst T) | fail m!"the equality `{P}` at a type without a primitive"
    let (pty, ptm, ppf, pc) ← pairR (← goP ctx args[1]!) (← goP ctx args[2]!)
    let p := match k with | none => mkConst ``Prim.natEq | some w => mkApp (mkConst ``Prim.weq) w
    let tm := mkAppN (mkConst ``Tm.prim) #[Γ, pty, tyBool, p, ptm]
    fin tm (← ifPf (mkAppM ``Den.prim #[p, ppf])) (← primC p pc)
  | some ``Ne, 3 =>
    if let some xm ← eqMethod? ctx (ctx.subst args[0]!) then
      let r ← applyAll ctx (mkApp2 xm args[1]! args[2]!) xm #[args[1]!, args[2]!] false
      let pf ← ifPf do
        let d ← mkDecide (← mkEq (ctx.subst args[1]!) (ctx.subst args[2]!))
        mkAppM ``Den.decNot #[← mkExpectedTypeHint r.pf (denE Γ tyBool r.tm ctx.rho d)]
      return ← fin (primB (mkConst ``Prim.bnot) tyBool r) pf
        (← costPf #[r.cpf] fun ys => mkAppM ``CEq.decNot ys)
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
  -- The recursors of the types without recursive constructor arguments, at a constant motive,
  -- are their case analyses (minor premises first, the major premise last).
  | ``Bool.rec, 4 =>
    goCond ctx e (← inferType (ctx.subst e)) args[3]! args[2]!.headBeta args[1]!.headBeta
  | ``Option.rec, 5 => goCaseOpt ctx e args[0]! args[4]! args[2]!.headBeta args[3]!
  | ``Sum.rec, 6 => goCaseSum ctx e args[0]! args[1]! args[5]! args[3]! args[4]!
  | ``Prod.rec, 5 => goProdCase ctx e args[4]! args[3]! false
  | ``Option.elim, 5 => goCaseOpt ctx e args[0]! args[2]! args[3]! args[4]!
  | ``id, 2 =>
    let r ← goP ctx args[1]!
    finish ctx e r.tm r.ty r.pf r.fn r.cpf
  | _, _ =>
    let env ← getEnv
    -- A recursive call of the enclosing structural recursion.
    if let some k := ctx.kids.head? then
      if c == k.frame.fn then return ← goRecCall ctx e args
    -- A constructor of a represented inductive type.
    if let some (.ctorInfo ci) := env.find? c then
      if let some r ← indRep? (← inferType (ctx.subst e)) then
        if r.ind == ci.induct then
          let some cr := r.ctors.find? (·.name == c) | fail m!"internal: `{c}`"
          return ← goCon ctx e r cr args
    -- A case analysis on a value of a represented inductive type.
    if let .str I "casesOn" := c then
      if let some (.inductInfo ind) := env.find? I then
        let np := ind.numParams
        if args.size == np + 2 + ind.numCtors && ind.numIndices == 0 then
          if let some r ← indRep? (← inferType (ctx.subst args[np + 1]!)) then
            let motive ← Core.betaReduce (← instantiateMVars args[np]!)
            let constMotive := match motive.consumeMData with
              | .lam _ _ b _ => !b.hasLooseBVars
              | _ => false
            unless constMotive do
              fail m!"the case analysis `{e}`, whose motive depends on the scrutinee"
            let lvls := e.getAppFn.constLevels!
            let sargs := args.map ctx.subst
            let alts := args.extract (np + 2) args.size
            return ← goIndCases ctx e r args[np + 1]! (fun _ => pure alts) none
              (fun t _ => mkAppN (mkConst c lvls) (sargs.set! (np + 1) t)) #[]
    -- A structural recursion.
    if (Structural.eqnInfoExt.find? env c).isSome then return ← goStructRec ctx e c args
    if (← isMatcher c) || (← unfoldable c) then goP ctx (← deltaApp c e)
    else if c.isStr && (c.getString! == "brecOn" || c.getString! == "rec") then
      fail m!"the recursion `{c}` (use List.foldl or Nat.iterate)"
    else fail m!"the constant `{c}` in `{e}`"

/-- Head β-reduction through metadata: an alternative of a matcher unfolded to `casesOn` applies
the alternative of the source to its fields. -/
partial def headBetaMData (e : Expr) : Expr :=
  let e' := e.consumeMData.headBeta
  match e'.getAppFn.consumeMData with
  | f@(.lam ..) => if e'.getAppNumArgs > 0 then headBetaMData (mkAppN f e'.getAppArgs) else e'
  | _ => e'

/-- The literal of the element `i` of a finite ground type of positions. -/
partial def posLit (sh : RecShape) (i : Nat) : MetaM Expr := do
  match sh with
  | .direct 1 => return Lean.mkConst ``PUnit.unit [Level.one]
  | .direct 2 => return if i == 0 then mkConst ``Bool.false else mkConst ``Bool.true
  | .direct n =>
    let pf := mkApp3 (mkConst ``of_decide_eq_true)
      (mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat) (mkNatLit i) (mkNatLit n))
      (mkApp2 (mkConst ``Nat.decLt) (mkNatLit i) (mkNatLit n))
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
    return mkApp3 (mkConst ``Fin.mk) (mkNatLit n) (mkNatLit i) pf
  | _ => throwError "reflect_d: internal: a position literal"

/-- A constructor of a represented inductive type applied to its arguments: `con` of the
injection of its fields and the table of its children (`ptab`). -/
partial def goCon (ctx : Ctx) (e : Expr) (r : IndRep) (c : CtorRep) (args : Array Expr) :
    M Res := do
  let Γ := ctx.gamma
  let np := r.params.size
  unless args.size == np + c.arity do fail m!"the partial application `{e}` of a constructor"
  let cargs := args.extract np args.size
  let X := r.ty
  -- The fields, as a right-nested tuple.
  let rfs ← c.fields.mapM fun i => goP ctx cargs[i]!
  let mut fr : Res ← if rfs.isEmpty then do
      let u := Lean.mkConst ``PUnit.unit [Level.one]
      let f := mkConst ``FTy.unit
      pure { tm := mkApp3 (mkConst ``Tm.lit) Γ f u, ty := tyUnit,
             pf := ← ifPf (mkAppM ``Den.lit #[f, u, ctx.rho]), val := u, dv := u : Res }
    else pure rfs.back!
  for i in (List.range (rfs.size - 1)).reverse do
    let x := rfs[i]!
    fr := { tm := mkAppN (mkConst ``Tm.pair) #[Γ, x.ty, fr.ty, x.tm, fr.tm],
            ty := tyC `prod #[x.ty, fr.ty], pf := ← ifPf (mkAppM ``Den.pair #[x.pf, fr.pf]),
            val := default, dv := default }
  -- The children, as a table.
  let arg ← match c.shape.fty? with
    | none => pure fr
    | some f => do
      if let .fn _ := c.shape then
        fail m!"the constructor application `{e}`, whose children are a function: its table is \
          not built"
      let rks ← c.recs.mapM fun i => goP ctx cargs[i]!
      let tmTy := mkApp2 (mkConst ``Tm) Γ X
      let ts ← kidTable c.shape tmTy (rks.map (·.tm))
      let B := Expr.lam `_ (mkApp (mkConst ``FTy.den) f) X .default
      let piTy := mkApp2 (mkConst ``Ty.pi) f B
      let tab := mkApp4 (mkConst ``Tm.ptab) Γ f B ts
      let tabPf ← ifPf do
        let vs ← kidTable c.shape (valE X) (rks.map (·.dv))
        let hj ← withLocalDeclD `j (mkApp (mkConst ``FTy.den) f) fun j => do
          let motive ← withLocalDeclD `j (mkApp (mkConst ``FTy.den) f) fun j' =>
            mkLambdaFVars #[j'] (denE Γ X (mkApp ts j').headBeta ctx.rho (mkApp vs j').headBeta)
          let pf ← match c.shape with
            | .direct 1 => pure rks[0]!.pf
            | .direct 2 =>
              pure <| mkApp4 (mkConst ``Bool.rec [Level.zero]) motive rks[0]!.pf rks[1]!.pf j
            | .direct n => do
              let Q ← withLocalDeclD `t tmTy fun t => withLocalDeclD `v (valE X) fun v => do
                mkLambdaFVars #[t, v] (denE Γ X t ctx.rho v)
              let mut fa := mkApp3 (mkConst ``List.Forall₂.nil [0, 0]) tmTy (valE X) Q
              for k in (List.range (n - 1)).reverse do
                let rk := rks[k + 1]!
                let tl := rks.extract (k + 2) rks.size
                fa := mkAppN (mkConst ``List.Forall₂.cons [0, 0])
                  #[tmTy, valE X, Q, rk.tm, rk.dv, ← mkListLit tmTy (tl.map (·.tm)).toList,
                    ← mkListLit (valE X) (tl.map (·.dv)).toList, rk.pf, fa]
              pure <| mkAppN (mkConst ``pick_rel) #[tmTy, valE X, Q, rks[0]!.tm, rks[0]!.dv,
                ← mkListLit tmTy (rks.extract 1 rks.size |>.map (·.tm)).toList,
                ← mkListLit (valE X) (rks.extract 1 rks.size |>.map (·.dv)).toList, rks[0]!.pf, fa,
                mkApp2 (mkConst ``Fin.val) (mkNatLit n) j]
            | _ => fail m!"internal: the table of `{e}`"
          mkLambdaFVars #[j] (← mkExpectedTypeHint pf (mkApp motive j).headBeta)
        mkAppOptM ``Den.ptab #[none, none, f, B, ts, vs, hj]
      let fr' := fr
      pure { tm := mkAppN (mkConst ``Tm.pair) #[Γ, fr'.ty, piTy, fr'.tm, tab],
             ty := tyC `prod #[fr'.ty, piTy], pf := ← ifPf (mkAppM ``Den.pair #[fr'.pf, tabPf]),
             val := default, dv := default : Res }
  -- The injection into the sum over the constructors.
  let pre := sigPrefixes r.ctors
  let some j := r.ctors.findIdx? (·.declIdx == c.declIdx) | fail m!"internal: `{e}`"
  let rec inj : Nat → Expr → Expr → M (Expr × Expr)
    | 0, tm, pf => return (tm, pf)
    | l + 1, tm, pf => do
      let c' := r.ctors[l + 1]!
      let L := mkApp2 (mkConst ``Sig.conTy) pre[l]! X
      let R := mkApp3 (mkConst ``Sig.kidTy) c'.fieldTy c'.posE X
      if j == l + 1 then
        return (mkAppN (mkConst ``Tm.inr) #[Γ, L, R, tm],
          ← ifPf (mkAppOptM ``Den.inr #[none, none, L, none, none, none, pf]))
      else
        let (tm', pf') ← inj l tm pf
        return (mkAppN (mkConst ``Tm.inl) #[Γ, L, R, tm'],
          ← ifPf (mkAppOptM ``Den.inl #[none, none, none, R, none, none, pf']))
  let (itm, ipf) ← inj (r.ctors.size - 1) arg.tm arg.pf
  let tm := mkAppN (mkConst ``Tm.con) #[Γ, r.sig, r.fo, itm]
  let pf ← ifPf (mkAppOptM ``Den.con #[none, none, r.sig, r.fo, itm, none, ipf])
  finish ctx e tm X pf

/-- The tuple of the translations `rs`: `()` for none, the right-nested pairs. -/
partial def tupleRes (ctx : Ctx) (rs : Array Res) : M Res := do
  let Γ := ctx.gamma
  if rs.isEmpty then
    let u := Lean.mkConst ``PUnit.unit [Level.one]
    let f := mkConst ``FTy.unit
    return { tm := mkApp3 (mkConst ``Tm.lit) Γ f u, ty := tyUnit,
             pf := ← ifPf (mkAppM ``Den.lit #[f, u, ctx.rho]), val := u, dv := u }
  let mut acc := rs.back!
  for i in (List.range (rs.size - 1)).reverse do
    let x := rs[i]!
    acc := { tm := mkAppN (mkConst ``Tm.pair) #[Γ, x.ty, acc.ty, x.tm, acc.tm],
             ty := tyC `prod #[x.ty, acc.ty], pf := ← ifPf (mkAppM ``Den.pair #[x.pf, acc.pf]),
             val := default, dv := default }
  return acc

/-- A case analysis on a value of a represented inductive type, or, with `rec?`, the match of a
structural recursion on its recursion argument: the eliminator `fold` whose step at a
constructor is its alternative (`altsAt zs`, the alternatives at the changing arguments `zs`); in
a recursion, a recursive call on a child is the application of the recursive results at its
position. A recursion whose arguments at the positions `acc.chg` change (an accumulator) is the
eliminator at the motive `arr Y c`, `Y` the tuple of the changing arguments, applied to their
initial values `init`; each step is then a closure of `Y`. `srcAt t' zs` is the source term at
the scrutinee `t'` and the changing arguments `zs`. -/
partial def goIndCases (ctx : Ctx) (e : Expr) (r : IndRep) (major : Expr)
    (altsAt : Array Expr → MetaM (Array Expr)) (rec? : Option RecFrame)
    (srcAt : Expr → Array Expr → Expr) (init : Array Expr) : M Res := do
  let Γ := ctx.gamma
  let (cRes, _, E) ← branchRep (← inferType (ctx.subst e))
  let acc := (rec?.map (·.acc)).getD {}
  let hasAcc := !acc.chg.isEmpty
  let Y := fieldTupleTy acc.tys.toList
  let cTy := if hasAcc then tyC `arr #[Y, cRes] else cRes
  let X := r.ty
  let S := r.sig
  let rm ← goP ctx major
  let pre := sigPrefixes r.ctors
  let altTyOf (c : CtorRep) : Expr := match c.shape.fty? with
    | none => c.fieldTy
    | some f => tyC `prod #[c.fieldTy, tyC `prod #[mkApp2 (mkConst ``Ty.pi) f
        (.lam `_ (mkApp (mkConst ``FTy.den) f) X .default), tyC `arr #[tyBase f, cTy]]]
  let accVal (zs : Array Expr) : Expr :=
    fieldTupleVal ((acc.encs.zip zs).map fun (en, z) => match en with
      | some f => mkApp f z
      | none => z).toList acc.tys.toList
  -- The translation of the alternative of `c` under its arguments `xs`, the hypotheses `ihs` and
  -- the changing arguments `zs`, its bound value `vv`, the recursive results `recV`: the body of
  -- the step function.
  let step (c : CtorRep) (xs ihs zs : Array Expr) (vv recV : Expr) : M Res := do
    let alts ← altsAt zs
    let alt ← etaN ctx alts[c.declIdx]! c.arity
    let body := headBetaMData (mkAppN alt xs)
    let aTy := altTyOf c
    let pre' := match c.shape.fty? with | none => [] | some _ => [false]
    let paths := fieldPaths c.fields.size
    let mut ctx' := ctx.bind aTy vv
    ctx' := { ctx' with kids := [] }
    for h : l in [0:c.fields.size] do
      let y := xs[c.fields[l]]!
      let dv := match c.fieldEnc[l]! with | some f => mkApp f y | none => y
      ctx' := ctx'.push { fvar := y.fvarId!, level := ctx.depth, path := pre' ++ paths[l]!,
                          baseTy := aTy, val := y, dval := dv }
    if let some fr := rec? then
      let some f := c.shape.fty? | pure ()
      let recEn : Entry := { fvar := ← mkFreshFVarId, level := ctx.depth, path := [true, true],
                             baseTy := aTy, val := recV, dval := recV }
      let mut ks := []
      for h : i in [0:c.recs.size] do
        let fnChild := match c.shape with | .fn _ => true | _ => false
        let pos ← if fnChild then pure default else posLit c.shape i
        ks := { fvar := xs[c.recs[i]]!.fvarId!, fnChild, pos, posTy := f,
                ih := ihs.getD i default, frame := fr, recEntry := recEn : Kid } :: ks
      ctx' := { ctx' with kids := ks }
    unless hasAcc do return ← goP ctx' body
    let zpaths := fieldPaths zs.size
    let mut ctx'' := ctx'.bind Y (accVal zs)
    for h : l in [0:zs.size] do
      let z := zs[l]
      let dv := match acc.encs[l]! with | some f => mkApp f z | none => z
      ctx'' := ctx''.push { fvar := z.fvarId!, level := ctx.depth + 1, path := zpaths[l]!,
                            baseTy := Y, val := z, dval := dv }
    let rb ← goP ctx'' body
    return { rb with tm := mkAppN (mkConst ``Tm.lam) #[ctx'.gamma, Y, cRes, rb.tm] }
  let ctorTy (c : CtorRep) : MetaM Expr := do
    instantiateForall (← getConstInfoCtor c.name).type r.params
  let zDecls := acc.srcTys.mapIdx fun i T => (Name.mkSimple s!"z{i}", T)
  -- The steps without derivations: the D-terms.
  let mut steps : Array Res := #[]
  for c in r.ctors do
    let rb ← withReader (fun _ => true) <| forallTelescope (← ctorTy c) fun xs _ =>
      withLocalDeclsDND zDecls fun zs => do
        let rb ← step c xs #[] zs default default
        if rb.tm.hasAnyFVar (fun fv => (xs ++ zs).any (·.fvarId! == fv)) then
          fail m!"the alternative of `{c.name}` in `{e}` gives a D-term that depends on a field \
            (a literal or a width)"
        return rb
    steps := steps.push rb
  -- The tuple of the steps, first innermost.
  let mut gtm := mkAppN (mkConst ``Tm.lam) #[Γ, altTyOf r.ctors[0]!, cTy, steps[0]!.tm]
  let mut gTy := mkApp3 (mkConst ``Sig.stepsTy) pre[0]! X cTy
  for h : j in [1:r.ctors.size] do
    let c := r.ctors[j]!
    let lamTm := mkAppN (mkConst ``Tm.lam) #[Γ, altTyOf c, cTy, steps[j]!.tm]
    gtm := mkAppN (mkConst ``Tm.pair) #[Γ, gTy, tyC `arr #[altTyOf c, cTy], gtm, lamTm]
    gTy := mkApp3 (mkConst ``Sig.stepsTy) pre[j]! X cTy
  let foldTm := mkAppN (mkConst ``Tm.fold) #[Γ, S, cTy, r.fo, gtm, rm.tm]
  let zr ← if hasAcc then tupleRes ctx (← init.mapM (goP ctx)) else pure default
  let tm := if hasAcc then mkAppN (mkConst ``Tm.app) #[Γ, Y, cRes, foldTm, zr.tm] else foldTm
  if ← synMode then return { tm, ty := cRes, pf := mkConst ``True.intro, val := default,
                             dv := default }
  -- The derivation of the steps: the closures, paired.
  let mut gpf ← mkAppM ``Den.lam #[steps[0]!.tm, ctx.rho]
  for h : j in [1:r.ctors.size] do
    gpf ← mkAppM ``Den.pair #[gpf, ← mkAppM ``Den.lam #[steps[j]!.tm, ctx.rho]]
  let gv := (← instantiateMVars (← inferType gpf)).appArg!
  let hg ← mkExpectedTypeHint gpf (denE Γ (mkApp3 (mkConst ``Sig.stepsTy) S X cTy) gtm ctx.rho gv)
  let selfTy := r.srcTy
  let srcMajor := ctx.subst major
  let F (t : Expr) (zs : Array Expr) : Expr := (mkApp E (srcAt t zs)).headBeta
  let stmt (t : Expr) (zs : Array Expr) : Expr :=
    let fw := mkAppN (mkConst ``foldW) #[S, cTy, gv, mkApp r.enc t]
    let lhs := if hasAcc then
        mkAppN (mkConst ``CTree.bind) #[valE cTy, valE cRes, fw,
          .lam `G (valE cTy) (mkApp (.bvar 0) (accVal zs)) .default]
      else fw
    mkApp3 (mkConst ``Eq [1]) (mkApp (mkConst ``CTree) (valE cRes)) lhs
      (mkApp2 (mkConst ``CTree.ret) (valE cRes) (F t zs))
  let motive ← withLocalDeclD `t selfTy fun t => withLocalDeclsDND zDecls fun zs => do
    mkLambdaFVars #[t] (← mkForallFVars zs (stmt t zs))
  -- The minor premises: the derivation of each alternative at its bound value.
  let ind ← getConstInfoInduct r.ind
  let mut minors := Array.replicate ind.numCtors (default : Expr)
  for c in r.ctors do
    let m ← forallTelescope (← ctorTy c) fun xs _ => do
      let ihTys ← if rec?.isSome then c.recs.mapM fun i => do
          let x := xs[i]!
          let A ← whnf (← inferType x)
          match A with
          | .forallE n R _ bi => withLocalDecl n bi R fun a => do
              mkForallFVars #[a] (mkApp motive (mkApp x a)).headBeta
          | _ => pure (mkApp motive x).headBeta
        else pure #[]
      withLocalDeclsDND (ihTys.mapIdx fun i T => (Name.mkSimple s!"ih{i}", T)) fun ihs => do
      withLocalDeclsDND zDecls fun zs => do
        let fvals := (c.fields.zip c.fieldEnc).map fun (i, en) => match en with
          | some f => mkApp f xs[i]!
          | none => xs[i]!
        let fv := fieldTupleVal fvals.toList c.fieldTys.toList
        let (vv, recV) ← match c.shape.fty? with
          | none => pure (fv, default)
          | some f => do
            let encKids ← match c.shape with
              | .fn _ => withLocalDeclD `a (mkApp (mkConst ``FTy.den) f) fun a =>
                  mkLambdaFVars #[a] (mkApp r.enc (mkApp xs[c.recs[0]!]! a))
              | _ => kidTable c.shape (valE X) (c.recs.map fun i => mkApp r.enc xs[i]!)
            let recV ← withLocalDeclD `j (mkApp (mkConst ``FTy.den) f) fun j =>
              mkLambdaFVars #[j] (mkAppN (mkConst ``foldW) #[S, cTy, gv, (mkApp encKids j).headBeta])
            let piTy := mkApp2 (mkConst ``Ty.pi) f (.lam `_ (mkApp (mkConst ``FTy.den) f) X .default)
            let arrTy := tyC `arr #[tyBase f, cTy]
            let inner := mkApp4 (mkConst ``Prod.mk [0, 0]) (valE piTy) (valE arrTy) encKids recV
            pure (mkApp4 (mkConst ``Prod.mk [0, 0]) (valE c.fieldTy)
              (valE (tyC `prod #[piTy, arrTy])) fv inner, recV)
        let rb ← step c xs ihs zs vv recV
        let goal := stmt (mkAppN (mkConst c.name) (r.params ++ xs)) zs
        mkLambdaFVars (xs ++ ihs ++ zs) (← mkExpectedTypeHint rb.pf goal)
    minors := minors.set! c.declIdx m
  let elim (t : Expr) : Expr := if rec?.isSome then
      mkAppN (mkConst (r.ind ++ `rec) [Level.zero]) (r.params ++ #[motive] ++ minors ++ #[t])
    else
      mkAppN (mkConst (r.ind ++ `casesOn) [Level.zero]) (r.params ++ #[motive, t] ++ minors)
  let pf ← if hasAcc then do
      let zs0 := init.map ctx.subst
      let h0 ← mkExpectedTypeHint (mkAppN (elim srcMajor) zs0) (stmt srcMajor zs0)
      mkAppOptM ``Den.foldApp #[none, none, S, Y, cRes, r.fo, gtm, rm.tm, zr.tm, gv,
        mkApp r.enc srcMajor, zr.dv, F srcMajor zs0, hg, rm.pf, zr.pf, h0]
    else do
      let hF ← withLocalDeclD `t selfTy fun t => mkLambdaFVars #[t] (elim t)
      let Fl ← withLocalDeclD `t selfTy fun t => mkLambdaFVars #[t] (F t #[])
      mkAppOptM ``Den.foldEnc #[none, none, S, cTy, r.fo, gtm, rm.tm, gv, selfTy, r.enc, Fl,
        srcMajor, hg, rm.pf, hF]
  finish ctx e tm cRes pf

/-- A recursive call of the enclosing recursion on a child of the node: the recursive results
applied at the position of the child, and to the tuple of the changing arguments of the call. -/
partial def goRecCall (ctx : Ctx) (e : Expr) (args : Array Expr) : M Res := do
  let some k0 := ctx.kids.head? | fail m!"internal: `{e}`"
  let fr := k0.frame
  unless args.size == fr.args.size do
    fail m!"the recursive call `{e}` at another number of arguments"
  for h : i in [0:args.size] do
    if i != fr.pos && !fr.acc.chg.contains i && ctx.subst args[i] != fr.args[i]! then
      fail m!"internal: the recursive call `{e}` changes the argument `{fr.args[i]!}`"
  let a := args[fr.pos]!.consumeMData
  let (kid, arg?) ← match a with
    | .fvar fv => match ctx.kids.find? (fun k => k.fvar == fv && !k.fnChild) with
      | some k => pure (k, none)
      | none => fail m!"the recursive call `{e}` on `{a}`, which is not a child of the node"
    | .app (.fvar fv) x => match ctx.kids.find? (fun k => k.fvar == fv && k.fnChild) with
      | some k => pure (k, some x)
      | none => fail m!"the recursive call `{e}` on `{a}`, which is not a child of the node"
    | _ => fail m!"the recursive call `{e}` on `{a}`, which is not a child of the node"
  let rf ← refVar ctx kid.recEntry
  let some (_, cTy) := tyArgs2 `arr rf.ty | fail m!"internal: `{e}`"
  let f := kid.posTy
  let ja ← match arg? with
    | some x => goP ctx x
    | none => do
      let tm := mkApp3 (mkConst ``Tm.lit) ctx.gamma f kid.pos
      pure { tm, ty := tyBase f, pf := ← ifPf (mkAppM ``Den.lit #[f, kid.pos, ctx.rho]),
             val := kid.pos, dv := kid.pos : Res }
  let app1 := mkAppN (mkConst ``Tm.app) #[ctx.gamma, tyBase f, cTy, rf.tm, ja.tm]
  let hasAcc := !fr.acc.chg.isEmpty
  let (cRes, _, E) ← branchRep (← inferType (ctx.subst e))
  let zsSrc := fr.acc.chg.map fun i => args[i]!
  let zr ← if hasAcc then tupleRes ctx (← zsSrc.mapM (goP ctx)) else pure default
  let Y := fieldTupleTy fr.acc.tys.toList
  let tm := if hasAcc then mkAppN (mkConst ``Tm.app) #[ctx.gamma, Y, cRes, app1, zr.tm] else app1
  let pf ← ifPf do
    let ih := match arg? with
      | some _ => mkApp kid.ih ja.dv
      | none => kid.ih
    let w := (mkApp E (ctx.subst e)).headBeta
    let recJ := mkApp kid.recEntry.dval ja.dv
    if hasAcc then
      let h := mkAppN ih (zsSrc.map ctx.subst)
      let lhs := mkAppN (mkConst ``CTree.bind) #[valE cTy, valE cRes, recJ,
        .lam `G (valE cTy) (mkApp (.bvar 0) zr.dv) .default]
      let h ← mkExpectedTypeHint h (← mkEq lhs (mkApp2 (mkConst ``CTree.ret) (valE cRes) w))
      mkAppM ``Den.app2 #[rf.pf, ja.pf, zr.pf, h]
    else
      let h ← mkExpectedTypeHint ih (← mkEq recJ (mkApp2 (mkConst ``CTree.ret) (valE cTy) w))
      mkAppM ``Den.app #[rf.pf, ja.pf, h]
  finish ctx e tm cRes pf

/-- The calls of the constant `c` in `e`, by their arguments. -/
partial def collectCalls (c : Name) (e : Expr) : Array (Array Expr) :=
  go e #[]
where
  go (e : Expr) (acc : Array (Array Expr)) : Array (Array Expr) :=
    match e with
    | .app .. =>
      let acc := if e.getAppFn.isConstOf c then acc.push e.getAppArgs else acc
      e.getAppArgs.foldl (fun a x => go x a) (go e.getAppFn acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => acc

/-- A structural recursion over a represented inductive type: its body, a match on the recursion
argument, as the eliminator (`goIndCases`); the arguments that change in its recursive calls
are the argument of the eliminator at a function motive. -/
partial def goStructRec (ctx : Ctx) (e : Expr) (c : Name) (args : Array Expr) : M Res := do
  let env ← getEnv
  let some info := Structural.eqnInfoExt.find? env c | fail m!"internal: `{c}`"
  if info.declNames.size > 1 then
    fail m!"the mutual structural recursion `{c}`"
  let lvls := e.getAppFn.constLevels!
  let value := info.value.instantiateLevelParams info.levelParams lvls
  let rec arity : Expr → Nat
    | .lam _ _ b _ => arity b + 1
    | _ => 0
  unless args.size == arity value do
    fail m!"the structural recursion `{c}` applied to {args.size} arguments, its equations take \
      {arity value}"
  let pos := info.recArgPos
  let major := args[pos]!
  let some r ← indRep? (← inferType (ctx.subst major))
    | fail m!"the structural recursion `{c}` over `{← inferType (ctx.subst major)}`, which is \
        not a represented inductive type (use List.foldl or Nat.iterate)"
  -- The arguments that change in a recursive call.
  let chg ← lambdaTelescope value fun ys b => do
    let calls := collectCalls c b
    let mut chg := #[]
    for h : i in [0:ys.size] do
      if i != pos && calls.any (fun as => as.size > i && as[i]! != ys[i]) then chg := chg.push i
    return chg
  let srcTys ← chg.mapM fun i => inferType (ctx.subst args[i]!)
  let reps ← srcTys.mapM fun T => do
    let (τ, encd) ← tyOf T
    return (τ, ← if encd then encoder? T else pure none)
  let acc : AccInfo := { chg, srcTys, tys := reps.map (·.1), encs := reps.map (·.2) }
  let casesOn := r.ind ++ `casesOn
  let np := r.params.size
  let altsAt (zs : Array Expr) : MetaM (Array Expr) := do
    let args' := (chg.zip zs).foldl (fun as (i, z) => as.set! i z) args
    let mut body := (value.beta args').headBeta
    if let .const m _ := body.getAppFn then
      if ← isMatcher m then body := ((← (deltaApp m body).run true |>.run' #[])).headBeta
    let bargs := body.getAppArgs
    unless body.getAppFn.isConstOf casesOn && bargs.size == np + 2 + r.ctors.size &&
        bargs[np + 1]! == major do
      throwError "reflect_d: the structural recursion `{c}` is not a match on its recursion \
        argument with one alternative per constructor: {body}"
    return bargs.extract (np + 2) bargs.size
  let _ ← (withLocalDeclsDND (srcTys.mapIdx fun i T => (Name.mkSimple s!"z{i}", T)) altsAt :
    MetaM (Array Expr))
  let fr : RecFrame := { fn := c, levels := lvls, args := args.map ctx.subst, pos, acc }
  goIndCases ctx e r major altsAt (some fr)
    (fun t zs => mkAppN (mkConst c lvls)
      ((chg.zip zs).foldl (fun as (i, z) => as.set! i z) ((args.map ctx.subst).set! pos t)))
    (chg.map fun i => args[i]!)

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
  if let some (x, rest) := methodMatch? ctx fn args then
    let rm ← applyAll ctx e x rest true
    if ← synMode then return rm
    return ← finishM ctx e rm.tm rm.ty rm.pf rm.cpf
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
  if let some (x, rest) := methodMatch? ctx fn args then
    let rm ← applyAll ctx e x rest true
    if ← synMode then return rm
    return ← finishT ctx e rm.tm rm.ty rm.pf rm.cpf
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
  /-- The instance parameters without an instance at the representation of the parameters, the
  record parameters and the fields of the unbundled records (`unbundle`). -/
  insts : Array Expr := #[]
  /-- The record parameters and the fields of the unbundled records. -/
  recs : Array Expr := #[]
  costStatics : Array Expr := #[]
  dBinders : Array Expr := #[]
  cBinders : Array Expr := #[]
  args : Array Expr := #[]
  entries : List Entry := []
  tys : List Expr := []
  rho : Expr
  /-- For each binder, whether the body or the type of a later binder that is not a proof
  mentions it. -/
  used : Array Bool := #[]
  /-- For each binder, whether the result type or the type of a later binder that is not a
  proof mentions it. -/
  inType : Array Bool := #[]

/-- Add the parameter `x : T` named `n` with source value `val` to the D context: a function
(`funShape`) as a D function value `g` with its hypotheses `hA` (denotation) and `hC` (cost),
data as itself. A class method (`method`) is no binder of the theorems: `val` is the method,
and `x` stands for it in the body. -/
def addParam (O x val : Expr) (n : Name) (T : Expr) (method : Bool) (ps : Params)
    (k : Params → MetaM Unit) : MetaM Unit := do
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
  let own := if method then #[] else #[x]
  if let some (a, bt) := (if fnParam then tyArgs2 `arr τ else none) then
    let nArgs := doms.size
    let srcApp (v : Expr) : Expr := (mkAppN val (tupleProjs dτs.toList v)).headBeta
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
                              val, dval := g, fn := some (.param g hA hC eff nArgs) }
          k { ps with costStatics := ps.costStatics.push cs,
                      dBinders := ps.dBinders ++ own ++ #[g, hA],
                      cBinders := ps.cBinders ++ own ++ #[g, hC],
                      args := ps.args ++ own, entries := en :: ps.entries,
                      tys := τ :: ps.tys,
                      rho := mkAppN (mkConst ``Env.cons) #[gam, τ, g, ps.rho] }
  else
    let v ← if isOpt then encode T val else pure val
    let en : Entry :=
      { fvar := x.fvarId!, level := i, path := [], baseTy := τ, val, dval := v }
    k { ps with dBinders := ps.dBinders ++ own, cBinders := ps.cBinders ++ own,
                args := ps.args ++ own, entries := en :: ps.entries,
                tys := τ :: ps.tys,
                rho := mkAppN (mkConst ``Env.cons) #[gam, τ, v, ps.rho] }

/-- Whether `t` is a method term: it mentions an instance or a record field of `insts`, its
free variables are static parameters or of `insts`, and its type is data or a function on data;
a function into `SPComp` or `SPTree` (a program of a record) when `t` mentions a record of
`recs`. -/
def isMethodTerm (stat insts recs : Array Expr) (t : Expr) : MetaM Bool := do
  if t.hasLooseBVars then return false
  unless t.hasAnyFVar (fun fv => insts.any (·.fvarId! == fv)) do return false
  if t.hasAnyFVar (fun fv => !stat.any (·.fvarId! == fv) && !insts.any (·.fvarId! == fv)) then
    return false
  let isRec := t.hasAnyFVar (fun fv => recs.any (·.fvarId! == fv))
  try
    let T ← inferType t
    let (doms, cod) ← funShape T
    let γ? ← do if let some γ ← spcompArg? cod then pure (some γ) else treeArg? cod
    if let some γ := γ? then
      unless isRec do return false
      let field ← match t.getAppFn with
        | .const c _ => return (← getProjectionFnInfo? c).any (!·.fromClass)
        | .proj .. => pure true
        | _ => pure false
      unless field do return false
      for d in doms do discard <| tyOf d
      discard <| tyOf γ
      return true
    if T.containsConst (fun c => c == ``SPComp || c == ``SPTree) then return false
    for d in doms do discard <| tyOf d
    discard <| tyOf cod
    return true
  catch _ => return false

/-- The class method terms of `e` (`isMethodTerm`), each the longest such prefix of an
application of a class projection or of a constant that is not unfolded, and the types
`FTy.den F` of a static `F` at which `e` states an equality; the definitions that the
translation unfolds (`unfoldable`, outside `CatCrypt.Core` and D) are scanned to the depth
`depth`. -/
partial def scanMethods (stat insts recs : Array Expr) (e : Expr) (depth : Nat)
    (acc : Array Expr × Array Expr) : MetaM (Array Expr × Array Expr) := do
  let go (x : Expr) (a : Array Expr × Array Expr) := scanMethods stat insts recs x depth a
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let mut acc := acc
    if fn.isConstOf ``Eq && args.size == 3 then
      let T := args[0]!.consumeMData
      let T ← match ← ftyDen? T with
        | some f => pure (mkApp (mkConst ``FTy.den) f)
        | none => pure T
      if T.isAppOfArity ``FTy.den 1 && stat.contains T.appArg! && !acc.2.contains T then
        acc := (acc.1, acc.2.push T)
    if let .const c lvls := fn then
      let proj := (← getProjectionFnInfo? c).isSome
      let heads := proj || !(← unfoldable c)
      for k' in [0:if heads then args.size else 0] do
        let k := args.size - k'
        let t := mkAppN fn (args.extract 0 k)
        if ← isMethodTerm stat insts recs t then
          let acc' := if acc.1.contains t then acc else (acc.1.push t, acc.2)
          return ← (args.extract k args.size).foldlM (fun a x => go x a) acc'
      acc ← args.foldlM (fun a x => go x a) acc
      let native := (`CatCrypt.Core).isPrefixOf c || (`CatCrypt.Complexity).isPrefixOf c
      if depth > 0 && !native && (← unfoldable c) then
        let info ← getConstInfo c
        if info.hasValue then
          let v ← instantiateValueLevelParams info lvls
          acc ← scanMethods stat insts recs (v.beta args) (depth - 1) acc
      return acc
    args.foldlM (fun a x => go x a) (← go fn acc)
  | .lam _ _ b _ | .forallE _ _ b _ => go b acc
  | .letE _ _ v b _ => go b (← go v acc)
  | .mdata _ b => go b acc
  | .proj _ _ s =>
    if ← isMethodTerm stat insts recs e then
      return if acc.1.contains e then acc else (acc.1.push e, acc.2)
    go s acc
  | _ => return acc

/-- The name of a method term: the last component of its head constant. -/
def methodName (t : Expr) : Name :=
  match t.getAppFn.constName? with
  | some (.str _ s) => .mkSimple s
  | _ => `method

/-- Add the class methods `ms` and the equality methods of the types `eqTys` to the D context,
innermost; `k` receives the parameters, the methods and the equality methods, each with the
variable that stands for it. -/
partial def addMethods (O : Expr) (ms eqTys : List Expr) (ps : Params)
    (methods eqs : List (Expr × Expr))
    (k : Params → List (Expr × Expr) → List (Expr × Expr) → MetaM Unit) : MetaM Unit := do
  match ms, eqTys with
  | t :: ms, _ =>
    let T ← inferType t
    let n := methodName t
    withLocalDeclD n T fun x =>
      addParam O x t n T true ps fun ps' =>
        addMethods O ms eqTys ps' ((t, x) :: methods) eqs k
  | [], T :: eqTys =>
    let dec ← synthInstance? (← mkAppM ``DecidableEq #[T])
    let some inst := dec | addMethods O [] eqTys ps methods eqs k
    let t ← withLocalDeclD `a T fun a => withLocalDeclD `b T fun b => do
      mkLambdaFVars #[a, b] (mkApp2 (mkConst ``Decidable.decide)
        (← mkEq a b) (mkApp2 inst a b))
    let T2 ← inferType t
    withLocalDeclD `eq T2 fun x =>
      addParam O x t `eq T2 true ps fun ps' =>
        addMethods O [] eqTys ps' methods ((T, x) :: eqs) k
  | [], [] => k ps methods eqs

/-- The constructor of the record type `T`, applied to the parameters of `T`, when `T` is a
structure in `Type` (a class or not) that has no representation in D. -/
def recordCtor? (T : Expr) : MetaM (Option Expr) := do
  if ← isProp T then return none
  let T' ← whnf T
  let .const sn lvls := T'.getAppFn | return none
  let env ← getEnv
  unless isStructure env sn do return none
  if (← observing? (tyOf T)).isSome then return none
  let ctor := getStructureCtor env sn
  return some (mkAppN (mkConst ctor.name lvls) T'.getAppArgs)

/-- Whether the constructor `ctor` (applied to its parameters) has a field that is a type. -/
def hasTypeField (ctor : Expr) : MetaM Bool := do
  forallTelescopeReducing (← inferType ctor) fun xs _ =>
    xs.anyM fun x => return (← inferType x).isSort

/-- Unbundle the record parameter `n` with constructor `ctor`: a field that is a type is a
static parameter `F : FTy` and is `FTy.den F` in the record, every other field (data, instance
or proof) a binder of the theorems among `insts`; `k` receives the record, the constructor
applied to the fields. -/
partial def unbundle (n : Name) (e : Expr) (ps : Params) (k : Params → Expr → MetaM Unit) :
    MetaM Unit := do
  match ← whnf (← inferType e) with
  | .forallE fn fT _ bi =>
    let nm := n.appendAfter s!"_{fn.eraseMacroScopes}"
    if fT.isSort then
      unless fT == mkSort Level.one do
        throwError "reflect_d: the field `{fn}` of the record `{n}` is not a type in `Type`"
      withLocalDeclD (nm.appendAfter "F") (mkConst ``FTy) fun f =>
        unbundle n (mkApp e (mkApp (mkConst ``FTy.den) f))
          { ps with statics := ps.statics.push f } k
    else
      withLocalDecl nm (if bi.isInstImplicit then .instImplicit else .default) fT fun x =>
        unbundle n (mkApp e x)
          { ps with insts := ps.insts.push x, recs := ps.recs.push x,
                    dBinders := ps.dBinders.push x, cBinders := ps.cBinders.push x } k
  | _ => k ps e

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
        if let some inst ← synthInstance? T then
          params fuel (b.instantiate1 inst) { ps with args := ps.args.push inst } k
        else if let some ctor ← (do
            let some ctor ← recordCtor? T | pure none
            if ← hasTypeField ctor then pure (some ctor) else pure none) then
          unbundle n ctor ps fun ps' r =>
            params fuel (b.instantiate1 r) { ps' with args := ps'.args.push r } k
        else if ← isProp T then
          withLocalDecl n .instImplicit T fun h =>
            params fuel (b.instantiate1 h)
              { ps with dBinders := ps.dBinders.push h, cBinders := ps.cBinders.push h,
                        args := ps.args.push h } k
        else
          unless T.hasAnyFVar (fun fv => ps.statics.any (·.fvarId! == fv)) do
            throwError "reflect_d: no instance `{T}` at the representation of the parameters"
          withLocalDecl n .instImplicit T fun i =>
            params fuel (b.instantiate1 i)
              { ps with insts := ps.insts.push i, dBinders := ps.dBinders.push i,
                        cBinders := ps.cBinders.push i, args := ps.args.push i } k
      else if ← isProp T then
        withLocalDecl n bi T fun h =>
          params fuel (b.instantiate1 h)
            { ps with dBinders := ps.dBinders.push h, cBinders := ps.cBinders.push h,
                      args := ps.args.push h } k
      else if let some ctor ← recordCtor? T then
        if ← hasTypeField ctor then
          unbundle n ctor ps fun ps' r =>
            params fuel (b.instantiate1 r) { ps' with args := ps'.args.push r } k
        else
          withLocalDeclD n T fun x =>
            params fuel (b.instantiate1 x)
              { ps with insts := ps.insts.push x, recs := ps.recs.push x,
                        dBinders := ps.dBinders.push x, cBinders := ps.cBinders.push x,
                        args := ps.args.push x } k
      else if ps.inType.getD ps.args.size (b.hasLooseBVar 0) || !bi.isExplicit then
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
        withLocalDeclD n T fun x =>
          addParam O x x n T false ps fun ps' => params fuel (b.instantiate1 x) ps' k
    -- A binder is used when the body or the type of a later binder that is not a proof
    -- mentions it, and occurs in a type when the type of a later binder that is not a proof
    -- or the result type mentions it.
    let used ← lambdaTelescope info.value fun xs body => do
      let mut us : Array Bool := #[]
      for h : j in [0:xs.size] do
        let fv := xs[j].fvarId!
        let mut u := body.containsFVar fv
        for k in [j+1:xs.size] do
          let Tk ← inferType xs[k]!
          if Tk.containsFVar fv && !(← isProp Tk) then u := true
        us := us.push u
      return us
    let inType ← forallTelescope info.type fun xs res => do
      let mut us : Array Bool := #[]
      for h : j in [0:xs.size] do
        let fv := xs[j].fvarId!
        let mut u := res.containsFVar fv
        for k in [j+1:xs.size] do
          let Tk ← inferType xs[k]!
          if Tk.containsFVar fv && !(← isProp Tk) then u := true
        us := us.push u
      return us
    params 1024 info.type { rho := mkConst ``Env.nil, used, inType } fun ps bodyT => do
      let body := if (Structural.eqnInfoExt.find? (← getEnv) c).isSome then
          mkAppN (mkConst c) ps.args
        else info.value.beta ps.args
      let (ms, eqTys) ← if ps.insts.isEmpty then pure (#[], #[])
        else scanMethods ps.statics ps.insts ps.recs body 8 (#[], #[])
      let ms := ms.qsort (fun a b => a.approxDepth.toNat > b.approxDepth.toNat)
      addMethods O ms.toList eqTys.toList ps [] [] fun ps methods eqs => do
      let ctx : Ctx := { entries := ps.entries, tys := ps.tys, rho := ps.rho, oracle := O,
                         methods, eqMethods := eqs }
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
      -- In a `module` file the D-term is exposed, so that importing modules unfold it (as
      -- the costed forms of `derive_timed` are): the time link of `TimedLink` walks its body.
      withExporting (isExporting := (← getEnv).header.isModule) <| addDecl (.defnDecl dv)
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
