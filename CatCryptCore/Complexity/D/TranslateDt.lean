/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Translate
public import CatCryptCore.Complexity.D.TimedLink
public import CatCryptCore.Tactics.StdCosts

/-!
# The charges of `derive_timed` on D terms, with one soundness theorem

`Tm.dt t η` (`η` a translated environment) is the costed tree that `derive_timed` assigns to
the source of a D term `t`, stated on the syntax of D: a `let` and a `seq` are free, a call
costs one plus the callee and the argument (a call on `unit` costs the callee and the
argument), a conditional and a match on a sum or a list cost one plus the scrutinee and the
branch taken, constructors, projections, literals, variables and abstractions are free, an
operation on words or `Bool` costs one, a left fold costs the registered cost
`List.foldl.timedCost` of its step closure, an iteration one plus the step per round
(`iterCost`), and a `sample`, `get`, `set` or `query` node costs its unit. `Tm.allow t` counts
on the syntax the β-steps of D that these charges leave out: one per `letE` and `seq`, one per
call on `unit`.
This is the cost model of the call-by-value λ-calculus of Forster and Kunze (*A Certifying
Extraction with Time Bounds from Coq to Call-By-Value Lambda Calculus*, ITP 2019), with the
charges of `derive_timed`.

Values are translated by `Ty.hat`: a first-order type to its values, a function type to a pure
costed closure, a function and its cost. An environment `EnvHat Γ` gives a variable of function
type a costed tree for each argument (`Ty.hatE`), so that a function variable is an effectful
parameter, as in the telescope of `link_timed`. `Sim` relates translated values and values of
D (the step equation of a data function at function types), `SimE` an environment entry and a
value (`TimedSim` at allowance `0` for a function variable).

The soundness theorem `Tm.dt_timedSim` states, for a term of the fragment `Tm.InDtFrag` in
related environments, `TimedSim (Sim τ) 1 t.allow (t.dt η) (t.eval ρ)`: the evaluation of
`t` has the effect nodes of `t.dt η` and at most `t.allow` plus its charges as steps on every
path. It holds at any charge `cc a ≤ 1` of a call of a function variable (`Tm.dtC_timedSim`,
with allowance `Tm.allowC cc`): the β-step of the call is paid by its charge and by the
allowance `1 - cc a`. At the charge `1` of every call, the allowance does not depend on the
argument types, so that it reduces to a numeral at a type `base MF` for a variable `MF`, where
`callCost` is undecided. Its corollaries are the cost bound `Tm.cost_le_dt` and the meaning of the
erasure `Tm.dt_run`, `Tm.dt_erase`.

The fragment: variables of a type other than a function type, calls of function variables and
of pure costed closures, abstractions with a pure body (`Tm.Pure`: no effect and no call of a
function variable), `letE`, `seq`, literals, pairs and projections, sums and `case`, lists and
`lcase`, `ite`, `foldl` and `iter` with a step that is a pure costed closure, operations of unit
cost (on words and `Bool`), `sample`, `get`, `set`, `query` and `fail`. Operations on `ℕ` and on
`Fin (n + 1)` are outside it.

## Main definitions

* `Ty.hat`, `Ty.hatE`, `Sim`, `SimE`, `EnvHat`, `SimEnv`
* `Tm.dtC`, `Tm.allowC`: the charges and the allowance at a charge `cc a ≤ 1` of a call;
  `Tm.dt`, `Tm.allow`: at the charge `callCost` of `derive_timed`
* `Tm.Pure`, `Tm.InDtFrag`, `iterCost`

## Main results

* `TimedSimTree.bindCont`, `TimedSim.bindCont`: the costed bind against a D bind under any
  continuation.
* `Tm.dtC_timedSim`, `Tm.dt_timedSim`, `Tm.cost_le_dt`, `Tm.dt_run`, `Tm.dt_erase`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core

/-! ## Simulation under any continuation -/

namespace TimedSimTree

variable {α β γ δ : Type} {R : α → β → Prop} {K : ℕ}

/-- The relation on the leaves may be weakened. -/
theorem rel_mono {R' : α → β → Prop} (hR : ∀ a v, R a v → R' a v) {n : ℕ}
    {A : SPTree.Timed α} {t : CTree β} (h : TimedSimTree R K n A t) :
    TimedSimTree R' K n A t := by
  induction h with
  | ret hr => exact .ret (hR _ _ hr)
  | tick _ hm ih => exact .tick ih hm
  | sample f e m _ hm ih => exact .sample f e m ih hm
  | get i f m _ hm ih => exact .get i f m ih hm
  | set i f v m _ hm ih => exact .set i f v m ih hm
  | fail => exact .fail
  | query d r x m _ hm ih => exact .query d r x m ih hm

/-- A costed bind and a D bind under any continuation. -/
theorem bindCont {S : γ → δ → Prop} {f : α → ℕ × SPTree.Timed γ} {g : β → CTree δ} {m : ℕ}
    (hf : ∀ a v, R a v → TimedSimTree S K (m + K * (f a).1) (f a).2 (g v))
    {n : ℕ} {A : SPTree.Timed α} {t : CTree β} (h : TimedSimTree R K n A t) :
    TimedSimTree S K (n + m + K * (A.bind f).1) (A.bind f).2 (t.bind g) := by
  induction h with
  | ret hR => exact (hf _ _ hR).mono (by simp only [SPTree.Timed.bind]; omega)
  | tick _ hm ih => exact .tick ih (by omega)
  | sample f' e mb _ hmb ih =>
    refine .sample f' e (fun b => mb b + m + K * (SPTree.Timed.bind _ f).1) ih fun b => ?_
    have := hmb b
    rw [Nat.mul_add]
    omega
  | get i f' mb _ hmb ih =>
    refine .get i f' (fun x => mb x + m + K * (SPTree.Timed.bind _ f).1) ih fun x => ?_
    have := hmb x
    rw [Nat.mul_add]
    omega
  | set i f' v mb _ hmb ih =>
    refine .set i f' v (mb + m + K * (SPTree.Timed.bind _ f).1) ih ?_
    rw [Nat.mul_add]
    omega
  | fail => exact .fail
  | query d r x mb _ hmb ih =>
    refine .query d r x (fun y => mb y + m + K * (SPTree.Timed.bind _ f).1) ih fun y => ?_
    have := hmb y
    rw [Nat.mul_add]
    omega

end TimedSimTree

/-- The costed bind of a step-prefixed tree: its step cost in front of the bind of its tree. -/
noncomputable def bindT {α β : Type} (x : ℕ × SPTree.Timed α) (f : α → ℕ × SPTree.Timed β) :
    ℕ × SPTree.Timed β :=
  SPTree.Timed.delay x.1 (x.2.bind f)

namespace TimedSim

variable {α β γ δ : Type} {R : α → β → Prop} {K n : ℕ}

/-- The relation on the leaves may be weakened. -/
theorem rel_mono {R' : α → β → Prop} (hR : ∀ a v, R a v → R' a v)
    {x : ℕ × SPTree.Timed α} {t : CTree β} (h : TimedSim R K n x t) : TimedSim R' K n x t :=
  TimedSimTree.rel_mono hR h

/-- A costed bind and a D bind under any continuation, the allowances added. -/
theorem bindCont {S : γ → δ → Prop} {f : α → ℕ × SPTree.Timed γ} {g : β → CTree δ} {m : ℕ}
    {x : ℕ × SPTree.Timed α} {t : CTree β} (hx : TimedSim R K n x t)
    (hf : ∀ a v, R a v → TimedSim S K m (f a) (g v)) :
    TimedSim S K (n + m) (bindT x f) (t.bind g) := by
  refine (TimedSimTree.bindCont (m := m) hf hx).mono ?_
  simp only [bindT, SPTree.Timed.delay, Nat.mul_add]
  omega

/-- A step cost `c` in front of the costed tree and the allowance `m` pay for a tick in front of
the D tree. -/
theorem delay_tick_le {m c : ℕ} {x : ℕ × SPTree.Timed α} {t : CTree β}
    (h : TimedSim R K n x t) (hc : 1 ≤ m + K * c) :
    TimedSim R K (n + m) (SPTree.Timed.delay c x) (.tick t) := by
  refine TimedSimTree.tick h ?_
  simp only [SPTree.Timed.delay, Nat.mul_add]
  omega

/-- Related leaves after `m` ticks of the D tree, paid by the allowance and the step cost. -/
theorem stepN_ret {m c : ℕ} {a : α} {w : β} (h : R a w) (hm : m ≤ n + K * c) :
    TimedSim R K n (c, .ret a) (stepN CTree.tick m (.ret w)) :=
  TimedSimTree.stepN_tick (TimedSimTree.ret (n := 0) h) m (by grind)

end TimedSim

/-! ## Translated values -/

/-- The translated values of a type: a function type is a pure costed closure, a function and
its cost; the other types have their values. -/
def Ty.hat : Ty → Type
  | .base f => f.den
  | .nat => ℕ
  | .prod a b => Ty.hat a × Ty.hat b
  | .sum a b => Ty.hat a ⊕ Ty.hat b
  | .arr a b => (Ty.hat a → Ty.hat b) × (Ty.hat a → ℕ)
  | .list a => List (Ty.hat a)

/-- The translated environment entries: a variable of function type is a costed tree for each
argument, a variable of any other type a translated value. -/
def Ty.hatE : Ty → Type 1
  | .base f => ULift (Ty.hat (.base f))
  | .nat => ULift (Ty.hat .nat)
  | .prod a b => ULift (Ty.hat (.prod a b))
  | .sum a b => ULift (Ty.hat (.sum a b))
  | .arr a b => Ty.hat a → ℕ × SPTree.Timed (Ty.hat b)
  | .list a => ULift (Ty.hat (.list a))

/-- Whether a type is a function type. -/
def Ty.isArr : Ty → Bool
  | .arr _ _ => true
  | _ => false

/-- A translated value as an environment entry: a pure costed closure is the costed tree of
its value behind its cost. -/
noncomputable def Ty.ofHat : (τ : Ty) → τ.hat → τ.hatE
  | .base _, u => ⟨u⟩
  | .nat, u => ⟨u⟩
  | .prod _ _, u => ⟨u⟩
  | .sum _ _, u => ⟨u⟩
  | .arr _ _, p => fun u => (p.2 u, .ret (p.1 u))
  | .list _, u => ⟨u⟩

/-- The costed tree of a variable read: the entry as a value at no cost; a variable of
function type is not read as a value. -/
noncomputable def Ty.read : (τ : Ty) → τ.hatE → ℕ × SPTree.Timed τ.hat
  | .base _, u => (0, .ret u.down)
  | .nat, u => (0, .ret u.down)
  | .prod _ _, u => (0, .ret u.down)
  | .sum _ _, u => (0, .ret u.down)
  | .arr _ _, _ => (0, .fail)
  | .list _, u => (0, .ret u.down)

/-- The value of D of a translated first-order value. -/
def Ty.toVal : (τ : Ty) → τ.FO → τ.hat → Val τ
  | .base _, _, u => u
  | .nat, _, u => u
  | .prod a b, h, u => (a.toVal h.1 u.1, b.toVal h.2 u.2)
  | .sum a b, h, u => Sum.map (a.toVal h.1) (b.toVal h.2) u
  | .arr _ _, h, _ => False.elim h
  | .list a, h, u => List.map (a.toVal h) u

/-- The translated value of a first-order value of D. -/
def Ty.ofVal : (τ : Ty) → τ.FO → Val τ → τ.hat
  | .base _, _, v => v
  | .nat, _, v => v
  | .prod a b, h, v => (a.ofVal h.1 v.1, b.ofVal h.2 v.2)
  | .sum a b, h, v => Sum.map (a.ofVal h.1) (b.ofVal h.2) v
  | .arr _ _, h, _ => False.elim h
  | .list a, h, v => List.map (a.ofVal h) v

/-- Translated values and values of D: equal at ground types, componentwise at products, sums
and lists, and at a function type the step equation of a data function, its steps bounded by
the cost of the closure. -/
def Sim : (τ : Ty) → τ.hat → Val τ → Prop
  | .base _, u, v => u = v
  | .nat, u, v => u = v
  | .prod a b, u, v => Sim a u.1 v.1 ∧ Sim b u.2 v.2
  | .sum a b, u, v => Sum.LiftRel (Sim a) (Sim b) u v
  | .arr a b, p, g => ∀ u v, Sim a u v →
      ∃ m w, g v = stepN CTree.tick m (.ret w) ∧ m ≤ p.2 u ∧ Sim b (p.1 u) w
  | .list a, u, v => List.Forall₂ (Sim a) u v

/-- Environment entries and values of D: `Sim` at a type other than a function type; at a
function type, the costed tree of each related argument simulates the call at allowance
`0`. -/
def SimE : (τ : Ty) → τ.hatE → Val τ → Prop
  | .base f, u, v => Sim (.base f) u.down v
  | .nat, u, v => Sim .nat u.down v
  | .prod a b, u, v => Sim (.prod a b) u.down v
  | .sum a b, u, v => Sim (.sum a b) u.down v
  | .arr a b, F, g => ∀ u v, Sim a u v → TimedSim (Sim b) 1 0 (F u) (g v)
  | .list a, u, v => Sim (.list a) u.down v

/-- Translated environments. -/
def EnvHat (Γ : List Ty) : Type 1 := (τ : Ty) → Var Γ τ → τ.hatE

/-- Extend a translated environment by a translated value for the innermost variable. -/
noncomputable def EnvHat.cons {Γ : List Ty} {σ : Ty} (u : σ.hat) (η : EnvHat Γ) : EnvHat (σ :: Γ) :=
  fun _ x => match x with
    | .here => Ty.ofHat σ u
    | .there y => η _ y

/-- Related environments: every entry is related to the value of its variable. -/
def SimEnv {Γ : List Ty} (η : EnvHat Γ) (ρ : Env Γ) : Prop :=
  ∀ τ (x : Var Γ τ), SimE τ (η τ x) (ρ τ x)

/-! ## Lemmas on translated values -/

/-- At a first-order type, a value of D related to a translated value is its value of D. -/
theorem Sim.toVal_eq : ∀ (τ : Ty) (h : τ.FO) {u : τ.hat} {v : Val τ}, Sim τ u v →
    v = τ.toVal h u := by
  intro τ
  induction τ with
  | base f => intro _ u v hs; exact hs.symm
  | nat => intro _ u v hs; exact hs.symm
  | prod a b iha ihb =>
    intro h u v hs
    exact Prod.ext (iha h.1 hs.1) (ihb h.2 hs.2)
  | sum a b iha ihb =>
    intro h u v hs
    cases hs with
    | inl hs => exact congrArg Sum.inl (iha h.1 hs)
    | inr hs => exact congrArg Sum.inr (ihb h.2 hs)
  | arr a b _ _ => intro h; exact h.elim
  | list a ih =>
    intro h u v hs
    induction hs with
    | nil => rfl
    | cons hx _ ihl => exact congrArg₂ List.cons (ih h hx) ihl

/-- At a first-order type, the translated value of a value of D is related to it. -/
theorem Sim.ofVal : ∀ (τ : Ty) (h : τ.FO) (v : Val τ), Sim τ (τ.ofVal h v) v := by
  intro τ
  induction τ with
  | base f => intro _ v; rfl
  | nat => intro _ v; rfl
  | prod a b iha ihb => intro h v; exact ⟨iha h.1 v.1, ihb h.2 v.2⟩
  | sum a b iha ihb =>
    intro h v
    cases v with
    | inl x => exact Sum.LiftRel.inl (iha h.1 x)
    | inr y => exact Sum.LiftRel.inr (ihb h.2 y)
  | arr a b _ _ => intro h; exact h.elim
  | list a ih =>
    intro h v
    induction v with
    | nil => exact List.Forall₂.nil
    | cons x xs ihl => exact List.Forall₂.cons (ih h x) ihl

/-- A related translated value is a related environment entry. -/
theorem SimE.ofHat (τ : Ty) {u : τ.hat} {v : Val τ} (hs : Sim τ u v) :
    SimE τ (τ.ofHat u) v := by
  cases τ with
  | arr a b =>
    intro u' v' huv
    obtain ⟨m, w, hg, hm, hw⟩ := hs u' v' huv
    rw [hg]
    exact TimedSim.stepN_ret hw (by omega)
  | _ => exact hs

/-- The read of a related entry of a type other than a function type simulates the returned
value. -/
theorem SimE.read (τ : Ty) (h : τ.isArr = false) {e : τ.hatE} {v : Val τ} (hs : SimE τ e v) :
    TimedSim (Sim τ) 1 0 (τ.read e) (.ret v) := by
  cases τ with
  | arr a b => simp [Ty.isArr] at h
  | _ => exact TimedSim.ret hs

/-- Related environments extended by related values are related. -/
theorem SimEnv.cons {Γ : List Ty} {σ : Ty} {η : EnvHat Γ} {ρ : Env Γ} {u : σ.hat}
    {v : Val σ} (hρ : SimEnv η ρ) (hs : Sim σ u v) : SimEnv (η.cons u) (ρ.cons v) := by
  intro τ x
  cases x with
  | here => exact SimE.ofHat σ hs
  | there y => exact hρ _ y

/-- Every translated type is inhabited. -/
theorem Ty.hat_nonempty : ∀ τ : Ty, Nonempty τ.hat
  | .base f => FTy.instNonempty f
  | .nat => ⟨(0 : ℕ)⟩
  | .prod a b => ⟨(Classical.choice (Ty.hat_nonempty a), Classical.choice (Ty.hat_nonempty b))⟩
  | .sum a _ => ⟨Sum.inl (Classical.choice (Ty.hat_nonempty a))⟩
  | .arr _ b => ⟨(fun _ => Classical.choice (Ty.hat_nonempty b), fun _ => 0)⟩
  | .list _ => ⟨[]⟩

/-- The value of a costed tree that is a leaf; a chosen value at any other tree. -/
noncomputable def Ty.pureVal (τ : Ty) : SPTree.Timed τ.hat → τ.hat
  | .ret a => a
  | _ => Classical.choice (Ty.hat_nonempty τ)

/-- A D tree simulated by a leaf is a leaf after at most the allowance and the step cost in
ticks. -/
theorem TimedSim.ret_inv {α β : Type} {R : α → β → Prop} {K n : ℕ} {x : ℕ × SPTree.Timed α}
    {a : α} (hx : x.2 = .ret a) {t : CTree β} (h : TimedSim R K n x t) :
    ∃ m w, t = stepN CTree.tick m (.ret w) ∧ m ≤ n + K * x.1 ∧ R a w := by
  unfold TimedSim at h
  rw [hx] at h
  generalize n + K * x.1 = N at h ⊢
  induction t generalizing N with
  | ret w => cases h with | ret hr => exact ⟨0, w, rfl, Nat.zero_le _, hr⟩
  | tick t ih =>
    cases h with
    | tick h hm =>
      obtain ⟨m, w, he, hle, hr⟩ := ih _ h
      exact ⟨m + 1, w, by rw [he]; rfl, by omega, hr⟩
  | _ => cases h

/-! ## The charges on D syntax -/

/-- The charge of a call on an argument of type `a`: one, and none on `unit`. -/
def callCost (a : Ty) : ℕ := if a = .unit then 0 else 1

/-- The charge of a call is at most one. -/
theorem callCost_le_one (a : Ty) : callCost a ≤ 1 := by
  unfold callCost; split <;> omega

/-- The charge of `k` rounds of a pure costed closure from `acc`: one plus the cost of the
closure per round. -/
def iterCost {c : Ty} (p : Ty.hat (.arr c c)) : c.hat → ℕ → ℕ
  | _, 0 => 0
  | acc, k + 1 => 1 + p.2 acc + iterCost p (p.1 acc) k

/-- Whether `derive_timed` and D both charge a primitive operation one step: the operations on
words and `Bool`. -/
def Prim.unitCost {a b : Ty} : Prim a b → Bool
  | .natAdd | .natSub | .natMul | .natDiv | .natMod | .natEq | .natLt => false
  | .finAdd _ | .finSub _ | .finMul _ | .finEq _ | .finLt _ | .finOfNat _ | .finToNat _ =>
    false
  | _ => true

/-- An operation of unit cost costs D one step at every argument. -/
theorem Prim.cost_eq_one_of_unitCost {a b : Ty} (p : Prim a b) (hp : p.unitCost = true)
    (v : Val a) : p.cost v = 1 := by
  cases p <;> simp_all [Prim.unitCost, Prim.cost]

/-- A primitive operation on translated values. -/
def Prim.applyHat {a b : Ty} (p : Prim a b) (u : a.hat) : b.hat :=
  b.ofVal p.fo.2 (p.apply (a.toVal p.fo.1 u))

namespace Tm

variable {Γ : List Ty} {τ : Ty}

/-- The variable a term is, if it is one. -/
def headVar? : {Γ : List Ty} → {τ : Ty} → Tm Γ τ → Option (Var Γ τ)
  | _, _, .var y => some y
  | _, _, _ => none

/-- A term with a head variable is that variable. -/
theorem eq_var_of_headVar? {t : Tm Γ τ} {y : Var Γ τ} (h : t.headVar? = some y) :
    t = .var y := by
  cases t <;> simp_all [headVar?]

/-- The allowance of a term at the charge `cc a` of a call of a function variable on an argument
of type `a`: the β-steps of D that the charges leave out, one per `letE` and `seq` and `1 - cc a`
per call; the allowance of the body of an abstraction is part of the cost of its closure. -/
def allowC (cc : Ty → ℕ) : {Γ : List Ty} → {τ : Ty} → Tm Γ τ → ℕ
  | _, _, .app (a := a) f x => f.allowC cc + x.allowC cc + (1 - cc a)
  | _, _, .letE e b => e.allowC cc + b.allowC cc + 1
  | _, _, .seq e b => e.allowC cc + b.allowC cc + 1
  | _, _, .prim _ x => x.allowC cc
  | _, _, .pair x y => x.allowC cc + y.allowC cc
  | _, _, .fst p => p.allowC cc
  | _, _, .snd p => p.allowC cc
  | _, _, .inl x => x.allowC cc
  | _, _, .inr x => x.allowC cc
  | _, _, .case s l r => s.allowC cc + max (l.allowC cc) (r.allowC cc)
  | _, _, .ite c t e => c.allowC cc + max (t.allowC cc) (e.allowC cc)
  | _, _, .cons x xs => x.allowC cc + xs.allowC cc
  | _, _, .lcase xs n c => xs.allowC cc + max (n.allowC cc) (c.allowC cc)
  | _, _, .foldl f i xs => f.allowC cc + i.allowC cc + xs.allowC cc
  | _, _, .iter n f i => n.allowC cc + f.allowC cc + i.allowC cc
  | _, _, .set _ _ x => x.allowC cc
  | _, _, .query _ _ x => x.allowC cc
  | _, _, _ => 0

/-- The costed tree of the charges of `derive_timed` for a term, a call of a function variable on
an argument of type `a` charged `cc a`; outside the fragment `InDtFrag` it is `fail`. An
abstraction is the pure costed closure that reads the value of its body at the leaf and costs the
allowance and the step cost of the body. -/
noncomputable def dtC (cc : Ty → ℕ) :
    {Γ : List Ty} → {τ : Ty} → Tm Γ τ → EnvHat Γ → ℕ × SPTree.Timed τ.hat
  | _, τ, .var x, η => τ.read (η τ x)
  | _, _, .lam (b := b) body, η =>
    (0, .ret (fun u => b.pureVal (body.dtC cc (η.cons u)).2,
      fun u => body.allowC cc + (body.dtC cc (η.cons u)).1))
  | _, _, .app (a := a) f x, η =>
    match f.headVar? with
    | some y => bindT (x.dtC cc η) fun u => SPTree.Timed.delay (cc a) (η _ y u)
    | none => bindT (f.dtC cc η) fun p => bindT (x.dtC cc η) fun u => (1 + p.2 u, .ret (p.1 u))
  | _, _, .letE e b, η => bindT (e.dtC cc η) fun u => b.dtC cc (η.cons u)
  | _, _, .seq e b, η => bindT (e.dtC cc η) fun _ => b.dtC cc η
  | _, _, .natLit n, _ => (0, .ret n)
  | _, _, .lit _ v, _ => (0, .ret v)
  | _, _, .prim p x, η => bindT (x.dtC cc η) fun u => (1, .ret (p.applyHat u))
  | _, _, .pair x y, η => bindT (x.dtC cc η) fun u => bindT (y.dtC cc η) fun w => (0, .ret (u, w))
  | _, _, .fst p, η => bindT (p.dtC cc η) fun u => (0, .ret u.1)
  | _, _, .snd p, η => bindT (p.dtC cc η) fun u => (0, .ret u.2)
  | _, _, .inl (a := a) (b := b) x, η =>
    bindT (x.dtC cc η) fun u => (0, .ret (Sum.inl u : a.hat ⊕ b.hat))
  | _, _, .inr (a := a) (b := b) x, η =>
    bindT (x.dtC cc η) fun u => (0, .ret (Sum.inr u : a.hat ⊕ b.hat))
  | _, _, .case (a := a) (b := b) s l r, η =>
    bindT (s.dtC cc η) fun (u : a.hat ⊕ b.hat) =>
      SPTree.Timed.delay 1
        (Sum.elim (fun x => l.dtC cc (η.cons x)) (fun y => r.dtC cc (η.cons y)) u)
  | _, _, .ite c t e, η =>
    bindT (c.dtC cc η) fun (b : Bool) =>
      SPTree.Timed.delay 1 (bif b then t.dtC cc η else e.dtC cc η)
  | _, _, .nil (a := a), _ => (0, .ret ([] : List a.hat))
  | _, _, .cons (a := a) x xs, η =>
    bindT (x.dtC cc η) fun u => bindT (xs.dtC cc η) fun (l : List a.hat) => (0, .ret (u :: l))
  | _, _, .lcase (a := a) xs n c, η =>
    bindT (xs.dtC cc η) fun (l : List a.hat) => SPTree.Timed.delay 1
      (match l with
        | [] => n.dtC cc η
        | x :: l' => c.dtC cc ((η.cons (σ := .list a) l').cons x))
  | _, _, .foldl (a := a) (c := c) f i xs, η =>
    bindT (f.dtC cc η) fun (p : Ty.hat (.arr (.prod c a) c)) => bindT (i.dtC cc η) fun acc =>
      bindT (xs.dtC cc η) fun (l : List a.hat) =>
        (List.foldl.timedCost (fun x y => p.1 (x, y)) (fun x y => p.2 (x, y)) acc l,
          .ret (List.foldl (fun x y => p.1 (x, y)) acc l))
  | _, _, .iter (c := c) n f i, η =>
    bindT (n.dtC cc η) fun (k : ℕ) => bindT (f.dtC cc η) fun (p : Ty.hat (.arr c c)) =>
      bindT (i.dtC cc η) fun acc => (iterCost p acc k, .ret (p.1^[k] acc))
  | _, _, .sample f, _ =>
    (0, .sample f.den (FTy.instFintype f) (FTy.instNonempty f) (fun _ => 0) fun v => .ret v)
  | _, _, .get n f, _ => (0, .get (f.loc n) (fun _ => 0) fun v => .ret v)
  | _, _, .set n f x, η => bindT (x.dtC cc η) fun u => (0, .set (f.loc n) u 0 (.ret ()))
  | _, _, .query _ r x, η => bindT (x.dtC cc η) fun _ =>
    (0, .sample r.den (FTy.instFintype r) (FTy.instNonempty r) (fun _ => 0) fun v => .ret v)
  | _, _, .fail, _ => (0, .fail)

/-- The allowance at the charges of `derive_timed`: `callCost`, one per call and none on `unit`. -/
def allow (t : Tm Γ τ) : ℕ := t.allowC callCost

/-- The costed tree of the charges of `derive_timed`: `dtC` at the charge `callCost` of a call. -/
noncomputable def dt (t : Tm Γ τ) (η : EnvHat Γ) : ℕ × SPTree.Timed τ.hat := t.dtC callCost η

/-- The pure terms: no effect and no call of a function variable. Their costed trees are
leaves (`dt_pure`), so that an abstraction with a pure body is a pure costed closure. -/
def Pure : {Γ : List Ty} → {τ : Ty} → Tm Γ τ → Prop
  | _, τ, .var _ => τ.isArr = false
  | _, _, .lam _ => True
  | _, _, .app f x => f.headVar? = none ∧ f.Pure ∧ x.Pure
  | _, _, .letE e b => e.Pure ∧ b.Pure
  | _, _, .seq e b => e.Pure ∧ b.Pure
  | _, _, .natLit _ => True
  | _, _, .lit _ _ => True
  | _, _, .prim _ x => x.Pure
  | _, _, .pair x y => x.Pure ∧ y.Pure
  | _, _, .fst p => p.Pure
  | _, _, .snd p => p.Pure
  | _, _, .inl x => x.Pure
  | _, _, .inr x => x.Pure
  | _, _, .case s l r => s.Pure ∧ l.Pure ∧ r.Pure
  | _, _, .ite c t e => c.Pure ∧ t.Pure ∧ e.Pure
  | _, _, .nil => True
  | _, _, .cons x xs => x.Pure ∧ xs.Pure
  | _, _, .lcase xs n c => xs.Pure ∧ n.Pure ∧ c.Pure
  | _, _, .foldl f i xs => f.Pure ∧ i.Pure ∧ xs.Pure
  | _, _, .iter n f i => n.Pure ∧ f.Pure ∧ i.Pure
  | _, _, _ => False

/-- The costed tree of a pure term is a leaf. -/
theorem dtC_pure (cc : Ty → ℕ) : ∀ {Γ : List Ty} {τ : Ty} (t : Tm Γ τ), t.Pure →
    ∀ η : EnvHat Γ, ∃ u, (t.dtC cc η).2 = .ret u := by
  intro Γ τ t
  induction t with
  | @var _ σ x =>
    intro ht η
    cases σ <;> simp_all [Pure, Ty.isArr, dtC, Ty.read]
  | lam b ih => intro _ η; exact ⟨_, rfl⟩
  | app f x ihf ihx =>
    intro ht η
    obtain ⟨hv, hf, hx⟩ := ht
    obtain ⟨p, hp⟩ := ihf hf η
    obtain ⟨u, hu⟩ := ihx hx η
    simp [dtC, hv, bindT, SPTree.Timed.delay, hp, hu, SPTree.Timed.bind]
  | letE e b ihe ihb =>
    intro ht η
    obtain ⟨u, hu⟩ := ihe ht.1 η
    obtain ⟨w, hw⟩ := ihb ht.2 (η.cons u)
    simp [dtC, bindT, SPTree.Timed.delay, hu, hw, SPTree.Timed.bind]
  | seq e b ihe ihb =>
    intro ht η
    obtain ⟨u, hu⟩ := ihe ht.1 η
    obtain ⟨w, hw⟩ := ihb ht.2 η
    simp [dtC, bindT, SPTree.Timed.delay, hu, hw, SPTree.Timed.bind]
  | natLit n => intro _ η; exact ⟨_, rfl⟩
  | lit f v => intro _ η; exact ⟨_, rfl⟩
  | prim p x ih =>
    intro ht η
    obtain ⟨u, hu⟩ := ih ht η
    simp [dtC, bindT, SPTree.Timed.delay, hu, SPTree.Timed.bind]
  | pair x y ihx ihy =>
    intro ht η
    obtain ⟨u, hu⟩ := ihx ht.1 η
    obtain ⟨w, hw⟩ := ihy ht.2 η
    simp only [dtC, bindT, SPTree.Timed.delay, hu, hw, SPTree.Timed.bind]
    exact ⟨_, rfl⟩
  | fst p ih =>
    intro ht η
    obtain ⟨u, hu⟩ := ih ht η
    simp [dtC, bindT, SPTree.Timed.delay, hu, SPTree.Timed.bind]
  | snd p ih =>
    intro ht η
    obtain ⟨u, hu⟩ := ih ht η
    simp [dtC, bindT, SPTree.Timed.delay, hu, SPTree.Timed.bind]
  | inl x ih =>
    intro ht η
    obtain ⟨u, hu⟩ := ih ht η
    simp only [dtC, bindT, SPTree.Timed.delay, hu, SPTree.Timed.bind]
    exact ⟨_, rfl⟩
  | inr x ih =>
    intro ht η
    obtain ⟨u, hu⟩ := ih ht η
    simp only [dtC, bindT, SPTree.Timed.delay, hu, SPTree.Timed.bind]
    exact ⟨_, rfl⟩
  | case s l r ihs ihl ihr =>
    intro ht η
    obtain ⟨u, hu⟩ := ihs ht.1 η
    cases u with
    | inl x =>
      obtain ⟨w, hw⟩ := ihl ht.2.1 (η.cons x)
      simp [dtC, bindT, SPTree.Timed.delay, hu, hw, SPTree.Timed.bind]
    | inr y =>
      obtain ⟨w, hw⟩ := ihr ht.2.2 (η.cons y)
      simp [dtC, bindT, SPTree.Timed.delay, hu, hw, SPTree.Timed.bind]
  | ite c t e ihc iht ihe =>
    intro ht η
    obtain ⟨u, hu⟩ := ihc ht.1 η
    cases u with
    | false =>
      obtain ⟨w, hw⟩ := ihe ht.2.2 η
      simp [dtC, bindT, SPTree.Timed.delay, hu, hw, SPTree.Timed.bind]
    | true =>
      obtain ⟨w, hw⟩ := iht ht.2.1 η
      simp [dtC, bindT, SPTree.Timed.delay, hu, hw, SPTree.Timed.bind]
  | nil => intro _ η; exact ⟨_, rfl⟩
  | cons x xs ihx ihxs =>
    intro ht η
    obtain ⟨u, hu⟩ := ihx ht.1 η
    obtain ⟨w, hw⟩ := ihxs ht.2 η
    simp only [dtC, bindT, SPTree.Timed.delay, hu, hw, SPTree.Timed.bind]
    exact ⟨_, rfl⟩
  | lcase xs n c ihxs ihn ihc =>
    intro ht η
    obtain ⟨u, hu⟩ := ihxs ht.1 η
    cases u with
    | nil =>
      obtain ⟨w, hw⟩ := ihn ht.2.1 η
      simp [dtC, bindT, SPTree.Timed.delay, hu, hw, SPTree.Timed.bind]
    | cons x l =>
      obtain ⟨w, hw⟩ := ihc ht.2.2 ((η.cons (σ := .list _) l).cons x)
      simp [dtC, bindT, SPTree.Timed.delay, hu, hw, SPTree.Timed.bind]
  | foldl f i xs ihf ihi ihxs =>
    intro ht η
    obtain ⟨p, hp⟩ := ihf ht.1 η
    obtain ⟨u, hu⟩ := ihi ht.2.1 η
    obtain ⟨w, hw⟩ := ihxs ht.2.2 η
    simp [dtC, bindT, SPTree.Timed.delay, hp, hu, hw, SPTree.Timed.bind]
  | iter n f i ihn ihf ihi =>
    intro ht η
    obtain ⟨k, hk⟩ := ihn ht.1 η
    obtain ⟨p, hp⟩ := ihf ht.2.1 η
    obtain ⟨u, hu⟩ := ihi ht.2.2 η
    simp [dtC, bindT, SPTree.Timed.delay, hk, hp, hu, SPTree.Timed.bind]
  | sample f => intro ht; simp [Pure] at ht
  | get n f => intro ht; simp [Pure] at ht
  | set n f x ih => intro ht; simp [Pure] at ht
  | query d r x ih => intro ht; simp [Pure] at ht
  | fail => intro ht; simp [Pure] at ht

/-- The fragment of the soundness theorem: variables of a type other than a function type,
calls of a function variable or of a pure costed closure, abstractions with a pure body,
`letE`, `seq`, literals, operations of unit cost, pairs and projections, sums and `case`, lists
and `lcase`, `ite`, `foldl` and `iter`, `sample`, `get`, `set`, `query` and `fail`. -/
def InDtFrag : {Γ : List Ty} → {τ : Ty} → Tm Γ τ → Prop
  | _, τ, .var _ => τ.isArr = false
  | _, _, .lam b => b.InDtFrag ∧ b.Pure
  | _, _, .app f x => (f.headVar?.isSome = true ∨ f.InDtFrag) ∧ x.InDtFrag
  | _, _, .letE e b => e.InDtFrag ∧ b.InDtFrag
  | _, _, .seq e b => e.InDtFrag ∧ b.InDtFrag
  | _, _, .natLit _ => True
  | _, _, .lit _ _ => True
  | _, _, .prim p x => p.unitCost = true ∧ x.InDtFrag
  | _, _, .pair x y => x.InDtFrag ∧ y.InDtFrag
  | _, _, .fst p => p.InDtFrag
  | _, _, .snd p => p.InDtFrag
  | _, _, .inl x => x.InDtFrag
  | _, _, .inr x => x.InDtFrag
  | _, _, .case s l r => s.InDtFrag ∧ l.InDtFrag ∧ r.InDtFrag
  | _, _, .ite c t e => c.InDtFrag ∧ t.InDtFrag ∧ e.InDtFrag
  | _, _, .nil => True
  | _, _, .cons x xs => x.InDtFrag ∧ xs.InDtFrag
  | _, _, .lcase xs n c => xs.InDtFrag ∧ n.InDtFrag ∧ c.InDtFrag
  | _, _, .foldl f i xs => f.InDtFrag ∧ i.InDtFrag ∧ xs.InDtFrag
  | _, _, .iter n f i => n.InDtFrag ∧ f.InDtFrag ∧ i.InDtFrag
  | _, _, .sample _ => True
  | _, _, .get _ _ => True
  | _, _, .set _ _ x => x.InDtFrag
  | _, _, .query _ _ x => x.InDtFrag
  | _, _, .fail => True

/-- A left fold of D with a step related to a pure costed closure, from related accumulators
over related lists, is a leaf after at most the registered cost of `List.foldl` in ticks, at a
value related to the fold of the closure. -/
theorem foldT_sim {a c : Ty} {p : Ty.hat (.arr (.prod c a) c)} {g : Val (.arr (.prod c a) c)}
    (hg : Sim (.arr (.prod c a) c) p g) {l : List a.hat} {l' : List (Val a)}
    (hl : List.Forall₂ (Sim a) l l') : ∀ {acc : c.hat} {v : Val c}, Sim c acc v →
    ∃ m w, foldT CTree.tick g v l' = stepN CTree.tick m (.ret w) ∧
      m ≤ List.foldl.timedCost (fun x y => p.1 (x, y)) (fun x y => p.2 (x, y)) acc l ∧
      Sim c (List.foldl (fun x y => p.1 (x, y)) acc l) w := by
  induction hl with
  | nil => intro acc v h; exact ⟨0, v, rfl, Nat.zero_le _, h⟩
  | @cons x x' l l' hx _ ih =>
    intro acc v h
    obtain ⟨m₁, w₁, h₁, hm₁, hw₁⟩ := hg (acc, x) (v, x') ⟨h, hx⟩
    obtain ⟨m₂, w₂, h₂, hm₂, hw₂⟩ := ih hw₁
    refine ⟨m₁ + m₂ + 1, w₂, ?_, ?_, hw₂⟩
    · have hf : foldT CTree.tick g v (x' :: l') =
          CTree.tick ((g (v, x')).bind fun acc' => foldT CTree.tick g acc' l') := rfl
      rw [hf, h₁, Reflect.stepN_ret_bind, h₂, Reflect.stepN_tick_add]
      rfl
    · simp [List.foldl.timedCost]
      omega

/-- An iteration of D with a step related to a pure costed closure, from related accumulators,
is a leaf after at most `iterCost` in ticks, at a value related to the iterate of the
closure. -/
theorem iterT_sim {c : Ty} {p : Ty.hat (.arr c c)} {g : Val (.arr c c)}
    (hg : Sim (.arr c c) p g) (k : ℕ) : ∀ {acc : c.hat} {v : Val c}, Sim c acc v →
    ∃ m w, iterT CTree.tick g v k = stepN CTree.tick m (.ret w) ∧ m ≤ iterCost p acc k ∧
      Sim c (p.1^[k] acc) w := by
  induction k with
  | zero => intro acc v h; exact ⟨0, v, rfl, Nat.zero_le _, h⟩
  | succ k ih =>
    intro acc v h
    obtain ⟨m₁, w₁, h₁, hm₁, hw₁⟩ := hg acc v h
    obtain ⟨m₂, w₂, h₂, hm₂, hw₂⟩ := ih hw₁
    refine ⟨m₁ + m₂ + 1, w₂, ?_, ?_, hw₂⟩
    · have hf : iterT CTree.tick g v (k + 1) =
          CTree.tick ((g v).bind fun acc' => iterT CTree.tick g acc' k) := rfl
      rw [hf, h₁, Reflect.stepN_ret_bind, h₂, Reflect.stepN_tick_add]
      rfl
    · simp only [iterCost]
      omega

/-! ## Soundness -/

/-- Soundness of the charges on D at any charge `cc a ≤ 1` of a call: in related environments,
the evaluation of a term of the fragment is simulated by its costed tree `t.dtC cc η` at factor
`1` and allowance `t.allowC cc`. The β-step of a call is paid by its charge `cc a` and by the
allowance `1 - cc a`. -/
theorem dtC_timedSim (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) :
    ∀ {Γ : List Ty} {τ : Ty} (t : Tm Γ τ), t.InDtFrag → ∀ {η : EnvHat Γ} {ρ : Env Γ},
      SimEnv η ρ → TimedSim (Sim τ) 1 (t.allowC cc) (t.dtC cc η) (t.eval ρ) := by
  intro Γ τ t
  induction t with
  | var x => intro ht η ρ hρ; exact SimE.read _ ht (hρ _ x)
  | @lam _ a b body ih =>
    intro ht η ρ hρ
    refine TimedSim.ret fun u v huv => ?_
    obtain ⟨w₀, hw₀⟩ := dtC_pure cc body ht.2 (η.cons u)
    obtain ⟨m, w, he, hm, hw⟩ := TimedSim.ret_inv hw₀ (ih ht.1 (hρ.cons huv))
    refine ⟨m, w, he, ?_, ?_⟩
    · simpa using hm
    · change Sim b (b.pureVal (body.dtC cc (η.cons u)).2) w
      rw [hw₀]
      exact hw
  | @app _ a b f x ihf ihx =>
    intro ht η ρ hρ
    cases hv : f.headVar? with
    | some y =>
      obtain rfl := eq_var_of_headVar? hv
      have hev : (Tm.app (.var y) x).eval ρ = (x.eval ρ).bind fun v => .tick (ρ _ y v) := rfl
      have hdt : (Tm.app (.var y) x).dtC cc η =
          bindT (x.dtC cc η) fun u => SPTree.Timed.delay (cc a) (η _ y u) := by
        simp [dtC, headVar?]
      rw [hev, hdt]
      refine (TimedSim.bindCont (m := 1 - cc a) (ihx ht.2 hρ) fun u v huv => ?_).mono
        (by simp only [allowC]; omega)
      have h0 : TimedSim (Sim b) 1 0 (η _ y u) (ρ _ y v) := hρ _ y u v huv
      have hc := hcc a
      exact (TimedSim.delay_tick_le (m := 1 - cc a) h0 (by omega)).mono (by omega)
    | none =>
      have hf : f.InDtFrag := by simpa [hv] using ht.1
      have hev : (Tm.app f x).eval ρ =
          (f.eval ρ).bind fun g => (x.eval ρ).bind fun v => .tick (g v) := rfl
      have hdt : (Tm.app f x).dtC cc η = bindT (f.dtC cc η) fun p =>
          bindT (x.dtC cc η) fun u => (1 + p.2 u, .ret (p.1 u)) := by
        simp [dtC, hv]
      rw [hev, hdt]
      refine (TimedSim.bindCont (m := x.allowC cc + 0) (ihf hf hρ) fun p g hpg =>
        TimedSim.bindCont (ihx ht.2 hρ) fun u v huv => ?_).mono (by simp only [allowC]; omega)
      obtain ⟨m, w, hg, hm, hw⟩ := hpg u v huv
      rw [hg]
      exact TimedSim.stepN_ret (m := m + 1) hw (by omega)
  | letE e b ihe ihb =>
    intro ht η ρ hρ
    rw [Tm.eval_letE]
    exact (TimedSim.bind (m := b.allowC cc + 1) (ihe ht.1 hρ) fun u v huv =>
      TimedSimTree.tick (ihb ht.2 (hρ.cons huv)) (by omega)).mono (by simp only [allowC]; omega)
  | seq e b ihe ihb =>
    intro ht η ρ hρ
    have hev : (Tm.seq e b).eval ρ = (e.eval ρ).bind fun _ => .tick (b.eval ρ) := rfl
    rw [hev]
    exact (TimedSim.bind (m := b.allowC cc + 1) (ihe ht.1 hρ) fun u v huv =>
      TimedSimTree.tick (ihb ht.2 hρ) (by omega)).mono (by simp only [allowC]; omega)
  | natLit n => intro _ η ρ _; exact TimedSim.ret rfl
  | lit f v => intro _ η ρ _; exact TimedSim.ret rfl
  | @prim _ a b p x ih =>
    intro ht η ρ hρ
    have hev : (Tm.prim p x).eval ρ =
        (x.eval ρ).bind fun v => stepN CTree.tick (p.cost v) (.ret (p.apply v)) := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := 0) (ih ht.2 hρ) fun u v huv => ?_).mono
      (by simp only [allowC]; omega)
    rw [p.cost_eq_one_of_unitCost ht.1 v]
    refine TimedSim.stepN_ret ?_ (by omega)
    rw [Sim.toVal_eq _ p.fo.1 huv]
    exact Sim.ofVal _ p.fo.2 _
  | @pair _ a b x y ihx ihy =>
    intro ht η ρ hρ
    have hev : (Tm.pair x y).eval ρ =
        (x.eval ρ).bind fun u => (y.eval ρ).bind fun v => .ret ((u, v) : Val a × Val b) := rfl
    rw [hev]
    exact (TimedSim.bindCont (ihx ht.1 hρ) fun _ _ huv => TimedSim.bindCont (m := 0)
      (ihy ht.2 hρ) fun _ _ huv' => TimedSim.ret ⟨huv, huv'⟩).mono (by simp only [allowC]; omega)
  | @fst _ a b p ih =>
    intro ht η ρ hρ
    have hev : (Tm.fst p).eval ρ = (p.eval ρ).bind fun (v : Val a × Val b) => .ret v.1 := rfl
    rw [hev]
    exact (TimedSim.bindCont (m := 0) (ih ht hρ) fun _ _ huv => TimedSim.ret huv.1).mono
      (by simp only [allowC]; omega)
  | @snd _ a b p ih =>
    intro ht η ρ hρ
    have hev : (Tm.snd p).eval ρ = (p.eval ρ).bind fun (v : Val a × Val b) => .ret v.2 := rfl
    rw [hev]
    exact (TimedSim.bindCont (m := 0) (ih ht hρ) fun _ _ huv => TimedSim.ret huv.2).mono
      (by simp only [allowC]; omega)
  | @inl _ a b x ih =>
    intro ht η ρ hρ
    have hev : (Tm.inl (b := b) x).eval ρ =
        (x.eval ρ).bind fun v => .ret (Sum.inl v : Val a ⊕ Val b) := rfl
    rw [hev]
    exact (TimedSim.bindCont (m := 0) (ih ht hρ) fun _ _ huv =>
      TimedSim.ret (Sum.LiftRel.inl huv)).mono (by simp only [allowC]; omega)
  | @inr _ a b x ih =>
    intro ht η ρ hρ
    have hev : (Tm.inr (a := a) x).eval ρ =
        (x.eval ρ).bind fun v => .ret (Sum.inr v : Val a ⊕ Val b) := rfl
    rw [hev]
    exact (TimedSim.bindCont (m := 0) (ih ht hρ) fun _ _ huv =>
      TimedSim.ret (Sum.LiftRel.inr huv)).mono (by simp only [allowC]; omega)
  | @case _ a b c s l r ihs ihl ihr =>
    intro ht η ρ hρ
    have hev : (Tm.case s l r).eval ρ = (s.eval ρ).bind fun (v : Val a ⊕ Val b) =>
        .tick (Sum.elim (fun x => l.eval (ρ.cons x)) (fun y => r.eval (ρ.cons y)) v) := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := max (l.allowC cc) (r.allowC cc) + 0) (ihs ht.1 hρ)
      fun u v huv => ?_).mono (by simp only [allowC]; omega)
    refine TimedSim.delay_tick_le ?_ (by omega)
    cases huv with
    | inl h => exact (ihl ht.2.1 (hρ.cons h)).mono (by omega)
    | inr h => exact (ihr ht.2.2 (hρ.cons h)).mono (by omega)
  | ite c t e ihc iht ihe =>
    intro ht η ρ hρ
    have hev : (Tm.ite c t e).eval ρ =
        (c.eval ρ).bind fun (b : Bool) => .tick (bif b then t.eval ρ else e.eval ρ) := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := max (t.allowC cc) (e.allowC cc) + 0) (ihc ht.1 hρ)
      fun b b' hb => ?_).mono (by simp only [allowC]; omega)
    have hb' : b = b' := hb
    subst hb'
    refine TimedSim.delay_tick_le ?_ (by omega)
    cases b
    · exact (ihe ht.2.2 hρ).mono (by omega)
    · exact (iht ht.2.1 hρ).mono (by omega)
  | nil => intro _ η ρ _; exact TimedSim.ret List.Forall₂.nil
  | @cons _ a x xs ihx ihxs =>
    intro ht η ρ hρ
    have hev : (Tm.cons x xs).eval ρ = (x.eval ρ).bind fun v =>
        (xs.eval ρ).bind fun (l : List (Val a)) => .ret (v :: l) := rfl
    rw [hev]
    exact (TimedSim.bindCont (ihx ht.1 hρ) fun _ _ huv => TimedSim.bindCont (m := 0)
      (ihxs ht.2 hρ) fun _ _ huv' => TimedSim.ret (List.Forall₂.cons huv huv')).mono
      (by simp only [allowC]; omega)
  | @lcase _ a c xs n cb ihxs ihn ihc =>
    intro ht η ρ hρ
    have hev : (Tm.lcase xs n cb).eval ρ = (xs.eval ρ).bind fun (l : List (Val a)) =>
        .tick (listCase l (n.eval ρ) fun x l' =>
          cb.eval ((ρ.cons (τ := .list a) l').cons x)) := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := max (n.allowC cc) (cb.allowC cc) + 0) (ihxs ht.1 hρ)
      fun u v huv => ?_).mono (by simp only [allowC]; omega)
    refine TimedSim.delay_tick_le ?_ (by omega)
    cases huv with
    | nil => exact (ihn ht.2.1 hρ).mono (by omega)
    | cons hx hl => exact (ihc ht.2.2 ((hρ.cons (σ := .list a) hl).cons hx)).mono (by omega)
  | @foldl _ a c f i xs ihf ihi ihxs =>
    intro ht η ρ hρ
    have hev : (Tm.foldl f i xs).eval ρ = (f.eval ρ).bind fun g => (i.eval ρ).bind fun acc =>
        (xs.eval ρ).bind fun l => foldT CTree.tick g acc l := rfl
    rw [hev]
    refine (TimedSim.bindCont (ihf ht.1 hρ) fun p g hpg =>
      TimedSim.bindCont (ihi ht.2.1 hρ) fun acc v hacc =>
      TimedSim.bindCont (m := 0) (ihxs ht.2.2 hρ) fun l l' hl => ?_).mono
      (by simp only [allowC]; omega)
    obtain ⟨m, w, he, hm, hw⟩ := foldT_sim hpg hl hacc
    rw [he]
    exact TimedSim.stepN_ret hw (by omega)
  | @iter _ c n f i ihn ihf ihi =>
    intro ht η ρ hρ
    have hev : (Tm.iter n f i).eval ρ = (n.eval ρ).bind fun (k : ℕ) => (f.eval ρ).bind fun g =>
        (i.eval ρ).bind fun acc => iterT CTree.tick g acc k := rfl
    rw [hev]
    refine (TimedSim.bindCont (ihn ht.1 hρ) fun k k' hk =>
      TimedSim.bindCont (ihf ht.2.1 hρ) fun p g hpg =>
      TimedSim.bindCont (m := 0) (ihi ht.2.2 hρ) fun acc v hacc => ?_).mono
      (by simp only [allowC]; omega)
    have hk' : k = k' := hk
    subst hk'
    obtain ⟨m, w, he, hm, hw⟩ := iterT_sim hpg k hacc
    rw [he]
    exact TimedSim.stepN_ret hw (by omega)
  | sample f =>
    intro _ η ρ _
    exact TimedSim.sample le_rfl f (Equiv.refl _) fun _ => TimedSim.ret rfl
  | get n f => intro _ η ρ _; exact TimedSim.get le_rfl n f fun _ => TimedSim.ret rfl
  | set n f x ih =>
    intro ht η ρ hρ
    have hev : (Tm.set n f x).eval ρ =
        (x.eval ρ).bind fun v => .set n f v (.ret (() : Unit)) := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := 0) (ih ht hρ) fun u v huv => ?_).mono
      (by simp only [allowC]; omega)
    have h' : u = v := huv
    subst h'
    exact TimedSim.set le_rfl n f u (TimedSim.ret rfl)
  | query d r x ih =>
    intro ht η ρ hρ
    have hev : (Tm.query d r x).eval ρ = (x.eval ρ).bind fun v => .query d r v .ret := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := 0) (ih ht hρ) fun _ v _ => ?_).mono
      (by simp only [allowC]; omega)
    exact TimedSim.query le_rfl d r v fun _ => TimedSim.ret rfl
  | fail => intro _ η ρ _; exact TimedSim.fail

/-- Soundness of the charges of `derive_timed` on D: in related environments, the evaluation of
a term of the fragment is simulated by its costed tree at factor `1` and allowance
`t.allow`. -/
theorem dt_timedSim {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) (ht : t.InDtFrag) {η : EnvHat Γ}
    {ρ : Env Γ} (hρ : SimEnv η ρ) : TimedSim (Sim τ) 1 t.allow (t.dt η) (t.eval ρ) :=
  dtC_timedSim callCost callCost_le_one t ht hρ

/-- The cost of a term of the fragment is at most its allowance plus the time of its costed
tree. -/
theorem cost_le_dt (t : Tm Γ τ) (ht : t.InDtFrag) {η : EnvHat Γ} {ρ : Env Γ}
    (hρ : SimEnv η ρ) : t.cost ρ ≤ t.allow + SPTree.Timed.stepTime (t.dt η) := by
  have h := (dt_timedSim t ht hρ).cost_le
  rw [Nat.one_mul] at h
  exact h

/-- At a first-order term of the fragment whose evaluation is query-free, the evaluation means
the compiled erasure of its costed tree, read back as values of D. -/
theorem dt_run (O : CTree.Oracle) (t : Tm Γ τ) (ht : t.InDtFrag) (hτ : τ.FO)
    {η : EnvHat Γ} {ρ : Env Γ} (hρ : SimEnv η ρ) (hq : (t.eval ρ).QueryFree) :
    (t.eval ρ).run O =
      SPComp.bind (t.dt η).2.erase.compile fun a => SPComp.pure (τ.toVal hτ a) :=
  TimedSim.run ((dt_timedSim t ht hρ).rel_mono fun _ _ h => Sim.toVal_eq τ hτ h) hq O

/-- At a first-order term of the fragment over a first-order context whose evaluation is
query-free, the compiled erasure of its costed tree, read back as values of D, is the
denotation. -/
theorem dt_erase (O : CTree.Oracle) (t : Tm Γ τ) (ht : t.InDtFrag) (hτ : τ.FO)
    (hΓ : ∀ σ ∈ Γ, σ.FO) {η : EnvHat Γ} {ρ : Env Γ} (hρ : SimEnv η ρ)
    (hq : (t.eval ρ).QueryFree) :
    SPComp.bind (t.dt η).2.erase.compile (fun a => SPComp.pure (τ.toVal hτ a)) =
      t.denote O ρ := by
  rw [← t.run_eval O hτ hΓ ρ, dt_run O t ht hτ hρ hq]

end Tm

end CatCrypt.Complexity.D
