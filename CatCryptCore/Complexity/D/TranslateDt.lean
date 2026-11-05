/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Translate
public import CatCryptCore.Complexity.D.TimedLink

/-!
# The charges of `derive_timed` on D terms, with one soundness theorem

`Tm.dt t η` (`η` a translated environment) is the costed tree that `derive_timed` assigns to
the source of a D term `t`, stated on the syntax of D: a `let` and a `seq` are free, a call
costs one plus the callee and the argument (a call on `unit` costs the callee and the
argument), a conditional costs one plus the condition and the branch taken, constructors,
projections, literals and variables are free, an operation on words or `Bool` costs one, and
a `sample`, `get`, `set` or `query` node costs its unit. `Tm.allow t` counts on the syntax the
β-steps of D that these charges leave out: one per `letE` and `seq`, one per call on `unit`.
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
path. Its corollaries are the cost bound `Tm.cost_le_dt` and the meaning of the erasure
`Tm.dt_run`, `Tm.dt_erase`.

The fragment is the one of `link_timed`: variables of a type other than a function type, calls
of function variables and of pure costed closures, `letE`, `seq`, literals, pairs and
projections, `ite`, operations of unit cost (on words and `Bool`), `sample`, `get`, `set`,
`query` and `fail`. Operations on `ℕ` and on `Fin (n + 1)`, abstractions, sums, lists, `case`,
`lcase`, `foldl` and `iter` are outside it.

## Main definitions

* `Ty.hat`, `Ty.hatE`, `Sim`, `SimE`, `EnvHat`, `SimEnv`
* `Tm.dt`, `Tm.allow`, `Tm.InDtFrag`

## Main results

* `TimedSimTree.bindCont`, `TimedSim.bindCont`: the costed bind against a D bind under any
  continuation.
* `Tm.dt_timedSim`, `Tm.cost_le_dt`, `Tm.dt_run`, `Tm.dt_erase`
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

/-! ## The charges on D syntax -/

/-- The charge of a call on an argument of type `a`: one, and none on `unit`. -/
def callCost (a : Ty) : ℕ := if a = .unit then 0 else 1

/-- The charge of a call is at most one. -/
theorem callCost_le_one (a : Ty) : callCost a ≤ 1 := by
  unfold callCost; split <;> omega

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

/-- The costed tree of the charges of `derive_timed` for a term; outside the fragment
`InDtFrag` it is `fail`. -/
noncomputable def dt : {Γ : List Ty} → {τ : Ty} → Tm Γ τ → EnvHat Γ → ℕ × SPTree.Timed τ.hat
  | _, τ, .var x, η => τ.read (η τ x)
  | _, _, .app (a := a) f x, η =>
    match f.headVar? with
    | some y => bindT (x.dt η) fun u => SPTree.Timed.delay (callCost a) (η _ y u)
    | none => bindT (f.dt η) fun p => bindT (x.dt η) fun u => (1 + p.2 u, .ret (p.1 u))
  | _, _, .letE e b, η => bindT (e.dt η) fun u => b.dt (η.cons u)
  | _, _, .seq e b, η => bindT (e.dt η) fun _ => b.dt η
  | _, _, .natLit n, _ => (0, .ret n)
  | _, _, .lit _ v, _ => (0, .ret v)
  | _, _, .prim p x, η => bindT (x.dt η) fun u => (1, .ret (p.applyHat u))
  | _, _, .pair x y, η => bindT (x.dt η) fun u => bindT (y.dt η) fun w => (0, .ret (u, w))
  | _, _, .fst p, η => bindT (p.dt η) fun u => (0, .ret u.1)
  | _, _, .snd p, η => bindT (p.dt η) fun u => (0, .ret u.2)
  | _, _, .ite c t e, η =>
    bindT (c.dt η) fun (b : Bool) => SPTree.Timed.delay 1 (bif b then t.dt η else e.dt η)
  | _, _, .sample f, _ =>
    (0, .sample f.den (FTy.instFintype f) (FTy.instNonempty f) (fun _ => 0) fun v => .ret v)
  | _, _, .get n f, _ => (0, .get (f.loc n) (fun _ => 0) fun v => .ret v)
  | _, _, .set n f x, η => bindT (x.dt η) fun u => (0, .set (f.loc n) u 0 (.ret ()))
  | _, _, .query _ r x, η => bindT (x.dt η) fun _ =>
    (0, .sample r.den (FTy.instFintype r) (FTy.instNonempty r) (fun _ => 0) fun v => .ret v)
  | _, _, .fail, _ => (0, .fail)
  | _, _, _, _ => (0, .fail)

/-- The allowance of a term: the β-steps of D that the charges of `derive_timed` leave out, one
per `letE` and `seq` and one per call on `unit`. -/
def allow : {Γ : List Ty} → {τ : Ty} → Tm Γ τ → ℕ
  | _, _, .app (a := a) f x => f.allow + x.allow + (1 - callCost a)
  | _, _, .letE e b => e.allow + b.allow + 1
  | _, _, .seq e b => e.allow + b.allow + 1
  | _, _, .prim _ x => x.allow
  | _, _, .pair x y => x.allow + y.allow
  | _, _, .fst p => p.allow
  | _, _, .snd p => p.allow
  | _, _, .ite c t e => c.allow + max t.allow e.allow
  | _, _, .set _ _ x => x.allow
  | _, _, .query _ _ x => x.allow
  | _, _, _ => 0

/-- The fragment of the soundness theorem: variables of a type other than a function type,
calls of a function variable or of a pure costed closure, `letE`, `seq`, literals, operations
of unit cost, pairs and projections, `ite`, `sample`, `get`, `set`, `query` and `fail`. -/
def InDtFrag : {Γ : List Ty} → {τ : Ty} → Tm Γ τ → Prop
  | _, τ, .var _ => τ.isArr = false
  | _, _, .app f x => (f.headVar?.isSome = true ∨ f.InDtFrag) ∧ x.InDtFrag
  | _, _, .letE e b => e.InDtFrag ∧ b.InDtFrag
  | _, _, .seq e b => e.InDtFrag ∧ b.InDtFrag
  | _, _, .natLit _ => True
  | _, _, .lit _ _ => True
  | _, _, .prim p x => p.unitCost = true ∧ x.InDtFrag
  | _, _, .pair x y => x.InDtFrag ∧ y.InDtFrag
  | _, _, .fst p => p.InDtFrag
  | _, _, .snd p => p.InDtFrag
  | _, _, .ite c t e => c.InDtFrag ∧ t.InDtFrag ∧ e.InDtFrag
  | _, _, .sample _ => True
  | _, _, .get _ _ => True
  | _, _, .set _ _ x => x.InDtFrag
  | _, _, .query _ _ x => x.InDtFrag
  | _, _, .fail => True
  | _, _, _ => False

/-! ## Soundness -/

/-- Soundness of the charges of `derive_timed` on D: in related environments, the evaluation of
a term of the fragment is simulated by its costed tree at factor `1` and allowance
`t.allow`. -/
theorem dt_timedSim : ∀ {Γ : List Ty} {τ : Ty} (t : Tm Γ τ), t.InDtFrag →
    ∀ {η : EnvHat Γ} {ρ : Env Γ}, SimEnv η ρ → TimedSim (Sim τ) 1 t.allow (t.dt η) (t.eval ρ) := by
  intro Γ τ t
  induction t with
  | var x => intro ht η ρ hρ; exact SimE.read _ ht (hρ _ x)
  | lam b ih => intro ht; simp [InDtFrag] at ht
  | @app _ a b f x ihf ihx =>
    intro ht η ρ hρ
    cases hv : f.headVar? with
    | some y =>
      obtain rfl := eq_var_of_headVar? hv
      have hev : (Tm.app (.var y) x).eval ρ = (x.eval ρ).bind fun v => .tick (ρ _ y v) := rfl
      have hdt : (Tm.app (.var y) x).dt η =
          bindT (x.dt η) fun u => SPTree.Timed.delay (callCost a) (η _ y u) := by
        simp [dt, headVar?]
      rw [hev, hdt]
      refine (TimedSim.bindCont (m := 1 - callCost a) (ihx ht.2 hρ) fun u v huv => ?_).mono
        (by simp only [allow]; omega)
      have h0 : TimedSim (Sim b) 1 0 (η _ y u) (ρ _ y v) := hρ _ y u v huv
      have hc := callCost_le_one a
      exact (TimedSim.delay_tick_le (m := 1 - callCost a) h0 (by omega)).mono (by omega)
    | none =>
      have hf : f.InDtFrag := by simpa [hv] using ht.1
      have hev : (Tm.app f x).eval ρ =
          (f.eval ρ).bind fun g => (x.eval ρ).bind fun v => .tick (g v) := rfl
      have hdt : (Tm.app f x).dt η = bindT (f.dt η) fun p =>
          bindT (x.dt η) fun u => (1 + p.2 u, .ret (p.1 u)) := by
        simp [dt, hv]
      rw [hev, hdt]
      refine (TimedSim.bindCont (m := x.allow + 0) (ihf hf hρ) fun p g hpg =>
        TimedSim.bindCont (ihx ht.2 hρ) fun u v huv => ?_).mono (by simp only [allow]; omega)
      obtain ⟨m, w, hg, hm, hw⟩ := hpg u v huv
      rw [hg]
      exact TimedSim.stepN_ret (m := m + 1) hw (by omega)
  | letE e b ihe ihb =>
    intro ht η ρ hρ
    rw [Tm.eval_letE]
    exact (TimedSim.bind (m := b.allow + 1) (ihe ht.1 hρ) fun u v huv =>
      TimedSimTree.tick (ihb ht.2 (hρ.cons huv)) (by omega)).mono (by simp only [allow]; omega)
  | seq e b ihe ihb =>
    intro ht η ρ hρ
    have hev : (Tm.seq e b).eval ρ = (e.eval ρ).bind fun _ => .tick (b.eval ρ) := rfl
    rw [hev]
    exact (TimedSim.bind (m := b.allow + 1) (ihe ht.1 hρ) fun u v huv =>
      TimedSimTree.tick (ihb ht.2 hρ) (by omega)).mono (by simp only [allow]; omega)
  | natLit n => intro _ η ρ _; exact TimedSim.ret rfl
  | lit f v => intro _ η ρ _; exact TimedSim.ret rfl
  | @prim _ a b p x ih =>
    intro ht η ρ hρ
    have hev : (Tm.prim p x).eval ρ =
        (x.eval ρ).bind fun v => stepN CTree.tick (p.cost v) (.ret (p.apply v)) := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := 0) (ih ht.2 hρ) fun u v huv => ?_).mono
      (by simp only [allow]; omega)
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
      (ihy ht.2 hρ) fun _ _ huv' => TimedSim.ret ⟨huv, huv'⟩).mono (by simp only [allow]; omega)
  | @fst _ a b p ih =>
    intro ht η ρ hρ
    have hev : (Tm.fst p).eval ρ = (p.eval ρ).bind fun (v : Val a × Val b) => .ret v.1 := rfl
    rw [hev]
    exact (TimedSim.bindCont (m := 0) (ih ht hρ) fun _ _ huv => TimedSim.ret huv.1).mono
      (by simp only [allow]; omega)
  | @snd _ a b p ih =>
    intro ht η ρ hρ
    have hev : (Tm.snd p).eval ρ = (p.eval ρ).bind fun (v : Val a × Val b) => .ret v.2 := rfl
    rw [hev]
    exact (TimedSim.bindCont (m := 0) (ih ht hρ) fun _ _ huv => TimedSim.ret huv.2).mono
      (by simp only [allow]; omega)
  | inl x ih => intro ht; simp [InDtFrag] at ht
  | inr x ih => intro ht; simp [InDtFrag] at ht
  | case s l r ihs ihl ihr => intro ht; simp [InDtFrag] at ht
  | ite c t e ihc iht ihe =>
    intro ht η ρ hρ
    have hev : (Tm.ite c t e).eval ρ =
        (c.eval ρ).bind fun (b : Bool) => .tick (bif b then t.eval ρ else e.eval ρ) := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := max t.allow e.allow + 0) (ihc ht.1 hρ)
      fun b b' hb => ?_).mono (by simp only [allow]; omega)
    have hb' : b = b' := hb
    subst hb'
    refine TimedSim.delay_tick_le ?_ (by omega)
    cases b
    · exact (ihe ht.2.2 hρ).mono (by omega)
    · exact (iht ht.2.1 hρ).mono (by omega)
  | nil => intro ht; simp [InDtFrag] at ht
  | cons x xs ihx ihxs => intro ht; simp [InDtFrag] at ht
  | lcase xs n c ihxs ihn ihc => intro ht; simp [InDtFrag] at ht
  | foldl f i xs ihf ihi ihxs => intro ht; simp [InDtFrag] at ht
  | iter n f i ihn ihf ihi => intro ht; simp [InDtFrag] at ht
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
      (by simp only [allow]; omega)
    have h' : u = v := huv
    subst h'
    exact TimedSim.set le_rfl n f u (TimedSim.ret rfl)
  | query d r x ih =>
    intro ht η ρ hρ
    have hev : (Tm.query d r x).eval ρ = (x.eval ρ).bind fun v => .query d r v .ret := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := 0) (ih ht hρ) fun _ v _ => ?_).mono
      (by simp only [allow]; omega)
    exact TimedSim.query le_rfl d r v fun _ => TimedSim.ret rfl
  | fail => intro _ η ρ _; exact TimedSim.fail

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
