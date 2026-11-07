/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Translate
public import CatCryptCore.Complexity.D.TimedLink
public import CatCryptCore.Tactics.StdCosts
public import CatCryptCore.Container.DillerNahm

/-!
# The charges of `derive_timed` on D terms, with one soundness theorem

`Tm.dt t η` (`η` a translated environment) is the costed tree that `derive_timed` assigns to
the source of a D term `t`, stated on the syntax of D: a `let` and a `seq` are free, a call
costs one plus the callee and the argument (a call on `unit` costs the callee and the
argument), a conditional and a match on a sum or a list cost one plus the scrutinee and the
branch taken, constructors, projections, literals, variables and abstractions are free, an
operation on words or `Bool` costs one, a left fold costs the registered cost
`List.foldl.timedCost` of its step closure, an iteration one plus the step per round
(`iterCost`), a constructor `con` nothing, its children being a table (`conHat`), as
`derive_timed` charges a constructor, an eliminator `fold` one plus
the cost of the step function of the root, a recursive result one plus the cost of the step
function at the child each time the step applies it (`foldHat`, `stepHat`), a table `ptab` the
sum of the charges of its components (`tabCost`), a read `papp` and a pair `spair` nothing, a
case analysis `scase` on a dependent pair or `fcase` on a finite ground value one plus the
scrutinee and the branch taken, and a `sample`, `get`, `set` or `query` node costs its unit. `Tm.allow t` counts
on the syntax the β-steps of D that these charges leave out: one per `letE` and `seq`, one per
call on `unit`.
This is the cost model of the call-by-value λ-calculus of Forster and Kunze (*A Certifying
Extraction with Time Bounds from Coq to Call-By-Value Lambda Calculus*, ITP 2019), with the
charges of `derive_timed`.

Values are translated by `Ty.hat`, by recursion on the code: a first-order type to its values,
an inductive type to the W-type of its constructors with their translated fields (`Sig.hatF`),
so that a field may hold a pure costed closure, a function type to a pure costed closure, a
function and its cost, the costed function `Container.Costed` of the Diller–Nahm model (whose
morphism is `Container.Costed.toDN`), a dependent product `pi f B` to the table of the translated components, a dependent
sum `sig f B` to the dependent pair of an index and a translated value of `B j`. An environment `EnvHat Γ` gives a variable of function
type a costed tree for each argument (`Ty.hatE`), so that a function variable is an effectful
parameter, as in the telescope of `link_timed`. `Sim` relates translated values and values of
D (the step equation of a data function at function types), `SimE` an environment entry and a
value (`TimedSim` at allowance `0` for a function variable); at an inductive type `Sim` is the
lifting `Container.WLift` of `Sim` at the fields over the W-type: two nodes of one constructor with
related fields and related children.

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
`lcase`, `ite`, `foldl` and `iter` with a step that is a pure costed closure, `con`, `fold` with
step functions that are pure costed closures, `ptab` with pure
components (a table is built from data, as an abstraction with a pure body), `papp`, `spair`,
`scase` and `fcase`, operations of unit cost (on words and `Bool`), `sample`, `get`, `set`,
`query` and `fail`. Operations on `ℕ` and on
`Fin (n + 1)` are outside it.

## Main definitions

* `Ty.hat`, `Sig.hatF`, `ISig.hatF`, `Ty.hatE`, `Sim`, `Sig.SimF`, `ISig.SimF`, `SimE`,
  `EnvHat`, `SimEnv` (the maps `Container.wmapF`, `Container.iwmapF` of the fields of W-types are
  in `CatCryptCore/Container/WTypes.lean`)
* `conHatI`, `stepHatI`, `foldHatI`: the translated node, step and eliminator of an indexed
  family
* `tabCost`, `conHat`, `stepHat`, `foldHat`: the charge of a tabulation, the translated node of
  a constructor, the charges of a step and of an eliminator over translated nodes
* `Tm.dtC`, `Tm.allowC`: the charges and the allowance at a charge `cc a ≤ 1` of a call;
  `Tm.dt`, `Tm.allow`: at the charge `callCost` of `derive_timed`
* `Tm.Pure`, `Tm.InDtFrag`, `iterCost`

## Main results

* `TimedSimTree.bindCont`, `TimedSim.bindCont`: the costed bind against a D bind under any
  continuation.
* `tabT_stepN`, `stepAt_sim`, `foldW_sim`: a tabulation and an eliminator at pure costed
  closures are leaves within their charges, by induction on the signature and on the relation
  of the values; `conAt_sim`: a constructor builds a node related to the translated node of its
  translated argument; `conAtI_sim`, `stepAtI_sim`, `foldIW_sim` for indexed families
* `tabCost_add`, `tabDep_stepN`: the charge of a tabulation is additive, and a dependent
  tabulation of leaves is a leaf within the sum of their costs
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

mutual

/-- The translated values of a type: a function type is a pure costed closure, a function and
its cost; an inductive type is the W-type of its constructors with their translated fields; the
other types have their values. -/
def Ty.hat : Ty → Type
  | .base f => f.den
  | .nat => ℕ
  | .prod a b => Ty.hat a × Ty.hat b
  | .sum a b => Ty.hat a ⊕ Ty.hat b
  | .arr a b => Container.Costed (Ty.hat a) (Ty.hat b)
  | .list a => List (Ty.hat a)
  | .mu S => WType (fun s : (c : S.Ctor) × Sig.hatF S c => S.Pos s.1)
  | .pi f B => (j : f.den) → Ty.hat (B j)
  | .sig f B => (j : f.den) × Ty.hat (B j)
  | .imu _ S i => IW (fun j => (c : (S j).Ctor) × ISig.hatF (S j) c) (fun j a => (S j).Pos a.1)
      (fun j a p => (S j).nx a.1 p) i

/-- The translated fields of the constructors of a signature. -/
def Sig.hatF : (S : Sig) → S.Ctor → Type
  | .base a, _ => Ty.hat a
  | .ext S _ _, .inl c => Sig.hatF S c
  | .ext _ a _, .inr _ => Ty.hat a

/-- The translated fields of the constructors of an indexed signature. -/
def ISig.hatF {f : FTy} : (S : ISig f) → S.Ctor → Type
  | .base a => fun _ => Ty.hat a
  | .ext S a _ _ => Sum.elim (ISig.hatF S) fun _ => Ty.hat a

end

/-- The translated environment entries: a variable of function type is a costed tree for each
argument, a variable of any other type a translated value. -/
def Ty.hatE : Ty → Type 1
  | .base f => ULift (Ty.hat (.base f))
  | .nat => ULift (Ty.hat .nat)
  | .prod a b => ULift (Ty.hat (.prod a b))
  | .sum a b => ULift (Ty.hat (.sum a b))
  | .arr a b => Ty.hat a → ℕ × SPTree.Timed (Ty.hat b)
  | .list a => ULift (Ty.hat (.list a))
  | .mu S => ULift (Ty.hat (.mu S))
  | .pi f B => ULift (Ty.hat (.pi f B))
  | .sig f B => ULift (Ty.hat (.sig f B))
  | .imu f S i => ULift (Ty.hat (.imu f S i))

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
  | .mu _, u => ⟨u⟩
  | .pi _ _, u => ⟨u⟩
  | .sig _ _, u => ⟨u⟩
  | .imu _ _ _, u => ⟨u⟩

/-- The costed tree of a variable read: the entry as a value at no cost; a variable of
function type is not read as a value. -/
noncomputable def Ty.read : (τ : Ty) → τ.hatE → ℕ × SPTree.Timed τ.hat
  | .base _, u => (0, .ret u.down)
  | .nat, u => (0, .ret u.down)
  | .prod _ _, u => (0, .ret u.down)
  | .sum _ _, u => (0, .ret u.down)
  | .arr _ _, _ => (0, .fail)
  | .list _, u => (0, .ret u.down)
  | .mu _, u => (0, .ret u.down)
  | .pi _ _, u => (0, .ret u.down)
  | .sig _ _, u => (0, .ret u.down)
  | .imu _ _ _, u => (0, .ret u.down)

mutual

/-- The value of D of a translated first-order value. -/
def Ty.toVal : (τ : Ty) → τ.FO → τ.hat → Val τ
  | .base _, _, u => u
  | .nat, _, u => u
  | .prod a b, h, u => (a.toVal h.1 u.1, b.toVal h.2 u.2)
  | .sum a b, h, u => Sum.map (a.toVal h.1) (b.toVal h.2) u
  | .arr _ _, h, _ => False.elim h
  | .list a, h, u => List.map (a.toVal h) u
  | .mu S, h, u => Container.wmapF (P := S.Pos) (fun c x => Sig.toValF S h c x) u
  | .pi _ B, h, u => fun j => (B j).toVal (h j) (u j)
  | .sig _ B, h, u => ⟨u.1, (B u.1).toVal (h u.1) u.2⟩
  | .imu _ S _, h, u => Container.iwmapF
      (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c) (nx := fun j c p => (S j).nx c p)
      (fun j c x => ISig.toValF (S j) (h j) c x) u

/-- The field of D of a translated field of a first-order signature. -/
def Sig.toValF : (S : Sig) → S.FO → (c : S.Ctor) → S.hatF c → S.Fld c
  | .base a, h, _, x => a.toVal h x
  | .ext S _ _, h, .inl c, x => Sig.toValF S h.1 c x
  | .ext _ a _, h, .inr _, x => a.toVal h.2 x

/-- The field of D of a translated field of a first-order indexed signature. -/
def ISig.toValF {f : FTy} : (S : ISig f) → S.FO → (c : S.Ctor) → S.hatF c → S.Fld c
  | .base a, h => fun _ x => a.toVal h x
  | .ext S a _ _, h => fun c => match c with
    | .inl c => ISig.toValF S h.1 c
    | .inr _ => fun x => a.toVal h.2 x

end

mutual

/-- The translated value of a first-order value of D. -/
def Ty.ofVal : (τ : Ty) → τ.FO → Val τ → τ.hat
  | .base _, _, v => v
  | .nat, _, v => v
  | .prod a b, h, v => (a.ofVal h.1 v.1, b.ofVal h.2 v.2)
  | .sum a b, h, v => Sum.map (a.ofVal h.1) (b.ofVal h.2) v
  | .arr _ _, h, _ => False.elim h
  | .list a, h, v => List.map (a.ofVal h) v
  | .mu S, h, v => Container.wmapF (P := S.Pos) (fun c x => Sig.ofValF S h c x) v
  | .pi _ B, h, v => fun j => (B j).ofVal (h j) (v j)
  | .sig _ B, h, v => ⟨v.1, (B v.1).ofVal (h v.1) v.2⟩
  | .imu _ S _, h, v => Container.iwmapF
      (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c) (nx := fun j c p => (S j).nx c p)
      (fun j c x => ISig.ofValF (S j) (h j) c x) v

/-- The translated field of a field of D of a first-order signature. -/
def Sig.ofValF : (S : Sig) → S.FO → (c : S.Ctor) → S.Fld c → S.hatF c
  | .base a, h, _, x => a.ofVal h x
  | .ext S _ _, h, .inl c, x => Sig.ofValF S h.1 c x
  | .ext _ a _, h, .inr _, x => a.ofVal h.2 x

/-- The translated field of a field of D of a first-order indexed signature. -/
def ISig.ofValF {f : FTy} : (S : ISig f) → S.FO → (c : S.Ctor) → S.Fld c → S.hatF c
  | .base a, h => fun _ x => a.ofVal h x
  | .ext S a _ _, h => fun c => match c with
    | .inl c => ISig.ofValF S h.1 c
    | .inr _ => fun x => a.ofVal h.2 x

end

mutual

/-- Translated values and values of D: equal at ground types, componentwise at products, sums
and lists, at a function type the step equation of a data function, its steps bounded by the
cost of the closure, and at an inductive type the lifting `Container.WLift` of the relation of the
fields: two nodes of one constructor with related fields and related children. -/
def Sim : (τ : Ty) → τ.hat → Val τ → Prop
  | .base _, u, v => u = v
  | .nat, u, v => u = v
  | .prod a b, u, v => Sim a u.1 v.1 ∧ Sim b u.2 v.2
  | .sum a b, u, v => Sum.LiftRel (Sim a) (Sim b) u v
  | .arr a b, p, g => ∀ u v, Sim a u v →
      ∃ m w, g v = stepN CTree.tick m (.ret w) ∧ m ≤ p.2 u ∧ Sim b (p.1 u) w
  | .list a, u, v => List.Forall₂ (Sim a) u v
  | .mu S, u, v => Container.WLift (P := S.Pos) (Sig.SimF S) u v
  | .pi _ B, u, v => ∀ j, Sim (B j) (u j) (v j)
  | .sig _ B, u, v => ∃ e : u.1 = v.1, Sim (B v.1) (e ▸ u.2) v.2
  | .imu _ S _, u, v => Container.IWLift
      (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c) (nx := fun j c p => (S j).nx c p)
      (fun j c x y => ISig.SimF (S j) c x y) u v

/-- `Sim` at the fields of the constructors of a signature. -/
def Sig.SimF : (S : Sig) → (c : S.Ctor) → S.hatF c → S.Fld c → Prop
  | .base a, _, x, y => Sim a x y
  | .ext S _ _, .inl c, x, y => Sig.SimF S c x y
  | .ext _ a _, .inr _, x, y => Sim a x y

/-- `Sim` at the fields of the constructors of an indexed signature. -/
def ISig.SimF {f : FTy} : (S : ISig f) → (c : S.Ctor) → S.hatF c → S.Fld c → Prop
  | .base a => fun _ x y => Sim a x y
  | .ext S a _ _ => fun c => match c with
    | .inl c => ISig.SimF S c
    | .inr _ => fun x y => Sim a x y

end

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
  | .mu S, u, v => Sim (.mu S) u.down v
  | .pi f B, u, v => Sim (.pi f B) u.down v
  | .sig f B, u, v => Sim (.sig f B) u.down v
  | .imu f S i, u, v => Sim (.imu f S i) u.down v

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

mutual

/-- At a first-order type, a value of D related to a translated value is its value of D. -/
theorem Sim.toVal_eq : ∀ (τ : Ty) (h : τ.FO) {u : τ.hat} {v : Val τ}, Sim τ u v →
    v = τ.toVal h u
  | .base _, _, _, _, hs => hs.symm
  | .nat, _, _, _, hs => hs.symm
  | .prod a b, h, _, _, hs => Prod.ext (Sim.toVal_eq a h.1 hs.1) (Sim.toVal_eq b h.2 hs.2)
  | .sum a b, h, _, _, hs => by
    cases hs with
    | inl hs => exact congrArg Sum.inl (Sim.toVal_eq a h.1 hs)
    | inr hs => exact congrArg Sum.inr (Sim.toVal_eq b h.2 hs)
  | .arr _ _, h, _, _, _ => h.elim
  | .list a, h, _, _, hs => by
    induction hs with
    | nil => rfl
    | cons hx _ ihl => exact congrArg₂ List.cons (Sim.toVal_eq a h hx) ihl
  | .mu S, h, u, v, hs => by
    change Container.WLift (P := S.Pos) (Sig.SimF S) u v at hs
    induction hs with
    | @mk c x y k k' hxy _ ih =>
      have e1 := Sig.SimF.toVal_eq S h c hxy
      subst e1
      have e2 : k' = fun p => Ty.toVal (.mu S) h (k p) := funext ih
      subst e2
      rfl
  | .pi _ B, h, _, _, hs => funext fun j => Sim.toVal_eq (B j) (h j) (hs j)
  | .sig f B, h, u, v, hs => by
    change (j : f.den) × Ty.hat (B j) at u
    change (j : f.den) × Val (B j) at v
    obtain ⟨i, x⟩ := u
    obtain ⟨j, y⟩ := v
    change ∃ e : i = j, Sim (B j) (e ▸ x) y at hs
    obtain ⟨rfl, hxy⟩ := hs
    show (⟨i, y⟩ : (j : f.den) × Val (B j)) = ⟨i, (B i).toVal (h i) x⟩
    rw [← Sim.toVal_eq (B i) (h i) hxy]
  | .imu f S _, h, u, v, hs => by
    have h' : ∀ j, (S j).FO := h
    show v = Container.iwmapF
        (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c)
        (nx := fun j c p => (S j).nx c p) (fun j c x => ISig.toValF (S j) (h' j) c x) u
    clear h
    change Container.IWLift
        (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c)
        (nx := fun j c p => (S j).nx c p) (fun j c x y => ISig.SimF (S j) c x y) u v at hs
    induction hs with
    | @mk i c x y k k' hxy _ ih =>
      have e1 := ISig.SimF.toVal_eq (S i) (h' i) c hxy
      subst e1
      have e2 : k' = fun p => Container.iwmapF
          (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c) (nx := fun j c p => (S j).nx c p)
          (fun j c x => ISig.toValF (S j) (h' j) c x) (k p) := funext ih
      subst e2
      rfl

/-- At the fields of a first-order signature, a field of D related to a translated field is its
field of D. -/
theorem Sig.SimF.toVal_eq : ∀ (S : Sig) (h : S.FO) (c : S.Ctor) {x : S.hatF c} {y : S.Fld c},
    Sig.SimF S c x y → y = Sig.toValF S h c x
  | .base a, h, _, _, _, hs => Sim.toVal_eq a h hs
  | .ext S _ _, h, .inl c, _, _, hs => Sig.SimF.toVal_eq S h.1 c hs
  | .ext _ a _, h, .inr _, _, _, hs => Sim.toVal_eq a h.2 hs

/-- At the fields of a first-order indexed signature, a field of D related to a translated field
is its field of D. -/
theorem ISig.SimF.toVal_eq {f : FTy} : ∀ (S : ISig f) (h : S.FO) (c : S.Ctor) {x : S.hatF c}
    {y : S.Fld c}, ISig.SimF S c x y → y = ISig.toValF S h c x
  | .base a, h, _, _, _, hs => Sim.toVal_eq a h hs
  | .ext S a _ _, h, c, _, _, hs => by
    cases c with
    | inl c => exact ISig.SimF.toVal_eq S h.1 c hs
    | inr _ => exact Sim.toVal_eq a h.2 hs

end

mutual

/-- At a first-order type, the translated value of a value of D is related to it. -/
theorem Sim.ofVal : ∀ (τ : Ty) (h : τ.FO) (v : Val τ), Sim τ (τ.ofVal h v) v
  | .base _, _, _ => rfl
  | .nat, _, _ => rfl
  | .prod a b, h, v => ⟨Sim.ofVal a h.1 v.1, Sim.ofVal b h.2 v.2⟩
  | .sum a b, h, v => by
    cases v with
    | inl x => exact Sum.LiftRel.inl (Sim.ofVal a h.1 x)
    | inr y => exact Sum.LiftRel.inr (Sim.ofVal b h.2 y)
  | .arr _ _, h, _ => h.elim
  | .list a, h, v => by
    induction v with
    | nil => exact List.Forall₂.nil
    | cons x xs ihl => exact List.Forall₂.cons (Sim.ofVal a h x) ihl
  | .mu S, h, v => by
    induction v with
    | mk a k ih =>
      obtain ⟨c, y⟩ := a
      exact Container.WLift.mk (Sig.SimF.ofVal S h c y) ih
  | .pi _ B, h, v => fun j => Sim.ofVal (B j) (h j) (v j)
  | .sig _ B, h, v => ⟨rfl, Sim.ofVal (B v.1) (h v.1) v.2⟩
  | .imu _ S _, h, v => by
    have h' : ∀ j, (S j).FO := h
    show Container.IWLift
        (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c)
        (nx := fun j c p => (S j).nx c p) (fun j c x y => ISig.SimF (S j) c x y)
      (Container.iwmapF
          (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c)
          (nx := fun j c p => (S j).nx c p) (fun j c x => ISig.ofValF (S j) (h' j) c x) v) v
    clear h
    induction v with
    | mk i a k ih =>
      obtain ⟨c, y⟩ := a
      exact Container.IWLift.mk
          (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c)
          (nx := fun j c p => (S j).nx c p) (R := fun j c x y => ISig.SimF (S j) c x y)
        (ISig.SimF.ofVal (S i) (h' i) c y) ih

/-- At the fields of a first-order signature, the translated field of a field of D is related to
it. -/
theorem Sig.SimF.ofVal : ∀ (S : Sig) (h : S.FO) (c : S.Ctor) (y : S.Fld c),
    Sig.SimF S c (Sig.ofValF S h c y) y
  | .base a, h, _, y => Sim.ofVal a h y
  | .ext S _ _, h, .inl c, y => Sig.SimF.ofVal S h.1 c y
  | .ext _ a _, h, .inr _, y => Sim.ofVal a h.2 y

/-- At the fields of a first-order indexed signature, the translated field of a field of D is
related to it. -/
theorem ISig.SimF.ofVal {f : FTy} : ∀ (S : ISig f) (h : S.FO) (c : S.Ctor) (y : S.Fld c),
    ISig.SimF S c (ISig.ofValF S h c y) y
  | .base a, h, _, y => Sim.ofVal a h y
  | .ext S a _ _, h, c, y => by
    cases c with
    | inl c => exact ISig.SimF.ofVal S h.1 c y
    | inr _ => exact Sim.ofVal a h.2 y

end

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

mutual

/-- Every translated type is inhabited. -/
theorem Ty.hat_nonempty : ∀ τ : Ty, Nonempty τ.hat
  | .base f => FTy.instNonempty f
  | .nat => ⟨(0 : ℕ)⟩
  | .prod a b => ⟨(Classical.choice (Ty.hat_nonempty a), Classical.choice (Ty.hat_nonempty b))⟩
  | .sum a _ => ⟨Sum.inl (Classical.choice (Ty.hat_nonempty a))⟩
  | .arr _ b => ⟨(fun _ => Classical.choice (Ty.hat_nonempty b), fun _ => 0)⟩
  | .list _ => ⟨[]⟩
  | .mu S => ⟨WType.mk ⟨(Sig.leaf S).1.1, Classical.choice (Sig.hatF_nonempty S _)⟩
      fun p => ((Sig.leaf S).2 p).elim⟩
  | .pi _ B => ⟨fun j => Classical.choice (Ty.hat_nonempty (B j))⟩
  | .sig f B => ⟨⟨(FTy.instInhabited f).default,
      Classical.choice (Ty.hat_nonempty (B (FTy.instInhabited f).default))⟩⟩
  | .imu _ S i => ⟨Container.IPW.mk i
      ⟨(ISig.leaf (S i)).1.1, Classical.choice (ISig.hatF_nonempty (S i) _)⟩
      fun p => ((ISig.leaf (S i)).2 p).elim⟩

/-- Every translated field is inhabited. -/
theorem Sig.hatF_nonempty : ∀ (S : Sig) (c : S.Ctor), Nonempty (S.hatF c)
  | .base a, _ => Ty.hat_nonempty a
  | .ext S _ _, .inl c => Sig.hatF_nonempty S c
  | .ext _ a _, .inr _ => Ty.hat_nonempty a

/-- Every translated field of an indexed signature is inhabited. -/
theorem ISig.hatF_nonempty {f : FTy} : ∀ (S : ISig f) (c : S.Ctor), Nonempty (S.hatF c)
  | .base a, _ => Ty.hat_nonempty a
  | .ext S a _ _, c => by
    cases c with
    | inl c => exact ISig.hatF_nonempty S c
    | inr _ => exact Ty.hat_nonempty a

end

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
def callCost : Ty → ℕ
  | .base .unit => 0
  | _ => 1

/-- The charge of a call is at most one. -/
theorem callCost_le_one (a : Ty) : callCost a ≤ 1 := by
  unfold callCost; split <;> omega

/-- The charge of `k` rounds of a pure costed closure from `acc`: one plus the cost of the
closure per round. -/
def iterCost {c : Ty} (p : Ty.hat (.arr c c)) : c.hat → ℕ → ℕ
  | _, 0 => 0
  | acc, k + 1 => 1 + p.2 acc + iterCost p (p.1 acc) k

/-- The charge of a tabulation over `Fin n` at the costs `c`: their sum, in the order of
`tabFin`. -/
def tabCostFin : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, c => c 0 + tabCostFin n fun i => c i.succ

/-- The charge of a tabulation over the functions `Fin q → r.den`, from the charge `tc` of a
tabulation over `r`. -/
def tabCostTab (r : FTy) (tc : (r.den → ℕ) → ℕ) : (q : ℕ) → ((Fin q → r.den) → ℕ) → ℕ
  | 0, c => c Fin.elim0
  | q + 1, c => tc fun a => tabCostTab r tc q fun h => c (Fin.cons a h : Fin (q + 1) → r.den)

/-- The charge of a tabulation over a finite ground type at the costs `c`: their sum over the
elements, in the order of `tabT`. -/
def tabCost : (f : FTy) → (f.den → ℕ) → ℕ
  | .unit, c => c ()
  | .bool, c => c false + c true
  | .word w, c => tabCostFin (2 ^ w) fun i => c (BitVec.ofFin i)
  | .fin n, c => tabCostFin (n + 1) c
  | .tab q r, c => tabCostTab r (tabCost r) q c

/-- The translated node of a constructor of `S` at a translated argument, built by `mk`; the
children of a constructor with positions are the table in its argument. -/
def conHat {S₀ : Sig} : (S : Sig) →
    ((a : (c : S.Ctor) × S.hatF c) → (S.Pos a.1 → Ty.hat (.mu S₀)) → Ty.hat (.mu S₀)) →
    Ty.hat (S.conTy (.mu S₀)) → Ty.hat (.mu S₀)
  | .base _, mk, u => mk ⟨(), u⟩ fun p => Empty.elim p
  | .ext S _ none, mk, .inl u => conHat S (fun b k => mk ⟨.inl b.1, b.2⟩ k) u
  | .ext _ _ none, mk, .inr u => mk ⟨.inr (), u⟩ fun p => Empty.elim p
  | .ext S _ (some _), mk, .inl u => conHat S (fun b k => mk ⟨.inl b.1, b.2⟩ k) u
  | .ext _ a (some f), mk, .inr u =>
    let u' : a.hat × (f.den → Ty.hat (.mu S₀)) := u
    mk ⟨.inr (), u'.1⟩ u'.2

/-- The costed step of an eliminator of `S` at a translated node of constructor and field `a`,
from the translated step functions `p`, the translated children `kids` and the costed recursive
results `rec`: the value and the cost of the step function of the constructor at the field, the
children and the results. -/
noncomputable def stepHat {S₀ : Sig} {c : Ty} : (S : Sig) →
    Ty.hat (S.stepsTy (.mu S₀) c) → (a : (c : S.Ctor) × S.hatF c) →
    (S.Pos a.1 → Ty.hat (.mu S₀)) → (S.Pos a.1 → c.hat × ℕ) → c.hat × ℕ
  | .base a, p, ⟨_, x⟩, _, _ =>
    let p' : (a.hat → c.hat) × (a.hat → ℕ) := p
    (p'.1 x, p'.2 x)
  | .ext S _ _, p, ⟨.inl c', x⟩, kids, rec => stepHat S p.1 ⟨c', x⟩ kids rec
  | .ext _ a none, p, ⟨.inr _, x⟩, _, _ =>
    let p' : (a.hat → c.hat) × (a.hat → ℕ) := p.2
    (p'.1 x, p'.2 x)
  | .ext _ a (some f), p, ⟨.inr _, x⟩, kids, rec =>
    let p' : Ty.hat (.arr (Sig.altTy a (some f) (.mu S₀) c) c) := p.2
    let arg : a.hat × ((f.den → Ty.hat (.mu S₀)) × ((f.den → c.hat) × (f.den → ℕ))) :=
      (x, kids, (fun j => (rec j).1, fun j => (rec j).2))
    (p'.1 arg, p'.2 arg)

/-- The costed eliminator of `mu S` with the translated step functions `p`: the value and the
cost of the step at each node, its recursive results the costed eliminator at the children. -/
noncomputable def foldHat {S : Sig} {c : Ty} (p : Ty.hat (S.stepsTy (.mu S) c)) :
    Ty.hat (.mu S) → c.hat × ℕ
  | ⟨a, kids⟩ => stepHat S p a kids fun j => foldHat p (kids j)

/-- The translated node of a constructor of a signature of an indexed family at a translated
argument, built by `mk`. -/
def conHatI {f : FTy} {X : f.den → Ty} {R : Type} : (S : ISig f) →
    ((a : (c : S.Ctor) × S.hatF c) → ((p : S.Pos a.1) → Ty.hat (X (S.nx a.1 p))) → R) →
    Ty.hat (S.conTy X) → R
  | .base _, mk, u => mk ⟨(), u⟩ fun p => Empty.elim p
  | .ext S _ none _, mk, u =>
    match (u : Ty.hat (S.conTy X) ⊕ Ty.hat _) with
    | .inl u => conHatI S (fun a k => mk ⟨.inl a.1, a.2⟩ k) u
    | .inr u => mk ⟨.inr (), u⟩ fun p => Empty.elim p
  | .ext S a (some h) nx, mk, u =>
    match (u : Ty.hat (S.conTy X) ⊕ (a.hat × ((p : h.den) → Ty.hat (X (nx p))))) with
    | .inl u => conHatI S (fun a k => mk ⟨.inl a.1, a.2⟩ k) u
    | .inr u => mk ⟨.inr (), u.1⟩ u.2

/-- The costed step of an eliminator at a signature of an indexed family, at a translated node:
the value and the cost of the step function of the constructor at the field, the children and
the costed recursive results, each recursive result a costed closure on `unit`. -/
noncomputable def stepHatI {f : FTy} {X c : f.den → Ty} {r : Ty} : (S : ISig f) →
    Ty.hat (S.stepsTy X c r) → (a : (c' : S.Ctor) × S.hatF c') →
    ((p : S.Pos a.1) → Ty.hat (X (S.nx a.1 p))) → ((p : S.Pos a.1) → (c (S.nx a.1 p)).hat × ℕ) →
    r.hat × ℕ
  | .base a, p, x, _, _ =>
    let p' : (a.hat → r.hat) × (a.hat → ℕ) := p
    (p'.1 x.2, p'.2 x.2)
  | .ext S a none _, p, ⟨c', x⟩, kids, rec =>
    match c', x, kids, rec with
    | .inl c'', x, kids, rec => stepHatI S p.1 ⟨c'', x⟩ kids rec
    | .inr _, x, _, _ =>
      let p' : (a.hat → r.hat) × (a.hat → ℕ) := p.2
      (p'.1 x, p'.2 x)
  | .ext S a (some h) nx, p, ⟨c', x⟩, kids, rec =>
    match c', x, kids, rec with
    | .inl c'', x, kids, rec => stepHatI S p.1 ⟨c'', x⟩ kids rec
    | .inr _, x, kids, rec =>
      let p' : Ty.hat (.arr (ISig.altTy a (some h) nx X c) r) := p.2
      let arg : a.hat × (((q : h.den) → Ty.hat (X (nx q))) ×
          ((q : h.den) → (Unit → (c (nx q)).hat) × (Unit → ℕ))) :=
        (x, kids, fun q => (fun _ => (rec q).1, fun _ => (rec q).2))
      (p'.1 arg, p'.2 arg)

/-- The costed eliminator of an indexed family with the table `p` of translated step functions:
the value and the cost of the step at each node, its recursive results the costed eliminator at
the children. -/
noncomputable def foldHatI {f : FTy} {S : f.den → ISig f} {c : f.den → Ty}
    (p : (j : f.den) → Ty.hat ((S j).stepsTy (fun j' => .imu f S j') c (c j))) :
    {i : f.den} → Ty.hat (.imu f S i) → (c i).hat × ℕ
  | _, .mk i a kids => stepHatI (S i) (p i) a kids fun q => foldHatI p (kids q)

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
  | _, _, .con x => x.allowC cc
  | _, _, .fold g x => g.allowC cc + x.allowC cc
  | _, _, .icon x => x.allowC cc
  | _, _, .ifold (c := _) g x => g.allowC cc + x.allowC cc
  | _, _, .ptab (f := f) ts => tabCost f fun j => (ts j).allowC cc
  | _, _, .papp (B := B) t _ => t.allowC cc
  | _, _, .spair _ x => x.allowC cc
  | _, _, .scase s ks => s.allowC cc + Finset.univ.sup fun j => (ks j).allowC cc
  | _, _, .fcase i ks => i.allowC cc + Finset.univ.sup fun j => (ks j).allowC cc
  | _, _, .var _ => 0
  | _, _, .lam _ => 0
  | _, _, .natLit _ => 0
  | _, _, .lit _ _ => 0
  | _, _, .nil => 0
  | _, _, .sample _ => 0
  | _, _, .get _ _ => 0
  | _, _, .fail => 0

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
  | _, _, .con (S := S) x, η => bindT (x.dtC cc η) fun u =>
    (0, .ret (conHat S (fun a k => (WType.mk a k : Ty.hat (.mu S))) u))
  | _, _, .fold g x, η => bindT (g.dtC cc η) fun p => bindT (x.dtC cc η) fun w =>
    (1 + (foldHat p w).2, .ret (foldHat p w).1)
  | _, _, .icon (f := f) (S := S) (i := i) x, η => bindT (x.dtC cc η) fun u =>
    (0, .ret (conHatI (X := fun j => .imu f S j) (S i)
      (fun a k => (Container.IPW.mk i a k : Ty.hat (.imu f S i))) u))
  | _, _, .ifold (c := c) g x, η => bindT (g.dtC cc η) fun p => bindT (x.dtC cc η) fun w =>
    (1 + (foldHatI (c := c) p w).2, .ret (foldHatI (c := c) p w).1)
  | _, _, .ptab (f := f) (B := B) ts, η =>
    (tabCost f fun j => ((ts j).dtC cc η).1,
      .ret fun j => (B j).pureVal ((ts j).dtC cc η).2)
  | _, _, .papp (B := B) t j, η =>
    bindT (t.dtC cc η) fun (u : (j : _) → (B j).hat) => (0, .ret (u j))
  | _, _, .spair (f := f) (B := B) j x, η =>
    bindT (x.dtC cc η) fun u => (0, .ret (⟨j, u⟩ : (j : f.den) × (B j).hat))
  | _, _, .scase (f := f) (B := B) s ks, η =>
    bindT (s.dtC cc η) fun (u : (j : f.den) × (B j).hat) =>
      SPTree.Timed.delay 1 ((ks u.1).dtC cc (η.cons u.2))
  | _, _, .fcase (f := f) i ks, η =>
    bindT (i.dtC cc η) fun (j : f.den) => SPTree.Timed.delay 1 ((ks j).dtC cc η)

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
  | _, _, .con x => x.Pure
  | _, _, .fold g x => g.Pure ∧ x.Pure
  | _, _, .icon x => x.Pure
  | _, _, .ifold (c := _) g x => g.Pure ∧ x.Pure
  | _, _, .ptab ts => ∀ j, (ts j).Pure
  | _, _, .papp (B := B) t _ => t.Pure
  | _, _, .spair _ x => x.Pure
  | _, _, .scase s ks => s.Pure ∧ ∀ j, (ks j).Pure
  | _, _, .fcase i ks => i.Pure ∧ ∀ j, (ks j).Pure
  | _, _, .sample _ => False
  | _, _, .get _ _ => False
  | _, _, .set _ _ _ => False
  | _, _, .query _ _ _ => False
  | _, _, .fail => False

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
  | con x ih =>
    intro ht η
    obtain ⟨u, hu⟩ := ih ht η
    simp only [dtC, bindT, SPTree.Timed.delay, hu, SPTree.Timed.bind]
    exact ⟨_, rfl⟩
  | fold g x ihg ihx =>
    intro ht η
    obtain ⟨p, hp⟩ := ihg ht.1 η
    obtain ⟨w, hw⟩ := ihx ht.2 η
    simp only [dtC, bindT, SPTree.Timed.delay, hp, hw, SPTree.Timed.bind]
    exact ⟨_, rfl⟩
  | icon x ih =>
    intro ht η
    obtain ⟨u, hu⟩ := ih ht η
    simp only [dtC, bindT, SPTree.Timed.delay, hu, SPTree.Timed.bind]
    exact ⟨_, rfl⟩
  | ifold g x ihg ihx =>
    intro ht η
    obtain ⟨p, hp⟩ := ihg ht.1 η
    obtain ⟨w, hw⟩ := ihx ht.2 η
    simp only [dtC, bindT, SPTree.Timed.delay, hp, hw, SPTree.Timed.bind]
    exact ⟨_, rfl⟩
  | ptab ts ih => intro _ η; exact ⟨_, rfl⟩
  | papp t j ih =>
    intro ht η
    obtain ⟨u, hu⟩ := ih ht η
    simp only [dtC, bindT, SPTree.Timed.delay, hu, SPTree.Timed.bind]
    exact ⟨_, rfl⟩
  | spair j x ih =>
    intro ht η
    obtain ⟨u, hu⟩ := ih ht η
    simp only [dtC, bindT, SPTree.Timed.delay, hu, SPTree.Timed.bind]
    exact ⟨_, rfl⟩
  | scase s ks ihs ihks =>
    intro ht η
    obtain ⟨u, hu⟩ := ihs ht.1 η
    obtain ⟨w, hw⟩ := ihks u.1 (ht.2 u.1) (η.cons u.2)
    simp only [dtC, bindT, SPTree.Timed.delay, hu, hw, SPTree.Timed.bind]
    exact ⟨_, rfl⟩
  | fcase i ks ihi ihks =>
    intro ht η
    obtain ⟨u, hu⟩ := ihi ht.1 η
    obtain ⟨w, hw⟩ := ihks u (ht.2 u) η
    simp only [dtC, bindT, SPTree.Timed.delay, hu, hw, SPTree.Timed.bind]
    exact ⟨_, rfl⟩

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
  | _, _, .con x => x.InDtFrag
  | _, _, .fold g x => g.InDtFrag ∧ x.InDtFrag
  | _, _, .icon x => x.InDtFrag
  | _, _, .ifold (c := _) g x => g.InDtFrag ∧ x.InDtFrag
  | _, _, .ptab ts => ∀ j, (ts j).InDtFrag ∧ (ts j).Pure
  | _, _, .papp (B := B) t _ => t.InDtFrag
  | _, _, .spair _ x => x.InDtFrag
  | _, _, .scase s ks => s.InDtFrag ∧ ∀ j, (ks j).InDtFrag
  | _, _, .fcase i ks => i.InDtFrag ∧ ∀ j, (ks j).InDtFrag

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

/-! ## Inductive types -/

/-- A tabulation over `Fin n` of trees that are leaves after `m i` ticks is the leaf of their
values after `tabCostFin n m` ticks. -/
theorem tabFin_stepN {X : Type} : ∀ (n : ℕ) {g : Fin n → CTree X} {m : Fin n → ℕ}
    {w : Fin n → X}, (∀ i, g i = stepN CTree.tick (m i) (.ret (w i))) →
      tabFin n g = stepN CTree.tick (tabCostFin n m) (.ret w)
  | 0, _, _, w, _ => by
    show CTree.ret Fin.elim0 = CTree.ret w
    exact congrArg CTree.ret (funext fun i => i.elim0)
  | n + 1, g, m, w, hg => by
    have ih := tabFin_stepN n (g := fun i => g i.succ) (m := fun i => m i.succ)
      (w := fun i => w i.succ) fun i => hg i.succ
    rw [tabFin, hg 0, Reflect.stepN_ret_bind, ih, Reflect.stepN_ret_bind, Reflect.stepN_tick_add]
    exact congrArg _ (congrArg CTree.ret (Fin.cons_self_tail w))

theorem tabTab_stepN (r : FTy) (tr : ∀ {Y : Type}, (r.den → CTree Y) → CTree (r.den → Y))
    (tc : (r.den → ℕ) → ℕ)
    (htr : ∀ {Y : Type} {g : r.den → CTree Y} {m : r.den → ℕ} {w : r.den → Y},
      (∀ a, g a = stepN CTree.tick (m a) (.ret (w a))) →
        tr g = stepN CTree.tick (tc m) (.ret w))
    {X : Type} : ∀ (q : ℕ) {g : (Fin q → r.den) → CTree X} {m : (Fin q → r.den) → ℕ}
      {w : (Fin q → r.den) → X}, (∀ v, g v = stepN CTree.tick (m v) (.ret (w v))) →
      tabTab r tr q g = stepN CTree.tick (tabCostTab r tc q m) (.ret w)
  | 0, g, m, w, hg => by
    rw [tabTab, hg Fin.elim0, Reflect.stepN_ret_bind]
    refine congrArg _ (congrArg CTree.ret (funext fun v => ?_))
    rw [show v = Fin.elim0 from funext fun i => i.elim0]
  | q + 1, g, m, w, hg => by
    have hin := fun a => tabTab_stepN r tr tc htr q
      (g := fun h => g (Fin.cons a h : Fin (q + 1) → r.den))
      (m := fun h => m (Fin.cons a h : Fin (q + 1) → r.den))
      (w := fun h => w (Fin.cons a h : Fin (q + 1) → r.den)) fun h => hg _
    rw [tabTab, htr hin, Reflect.stepN_ret_bind]
    exact congrArg _ (congrArg CTree.ret (funext fun v => by simp only [Fin.cons_self_tail]))

/-- A tabulation of trees that are leaves after `m j` ticks is the leaf of their values after
`tabCost f m` ticks. -/
theorem tabT_stepN : ∀ (f : FTy) {X : Type} {g : f.den → CTree X} {m : f.den → ℕ}
    {w : f.den → X}, (∀ j, g j = stepN CTree.tick (m j) (.ret (w j))) →
      tabT f g = stepN CTree.tick (tabCost f m) (.ret w)
  | .unit, X, g, m, w, hg => by
    rw [tabT, hg (), Reflect.stepN_ret_bind]
    rfl
  | .bool, X, g, m, w, hg => by
    rw [tabT, hg false, Reflect.stepN_ret_bind, hg true, Reflect.stepN_ret_bind,
      Reflect.stepN_tick_add]
    exact congrArg _ (congrArg CTree.ret (funext fun b => by cases b <;> rfl))
  | .word n, X, g, m, w, hg => by
    rw [tabT, tabFin_stepN (2 ^ n) (m := fun i => m (BitVec.ofFin i))
      (w := fun i => w (BitVec.ofFin i)) fun i => hg _, Reflect.stepN_ret_bind]
    rfl
  | .fin n, X, g, m, w, hg => tabFin_stepN (n + 1) hg
  | .tab q r, X, g, m, w, hg =>
    tabTab_stepN r (fun g' => tabT r g') (tabCost r) (fun h => tabT_stepN r h) q hg

theorem tabCostFin_mono : ∀ (n : ℕ) {c c' : Fin n → ℕ}, (∀ i, c i ≤ c' i) →
    tabCostFin n c ≤ tabCostFin n c'
  | 0, _, _, _ => le_rfl
  | n + 1, _, _, h => Nat.add_le_add (h 0) (tabCostFin_mono n fun i => h i.succ)

theorem tabCostTab_mono (r : FTy) (tc : (r.den → ℕ) → ℕ)
    (htc : ∀ {c c' : r.den → ℕ}, (∀ a, c a ≤ c' a) → tc c ≤ tc c') :
    ∀ (q : ℕ) {c c' : (Fin q → r.den) → ℕ}, (∀ v, c v ≤ c' v) →
      tabCostTab r tc q c ≤ tabCostTab r tc q c'
  | 0, _, _, h => h _
  | q + 1, _, _, h => htc fun _ => tabCostTab_mono r tc htc q fun _ => h _

/-- The charge of a tabulation is monotone in the costs. -/
theorem tabCost_mono : ∀ (f : FTy) {c c' : f.den → ℕ}, (∀ j, c j ≤ c' j) →
    tabCost f c ≤ tabCost f c'
  | .unit, _, _, h => h ()
  | .bool, _, _, h => Nat.add_le_add (h false) (h true)
  | .word n, _, _, h => tabCostFin_mono (2 ^ n) fun _ => h _
  | .fin n, _, _, h => tabCostFin_mono (n + 1) h
  | .tab q r, _, _, h => tabCostTab_mono r (tabCost r) (fun h' => tabCost_mono r h') q h

theorem tabCostFin_add : ∀ (n : ℕ) (c c' : Fin n → ℕ),
    tabCostFin n (fun i => c i + c' i) = tabCostFin n c + tabCostFin n c'
  | 0, _, _ => rfl
  | n + 1, c, c' => by
    simp only [tabCostFin, tabCostFin_add n (fun i => c i.succ) (fun i => c' i.succ)]
    omega

theorem tabCostTab_add (r : FTy) (tc : (r.den → ℕ) → ℕ)
    (htc : ∀ c c' : r.den → ℕ, tc (fun a => c a + c' a) = tc c + tc c') :
    ∀ (q : ℕ) (c c' : (Fin q → r.den) → ℕ),
      tabCostTab r tc q (fun v => c v + c' v) = tabCostTab r tc q c + tabCostTab r tc q c'
  | 0, _, _ => rfl
  | q + 1, c, c' => by
    simp only [tabCostTab, tabCostTab_add r tc htc q]
    exact htc _ _

/-- The charge of a tabulation is additive in the costs. -/
theorem tabCost_add : ∀ (f : FTy) (c c' : f.den → ℕ),
    tabCost f (fun j => c j + c' j) = tabCost f c + tabCost f c'
  | .unit, _, _ => rfl
  | .bool, c, c' => by simp only [tabCost]; omega
  | .word n, _, _ => tabCostFin_add (2 ^ n) _ _
  | .fin n, _, _ => tabCostFin_add (n + 1) _ _
  | .tab q r, _, _ => tabCostTab_add r (tabCost r) (tabCost_add r) q _ _

/-- A dependent tabulation of trees that are leaves after `m j` ticks is the leaf of their values
after `tabCost f m` ticks. -/
theorem tabDep_stepN (f : FTy) {X : f.den → Type} (d : (j : f.den) → X j)
    {g : (j : f.den) → CTree (X j)} {m : f.den → ℕ} {w : (j : f.den) → X j}
    (hg : ∀ j, g j = stepN CTree.tick (m j) (.ret (w j))) :
    tabDep f d g = stepN CTree.tick (tabCost f m) (.ret w) := by
  have ht := tabT_stepN f (g := fun j => (g j).bind fun x => .ret (⟨j, x⟩ : (j : f.den) × X j))
    (m := m) (w := fun j => ⟨j, w j⟩) fun j => by rw [hg j, Reflect.stepN_ret_bind]
  rw [tabDep, ht, Reflect.stepN_ret_bind]
  exact congrArg _ (congrArg CTree.ret (funext fun j => sigmaAt_mk (FTy.decEq f) d j (w j)))

/-- A constructor at an argument of D related to a translated argument: `R` holds of the nodes
that `mkH` and `mk` build from related fields and related children. -/
theorem conAt_sim {S₀ : Sig} {R : Ty.hat (.mu S₀) → Val (.mu S₀) → Prop} : ∀ (S : Sig)
    (mkH : (a : (c : S.Ctor) × S.hatF c) → (S.Pos a.1 → Ty.hat (.mu S₀)) → Ty.hat (.mu S₀))
    (mk : (a : (Sig.den S).A) → ((Sig.den S).B a → Val (.mu S₀)) → Val (.mu S₀)),
    (∀ (c : S.Ctor) (x : S.hatF c) (y : S.Fld c) (k : S.Pos c → Ty.hat (.mu S₀))
      (k' : S.Pos c → Val (.mu S₀)), Sig.SimF S c x y → (∀ p, Sim (.mu S₀) (k p) (k' p)) →
      R (mkH ⟨c, x⟩ k) (mk ⟨c, y⟩ k')) →
    ∀ {u : Ty.hat (S.conTy (.mu S₀))} {v : Val (S.conTy (.mu S₀))}, Sim _ u v →
      R (conHat S mkH u) (conAt S mk v)
  | .base _, _, _, hmk, _, _, hs => hmk () _ _ _ _ hs fun p => p.elim
  | .ext S a none, mkH, mk, hmk, u, v, hs => by
    have h' : Sum.LiftRel (Sim (S.conTy (.mu S₀))) (Sim a) u v := hs
    cases h' with
    | inl h =>
      exact conAt_sim S (fun b k => mkH ⟨.inl b.1, b.2⟩ k) (fun b k => mk ⟨.inl b.1, b.2⟩ k)
        (fun c x y k k' hxy hk => hmk (.inl c) x y k k' hxy hk) h
    | inr h => exact hmk (.inr ()) _ _ _ _ h fun p => p.elim
  | .ext S a (some f), mkH, mk, hmk, u, v, hs => by
    have h' : Sum.LiftRel (Sim (S.conTy (.mu S₀))) (Sim (.prod a (.pi f fun _ => .mu S₀))) u
        v := hs
    cases h' with
    | inl h =>
      exact conAt_sim S (fun b k => mkH ⟨.inl b.1, b.2⟩ k) (fun b k => mk ⟨.inl b.1, b.2⟩ k)
        (fun c x y k k' hxy hk => hmk (.inl c) x y k k' hxy hk) h
    | inr h => exact hmk (.inr ()) _ _ _ _ h.1 h.2

/-- A step of an eliminator at step functions related to translated step functions, at related
fields and children, at recursive results that are leaves within their costs: a leaf after at
most the cost of `stepHat`, related to its value. -/
theorem stepAt_sim {S₀ : Sig} {c : Ty} : ∀ (S : Sig)
    {p : Ty.hat (S.stepsTy (.mu S₀) c)} {g : Val (S.stepsTy (.mu S₀) c)}, Sim _ p g →
    ∀ {c₀ : S.Ctor} {x : S.hatF c₀} {y : S.Fld c₀}, Sig.SimF S c₀ x y →
    ∀ {kidsH : S.Pos c₀ → Ty.hat (.mu S₀)} {kids : S.Pos c₀ → Val (.mu S₀)},
      (∀ q, Sim (.mu S₀) (kidsH q) (kids q)) →
    ∀ {recD : S.Pos c₀ → CTree (Val c)} {recH : S.Pos c₀ → c.hat × ℕ},
      (∀ j, ∃ m w, recD j = stepN CTree.tick m (.ret w) ∧ m ≤ (recH j).2 ∧ Sim c (recH j).1 w) →
      ∃ m w, stepAt S g ⟨c₀, y⟩ kids recD = stepN CTree.tick m (.ret w) ∧
        m ≤ (stepHat S p ⟨c₀, x⟩ kidsH recH).2 ∧ Sim c (stepHat S p ⟨c₀, x⟩ kidsH recH).1 w
  | .base _, _, _, hpg, _, _, _, hxy, _, _, _, _, _, _ => hpg _ _ hxy
  | .ext S _ _, _, _, hpg, .inl _, _, _, hxy, _, _, hk, _, _, hr =>
    stepAt_sim S hpg.1 (c₀ := _) hxy hk hr
  | .ext _ _ none, _, _, hpg, .inr _, _, _, hxy, _, _, _, _, _, _ => hpg.2 _ _ hxy
  | .ext _ _ (some _), _, _, hpg, .inr _, _, _, hxy, _, _, hk, _, _, hr =>
    hpg.2 _ _ ⟨hxy, hk, fun j j' hj => by subst hj; exact hr j⟩

/-- The eliminator at step functions related to translated step functions, at related values:
a leaf after at most the cost of `foldHat`, related to its value. -/
theorem foldW_sim {S : Sig} {c : Ty} {p : Ty.hat (S.stepsTy (.mu S) c)}
    {g : Val (S.stepsTy (.mu S) c)} (hpg : Sim _ p g) {wH : Ty.hat (.mu S)} {w : Val (.mu S)}
    (hw : Sim (.mu S) wH w) :
    ∃ m v, foldW g w = stepN CTree.tick m (.ret v) ∧ m ≤ (foldHat p wH).2 ∧
      Sim c (foldHat p wH).1 v := by
  change Container.WLift (P := S.Pos) (Sig.SimF S) wH w at hw
  induction hw with
  | mk hxy hk ih => exact stepAt_sim S hpg hxy hk ih

/-- A constructor of a signature of an indexed family at an argument of D related to a translated
argument: `R` holds of the nodes that `mkH` and `mk` build from related fields and children. -/
theorem conAtI_sim {f : FTy} {X : f.den → Ty} {T U : Type} {R : T → U → Prop} : ∀ (S : ISig f)
    (mkH : (a : (c : S.Ctor) × S.hatF c) → ((p : S.Pos a.1) → Ty.hat (X (S.nx a.1 p))) → T)
    (mk : (a : (c : S.Ctor) × S.Fld c) → ((p : S.Pos a.1) → Val (X (S.nx a.1 p))) → U),
    (∀ (c : S.Ctor) (x : S.hatF c) (y : S.Fld c) (k : (p : S.Pos c) → Ty.hat (X (S.nx c p)))
      (k' : (p : S.Pos c) → Val (X (S.nx c p))), ISig.SimF S c x y →
      (∀ p, Sim _ (k p) (k' p)) → R (mkH ⟨c, x⟩ k) (mk ⟨c, y⟩ k')) →
    ∀ {u : Ty.hat (S.conTy X)} {v : Val (S.conTy X)}, Sim _ u v →
      R (conHatI S mkH u) (conAtI S mk v)
  | .base _, _, _, hmk, _, _, hs => hmk () _ _ _ _ hs fun p => p.elim
  | .ext S a none nx, mkH, mk, hmk, u, v, hs => by
    have h' : Sum.LiftRel (Sim (S.conTy X)) (Sim a) u v := hs
    cases h' with
    | inl h =>
      exact conAtI_sim S (fun b k => mkH ⟨.inl b.1, b.2⟩ k) (fun b k => mk ⟨.inl b.1, b.2⟩ k)
        (fun c x y k k' hxy hk => hmk (.inl c) x y k k' hxy hk) h
    | inr h => exact hmk (.inr ()) _ _ _ _ h fun p => p.elim
  | .ext S a (some g) nx, mkH, mk, hmk, u, v, hs => by
    have h' : Sum.LiftRel (Sim (S.conTy X)) (Sim (.prod a (.pi g fun p => X (nx p)))) u v := hs
    cases h' with
    | inl h =>
      exact conAtI_sim S (fun b k => mkH ⟨.inl b.1, b.2⟩ k) (fun b k => mk ⟨.inl b.1, b.2⟩ k)
        (fun c x y k k' hxy hk => hmk (.inl c) x y k k' hxy hk) h
    | inr h => exact hmk (.inr ()) _ _ _ _ h.1 h.2

/-- A step of an eliminator of an indexed family at step functions related to translated step
functions, at related fields and children, at recursive results that are leaves within their
costs: a leaf after at most the cost of `stepHatI`, related to its value. -/
theorem stepAtI_sim {f : FTy} {X c : f.den → Ty} {r : Ty} : ∀ (S : ISig f)
    {p : Ty.hat (S.stepsTy X c r)} {g : Val (S.stepsTy X c r)}, Sim _ p g →
    ∀ {c₀ : S.Ctor} {x : S.hatF c₀} {y : S.Fld c₀}, ISig.SimF S c₀ x y →
    ∀ {kidsH : (q : S.Pos c₀) → Ty.hat (X (S.nx c₀ q))}
      {kids : (q : S.Pos c₀) → Val (X (S.nx c₀ q))},
      (∀ q, Sim _ (kidsH q) (kids q)) →
    ∀ {recD : (q : S.Pos c₀) → CTree (Val (c (S.nx c₀ q)))}
      {recH : (q : S.Pos c₀) → (c (S.nx c₀ q)).hat × ℕ},
      (∀ q, ∃ m w, recD q = stepN CTree.tick m (.ret w) ∧ m ≤ (recH q).2 ∧ Sim _ (recH q).1 w) →
      ∃ m w, stepAtI S g ⟨c₀, y⟩ kids recD = stepN CTree.tick m (.ret w) ∧
        m ≤ (stepHatI S p ⟨c₀, x⟩ kidsH recH).2 ∧ Sim r (stepHatI S p ⟨c₀, x⟩ kidsH recH).1 w
  | .base _, _, _, hpg, _, _, _, hxy, _, _, _, _, _, _ => hpg _ _ hxy
  | .ext S _ none _, _, _, hpg, c₀, _, _, hxy, _, _, hk, _, _, hr => by
    cases c₀ with
    | inl c₀ => exact stepAtI_sim S hpg.1 (c₀ := c₀) hxy hk hr
    | inr _ => exact hpg.2 _ _ hxy
  | .ext S _ (some _) _, _, _, hpg, c₀, _, _, hxy, _, _, hk, _, _, hr => by
    cases c₀ with
    | inl c₀ => exact stepAtI_sim S hpg.1 (c₀ := c₀) hxy hk hr
    | inr _ =>
      refine hpg.2 _ _ ⟨hxy, hk, fun q u v _ => ?_⟩
      obtain ⟨m, w, he, hm, hw⟩ := hr q
      exact ⟨m, w, he, hm, hw⟩

/-- The eliminator of an indexed family at step functions related to translated step
functions, at related values: a leaf after at most the cost of `foldHatI`, related to its
value. -/
theorem foldIW_sim {f : FTy} {S : f.den → ISig f} {c : f.den → Ty}
    {p : (j : f.den) → Ty.hat ((S j).stepsTy (fun j' => .imu f S j') c (c j))}
    {g : (j : f.den) → Val ((S j).stepsTy (fun j' => .imu f S j') c (c j))}
    (hpg : Sim (.pi f fun j => (S j).stepsTy (fun j' => .imu f S j') c (c j)) p g) {i : f.den}
    {wH : Ty.hat (.imu f S i)} {w : Val (.imu f S i)} (hw : Sim (.imu f S i) wH w) :
    ∃ m v, foldIW g w = stepN CTree.tick m (.ret v) ∧ m ≤ (foldHatI p wH).2 ∧
      Sim (c i) (foldHatI p wH).1 v := by
  change Container.IWLift
      (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c)
      (nx := fun j c p => (S j).nx c p) (fun j c x y => ISig.SimF (S j) c x y) wH w at hw
  induction hw with
  | mk hxy hk ih => exact stepAtI_sim (S _) (hpg _) hxy hk ih

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
  | @con _ S x ih =>
    intro ht η ρ hρ
    have hev : (Tm.con x).eval ρ = (x.eval ρ).bind fun v =>
        .ret (conAt (X := .mu S) S (fun a k => (WType.mk a k : Val (.mu S))) v) := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := 0) (ih ht hρ) fun u v huv => ?_).mono
      (by simp only [allowC]; omega)
    have he : Sim (.mu S) _ _ := conAt_sim (R := Sim (.mu S)) S _ _
      (fun _ _ _ _ _ hxy hk => Container.WLift.mk hxy hk) huv
    exact TimedSim.stepN_ret (m := 0) he (by omega)
  | @fold _ S c g x ihg ihx =>
    intro ht η ρ hρ
    have hev : (Tm.fold g x).eval ρ = (g.eval ρ).bind fun gv =>
        (x.eval ρ).bind fun w => .tick (foldW gv w) := rfl
    rw [hev]
    refine (TimedSim.bindCont (ihg ht.1 hρ) fun p gv hpg =>
      TimedSim.bindCont (m := 0) (ihx ht.2 hρ) fun wH w hw => ?_).mono
      (by simp only [allowC]; omega)
    obtain ⟨m, v, he, hm, hv⟩ := foldW_sim hpg hw
    rw [show CTree.tick (foldW gv w) = stepN CTree.tick (m + 1) (.ret v) by rw [he]; rfl]
    exact TimedSim.stepN_ret hv (by omega)
  | @icon _ f S i x ih =>
    intro ht η ρ hρ
    have hev : (Tm.icon x).eval ρ = (x.eval ρ).bind fun v =>
        .ret (conAtI (X := fun j => .imu f S j) (S i)
          (fun a k => (Container.IPW.mk i a k : Val (.imu f S i))) v) := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := 0) (ih ht hρ) fun u v huv => ?_).mono
      (by simp only [allowC]; omega)
    have he : Sim (.imu f S i) _ _ := conAtI_sim (X := fun j => .imu f S j)
      (R := Sim (.imu f S i)) (S i) _ _
      (fun _ _ _ _ _ hxy hk => Container.IWLift.mk
          (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c) (nx := fun j c p => (S j).nx c p)
        (R := fun j c x y => ISig.SimF (S j) c x y) hxy hk) huv
    exact TimedSim.stepN_ret (m := 0) he (by omega)
  | @ifold _ f S c i g x ihg ihx =>
    intro ht η ρ hρ
    have hev : (Tm.ifold g x).eval ρ = (g.eval ρ).bind fun gv =>
        (x.eval ρ).bind fun w => .tick (foldIW (c := c) gv w) := rfl
    rw [hev]
    refine (TimedSim.bindCont (ihg ht.1 hρ) fun p gv hpg =>
      TimedSim.bindCont (m := 0) (ihx ht.2 hρ) fun wH w hw => ?_).mono
      (by simp only [allowC]; omega)
    obtain ⟨m, v, he, hm, hv⟩ := foldIW_sim hpg hw
    rw [show CTree.tick (foldIW gv w) = stepN CTree.tick (m + 1) (.ret v) by rw [he]; rfl]
    exact TimedSim.stepN_ret hv (by omega)
  | @ptab _ f B ts ih =>
    intro ht η ρ hρ
    have ht : ∀ j, (ts j).InDtFrag ∧ (ts j).Pure := ht
    have hk : ∀ j, ∃ (m : ℕ) (w : Val (B j)), (ts j).eval ρ = stepN CTree.tick m (.ret w) ∧
        m ≤ (ts j).allowC cc + ((ts j).dtC cc η).1 ∧
          Sim (B j) ((B j).pureVal ((ts j).dtC cc η).2) w := fun j => by
      obtain ⟨u, hu⟩ := dtC_pure cc (ts j) (ht j).2 η
      obtain ⟨m, w, he, hm, hw⟩ := TimedSim.ret_inv hu (ih j (ht j).1 hρ)
      refine ⟨m, w, he, by simpa using hm, ?_⟩
      rw [hu]
      exact hw
    choose m w he hm hw using hk
    have hev : (Tm.ptab ts).eval ρ = stepN CTree.tick (tabCost f m) (.ret w) :=
      tabDep_stepN f _ he
    rw [hev]
    refine TimedSim.stepN_ret (show Sim (.pi f B) _ w from hw) ?_
    have hle := tabCost_mono f hm
    rw [tabCost_add] at hle
    simp only [allowC]
    omega
  | @papp _ f B t j ih =>
    intro ht η ρ hρ
    have hev : (Tm.papp t j).eval ρ =
        (t.eval ρ).bind fun (v : (j : f.den) → Val (B j)) => .ret (v j) := rfl
    rw [hev]
    exact (TimedSim.bindCont (m := 0) (ih ht hρ) fun _ _ huv => TimedSim.ret (huv j)).mono
      (by simp only [allowC]; omega)
  | @spair _ f B j x ih =>
    intro ht η ρ hρ
    have hev : (Tm.spair j x).eval ρ =
        (x.eval ρ).bind fun v => .ret (⟨j, v⟩ : (j : f.den) × Val (B j)) := rfl
    rw [hev]
    exact (TimedSim.bindCont (m := 0) (ih ht hρ) fun _ _ huv =>
      TimedSim.ret (show Sim (.sig f B) ⟨j, _⟩ ⟨j, _⟩ from ⟨rfl, huv⟩)).mono
      (by simp only [allowC]; omega)
  | @scase _ f B c s ks ihs ihks =>
    intro ht η ρ hρ
    have hev : (Tm.scase s ks).eval ρ = (s.eval ρ).bind fun (v : (j : f.den) × Val (B j)) =>
        .tick ((ks v.1).eval (ρ.cons v.2)) := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := (Finset.univ.sup fun j => (ks j).allowC cc) + 0)
      (ihs ht.1 hρ) fun u v huv => ?_).mono (by simp only [allowC]; omega)
    change (j : f.den) × Ty.hat (B j) at u
    change (j : f.den) × Val (B j) at v
    obtain ⟨i, x⟩ := u
    obtain ⟨j, y⟩ := v
    change ∃ e : i = j, Sim (B j) (e ▸ x) y at huv
    obtain ⟨rfl, hxy⟩ := huv
    refine TimedSim.delay_tick_le ?_ (by omega)
    exact (ihks i (ht.2 i) (hρ.cons hxy)).mono
      (Finset.le_sup (f := fun j => (ks j).allowC cc) (Finset.mem_univ i))
  | @fcase _ f c i ks ihi ihks =>
    intro ht η ρ hρ
    have hev : (Tm.fcase i ks).eval ρ =
        (i.eval ρ).bind fun (j : f.den) => .tick ((ks j).eval ρ) := rfl
    rw [hev]
    refine (TimedSim.bindCont (m := (Finset.univ.sup fun j => (ks j).allowC cc) + 0)
      (ihi ht.1 hρ) fun u v huv => ?_).mono (by simp only [allowC]; omega)
    change f.den at u v
    have huv' : u = v := huv
    subst huv'
    refine TimedSim.delay_tick_le ?_ (by omega)
    exact (ihks u (ht.2 u) hρ).mono
      (Finset.le_sup (f := fun j => (ks j).allowC cc) (Finset.mem_univ u))

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
