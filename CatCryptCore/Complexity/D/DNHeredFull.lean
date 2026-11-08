/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.DNHered
public import CatCryptCore.Complexity.D.OpenTree

/-!
# The Diller–Nahm function space with call demands

The hereditary Diller–Nahm object `Ty.dnObjH τ` of a type of D has, at a function type
`arr a b`, the shapes of the Diller–Nahm function space with a clock: a Diller–Nahm morphism
`DNLens a.dnObjH b.dnObjH` (a forward map and, at each argument and each position of the result,
the finite multiset of positions of the argument that the position demands, the call demand) and
a cost at each argument. Its positions at a shape are a data token, a clock tick, and the call
tokens `⟨u, z⟩`, an argument `u` with a position `z` of the result (Diller–Nahm 1974; Pédrot,
LICS 2014). At the other types the shapes are the translated values `Ty.hat` and the positions a
data token and a clock tick, as in `Ty.dn`.

The Dialectica predicate `Ty.simPredH τ v s y` holds at a data token when `Sim` relates the
translated value of `s` (`Ty.forget`) to `v`, at a clock tick always, and at a call token
`⟨u, z⟩` of a function `g` when at every value `v` satisfying the predicate of the argument at
the positions that the shape demands for `z`, `g v` is a leaf after at most the cost of `s` at
`u`, at a value satisfying the predicate of the result at `z`. The predicate at the call tokens
of a shape is the Dialectica soundness (equation (9) of Moss and von Glehn) of the morphism of
the application (`Ty.forall_simPredH_call_iff_dnSound`).

A translated value is a hereditary shape by `Ty.lift`, which demands of an argument its data
token and the clock ticks of the cost; `Ty.forget` reads the translated value back
(`Ty.forget_lift`). `Sim` is the predicate of the lifted shape at every position
(`Ty.forall_simPredH_lift_iff`), at every argument type, and `Sim` at a function type is the
soundness of the morphism of the application of the lifted closure (`Sim.arr_iff_dnSoundH`).
The translation `Tm.dtH` is the costed tree of lifted values of `Tm.dtC`, and `Tm.dtC` is its
image under `Ty.forget` (`Tm.dtH_forget`).

The shape `Tm.costedH` of an abstraction refines the lifted closure by the call demand of its
body (`Ty.argDem`): a body of the fragment is pure and calls no variable of function type, so its
demand on an argument of function type has no call token, and on an argument of any other type it
is the data token. The evaluation of a pure term of the fragment reads only the variables that
are not of function type (`Tm.interp_congr`), and the morphism of an abstraction with this demand
is sound at every argument type (`Tm.dnHH_sound`).

## Main definitions

* `Ty.dnObjH`, `Ty.hatH`, `Ty.posH`: the hereditary object with the call demands
* `Ty.forget`, `Ty.lift`: translated values and hereditary shapes
* `Ty.simPredH`: the Dialectica predicate of a value
* `Ty.appDNH`, `Tm.dtH`: the morphism of an application and the translation
* `Ty.argDem`, `Tm.costedH`, `Tm.dnHH`: the call demand of a pure body, the shape of an
  abstraction and its morphism

## Main results

* `Ty.forget_lift`: lifting and forgetting gives back the translated value
* `Ty.forall_simPredH_lift_iff`: `Sim` is the predicate of the lifted shape at every position
* `Ty.forall_simPredH_call_iff_dnSound`: the predicate at the call tokens is equation (9)
* `Sim.arr_iff_dnSoundH`: `Sim` at a function type, at every argument type, is the soundness of
  the morphism of the application of the lifted closure
* `Tm.dtH_forget`: the translation followed by `Ty.forget` is `Tm.dtC`
* `Tm.interp_congr`: a pure term of the fragment reads only the variables of data type
* `Tm.dnHH_sound`: the soundness of the morphism of an abstraction at every argument type

## References

* J. Diller, *Eine Variante zur Dialectica-Interpretation der Heyting-Arithmetik endlicher
  Typen*, Arch. Math. Logik 16 (1974);
* P.-M. Pédrot, *A functional functional interpretation*, LICS 2014;
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core CatCrypt.Container

/-! ## The hereditary object with call demands -/

/-- The hereditary Diller–Nahm object of a type of D. At a function type `arr a b` its shapes are
a Diller–Nahm morphism from the object of `a` to the object of `b` (a forward map and a call
demand) with a cost at each argument, and its positions at a shape are a data token
(`.inl false`), a clock tick (`.inl true`) and the call tokens `.inr ⟨u, z⟩`. At the other types
its shapes are the translated values and its positions a data token (`false`) and a clock tick
(`true`). -/
def Ty.dnObjH : Ty → PFunctor.{0, 0}
  | .arr a b => ⟨DNLens (Ty.dnObjH a) (Ty.dnObjH b) × ((Ty.dnObjH a).A → ℕ),
      fun s => Bool ⊕ Σ u, (Ty.dnObjH b).B (s.1.toFunA u)⟩
  | .base f => ⟨Ty.hat (.base f), fun _ => Bool⟩
  | .nat => ⟨Ty.hat .nat, fun _ => Bool⟩
  | .prod a b => ⟨Ty.hat (.prod a b), fun _ => Bool⟩
  | .sum a b => ⟨Ty.hat (.sum a b), fun _ => Bool⟩
  | .list a => ⟨Ty.hat (.list a), fun _ => Bool⟩
  | .mu S => ⟨Ty.hat (.mu S), fun _ => Bool⟩
  | .pi f B => ⟨Ty.hat (.pi f B), fun _ => Bool⟩
  | .sig f B => ⟨Ty.hat (.sig f B), fun _ => Bool⟩
  | .imu f S i => ⟨Ty.hat (.imu f S i), fun _ => Bool⟩

/-- The hereditary shapes of a type. -/
abbrev Ty.hatH (τ : Ty) : Type := (Ty.dnObjH τ).A

/-- The hereditary positions at a shape. -/
abbrev Ty.posH (τ : Ty) (s : τ.hatH) : Type := (Ty.dnObjH τ).B s

/-- The data token at a shape. -/
def Ty.dtokH : (τ : Ty) → (s : τ.hatH) → τ.posH s
  | .arr _ _, _ => .inl false
  | .base _, _ => false
  | .nat, _ => false
  | .prod _ _, _ => false
  | .sum _ _, _ => false
  | .list _, _ => false
  | .mu _, _ => false
  | .pi _ _, _ => false
  | .sig _ _, _ => false
  | .imu _ _ _, _ => false

/-- The clock tick at a shape. -/
def Ty.tickH : (τ : Ty) → (s : τ.hatH) → τ.posH s
  | .arr _ _, _ => .inl true
  | .base _, _ => true
  | .nat, _ => true
  | .prod _ _, _ => true
  | .sum _ _, _ => true
  | .list _, _ => true
  | .mu _, _ => true
  | .pi _ _, _ => true
  | .sig _ _, _ => true
  | .imu _ _ _, _ => true

/-- The translated value of a hereditary shape and the hereditary shape of a translated value.
At a function type the translated closure of a shape is its forward map and cost at the lifted
arguments, and the shape of a translated closure demands, at each position of the result, the
data token of the argument and the clock ticks of the cost. -/
def Ty.forgetLift : (τ : Ty) → (τ.hatH → τ.hat) × (τ.hat → τ.hatH)
  | .arr a b =>
    (fun s => (fun u => (Ty.forgetLift b).1 (s.1.toFunA ((Ty.forgetLift a).2 u)),
        fun u => s.2 ((Ty.forgetLift a).2 u)),
      fun p => (⟨fun u => (Ty.forgetLift b).2 (p.1 ((Ty.forgetLift a).1 u)),
        fun u _ => {Ty.dtokH a u} + p.2 ((Ty.forgetLift a).1 u) • {Ty.tickH a u}⟩,
        fun u => p.2 ((Ty.forgetLift a).1 u)))
  | .base _ => (id, id)
  | .nat => (id, id)
  | .prod _ _ => (id, id)
  | .sum _ _ => (id, id)
  | .list _ => (id, id)
  | .mu _ => (id, id)
  | .pi _ _ => (id, id)
  | .sig _ _ => (id, id)
  | .imu _ _ _ => (id, id)

/-- The translated value of a hereditary shape. -/
def Ty.forget (τ : Ty) : τ.hatH → τ.hat := (Ty.forgetLift τ).1

/-- The hereditary shape of a translated value: at a function type the demand of a position of
the result is the data token of the argument and the clock ticks of the cost. -/
def Ty.lift (τ : Ty) : τ.hat → τ.hatH := (Ty.forgetLift τ).2

/-- **Lifting and forgetting gives back the translated value.** -/
theorem Ty.forget_lift : ∀ (τ : Ty) (u : τ.hat), τ.forget (τ.lift u) = u
  | .arr a b, p => by
    have ha := Ty.forget_lift a
    have hb := Ty.forget_lift b
    change ((fun u => b.forget (b.lift (p.1 (a.forget (a.lift u))))),
      fun u => p.2 (a.forget (a.lift u))) = p
    simp only [ha, hb]
    rfl
  | .base _, _ => rfl
  | .nat, _ => rfl
  | .prod _ _, _ => rfl
  | .sum _ _, _ => rfl
  | .list _, _ => rfl
  | .mu _, _ => rfl
  | .pi _ _, _ => rfl
  | .sig _ _, _ => rfl
  | .imu _ _ _, _ => rfl

/-! ## The Dialectica predicate -/

/-- The Dialectica predicate of a value of D on the hereditary object: at a data token `Sim` of
the translated value of the shape, at a clock tick `True`, and at a call token `⟨u, z⟩` of a
function `g` with shape `s`: at every value `v` satisfying the predicate of the argument at the
positions that `s` demands for `z`, `g v` is a leaf after at most the cost of `s` at `u`, at a
value satisfying the predicate of the result at `z`. -/
def Ty.simPredH : (τ : Ty) → Val τ → (s : τ.hatH) → τ.posH s → Prop
  | .arr a b, g, s, .inl false => Sim (.arr a b) (Ty.forget (.arr a b) s) g
  | .arr _ _, _, _, .inl true => True
  | .arr a b, g, s, .inr ⟨u, z⟩ => ∀ v, (∀ x ∈ s.1.toFunB u z, Ty.simPredH a v u x) →
      ∃ m w, g v = stepN CTree.tick m (.ret w) ∧ m ≤ s.2 u ∧ Ty.simPredH b w (s.1.toFunA u) z
  | .base f, v, s, y => y = false → Sim (.base f) s v
  | .nat, v, s, y => y = false → Sim .nat s v
  | .prod a b, v, s, y => y = false → Sim (.prod a b) s v
  | .sum a b, v, s, y => y = false → Sim (.sum a b) s v
  | .list a, v, s, y => y = false → Sim (.list a) s v
  | .mu S, v, s, y => y = false → Sim (.mu S) s v
  | .pi f B, v, s, y => y = false → Sim (.pi f B) s v
  | .sig f B, v, s, y => y = false → Sim (.sig f B) s v
  | .imu f S i, v, s, y => y = false → Sim (.imu f S i) s v

/-- The predicate at the data token is `Sim` of the translated value. -/
theorem Ty.simPredH_dtokH :
    ∀ (τ : Ty) {v : Val τ} {s : τ.hatH}, τ.simPredH v s (τ.dtokH s) ↔ Sim τ (τ.forget s) v
  | .arr _ _, _, _ => Iff.rfl
  | .base _, _, _ => ⟨fun h => h rfl, fun h _ => h⟩
  | .nat, _, _ => ⟨fun h => h rfl, fun h _ => h⟩
  | .prod _ _, _, _ => ⟨fun h => h rfl, fun h _ => h⟩
  | .sum _ _, _, _ => ⟨fun h => h rfl, fun h _ => h⟩
  | .list _, _, _ => ⟨fun h => h rfl, fun h _ => h⟩
  | .mu _, _, _ => ⟨fun h => h rfl, fun h _ => h⟩
  | .pi _ _, _, _ => ⟨fun h => h rfl, fun h _ => h⟩
  | .sig _ _, _, _ => ⟨fun h => h rfl, fun h _ => h⟩
  | .imu _ _ _, _, _ => ⟨fun h => h rfl, fun h _ => h⟩

/-- The predicate holds at the clock tick. -/
theorem Ty.simPredH_tickH : ∀ (τ : Ty) (v : Val τ) (s : τ.hatH), τ.simPredH v s (τ.tickH s)
  | .arr _ _, _, _ => trivial
  | .base _, _, _ => fun h => absurd h Bool.noConfusion
  | .nat, _, _ => fun h => absurd h Bool.noConfusion
  | .prod _ _, _, _ => fun h => absurd h Bool.noConfusion
  | .sum _ _, _, _ => fun h => absurd h Bool.noConfusion
  | .list _, _, _ => fun h => absurd h Bool.noConfusion
  | .mu _, _, _ => fun h => absurd h Bool.noConfusion
  | .pi _ _, _, _ => fun h => absurd h Bool.noConfusion
  | .sig _ _, _, _ => fun h => absurd h Bool.noConfusion
  | .imu _ _ _, _, _ => fun h => absurd h Bool.noConfusion

/-- The data token demanded by a lifted closure gives `Sim` of the argument. -/
theorem Ty.sim_of_forall_lift_dem {a b : Ty} {p : Ty.hat (.arr a b)} {u : a.hatH}
    {z : b.posH ((Ty.lift (.arr a b) p).1.toFunA u)} {v : Val a}
    (hv : ∀ x ∈ (Ty.lift (.arr a b) p).1.toFunB u z, a.simPredH v u x) :
    Sim a (a.forget u) v :=
  (Ty.simPredH_dtokH a).1 (hv _ (Multiset.mem_add.2 (.inl (Multiset.mem_singleton_self _))))

/-- A value related to the translated argument satisfies the predicate at the positions demanded
by a lifted closure: its data token and the clock ticks of the cost. -/
theorem Ty.forall_lift_dem_of_sim {a b : Ty} {p : Ty.hat (.arr a b)} {u : a.hatH}
    {z : b.posH ((Ty.lift (.arr a b) p).1.toFunA u)} {v : Val a} (h : Sim a (a.forget u) v) :
    ∀ x ∈ (Ty.lift (.arr a b) p).1.toFunB u z, a.simPredH v u x := by
  intro x hx
  change x ∈ {a.dtokH u} + _ • {a.tickH u} at hx
  rcases Multiset.mem_add.1 hx with hx | hx
  · rw [Multiset.mem_singleton.1 hx]
    exact (Ty.simPredH_dtokH a).2 h
  · rw [Multiset.nsmul_singleton] at hx
    rw [Multiset.eq_of_mem_replicate hx]
    exact Ty.simPredH_tickH a v u

/-- `Sim` gives the predicate of the lifted shape at every position. -/
theorem Ty.simPredH_lift :
    ∀ (τ : Ty) {u : τ.hat} {v : Val τ}, Sim τ u v → ∀ y, τ.simPredH v (τ.lift u) y
  | .arr a b, p, g, h, .inl false => by
    change Sim (.arr a b) (Ty.forget (.arr a b) (Ty.lift (.arr a b) p)) g
    rw [Ty.forget_lift]
    exact h
  | .arr _ _, _, _, _, .inl true => trivial
  | .arr _ b, _, _, h, .inr ⟨_, z⟩ => fun v hv => by
    obtain ⟨m, w, h1, h2, h3⟩ := h _ v (Ty.sim_of_forall_lift_dem hv)
    exact ⟨m, w, h1, h2, Ty.simPredH_lift b h3 z⟩
  | .base _, _, _, h, _ => fun _ => h
  | .nat, _, _, h, _ => fun _ => h
  | .prod _ _, _, _, h, _ => fun _ => h
  | .sum _ _, _, _, h, _ => fun _ => h
  | .list _, _, _, h, _ => fun _ => h
  | .mu _, _, _, h, _ => fun _ => h
  | .pi _ _, _, _, h, _ => fun _ => h
  | .sig _ _, _, _, h, _ => fun _ => h
  | .imu _ _ _, _, _, h, _ => fun _ => h

/-- **`Sim` is the Dialectica predicate of the lifted shape at every position**, at every
type. -/
theorem Ty.forall_simPredH_lift_iff (τ : Ty) {u : τ.hat} {v : Val τ} :
    (∀ y, τ.simPredH v (τ.lift u) y) ↔ Sim τ u v := by
  refine ⟨fun h => ?_, fun h => Ty.simPredH_lift τ h⟩
  have := (Ty.simPredH_dtokH τ).1 (h (τ.dtokH _))
  rwa [Ty.forget_lift] at this

/-! ## The glued objects and the morphism of an application -/

/-- The glued object of a type: a hereditary shape and a value of D as shape, the positions of
the hereditary shape as positions. -/
abbrev Ty.dnGH (τ : Ty) : PFunctor.{0, 0} := ⟨τ.hatH × Val τ, fun s => τ.posH s.1⟩

/-- The Dialectica predicate of the glued object. -/
def Ty.predGH (τ : Ty) : CwF.Pred τ.dnGH := fun s y => τ.simPredH s.2 s.1 y

/-- The glued computation object of a type: a cost, a hereditary shape and a tree of D as shape,
the positions of the hereditary shape as positions. -/
abbrev Ty.dnGCH (τ : Ty) : PFunctor.{0, 0} :=
  ⟨ℕ × τ.hatH × CTree (Val τ), fun s => τ.posH s.2.1⟩

/-- The Dialectica predicate of the glued computation object: the tree is a leaf after at most
the cost, at a value whose predicate holds at the shape. -/
def Ty.predGCH (τ : Ty) : CwF.Pred τ.dnGCH := fun s y =>
  ∃ m w, s.2.2 = stepN CTree.tick m (.ret w) ∧ m ≤ s.1 ∧ τ.simPredH w s.2.1 y

/-- The Diller–Nahm morphism of a hereditary shape `s` of a function type applied to a function
`g` of D: forward the cost, the forward map and the tree of `g`; backward the call demand of
`s`. -/
def Ty.appDNH {a b : Ty} (s : (Ty.arr a b).hatH) (g : Val (.arr a b)) :
    DNLens a.dnGH b.dnGCH where
  toFunA x := (s.2 x.1, s.1.toFunA x.1, g x.2)
  toFunB x y := s.1.toFunB x.1 y

/-- **The predicate at the call tokens is equation (9)** of Moss and von Glehn for the morphism
of the application. -/
theorem Ty.forall_simPredH_call_iff_dnSound {a b : Ty} (s : (Ty.arr a b).hatH)
    (g : Val (.arr a b)) :
    (∀ u z, (Ty.arr a b).simPredH g s (.inr ⟨u, z⟩)) ↔
      CwF.DNSound a.predGH b.predGCH (Ty.appDNH s g) :=
  ⟨fun h x y hx => h x.1 y x.2 hx, fun h u z v hv => h (u, v) z hv⟩

/-- **`Sim` at a function type, at every argument type, is the Dialectica soundness of the
morphism of the application of the lifted closure.** -/
theorem Sim.arr_iff_dnSoundH {a b : Ty} {p : Ty.hat (.arr a b)} {g : Val (.arr a b)} :
    Sim (.arr a b) p g ↔
      CwF.DNSound a.predGH b.predGCH (Ty.appDNH (Ty.lift (.arr a b) p) g) := by
  rw [← Ty.forall_simPredH_call_iff_dnSound]
  constructor
  · intro h u z
    exact Ty.simPredH_lift (.arr a b) h (.inr ⟨u, z⟩)
  · intro h u v huv
    have hu : Sim a (a.forget (a.lift u)) v := by rwa [Ty.forget_lift]
    have hd := fun z => h (a.lift u) z v (Ty.forall_lift_dem_of_sim hu)
    obtain ⟨m, w, h1, h2, -⟩ := hd (b.dtokH _)
    refine ⟨m, w, h1, ?_, ?_⟩
    · change m ≤ p.2 (a.forget (a.lift u)) at h2
      rwa [Ty.forget_lift] at h2
    · have hall : ∀ z, b.simPredH w (b.lift (p.1 (a.forget (a.lift u)))) z := fun z => by
        obtain ⟨m', w', h1', -, h3'⟩ := hd z
        obtain ⟨-, rfl⟩ := stepN_tick_ret_inj (h1.symm.trans h1')
        exact h3'
      rw [Ty.forget_lift] at hall
      exact (Ty.forall_simPredH_lift_iff b).1 hall

/-! ## The translation -/

namespace Tm

variable {Γ : List Ty} {σ τ : Ty}

/-- The translation of a term into hereditary shapes: the costed tree `Tm.dtC` with its leaves
lifted. -/
noncomputable def dtH (cc : Ty → ℕ) (t : Tm Γ τ) (η : EnvHat Γ) : ℕ × SPTree.Timed τ.hatH :=
  ((t.dtC cc η).1, ((t.dtC cc η).2.map τ.lift fun _ => 0).2)

/-- **The translation followed by `Ty.forget` is `Tm.dtC`.** -/
theorem dtH_forget (cc : Ty → ℕ) (t : Tm Γ τ) (η : EnvHat Γ) :
    ((t.dtH cc η).1, ((t.dtH cc η).2.map τ.forget fun _ => 0).2) = t.dtC cc η := by
  simp only [dtH, SPTree.Timed.map, SPTree.Timed.bind_ret_bind, Ty.forget_lift]
  grind [SPTree.Timed.bind_ret]

/-- Unfolding lemma of `Tm.dtH` at an abstraction: the lifted costed function of its body. -/
theorem dtH_lam (cc : Ty → ℕ) (t : Tm (σ :: Γ) τ) (η : EnvHat Γ) :
    (Tm.lam t).dtH cc η = (0, .ret (Ty.lift (.arr σ τ) (t.costedC cc η))) :=
  rfl

end Tm

/-! ## Pure terms read only the data variables -/

/-- Two environments of D agree at the variables that are not of function type. -/
def Env.AgreeData {Δ : List Ty} (ρ ρ' : Env Δ) : Prop :=
  ∀ τ (x : Var Δ τ), τ.isArr = false → ρ τ x = ρ' τ x

/-- Agreement at the variables that are not of function type is kept by an extension. -/
theorem Env.AgreeData.cons {Δ : List Ty} {σ : Ty} {ρ ρ' : Env Δ} (h : ρ.AgreeData ρ')
    (v : Val σ) : (ρ.cons v).AgreeData (ρ'.cons v) := by
  intro τ x hx
  cases x with
  | here => rfl
  | there y => exact h _ y hx

/-- **A pure term of the fragment reads only the variables that are not of function type**: its
evaluation in two environments that agree at those variables is the same tree. -/
theorem Tm.interp_congr (tk : ∀ {α : Type}, CTree α → CTree α) {Δ : List Ty} {τ : Ty}
    (t : Tm Δ τ) :
    t.InDtFrag → t.Pure → ∀ {ρ ρ' : Env Δ}, ρ.AgreeData ρ' → t.interp tk ρ = t.interp tk ρ' := by
  induction t with
  | var x => intro _ hp ρ ρ' h; simp only [Tm.interp, h _ x hp]
  | lam body ih =>
    intro ht _ ρ ρ' h
    have hb : ∀ v, body.interp tk (ρ.cons v) = body.interp tk (ρ'.cons v) :=
      fun v => ih ht.1 ht.2 (h.cons v)
    simp only [Tm.interp, hb]
  | app f x ihf ihx =>
    intro ht hp ρ ρ' h
    have hf : f.InDtFrag := by simpa [hp.1] using ht.1
    simp only [Tm.interp, ihf hf hp.2.1 h, ihx ht.2 hp.2.2 h]
  | letE e b ihe ihb =>
    intro ht hp ρ ρ' h
    have hb : ∀ v, b.interp tk (ρ.cons v) = b.interp tk (ρ'.cons v) :=
      fun v => ihb ht.2 hp.2 (h.cons v)
    simp only [Tm.interp, ihe ht.1 hp.1 h, hb]
  | seq e b ihe ihb =>
    intro ht hp ρ ρ' h
    simp only [Tm.interp, ihe ht.1 hp.1 h, ihb ht.2 hp.2 h]
  | natLit n => intro _ _ ρ ρ' _; rfl
  | lit f v => intro _ _ ρ ρ' _; rfl
  | prim p x ih => intro ht hp ρ ρ' h; simp only [Tm.interp, ih ht.2 hp h]
  | pair x y ihx ihy =>
    intro ht hp ρ ρ' h; simp only [Tm.interp, ihx ht.1 hp.1 h, ihy ht.2 hp.2 h]
  | fst p ih => intro ht hp ρ ρ' h; simp only [Tm.interp, ih ht hp h]
  | snd p ih => intro ht hp ρ ρ' h; simp only [Tm.interp, ih ht hp h]
  | inl x ih => intro ht hp ρ ρ' h; simp only [Tm.interp, ih ht hp h]
  | inr x ih => intro ht hp ρ ρ' h; simp only [Tm.interp, ih ht hp h]
  | case s l r ihs ihl ihr =>
    intro ht hp ρ ρ' h
    have hl : ∀ v, l.interp tk (ρ.cons v) = l.interp tk (ρ'.cons v) :=
      fun v => ihl ht.2.1 hp.2.1 (h.cons v)
    have hr : ∀ v, r.interp tk (ρ.cons v) = r.interp tk (ρ'.cons v) :=
      fun v => ihr ht.2.2 hp.2.2 (h.cons v)
    simp only [Tm.interp, ihs ht.1 hp.1 h, hl, hr]
  | ite c t e ihc iht ihe =>
    intro ht hp ρ ρ' h
    simp only [Tm.interp, ihc ht.1 hp.1 h, iht ht.2.1 hp.2.1 h, ihe ht.2.2 hp.2.2 h]
  | nil => intro _ _ ρ ρ' _; rfl
  | cons x xs ihx ihxs =>
    intro ht hp ρ ρ' h; simp only [Tm.interp, ihx ht.1 hp.1 h, ihxs ht.2 hp.2 h]
  | lcase xs n c ihxs ihn ihc =>
    intro ht hp ρ ρ' h
    have hc : ∀ x l', c.interp tk ((ρ.cons l').cons x) = c.interp tk ((ρ'.cons l').cons x) :=
      fun x l' => ihc ht.2.2 hp.2.2 ((h.cons l').cons x)
    simp only [Tm.interp, ihxs ht.1 hp.1 h, ihn ht.2.1 hp.2.1 h]
    refine congrArg (CTree.bind _) (funext fun l => ?_)
    exact congrArg (fun t => tk t) (congrArg (listCase l _) (funext fun x => funext (hc x)))
  | foldl f i xs ihf ihi ihxs =>
    intro ht hp ρ ρ' h
    simp only [Tm.interp, ihf ht.1 hp.1 h, ihi ht.2.1 hp.2.1 h, ihxs ht.2.2 hp.2.2 h]
  | iter n f i ihn ihf ihi =>
    intro ht hp ρ ρ' h
    simp only [Tm.interp, ihn ht.1 hp.1 h, ihf ht.2.1 hp.2.1 h, ihi ht.2.2 hp.2.2 h]
  | sample f => intro _ hp; exact hp.elim
  | get n f => intro _ hp; exact hp.elim
  | set n f x _ => intro _ hp; exact hp.elim
  | query d r x _ => intro _ hp; exact hp.elim
  | fail => intro _ hp; exact hp.elim
  | con x ih => intro ht hp ρ ρ' h; simp only [Tm.interp, ih ht hp h]
  | fold g x ihg ihx =>
    intro ht hp ρ ρ' h; simp only [Tm.interp, ihg ht.1 hp.1 h, ihx ht.2 hp.2 h]
  | icon x ih => intro ht hp ρ ρ' h; simp only [Tm.interp, ih ht hp h]
  | ifold g x ihg ihx =>
    intro ht hp ρ ρ' h; simp only [Tm.interp, ihg ht.1 hp.1 h, ihx ht.2 hp.2 h]
  | ptab ts ih =>
    intro ht hp ρ ρ' h
    have hts : ∀ j, (ts j).interp tk ρ = (ts j).interp tk ρ' := fun j => ih j (ht j).1 (hp j) h
    simp only [Tm.interp]
    exact congrArg (tabDep _ _) (funext hts)
  | papp t j ih => intro ht hp ρ ρ' h; simp only [Tm.interp, ih ht hp h]
  | spair j x ih => intro ht hp ρ ρ' h; simp only [Tm.interp, ih ht hp h]
  | scase s ks ihs ihks =>
    intro ht hp ρ ρ' h
    have hks : ∀ j v, (ks j).interp tk (ρ.cons v) = (ks j).interp tk (ρ'.cons v) :=
      fun j v => ihks j (ht.2 j) (hp.2 j) (h.cons v)
    simp only [Tm.interp, ihs ht.1 hp.1 h, hks]
  | fcase i ks ihi ihks =>
    intro ht hp ρ ρ' h
    have hks : ∀ j, (ks j).interp tk ρ = (ks j).interp tk ρ' :=
      fun j => ihks j (ht.2 j) (hp.2 j) h
    simp only [Tm.interp, ihi ht.1 hp.1 h, hks]

/-! ## The shape of an abstraction with its call demand -/

/-- A type that is a function type is `arr a b`. -/
theorem Ty.exists_eq_arr_of_isArr : ∀ σ : Ty, σ.isArr = true → ∃ a b, σ = .arr a b
  | .arr a b, _ => ⟨a, b, rfl⟩
  | .base _, h => Bool.noConfusion h
  | .nat, h => Bool.noConfusion h
  | .prod _ _, h => Bool.noConfusion h
  | .sum _ _, h => Bool.noConfusion h
  | .list _, h => Bool.noConfusion h
  | .mu _, h => Bool.noConfusion h
  | .pi _ _, h => Bool.noConfusion h
  | .sig _ _, h => Bool.noConfusion h
  | .imu _ _ _, h => Bool.noConfusion h

/-- The call demand of a pure body of the fragment on its argument: no call token at an argument
of function type, which a pure body does not call, and the data token at any other type. -/
def Ty.argDem : (σ : Ty) → (u : σ.hatH) → Multiset (σ.posH u)
  | .arr _ _, _ => 0
  | .base _, _ => {false}
  | .nat, _ => {false}
  | .prod _ _, _ => {false}
  | .sum _ _, _ => {false}
  | .list _, _ => {false}
  | .mu _, _ => {false}
  | .pi _ _, _ => {false}
  | .sig _ _, _ => {false}
  | .imu _ _ _, _ => {false}

/-- The call demand of a pure body is at most the data token. -/
theorem Ty.argDem_le : ∀ (σ : Ty) (u : σ.hatH), σ.argDem u ≤ {σ.dtokH u}
  | .arr _ _, _ => Multiset.zero_le _
  | .base _, _ => le_rfl
  | .nat, _ => le_rfl
  | .prod _ _, _ => le_rfl
  | .sum _ _, _ => le_rfl
  | .list _, _ => le_rfl
  | .mu _, _ => le_rfl
  | .pi _ _, _ => le_rfl
  | .sig _ _, _ => le_rfl
  | .imu _ _ _, _ => le_rfl

/-- The predicate of a value at the call demand of a pure body: the argument type is a function
type, or the value is related to the translated argument. -/
theorem Ty.isArr_or_sim_of_argDem : ∀ (σ : Ty) {u : σ.hatH} {v : Val σ},
    (∀ x ∈ σ.argDem u, σ.simPredH v u x) → σ.isArr = true ∨ Sim σ (σ.forget u) v
  | .arr _ _, _, _, _ => .inl rfl
  | .base _, _, _, h => .inr (h false (Multiset.mem_singleton_self _) rfl)
  | .nat, _, _, h => .inr (h false (Multiset.mem_singleton_self _) rfl)
  | .prod _ _, _, _, h => .inr (h false (Multiset.mem_singleton_self _) rfl)
  | .sum _ _, _, _, h => .inr (h false (Multiset.mem_singleton_self _) rfl)
  | .list _, _, _, h => .inr (h false (Multiset.mem_singleton_self _) rfl)
  | .mu _, _, _, h => .inr (h false (Multiset.mem_singleton_self _) rfl)
  | .pi _ _, _, _, h => .inr (h false (Multiset.mem_singleton_self _) rfl)
  | .sig _ _, _, _, h => .inr (h false (Multiset.mem_singleton_self _) rfl)
  | .imu _ _ _, _, _, h => .inr (h false (Multiset.mem_singleton_self _) rfl)

namespace Tm

variable {Γ : List Ty} {σ τ : Ty}

/-- The hereditary shape of the abstraction of a term: the lifted costed function of the term,
whose demand at each position of the result is the call demand `Ty.argDem` of the body on its
argument and the clock ticks of the cost. -/
noncomputable def costedH (cc : Ty → ℕ) (t : Tm (σ :: Γ) τ) (η : EnvHat Γ) :
    (Ty.arr σ τ).hatH :=
  (⟨fun u => τ.lift ((t.costedC cc η).1 (σ.forget u)),
    fun u _ => σ.argDem u + (t.costedC cc η).2 (σ.forget u) • {σ.tickH u}⟩,
    fun u => (t.costedC cc η).2 (σ.forget u))

/-- The translated value of the shape of an abstraction is its costed function. -/
theorem forget_costedH (cc : Ty → ℕ) (t : Tm (σ :: Γ) τ) (η : EnvHat Γ) :
    (Ty.arr σ τ).forget (t.costedH cc η) = t.costedC cc η := by
  change ((fun u => τ.forget (τ.lift ((t.costedC cc η).1 (σ.forget (σ.lift u))))),
    fun u => (t.costedC cc η).2 (σ.forget (σ.lift u))) = t.costedC cc η
  simp only [Ty.forget_lift]

/-- The call demand of the shape of an abstraction is at most the demand of its lifted costed
function. -/
theorem costedH_toFunB_le (cc : Ty → ℕ) (t : Tm (σ :: Γ) τ) (η : EnvHat Γ) (u : σ.hatH)
    (z : τ.posH ((t.costedH cc η).1.toFunA u)) :
    (t.costedH cc η).1.toFunB u z ≤ (Ty.lift (.arr σ τ) (t.costedC cc η)).1.toFunB u z :=
  add_le_add (Ty.argDem_le σ u) le_rfl

/-- The Diller–Nahm morphism of a term in the context of one more variable, at a translated
environment and an environment of D of the others: the morphism of the application of the shape
of its abstraction and of its closure. -/
noncomputable def dnHH (cc : Ty → ℕ) (t : Tm (σ :: Γ) τ) (η : EnvHat Γ) (ρ : Env Γ) :
    DNLens σ.dnGH τ.dnGCH :=
  Ty.appDNH (t.costedH cc η) fun v => t.eval (ρ.cons v)

/-- A pure body of the fragment at a function-type argument: at every value of the argument, its
evaluation is a leaf after at most the cost of its costed function, at a value related to the
value of its costed function. -/
theorem costedC_eval_arr (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) {a b : Ty}
    (t : Tm (.arr a b :: Γ) τ) (ht : t.InDtFrag) (hp : t.Pure) {η : EnvHat Γ} {ρ : Env Γ}
    (hρ : SimEnv η ρ) (u : Ty.hat (.arr a b)) (v : Val (.arr a b)) :
    ∃ m w, t.eval (ρ.cons v) = stepN CTree.tick m (.ret w) ∧ m ≤ (t.costedC cc η).2 u ∧
      Sim τ ((t.costedC cc η).1 u) w := by
  have hE : SimE (.arr a b) (fun _ => (0, .fail)) (Val.default (.arr a b)) :=
    fun _ _ _ => TimedSimTree.fail
  have h1 := dtC_timedSim cc hcc t ht (hρ.consE hE)
  have h2 : t.dtC cc (η.consE fun _ => (0, .fail)) = t.dtC cc (η.cons u) := by
    refine dtC_congr cc t ht hp ?_
    intro τ' x hx
    cases x with
    | here => exact absurd hx (by simp [Ty.isArr])
    | there y => rfl
  have h3 : t.eval (ρ.cons (Val.default (.arr a b))) = t.eval (ρ.cons v) := by
    refine Tm.interp_congr _ t ht hp ?_
    intro τ' x hx
    cases x with
    | here => exact absurd hx (by simp [Ty.isArr])
    | there y => rfl
  rw [h2, h3] at h1
  obtain ⟨w₀, hw₀⟩ := dtC_pure cc t hp (η.cons u)
  obtain ⟨m, w, he, hm, hs⟩ := TimedSim.ret_inv hw₀ h1
  refine ⟨m, w, he, ?_, ?_⟩
  · change m ≤ t.allowC cc + (t.dtC cc (η.cons u)).1
    omega
  · change Sim τ (τ.pureVal (t.dtC cc (η.cons u)).2) w
    rw [hw₀]
    exact hs

/-- A pure body of the fragment at a function-type argument, or at a value related to the
argument: its evaluation is a leaf after at most the cost of its costed function, at a value
related to the value of its costed function. -/
theorem costedC_eval (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) (t : Tm (σ :: Γ) τ) (ht : t.InDtFrag)
    (hp : t.Pure) {η : EnvHat Γ} {ρ : Env Γ} (hρ : SimEnv η ρ) {u : σ.hat} {v : Val σ}
    (h : σ.isArr = true ∨ Sim σ u v) :
    ∃ m w, t.eval (ρ.cons v) = stepN CTree.tick m (.ret w) ∧ m ≤ (t.costedC cc η).2 u ∧
      Sim τ ((t.costedC cc η).1 u) w := by
  rcases h with h | h
  · obtain ⟨a, b, rfl⟩ := Ty.exists_eq_arr_of_isArr σ h
    exact costedC_eval_arr cc hcc t ht hp hρ u v
  · have hl : TimedSimTree (Sim (.arr σ τ)) 1 _ (.ret (t.costedC cc η))
        (.ret fun v => t.eval (ρ.cons v)) := dtC_timedSim cc hcc (Tm.lam t) ⟨ht, hp⟩ hρ
    cases hl with
    | ret hs => exact hs u v h

/-- **Soundness at every argument type.** The Diller–Nahm morphism of a pure term of the
fragment in the context of one more variable, of any type, in related environments, with the
call demand of the body on its argument, satisfies equation (9) of Moss and von Glehn at the
Dialectica predicates. -/
theorem dnHH_sound (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) (t : Tm (σ :: Γ) τ) (ht : t.InDtFrag)
    (hp : t.Pure) {η : EnvHat Γ} {ρ : Env Γ} (hρ : SimEnv η ρ) :
    CwF.DNSound σ.predGH τ.predGCH (t.dnHH cc η ρ) := by
  intro x y hx
  have hσ := Ty.isArr_or_sim_of_argDem σ fun q hq => hx q (Multiset.mem_add.2 (.inl hq))
  obtain ⟨m, w, h1, h2, h3⟩ := costedC_eval cc hcc t ht hp hρ hσ
  exact ⟨m, w, h1, h2, Ty.simPredH_lift τ h3 y⟩

end Tm

end CatCrypt.Complexity.D
