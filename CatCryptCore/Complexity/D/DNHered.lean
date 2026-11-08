/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.PriceSound
public import CatCryptCore.Container.CwFPi

/-!
# The hereditary Diller–Nahm object of a type of D

The hereditary Diller–Nahm object `Ty.dnH τ` of a type of D has the translated values `τ.hat` as
shapes. Its positions (`Ty.dnPos`) are defined by recursion on the type: at a product the sum of
the positions of the components, at a sum the positions of the summand of the shape, at a function
type `arr a b` at a costed closure `p` a clock tick of the closure (`none`) or a call token
`⟨u, z⟩`, an argument `u` with a position `z` of the result `p.1 u` (the position type of the
function space of the Diller–Nahm model, as in Pédrot's functional Dialectica interpretation), and
at the other types a data token (`false`) and a clock tick (`true`), as `Ty.dn`.

The Dialectica predicate `Ty.simPred τ v` of a value `v` of D holds at a data token of a data type
when the shape is related to `v` by `Sim`, at a clock tick always, componentwise at products and
sums, and at a call token `⟨u, z⟩` of a function `g` when at every value `v` that satisfies the
predicate of the argument type at every position of `u`, `g v` is a leaf after at most the cost
`p.2 u` of the closure, at a value that satisfies the predicate of the result at `z`. `Sim` is this
predicate at every position (`Ty.sim_iff_forall_simPred`).

At a first-order argument type the demand of a call is finite: the data tokens `Ty.dataToks a u`
of the argument (`Ty.forall_dataToks_iff`). The Diller–Nahm morphism of a costed closure applied
to a function of D (`Ty.appDN`) goes from the glued object of the argument (`Ty.dnG`, a translated
value and a value) to the glued computation object of the result (`Ty.dnGC`, a cost, a translated
value and a tree), and demands, at each position of the result, the data tokens of the argument and
the clock ticks of the cost. `Sim` at the function type is the Dialectica soundness (equation (9)
of Moss and von Glehn, `CwF.DNSound`) of this morphism (`Sim.arr_iff_dnSound`), and the soundness
theorem of D at an abstraction is the soundness of the morphism `Tm.dnH` of a pure term of the
fragment in the context of one first-order variable (`Tm.dnH_sound`).

## Main definitions

* `Ty.dnPos`, `Ty.dnH`, `Ty.tick`, `Ty.dataToks`: the hereditary object
* `Ty.simPred`: the Dialectica predicate of a value
* `Ty.dnG`, `Ty.predG`, `Ty.dnGC`, `Ty.predGC`: the glued objects of values and computations
* `Ty.appDN`, `Tm.dnH`: the morphisms of an application and of a term

## Main results

* `Ty.sim_iff_forall_simPred`: `Sim` is the Dialectica predicate at every position
* `Ty.forall_dataToks_iff`: at a first-order type, `Sim` is the predicate at the data tokens
* `Sim.arr_iff_dnSound`: `Sim` at a function type with a first-order argument is the Dialectica
  soundness of the morphism of the application
* `Tm.dnH_sound`: the soundness theorem of the morphism of a pure term

## References

* P.-M. Pédrot, *A functional functional interpretation*, LICS 2014;
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018;
* J. Diller, *Eine Variante zur Dialectica-Interpretation der Heyting-Arithmetik endlicher
  Typen*, Arch. Math. Logik 16 (1974).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Container

/-! ## The hereditary object -/

/-- The positions of the hereditary Diller–Nahm object at a translated value: at a product the sum
of the positions of the components, at a sum those of the summand, at a function type a clock tick
of the closure (`none`) or a call token, an argument with a position of the result, and at the
other types a data token (`false`) and a clock tick (`true`). -/
def Ty.dnPos : (τ : Ty) → τ.hat → Type
  | .base _, _ => Bool
  | .nat, _ => Bool
  | .prod a b, u => Ty.dnPos a u.1 ⊕ Ty.dnPos b u.2
  | .sum a b, u => Sum.elim (Ty.dnPos a) (Ty.dnPos b) u
  | .arr a b, p => Option (Σ u : a.hat, Ty.dnPos b (p.1 u))
  | .list _, _ => Bool
  | .mu _, _ => Bool
  | .pi _ _, _ => Bool
  | .sig _ _, _ => Bool
  | .imu _ _ _, _ => Bool

/-- The hereditary Diller–Nahm object of a type of D: translated values as shapes, the hereditary
positions `Ty.dnPos` as positions. -/
abbrev Ty.dnH (τ : Ty) : PFunctor.{0, 0} := ⟨τ.hat, τ.dnPos⟩

/-- The clock tick at a shape: the tick of the first component at a product, of the summand at a
sum, the tick `none` of a closure at a function type. -/
def Ty.tick : (τ : Ty) → (u : τ.hat) → τ.dnPos u
  | .base _, _ => true
  | .nat, _ => true
  | .prod a _, u => .inl (Ty.tick a u.1)
  | .sum a _, .inl x => Ty.tick a x
  | .sum _ b, .inr y => Ty.tick b y
  | .arr _ _, _ => none
  | .list _, _ => true
  | .mu _, _ => true
  | .pi _ _, _ => true
  | .sig _ _, _ => true
  | .imu _ _ _, _ => true

/-- The data tokens at a shape: the data tokens of both components at a product, of the summand at
a sum, none at a function type, and the data token `false` at the other types. -/
def Ty.dataToks : (τ : Ty) → (u : τ.hat) → Multiset (τ.dnPos u)
  | .base _, _ => {false}
  | .nat, _ => {false}
  | .prod a b, u => (Ty.dataToks a u.1).map Sum.inl + (Ty.dataToks b u.2).map Sum.inr
  | .sum a _, .inl x => Ty.dataToks a x
  | .sum _ b, .inr y => Ty.dataToks b y
  | .arr _ _, _ => 0
  | .list _, _ => {false}
  | .mu _, _ => {false}
  | .pi _ _, _ => {false}
  | .sig _ _, _ => {false}
  | .imu _ _ _, _ => {false}

/-! ## The Dialectica predicate -/

/-- The Dialectica predicate of a value of D on the hereditary object: at a data token of a data
type `Sim`, at a clock tick of a data type and of a closure `True`, componentwise at products and
sums, and at a call token `⟨u, z⟩` of a function `g` with costed closure `p`: at every value `v`
satisfying the predicate of the argument at every position of `u`, `g v` is a leaf after at most
`p.2 u` steps at a value satisfying the predicate of the result at `z`. -/
def Ty.simPred : (τ : Ty) → Val τ → (u : τ.hat) → τ.dnPos u → Prop
  | .base f, v, u, y => y = false → Sim (.base f) u v
  | .nat, v, u, y => y = false → Sim .nat u v
  | .prod a _, v, u, .inl y => Ty.simPred a v.1 u.1 y
  | .prod _ b, v, u, .inr y => Ty.simPred b v.2 u.2 y
  | .sum a _, .inl v, .inl u, y => Ty.simPred a v u y
  | .sum _ b, .inr v, .inr u, y => Ty.simPred b v u y
  | .sum _ _, .inl _, .inr _, _ => False
  | .sum _ _, .inr _, .inl _, _ => False
  | .arr _ _, _, _, none => True
  | .arr a b, g, p, some ⟨u, z⟩ => ∀ v, (∀ x, Ty.simPred a v u x) →
      ∃ m w, g v = stepN CTree.tick m (.ret w) ∧ m ≤ p.2 u ∧ Ty.simPred b w (p.1 u) z
  | .list a, v, u, y => y = false → Sim (.list a) u v
  | .mu S, v, u, y => y = false → Sim (.mu S) u v
  | .pi f B, v, u, y => y = false → Sim (.pi f B) u v
  | .sig f B, v, u, y => y = false → Sim (.sig f B) u v
  | .imu f S i, v, u, y => y = false → Sim (.imu f S i) u v

/-- Ticks in front of a leaf determine the number of ticks and the leaf. -/
theorem stepN_tick_ret_inj {α : Type} :
    ∀ {m m' : ℕ} {w w' : α}, stepN CTree.tick m (.ret w) = stepN CTree.tick m' (.ret w') →
      m = m' ∧ w = w'
  | 0, 0, _, _, h => ⟨rfl, CTree.ret.inj h⟩
  | 0, _ + 1, _, _, h => by cases h
  | _ + 1, 0, _, _, h => by cases h
  | _ + 1, _ + 1, _, _, h => by
    obtain ⟨h1, h2⟩ := stepN_tick_ret_inj (CTree.tick.inj h)
    exact ⟨congrArg (· + 1) h1, h2⟩

/-- **`Sim` is the Dialectica predicate at every position** of the hereditary object. -/
theorem Ty.sim_iff_forall_simPred :
    ∀ (τ : Ty) {u : τ.hat} {v : Val τ}, Sim τ u v ↔ ∀ y, τ.simPred v u y
  | .prod a b, _, _ =>
    (and_congr (Ty.sim_iff_forall_simPred a) (Ty.sim_iff_forall_simPred b)).trans
      ⟨fun h y => by rcases y with y | y; exacts [h.1 y, h.2 y],
        fun h => ⟨fun y => h (.inl y), fun y => h (.inr y)⟩⟩
  | .sum a _, .inl _, .inl _ => Sum.liftRel_inl_inl.trans (Ty.sim_iff_forall_simPred a)
  | .sum a _, .inl u, .inr _ =>
    ⟨fun h => absurd h Sum.not_liftRel_inl_inr, fun h => (h (Ty.tick a u)).elim⟩
  | .sum _ b, .inr u, .inl _ =>
    ⟨fun h => absurd h Sum.not_liftRel_inr_inl, fun h => (h (Ty.tick b u)).elim⟩
  | .sum _ b, .inr _, .inr _ => Sum.liftRel_inr_inr.trans (Ty.sim_iff_forall_simPred b)
  | .arr a b, _, _ => by
    have iha := @Ty.sim_iff_forall_simPred a
    have ihb := @Ty.sim_iff_forall_simPred b
    constructor
    · intro h y
      rcases y with _ | ⟨u, z⟩
      · trivial
      · intro v hv
        obtain ⟨m, w, h1, h2, h3⟩ := h u v (iha.2 hv)
        exact ⟨m, w, h1, h2, ihb.1 h3 z⟩
    · intro h u v huv
      obtain ⟨m, w, h1, h2, -⟩ := h (some ⟨u, Ty.tick b _⟩) v (iha.1 huv)
      refine ⟨m, w, h1, h2, ihb.2 fun z => ?_⟩
      obtain ⟨m', w', h1', -, h3'⟩ := h (some ⟨u, z⟩) v (iha.1 huv)
      obtain ⟨-, rfl⟩ := stepN_tick_ret_inj (h1.symm.trans h1')
      exact h3'
  | .base _, _, _ => ⟨fun h _ _ => h, fun h => h false rfl⟩
  | .nat, _, _ => ⟨fun h _ _ => h, fun h => h false rfl⟩
  | .list _, _, _ => ⟨fun h _ _ => h, fun h => h false rfl⟩
  | .mu _, _, _ => ⟨fun h _ _ => h, fun h => h false rfl⟩
  | .pi _ _, _, _ => ⟨fun h _ _ => h, fun h => h false rfl⟩
  | .sig _ _, _, _ => ⟨fun h _ _ => h, fun h => h false rfl⟩
  | .imu _ _ _, _, _ => ⟨fun h _ _ => h, fun h => h false rfl⟩

/-- At a first-order type the data tokens of a shape are not empty. -/
theorem Ty.dataToks_ne_zero : ∀ (τ : Ty), τ.FO → ∀ u : τ.hat, τ.dataToks u ≠ 0
  | .prod a b, h, u => fun h0 => by
    have hle : (a.dataToks u.1).map (Sum.inl (β := b.dnPos u.2)) ≤ 0 :=
      (Multiset.le_add_right _ ((b.dataToks u.2).map Sum.inr)).trans h0.le
    exact Ty.dataToks_ne_zero a h.1 u.1 (Multiset.map_eq_zero.1 (Multiset.le_zero.1 hle))
  | .sum a _, h, .inl u => Ty.dataToks_ne_zero a h.1 u
  | .sum _ b, h, .inr u => Ty.dataToks_ne_zero b h.2 u
  | .arr _ _, h, _ => h.elim
  | .base _, _, _ => Multiset.singleton_ne_zero _
  | .nat, _, _ => Multiset.singleton_ne_zero _
  | .list _, _, _ => Multiset.singleton_ne_zero _
  | .mu _, _, _ => Multiset.singleton_ne_zero _
  | .pi _ _, _, _ => Multiset.singleton_ne_zero _
  | .sig _ _, _, _ => Multiset.singleton_ne_zero _
  | .imu _ _ _, _, _ => Multiset.singleton_ne_zero _

/-- **At a first-order type `Sim` is the predicate at the data tokens.** -/
theorem Ty.forall_dataToks_iff : ∀ (τ : Ty), τ.FO → ∀ {u : τ.hat} {v : Val τ},
    (∀ x ∈ τ.dataToks u, τ.simPred v u x) ↔ Sim τ u v
  | .prod a b, h, _, _ => by
    refine Iff.trans ?_
      (and_congr (Ty.forall_dataToks_iff a h.1) (Ty.forall_dataToks_iff b h.2))
    change (∀ x ∈ (Ty.dataToks a _).map Sum.inl + (Ty.dataToks b _).map Sum.inr, _) ↔ _
    refine ⟨fun hx => ⟨fun x hx' => hx (.inl x) (Multiset.mem_add.2
        (.inl (Multiset.mem_map_of_mem _ hx'))), fun x hx' => hx (.inr x) (Multiset.mem_add.2
        (.inr (Multiset.mem_map_of_mem _ hx')))⟩, fun hx x hx' => ?_⟩
    rcases Multiset.mem_add.1 hx' with hx' | hx'
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx'
      exact hx.1 y hy
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx'
      exact hx.2 y hy
  | .sum a _, h, .inl _, .inl _ =>
    (Ty.forall_dataToks_iff a h.1).trans Sum.liftRel_inl_inl.symm
  | .sum a _, h, .inl u, .inr _ => by
    refine ⟨fun hx => ?_, fun h' => absurd h' Sum.not_liftRel_inl_inr⟩
    obtain ⟨x, hx'⟩ := Multiset.exists_mem_of_ne_zero (Ty.dataToks_ne_zero a h.1 u)
    exact (hx x hx').elim
  | .sum _ b, h, .inr u, .inl _ => by
    refine ⟨fun hx => ?_, fun h' => absurd h' Sum.not_liftRel_inr_inl⟩
    obtain ⟨x, hx'⟩ := Multiset.exists_mem_of_ne_zero (Ty.dataToks_ne_zero b h.2 u)
    exact (hx x hx').elim
  | .sum _ b, h, .inr _, .inr _ =>
    (Ty.forall_dataToks_iff b h.2).trans Sum.liftRel_inr_inr.symm
  | .arr _ _, h, _, _ => h.elim
  | .base _, _, _, _ => ⟨fun h => h false (Multiset.mem_singleton_self _) rfl, fun h _ _ _ => h⟩
  | .nat, _, _, _ => ⟨fun h => h false (Multiset.mem_singleton_self _) rfl, fun h _ _ _ => h⟩
  | .list _, _, _, _ => ⟨fun h => h false (Multiset.mem_singleton_self _) rfl, fun h _ _ _ => h⟩
  | .mu _, _, _, _ => ⟨fun h => h false (Multiset.mem_singleton_self _) rfl, fun h _ _ _ => h⟩
  | .pi _ _, _, _, _ => ⟨fun h => h false (Multiset.mem_singleton_self _) rfl, fun h _ _ _ => h⟩
  | .sig _ _, _, _, _ => ⟨fun h => h false (Multiset.mem_singleton_self _) rfl, fun h _ _ _ => h⟩
  | .imu _ _ _, _, _, _ =>
    ⟨fun h => h false (Multiset.mem_singleton_self _) rfl, fun h _ _ _ => h⟩

/-! ## The glued objects and the morphism of an application -/

/-- The glued object of a type: a translated value and a value of D as shape, the hereditary
positions of the translated value as positions. -/
abbrev Ty.dnG (τ : Ty) : PFunctor.{0, 0} := ⟨τ.hat × Val τ, fun s => τ.dnPos s.1⟩

/-- The Dialectica predicate of the glued object: `Ty.simPred` of the value at the translated
value. -/
def Ty.predG (τ : Ty) : CwF.Pred τ.dnG := fun s y => τ.simPred s.2 s.1 y

/-- The glued computation object of a type: a cost, a translated value and a tree of D as shape,
the hereditary positions of the translated value as positions. -/
abbrev Ty.dnGC (τ : Ty) : PFunctor.{0, 0} := ⟨ℕ × τ.hat × CTree (Val τ), fun s => τ.dnPos s.2.1⟩

/-- The Dialectica predicate of the glued computation object: the tree is a leaf after at most the
cost, at a value whose predicate holds at the translated value. -/
def Ty.predGC (τ : Ty) : CwF.Pred τ.dnGC := fun s y =>
  ∃ m w, s.2.2 = stepN CTree.tick m (.ret w) ∧ m ≤ s.1 ∧ τ.simPred w s.2.1 y

/-- The Diller–Nahm morphism of a costed closure `p` applied to a function `g` of D: forward the
cost, the translated result and the tree of `g`; backward, at every position of the result, the
data tokens of the argument and the clock ticks of the cost. -/
def Ty.appDN {a b : Ty} (p : Costed a.hat b.hat) (g : Val a → CTree (Val b)) :
    DNLens a.dnG b.dnGC where
  toFunA s := (p.2 s.1, p.1 s.1, g s.2)
  toFunB s _ := a.dataToks s.1 + p.2 s.1 • {a.tick s.1}

/-- The number of positions demanded by a position of the result: the data tokens of the argument
and the cost. -/
theorem Ty.card_appDN_toFunB {a b : Ty} (p : Costed a.hat b.hat) (g : Val a → CTree (Val b))
    (s : a.hat × Val a) (y : b.dnPos (p.1 s.1)) :
    Multiset.card ((Ty.appDN p g).toFunB s y) = Multiset.card (a.dataToks s.1) + p.2 s.1 := by
  simp [Ty.appDN]

/-- **`Sim` at a function type with a first-order argument is the Dialectica soundness of the
morphism of the application.** -/
theorem Sim.arr_iff_dnSound {a b : Ty} (ha : a.FO) {p : Ty.hat (.arr a b)}
    {g : Val (.arr a b)} :
    Sim (.arr a b) p g ↔ CwF.DNSound a.predG b.predGC (Ty.appDN p g) := by
  constructor
  · intro h s y hx
    have hs : Sim a s.1 s.2 :=
      (Ty.forall_dataToks_iff a ha).1 fun x hx' => hx x (Multiset.mem_add.2 (.inl hx'))
    obtain ⟨m, w, h1, h2, h3⟩ := h s.1 s.2 hs
    exact ⟨m, w, h1, h2, (Ty.sim_iff_forall_simPred b).1 h3 y⟩
  · intro h u v huv
    have hx : ∀ x ∈ (Ty.appDN p g).toFunB (u, v) (Ty.tick b (p.1 u)), a.predG (u, v) x :=
      fun x _ => (Ty.sim_iff_forall_simPred a).1 huv x
    obtain ⟨m, w, h1, h2, -⟩ := h (u, v) _ hx
    refine ⟨m, w, h1, h2, (Ty.sim_iff_forall_simPred b).2 fun z => ?_⟩
    obtain ⟨m', w', h1', -, h3'⟩ := h (u, v) z fun x _ => (Ty.sim_iff_forall_simPred a).1 huv x
    obtain ⟨-, rfl⟩ := stepN_tick_ret_inj (h1.symm.trans h1')
    exact h3'

/-! ## The morphism of a term -/

namespace Tm

variable {Γ : List Ty} {σ τ : Ty}

/-- The Diller–Nahm morphism of a term in the context of one more variable, at a translated
environment and an environment of D of the others: the morphism of the application of its costed
function and its closure. -/
noncomputable def dnH (cc : Ty → ℕ) (t : Tm (σ :: Γ) τ) (η : EnvHat Γ) (ρ : Env Γ) :
    DNLens σ.dnG τ.dnGC :=
  Ty.appDN (t.costedC cc η) fun v => t.eval (ρ.cons v)

/-- **Soundness.** The Diller–Nahm morphism of a pure term of the fragment in the context of a
first-order variable, in related environments, satisfies equation (9) of Moss and von Glehn at
the Dialectica predicates of `Sim`: the soundness theorem `dtC_timedSim` at the abstraction of the
term. -/
theorem dnH_sound (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) (t : Tm (σ :: Γ) τ) (ht : t.InDtFrag)
    (hp : t.Pure) (hσ : σ.FO) {η : EnvHat Γ} {ρ : Env Γ} (hρ : SimEnv η ρ) :
    CwF.DNSound σ.predG τ.predGC (t.dnH cc η ρ) := by
  have h : TimedSimTree (Sim (.arr σ τ)) 1 _ (.ret (t.costedC cc η))
      (.ret fun v => t.eval (ρ.cons v)) := dtC_timedSim cc hcc (Tm.lam t) ⟨ht, hp⟩ hρ
  cases h with
  | ret hs => exact (Sim.arr_iff_dnSound hσ).1 hs

end Tm

end CatCrypt.Complexity.D
