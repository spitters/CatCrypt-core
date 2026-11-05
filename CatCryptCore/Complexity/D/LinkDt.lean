/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.TranslateDt

/-!
# A costed tree above the charges of `Tm.dt`, and the simulation it inherits

`TreeLe S A B` states that the costed tree `B` has the nodes of `A` in the same order, with
leaves related by `S` and every step cost of `B` at least the step cost of `A` at the same
place; `CostLe S x y` adds the step cost in front. A costed tree above another simulates what
the other simulates (`TimedSimTree.of_treeLe`, `TimedSim.of_costLe`). With the soundness theorem
`Tm.dt_timedSim` this gives `Tm.timedSim_of_costLe`: a costed tree `X` above `t.dt η` simulates
the evaluation of `t` at the allowance `t.allow`, with leaves equal to the values of D. This is
the theorem through which `link_timed` proves the simulation of a definition in the fragment of
`Tm.dt_timedSim`: per definition only `CostLe` between the costed form of `derive_timed` and
`t.dt η` remains, a comparison of two costed trees of the same shape.

At a first-order type, translated values and values of D are the same type (`Ty.hat_eq_val`)
and related exactly when they are equal up to the cast (`Sim.cast_eq`, `Sim.cast_self`). At a
concrete type the cast is the identity by definitional unfolding. The translated environment of
a telescope is built from `EnvHat.nil` and `EnvHat.consE` with the entries `dataEntry` for a data
function and `treeEntry` for a tree function, related to their D values by `SimE.dataEntry` and
`SimE.treeEntry`.

## Main definitions

* `TreeLe`, `CostLe`
* `EnvHat.nil`, `EnvHat.consE`, `dataEntry`, `treeEntry`

## Main results

* `TimedSimTree.of_treeLe`, `TimedSim.of_costLe`, `CostLe.bind`, `TreeLe.refl`
* `foldl_timedCost_mono`: the registered cost of `List.foldl` is monotone in the step cost
* `Ty.hat_eq_val`, `Sim.cast_eq`, `Sim.cast_self`
* `SimEnv.nil`, `SimEnv.consE`, `SimE.dataEntry`, `SimE.treeEntry`
* `Tm.timedSim_of_costLe`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core

/-! ## Costed trees above costed trees -/

/-- `TreeLe S A B`: the costed tree `B` has the nodes of `A` in the same order, the leaves are
related by `S`, and every step cost of `B` is at least the step cost of `A` at the same place. -/
inductive TreeLe {α β : Type} (S : α → β → Prop) : SPTree.Timed α → SPTree.Timed β → Prop where
  /-- Related leaves. -/
  | ret {a : α} {b : β} (h : S a b) : TreeLe S (.ret a) (.ret b)
  /-- Samples of the same type. -/
  | sample {γ : Type} {finγ finγ' : Fintype γ} {neγ neγ' : Nonempty γ} {c c' : γ → ℕ}
      {k : γ → SPTree.Timed α} {k' : γ → SPTree.Timed β} (hc : ∀ x, c x ≤ c' x)
      (hk : ∀ x, TreeLe S (k x) (k' x)) :
      TreeLe S (.sample γ finγ neγ c k) (.sample γ finγ' neγ' c' k')
  /-- Samples of the same distribution. -/
  | sampleDist {γ : Type} {μ : Prob.SDistr γ} {c c' : γ → ℕ} {k : γ → SPTree.Timed α}
      {k' : γ → SPTree.Timed β} (hc : ∀ x, c x ≤ c' x) (hk : ∀ x, TreeLe S (k x) (k' x)) :
      TreeLe S (.sampleDist γ μ c k) (.sampleDist γ μ c' k')
  /-- Reads of the same location. -/
  | get {l : Location} {c c' : l.ty → ℕ} {k : l.ty → SPTree.Timed α}
      {k' : l.ty → SPTree.Timed β} (hc : ∀ x, c x ≤ c' x) (hk : ∀ x, TreeLe S (k x) (k' x)) :
      TreeLe S (.get l c k) (.get l c' k')
  /-- Writes of the same value to the same location. -/
  | set {l : Location} {v : l.ty} {c c' : ℕ} {A : SPTree.Timed α} {B : SPTree.Timed β}
      (hc : c ≤ c') (hk : TreeLe S A B) : TreeLe S (.set l v c A) (.set l v c' B)
  /-- Failure. -/
  | fail : TreeLe S .fail .fail
  /-- Loads of the same heap. -/
  | load {h₀ : Heap} {c c' : ℕ} {A : SPTree.Timed α} {B : SPTree.Timed β}
      (hc : c ≤ c') (hk : TreeLe S A B) : TreeLe S (.load h₀ c A) (.load h₀ c' B)

/-- `CostLe S x y`: the step cost in front of `y` is at least the one of `x`, and the tree of `y`
is above the tree of `x` (`TreeLe`). -/
def CostLe {α β : Type} (S : α → β → Prop) (x : ℕ × SPTree.Timed α)
    (y : ℕ × SPTree.Timed β) : Prop :=
  x.1 ≤ y.1 ∧ TreeLe S x.2 y.2

namespace TreeLe

variable {α β : Type}

/-- A costed tree is above itself when its leaves are related to themselves. -/
theorem refl {S : α → α → Prop} (hS : ∀ a, S a a) : ∀ A : SPTree.Timed α, TreeLe S A A
  | .ret a => .ret (hS a)
  | .sample _ _ _ _ k => .sample (fun _ => le_rfl) fun x => refl hS (k x)
  | .sampleDist _ _ _ k => .sampleDist (fun _ => le_rfl) fun x => refl hS (k x)
  | .get _ _ k => .get (fun _ => le_rfl) fun x => refl hS (k x)
  | .set _ _ _ A => .set le_rfl (refl hS A)
  | .fail => .fail
  | .load _ _ A => .load le_rfl (refl hS A)

end TreeLe

theorem CostLe.mk {α β : Type} {S : α → β → Prop} {c c' : ℕ} {A : SPTree.Timed α}
    {B : SPTree.Timed β} (hc : c ≤ c') (h : TreeLe S A B) : CostLe S (c, A) (c', B) :=
  ⟨hc, h⟩

/-- The step costs in front of costed trees above each other. -/
theorem CostLe.fst_le {α β : Type} {S : α → β → Prop} {x : ℕ × SPTree.Timed α}
    {y : ℕ × SPTree.Timed β} (h : CostLe S x y) : x.1 ≤ y.1 :=
  h.1

/-- The trees of costed trees above each other. -/
theorem CostLe.tree {α β : Type} {S : α → β → Prop} {x : ℕ × SPTree.Timed α}
    {y : ℕ × SPTree.Timed β} (h : CostLe S x y) : TreeLe S x.2 y.2 :=
  h.2

/-- Binds of trees with equal leaves and continuations above each other. -/
theorem CostLe.bind {α γ δ : Type} {S : γ → δ → Prop} {A A' : SPTree.Timed α}
    {k : α → ℕ × SPTree.Timed γ} {k' : α → ℕ × SPTree.Timed δ}
    (hA : TreeLe (fun a b => a = b) A A') (hk : ∀ a, CostLe S (k a) (k' a)) :
    CostLe S (A.bind k) (A'.bind k') := by
  induction hA with
  | ret h => subst h; exact hk _
  | sample hc _ ih =>
    exact ⟨le_rfl, .sample (fun x => Nat.add_le_add (hc x) (ih x).1) fun x => (ih x).2⟩
  | sampleDist hc _ ih =>
    exact ⟨le_rfl, .sampleDist (fun x => Nat.add_le_add (hc x) (ih x).1) fun x => (ih x).2⟩
  | get hc _ ih =>
    exact ⟨le_rfl, .get (fun x => Nat.add_le_add (hc x) (ih x).1) fun x => (ih x).2⟩
  | set hc _ ih => exact ⟨le_rfl, .set (Nat.add_le_add hc ih.1) ih.2⟩
  | fail => exact ⟨le_rfl, .fail⟩
  | load hc _ ih => exact ⟨le_rfl, .load (Nat.add_le_add hc ih.1) ih.2⟩

/-- A costed tree above a costed tree that simulates a D tree simulates it, the leaves related
through `S`. -/
theorem TimedSimTree.of_treeLe {α β γ : Type} {R : α → γ → Prop} {S : α → β → Prop}
    {R' : β → γ → Prop} {K : ℕ} (hS : ∀ a b w, S a b → R a w → R' b w) {n : ℕ}
    {A : SPTree.Timed α} {t : CTree γ} (h : TimedSimTree R K n A t) :
    ∀ {B : SPTree.Timed β}, TreeLe S A B → TimedSimTree R' K n B t := by
  induction h with
  | ret hr => intro B hB; cases hB with | ret hs => exact .ret (hS _ _ _ hs hr)
  | tick _ hm ih => intro B hB; exact .tick (ih hB) hm
  | sample f e m _ hm ih =>
    intro B hB
    cases hB with
    | sample hc hk =>
      exact .sample f e m (fun b => ih b (hk b)) fun b =>
        (hm b).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hc b)) _)
  | get i f m _ hm ih =>
    intro B hB
    cases hB with
    | get hc hk =>
      exact .get i f m (fun x => ih x (hk x)) fun x =>
        (hm x).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hc x)) _)
  | set i f v m _ hm ih =>
    intro B hB
    cases hB with
    | set hc hk =>
      exact .set i f v m (ih hk) ((hm.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hc) _)))
  | fail => intro B hB; cases hB with | fail => exact .fail
  | query d r x m _ hm ih =>
    intro B hB
    cases hB with
    | @sample _ _ finγ' _ _ _ _ _ _ hc hk =>
      obtain rfl : finγ' = FTy.instFintype r := Subsingleton.elim _ _
      exact .query d r x m (fun y => ih y (hk y)) fun y =>
        (hm y).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hc y)) _)

/-- A costed tree above a costed tree that simulates a D tree simulates it. -/
theorem TimedSim.of_costLe {α β γ : Type} {R : α → γ → Prop} {S : α → β → Prop}
    {R' : β → γ → Prop} {K n : ℕ} (hS : ∀ a b w, S a b → R a w → R' b w)
    {x : ℕ × SPTree.Timed α} {y : ℕ × SPTree.Timed β} {t : CTree γ} (h : TimedSim R K n x t)
    (hxy : CostLe S x y) : TimedSim R' K n y t :=
  TimedSimTree.of_treeLe hS
    (TimedSimTree.mono h (Nat.add_le_add_left (Nat.mul_le_mul_left K hxy.1) n)) hxy.2

/-- The registered cost of a left fold is monotone in the cost of its step. -/
theorem foldl_timedCost_mono {α β : Type} (f : α → β → α) {c c' : α → β → ℕ}
    (h : ∀ a b, c a b ≤ c' a b) (init : α) (l : List β) :
    List.foldl.timedCost f c init l ≤ List.foldl.timedCost f c' init l := by
  induction l generalizing init with
  | nil => simp [List.foldl.timedCost]
  | cons b l ih =>
    have := h init b
    have := ih (f init b)
    simp [List.foldl.timedCost]
    omega

/-! ## First-order translated values -/

/-- At a first-order type, the translated values are the values of D. -/
theorem Ty.hat_eq_val : ∀ τ : Ty, τ.FO → τ.hat = Val τ
  | .base _, _ => rfl
  | .nat, _ => rfl
  | .prod a b, h => congrArg₂ Prod (Ty.hat_eq_val a h.1) (Ty.hat_eq_val b h.2)
  | .sum a b, h => congrArg₂ Sum (Ty.hat_eq_val a h.1) (Ty.hat_eq_val b h.2)
  | .arr _ _, h => h.elim
  | .list a, h => congrArg List (Ty.hat_eq_val a h)

theorem cast_prod {A A' B B' : Type} (pa : A = A') (pb : B = B') (p : (A × B) = (A' × B'))
    (x : A × B) : cast p x = (cast pa x.1, cast pb x.2) := by
  subst pa
  subst pb
  rfl

theorem cast_sum {A A' B B' : Type} (pa : A = A') (pb : B = B') (p : (A ⊕ B) = (A' ⊕ B'))
    (x : A ⊕ B) : cast p x = Sum.map (cast pa) (cast pb) x := by
  subst pa
  subst pb
  cases x <;> rfl

theorem cast_list {A A' : Type} (pa : A = A') (p : List A = List A') (x : List A) :
    cast p x = List.map (cast pa) x := by
  subst pa
  rw [cast_eq]
  induction x with
  | nil => rfl
  | cons a l ih => exact congrArg (List.cons a) ih

/-- At a first-order type, the value of D of a translated value is its cast. -/
theorem Ty.toVal_eq_cast : ∀ (τ : Ty) (h : τ.FO) (u : τ.hat),
    τ.toVal h u = cast (Ty.hat_eq_val τ h) u
  | .base _, _, _ => rfl
  | .nat, _, _ => rfl
  | .prod a b, h, u => by
    show (a.toVal h.1 u.1, b.toVal h.2 u.2) = _
    rw [Ty.toVal_eq_cast a h.1, Ty.toVal_eq_cast b h.2]
    exact (cast_prod (Ty.hat_eq_val a h.1) (Ty.hat_eq_val b h.2) _ u).symm
  | .sum a b, h, u => by
    show Sum.map (a.toVal h.1) (b.toVal h.2) u = _
    have ha : a.toVal h.1 = cast (Ty.hat_eq_val a h.1) :=
      funext fun x => Ty.toVal_eq_cast a h.1 x
    have hb : b.toVal h.2 = cast (Ty.hat_eq_val b h.2) :=
      funext fun x => Ty.toVal_eq_cast b h.2 x
    rw [ha, hb]
    exact (cast_sum (Ty.hat_eq_val a h.1) (Ty.hat_eq_val b h.2) _ u).symm
  | .arr _ _, h, _ => h.elim
  | .list a, h, u => by
    show List.map (a.toVal h) u = _
    have ha : a.toVal h = cast (Ty.hat_eq_val a h) := funext fun x => Ty.toVal_eq_cast a h x
    rw [ha]
    exact (cast_list (Ty.hat_eq_val a h) _ u).symm

/-- At a first-order type, the translated value of a value of D is its cast. -/
theorem Ty.ofVal_eq_cast : ∀ (τ : Ty) (h : τ.FO) (v : Val τ),
    τ.ofVal h v = cast (Ty.hat_eq_val τ h).symm v
  | .base _, _, _ => rfl
  | .nat, _, _ => rfl
  | .prod a b, h, v => by
    show (a.ofVal h.1 v.1, b.ofVal h.2 v.2) = _
    rw [Ty.ofVal_eq_cast a h.1, Ty.ofVal_eq_cast b h.2]
    exact (cast_prod (Ty.hat_eq_val a h.1).symm (Ty.hat_eq_val b h.2).symm _ v).symm
  | .sum a b, h, v => by
    show Sum.map (a.ofVal h.1) (b.ofVal h.2) v = _
    have ha : a.ofVal h.1 = cast (Ty.hat_eq_val a h.1).symm :=
      funext fun x => Ty.ofVal_eq_cast a h.1 x
    have hb : b.ofVal h.2 = cast (Ty.hat_eq_val b h.2).symm :=
      funext fun x => Ty.ofVal_eq_cast b h.2 x
    rw [ha, hb]
    exact (cast_sum (Ty.hat_eq_val a h.1).symm (Ty.hat_eq_val b h.2).symm _ v).symm
  | .arr _ _, h, _ => h.elim
  | .list a, h, v => by
    show List.map (a.ofVal h) v = _
    have ha : a.ofVal h = cast (Ty.hat_eq_val a h).symm :=
      funext fun x => Ty.ofVal_eq_cast a h x
    rw [ha]
    exact (cast_list (Ty.hat_eq_val a h).symm _ v).symm

/-- At a first-order type, a value of D related to a translated value is its cast. -/
theorem Sim.cast_eq (τ : Ty) (h : τ.FO) {u : τ.hat} {v : Val τ} (hs : Sim τ u v) :
    v = cast (Ty.hat_eq_val τ h) u :=
  (Sim.toVal_eq τ h hs).trans (Ty.toVal_eq_cast τ h u)

/-- At a first-order type, a value of D is related to its cast. -/
theorem Sim.cast_self (τ : Ty) (h : τ.FO) (v : Val τ) :
    Sim τ (cast (Ty.hat_eq_val τ h).symm v) v := by
  rw [← Ty.ofVal_eq_cast τ h v]
  exact Sim.ofVal τ h v

/-- A simulation of costed trees whose leaf type is cast. -/
theorem TimedSim.cast_leaves {α β γ : Type} (p : α = β) {R : α → γ → Prop}
    {R' : β → γ → Prop} {K n : ℕ} (hR : ∀ a w, R a w → R' (cast p a) w)
    {x : ℕ × SPTree.Timed α} {t : CTree γ} (h : TimedSim R K n x t) :
    TimedSim R' K n (cast (congrArg (fun T => ℕ × SPTree.Timed T) p) x) t := by
  subst p
  exact TimedSim.rel_mono hR h

/-! ## Translated environments of a telescope -/

/-- The empty translated environment. -/
def EnvHat.nil : EnvHat [] := fun _ x => nomatch x

/-- Extend a translated environment by an entry for the innermost variable. -/
def EnvHat.consE {Γ : List Ty} {σ : Ty} (e : σ.hatE) (η : EnvHat Γ) : EnvHat (σ :: Γ) :=
  fun _ x => match x with
    | .here => e
    | .there y => η _ y

theorem SimEnv.nil : SimEnv EnvHat.nil Env.nil := fun _ x => nomatch x

theorem SimEnv.consE {Γ : List Ty} {σ : Ty} {η : EnvHat Γ} {ρ : Env Γ} {e : σ.hatE}
    {v : Val σ} (hρ : SimEnv η ρ) (he : SimE σ e v) : SimEnv (η.consE e) (ρ.cons v) := by
  intro τ x
  cases x with
  | here => exact he
  | there y => exact hρ _ y

/-- The entry of a data function `f` of cost `fc` between first-order types. -/
noncomputable def dataEntry {a b : Ty} (ha : a.FO) (hb : b.FO) (f : Val a → Val b)
    (fc : Val a → ℕ) : (Ty.arr a b).hatE := fun u =>
  (fc (cast (Ty.hat_eq_val a ha) u),
    .ret (cast (Ty.hat_eq_val b hb).symm (f (cast (Ty.hat_eq_val a ha) u))))

/-- A D value with the step equation of a data function at a cost bounded by `fc` is related
to its entry. -/
theorem SimE.dataEntry {a b : Ty} (ha : a.FO) (hb : b.FO) {f : Val a → Val b}
    {fc C : Val a → ℕ} {g : Val (.arr a b)}
    (hg : ∀ v, g v = stepN CTree.tick (C v) (.ret (f v))) (hC : ∀ v, C v ≤ fc v) :
    SimE (.arr a b) (D.dataEntry ha hb f fc) g := by
  intro u v huv
  have hv := Sim.cast_eq a ha huv
  subst hv
  rw [hg]
  have := hC (cast (Ty.hat_eq_val a ha) u)
  exact TimedSim.stepN_ret (Sim.cast_self b hb _) (by omega)

/-- The entry of a tree function `F` between first-order types. -/
noncomputable def treeEntry {a b : Ty} (ha : a.FO) (hb : b.FO)
    (F : Val a → ℕ × SPTree.Timed (Val b)) : (Ty.arr a b).hatE := fun u =>
  cast (congrArg (fun T => ℕ × SPTree.Timed T) (Ty.hat_eq_val b hb).symm)
    (F (cast (Ty.hat_eq_val a ha) u))

/-- A D value simulated by the costed trees of `F` at allowance `0` is related to its entry. -/
theorem SimE.treeEntry {a b : Ty} (ha : a.FO) (hb : b.FO)
    {F : Val a → ℕ × SPTree.Timed (Val b)} {g : Val (.arr a b)}
    (hF : ∀ v, TimedSim (fun x w => x = w) 1 0 (F v) (g v)) :
    SimE (.arr a b) (D.treeEntry ha hb F) g := by
  intro u v huv
  have hv := Sim.cast_eq a ha huv
  subst hv
  refine TimedSim.cast_leaves (Ty.hat_eq_val b hb).symm (fun x w hxw => ?_) (hF _)
  subst hxw
  exact Sim.cast_self b hb x

/-! ## The simulation through the soundness theorem -/

/-- A costed tree `X` above the charges `t.dt η` of a first-order term of the fragment simulates
its evaluation at the allowance `t.allow`, with leaves equal to the values of D. -/
theorem Tm.timedSim_of_costLe {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) (ht : t.InDtFrag)
    (hτ : τ.FO) {η : EnvHat Γ} {ρ : Env Γ} (hρ : SimEnv η ρ) {X : ℕ × SPTree.Timed (Val τ)}
    (hX : CostLe (fun a b => cast (Ty.hat_eq_val τ hτ) a = b) (t.dt η) X) :
    TimedSim (fun a w => a = w) 1 t.allow X (t.eval ρ) :=
  TimedSim.of_costLe (fun _ _ _ hab haw => hab.symm.trans (Sim.cast_eq τ hτ haw).symm)
    (Tm.dt_timedSim t ht hρ) hX

/-- The meaning of a simulation with equal leaves at a query-free D tree. -/
theorem TimedSim.run_eq {α : Type} {K n : ℕ} {x : ℕ × SPTree.Timed α} {t : CTree α}
    (h : TimedSim (fun a w => a = w) K n x t) (hq : t.QueryFree) (O : CTree.Oracle) :
    t.run O = SPComp.bind x.2.erase.compile fun a => SPComp.pure a :=
  TimedSim.run (enc := fun a => a) (TimedSim.rel_mono (fun _ _ h => h.symm) h) hq O

end CatCrypt.Complexity.D

end
