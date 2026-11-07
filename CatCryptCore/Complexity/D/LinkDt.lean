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

`TreeLeA S D A B` and `CostLeA S e d x y` relax the comparison by a deficit: on every path the
step costs of the lower tree may exceed those of the upper one by at most `D` (by `e` in front and
`d` in the tree), and the upper tree simulates at the allowance raised by the deficit
(`TimedSimTree.of_treeLeA`, `TimedSim.of_costLeA`). This is the comparison that pays the unit
call of a free function value from the allowance, as the walk does (`DSim.appFree`):
`Tm.timedSim_of_costLeA` states the simulation from `CostLeA` at any charge `cc a ≤ 1` of a call
(`Tm.dtC`), at the allowance `t.allowC cc + (e + d)`. A costed bind whose continuation returns a
function `g` of the bound value at zero cost is compared as its tree with the leaf relation
composed with `g` (`TreeLeA.map_right`, `TreeLeA.map_left`).

At a first-order type, translated values and values of D are the same type (`Ty.hat_eq_val`)
and related exactly when they are equal up to the cast (`Sim.cast_eq`, `Sim.cast_self`). At a
concrete type the cast is the identity by definitional unfolding. The translated environment of
a telescope is built from `EnvHat.nil` and `EnvHat.consE` with the entries `dataEntry` for a data
function and `treeEntry` for a tree function, related to their D values by `SimE.dataEntry` and
`SimE.treeEntry`.

## Main definitions

* `TreeLe`, `CostLe`; `TreeLeA`, `CostLeA`: up to a deficit
* `EnvHat.nil`, `EnvHat.consE`, `dataEntry`, `treeEntry`

## Main results

* `TimedSimTree.of_treeLe`, `TimedSim.of_costLe`, `CostLe.bind`, `TreeLe.refl`
* `TimedSimTree.of_treeLeA`, `TimedSim.of_costLeA`, `CostLeA.bind`, `TreeLeA.mono`,
  `TreeLeA.of_treeLe`
* `TreeLeA.map_right`, `TreeLeA.map_left`, `CostLeA.map_right`, `CostLeA.map_left`: a costed bind
  whose continuation returns a function `g` of the bound value at zero cost is its tree with the
  leaves mapped by `g`, at the same deficits
* `foldl_timedCost_mono`: the registered cost of `List.foldl` is monotone in the step cost
* `Ty.hat_eq_val`, `Sim.cast_eq`, `Sim.cast_self`
* `SimEnv.nil`, `SimEnv.consE`, `SimE.dataEntry`, `SimE.treeEntry`
* `Tm.timedSim_of_costLe`, `Tm.timedSim_of_costLeA`
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

/-! ## Costed trees above costed trees up to a deficit -/

/-- `TreeLeA S D A B`: the costed tree `B` has the nodes of `A` in the same order, the leaves are
related by `S`, and on every path the step costs of `A` exceed those of `B` by at most `D` in
total: at a child `x` of a node the step cost of `A` is at most the one of `B` plus `e x`, the
subtree has deficit `d x`, and `e x + d x ≤ D`. -/
inductive TreeLeA {α β : Type} (S : α → β → Prop) : ℕ → SPTree.Timed α → SPTree.Timed β → Prop
    where
  /-- Related leaves. -/
  | ret {D : ℕ} {a : α} {b : β} (h : S a b) : TreeLeA S D (.ret a) (.ret b)
  /-- Samples of the same type. -/
  | sample {D : ℕ} {γ : Type} {finγ finγ' : Fintype γ} {neγ neγ' : Nonempty γ} {c c' : γ → ℕ}
      {k : γ → SPTree.Timed α} {k' : γ → SPTree.Timed β} (e d : γ → ℕ)
      (hc : ∀ x, c x ≤ c' x + e x) (hk : ∀ x, TreeLeA S (d x) (k x) (k' x))
      (hd : ∀ x, e x + d x ≤ D) :
      TreeLeA S D (.sample γ finγ neγ c k) (.sample γ finγ' neγ' c' k')
  /-- Samples of the same distribution. -/
  | sampleDist {D : ℕ} {γ : Type} {μ : Prob.SDistr γ} {c c' : γ → ℕ} {k : γ → SPTree.Timed α}
      {k' : γ → SPTree.Timed β} (e d : γ → ℕ) (hc : ∀ x, c x ≤ c' x + e x)
      (hk : ∀ x, TreeLeA S (d x) (k x) (k' x)) (hd : ∀ x, e x + d x ≤ D) :
      TreeLeA S D (.sampleDist γ μ c k) (.sampleDist γ μ c' k')
  /-- Reads of the same location. -/
  | get {D : ℕ} {l : Location} {c c' : l.ty → ℕ} {k : l.ty → SPTree.Timed α}
      {k' : l.ty → SPTree.Timed β} (e d : l.ty → ℕ) (hc : ∀ x, c x ≤ c' x + e x)
      (hk : ∀ x, TreeLeA S (d x) (k x) (k' x)) (hd : ∀ x, e x + d x ≤ D) :
      TreeLeA S D (.get l c k) (.get l c' k')
  /-- Writes of the same value to the same location. -/
  | set {D : ℕ} {l : Location} {v : l.ty} {c c' : ℕ} {A : SPTree.Timed α} {B : SPTree.Timed β}
      (e d : ℕ) (hc : c ≤ c' + e) (hk : TreeLeA S d A B) (hd : e + d ≤ D) :
      TreeLeA S D (.set l v c A) (.set l v c' B)
  /-- Failure. -/
  | fail {D : ℕ} : TreeLeA S D .fail .fail
  /-- Loads of the same heap. -/
  | load {D : ℕ} {h₀ : Heap} {c c' : ℕ} {A : SPTree.Timed α} {B : SPTree.Timed β}
      (e d : ℕ) (hc : c ≤ c' + e) (hk : TreeLeA S d A B) (hd : e + d ≤ D) :
      TreeLeA S D (.load h₀ c A) (.load h₀ c' B)

/-- `CostLeA S e d x y`: the step cost in front of `x` is at most the one of `y` plus `e`, and the
tree of `y` is above the tree of `x` up to the deficit `d` (`TreeLeA`). -/
def CostLeA {α β : Type} (S : α → β → Prop) (e d : ℕ) (x : ℕ × SPTree.Timed α)
    (y : ℕ × SPTree.Timed β) : Prop :=
  x.1 ≤ y.1 + e ∧ TreeLeA S d x.2 y.2

namespace TreeLeA

variable {α β : Type} {S : α → β → Prop}

/-- A larger deficit. -/
theorem mono {D : ℕ} {A : SPTree.Timed α} {B : SPTree.Timed β} (h : TreeLeA S D A B) {D' : ℕ}
    (hD : D ≤ D') : TreeLeA S D' A B := by
  cases h with
  | ret h => exact .ret h
  | sample e d hc hk hd => exact .sample e d hc hk fun x => (hd x).trans hD
  | sampleDist e d hc hk hd => exact .sampleDist e d hc hk fun x => (hd x).trans hD
  | get e d hc hk hd => exact .get e d hc hk fun x => (hd x).trans hD
  | set e d hc hk hd => exact .set e d hc hk (hd.trans hD)
  | fail => exact .fail
  | load e d hc hk hd => exact .load e d hc hk (hd.trans hD)

/-- A tree above another without deficit is above it at any deficit. -/
theorem of_treeLe {A : SPTree.Timed α} {B : SPTree.Timed β} (h : TreeLe S A B) (D : ℕ) :
    TreeLeA S D A B := by
  induction h generalizing D with
  | ret h => exact .ret h
  | sample hc _ ih =>
    exact .sample (fun _ => 0) (fun _ => D) (fun x => (hc x).trans (Nat.le_add_right _ _))
      (fun x => ih x D) fun _ => (Nat.zero_add D).le
  | sampleDist hc _ ih =>
    exact .sampleDist (fun _ => 0) (fun _ => D) (fun x => (hc x).trans (Nat.le_add_right _ _))
      (fun x => ih x D) fun _ => (Nat.zero_add D).le
  | get hc _ ih =>
    exact .get (fun _ => 0) (fun _ => D) (fun x => (hc x).trans (Nat.le_add_right _ _))
      (fun x => ih x D) fun _ => (Nat.zero_add D).le
  | set hc _ ih => exact .set 0 D (hc.trans (Nat.le_add_right _ _)) (ih D) (Nat.zero_add D).le
  | fail => exact .fail
  | load hc _ ih => exact .load 0 D (hc.trans (Nat.le_add_right _ _)) (ih D) (Nat.zero_add D).le

/-- A costed tree is above itself at deficit `0` when its leaves are related to themselves. -/
theorem refl {S : α → α → Prop} (hS : ∀ a, S a a) (A : SPTree.Timed α) : TreeLeA S 0 A A :=
  of_treeLe (TreeLe.refl hS A) 0

/-- The node rules with one deficit `e` of the step cost and one deficit `d` of the subtrees at
every child, the deficit of the node `e + d`. -/
theorem sample' {e d : ℕ} {γ : Type} {finγ finγ' : Fintype γ} {neγ neγ' : Nonempty γ}
    {c c' : γ → ℕ} {k : γ → SPTree.Timed α} {k' : γ → SPTree.Timed β}
    (hc : ∀ x, c x ≤ c' x + e) (hk : ∀ x, TreeLeA S d (k x) (k' x)) :
    TreeLeA S (e + d) (.sample γ finγ neγ c k) (.sample γ finγ' neγ' c' k') :=
  .sample (fun _ => e) (fun _ => d) hc hk fun _ => le_rfl

theorem sampleDist' {e d : ℕ} {γ : Type} {μ : Prob.SDistr γ} {c c' : γ → ℕ}
    {k : γ → SPTree.Timed α} {k' : γ → SPTree.Timed β} (hc : ∀ x, c x ≤ c' x + e)
    (hk : ∀ x, TreeLeA S d (k x) (k' x)) :
    TreeLeA S (e + d) (.sampleDist γ μ c k) (.sampleDist γ μ c' k') :=
  .sampleDist (fun _ => e) (fun _ => d) hc hk fun _ => le_rfl

theorem get' {e d : ℕ} {l : Location} {c c' : l.ty → ℕ} {k : l.ty → SPTree.Timed α}
    {k' : l.ty → SPTree.Timed β} (hc : ∀ x, c x ≤ c' x + e)
    (hk : ∀ x, TreeLeA S d (k x) (k' x)) : TreeLeA S (e + d) (.get l c k) (.get l c' k') :=
  .get (fun _ => e) (fun _ => d) hc hk fun _ => le_rfl

theorem set' {e d : ℕ} {l : Location} {v : l.ty} {c c' : ℕ} {A : SPTree.Timed α}
    {B : SPTree.Timed β} (hc : c ≤ c' + e) (hk : TreeLeA S d A B) :
    TreeLeA S (e + d) (.set l v c A) (.set l v c' B) :=
  .set e d hc hk le_rfl

theorem load' {e d : ℕ} {h₀ : Heap} {c c' : ℕ} {A : SPTree.Timed α} {B : SPTree.Timed β}
    (hc : c ≤ c' + e) (hk : TreeLeA S d A B) :
    TreeLeA S (e + d) (.load h₀ c A) (.load h₀ c' B) :=
  .load e d hc hk le_rfl

/-- Leaves and failures at deficit `0`. -/
theorem ret0 {a : α} {b : β} (h : S a b) : TreeLeA S 0 (.ret a) (.ret b) := .ret h

theorem fail0 : TreeLeA S 0 (.fail : SPTree.Timed α) (.fail : SPTree.Timed β) := .fail

end TreeLeA

namespace CostLeA

variable {α β : Type} {S : α → β → Prop}

theorem mk {e d c c' : ℕ} {A : SPTree.Timed α} {B : SPTree.Timed β} (hc : c ≤ c' + e)
    (h : TreeLeA S d A B) : CostLeA S e d (c, A) (c', B) :=
  ⟨hc, h⟩

/-- The step costs in front of costed trees above each other up to a deficit. -/
theorem fst_le {e d : ℕ} {x : ℕ × SPTree.Timed α} {y : ℕ × SPTree.Timed β}
    (h : CostLeA S e d x y) : x.1 ≤ y.1 + e :=
  h.1

/-- The trees of costed trees above each other up to a deficit. -/
theorem tree {e d : ℕ} {x : ℕ × SPTree.Timed α} {y : ℕ × SPTree.Timed β}
    (h : CostLeA S e d x y) : TreeLeA S d x.2 y.2 :=
  h.2

/-- Larger deficits. -/
theorem mono {e d e' d' : ℕ} {x : ℕ × SPTree.Timed α} {y : ℕ × SPTree.Timed β}
    (h : CostLeA S e d x y) (he : e ≤ e') (hd : d ≤ d') : CostLeA S e' d' x y :=
  ⟨h.1.trans (Nat.add_le_add_left he _), h.2.mono hd⟩

/-- A costed tree above another without deficit. -/
theorem of_costLe {x : ℕ × SPTree.Timed α} {y : ℕ × SPTree.Timed β} (h : CostLe S x y)
    (e d : ℕ) : CostLeA S e d x y :=
  ⟨h.1.trans (Nat.le_add_right _ _), TreeLeA.of_treeLe h.2 d⟩

/-- The deficit of a bind: the first trees with equal leaves at deficit `d₁`, the continuations
at deficits `e₂` in front and `d₂` in the tree. On a path the front deficit of the continuation
is spent either in front of the bind (when the first tree is a leaf) or at the node of the first
tree above it, so that the bind has deficit `e₂` in front and `d₁ + e₂ + d₂` in the tree. -/
theorem bind {γ δ ε : Type} {S : γ → δ → Prop} {d₁ e₂ d₂ : ℕ} {A A' : SPTree.Timed ε}
    {k : ε → ℕ × SPTree.Timed γ} {k' : ε → ℕ × SPTree.Timed δ}
    (hA : TreeLeA (fun a b => a = b) d₁ A A') (hk : ∀ a, CostLeA S e₂ d₂ (k a) (k' a)) :
    CostLeA S e₂ (d₁ + e₂ + d₂) (A.bind k) (A'.bind k') := by
  -- On a path the front deficit `f ≤ e₂` and the tree deficit `g` of the bind sum to at most
  -- `d₁ + e₂ + d₂`.
  suffices H : ∃ f g, f ≤ e₂ ∧ f + g ≤ d₁ + e₂ + d₂ ∧ (A.bind k).1 ≤ (A'.bind k').1 + f ∧
      TreeLeA S g (A.bind k).2 (A'.bind k').2 by
    obtain ⟨f, g, hf, hfg, h1, h2⟩ := H
    exact ⟨h1.trans (Nat.add_le_add_left hf _), h2.mono (by omega)⟩
  induction hA with
  | ret h =>
    subst h
    exact ⟨e₂, d₂, le_rfl, by omega, (hk _).1, (hk _).2⟩
  | @sample D _ _ _ _ _ _ _ _ _ e d hc _ hd ih =>
    choose f g hf hfg h1 h2 using ih
    refine ⟨0, D + e₂ + d₂, Nat.zero_le _, by omega, Nat.zero_le _, ?_⟩
    exact .sample (fun x => e x + f x) g (fun x => by have := hc x; have := h1 x; simp; omega)
      h2 fun x => by have := hd x; have := hfg x; omega
  | @sampleDist D _ _ _ _ _ _ e d hc _ hd ih =>
    choose f g hf hfg h1 h2 using ih
    refine ⟨0, D + e₂ + d₂, Nat.zero_le _, by omega, Nat.zero_le _, ?_⟩
    exact .sampleDist (fun x => e x + f x) g
      (fun x => by have := hc x; have := h1 x; simp; omega)
      h2 fun x => by have := hd x; have := hfg x; omega
  | @get D _ _ _ _ _ e d hc _ hd ih =>
    choose f g hf hfg h1 h2 using ih
    refine ⟨0, D + e₂ + d₂, Nat.zero_le _, by omega, Nat.zero_le _, ?_⟩
    exact .get (fun x => e x + f x) g (fun x => by have := hc x; have := h1 x; simp; omega)
      h2 fun x => by have := hd x; have := hfg x; omega
  | @set D _ _ _ _ _ _ e d hc _ hd ih =>
    obtain ⟨f, g, hf, hfg, h1, h2⟩ := ih
    refine ⟨0, D + e₂ + d₂, Nat.zero_le _, by omega, Nat.zero_le _, ?_⟩
    exact .set (e + f) g (by omega) h2 (by omega)
  | fail => exact ⟨0, 0, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, .fail⟩
  | @load D _ _ _ _ _ e d hc _ hd ih =>
    obtain ⟨f, g, hf, hfg, h1, h2⟩ := ih
    refine ⟨0, D + e₂ + d₂, Nat.zero_le _, by omega, Nat.zero_le _, ?_⟩
    exact .load (e + f) g (by omega) h2 (by omega)

end CostLeA

/-! ## The leaf map at zero cost

A costed bind `B.bind fun y => (0, ret (g y))`, whose continuation returns a function `g` of the
bound value at zero cost, is the costed tree `B` with its leaves mapped by `g` at the same step
costs (`SPTree.Timed.map g fun _ => 0` by definition), its own step cost `0`
(`SPTree.Timed.bind_ret_fst`). On either side of a comparison it is read as `B` with the leaf
relation composed with `g`, at the same deficits. -/

namespace TreeLeA

variable {α β : Type}

/-- The leaves of the upper tree mapped by `g` at zero cost: same nodes and step costs, the
leaf relation `S'` reached from `S` through `g`. -/
theorem map_right {β' : Type} {S : α → β → Prop} {S' : α → β' → Prop} {g : β → β'} {D : ℕ}
    {A : SPTree.Timed α} {B : SPTree.Timed β} (h : TreeLeA S D A B)
    (hS : ∀ a b, S a b → S' a (g b)) :
    TreeLeA S' D A (B.bind fun y => (0, .ret (g y))).2 := by
  induction h with
  | ret h => exact .ret (hS _ _ h)
  | sample e d hc _ hd ih =>
    exact .sample e d (fun x => by simpa [SPTree.Timed.bind_ret_fst] using hc x) ih hd
  | sampleDist e d hc _ hd ih =>
    exact .sampleDist e d (fun x => by simpa [SPTree.Timed.bind_ret_fst] using hc x) ih hd
  | get e d hc _ hd ih =>
    exact .get e d (fun x => by simpa [SPTree.Timed.bind_ret_fst] using hc x) ih hd
  | set e d hc _ hd ih =>
    exact .set e d (by simpa [SPTree.Timed.bind_ret_fst] using hc) ih hd
  | fail => exact .fail
  | load e d hc _ hd ih =>
    exact .load e d (by simpa [SPTree.Timed.bind_ret_fst] using hc) ih hd

/-- The leaves of the lower tree mapped by `g` at zero cost: same nodes and step costs, the
leaf relation `S'` reached from `S` through `g`. -/
theorem map_left {α' : Type} {S : α → β → Prop} {S' : α' → β → Prop} {g : α → α'} {D : ℕ}
    {A : SPTree.Timed α} {B : SPTree.Timed β} (h : TreeLeA S D A B)
    (hS : ∀ a b, S a b → S' (g a) b) :
    TreeLeA S' D (A.bind fun y => (0, .ret (g y))).2 B := by
  induction h with
  | ret h => exact .ret (hS _ _ h)
  | sample e d hc _ hd ih =>
    exact .sample e d (fun x => by simpa [SPTree.Timed.bind_ret_fst] using hc x) ih hd
  | sampleDist e d hc _ hd ih =>
    exact .sampleDist e d (fun x => by simpa [SPTree.Timed.bind_ret_fst] using hc x) ih hd
  | get e d hc _ hd ih =>
    exact .get e d (fun x => by simpa [SPTree.Timed.bind_ret_fst] using hc x) ih hd
  | set e d hc _ hd ih =>
    exact .set e d (by simpa [SPTree.Timed.bind_ret_fst] using hc) ih hd
  | fail => exact .fail
  | load e d hc _ hd ih =>
    exact .load e d (by simpa [SPTree.Timed.bind_ret_fst] using hc) ih hd

end TreeLeA

namespace CostLeA

variable {α β : Type}

/-- A costed pair above the step cost `0` and the tree `B` is above the leaf map of `B` at zero
cost, at the same deficits. -/
theorem map_right {β' : Type} {S : α → β → Prop} {S' : α → β' → Prop} {g : β → β'} {e d : ℕ}
    {x : ℕ × SPTree.Timed α} {B : SPTree.Timed β} (h : CostLeA S e d x (0, B))
    (hS : ∀ a b, S a b → S' a (g b)) :
    CostLeA S' e d x (B.bind fun y => (0, .ret (g y))) :=
  ⟨by rw [SPTree.Timed.bind_ret_fst]; exact h.1, h.2.map_right hS⟩

/-- The leaf map at zero cost of a tree `A` is below what the costed pair of step cost `0` and
`A` is below, at the same deficits. -/
theorem map_left {α' : Type} {S : α → β → Prop} {S' : α' → β → Prop} {g : α → α'} {e d : ℕ}
    {A : SPTree.Timed α} {y : ℕ × SPTree.Timed β} (h : CostLeA S e d (0, A) y)
    (hS : ∀ a b, S a b → S' (g a) b) :
    CostLeA S' e d (A.bind fun y => (0, .ret (g y))) y :=
  ⟨by rw [SPTree.Timed.bind_ret_fst]; exact h.1, h.2.map_left hS⟩

end CostLeA

/-- A costed tree above a costed tree that simulates a D tree, up to the deficit `D`, simulates
it at the allowance raised by `K * D`: each step that the deficit leaves out is paid by the
allowance. -/
theorem TimedSimTree.of_treeLeA {α β γ : Type} {R : α → γ → Prop} {S : α → β → Prop}
    {R' : β → γ → Prop} {K : ℕ} (hS : ∀ a b w, S a b → R a w → R' b w) {n : ℕ}
    {A : SPTree.Timed α} {t : CTree γ} (h : TimedSimTree R K n A t) :
    ∀ {D : ℕ} {B : SPTree.Timed β}, TreeLeA S D A B → TimedSimTree R' K (n + K * D) B t := by
  induction h with
  | ret hr => intro D B hB; cases hB with | ret hs => exact .ret (hS _ _ _ hs hr)
  | tick _ hm ih => intro D B hB; exact .tick (ih hB) (by omega)
  | sample f e m _ hm ih =>
    intro D B hB
    cases hB with
    | sample ec dc hc hk hd =>
      refine .sample f e (fun b => m b + K * dc b) (fun b => ih b (hk b)) fun b => ?_
      have h1 := Nat.mul_le_mul_left K (hc b)
      have h2 := Nat.mul_le_mul_left K (hd b)
      rw [Nat.mul_add] at h1 h2
      have := hm b
      omega
  | get i f m _ hm ih =>
    intro D B hB
    cases hB with
    | get ec dc hc hk hd =>
      refine .get i f (fun x => m x + K * dc x) (fun x => ih x (hk x)) fun x => ?_
      have h1 := Nat.mul_le_mul_left K (hc x)
      have h2 := Nat.mul_le_mul_left K (hd x)
      rw [Nat.mul_add] at h1 h2
      have := hm x
      omega
  | set i f v m _ hm ih =>
    intro D B hB
    cases hB with
    | set ec dc hc hk hd =>
      refine .set i f v (m + K * dc) (ih hk) ?_
      have h1 := Nat.mul_le_mul_left K hc
      have h2 := Nat.mul_le_mul_left K hd
      rw [Nat.mul_add] at h1 h2
      omega
  | fail => intro D B hB; cases hB with | fail => exact .fail
  | query d r x m _ hm ih =>
    intro D B hB
    cases hB with
    | @sample _ _ _ finγ' _ _ _ _ _ _ ec dc hc hk hd =>
      obtain rfl : finγ' = FTy.instFintype r := Subsingleton.elim _ _
      refine .query d r x (fun y => m y + K * dc y) (fun y => ih y (hk y)) fun y => ?_
      have h1 := Nat.mul_le_mul_left K (hc y)
      have h2 := Nat.mul_le_mul_left K (hd y)
      rw [Nat.mul_add] at h1 h2
      have := hm y
      omega

/-- A costed tree above a costed tree that simulates a D tree, up to the deficits `e` in front
and `d` in the tree, simulates it at the allowance raised by `K * (e + d)`. -/
theorem TimedSim.of_costLeA {α β γ : Type} {R : α → γ → Prop} {S : α → β → Prop}
    {R' : β → γ → Prop} {K n e d : ℕ} (hS : ∀ a b w, S a b → R a w → R' b w)
    {x : ℕ × SPTree.Timed α} {y : ℕ × SPTree.Timed β} {t : CTree γ} (h : TimedSim R K n x t)
    (hxy : CostLeA S e d x y) : TimedSim R' K (n + K * (e + d)) y t := by
  have h' := TimedSimTree.of_treeLeA hS h hxy.2
  refine TimedSimTree.mono h' ?_
  have h1 := Nat.mul_le_mul_left K hxy.1
  rw [Nat.mul_add] at h1
  rw [Nat.mul_add]
  omega

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
  | .mu _, _ => rfl
  | .pi f B, h => congrArg (fun F : f.den → Type => (j : f.den) → F j)
      (funext fun j => Ty.hat_eq_val (B j) (h j))
  | .sig f B, h => congrArg (fun F : f.den → Type => (j : f.den) × F j)
      (funext fun j => Ty.hat_eq_val (B j) (h j))

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

theorem cast_pi {I : Type} {A A' : I → Type} (pa : ∀ j, A j = A' j)
    (p : ((j : I) → A j) = ((j : I) → A' j)) (x : (j : I) → A j) :
    cast p x = fun j => cast (pa j) (x j) := by
  obtain rfl : A = A' := funext pa
  rfl

theorem cast_sigma {I : Type} {A A' : I → Type} (pa : ∀ j, A j = A' j)
    (p : ((j : I) × A j) = ((j : I) × A' j)) (x : (j : I) × A j) :
    cast p x = ⟨x.1, cast (pa x.1) x.2⟩ := by
  obtain rfl : A = A' := funext pa
  rfl

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
  | .mu _, _, _ => rfl
  | .pi f B, h, u =>
    (funext fun j => Ty.toVal_eq_cast (B j) (h j) (u j)).trans
      (cast_pi (fun j => Ty.hat_eq_val (B j) (h j)) (Ty.hat_eq_val (.pi f B) h) u).symm
  | .sig f B, h, u => by
    change (j : f.den) × Ty.hat (B j) at u
    show (⟨u.1, (B u.1).toVal (h u.1) u.2⟩ : (j : f.den) × Val (B j)) = _
    rw [Ty.toVal_eq_cast (B u.1) (h u.1) u.2]
    exact (cast_sigma (fun j => Ty.hat_eq_val (B j) (h j)) (Ty.hat_eq_val (.sig f B) h) u).symm

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
  | .mu _, _, _ => rfl
  | .pi f B, h, v =>
    (funext fun j => Ty.ofVal_eq_cast (B j) (h j) (v j)).trans
      (cast_pi (fun j => (Ty.hat_eq_val (B j) (h j)).symm) (Ty.hat_eq_val (.pi f B) h).symm
        v).symm
  | .sig f B, h, v => by
    change (j : f.den) × Val (B j) at v
    show (⟨v.1, (B v.1).ofVal (h v.1) v.2⟩ : (j : f.den) × Ty.hat (B j)) = _
    rw [Ty.ofVal_eq_cast (B v.1) (h v.1) v.2]
    exact (cast_sigma (fun j => (Ty.hat_eq_val (B j) (h j)).symm)
      (Ty.hat_eq_val (.sig f B) h).symm v).symm

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

/-- A costed tree `X` above the charges `t.dtC cc η` (at a charge `cc a ≤ 1` of a call) of a
first-order term of the fragment up to the deficits `e` in front and `d` in the tree simulates
its evaluation at the allowance `t.allowC cc + (e + d)`, with leaves equal to the values of D:
the steps of the charges that `X` leaves out are paid from the allowance. These are the unit call
of a function value that the costed form charges nothing for (a projection or re-pairing, as the
walk pays it by `DSim.appFree`), and, at the charge `1` of every call, the call on `unit`, which
the costed form charges nothing for. -/
theorem Tm.timedSim_of_costLeA (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) {Γ : List Ty} {τ : Ty}
    (t : Tm Γ τ) (ht : t.InDtFrag) (hτ : τ.FO) {η : EnvHat Γ} {ρ : Env Γ} (hρ : SimEnv η ρ)
    {e d : ℕ} {X : ℕ × SPTree.Timed (Val τ)}
    (hX : CostLeA (fun a b => cast (Ty.hat_eq_val τ hτ) a = b) e d (t.dtC cc η) X) :
    TimedSim (fun a w => a = w) 1 (t.allowC cc + (e + d)) X (t.eval ρ) := by
  have h := TimedSim.of_costLeA (fun _ _ _ hab haw => hab.symm.trans (Sim.cast_eq τ hτ haw).symm)
    (Tm.dtC_timedSim cc hcc t ht hρ) hX
  rwa [Nat.one_mul] at h

/-- The meaning of a simulation with equal leaves at a query-free D tree. -/
theorem TimedSim.run_eq {α : Type} {K n : ℕ} {x : ℕ × SPTree.Timed α} {t : CTree α}
    (h : TimedSim (fun a w => a = w) K n x t) (hq : t.QueryFree) (O : CTree.Oracle) :
    t.run O = SPComp.bind x.2.erase.compile fun a => SPComp.pure a :=
  TimedSim.run (enc := fun a => a) (TimedSim.rel_mono (fun _ _ h => h.symm) h) hq O

end CatCrypt.Complexity.D

end
