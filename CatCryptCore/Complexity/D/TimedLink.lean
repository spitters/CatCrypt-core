/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Link
public import CatCryptCore.Complexity.D.Reflect
public import CatCryptCore.Tactics.DLink

/-!
# Correspondence of costed trees and reflected D-terms, per construct

The judgements and rules that relate the costed form `R.tree.timed` of `derive_reduction` to the
evaluation of the D-term `R.tree.d` of `reflect_d`, one rule per construct of the first-order
fragment without `ℕ` arithmetic. Each rule is stated over all terms of its construct.

* `DSim K n c t ρ v`: the data term `t` evaluates in `ρ` to `v` without effects, in at most
  `n + K * c` steps; `c` is the charge of `derive_timed` for its source and `n` an additive
  allowance.
* `TSim E K n x t ρ`: the costed tree `x` simulates the evaluation of the tree term `t` in `ρ`
  (`TimedSim E K n x (t.eval ρ)`).

The tree rules take the D term that `reflect_d` builds for a construct and the costed tree that
`derive_timed` builds for the same construct. A `letE` of D charges a β-step that the costed
form does not; it is paid by the allowance (one unit per `letE`, sample, get, set, bind and call
without arguments) or by a unit charge of the costed form (a conditional, a call with arguments,
a primitive operation), at the factor `K ≥ 1`.

## Main definitions

* `DSim`, `TSim`

## Main results

* `TimedSim.stepN_delay`, `TimedSim.le_fst`: steps in front of the D tree against a step cost in
  front of the costed tree, and weakening of that step cost.
* Tree rules `TSim.ret`, `TSim.fail`, `TSim.sample`, `TSim.get`, `TSim.set`, `TSim.letE`,
  `TSim.bind`, `TSim.ite`, `TSim.call`, `TSim.call0`, and `TSim.le_fst`, `TSim.mono`,
  `TSim.cost_le`.
* Data rules `DSim.var`, `DSim.lit`, `DSim.natLit`, `DSim.pair`, `DSim.fst`, `DSim.snd`,
  `DSim.prim`, `DSim.decide`, `DSim.app`, `DSim.letE`, `DSim.ite`, `DSim.le`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core Reflect

namespace TimedSim

variable {α β : Type} {R : α → β → Prop} {K n : ℕ}

/-- `m` steps in front of the D tree against the step cost `c` in front of the costed tree, the
excess over `K * c` paid by the allowance `n₀`. -/
theorem stepN_delay {m n₀ c : ℕ} {x : ℕ × SPTree.Timed α} {t : CTree β}
    (hm : m ≤ n₀ + K * c) (h : TimedSim R K n x t) :
    TimedSim R K (n₀ + n) (SPTree.Timed.delay c x) (stepN CTree.tick m t) := by
  refine TimedSimTree.stepN_tick h m ?_
  show n + K * x.1 + m ≤ n₀ + n + K * (c + x.1)
  rw [Nat.mul_add]
  omega

/-- The step cost in front of the costed tree may be raised. -/
theorem le_fst {c c' : ℕ} {A : SPTree.Timed α} {t : CTree β} (hc : c ≤ c')
    (h : TimedSim R K n (c, A) t) : TimedSim R K n (c', A) t :=
  TimedSimTree.mono h (Nat.add_le_add_left (Nat.mul_le_mul_left K hc) n)

end TimedSim

namespace TimedLink

variable {Γ : List Ty} {ρ : Env Γ} {α γ β : Type} {τ a b : Ty} {K : ℕ}

/-- The data term `t` evaluates in `ρ` to `v` in at most `n + K * c` steps; `c` is the
`derive_timed` charge of its source. -/
def DSim (K n c : ℕ) (t : Tm Γ τ) (ρ : Env Γ) (v : Val τ) : Prop :=
  ∃ m, CEq t ρ m v ∧ m ≤ n + K * c

/-- The tree term `t` in `ρ` is simulated by the costed tree `x`. -/
def TSim (E : α → Val τ → Prop) (K n : ℕ) (x : ℕ × SPTree.Timed α) (t : Tm Γ τ)
    (ρ : Env Γ) : Prop :=
  TimedSim E K n x (t.eval ρ)

namespace DSim

theorem var (x : Var Γ τ) : DSim K 0 0 (.var x) ρ (ρ τ x) :=
  ⟨0, CEq.var x ρ, Nat.zero_le _⟩

theorem lit (f : FTy) (v : f.den) : DSim K 0 0 (.lit f v : Tm Γ (.base f)) ρ v :=
  ⟨0, CEq.lit f v ρ, Nat.zero_le _⟩

theorem natLit (k : ℕ) : DSim K 0 0 (.natLit k : Tm Γ .nat) ρ k :=
  ⟨0, CEq.natLit k ρ, Nat.zero_le _⟩

theorem pair {x : Tm Γ a} {y : Tm Γ b} {u : Val a} {v : Val b} {n₁ n₂ c₁ c₂ : ℕ}
    (hx : DSim K n₁ c₁ x ρ u) (hy : DSim K n₂ c₂ y ρ v) :
    DSim K (n₁ + n₂) (c₁ + c₂) (.pair x y) ρ ((u, v) : Val a × Val b) := by
  obtain ⟨m₁, h₁, l₁⟩ := hx
  obtain ⟨m₂, h₂, l₂⟩ := hy
  refine ⟨m₁ + m₂, CEq.pair h₁ h₂, ?_⟩
  rw [Nat.mul_add]
  omega

theorem fst {p : Tm Γ (.prod a b)} {v : Val a × Val b} {n c : ℕ} (h : DSim K n c p ρ v) :
    DSim K n c (.fst p) ρ v.1 := by
  obtain ⟨m, hm, l⟩ := h
  exact ⟨m, CEq.fst hm, l⟩

theorem snd {p : Tm Γ (.prod a b)} {v : Val a × Val b} {n c : ℕ} (h : DSim K n c p ρ v) :
    DSim K n c (.snd p) ρ v.2 := by
  obtain ⟨m, hm, l⟩ := h
  exact ⟨m, CEq.snd hm, l⟩

/-- An operation that `derive_timed` charges one unit (a word, `Bool`, `Fin` or `ZMod`
operation): its D cost beyond `K` is paid by the allowance `n₀`. -/
theorem prim (p : Prim a b) {x : Tm Γ a} {v : Val a} {n n₀ c : ℕ}
    (hx : DSim K n c x ρ v) (hp : p.cost v ≤ n₀ + K) :
    DSim K (n + n₀) (1 + c) (.prim p x) ρ (p.apply v) := by
  obtain ⟨m, hm, l⟩ := hx
  refine ⟨m + p.cost v, CEq.prim p hm, ?_⟩
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- A decision atom in a condition, which `derive_timed` charges nothing beyond its
arguments: its D cost is paid by the allowance `n₀`. -/
theorem decide (p : Prim a b) {x : Tm Γ a} {v : Val a} {n n₀ c : ℕ}
    (hx : DSim K n c x ρ v) (hp : p.cost v ≤ n₀) :
    DSim K (n + n₀) c (.prim p x) ρ (p.apply v) := by
  obtain ⟨m, hm, l⟩ := hx
  exact ⟨m + p.cost v, CEq.prim p hm, by omega⟩

/-- A data function value applied: the β-step and its `m ≤ d` steps against the charge
`1 + d` of the call. -/
theorem app (hK : 1 ≤ K) {F : Tm Γ (.arr a b)} {x : Tm Γ a} {g : Val (.arr a b)} {v : Val a}
    {w : Val b} {n c d m : ℕ} (hF : CEq F ρ 0 g) (hx : DSim K n c x ρ v)
    (hg : g v = stepN CTree.tick m (.ret w)) (hm : m ≤ d) :
    DSim K n (1 + d + c) (.app F x) ρ w := by
  obtain ⟨mx, hmx, l⟩ := hx
  refine ⟨0 + mx + (m + 1), CEq.app hF hmx hg, ?_⟩
  have hd := Nat.mul_le_mul_right d hK
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  omega

/-- A data `let`: its β-step is paid by the allowance. -/
theorem letE {e : Tm Γ a} {bt : Tm (a :: Γ) b} {u : Val a} {w : Val b} {n₁ n₂ c₁ c₂ : ℕ}
    (he : DSim K n₁ c₁ e ρ u) (hb : DSim K n₂ c₂ bt (ρ.cons u) w) :
    DSim K (n₁ + n₂ + 1) (c₁ + c₂) (.letE e bt) ρ w := by
  obtain ⟨m₁, h₁, l₁⟩ := he
  obtain ⟨m₂, h₂, l₂⟩ := hb
  refine ⟨m₁ + (m₂ + 1), CEq.letE h₁ h₂, ?_⟩
  rw [Nat.mul_add]
  omega

/-- A data conditional: the β-step is paid by the unit charge of the conditional. -/
theorem ite (hK : 1 ≤ K) {P : Prop} [Decidable P] {bt : Tm Γ .bool} {t e : Tm Γ τ}
    {u w : Val τ} {n₁ n₂ cb ct ce c : ℕ} (hb : DSim K n₁ cb bt ρ (Decidable.decide P))
    (ht : DSim K n₂ ct t ρ u) (he : DSim K n₂ ce e ρ w) (hct : 1 + cb + ct ≤ c)
    (hce : 1 + cb + ce ≤ c) :
    DSim K (n₁ + n₂) c (.ite bt t e) ρ (if P then u else w) := by
  obtain ⟨mb, hmb, lb⟩ := hb
  obtain ⟨mt, hmt, lt⟩ := ht
  obtain ⟨me, hme, le⟩ := he
  refine ⟨mb + ((if P then mt else me) + 1), CEq.ite id hmb hmt hme, ?_⟩
  have h1 := Nat.mul_le_mul_left K hct
  have h2 := Nat.mul_le_mul_left K hce
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at h1 h2
  by_cases hP : P
  · rw [ite_eq_left hP]
    omega
  · rw [ite_eq_right hP]
    omega

theorem le {t : Tm Γ τ} {v : Val τ} {n n' c c' : ℕ} (hn : n ≤ n') (hc : c ≤ c')
    (h : DSim K n c t ρ v) : DSim K n' c' t ρ v := by
  obtain ⟨m, hm, l⟩ := h
  exact ⟨m, hm, by have := Nat.mul_le_mul_left K hc; omega⟩

end DSim

namespace TSim

variable {E : α → Val τ → Prop}

theorem le_fst {A : SPTree.Timed α} {t : Tm Γ τ} {n c c' : ℕ} (hc : c ≤ c')
    (h : TSim E K n (c, A) t ρ) : TSim E K n (c', A) t ρ :=
  TimedSim.le_fst hc h

theorem mono {x : ℕ × SPTree.Timed α} {t : Tm Γ τ} {n n' : ℕ} (hn : n ≤ n')
    (h : TSim E K n x t ρ) : TSim E K n' x t ρ :=
  TimedSim.mono h hn

/-- The cost of the D term is at most the allowance plus `K` times the time of the costed
tree. -/
theorem cost_le {x : ℕ × SPTree.Timed α} {t : Tm Γ τ} {n : ℕ} (h : TSim E K n x t ρ) :
    t.cost ρ ≤ n + K * SPTree.Timed.stepTime x :=
  TimedSim.cost_le h

/-- `SPTree.ret a` against the data term of `a`. -/
theorem ret {t : Tm Γ τ} {a : α} {v : Val τ} {n c : ℕ}
    (ht : DSim K n c t ρ v) (hE : E a v) : TSim E K n (c, .ret a) t ρ := by
  obtain ⟨m, hm, l⟩ := ht
  unfold TSim TimedSim
  rw [hm]
  exact TimedSimTree.stepN_tick (TimedSimTree.ret (n := 0) hE) m
    (by show 0 + m ≤ n + K * c; omega)

/-- `SPTree.fail` against `Tm.fail`. -/
theorem fail {n c : ℕ} : TSim E K n (c, .fail) (Tm.fail : Tm Γ τ) ρ :=
  TimedSim.fail

/-- A sample node against `letE (sample f) k`; the β-step of each continuation is paid by the
allowance. -/
theorem sample (hK : 1 ≤ K) (f : FTy) {finβ : Fintype β} {neβ : Nonempty β} (e : β ≃ f.den)
    {cs : β → ℕ} {ks : β → SPTree.Timed α} {k : Tm (.base f :: Γ) τ} {n c : ℕ}
    (hk : ∀ x, TSim E K n (cs x, ks x) k (ρ.cons (τ := .base f) (e x))) :
    TSim E K (n + 1) (c, .sample β finβ neβ cs ks) (.letE (.sample f) k) ρ :=
  TimedSim.le_fst (Nat.zero_le c) (TimedSim.eval_letE_sample hK e fun x =>
    TimedSim.tick (hk x) (by omega))

/-- A get node against `letE (get i f) k`. -/
theorem get (hK : 1 ≤ K) (i : ℕ) (f : FTy) {cs : f.den → ℕ} {ks : f.den → SPTree.Timed α}
    {k : Tm (.base f :: Γ) τ} {n c : ℕ}
    (hk : ∀ v, TSim E K n (cs v, ks v) k (ρ.cons (τ := .base f) v)) :
    TSim E K (n + 1) (c, .get (f.loc i) cs ks) (.letE (.get i f) k) ρ :=
  TimedSim.le_fst (Nat.zero_le c) (TimedSim.get hK i f fun v =>
    TimedSim.tick (hk v) (by omega))

/-- A set node against `letE (set i f x) k`; the evaluation of `x` is paid by the step cost in
front of the costed tree. -/
theorem set (hK : 1 ≤ K) (i : ℕ) (f : FTy) {x : Tm Γ (.base f)} {v : f.den}
    {cs : ℕ} {ks : SPTree.Timed α} {k : Tm (.unit :: Γ) τ} {n₁ n₂ cx c : ℕ}
    (hx : DSim K n₁ cx x ρ v) (hk : TSim E K n₂ (cs, ks) k (ρ.cons (τ := .unit) ()))
    (hc : cx ≤ c) :
    TSim E K (n₁ + n₂ + 1) (c, .set (f.loc i) v cs ks) (.letE (.set i f x) k) ρ := by
  obtain ⟨m, hm, l⟩ := hx
  have key : (Tm.letE (.set i f x) k).eval ρ =
      stepN CTree.tick m (.set i f v (.tick (k.eval (ρ.cons (τ := .unit) ())))) := by
    have hs : (Tm.set i f x).eval ρ = stepN CTree.tick m (.set i f v (.ret ())) := by
      show (x.eval ρ).bind _ = _
      rw [hm, stepN_tick_bind]
      rfl
    rw [Tm.eval_letE, hs]
    exact stepN_tick_bind _ _ _
  unfold TSim
  rw [key]
  have hcK := Nat.mul_le_mul_left K hc
  exact TimedSim.shift (TimedSim.set hK i f v (TimedSim.tick (n := n₂ + 1) hk (by omega))) m
    (by omega)

/-- A first-order `let` against the costed body with the charge of the bound value in
front. -/
theorem letE {e : Tm Γ a} {bt : Tm (a :: Γ) τ} {u : Val a} {x : ℕ × SPTree.Timed α}
    {n₁ n₂ ce c : ℕ} (he : DSim K n₁ ce e ρ u) (hb : TSim E K n₂ x bt (ρ.cons u))
    (hc : ce + x.1 ≤ c) : TSim E K (n₁ + n₂ + 1) (c, x.2) (.letE e bt) ρ := by
  obtain ⟨m, hm, l⟩ := he
  have hcK := Nat.mul_le_mul_left K hc
  rw [Nat.mul_add] at hcK
  exact TimedSim.eval_letE_ceq hm hb (by omega)

/-- A costed bind against `letE s k`; the β-step at each junction is paid by the allowance. -/
theorem bind {E₁ : γ → Val a → Prop} {s : Tm Γ a} {k : Tm (a :: Γ) τ}
    {x : ℕ × SPTree.Timed γ} {f : γ → ℕ × SPTree.Timed α} {n₁ n₂ : ℕ}
    (hs : TSim E₁ K n₁ x s ρ) (hk : ∀ y u, E₁ y u → TSim E K n₂ (f y) k (ρ.cons u)) :
    TSim E K (n₁ + n₂ + 1) (SPTree.Timed.delay x.1 (x.2.bind f)) (.letE s k) ρ := by
  have hs' : TimedSim E₁ K n₁ x (s.eval ρ) := hs
  unfold TSim
  rw [Tm.eval_letE]
  exact TimedSim.bind (m := n₂ + 1) hs' fun y u h =>
    TimedSim.tick (n := n₂ + 1) (c := (f y).1)
      (show TimedSim E K n₂ ((f y).1, (f y).2) (k.eval (ρ.cons u)) from hk y u h) (by omega)

/-- A costed conditional with charge `c ≥ 1 + cb` against `ite`; the β-step is paid by the unit
charge of the conditional. -/
theorem ite (hK : 1 ≤ K) {P : Prop} [Decidable P] {bt : Tm Γ .bool} {t e : Tm Γ τ}
    {x y : ℕ × SPTree.Timed α} {n₁ n₂ cb c : ℕ}
    (hb : DSim K n₁ cb bt ρ (decide P)) (ht : TSim E K n₂ x t ρ) (he : TSim E K n₂ y e ρ)
    (hc : 1 + cb ≤ c) :
    TSim E K (n₁ + n₂) (SPTree.Timed.delay c (if P then x else y)) (.ite bt t e) ρ := by
  obtain ⟨mb, hmb, l⟩ := hb
  have key : (Tm.ite bt t e).eval ρ =
      stepN CTree.tick (mb + 1) (bif decide P then t.eval ρ else e.eval ρ) := by
    show ((bt.eval ρ).bind (fun (v : Bool) => CTree.tick (bif v then t.eval ρ else e.eval ρ))) = _
    rw [hmb]
    exact (stepN_ret_bind mb (decide P) _).trans (stepN_tick_succ _ _)
  have hm : mb + 1 ≤ n₁ + K * c := by
    have := Nat.mul_le_mul_left K hc
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  unfold TSim
  rw [key]
  by_cases hP : P
  · have hb' : (bif decide P then t.eval ρ else e.eval ρ) = t.eval ρ := by simp [hP]
    rw [hb', ite_eq_left hP]
    exact TimedSim.stepN_delay hm ht
  · have hb' : (bif decide P then t.eval ρ else e.eval ρ) = e.eval ρ := by simp [hP]
    rw [hb', ite_eq_right hP]
    exact TimedSim.stepN_delay hm he

/-- A call of a tree function value `g` on a data argument: the evaluation of the argument and
the β-step against the charge `c ≥ 1 + cx + y.1` of the call. -/
theorem call (hK : 1 ≤ K) {F : Tm Γ (.arr a τ)} {x : Tm Γ a} {g : Val (.arr a τ)} {u : Val a}
    {y : ℕ × SPTree.Timed α} {n₁ n₂ cx c : ℕ}
    (hF : CEq F ρ 0 g) (hx : DSim K n₁ cx x ρ u) (hg : TimedSim E K n₂ y (g u))
    (hc : 1 + cx + y.1 ≤ c) : TSim E K (n₁ + n₂) (c, y.2) (.app F x) ρ := by
  obtain ⟨m, hm, l⟩ := hx
  have hcK := Nat.mul_le_mul_left K hc
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at hcK
  exact TimedSim.eval_app_ceq hF hm hg (by omega)

/-- A call of a tree function value on `unit`, the reflection of a tree without arguments: the
β-step has no counterpart in the costed tree and is paid by the allowance. -/
theorem call0 {F : Tm Γ (.arr .unit τ)} {g : Val (.arr .unit τ)}
    {y : ℕ × SPTree.Timed α} {n : ℕ} (hF : CEq F ρ 0 g) (hg : TimedSim E K n y (g ())) :
    TSim E K (n + 1) y (.app F (.lit .unit ())) ρ :=
  TimedSim.eval_app_ceq hF (CEq.lit .unit () ρ) hg (by omega)

end TSim

end TimedLink

end CatCrypt.Complexity.D
