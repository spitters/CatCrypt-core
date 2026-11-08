/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.SPTreeTimedOps
public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.XDijkstra.XTimedMonad
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.RingNF

/-!
# Rule lemmas of `time_bound`

The simp set `time_bound_simps` and the rule lemmas that `time_bound` and `allret_bound`
(`CatCryptCore.Tactics.AutoTime`) apply: the time bounds of costed binds and conditionals of
`SPTree.Timed` and of oracle trees under a leaf invariant, and the bounds of `if` by its branches
(`AutoTime.ite_le_ite_of`, `AutoTime.ite_le_max_of`). Users that state or prove with these import
this module publicly and the procedure privately.
-/

public section

set_option autoImplicit false

/-- Unfolding equations of costed definitions whose bodies `time_bound` does not see. -/
register_simp_attr time_bound_simps

/-! ## Time bounds of costed binds under a leaf invariant -/

namespace CatCrypt.Core.SPTree.Timed

variable {α β γ : Type}

/-- A predicate that holds everywhere holds at every leaf. -/
theorem allRet_of_forall {Q : α → Prop} (h : ∀ a, Q a) (t : SPTree.Timed α) : AllRet Q t :=
  allRet_mono (Q := fun _ => True) (fun a _ => h a) t (by
    induction t with
    | ret a => exact trivial
    | sample γ finγ neγ c k ih => exact ih
    | sampleDist γ μ c k ih => exact ih
    | get l c k ih => exact ih
    | set l v c t ih => exact ih
    | fail => exact trivial
    | load h₀ c t ih => exact ih)

/-- Two leaf invariants give their conjunction. -/
theorem allRet_and {Q R : α → Prop} {t : SPTree.Timed α} (hQ : AllRet Q t)
    (hR : AllRet R t) : AllRet (fun a => Q a ∧ R a) t := by
  induction t with
  | ret a => exact ⟨hQ, hR⟩
  | sample γ finγ neγ c k ih => exact fun b => ih b (hQ b) (hR b)
  | sampleDist γ μ c k ih => exact fun b => ih b (hQ b) (hR b)
  | get l c k ih => exact fun v => ih v (hQ v) (hR v)
  | set l v c t ih => exact ih hQ hR
  | fail => exact trivial
  | load h₀ c t ih => exact ih hQ hR

/-- The leaves of a costed bind satisfy `Q` when, at every leaf `a` of the tree, the leaves of
the continuation at `a` do. -/
theorem allRet_bind_of {Q : β → Prop} {t : SPTree.Timed α} {f : α → ℕ × SPTree.Timed β}
    (h : AllRet (fun a => AllRet Q (f a).2) t) : AllRet Q (t.bind f).2 :=
  (allRet_bind Q t f).2 h

/-- Two continuations that agree at the values satisfying a leaf invariant `Q` of the tree give
the same costed bind. -/
theorem bind_congr_of_allRet {Q : α → Prop} {A : SPTree.Timed α}
    {f g : α → ℕ × SPTree.Timed β} (hA : AllRet Q A) (h : ∀ a, Q a → f a = g a) :
    A.bind f = A.bind g := by
  induction A with
  | ret a => exact h a hA
  | sample γ finγ neγ c k ih =>
    have hk := fun b => ih b (hA b)
    simp only [bind, hk]
  | sampleDist γ μ c k ih =>
    have hk := fun b => ih b (hA b)
    simp only [bind, hk]
  | get l c k ih =>
    have hk := fun v => ih v (hA v)
    simp only [bind, hk]
  | set l v c t ih => simp only [bind, ih hA]
  | fail => rfl
  | load h₀ c t ih => simp only [bind, ih hA]

/-- The time of a costed bind is at most the time of the tree plus a bound `T` on the
continuation at the values satisfying a leaf invariant `Q` of the tree. -/
theorem stepTime_bind_le_of_allRet {Q : α → Prop} (A : SPTree.Timed α)
    (f : α → ℕ × SPTree.Timed β) (T : ℕ) (hA : AllRet Q A)
    (hf : ∀ a, Q a → stepTime (f a) ≤ T) : stepTime (A.bind f) ≤ A.time + T := by
  classical
  have h := stepTime_bind_le A (fun a => if Q a then f a else (0, fail)) T fun a => by
    split_ifs with hq
    · exact hf a hq
    · simp [stepTime, time_fail]
  rwa [bind_congr_of_allRet hA fun a hq => ite_eq_left hq] at h

/-- A step cost `C` in front of a costed bind whose continuation is bounded at the values
satisfying a leaf invariant of the tree. -/
theorem prefix_bind_le_of_allRet {Q : α → Prop} (C : ℕ) (k : SPTree.Timed α)
    (f : α → ℕ × SPTree.Timed β) (B : ℕ) (hk : AllRet Q k)
    (h : ∀ s, Q s → stepTime (f s) ≤ B) :
    C + (k.bind f).1 + (k.bind f).2.time ≤ C + (k.time + B) := by
  have := stepTime_bind_le_of_allRet k f B hk h
  simp only [stepTime] at this
  omega

/-- A costed run from a reset heap of a prefix `P` followed by a continuation `k` bounded at the
values satisfying a leaf invariant of `P`, in the step-prefixed form of `derive_reduction`. -/
theorem stepTime_load_bind_le_of_allRet {Q : β → Prop} (h₀ : Heap) (c₁ c₂ : ℕ)
    (P : ℕ × SPTree.Timed β) (k : β → ℕ × SPTree.Timed γ) {B K : ℕ} (hP : stepTime P ≤ B)
    (hQ : AllRet Q P.2) (hk : ∀ x, Q x → stepTime (k x) ≤ K) :
    stepTime ((0 : ℕ), load h₀ (c₁ + (c₂ + P.1) + (P.2.bind k).1) (P.2.bind k).2) ≤
      h₀.data.keys.card + c₁ + c₂ + B + K + 1 := by
  have := stepTime_bind_le_of_allRet P.2 k K hQ hk
  simp only [stepTime, time_load] at hP this ⊢
  omega

end CatCrypt.Core.SPTree.Timed

namespace CatCrypt.Tactics.AutoTime

open CatCrypt.Core CatCrypt.Crypto

/-! ## Rules for costed computation trees -/

section SPTree

variable {α β : Type} {P B : ℕ}

theorem st_start {x : ℕ × SPTree.Timed α} (h : 0 + SPTree.Timed.stepTime x ≤ B) :
    SPTree.Timed.stepTime x ≤ B := by
  simpa using h

theorem time_start {t : SPTree.Timed α} (h : 0 + t.time ≤ B) : t.time ≤ B := by
  simpa using h

theorem st_pair {c : ℕ} {t : SPTree.Timed α} (h : P + c + t.time ≤ B) :
    P + SPTree.Timed.stepTime (c, t) ≤ B := by
  simp only [SPTree.Timed.stepTime]
  omega

/-- A pair `(e, y.2)` whose step cost `e` is `c + y.1`: the pair is `y` after `c`. -/
theorem st_pair_fst {e c : ℕ} {y : ℕ × SPTree.Timed α} (he : e = c + y.1)
    (h : P + c + SPTree.Timed.stepTime y ≤ B) : P + SPTree.Timed.stepTime (e, y.2) ≤ B := by
  subst he
  simp only [SPTree.Timed.stepTime] at h ⊢
  omega

theorem fst_le_of_stepTime {x : ℕ × SPTree.Timed α} {E : ℕ}
    (h : SPTree.Timed.stepTime x ≤ E) : x.1 ≤ E := by
  simp only [SPTree.Timed.stepTime] at h
  omega

theorem st_delay {c : ℕ} {x : ℕ × SPTree.Timed α} (h : P + c + SPTree.Timed.stepTime x ≤ B) :
    P + SPTree.Timed.stepTime (SPTree.Timed.delay c x) ≤ B := by
  rw [SPTree.Timed.stepTime_delay]
  omega

theorem st_map {f : α → β} {fc : α → ℕ} {A : SPTree.Timed α}
    (h : P + SPTree.Timed.stepTime (A.bind fun a => (fc a, .ret (f a))) ≤ B) :
    P + SPTree.Timed.stepTime (A.map f fc) ≤ B :=
  h

theorem st_ite {c : Prop} [Decidable c] {x y : ℕ × SPTree.Timed α}
    (hx : c → P + SPTree.Timed.stepTime x ≤ B) (hy : ¬c → P + SPTree.Timed.stepTime y ≤ B) :
    P + SPTree.Timed.stepTime (if c then x else y) ≤ B := by
  by_cases hc : c
  · simpa only [ite_eq_left hc] using hx hc
  · simpa only [ite_eq_right hc] using hy hc

theorem st_dite {c : Prop} [Decidable c] {x : c → ℕ × SPTree.Timed α}
    {y : ¬c → ℕ × SPTree.Timed α} (hx : ∀ h : c, P + SPTree.Timed.stepTime (x h) ≤ B)
    (hy : ∀ h : ¬c, P + SPTree.Timed.stepTime (y h) ≤ B) :
    P + SPTree.Timed.stepTime (if h : c then x h else y h) ≤ B := by
  by_cases hc : c
  · simpa only [dite_eq_left hc] using hx hc
  · simpa only [dite_eq_right hc] using hy hc

theorem st_bind_ret {a : α} {f : α → ℕ × SPTree.Timed β}
    (h : P + SPTree.Timed.stepTime (f a) ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.ret a).bind f) ≤ B := by
  simpa only [SPTree.Timed.bind] using h

theorem st_bind_sample {γ : Type} {fγ : Fintype γ} {nγ : Nonempty γ} {c : γ → ℕ}
    {k : γ → SPTree.Timed α} {f : α → ℕ × SPTree.Timed β}
    (h : ∀ b, P + 1 + c b + SPTree.Timed.stepTime ((k b).bind f) ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.sample γ fγ nγ c k).bind f) ≤ B := by
  let _ := fγ
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_sample, Nat.zero_add]
  have hs : (Finset.univ.sup fun b => c b + (SPTree.Timed.bind (k b) f).1 +
      (SPTree.Timed.bind (k b) f).2.time) ≤ B - P - 1 :=
    Finset.sup_le fun b _ => by
      have := h b
      simp only [SPTree.Timed.stepTime] at this
      omega
  have h0 := h (Classical.choice nγ)
  omega

theorem st_bind_get {l : Location} {c : l.ty → ℕ} {k : l.ty → SPTree.Timed α}
    {f : α → ℕ × SPTree.Timed β} (h0 : P + 1 ≤ B)
    (h : ∀ v, P + 1 + c v + SPTree.Timed.stepTime ((k v).bind f) ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.get l c k).bind f) ≤ B := by
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_get, Nat.zero_add]
  have hs : (Finset.univ.sup fun v => c v + (SPTree.Timed.bind (k v) f).1 +
      (SPTree.Timed.bind (k v) f).2.time) ≤ B - P - 1 :=
    Finset.sup_le fun v _ => by
      have := h v
      simp only [SPTree.Timed.stepTime] at this
      omega
  omega

theorem st_bind_set {l : Location} {v : l.ty} {c : ℕ} {t : SPTree.Timed α}
    {f : α → ℕ × SPTree.Timed β} (h : P + 1 + c + SPTree.Timed.stepTime (t.bind f) ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.set l v c t).bind f) ≤ B := by
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_set] at h ⊢
  omega

theorem st_bind_fail {f : α → ℕ × SPTree.Timed β} (h : P ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.fail : SPTree.Timed α).bind f) ≤ B := by
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_fail]
  omega

/-- A bind after a tree `A` that is not a node: the time of `A` joins the path. -/
theorem st_bind {A : SPTree.Timed α} {f : α → ℕ × SPTree.Timed β} (h0 : P + A.time ≤ B)
    (h : ∀ a, P + A.time + SPTree.Timed.stepTime (f a) ≤ B) :
    P + SPTree.Timed.stepTime (A.bind f) ≤ B := by
  have := SPTree.Timed.stepTime_bind_le A f (B - P - A.time) fun a => by
    have := h a
    omega
  omega

theorem st_of {x : ℕ × SPTree.Timed α} {T : ℕ} (h : SPTree.Timed.stepTime x ≤ T)
    (h0 : P + T ≤ B) : P + SPTree.Timed.stepTime x ≤ B := by
  omega

theorem time_ret {a : α} (h : P ≤ B) : P + (SPTree.Timed.ret a).time ≤ B := by
  simp only [SPTree.Timed.time_ret]
  omega

theorem time_sample {γ : Type} {fγ : Fintype γ} {nγ : Nonempty γ} {c : γ → ℕ}
    {k : γ → SPTree.Timed α} (h : ∀ b, P + 1 + c b + (k b).time ≤ B) :
    P + (SPTree.Timed.sample γ fγ nγ c k).time ≤ B := by
  let _ := fγ
  rw [SPTree.Timed.time_sample]
  have hs : (Finset.univ.sup fun b => c b + (k b).time) ≤ B - P - 1 :=
    Finset.sup_le fun b _ => by
      have := h b
      omega
  have h0 := h (Classical.choice nγ)
  omega

/-- The time of a sampling node of a sub-distribution: its unit and, for every sample, the step
cost and the time of the continuation. The second hypothesis bounds the unit on an empty
sample space. -/
theorem time_sampleDist {γ : Type} {μ : Prob.SDistr γ} {c : γ → ℕ} {k : γ → SPTree.Timed α}
    (h : ∀ b, P + 1 + c b + (k b).time ≤ B) (h₀ : P + 1 ≤ B) :
    P + (SPTree.Timed.sampleDist γ μ c k).time ≤ B := by
  rw [SPTree.Timed.time_sampleDist]
  have hs : (⨆ b, c b + (k b).time) ≤ B - P - 1 :=
    ciSup_le' fun b => by
      have := h b
      omega
  omega

/-- The step time of a sampling node of a sub-distribution followed by a costed bind. -/
theorem st_bind_sampleDist {γ : Type} {μ : Prob.SDistr γ} {c : γ → ℕ}
    {k : γ → SPTree.Timed α} {f : α → ℕ × SPTree.Timed β}
    (h : ∀ b, P + 1 + c b + SPTree.Timed.stepTime ((k b).bind f) ≤ B) (h₀ : P + 1 ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.sampleDist γ μ c k).bind f) ≤ B := by
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_sampleDist,
    Nat.zero_add]
  have hs : (⨆ b, c b + (SPTree.Timed.bind (k b) f).1 + (SPTree.Timed.bind (k b) f).2.time) ≤
      B - P - 1 :=
    ciSup_le' fun b => by
      have := h b
      simp only [SPTree.Timed.stepTime] at this
      omega
  omega

theorem time_get {l : Location} {c : l.ty → ℕ} {k : l.ty → SPTree.Timed α} (h0 : P + 1 ≤ B)
    (h : ∀ v, P + 1 + c v + (k v).time ≤ B) : P + (SPTree.Timed.get l c k).time ≤ B := by
  rw [SPTree.Timed.time_get]
  have hs : (Finset.univ.sup fun v => c v + (k v).time) ≤ B - P - 1 :=
    Finset.sup_le fun v _ => by
      have := h v
      omega
  omega

theorem time_set {l : Location} {v : l.ty} {c : ℕ} {t : SPTree.Timed α}
    (h : P + 1 + c + t.time ≤ B) : P + (SPTree.Timed.set l v c t).time ≤ B := by
  rw [SPTree.Timed.time_set]
  omega

theorem time_fail (h : P ≤ B) : P + (SPTree.Timed.fail : SPTree.Timed α).time ≤ B := by
  rw [SPTree.Timed.time_fail]
  omega

/-- The tree `y.2` on a path whose cost `P` has the summand `y.1`: the two are `stepTime y`. -/
theorem time_snd_fst {Q : ℕ} {y : ℕ × SPTree.Timed α} (he : P = Q + y.1)
    (h : Q + SPTree.Timed.stepTime y ≤ B) : P + y.2.time ≤ B := by
  subst he
  simp only [SPTree.Timed.stepTime] at h
  omega

/-- The step cost of a costed bind `A.bind g` in front of a bind after its tree: the time of
the bind of `A` into the continuations `g s` followed by `k`. -/
theorem stepTime_fst_bind_bind {γ : Type} (A : SPTree.Timed γ) (g : γ → ℕ × SPTree.Timed α)
    (k : α → ℕ × SPTree.Timed β) :
    (A.bind g).1 + SPTree.Timed.stepTime ((A.bind g).2.bind k) =
      SPTree.Timed.stepTime (A.bind fun s => SPTree.Timed.delay (g s).1 ((g s).2.bind k)) := by
  induction A with
  | ret a => simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.delay]; omega
  | sample γ' finγ neγ c k' ih =>
    let _ := finγ
    simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_sample,
      Nat.zero_add]
    congr 2
    funext b
    have := ih b
    simp only [SPTree.Timed.stepTime] at this
    omega
  | sampleDist γ' μ c k' ih =>
    simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_sampleDist,
      Nat.zero_add]
    congr 2
    funext b
    have := ih b
    simp only [SPTree.Timed.stepTime] at this
    omega
  | get l c k' ih =>
    simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_get, Nat.zero_add]
    congr 2
    funext v
    have := ih v
    simp only [SPTree.Timed.stepTime] at this
    omega
  | set l v c t ih =>
    simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_set] at ih ⊢
    omega
  | fail => simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_fail]
  | load h₀ c t ih =>
    simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_load] at ih ⊢
    omega

/-- The step cost of a costed bind `A.bind g` is at most a bound `c` of the step costs of the
continuations `g a`. -/
theorem bind_fst_le {γ : Type} (A : SPTree.Timed γ) {g : γ → ℕ × SPTree.Timed α} {c : ℕ}
    (h : ∀ a, (g a).1 ≤ c) : (A.bind g).1 ≤ c := by
  cases A with
  | ret a => exact h a
  | _ => exact Nat.zero_le _

/-- A bind after the tree `y.2` of a costed bind `y = A.bind g` on a path whose cost `P` has the
summand `y.1`: the two are the bind of `A` into the continuations `g s` followed by `k`. -/
theorem st_snd_bind_fst {γ : Type} {Q : ℕ} {A : SPTree.Timed γ} {g : γ → ℕ × SPTree.Timed α}
    {k : α → ℕ × SPTree.Timed β} (he : P = Q + (A.bind g).1)
    (h : Q + SPTree.Timed.stepTime
      (A.bind fun s => SPTree.Timed.delay (g s).1 ((g s).2.bind k)) ≤ B) :
    P + SPTree.Timed.stepTime ((A.bind g).2.bind k) ≤ B := by
  subst he
  rw [← stepTime_fst_bind_bind] at h
  omega

theorem time_snd {x : ℕ × SPTree.Timed α} (h : P + SPTree.Timed.stepTime x ≤ B) :
    P + x.2.time ≤ B := by
  simp only [SPTree.Timed.stepTime] at h
  omega

theorem time_ite {c : Prop} [Decidable c] {x y : SPTree.Timed α}
    (hx : c → P + x.time ≤ B) (hy : ¬c → P + y.time ≤ B) :
    P + (if c then x else y).time ≤ B := by
  by_cases hc : c
  · simpa only [ite_eq_left hc] using hx hc
  · simpa only [ite_eq_right hc] using hy hc

theorem time_dite {c : Prop} [Decidable c] {x : c → SPTree.Timed α} {y : ¬c → SPTree.Timed α}
    (hx : ∀ h : c, P + (x h).time ≤ B) (hy : ∀ h : ¬c, P + (y h).time ≤ B) :
    P + (if h : c then x h else y h).time ≤ B := by
  by_cases hc : c
  · simpa only [dite_eq_left hc] using hx hc
  · simpa only [dite_eq_right hc] using hy hc

theorem time_of {t : SPTree.Timed α} {T : ℕ} (h : t.time ≤ T) (h0 : P + T ≤ B) :
    P + t.time ≤ B := by
  omega

theorem time_load {h₀ : Heap} {c : ℕ} {t : SPTree.Timed α}
    (h : P + 1 + h₀.data.keys.card + c + t.time ≤ B) :
    P + (SPTree.Timed.load h₀ c t).time ≤ B := by
  rw [SPTree.Timed.time_load]
  omega

/-- An arithmetic leaf read as a path `Q` followed by the time `T` of a tree. -/
theorem arith_time (l Q T B : ℕ) (he : l = Q + T) (h : Q + T ≤ B) : l ≤ B := by
  omega

/-- A bind after a tree `A` that is not a node, with a leaf invariant `Q` of `A`: the
continuation is bounded at the values satisfying `Q`. -/
theorem st_bind_inv {Q : α → Prop} {A : SPTree.Timed α} {f : α → ℕ × SPTree.Timed β}
    (hA : SPTree.Timed.AllRet Q A) (h0 : P + A.time ≤ B)
    (h : ∀ a, Q a → P + A.time + SPTree.Timed.stepTime (f a) ≤ B) :
    P + SPTree.Timed.stepTime (A.bind f) ≤ B := by
  have := SPTree.Timed.stepTime_bind_le_of_allRet A f (B - P - A.time) hA fun a ha => by
    have := h a ha
    omega
  omega

/-! ### Rules for leaf invariants -/

theorem ar_ret {Q : α → Prop} {a : α} (h : Q a) : SPTree.Timed.AllRet Q (.ret a) := h

theorem ar_sample {Q : α → Prop} {γ : Type} {fγ : Fintype γ} {nγ : Nonempty γ} {c : γ → ℕ}
    {k : γ → SPTree.Timed α} (h : ∀ b, SPTree.Timed.AllRet Q (k b)) :
    SPTree.Timed.AllRet Q (.sample γ fγ nγ c k) := h

theorem ar_get {Q : α → Prop} {l : Location} {c : l.ty → ℕ} {k : l.ty → SPTree.Timed α}
    (h : ∀ v, SPTree.Timed.AllRet Q (k v)) : SPTree.Timed.AllRet Q (.get l c k) := h

theorem ar_set {Q : α → Prop} {l : Location} {v : l.ty} {c : ℕ} {t : SPTree.Timed α}
    (h : SPTree.Timed.AllRet Q t) : SPTree.Timed.AllRet Q (.set l v c t) := h

theorem ar_load {Q : α → Prop} {h₀ : Heap} {c : ℕ} {t : SPTree.Timed α}
    (h : SPTree.Timed.AllRet Q t) : SPTree.Timed.AllRet Q (.load h₀ c t) := h

theorem ar_fail {Q : α → Prop} : SPTree.Timed.AllRet Q (.fail : SPTree.Timed α) := trivial

theorem ar_ite {Q : α → Prop} {c : Prop} [Decidable c] {x y : SPTree.Timed α}
    (hx : c → SPTree.Timed.AllRet Q x) (hy : ¬c → SPTree.Timed.AllRet Q y) :
    SPTree.Timed.AllRet Q (if c then x else y) := by
  by_cases hc : c
  · simpa only [ite_eq_left hc] using hx hc
  · simpa only [ite_eq_right hc] using hy hc

theorem ar_dite {Q : α → Prop} {c : Prop} [Decidable c] {x : c → SPTree.Timed α}
    {y : ¬c → SPTree.Timed α} (hx : ∀ h : c, SPTree.Timed.AllRet Q (x h))
    (hy : ∀ h : ¬c, SPTree.Timed.AllRet Q (y h)) :
    SPTree.Timed.AllRet Q (if h : c then x h else y h) := by
  by_cases hc : c
  · simpa only [dite_eq_left hc] using hx hc
  · simpa only [dite_eq_right hc] using hy hc

theorem ar_bind {Q : β → Prop} {A : SPTree.Timed α} {f : α → ℕ × SPTree.Timed β}
    (h : SPTree.Timed.AllRet (fun a => SPTree.Timed.AllRet Q (f a).2) A) :
    SPTree.Timed.AllRet Q (A.bind f).2 :=
  SPTree.Timed.allRet_bind_of h

/-- A tree whose leaves are not visible: the invariant at every value. -/
theorem ar_any {Q : α → Prop} {t : SPTree.Timed α} (h : ∀ a, Q a) : SPTree.Timed.AllRet Q t :=
  SPTree.Timed.allRet_of_forall h t

end SPTree

/-! ## Rules for costed oracle adversaries -/

section Oracle

variable {D R α β : Type} {P B : ℕ}

theorem tb_start {A : OracleAdv.Timed D R α} {n : ℕ} (h : A.TimeBound (n - 0)) :
    A.TimeBound n := by
  simpa using h

theorem stb_start {x : ℕ × OracleAdv.Timed D R α} {n : ℕ}
    (h : OracleAdv.Timed.StepTimeBound x (n - 0)) : OracleAdv.Timed.StepTimeBound x n := by
  simpa using h

theorem tb_ret {a : α} {n : ℕ} : (OracleAdv.Timed.ret a : OracleAdv.Timed D R α).TimeBound n :=
  trivial

theorem tb_rand {γ : Type} {p : PMF γ} {c : γ → ℕ} {k : γ → OracleAdv.Timed D R α}
    (h0 : P + 1 ≤ B) (h1 : ∀ b, P + 1 + c b ≤ B)
    (h2 : ∀ b, (k b).TimeBound (B - (P + 1 + c b))) :
    (OracleAdv.Timed.rand p c k).TimeBound (B - P) := by
  refine ⟨by omega, fun b => ⟨by have := h1 b; omega, ?_⟩⟩
  have e : B - P - 1 - c b = B - (P + 1 + c b) := by omega
  rw [e]
  exact h2 b

theorem tb_query {d : D} {c : R → ℕ} {k : R → OracleAdv.Timed D R α}
    (h0 : P + 1 ≤ B) (h1 : ∀ r, P + 1 + c r ≤ B)
    (h2 : ∀ r, (k r).TimeBound (B - (P + 1 + c r))) :
    (OracleAdv.Timed.query d c k).TimeBound (B - P) := by
  refine ⟨by omega, fun r => ⟨by have := h1 r; omega, ?_⟩⟩
  have e : B - P - 1 - c r = B - (P + 1 + c r) := by omega
  rw [e]
  exact h2 r

theorem tb_ite {c : Prop} [Decidable c] {x y : OracleAdv.Timed D R α}
    (hx : c → x.TimeBound (B - P)) (hy : ¬c → y.TimeBound (B - P)) :
    (if c then x else y).TimeBound (B - P) := by
  by_cases hc : c
  · simpa only [ite_eq_left hc] using hx hc
  · simpa only [ite_eq_right hc] using hy hc

theorem tb_dite {c : Prop} [Decidable c] {x : c → OracleAdv.Timed D R α}
    {y : ¬c → OracleAdv.Timed D R α} (hx : ∀ h : c, (x h).TimeBound (B - P))
    (hy : ∀ h : ¬c, (y h).TimeBound (B - P)) :
    (if h : c then x h else y h).TimeBound (B - P) := by
  by_cases hc : c
  · simpa only [dite_eq_left hc] using hx hc
  · simpa only [dite_eq_right hc] using hy hc

theorem tb_of {A : OracleAdv.Timed D R α} {T : ℕ} (h : A.TimeBound T) (h0 : P + T ≤ B) :
    A.TimeBound (B - P) :=
  h.mono (by omega)

theorem tb_snd {x : ℕ × OracleAdv.Timed D R α} (h : OracleAdv.Timed.StepTimeBound x (B - P)) :
    x.2.TimeBound (B - P) :=
  h.2.mono (Nat.sub_le _ _)

/-- The adversary of a step-prefixed tree of time `T` has time `T` less the step cost. -/
theorem tb_snd_of_stb {x : ℕ × OracleAdv.Timed D R α} {T : ℕ}
    (h : OracleAdv.Timed.StepTimeBound x T) : x.2.TimeBound (T - x.1) :=
  h.2

theorem stb_pair {c : ℕ} {A : OracleAdv.Timed D R α} (h0 : P + c ≤ B)
    (h : A.TimeBound (B - (P + c))) : OracleAdv.Timed.StepTimeBound (c, A) (B - P) := by
  refine ⟨by dsimp only; omega, ?_⟩
  have e : B - P - c = B - (P + c) := by omega
  simpa only [e] using h

/-- A pair `(e, y.2)` whose step cost `e` is `c + y.1`: the pair is `y` after `c`. -/
theorem stb_pair_fst {e c : ℕ} {y : ℕ × OracleAdv.Timed D R α} (he : e = c + y.1)
    (h0 : P + c ≤ B) (h : OracleAdv.Timed.StepTimeBound y (B - (P + c))) :
    OracleAdv.Timed.StepTimeBound (e, y.2) (B - P) := by
  subst he
  obtain ⟨h1, h2⟩ := h
  refine ⟨by dsimp only; omega, ?_⟩
  have e' : B - P - (c + y.1) = B - (P + c) - y.1 := by omega
  dsimp only
  rw [e']
  exact h2

theorem fst_le_of_stb {x : ℕ × OracleAdv.Timed D R α} {E : ℕ}
    (h : OracleAdv.Timed.StepTimeBound x E) : x.1 ≤ E :=
  h.1

theorem stb_delay {c : ℕ} {x : ℕ × OracleAdv.Timed D R α} (h0 : P + c ≤ B)
    (h : OracleAdv.Timed.StepTimeBound x (B - (P + c))) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay c x) (B - P) :=
  (OracleAdv.Timed.stepTimeBound_delay h).mono (by omega)

theorem stb_ite {c : Prop} [Decidable c] {x y : ℕ × OracleAdv.Timed D R α}
    (hx : c → OracleAdv.Timed.StepTimeBound x (B - P))
    (hy : ¬c → OracleAdv.Timed.StepTimeBound y (B - P)) :
    OracleAdv.Timed.StepTimeBound (if c then x else y) (B - P) := by
  by_cases hc : c
  · simpa only [ite_eq_left hc] using hx hc
  · simpa only [ite_eq_right hc] using hy hc

theorem stb_dite {c : Prop} [Decidable c] {x : c → ℕ × OracleAdv.Timed D R α}
    {y : ¬c → ℕ × OracleAdv.Timed D R α}
    (hx : ∀ h : c, OracleAdv.Timed.StepTimeBound (x h) (B - P))
    (hy : ∀ h : ¬c, OracleAdv.Timed.StepTimeBound (y h) (B - P)) :
    OracleAdv.Timed.StepTimeBound (if h : c then x h else y h) (B - P) := by
  by_cases hc : c
  · simpa only [dite_eq_left hc] using hx hc
  · simpa only [dite_eq_right hc] using hy hc

theorem stb_bind_ret {a : α} {f : α → ℕ × OracleAdv.Timed D R β}
    (h : OracleAdv.Timed.StepTimeBound (f a) (B - P)) :
    OracleAdv.Timed.StepTimeBound ((OracleAdv.Timed.ret a).bind f) (B - P) := by
  simpa only [OracleAdv.Timed.bind] using h

theorem stb_bind_rand {γ : Type} {p : PMF γ} {c : γ → ℕ} {k : γ → OracleAdv.Timed D R α}
    {f : α → ℕ × OracleAdv.Timed D R β} (h0 : P + 1 ≤ B) (h1 : ∀ b, P + 1 + c b ≤ B)
    (h2 : ∀ b, OracleAdv.Timed.StepTimeBound ((k b).bind f) (B - (P + 1 + c b))) :
    OracleAdv.Timed.StepTimeBound ((OracleAdv.Timed.rand p c k).bind f) (B - P) := by
  simp only [OracleAdv.Timed.bind, OracleAdv.Timed.stepTimeBound_zero]
  refine ⟨by omega, fun b => ⟨?_, ?_⟩⟩ <;> dsimp only
  · have := h1 b
    have := (h2 b).1
    omega
  · have := h1 b
    have := (h2 b).1
    have e : B - P - 1 - (c b + ((k b).bind f).1) = B - (P + 1 + c b) - ((k b).bind f).1 := by
      omega
    rw [e]
    exact (h2 b).2

theorem stb_bind_query {d : D} {c : R → ℕ} {k : R → OracleAdv.Timed D R α}
    {f : α → ℕ × OracleAdv.Timed D R β} (h0 : P + 1 ≤ B) (h1 : ∀ r, P + 1 + c r ≤ B)
    (h2 : ∀ r, OracleAdv.Timed.StepTimeBound ((k r).bind f) (B - (P + 1 + c r))) :
    OracleAdv.Timed.StepTimeBound ((OracleAdv.Timed.query d c k).bind f) (B - P) := by
  simp only [OracleAdv.Timed.bind, OracleAdv.Timed.stepTimeBound_zero]
  refine ⟨by omega, fun r => ⟨?_, ?_⟩⟩ <;> dsimp only
  · have := h1 r
    have := (h2 r).1
    omega
  · have := h1 r
    have := (h2 r).1
    have e : B - P - 1 - (c r + ((k r).bind f).1) = B - (P + 1 + c r) - ((k r).bind f).1 := by
      omega
    rw [e]
    exact (h2 r).2

/-- A bind after an adversary `A` of time `T` that is not a node: `T` joins the path. -/
theorem stb_bind {A : OracleAdv.Timed D R α} {f : α → ℕ × OracleAdv.Timed D R β} {T : ℕ}
    (hA : A.TimeBound T) (h0 : P + T ≤ B)
    (hf : ∀ a, OracleAdv.Timed.StepTimeBound (f a) (B - (P + T))) :
    OracleAdv.Timed.StepTimeBound (A.bind f) (B - P) :=
  (OracleAdv.Timed.timeBound_bind hA hf).mono (by omega)

theorem stb_of {x : ℕ × OracleAdv.Timed D R α} {T : ℕ}
    (h : OracleAdv.Timed.StepTimeBound x T) (h0 : P + T ≤ B) :
    OracleAdv.Timed.StepTimeBound x (B - P) :=
  h.mono (by omega)

end Oracle

/-- An `if` is at most the `if` on the same condition of larger branches. -/
theorem ite_le_ite_of {c : Prop} [Decidable c] {a b a' b' : ℕ} (h₁ : a ≤ a') (h₂ : b ≤ b') :
    (if c then a else b) ≤ (if c then a' else b') := by
  split <;> assumption

/-- An `if` is at most the maximum of larger branches. -/
theorem ite_le_max_of {c : Prop} [Decidable c] {a b a' b' : ℕ} (h₁ : a ≤ a') (h₂ : b ≤ b') :
    (if c then a else b) ≤ max a' b' := by
  split <;> omega

end CatCrypt.Tactics.AutoTime

end
