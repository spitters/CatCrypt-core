/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCryptCore.Core.SPTreeTimed
import all CatCryptCore.Core.SPTreeTimed

@[expose] public meta section

set_option autoImplicit false

/-!
# Costed combinators of syntactic computation trees

The combinators that build `SPTree` values, `SPTree.bind` and `SPTree.map`, together with
their costed forms on `SPTree.Timed` in the step-prefixed convention of `derive_timed`: a
costed tree is a pair `(c, t) : ℕ × SPTree.Timed α` of a step cost `c`, the cost of computing
the first node of `t`, and the costed tree `t`. Its time `SPTree.Timed.stepTime` is
`c + t.time`.

The costed bind charges the step cost of the continuation at each leaf to the continuation of
the node above the leaf; the costed map charges the cost of the function at each leaf.

## Main definitions

* `SPTree.map` — apply a function to the leaves
* `SPTree.Timed.delay`, `SPTree.Timed.stepTime` — a step cost in front, the time of a pair
* `SPTree.Timed.bind`, `SPTree.Timed.map` — costed forms of `SPTree.bind` and `SPTree.map`

## Main results

* `SPTree.Timed.erase_bind`, `SPTree.Timed.erase_map` — erasure gives the uncosted combinator
* `SPTree.Timed.stepTime_bind_le`, `SPTree.Timed.stepTime_map_le`,
  `SPTree.Timed.prefix_bind_le` — times add
* `SPTree.Timed.erase_snd_ite`, `SPTree.Timed.erase_snd_dite` — erasure commutes with `if`
-/

namespace CatCrypt.Core

namespace SPTree

variable {α β : Type}

/-- The tree `s` with `f` applied to its leaves. -/
def map (f : α → β) (s : SPTree α) : SPTree β := s.bind fun a => .ret (f a)

theorem compile_map (f : α → β) (s : SPTree α) :
    (s.map f).compile = SPComp.bind s.compile fun a => SPComp.pure (f a) := by
  simp only [map, compile_bind, compile_ret]

end SPTree

namespace SPTree.Timed

variable {α β : Type}

theorem erase_ret (a : α) : (ret a : SPTree.Timed α).erase = .ret a := by
  simp only [erase]

theorem erase_sample (γ : Type) (finγ : Fintype γ) (neγ : Nonempty γ) (c : γ → ℕ)
    (k : γ → SPTree.Timed α) :
    (sample γ finγ neγ c k).erase = .sample γ finγ neγ fun b => (k b).erase := by
  simp only [erase]

theorem erase_get (l : Location) (c : l.ty → ℕ) (k : l.ty → SPTree.Timed α) :
    (get l c k).erase = .get l fun v => (k v).erase := by
  simp only [erase]

theorem erase_set (l : Location) (v : l.ty) (c : ℕ) (t : SPTree.Timed α) :
    (set l v c t).erase = .set l v t.erase := by
  simp only [erase]

theorem erase_fail : (fail : SPTree.Timed α).erase = .fail := by
  simp only [erase]

theorem time_ret (a : α) : (ret a : SPTree.Timed α).time = 0 := by
  simp only [time]

theorem time_sample (γ : Type) (finγ : Fintype γ) (neγ : Nonempty γ) (c : γ → ℕ)
    (k : γ → SPTree.Timed α) :
    (sample γ finγ neγ c k).time = 1 + @Finset.sup ℕ γ _ _ (@Finset.univ γ finγ)
      fun b => c b + (k b).time := by
  simp only [time]

theorem time_get (l : Location) (c : l.ty → ℕ) (k : l.ty → SPTree.Timed α) :
    (get l c k).time = 1 + Finset.univ.sup fun v => c v + (k v).time := by
  simp only [time]

theorem time_set (l : Location) (v : l.ty) (c : ℕ) (t : SPTree.Timed α) :
    (set l v c t).time = 1 + (c + t.time) := by
  simp only [time]

theorem time_fail : (fail : SPTree.Timed α).time = 0 := by
  simp only [time]

/-- The step cost `c` in front of the step-prefixed tree `x`. -/
def delay (c : ℕ) (x : ℕ × SPTree.Timed α) : ℕ × SPTree.Timed α := (c + x.1, x.2)

/-- The time of a step-prefixed tree: its step cost plus the time of the tree. -/
def stepTime (x : ℕ × SPTree.Timed α) : ℕ := x.1 + x.2.time

/-- Costed bind: the continuation `f` returns a step-prefixed tree, whose step cost is added to
the step cost of the continuation leading to the leaf. -/
def bind : SPTree.Timed α → (α → ℕ × SPTree.Timed β) → ℕ × SPTree.Timed β
  | ret a, f => f a
  | sample γ finγ neγ c k, f =>
    (0, sample γ finγ neγ (fun b => c b + (bind (k b) f).1) fun b => (bind (k b) f).2)
  | get l c k, f => (0, get l (fun v => c v + (bind (k v) f).1) fun v => (bind (k v) f).2)
  | set l v c t, f => (0, set l v (c + (bind t f).1) (bind t f).2)
  | fail, _ => (0, fail)

/-- Costed map: `f` at a leaf `a` costs `fc a`. -/
def map (f : α → β) (fc : α → ℕ) (A : SPTree.Timed α) : ℕ × SPTree.Timed β :=
  A.bind fun a => (fc a, ret (f a))

theorem erase_bind (A : SPTree.Timed α) (f : α → ℕ × SPTree.Timed β) :
    (A.bind f).2.erase = A.erase.bind fun a => (f a).2.erase := by
  induction A with
  | ret a => rfl
  | sample γ finγ neγ c k ih => simp only [bind, erase, SPTree.bind, ih]
  | get l c k ih => simp only [bind, erase, SPTree.bind, ih]
  | set l v c t ih => simp only [bind, erase, SPTree.bind, ih]
  | fail => rfl

theorem erase_map (f : α → β) (fc : α → ℕ) (A : SPTree.Timed α) :
    (A.map f fc).2.erase = A.erase.map f := by
  simp only [map, erase_bind, SPTree.map, erase]

theorem stepTime_delay (c : ℕ) (x : ℕ × SPTree.Timed α) :
    stepTime (delay c x) = c + stepTime x := by
  simp only [stepTime, delay, Nat.add_assoc]

/-- The time of a costed bind is at most the time of the tree plus a bound `T` on the times of
the continuation. -/
theorem stepTime_bind_le (A : SPTree.Timed α) (f : α → ℕ × SPTree.Timed β) (T : ℕ)
    (hf : ∀ a, stepTime (f a) ≤ T) : stepTime (A.bind f) ≤ A.time + T := by
  induction A with
  | ret a => simpa [bind, time] using hf a
  | sample γ finγ neγ c k ih =>
    let _ := finγ
    simp only [stepTime, bind, time, Nat.zero_add]
    have hs : (Finset.univ.sup fun b => c b + (bind (k b) f).1 + (bind (k b) f).2.time) ≤
        (Finset.univ.sup fun b => c b + (k b).time) + T :=
      Finset.sup_le fun b _ => by
        have h1 := ih b
        have h2 : c b + (k b).time ≤ Finset.univ.sup fun b => c b + (k b).time :=
          Finset.le_sup (f := fun b => c b + (k b).time) (Finset.mem_univ b)
        simp only [stepTime] at h1
        omega
    omega
  | get l c k ih =>
    simp only [stepTime, bind, time, Nat.zero_add]
    have hs : (Finset.univ.sup fun v => c v + (bind (k v) f).1 + (bind (k v) f).2.time) ≤
        (Finset.univ.sup fun v => c v + (k v).time) + T :=
      Finset.sup_le fun v _ => by
        have h1 := ih v
        have h2 : c v + (k v).time ≤ Finset.univ.sup fun v => c v + (k v).time :=
          Finset.le_sup (f := fun v => c v + (k v).time) (Finset.mem_univ v)
        simp only [stepTime] at h1
        omega
    omega
  | set l v c t ih =>
    simp only [stepTime, bind, time] at ih ⊢
    omega
  | fail => simp [stepTime, bind, time]

/-- The time of a costed map is at most the time of the tree plus a bound `t` on the cost of
the function. -/
theorem stepTime_map_le (f : α → β) (fc : α → ℕ) (A : SPTree.Timed α) (t : ℕ)
    (hf : ∀ a, fc a ≤ t) : stepTime (A.map f fc) ≤ A.time + t :=
  stepTime_bind_le A _ t fun a => by simpa [stepTime, time] using hf a

/-- A step cost `C` in front of a costed bind: its time is at most `C`, the time of the tree
and a bound on the times of the continuation. -/
theorem prefix_bind_le (C : ℕ) (k : SPTree.Timed α) (f : α → ℕ × SPTree.Timed β) (B : ℕ)
    (h : ∀ s, stepTime (f s) ≤ B) :
    C + (k.bind f).1 + (k.bind f).2.time ≤ C + (k.time + B) := by
  have := stepTime_bind_le k f B h
  simp only [stepTime] at this
  omega

/-- Erasure of a step-prefixed tree commutes with `if`. -/
theorem erase_snd_ite (c : Prop) [Decidable c] (x y : ℕ × SPTree.Timed α) :
    (if c then x else y).2.erase = if c then x.2.erase else y.2.erase := by
  split <;> rfl

/-- Erasure of a step-prefixed tree commutes with a dependent `if`. -/
theorem erase_snd_dite (c : Prop) [Decidable c] (x : c → ℕ × SPTree.Timed α)
    (y : ¬c → ℕ × SPTree.Timed α) :
    (if h : c then x h else y h).2.erase = if h : c then (x h).2.erase else (y h).2.erase := by
  split <;> rfl

end SPTree.Timed

end CatCrypt.Core
