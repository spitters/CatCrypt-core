/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad
public import CatCryptCore.Crypto.UCMonad.SPCompInstance
public import CatCryptCore.Crypto.SDist

/-!
# Round-Indexed Monad for Multi-Round UC Protocols

This file defines `RoundM n α`, a round-indexed monad for multi-round UC protocols.
`RoundM` is defined by recursion on `Nat`, so no inductive type with a nested
occurrence, and no strict-positivity check, is involved.

## Key idea

```
RoundM 0 α       = SPComp α
RoundM (n+1) α   = SPComp (α ⊕ RoundM n α)
```

## Proof technique

- `flatten_bind'` — flatten is a monad morphism (used for bind associativity)
- `flattenAll_bind` — full flattening is a monad morphism (used for PPL proofs)
- `sdistRoundM` defined via `flattenAll`, reducing all PPL proofs to `SPComp` level
-/

@[expose] public section

namespace UCMonad.RoundMUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Section 1: RoundM Type -/

/-- `RoundM n α`: a computation of at most `n` further rounds. With no rounds left it is an
    `SPComp α`; otherwise one `SPComp` step returns either the result or the rest of the
    computation with one round fewer. -/
noncomputable def RoundM : Nat → Type → Type
  | 0, α => SPComp α
  | n + 1, α => SPComp (α ⊕ RoundM n α)

/-! ## Section 2: Constructors -/

/-- Return a value without using a round. -/
noncomputable def RoundM.done {α : Type} : (n : Nat) → α → RoundM n α
  | 0, a => SPComp.pure a
  | _ + 1, a => SPComp.pure (.inl a)

/-- End the current round and continue with `k`. -/
noncomputable def RoundM.yield {α : Type} (n : Nat) (k : RoundM n α) : RoundM (n + 1) α :=
  SPComp.pure (.inr k)

/-- Run one round: a result, or the rest of the computation. -/
noncomputable def RoundM.runStep {α : Type} (n : Nat) :
    RoundM (n + 1) α → SPComp (α ⊕ RoundM n α) := id

/-- The failing computation at every round bound. -/
noncomputable def RoundM.fail {α : Type} : (n : Nat) → RoundM n α
  | 0 => SPComp.fail
  | n + 1 => (SPComp.fail : SPComp (α ⊕ RoundM n α))

/-! ## Section 3: Flatten -/

/-- Merge the first two rounds into one, lowering the round bound by one. -/
noncomputable def RoundM.flatten {α : Type} : (n : Nat) → RoundM (n + 1) α → RoundM n α
  | 0, c => SPComp.bind c (fun | .inl a => SPComp.pure a | .inr k => k)
  | n + 1, c => SPComp.bind c (fun
    | .inl a => (SPComp.pure (.inl a) : SPComp (α ⊕ RoundM n α))
    | .inr k => k)

/-! ## Section 4: Bind -/

/-- Sequential composition at round bound `n`; a continuation started after a round boundary
    is flattened to the remaining bound. -/
noncomputable def RoundM.bind' {α β : Type} :
    (n : Nat) → RoundM n α → (α → RoundM n β) → RoundM n β
  | 0, c, f => SPComp.bind c f
  | n + 1, c, f => SPComp.bind c (fun
    | .inl a => f a
    | .inr k => SPComp.pure (.inr (RoundM.bind' n k (fun a => RoundM.flatten n (f a)))))

/-! ## Section 4b: Equation Lemmas -/

@[simp] theorem RoundM.flatten_zero {α : Type} (c : RoundM 1 α) :
    RoundM.flatten 0 c = SPComp.bind c (fun | .inl a => SPComp.pure a | .inr k => k) := rfl

@[simp] theorem RoundM.flatten_succ {α : Type} (n : Nat) (c : RoundM (n + 2) α) :
    RoundM.flatten (n + 1) c = SPComp.bind c (fun
      | .inl a => (SPComp.pure (.inl a) : SPComp (α ⊕ RoundM n α))
      | .inr k => k) := rfl

@[simp] theorem RoundM.bind'_zero {α β : Type} (c : SPComp α) (f : α → SPComp β) :
    RoundM.bind' 0 c f = SPComp.bind c f := rfl

@[simp] theorem RoundM.bind'_succ {α β : Type} (n : Nat) (c : RoundM (n + 1) α)
    (f : α → RoundM (n + 1) β) :
    RoundM.bind' (n + 1) c f = SPComp.bind c (fun
      | .inl a => f a
      | .inr k => SPComp.pure (.inr (RoundM.bind' n k (fun a => RoundM.flatten n (f a))))) := rfl

/-! ## Section 4c: Flatten-Bind Commutativity -/

set_option maxHeartbeats 800000 in
/-- `RoundM.flatten` commutes with bind: it is a monad morphism. -/
theorem flatten_bind' {α β : Type} (n : Nat)
    (c : RoundM (n + 1) α) (g : α → RoundM (n + 1) β) :
    RoundM.flatten n (RoundM.bind' (n + 1) c g) =
    RoundM.bind' n (RoundM.flatten n c) (fun a => RoundM.flatten n (g a)) := by
  cases n with
  | zero =>
    change SPComp (α ⊕ RoundM 0 α) at c
    change α → SPComp (β ⊕ RoundM 0 β) at g
    dsimp only [RoundM.flatten, RoundM.bind']
    rw [SPComp.bind_assoc, SPComp.bind_assoc]
    congr 1; funext x; cases x with
    | inl a => simp only [SPComp.pure_bind]
    | inr k => simp only [SPComp.pure_bind]
  | succ m =>
    change SPComp (α ⊕ RoundM (m + 1) α) at c
    change α → SPComp (β ⊕ RoundM (m + 1) β) at g
    dsimp only [RoundM.flatten, RoundM.bind']
    rw [SPComp.bind_assoc, SPComp.bind_assoc]
    congr 1; funext x; cases x with
    | inl a => simp only [SPComp.pure_bind]
    | inr k => simp only [SPComp.pure_bind]

/-! ## Section 4d: FlattenAll — Collapse All Rounds to SPComp -/

/-- Collapse all rounds to a single `SPComp` computation by iterated flattening. -/
noncomputable def RoundM.flattenAll {α : Type} : (n : Nat) → RoundM n α → SPComp α
  | 0, c => c
  | n + 1, c => RoundM.flattenAll n (RoundM.flatten n c)

@[simp] theorem RoundM.flattenAll_zero {α : Type} (c : SPComp α) :
    RoundM.flattenAll 0 c = c := rfl

@[simp] theorem RoundM.flattenAll_succ {α : Type} (n : Nat) (c : RoundM (n + 1) α) :
    RoundM.flattenAll (n + 1) c = RoundM.flattenAll n (RoundM.flatten n c) := rfl

set_option maxHeartbeats 800000 in
/-- `flattenAll` is a monad morphism: it commutes with `bind`. -/
theorem flattenAll_bind {α β : Type} (n : Nat)
    (c : RoundM n α) (f : α → RoundM n β) :
    RoundM.flattenAll n (RoundM.bind' n c f) =
    SPComp.bind (RoundM.flattenAll n c) (fun a => RoundM.flattenAll n (f a)) := by
  induction n generalizing α β with
  | zero => rfl
  | succ n ih =>
    simp only [RoundM.flattenAll_succ]
    rw [flatten_bind' n c f, ih]

/-! ## Section 5: Monad Instance + Laws -/

/-- The continuation function used by `bind'` at level `n+1`. -/
noncomputable def RoundM.bindCont {α β : Type} (n : Nat) (f : α → RoundM (n + 1) β) :
    (α ⊕ RoundM n α) → SPComp (β ⊕ RoundM n β) :=
  fun
    | .inl a => f a
    | .inr k => SPComp.pure (.inr (RoundM.bind' n k (fun a => RoundM.flatten n (f a))))

/-- The monad structure of `RoundM n`. -/
noncomputable instance (n : Nat) : Monad (RoundM n) where
  pure := RoundM.done n
  bind := RoundM.bind' n

/-- Unfolding lemma: `>>=` at `RoundM (n+1)` reduces to `SPComp.bind`. -/
theorem RoundM.hbind_succ {α β : Type} (n : Nat) (c : RoundM (n + 1) α)
    (f : α → RoundM (n + 1) β) :
    (c >>= f : RoundM (n + 1) β) = SPComp.bind c (RoundM.bindCont n f) := rfl

-- pure_bind: bind' n (done n a) f = f a
/-- Left unit law of `RoundM.bind'`. -/
theorem roundM_pure_bind {α β : Type} (n : Nat) (a : α) (f : α → RoundM n β) :
    RoundM.bind' n (RoundM.done n a) f = f a := by
  cases n with
  | zero => exact SPComp.pure_bind a f
  | succ n =>
    show SPComp.bind (SPComp.pure (Sum.inl a)) _ = f a
    exact SPComp.pure_bind (Sum.inl a) _

-- bind_done: bind' n m (done n) = m
/-- Right unit law of `RoundM.bind'`. -/
theorem roundM_bind_done {α : Type} (n : Nat) (m : RoundM n α) :
    RoundM.bind' n m (RoundM.done n) = m := by
  induction n with
  | zero => exact SPComp.bind_pure m
  | succ n ih =>
    change SPComp.bind m _ = m
    conv_rhs => rw [← SPComp.bind_pure m]
    congr 1; funext x; cases x with
    | inl _ => rfl
    | inr k =>
      show SPComp.pure (Sum.inr (RoundM.bind' n k
        (fun a => RoundM.flatten n (RoundM.done (n + 1) a)))) = _
      -- flatten_done: flatten n (done (n+1) a) = done n a
      have hfd : ∀ a : α, RoundM.flatten n (RoundM.done (n + 1) a) = RoundM.done n a := by
        intro a; cases n with
        | zero =>
          unfold RoundM.flatten RoundM.done
          exact SPComp.pure_bind (Sum.inl a) _
        | succ m =>
          unfold RoundM.flatten RoundM.done
          exact SPComp.pure_bind (Sum.inl a) _
      simp only [hfd]
      exact congrArg SPComp.pure (congrArg Sum.inr (ih k))

-- bind_assoc: standard but requires flatten-bind commutativity
/-- Associativity of `RoundM.bind'`. -/
theorem roundM_bind_assoc {α β γ : Type} (n : Nat)
    (m : RoundM n α) (f : α → RoundM n β) (g : β → RoundM n γ) :
    RoundM.bind' n (RoundM.bind' n m f) g =
    RoundM.bind' n m (fun a => RoundM.bind' n (f a) g) := by
  induction n with
  | zero => exact SPComp.bind_assoc m f g
  | succ n ih =>
    change SPComp (α ⊕ RoundM n α) at m
    change SPComp.bind (SPComp.bind m _) _ = SPComp.bind m _
    rw [SPComp.bind_assoc]
    congr 1; funext x; cases x with
    | inl _ => rfl
    | inr k =>
      simp only [SPComp.pure_bind]
      congr 1; congr 1
      rw [ih]
      congr 1; funext a
      exact (flatten_bind' n (f a) g).symm

/-- `RoundM n` is a lawful monad. -/
noncomputable instance (n : Nat) : LawfulMonad (RoundM n) := LawfulMonad.mk'
  (id_map := roundM_bind_done n)
  (pure_bind := roundM_pure_bind n)
  (bind_assoc := roundM_bind_assoc n)

/-! ## Section 6: Depth Embedding -/

/-- View a computation of at most `n` rounds as one of at most `n + 1` rounds. -/
noncomputable def RoundM.embed {α : Type} : (n : Nat) → RoundM n α → RoundM (n + 1) α
  | 0, c => SPComp.bind c (fun a => SPComp.pure (.inl a))
  | n + 1, c => SPComp.bind c (fun
    | .inl a => SPComp.pure (.inl a)
    | .inr k => SPComp.pure (.inr (RoundM.embed n k)))

/-- View a computation of at most `n` rounds as one of at most `n + k` rounds. -/
noncomputable def RoundM.pad {α : Type} (n : Nat) :
    (k : Nat) → RoundM n α → RoundM (n + k) α
  | 0, c => c
  | k + 1, c => RoundM.embed (n + k) (RoundM.pad n k c)

/-! ## Section 7: Parallel Composition on Sum -/

/-- The coproduct of two arrows: run `f` on a left input and `g` on a right input, tagging
    the result with the same side. -/
noncomputable def mapSumRoundM (n : Nat) {α β γ δ : Type}
    (f : α → RoundM n β) (g : γ → RoundM n δ) :
    (α ⊕ γ) → RoundM n (β ⊕ δ)
  | .inl a => f a >>= fun b => pure (.inl b)
  | .inr c => g c >>= fun d => pure (.inr d)

/-- `mapSumRoundM` on a left input. -/
@[simp]
theorem mapSumRoundM_inl (n : Nat) {α β γ δ : Type}
    (f : α → RoundM n β) (g : γ → RoundM n δ) (a : α) :
    mapSumRoundM n f g (.inl a) = f a >>= fun b => pure (.inl b) := rfl

/-- `mapSumRoundM` on a right input. -/
@[simp]
theorem mapSumRoundM_inr (n : Nat) {α β γ δ : Type}
    (f : α → RoundM n β) (g : γ → RoundM n δ) (c : γ) :
    mapSumRoundM n f g (.inr c) = g c >>= fun d => pure (.inr d) := rfl

/-- The coproduct of two identities is the identity. -/
theorem mapSumRoundM_pure_pure (n : Nat) {α β : Type} :
    mapSumRoundM n (pure : α → RoundM n α) (pure : β → RoundM n β) = pure := by
  funext x; cases x with
  | inl a => exact pure_bind a _
  | inr b => exact pure_bind b _

/-- The coproduct with the identity on the left commutes with Kleisli composition. -/
theorem mapSumRoundM_pure_kleisli (n : Nat) {α β γ δ : Type}
    (f : β → RoundM n γ) (g : γ → RoundM n δ) :
    (fun x : α ⊕ β => mapSumRoundM n pure f x >>= mapSumRoundM n pure g)
    = mapSumRoundM n pure (fun b => f b >>= g) := by
  funext x; cases x with
  | inl a => simp only [mapSumRoundM_inl, pure_bind]
  | inr b => simp only [mapSumRoundM_inr, pure_bind, bind_assoc]

/-! ## Section 8: Statistical Distance

The key insight: define `sdistRoundM` via `flattenAll`, which collapses all rounds to `SPComp`.
Since `flattenAll` is a monad morphism (`flattenAll_bind`), both PPLs reduce directly to
the corresponding `SPComp`-level properties (`sdist_comp_right`, `sdist_comp_left`). -/

/-- Statistical distance for `RoundM`, defined via `flattenAll`.
    This measures the distance between the fully-flattened executions,
    which corresponds to the environment's view in UC security. -/
noncomputable def sdistRoundM {α β : Type} (n : Nat)
    (f g : α → RoundM n β) : ℝ≥0∞ :=
  sdist (fun a => RoundM.flattenAll n (f a)) (fun a => RoundM.flattenAll n (g a))

/-- `sdistRoundM` vanishes on equal arrows. -/
theorem sdistRoundM_self {α β : Type} (n : Nat)
    (f : α → RoundM n β) : sdistRoundM n f f = 0 := sdist_self _

/-- `sdistRoundM` is symmetric. -/
theorem sdistRoundM_sym {α β : Type} (n : Nat)
    (f g : α → RoundM n β) : sdistRoundM n f g = sdistRoundM n g f := sdist_sym _ _

/-- `sdistRoundM` satisfies the triangle inequality. -/
theorem sdistRoundM_triangle {α β : Type} (n : Nat)
    (f g h : α → RoundM n β) :
    sdistRoundM n f h ≤ sdistRoundM n f g + sdistRoundM n g h := sdist_triangle _ _ _

/-- Post-composition with a common arrow does not increase `sdistRoundM`. -/
theorem sdistRoundM_comp_right {α β γ : Type} (n : Nat)
    (f g : α → RoundM n β) (k : β → RoundM n γ) :
    sdistRoundM n (fun a => f a >>= k) (fun a => g a >>= k) ≤ sdistRoundM n f g := by
  show sdist (fun a => RoundM.flattenAll n (RoundM.bind' n (f a) k))
             (fun a => RoundM.flattenAll n (RoundM.bind' n (g a) k)) ≤ _
  simp only [flattenAll_bind]
  exact sdist_comp_right _ _ _

/-- Pre-composition with a common arrow does not increase `sdistRoundM`. -/
theorem sdistRoundM_comp_left {α β γ : Type} (n : Nat)
    (f : α → RoundM n β) (g₁ g₂ : β → RoundM n γ) :
    sdistRoundM n (fun a => f a >>= g₁) (fun a => f a >>= g₂) ≤ sdistRoundM n g₁ g₂ := by
  show sdist (fun a => RoundM.flattenAll n (RoundM.bind' n (f a) g₁))
             (fun a => RoundM.flattenAll n (RoundM.bind' n (f a) g₂)) ≤ _
  simp only [flattenAll_bind]
  exact sdist_comp_left _ _ _

/-! ## Section 9: UCMonadMetric Instance -/

/-- The UC metric structure on `RoundM n`: coproduct `mapSumRoundM`, distance `sdistRoundM`. -/
noncomputable instance (n : Nat) : UCMonadMetric (RoundM n) where
  ucMapSum := mapSumRoundM n
  ucMapSum_inl := fun _f _g _a => rfl
  ucMapSum_inr := fun _f _g _c => rfl
  ucMapSum_pure_pure := mapSumRoundM_pure_pure n
  ucMapSum_pure_kleisli := fun f g => mapSumRoundM_pure_kleisli n f g
  ucSdist := sdistRoundM n
  ucSdist_self := sdistRoundM_self n
  ucSdist_sym := sdistRoundM_sym n
  ucSdist_triangle := sdistRoundM_triangle n
  ucSdist_comp_right := sdistRoundM_comp_right n
  ucSdist_comp_left := sdistRoundM_comp_left n

end UCMonad.RoundMUC
