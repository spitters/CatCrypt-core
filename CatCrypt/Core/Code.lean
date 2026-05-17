/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Core.Heap
import CatCrypt.Prob.SDistr

/-!
# Code Representation

This file defines the representation of stateful probabilistic computations.
We use the direct semantic model: `SPComp α = Heap → SDistr (α × Heap)`.

## Main definitions

* `SPComp α` - Stateful probabilistic computation returning `α`
* `SPComp.pure` - Pure computation
* `SPComp.get` - Read from a location
* `SPComp.set` - Write to a location
* `SPComp.sample` - Sample from uniform distribution
* `SPComp.fail` - Failed computation
* `SPComp.assert` - Assertion (fail if false)
-/

namespace CatCrypt.Core

open CatCrypt.Prob

/-- Stateful probabilistic computation.
    A function from initial heap to a sub-distribution over (result, final heap) pairs. -/
def SPComp (α : Type*) := Heap → SDistr (α × Heap)

namespace SPComp

variable {α β γ : Type*}

/-! ## Monad operations -/

/-- Pure computation: return value without changing state -/
noncomputable def pure (a : α) : SPComp α :=
  fun h => SDistr.pure (a, h)

/-- Bind: sequential composition -/
noncomputable def bind (c : SPComp α) (f : α → SPComp β) : SPComp β :=
  fun h => (c h).bind fun (a, h') => f a h'

noncomputable instance : Monad SPComp where
  pure := SPComp.pure
  bind := SPComp.bind

/-! ## State operations -/

/-- Read from a memory location -/
noncomputable def get (l : Location) : SPComp l.ty :=
  fun h => SDistr.pure (h.get l, h)

/-- Write to a memory location -/
noncomputable def set (l : Location) (v : l.ty) : SPComp Unit :=
  fun h => SDistr.pure ((), h.set l v)

/-! ## Probabilistic operations -/

/-- Sample uniformly from a finite nonempty type -/
noncomputable def sample (α : Type*) [Fintype α] [Nonempty α] : SPComp α :=
  fun h => (SDistr.uniform α).bind fun a => SDistr.pure (a, h)

/-- Failed computation -/
noncomputable def fail : SPComp α :=
  fun _ => SDistr.fail

/-- Binding from a failed computation gives failure -/
@[simp]
theorem fail_bind (f : α → SPComp β) : SPComp.bind fail f = fail := by
  funext h; simp only [bind, fail]; exact SDistr.bind_fail _

/-! ## Assertions -/

/-- Assert a decidable proposition; fail if false -/
noncomputable def assert (P : Prop) [Decidable P] : SPComp Unit :=
  if P then pure () else fail

/-! ## Derived operations -/

/-- Sequence two computations, ignoring the first result -/
noncomputable def seq {α β : Type*} (c1 : SPComp α) (c2 : SPComp β) : SPComp β :=
  c1.bind fun _ => c2

/-! ## Basic lemmas -/

theorem pure_def (a : α) (h : Heap) : (pure a : SPComp α) h = SDistr.pure (a, h) := rfl

theorem bind_def {α β : Type*} (c : SPComp α) (f : α → SPComp β) (h : Heap) :
    (c.bind f) h = (c h).bind fun (a, h') => f a h' := rfl

theorem get_def (l : Location) (h : Heap) :
    (get l) h = SDistr.pure (h.get l, h) := rfl

theorem set_def (l : Location) (v : l.ty) (h : Heap) :
    (set l v) h = SDistr.pure ((), h.set l v) := rfl

/-- Binding pure with a function gives the function applied to the value -/
@[simp]
theorem pure_bind' (a : α) (f : α → SPComp β) (h : Heap) :
    (SPComp.bind (pure a) f) h = f a h := by
  unfold SPComp.bind pure
  rw [SDistr.pure_bind]

/-- Binding pure after a computation is identity -/
theorem bind_pure' (c : SPComp α) (h : Heap) :
    (SPComp.bind c pure) h = c h := by
  simp only [SPComp.bind, pure, Prod.mk.eta, SDistr.bind_pure]

/-- Monad bind on SPComp is SPComp.bind -/
@[simp]
theorem monad_bind_eq {α β : Type} (c : SPComp α) (f : α → SPComp β) : c >>= f = SPComp.bind c f := rfl

/-- Monad pure on SPComp is SPComp.pure -/
@[simp]
theorem monad_pure_eq {α : Type*} (a : α) : (Pure.pure a : SPComp α) = SPComp.pure a := rfl

/-- Sample followed by pure with a function simplifies to uniform bind with pure.
    This is key for coupling proofs where we need the distribution over (result, heap). -/
theorem sample_bind_pure (α : Type*) [Fintype α] [Nonempty α] (f : α → β) (h : Heap) :
    (SPComp.bind (sample α) (fun a => pure (f a))) h =
    (SDistr.uniform α).bind (fun a => SDistr.pure (f a, h)) := by
  simp only [SPComp.bind, sample, pure, SDistr.bind_assoc, SDistr.pure_bind]

/-- Sample followed by pure of the sampled value simplifies to uniform bind.
    Special case where f is identity. -/
theorem sample_bind_pure_id (α : Type*) [Fintype α] [Nonempty α] (h : Heap) :
    (sample α) h = (SDistr.uniform α).bind (fun a => SDistr.pure (a, h)) := rfl

/-- Sampling from a product type is equivalent to sampling each component independently. -/
@[simp, grind =]
theorem sample_prod_eq (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    SPComp.sample (A × B) =
    SPComp.bind (SPComp.sample A) (fun a =>
      SPComp.bind (SPComp.sample B) (fun b =>
        SPComp.pure (a, b))) := by
  funext h
  simp only [sample, SPComp.bind, SPComp.pure, SDistr.bind_assoc, SDistr.pure_bind]
  have := congr_arg (fun d => d.bind (fun ab => SDistr.pure (ab, h)))
    (SDistr.uniform_nested_eq_prod A B)
  simp only [SDistr.bind_assoc, SDistr.pure_bind] at this
  exact this.symm

/-! ## Associativity and unit laws -/

/-- Bind associativity for SPComp -/
@[simp, grind =]
theorem bind_assoc (c : SPComp α) (f : α → SPComp β) (g : β → SPComp γ) :
    SPComp.bind (SPComp.bind c f) g = SPComp.bind c (fun a => SPComp.bind (f a) g) := by
  funext h; simp only [SPComp.bind, SDistr.bind_assoc]

/-- Right identity: bind with pure -/
@[simp, grind =]
theorem bind_pure (c : SPComp α) : SPComp.bind c pure = c := by
  funext h
  exact bind_pure' c h

/-- Left identity: pure then bind -/
@[simp, grind =]
theorem pure_bind (a : α) (f : α → SPComp β) : SPComp.bind (pure a) f = f a := by
  funext h
  exact pure_bind' a f h

/-! ## Functorial map -/

/-- Functorial map for SPComp -/
noncomputable def map (f : α → β) (c : SPComp α) : SPComp β :=
  c.bind (fun a => pure (f a))

@[simp]
theorem map_id (c : SPComp α) : SPComp.map id c = c := bind_pure c

@[simp]
theorem map_comp (f : α → β) (g : β → γ) (c : SPComp α) :
    SPComp.map g (SPComp.map f c) = SPComp.map (g ∘ f) c := by
  simp only [SPComp.map, bind_assoc, pure_bind, Function.comp]

@[simp]
theorem map_pure (f : α → β) (a : α) :
    SPComp.map f (pure a) = pure (f a) := pure_bind a _

/-! ## Bijection on Uniform Sample -/

/-- Applying a bijection inside a uniform sample doesn't change the distribution.

    If `e : α ≃ β` is a bijection, then sampling `a : α` uniformly and returning `f (e a)`
    is the same as sampling `b : β` uniformly and returning `f b`.
    This lifts `SDistr.uniform_bind_bij` to `SPComp`. -/
theorem sample_bind_pure_equiv [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) (f : β → γ) :
    SPComp.bind (SPComp.sample α) (fun a => SPComp.pure (f (e a))) =
    SPComp.bind (SPComp.sample β) (fun b => SPComp.pure (f b)) := by
  funext h
  simp only [bind_def, sample, pure, SDistr.bind_assoc, SDistr.pure_bind]
  conv_lhs =>
    arg 2; ext a
    rw [show SDistr.pure (f (e a), h) = (SDistr.pure (e a)).bind
          (fun b => SDistr.pure (f b, h)) from by rw [SDistr.pure_bind]]
  rw [← SDistr.bind_assoc, SDistr.uniform_bind_bij]

/-- Applying a bijection inside a uniform sample with arbitrary continuation.

    Generalizes `sample_bind_pure_equiv` to non-pure continuations.
    If `e : α ≃ β`, then `sample α >>= (k ∘ e) = sample β >>= k`. -/
theorem sample_bind_equiv [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) (k : β → SPComp γ) :
    SPComp.bind (SPComp.sample α) (fun a => k (e a)) =
    SPComp.bind (SPComp.sample β) k := by
  funext h
  simp only [bind_def, sample, SDistr.bind_assoc, SDistr.pure_bind]
  exact SDistr.uniform_bind_equiv_comp e (fun b => k b h)

/-- Bijection cancellation in context: apply a context-dependent bijection
    inside `bind c (fun x => sample >>= ...)`.

    This handles the common ROM pattern where a key `x` determines a bijection
    `e x : α ≃ β` applied to a uniform sample. -/
theorem bind_sample_bijection {δ : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (c : SPComp γ) (e : γ → (α ≃ β)) (k : γ → β → SPComp δ) :
    SPComp.bind c (fun x => SPComp.bind (SPComp.sample α) (fun a => k x (e x a))) =
    SPComp.bind c (fun x => SPComp.bind (SPComp.sample β) (fun b => k x b)) := by
  congr 1; funext x
  exact sample_bind_equiv (e x) (k x)

/-! ## Purity: Heap-Independent Computations -/

/-- A computation is *pure* if it doesn't depend on or modify the heap.
    Formally, there exists a sub-distribution `d` over values such that
    for every initial heap `h`, the computation returns `(a, h)` (unchanged heap)
    with probability `d(a)`. -/
def IsPure (c : SPComp α) : Prop :=
  ∃ d : SDistr α, ∀ h, c h = d.bind (fun a => SDistr.pure (a, h))

/-- `pure a` is pure. -/
theorem pure_isPure (a : α) : IsPure (pure a : SPComp α) :=
  ⟨SDistr.pure a, fun h => by simp [pure, SDistr.pure_bind]⟩

/-- `sample α` is pure (doesn't touch the heap). -/
theorem sample_isPure (α : Type*) [Fintype α] [Nonempty α] : IsPure (sample α) :=
  ⟨SDistr.uniform α, fun _ => rfl⟩

/-- `fail` is pure (doesn't touch the heap — it produces no results at all). -/
theorem fail_isPure : IsPure (fail : SPComp α) :=
  ⟨SDistr.fail, fun _ => (SDistr.bind_fail _).symm⟩

/-- Bind of pure computations is pure. -/
theorem bind_isPure {c : SPComp α} {f : α → SPComp β}
    (hc : IsPure c) (hf : ∀ a, IsPure (f a)) : IsPure (c.bind f) := by
  obtain ⟨dc, hdc⟩ := hc
  choose df hdf using hf
  refine ⟨dc.bind (fun a => df a), fun h => ?_⟩
  simp only [bind, hdc h, SDistr.bind_assoc]
  congr 1
  funext a
  simp only [SDistr.pure_bind, hdf a h]

/-- Two pure computations commute in bind (Fubini for SPComp).

    If `c₁` and `c₂` are both pure, then:
    `c₁ >>= fun a => c₂ >>= fun b => k a b`
    equals
    `c₂ >>= fun b => c₁ >>= fun a => k a b`

    This is the key lemma for hybrid game decomposition in PKE security proofs. -/
theorem isPure_bind_comm (c₁ : SPComp α) (c₂ : SPComp β)
    (k : α → β → SPComp γ)
    (hc₁ : IsPure c₁) (hc₂ : IsPure c₂) :
    SPComp.bind c₁ (fun a => SPComp.bind c₂ (fun b => k a b)) =
    SPComp.bind c₂ (fun b => SPComp.bind c₁ (fun a => k a b)) := by
  obtain ⟨d₁, hd₁⟩ := hc₁
  obtain ⟨d₂, hd₂⟩ := hc₂
  funext h
  simp only [bind, hd₁ h, hd₂ h, SDistr.bind_assoc, SDistr.pure_bind]
  exact SDistr.bind_comm d₁ d₂ (fun a b => k a b h)

/-- One-sided commutativity: an `IsPure` computation can be commuted past ANY
    computation (not just another IsPure one).

    This generalizes `isPure_bind_comm` by dropping the requirement that `c₂` be IsPure.
    The proof uses `SDistr.bind_comm` (Fubini) at the distribution level, where
    `c₁`'s extracted distribution commutes with `c₂ h` for any heap `h`. -/
theorem isPure_bind_comm_left (c₁ : SPComp α) (c₂ : SPComp β)
    (k : α → β → SPComp γ) (hc₁ : IsPure c₁) :
    SPComp.bind c₁ (fun a => SPComp.bind c₂ (fun b => k a b)) =
    SPComp.bind c₂ (fun b => SPComp.bind c₁ (fun a => k a b)) := by
  obtain ⟨d₁, hd₁⟩ := hc₁
  funext h
  simp only [bind, hd₁, SDistr.bind_assoc, SDistr.pure_bind]
  exact SDistr.bind_comm d₁ (c₂ h) (fun a ⟨b, h'⟩ => k a b h')

/-! ## LawfulMonad instance -/

/-- SPComp is a lawful monad. The laws follow from `pure_bind`, `bind_pure`, `bind_assoc`. -/
noncomputable instance : LawfulMonad SPComp := LawfulMonad.mk'
  (id_map := fun x => bind_pure x)
  (pure_bind := fun x f => pure_bind x f)
  (bind_assoc := fun x f g => bind_assoc x f g)

/-! ## Monadic fold -/

/-- Monadic fold over a list of steps. Useful for key schedules and hybrid arguments.

    `foldM init [f, g, h] = f init >>= fun a => g a >>= fun b => h b`

    Each step takes the accumulator and produces a new computation. -/
noncomputable def foldM (init : α) : List (α → SPComp α) → SPComp α
  | [] => pure init
  | f :: rest => f init >>= fun a => foldM a rest

@[simp] theorem foldM_nil (init : α) : foldM init [] = pure init := rfl

@[simp] theorem foldM_cons (init : α) (f : α → SPComp α) (rest : List (α → SPComp α)) :
    foldM init (f :: rest) = f init >>= fun a => foldM a rest := rfl

theorem foldM_singleton (init : α) (f : α → SPComp α) :
    foldM init [f] = f init := by
  simp [foldM]; exact SPComp.bind_pure (f init)

theorem foldM_append (init : α) (xs ys : List (α → SPComp α)) :
    foldM init (xs ++ ys) = SPComp.bind (foldM init xs) (fun a => foldM a ys) := by
  induction xs generalizing init with
  | nil => simp only [List.nil_append, foldM_nil, SPComp.pure_bind]
  | cons f rest ih =>
    simp only [List.cons_append, foldM_cons]
    show SPComp.bind (f init) _ = SPComp.bind (SPComp.bind (f init) _) _
    rw [SPComp.bind_assoc]
    congr 1; funext a; exact ih a

end SPComp

/-! ## SDistr → SPComp Lift -/

/-- Lift a pure distribution to a stateful computation (heap-independent). -/
noncomputable def liftSDistr {α : Type} (d : CatCrypt.Prob.SDistr α) : SPComp α :=
  fun h => d.bind fun a => CatCrypt.Prob.SDistr.pure (a, h)

theorem liftSDistr_isPure {α : Type} (d : CatCrypt.Prob.SDistr α) :
    SPComp.IsPure (liftSDistr d) :=
  ⟨d, fun _ => rfl⟩

end CatCrypt.Core
