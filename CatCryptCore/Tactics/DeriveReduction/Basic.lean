/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.CodeSequenceTimed
public import CatCryptCore.Core.SPTree
public import CatCryptCore.Tactics.DeriveTimed.Basic

/-!
# Lemmas and definitions of the costed forms of `derive_reduction`

The declarations that the computation trees, erasure theorems and compile equations derived by
`derive_reduction` (`CatCryptCore.Tactics.DeriveReduction`) refer to: the compile and erasure
lemmas of `SPTree` (`DeriveReduction.compile_bind_pure_of_erase` and the lemmas of namespace
`CatCrypt.Core.SPTree` here) and the case analysis of a sum (`DeriveReduction.sumDispatch`).
Users that state or prove with these import this module publicly and the procedure privately.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Core.SPTree

variable {α β : Type}

theorem compile_bind_eq {s : SPTree α} {f : α → SPTree β} {c : SPComp α} {k : α → SPComp β}
    (hs : s.compile = c) (hf : ∀ a, (f a).compile = k a) :
    (s.bind f).compile = SPComp.bind c k := by
  rw [compile_bind, hs, funext hf]

theorem compile_sample_eq {fi : Fintype β} {ne : Nonempty β} {k : β → SPTree α}
    {k₀ : β → SPComp α} (h : ∀ b, (k b).compile = k₀ b) :
    (SPTree.sample β fi ne k).compile = SPComp.bind (@SPComp.sample β fi ne) k₀ := by
  simp only [compile, funext h]

theorem compile_sample_ret {fi : Fintype β} {ne : Nonempty β} :
    (SPTree.sample β fi ne fun b => .ret b).compile = @SPComp.sample β fi ne := by
  simp only [compile]
  exact SPComp.bind_pure _

theorem compile_get_eq {l : Location} {k : l.ty → SPTree α} {k₀ : l.ty → SPComp α}
    (h : ∀ v, (k v).compile = k₀ v) :
    (SPTree.get l k).compile = SPComp.bind (SPComp.get l) k₀ := by
  simp only [compile, funext h]

theorem compile_get_ret {l : Location} :
    (SPTree.get l fun v => .ret v).compile = SPComp.get l := by
  simp only [compile]
  exact SPComp.bind_pure _

theorem compile_set_eq {l : Location} {v : l.ty} {t : SPTree α} {k₀ : Unit → SPComp α}
    (h : t.compile = k₀ ()) :
    (SPTree.set l v t).compile = SPComp.bind (SPComp.set l v) k₀ := by
  simp only [compile, h]

theorem compile_set_ret {l : Location} {v : l.ty} :
    (SPTree.set l v (.ret ())).compile = SPComp.set l v := by
  simp only [compile]
  exact SPComp.bind_pure _

theorem compile_load_eq {h₀ : Heap} {t : SPTree α} {c : SPComp α} (h : t.compile = c) :
    (SPTree.load h₀ t).compile = fun _ => c h₀ := by
  rw [compile_load, h]

theorem compile_load_initHeap_eq {h₀ : Heap} {t : SPTree α} {k₀ : Unit → SPComp α}
    (h : t.compile = k₀ ()) :
    (SPTree.load h₀ t).compile = SPComp.bind (CatCrypt.Crypto.SPComp.initHeap h₀) k₀ := by
  funext h'
  simp only [compile_load, h, SPComp.bind, CatCrypt.Crypto.SPComp.initHeap,
    CatCrypt.Prob.SDistr.pure_bind]

theorem compile_load_initHeap_ret {h₀ : Heap} :
    (SPTree.load h₀ (.ret ())).compile = CatCrypt.Crypto.SPComp.initHeap h₀ := by
  funext h'
  simp only [compile_load, compile_ret, SPComp.pure, CatCrypt.Crypto.SPComp.initHeap]

theorem compile_ite_eq {p : Prop} [Decidable p] {t e : SPTree α} {t₀ e₀ : SPComp α}
    (ht : t.compile = t₀) (he : e.compile = e₀) :
    (if p then t else e).compile = if p then t₀ else e₀ := by
  split <;> assumption

theorem compile_dite_eq {p : Prop} [Decidable p] {t : p → SPTree α} {e : ¬p → SPTree α}
    {t₀ : p → SPComp α} {e₀ : ¬p → SPComp α} (ht : ∀ h, (t h).compile = t₀ h)
    (he : ∀ h, (e h).compile = e₀ h) :
    (if h : p then t h else e h).compile = if h : p then t₀ h else e₀ h := by
  split
  · exact ht _
  · exact he _

end CatCrypt.Core.SPTree

namespace CatCrypt.Tactics.DeriveReduction

open CatCrypt.Core

/-- The erasure of a costed tree whose results hold costed closures, followed by `ε` and
compiled: from the erasure theorem `h1` of the costed tree and the compile equation `h2` of the
erased tree, the compiled erasure followed by `ε` is the computation `c`; `hε` relates the
erasure `ε'` of the statement to the erasure `ε` of the erasure theorem. -/
theorem compile_bind_pure_of_erase {α β : Type} (X : SPTree.Timed α) (ε ε' : α → β)
    (t : SPTree β) (c : SPComp β) (hε : ε' = ε)
    (h1 : X.erase.bind (fun y => SPTree.ret (ε y)) = t) (h2 : t.compile = c) :
    SPComp.bind X.erase.compile (fun y => SPComp.pure (ε' y)) = c := by
  subst hε
  rw [← h2, ← h1, SPTree.compile_bind]
  rfl

/-- The case analysis of `x : α ⊕ β` by `f` on the left and `g` on the right, written as a
`match`. Its matcher `sumDispatch.match_1` is the form in which `derive_reduction` keeps a
dispatch `Sum.elim f g x`, `Sum.casesOn x f g` or `Sum.rec f g x` on a sum `x` that is not a
constructor (`sumDispatch?`). -/
@[expose] def sumDispatch.{u, v, w} {α : Type u} {β : Type v} (motive : α ⊕ β → Sort w)
    (x : α ⊕ β) (f : (a : α) → motive (.inl a)) (g : (b : β) → motive (.inr b)) : motive x :=
  match x with
  | .inl a => f a
  | .inr b => g b

end CatCrypt.Tactics.DeriveReduction

end
