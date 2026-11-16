/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCOracleGame

/-!
# Query bounds of reductions by a potential

`OProt.isQueryBound_reduce` bounds the queries of `reduce` with `n` activations by `n * m` when
every activation asks at most `m` queries. A protocol whose activations spend a resource of its
state, such as the unused instances of a CryptoVerif context, which each answer once, has a bound
that does not grow with the number of activations: a potential `Φ` on the protocol state such
that an activation from `t` asks queries of total cost plus the potential of the next state at
most `Φ t`. The reduction then asks queries of total cost at most `Φ` of the initial state.

## Main results

* `OracleAdv.IsQueryBoundByRet` — a cost bound on the queries of a program plus a potential of
  its returned value.
* `OracleAdv.isQueryBoundBy_bind_ret`, `OracleAdv.isQueryBoundByRet_bind_ret` — composition with
  a continuation and with a return.
* `OracleAdv.isQueryBound_of_isQueryBoundBy_one`, `OracleAdv.isQueryBoundBy_of_isQueryBound` —
  query bounds and cost bounds at the unit cost.
* `OProt.isQueryBoundBy_reduce_pot`, `OProt.isQueryBound_reduce_pot` — the potential form of
  `OProt.isQueryBound_reduce`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

namespace OracleAdv

variable {D R α β : Type}

/-- `IsQueryBoundByRet cost Φ A n`: on every path of `A`, the sum of `cost d` over the queries
`d` plus the potential `Φ a` of the returned value `a` is at most `n`. -/
def IsQueryBoundByRet (cost : D → ℕ) (Φ : α → ℕ) : OracleAdv D R α → ℕ → Prop
  | ret a, n => Φ a ≤ n
  | rand _ k, n => ∀ b, IsQueryBoundByRet cost Φ (k b) n
  | query d k, n => cost d ≤ n ∧ ∀ r, IsQueryBoundByRet cost Φ (k r) (n - cost d)

/-- A bound with a potential on the result, followed by continuations bounded by the potential
of their argument, bounds the composite. -/
theorem isQueryBoundBy_bind_ret {cost : D → ℕ} {Φ : α → ℕ} {A : OracleAdv D R α}
    {f : α → OracleAdv D R β} {n : ℕ} (hA : A.IsQueryBoundByRet cost Φ n)
    (hf : ∀ a, (f a).IsQueryBoundBy cost (Φ a)) : (A.bind f).IsQueryBoundBy cost n := by
  induction A generalizing n with
  | ret a => exact (hf a).mono hA
  | rand p k ih => exact fun b => ih b (hA b)
  | query d k ih => exact ⟨hA.1, fun r => ih r (hA.2 r)⟩

/-- A program with cost at most `m ≤ n`, followed by a return whose value has potential at most
`n - m`, is bounded by `n` with that potential. -/
theorem isQueryBoundByRet_bind_ret {cost : D → ℕ} {Φ : β → ℕ} {X : OracleAdv D R α}
    {f : α → β} {m n : ℕ} (hX : X.IsQueryBoundBy cost m) (hmn : m ≤ n)
    (hf : ∀ a, Φ (f a) + m ≤ n) :
    (X.bind fun a => ret (f a)).IsQueryBoundByRet cost Φ n := by
  induction X generalizing m n with
  | ret a => exact (Nat.le_add_right _ _).trans (hf a)
  | rand p k ih => exact fun b => ih b (hX b) hmn hf
  | query d k ih =>
    obtain ⟨hle, hk⟩ := hX
    refine ⟨hle.trans hmn, fun r => ih r (hk r) (by omega) fun a => ?_⟩
    have := hf a
    omega

/-- A cost bound for the unit cost is a query bound. -/
theorem isQueryBound_of_isQueryBoundBy_one {A : OracleAdv D R α} {n : ℕ}
    (h : A.IsQueryBoundBy (fun _ => 1) n) : A.IsQueryBound n := by
  induction A generalizing n with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (h b)
  | query d k ih =>
    obtain ⟨h1, hk⟩ := h
    cases n with
    | zero => simp at h1
    | succ n => exact fun r => ih r (by simpa using hk r)

/-- A query bound is a cost bound for every cost at most `1`. -/
theorem isQueryBoundBy_of_isQueryBound {cost : D → ℕ} (hc : ∀ d, cost d ≤ 1)
    {A : OracleAdv D R α} {n : ℕ} (h : A.IsQueryBound n) : A.IsQueryBoundBy cost n := by
  induction A generalizing n with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (h b)
  | query d k ih =>
    cases n with
    | zero => exact h.elim
    | succ n => exact ⟨(hc d).trans (by omega), fun r => (ih r (h r)).mono (by grind)⟩

end OracleAdv

namespace UCTransparent.OProt

open CatCrypt.Core CatCrypt.Prob

variable {τ E O Q A ζ : Type}

/-- **Queries of `reduce` by a potential.** If every activation of `P` from the state `t` asks
queries of total cost plus the potential of the next state at most `Φ t`, then `reduce` from the
state `t` asks queries of total cost at most `Φ t`, at every number of activations. -/
theorem isQueryBoundBy_reduce_pot (P : OProt τ E O Q A) (Z : Strat ζ E O)
    (dist : ζ → SPComp Bool) (cost : Q → ℕ) (Φ : τ → ℕ)
    (hP : ∀ t e, (P.step t e).IsQueryBoundByRet cost (fun p => Φ p.1) (Φ t)) :
    ∀ (n : ℕ) (z : ζ) (t : τ) (h : CatCrypt.Core.Heap),
      (P.reduce Z dist n z t h).IsQueryBoundBy cost (Φ t) := by
  intro n
  induction n with
  | zero => intro z t h o; rcases o with _ | _ <;> trivial
  | succ n ih =>
    intro z t h o
    rcases o with _ | ⟨⟨z₁, e⟩, h₁⟩
    · trivial
    · refine OracleAdv.isQueryBoundBy_bind_ret (hP t e) fun p o' => ?_
      rcases o' with _ | ⟨z₂, h₂⟩
      · trivial
      · exact ih z₂ p.1 h₂

/-- **Queries of the reduction by a potential** (`isQueryBound_reduce` with a potential). If
every activation of `P` from the state `t` asks queries plus the potential of the next state at
most `Φ t`, the reduction of every environment asks at most `Φ P.init` queries. -/
theorem isQueryBound_reduce_pot (P : OProt τ E O Q A) (Z : UCConcrete.Env (Strat ζ E O) ζ)
    (Φ : τ → ℕ) (hP : ∀ t e, (P.step t e).IsQueryBoundByRet (fun _ => 1) (fun p => Φ p.1) (Φ t)) :
    (P.reduction Z).IsQueryBound (Φ P.init) :=
  OracleAdv.isQueryBound_of_isQueryBoundBy_one
    (isQueryBoundBy_reduce_pot P Z.input Z.dist _ Φ hP _ _ _ _)

end UCTransparent.OProt

end CatCrypt.Crypto
