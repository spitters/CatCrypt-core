/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.LinkDt
public import CatCryptCore.Container.DillerNahm

/-!
# The interpretation of D in the Diller–Nahm category

## Substitution of a certified callee

A certified callee is a term `g : Tm (a :: Γ) b` of the fragment `Tm.InDtFrag` in the context of
its argument, with its soundness theorem `Tm.dtC_timedSim`; its body may sample, read, write and
query. Substituted for a function variable of a term `t : Tm (.arr a b :: Γ) τ`, it is the
closure `fun v => g.eval (ρ.cons v)` bound to that variable, the value of `Tm.lam g`, and the
substituted term evaluates as `t` in `ρ.cons` of that closure (the β-redex
`Tm.letE (Tm.lam g) t` evaluates so after one step, `Tm.eval_letE_lam`). Its costed tree is
`t.dtC cc` at the environment whose entry for the variable is `calleeEntry cc g η`: at each call
on a translated argument `u`, the charge `cc a` of the call and the cost of the callee, its
allowance `g.allowC cc` and its charges `g.dtC cc (η.cons u)` (`Tm.dtC_call_calleeEntry`). The
outer charges are those of `t`.

`Tm.dtC_subst` states the simulation of the substituted evaluation by that costed tree at the
allowance of `t` alone. It is the soundness theorem `Tm.dtC_timedSim` of `t` in the environment
extended by the callee, whose entry is related to the closure by the soundness theorem of `g`
(`SimE.calleeEntry`): the allowance of the callee is moved into the step cost of its entry
(`TimedSim.delay_allow`). An abstraction with an effectful body is outside the fragment
(`Tm.InDtFrag` asks for a pure body), so the substitution of an effectful callee is not an instance
of the soundness theorem of the redex; it is the soundness theorem of `t` at a callee entry.

## Main definitions

* `calleeEntry`: the entry of a certified callee

## Main results

* `TimedSim.delay_allow`: at factor one, an allowance is a step cost in front
* `SimE.calleeEntry`: the entry of a certified callee is related to its closure
* `Tm.dtC_subst`, `Tm.cost_subst_le`, `Tm.eval_letE_lam`, `Tm.dtC_subst_letE`: the
  substitution theorem, its cost bound, and its form at the β-redex
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core CatCrypt.Container

/-! ## Substitution of a certified callee -/

/-- At factor one, the allowance of a simulation is a step cost in front of the costed tree. -/
theorem TimedSim.delay_allow {α β : Type} {R : α → β → Prop} {n : ℕ} {x : ℕ × SPTree.Timed α}
    {t : CTree β} (h : TimedSim R 1 n x t) : TimedSim R 1 0 (SPTree.Timed.delay n x) t := by
  refine TimedSimTree.mono h ?_
  simp only [SPTree.Timed.delay]
  omega

/-- The entry of the certified callee `g`, a term in the context of its argument: at a translated
argument `u`, the charges of `g` at `η.cons u` behind its allowance. -/
noncomputable def calleeEntry (cc : Ty → ℕ) {Γ : List Ty} {a b : Ty} (g : Tm (a :: Γ) b)
    (η : EnvHat Γ) : (Ty.arr a b).hatE :=
  fun u => SPTree.Timed.delay (g.allowC cc) (g.dtC cc (η.cons u))

/-- The entry of a certified callee is related to its closure: by the soundness theorem of the
callee, at each related argument. -/
theorem SimE.calleeEntry (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) {Γ : List Ty} {a b : Ty}
    (g : Tm (a :: Γ) b) (hg : g.InDtFrag) {η : EnvHat Γ} {ρ : Env Γ} (hρ : SimEnv η ρ) :
    SimE (.arr a b) (D.calleeEntry cc g η) (fun v => g.eval (ρ.cons v)) :=
  fun _ _ huv => TimedSim.delay_allow (Tm.dtC_timedSim cc hcc g hg (hρ.cons huv))

namespace Tm

variable {Γ : List Ty} {a b τ : Ty}

/-- A call of the substituted variable: the charge of the call, then the cost of the callee at
the translated argument, its allowance and its charges. -/
theorem dtC_call_calleeEntry (cc : Ty → ℕ) (g : Tm (a :: Γ) b)
    (x : Tm (.arr a b :: Γ) a) (η : EnvHat Γ) :
    (Tm.app (.var .here) x).dtC cc (η.consE (calleeEntry cc g η)) =
      bindT (x.dtC cc (η.consE (calleeEntry cc g η))) fun u =>
        SPTree.Timed.delay (cc a) (SPTree.Timed.delay (g.allowC cc) (g.dtC cc (η.cons u))) := by
  simp [dtC, headVar?, EnvHat.consE, calleeEntry]

/-- **The substitution theorem.** A certified callee `g` substituted for the function variable of
`t`: the evaluation of `t` with that variable bound to the closure of `g` is simulated by the
charges of `t` at the entry of the callee, at the allowance of `t`. Each call is charged the
charge of the call and the cost of the callee at its argument (`dtC_call_calleeEntry`). -/
theorem dtC_subst (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) (t : Tm (.arr a b :: Γ) τ)
    (ht : t.InDtFrag) (g : Tm (a :: Γ) b) (hg : g.InDtFrag) {η : EnvHat Γ} {ρ : Env Γ}
    (hρ : SimEnv η ρ) :
    TimedSim (Sim τ) 1 (t.allowC cc) (t.dtC cc (η.consE (calleeEntry cc g η)))
      (t.eval (ρ.cons fun v => g.eval (ρ.cons v))) :=
  dtC_timedSim cc hcc t ht (hρ.consE (SimE.calleeEntry cc hcc g hg hρ))

/-- The cost of the substituted evaluation is at most the allowance of `t` plus the time of the
charges of `t` at the entry of the callee. -/
theorem cost_subst_le (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) (t : Tm (.arr a b :: Γ) τ)
    (ht : t.InDtFrag) (g : Tm (a :: Γ) b) (hg : g.InDtFrag) {η : EnvHat Γ} {ρ : Env Γ}
    (hρ : SimEnv η ρ) :
    (t.eval (ρ.cons fun v => g.eval (ρ.cons v))).cost ≤
      t.allowC cc + SPTree.Timed.stepTime (t.dtC cc (η.consE (calleeEntry cc g η))) := by
  have h := (dtC_subst cc hcc t ht g hg hρ).cost_le
  rwa [Nat.one_mul] at h

/-- The β-redex of the substitution evaluates as the substituted term after one step. -/
theorem eval_letE_lam (t : Tm (.arr a b :: Γ) τ) (g : Tm (a :: Γ) b) (ρ : Env Γ) :
    (Tm.letE (.lam g) t).eval ρ = .tick (t.eval (ρ.cons fun v => g.eval (ρ.cons v))) :=
  rfl

/-- The substitution theorem at the β-redex `letE (lam g) t`, whose step is paid by the
allowance. -/
theorem dtC_subst_letE (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) (t : Tm (.arr a b :: Γ) τ)
    (ht : t.InDtFrag) (g : Tm (a :: Γ) b) (hg : g.InDtFrag) {η : EnvHat Γ} {ρ : Env Γ}
    (hρ : SimEnv η ρ) :
    TimedSim (Sim τ) 1 (t.allowC cc + 1) (t.dtC cc (η.consE (calleeEntry cc g η)))
      ((Tm.letE (.lam g) t).eval ρ) := by
  rw [eval_letE_lam]
  exact TimedSimTree.tick (dtC_subst cc hcc t ht g hg hρ) (by omega)

end Tm

/-! ## Renaming -/

/-- A translated environment read through a renaming. -/
def EnvHat.comp {Γ Δ : List Ty} (η : EnvHat Δ) (r : Ren Γ Δ) : EnvHat Γ :=
  fun _ x => η _ (r _ x)

theorem EnvHat.comp_lift {Γ Δ : List Ty} {σ : Ty} (η : EnvHat Δ) (r : Ren Γ Δ) (u : σ.hat) :
    (η.cons u).comp r.lift = (η.comp r).cons u := by
  funext τ x
  cases x <;> rfl

/-- The renaming that skips the innermost variable of the target. -/
def Ren.wk {Γ : List Ty} (σ : Ty) : Ren Γ (σ :: Γ) := fun _ x => .there x

/-- A translated environment extended twice, read through the renaming that skips the second
innermost variable, is the environment extended by the innermost entry. -/
theorem EnvHat.cons_cons_comp_lift_wk {Γ : List Ty} {σ σ' : Ty} (η : EnvHat Γ) (u : σ'.hat)
    (w : σ.hat) : ((η.cons u).cons w).comp (Ren.wk σ').lift = η.cons w := by
  funext τ x
  cases x <;> rfl

namespace Tm

/-- The head variable of a renamed term is the renamed head variable. -/
theorem headVar?_rename {Γ Δ : List Ty} {τ : Ty} (t : Tm Γ τ) (r : Ren Γ Δ) :
    (t.rename r).headVar? = t.headVar?.map (r τ) := by
  cases t <;> rfl

/-- Renaming keeps the allowance. -/
theorem allowC_rename (cc : Ty → ℕ) {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ {Δ : List Ty} (r : Ren Γ Δ), (t.rename r).allowC cc = t.allowC cc := by
  induction t <;> intro Δ r <;> simp only [rename, allowC, *]

/-- Renaming keeps purity. -/
theorem pure_rename {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ {Δ : List Ty} (r : Ren Γ Δ), (t.rename r).Pure ↔ t.Pure := by
  induction t <;> intro Δ r <;>
    simp only [rename, Pure, headVar?_rename, Option.map_eq_none_iff, *]

/-- Renaming keeps the fragment. -/
theorem inDtFrag_rename {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ {Δ : List Ty} (r : Ren Γ Δ), (t.rename r).InDtFrag ↔ t.InDtFrag := by
  induction t <;> intro Δ r <;>
    simp only [rename, InDtFrag, headVar?_rename, Option.isSome_map, pure_rename, *]

/-- The charges of a renamed term are the charges of the term in the environment read through the
renaming. -/
theorem dtC_rename (cc : Ty → ℕ) {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ {Δ : List Ty} (r : Ren Γ Δ) (η : EnvHat Δ), (t.rename r).dtC cc η = t.dtC cc (η.comp r) := by
  induction t with
  | app f x ihf ihx =>
    intro Δ r η
    cases hv : f.headVar? with
    | some y =>
      obtain rfl := eq_var_of_headVar? hv
      simp only [rename, dtC, headVar?, ihx]
      rfl
    | none =>
      have hr : (f.rename r).headVar? = none := by rw [headVar?_rename, hv]; rfl
      simp only [rename, dtC, hr, hv, ihf, ihx]
  | lcase xs n c ihxs ihn ihc =>
    intro Δ r η
    simp only [rename, dtC, ihxs, ihn, ihc, EnvHat.comp_lift]
    congr 1
    funext l
    congr 1
    cases l with
    | nil => rfl
    | cons x l' => exact congrArg _ (congrArg _ (EnvHat.comp_lift (σ := .list _) η r l'))
  | _ =>
    intro Δ r η
    simp only [rename, dtC, allowC_rename, EnvHat.comp_lift, *]
    try rfl

end Tm

/-! ## The Diller–Nahm functor of the pure fragment -/

/-- The Diller–Nahm object of a type: its translated values as shapes, with the cost tokens at
each, a data token (`false`) and a clock tick (`true`), as positions. -/
abbrev Ty.dn (τ : Ty) : PFunctor := Container.clockPos τ.hat

/-- At a type other than a function type, the read of a translated value as an entry is the value
at no cost. -/
theorem Ty.read_ofHat {τ : Ty} (h : τ.isArr = false) (u : τ.hat) :
    τ.read (τ.ofHat u) = (0, .ret u) := by
  cases τ <;> simp_all [Ty.isArr, Ty.read, Ty.ofHat]

namespace Tm

variable {Γ : List Ty} {ρ σ τ : Ty}

/-- The costed function of a term in the context of one more variable, at a translated environment
of the others: the value and the cost of its pure costed closure, the translation of the
abstraction (`dtC_lam`). -/
noncomputable def costedC (cc : Ty → ℕ) (t : Tm (σ :: Γ) τ) (η : EnvHat Γ) :
    Container.Costed σ.hat τ.hat where
  fn u := τ.pureVal (t.dtC cc (η.cons u)).2
  cost u := t.allowC cc + (t.dtC cc (η.cons u)).1

/-- The abstraction of a term translates to its costed function. -/
theorem dtC_lam (cc : Ty → ℕ) (t : Tm (σ :: Γ) τ) (η : EnvHat Γ) :
    (Tm.lam t).dtC cc η = (0, .ret ((t.costedC cc η).fn, (t.costedC cc η).cost)) :=
  rfl

/-- The Diller–Nahm morphism of a term in the context of one more variable: its costed function,
whose backward map sends a data token of the output to its demand, one data token of the input and
the clock ticks of its cost, and a clock tick to one clock tick. -/
noncomputable def dnC (cc : Ty → ℕ) (t : Tm (σ :: Γ) τ) (η : EnvHat Γ) :
    DNLens (Ty.dn σ) (Ty.dn τ) :=
  (t.costedC cc η).toDN

/-- The demand of a data token of the output: one data token and the clock ticks of the cost. -/
theorem dnC_toFunB_false (cc : Ty → ℕ) (t : Tm (σ :: Γ) τ) (η : EnvHat Γ) (u : σ.hat) :
    (t.dnC cc η).toFunB u false = {false} + (t.costedC cc η).cost u • {true} :=
  Container.Costed.toDN_false _ u

/-- **Identity.** The variable is the identity morphism. -/
theorem costedC_var (cc : Ty → ℕ) (hσ : σ.isArr = false) (η : EnvHat Γ) :
    (Tm.var .here : Tm (σ :: Γ) σ).costedC cc η = Container.Costed.id σ.hat := by
  ext u
  · change σ.pureVal (σ.read (σ.ofHat u)).2 = u
    rw [Ty.read_ofHat hσ]
    rfl
  · change 0 + (σ.read (σ.ofHat u)).1 = 0
    rw [Ty.read_ofHat hσ]
    rfl

/-- **Identity.** The Diller–Nahm morphism of the variable is the identity. -/
theorem dnC_var (cc : Ty → ℕ) (hσ : σ.isArr = false) (η : EnvHat Γ) :
    (Tm.var .here : Tm (σ :: Γ) σ).dnC cc η = DNLens.id (Ty.dn σ) := by
  rw [dnC, costedC_var cc hσ, Container.Costed.toDN_id]

/-- The composite of `s` and `t` in the syntax of D: `t` after `s`, the β-redex
`let x := s in t`, whose contractum is the substitution of `s` for the variable of `t`. -/
def letComp (s : Tm (ρ :: Γ) σ) (t : Tm (σ :: Γ) τ) : Tm (ρ :: Γ) τ :=
  .letE s (t.rename (Ren.wk ρ).lift)

/-- **Composition is substitution.** The costed function of `t` after a pure `s` is the composite
of their costed functions with the clock tick of the β-step between them. -/
theorem costedC_letComp (cc : Ty → ℕ) (s : Tm (ρ :: Γ) σ) (t : Tm (σ :: Γ) τ) (hs : s.Pure)
    (η : EnvHat Γ) :
    (letComp s t).costedC cc η =
      Container.Costed.comp (t.costedC cc η)
        (Container.Costed.comp (Container.Costed.tick σ.hat) (s.costedC cc η)) := by
  ext u
  all_goals
    obtain ⟨w, hw⟩ := dtC_pure cc s hs (η.cons u)
    have hd : (letComp s t).dtC cc (η.cons u) =
        SPTree.Timed.delay (s.dtC cc (η.cons u)).1 (t.dtC cc (η.cons w)) := by
      simp only [letComp, dtC, bindT, hw, dtC_rename, EnvHat.cons_cons_comp_lift_wk]
      rfl
    have hfn : (s.costedC cc η).fn u = w := by
      change σ.pureVal (s.dtC cc (η.cons u)).2 = w
      rw [hw]
      rfl
  · change τ.pureVal ((letComp s t).dtC cc (η.cons u)).2 =
      τ.pureVal (t.dtC cc (η.cons ((s.costedC cc η).fn u))).2
    rw [hd, hfn]
    rfl
  · change (letComp s t).allowC cc + ((letComp s t).dtC cc (η.cons u)).1 =
      (s.allowC cc + (s.dtC cc (η.cons u)).1 + 1) +
        (t.allowC cc + (t.dtC cc (η.cons ((s.costedC cc η).fn u))).1)
    rw [hd, hfn]
    simp only [letComp, allowC, allowC_rename, SPTree.Timed.delay]
    omega

/-- **Composition is substitution.** The Diller–Nahm morphism of `t` after a pure `s` is the
composite of their morphisms with the clock tick of the β-step between them. -/
theorem dnC_letComp (cc : Ty → ℕ) (s : Tm (ρ :: Γ) σ) (t : Tm (σ :: Γ) τ) (hs : s.Pure)
    (η : EnvHat Γ) :
    (letComp s t).dnC cc η =
      DNLens.comp (t.dnC cc η)
        (DNLens.comp (Container.Costed.tick σ.hat).toDN (s.dnC cc η)) := by
  rw [dnC, costedC_letComp cc s t hs, Container.Costed.toDN_comp, Container.Costed.toDN_comp]
  rfl

/-- **The functor bounds evaluation.** A pure term of the fragment, in related environments and at
related values of its variable, evaluates to a leaf after at most the clock ticks that a data token
of its output demands, at a value related to the forward map of its Diller–Nahm morphism. This is
the soundness theorem `dtC_timedSim` at the abstraction of the term. -/
theorem dnC_bounds (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) (t : Tm (σ :: Γ) τ) (ht : t.InDtFrag)
    (hp : t.Pure) {η : EnvHat Γ} {ρ' : Env Γ} (hρ : SimEnv η ρ') {u : σ.hat} {v : Val σ}
    (huv : Sim σ u v) :
    ∃ m w, t.eval (ρ'.cons v) = stepN CTree.tick m (.ret w) ∧
      m ≤ ((t.dnC cc η).toFunB u false).count true ∧ Sim τ ((t.dnC cc η).toFunA u) w := by
  have h : TimedSimTree (Sim (.arr σ τ)) 1 _ (.ret ((t.costedC cc η).fn, (t.costedC cc η).cost))
      (.ret fun v => t.eval (ρ'.cons v)) := dtC_timedSim cc hcc (Tm.lam t) ⟨ht, hp⟩ hρ
  cases h with
  | ret hs =>
    obtain ⟨m, w', he', hm, hw'⟩ := hs u v huv
    refine ⟨m, w', he', ?_, hw'⟩
    rw [dnC, Container.Costed.toDN_false]
    simpa using hm

end Tm

end CatCrypt.Complexity.D
