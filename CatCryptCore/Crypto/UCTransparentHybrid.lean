/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparent

@[expose] public section
set_option autoImplicit false

/-!
# Hybrid composition for transparent realization

A hybrid protocol `π` calls a subroutine once per activation: on an event
`e` it computes a subroutine event (`pre`), the subroutine answers, and `π`
computes its output from the answer (`post`). `π.withSub X` is `π` running
with the subroutine system `X`. In the `G`-hybrid model the subroutine is the
ideal world of `G` (`UCTransparent.ideal G S_G`); in the real world it is a
protocol `ρ` realizing it.

## Main definitions

* `Hybrid σ E O EG OG` — a hybrid protocol with state `σ`, outer interface
  `(E, O)` and subroutine interface `(EG, OG)`, with lossless `pre`, `post`.
* `Hybrid.withSub π X` — the composed system.
* `Hybrid.reduce π Z` — the environment for the subroutine obtained by
  running the outer environment `Z` together with `π`;
  `Hybrid.reduceEnv` does the same for `UCConcrete.Env`.

## Main results

* `Hybrid.view_withSub` — the view of `Z` against `π.withSub X` is the first
  component of the view of `π.reduce Z` against `X`.
* `Hybrid.adv_withSub` — the advantage of `Z` between `π.withSub X` and
  `π.withSub Y` equals the advantage of `π.reduceEnv Z` between `X` and `Y`.
* `Hybrid.realizes_compose` — if `π.withSub Y` realizes `I` with bound `b₁`
  and `X` realizes `Y` with bound `b₂`, then `π.withSub X` realizes `I` with
  bound `b₁ ζ Z + b₂ (ζ × σ) (π.reduceEnv Z)`.
* `Hybrid.transparent_compose` — the transparent instance: every hypothesis
  is structural (losslessness, agreement of the simulators with the
  protocols on guarded transitions), and the bound is the sum of two
  guard-failure probabilities, one for the outer guard on the hybrid run and
  one for the inner guard on the run of `ρ` against the reduced environment.

The hypotheses of `realizes_compose` are the realization statements being
composed; `transparent_compose` derives both from `transparent_realizes`, so
no advantage bound is assumed there.
-/

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-- A hybrid protocol: state `σ`, outer events `E` and outputs `O`, one call
    per activation to a subroutine with events `EG` and outputs `OG`. -/
structure Hybrid (σ E O EG OG : Type) where
  /-- Initial state. -/
  init : σ
  /-- From an outer event, the subroutine event. -/
  pre : σ → E → SPComp (σ × EG)
  /-- From the subroutine answer, the outer output. -/
  post : σ → OG → SPComp (σ × O)
  /-- `pre` never fails. -/
  pre_noFail : ∀ s e, SPComp.NoFail (pre s e)
  /-- `post` never fails. -/
  post_noFail : ∀ s o, SPComp.NoFail (post s o)

namespace Hybrid

variable {σ τ υ ζ E O EG OG : Type}

/-- The hybrid protocol `π` running with the subroutine system `X`. -/
noncomputable def withSub (π : Hybrid σ E O EG OG) (X : Sys τ EG OG) : Sys (σ × τ) E O where
  init := (π.init, X.init)
  step t e :=
    SPComp.bind (π.pre t.1 e) fun a =>
      SPComp.bind (X.step t.2 a.2) fun q =>
        SPComp.bind (π.post a.1 q.2) fun r => SPComp.pure ((r.1, q.1), r.2)

/-- The environment for the subroutine obtained by running `Z` with `π`: its
    state is the pair of the state of `Z` and the state of `π`. -/
noncomputable def reduce (π : Hybrid σ E O EG OG) (Z : Strat ζ E O) : Strat (ζ × σ) EG OG where
  rounds := Z.rounds
  init := (Z.init, π.init)
  next zs :=
    SPComp.bind (Z.next zs.1) fun a =>
      SPComp.bind (π.pre zs.2 a.2) fun b => SPComp.pure ((a.1, b.1), b.2)
  obs zs o :=
    SPComp.bind (π.post zs.2 o) fun r =>
      SPComp.bind (Z.obs zs.1 r.2) fun z => SPComp.pure (z, r.1)
  next_noFail _ :=
    Assumptions.SPComp.bind_noFail (Z.next_noFail _) fun _ =>
      Assumptions.SPComp.bind_noFail (π.pre_noFail _ _) fun _ => SPComp.pure_noFail _
  obs_noFail _ _ :=
    Assumptions.SPComp.bind_noFail (π.post_noFail _ _) fun _ =>
      Assumptions.SPComp.bind_noFail (Z.obs_noFail _ _) fun _ => SPComp.pure_noFail _

/-- The reduced `UCConcrete.Env`: reduced strategy, same heap, and the
    distinguisher applied to the first component. -/
noncomputable def reduceEnv (π : Hybrid σ E O EG OG) (Z : Env (Strat ζ E O) ζ) :
    Env (Strat (ζ × σ) EG OG) (ζ × σ) :=
  ⟨π.reduce Z.input, Z.heap, fun zs => Z.dist zs.1⟩

/-- The run against the composed system is the run of the reduced
    environment against the subroutine, up to regrouping the configuration. -/
theorem loop_withSub (π : Hybrid σ E O EG OG) (X : Sys τ EG OG) (Z : Strat ζ E O) :
    ∀ n (c : ζ × (σ × τ) × Bool),
      SPComp.map (fun c => ((c.1, c.2.1.1), c.2.1.2, c.2.2))
          (loop (π.withSub X) (fun _ => false) Z n c) =
        loop X (fun _ => false) (π.reduce Z) n ((c.1, c.2.1.1), c.2.1.2, c.2.2) := by
  intro n
  induction n with
  | zero => intro c; simp [loop, SPComp.map]
  | succ n ih =>
    intro c
    simp only [loop, withSub, reduce, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind] at ih ⊢
    congr 1; funext a; congr 1; funext b; congr 1; funext q; congr 1; funext r
    congr 1; funext z
    exact ih _

/-- The view of `Z` against `π.withSub X` is the first component of the view
    of `π.reduce Z` against `X`. -/
theorem view_withSub (π : Hybrid σ E O EG OG) (X : Sys τ EG OG) (Z : Strat ζ E O) :
    view (π.withSub X) Z = SPComp.map Prod.fst (view X (π.reduce Z)) := by
  unfold view run
  have h := loop_withSub π X Z Z.rounds (Z.init, (π.withSub X).init, false)
  have h2 : SPComp.map Prod.fst (loop (π.withSub X) (fun _ => false) Z Z.rounds
      (Z.init, (π.withSub X).init, false)) =
      SPComp.map Prod.fst (SPComp.map Prod.fst (SPComp.map
        (fun c => ((c.1, c.2.1.1), c.2.1.2, c.2.2))
        (loop (π.withSub X) (fun _ => false) Z Z.rounds (Z.init, (π.withSub X).init, false)))) := by
    simp [SPComp.map, SPComp.bind_assoc]
  rw [h2, h]; rfl

/-- The advantage of `Z` between `π.withSub X` and `π.withSub Y` is the
    advantage of the reduced environment between `X` and `Y`. -/
theorem adv_withSub (π : Hybrid σ E O EG OG) (X : Sys τ EG OG) (Y : Sys υ EG OG)
    (Z : Env (Strat ζ E O) ζ) :
    adv (π.withSub X) (π.withSub Y) Z = adv X Y (π.reduceEnv Z) := by
  rw [adv_eq, adv_eq, view_withSub, view_withSub]
  simp [reduceEnv, SPComp.map, SPComp.bind_assoc]

/-- **Hybrid composition** (composition plumbing). If `π.withSub Y` realizes `I` with bound `b₁`
    and `X` realizes `Y` with bound `b₂`, then `π.withSub X` realizes `I`
    with the sum of `b₁` and of `b₂` at the reduced environment. -/
theorem realizes_compose {υ' : Type} (π : Hybrid σ E O EG OG) (X : Sys τ EG OG)
    (Y : Sys υ EG OG) (I : Sys υ' E O)
    (b₁ : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞)
    (b₂ : (ζ : Type) → Env (Strat ζ EG OG) ζ → ℝ≥0∞)
    (h₁ : Realizes (π.withSub Y) I b₁) (h₂ : Realizes X Y b₂) :
    Realizes (π.withSub X) I (fun ζ Z => b₂ (ζ × σ) (π.reduceEnv Z) + b₁ ζ Z) := by
  intro ζ
  have hsub : DistC (view (π.withSub X) (ζ := ζ)) (view (π.withSub Y))
      (fun Z => b₂ (ζ × σ) (π.reduceEnv Z)) := fun Z => by
    have := adv_withSub π X Y Z
    unfold adv at this
    rw [this]
    exact h₂ (ζ × σ) (π.reduceEnv Z)
  exact hsub.triangle (h₁ ζ)

/-- Single steps of `π.withSub X` never fail when those of `X` never fail. -/
theorem withSub_noFail (π : Hybrid σ E O EG OG) (X : Sys τ EG OG)
    (hX : ∀ t e, SPComp.NoFail (X.step t e)) :
    ∀ t e, SPComp.NoFail ((π.withSub X).step t e) := by
  intro t e
  simp only [withSub]
  exact Assumptions.SPComp.bind_noFail (π.pre_noFail _ _) fun _ =>
    Assumptions.SPComp.bind_noFail (hX _ _) fun _ =>
      Assumptions.SPComp.bind_noFail (π.post_noFail _ _) fun _ => SPComp.pure_noFail _

/-- Single steps of `ideal F S` never fail when those of `S` never fail. -/
theorem ideal_noFail {σ' E' O' : Type} (F : TFunc σ' E' O') (S : Sys σ' E' O')
    (hS : ∀ s e, SPComp.NoFail (S.step s e)) :
    ∀ t e, SPComp.NoFail ((ideal F S).step t e) := by
  intro t e
  simp only [ideal]
  exact Assumptions.SPComp.bind_noFail (hS _ _) fun _ => SPComp.pure_noFail _

/-- **Transparent hybrid composition** (composition plumbing). Let `G` be a transparent
    functionality realized by the lossless protocol `ρ` through the lossless
    simulator `S_G`, and let `F` be a transparent functionality over the
    state space of the `G`-hybrid world `π.withSub (ideal G S_G)`, with
    lossless simulator `S_F`. Assume that each simulator starts in the
    initial state of the system it simulates and agrees with it on every
    transition that keeps the respective guard true. Then `π.withSub ρ`
    realizes `ideal F S_F`, with bound the probability that the guard of `G`
    fails on the run of `ρ` against the reduced environment plus the
    probability that the guard of `F` fails on the run of the `G`-hybrid
    world. -/
theorem transparent_compose {σG : Type} (π : Hybrid σ E O EG OG)
    (ρ S_G : Sys σG EG OG) (G : TFunc σG EG OG)
    (S_F : Sys (σ × σG × Trace σG EG OG × Bool) E O)
    (F : TFunc (σ × σG × Trace σG EG OG × Bool) E O)
    (hρ : ∀ s e, SPComp.NoFail (ρ.step s e)) (hSG : ∀ s e, SPComp.NoFail (S_G.step s e))
    (hSF : ∀ s e, SPComp.NoFail (S_F.step s e))
    (hinitG : S_G.init = ρ.init) (hinitF : S_F.init = (π.withSub (ideal G S_G)).init)
    (hsimG : ∀ s (tr : Trace σG EG OG) e,
      SPComp.bind (ρ.step s e) (fun p => if G.guard (tr ++ [(e, p.2, p.1)])
        then SPComp.pure p else SPComp.fail) =
      SPComp.bind (S_G.step s e) (fun p => if G.guard (tr ++ [(e, p.2, p.1)])
        then SPComp.pure p else SPComp.fail))
    (hsimF : ∀ s (tr : Trace (σ × σG × Trace σG EG OG × Bool) E O) e,
      SPComp.bind ((π.withSub (ideal G S_G)).step s e)
        (fun p => if F.guard (tr ++ [(e, p.2, p.1)]) then SPComp.pure p else SPComp.fail) =
      SPComp.bind (S_F.step s e)
        (fun p => if F.guard (tr ++ [(e, p.2, p.1)]) then SPComp.pure p else SPComp.fail)) :
    Realizes (π.withSub ρ) (ideal F S_F) (fun _ Z =>
      guardFail ρ G.guard (π.reduceEnv Z) + guardFail (π.withSub (ideal G S_G)) F.guard Z) :=
  realizes_compose π ρ (ideal G S_G) (ideal F S_F) _ _
    (transparent_realizes (π.withSub (ideal G S_G)) F S_F hinitF
      (withSub_noFail π _ (ideal_noFail G S_G hSG)) hSF hsimF)
    (transparent_realizes ρ G S_G hinitG hρ hSG hsimG)

end Hybrid

end CatCrypt.Crypto.UCTransparent
