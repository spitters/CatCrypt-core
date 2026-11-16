/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.CryptoVerif.Find

/-!
# Events of CryptoVerif games and their transport across indistinguishability

CryptoVerif's distinguishers read the executed events, and a CryptoVerif event bound
`query event(e) ==> false` moves along a sequence of games. Here the output of each call
carries the events it executed, so an environment can watch an event: `watchEnv Z w` runs `Z`,
keeps the disjunction of `w` over the outputs it observes, and accepts on that flag. When the
bad predicate of a system is the old predicate or `w` of the output, at every step, the
probability `prBad` of the bad event is the acceptance probability of the watching
environment against the same system. An event bound therefore crosses a `Realizes` step at the
cost of the step's bound at the watching environment.

## Main results

* `watchStrat`, `watchEnv` — the strategy that also keeps the disjunction of a test on its
  observed outputs, and the environment that accepts on it.
* `loop_watch`, `prBad_eq_watch` — for a system whose bad predicate is the old one or a test
  of the output, the flagged run is the run of the watching strategy, and `prBad` is the
  acceptance probability of `watchEnv`.
* `CvGame.evBad`, `CvGame.prBad_eq_watch` — the event `e` in the log of a game, and its
  probability as the acceptance probability of the environment that watches `e` in the
  outputs.
* `CvEventBound`, `CvEventBound.transport` — the event bound `query event(e) ==> false` at a
  bound `δ`, and its transport across `Realizes G.sys G'.sys ε`: the bound `δ + ε` at the watching
  environment.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.CryptoVerifLogic

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open scoped ENNReal

section Watch

variable {τ ζ E O ρ : Type}

/-- The strategy `Z` that keeps, beside its state, the disjunction of the test `w` on the
outputs it observes, started at `false`. -/
noncomputable def watchStrat (Z : Strat ζ E O) (w : O → Bool) : Strat (ζ × Bool) E O where
  rounds := Z.rounds
  init := (Z.init, false)
  next zb := SPComp.map (fun a => ((a.1, zb.2), a.2)) (Z.next zb.1)
  obs zb o := SPComp.map (fun z => (z, zb.2 || w o)) (Z.obs zb.1 o)
  next_noFail _ :=
    CatCrypt.Crypto.Assumptions.SPComp.bind_noFail (Z.next_noFail _) fun _ =>
      SPComp.pure_noFail _
  obs_noFail _ _ :=
    CatCrypt.Crypto.Assumptions.SPComp.bind_noFail (Z.obs_noFail _ _) fun _ =>
      SPComp.pure_noFail _

/-- The environment `Z` with the strategy `watchStrat Z.input w`, whose distinguisher outputs
the flag. -/
noncomputable def watchEnv (Z : Env (Strat ζ E O) ζ) (w : O → Bool) :
    Env (Strat (ζ × Bool) E O) (ζ × Bool) where
  input := watchStrat Z.input w
  heap := Z.heap
  dist zb := SPComp.pure zb.2

/-- For a system whose step is a map of a kernel `K` and whose bad predicate on the new state
is the old one or the test `w` of the output, the run of the watching strategy is the flagged
run, from a flag that is set whenever the state is bad. -/
theorem loop_watch (S : Sys τ E O) (bad : τ → Bool) (w : O → Bool)
    (K : τ → E → SPComp ρ) (u : τ → E → ρ → τ) (out : τ → E → ρ → O)
    (hS : ∀ t a, S.step t a = SPComp.map (fun r => (u t a r, out t a r)) (K t a))
    (hbad : ∀ t a r, bad (u t a r) = (bad t || w (out t a r))) (Z : Strat ζ E O) {β : Type} :
    ∀ (n : ℕ) (z : ζ) (t : τ) (f : Bool) (C : ζ × τ × Bool → SPComp β),
      (bad t = true → f = true) →
      SPComp.bind (loop S (fun _ => false) (watchStrat Z w) n ((z, f), t, false))
          (fun c => C (c.1.1, c.2.1, c.1.2)) =
        SPComp.bind (loop S bad Z n (z, t, f)) C := by
  intro n
  induction n with
  | zero => intro z t f C _; simp [loop, SPComp.pure_bind]
  | succ n ih =>
    intro z t f C hf
    have hn : ∀ zb, (watchStrat Z w).next zb =
        SPComp.map (fun a => ((a.1, zb.2), a.2)) (Z.next zb.1) := fun _ => rfl
    have ho : ∀ zb o, (watchStrat Z w).obs zb o =
        SPComp.map (fun z => (z, zb.2 || w o)) (Z.obs zb.1 o) := fun _ _ => rfl
    simp only [loop, hS, hn, ho, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Bool.or_false]
    congr 1; funext a; congr 1; funext r; congr 1; funext z'
    have hor : (f || bad (u t a.2 r)) = (f || w (out t a.2 r)) := by
      rw [hbad]
      cases h : bad t <;> simp_all
    rw [hor]
    exact ih _ _ _ _ fun h => by
      rw [hbad] at h
      cases h' : bad t <;> simp_all

/-- **The bad event as an acceptance probability.** For a system whose bad predicate on the
new state is the old one or the test `w` of the output, and whose initial state is good,
`prBad S bad Z` is the probability that `watchEnv Z w` accepts against `S`. -/
theorem prBad_eq_watch (S : Sys τ E O) (bad : τ → Bool) (w : O → Bool)
    (K : τ → E → SPComp ρ) (u : τ → E → ρ → τ) (out : τ → E → ρ → O)
    (hS : ∀ t a, S.step t a = SPComp.map (fun r => (u t a r, out t a r)) (K t a))
    (hbad : ∀ t a r, bad (u t a r) = (bad t || w (out t a r))) (hinit : bad S.init = false)
    (Z : Env (Strat ζ E O) ζ) :
    prBad S bad Z = prTrue (SPComp.bind (view S (watchEnv Z w).input) (watchEnv Z w).dist)
      Z.heap := by
  unfold prBad run view
  rw [hinit, ← loop_watch S bad w K u out hS hbad Z.input _ _ _ _ (fun c => SPComp.pure c.2.2)
    (by simp [hinit])]
  simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  rfl

end Watch

variable {I : CvIface}

/-- The event `e` has been executed: it is in the log of the configuration. -/
def CvGame.evBad (G : CvGame I) (e : I.Ev) (c : CvConf G) : Bool :=
  decide (e ∈ c.log)

/-- The test of an output for the event `e`. -/
def cvWatch (e : I.Ev) (o : CvOut I) : Bool :=
  decide (e ∈ o.2)

/-- **Events in the view.** The probability that the event `e` is executed in a run of `Z`
against the game `G` is the acceptance probability of the environment that watches `e` in the
outputs. -/
theorem CvGame.prBad_eq_watch (G : CvGame I) (e : I.Ev) {ζ : Type}
    (Z : Env (Strat ζ (CvCall I) (CvOut I)) ζ) :
    prBad G.sys (G.evBad e) Z =
      prTrue (SPComp.bind (view G.sys (watchEnv Z (cvWatch e)).input)
        (watchEnv Z (cvWatch e)).dist) Z.heap :=
  CatCrypt.Crypto.CryptoVerifLogic.prBad_eq_watch G.sys (G.evBad e) (cvWatch e) G.kernel G.next
    (fun _ _ r => G.out r) (fun _ _ => rfl)
    (fun c a r => by simp [CvGame.evBad, cvWatch, G.log_next c a r])
    (by simp [CvGame.evBad, CvGame.sys]) Z

/-- CryptoVerif's `query event(e) ==> false` at the bound `δ`: in every run of every
environment against `G`, the event `e` is executed with probability at most `δ`. -/
def CvEventBound (G : CvGame I) (e : I.Ev) (δ : CvBound I) : Prop :=
  ∀ (ζ : Type) (Z : Env (Strat ζ (CvCall I) (CvOut I)) ζ), prBad G.sys (G.evBad e) Z ≤ δ ζ Z

/-- **Transport of an event bound.** If `G ≈_ε G'` and the event `e` has probability at most
`δ` in `G'`, then it has probability at most `δ + ε` in `G`, with `ε` at the environment that
watches `e`. -/
theorem CvEventBound.transport {G G' : CvGame I} {e : I.Ev} {ε δ : CvBound I}
    (h : Realizes G.sys G'.sys ε) (h' : CvEventBound G' e δ) :
    CvEventBound G e fun ζ Z => δ ζ Z + ε (ζ × Bool) (watchEnv Z (cvWatch e)) := by
  intro ζ Z
  have hg := h (ζ × Bool) (watchEnv Z (cvWatch e))
  have hG := G.prBad_eq_watch e Z
  have hG' := G'.prBad_eq_watch e Z
  have hδ := h' ζ Z
  simp only [Env.gap] at hg
  rw [hG]
  rw [hG'] at hδ
  calc _ ≤ prTrue (SPComp.bind (view G'.sys (watchEnv Z (cvWatch e)).input)
        (watchEnv Z (cvWatch e)).dist) Z.heap + ε (ζ × Bool) (watchEnv Z (cvWatch e)) :=
          le_add_of_absDiff_le hg
    _ ≤ δ ζ Z + ε (ζ × Bool) (watchEnv Z (cvWatch e)) := by gcongr

end CatCrypt.Crypto.CryptoVerifLogic
