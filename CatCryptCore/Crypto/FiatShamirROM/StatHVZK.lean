/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Game
public import CatCryptCore.Crypto.Constructions.ECBCPRFFlag

/-!
# Fiat–Shamir in the random-oracle model: the signing-oracle simulation

The signing-oracle simulation hop of `FiatShamirROM.Game` for a protocol whose
honest-verifier zero knowledge holds up to a statistical distance: at a pair
`(x, w)`, for every message and every visible oracle, every test on traces with
values in `[0, 1]` has expectation under the trace of the honest attempt (on the
attempts whose hidden points are undefined) at most its expectation under the
simulated trace plus `δ`, both averaged over uniform oracle values. The trace of an
attempt is its evaluated public entries, its programmed public entries and its
answer, so a test does not read the hidden entries. The distances may depend on the
pair; the bound on the EUF-CMA advantage is then an expectation over the generator.

For a Σ-protocol the tests read the transcript `(a, z)` and do not read the
commitment of a rejected transcript, because the signing oracle answers a rejected
attempt without its commitment; such a protocol is the instance
`Sigma.toProtocol P M`.

## Main definitions

* `Protocol.StatHVZK δ`, `Protocol.KeyBound Γ` — statistical HVZK and the key
  bound at every generated pair
* `Protocol.hvzkDistAt x w`, `Protocol.keyDistAt x w` — the least distance and the
  least key bound at one pair
* `Sigma.RejectBlind g` — the test `g` does not read the commitment of a rejected
  transcript
* `Sigma.StatHVZKAt x w δ`, `Sigma.StatHVZK δ` — statistical HVZK with distance
  `δ` at one pair and at every generated pair
* `Sigma.hvzkDistAt x w`, `Sigma.hvzkDist` — the least such distances
* `Sigma.commitDistAt x w`, `Sigma.commitDist` — the largest probability of a
  commitment value at one pair and over the generated pairs
* `Sigma.hvzkDistOn E x w` — the HVZK distance at `(x, w)` on the transcripts
  whose response satisfies `E`

## Main results

* `run_real_le_sim` — on the outcomes with the flag cleared, a test of the real
  run is at most the same test of the simulated run plus `q·δ`, for a run with at
  most `q` signing queries
* `Protocol.eufcmaAdvantage_le_simAdvantage_perKey` — the EUF-CMA advantage is at
  most the simulated-game advantage plus the expectation over generated pairs of
  `qS·δ(x, w) + qS·(qH + V + μ·qS)·Γ(x, w)`
* `Protocol.eufcmaAdvantage_le_simAdvantage_dist`,
  `Protocol.eufcmaAdvantage_le_simAdvantage_stat` — the same with the distances
  `hvzkDistAt` and `keyDistAt`, and with constant bounds
* `Sigma.statHVZKAt_toProtocol`, `Sigma.keyBoundAt_toProtocol` — statistical HVZK
  and the commitment bound of a Σ-protocol give those of its protocol
* `eufcmaAdvantage_le_simAdvantage_perKey`, `eufcmaAdvantage_le_simAdvantage_dist`,
  `eufcmaAdvantage_le_simAdvantage_stat`, `eufcmaAdvantage_le_simAdvantage` — for
  a Σ-protocol, the bounds `qS·δ + qS·(qH + 1 + qS)·γ` and, for perfect HVZK,
  `qS·(qH + 1 + qS)·γ`
* `Sigma.PerfectHVZK.statHVZK` — perfect HVZK is statistical HVZK with distance
  `0`
* `Sigma.hvzkDistAt_le_on_add_on`, `Sigma.hvzkDistOn_eq_zero_of_eq`,
  `Sigma.hvzkDistOn_reject_eq_zero` — splitting the HVZK distance of a Σ-protocol
  by an event on the response
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open CatCrypt.Crypto.Constructions.ECBCPRF (tsum_bind_mul tsum_pure_mul)
open scoped ENNReal

/-- Expectation of `g` under the image of `p` by `f`. -/
theorem tsum_map_mul' {α β : Type} (p : PMF α) (f : α → β) (g : β → ℝ≥0∞) :
    ∑' y, (p.map f) y * g y = ∑' a, p a * g (f a) := by
  rw [PMF.map, tsum_bind_mul]
  exact tsum_congr fun a => congrArg _ (tsum_pure_mul (f a) g)

/-! ## Distances of a protocol -/

namespace Protocol

variable (G : Protocol)

/-- **Statistical honest-verifier zero knowledge** with distance `δ` at every
generated pair. -/
def StatHVZK (δ : ℝ≥0∞) : Prop :=
  ∀ x w, (x, w) ∈ G.gen.support → G.StatHVZKAt x w δ

/-- **Key bound** `Γ` at every generated pair. -/
def KeyBound (Γ : ℝ≥0∞) : Prop :=
  ∀ x w, (x, w) ∈ G.gen.support → G.KeyBoundAt x w Γ

/-- The HVZK distance of `G` at the pair `(x, w)`: the supremum, over messages,
visible oracles and tests on traces with values in `[0, 1]`, of the expectation of
the test on the trace of the attempt (on the attempts whose hidden points are
undefined) minus its expectation on the simulated trace, over uniform values. -/
noncomputable def hvzkDistAt (x : G.Stmt) (w : G.Wit) : ℝ≥0∞ :=
  ⨆ (m : G.Msg) (look : G.Key → Option G.Ch) (g : G.Trace → ℝ≥0∞) (_ : ∀ y, g y ≤ 1),
    (∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformOfFintype G.Rand r *
      (if G.hidFresh look x w m r (G.vals look x w m r e) then
        g (G.trace x w m r (G.vals look x w m r e)) else 0)) -
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' s, PMF.uniformOfFintype G.SimRand s *
      g (G.simTrace look x m e s)

/-- The key distance of `G` at the pair `(x, w)`: the supremum, over messages,
visible oracles and randomized guessers on traces, of the expected number of
programmed or hidden entries whose point the guess from `guessView` hits. -/
noncomputable def keyDistAt (x : G.Stmt) (w : G.Wit) : ℝ≥0∞ :=
  ⨆ (m : G.Msg) (look : G.Key → Option G.Ch) (Q : G.Trace → PMF G.Key),
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformOfFintype G.Rand r *
      ∑ i, (if G.flagging x w m r (G.vals look x w m r e) i then
        Q (G.guessView look x w m r e i) (G.key x w m r (G.vals look x w m r e) i) else 0)

theorem statHVZKAt_hvzkDistAt (x : G.Stmt) (w : G.Wit) :
    G.StatHVZKAt x w (G.hvzkDistAt x w) := by
  intro m look g hg
  rw [← tsub_le_iff_left]
  exact le_iSup_of_le m <| le_iSup_of_le look <| le_iSup_of_le g <| le_iSup_of_le hg le_rfl

theorem keyBoundAt_keyDistAt (x : G.Stmt) (w : G.Wit) : G.KeyBoundAt x w (G.keyDistAt x w) :=
  fun m look Q => le_iSup_of_le m <| le_iSup_of_le look <| le_iSup_of_le Q le_rfl

end Protocol

/-! ## Σ-protocols -/

namespace Sigma

variable (P : Sigma)

/-- The test `g` on transcripts does not read the commitment of a rejected
transcript. -/
def RejectBlind (g : P.Com × P.Resp → ℝ≥0∞) : Prop :=
  ∀ a a' z, P.accept z = false → g (a, z) = g (a', z)

/-- **Statistical honest-verifier zero knowledge at one pair** with distance `δ`.
For the pair `(x, w)`, every challenge `e` and every test `g` with values in
`[0, 1]` that does not read the commitment of a rejected transcript, the
expectation of `g` on the honest transcript `(commit, respond e)` under uniform
prover randomness is at most its expectation on the simulator output under
uniform simulator randomness, plus `δ`. -/
def StatHVZKAt (x : P.Stmt) (w : P.Wit) (δ : ℝ≥0∞) : Prop :=
  ∀ e (g : P.Com × P.Resp → ℝ≥0∞), (∀ y, g y ≤ 1) → P.RejectBlind g →
    ∑' r, PMF.uniformOfFintype P.Rand r * g (P.commit x w r, P.respond x w r e) ≤
      ∑' s, PMF.uniformOfFintype P.SimRand s * g (P.simulate x e s) + δ

/-- **Statistical honest-verifier zero knowledge** with distance `δ` at every
generated pair. -/
def StatHVZK (δ : ℝ≥0∞) : Prop :=
  ∀ x w, (x, w) ∈ P.gen.support → P.StatHVZKAt x w δ

/-- The HVZK distance of `P` at the pair `(x, w)`: the supremum, over challenges
and tests with values in `[0, 1]` that do not read the commitment of a rejected
transcript, of the expectation of the test on the honest transcript minus its
expectation on the simulated transcript. -/
noncomputable def hvzkDistAt (x : P.Stmt) (w : P.Wit) : ℝ≥0∞ :=
  ⨆ (e : P.Ch) (g : P.Com × P.Resp → ℝ≥0∞) (_ : ∀ y, g y ≤ 1) (_ : P.RejectBlind g),
    (∑' r, PMF.uniformOfFintype P.Rand r * g (P.commit x w r, P.respond x w r e)) -
      ∑' s, PMF.uniformOfFintype P.SimRand s * g (P.simulate x e s)

/-- The HVZK distance of `P`: the supremum of `hvzkDistAt` over generated
pairs. -/
noncomputable def hvzkDist : ℝ≥0∞ :=
  ⨆ (x : P.Stmt) (w : P.Wit) (_ : (x, w) ∈ P.gen.support), P.hvzkDistAt x w

theorem statHVZKAt_hvzkDistAt (x : P.Stmt) (w : P.Wit) :
    P.StatHVZKAt x w (P.hvzkDistAt x w) := by
  intro e g hg hb
  rw [← tsub_le_iff_left]
  exact le_iSup_of_le e <| le_iSup_of_le g <| le_iSup_of_le hg <| le_iSup_of_le hb le_rfl

theorem statHVZK_hvzkDist : P.StatHVZK P.hvzkDist := by
  intro x w hxw e g hg hb
  refine (P.statHVZKAt_hvzkDistAt x w e g hg hb).trans (add_le_add le_rfl ?_)
  exact le_iSup_of_le x <| le_iSup_of_le w <| le_iSup_of_le hxw le_rfl

/-- The commitment distance of `P` at the pair `(x, w)`: the largest probability
of a commitment value under uniform prover randomness. -/
noncomputable def commitDistAt (x : P.Stmt) (w : P.Wit) : ℝ≥0∞ :=
  ⨆ (a : P.Com), (PMF.uniformOfFintype P.Rand).toOuterMeasure {r | P.commit x w r = a}

/-- The commitment distance of `P`: the supremum of `commitDistAt` over generated
pairs. -/
noncomputable def commitDist : ℝ≥0∞ :=
  ⨆ (x : P.Stmt) (w : P.Wit) (_ : (x, w) ∈ P.gen.support) (a : P.Com),
    (PMF.uniformOfFintype P.Rand).toOuterMeasure {r | P.commit x w r = a}

theorem commitBoundAt_commitDistAt (x : P.Stmt) (w : P.Wit) :
    P.CommitBoundAt x w (P.commitDistAt x w) := fun a => le_iSup_of_le a le_rfl

theorem commitBound_commitDist : P.CommitBound P.commitDist := fun x w hxw a =>
  le_iSup_of_le x <| le_iSup_of_le w <| le_iSup_of_le hxw <| le_iSup_of_le a le_rfl

variable {P}

/-- Perfect HVZK is statistical HVZK with distance `0`. -/
theorem PerfectHVZK.statHVZK (h : P.PerfectHVZK) : P.StatHVZK 0 := by
  intro x w hxw e g _ _
  have := congrArg (fun p : PMF (P.Com × P.Resp) => ∑' y, p y * g y) (h x w hxw e)
  simp only [tsum_map_mul'] at this
  rw [this, add_zero]

variable (P) {M : Type} [DecidableEq M]

/-- The view of a transcript `(a, z)` on `m` with challenge `e`: the entry
`((a, m), e)` and the signature `(a, z)` when `z` is accepted, nothing
otherwise. -/
def transcriptView (m : M) (e : P.Ch) (az : P.Com × P.Resp) : (P.toProtocol M).View :=
  if P.accept az.2 then ([((az.1, m), e)], some az) else ([], none)

theorem view_toProtocol (x : P.Stmt) (w : P.Wit) (m : M) (r : P.Rand)
    (e : Fin 1 → P.Ch) :
    (P.toProtocol M).view x w m r e =
      P.transcriptView m (e 0) (P.commit x w r, P.respond x w r (e 0)) := by
  unfold Protocol.view Protocol.pubEntries Protocol.entries transcriptView
  cases h : P.accept (P.respond x w r (e 0)) <;>
    simp [toProtocol, h, List.finRange_succ, Fin.fin_one_eq_zero]

theorem simulate_toProtocol (x : P.Stmt) (m : M) (e : Fin 1 → P.Ch) (s : P.SimRand) :
    (P.toProtocol M).simulate x m e s = P.transcriptView m (e 0) (P.simulate x (e 0) s) :=
  rfl

theorem vals_toProtocol (look : (P.toProtocol M).Key → Option P.Ch) (x : P.Stmt) (w : P.Wit)
    (m : M) (r : P.Rand) (e : Fin 1 → P.Ch) : (P.toProtocol M).vals look x w m r e = e :=
  Protocol.vals_of_ev_false (fun _ => rfl) look x w m r e

theorem trace_toProtocol (x : P.Stmt) (w : P.Wit) (m : M) (r : P.Rand) (e : Fin 1 → P.Ch) :
    (P.toProtocol M).trace x w m r e =
      ([], P.transcriptView m (e 0) (P.commit x w r, P.respond x w r (e 0))) := by
  rw [Protocol.trace, Protocol.evEntries_of_ev_false (fun _ => rfl), view_toProtocol]

theorem simTrace_toProtocol (look : (P.toProtocol M).Key → Option P.Ch) (x : P.Stmt) (m : M)
    (e : Fin 1 → P.Ch) (s : P.SimRand) :
    (P.toProtocol M).simTrace look x m e s =
      ([], P.transcriptView m (e 0) (P.simulate x (e 0) s)) :=
  Protocol.simTrace_of_simKey_none (fun _ _ => rfl) look e

theorem guessView_toProtocol (look : (P.toProtocol M).Key → Option P.Ch) (x : P.Stmt)
    (w : P.Wit) (m : M) (r : P.Rand) (e : Fin 1 → P.Ch) (i : Fin 1) :
    (P.toProtocol M).guessView look x w m r e i = ([], [], none) := by
  unfold Protocol.guessView
  split
  · rfl
  · next h =>
    rw [vals_toProtocol, trace_toProtocol]
    rw [vals_toProtocol] at h
    have h' : P.accept (P.respond x w r (e 0)) = false := by
      simp only [toProtocol, Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      exact h.1
    simp [transcriptView, h']

/-- Statistical HVZK of `P` at a pair gives statistical HVZK of its protocol on
messages `M` at that pair. -/
theorem statHVZKAt_toProtocol {x : P.Stmt} {w : P.Wit} {δ : ℝ≥0∞} (h : P.StatHVZKAt x w δ) :
    (P.toProtocol M).StatHVZKAt x w δ := by
  intro m look g hg
  simp only [vals_toProtocol, trace_toProtocol, simTrace_toProtocol]
  have hstep : ∀ e : Fin 1 → P.Ch, ∑' r, PMF.uniformOfFintype P.Rand r *
      (if (P.toProtocol M).hidFresh look x w m r e then
        g ([], P.transcriptView m (e 0) (P.commit x w r, P.respond x w r (e 0))) else 0) ≤
      ∑' s, PMF.uniformOfFintype P.SimRand s *
        g ([], P.transcriptView m (e 0) (P.simulate x (e 0) s)) + δ := fun e => by
    have hb : P.RejectBlind (fun az => g ([], P.transcriptView m (e 0) az)) := by
      intro a a' z hz
      simp [transcriptView, hz]
    refine (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _).trans
      (h (e 0) (fun az => g ([], P.transcriptView m (e 0) az)) (fun _ => hg _) hb)
    split_ifs
    · exact le_rfl
    · exact zero_le
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin 1 → P.Ch) e * (∑' s, PMF.uniformOfFintype P.SimRand s *
          g ([], P.transcriptView m (e 0) (P.simulate x (e 0) s)) + δ) :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right (hstep e) _
    _ = _ := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The commitment bound of `P` at a pair is a key bound of its protocol on
messages `M` at that pair. -/
theorem keyBoundAt_toProtocol {x : P.Stmt} {w : P.Wit} {γ : ℝ≥0∞} (h : P.CommitBoundAt x w γ) :
    (P.toProtocol M).KeyBoundAt x w γ := by
  intro m look Q
  simp only [guessView_toProtocol, vals_toProtocol, Fin.sum_univ_one]
  set q := Q ([], [], none)
  have hr : ∑' r, PMF.uniformOfFintype P.Rand r * q (P.commit x w r, m) ≤ γ := by
    rw [← tsum_map_mul' (PMF.uniformOfFintype P.Rand) (fun r => (P.commit x w r, m)) q]
    calc ∑' y, ((PMF.uniformOfFintype P.Rand).map fun r => (P.commit x w r, m)) y * q y
        ≤ ∑' y, γ * q y := by
          refine ENNReal.tsum_le_tsum fun y => mul_le_mul_left ?_ _
          rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
          exact (MeasureTheory.measure_mono fun r hr => congrArg Prod.fst hr).trans (h y.1)
      _ = γ := by rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin 1 → P.Ch) e *
        ∑' r, PMF.uniformOfFintype P.Rand r * q (P.commit x w r, m) := by
        refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _) _
        split_ifs
        · exact le_rfl
        · exact zero_le
    _ ≤ ∑' e, PMF.uniformOfFintype (Fin 1 → P.Ch) e * γ :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right hr _
    _ = γ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Sigma

/-! ## The hop -/

section Stat

variable {G : Protocol}

/-- The test `g` on outcomes with the flag cleared, `0` on the others. -/
def offFlag {β σ : Type} (g : β × (σ × Bool) → ℝ≥0∞) (y : β × (σ × Bool)) : ℝ≥0∞ :=
  if y.2.2 = true then 0 else g y

theorem offFlag_le {β σ : Type} (g : β × (σ × Bool) → ℝ≥0∞) (y : β × (σ × Bool)) :
    offFlag g y ≤ g y := by
  unfold offFlag; split_ifs <;> simp

/-- The outcome `y` with the hidden entries replaced by `l`. -/
def setRej {β : Type} (l : List (G.Key × G.Ch)) (y : β × (G.Tables × Bool)) :
    β × (G.Tables × Bool) :=
  (y.1, ({ y.2.1 with rej := l }, y.2.2))

/-- The test `g` does not read the hidden entries. -/
def RejInsensitive {β : Type} (g : β × (G.Tables × Bool) → ℝ≥0∞) : Prop :=
  ∀ y l, g (setRej l y) = g y

/-- The test on traces that one signing step induces from the test `F` on its
outcomes: the test of the outcome of `traceOut` with the flag cleared. -/
def signTest (F : G.Answer × (G.Tables × Bool) → ℝ≥0∞) (t : G.Tables) (b : Bool)
    (m : G.Msg) (tr : G.Trace) : ℝ≥0∞ :=
  offFlag F (traceOut t b m tr)

theorem signTest_le_one (F : G.Answer × (G.Tables × Bool) → ℝ≥0∞) (hF : ∀ y, F y ≤ 1)
    (t : G.Tables) (b : Bool) (m : G.Msg) (tr : G.Trace) : signTest F t b m tr ≤ 1 :=
  (offFlag_le F _).trans (hF _)

/-- The programmed public entries of an attempt are at distinct points. -/
theorem nodup_pubEntries (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand)
    (v : Fin G.μ → G.Ch) : ((G.pubEntries x w m r v).map Prod.fst).Nodup := by
  simp only [Protocol.pubEntries, Protocol.entries, List.map_map]
  exact ((List.nodup_finRange _).filter _).map fun i j h => G.key_inj x w m r v i j h

/-- The real signing answer from `(e, r)` with the flag cleared is bounded by the
test of the trace of the attempt against the visible oracle when its hidden points
are undefined there, and by `0` otherwise. -/
theorem offFlag_realSignOut_le (F : G.Answer × (G.Tables × Bool) → ℝ≥0∞)
    (hF : RejInsensitive F) (x : G.Stmt) (w : G.Wit) (t : G.Tables) (b : Bool) (m : G.Msg)
    (e : Fin G.μ → G.Ch) (r : G.Rand) :
    offFlag F (realSignOut x w t b m e r) ≤
      if G.hidFresh t.lookup x w m r (G.vals t.lookup x w m r e) then
        signTest F t b m (G.trace x w m r (G.vals t.lookup x w m r e)) else 0 := by
  cases hfl : (realSignOut x w t b m e r).2.2
  swap
  · simp [offFlag, hfl]
  obtain ⟨rfl, h1, h2⟩ := fresh_of_realSignOut x w t b m e r hfl
  set v := G.vals t.lookup x w m r e with hv
  have hfr : G.hidFresh t.lookup x w m r v = true := List.all_eq_true.mpr fun i _ => by
    cases hp : G.pub x w m r v i
    · have hf : G.flagging x w m r v i = true := by simp [Protocol.flagging, hp]
      simp [Protocol.lookup_eq_none_of_lookupAll (h1 i hf)]
    · simp
  rw [if_pos hfr, realSignOut_of_fresh x w t false m e r h1 h2]
  have hpe : ∀ p ∈ G.pubEntries x w m r v, (hashAll t (G.evEntries x w m r v)).lookup p.1 = none :=
    fun p hp => by
      obtain ⟨i, hi, rfl⟩ := Protocol.mem_entries hp
      have hev : G.ev i = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hi
        exact hi.1
      rw [Protocol.lookup_hashAll_of_notMem _ _ (Protocol.key_notMem_evEntries hev)]
      exact Protocol.lookup_eq_none_of_lookupAll (h1 i (by simp [Protocol.flagging, hev]))
  unfold signTest traceOut programOut
  rw [show (G.trace x w m r v).2.1 = G.pubEntries x w m r v from rfl,
    show (G.trace x w m r v).1 = G.evEntries x w m r v from rfl,
    programAll_of_fresh _ false _ hpe (nodup_pubEntries x w m r v)]
  unfold offFlag
  rw [← hF _ t.rej]
  exact le_rfl

/-- **One transition.** For a pair with statistical HVZK distance `δ` and a test
`F` with values in `[0, 1]` that does not read the hidden entries, on the outcomes
with the flag cleared a test of one real transition is at most the same test of one
simulated transition, plus `δ` for a signing query. -/
theorem realStep_le_simStep {δ : ℝ≥0∞} (xw : G.Stmt × G.Wit) (hZK : G.StatHVZKAt xw.1 xw.2 δ)
    (s : G.Tables × Bool) (d : G.Query)
    (F : G.Answer × (G.Tables × Bool) → ℝ≥0∞) (hF : ∀ y, F y ≤ 1) (hFr : RejInsensitive F) :
    ∑' o, toOracle (realStep xw) s d o * offFlag F o ≤
      ∑' o, toOracle (simStep xw.1) s d o * F o + (if d.isRight then δ else 0) := by
  obtain ⟨t, b⟩ := s
  cases d with
  | inl k =>
    simp only [Sum.isRight_inl, Bool.false_eq_true, if_false, add_zero]
    simp only [toOracle, realStep, simStep, realHashStep, hashStep]
    cases t.lookup k with
    | some e => exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offFlag_le F o) _
    | none =>
      cases lookupIn t.rej k with
      | some e =>
        simp only [Step.toPMF]
        rw [tsum_pure_mul]
        simp [offFlag]
      | none => exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offFlag_le F o) _
  | inr m =>
    simp only [toOracle, realStep, simStep, Step.toPMF, sampleVec, tsum_bind_mul,
      tsum_map_mul', Sum.isRight_inr, if_true]
    calc ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformOfFintype G.Rand r *
          offFlag F (realSignOut xw.1 xw.2 t b m e r)
        ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformOfFintype G.Rand r *
            (if G.hidFresh t.lookup xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) then
              signTest F t b m (G.trace xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e))
              else 0) :=
          ENNReal.tsum_le_tsum fun e => mul_le_mul_right (ENNReal.tsum_le_tsum fun r =>
            mul_le_mul_right (offFlag_realSignOut_le F hFr xw.1 xw.2 t b m e r) _) _
      _ ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' z,
            PMF.uniformOfFintype G.SimRand z * signTest F t b m (G.simTrace t.lookup xw.1 m e z) +
            δ := hZK m t.lookup (signTest F t b m) (signTest_le_one F hF t b m)
      _ ≤ _ := by
          gcongr with e z
          exact offFlag_le F _

variable {α : Type}

/-- A real run started with the flag set gives every test of `offFlag` the value
`0`. -/
theorem run_real_offFlag_true (xw : G.Stmt × G.Wit) (A : OracleAdv G.Query G.Answer α)
    (t : G.Tables) (g : α × (G.Tables × Bool) → ℝ≥0∞) :
    ∑' y, OracleAdv.run (toOracle (realStep xw)) A (t, true) y * offFlag g y = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun y => ?_
  obtain ⟨a, t', fl⟩ := y
  cases fl with
  | true => simp [offFlag]
  | false =>
    rw [OracleAdv.run_flag_apply_false_of_true _ (fun t d r t' =>
      (PMF.apply_eq_zero_iff _ _).mpr fun hx => Bool.noConfusion (realStep_flag xw t d _ hx)),
      zero_mul]

/-- Programming entries does not read the hidden entries and keeps them. -/
theorem programAll_setRej (l : List (G.Key × G.Ch)) (t : G.Tables) (b : Bool)
    (v : List (G.Key × G.Ch)) :
    programAll { t with rej := l } b v =
      ({ (programAll t b v).1 with rej := l }, (programAll t b v).2) := by
  induction v generalizing t b with
  | nil => rfl
  | cons p v ih =>
    unfold programAll
    rw [show ({ t with rej := l } : G.Tables).lookup p.1 = t.lookup p.1 from rfl]
    cases t.lookup p.1 with
    | some _ => exact ih t true
    | none => exact ih { t with prog := t.prog ++ [p] } b

/-- Answering a trace does not read the hidden entries and keeps them. -/
theorem traceOut_setRej (l : List (G.Key × G.Ch)) (t : G.Tables) (b : Bool) (m : G.Msg)
    (tr : G.Trace) :
    traceOut { t with rej := l } b m tr =
      Prod.map id (fun s' => ({ s'.1 with rej := l }, s'.2)) (traceOut t b m tr) := by
  unfold traceOut programOut
  rw [show hashAll { t with rej := l } tr.1 = { hashAll t tr.1 with rej := l } from rfl,
    programAll_setRej]
  rfl

/-- A simulated transition does not read the hidden entries and keeps them. -/
theorem simStep_setRej (x₀ : G.Stmt) (l : List (G.Key × G.Ch)) (s : G.Tables × Bool)
    (d : G.Query) :
    (toOracle (simStep x₀) s d).map (Prod.map id fun s' => ({ s'.1 with rej := l }, s'.2)) =
      toOracle (simStep x₀) ({ s.1 with rej := l }, s.2) d := by
  obtain ⟨t, b⟩ := s
  cases d with
  | inl k =>
    simp only [toOracle, simStep, hashStep]
    rw [show ({ t with rej := l } : G.Tables).lookup k = t.lookup k from rfl]
    cases t.lookup k with
    | some e => simp only [Step.toPMF, PMF.pure_map]; rfl
    | none => simp only [Step.toPMF, PMF.map_comp]; rfl
  | inr m =>
    simp only [toOracle, simStep, Step.toPMF, sampleVec, PMF.map_bind, PMF.map_comp]
    refine congrArg _ (funext fun e => congrArg _ (funext fun z => ?_))
    simp only [Function.comp_apply, simSignOut]
    rw [traceOut_setRej l t]
    rfl

/-- The expectation of a test under a simulated run does not depend on the hidden
entries when the test does not read them. -/
theorem tsum_run_sim_setRej (x₀ : G.Stmt) (A : OracleAdv G.Query G.Answer α)
    (g : α × (G.Tables × Bool) → ℝ≥0∞) (hg : RejInsensitive g) (s : G.Tables × Bool)
    (l : List (G.Key × G.Ch)) :
    ∑' y, OracleAdv.run (toOracle (simStep x₀)) A ({ s.1 with rej := l }, s.2) y * g y =
      ∑' y, OracleAdv.run (toOracle (simStep x₀)) A s y * g y := by
  have hm := OracleAdv.run_map_state _ _
    (fun s' : G.Tables × Bool => ({ s'.1 with rej := l }, s'.2)) (simStep_setRej x₀ l) A s
  refine (congrArg (fun p : PMF (α × (G.Tables × Bool)) => ∑' y, p y * g y) hm).symm.trans ?_
  dsimp only
  rw [tsum_map_mul']
  exact tsum_congr fun y => congrArg _ (hg y l)

/-- A query bound on `query d k` bounds every continuation: one hash query or
one signing query fewer. -/
theorem isQueryBound₂_query_cases {D₁ D₂ R : Type} (d : D₁ ⊕ D₂) (k : R → OracleAdv (D₁ ⊕ D₂) R α)
    (h q : ℕ) (hA : IsQueryBound₂ (.query d k) h q) :
    ∃ h' q', q' + (if d.isRight then 1 else 0) = q ∧ ∀ r, IsQueryBound₂ (k r) h' q' := by
  cases d with
  | inl key =>
    cases h with
    | zero => exact hA.elim
    | succ h => exact ⟨h, q, rfl, hA⟩
  | inr m =>
    cases q with
    | zero => exact hA.elim
    | succ q => exact ⟨h, q, rfl, hA⟩

theorem ite_add_mul_eq (b : Bool) (q' : ℕ) (δ : ℝ≥0∞) :
    (if b then δ else 0) + (q' : ℝ≥0∞) * δ = ((q' + if b then 1 else 0 : ℕ) : ℝ≥0∞) * δ := by
  cases b <;> simp [add_mul, add_comm]

/-- **Statistical hop for runs.** For a pair with statistical HVZK distance `δ`
and a run with at most `h` hash and `q` signing queries, a test `g` with values in
`[0, 1]` that does not read the hidden entries, on the real outcomes with the flag
cleared, is at most the test on the simulated run plus `q·δ`. -/
theorem run_real_le_sim {δ : ℝ≥0∞} (xw : G.Stmt × G.Wit) (hZK : G.StatHVZKAt xw.1 xw.2 δ)
    (A : OracleAdv G.Query G.Answer α) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) (s : G.Tables × Bool)
    (g : α × (G.Tables × Bool) → ℝ≥0∞) (hg : ∀ y, g y ≤ 1) (hgr : RejInsensitive g) :
    ∑' y, OracleAdv.run (toOracle (realStep xw)) A s y * offFlag g y ≤
      ∑' y, OracleAdv.run (toOracle (simStep xw.1)) A s y * g y + q * δ := by
  induction A generalizing h q s with
  | ret a =>
    simp only [OracleAdv.run_ret, tsum_pure_mul]
    exact (offFlag_le g _).trans le_self_add
  | rand p k ih =>
    simp only [OracleAdv.run_rand, tsum_bind_mul]
    calc _ ≤ ∑' b, p b * (∑' y, OracleAdv.run (toOracle (simStep xw.1)) (k b) s y * g y +
            q * δ) := ENNReal.tsum_le_tsum fun b => mul_le_mul_right (ih b h q (hA b) s) _
      _ = _ := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    simp only [OracleAdv.run_query, tsum_bind_mul]
    -- the value of the rest of the simulated run, a test with values in `[0, 1]`
    set Y : G.Answer × (G.Tables × Bool) → ℝ≥0∞ := fun o =>
      ∑' y, OracleAdv.run (toOracle (simStep xw.1)) (k o.1) o.2 y * g y with hY
    have hY1 : ∀ o, Y o ≤ 1 := fun o =>
      (ENNReal.tsum_le_tsum fun y => mul_le_of_le_one_right' (hg y)).trans
        (le_of_eq (PMF.tsum_coe _))
    have hYr : RejInsensitive Y := fun o l =>
      tsum_run_sim_setRej xw.1 (k o.1) g hgr o.2 l
    obtain ⟨h', q', hq', hk⟩ := isQueryBound₂_query_cases d k h q hA
    have hpt : ∀ o : G.Answer × (G.Tables × Bool),
        ∑' y, OracleAdv.run (toOracle (realStep xw)) (k o.1) o.2 y * offFlag g y ≤
          offFlag Y o + q' * δ := by
      rintro ⟨r, t, fl⟩
      cases fl with
      | true =>
        rw [run_real_offFlag_true]
        exact zero_le
      | false => exact ih r h' q' (hk r) (t, false)
    calc _ ≤ ∑' o, toOracle (realStep xw) s d o * (offFlag Y o + q' * δ) :=
          ENNReal.tsum_le_tsum fun o => mul_le_mul_right (hpt o) _
      _ = ∑' o, toOracle (realStep xw) s d o * offFlag Y o + q' * δ := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ ≤ ∑' o, toOracle (simStep xw.1) s d o * Y o + (if d.isRight then δ else 0) + q' * δ :=
          add_le_add (realStep_le_simStep xw hZK s d Y hY1 hYr) le_rfl
      _ = _ := by rw [add_assoc, ← hq', ite_add_mul_eq]

/-- The probability of an event as the expectation of its indicator. -/
theorem toOuterMeasure_eq_tsum_ite {β : Type} (p : PMF β) (E : β → Bool) :
    p.toOuterMeasure {y | E y = true} = ∑' y, p y * (if E y = true then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun y => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, mul_ite, mul_one, mul_zero]

/-- Winning in the real run has probability at most winning in the simulated run,
plus `q·δ`, plus the probability that the real run sets the flag. -/
theorem run_real_wins_le_stat {δ : ℝ≥0∞} (xw : G.Stmt × G.Wit) (hZK : G.StatHVZKAt xw.1 xw.2 δ)
    (A : OracleAdv G.Query G.Answer G.Forgery) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) (s : G.Tables × Bool) (x : G.Stmt) :
    (OracleAdv.run (toOracle (realStep xw)) A s).toOuterMeasure {y | wins x y = true} ≤
      (OracleAdv.run (toOracle (simStep xw.1)) A s).toOuterMeasure {y | wins x y = true} +
        q * δ +
      (OracleAdv.run (toOracle (realStep xw)) A s).toOuterMeasure {y | y.2.2 = true} := by
  set g : G.Forgery × (G.Tables × Bool) → ℝ≥0∞ := fun y => if wins x y = true then 1 else 0
  have hg : ∀ y, g y ≤ 1 := fun y => by simp only [g]; split_ifs <;> simp
  have hgr : RejInsensitive g := fun _ _ => rfl
  rw [toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite]
  calc _ ≤ ∑' y, OracleAdv.run (toOracle (realStep xw)) A s y *
          (offFlag g y + if y.2.2 = true then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun y => mul_le_mul_right ?_ _
        simp only [offFlag, g]
        split_ifs <;> simp
    _ = ∑' y, OracleAdv.run (toOracle (realStep xw)) A s y * offFlag g y +
          ∑' y, OracleAdv.run (toOracle (realStep xw)) A s y *
            (if y.2.2 = true then 1 else 0) := by
        simp only [mul_add]
        rw [ENNReal.tsum_add]
    _ ≤ _ := add_le_add (run_real_le_sim xw hZK A h q hA s g hg hgr) le_rfl

/-- **Signing-oracle simulation with distances depending on the pair.** For a
protocol whose generated pairs `(x, w)` have statistical HVZK distance `δ (x, w)`
and key bound `Γ (x, w)`, and every adversary with at most `qH` hash and `qS`
signing queries, the EUF-CMA advantage is at most the advantage in the game whose
signing oracle is simulated from the statement by programming the random oracle,
plus the expectation over the generator of
`qS·δ(x, w) + qS·(qH + V + μ·qS)·Γ(x, w)`. -/
theorem Protocol.eufcmaAdvantage_le_simAdvantage_perKey {δ Γ : G.Stmt × G.Wit → ℝ≥0∞}
    (hZK : ∀ xw ∈ G.gen.support, G.StatHVZKAt xw.1 xw.2 (δ xw))
    (hΓ : ∀ xw ∈ G.gen.support, G.KeyBoundAt xw.1 xw.2 (Γ xw)) {qH qS : ℕ}
    (A : G.Adversary qH qS) :
    eufcmaAdvantage A ≤ simAdvantage A +
      ∑' xw, G.gen xw * (qS * δ xw + ((qS * (qH + G.V + G.μ * qS) : ℕ) : ℝ≥0∞) * Γ xw) := by
  unfold eufcmaAdvantage simAdvantage eufcmaGame simGame
  rw [prTrue_gameDist, prTrue_gameDist, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun xw => ?_
  rw [← mul_add]
  by_cases hxw : xw ∈ G.gen.support
  · have hB := isQueryBound₂_withVerify xw.1 _ qH qS (A.isQueryBound xw.1)
    refine mul_le_mul_right ?_ _
    refine (run_real_wins_le_stat xw (hZK xw hxw) _ (qH + G.V) qS hB _ _).trans ?_
    rw [add_assoc]
    refine add_le_add le_rfl (add_le_add le_rfl ?_)
    refine (run_real_flag_le xw (hΓ xw hxw) _ (qH + G.V) qS hB Protocol.Tables.empty rfl).trans
      (le_of_eq ?_)
    simp [Protocol.Tables.empty]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hxw]

/-- **Signing-oracle simulation at the distances of the pairs.** For every protocol
and every adversary with at most `qH` hash and `qS` signing queries, the EUF-CMA
advantage is at most the simulated-game advantage plus the expectation over the
generator of `qS·hvzkDistAt x w + qS·(qH + V + μ·qS)·keyDistAt x w`. -/
theorem Protocol.eufcmaAdvantage_le_simAdvantage_dist {qH qS : ℕ} (A : G.Adversary qH qS) :
    eufcmaAdvantage A ≤ simAdvantage A +
      ∑' xw, G.gen xw * (qS * G.hvzkDistAt xw.1 xw.2 +
        ((qS * (qH + G.V + G.μ * qS) : ℕ) : ℝ≥0∞) * G.keyDistAt xw.1 xw.2) :=
  Protocol.eufcmaAdvantage_le_simAdvantage_perKey (δ := fun xw => G.hvzkDistAt xw.1 xw.2)
    (Γ := fun xw => G.keyDistAt xw.1 xw.2)
    (fun xw _ => G.statHVZKAt_hvzkDistAt xw.1 xw.2)
    (fun xw _ => G.keyBoundAt_keyDistAt xw.1 xw.2) A

/-- **Signing-oracle simulation with statistical HVZK.** For a protocol with
statistical HVZK distance `δ` and key bound `Γ`, and every adversary with at most
`qH` hash and `qS` signing queries, the EUF-CMA advantage is at most the advantage
in the game whose signing oracle is simulated from the statement by programming the
random oracle, plus `qS·δ + qS·(qH + V + μ·qS)·Γ`. -/
theorem Protocol.eufcmaAdvantage_le_simAdvantage_stat {δ : ℝ≥0∞} (hZK : G.StatHVZK δ)
    {Γ : ℝ≥0∞} (hΓ : G.KeyBound Γ) {qH qS : ℕ} (A : G.Adversary qH qS) :
    eufcmaAdvantage A ≤
      simAdvantage A + (qS * δ + ((qS * (qH + G.V + G.μ * qS) : ℕ) : ℝ≥0∞) * Γ) := by
  refine (Protocol.eufcmaAdvantage_le_simAdvantage_perKey (δ := fun _ => δ) (Γ := fun _ => Γ)
    (fun xw hxw => hZK xw.1 xw.2 hxw) (fun xw hxw => hΓ xw.1 xw.2 hxw) A).trans (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Stat

/-! ## Σ-protocols: the hop -/

section SigmaStat

variable {P : Sigma} {M : Type} [DecidableEq M]

/-- **Signing-oracle simulation with distances depending on the pair.** For a
Σ-protocol whose generated pairs `(x, w)` have statistical HVZK distance
`δ (x, w)` and commitment bound `γ (x, w)`, and every adversary with at most `qH`
hash and `qS` signing queries, the EUF-CMA advantage is at most the advantage in
the game whose signing oracle is simulated from the statement by programming the
random oracle, plus the expectation over the generator of
`qS·δ(x, w) + qS·(qH + 1 + qS)·γ(x, w)`. -/
theorem eufcmaAdvantage_le_simAdvantage_perKey {δ γ : P.Stmt × P.Wit → ℝ≥0∞}
    (hZK : ∀ xw ∈ P.gen.support, P.StatHVZKAt xw.1 xw.2 (δ xw))
    (hγ : ∀ xw ∈ P.gen.support, P.CommitBoundAt xw.1 xw.2 (γ xw)) {qH qS : ℕ}
    (A : Adversary P M qH qS) :
    eufcmaAdvantage A ≤ simAdvantage A +
      ∑' xw, P.gen xw * (qS * δ xw + ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * γ xw) := by
  have h := Protocol.eufcmaAdvantage_le_simAdvantage_perKey (G := P.toProtocol M) (δ := δ)
    (Γ := γ) (fun xw hxw => P.statHVZKAt_toProtocol (hZK xw hxw))
    (fun xw hxw => P.keyBoundAt_toProtocol (hγ xw hxw)) A
  simp only [one_mul] at h
  exact h

/-- **Signing-oracle simulation at the distances of the pairs.** For every
Σ-protocol and every adversary with at most `qH` hash and `qS` signing queries,
the EUF-CMA advantage is at most the simulated-game advantage plus the
expectation over the generator of
`qS·hvzkDistAt x w + qS·(qH + 1 + qS)·commitDistAt x w`. -/
theorem eufcmaAdvantage_le_simAdvantage_dist {qH qS : ℕ} (A : Adversary P M qH qS) :
    eufcmaAdvantage A ≤ simAdvantage A +
      ∑' xw, P.gen xw * (qS * P.hvzkDistAt xw.1 xw.2 +
        ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * P.commitDistAt xw.1 xw.2) :=
  eufcmaAdvantage_le_simAdvantage_perKey (δ := fun xw => P.hvzkDistAt xw.1 xw.2)
    (γ := fun xw => P.commitDistAt xw.1 xw.2)
    (fun xw _ => P.statHVZKAt_hvzkDistAt xw.1 xw.2)
    (fun xw _ => P.commitBoundAt_commitDistAt xw.1 xw.2) A

/-- **Signing-oracle simulation with statistical HVZK.** For a Σ-protocol with
statistical HVZK distance `δ` and commitment bound `γ`, and every adversary with
at most `qH` hash and `qS` signing queries, the EUF-CMA advantage is at most the
advantage in the game whose signing oracle is simulated from the statement by
programming the random oracle, plus `qS·δ + qS·(qH + 1 + qS)·γ`. -/
theorem eufcmaAdvantage_le_simAdvantage_stat {δ : ℝ≥0∞} (hZK : P.StatHVZK δ) {γ : ℝ≥0∞}
    (hγ : P.CommitBound γ) {qH qS : ℕ} (A : Adversary P M qH qS) :
    eufcmaAdvantage A ≤
      simAdvantage A + (qS * δ + ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * γ) := by
  refine (eufcmaAdvantage_le_simAdvantage_perKey (δ := fun _ => δ) (γ := fun _ => γ)
    (fun xw hxw => hZK xw.1 xw.2 hxw) (fun xw hxw => hγ xw.1 xw.2 hxw) A).trans (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Signing-oracle simulation.** For a Σ-protocol with perfect HVZK and
commitment bound `γ`, and every adversary with at most `qH` hash queries and `qS`
signing queries, the EUF-CMA advantage is at most the advantage in the game whose
signing oracle is simulated from the statement by programming the random oracle,
plus `qS·(qH + 1 + qS)·γ`. -/
theorem eufcmaAdvantage_le_simAdvantage (hZK : P.PerfectHVZK) {γ : ℝ≥0∞}
    (hγ : P.CommitBound γ) {qH qS : ℕ} (A : Adversary P M qH qS) :
    eufcmaAdvantage A ≤ simAdvantage A + ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * γ := by
  simpa using eufcmaAdvantage_le_simAdvantage_stat hZK.statHVZK hγ A

end SigmaStat

/-! ## Distances at one generated pair -/

namespace Sigma

variable (P : Sigma)

/-- The HVZK distance of `P` at `(x, w)` on the transcripts whose response
satisfies `E`: the supremum, over challenges and tests with values in `[0, 1]`
that do not read the commitment of a rejected transcript, of the expectation of
the test restricted to those transcripts on the honest side minus the same
expectation on the simulated side. -/
noncomputable def hvzkDistOn (E : P.Resp → Bool) (x : P.Stmt) (w : P.Wit) : ℝ≥0∞ :=
  ⨆ (e : P.Ch) (g : P.Com × P.Resp → ℝ≥0∞) (_ : ∀ y, g y ≤ 1) (_ : P.RejectBlind g),
    (∑' r, PMF.uniformOfFintype P.Rand r *
        (if E (P.respond x w r e) then g (P.commit x w r, P.respond x w r e) else 0)) -
      ∑' s, PMF.uniformOfFintype P.SimRand s *
        (if E (P.simulate x e s).2 then g (P.simulate x e s) else 0)

/-- **Splitting the HVZK distance by an event on the response.** The distance at
`(x, w)` is at most the distance on the transcripts whose response satisfies `E`
plus the distance on the others. -/
theorem hvzkDistAt_le_on_add_on (E : P.Resp → Bool) (x : P.Stmt) (w : P.Wit) :
    P.hvzkDistAt x w ≤ P.hvzkDistOn E x w + P.hvzkDistOn (fun z => !E z) x w := by
  refine iSup_le fun e => iSup_le fun g => iSup_le fun hg => iSup_le fun hb => ?_
  have hsplit : ∀ {β : Type} [Fintype β] [Nonempty β] (F : β → P.Com × P.Resp),
      ∑' b, PMF.uniformOfFintype β b * g (F b) =
        (∑' b, PMF.uniformOfFintype β b * (if E (F b).2 then g (F b) else 0)) +
          ∑' b, PMF.uniformOfFintype β b * (if (!E (F b).2) then g (F b) else 0) := by
    intro β _ _ F
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun b => ?_
    rw [← mul_add]
    cases E (F b).2 <;> simp
  rw [hsplit (fun r => (P.commit x w r, P.respond x w r e)), hsplit (P.simulate x e)]
  refine add_tsub_add_le_tsub_add_tsub.trans (add_le_add ?_ ?_)
  · exact le_iSup_of_le e <| le_iSup_of_le g <| le_iSup_of_le hg <| le_iSup_of_le hb le_rfl
  · exact le_iSup_of_le e <| le_iSup_of_le g <| le_iSup_of_le hg <| le_iSup_of_le hb le_rfl

/-- **Matching transcripts have distance zero.** If, for every challenge, every
transcript whose response satisfies `E` has the same probability on the honest
and the simulated side, the distance on those transcripts is `0`. -/
theorem hvzkDistOn_eq_zero_of_eq (E : P.Resp → Bool) (x : P.Stmt) (w : P.Wit)
    (h : ∀ e (t : P.Com × P.Resp), E t.2 = true →
      (PMF.uniformOfFintype P.Rand).map (fun r => (P.commit x w r, P.respond x w r e)) t =
        (PMF.uniformOfFintype P.SimRand).map (P.simulate x e) t) :
    P.hvzkDistOn E x w = 0 := by
  refine le_antisymm (iSup_le fun e => iSup_le fun g => iSup_le fun _ => iSup_le fun _ => ?_)
    zero_le
  rw [tsub_le_iff_right, zero_add]
  have key := tsum_map_mul' (PMF.uniformOfFintype P.Rand)
    (fun r => (P.commit x w r, P.respond x w r e)) (fun t => if E t.2 then g t else 0)
  have key' := tsum_map_mul' (PMF.uniformOfFintype P.SimRand) (P.simulate x e)
    (fun t => if E t.2 then g t else 0)
  simp only at key key'
  rw [← key, ← key']
  refine le_of_eq (tsum_congr fun t => ?_)
  by_cases ht : E t.2 = true
  · rw [h e t ht]
  · simp [ht]

/-- **Rejected transcripts have distance zero when accepted ones match.** For a
Σ-protocol whose rejected responses are all equal to `z₀`, if at `(x, w)` every
accepted transcript has the same probability on the honest and the simulated
side, the HVZK distance on the rejected transcripts is `0`: a test that does not
read the commitment of a rejected transcript sees only the probability of
rejection, which is one minus the probability of acceptance on both sides. -/
theorem hvzkDistOn_reject_eq_zero (x : P.Stmt) (w : P.Wit)
    (z₀ : P.Resp) (hz₀ : ∀ z, P.accept z = false → z = z₀)
    (h : ∀ e (t : P.Com × P.Resp), P.accept t.2 = true →
      (PMF.uniformOfFintype P.Rand).map (fun r => (P.commit x w r, P.respond x w r e)) t =
        (PMF.uniformOfFintype P.SimRand).map (P.simulate x e) t) :
    P.hvzkDistOn (fun z => !P.accept z) x w = 0 := by
  refine le_antisymm (iSup_le fun e => iSup_le fun g => iSup_le fun _ => iSup_le fun hb => ?_)
    zero_le
  rw [tsub_le_iff_right, zero_add]
  set a₀ : P.Com := (P.simulate x e (Classical.arbitrary _)).1
  set c : ℝ≥0∞ := g (a₀, z₀)
  have hg : ∀ t : P.Com × P.Resp, (if (!P.accept t.2) = true then g t else 0) =
      c * (if P.accept t.2 = true then 0 else 1) := by
    rintro ⟨a, z⟩
    cases hz : P.accept z
    · obtain rfl := hz₀ z hz
      simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false, mul_one]
      exact hb a a₀ _ hz
    · simp
  -- the probability of acceptance under the image of `p` by `F`
  have hacc : ∀ {β : Type} [Fintype β] [Nonempty β] (F : β → P.Com × P.Resp),
      ∑' b, PMF.uniformOfFintype β b * (if P.accept (F b).2 = true then 0 else 1) =
        1 - ∑' t, ((PMF.uniformOfFintype β).map F) t *
          (if P.accept t.2 = true then 1 else 0) := by
    intro β _ _ F
    rw [tsum_map_mul']
    refine ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top ?_) ?_
    · exact (ENNReal.tsum_le_tsum fun b => mul_le_of_le_one_right' (by split_ifs <;> simp)).trans
        (le_of_eq (PMF.tsum_coe _))
    · rw [← ENNReal.tsum_add]
      refine (tsum_congr fun b => ?_).trans (PMF.tsum_coe (PMF.uniformOfFintype β))
      rw [← mul_add]
      split_ifs <;> simp
  have hA : ∑' t, ((PMF.uniformOfFintype P.Rand).map
        (fun r => (P.commit x w r, P.respond x w r e))) t *
        (if P.accept t.2 = true then 1 else 0) =
      ∑' t, ((PMF.uniformOfFintype P.SimRand).map (P.simulate x e)) t *
        (if P.accept t.2 = true then 1 else 0) := by
    refine tsum_congr fun t => ?_
    by_cases ht : P.accept t.2 = true
    · rw [h e t ht]
    · simp [ht]
  have h1 := hacc (fun r => (P.commit x w r, P.respond x w r e))
  have h2 := hacc (P.simulate x e)
  simp only at h1 h2
  refine le_of_eq ?_
  calc (∑' r, PMF.uniformOfFintype P.Rand r * (if (!P.accept (P.respond x w r e)) = true then
          g (P.commit x w r, P.respond x w r e) else 0))
      = c * ∑' r, PMF.uniformOfFintype P.Rand r *
          (if P.accept (P.respond x w r e) = true then 0 else 1) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun r => (congrArg (PMF.uniformOfFintype P.Rand r * ·)
          (hg (P.commit x w r, P.respond x w r e))).trans (mul_left_comm _ _ _)
    _ = c * ∑' s, PMF.uniformOfFintype P.SimRand s *
          (if P.accept (P.simulate x e s).2 = true then 0 else 1) := by
        rw [h1, h2, hA]
    _ = _ := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun s => ((congrArg (PMF.uniformOfFintype P.SimRand s * ·)
          (hg (P.simulate x e s))).trans (mul_left_comm _ _ _)).symm

/-- **The HVZK distance split by an event on the response.** `hvzkDist` is at
most the supremum, over generated pairs, of the distance on the transcripts whose
response satisfies `E` plus the distance on the others. -/
theorem hvzkDist_le_iSup_on_add_on (E : P.Resp → Bool) :
    P.hvzkDist ≤ ⨆ (x : P.Stmt) (w : P.Wit) (_ : (x, w) ∈ P.gen.support),
      (P.hvzkDistOn E x w + P.hvzkDistOn (fun z => !E z) x w) :=
  iSup_le fun x => iSup_le fun w => iSup_le fun hxw =>
    (P.hvzkDistAt_le_on_add_on E x w).trans
      (le_iSup_of_le x <| le_iSup_of_le w <| le_iSup_of_le hxw le_rfl)

end Sigma

end CatCrypt.Crypto.FiatShamirROM

