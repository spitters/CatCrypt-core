/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.StatHVZK
public import CatCryptCore.Crypto.HybridArgument
public import CatCryptCore.ForMathlib.PMFSupport

/-!
# Fiat–Shamir in the random-oracle model: signers that sample the challenges first

A game `attGame D` for a protocol `G : Protocol` whose signing oracle on `m`
samples the values `e` of the entries first and then a signing attempt `a` from the
sampler `D (x, w) m e`. An attempt (`Protocol.Attempt`) gives the points of the
entries and their public marks as functions of the values, and the answer; its
values against the oracle are those of `Protocol.vals`: an evaluated entry takes the
oracle value at its point when defined and its value in `e` otherwise, a programmed
entry takes its value in `e`. The programmed public entries are programmed, the
evaluated public entries are recorded as oracle entries and the hidden entries as
hidden entries. The flag is set when a hidden entry lands on a defined point or an
evaluated public entry on the point of a hidden entry only. The real signer of `G`
with its programmed entries programmed is the sampler `G.witSampler`.

The sampler may read every value of `e`, including the values of programmed entries
whose points come after the point of the entry it computes: for FAEST the hidden
leaf of a GGM tree is the decoding of a challenge computed after the leaf
commitments.

## Main definitions

* `Protocol.Attempt`, `Protocol.Sampler` — a signing attempt with the values of its
  programmed entries fixed, and a sampler of attempts
* `Protocol.witSampler` — the real signer with its programmed entries programmed
* `attSignOut`, `attStep` — the signing answer of an attempt and the oracle of the
  game
* `attGame D A`, `attAdvantage D A` — the game and its advantage
* `Protocol.ProgBoundAt`, `Protocol.AttHVZKAt`, `Protocol.AttKeyBoundAt` — the bound
  on guessing the points of programmed entries of the real signer, statistical HVZK
  of a sampler, and the bound on guessing the points of hidden entries of a sampler
* `chalGame D B` — the game of a distinguisher `B` with one query to the signing
  answer of `D`
* `hybDist D D' k A` — the distinguisher that answers the signing queries before the
  `k`-th from `D'`, the `k`-th from the challenge and the later ones from `D`

## Main results

* `Protocol.eufcma_le_wit` — the EUF-CMA advantage is at most the advantage at the
  witness sampler plus the expectation over generated pairs of `qS·Q·Γ_P(x, w)`,
  `Q = qH + V + μ·qS`
* `Protocol.attAdvantage_hybrid` — the distance between the advantages at two
  samplers is at most the sum over `k < qS` of the advantages of `hybDist D D' k A`
* `Protocol.att_le_sim` — the advantage at a sampler with HVZK distance `δ` and
  hidden-key bound `Γ_H` is at most the simulated-game advantage plus the
  expectation over generated pairs of `qS·δ(x, w) + qS·Q·Γ_H(x, w)`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open CatCrypt.Crypto.Constructions.ECBCPRF (tsum_bind_mul tsum_pure_mul)
open scoped ENNReal

/-! ## Attempts and samplers -/

namespace Protocol

variable (G : Protocol)

/-- A signing attempt whose programmed entries take fixed values: the point of entry
`i` from the values `v`, reading only the values before `i`, at distinct points;
the public marks; and the answer. -/
structure Attempt where
  /-- The point of entry `i` from the values. -/
  key : (Fin G.μ → G.Ch) → Fin G.μ → G.Key
  /-- The point of entry `i` reads only the values of the entries before it. -/
  key_causal : ∀ (v v' : Fin G.μ → G.Ch) (i : Fin G.μ),
    (∀ j, j < i → v j = v' j) → key v i = key v' i
  /-- The entries are at distinct points. -/
  key_inj : ∀ (v : Fin G.μ → G.Ch) (i j : Fin G.μ), key v i = key v j → i = j
  /-- Entry `i` is public. -/
  pub : (Fin G.μ → G.Ch) → Fin G.μ → Bool
  /-- The answer. -/
  sign : (Fin G.μ → G.Ch) → Option G.Sig

/-- A sampler of attempts on the message `m` for the pair `(x, w)` from the values
`e` of the entries. -/
abbrev Sampler := G.Stmt × G.Wit → G.Msg → (Fin G.μ → G.Ch) → PMF G.Attempt

/-- The attempt of the real signer for `(x, w)` on `m` with the randomness `r`. -/
def witAttempt (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) : G.Attempt :=
  ⟨G.key x w m r, G.key_causal x w m r, G.key_inj x w m r, G.pub x w m r, G.sign x w m r⟩

/-- The real signer with its programmed entries programmed: uniform randomness,
independent of the values. -/
noncomputable def witSampler : G.Sampler :=
  fun xw m _ => (PMF.uniformOfFintype G.Rand).map (G.witAttempt xw.1 xw.2 m)

end Protocol

namespace Protocol.Attempt

variable {G : Protocol} (a : G.Attempt)

/-- The values of the attempt against the oracle `look`: an evaluated entry takes the
value of `look` at its point when defined and its value in `e` otherwise; a
programmed entry takes its value in `e`. -/
def vals (look : G.Key → Option G.Ch) (e : Fin G.μ → G.Ch) : Fin G.μ → G.Ch :=
  effVec (fun i => if G.ev i then look else fun _ => none) a.key e

/-- The entries `i` with the values `v` that satisfy `p`, in order. -/
def entries (v : Fin G.μ → G.Ch) (p : Fin G.μ → Bool) : List (G.Key × G.Ch) :=
  ((List.finRange G.μ).filter p).map fun i => (a.key v i, v i)

/-- The programmed public entries with the values `v`. -/
def pubEntries (v : Fin G.μ → G.Ch) : List (G.Key × G.Ch) :=
  a.entries v fun i => !G.ev i && a.pub v i

/-- The evaluated public entries with the values `v`. -/
def evEntries (v : Fin G.μ → G.Ch) : List (G.Key × G.Ch) :=
  a.entries v fun i => G.ev i && a.pub v i

/-- The hidden entries with the values `v`. -/
def hidEntries (v : Fin G.μ → G.Ch) : List (G.Key × G.Ch) :=
  a.entries v fun i => !a.pub v i

/-- The trace with the values `v`: the evaluated public entries, the programmed
public entries and the answer. -/
def trace (v : Fin G.μ → G.Ch) : G.Trace :=
  (a.evEntries v, a.pubEntries v, a.sign v)

/-- The hidden entries with the values `v` are at points undefined in `look`. -/
def hidFresh (look : G.Key → Option G.Ch) (v : Fin G.μ → G.Ch) : Bool :=
  (List.finRange G.μ).all fun i => a.pub v i || (look (a.key v i)).isNone

/-- The trace from which the point of entry `i` of the attempt against `look` is
guessed: the trace when the entry is hidden at a point undefined in `look`, and the
empty trace otherwise. -/
def guessView (look : G.Key → Option G.Ch) (e : Fin G.μ → G.Ch) (i : Fin G.μ) : G.Trace :=
  if a.pub (a.vals look e) i || (look (a.key (a.vals look e) i)).isSome then ([], [], none)
  else a.trace (a.vals look e)

end Protocol.Attempt

namespace Protocol

variable {G : Protocol} (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand)

@[simp] theorem witAttempt_key : (G.witAttempt x w m r).key = G.key x w m r := rfl

@[simp] theorem witAttempt_pub : (G.witAttempt x w m r).pub = G.pub x w m r := rfl

@[simp] theorem witAttempt_sign : (G.witAttempt x w m r).sign = G.sign x w m r := rfl

theorem witAttempt_vals (look : G.Key → Option G.Ch) (e : Fin G.μ → G.Ch) :
    (G.witAttempt x w m r).vals look e = G.vals look x w m r e := rfl

theorem witAttempt_trace (v : Fin G.μ → G.Ch) :
    (G.witAttempt x w m r).trace v = G.trace x w m r v := rfl

theorem witAttempt_hidEntries (v : Fin G.μ → G.Ch) :
    (G.witAttempt x w m r).hidEntries v = G.hidEntries x w m r v := rfl

theorem witAttempt_hidFresh (look : G.Key → Option G.Ch) (v : Fin G.μ → G.Ch) :
    (G.witAttempt x w m r).hidFresh look v = G.hidFresh look x w m r v := rfl

theorem witAttempt_guessView (look : G.Key → Option G.Ch) (e : Fin G.μ → G.Ch)
    (i : Fin G.μ) :
    (G.witAttempt x w m r).guessView look e i = G.guessView look x w m r e i := rfl

end Protocol

/-! ## The game -/

section AttGame

variable {G : Protocol}

/-- The signing answer on `m` of the attempt `a` with the values `e` from the tables
`t`. The trace of the attempt against all entries is answered by `traceOut`, which
records the fresh evaluated public entries in `hash` and programs the programmed
public entries; the flag of `traceOut` is not kept. The hidden entries at undefined
points are recorded in `rej`. The flag is set when a hidden entry lands on a defined
point or an evaluated public entry on the point of a hidden entry only. -/
def attSignOut (t : G.Tables) (b : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch)
    (a : G.Attempt) : G.Answer × (G.Tables × Bool) :=
  ((traceOut t b m (a.trace (a.vals t.lookupAll e))).1,
    ({ (traceOut t b m (a.trace (a.vals t.lookupAll e))).2.1 with
        rej := t.rej ++ (a.hidEntries (a.vals t.lookupAll e)).filter
          fun p => (t.lookupAll p.1).isNone },
      b || (List.finRange G.μ).any fun i =>
        if a.pub (a.vals t.lookupAll e) i then
          G.ev i && (t.lookup (a.key (a.vals t.lookupAll e) i)).isNone &&
            (lookupIn t.rej (a.key (a.vals t.lookupAll e) i)).isSome
        else (t.lookupAll (a.key (a.vals t.lookupAll e) i)).isSome))

/-- The signing oracle of the sampler `D` for the pair `xw` on `m` from the state
`s`: uniform values `e`, then an attempt from `D xw m e`. -/
noncomputable def attSign (D : G.Sampler) (xw : G.Stmt × G.Wit) (s : G.Tables × Bool)
    (m : G.Msg) : PMF (G.Answer × (G.Tables × Bool)) :=
  (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind fun e => (D xw m e).map (attSignOut s.1 s.2 m e)

/-- The oracle of the game at the sampler `D` for the pair `xw`: the hash queries of
the real game and the signing oracle `attSign D xw`. -/
noncomputable def attStep (D : G.Sampler) (xw : G.Stmt × G.Wit) (s : G.Tables × Bool) :
    G.Query → Step G.Answer (G.Tables × Bool) G.Ch
  | .inl k => realHashStep s.1 s.2 k
  | .inr m => .plain (attSign D xw s m)

/-- The EUF-CMA game with the signing oracle of the sampler `D`. -/
noncomputable def attGame (D : G.Sampler) {qH qS : ℕ} (A : G.Adversary qH qS) : SPComp Bool :=
  PRPPRF.pmfGame (gameDist (attStep D) A)

/-- The advantage in the game with the signing oracle of the sampler `D`. -/
noncomputable def attAdvantage (D : G.Sampler) {qH qS : ℕ} (A : G.Adversary qH qS) : ℝ≥0∞ :=
  prTrue (attGame D A) Heap.empty

theorem attStep_inl (D : G.Sampler) (xw : G.Stmt × G.Wit) (s : G.Tables × Bool) (k : G.Key) :
    toOracle (attStep D xw) s (.inl k) = toOracle (realStep xw) s (.inl k) := rfl

end AttGame

/-! ## The witness sampler -/

namespace Protocol

variable (G : Protocol)

/-- **Programmed-key bound at one pair.** For the pair `(x, w)`, every message, every
oracle `look` and every point `k`, the expected number of programmed entries of the
real attempt against `look` at the point `k`, over uniform values and uniform
randomness, is at most `Γ`. -/
def ProgBoundAt (x : G.Stmt) (w : G.Wit) (Γ : ℝ≥0∞) : Prop :=
  ∀ (m : G.Msg) (look : G.Key → Option G.Ch) (k : G.Key),
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformOfFintype G.Rand r *
      ∑ i, (if G.ev i = false ∧ G.key x w m r (G.vals look x w m r e) i = k then 1 else 0) ≤ Γ

variable {G}

/-- The key bound at a pair bounds the guess of the points of programmed entries. -/
theorem KeyBoundAt.progBoundAt {x : G.Stmt} {w : G.Wit} {Γ : ℝ≥0∞} (h : G.KeyBoundAt x w Γ) :
    G.ProgBoundAt x w Γ := by
  intro m look k
  refine le_trans ?_ (h m look fun _ => PMF.pure k)
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (Finset.sum_le_sum fun i _ => ?_) _) _
  by_cases hi : G.ev i = false ∧ G.key x w m r (G.vals look x w m r e) i = k
  · rw [if_pos hi, if_pos (by simp [Protocol.flagging, hi.1]), hi.2, PMF.pure_apply, if_pos rfl]
  · rw [if_neg hi]
    exact zero_le

end Protocol

section Wit

variable {G : Protocol}

/-- A real signing attempt whose programmed entries are at undefined points is the
signing answer of its attempt with the programmed entries programmed. -/
theorem realSignOut_eq_attSignOut (x : G.Stmt) (w : G.Wit) (t : G.Tables) (b : Bool)
    (m : G.Msg) (e : Fin G.μ → G.Ch) (r : G.Rand)
    (h : ∀ i, G.ev i = false →
      t.lookupAll (G.key x w m r (G.vals t.lookupAll x w m r e) i) = none) :
    realSignOut x w t b m e r = attSignOut t b m e (G.witAttempt x w m r) := by
  have hv : G.honestVals t.lookupAll x w m r e = G.vals t.lookupAll x w m r e := by
    refine effVec_congr _ _ (G.key_causal x w m r) e _ fun i => ?_
    change t.lookupAll (G.key x w m r (G.vals t.lookupAll x w m r e) i) =
      (if G.ev i then t.lookupAll else fun _ => none)
        (G.key x w m r (G.vals t.lookupAll x w m r e) i)
    cases hev : G.ev i
    · exact h i hev
    · rfl
  set v := G.vals t.lookupAll x w m r e with hvdef
  have hev_of : ∀ i, (!G.ev i && G.pub x w m r v i) = true → G.ev i = false := fun i hi => by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hi
    exact hi.1
  have hpe : ∀ p ∈ G.pubEntries x w m r v,
      (hashAll t (G.evEntries x w m r v)).lookup p.1 = none := fun p hp => by
    obtain ⟨i, hi, rfl⟩ := Protocol.mem_entries hp
    rw [Protocol.lookup_hashAll_of_notMem _ _ (Protocol.key_notMem_evEntries (hev_of i hi))]
    exact Protocol.lookup_eq_none_of_lookupAll (h i (hev_of i hi))
  have hp : (G.pubEntries x w m r v).filter (fun p => (t.lookupAll p.1).isNone) =
      G.pubEntries x w m r v := List.filter_eq_self.mpr fun p hp => by
    obtain ⟨i, hi, rfl⟩ := Protocol.mem_entries hp
    simp [h i (hev_of i hi)]
  have hany : ((List.finRange G.μ).any fun i =>
      if G.flagging x w m r v i then (t.lookupAll (G.key x w m r v i)).isSome
      else (t.lookup (G.key x w m r v i)).isNone &&
        (lookupIn t.rej (G.key x w m r v i)).isSome) =
      ((List.finRange G.μ).any fun i =>
        if G.pub x w m r v i then
          G.ev i && (t.lookup (G.key x w m r v i)).isNone &&
            (lookupIn t.rej (G.key x w m r v i)).isSome
        else (t.lookupAll (G.key x w m r v i)).isSome) := by
    refine congrArg (List.any _) (funext fun i => ?_)
    cases hev : G.ev i <;> cases hpb : G.pub x w m r v i <;>
      simp [Protocol.flagging, hev, hpb, h i]
  rw [show attSignOut t b m e (G.witAttempt x w m r) =
      ((traceOut t b m (G.trace x w m r v)).1,
        ({ (traceOut t b m (G.trace x w m r v)).2.1 with
            rej := t.rej ++ (G.hidEntries x w m r v).filter fun p => (t.lookupAll p.1).isNone },
          b || (List.finRange G.μ).any fun i =>
            if G.pub x w m r v i then
              G.ev i && (t.lookup (G.key x w m r v i)).isNone &&
                (lookupIn t.rej (G.key x w m r v i)).isSome
            else (t.lookupAll (G.key x w m r v i)).isSome)) from rfl]
  unfold traceOut programOut
  rw [show (G.trace x w m r v).2.1 = G.pubEntries x w m r v from rfl,
    show (G.trace x w m r v).1 = G.evEntries x w m r v from rfl,
    show (G.trace x w m r v).2.2 = G.sign x w m r v from rfl,
    programAll_of_fresh _ b _ hpe (nodup_pubEntries x w m r v), ← hany]
  simp only [realSignOut, hv, hp]
  rfl

/-- The expectation of `f` under `p` is at most that of `f'` plus `C` when `f ≤ f' + C`
on the support. -/
theorem tsum_mul_le_tsum_mul_add {β : Type} (p : PMF β) (f f' : β → ℝ≥0∞) (C : ℝ≥0∞)
    (h : ∀ y ∈ p.support, f y ≤ f' y + C) : ∑' y, p y * f y ≤ ∑' y, p y * f' y + C := by
  calc ∑' y, p y * f y ≤ ∑' y, p y * (f' y + C) := ENNReal.tsum_le_tsum fun y => by
        by_cases hy : p y = 0
        · simp [hy]
        · exact mul_le_mul_right (h y ((PMF.mem_support_iff _ _).mpr hy)) _
    _ = _ := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- A programmed entry of the real attempt with the values `e` and the randomness `r`
from the tables `t` lands on a defined point. -/
def progColl (x : G.Stmt) (w : G.Wit) (t : G.Tables) (m : G.Msg) (e : Fin G.μ → G.Ch)
    (r : G.Rand) : Bool :=
  (List.finRange G.μ).any fun i =>
    !G.ev i && (t.lookupAll (G.key x w m r (G.vals t.lookupAll x w m r e) i)).isSome

/-- A programmed entry of a real attempt lands on a defined point of the tables `t`
with probability at most `|t|·Γ`. -/
theorem tsum_progColl_le (x : G.Stmt) (w : G.Wit) {Γ : ℝ≥0∞} (hP : G.ProgBoundAt x w Γ)
    (t : G.Tables) (m : G.Msg) :
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformOfFintype G.Rand r *
      (if progColl x w t m e r = true then 1 else 0) ≤ t.size * Γ := by
  set N := t.keys.length
  -- the programmed entries at the `j`-th defined point
  let F : ℕ → (Fin G.μ → G.Ch) → G.Rand → ℝ≥0∞ := fun j e r =>
    ∑ i, (if G.ev i = false ∧
      some (G.key x w m r (G.vals t.lookupAll x w m r e) i) = t.keys[j]? then 1 else 0)
  have h1 : ∀ e r, (if progColl x w t m e r = true then (1 : ℝ≥0∞) else 0) ≤
      ∑ j ∈ Finset.range N, F j e r := fun e r => by
    split_ifs with hc
    · obtain ⟨i, -, hi⟩ := List.any_eq_true.mp hc
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hi
      obtain ⟨j, hjk⟩ := List.mem_iff_getElem?.mp (Protocol.lookupAll_isSome_mem hi.2)
      have hjN : j < N := (List.getElem?_eq_some_iff.mp hjk).1
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => F j e r) (fun _ _ => zero_le)
        (Finset.mem_range.mpr hjN))
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => (if G.ev i = false ∧
        some (G.key x w m r (G.vals t.lookupAll x w m r e) i) = t.keys[j]? then (1 : ℝ≥0∞)
        else 0)) (fun _ _ => zero_le) (Finset.mem_univ i))
      rw [if_pos ⟨hi.1, hjk.symm⟩]
    · exact zero_le
  have h2 : ∀ j, ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e *
      ∑' r, PMF.uniformOfFintype G.Rand r * F j e r ≤ Γ := fun j => by
    cases hj : t.keys[j]? with
    | none => simp [F, hj]
    | some k => simpa [F, hj] using hP m t.lookupAll k
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' r,
        PMF.uniformOfFintype G.Rand r * ∑ j ∈ Finset.range N, F j e r :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (h1 e r) _) _
    _ = ∑ j ∈ Finset.range N, ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e *
          ∑' r, PMF.uniformOfFintype G.Rand r * F j e r := tsum_mul_tsum_mul_finsetSum _ _ _ _
    _ ≤ ∑ _j ∈ Finset.range N, Γ := Finset.sum_le_sum fun j _ => h2 j
    _ = t.size * Γ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          show N = t.size from Protocol.Tables.length_keys t]

variable {α : Type}

/-- One real signing step against the signing step of the witness sampler, for a test
`Y` of the outcome bounded by `1` and above by `Y'` plus `C` on the outcomes of the
witness sampler. -/
theorem realSign_le_witSign (xw : G.Stmt × G.Wit) {Γ : ℝ≥0∞}
    (hP : G.ProgBoundAt xw.1 xw.2 Γ) (s : G.Tables × Bool) (m : G.Msg)
    (Y Y' : G.Answer × (G.Tables × Bool) → ℝ≥0∞) (C : ℝ≥0∞) (hY1 : ∀ o, Y o ≤ 1)
    (hY : ∀ e r, Y (realSignOut xw.1 xw.2 s.1 s.2 m e r) ≤
      Y' (realSignOut xw.1 xw.2 s.1 s.2 m e r) + C) :
    ∑' o, toOracle (realStep xw) s (.inr m) o * Y o ≤
      ∑' o, toOracle (attStep G.witSampler xw) s (.inr m) o * Y' o + (C + s.1.size * Γ) := by
  obtain ⟨t, b⟩ := s
  simp only [toOracle, realStep, attStep, attSign, Protocol.witSampler, Step.toPMF, sampleVec,
    tsum_bind_mul, tsum_map_mul']
  have hpt : ∀ e r, Y (realSignOut xw.1 xw.2 t b m e r) ≤
      Y' (attSignOut t b m e (G.witAttempt xw.1 xw.2 m r)) + C +
        (if progColl xw.1 xw.2 t m e r = true then 1 else 0) := fun e r => by
    by_cases hc : progColl xw.1 xw.2 t m e r = true
    · rw [if_pos hc]
      exact (hY1 _).trans le_add_self
    · rw [if_neg hc, add_zero, ← realSignOut_eq_attSignOut xw.1 xw.2 t b m e r fun i hi => ?_]
      · exact hY e r
      · simp only [progColl, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true, not_exists, not_and] at hc
        simpa using hc i hi
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' r,
        PMF.uniformOfFintype G.Rand r * (Y' (attSignOut t b m e (G.witAttempt xw.1 xw.2 m r)) +
          C + (if progColl xw.1 xw.2 t m e r = true then 1 else 0)) :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (hpt e r) _) _
    _ = ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' r,
          PMF.uniformOfFintype G.Rand r * Y' (attSignOut t b m e (G.witAttempt xw.1 xw.2 m r)) +
        C + ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' r,
          PMF.uniformOfFintype G.Rand r * (if progColl xw.1 xw.2 t m e r = true then 1 else 0) := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := by
        rw [add_assoc]
        exact add_le_add le_rfl (add_le_add le_rfl (tsum_progColl_le xw.1 xw.2 hP t m))

/-- **Programmed entries programmed, for runs.** For a pair with programmed-key bound
`Γ` and a run with at most `h` hash and `q` signing queries from tables with `L`
entries, a test `g` with values in `[0, 1]` of the real run is at most the test of the
run with the signing oracle of the witness sampler plus `q·(L + h + μ·q)·Γ`. -/
theorem run_real_le_wit (xw : G.Stmt × G.Wit) {Γ : ℝ≥0∞} (hP : G.ProgBoundAt xw.1 xw.2 Γ)
    (A : OracleAdv G.Query G.Answer α) (h q : ℕ) (hA : IsQueryBound₂ A h q)
    (s : G.Tables × Bool) (g : α × (G.Tables × Bool) → ℝ≥0∞) (hg : ∀ y, g y ≤ 1) :
    ∑' y, OracleAdv.run (toOracle (realStep xw)) A s y * g y ≤
      ∑' y, OracleAdv.run (toOracle (attStep G.witSampler xw)) A s y * g y +
        ((q * (s.1.size + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ := by
  induction A generalizing h q s with
  | ret a =>
    simp only [OracleAdv.run_ret, tsum_pure_mul]
    exact le_self_add
  | rand p k ih =>
    simp only [OracleAdv.run_rand, tsum_bind_mul]
    calc _ ≤ ∑' c, p c * (∑' y, OracleAdv.run (toOracle (attStep G.witSampler xw)) (k c) s y *
            g y + ((q * (s.1.size + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ) :=
          ENNReal.tsum_le_tsum fun c => mul_le_mul_right (ih c h q (hA c) s) _
      _ = _ := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    simp only [OracleAdv.run_query, tsum_bind_mul]
    have hY1 : ∀ o : G.Answer × (G.Tables × Bool),
        ∑' y, OracleAdv.run (toOracle (realStep xw)) (k o.1) o.2 y * g y ≤ 1 := fun o =>
      (ENNReal.tsum_le_tsum fun y => mul_le_of_le_one_right' (hg y)).trans
        (le_of_eq (PMF.tsum_coe _))
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        rw [attStep_inl]
        refine tsum_mul_le_tsum_mul_add _ _ _ _ fun o ho => (ih o.1 h q (hA o.1) o.2).trans ?_
        have hs := (realStep_support xw s (.inl key) o ho).2
        simp only [Sum.elim_inl] at hs
        refine add_le_add le_rfl (mul_le_mul_left ?_ _)
        exact_mod_cast Nat.mul_le_mul_left _ (by omega)
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        refine (realSign_le_witSign xw hP s m _
          (fun o => ∑' y, OracleAdv.run (toOracle (attStep G.witSampler xw)) (k o.1) o.2 y * g y)
          (((q * (s.1.size + G.μ + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ) hY1 fun e r => ?_).trans ?_
        · refine (ih _ h q (hA _) _).trans (add_le_add le_rfl (mul_le_mul_left ?_ _))
          have hs := (realSignOut_support xw.1 xw.2 s.1 s.2 m e r).2
          exact_mod_cast Nat.mul_le_mul_left _ (by omega)
        · refine add_le_add le_rfl ?_
          rw [← add_mul]
          refine mul_le_mul_left ?_ _
          have : q * (s.1.size + G.μ + h + G.μ * q) + s.1.size ≤
              (q + 1) * (s.1.size + h + G.μ * (q + 1)) := by
            simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
            nlinarith
          exact_mod_cast this

/-- **Programmed entries programmed.** For a protocol whose generated pairs `(x, w)`
have programmed-key bound `Γ (x, w)`, and every adversary with at most `qH` hash and
`qS` signing queries, the EUF-CMA advantage is at most the advantage in the game at
the witness sampler plus the expectation over the generator of
`qS·(qH + V + μ·qS)·Γ(x, w)`. -/
theorem Protocol.eufcma_le_wit {Γ : G.Stmt × G.Wit → ℝ≥0∞}
    (hP : ∀ xw ∈ G.gen.support, G.ProgBoundAt xw.1 xw.2 (Γ xw)) {qH qS : ℕ}
    (A : G.Adversary qH qS) :
    eufcmaAdvantage A ≤ attAdvantage G.witSampler A +
      ∑' xw, G.gen xw * (((qS * (qH + G.V + G.μ * qS) : ℕ) : ℝ≥0∞) * Γ xw) := by
  unfold eufcmaAdvantage attAdvantage eufcmaGame attGame
  rw [prTrue_gameDist, prTrue_gameDist, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun xw => ?_
  rw [← mul_add]
  by_cases hxw : xw ∈ G.gen.support
  · refine mul_le_mul_right ?_ _
    have hB := isQueryBound₂_withVerify xw.1 _ qH qS (A.isQueryBound xw.1)
    rw [toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite]
    refine (run_real_le_wit xw (hP xw hxw) _ (qH + G.V) qS hB (Protocol.Tables.empty, false)
      _ fun y => by split_ifs <;> simp).trans (le_of_eq ?_)
    simp [Protocol.Tables.empty, Protocol.Tables.size]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hxw]

end Wit

/-! ## The hybrid over the signing queries -/

section Hybrid

variable {G : Protocol}

/-- The one-query challenge oracle of the sampler `D` for the pair `xw`: on a message
and a state it gives the signing answer of `attSign D xw`. -/
noncomputable def chalOracle (D : G.Sampler) (xw : G.Stmt × G.Wit) :
    Unit → G.Msg × (G.Tables × Bool) → PMF ((G.Answer × (G.Tables × Bool)) × Unit) :=
  fun _ q => (attSign D xw q.2 q.1).map fun o => (o, ())

/-- The game of a distinguisher `B` against the challenge oracle of the sampler `D`:
`B` receives a generated pair and outputs a bit. -/
noncomputable def chalGame (D : G.Sampler)
    (B : G.Stmt × G.Wit → OracleAdv (G.Msg × (G.Tables × Bool)) (G.Answer × (G.Tables × Bool))
      Bool) : SPComp Bool :=
  PRPPRF.pmfGame (G.gen.bind fun xw => (OracleAdv.run (chalOracle D xw) (B xw) ()).map Prod.fst)

/-- The oracle whose signing query from a state with `n` signed messages uses the
sampler `Ds n`. -/
noncomputable def hybStep (Ds : ℕ → G.Sampler) (xw : G.Stmt × G.Wit) (s : G.Tables × Bool) :
    G.Query → Step G.Answer (G.Tables × Bool) G.Ch
  | .inl k => realHashStep s.1 s.2 k
  | .inr m => .plain (attSign (Ds s.1.signed.length) xw s m)

/-- The run of an adversary with the oracle of the game in which the signing query
`j` (from `0`) uses the sampler `D'` for `j < k`, the challenge oracle for `j = k` and
the sampler `D` for `j > k`; hash queries and the samplers are run by the
distinguisher. The counter `j` is the number of signing queries asked so far, and
`f` maps the output and final state. -/
noncomputable def hybRun (D D' : G.Sampler) (k : ℕ) (xw : G.Stmt × G.Wit) {α β : Type}
    (f : α × (G.Tables × Bool) → β) :
    ℕ → OracleAdv G.Query G.Answer α → G.Tables × Bool →
      OracleAdv (G.Msg × (G.Tables × Bool)) (G.Answer × (G.Tables × Bool)) β
  | _, .ret a, s => .ret (f (a, s))
  | j, .rand p c, s => .rand p fun b => hybRun D D' k xw f j (c b) s
  | j, .query (.inl key) c, s =>
    .rand (toOracle (realStep xw) s (.inl key)) fun o => hybRun D D' k xw f j (c o.1) o.2
  | j, .query (.inr m) c, s =>
    if j = k then .query (m, s) fun o => hybRun D D' k xw f (j + 1) (c o.1) o.2
    else .rand (attSign (if j < k then D' else D) xw s m) fun o =>
      hybRun D D' k xw f (j + 1) (c o.1) o.2

/-- **The `k`-th hybrid distinguisher.** On the pair `(x, w)` it runs the adversary
`A` with the verifier's queries, answers the signing queries before the `k`-th from
`D'`, the `k`-th from the challenge oracle and the later ones from `D`, and outputs
whether the forgery wins. -/
noncomputable def hybDist (D D' : G.Sampler) (k : ℕ) {qH qS : ℕ} (A : G.Adversary qH qS)
    (xw : G.Stmt × G.Wit) :
    OracleAdv (G.Msg × (G.Tables × Bool)) (G.Answer × (G.Tables × Bool)) Bool :=
  hybRun D D' k xw (wins xw.1) 0 (withVerify xw.1 (A.run xw.1)) (Protocol.Tables.empty, false)

/-- The distinguisher `hybRun` from the signing query `j` asks at most one query, and
none after the `k`-th signing query. -/
theorem isQueryBound_hybRun (D D' : G.Sampler) (k : ℕ) (xw : G.Stmt × G.Wit) {α β : Type}
    (f : α × (G.Tables × Bool) → β) (A : OracleAdv G.Query G.Answer α) (j : ℕ)
    (s : G.Tables × Bool) :
    (hybRun D D' k xw f j A s).IsQueryBound (if j ≤ k then 1 else 0) := by
  induction A generalizing j s with
  | ret a => trivial
  | rand p c ih => exact fun b => ih b j s
  | query d c ih =>
    cases d with
    | inl key => exact fun o => ih o.1 j o.2
    | inr m =>
      by_cases hj : j = k
      · subst hj
        simp only [hybRun, if_true, le_refl]
        intro o
        have := ih o.1 (j + 1) o.2
        simpa using this
      · simp only [hybRun, hj, if_false]
        intro o
        refine (ih o.1 (j + 1) o.2).mono ?_
        split_ifs <;> omega

/-- **One query.** The `k`-th hybrid distinguisher asks the challenge oracle at most
once. -/
theorem isQueryBound_hybDist (D D' : G.Sampler) (k : ℕ) {qH qS : ℕ} (A : G.Adversary qH qS)
    (xw : G.Stmt × G.Wit) : (hybDist D D' k A xw).IsQueryBound 1 := by
  have := isQueryBound_hybRun D D' k xw (wins xw.1) (withVerify xw.1 (A.run xw.1)) 0
    (Protocol.Tables.empty, false)
  unfold hybDist
  simpa using this

/-- A hash query keeps the signed messages. -/
theorem realStep_signed_inl (xw : G.Stmt × G.Wit) (s : G.Tables × Bool) (k : G.Key)
    (o : G.Answer × (G.Tables × Bool))
    (ho : o ∈ (toOracle (realStep xw) s (.inl k)).support) : o.2.1.signed = s.1.signed := by
  obtain ⟨t, b⟩ := s
  simp only [toOracle, realStep, realHashStep] at ho
  cases hl : t.lookup k with
  | some e =>
    simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
    subst ho; rfl
  | none =>
    cases hr : lookupIn t.rej k with
    | some e =>
      simp only [hl, hr, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho; rfl
    | none =>
      simp only [hl, hr, Step.toPMF, PMF.support_map, Set.mem_image] at ho
      obtain ⟨e, _, rfl⟩ := ho
      rfl

/-- A signing answer records its message as signed. -/
theorem attSign_signed (D : G.Sampler) (xw : G.Stmt × G.Wit) (s : G.Tables × Bool) (m : G.Msg)
    (o : G.Answer × (G.Tables × Bool)) (ho : o ∈ (attSign D xw s m).support) :
    o.2.1.signed = s.1.signed ++ [m] := by
  simp only [attSign, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at ho
  obtain ⟨e, _, a, _, rfl⟩ := ho
  rfl

/-- The run of `hybRun` against the challenge oracle of `C` is the run of the oracle
whose signing query `j` uses `D'` for `j < k`, `C` for `j = k` and `D` for `j > k`. -/
theorem run_hybRun (D D' C : G.Sampler) (k : ℕ) (xw : G.Stmt × G.Wit) {α β : Type}
    (f : α × (G.Tables × Bool) → β) (A : OracleAdv G.Query G.Answer α) (j : ℕ)
    (s : G.Tables × Bool) (hj : s.1.signed.length = j) :
    OracleAdv.run (chalOracle C xw) (hybRun D D' k xw f j A s) () =
      (OracleAdv.run (toOracle (hybStep (fun n => if n < k then D' else if n = k then C else D)
        xw)) A s).map fun y => (f y, ()) := by
  induction A generalizing j s with
  | ret a => simp [hybRun, PMF.pure_map]
  | rand p c ih => simp only [hybRun, OracleAdv.run_rand, PMF.map_bind, ih _ j s hj]
  | query d c ih =>
    cases d with
    | inl key =>
      simp only [hybRun, OracleAdv.run_rand, OracleAdv.run_query, PMF.map_bind]
      refine PMF.bind_congr_support _ _ _ fun o ho => ih o.1 j o.2 ?_
      rw [realStep_signed_inl xw s key o ho, hj]
    | inr m =>
      simp only [OracleAdv.run_query, PMF.map_bind]
      have hc : ∀ o ∈ (attSign (if j < k then D' else if j = k then C else D) xw s m).support,
          OracleAdv.run (chalOracle C xw) (hybRun D D' k xw f (j + 1) (c o.1) o.2) () =
            (OracleAdv.run (toOracle (hybStep (fun n => if n < k then D' else if n = k then C
              else D) xw)) (c o.1) o.2).map fun y => (f y, ()) := fun o ho => ih o.1 (j + 1) o.2
        (by rw [attSign_signed _ xw s m o ho, List.length_append, hj, List.length_singleton])
      have hs : toOracle (hybStep (fun n => if n < k then D' else if n = k then C else D) xw)
          s (.inr m) = attSign (if j < k then D' else if j = k then C else D) xw s m := by
        simp only [toOracle, hybStep, Step.toPMF, hj]
      rw [hs]
      by_cases hjk : j = k
      · subst hjk
        simp only [hybRun, if_true, OracleAdv.run_query, chalOracle, PMF.bind_map,
          lt_irrefl, if_false] at hc ⊢
        exact PMF.bind_congr_support _ _ _ hc
      · simp only [hybRun, hjk, if_false, OracleAdv.run_rand] at hc ⊢
        exact PMF.bind_congr_support _ _ _ hc

/-- The game in which the signing query `j` uses `D'` for `j < n` and `D` otherwise. -/
noncomputable def hybGame (D D' : G.Sampler) (n : ℕ) {qH qS : ℕ} (A : G.Adversary qH qS) :
    SPComp Bool :=
  PRPPRF.pmfGame (gameDist (fun xw => hybStep (fun j => if j < n then D' else D) xw) A)

theorem hybStep_const (D : G.Sampler) (xw : G.Stmt × G.Wit) :
    hybStep (fun _ => D) xw = attStep D xw := by
  funext s d
  cases d <;> rfl

/-- The challenge game of the `k`-th distinguisher at `C` is the game whose signing
query `j` uses `D'` for `j < k`, `C` for `j = k` and `D` for `j > k`. -/
theorem chalGame_hybDist (D D' C : G.Sampler) (k : ℕ) {qH qS : ℕ} (A : G.Adversary qH qS) :
    chalGame C (hybDist D D' k A) = PRPPRF.pmfGame (gameDist (fun xw =>
      hybStep (fun n => if n < k then D' else if n = k then C else D) xw) A) := by
  unfold chalGame gameDist hybDist
  congr 1
  refine congrArg _ (funext fun xw => ?_)
  rw [run_hybRun D D' C k xw _ _ 0 _ rfl, PMF.map_comp]
  rfl

theorem chalGame_hybDist_left (D D' : G.Sampler) (k : ℕ) {qH qS : ℕ} (A : G.Adversary qH qS) :
    chalGame D (hybDist D D' k A) = hybGame D D' k A := by
  rw [chalGame_hybDist]
  unfold hybGame
  congr 2
  funext xw
  congr 1
  funext n
  split_ifs <;> rfl

theorem chalGame_hybDist_right (D D' : G.Sampler) (k : ℕ) {qH qS : ℕ}
    (A : G.Adversary qH qS) : chalGame D' (hybDist D D' k A) = hybGame D D' (k + 1) A := by
  rw [chalGame_hybDist]
  unfold hybGame
  congr 2
  funext xw
  congr 1
  funext n
  by_cases h1 : n < k
  · rw [if_pos h1, if_pos (by omega)]
  · by_cases h2 : n = k
    · rw [if_neg h1, if_pos h2, if_pos (by omega)]
    · rw [if_neg h1, if_neg h2, if_neg (by omega)]

/-- With at most `q` signing queries left from a state with `L` signed messages and
`L + q ≤ n`, the oracle whose signing query `j` uses `D'` for `j < n` gives the run
of the game at `D'`. -/
theorem run_hybStep_of_le (D D' : G.Sampler) (xw : G.Stmt × G.Wit) {α : Type}
    (A : OracleAdv G.Query G.Answer α) (h q n : ℕ) (hA : IsQueryBound₂ A h q)
    (s : G.Tables × Bool) (hs : s.1.signed.length + q ≤ n) :
    OracleAdv.run (toOracle (hybStep (fun j => if j < n then D' else D) xw)) A s =
      OracleAdv.run (toOracle (attStep D' xw)) A s := by
  induction A generalizing h q s with
  | ret a => rfl
  | rand p c ih => simp only [OracleAdv.run_rand, fun b => ih b h q (hA b) s hs]
  | query d c ih =>
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        simp only [OracleAdv.run_query]
        refine PMF.bind_congr_support _ _ _ fun o ho => ih o.1 h q (hA o.1) o.2 ?_
        rw [realStep_signed_inl xw s key o ho]
        exact hs
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        have hst : toOracle (hybStep (fun j => if j < n then D' else D) xw) s (.inr m) =
            toOracle (attStep D' xw) s (.inr m) := by
          simp only [toOracle, hybStep, attStep, Step.toPMF]
          rw [if_pos (by omega)]
        simp only [OracleAdv.run_query]
        rw [hst]
        refine PMF.bind_congr_support _ _ _ fun o ho => ih o.1 h q (hA o.1) o.2 ?_
        rw [show toOracle (attStep D' xw) s (.inr m) = attSign D' xw s m from rfl] at ho
        rw [attSign_signed D' xw s m o ho, List.length_append, List.length_singleton]
        omega

/-- **Hybrid over the signing queries.** For samplers `D` and `D'` and every adversary
with at most `qH` hash and `qS` signing queries, the distance between the advantages
in the games at `D` and at `D'` is at most the sum over `k < qS` of the advantages of
the distinguisher `hybDist D D' k A` between the challenge oracles of `D` and `D'`. -/
theorem Protocol.attAdvantage_hybrid (D D' : G.Sampler) {qH qS : ℕ} (A : G.Adversary qH qS) :
    Advantage (attGame D A) (attGame D' A) ≤
      ∑ k ∈ Finset.range qS, Advantage (chalGame D (hybDist D D' k A))
        (chalGame D' (hybDist D D' k A)) := by
  have h0 : hybGame D D' 0 A = attGame D A := by
    unfold hybGame attGame
    simp only [Nat.not_lt_zero, if_false]
    simp only [hybStep_const]
  have hq : hybGame D D' qS A = attGame D' A := by
    unfold hybGame attGame gameDist
    congr 2
    funext xw
    rw [run_hybStep_of_le D D' xw _ (qH + G.V) qS qS
      (isQueryBound₂_withVerify xw.1 _ qH qS (A.isQueryBound xw.1)) _ (by simp [Protocol.Tables.empty])]
  rw [← h0, ← hq]
  refine (HybridArgument.advantage_hybrid_dep_bool (fun n => hybGame D D' n A) qS).trans
    (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [chalGame_hybDist_left, chalGame_hybDist_right]

end Hybrid

/-! ## Statistical HVZK and the hidden-key bound of a sampler -/

namespace Protocol

variable (G : Protocol)

/-- **Statistical HVZK of a sampler at one pair** with distance `δ`. For the pair
`xw`, every message `m`, every oracle `look` and every test `g` with values in
`[0, 1]` on traces, the expectation of `g` on the trace of an attempt from `D xw m e`
against `look`, restricted to the attempts whose hidden points are undefined in
`look`, under uniform values `e`, is at most its expectation on the simulated trace
against `look` plus `δ`. -/
def AttHVZKAt (D : G.Sampler) (xw : G.Stmt × G.Wit) (δ : ℝ≥0∞) : Prop :=
  ∀ (m : G.Msg) (look : G.Key → Option G.Ch) (g : G.Trace → ℝ≥0∞), (∀ y, g y ≤ 1) →
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
      (if a.hidFresh look (a.vals look e) then g (a.trace (a.vals look e)) else 0) ≤
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' s, PMF.uniformOfFintype G.SimRand s *
      g (G.simTrace look xw.1 m e s) + δ

/-- **Hidden-key bound of a sampler at one pair.** For the pair `xw`, every message,
every oracle `look` and every randomized guesser `Q` on traces, the expected number
of hidden entries of an attempt from `D xw m e` against `look` whose point the guess
from `guessView` hits, under uniform values `e`, is at most `Γ`. -/
def AttKeyBoundAt (D : G.Sampler) (xw : G.Stmt × G.Wit) (Γ : ℝ≥0∞) : Prop :=
  ∀ (m : G.Msg) (look : G.Key → Option G.Ch) (Q : G.Trace → PMF G.Key),
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
      ∑ i, (if a.pub (a.vals look e) i then 0 else
        Q (a.guessView look e i) (a.key (a.vals look e) i)) ≤ Γ

variable {G}

/-- Statistical HVZK of the protocol at a pair is statistical HVZK of the witness
sampler. -/
theorem StatHVZKAt.attHVZKAt_wit {x : G.Stmt} {w : G.Wit} {δ : ℝ≥0∞}
    (h : G.StatHVZKAt x w δ) : G.AttHVZKAt G.witSampler (x, w) δ := by
  intro m look g hg
  simp only [witSampler, tsum_map_mul']
  exact h m look g hg

/-- The key bound of the protocol at a pair bounds the hidden-key guess of the witness
sampler. -/
theorem KeyBoundAt.attKeyBoundAt_wit {x : G.Stmt} {w : G.Wit} {Γ : ℝ≥0∞}
    (h : G.KeyBoundAt x w Γ) : G.AttKeyBoundAt G.witSampler (x, w) Γ := by
  intro m look Q
  simp only [witSampler, tsum_map_mul']
  refine le_trans ?_ (h m look Q)
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (Finset.sum_le_sum fun i _ => ?_) _) _
  rw [witAttempt_pub, witAttempt_vals, witAttempt_key, witAttempt_guessView]
  cases hp : G.pub x w m r (G.vals look x w m r e) i
  · simp [Protocol.flagging, hp]
  · simp

end Protocol

/-! ## The signing answer of an attempt with fresh hidden entries -/

section Fresh

variable {G : Protocol} (t : G.Tables) (b : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch)
  (a : G.Attempt)

/-- An attempt whose hidden entries are at undefined points and whose evaluated public
entries are not at the points of hidden entries only takes the values against the
visible oracle, is answered by `traceOut` with its hidden entries recorded, and keeps
the flag. -/
theorem attSignOut_of_fresh
    (h1 : ∀ i, a.pub (a.vals t.lookup e) i = false →
      t.lookupAll (a.key (a.vals t.lookup e) i) = none)
    (h2 : ∀ i, a.pub (a.vals t.lookup e) i = true → G.ev i = true →
      (t.lookup (a.key (a.vals t.lookup e) i)).isNone →
        lookupIn t.rej (a.key (a.vals t.lookup e) i) = none) :
    attSignOut t b m e a = ((traceOut t b m (a.trace (a.vals t.lookup e))).1,
      ({ (traceOut t b m (a.trace (a.vals t.lookup e))).2.1 with
          rej := t.rej ++ a.hidEntries (a.vals t.lookup e) }, b)) := by
  have hv : a.vals t.lookupAll e = a.vals t.lookup e := by
    refine effVec_congr _ _ a.key_causal e _ fun i => ?_
    change (if G.ev i then t.lookupAll else fun _ => none) (a.key (a.vals t.lookup e) i) =
      (if G.ev i then t.lookup else fun _ => none) (a.key (a.vals t.lookup e) i)
    cases hev : G.ev i
    · rfl
    · simp only [if_true]
      cases hp : a.pub (a.vals t.lookup e) i
      · rw [h1 i hp, Protocol.lookup_eq_none_of_lookupAll (h1 i hp)]
      · exact Protocol.lookupAll_eq_lookup (h2 i hp hev)
  set v := a.vals t.lookup e
  have hh : (a.hidEntries v).filter (fun p => (t.lookupAll p.1).isNone) = a.hidEntries v :=
    List.filter_eq_self.mpr fun p hp => by
      simp only [Protocol.Attempt.hidEntries, Protocol.Attempt.entries, List.mem_map,
        List.mem_filter, List.mem_finRange, true_and] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      simp [h1 i (by simpa using hi)]
  have hany : ((List.finRange G.μ).any fun i =>
      if a.pub v i then
        G.ev i && (t.lookup (a.key v i)).isNone && (lookupIn t.rej (a.key v i)).isSome
      else (t.lookupAll (a.key v i)).isSome) = false := by
    refine List.any_eq_false.mpr fun i _ => ?_
    cases hp : a.pub v i
    · simp [h1 i hp]
    · cases hev : G.ev i
      · simp
      · simp only [if_true, Bool.true_and, Bool.and_eq_true, not_and]
        intro hn
        simp [h2 i hp hev hn]
  simp only [attSignOut, hv]
  rw [hh, hany, Bool.or_false]

/-- A signing answer of an attempt that leaves the flag cleared starts with the flag
cleared and satisfies the hypotheses of `attSignOut_of_fresh`. -/
theorem fresh_of_attSignOut (h : (attSignOut t b m e a).2.2 = false) :
    b = false ∧
      (∀ i, a.pub (a.vals t.lookup e) i = false →
        t.lookupAll (a.key (a.vals t.lookup e) i) = none) ∧
      (∀ i, a.pub (a.vals t.lookup e) i = true → G.ev i = true →
        (t.lookup (a.key (a.vals t.lookup e) i)).isNone →
          lookupIn t.rej (a.key (a.vals t.lookup e) i) = none) := by
  simp only [attSignOut, Bool.or_eq_false_iff, List.any_eq_false, List.mem_finRange,
    true_implies] at h
  obtain ⟨hb, h⟩ := h
  set v := a.vals t.lookupAll e with hvd
  have c1 : ∀ i, a.pub v i = false → t.lookupAll (a.key v i) = none := fun i hp => by
    have := h i
    rw [if_neg (by simp [hp])] at this
    simpa using this
  have c2 : ∀ i, a.pub v i = true → G.ev i = true → (t.lookup (a.key v i)).isNone →
      lookupIn t.rej (a.key v i) = none := fun i hp hev hn => by
    have := h i
    rw [if_pos hp] at this
    simpa [hev, hn] using this
  have hr : a.vals t.lookup e = v := by
    refine effVec_congr _ _ a.key_causal e _ fun i => ?_
    change (if G.ev i then t.lookup else fun _ => none) (a.key v i) =
      (if G.ev i then t.lookupAll else fun _ => none) (a.key v i)
    cases hev : G.ev i
    · rfl
    · simp only [if_true]
      cases hp : a.pub v i
      · rw [c1 i hp, Protocol.lookup_eq_none_of_lookupAll (c1 i hp)]
      · exact (Protocol.lookupAll_eq_lookup (c2 i hp hev)).symm
  rw [hr]
  exact ⟨hb, c1, c2⟩

end Fresh

/-! ## The statistical hop at a sampler -/

section AttStat

variable {G : Protocol}

/-- The test `g` does not read the flag. -/
def FlagInsensitive {β σ : Type} (g : β × (σ × Bool) → ℝ≥0∞) : Prop :=
  ∀ y c, g (y.1, (y.2.1, c)) = g y

/-- The tables after programming do not depend on the flag. -/
theorem programAll_fst_flag (t : G.Tables) (b b' : Bool) (l : List (G.Key × G.Ch)) :
    (programAll t b l).1 = (programAll t b' l).1 := by
  induction l generalizing t b b' with
  | nil => rfl
  | cons p l ih =>
    unfold programAll
    split
    · exact ih t true true
    · exact ih _ b b'

/-- Forgetting the flag commutes with a simulated transition. -/
theorem simStep_forgetFlag (x₀ : G.Stmt) (s : G.Tables × Bool) (d : G.Query) :
    (toOracle (simStep x₀) s d).map (Prod.map id fun s' => (s'.1, false)) =
      (toOracle (simStep x₀) (s.1, false) d).map (Prod.map id fun s' => (s'.1, false)) := by
  obtain ⟨t, b⟩ := s
  cases d with
  | inl k =>
    simp only [toOracle, simStep, hashStep]
    cases t.lookup k with
    | some e => simp only [Step.toPMF, PMF.pure_map]; rfl
    | none => simp only [Step.toPMF, PMF.map_comp]; rfl
  | inr m =>
    simp only [toOracle, simStep, Step.toPMF, sampleVec, PMF.map_bind, PMF.map_comp]
    refine congrArg _ (funext fun e => congrArg _ (funext fun z => ?_))
    simp only [Function.comp_apply, simSignOut, traceOut, programOut, Prod.map]
    rw [programAll_fst_flag _ b false]

/-- The expectation of a test under a simulated run does not depend on the initial
flag when the test does not read the flag. -/
theorem tsum_run_sim_setFlag {α : Type} (x₀ : G.Stmt) (A : OracleAdv G.Query G.Answer α)
    (g : α × (G.Tables × Bool) → ℝ≥0∞) (hg : FlagInsensitive g) (t : G.Tables) (c : Bool) :
    ∑' y, OracleAdv.run (toOracle (simStep x₀)) A (t, c) y * g y =
      ∑' y, OracleAdv.run (toOracle (simStep x₀)) A (t, false) y * g y := by
  have hm : ∀ c', (OracleAdv.run (toOracle (simStep x₀)) A (t, c')).map
      (Prod.map id fun s' => (s'.1, false)) =
      OracleAdv.run (fun s d => (toOracle (simStep x₀) s d).map
        (Prod.map id fun s' => (s'.1, false))) A (t, false) := fun c' =>
    OracleAdv.run_map_state _ _ (fun s' : G.Tables × Bool => (s'.1, false))
      (simStep_forgetFlag x₀) A (t, c')
  have hE : ∀ c', ∑' y, OracleAdv.run (toOracle (simStep x₀)) A (t, c') y * g y =
      ∑' y, ((OracleAdv.run (toOracle (simStep x₀)) A (t, c')).map
        (Prod.map id fun s' => (s'.1, false))) y * g y := fun c' => by
    rw [tsum_map_mul']
    exact tsum_congr fun y => congrArg _ (hg y false).symm
  rw [hE c, hE false, hm c, hm false]

/-- The signing answer of an attempt with the flag cleared is bounded by the test of
the answer of its trace against the visible oracle when its hidden points are
undefined there, and by `0` otherwise. -/
theorem offFlag_attSignOut_le (F : G.Answer × (G.Tables × Bool) → ℝ≥0∞)
    (hFr : RejInsensitive F) (hFf : FlagInsensitive F) (t : G.Tables) (b : Bool) (m : G.Msg)
    (e : Fin G.μ → G.Ch) (a : G.Attempt) :
    offFlag F (attSignOut t b m e a) ≤
      if a.hidFresh t.lookup (a.vals t.lookup e) then
        F (traceOut t false m (a.trace (a.vals t.lookup e))) else 0 := by
  cases hfl : (attSignOut t b m e a).2.2
  swap
  · simp [offFlag, hfl]
  obtain ⟨rfl, h1, h2⟩ := fresh_of_attSignOut t b m e a hfl
  have hfr : a.hidFresh t.lookup (a.vals t.lookup e) = true := List.all_eq_true.mpr fun i _ => by
    cases hp : a.pub (a.vals t.lookup e) i
    · simp [Protocol.lookup_eq_none_of_lookupAll (h1 i hp)]
    · simp
  rw [if_pos hfr, attSignOut_of_fresh t false m e a h1 h2]
  unfold offFlag
  simp only [Bool.false_eq_true, if_false]
  rw [show ((traceOut t false m (a.trace (a.vals t.lookup e))).1,
      ({ (traceOut t false m (a.trace (a.vals t.lookup e))).2.1 with
          rej := t.rej ++ a.hidEntries (a.vals t.lookup e) }, false)) =
      setRej (t.rej ++ a.hidEntries (a.vals t.lookup e))
        ((traceOut t false m (a.trace (a.vals t.lookup e))).1,
          ((traceOut t false m (a.trace (a.vals t.lookup e))).2.1, false)) from rfl, hFr,
    hFf (traceOut t false m (a.trace (a.vals t.lookup e))) false]

/-- **One transition at a sampler.** For a sampler with statistical HVZK distance `δ`
at the pair and a test `F` with values in `[0, 1]` that reads neither the hidden
entries nor the flag, on the outcomes with the flag cleared a test of one transition
of the game at the sampler is at most the same test of one simulated transition, plus
`δ` for a signing query. -/
theorem attStep_le_simStep (D : G.Sampler) {δ : ℝ≥0∞} (xw : G.Stmt × G.Wit)
    (hZK : G.AttHVZKAt D xw δ) (s : G.Tables × Bool) (d : G.Query)
    (F : G.Answer × (G.Tables × Bool) → ℝ≥0∞) (hF : ∀ y, F y ≤ 1) (hFr : RejInsensitive F)
    (hFf : FlagInsensitive F) :
    ∑' o, toOracle (attStep D xw) s d o * offFlag F o ≤
      ∑' o, toOracle (simStep xw.1) s d o * F o + (if d.isRight then δ else 0) := by
  obtain ⟨t, b⟩ := s
  cases d with
  | inl k =>
    simp only [Sum.isRight_inl, Bool.false_eq_true, if_false, add_zero]
    simp only [toOracle, attStep, simStep, realHashStep, hashStep]
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
    simp only [toOracle, attStep, simStep, Step.toPMF, attSign, sampleVec, tsum_bind_mul,
      tsum_map_mul', Sum.isRight_inr, if_true]
    cases b with
    | true =>
      refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun e => ?_)) zero_le
      exact mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr fun a =>
        mul_eq_zero_of_right _ (if_pos rfl))
    | false =>
      calc ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
            offFlag F (attSignOut t false m e a)
          ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
              (if a.hidFresh t.lookup (a.vals t.lookup e) then
                F (traceOut t false m (a.trace (a.vals t.lookup e))) else 0) :=
            ENNReal.tsum_le_tsum fun e => mul_le_mul_right (ENNReal.tsum_le_tsum fun a =>
              mul_le_mul_right (offFlag_attSignOut_le F hFr hFf t false m e a) _) _
        _ ≤ _ := hZK m t.lookup (fun tr => F (traceOut t false m tr)) fun _ => hF _

variable {α : Type}

/-- The flag of a transition of the game at a sampler stays set. -/
theorem attStep_flag (D : G.Sampler) (xw : G.Stmt × G.Wit) (t : G.Tables) (d : G.Query)
    (o : G.Answer × (G.Tables × Bool))
    (ho : o ∈ (toOracle (attStep D xw) (t, true) d).support) : o.2.2 = true := by
  cases d with
  | inl k => exact realStep_flag xw t (.inl k) o ho
  | inr m =>
    simp only [toOracle, attStep, Step.toPMF, attSign, PMF.mem_support_bind_iff,
      PMF.support_map, Set.mem_image] at ho
    obtain ⟨e, _, a, _, rfl⟩ := ho
    simp [attSignOut]

/-- A run of the game at a sampler started with the flag set gives every test of
`offFlag` the value `0`. -/
theorem run_att_offFlag_true (D : G.Sampler) (xw : G.Stmt × G.Wit)
    (A : OracleAdv G.Query G.Answer α) (t : G.Tables) (g : α × (G.Tables × Bool) → ℝ≥0∞) :
    ∑' y, OracleAdv.run (toOracle (attStep D xw)) A (t, true) y * offFlag g y = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun y => ?_
  obtain ⟨a, t', fl⟩ := y
  cases fl with
  | true => simp [offFlag]
  | false =>
    rw [OracleAdv.run_flag_apply_false_of_true _ (fun t d r t' =>
      (PMF.apply_eq_zero_iff _ _).mpr fun hx => Bool.noConfusion (attStep_flag D xw t d _ hx)),
      zero_mul]

/-- **Statistical hop for runs at a sampler.** For a sampler with statistical HVZK
distance `δ` at the pair and a run with at most `h` hash and `q` signing queries, a
test `g` with values in `[0, 1]` that reads neither the hidden entries nor the flag,
on the outcomes with the flag cleared, is at most the test on the simulated run plus
`q·δ`. -/
theorem run_att_le_sim (D : G.Sampler) {δ : ℝ≥0∞} (xw : G.Stmt × G.Wit)
    (hZK : G.AttHVZKAt D xw δ) (A : OracleAdv G.Query G.Answer α) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) (s : G.Tables × Bool)
    (g : α × (G.Tables × Bool) → ℝ≥0∞) (hg : ∀ y, g y ≤ 1) (hgr : RejInsensitive g)
    (hgf : FlagInsensitive g) :
    ∑' y, OracleAdv.run (toOracle (attStep D xw)) A s y * offFlag g y ≤
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
    set Y : G.Answer × (G.Tables × Bool) → ℝ≥0∞ := fun o =>
      ∑' y, OracleAdv.run (toOracle (simStep xw.1)) (k o.1) o.2 y * g y with hY
    have hY1 : ∀ o, Y o ≤ 1 := fun o =>
      (ENNReal.tsum_le_tsum fun y => mul_le_of_le_one_right' (hg y)).trans
        (le_of_eq (PMF.tsum_coe _))
    have hYr : RejInsensitive Y := fun o l =>
      tsum_run_sim_setRej xw.1 (k o.1) g hgr o.2 l
    have hYf : FlagInsensitive Y := fun o c =>
      (tsum_run_sim_setFlag xw.1 (k o.1) g hgf o.2.1 c).trans
        (tsum_run_sim_setFlag xw.1 (k o.1) g hgf o.2.1 o.2.2).symm
    obtain ⟨h', q', hq', hk⟩ := isQueryBound₂_query_cases d k h q hA
    have hpt : ∀ o : G.Answer × (G.Tables × Bool),
        ∑' y, OracleAdv.run (toOracle (attStep D xw)) (k o.1) o.2 y * offFlag g y ≤
          offFlag Y o + q' * δ := by
      rintro ⟨r, t, fl⟩
      cases fl with
      | true =>
        rw [run_att_offFlag_true]
        exact zero_le
      | false => exact ih r h' q' (hk r) (t, false)
    calc _ ≤ ∑' o, toOracle (attStep D xw) s d o * (offFlag Y o + q' * δ) :=
          ENNReal.tsum_le_tsum fun o => mul_le_mul_right (hpt o) _
      _ = ∑' o, toOracle (attStep D xw) s d o * offFlag Y o + q' * δ := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ ≤ ∑' o, toOracle (simStep xw.1) s d o * Y o + (if d.isRight then δ else 0) + q' * δ :=
          add_le_add (attStep_le_simStep D xw hZK s d Y hY1 hYr hYf) le_rfl
      _ = _ := by rw [add_assoc, ← hq', ite_add_mul_eq]

/-- Winning in the game at a sampler has probability at most winning in the simulated
run, plus `q·δ`, plus the probability that the run at the sampler sets the flag. -/
theorem run_att_wins_le_stat (D : G.Sampler) {δ : ℝ≥0∞} (xw : G.Stmt × G.Wit)
    (hZK : G.AttHVZKAt D xw δ) (A : OracleAdv G.Query G.Answer G.Forgery) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) (s : G.Tables × Bool) (x : G.Stmt) :
    (OracleAdv.run (toOracle (attStep D xw)) A s).toOuterMeasure {y | wins x y = true} ≤
      (OracleAdv.run (toOracle (simStep xw.1)) A s).toOuterMeasure {y | wins x y = true} +
        q * δ +
      (OracleAdv.run (toOracle (attStep D xw)) A s).toOuterMeasure {y | y.2.2 = true} := by
  set g : G.Forgery × (G.Tables × Bool) → ℝ≥0∞ := fun y => if wins x y = true then 1 else 0
  have hg : ∀ y, g y ≤ 1 := fun y => by simp only [g]; split_ifs <;> simp
  have hgr : RejInsensitive g := fun _ _ => rfl
  have hgf : FlagInsensitive g := fun _ _ => rfl
  rw [toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite]
  calc _ ≤ ∑' y, OracleAdv.run (toOracle (attStep D xw)) A s y *
          (offFlag g y + if y.2.2 = true then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun y => mul_le_mul_right ?_ _
        simp only [offFlag, g]
        split_ifs <;> simp
    _ = ∑' y, OracleAdv.run (toOracle (attStep D xw)) A s y * offFlag g y +
          ∑' y, OracleAdv.run (toOracle (attStep D xw)) A s y *
            (if y.2.2 = true then 1 else 0) := by
        simp only [mul_add]
        rw [ENNReal.tsum_add]
    _ ≤ _ := add_le_add (run_att_le_sim D xw hZK A h q hA s g hg hgr hgf) le_rfl

end AttStat

/-! ## Tables grow along a run at a sampler -/

section AttGrow

variable {G : Protocol}

/-- Programming entries adds at most their number of public entries. -/
theorem programAll_prog_length (t : G.Tables) (b : Bool) (l : List (G.Key × G.Ch)) :
    (programAll t b l).1.prog.length ≤ t.prog.length + l.length := by
  induction l generalizing t b with
  | nil => exact le_refl _
  | cons p l ih =>
    unfold programAll
    split
    · exact (ih t true).trans (by simp)
    · refine (ih _ b).trans ?_
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

theorem le_programAll (t : G.Tables) (b : Bool) (l : List (G.Key × G.Ch)) :
    t.Le (programAll t b l).1 := by
  obtain ⟨h1, -, h3, h4, -⟩ := programAll_tables t b l
  exact ⟨h4, by rw [h1], by rw [h3]⟩

/-- The points of programmed entries are defined after programming. -/
theorem programAll_mem_keys (t : G.Tables) (b : Bool) (l : List (G.Key × G.Ch)) :
    ∀ p ∈ l, p.1 ∈ (programAll t b l).1.keys := by
  induction l generalizing t b with
  | nil => intro p hp; simp at hp
  | cons q l ih =>
    intro p hp
    unfold programAll
    split
    · rename_i e he
      rcases List.mem_cons.mp hp with rfl | hp
      · exact (le_programAll t true l).keys_subset
          (Protocol.lookup_isSome_mem_keys (by rw [he]; rfl))
      · exact ih t true p hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · refine (le_programAll _ b l).keys_subset (Protocol.Tables.mem_keys.mpr
          ⟨p, Or.inl (by simp), rfl⟩)
      · exact ih _ b p hp

theorem le_traceOut (t : G.Tables) (b : Bool) (m : G.Msg) (tr : G.Trace) :
    t.Le (traceOut t b m tr).2.1 := by
  have h := le_programAll (hashAll t tr.1) b tr.2.1
  exact (show t.Le (hashAll t tr.1) from
    ⟨List.prefix_refl _, List.prefix_append _ _, List.prefix_refl _⟩).trans h

theorem rej_traceOut (t : G.Tables) (b : Bool) (m : G.Msg) (tr : G.Trace) :
    (traceOut t b m tr).2.1.rej = t.rej :=
  (programAll_tables (hashAll t tr.1) b tr.2.1).2.2.1

theorem size_traceOut_le (t : G.Tables) (b : Bool) (m : G.Msg) (tr : G.Trace) :
    (traceOut t b m tr).2.1.hash.length + (traceOut t b m tr).2.1.prog.length ≤
      t.hash.length + t.prog.length + tr.1.length + tr.2.1.length := by
  have h1 := (programAll_tables (hashAll t tr.1) b tr.2.1).1
  have h2 := programAll_prog_length (hashAll t tr.1) b tr.2.1
  have h3 := List.length_filter_le (fun p : G.Key × G.Ch => (t.lookup p.1).isNone) tr.1
  change (programAll (hashAll t tr.1) b tr.2.1).1.hash.length +
    (programAll (hashAll t tr.1) b tr.2.1).1.prog.length ≤ _
  rw [h1]
  simp only [hashAll, List.length_append] at h2 ⊢
  omega

/-- The evaluated public, programmed public and hidden entries of an attempt are `μ`
entries in all. -/
theorem Protocol.Attempt.length_entries (a : G.Attempt) (v : Fin G.μ → G.Ch) :
    (a.evEntries v).length + (a.pubEntries v).length + (a.hidEntries v).length = G.μ := by
  simp only [Protocol.Attempt.evEntries, Protocol.Attempt.pubEntries,
    Protocol.Attempt.hidEntries, Protocol.Attempt.entries, List.length_map]
  have h1 := List.length_eq_length_filter_add (a.pub v) (l := List.finRange G.μ)
  have h2 := List.length_eq_length_filter_add G.ev
    (l := (List.finRange G.μ).filter (a.pub v))
  simp only [List.filter_filter, List.length_finRange] at h1 h2
  omega

theorem Protocol.Attempt.mem_entries {a : G.Attempt} {v : Fin G.μ → G.Ch}
    {p : Fin G.μ → Bool} {q : G.Key × G.Ch} (hq : q ∈ a.entries v p) :
    ∃ i, p i = true ∧ q = (a.key v i, v i) := by
  simp only [Protocol.Attempt.entries, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  exact ⟨i, hi, rfl⟩

theorem Protocol.Attempt.mem_entries_of {a : G.Attempt} {v : Fin G.μ → G.Ch}
    {p : Fin G.μ → Bool} {i : Fin G.μ} (hi : p i = true) : (a.key v i, v i) ∈ a.entries v p :=
  List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_finRange i, hi⟩, rfl⟩

variable (t : G.Tables) (b : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch) (a : G.Attempt)

/-- A signing answer of an attempt extends the tables by at most `μ` entries. -/
theorem attSignOut_support :
    t.Le (attSignOut t b m e a).2.1 ∧ (attSignOut t b m e a).2.1.size ≤ t.size + G.μ := by
  set v := a.vals t.lookupAll e
  have hL := le_traceOut t b m (a.trace v)
  have hr := rej_traceOut t b m (a.trace v)
  refine ⟨⟨hL.1, hL.2.1, List.prefix_append _ _⟩, ?_⟩
  have hs : (traceOut t b m (a.trace v)).2.1.hash.length +
      (traceOut t b m (a.trace v)).2.1.prog.length ≤
      t.hash.length + t.prog.length + (a.evEntries v).length + (a.pubEntries v).length :=
    size_traceOut_le t b m (a.trace v)
  have h0 := a.length_entries v
  have h3 := List.length_filter_le (fun p : G.Key × G.Ch => (t.lookupAll p.1).isNone)
    (a.hidEntries v)
  change (traceOut t b m (a.trace v)).2.1.prog.length +
    (traceOut t b m (a.trace v)).2.1.hash.length +
      (t.rej ++ (a.hidEntries v).filter fun p => (t.lookupAll p.1).isNone).length ≤
    t.prog.length + t.hash.length + t.rej.length + G.μ
  rw [List.length_append]
  omega

/-- Every point of a signing attempt is defined after it. -/
theorem attSignOut_key (i : Fin G.μ) :
    a.key (a.vals t.lookupAll e) i ∈ (attSignOut t b m e a).2.1.keys := by
  set v := a.vals t.lookupAll e
  have hLe : (traceOut t b m (a.trace v)).2.1.Le (attSignOut t b m e a).2.1 :=
    ⟨List.prefix_refl _, List.prefix_refl _, by
      rw [show (attSignOut t b m e a).2.1.rej = t.rej ++ _ from rfl, rej_traceOut]
      exact List.prefix_append _ _⟩
  cases hl : t.lookupAll (a.key v i) with
  | some _ =>
    exact (attSignOut_support t b m e a).1.keys_subset
      (Protocol.lookupAll_isSome_mem (by rw [hl]; rfl))
  | none =>
    cases hp : a.pub v i
    · refine Protocol.Tables.mem_keys.mpr ⟨(a.key v i, v i), Or.inr (Or.inr ?_), rfl⟩
      refine List.mem_append_right _ (List.mem_filter.mpr
        ⟨Protocol.Attempt.mem_entries_of (by rw [Bool.not_eq_true']; exact hp), by simp [hl]⟩)
    · cases hev : G.ev i
      · have hi : (!G.ev i && a.pub v i) = true := by simp [hev, hp]
        exact hLe.keys_subset (show a.key v i ∈
            (programAll (hashAll t (a.trace v).1) b (a.trace v).2.1).1.keys from
          programAll_mem_keys _ b _ (a.key v i, v i) (Protocol.Attempt.mem_entries_of hi))
      · refine hLe.keys_subset ((le_programAll _ b _).keys_subset
          (Protocol.Tables.mem_keys.mpr ⟨(a.key v i, v i), Or.inr (Or.inl ?_), rfl⟩))
        refine List.mem_append_right _ (List.mem_filter.mpr
          ⟨Protocol.Attempt.mem_entries_of (by simp only [hev, Bool.true_and]; exact hp), ?_⟩)
        simp [Protocol.lookup_eq_none_of_lookupAll hl]

/-- A signing answer of an attempt none of whose points is among the entries `l`
commutes with adding `l` to the hidden entries. -/
theorem attSignOut_addRejs (l : List (G.Key × G.Ch))
    (hk : ∀ i, a.key (a.vals t.lookupAll e) i ∉ l.map Prod.fst) :
    attSignOut (t.addRejs l) b m e a =
      Prod.map id (Prod.map (Protocol.Tables.addRejs l) id) (attSignOut t b m e a) := by
  have hv : a.vals (t.addRejs l).lookupAll e = a.vals t.lookupAll e :=
    effVec_congr _ _ a.key_causal e _ fun i => by
      change (if G.ev i then (t.addRejs l).lookupAll else fun _ => none)
          (a.key (a.vals t.lookupAll e) i) =
        (if G.ev i then t.lookupAll else fun _ => none) (a.key (a.vals t.lookupAll e) i)
      cases G.ev i
      · rfl
      · exact Protocol.lookupAll_addRejs_of_notMem l t (hk i)
  set v := a.vals t.lookupAll e
  have hl : ∀ i, (t.addRejs l).lookupAll (a.key v i) = t.lookupAll (a.key v i) :=
    fun i => Protocol.lookupAll_addRejs_of_notMem l t (hk i)
  have hr : ∀ i, lookupIn (t.addRejs l).rej (a.key v i) = lookupIn t.rej (a.key v i) :=
    fun i => lookupIn_append_of_notMem _ _ (hk i)
  have hlk : ∀ k, (t.addRejs l).lookup k = t.lookup k := fun _ => rfl
  have hf : (a.hidEntries v).filter (fun q => ((t.addRejs l).lookupAll q.1).isNone) =
      (a.hidEntries v).filter (fun q => (t.lookupAll q.1).isNone) :=
    List.filter_congr fun q hq => by
      obtain ⟨i, _, rfl⟩ := Protocol.Attempt.mem_entries hq
      rw [hl i]
  have ht : traceOut (t.addRejs l) b m (a.trace v) =
      Prod.map id (fun s' => ({ s'.1 with rej := l ++ t.rej }, s'.2))
        (traceOut t b m (a.trace v)) := traceOut_setRej (l ++ t.rej) t b m _
  simp only [attSignOut, hv, hl, hr, hlk, hf, ht]
  simp only [Protocol.Tables.addRejs, Prod.map, id, List.append_assoc]
  rfl

end AttGrow

section AttRun

variable {G : Protocol} {α : Type} (D : G.Sampler) (xw : G.Stmt × G.Wit)

theorem attSign_bind {β : Type} (s : G.Tables × Bool) (m : G.Msg)
    (g : G.Answer × (G.Tables × Bool) → PMF β) :
    (attSign D xw s m).bind g = (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind fun e =>
      (D xw m e).bind fun a => g (attSignOut s.1 s.2 m e a) := by
  simp only [attSign, PMF.bind_bind, PMF.bind_map, Function.comp_def]

theorem mem_support_attSign {s : G.Tables × Bool} {m : G.Msg}
    {o : G.Answer × (G.Tables × Bool)} (ho : o ∈ (attSign D xw s m).support) :
    ∃ e a, o = attSignOut s.1 s.2 m e a := by
  simp only [attSign, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at ho
  obtain ⟨e, _, a, _, rfl⟩ := ho
  exact ⟨e, a, rfl⟩

/-- Every transition of the game at a sampler extends the tables, by at most one entry
for a hash query and at most `μ` entries for a signing query. -/
theorem attStep_support (s : G.Tables × Bool) (d : G.Query)
    (o : G.Answer × (G.Tables × Bool)) (ho : o ∈ (toOracle (attStep D xw) s d).support) :
    s.1.Le o.2.1 ∧ o.2.1.size ≤ s.1.size + Sum.elim (fun _ => 1) (fun _ => G.μ) d := by
  cases d with
  | inl k => exact realStep_support xw s (.inl k) o ho
  | inr m =>
    obtain ⟨e, a, rfl⟩ := mem_support_attSign D xw ho
    exact attSignOut_support _ _ _ _ _

theorem run_att_support_le (A : OracleAdv G.Query G.Answer α)
    (s : G.Tables × Bool) (y : α × (G.Tables × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (attStep D xw)) A s).support) : s.1.Le y.2.1 := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact Protocol.Tables.Le.refl _
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b s hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    exact (attStep_support D xw s d o ho).1.trans (ih o.1 o.2 hy)

theorem run_att_support_flag (A : OracleAdv G.Query G.Answer α)
    (s : G.Tables × Bool) (y : α × (G.Tables × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (attStep D xw)) A s).support) (hs : s.2 = true) :
    y.2.2 = true := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact hs
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b s hb hs
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    obtain ⟨t, b⟩ := s
    dsimp only at hs
    subst hs
    exact ih o.1 o.2 hy (attStep_flag D xw t d o ho)

theorem run_att_support_size (A : OracleAdv G.Query G.Answer α)
    (h q : ℕ) (hA : IsQueryBound₂ A h q) (s : G.Tables × Bool) (y : α × (G.Tables × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (attStep D xw)) A s).support) :
    y.2.1.size ≤ s.1.size + h + G.μ * q := by
  induction A generalizing h q s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    show s.1.size ≤ _
    omega
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b h q (hA b) s hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    have hs := (attStep_support D xw s d o ho).2
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        have := ih o.1 h q (hA o.1) o.2 hy
        simp only [Sum.elim_inl] at hs
        omega
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        have := ih o.1 h q (hA o.1) o.2 hy
        simp only [Sum.elim_inr] at hs
        rw [Nat.mul_succ]
        omega

/-- A run of the game at a sampler from tables in which `k₀` is defined defines `k₀`
at the end. -/
theorem run_att_keys_eq_one (A : OracleAdv G.Query G.Answer α)
    (s : G.Tables × Bool) (k₀ : G.Key) (hk : k₀ ∈ s.1.keys) (E : Set (α × (G.Tables × Bool)))
    (hE : ∀ y, k₀ ∈ y.2.1.keys → y ∈ E) :
    (OracleAdv.run (toOracle (attStep D xw)) A s).toOuterMeasure E = 1 :=
  toOuterMeasure_eq_one_of_support _ _ fun y hy =>
    hE y ((run_att_support_le D xw A s y hy).keys_subset hk)

/-- A signing query in the induction of `run_att_addRejs_flag_le`. -/
theorem run_att_addRejs_sign_le (l : List (G.Key × G.Ch))
    (k : G.Answer → OracleAdv G.Query G.Answer α) (t : G.Tables) (m : G.Msg)
    (ih : ∀ c (t' : G.Tables) (b' : Bool),
      (OracleAdv.run (toOracle (attStep D xw)) (k c) (t'.addRejs l, b')).toOuterMeasure
          {y | y.2.2 = true} ≤
        (OracleAdv.run (toOracle (attStep D xw)) (k c) (t', b')).toOuterMeasure
          {y | y.2.2 = true ∨ ∃ p ∈ l, p.1 ∈ y.2.1.keys}) :
    (OracleAdv.run (toOracle (attStep D xw)) (.query (.inr m) k)
        (t.addRejs l, false)).toOuterMeasure {y | y.2.2 = true} ≤
      (OracleAdv.run (toOracle (attStep D xw)) (.query (.inr m) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true ∨ ∃ p ∈ l, p.1 ∈ y.2.1.keys} := by
  simp only [OracleAdv.run_query, toOracle, attStep, Step.toPMF, attSign_bind,
    PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun a => mul_le_mul_right ?_ _) _
  by_cases hc : ∃ i, a.key (a.vals t.lookupAll e) i ∈ l.map Prod.fst
  · obtain ⟨i, hi⟩ := hc
    obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hi
    refine (toOuterMeasure_le_one _ _).trans (le_of_eq
      (run_att_keys_eq_one D xw _ _ p.1 ?_ _ fun y hy => Or.inr ⟨p, hp, hy⟩).symm)
    rw [hpk]
    exact attSignOut_key _ _ _ _ _ i
  · rw [attSignOut_addRejs t false m e a l fun i hi => hc ⟨i, hi⟩]
    exact ih _ _ _

/-- **Hidden entries change the flag only where they are reached**, for the game at a
sampler. -/
theorem run_att_addRejs_flag_le (l : List (G.Key × G.Ch))
    (A : OracleAdv G.Query G.Answer α) (t : G.Tables) (b : Bool) :
    (OracleAdv.run (toOracle (attStep D xw)) A (t.addRejs l, b)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (OracleAdv.run (toOracle (attStep D xw)) A (t, b)).toOuterMeasure
        {y | y.2.2 = true ∨ ∃ p ∈ l, p.1 ∈ y.2.1.keys} := by
  induction A generalizing t b with
  | ret a =>
    simp only [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    split_ifs with h1 h2 <;> first | exact le_rfl | exact zero_le | exact absurd (Or.inl h1) h2
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    exact ENNReal.tsum_le_tsum fun c => mul_le_mul_right (ih c t b) _
  | query d k ih =>
    by_cases hb : b = true ∨ ∃ p ∈ l, p.1 ∈ t.keys
    · refine (toOuterMeasure_le_one _ _).trans (le_of_eq ?_)
      refine (toOuterMeasure_eq_one_of_support _ _ fun y hy => ?_).symm
      rcases hb with hb | ⟨p, hp, hk⟩
      · exact Or.inl (run_att_support_flag D xw _ (t, b) y hy hb)
      · exact Or.inr ⟨p, hp, (run_att_support_le D xw _ (t, b) y hy).keys_subset hk⟩
    simp only [not_or, Bool.not_eq_true, not_exists, not_and] at hb
    obtain ⟨rfl, hk⟩ := hb
    cases d with
    | inl key =>
      by_cases hke : key ∈ l.map Prod.fst
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hke
        refine (toOuterMeasure_le_one _ _).trans (le_of_eq ?_)
        refine (toOuterMeasure_eq_one_of_support _ _ fun y hy => ?_).symm
        rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
        obtain ⟨o, ho, hy⟩ := hy
        exact Or.inr ⟨p, hp, (run_att_support_le D xw _ o.2 y hy).keys_subset
          (realStep_key_inl xw _ _ o ho)⟩
      · rw [OracleAdv.run_query, OracleAdv.run_query, attStep_inl, attStep_inl,
          realStep_addRejs_inl xw l t false key hke,
          PMF.bind_map, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
        exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (ih o.1 o.2.1 o.2.2) _
    | inr m => exact run_att_addRejs_sign_le D xw l k t m fun c => ih c

end AttRun

/-! ## The flag of the game at a sampler -/

section AttFlag

variable {G : Protocol} {α : Type} (D : G.Sampler) (xw : G.Stmt × G.Wit)

/-- A finite sum inside two weighted sums, the inner weights depending on the outer
index, is the finite sum of the weighted sums. -/
theorem tsum_mul_tsum_dep_finsetSum {β γ ι : Type} (p : β → ℝ≥0∞) (p' : β → γ → ℝ≥0∞)
    (s : Finset ι) (F : ι → β → γ → ℝ≥0∞) :
    ∑' b, p b * ∑' c, p' b c * ∑ j ∈ s, F j b c =
      ∑ j ∈ s, ∑' b, p b * ∑' c, p' b c * F j b c := by
  have h1 : ∀ b, ∑' c, p' b c * ∑ j ∈ s, F j b c = ∑ j ∈ s, ∑' c, p' b c * F j b c :=
    fun b => by
      simp only [Finset.mul_sum]
      exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
  calc _ = ∑' b, ∑ j ∈ s, p b * ∑' c, p' b c * F j b c :=
        tsum_congr fun b => by rw [h1 b, Finset.mul_sum]
    _ = _ := Summable.tsum_finsetSum fun _ _ => ENNReal.summable

/-- **Guessing the hidden points of an attempt.** For a sampler with hidden-key bound
`Γ` and runs `R tr` indexed by traces whose final tables have at most `N` points on the
traces `guessView`, the expectation over the values and the attempts of the number of
hidden entries whose point is defined at the end of `R (guessView …)` is at most
`N·Γ`. -/
theorem tsum_att_guess_le {Γ : ℝ≥0∞} (hΓ : G.AttKeyBoundAt D xw Γ) (m : G.Msg)
    (look : G.Key → Option G.Ch) (R : G.Trace → PMF (α × (G.Tables × Bool))) (N : ℕ)
    (hN : ∀ e (a : G.Attempt) i, ∀ y ∈ (R (a.guessView look e i)).support,
      y.2.1.keys.length ≤ N) :
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
      ∑ i, (if a.pub (a.vals look e) i then 0 else
        (R (a.guessView look e i)).toOuterMeasure
          {y | a.key (a.vals look e) i ∈ y.2.1.keys}) ≤ N * Γ := by
  rcases isEmpty_or_nonempty G.Key with hK | ⟨⟨k₀⟩⟩
  · refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun e => mul_eq_zero_of_right _
      (ENNReal.tsum_eq_zero.mpr fun a => mul_eq_zero_of_right _ ?_))) zero_le
    have : IsEmpty (Fin G.μ) := ⟨fun i => hK.false (a.key (fun _ => Classical.arbitrary _) i)⟩
    simp
  -- the guess of the `j`-th point of the final tables
  let Q : ℕ → G.Trace → PMF G.Key := fun j tr => (R tr).map fun y => y.2.1.keys.getD j k₀
  have h1 : ∀ e (a : G.Attempt) i, (if a.pub (a.vals look e) i then 0 else
      (R (a.guessView look e i)).toOuterMeasure {y | a.key (a.vals look e) i ∈ y.2.1.keys}) ≤
      ∑ j ∈ Finset.range N, (if a.pub (a.vals look e) i then 0 else
        Q j (a.guessView look e i) (a.key (a.vals look e) i)) := fun e a i => by
    split_ifs
    · exact zero_le
    · exact toOuterMeasure_mem_le_sum (R (a.guessView look e i)) (fun y => y.2.1.keys)
        N k₀ (a.key (a.vals look e) i) (hN e a i)
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
        ∑ j ∈ Finset.range N, ∑ i, (if a.pub (a.vals look e) i then 0 else
          Q j (a.guessView look e i) (a.key (a.vals look e) i)) := by
        refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun a => mul_le_mul_right ?_ _) _
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun i _ => h1 e a i
    _ = ∑ j ∈ Finset.range N, ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e *
          ∑' a, D xw m e a * ∑ i, (if a.pub (a.vals look e) i then 0 else
            Q j (a.guessView look e i) (a.key (a.vals look e) i)) :=
        tsum_mul_tsum_dep_finsetSum _ (fun e a => D xw m e a) _ _
    _ ≤ ∑ _j ∈ Finset.range N, Γ := Finset.sum_le_sum fun j _ => hΓ m look (Q j)
    _ = N * Γ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The rest of a run of the game at a sampler after a signing attempt on `m` from
`t` with the trace `tr`, the flag cleared and the hidden entries left out. -/
noncomputable def attContRun (k : G.Answer → OracleAdv G.Query G.Answer α) (t : G.Tables)
    (m : G.Msg) (tr : G.Trace) : PMF (α × (G.Tables × Bool)) :=
  OracleAdv.run (toOracle (attStep D xw)) (k (traceOut t false m tr).1)
    ((traceOut t false m tr).2.1, false)

theorem Protocol.Attempt.length_guessView_le (a : G.Attempt) (look : G.Key → Option G.Ch)
    (e : Fin G.μ → G.Ch) (i : Fin G.μ) :
    (a.guessView look e i).1.length + (a.guessView look e i).2.1.length ≤ G.μ := by
  unfold Protocol.Attempt.guessView
  split
  · exact Nat.zero_le _
  · have := a.length_entries (a.vals look e)
    simp only [Protocol.Attempt.trace]
    omega

/-- One signing attempt in the induction of `run_att_flag_le`. -/
theorem att_flag_sign_term_le {Γ : ℝ≥0∞}
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ) (t : G.Tables)
    (ht : t.rej = []) (m : G.Msg) (e : Fin G.μ → G.Ch) (a : G.Attempt)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] →
      (OracleAdv.run (toOracle (attStep D xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤
        ((q * (t'.hash.length + t'.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ) :
    (OracleAdv.run (toOracle (attStep D xw)) (k (attSignOut t false m e a).1)
        (attSignOut t false m e a).2).toOuterMeasure {y | y.2.2 = true} ≤
      ((q * (t.hash.length + t.prog.length + G.μ + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ +
        ∑ i, (if a.pub (a.vals t.lookup e) i then 0 else
          (attContRun D xw k t m (a.guessView t.lookup e i)).toOuterMeasure
            {y | a.key (a.vals t.lookup e) i ∈ y.2.1.keys}) := by
  set v := a.vals t.lookup e with hv
  by_cases hc : ∃ i, a.pub v i = false ∧ (t.lookup (a.key v i)).isSome
  · obtain ⟨i, hf, hi⟩ := hc
    refine (toOuterMeasure_le_one _ _).trans (le_trans ?_ le_add_self)
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun i =>
      if a.pub v i then 0 else
        (attContRun D xw k t m (a.guessView t.lookup e i)).toOuterMeasure
          {y | a.key v i ∈ y.2.1.keys}) (fun _ _ => zero_le) (Finset.mem_univ i))
    have hg : a.guessView t.lookup e i = ([], [], none) := by
      simp only [Protocol.Attempt.guessView, ← hv, hi, Bool.or_true, if_true]
    simp only [hf, Bool.false_eq_true, if_false, hg]
    refine (run_att_keys_eq_one D xw _ _ _ ?_ _ fun y hy => hy).symm
    exact (le_traceOut t false m _).keys_subset (Protocol.lookup_isSome_mem_keys hi)
  simp only [not_exists, not_and, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at hc
  rw [attSignOut_of_fresh t false m e a
    (fun i hf => (Protocol.lookupAll_of_rej_nil ht _).trans (hc i hf))
    (fun i _ _ _ => by rw [ht]; exact lookupIn_nil _)]
  set T₀ : G.Tables := (traceOut t false m (a.trace v)).2.1
  have hT : ({ T₀ with rej := t.rej ++ a.hidEntries v } : G.Tables) =
      T₀.addRejs (a.hidEntries v) := by
    simp only [Protocol.Tables.addRejs, T₀, rej_traceOut, ht, List.nil_append,
      List.append_nil]
  rw [hT]
  refine (run_att_addRejs_flag_le D xw _ _ T₀ false).trans ?_
  refine (MeasureTheory.measure_mono (fun y hy => hy)).trans
    ((MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_))
  · refine (ih _ T₀ (by rw [rej_traceOut, ht])).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
    have h1 : T₀.hash.length + T₀.prog.length ≤ t.hash.length + t.prog.length +
        (a.evEntries v).length + (a.pubEntries v).length :=
      size_traceOut_le t false m (a.trace v)
    have h2 := a.length_entries v
    exact_mod_cast Nat.mul_le_mul_left _ (by omega)
  · calc _ ≤ (attContRun D xw k t m (a.trace v)).toOuterMeasure
            (⋃ i ∈ Finset.univ.filter (fun i => a.pub v i = false),
              {y | a.key v i ∈ y.2.1.keys}) := by
          refine MeasureTheory.measure_mono fun y hy => ?_
          obtain ⟨p, hp, hk⟩ := hy
          obtain ⟨i, hi, rfl⟩ := Protocol.Attempt.mem_entries hp
          simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨i, by simpa using hi, hk⟩
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => a.pub v i = false),
            (attContRun D xw k t m (a.trace v)).toOuterMeasure
              {y | a.key v i ∈ y.2.1.keys} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ = ∑ i ∈ Finset.univ.filter (fun i => a.pub v i = false),
            (if a.pub v i then 0 else
              (attContRun D xw k t m (a.guessView t.lookup e i)).toOuterMeasure
                {y | a.key v i ∈ y.2.1.keys}) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : a.pub v i = false := (Finset.mem_filter.mp hi).2
          have hg : a.guessView t.lookup e i = a.trace v := by
            simp only [Protocol.Attempt.guessView, ← hv, hi', hc i hi', Option.isSome_none,
              Bool.or_false, Bool.false_eq_true, if_false]
          rw [hi', hg]
          rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- A hash query in the induction of `run_att_flag_le`. -/
theorem att_flag_hash_step_le {Γ : ℝ≥0∞}
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ) (t : G.Tables)
    (ht : t.rej = []) (key : G.Key)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] →
      (OracleAdv.run (toOracle (attStep D xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤
        ((q * (t'.hash.length + t'.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ) :
    (OracleAdv.run (toOracle (attStep D xw)) (.query (.inl key) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      ((q * (t.hash.length + t.prog.length + (h + 1) + G.μ * q) : ℕ) : ℝ≥0∞) * Γ := by
  rw [OracleAdv.run_query]
  simp only [toOracle, attStep, realHashStep]
  cases hl : t.lookup key with
  | some e =>
    simp only [Step.toPMF, PMF.pure_bind]
    refine (ih _ t ht).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
    exact_mod_cast Nat.mul_le_mul_left _ (by omega)
  | none =>
    have hr : lookupIn t.rej key = none := by rw [ht]; exact lookupIn_nil key
    simp only [hr, Step.toPMF, PMF.bind_map, Function.comp_def, PMF.toOuterMeasure_bind_apply]
    calc ∑' e, PMF.uniformOfFintype G.Ch e * (OracleAdv.run (toOracle (attStep D xw))
          (k (.inl e)) ({ t with hash := t.hash ++ [(key, e)] }, false)).toOuterMeasure _
        ≤ ∑' e, PMF.uniformOfFintype G.Ch e *
          (((q * (t.hash.length + t.prog.length + (h + 1) + G.μ * q) : ℕ) :
            ℝ≥0∞) * Γ) := by
          refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
          refine (ih _ { t with hash := t.hash ++ [(key, e)] } ht).trans (le_of_eq ?_)
          simp only [List.length_append, List.length_singleton]
          congr 3
          omega
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The guess terms of a signing attempt in the induction of `run_att_flag_le`. -/
theorem att_flag_guess_le {Γ : ℝ≥0∞} (hΓ : G.AttKeyBoundAt D xw Γ)
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ)
    (hk : ∀ r, IsQueryBound₂ (k r) h q) (t : G.Tables) (ht : t.rej = []) (m : G.Msg) :
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
      ∑ i, (if a.pub (a.vals t.lookup e) i then 0 else
        (attContRun D xw k t m (a.guessView t.lookup e i)).toOuterMeasure
          {y | a.key (a.vals t.lookup e) i ∈ y.2.1.keys}) ≤
      ((t.hash.length + t.prog.length + G.μ + h + G.μ * q : ℕ) : ℝ≥0∞) * Γ := by
  refine tsum_att_guess_le D xw hΓ m t.lookup (attContRun D xw k t m) _ fun e a i y hy => ?_
  rw [Protocol.Tables.length_keys]
  have h1 := run_att_support_size D xw _ h q (hk _) _ y hy
  have h2 := a.length_guessView_le t.lookup e i
  have h3 := size_traceOut_le t false m (a.guessView t.lookup e i)
  have h4 := rej_traceOut t false m (a.guessView t.lookup e i)
  simp only [Protocol.Tables.size, h4, ht, List.length_nil] at h1 h3 ⊢
  omega

/-- A signing query in the induction of `run_att_flag_le`. -/
theorem att_flag_sign_step_le {Γ : ℝ≥0∞} (hΓ : G.AttKeyBoundAt D xw Γ)
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ)
    (hk : ∀ r, IsQueryBound₂ (k r) h q) (t : G.Tables) (ht : t.rej = []) (m : G.Msg)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] →
      (OracleAdv.run (toOracle (attStep D xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤
        ((q * (t'.hash.length + t'.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ) :
    (OracleAdv.run (toOracle (attStep D xw)) (.query (.inr m) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (((q + 1) * (t.hash.length + t.prog.length + h + G.μ * (q + 1)) : ℕ) : ℝ≥0∞) * Γ := by
  set L := t.hash.length + t.prog.length with hL
  set N := L + G.μ + h + G.μ * q with hN
  set B : ℝ≥0∞ := ((q * N : ℕ) : ℝ≥0∞) * Γ with hB
  -- the guess terms of the attempt `a` with the values `e`
  set S : (Fin G.μ → G.Ch) → G.Attempt → ℝ≥0∞ := fun e a =>
    ∑ i, (if a.pub (a.vals t.lookup e) i then 0 else
      (attContRun D xw k t m (a.guessView t.lookup e i)).toOuterMeasure
        {y | a.key (a.vals t.lookup e) i ∈ y.2.1.keys}) with hS
  have hterm := fun e a => att_flag_sign_term_le D xw k h q t ht m e a ih
  have hsum : ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e *
      ∑' a, D xw m e a * S e a ≤ (N : ℝ≥0∞) * Γ := by
    have := att_flag_guess_le D xw hΓ k h q hk t ht m
    rw [hS, hN, hL]
    exact_mod_cast this
  rw [OracleAdv.run_query]
  simp only [toOracle, attStep, Step.toPMF, attSign_bind, PMF.toOuterMeasure_bind_apply]
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e *
        ∑' a, D xw m e a * (B + S e a) :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun a => mul_le_mul_right ((hterm e a).trans (le_of_eq (by
            rw [hB, hN, hL, hS]))) _) _
    _ = B + ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e *
          ∑' a, D xw m e a * S e a := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ B + N * Γ := add_le_add_right hsum _
    _ = _ := by
        rw [hB, hN, hL]
        push_cast
        ring

/-- **Collision bound at a sampler.** For a sampler with hidden-key bound `Γ` at the
pair, from tables with no hidden entry, with `L` entries and the flag cleared, a run of
the game at the sampler asking at most `h` hash and `q` signing queries sets the flag
with probability at most `q·(L + h + μ·q)·Γ`. -/
theorem run_att_flag_le {Γ : ℝ≥0∞} (hΓ : G.AttKeyBoundAt D xw Γ)
    (A : OracleAdv G.Query G.Answer α) (h q : ℕ) (hA : IsQueryBound₂ A h q)
    (t : G.Tables) (ht : t.rej = []) :
    (OracleAdv.run (toOracle (attStep D xw)) A (t, false)).toOuterMeasure {y | y.2.2 = true} ≤
      ((q * (t.hash.length + t.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ := by
  induction A generalizing h q t with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (OracleAdv.run (toOracle (attStep D xw)) (k b) (t, false)).toOuterMeasure _
        ≤ ∑' b, p b *
            (((q * (t.hash.length + t.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ) :=
          ENNReal.tsum_le_tsum fun b => mul_le_mul_right (ih b h q (hA b) t ht) _
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        exact att_flag_hash_step_le D xw k h q t ht key fun c t' ht' => ih c h q (hA c) t' ht'
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        exact att_flag_sign_step_le D xw hΓ k h q hA t ht m fun c t' ht' =>
          ih c h q (hA c) t' ht'

end AttFlag

/-! ## The simulation hop at a sampler -/

section AttSim

variable {G : Protocol}

/-- **Signing-oracle simulation at a sampler.** For a sampler whose generated pairs
`xw` have statistical HVZK distance `δ xw` and hidden-key bound `Γ xw`, and every
adversary with at most `qH` hash and `qS` signing queries, the advantage in the game
at the sampler is at most the simulated-game advantage plus the expectation over the
generator of `qS·δ(x, w) + qS·(qH + V + μ·qS)·Γ(x, w)`. -/
theorem Protocol.att_le_sim (D : G.Sampler) {δ Γ : G.Stmt × G.Wit → ℝ≥0∞}
    (hZK : ∀ xw ∈ G.gen.support, G.AttHVZKAt D xw (δ xw))
    (hΓ : ∀ xw ∈ G.gen.support, G.AttKeyBoundAt D xw (Γ xw)) {qH qS : ℕ}
    (A : G.Adversary qH qS) :
    attAdvantage D A ≤ simAdvantage A +
      ∑' xw, G.gen xw * (qS * δ xw + ((qS * (qH + G.V + G.μ * qS) : ℕ) : ℝ≥0∞) * Γ xw) := by
  unfold attAdvantage simAdvantage attGame simGame
  rw [prTrue_gameDist, prTrue_gameDist, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun xw => ?_
  rw [← mul_add]
  by_cases hxw : xw ∈ G.gen.support
  · have hB := isQueryBound₂_withVerify xw.1 _ qH qS (A.isQueryBound xw.1)
    refine mul_le_mul_right ?_ _
    refine (run_att_wins_le_stat D xw (hZK xw hxw) _ (qH + G.V) qS hB _ _).trans ?_
    rw [add_assoc]
    refine add_le_add le_rfl (add_le_add le_rfl ?_)
    refine (run_att_flag_le D xw (hΓ xw hxw) _ (qH + G.V) qS hB Protocol.Tables.empty rfl).trans
      (le_of_eq ?_)
    simp [Protocol.Tables.empty]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hxw]

end AttSim

end CatCrypt.Crypto.FiatShamirROM
