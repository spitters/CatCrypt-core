/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.StraightLineCls
public import CatCryptCore.ForMathlib.PMFSupport

/-!
# Fiat–Shamir in the random-oracle model: eager evaluation of marker points

A family of markers for key classes `κ` designates some oracle points, all of one
class `desCls`. A hash query at an undefined designated point `k` first evaluates the
markers in order: marker `i` is at the point `pt k look i` read against the lookup
`look` after the markers before `i`, in the class `cls i`; it keeps its recorded value
or takes a fresh uniform value recorded in `hash`. Then the query is answered. No
programmed entry of a simulated attempt has a marker class, and the evaluated
simulator points of one attempt with a marker class are distinct.

Evaluating an undefined point of a marker class early does not change the
distribution of the simulated game, up to the values of that point: the simulated
oracle commutes with filling the point by a uniform value. Since a filled oracle
accepts every forgery the unfilled one accepts, the marker game wins at least as
often as the simulated game.

## Main definitions

* `Protocol.Markers κ` — designated points and markers evaluated before them
* `Protocol.Markers.nmc` — the number of markers of a class
* `Protocol.Markers.none` — the family without designated points and markers
* `simStepMk M x` — the simulated oracle with the markers evaluated before every
  fresh designated hash query

## Main results

* `uniform_bind_update_sel` — resampling a coordinate selected by the vector itself
  leaves a uniform vector uniform, when the selection is stable under the resampling
* `run_eager_of_step` — an oracle that commutes with filling a point commutes with
  filling it after a whole run
* `simStep_abs`, `simStepMk_abs` — the simulated and marker oracles factor through the
  lookup, the signed messages and the flag
* `aStep_eager` — one call of the simulated oracle on lookups commutes with filling an
  undefined point at which no programmed entry lies and which is the simulator point of
  at most one entry of an attempt
* `awins_le_eager`, `awins_le_aMark` — filling such a point, or evaluating the markers,
  before a run does not decrease the probability of winning
* `sim_wins_le_simMk` — winning the simulated game has probability at most winning
  the marker game, for every adversary and initial state
* `sim_wins_le_simMk_game` — the same bound for the run with the verifier's queries
  from the empty tables
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open scoped ENNReal

open Protocol

namespace Protocol

variable {G : Protocol}

/-- **Markers** for the key classes `κ`. The designated points `des` are all of the
class `desCls`. Before a fresh designated point `k`, the `nm` markers are evaluated
in order: marker `i` is at the point `pt k look i`, read against the lookup `look`
after the markers before `i`, in the class `cls i ≠ desCls`. No programmed entry of
a simulated attempt has a marker class, and two evaluated simulator points of one
attempt that coincide at a point of a marker class belong to the same entry. -/
structure Markers (κ : G.Classes) where
  /-- The designated points. -/
  des : G.Key → Bool
  /-- The class of the designated points. -/
  desCls : κ.ι
  /-- Every designated point is in the class `desCls`. -/
  des_cls : ∀ k, des k = true → κ.cls k = desCls
  /-- The number of markers. -/
  nm : ℕ
  /-- The point of marker `i` before the designated point `k`, from the lookup after
  the markers before `i`. -/
  pt : G.Key → (G.Key → Option G.Ch) → Fin nm → G.Key
  /-- The class of marker `i`. -/
  cls : Fin nm → κ.ι
  /-- The point of marker `i` is in the class `cls i`. -/
  pt_cls : ∀ k look i, κ.cls (pt k look i) = cls i
  /-- No marker class is the class of the designated points. -/
  cls_ne : ∀ i, cls i ≠ desCls
  /-- No programmed entry of a simulated attempt has a marker class. -/
  prog_cls : ∀ (look : G.Key → Option G.Ch) x m e s, ∀ q ∈ (G.simTrace look x m e s).2.1,
    ∀ i, κ.cls q.1 ≠ cls i
  /-- The evaluated simulator points of one attempt with a marker class are distinct. -/
  sim_inj : ∀ x m s (v : Fin G.μ → G.Ch) (i j : Fin G.μ) (k : G.Key) (c : Fin nm),
    κ.cls k = cls c → G.simKey x m s v i = some k → G.simKey x m s v j = some k → i = j

namespace Markers

variable {κ : G.Classes}

/-- The number of markers of the class `c`. -/
def nmc (M : Markers κ) (c : κ.ι) : ℕ := (Finset.univ.filter fun i => M.cls i = c).card

/-- The family without designated points and without markers, with the class `c₀` of
designated points. -/
def none (c₀ : κ.ι) : Markers κ where
  des := fun _ => false
  desCls := c₀
  des_cls := fun _ h => absurd h (by simp)
  nm := 0
  pt := fun _ _ i => i.elim0
  cls := fun i => i.elim0
  pt_cls := fun _ _ i => i.elim0
  cls_ne := fun i => i.elim0
  prog_cls := fun _ _ _ _ _ _ _ i => i.elim0
  sim_inj := fun _ _ _ _ _ _ _ c => c.elim0

end Markers

end Protocol

/-! ## The marker game -/

section MarkerGame

variable {G : Protocol} {κ : G.Classes}

/-- The tables after the markers `l` before the designated point `k`: a marker at a
defined point keeps its value, a marker at an undefined point takes a fresh uniform
value recorded in `hash`. -/
noncomputable def markTables (M : Markers κ) (k : G.Key) : G.Tables → List (Fin M.nm) →
    PMF G.Tables
  | t, [] => PMF.pure t
  | t, i :: l =>
    match t.lookup (M.pt k t.lookup i) with
    | some _ => markTables M k t l
    | none => (PMF.uniformOfFintype G.Ch).bind fun v =>
      markTables M k { t with hash := t.hash ++ [(M.pt k t.lookup i, v)] } l

/-- A hash query of the marker game: `hashStep`, except that a fresh designated point
first evaluates the markers in order. -/
noncomputable def markHashStep (M : Markers κ) (t : G.Tables) (b : Bool) (k : G.Key) :
    Step G.Answer (G.Tables × Bool) G.Ch :=
  match t.lookup k with
  | some e => .plain (PMF.pure (.inl e, (t, b)))
  | none =>
    if M.des k then
      .plain ((markTables M k t (List.finRange M.nm)).bind fun t' =>
        (PMF.uniformOfFintype G.Ch).map fun e =>
          (.inl e, ({ t' with hash := t'.hash ++ [(k, e)] }, b)))
    else .fresh fun e => (.inl e, ({ t with hash := t.hash ++ [(k, e)] }, b))

/-- The simulated oracle for the statement `x` with the markers `M` evaluated before
every fresh designated hash query. -/
noncomputable def simStepMk (M : Markers κ) (x : G.Stmt) (s : G.Tables × Bool) :
    G.Query → Step G.Answer (G.Tables × Bool) G.Ch
  | .inl k => markHashStep M s.1 s.2 k
  | .inr m => .plain (sampleVec G (simSignOut x s.1 s.2 m))

end MarkerGame

/-! ## Eager sampling of one point -/

section Eager

/-- **Resampling a selected coordinate.** If the coordinate `sel e` selected by a
vector `e` stays selected when it is resampled, resampling it leaves a uniform vector
uniform. -/
theorem uniform_bind_update_sel {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C]
    [Nonempty C] (sel : (ι → C) → Option ι)
    (hsel : ∀ e i c, sel e = some i → sel (Function.update e i c) = some i) :
    (PMF.uniformOfFintype (ι → C)).bind (fun e => (PMF.uniformOfFintype C).map fun c =>
      match sel e with
      | none => e
      | some i => Function.update e i c) = PMF.uniformOfFintype (ι → C) := by
  have hback : ∀ e i c, sel (Function.update e i c) = some i → sel e = some i := by
    intro e i c h
    have := hsel _ i (e i) h
    rwa [Function.update_idem, Function.update_eq_self] at this
  ext f
  rw [PMF.bind_apply]
  cases hf : sel f with
  | none =>
    rw [tsum_eq_single f]
    · simp only [PMF.map_apply, hf]
      simp only [if_true, PMF.tsum_coe, mul_one]
    · intro e hne
      rw [PMF.map_apply, ENNReal.tsum_eq_zero.2, mul_zero]
      intro c
      rw [if_neg]
      cases he : sel e with
      | none => exact hne.symm
      | some i =>
        rintro rfl
        rw [hsel e i c he] at hf
        exact absurd hf (by simp)
  | some i =>
    conv_rhs => rw [← Constructions.ECBCPRF.uniform_bind_update i, PMF.bind_apply]
    refine tsum_congr fun e => congrArg _ ?_
    simp only [PMF.map_apply]
    refine tsum_congr fun c => ?_
    have hiff : (f = match sel e with
        | none => e
        | some i => Function.update e i c) ↔ f = Function.update e i c := by
      cases he : sel e with
      | none =>
        constructor
        · rintro rfl
          rw [he] at hf
          exact absurd hf (by simp)
        · rintro rfl
          rw [hback e i c hf] at he
          exact absurd he (by simp)
      | some j =>
        by_cases hij : j = i
        · subst hij; exact Iff.rfl
        · constructor
          · rintro rfl
            rw [hsel e j c he] at hf
            exact absurd (Option.some_inj.1 hf) hij
          · rintro rfl
            rw [hback e i c hf] at he
            exact absurd (Option.some_inj.1 he).symm hij
    split_ifs <;> simp_all

/-- An event that holds after every outcome of `f y` when it holds at `y` has at least
the probability under `p.bind f` that it has under `p`. -/
theorem toOuterMeasure_le_bind {α : Type} (p : PMF α) (f : α → PMF α) (W : α → Bool)
    (hW : ∀ y, W y = true → ∀ z ∈ (f y).support, W z = true) :
    p.toOuterMeasure {y | W y = true} ≤ (p.bind f).toOuterMeasure {y | W y = true} := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : W a = true
  · rw [Set.indicator_of_mem (by exact ha), show (f a).toOuterMeasure {y | W y = true} = 1 from
      (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 fun z hz => hW a ha z hz, mul_one]
  · rw [Set.indicator_of_notMem (by exact ha)]
    exact zero_le

variable {D R α S V : Type}

/-- Filling the point after an outcome: when it is undefined in the state, by a value
of `U`. -/
noncomputable def fillAt (U : PMF V) (undef : S → Bool) (upd : S → V → S) (y : R × S) :
    PMF (R × S) :=
  if undef y.2 then U.map fun v => (y.1, upd y.2 v) else PMF.pure y

theorem run_defined (O : S → D → PMF (R × S)) (undef : S → Bool)
    (hpers : ∀ s d, undef s = false → ∀ y ∈ (O s d).support, undef y.2 = false)
    (A : OracleAdv D R α) (s : S) (hs : undef s = false) :
    ∀ y ∈ (OracleAdv.run O A s).support, undef y.2 = false := by
  induction A generalizing s with
  | ret a =>
    intro y hy
    simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    rw [hy]; exact hs
  | rand p k ih =>
    intro y hy
    obtain ⟨b, -, hb⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    exact ih b s hs y hb
  | query d k ih =>
    intro y hy
    obtain ⟨z, hz, hz'⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    exact ih z.1 z.2 (hpers s d hs z hz) y hz'

/-- **Eager sampling of one point.** Let an oracle commute with filling a point by a
value of `U` at every state where the point is undefined, and keep the point defined
once it is. A run from a state with the point filled by a value of `U` is the run from
the unfilled state followed by filling the point when it is still undefined. -/
theorem run_eager_of_step (O : S → D → PMF (R × S)) (U : PMF V) (undef : S → Bool)
    (upd : S → V → S)
    (hpers : ∀ s d, undef s = false → ∀ y ∈ (O s d).support, undef y.2 = false)
    (hstep : ∀ s d, undef s = true →
      U.bind (fun v => O (upd s v) d) = (O s d).bind (fillAt U undef upd))
    (A : OracleAdv D R α) (s : S) (hs : undef s = true) :
    U.bind (fun v => OracleAdv.run O A (upd s v)) =
      (OracleAdv.run O A s).bind (fun y => fillAt U undef upd y) := by
  have hdef : ∀ (B : OracleAdv D R α) s', undef s' = false →
      (OracleAdv.run O B s').bind (fun y => fillAt U undef upd y) = OracleAdv.run O B s' := by
    intro B s' hs'
    rw [PMF.bind_congr_support _ _ PMF.pure fun y hy => by
      rw [fillAt, run_defined O undef hpers B s' hs' y hy, if_neg (by simp)], PMF.bind_pure]
  induction A generalizing s with
  | ret a =>
    simp only [OracleAdv.run_ret, PMF.pure_bind, fillAt, hs, if_true]
    rfl
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.bind_bind]
    rw [PMF.bind_comm]
    exact congrArg _ (funext fun b => ih b s hs)
  | query d k ih =>
    simp only [OracleAdv.run_query]
    rw [← PMF.bind_bind, hstep s d hs, PMF.bind_bind, PMF.bind_bind]
    refine PMF.bind_congr_support _ _ _ fun y _ => ?_
    unfold fillAt
    by_cases hy : undef y.2 = true
    · rw [if_pos hy, PMF.bind_map]
      exact ih y.1 y.2 hy
    · rw [if_neg hy, PMF.pure_bind]
      exact (hdef _ _ (by simpa using hy)).symm

end Eager

/-! ## Lookups of lists of entries -/

section Lists

variable {K C : Type} [DecidableEq K]

theorem lookupIn_cons (p : K × C) (l : List (K × C)) (k : K) :
    lookupIn (p :: l) k = if p.1 = k then some p.2 else lookupIn l k := by
  unfold lookupIn findKey
  rw [List.findIdx?_cons]
  by_cases h : p.1 = k
  · simp [h]
  · simp only [h, decide_false, if_false]
    cases l.findIdx? (fun p => decide (p.1 = k)) <;> simp

theorem lookupIn_append (l l' : List (K × C)) (k : K) :
    lookupIn (l ++ l') k = (lookupIn l k).or (lookupIn l' k) := by
  induction l with
  | nil => simp [lookupIn_nil]
  | cons p l ih =>
    rw [List.cons_append, lookupIn_cons, lookupIn_cons, ih]
    split <;> simp

theorem lookupIn_filter (P : K → Bool) (l : List (K × C)) (k : K) :
    lookupIn (l.filter fun p => P p.1) k = if P k then lookupIn l k else none := by
  induction l with
  | nil => simp [lookupIn_nil]
  | cons p l ih =>
    rw [List.filter_cons]
    by_cases hp : P p.1
    · rw [if_pos hp, lookupIn_cons, lookupIn_cons, ih]
      by_cases hk : p.1 = k
      · subst hk; simp [hp]
      · simp [hk]
    · rw [if_neg hp, ih, lookupIn_cons]
      by_cases hk : p.1 = k
      · subst hk; simp [hp]
      · simp [hk]

end Lists

/-! ## The simulated game on lookups -/

section Abstract

variable {G : Protocol}

variable (G) in
/-- The state of the simulated game seen through its lookup: the visible oracle, the
signed messages and the flag. -/
abbrev AState := (G.Key → Option G.Ch) × List G.Msg × Bool

/-- The lookup `L` with the entries of `l` at points undefined in `L`. -/
def hashL (L : G.Key → Option G.Ch) (l : List (G.Key × G.Ch)) : G.Key → Option G.Ch :=
  fun k => (L k).or (lookupIn l k)

/-- Programming the entries `l` in order into the lookup `L`: an entry at a defined
point sets the flag, the others are recorded. -/
def progL : (G.Key → Option G.Ch) → Bool → List (G.Key × G.Ch) →
    (G.Key → Option G.Ch) × Bool
  | L, b, [] => (L, b)
  | L, b, p :: l =>
    match L p.1 with
    | some _ => progL L true l
    | none => progL (Function.update L p.1 (some p.2)) b l

/-- The simulated signing oracle on lookups. -/
def aSignOut (x : G.Stmt) (L : G.Key → Option G.Ch) (sg : List G.Msg) (b : Bool) (m : G.Msg)
    (e : Fin G.μ → G.Ch) (s : G.SimRand) : G.Answer × AState G :=
  (.inr (G.simTrace L x m e s).2.2,
    ((progL (hashL L (G.simTrace L x m e s).1) b (G.simTrace L x m e s).2.1).1, sg ++ [m],
      (progL (hashL L (G.simTrace L x m e s).1) b (G.simTrace L x m e s).2.1).2))

/-- A hash query on lookups. -/
noncomputable def aHash (σ : AState G) (k : G.Key) : PMF (G.Answer × AState G) :=
  match σ.1 k with
  | some e => PMF.pure (.inl e, σ)
  | none => (PMF.uniformOfFintype G.Ch).map fun e =>
    (.inl e, (Function.update σ.1 k (some e), σ.2))

/-- The simulated oracle on lookups. -/
noncomputable def aStep (x : G.Stmt) (σ : AState G) : G.Query → PMF (G.Answer × AState G)
  | .inl k => aHash σ k
  | .inr m => sampleVec G (aSignOut x σ.1 σ.2.1 σ.2.2 m)

/-- The lookup, signed messages and flag of a state. -/
def absT (s : G.Tables × Bool) : AState G := (s.1.lookup, s.1.signed, s.2)

/-- The winning condition on lookups. -/
def awins (x : G.Stmt) (y : G.Forgery × AState G) : Bool :=
  !(y.2.2.1.contains y.1.1) &&
    match verifyVals y.2.1 x y.1.1 y.1.2 G.V [] with
    | some vs => G.verify x y.1.1 y.1.2 vs
    | none => false

theorem wins_eq_awins (x : G.Stmt) (y : G.Forgery × (G.Tables × Bool)) :
    wins x y = awins x (Prod.map id absT y) := rfl

theorem lookup_hashAll (t : G.Tables) (l : List (G.Key × G.Ch)) :
    (hashAll t l).lookup = hashL t.lookup l := by
  funext k
  have hf := lookupIn_filter (fun k => (t.lookup k).isNone) l k
  simp only [Tables.lookup, hashAll, hashL, lookupIn_append] at hf ⊢
  rw [hf]
  clear hf
  by_cases h : ((lookupIn t.prog k).or (lookupIn t.hash k)).isNone = true <;>
    simp only [h, if_true] <;> cases h1 : lookupIn t.prog k <;> cases h2 : lookupIn t.hash k <;>
    simp_all

theorem lookup_snoc_hash (t : G.Tables) (k : G.Key) (e : G.Ch) (h : t.lookup k = none) :
    ({ t with hash := t.hash ++ [(k, e)] } : G.Tables).lookup =
      Function.update t.lookup k (some e) := by
  funext k'
  simp only [Tables.lookup] at h ⊢
  rw [lookupIn_append, lookupIn_cons, lookupIn_nil]
  by_cases hk : k' = k
  · subst hk
    simp only [Option.or_eq_none_iff] at h
    simp [h.1, h.2]
  · simp [Function.update_of_ne hk, Ne.symm hk, Tables.lookup]

theorem lookup_snoc_prog (t : G.Tables) (p : G.Key × G.Ch) (h : t.lookup p.1 = none) :
    ({ t with prog := t.prog ++ [p] } : G.Tables).lookup =
      Function.update t.lookup p.1 (some p.2) := by
  funext k'
  simp only [Tables.lookup] at h ⊢
  rw [lookupIn_append, lookupIn_cons, lookupIn_nil]
  by_cases hk : k' = p.1
  · subst hk
    simp only [Option.or_eq_none_iff] at h
    simp [h.1, h.2]
  · simp [Function.update_of_ne hk, Ne.symm hk, Tables.lookup]

theorem programAll_abs (t : G.Tables) (b : Bool) (l : List (G.Key × G.Ch)) :
    (programAll t b l).1.lookup = (progL t.lookup b l).1 ∧
      (programAll t b l).1.signed = t.signed ∧ (programAll t b l).2 = (progL t.lookup b l).2 := by
  induction l generalizing t b with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons p l ih =>
    simp only [programAll, progL]
    cases h : t.lookup p.1 with
    | some _ => exact ih t true
    | none =>
      have := ih { t with prog := t.prog ++ [p] } b
      rwa [lookup_snoc_prog t p h] at this

theorem simStep_abs (x : G.Stmt) (s : G.Tables × Bool) (d : G.Query) :
    (toOracle (simStep x) s d).map (Prod.map id absT) = aStep x (absT s) d := by
  rcases d with k | m
  · simp only [toOracle, simStep, hashStep, aStep, aHash, absT]
    cases h : s.1.lookup k with
    | some e => simp only [Step.toPMF, PMF.pure_map]; rfl
    | none =>
      simp only [Step.toPMF, PMF.map_comp]
      congr 1
      funext e
      simp only [Function.comp, Prod.map, absT, id]
      rw [lookup_snoc_hash _ _ _ h]
  · simp only [toOracle, simStep, aStep, Step.toPMF, sampleVec, PMF.map_bind, PMF.map_comp]
    congr 1; funext e; congr 1; funext r
    obtain ⟨h1, h2, h3⟩ := programAll_abs (hashAll s.1 (G.simTrace s.1.lookup x m e r).1) s.2
      (G.simTrace s.1.lookup x m e r).2.1
    rw [lookup_hashAll] at h1 h3
    simp only [Function.comp, simSignOut, traceOut, programOut, aSignOut, absT, Prod.map, id]
    exact Prod.ext rfl (Prod.ext h1 (Prod.ext rfl h3))

variable {κ : G.Classes}

/-- The lookup after the markers `l` before the designated point `k`. -/
noncomputable def aMark (M : Markers κ) (k : G.Key) : (G.Key → Option G.Ch) → List (Fin M.nm) →
    PMF (G.Key → Option G.Ch)
  | L, [] => PMF.pure L
  | L, i :: l =>
    match L (M.pt k L i) with
    | some _ => aMark M k L l
    | none => (PMF.uniformOfFintype G.Ch).bind fun v =>
      aMark M k (Function.update L (M.pt k L i) (some v)) l

/-- A hash query of the marker game on lookups. -/
noncomputable def aHashMk (M : Markers κ) (σ : AState G) (k : G.Key) :
    PMF (G.Answer × AState G) :=
  match σ.1 k with
  | some e => PMF.pure (.inl e, σ)
  | none =>
    if M.des k then
      (aMark M k σ.1 (List.finRange M.nm)).bind fun L =>
        (PMF.uniformOfFintype G.Ch).map fun e => (.inl e, (Function.update L k (some e), σ.2))
    else (PMF.uniformOfFintype G.Ch).map fun e => (.inl e, (Function.update σ.1 k (some e), σ.2))

/-- The marker game oracle on lookups. -/
noncomputable def aStepMk (M : Markers κ) (x : G.Stmt) (σ : AState G) :
    G.Query → PMF (G.Answer × AState G)
  | .inl k => aHashMk M σ k
  | .inr m => sampleVec G (aSignOut x σ.1 σ.2.1 σ.2.2 m)

theorem markTables_abs (M : Markers κ) (k : G.Key) (l : List (Fin M.nm)) (t : G.Tables) :
    (markTables M k t l).map (fun t' => (t'.lookup, t'.signed)) =
      (aMark M k t.lookup l).map fun L => (L, t.signed) := by
  induction l generalizing t with
  | nil => simp [markTables, aMark, PMF.pure_map]
  | cons i l ih =>
    simp only [markTables, aMark]
    cases h : t.lookup (M.pt k t.lookup i) with
    | some _ => exact ih t
    | none =>
      simp only [PMF.map_bind]
      congr 1
      funext v
      rw [ih, lookup_snoc_hash _ _ _ h]

theorem markTables_lookup_des (M : Markers κ) {k : G.Key} (hk : M.des k = true)
    (l : List (Fin M.nm)) (t : G.Tables) (t' : G.Tables) (ht' : t' ∈ (markTables M k t l).support) :
    t'.lookup k = t.lookup k := by
  induction l generalizing t with
  | nil =>
    simp only [markTables, PMF.support_pure, Set.mem_singleton_iff] at ht'
    rw [ht']
  | cons i l ih =>
    simp only [markTables] at ht'
    cases h : t.lookup (M.pt k t.lookup i) with
    | some _ => rw [h] at ht'; exact ih t ht'
    | none =>
      rw [h] at ht'
      obtain ⟨v, -, hv⟩ := (PMF.mem_support_bind_iff _ _ _).1 ht'
      rw [ih _ hv, lookup_snoc_hash _ _ _ h, Function.update_of_ne]
      intro he
      have := M.pt_cls k t.lookup i
      rw [← he, M.des_cls k hk] at this
      exact M.cls_ne i this.symm

theorem simStepMk_abs (M : Markers κ) (x : G.Stmt) (s : G.Tables × Bool) (d : G.Query) :
    (toOracle (simStepMk M x) s d).map (Prod.map id absT) = aStepMk M x (absT s) d := by
  rcases d with k | m
  · simp only [toOracle, simStepMk, markHashStep, aStepMk, aHashMk]
    cases h : s.1.lookup k with
    | some e =>
      have hs : (absT s).1 k = some e := h
      rw [hs]
      simp only [Step.toPMF, PMF.pure_map]
      rfl
    | none =>
      have hs : (absT s).1 k = none := h
      rw [hs]
      dsimp only
      by_cases hd : M.des k = true
      · simp only [hd, if_true, Step.toPMF, PMF.map_bind]
        rw [PMF.bind_congr_support _ _ (fun t' => (PMF.uniformOfFintype G.Ch).map fun e =>
            (.inl e, (Function.update t'.lookup k (some e), t'.signed, s.2))) fun t' ht' => by
          rw [PMF.map_comp]
          congr 1
          funext e
          simp only [Function.comp, Prod.map, absT, id]
          rw [lookup_snoc_hash _ _ _ ((markTables_lookup_des M hd _ _ _ ht').trans h)]]
        have hm := markTables_abs M k (List.finRange M.nm) s.1
        rw [show (fun t' : G.Tables => (PMF.uniformOfFintype G.Ch).map fun e =>
            ((.inl e, (Function.update t'.lookup k (some e), t'.signed, s.2)) :
              G.Answer × AState G)) =
            (fun q : (G.Key → Option G.Ch) × List G.Msg => (PMF.uniformOfFintype G.Ch).map
              fun e => (.inl e, (Function.update q.1 k (some e), q.2, s.2))) ∘
              (fun t' : G.Tables => (t'.lookup, t'.signed)) from rfl,
          ← PMF.bind_map, hm, PMF.bind_map]
        rfl
      · rw [if_neg hd, if_neg hd]
        have := simStep_abs x s (.inl k)
        simp only [toOracle, simStep, hashStep, aStep, aHash, h, hs] at this
        exact this
  · exact simStep_abs x s (.inr m)

end Abstract

/-! ## A simulated attempt against a lookup filled at one point -/

section OneStep

variable {G : Protocol}

theorem lookupIn_eq_some_of_forall {K C : Type} [DecidableEq K] (l : List (K × C)) (p : K)
    (c : C) (h : ∀ q ∈ l, q.1 = p → q.2 = c) (hm : p ∈ l.map Prod.fst) :
    lookupIn l p = some c := by
  induction l with
  | nil => simp at hm
  | cons q l ih =>
    rw [lookupIn_cons]
    by_cases hq : q.1 = p
    · rw [if_pos hq, h q List.mem_cons_self hq]
    · rw [if_neg hq]
      refine ih (fun q' hq' => h q' (List.mem_cons_of_mem _ hq')) ?_
      simp only [List.map_cons, List.mem_cons] at hm
      exact hm.resolve_left (Ne.symm hq)

theorem progL_update (L : G.Key → Option G.Ch) (b : Bool) (l : List (G.Key × G.Ch)) (p : G.Key)
    (v : G.Ch) (hp : p ∉ l.map Prod.fst) :
    progL (Function.update L p (some v)) b l =
      (Function.update (progL L b l).1 p (some v), (progL L b l).2) := by
  induction l generalizing L b with
  | nil => rfl
  | cons q l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hp
    simp only [progL, Function.update_of_ne (Ne.symm hp.1)]
    cases L q.1 with
    | some _ => exact ih L true hp.2
    | none =>
      rw [Function.update_comm hp.1, ih _ b hp.2]

theorem progL_apply_of_notMem (L : G.Key → Option G.Ch) (b : Bool) (l : List (G.Key × G.Ch))
    (p : G.Key) (hp : p ∉ l.map Prod.fst) : (progL L b l).1 p = L p := by
  induction l generalizing L b with
  | nil => rfl
  | cons q l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hp
    simp only [progL]
    cases L q.1 with
    | some _ => exact ih L true hp.2
    | none => rw [ih _ b hp.2, Function.update_of_ne hp.1]

theorem progL_apply_of_some (L : G.Key → Option G.Ch) (b : Bool) (l : List (G.Key × G.Ch))
    (q : G.Key) (c : G.Ch) (hq : L q = some c) : (progL L b l).1 q = some c := by
  induction l generalizing L b with
  | nil => exact hq
  | cons r l ih =>
    simp only [progL]
    cases hr : L r.1 with
    | some _ => exact ih L true hq
    | none =>
      refine ih _ b ?_
      rw [Function.update_of_ne]
      · exact hq
      · rintro rfl; rw [hq] at hr; exact absurd hr (by simp)

variable {x : G.Stmt} {m : G.Msg} {s : G.SimRand}

/-- The values of a simulated attempt are the only solution of their defining
equations. -/
theorem simVals_eq_of_fix (look : G.Key → Option G.Ch) (e u : Fin G.μ → G.Ch)
    (hu : ∀ i, u i = ((G.simKey x m s u i).bind look).getD (e i)) :
    u = G.simVals look x m s e := by
  have hprog : ∀ j, G.ev j = false → u j = G.simVals look x m s e j := by
    intro j hj
    rw [hu j, simKey_eq_none_of_ev_false x m s _ hj, simVals_apply_of_ev_false look x m s e hj]
    rfl
  funext i
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    rw [hu i, simVals_apply look x m s e i]
    congr 2
    refine G.simKey_causal x m s _ _ i fun j hj => ?_
    rcases hj with hj | hj
    · exact ih j hj
    · exact hprog j hj

/-- The first entry of the simulated attempt against `L` with the simulator point
`p`. -/
def selP (L : G.Key → Option G.Ch) (x : G.Stmt) (m : G.Msg) (s : G.SimRand) (p : G.Key)
    (e : Fin G.μ → G.Ch) : Option (Fin G.μ) :=
  (List.finRange G.μ).find? fun i => decide (G.simKey x m s (G.simVals L x m s e) i = some p)

variable {L : G.Key → Option G.Ch} {p : G.Key}

theorem selP_none {e : Fin G.μ → G.Ch} (h : selP L x m s p e = none) (i : Fin G.μ) :
    G.simKey x m s (G.simVals L x m s e) i ≠ some p := by
  have := List.find?_eq_none.1 h i (List.mem_finRange i)
  simpa using this

theorem selP_some_iff
    (hinj : ∀ (v : Fin G.μ → G.Ch) i j, G.simKey x m s v i = some p →
      G.simKey x m s v j = some p → i = j) (e : Fin G.μ → G.Ch) (i : Fin G.μ) :
    selP L x m s p e = some i ↔ G.simKey x m s (G.simVals L x m s e) i = some p := by
  constructor
  · intro h
    simpa using List.find?_some h
  · intro h
    cases hs : selP L x m s p e with
    | none => exact absurd h (selP_none hs i)
    | some j =>
      have hj : G.simKey x m s (G.simVals L x m s e) j = some p := by
        simpa using List.find?_some hs
      rw [hinj _ j i hj h]

theorem selP_update
    (hinj : ∀ (v : Fin G.μ → G.Ch) i j, G.simKey x m s v i = some p →
      G.simKey x m s v j = some p → i = j) (e : Fin G.μ → G.Ch) (i : Fin G.μ) (c : G.Ch)
    (h : selP L x m s p e = some i) : selP L x m s p (Function.update e i c) = some i := by
  rw [selP_some_iff hinj] at h ⊢
  have hev := G.simKey_ev x m s _ i (by rw [h]; rfl)
  rw [simKey_update hev e c i le_rfl, h]

theorem simVals_update_look_none {e : Fin G.μ → G.Ch} (h : selP L x m s p e = none) (v : G.Ch) :
    G.simVals (Function.update L p (some v)) x m s e = G.simVals L x m s e := by
  refine (simVals_eq_of_fix _ e _ fun i => ?_).symm
  rw [simVals_apply L x m s e i]
  have hne := selP_none h i
  cases hk : G.simKey x m s (G.simVals L x m s e) i with
  | none => rfl
  | some q =>
    have hq : q ≠ p := fun hq => hne (by rw [hk, hq])
    simp only [Option.bind_some, Function.update_of_ne hq]

theorem simVals_update_look_some
    (hinj : ∀ (v : Fin G.μ → G.Ch) i j, G.simKey x m s v i = some p →
      G.simKey x m s v j = some p → i = j) (hL : L p = none) {e : Fin G.μ → G.Ch} {i : Fin G.μ}
    (h : selP L x m s p e = some i) (v : G.Ch) :
    G.simVals (Function.update L p (some v)) x m s e = G.simVals L x m s (Function.update e i v) := by
  have hk := (selP_some_iff hinj e i).1 h
  have hev := G.simKey_ev x m s _ i (by rw [hk]; rfl)
  set u := G.simVals L x m s (Function.update e i v) with hu
  have hki : G.simKey x m s u i = some p := by rw [hu, simKey_update hev e v i le_rfl, hk]
  have hui : u i = v := by
    rw [hu, simVals_apply L x m s _ i, ← hu, hki]
    simp [hL]
  refine (simVals_eq_of_fix _ e u fun j => ?_).symm
  by_cases hji : j = i
  · subst hji
    rw [hki, hui]
    simp
  · conv_lhs => rw [hu, simVals_apply L x m s _ j, ← hu, Function.update_of_ne hji]
    cases hkj : G.simKey x m s u j with
    | none => rfl
    | some q =>
      have hq : q ≠ p := by
        rintro rfl
        exact hji (hinj u j i hkj hki)
      simp only [Option.bind_some, Function.update_of_ne hq]

theorem lookupIn_simTrace
    (hinj : ∀ (v : Fin G.μ → G.Ch) i j, G.simKey x m s v i = some p →
      G.simKey x m s v j = some p → i = j) {e : Fin G.μ → G.Ch} {i : Fin G.μ}
    (hk : G.simKey x m s (G.simVals L x m s e) i = some p) :
    lookupIn (G.simTrace L x m e s).1 p = some (G.simVals L x m s e i) := by
  refine lookupIn_eq_some_of_forall _ _ _ (fun q hq hqp => ?_) ?_
  · obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 hq
    obtain ⟨k, hkj, rfl⟩ := Option.map_eq_some_iff.1 hj
    simp only at hqp
    subst hqp
    rw [hinj _ j i hkj hk]
  · exact List.mem_map.2 ⟨(p, G.simVals L x m s e i),
      List.mem_filterMap.2 ⟨i, List.mem_finRange i, by simp [hk]⟩, rfl⟩

theorem notMem_simTrace_of_selP_none {e : Fin G.μ → G.Ch} (h : selP L x m s p e = none) :
    p ∉ (G.simTrace L x m e s).1.map Prod.fst := by
  intro hm
  obtain ⟨q, hq, hqp⟩ := List.mem_map.1 hm
  obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 hq
  obtain ⟨k, hkj, rfl⟩ := Option.map_eq_some_iff.1 hj
  simp only at hqp
  subst hqp
  exact selP_none h j hkj

theorem hashL_update (L : G.Key → Option G.Ch) (l : List (G.Key × G.Ch)) (p : G.Key) (v : G.Ch) :
    hashL (Function.update L p (some v)) l = Function.update (hashL L l) p (some v) := by
  funext k
  by_cases hk : k = p
  · subst hk; simp [hashL]
  · simp [hashL, Function.update_of_ne hk]

theorem aSignOut_of_selP_none (sg : List G.Msg) (b : Bool) {e : Fin G.μ → G.Ch}
    (hprog : ∀ q ∈ (G.simTrace L x m e s).2.1, q.1 ≠ p) (hL : L p = none)
    (h : selP L x m s p e = none) (v : G.Ch) :
    aSignOut x (Function.update L p (some v)) sg b m e s =
      ((aSignOut x L sg b m e s).1, (Function.update (aSignOut x L sg b m e s).2.1 p (some v),
        (aSignOut x L sg b m e s).2.2)) ∧ (aSignOut x L sg b m e s).2.1 p = none := by
  have htr : G.simTrace (Function.update L p (some v)) x m e s = G.simTrace L x m e s := by
    simp only [Protocol.simTrace, simVals_update_look_none h v]
  have h2 : p ∉ (G.simTrace L x m e s).2.1.map Prod.fst := by
    intro hm
    obtain ⟨q, hq, hqp⟩ := List.mem_map.1 hm
    exact hprog q hq hqp
  have h1 := notMem_simTrace_of_selP_none (s := s) h
  unfold aSignOut
  rw [htr, hashL_update, progL_update _ _ _ _ _ h2]
  refine ⟨rfl, ?_⟩
  simp only
  rw [progL_apply_of_notMem _ _ _ _ h2, hashL, hL, lookupIn_eq_none_of_notMem h1]
  rfl

theorem aSignOut_of_selP_some
    (hinj : ∀ (v : Fin G.μ → G.Ch) i j, G.simKey x m s v i = some p →
      G.simKey x m s v j = some p → i = j) (hL : L p = none) (sg : List G.Msg) (b : Bool)
    {e : Fin G.μ → G.Ch} {i : Fin G.μ} (h : selP L x m s p e = some i) (v : G.Ch) :
    aSignOut x (Function.update L p (some v)) sg b m e s =
      aSignOut x L sg b m (Function.update e i v) s := by
  have htr : G.simTrace (Function.update L p (some v)) x m e s =
      G.simTrace L x m (Function.update e i v) s := by
    simp only [Protocol.simTrace, simVals_update_look_some hinj hL h v]
  have hk : G.simKey x m s (G.simVals L x m s (Function.update e i v)) i = some p :=
    (selP_some_iff hinj _ i).1 (selP_update hinj e i v h)
  have hv : G.simVals L x m s (Function.update e i v) i = v := by
    rw [simVals_apply L x m s _ i, hk]
    simp [hL]
  have hh : hashL (Function.update L p (some v)) (G.simTrace L x m (Function.update e i v) s).1 =
      hashL L (G.simTrace L x m (Function.update e i v) s).1 := by
    funext k
    by_cases hkp : k = p
    · subst hkp
      simp only [hashL, Function.update_self, hL, Option.some_or, Option.none_or]
      rw [lookupIn_simTrace hinj hk, hv]
    · simp [hashL, Function.update_of_ne hkp]
  unfold aSignOut
  rw [htr, hh]

theorem aSignOut_defined_of_selP_some
    (hinj : ∀ (v : Fin G.μ → G.Ch) i j, G.simKey x m s v i = some p →
      G.simKey x m s v j = some p → i = j) (sg : List G.Msg) (b : Bool)
    {e : Fin G.μ → G.Ch} {i : Fin G.μ} (h : selP L x m s p e = some i) :
    ((aSignOut x L sg b m e s).2.1 p).isSome = true := by
  have hk := (selP_some_iff hinj e i).1 h
  have hc : hashL L (G.simTrace L x m e s).1 p = (L p).or (some (G.simVals L x m s e i)) := by
    rw [hashL, lookupIn_simTrace hinj hk]
  obtain ⟨c, hc'⟩ : ∃ c, hashL L (G.simTrace L x m e s).1 p = some c := by
    rw [hc]; cases L p <;> simp
  unfold aSignOut
  rw [progL_apply_of_some _ _ _ _ _ hc']
  rfl

theorem aSignOut_defined (sg : List G.Msg) (b : Bool) (e : Fin G.μ → G.Ch) (q : G.Key)
    (hq : (L q).isSome = true) : ((aSignOut x L sg b m e s).2.1 q).isSome = true := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hq
  unfold aSignOut
  rw [progL_apply_of_some _ _ _ q c (by rw [hashL, hc]; rfl)]
  rfl

/-- The point `p` is undefined in the lookup of a state. -/
def undefP (p : G.Key) (σ : AState G) : Bool := (σ.1 p).isNone

/-- The state with the point `p` defined with the value `v`. -/
def updP (p : G.Key) (σ : AState G) (v : G.Ch) : AState G :=
  (Function.update σ.1 p (some v), σ.2)

theorem mem_support_sampleVec_iff {β γ : Type} [Fintype β] [Nonempty β]
    (F : (Fin G.μ → G.Ch) → β → γ) (y : γ) (hy : y ∈ (sampleVec G F).support) :
    ∃ e r, y = F e r := by
  obtain ⟨e, -, he⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
  obtain ⟨r, -, hr⟩ := (PMF.mem_support_map_iff _ _ _).1 he
  exact ⟨e, r, hr.symm⟩

/-- The simulated oracle on lookups keeps a defined point defined. -/
theorem aStep_defined (x : G.Stmt) (p : G.Key) (σ : AState G) (d : G.Query)
    (hσ : undefP p σ = false) (y : G.Answer × AState G) (hy : y ∈ (aStep x σ d).support) :
    undefP p y.2 = false := by
  have hσ' : (σ.1 p).isSome = true := by simpa [undefP] using hσ
  rcases d with k | m
  · simp only [aStep, aHash] at hy
    cases hk : σ.1 k with
    | some e =>
      rw [hk] at hy
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      rw [hy]; exact hσ
    | none =>
      rw [hk] at hy
      obtain ⟨e, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
      simp only [undefP]
      by_cases hkp : p = k
      · subst hkp; simp
      · rw [Function.update_of_ne hkp]; exact hσ
  · obtain ⟨e, r, rfl⟩ := mem_support_sampleVec_iff _ y hy
    simpa [undefP] using aSignOut_defined (x := x) (m := m) (s := r) σ.2.1 σ.2.2 e p hσ'

/-- **One step of eager sampling.** At a state where the point `p` is undefined, a
call of the simulated oracle on lookups with `p` filled by a uniform value is the call
without it followed by filling `p` when it is still undefined, when the simulator
points equal to `p` of one attempt belong to one entry and no programmed entry is at
`p`. -/
theorem aStep_eager (x : G.Stmt) (p : G.Key)
    (hinj : ∀ m s (v : Fin G.μ → G.Ch) i j, G.simKey x m s v i = some p →
      G.simKey x m s v j = some p → i = j)
    (hprog : ∀ (look : G.Key → Option G.Ch) m e s, ∀ q ∈ (G.simTrace look x m e s).2.1, q.1 ≠ p)
    (σ : AState G) (hσ : undefP p σ = true) (d : G.Query) :
    (PMF.uniformOfFintype G.Ch).bind (fun v => aStep x (updP p σ v) d) =
      (aStep x σ d).bind (fillAt (PMF.uniformOfFintype G.Ch) (undefP p) (updP p)) := by
  obtain ⟨L, sg, b⟩ := σ
  have hL : L p = none := by simpa [undefP] using hσ
  rcases d with k | m
  · simp only [aStep, aHash, updP]
    by_cases hkp : k = p
    · subst hkp
      simp only [Function.update_self, hL, PMF.bind_map]
      congr 1
      funext e
      simp [fillAt, undefP]
    · simp only [Function.update_of_ne hkp]
      cases hk : L k with
      | some e =>
        simp only [PMF.pure_bind, fillAt, undefP, hL, Option.isNone_none, if_true]
        rfl
      | none =>
        simp only [PMF.map, PMF.bind_bind, Function.comp, PMF.pure_bind]
        rw [PMF.bind_comm]
        congr 1
        funext e
        simp only [fillAt, undefP, Function.update_of_ne (Ne.symm hkp), hL,
          Option.isNone_none, if_true, updP, PMF.map]
        congr 1
        funext v
        simp only [Function.comp]
        rw [Function.update_comm (Ne.symm hkp)]
  · simp only [aStep, updP]
    have hsel : ∀ (r : G.SimRand) e i c, selP L x m r p e = some i →
        selP L x m r p (Function.update e i c) = some i :=
      fun r e i c h => selP_update (hinj m r) e i c h
    have hper : ∀ r : G.SimRand,
        (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind (fun e =>
          (PMF.uniformOfFintype G.Ch).map fun v =>
            aSignOut x (Function.update L p (some v)) sg b m e r) =
        (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind (fun e =>
          fillAt (PMF.uniformOfFintype G.Ch) (undefP p) (updP p) (aSignOut x L sg b m e r)) := by
      intro r
      conv_rhs => rw [← uniform_bind_update_sel _ (hsel r), PMF.bind_bind]
      congr 1
      funext e
      rw [PMF.bind_map]
      cases h : selP L x m r p e with
      | none =>
        have h2 := (aSignOut_of_selP_none (x := x) sg b (hprog L m e r) hL h
          (Classical.arbitrary G.Ch)).2
        simp only [Function.comp_def, PMF.bind_const, fillAt, undefP, h2, Option.isNone_none,
          if_true]
        congr 1
        funext v
        rw [(aSignOut_of_selP_none (x := x) sg b (hprog L m e r) hL h v).1]
        rfl
      | some i =>
        simp only [Function.comp_def]
        have hd : ∀ c, fillAt (PMF.uniformOfFintype G.Ch) (undefP p) (updP p)
            (aSignOut x L sg b m (Function.update e i c) r) =
            PMF.pure (aSignOut x L sg b m (Function.update e i c) r) := by
          intro c
          have := aSignOut_defined_of_selP_some (x := x) (m := m) (hinj m r) sg b
            (hsel r e i c h)
          unfold fillAt
          rw [if_neg (by rw [undefP, ← Option.not_isSome, this]; decide)]
        simp only [hd]
        rw [PMF.map]
        congr 1
        funext v
        simp only [Function.comp]
        rw [aSignOut_of_selP_some (hinj m r) hL sg b h v]
    unfold sampleVec
    calc _ = (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind (fun e =>
          (PMF.uniformOfFintype G.Ch).bind fun v => (PMF.uniformOfFintype G.SimRand).map
            fun r => aSignOut x (Function.update L p (some v)) sg b m e r) := PMF.bind_comm _ _ _
      _ = (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind (fun e =>
          (PMF.uniformOfFintype G.SimRand).bind fun r => (PMF.uniformOfFintype G.Ch).map
            fun v => aSignOut x (Function.update L p (some v)) sg b m e r) := by
          congr 1
          funext e
          simp only [PMF.map]
          exact PMF.bind_comm _ _ _
      _ = (PMF.uniformOfFintype G.SimRand).bind (fun r =>
          (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind fun e => (PMF.uniformOfFintype G.Ch).map
            fun v => aSignOut x (Function.update L p (some v)) sg b m e r) := PMF.bind_comm _ _ _
      _ = (PMF.uniformOfFintype G.SimRand).bind (fun r =>
          (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind fun e =>
            fillAt (PMF.uniformOfFintype G.Ch) (undefP p) (updP p) (aSignOut x L sg b m e r)) := by
          congr 1
          funext r
          exact hper r
      _ = (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind (fun e =>
          (PMF.uniformOfFintype G.SimRand).bind fun r =>
            fillAt (PMF.uniformOfFintype G.Ch) (undefP p) (updP p) (aSignOut x L sg b m e r)) :=
          PMF.bind_comm _ _ _
      _ = _ := by
          simp only [PMF.bind_bind, PMF.bind_map]
          rfl

end OneStep

/-! ## Winning the marker game -/

section Main

variable {G : Protocol} {κ : G.Classes}

theorem verifyVals_mono {L L' : G.Key → Option G.Ch} (hL : ∀ k c, L k = some c → L' k = some c)
    (x : G.Stmt) (m : G.Msg) (σ : G.Sig) (n : ℕ) (acc vs : List G.Ch)
    (h : verifyVals L x m σ n acc = some vs) : verifyVals L' x m σ n acc = some vs := by
  induction n generalizing acc with
  | zero => exact h
  | succ n ih =>
    simp only [verifyVals] at h ⊢
    cases hk : L (G.vkey x m σ acc) with
    | none => rw [hk] at h; exact absurd h (by simp)
    | some c =>
      rw [hk] at h
      rw [hL _ _ hk]
      exact ih _ h

/-- A forgery that wins against a lookup wins against the lookup with one more point
defined. -/
theorem awins_updP (x : G.Stmt) (p : G.Key) (y : G.Forgery × AState G) (hy : awins x y = true)
    (hp : y.2.1 p = none) (v : G.Ch) : awins x (y.1, updP p y.2 v) = true := by
  have hL : ∀ k c, y.2.1 k = some c → (updP p y.2 v).1 k = some c := by
    intro k c hk
    have hkp : k ≠ p := by rintro rfl; rw [hp] at hk; exact absurd hk (by simp)
    simpa [updP, Function.update_of_ne hkp] using hk
  unfold awins at hy ⊢
  cases hv : verifyVals y.2.1 x y.1.1 y.1.2 G.V [] with
  | none => rw [hv] at hy; simp at hy
  | some vs =>
    rw [hv] at hy
    rw [verifyVals_mono hL x _ _ _ _ _ hv]
    exact hy

theorem toOuterMeasure_bind_le_bind {α β : Type} (p : PMF α) (f g : α → PMF β) (S : Set β)
    (h : ∀ a, (f a).toOuterMeasure S ≤ (g a).toOuterMeasure S) :
    (p.bind f).toOuterMeasure S ≤ (p.bind g).toOuterMeasure S := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a)

/-- **Eager evaluation of one point.** Filling an undefined point `p` by a uniform value
before a run of the simulated game on lookups does not decrease the probability of
winning, when the simulator points equal to `p` of one attempt belong to one entry and
no programmed entry is at `p`. -/
theorem awins_le_eager (x : G.Stmt) (p : G.Key)
    (hinj : ∀ m s (v : Fin G.μ → G.Ch) i j, G.simKey x m s v i = some p →
      G.simKey x m s v j = some p → i = j)
    (hprog : ∀ (look : G.Key → Option G.Ch) m e s, ∀ q ∈ (G.simTrace look x m e s).2.1, q.1 ≠ p)
    (B : OracleAdv G.Query G.Answer G.Forgery) (σ : AState G) (hσ : σ.1 p = none) :
    (OracleAdv.run (aStep x) B σ).toOuterMeasure {y | awins x y = true} ≤
      ((PMF.uniformOfFintype G.Ch).bind fun v => OracleAdv.run (aStep x) B (updP p σ v)).toOuterMeasure
        {y | awins x y = true} := by
  rw [run_eager_of_step (aStep x) _ (undefP p) (updP p)
    (fun σ d hσ y hy => aStep_defined x p σ d hσ y hy)
    (fun σ d hσ => aStep_eager x p hinj hprog σ hσ d) B σ (by simp [undefP, hσ])]
  refine toOuterMeasure_le_bind _ _ _ fun y hy z hz => ?_
  unfold fillAt at hz
  by_cases hu : undefP p y.2 = true
  · rw [if_pos hu] at hz
    obtain ⟨v, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
    exact awins_updP x p y hy (by simpa [undefP] using hu) v
  · rw [if_neg hu] at hz
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hy

/-- Evaluating the markers before the designated point `k` before a run of the
simulated game on lookups, with `k` answered by `e`, does not decrease the probability
of winning. -/
theorem awins_le_aMark (M : Markers κ) (x : G.Stmt) {k : G.Key} (hk : M.des k = true) (e : G.Ch)
    (B : OracleAdv G.Query G.Answer G.Forgery) (sg : List G.Msg) (b : Bool)
    (l : List (Fin M.nm)) (L : G.Key → Option G.Ch) (hL : L k = none) :
    (OracleAdv.run (aStep x) B (Function.update L k (some e), sg, b)).toOuterMeasure
        {y | awins x y = true} ≤
      ((aMark M k L l).bind fun L' =>
        OracleAdv.run (aStep x) B (Function.update L' k (some e), sg, b)).toOuterMeasure
          {y | awins x y = true} := by
  induction l generalizing L with
  | nil => simp [aMark, PMF.pure_bind]
  | cons i l ih =>
    simp only [aMark]
    cases hq : L (M.pt k L i) with
    | some _ => exact ih L hL
    | none =>
      set q := M.pt k L i with hqdef
      have hqk : q ≠ k := by
        intro he
        have := M.pt_cls k L i
        rw [← hqdef, he, M.des_cls k hk] at this
        exact M.cls_ne i this.symm
      have hinj : ∀ m s (v : Fin G.μ → G.Ch) i' j, G.simKey x m s v i' = some q →
          G.simKey x m s v j = some q → i' = j :=
        fun m s v i' j hi hj => M.sim_inj x m s v i' j q i (M.pt_cls k L i) hi hj
      have hprog : ∀ (look : G.Key → Option G.Ch) m e' s, ∀ r ∈ (G.simTrace look x m e' s).2.1,
          r.1 ≠ q := by
        intro look m e' s r hr hrq
        exact M.prog_cls look x m e' s r hr i (by rw [hrq, hqdef, M.pt_cls])
      refine (awins_le_eager x q hinj hprog B _ (by simp [Function.update_of_ne hqk, hq])).trans ?_
      rw [PMF.bind_bind]
      refine toOuterMeasure_bind_le_bind _ _ _ _ fun v => ?_
      simp only [updP]
      rw [Function.update_comm (Ne.symm hqk)]
      exact ih _ (by rw [Function.update_of_ne (Ne.symm hqk), hL])

theorem aStepMk_eq_aStep (M : Markers κ) (x : G.Stmt) (σ : AState G) (d : G.Query)
    (hd : ∀ k, d = .inl k → σ.1 k = none → M.des k = false) :
    aStepMk M x σ d = aStep x σ d := by
  rcases d with k | m
  · simp only [aStepMk, aStep, aHashMk, aHash]
    cases hk : σ.1 k with
    | some e => rfl
    | none => simp [hd k rfl hk]
  · rfl

/-- On lookups, winning the simulated game has probability at most winning the marker
game. -/
theorem awins_le_mk (M : Markers κ) (x : G.Stmt) (B : OracleAdv G.Query G.Answer G.Forgery)
    (σ : AState G) :
    (OracleAdv.run (aStep x) B σ).toOuterMeasure {y | awins x y = true} ≤
      (OracleAdv.run (aStepMk M x) B σ).toOuterMeasure {y | awins x y = true} := by
  induction B generalizing σ with
  | ret a => exact le_rfl
  | rand p k ih =>
    simp only [OracleAdv.run_rand]
    exact toOuterMeasure_bind_le_bind _ _ _ _ fun b => ih b σ
  | query d k ih =>
    simp only [OracleAdv.run_query]
    by_cases hdes : ∃ k₀, d = .inl k₀ ∧ σ.1 k₀ = none ∧ M.des k₀ = true
    · obtain ⟨k₀, rfl, hk₀, hd⟩ := hdes
      obtain ⟨L, sg, b⟩ := σ
      change L k₀ = none at hk₀
      simp only [aStep, aStepMk, aHash, aHashMk, hk₀, hd, if_true, PMF.bind_map, PMF.bind_bind]
      calc _ ≤ ((PMF.uniformOfFintype G.Ch).bind fun e =>
              (aMark M k₀ L (List.finRange M.nm)).bind fun L' =>
                OracleAdv.run (aStep x) (k (.inl e)) (Function.update L' k₀ (some e), sg, b)).toOuterMeasure
                {y | awins x y = true} :=
            toOuterMeasure_bind_le_bind _ _ _ _ fun e =>
              awins_le_aMark M x hd e (k (.inl e)) sg b _ L hk₀
        _ = ((aMark M k₀ L (List.finRange M.nm)).bind fun L' =>
              (PMF.uniformOfFintype G.Ch).bind fun e =>
                OracleAdv.run (aStep x) (k (.inl e)) (Function.update L' k₀ (some e), sg, b)).toOuterMeasure
                {y | awins x y = true} := by rw [PMF.bind_comm]
        _ ≤ _ := toOuterMeasure_bind_le_bind _ _ _ _ fun L' =>
              toOuterMeasure_bind_le_bind _ _ _ _ fun e => ih _ _
    · rw [aStepMk_eq_aStep M x σ d fun k₀ hk₀ hn => by
        cases h : M.des k₀
        · rfl
        · exact absurd ⟨k₀, hk₀, hn, h⟩ hdes]
      exact toOuterMeasure_bind_le_bind _ _ _ _ fun y => ih y.1 y.2

/-- **Winning the marker game.** For every adversary and initial state, winning the
simulated game has probability at most winning the marker game: evaluating the markers
before each fresh designated hash query defines more oracle points, with uniform values,
and a forgery accepted against fewer defined points is accepted against more. -/
theorem sim_wins_le_simMk (M : Markers κ) (x : G.Stmt)
    (A : OracleAdv G.Query G.Answer G.Forgery) (s : G.Tables × Bool) :
    (OracleAdv.run (toOracle (simStep x)) A s).toOuterMeasure {y | wins x y = true} ≤
      (OracleAdv.run (toOracle (simStepMk M x)) A s).toOuterMeasure {y | wins x y = true} := by
  have hset : {y : G.Forgery × (G.Tables × Bool) | wins x y = true} =
      Prod.map id absT ⁻¹' {z | awins x z = true} := rfl
  rw [hset, ← PMF.toOuterMeasure_map_apply, ← PMF.toOuterMeasure_map_apply,
    OracleAdv.run_map_state _ (aStep x) absT (simStep_abs x),
    OracleAdv.run_map_state _ (aStepMk M x) absT (simStepMk_abs M x)]
  exact awins_le_mk M x A (absT s)

/-- At one statement, winning the simulated game run with the verifier's queries from
the empty tables has probability at most winning the marker game. -/
theorem sim_wins_le_simMk_game (M : Markers κ) {qH qS : ℕ} (A : G.Adversary qH qS)
    (x : G.Stmt) :
    (OracleAdv.run (toOracle (simStep x)) (withVerify x (A.run x))
        (Protocol.Tables.empty, false)).toOuterMeasure {y | wins x y = true} ≤
      (OracleAdv.run (toOracle (simStepMk M x)) (withVerify x (A.run x))
        (Protocol.Tables.empty, false)).toOuterMeasure {y | wins x y = true} :=
  sim_wins_le_simMk M x _ _

end Main

end CatCrypt.Crypto.FiatShamirROM
