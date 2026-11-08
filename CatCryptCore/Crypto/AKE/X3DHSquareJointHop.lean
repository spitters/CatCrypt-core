/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareJoint
public import CatCryptCore.Crypto.OracleSimulation
public import CatCryptCore.Tactics.AutoDispatchExt

/-!
# Real signatures to simulated signatures in the joint-key model of X3DH

The first hop of the joint-key model of X3DH replaces the signatures of the Fiat–Shamir signing
attempt (`jointO`) by the signatures of the simulated signing oracle (`simSignO`), both in the
real protocol from the initial state `jInit`.

The two worlds differ only in the signing oracle of each party. Each party `q` has a
Fiat–Shamir state of its own (`JSt.tabs q`) with a flag, which the real signing attempt sets when
its programmed point is already defined. For a Σ-protocol that accepts every response, perfect
honest-verifier zero knowledge gives, one transition at a time (`realStep_le_simStep`), that a
test of the real world on the outcomes where no party's flag is set is at most the same test of
the simulated world (`run_jointO_offJ_le`). The probability that some flag is set is bounded by a
potential (`flagPot`): a party that has not signed contributes the number of points of its table
plus the remaining number of random-oracle queries, times the commitment bound `γ`
(`run_jointO_flag_le`). An environment asks at most `qH` queries of the random oracles of the
signatures, counting the injections, and requests signatures of the parties in `Ps` only
(`SigHashBound`); the distance of the two worlds is then at most `|Ps| · qH · γ` (`δSig`).

## Main definitions

* `sigHashCost`, `sigOutCost`, `SigHashBound` — the query bound of an environment
* `JFlagged`, `RejNil`, `offJ`, `flagPot` — the flags of the parties, the invariant of the real
  world, the test with the flags cleared, and the potential of the flags
* `δSig` — the bound of the hop

## Main results

* `run_jointO_offJ_le` — the real world with the flags cleared is below the simulated world
* `run_jointO_flag_le` — the probability of a flag is below the potential
* `joint_sig_hop_of` — the hop for a Σ-protocol with perfect HVZK and a commitment bound
* `joint_sig_hop` — the hop for X3DH with Schnorr at `ofDHGroup G`, with `γ = 1/|S|`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.FiatShamirROM CatCrypt.Crypto.OracleForking
open CatCrypt.Examples
open CatCrypt.Crypto.AKE.X3DHSquareSigned (completeSig layO)
open PMF (tsum_bind_mul)
open scoped ENNReal

/-! ## The query bound and the flags -/

section Defs

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt]

/-- The cost of an event in queries of the random oracles of the signatures: one for a hash
query and one for an injection, which queries the oracle of the peer. -/
def sigHashCost : JEv P → ℕ
  | .inr (.inr (.sigHash _ _)) => 1
  | .inr (.inr (.inject _ _ _ _)) => 1
  | _ => 0

/-- The cost of a request of a signature of a party outside `Ps`. -/
def sigOutCost (Ps : Finset PartyId) : JEv P → ℕ
  | .inr (.inr (.sigPub q)) => if q ∈ Ps then 0 else 1
  | _ => 0

/-- **The query bound of an environment of the joint-key model**: at most `qH` queries of the
random oracles of the signatures, counting the injections, and signatures of the parties in
`Ps` only. -/
def SigHashBound {K α : Type} (Ps : Finset PartyId) (qH : ℕ)
    (B : OracleAdv (JEv P) (JOut P K) α) : Prop :=
  B.IsQueryBoundBy (sigHashCost P) qH ∧ B.IsQueryBoundBy (sigOutCost P Ps) 0

/-- The flag of the Fiat–Shamir state of some party is set. -/
def JFlagged (l : JSt P) : Prop := ∃ q, (l.tabs q).2 = true

/-- No party has hidden entries in its tables. -/
def RejNil (l : JSt P) : Prop := ∀ q, (l.tabs q).1.rej = []

open Classical in
/-- The test `Y` on the outcomes where no flag is set, and `0` on the others. -/
noncomputable def offJ {β T : Type} (Y : β × (JSt P × T) → ℝ≥0∞) (o : β × (JSt P × T)) :
    ℝ≥0∞ :=
  if JFlagged P o.2.1 then 0 else Y o

open Classical in
/-- **The potential of the flags** with `h` remaining queries: `1` when a flag is set, plus, for
each party of `Ps` that has not signed, the number of points of its table plus `h`, times `γ`. -/
noncomputable def flagPot (Ps : Finset PartyId) (γ : ℝ≥0∞) (h : ℕ) (l : JSt P) : ℝ≥0∞ :=
  (if JFlagged P l then 1 else 0) +
    ∑ q ∈ Ps, if l.sigs q = none then (((l.tabs q).1.keys.length + h : ℕ) : ℝ≥0∞) * γ else 0

/-- **The bound of the signature hop**: `|Ps| · qH · γ`. -/
noncomputable def δSig (Ps : Finset PartyId) (qH : ℕ) (γ : ℝ≥0∞) : ℝ≥0∞ :=
  (Ps.card : ℝ≥0∞) * qH * γ

end Defs

/-! ## Transitions of the Fiat–Shamir oracles -/

section FSFacts

variable {P : FiatShamirROM.Sigma} [DecidableEq P.Stmt]

/-- A real transition from tables without hidden entries keeps them without hidden entries,
for a Σ-protocol that accepts every response. -/
theorem realStep_rej_nil (hacc : ∀ z, P.accept z = true) (xw : P.Stmt × P.Wit) (u : FSt P)
    (hu : u.1.rej = []) (d : (fsOf P).Query) :
    ∀ r ∈ (toOracle (realStep xw) u d).support, r.2.1.rej = [] := by
  obtain ⟨t, b⟩ := u
  intro r hr
  cases d with
  | inl k =>
    have hu' : t.rej = [] := hu
    simp only [toOracle, realStep, realHashStep, hu', lookupIn_nil] at hr
    cases hl : t.lookup k with
    | some e =>
      simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact hu'
    | none =>
      simp only [hl, Step.toPMF, PMF.support_map, Set.mem_image] at hr
      obtain ⟨e, -, rfl⟩ := hr
      rfl
  | inr m =>
    simp only [toOracle, realStep, Step.toPMF, sampleVec, PMF.support_bind, PMF.support_map,
      Set.mem_iUnion, Set.mem_image] at hr
    obtain ⟨e, -, r', -, rfl⟩ := hr
    simpa [realSignOut, Protocol.hidEntries, Protocol.entries, hacc] using hu

/-- A simulated transition keeps the hidden entries. -/
theorem simStep_rej (x : P.Stmt) (u : FSt P) (d : (fsOf P).Query) :
    ∀ r ∈ (toOracle (simStep x) u d).support, r.2.1.rej = u.1.rej := by
  intro r hr
  have h := simStep_setRej x u.1.rej u d
  have hu : (({ u.1 with rej := u.1.rej }, u.2) : FSt P) = u := rfl
  rw [hu] at h
  rw [← h, PMF.support_map] at hr
  obtain ⟨z, -, rfl⟩ := hr
  rfl

/-- A hash query of the real oracle from tables without hidden entries keeps the flag and adds
at most one point. -/
theorem realStep_hash_support (xw : P.Stmt × P.Wit) (u : FSt P) (hu : u.1.rej = [])
    (k : (fsOf P).Key) :
    ∀ r ∈ (toOracle (realStep xw) u (.inl k)).support,
      r.2.2 = u.2 ∧ r.2.1.keys.length ≤ u.1.keys.length + 1 := by
  obtain ⟨t, b⟩ := u
  have hu' : t.rej = [] := hu
  intro r hr
  simp only [toOracle, realStep, realHashStep, hu', lookupIn_nil] at hr
  cases hl : t.lookup k with
  | some e =>
    simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨rfl, Nat.le_succ _⟩
  | none =>
    simp only [hl, Step.toPMF, PMF.support_map, Set.mem_image] at hr
    obtain ⟨e, -, rfl⟩ := hr
    refine ⟨rfl, ?_⟩
    simp [Protocol.Tables.keys]
    omega

/-- **The flag of a signing attempt.** From tables without hidden entries and with the flag
cleared, the real signing attempt sets the flag with probability at most the number of points
of the tables times the commitment bound. -/
theorem realStep_sign_flag_le (xw : P.Stmt × P.Wit) {γ : ℝ≥0∞}
    (hγ : P.CommitBoundAt xw.1 xw.2 γ) (u : FSt P) (hu : u.1.rej = []) (hb : u.2 = false)
    (m : P.Stmt) :
    ∑' r, toOracle (realStep xw) u (.inr m) r * (if r.2.2 = true then 1 else 0) ≤
      (u.1.keys.length : ℝ≥0∞) * γ := by
  classical
  obtain ⟨t, b⟩ := u
  have hu' : t.rej = [] := hu
  have hb' : b = false := hb
  subst hb'
  have hmem : ∀ e r, (realSignOut xw.1 xw.2 t false m e r).2.2 = true →
      (P.commit xw.1 xw.2 r, m) ∈ t.keys := by
    intro e r h
    simp only [realSignOut, Fin.isValue, Sigma.toProtocol_μ, Protocol.flagging, Bool.not_false,
      Bool.true_or, ↓reduceIte, Bool.false_or, List.any_eq_true, List.mem_finRange, true_and,
      exists_const] at h
    exact Protocol.lookupAll_isSome_mem h
  have hpt : ∀ e r, (if (realSignOut xw.1 xw.2 t false m e r).2.2 = true then (1 : ℝ≥0∞)
      else 0) ≤ ∑ k ∈ t.keys.toFinset, if P.commit xw.1 xw.2 r = k.1 then 1 else 0 := by
    intro e r
    split_ifs with h
    · refine le_trans ?_ (Finset.single_le_sum (f := fun k : (fsOf P).Key =>
        if P.commit xw.1 xw.2 r = k.1 then (1 : ℝ≥0∞) else 0) (fun _ _ => zero_le)
        (List.mem_toFinset.mpr (hmem e r h)))
      simp
    · exact zero_le
  have hcol : ∀ a : P.Com,
      ∑' r, PMF.uniformFintype P.Rand r * (if P.commit xw.1 xw.2 r = a then 1 else 0) ≤ γ := by
    intro a
    refine le_trans (le_of_eq ?_) (hγ a)
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun r => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, mul_ite, mul_one, mul_zero]
  have hinner : ∀ e, ∑' r, PMF.uniformFintype P.Rand r *
      (if (realSignOut xw.1 xw.2 t false m e r).2.2 = true then (1 : ℝ≥0∞) else 0) ≤
      (t.keys.length : ℝ≥0∞) * γ := by
    intro e
    calc _ ≤ ∑' r, PMF.uniformFintype P.Rand r *
          ∑ k ∈ t.keys.toFinset, (if P.commit xw.1 xw.2 r = k.1 then (1 : ℝ≥0∞) else 0) :=
          ENNReal.tsum_le_tsum fun r => mul_le_mul_right (hpt e r) _
      _ = ∑ k ∈ t.keys.toFinset, ∑' r, PMF.uniformFintype P.Rand r *
          (if P.commit xw.1 xw.2 r = k.1 then (1 : ℝ≥0∞) else 0) := by
          simp only [tsum_fintype, Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ _k ∈ t.keys.toFinset, γ := Finset.sum_le_sum fun k _ => hcol k.1
      _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          exact_mod_cast List.toFinset_card_le t.keys
  simp only [toOracle, realStep, Step.toPMF, sampleVec, tsum_bind_mul, tsum_map_mul']
  calc _ ≤ ∑' e, PMF.uniformFintype (Fin (fsOf P).μ → P.Ch) e * ((t.keys.length : ℝ≥0∞) * γ) :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right (hinner e) _
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end FSFacts

/-! ## The tables of the parties along a step of the real protocol -/

section Tabs

variable {P : FiatShamirROM.Sigma} [DecidableEq P.Stmt] {K : Type}

/-- The answer of the layer in the phases of an honest or adversary event keeps its state. -/
theorem jPost_keep (pub : P.Wit → P.Stmt) (l : JSt P) (o : OOut P.Wit P.Stmt K)
    (hl : l.ph = .hon ∨ l.ph = .adv) : ∀ r ∈ (jPost P pub l o).support, r.1 = l := by
  intro r hr
  rcases l with ⟨tb, sg, pe, cr, ph⟩
  rcases hl with h | h <;> (simp only at h; subst h) <;> rcases o with o | o <;>
    simp only [jPost, PMF.support_pure, Set.mem_singleton_iff] at hr <;> rw [hr]

/-- The answer of the layer in the phase of a corruption keeps the tables, the signatures, the
peers and the phase. -/
theorem jPost_keep_corr (pub : P.Wit → P.Stmt) (l : JSt P) (o : OOut P.Wit P.Stmt K)
    (q : PartyId) (hl : l.ph = .corr q) : ∀ r ∈ (jPost P pub l o).support,
      r.1.tabs = l.tabs ∧ r.1.sigs = l.sigs ∧ r.1.peers = l.peers ∧ r.1.ph = l.ph := by
  intro r hr
  rcases l with ⟨tb, sg, pe, cr, ph⟩
  simp only at hl
  subst hl
  simp only [jPost] at hr
  split at hr <;> simp_all

/-- An event of the state machine of the layer keeps the tables and the signatures, and sets an
honest, adversary or corruption phase. -/
def FiltPre (l : JSt P) (e : JEv P) : Prop :=
  ∀ a ∈ (jPre P l e).support, a.1.tabs = l.tabs ∧ a.1.sigs = l.sigs ∧
    (a.1.ph = .hon ∨ a.1.ph = .adv ∨ ∃ q, a.1.ph = .corr q)

/-- An honest event is an event of the state machine of the layer. -/
theorem filtPre_inl (l : JSt P) (h : HEv) : FiltPre l (.inl h) := by
  intro a ha
  rcases h with ⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩ <;>
    simp only [jPre, PMF.support_pure, Set.mem_singleton_iff] at ha <;> subst ha
  · unfold notePeerJ
    split_ifs <;> exact ⟨rfl, rfl, Or.inl rfl⟩
  · exact ⟨rfl, rfl, Or.inl rfl⟩

/-- An adversary event of the X3DH state machine is an event of the state machine of the
layer. -/
theorem filtPre_inr_inl (l : JSt P) (g : RAEv P.Stmt) : FiltPre l (.inr (.inl g)) := by
  intro a ha
  cases g <;> simp only [jPre, PMF.support_pure, Set.mem_singleton_iff] at ha <;> subst ha <;>
    grind

/-- A property of the state of one party after an update at a party. -/
theorem update_tabs_prop (Q : FSt P → Prop) (f : PartyId → FSt P) (q q' : PartyId) (v : FSt P)
    (hq : Q (f q)) (hv : q = q' → Q v) : Q (Function.update f q' v q) := by
  by_cases h : q = q'
  · subst h
    simpa using hv rfl
  · simpa [Function.update_of_ne h] using hq

variable [Fintype P.Wit] [Nonempty P.Wit] [Fintype K] [Nonempty K]

/-- A step of the filtered world at an event of the state machine of the layer keeps the tables
and the signatures. -/
theorem filtJO_keep (A : AKEAlg P.Wit P.Stmt) (t : JSt P × RSt P.Wit P.Stmt K) (e : JEv P)
    (he : FiltPre t.1 e) :
    ∀ y ∈ (filtJO P A t e).support, y.2.1.tabs = t.1.tabs ∧ y.2.1.sigs = t.1.sigs := by
  intro y hy
  simp only [filtJO, X3DHSquareSigned.layO, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
    Set.mem_image] at hy
  obtain ⟨a, ha, z, -, r, hr, rfl⟩ := hy
  obtain ⟨h1, h2, h3 | h3 | ⟨q, h3⟩⟩ := he a ha
  · rw [jPost_keep A.pub a.1 z.1 (Or.inl h3) r hr]
    exact ⟨h1, h2⟩
  · rw [jPost_keep A.pub a.1 z.1 (Or.inr h3) r hr]
    exact ⟨h1, h2⟩
  · obtain ⟨k1, k2, -⟩ := jPost_keep_corr A.pub a.1 z.1 q h3 r hr
    exact ⟨k1.trans h1, k2.trans h2⟩

/-- **The tables of a party along a step of the real protocol with the signature oracles `O`.**
A property of the state of a party that every transition of the oracles keeps holds after a
step when it holds before. -/
theorem jointOWith_tabs_support (O : SigOracles P) (A : AKEAlg P.Wit P.Stmt)
    (Q : FSt P → Prop) (hO : ∀ xw u d, Q u → ∀ r ∈ (toOracle (O xw) u d).support, Q r.2)
    (t : JSt P × RSt P.Wit P.Stmt K) (e : JEv P) (q : PartyId) (hq : Q (t.1.tabs q)) :
    ∀ y ∈ (jointOWith P O A t e).support, Q (y.2.1.tabs q) := by
  intro y hy
  rcases e with h' | g | (q' | ⟨q', k⟩ | ⟨sid, pid, spk, σ⟩)
  · rw [jointOWith_inl] at hy
    rw [(filtJO_keep A t _ (filtPre_inl t.1 h') y hy).1]
    exact hq
  · rw [jointOWith_inr_inl] at hy
    rw [(filtJO_keep A t _ (filtPre_inr_inl t.1 g) y hy).1]
    exact hq
  · simp only [jointOWith, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
      Set.mem_image] at hy
    obtain ⟨l, -, r, hr, rfl⟩ := hy
    unfold signAt at hr
    split at hr
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
      exact hq
    · simp only [PMF.support_map, Set.mem_image] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      exact update_tabs_prop Q _ q q' z.2 hq fun h => by subst h; exact hO _ _ _ hq z hz
  · simp only [jointOWith, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
      Set.mem_image] at hy
    obtain ⟨l, -, r, hr, rfl⟩ := hy
    simp only [hashAt, PMF.support_map, Set.mem_image] at hr
    obtain ⟨z, hz, rfl⟩ := hr
    exact update_tabs_prop Q _ q q' z.2 hq fun h => by subst h; exact hO _ _ _ hq z hz
  · simp only [jointOWith] at hy
    split at hy
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      rw [hy]
      exact hq
    · rename_i q' _
      simp only [PMF.support_bind, Set.mem_iUnion] at hy
      obtain ⟨l, -, r, hr, hy⟩ := hy
      have hr' : Q (r.2.tabs q) := by
        simp only [hashAt, PMF.support_map, Set.mem_image] at hr
        obtain ⟨z, hz, rfl⟩ := hr
        exact update_tabs_prop Q _ q q' z.2 hq fun h => by subst h; exact hO _ _ _ hq z hz
      split at hy
      · simp only [PMF.support_map, Set.mem_image] at hy
        obtain ⟨c, -, rfl⟩ := hy
        exact hr'
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        rw [hy]
        exact hr'

end Tabs

/-! ## The real world with the flags cleared below the simulated world -/

section Hop

variable {P : FiatShamirROM.Sigma} [DecidableEq P.Stmt]

/-- An expectation under `p` is monotone in a test that is bounded on the support of `p`. -/
theorem tsum_mul_le_of_support {α : Type} (p : PMF α) (f g : α → ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a ≤ g a) : ∑' a, p a * f a ≤ ∑' a, p a * g a :=
  ENNReal.tsum_le_tsum fun a => by
    by_cases ha : a ∈ p.support
    · exact mul_le_mul_right (h a ha) _
    · simp [(PMF.apply_eq_zero_iff p a).mpr ha]

/-- An expectation under `p` depends only on the values of the test on the support of `p`. -/
theorem tsum_mul_congr_support {α : Type} (p : PMF α) (f g : α → ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a = g a) : ∑' a, p a * f a = ∑' a, p a * g a :=
  le_antisymm (tsum_mul_le_of_support p f g fun a ha => (h a ha).le)
    (tsum_mul_le_of_support p g f fun a ha => (h a ha).ge)

/-- The test with the flags cleared is below the test. -/
theorem offJ_le {β T : Type} (Y : β × (JSt P × T) → ℝ≥0∞) (o : β × (JSt P × T)) :
    offJ P Y o ≤ Y o := by
  unfold offJ
  split_ifs
  · exact zero_le
  · exact le_rfl

/-- Clearing the hidden entries of tables without hidden entries is the identity. -/
theorem setRej_nil_of {β : Type} (r : β × FSt P) (h : r.2.1.rej = []) : setRej [] r = r := by
  obtain ⟨a, ⟨⟨h1, h2, h3, h4⟩, b⟩⟩ := r
  simp only at h
  subst h
  rfl

/-- **One signature transition, real to simulated.** A transition of the signature oracle of a
party `q` from tables without hidden entries, followed by a continuation `C` that places the
new state of the oracle at `q`: a test with the flags cleared on the real transition is at most
the test on the simulated transition, for a Σ-protocol with perfect HVZK at the pair that
accepts every response. -/
theorem hop_core {β T : Type} (hacc : ∀ z, P.accept z = true) (xw : P.Stmt × P.Wit)
    (hZK : (fsOf P).StatHVZKAt xw.1 xw.2 0) (u : FSt P) (hu : u.1.rej = [])
    (d : (fsOf P).Query) (q : PartyId) (C : (fsOf P).Answer × FSt P → PMF (β × (JSt P × T)))
    (hC : ∀ r, ∀ o ∈ (C r).support, o.2.1.tabs q = r.2)
    (Y : β × (JSt P × T) → ℝ≥0∞) (hY : ∀ o, Y o ≤ 1) :
    ∑' o, ((toOracle (realStep xw) u d).bind C) o * offJ P Y o ≤
      ∑' o, ((toOracle (simStep xw.1) u d).bind C) o * Y o := by
  obtain ⟨F, hF⟩ : ∃ F : (fsOf P).Answer × FSt P → ℝ≥0∞, F = fun r => ∑' o, C r o * Y o :=
    ⟨_, rfl⟩
  obtain ⟨F', hF'⟩ : ∃ F' : (fsOf P).Answer × FSt P → ℝ≥0∞, F' = fun r => F (setRej [] r) :=
    ⟨_, rfl⟩
  have hF1 : ∀ r, F' r ≤ 1 := fun r => by
    rw [hF', hF]
    exact (ENNReal.tsum_le_tsum fun o => mul_le_of_le_one_right' (hY o)).trans
      (le_of_eq (PMF.tsum_coe _))
  have hFr : RejInsensitive F' := fun _ _ => by rw [hF']; rfl
  have hreal : ∀ r ∈ (toOracle (realStep xw) u d).support,
      ∑' o, C r o * offJ P Y o ≤ offFlag F' r := by
    intro r hr
    have hr0 := setRej_nil_of r (realStep_rej_nil hacc xw u hu d r hr)
    unfold offFlag
    split_ifs with hfl
    · refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun o => ?_)
      by_cases ho : o ∈ (C r).support
      · have hJ : JFlagged P o.2.1 := ⟨q, by rw [hC r o ho]; exact hfl⟩
        simp [offJ, hJ]
      · simp [(PMF.apply_eq_zero_iff _ _).mpr ho]
    · rw [hF']
      dsimp only
      rw [hr0, hF]
      exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offJ_le Y o) _
  have hsim : ∀ r ∈ (toOracle (simStep xw.1) u d).support, F' r = F r := by
    intro r hr
    have h := simStep_rej xw.1 u d r hr
    rw [hu] at h
    rw [hF']
    dsimp only
    rw [setRej_nil_of r h]
  rw [tsum_bind_mul, tsum_bind_mul]
  refine le_trans (tsum_mul_le_of_support _ _ _ hreal) ?_
  have h2 := realStep_le_simStep (G := fsOf P) xw hZK u d F' hF1 hFr
  rw [ite_self, add_zero] at h2
  exact h2.trans (le_of_eq (by rw [tsum_mul_congr_support _ _ _ hsim, hF]))

variable [Fintype P.Wit] [Nonempty P.Wit] {K : Type} [Fintype K] [Nonempty K]

/-- **One step, real to simulated signatures.** From a state without hidden entries, a test with
the flags cleared on a step of the real protocol is at most the test on a step with simulated
signatures. -/
theorem jointO_step_le (hacc : ∀ z, P.accept z = true) (A : AKEAlg P.Wit P.Stmt)
    (hZK : ∀ w, (fsOf P).StatHVZKAt (A.pub w) w 0) (t : JSt P × RSt P.Wit P.Stmt K)
    (ht : RejNil P t.1) (e : JEv P) (Y : JOut P K × (JSt P × RSt P.Wit P.Stmt K) → ℝ≥0∞)
    (hY : ∀ o, Y o ≤ 1) :
    ∑' o, jointO P A t e o * offJ P Y o ≤ ∑' o, simSignO P A t e o * Y o := by
  rcases e with h' | g | (q | ⟨q, k⟩ | ⟨sid, pid, spk, σ⟩)
  · simp only [jointO, simSignO, jointOWith_inl]
    exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offJ_le Y o) _
  · simp only [jointO, simSignO, jointOWith_inr_inl]
    exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offJ_le Y o) _
  · simp only [jointO, simSignO, jointOWith, tsum_bind_mul]
    refine ENNReal.tsum_le_tsum fun lt => mul_le_mul_right ?_ _
    unfold signAt
    rcases hs : t.1.sigs q with _ | c
    · dsimp only
      rw [PMF.map_comp, PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
      exact hop_core hacc (A.pub lt.1.1, lt.1.1) (hZK lt.1.1) (t.1.tabs q) (ht q)
        (.inr (A.pub lt.1.2)) q _
        (fun r o ho => by
          simp only [Function.comp_apply, PMF.support_pure, Set.mem_singleton_iff] at ho
          subst ho
          simp) Y hY
    · dsimp only
      rw [PMF.pure_map]
      exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offJ_le Y o) _
  · simp only [jointO, simSignO, jointOWith, tsum_bind_mul]
    refine ENNReal.tsum_le_tsum fun lt => mul_le_mul_right ?_ _
    simp only [hashAt, PMF.map_comp]
    rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
    exact hop_core hacc (A.pub lt.1.1, lt.1.1) (hZK lt.1.1) (t.1.tabs q) (ht q) (.inl k) q _
      (fun r o ho => by
        simp only [Function.comp_apply, PMF.support_pure, Set.mem_singleton_iff] at ho
        subst ho
        simp) Y hY
  · simp only [jointO, simSignO, jointOWith]
    rcases hp : t.1.peers (sid, pid) with _ | q
    · exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offJ_le Y o) _
    · rw [tsum_bind_mul, tsum_bind_mul]
      refine ENNReal.tsum_le_tsum fun lt => mul_le_mul_right ?_ _
      simp only [hashAt, PMF.bind_map]
      refine hop_core hacc (A.pub lt.1.1, lt.1.1) (hZK lt.1.1) (t.1.tabs q) (ht q)
        (.inl (σ.1, spk)) q _ ?_ Y hY
      intro r o ho
      simp only [Function.comp_apply] at ho
      split at ho
      · simp only [PMF.support_map, Set.mem_image] at ho
        obtain ⟨c, -, rfl⟩ := ho
        simp
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at ho
        subst ho
        simp

/-- A step of the real protocol keeps the tables without hidden entries. -/
theorem jointO_rejNil (hacc : ∀ z, P.accept z = true) (A : AKEAlg P.Wit P.Stmt)
    (t : JSt P × RSt P.Wit P.Stmt K) (ht : RejNil P t.1) (e : JEv P) :
    ∀ y ∈ (jointO P A t e).support, RejNil P y.2.1 := fun y hy q =>
  jointOWith_tabs_support _ A (fun u => u.1.rej = [])
    (fun xw u d hu r hr => realStep_rej_nil hacc xw u hu d r hr) t e q (ht q) y hy

/-- A set flag stays set along a run of the real protocol. -/
theorem run_jointO_flagged (A : AKEAlg P.Wit P.Stmt) {α : Type}
    (B : OracleAdv (JEv P) (JOut P K) α) (t : JSt P × RSt P.Wit P.Stmt K)
    (hfl : JFlagged P t.1) : ∀ y ∈ (OracleAdv.run (jointO P A) B t).support, JFlagged P y.2.1 := by
  refine OracleAdv.run_support_inv (jointO P A) (fun s => JFlagged P s.1) ?_ B t hfl
  intro s e x hs hx
  obtain ⟨q, hq⟩ := hs
  have hO : ∀ (xw : P.Stmt × P.Wit) (u : FSt P) (d : (fsOf P).Query), u.2 = true →
      ∀ r ∈ (toOracle (realStep xw) u d).support, r.2.2 = true := by
    intro xw u d hu r hr
    obtain ⟨tb, b⟩ := u
    simp only at hu
    subst hu
    exact realStep_flag (G := fsOf P) xw tb d r hr
  exact ⟨q, jointOWith_tabs_support (fun xw => realStep xw) A (fun u => u.2 = true) hO s e q hq
    x hx⟩

/-- **The real protocol with the flags cleared is below the protocol with simulated
signatures.** From a state without hidden entries, the expectation of a test with values in
`[0, 1]` on the output of a run of the real protocol, on the runs that set no flag, is at most
its expectation on a run with simulated signatures. -/
theorem run_jointO_offJ_le (hacc : ∀ z, P.accept z = true) (A : AKEAlg P.Wit P.Stmt)
    (hZK : ∀ w, (fsOf P).StatHVZKAt (A.pub w) w 0) {α : Type} (g : α → ℝ≥0∞)
    (hg : ∀ a, g a ≤ 1) (B : OracleAdv (JEv P) (JOut P K) α) (t : JSt P × RSt P.Wit P.Stmt K)
    (ht : RejNil P t.1) :
    ∑' y, OracleAdv.run (jointO P A) B t y * offJ P (fun y => g y.1) y ≤
      ∑' y, OracleAdv.run (simSignO P A) B t y * g y.1 := by
  induction B generalizing t with
  | ret a =>
    exact tsum_mul_le_of_support _ _ _ fun y _ => offJ_le _ y
  | rand p k ih =>
    simp only [OracleAdv.run_rand, tsum_bind_mul]
    exact ENNReal.tsum_le_tsum fun b => mul_le_mul_right (ih b t ht) _
  | query e k ih =>
    simp only [OracleAdv.run_query, tsum_bind_mul]
    have hY : ∀ o : JOut P K × (JSt P × RSt P.Wit P.Stmt K),
        ∑' y, OracleAdv.run (simSignO P A) (k o.1) o.2 y * g y.1 ≤ 1 := fun o =>
      (ENNReal.tsum_le_tsum fun y : α × (JSt P × RSt P.Wit P.Stmt K) =>
        mul_le_of_le_one_right' (hg y.1)).trans
        (le_of_eq (PMF.tsum_coe _))
    refine le_trans (tsum_mul_le_of_support _ _
      (offJ P fun o => ∑' y, OracleAdv.run (simSignO P A) (k o.1) o.2 y * g y.1) ?_)
      (jointO_step_le hacc A hZK t ht e _ hY)
    intro o ho
    unfold offJ
    split_ifs with hfl
    · refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun y => ?_)
      by_cases hy : y ∈ (OracleAdv.run (jointO P A) (k o.1) o.2).support
      · simp [run_jointO_flagged A (k o.1) o.2 hfl y hy]
      · simp [(PMF.apply_eq_zero_iff _ _).mpr hy]
    · exact ih o.1 o.2 (jointO_rejNil hacc A t ht e o ho)

end Hop

/-! ## The potential of the flags -/

section Pot

variable {P : FiatShamirROM.Sigma} [DecidableEq P.Stmt]

/-- An expectation of a test bounded on the support by a constant is bounded by it. -/
theorem tsum_mul_le_const {α : Type} (p : PMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a ≤ c) : ∑' a, p a * f a ≤ c :=
  (tsum_mul_le_of_support p f (fun _ => c) h).trans
    (le_of_eq (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]))

/-- The potential is monotone in the number of remaining queries. -/
theorem flagPot_mono (Ps : Finset PartyId) (γ : ℝ≥0∞) {h h' : ℕ} (hh : h ≤ h') (l : JSt P) :
    flagPot P Ps γ h l ≤ flagPot P Ps γ h' l := by
  unfold flagPot
  gcongr with q _
  split_ifs
  · gcongr
  · exact le_rfl

/-- **The potential after a hash query at `q`**: the flags and signatures kept, the tables of
the other parties kept, and at most one point added to the table of `q`, with one query fewer. -/
theorem flagPot_hash (Ps : Finset PartyId) (γ : ℝ≥0∞) (h : ℕ) (hh : 1 ≤ h) (l l' : JSt P)
    (q : PartyId) (hsig : l'.sigs = l.sigs) (hoth : ∀ q', q' ≠ q → l'.tabs q' = l.tabs q')
    (hfl : (l'.tabs q).2 = (l.tabs q).2)
    (hk : (l'.tabs q).1.keys.length ≤ (l.tabs q).1.keys.length + 1) :
    flagPot P Ps γ (h - 1) l' ≤ flagPot P Ps γ h l := by
  have hJ : JFlagged P l' ↔ JFlagged P l := by
    constructor <;> rintro ⟨q', hq'⟩ <;> refine ⟨q', ?_⟩ <;> by_cases e : q' = q
    · subst e; rwa [← hfl]
    · rwa [← hoth q' e]
    · subst e; rwa [hfl]
    · rwa [hoth q' e]
  unfold flagPot
  refine add_le_add (le_of_eq (by grind)) (Finset.sum_le_sum fun q' _ => ?_)
  rw [hsig]
  split_ifs
  · gcongr ?_ * γ
    norm_cast
    by_cases e : q' = q
    · subst e; omega
    · rw [hoth q' e]; omega
  · exact le_rfl

open Classical in
/-- **The potential after a signing attempt at `q`.** For a party `q` of `Ps` that has not
signed, a distribution `p` of answers and states of the oracle of `q` that sets the flag with
probability at most the number of points of the table of `q` times `γ` when the flag is
cleared, and states `L r` that place the state of the oracle at `q`, mark `q` as signed and keep
the other parties, the expected potential is at most the potential before. -/
theorem flagPot_sign (Ps : Finset PartyId) (γ : ℝ≥0∞) (h : ℕ) (l : JSt P) (q : PartyId)
    (hq : q ∈ Ps) (hnone : l.sigs q = none) (p : PMF ((fsOf P).Answer × FSt P))
    (hp : (l.tabs q).2 = false →
      ∑' r, p r * (if r.2.2 = true then 1 else 0) ≤ ((l.tabs q).1.keys.length : ℝ≥0∞) * γ)
    (L : (fsOf P).Answer × FSt P → JSt P) (hLq : ∀ r, (L r).tabs q = r.2)
    (hLs : ∀ r, (L r).sigs q ≠ none) (hLt : ∀ r q', q' ≠ q → (L r).tabs q' = l.tabs q')
    (hLg : ∀ r q', q' ≠ q → (L r).sigs q' = l.sigs q') :
    ∑' r, p r * flagPot P Ps γ h (L r) ≤ flagPot P Ps γ h l := by
  set R : ℝ≥0∞ := ∑ q' ∈ Ps.erase q, if l.sigs q' = none then
    (((l.tabs q').1.keys.length + h : ℕ) : ℝ≥0∞) * γ else 0 with hR
  have hl : flagPot P Ps γ h l = (if JFlagged P l then 1 else 0) +
      ((((l.tabs q).1.keys.length + h : ℕ) : ℝ≥0∞) * γ + R) := by
    unfold flagPot
    rw [← Finset.add_sum_erase _ _ hq, hnone, ite_eq_left rfl]
  have hLr : ∀ r, flagPot P Ps γ h (L r) = (if JFlagged P (L r) then 1 else 0) + R := by
    intro r
    unfold flagPot
    rw [← Finset.add_sum_erase _ _ hq, ite_eq_right (hLs r), zero_add, hR]
    refine congrArg _ (Finset.sum_congr rfl fun q' hq' => ?_)
    have e := Finset.ne_of_mem_erase hq'
    rw [hLg r q' e, hLt r q' e]
  simp only [hLr]
  by_cases hfl : JFlagged P l
  · refine tsum_mul_le_const _ _ _ fun r _ => ?_
    rw [hl, ite_eq_left hfl]
    refine add_le_add (by split_ifs <;> simp) ?_
    exact le_add_self
  · have hq0 : (l.tabs q).2 = false := by
      by_contra hc
      exact hfl ⟨q, by simpa using hc⟩
    have hpt : ∀ r, (if JFlagged P (L r) then (1 : ℝ≥0∞) else 0) + R ≤
        (if r.2.2 = true then 1 else 0) + R := by
      intro r
      refine add_le_add ?_ le_rfl
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso
        obtain ⟨q', hq'⟩ := h1
        by_cases e : q' = q
        · subst e; rw [hLq] at hq'; exact h2 hq'
        · rw [hLt r q' e] at hq'; exact hfl ⟨q', hq'⟩
      · exact zero_le
      · exact le_rfl
    calc _ ≤ ∑' r, p r * ((if r.2.2 = true then 1 else 0) + R) :=
          ENNReal.tsum_le_tsum fun r => mul_le_mul_right (hpt r) _
      _ = ∑' r, p r * (if r.2.2 = true then 1 else 0) + R := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ ≤ ((l.tabs q).1.keys.length : ℝ≥0∞) * γ + R := add_le_add (hp hq0) le_rfl
      _ ≤ _ := by
          rw [hl, ite_eq_right hfl, zero_add]
          gcongr
          exact_mod_cast Nat.le_add_right _ _

/-- The potential reads only the tables and the signatures. -/
theorem flagPot_congr (Ps : Finset PartyId) (γ : ℝ≥0∞) (h : ℕ) {l l' : JSt P}
    (htabs : l'.tabs = l.tabs) (hsigs : l'.sigs = l.sigs) :
    flagPot P Ps γ h l' = flagPot P Ps γ h l := by
  rcases l' with ⟨a, b, c, d⟩
  simp only at htabs hsigs
  subst htabs hsigs
  rfl

/-- **The potential after a hash query of the real oracle at `q`**, from tables without hidden
entries. -/
theorem flagPot_hashStep (Ps : Finset PartyId) (γ : ℝ≥0∞) (h : ℕ) (hh : 1 ≤ h) (l : JSt P)
    (hl : RejNil P l) (q : PartyId) (xw : P.Stmt × P.Wit) (k : (fsOf P).Key)
    (z : (fsOf P).Answer × FSt P) (hz : z ∈ (toOracle (realStep xw) (l.tabs q) (.inl k)).support)
    (l' : JSt P) (hsig : l'.sigs = l.sigs) (htabs : l'.tabs = Function.update l.tabs q z.2) :
    flagPot P Ps γ (h - 1) l' ≤ flagPot P Ps γ h l := by
  obtain ⟨h1, h2⟩ := realStep_hash_support xw (l.tabs q) (hl q) k z hz
  refine flagPot_hash Ps γ h hh l l' q hsig (fun q' e => ?_) ?_ ?_
  · rw [htabs, Function.update_of_ne e]
  · rw [htabs, Function.update_self]
    exact h1
  · rw [htabs, Function.update_self]
    exact h2

end Pot

/-! ## The probability of a flag -/

section Flag

variable {P : FiatShamirROM.Sigma} [DecidableEq P.Stmt] [Fintype P.Wit] [Nonempty P.Wit]
  {K : Type} [Fintype K] [Nonempty K]

/-- **One step of the potential.** From a state without hidden entries, the expected potential
after a step of the real protocol, with the remaining queries decreased by the cost of the
event, is at most the potential before, for an event within the bound of the environment. -/
theorem jointO_flag_step_le (A : AKEAlg P.Wit P.Stmt) {γ : ℝ≥0∞}
    (hγ : ∀ w, P.CommitBoundAt (A.pub w) w γ) (Ps : Finset PartyId) (h : ℕ)
    (t : JSt P × RSt P.Wit P.Stmt K) (ht : RejNil P t.1) (e : JEv P)
    (hc : sigHashCost P e ≤ h) (hs : sigOutCost P Ps e = 0) :
    ∑' o, jointO P A t e o * flagPot P Ps γ (h - sigHashCost P e) o.2.1 ≤
      flagPot P Ps γ h t.1 := by
  rcases e with h' | g | (q | ⟨q, k⟩ | ⟨sid, pid, spk, σ⟩)
  · refine tsum_mul_le_const _ _ _ fun o ho => le_of_eq ?_
    rw [jointO, jointOWith_inl] at ho
    obtain ⟨h1, h2⟩ := filtJO_keep A t _ (filtPre_inl t.1 h') o ho
    exact flagPot_congr Ps γ h h1 h2
  · refine tsum_mul_le_const _ _ _ fun o ho => le_of_eq ?_
    rw [jointO, jointOWith_inr_inl] at ho
    obtain ⟨h1, h2⟩ := filtJO_keep A t _ (filtPre_inr_inl t.1 g) o ho
    exact flagPot_congr Ps γ h h1 h2
  · have hq : q ∈ Ps := by
      by_contra hn
      simp [sigOutCost, hn] at hs
    simp only [sigHashCost, Nat.sub_zero, jointO, jointOWith, tsum_bind_mul]
    refine tsum_mul_le_const _ _ _ fun lt _ => ?_
    unfold signAt
    rcases hsq : t.1.sigs q with _ | c
    · dsimp only
      rw [PMF.map_comp, tsum_map_mul']
      refine flagPot_sign Ps γ h t.1 q hq hsq _ (fun hb => realStep_sign_flag_le
        (A.pub lt.1.1, lt.1.1) (hγ lt.1.1) (t.1.tabs q) (ht q) hb (A.pub lt.1.2)) _
        (fun r => by simp) (fun r => by simp) (fun r q' e => by simp [Function.update_of_ne e])
        (fun r q' e => by simp [Function.update_of_ne e])
    · dsimp only
      rw [PMF.pure_map]
      exact tsum_mul_le_const _ _ _ fun o ho => by
        rw [PMF.mem_support_pure_iff] at ho
        subst ho
        exact le_of_eq (flagPot_congr Ps γ h rfl rfl)
  · have hh : 1 ≤ h := hc
    refine tsum_mul_le_const _ _ _ fun o ho => ?_
    simp only [jointO, jointOWith, hashAt, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
      Set.mem_image] at ho
    obtain ⟨lt, -, r, ⟨z, hz, rfl⟩, rfl⟩ := ho
    exact flagPot_hashStep Ps γ h hh t.1 ht q _ k z hz _ rfl rfl
  · have hh : 1 ≤ h := hc
    refine tsum_mul_le_const _ _ _ fun o ho => ?_
    simp only [jointO, jointOWith] at ho
    split at ho
    · rw [PMF.mem_support_pure_iff] at ho
      subst ho
      exact (le_of_eq (flagPot_congr Ps γ _ rfl rfl)).trans (flagPot_mono Ps γ (Nat.sub_le h 1) _)
    · rename_i q _
      simp only [hashAt, PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at ho
      obtain ⟨lt, -, r, ⟨z, hz, rfl⟩, ho⟩ := ho
      have hst : o.2.1 = { t.1 with tabs := Function.update t.1.tabs q z.2, ph := .inj } := by
        split at ho
        · simp only [PMF.support_map, Set.mem_image] at ho
          obtain ⟨c, -, rfl⟩ := ho
          rfl
        · rw [PMF.mem_support_pure_iff] at ho
          subst ho
          rfl
      rw [hst]
      exact flagPot_hashStep Ps γ h hh t.1 ht q _ _ z hz _ rfl rfl

open Classical in
/-- **The probability of a flag.** From a state without hidden entries, a run of the real
protocol by an environment with at most `h` queries of the random oracles of the signatures and
signatures of the parties in `Ps` only sets some flag with probability at most the potential. -/
theorem run_jointO_flag_le (hacc : ∀ z, P.accept z = true) (A : AKEAlg P.Wit P.Stmt)
    {γ : ℝ≥0∞} (hγ : ∀ w, P.CommitBoundAt (A.pub w) w γ) (Ps : Finset PartyId) {α : Type}
    (B : OracleAdv (JEv P) (JOut P K) α) (h : ℕ) (hB1 : B.IsQueryBoundBy (sigHashCost P) h)
    (hB2 : B.IsQueryBoundBy (sigOutCost P Ps) 0) (t : JSt P × RSt P.Wit P.Stmt K)
    (ht : RejNil P t.1) :
    ∑' y, OracleAdv.run (jointO P A) B t y * (if JFlagged P y.2.1 then 1 else 0) ≤
      flagPot P Ps γ h t.1 := by
  induction B generalizing h t with
  | ret a =>
    refine tsum_mul_le_const _ _ _ fun y hy => ?_
    rw [OracleAdv.run_ret, PMF.mem_support_pure_iff] at hy
    subst hy
    exact le_self_add
  | rand p k ih =>
    simp only [OracleAdv.run_rand, tsum_bind_mul]
    exact tsum_mul_le_const _ _ _ fun b _ => ih b h (hB1 b) (hB2 b) t ht
  | query e k ih =>
    simp only [OracleAdv.run_query, tsum_bind_mul]
    obtain ⟨hc, hk1⟩ := hB1
    obtain ⟨hs, hk2⟩ := hB2
    refine le_trans (tsum_mul_le_of_support _ _ _ fun o ho => ih o.1 (h - sigHashCost P e)
      (hk1 o.1) (by simpa using hk2 o.1) o.2 (jointO_rejNil hacc A t ht e o ho)) ?_
    exact jointO_flag_step_le A hγ Ps h t ht e hc (Nat.le_zero.mp hs)

omit [Fintype P.Wit] [Nonempty P.Wit] [Fintype K] [Nonempty K] in
open Classical in
/-- The potential at the initial state is the bound of the hop. -/
theorem flagPot_jInit (Ps : Finset PartyId) (γ : ℝ≥0∞) (qH : ℕ) :
    flagPot P Ps γ qH (jInit P (K := K)).1 = δSig Ps qH γ := by
  have hJ : ¬ JFlagged P (jInit P (K := K)).1 := fun ⟨q, hq⟩ => Bool.false_ne_true hq
  unfold flagPot δSig
  rw [ite_eq_right hJ, zero_add]
  simp [jInit, JSt.init, Protocol.Tables.empty, Protocol.Tables.keys, Finset.sum_const,
    nsmul_eq_mul, mul_assoc]

/-- **Real signatures to simulated signatures, as a bound for each output.** -/
theorem jointO_apply_le (hacc : ∀ z, P.accept z = true) (A : AKEAlg P.Wit P.Stmt)
    (hZK : ∀ w, (fsOf P).StatHVZKAt (A.pub w) w 0) {γ : ℝ≥0∞}
    (hγ : ∀ w, P.CommitBoundAt (A.pub w) w γ) (Ps : Finset PartyId) (qH : ℕ)
    (B : OracleAdv (JEv P) (JOut P K) Bool) (hB : SigHashBound P Ps qH B) (b₀ : Bool) :
    (OracleAdv.run (jointO P A) B (jInit P)).map Prod.fst b₀ ≤
      (OracleAdv.run (simSignO P A) B (jInit P)).map Prod.fst b₀ + δSig Ps qH γ := by
  classical
  have hinit : RejNil P (jInit P (K := K)).1 := fun _ => rfl
  set g : Bool → ℝ≥0∞ := fun b => if b = b₀ then 1 else 0 with hg
  have hmap : ∀ p : PMF (Bool × (JSt P × RSt P.Wit P.Stmt K)),
      p.map Prod.fst b₀ = ∑' y, p y * g y.1 := by
    intro p
    rw [← tsum_map_mul' p Prod.fst g, hg]
    simp
  rw [hmap, hmap]
  have hflag := run_jointO_flag_le hacc A hγ Ps B qH hB.1 hB.2 (jInit P) hinit
  rw [flagPot_jInit] at hflag
  calc _ ≤ ∑' y, OracleAdv.run (jointO P A) B (jInit P) y *
        (offJ P (fun y => g y.1) y + if JFlagged P y.2.1 then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun y => mul_le_mul_right ?_ _
        unfold offJ
        split_ifs
        · rw [hg, zero_add]
          dsimp only
          split_ifs <;> simp
        · rw [add_zero]
    _ = ∑' y, OracleAdv.run (jointO P A) B (jInit P) y * offJ P (fun y => g y.1) y +
        ∑' y, OracleAdv.run (jointO P A) B (jInit P) y *
          (if JFlagged P y.2.1 then 1 else 0) := by
        simp only [mul_add]
        rw [ENNReal.tsum_add]
    _ ≤ _ := add_le_add (run_jointO_offJ_le hacc A hZK g (fun b => by
        rw [hg]; dsimp only; split_ifs <;> simp) B (jInit P) hinit) hflag

/-- **Hop 1 of the joint-key model of X3DH: real signatures to simulated signatures.** For a
Σ-protocol that accepts every response, with perfect HVZK and the commitment bound `γ` at
every pair `(pub w, w)`, and an environment `B` with at most `qH` queries of the random oracles
of the signatures that requests signatures of the parties in `Ps` only, the real protocol and
the protocol with simulated signatures, from the initial state, are at distance at most
`δSig Ps qH γ = |Ps| · qH · γ`. -/
theorem joint_sig_hop_of (hacc : ∀ z, P.accept z = true) (A : AKEAlg P.Wit P.Stmt)
    (hZK : ∀ w, (fsOf P).StatHVZKAt (A.pub w) w 0) {γ : ℝ≥0∞}
    (hγ : ∀ w, P.CommitBoundAt (A.pub w) w γ) (Ps : Finset PartyId) (qH : ℕ)
    (B : OracleAdv (JEv P) (JOut P K) Bool) (hB : SigHashBound P Ps qH B) :
    absDiff ((OracleAdv.run (jointO P A) B (jInit P)).map Prod.fst true)
      ((OracleAdv.run (simSignO P A) B (jInit P)).map Prod.fst true) ≤ δSig Ps qH γ := by
  have h1 := jointO_apply_le hacc A hZK hγ Ps qH B hB true
  have h2 := jointO_apply_le hacc A hZK hγ Ps qH B hB false
  set pr := (OracleAdv.run (jointO P A) B (jInit P)).map Prod.fst
  set ps := (OracleAdv.run (simSignO P A) B (jInit P)).map Prod.fst
  have hsum : ∀ p : PMF Bool, p false + p true = 1 := fun p => by
    rw [← tsum_bool, PMF.tsum_coe]
  refine sup_le (tsub_le_iff_left.mpr h1) (tsub_le_iff_left.mpr ?_)
  have hne : pr false ≠ ⊤ := PMF.apply_ne_top pr false
  refine (ENNReal.add_le_add_iff_left hne).mp ?_
  calc pr false + ps true ≤ ps false + δSig Ps qH γ + ps true := add_le_add h2 le_rfl
    _ = pr false + pr true + δSig Ps qH γ := by rw [add_right_comm, hsum, hsum]
    _ = _ := by ring

end Flag

/-! ## Schnorr at the Diffie–Hellman group -/

section Schnorr

open CatCrypt.Crypto.PAKE.DHExtract

variable {S W : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  {K : Type} [Fintype K] [Nonempty K]

/-- The pair of the public identity key and its secret is a generated pair of Schnorr at
`ofDHGroup G`. -/
theorem x3dhJointAlg_pub_mem_gen (G : DHGroup S W) (w : S) :
    ((x3dhJointAlg G).pub w, w) ∈ (schnorrSigma (GroupParam.ofDHGroup G)).gen.support :=
  (PMF.mem_support_map_iff _ _ _).mpr ⟨w, PMF.mem_support_uniformFintype w, rfl⟩

/-- **Hop 1 of the joint-key model of X3DH over the Diffie–Hellman group `G`.** For an
environment `B` with at most `qH` queries of the random oracles of the signatures that requests
signatures of the parties in `Ps` only, the real protocol of X3DH with Schnorr signatures under
the identity key and the protocol with simulated Schnorr signatures, from the initial state, are
at distance at most `|Ps| · qH / |S|`. -/
theorem joint_sig_hop (G : DHGroup S W) (Ps : Finset PartyId) (qH : ℕ)
    (B : OracleAdv (JEv (schnorrSigma (GroupParam.ofDHGroup G)))
      (JOut (schnorrSigma (GroupParam.ofDHGroup G)) K) Bool)
    (hB : SigHashBound _ Ps qH B) :
    absDiff ((OracleAdv.run (jointO _ (x3dhJointAlg G).toAKEAlg) B (jInit _)).map Prod.fst true)
      ((OracleAdv.run (simSignO _ (x3dhJointAlg G).toAKEAlg) B (jInit _)).map Prod.fst true) ≤
      δSig Ps qH (1 / Fintype.card S) :=
  joint_sig_hop_of (fun _ => rfl) _
    (fun w => Sigma.statHVZKAt_toProtocol _
      ((schnorrSigma_ofDHGroup_perfectHVZK G).statHVZK _ _ (x3dhJointAlg_pub_mem_gen G w)))
    (fun w => schnorrSigma_ofDHGroup_commitBound G _ _ (x3dhJointAlg_pub_mem_gen G w)) Ps qH B hB

end Schnorr

end CatCrypt.Crypto.AKE.X3DHSquare
