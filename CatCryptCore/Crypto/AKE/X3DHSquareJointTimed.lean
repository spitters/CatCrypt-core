/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareJoint
public import CatCryptCore.Crypto.AKE.X3DHSquareJointSimTimed
public import CatCryptCore.Crypto.AKE.X3DHSquareSignedTimed
public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Running time of the simulator of X3DH with a joint identity and signing key

The simulator `x3dhJointSim` is the layer `sigLayerJ` over the X3DH simulator `x3dhSimC`. This
file gives the costed steps of the one-call layer `sigLayerJH`: `jPreT` and `jPostT`, each the
distribution of `jPre` or `jPost` as one sampling node (`pmfT`), and `jPreS`, `jPostS`, which
return points of the support (`pmfS`). The costed layer `jLayerS` at the steps `jPreS`, `jPostS`
erases to `sigLayerJH` and has a potential time bound in the size `jsize` of its tables: the
peers of the sessions, the signatures, the identity keys of the corrupted parties and the
entries of the Fiat–Shamir tables of all parties. The step cost of the layer is the cost of its
decisions, of a lookup in the Fiat–Shamir table of one party and of a simulated signature
(`FiatShamirROM.simStep`).

`derive_simulator` builds the costed form `x3dhJointSim.timed` from the costed layer and the
costed X3DH simulator `x3dhSimC.timed` of `X3DHSquareJointSimTimed.lean`, with its erasure and
its graded time bound at layer steps of bounded cost. At the steps `jPreS`, `jPostS`, whose cost
grows with `jsize`, the potential certificate of the layer composes with the graded certificate
of `x3dhSimC` (`x3dhJointSim.timeBoundPot_timed`).

No module imports this file.

## Main results

* `jPre_grow`, `jPost_grow`: a step of the layer adds at most one entry at an event and three
  at an answer.
* `jLayerS_erases`, `jLayerS_potentialBound`: the costed layer erases to `sigLayerJH` and has a
  potential time bound in `jsize`.
* `x3dhJointSim.timed`, `x3dhJointSim.erase_timed`, `x3dhJointSim.timeBoundGraded_timed`: the
  costed simulator, its erasure and its graded time bound.
* `x3dhJointSim_erases_support`, `x3dhJointSim.timeBoundPot_timed`: its erasure and its
  potential time bound at the steps `jPreS`, `jPostS`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.FiatShamirROM CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.AKE.X3DHSquareSigned (pmfT pmfT_erase pmfT_time)

section Simulator

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt] {K : Type}

/-- The costed `pre` step of the joint signature layer: the distribution of `jPre` as one
sampling node. -/
noncomputable def jPreT (l : JSt P) (e : JEv P) : SPTree.Timed (JSt P × CEv P.Stmt) :=
  pmfT (jPre P l e)

/-- The costed `post` step of the joint signature layer: the distribution of `jPost` as one
sampling node. -/
noncomputable def jPostT (pub : P.Wit → P.Stmt) (l : JSt P) (o : OOut P.Wit P.Stmt K) :
    SPTree.Timed (JSt P × JOut P K) :=
  pmfT (jPost P pub l o)

end Simulator

/-! ## The potential certificate of the simulator -/

section Potential

open CatCrypt.Crypto.OracleForking
open CatCrypt.Crypto.AKE.X3DHSquareSigned (pmfS pmfS_erase pmfS_time allRet_pmfS
  ncard_update_isSome_le)

/-- A sum over a finite support grows by at most `k` when one value grows by at most `k`. -/
theorem finsum_le_of_update {α : Type} (f g : α → ℕ) (a : α) (k : ℕ)
    (hf : (Function.support f).Finite) (hg : ∀ x, x ≠ a → g x = f x) (ha : g a ≤ f a + k) :
    (Function.support g).Finite ∧ ∑ᶠ x, g x ≤ ∑ᶠ x, f x + k := by
  classical
  have hsub : Function.support g ⊆ insert a (Function.support f) := by
    intro x hx
    by_cases h : x = a
    · simp [h]
    · exact Set.mem_insert_of_mem _ (by rw [Function.mem_support, ← hg x h]; exact hx)
  have hT := hf.insert a
  refine ⟨hT.subset hsub, ?_⟩
  rw [finsum_eq_sum_of_support_subset g (s := hT.toFinset) (by simpa using hsub),
    finsum_eq_sum_of_support_subset f (s := hT.toFinset) (by simp [Set.subset_insert])]
  have hmem : a ∈ hT.toFinset := by simp
  rw [← Finset.add_sum_erase _ g hmem, ← Finset.add_sum_erase _ f hmem,
    Finset.sum_congr rfl fun x hx => hg x (Finset.ne_of_mem_erase hx)]
  grind

/-- Programming the entries `l` adds at most `l.length` entries. -/
theorem programAll_size {G : FiatShamirROM.Protocol} :
    ∀ (t : G.Tables) (b : Bool) (l : List (G.Key × G.Ch)),
      (programAll t b l).1.size ≤ t.size + l.length := by
  intro t b l
  induction l generalizing t b with
  | nil => simp [programAll]
  | cons p l ih =>
    unfold programAll
    split
    · have := ih t true
      simp only [List.length_cons]
      omega
    · have := ih { t with prog := t.prog ++ [p] } b
      simp only [Protocol.Tables.size, List.length_append, List.length_cons,
        List.length_nil] at this ⊢
      omega

/-- Recording the answers `l` adds at most `l.length` entries. -/
theorem hashAll_size {G : FiatShamirROM.Protocol} (t : G.Tables) (l : List (G.Key × G.Ch)) :
    (hashAll t l).size ≤ t.size + l.length := by
  have := List.length_filter_le (fun p => (t.lookup p.1).isNone) l
  simp only [hashAll, Protocol.Tables.size, List.length_append]
  omega

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt]

/-- A hash query adds at most one entry to the tables. -/
theorem hashStep_grow (t : FSt P) (k : (fsOf P).Key) :
    ∀ y ∈ (toOracle (fun s k => hashStep s.1 s.2 k) t k).support, y.2.1.size ≤ t.1.size + 1 := by
  intro y hy
  simp only [toOracle, hashStep] at hy
  split at hy
  · simp_all [Step.toPMF]
  · simp only [Step.toPMF, PMF.support_map, Set.mem_image] at hy
    obtain ⟨e, -, rfl⟩ := hy
    simp only [Protocol.Tables.size, List.length_append, List.length_singleton]
    omega

/-- A simulated signing query of the Fiat–Shamir signature of a Σ-protocol adds at most two
entries to the tables: one evaluated entry and one programmed entry. -/
theorem simSign_grow (ik : P.Stmt) (t : FSt P) (m : P.Stmt) :
    ∀ y ∈ (toOracle (FiatShamirROM.simStep ik) t (.inr m)).support,
      y.2.1.size ≤ t.1.size + 2 := by
  intro y hy
  simp only [toOracle, FiatShamirROM.simStep, Step.toPMF, sampleVec, PMF.support_bind,
    PMF.support_map, Set.mem_iUnion, Set.mem_image] at hy
  obtain ⟨e, -, s, -, rfl⟩ := hy
  have h1 := hashAll_size t.1 ((fsOf P).simTrace t.1.lookup ik m e s).1
  have h2 := programAll_size (hashAll t.1 ((fsOf P).simTrace t.1.lookup ik m e s).1) t.2
    ((fsOf P).simTrace t.1.lookup ik m e s).2.1
  have h3 : ((fsOf P).simTrace t.1.lookup ik m e s).1.length ≤ 1 := by
    simp only [Protocol.simTrace]
    exact (List.length_filterMap_le _ _).trans (by simp)
  have h4 : ((fsOf P).simTrace t.1.lookup ik m e s).2.1.length ≤ 1 := by
    simp only [Protocol.simTrace]
    split <;> simp
  simp only [simSignOut, traceOut, programOut, Protocol.Tables.size] at h1 h2 ⊢
  omega

/-- The size of the state of the joint signature layer: the number of sessions with a peer, of
parties that signed, of parties recorded corrupted, and of the entries of the Fiat–Shamir tables
of all parties. -/
noncomputable def jsize (l : JSt P) : ℕ :=
  {x | (l.peers x).isSome}.ncard + {q | (l.sigs q).isSome}.ncard +
    {q | (l.corr q).isSome}.ncard + ∑ᶠ q, (l.tabs q).1.size

/-- The tables of the state of the joint signature layer are finite. -/
def JFin (l : JSt P) : Prop :=
  {x | (l.peers x).isSome}.Finite ∧ {q | (l.sigs q).isSome}.Finite ∧
    {q | (l.corr q).isSome}.Finite ∧ (Function.support fun q => (l.tabs q).1.size).Finite

/-- The initial state of the joint signature layer has finite (empty) tables. -/
theorem jfin_init : JFin P (JSt.init P) := by
  simp [JFin, JSt.init, Protocol.Tables.empty, Protocol.Tables.size]

/-- Recording the peer of a session adds at most one entry. -/
theorem jsize_notePeer (l : JSt P) (x : Inst) (p : PartyId) (hl : JFin P l) :
    JFin P (notePeerJ P l x p) ∧ jsize P (notePeerJ P l x p) ≤ jsize P l + 1 := by
  unfold notePeerJ
  split
  · exact ⟨hl, by omega⟩
  · obtain ⟨h1, h2⟩ := ncard_update_isSome_le l.peers x (some p) hl.1
    exact ⟨⟨h1, hl.2⟩, by simp only [jsize]; omega⟩

/-- Recording the identity key of a corrupted party adds at most one entry. -/
theorem jsize_corr_update (l : JSt P) (q : PartyId) (v : Option P.Stmt) (hl : JFin P l) :
    JFin P { l with corr := Function.update l.corr q v } ∧
      jsize P { l with corr := Function.update l.corr q v } ≤ jsize P l + 1 := by
  obtain ⟨h1, h2⟩ := ncard_update_isSome_le l.corr q v hl.2.2.1
  exact ⟨⟨hl.1, hl.2.1, h1, hl.2.2.2⟩, by simp only [jsize]; omega⟩

/-- Replacing the tables of `q` by tables of at most `k` more entries adds at most `k` entries. -/
theorem jsize_tabs_update (l : JSt P) (q : PartyId) (r : FSt P) {k : ℕ}
    (hr : r.1.size ≤ (l.tabs q).1.size + k) (hl : JFin P l) :
    JFin P { l with tabs := Function.update l.tabs q r } ∧
      jsize P { l with tabs := Function.update l.tabs q r } ≤ jsize P l + k := by
  obtain ⟨h1, h2⟩ := finsum_le_of_update (fun q' => (l.tabs q').1.size)
    (fun q' => (Function.update l.tabs q r q').1.size) q k hl.2.2.2
    (fun x hx => by simp [Function.update_of_ne hx]) (by simpa using hr)
  exact ⟨⟨hl.1, hl.2.1, hl.2.2.1, h1⟩, by simp only [jsize] at h2 ⊢; omega⟩

/-- Recording the signature of `q` adds at most one entry. -/
theorem jsize_sigs_update (l : JSt P) (q : PartyId)
    (v : Option (P.Stmt × P.Stmt × Option (P.Com × P.Resp))) (hl : JFin P l) :
    JFin P { l with sigs := Function.update l.sigs q v } ∧
      jsize P { l with sigs := Function.update l.sigs q v } ≤ jsize P l + 1 := by
  obtain ⟨h1, h2⟩ := ncard_update_isSome_le l.sigs q v hl.2.1
  exact ⟨⟨hl.1, h1, hl.2.2⟩, by simp only [jsize]; omega⟩

/-- A hash query at the tables of `q` adds at most one entry. -/
theorem hashAt_grow (H : FSt P → (fsOf P).Key → Step (fsOf P).Answer (FSt P) P.Ch)
    (hH : ∀ s k, ∀ y ∈ (toOracle H s k).support, y.2.1.size ≤ s.1.size + 1)
    (l : JSt P) (q : PartyId) (k : (fsOf P).Key) (hl : JFin P l) :
    ∀ y ∈ (hashAt P H l q k).support, JFin P y.2 ∧ jsize P y.2 ≤ jsize P l + 1 := by
  intro y hy
  simp only [hashAt, PMF.support_map, Set.mem_image] at hy
  obtain ⟨r, hr, rfl⟩ := hy
  exact jsize_tabs_update P l q r.2 (hH _ _ r hr) hl

/-- A `pre` step of the joint signature layer adds at most one entry to its tables. -/
theorem jPre_grow (l : JSt P) (e : JEv P) (hl : JFin P l) :
    ∀ y ∈ (jPre P l e).support, JFin P y.1 ∧ jsize P y.1 ≤ jsize P l + 1 := by
  intro y hy
  rcases e with ((⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (a' | (q' | ⟨q', k'⟩ | ⟨sid, pid, spk, σ⟩)))
  · simp only [jPre, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact jsize_notePeer P l _ peer hl
  · simp only [jPre, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hl, by simp only [jsize]; omega⟩
  · cases a' <;> simp only [jPre, PMF.support_pure, Set.mem_singleton_iff] at hy <;>
      subst hy <;> exact ⟨hl, by simp only [jsize]; omega⟩
  · simp only [jPre, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hl, by simp only [jsize]; omega⟩
  · simp only [jPre, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hl, by simp only [jsize]; omega⟩
  · simp only [jPre] at hy
    split at hy
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hl, by simp only [jsize]; omega⟩
    · simp only [PMF.support_map, Set.mem_image] at hy
      obtain ⟨r, hr, rfl⟩ := hy
      exact hashAt_grow P _ (hashStep_grow P) l _ _ hl r hr

/-- A `post` step of the joint signature layer adds at most three entries to its tables: a
signature and two entries of the tables of the signer, one entry of a hash query, or the
identity key of a corrupted party. -/
theorem jPost_grow {K : Type} (pub : P.Wit → P.Stmt) (l : JSt P) (o : OOut P.Wit P.Stmt K)
    (hl : JFin P l) :
    ∀ y ∈ (jPost P pub l o).support, JFin P y.1 ∧ jsize P y.1 ≤ jsize P l + 3 := by
  intro y hy
  unfold jPost at hy
  split at hy
  rotate_left 2
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨h1, h2⟩ := jsize_corr_update P l _ (some (pub _)) hl
    exact ⟨h1, by dsimp only at h2 ⊢; omega⟩
  rotate_left 1
  · simp only [PMF.support_map, Set.mem_image] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    unfold signAt at hr
    split at hr
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨hl, by dsimp only; omega⟩
    · simp only [PMF.support_map, Set.mem_image] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      obtain ⟨h1, h2⟩ := jsize_tabs_update P l _ r'.2 (simSign_grow P _ _ _ r' hr') hl
      obtain ⟨h3, h4⟩ := jsize_sigs_update P _ _ (some (_, _, sigOf P r'.1)) h1
      exact ⟨h3, by dsimp only at h4 ⊢; omega⟩
  · simp only [PMF.support_map, Set.mem_image] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    have := hashAt_grow P _ (fun s k => hashStep_grow P s k) l _ _ hl r hr
    exact ⟨this.1, by dsimp only; omega⟩
  all_goals
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hl, by dsimp only; omega⟩

/-- The costed `pre` step of the joint signature layer on the support: the distribution of
`jPre` as one sampling node that returns points of its support. -/
noncomputable def jPreS (l : JSt P) (e : JEv P) : SPTree.Timed (JSt P × CEv P.Stmt) :=
  pmfS (jPre P l e)

/-- The costed `post` step of the joint signature layer on the support: the distribution of
`jPost` as one sampling node that returns points of its support. -/
noncomputable def jPostS {K : Type} (pub : P.Wit → P.Stmt) (l : JSt P)
    (o : OOut P.Wit P.Stmt K) : SPTree.Timed (JSt P × JOut P K) :=
  pmfS (jPost P pub l o)

/-- The costed joint signature layer at the steps `jPreS`, `jPostS` and the step costs
`preCost`, `postCost`. -/
noncomputable def jLayerS {K : Type} (pub : P.Wit → P.Stmt) (preCost : JSt P → JEv P → ℕ)
    (postCost : JSt P → OOut P.Wit P.Stmt K → ℕ) :
    Hybrid.Timed (JSt P) (JEv P) (JOut P K) (CEv P.Stmt) (OOut P.Wit P.Stmt K) :=
  ⟨JSt.init P, jPreS P, preCost, jPostS P pub, postCost⟩

/-- The costed joint signature layer `jLayerS` erases to `sigLayerJH P pub`. -/
theorem jLayerS_erases {K : Type} (pub : P.Wit → P.Stmt) (preCost : JSt P → JEv P → ℕ)
    (postCost : JSt P → OOut P.Wit P.Stmt K → ℕ) :
    (jLayerS P pub preCost postCost).Erases (sigLayerJH P pub) :=
  ⟨fun _ _ => by dsimp only [jLayerS, jPreS]; rw [pmfS_erase]; exact liftPMF_noFail _,
    fun _ _ => by dsimp only [jLayerS, jPostS]; rw [pmfS_erase]; exact liftPMF_noFail _,
    by dsimp only [jLayerS, jPreS, jPostS]; simp only [pmfS_erase]; rfl⟩

/-- **Potential time bound of the costed joint signature layer.** With the potential `jsize`
(peers of sessions, signatures, entries of the Fiat–Shamir tables) and step costs at most
`tl + tk · jsize l`, a `pre` step costs at most `tl + 1 + tk · (jsize l + 1)` and adds at most
one entry, a `post` step at most `tl + 1 + tk · (jsize l + 3)` and adds at most three. -/
noncomputable def jLayerS_potentialBound {K : Type} (pub : P.Wit → P.Stmt)
    (preCost : JSt P → JEv P → ℕ)
    (postCost : JSt P → OOut P.Wit P.Stmt K → ℕ) {tl tk : ℕ}
    (hpre : ∀ l e, preCost l e ≤ tl + tk * jsize P l)
    (hpost : ∀ l o, postCost l o ≤ tl + tk * jsize P l) :
    (jLayerS P pub preCost postCost).PotentialBound (fun _ => 1) (fun _ => 3) 0 0 (tl + 1) tk where
  Inv := JFin P
  Φ := jsize P
  init := jfin_init P
  pre s e hs := by
    refine ⟨?_, allRet_pmfS _ fun y hy => ?_⟩
    · have := hpre s e
      simp only [jLayerS, jPreS, SPTree.Timed.stepTime, pmfS_time]
      grind
    · have := jPre_grow P s e hs y hy
      simpa using this
  post s o hs := by
    refine ⟨?_, allRet_pmfS _ fun y hy => ?_⟩
    · have := hpost s o
      simp only [jLayerS, jPostS, SPTree.Timed.stepTime, pmfS_time]
      grind
    · have := jPost_grow P pub s o hs y hy
      simpa using this

end Potential

/-! ## The certificate of the simulator -/

derive_simulator x3dhJointSim

section JointPotential

open CatCrypt.Crypto.AKE.X3DHSquareSigned (pmfS_erase)

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K]

/-- **Erasure of the costed simulator of X3DH with a joint identity and signing key at the steps
on the support**: the derived costed form `x3dhJointSim.timed` at the costed steps `jPreS`,
`jPostS` of the layer erases to `x3dhJointSim G`. -/
theorem x3dhJointSim_erases_support (G : DHGroup S W)
    (preCost : JSt (schnorrSigma (Examples.GroupParam.ofDHGroup G)) →
      JEv (schnorrSigma (Examples.GroupParam.ofDHGroup G)) → ℕ)
    (postCost : JSt (schnorrSigma (Examples.GroupParam.ofDHGroup G)) →
      OOut (schnorrSigma (Examples.GroupParam.ofDHGroup G)).Wit
        (schnorrSigma (Examples.GroupParam.ofDHGroup G)).Stmt K → ℕ)
    (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ) (toFunCost : S → ℕ) :
    (x3dhJointSim.timed (K := K) G (jPreS _) preCost (jPostS _ (x3dhJointAlg G).pub) postCost
      coeCost expCost toFunCost).Erases (x3dhJointSim G) :=
  x3dhJointSim.erase_timed G _ _ _ _ coeCost expCost toFunCost
    (fun _ _ => pmfS_erase _) (fun _ _ => pmfS_erase _)

/-- **Potential running time of the costed simulator of X3DH with a joint identity and signing
key.** At the costed steps `jPreS`, `jPostS` of the layer, with step costs at most
`tl + tk · jsize l` in the size `jsize l` of the tables of the layer, and group operations of
costs at most `tc`, `te`, `tf`, the costed simulator has the potential time bound with the
import `1` of every outer event and answer, the constants
`tl + 2 + 202 + 20 tc + 20 te + 20 tf` and `tk + 40`, and the import `3` created per
activation: the potential is the size of the tables of the layer plus that of the X3DH
simulator below (the least activation count of its graded invariant), the layer adds at most
one entry at an event and three at an answer, and the X3DH simulator at most one activation per
message. -/
theorem x3dhJointSim.timeBoundPot_timed (G : DHGroup S W)
    (preCost : JSt (schnorrSigma (Examples.GroupParam.ofDHGroup G)) →
      JEv (schnorrSigma (Examples.GroupParam.ofDHGroup G)) → ℕ)
    (postCost : JSt (schnorrSigma (Examples.GroupParam.ofDHGroup G)) →
      OOut (schnorrSigma (Examples.GroupParam.ofDHGroup G)).Wit
        (schnorrSigma (Examples.GroupParam.ofDHGroup G)).Stmt K → ℕ)
    (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ) (toFunCost : S → ℕ)
    {tl tk tc te tf : ℕ}
    (hpre : ∀ l e, preCost l e ≤ tl + tk * jsize _ l)
    (hpost : ∀ l o, postCost l o ≤ tl + tk * jsize _ l) (hc : ∀ a b, coeCost a b ≤ tc)
    (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf) :
    (x3dhJointSim.timed (K := K) G (jPreS _) preCost (jPostS _ (x3dhJointAlg G).pub) postCost
      coeCost expCost toFunCost).TimeBoundPot (fun _ => 1) 1 0 0
      (tl + 2 + (202 + 20 * tc + 20 * te + 20 * tf)) (tk + 40) 3 := by
  have P := jLayerS_potentialBound _ (x3dhJointAlg G).pub preCost postCost hpre hpost
  have P' := Hybrid.Timed.PotentialBound.ofHybrid
    (jLayerS_erases _ (x3dhJointAlg G).pub preCost postCost) P
  have h₂ := (x3dhSimC.timeBoundGraded_timed (K := K) G coeCost expCost toFunCost hc he
    hf).timeBoundPot
  have h : (x3dhJointSim.timed (K := K) G (jPreS _) preCost (jPostS _ (x3dhJointAlg G).pub)
      postCost coeCost expCost toFunCost).TimeBoundPot (fun _ => 1) 1 0 0
      (tl + 1 + 1 + (202 + (20 * tc + (20 * te + 20 * tf)))) (tk + 40)
      (0 + (x3dhSimC.timed (K := K) G coeCost expCost toFunCost).compCount + 3) :=
    Simulator.comp.timeBoundPot_timed (κ := 3) (Simulator.ofMultiHybrid.timeBoundPot_timed P') h₂
      (fun _ => Nat.le_add_left 1 2) (fun _ => le_rfl)
  exact h.mono (by omega) le_rfl (by simp [x3dhSimC.timed, Simulator.Timed.compCount])
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)

end JointPotential

end CatCrypt.Crypto.AKE.X3DHSquare
