/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.DoubleRatchet
public import CatCryptCore.Crypto.Messaging.KEMCKA
public import CatCryptCore.Crypto.Assumptions.DualPRF

/-!
# The triple ratchet: confidentiality if either DDH or the KEM is secure

The triple ratchet of Dodis, Jost, Katsumata, Prest and Schmidt (Signal's SPQR) runs the
Diffie–Hellman CKA and a KEM CKA in parallel: its CKA is `prodCKA (dhCKA G) (kemCKA KEM)`,
whose epoch key is the pair `(k₁, k₂)` of the Diffie–Hellman key and the KEM key, and the root
step combines both keys with the root key. The secure-messaging game is the game
`sm_real`/`sm_ideal` of the double ratchet (`CatCryptCore.Crypto.Messaging.DoubleRatchet`)
over this CKA.

## The root step

The root step is modelled by a dual PRF `F : RK × K₁ → K₂ → RK × Sa`: the root KDF is
`trRoot F`, which maps the root key `rk` and the epoch key `(k₁, k₂)` to
`F (rk, k₁) k₂`, the next root key and the FS-AEAD state of the epoch. This is the KDF
`KDF(rk, dh ‖ pq)` of the triple ratchet with the input split between the concatenation
`rk ‖ dh` of the root key and the Diffie–Hellman secret (the left argument) and the KEM secret
`pq` (the right argument), as in the dual-PRF combiners of hybrid key exchange (Bindel,
Brendel, Fischlin, Goncalves and Stebila). The two assumptions are

* `DualPRF_Left_Advantage F`: `F (rk, k₁) ·` is a PRF under a uniform root key and a uniform
  Diffie–Hellman key, with the KEM key chosen by the adversary;
* `DualPRF_Right_Advantage F`: `F · k₂` is a PRF under a uniform KEM key, with the root key and
  the Diffie–Hellman key chosen by the adversary.

## The two chains

The proof follows the double ratchet with one change: in the CKA phase only one component of
each epoch key is replaced by a uniform value, and the other component stays the real key of
the run, known to the adversary and correlated with the transcript. A replacement
`mix : X → Key → Key` (`mixLeft`, `mixRight`) describes which component is replaced. The
phases are

1. CKA hybrids `trHybK` (the hop at epoch `t` is the distance between `cka_real` and
   `cka_mix`, the game in which only one component of the challenge key is uniform, at
   `trCKARed`); for the product CKA this distance is the CKA advantage of the component, the
   one-sided product hybrid `prodCKA_left_advantage_eq` / `prodCKA_right_advantage_eq`, at
   `prodCKARed₁` / `prodCKARedR`;
2. root hybrids `trHybP` (the hop at epoch `t`, `trRoot_real`/`trRoot_ideal`, replaces the
   root step on a uniform root key and a key with one uniform component by a uniform output);
   for the root step `trRoot F` the hop is a dual-PRF game with one query
   (`trRoot_left_advantage_eq`, `trRoot_right_advantage_eq`) at `trRootRedL` / `trRootRedR`;
3. the FS-AEAD hybrids `smHybF` of the double ratchet and their lemmas, unchanged.

The hybrids `smHybK` and `smHybP` of the double ratchet replace whole keys and sample them
independently of the transcript, so phases 1 and 2 use the generalisations `trHybK` and
`trHybP`, in which the replaced keys are `mix u I` for the real keys `I` of the run;
`trHybK_eq_smHybK` states that `trHybK` with `mix u _ = u` is `smHybK`.

The DDH chain replaces the Diffie–Hellman components and uses `cka_advantage_eq_ddh`; the KEM
chain replaces the KEM components and uses `kemCKA_advantage_eq`. Each chain bounds the
advantage, so the advantage is at most their minimum (`tr_advantage_le_min`), as in
`CatCrypt.Crypto.AKE.KeySchedule.hybridAdvantage_le_min`.

The dual-PRF games are games of oracle adversaries (`OracleAdv`); `oneQueryAdv pre q B` is
the oracle adversary that runs the computation `pre`, asks one query and runs the
distinguisher `B` on the answer, and `advantage_oneQuery_eq` identifies its PRF advantage with
the distance between two computations.

## Main definitions

* `mixKeys`, `cka_mix`, `mixLeft`, `mixRight` — partial replacement of CKA keys
* `prodCKARedR` — the CKA reduction of the second component with the real game of the first
* `trHybK`, `trCKAViewL`, `trCKAView`, `trCKARed` — the CKA phase with partial replacement
* `trHybP`, `trRootPub`, `trRootViewL`, `trRootView`, `trRoot_real`, `trRoot_ideal` — the root
  phase
* `runBit`, `oneQueryAdv`, `rootOracleRedOf` — one-query oracle adversaries
* `trRoot` — the root step from a dual PRF
* `trRootPreL`, `trRootRedL`, `trRootPreR`, `trRootRedR` — the dual-PRF reductions

## Main results

* `prodCKA_left_advantage_eq`, `prodCKA_right_advantage_eq` — the one-sided product hybrids
* `advantage_oneQuery_eq` — the PRF advantage of `oneQueryAdv`
* `sm_mix_advantage_le` — the secure-messaging advantage with partial key replacement
* `tr_advantage_le_ddh`, `tr_advantage_le_kem` — the DDH chain and the KEM chain
* `tr_advantage_le_min` — the advantage is at most the minimum of the two chains
* `oneQueryAdv.timeBound_timed`, `rootOracleRedOf.tree.timeBound_timed`,
  `trRootRedL.timeBound_timed`, `trRootRedR.timeBound_timed`, `trCKARed.timeBound_timed`,
  `prodCKARedR.timeBound_timed`, `ckaRun.tree.timeBound_timed` — the times of the costed
  reductions; the costed forms `trRootRedL.timed`, `trRootRedR.timed` (`derive_timed`) and
  `trCKARed.tree.timed`, `prodCKARedR.tree.timed` (`derive_reduction`) and the costs of the
  views `trCKAViewL.timedCost`, `trRootViewL.timedCost` (`derive_cost`) are derived

## References

* Y. Dodis, D. Jost, S. Katsumata, T. Prest, R. Schmidt, *Triple Ratchet: A Bandwidth
  Efficient Hybrid-Secure Signal Protocol*, EUROCRYPT 2025
* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019
* N. Bindel, J. Brendel, M. Fischlin, B. Goncalves, D. Stebila, *Hybrid Key Encapsulation
  Mechanisms and Authenticated Key Exchange*, PQCrypto 2019
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
  CatCrypt.Crypto.PRPPRF CatCrypt.Examples.KEMDEM CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

/-! ## Partial replacement of CKA keys -/

section Mix

variable {Sc Msg Key X : Type}

/-- The keys `ks` with the first `us.length` of them replaced by `mix u k`, for the entries
`u` of `us`. -/
def mixKeys (mix : X → Key → Key) : List X → List Key → List Key
  | [], ks => ks
  | _ :: _, [] => []
  | u :: us, k :: ks => mix u k :: mixKeys mix us ks

/-- `mixKeys` touches only the first `us.length` keys. -/
theorem mixKeys_append (mix : X → Key → Key) (us : List X) (ks ls : List Key)
    (h : us.length = ks.length) : mixKeys mix us (ks ++ ls) = mixKeys mix us ks ++ ls := by
  induction us generalizing ks with
  | nil =>
    cases ks with
    | nil => rfl
    | cons k ks => simp at h
  | cons u us ih =>
    cases ks with
    | nil => simp at h
    | cons k ks =>
      simp only [List.cons_append, mixKeys, ih ks (by simpa using h)]

/-- `mixKeys` at a list of `t + 1` entries and keys `ks ++ k :: ls` with `t` keys in `ks`. -/
theorem mixKeys_snoc (mix : X → Key → Key) (us : List X) (a : X) (ks : List Key) (k : Key)
    (ls : List Key) (h : us.length = ks.length) :
    mixKeys mix (us ++ [a]) (ks ++ k :: ls) = mixKeys mix us ks ++ mix a k :: ls := by
  induction us generalizing ks with
  | nil =>
    cases ks with
    | nil => rfl
    | cons k ks => simp at h
  | cons u us ih =>
    cases ks with
    | nil => simp at h
    | cons k' ks =>
      simp only [List.cons_append, mixKeys, ih ks (by simpa using h)]

/-- The CKA game in which the key of the challenge epoch is `mix u I` for a uniform `u` and
the real key `I`: with `mix u _ = u` it is the ideal game `cka_ideal`, and for a product CKA
with `mix` replacing one component it is the game in which only that component is uniform. -/
noncomputable def cka_mix [Fintype X] [Nonempty X] (C : CKADef Sc Msg Key)
    (mix : X → Key → Key) (k m : ℕ) : SPComp (CKAView Msg Key) :=
  SPComp.bind C.init fun i =>
    SPComp.bind (ckaRun C k i.2.1 i.2.2) fun p =>
      SPComp.bind (C.send p.2.1) fun o =>
        SPComp.bind (SPComp.sample X) fun u =>
          SPComp.bind (ckaRun C m (C.recv p.2.2 o.2.1).1 o.1) fun q =>
            SPComp.pure (i.1, p.1, (o.2.1, mix u o.2.2), q.1)

end Mix

/-! ## The one-sided product hybrid -/

section OneSided

variable {S₁ M₁ K₁ S₂ M₂ K₂ : Type}

/-- Replacement of the first component of a pair key. -/
def mixLeft (u : K₁) (k : K₁ × K₂) : K₁ × K₂ := (u, k.2)

/-- Replacement of the second component of a pair key. -/
def mixRight (u : K₂) (k : K₁ × K₂) : K₁ × K₂ := (k.1, u)

/-- The CKA distinguisher against `C₂` built from the CKA adversary `A` against the product:
it runs the real CKA game of `C₁` and calls `A` on the view of the product. -/
noncomputable def prodCKARedR (C₁ : CKADef S₁ M₁ K₁) (k m : ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPComp Bool) : CKAView M₂ K₂ → SPComp Bool :=
  ckaPubRedOf (cka_real C₁ k m) (fun v₁ v₂ => zipView v₁ v₂) A

/-- The real CKA game of a scheme whose initialisation and sending do not touch the heap does
not touch the heap. -/
theorem cka_real_isPure (C₁ : CKADef S₁ M₁ K₁) (h₀ : SPComp.IsPure C₁.init)
    (h₁ : ∀ s, SPComp.IsPure (C₁.send s)) (k m : ℕ) : SPComp.IsPure (cka_real C₁ k m) :=
  SPComp.bind_isPure h₀ fun _ => SPComp.bind_isPure (ckaRun_isPure C₁ h₁ _ _ _) fun _ =>
    SPComp.bind_isPure (h₁ _) fun _ =>
      SPComp.bind_isPure (ckaRun_isPure C₁ h₁ _ _ _) fun _ => SPComp.pure_isPure _

/-- The product game with a uniform first component of the challenge key is the ideal game of
`C₁` next to the real game of `C₂`, when sending in `C₁` does not touch the heap. -/
theorem cka_mix_left_prod [Fintype K₁] [Nonempty K₁] (C₁ : CKADef S₁ M₁ K₁)
    (C₂ : CKADef S₂ M₂ K₂) (h₁ : ∀ s, SPComp.IsPure (C₁.send s)) (k m : ℕ) :
    cka_mix (prodCKA C₁ C₂) (mixLeft (K₂ := K₂)) k m = prodHyb C₁ C₂ k m := by
  have hi : (prodCKA C₁ C₂).init = SPComp.bind C₁.init fun i₁ => SPComp.bind C₂.init fun i₂ =>
      SPComp.pure ((i₁.1, i₂.1), (i₁.2.1, i₂.2.1), (i₁.2.2, i₂.2.2)) := rfl
  have hs : ∀ s, (prodCKA C₁ C₂).send s = SPComp.bind (C₁.send s.1) fun o₁ =>
      SPComp.bind (C₂.send s.2) fun o₂ =>
        SPComp.pure ((o₁.1, o₂.1), (o₁.2.1, o₂.2.1), (o₁.2.2, o₂.2.2)) := fun _ => rfl
  have hr : ∀ r T, (prodCKA C₁ C₂).recv r T =
      (((C₁.recv r.1 T.1).1, (C₂.recv r.2 T.2).1), ((C₁.recv r.1 T.1).2, (C₂.recv r.2 T.2).2)) :=
    fun _ _ => rfl
  have hrun : ∀ n s r, SPComp.IsPure (ckaRun C₁ n s r) := ckaRun_isPure C₁ h₁
  simp only [cka_mix, prodHyb, cka_ideal, cka_real, hi, hs, hr, ckaRun_prod C₁ C₂ h₁,
    SPComp.bind_assoc, SPComp.pure_bind, mixLeft]
  simp only [zipView]; symm; bind_swap_nf

/-- The product game with a uniform second component of the challenge key is the real game of
`C₁` next to the ideal game of `C₂`, when sending in `C₁` does not touch the heap. -/
theorem cka_mix_right_prod [Fintype K₂] [Nonempty K₂] (C₁ : CKADef S₁ M₁ K₁)
    (C₂ : CKADef S₂ M₂ K₂) (h₁ : ∀ s, SPComp.IsPure (C₁.send s)) (k m : ℕ) :
    cka_mix (prodCKA C₁ C₂) (mixRight (K₁ := K₁)) k m =
      SPComp.bind (cka_real C₁ k m) fun v₁ => SPComp.bind (cka_ideal C₂ k m) fun v₂ =>
        SPComp.pure (zipView v₁ v₂) := by
  have hi : (prodCKA C₁ C₂).init = SPComp.bind C₁.init fun i₁ => SPComp.bind C₂.init fun i₂ =>
      SPComp.pure ((i₁.1, i₂.1), (i₁.2.1, i₂.2.1), (i₁.2.2, i₂.2.2)) := rfl
  have hs : ∀ s, (prodCKA C₁ C₂).send s = SPComp.bind (C₁.send s.1) fun o₁ =>
      SPComp.bind (C₂.send s.2) fun o₂ =>
        SPComp.pure ((o₁.1, o₂.1), (o₁.2.1, o₂.2.1), (o₁.2.2, o₂.2.2)) := fun _ => rfl
  have hr : ∀ r T, (prodCKA C₁ C₂).recv r T =
      (((C₁.recv r.1 T.1).1, (C₂.recv r.2 T.2).1), ((C₁.recv r.1 T.1).2, (C₂.recv r.2 T.2).2)) :=
    fun _ _ => rfl
  have hrun : ∀ n s r, SPComp.IsPure (ckaRun C₁ n s r) := ckaRun_isPure C₁ h₁
  simp only [cka_mix, cka_ideal, cka_real, hi, hs, hr, ckaRun_prod C₁ C₂ h₁,
    SPComp.bind_assoc, SPComp.pure_bind, mixRight]
  simp only [zipView]; symm; bind_swap_nf

/-- **One-sided product hybrid, first component.** When sending in `C₁` does not touch the
heap, the distance between the real CKA game of `prodCKA C₁ C₂` and the game in which only the
first component of the challenge key is uniform, for the adversary `A`, is the CKA advantage
of `C₁` at `prodCKARed₁ C₂ k m A`. -/
theorem prodCKA_left_advantage_eq [Fintype K₁] [Nonempty K₁] (C₁ : CKADef S₁ M₁ K₁)
    (C₂ : CKADef S₂ M₂ K₂) (h₁ : ∀ s, SPComp.IsPure (C₁.send s)) (k m : ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPComp Bool) :
    AdvantageA (cka_real (prodCKA C₁ C₂) k m) (cka_mix (prodCKA C₁ C₂) (mixLeft (K₂ := K₂)) k m)
      A = CKA_Advantage C₁ k m (prodCKARed₁ C₂ k m A) := by
  have e₁ : (cka_real (prodCKA C₁ C₂) k m).bind A =
      (cka_real C₁ k m).bind (prodCKARed₁ C₂ k m A) := by
    rw [cka_real_prod C₁ C₂ h₁]
    unfold prodCKARed₁ ckaPubRedOf
    simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  have e₂ : (cka_mix (prodCKA C₁ C₂) (mixLeft (K₂ := K₂)) k m).bind A =
      (cka_ideal C₁ k m).bind (prodCKARed₁ C₂ k m A) := by
    rw [cka_mix_left_prod C₁ C₂ h₁]
    unfold prodHyb prodCKARed₁ ckaPubRedOf
    simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  unfold CKA_Advantage AdvantageA
  rw [e₁, e₂]

/-- **One-sided product hybrid, second component.** When the initialisation and sending of
`C₁` do not touch the heap, the distance between the real CKA game of `prodCKA C₁ C₂` and the
game in which only the second component of the challenge key is uniform, for the adversary
`A`, is the CKA advantage of `C₂` at `prodCKARedR C₁ k m A`. -/
theorem prodCKA_right_advantage_eq [Fintype K₂] [Nonempty K₂] (C₁ : CKADef S₁ M₁ K₁)
    (C₂ : CKADef S₂ M₂ K₂) (h₀ : SPComp.IsPure C₁.init) (h₁ : ∀ s, SPComp.IsPure (C₁.send s))
    (k m : ℕ) (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPComp Bool) :
    AdvantageA (cka_real (prodCKA C₁ C₂) k m)
      (cka_mix (prodCKA C₁ C₂) (mixRight (K₁ := K₁)) k m) A =
      CKA_Advantage C₂ k m (prodCKARedR C₁ k m A) := by
  have e₁ : (cka_real (prodCKA C₁ C₂) k m).bind A =
      (cka_real C₂ k m).bind (prodCKARedR C₁ k m A) := by
    rw [cka_real_prod C₁ C₂ h₁]
    unfold prodCKARedR ckaPubRedOf
    simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
    exact SPComp.isPure_bind_comm_left _ _ _ (cka_real_isPure C₁ h₀ h₁ k m)
  have e₂ : (cka_mix (prodCKA C₁ C₂) (mixRight (K₁ := K₁)) k m).bind A =
      (cka_ideal C₂ k m).bind (prodCKARedR C₁ k m A) := by
    rw [cka_mix_right_prod C₁ C₂ h₁]
    unfold prodCKARedR ckaPubRedOf
    simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
    exact SPComp.isPure_bind_comm_left _ _ _ (cka_real_isPure C₁ h₀ h₁ k m)
  unfold CKA_Advantage AdvantageA
  rw [e₁, e₂]

end OneSided

/-! ## The CKA phase with partial key replacement -/

section SM

variable {Sc Msg Key X RK Sa W Ct : Type} [Fintype X] [Nonempty X] [Fintype RK]
  [Nonempty RK] [Fintype Sa] [Nonempty Sa] [SampleableType W] [SampleableType Ct]

/-- CKA hybrid `t` with the replacement `mix`: the key `I` of each of the first `t` epochs is
replaced by `mix u I` for a uniform `u`. -/
noncomputable def trHybK (C : CKADef Sc Msg Key) (mix : X → Key → Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t : ℕ) : SPComp (SMView Msg Ct) :=
  SPComp.bind C.init fun i =>
    SPComp.bind (ckaRun C msgs.length i.2.1 i.2.2) fun p =>
      SPComp.bind (SPComp.sample (Fin t → X)) fun u =>
        SPComp.bind (SPComp.sample RK) fun rk =>
          SPComp.pure ((i.1, p.1.map Prod.fst),
            smCts G D (rootRun R rk (mixKeys mix (List.ofFn u) (p.1.map Prod.snd))) msgs)

/-- The view of the CKA reduction with the replacement `mix`, from the list `us` of the
uniform values of the epochs before the challenge epoch, the root key `rk` and the CKA view
`v`. Its arguments are first-order data, so that its cost `trCKAViewL.timedCost` is derived. -/
def trCKAViewL (mix : X → Key → Key) (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (us : List X) (rk : RK)
    (v : CKAView Msg Key) : SMView Msg Ct :=
  ((v.1, v.2.1.map Prod.fst ++ v.2.2.1.1 :: v.2.2.2.map Prod.fst),
    smCts G D (rootRun R rk (mixKeys mix us (v.2.1.map Prod.snd) ++
      v.2.2.1.2 :: v.2.2.2.map Prod.snd)) msgs)

/-- The view of the CKA reduction at epoch `t` with the replacement `mix`, from the uniform
values `x.1` of the epochs before `t`, the root key `x.2` and the CKA view `v`. -/
def trCKAView (mix : X → Key → Key) (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t : ℕ) (x : (Fin t → X) × RK)
    (v : CKAView Msg Key) : SMView Msg Ct :=
  trCKAViewL mix R G D msgs (List.ofFn x.1) x.2 v

/-- The CKA distinguisher of epoch `t` with the replacement `mix`: replaced keys for the epochs
before `t`, the challenge key for epoch `t`, the real keys after it. -/
noncomputable def trCKARed (mix : X → Key → Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) (t : ℕ)
    (A : SMView Msg Ct → SPComp Bool) : CKAView Msg Key → SPComp Bool :=
  smSampleRedOf (trCKAView mix R G D msgs t) A

omit [Fintype Sa] [Nonempty Sa] [SampleableType Ct] in
/-- CKA hybrid `0` is the real game. -/
theorem trHybK_zero (C : CKADef Sc Msg Key) (mix : X → Key → Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) :
    trHybK C mix R G D msgs 0 = sm_real C R G D msgs := by
  simp only [trHybK, sm_real, sample_bind_unique, List.ofFn_zero, mixKeys]

omit [Fintype Sa] [Nonempty Sa] [SampleableType Ct] in
/-- CKA hybrid `t` is the real CKA game at the challenge epoch `t` of `trCKARed`. -/
theorem trHybK_bind_eq_real (C : CKADef Sc Msg Key) (mix : X → Key → Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t m : ℕ) (hm : msgs.length = t + (m + 1))
    (A : SMView Msg Ct → SPComp Bool) :
    (trHybK C mix R G D msgs t).bind A =
      (cka_real C t m).bind (trCKARed mix R G D msgs t A) := by
  simp only [trHybK, cka_real, trCKARed, smSampleRedOf, trCKAView, trCKAViewL,
    SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext i
  rw [hm, ckaRun_add_bind]
  apply ckaRun_bind_congr; intro p hp
  simp only [ckaRun, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext o; congr 1; funext q
  have hmk : ∀ (u : Fin t → X) (l : List Key), mixKeys mix (List.ofFn u)
      (p.1.map Prod.snd ++ l) = mixKeys mix (List.ofFn u) (p.1.map Prod.snd) ++ l :=
    fun u l => mixKeys_append mix _ _ _ (by simp [hp])
  simp only [List.map_append, List.map_cons, hmk, SPComp.sample_prod_eq, SPComp.bind_assoc,
    SPComp.pure_bind]

omit [Fintype Sa] [Nonempty Sa] [SampleableType Ct] in
/-- CKA hybrid `t + 1` is the game `cka_mix` at the challenge epoch `t` of `trCKARed`. -/
theorem trHybK_succ_bind_eq_mix (C : CKADef Sc Msg Key) (mix : X → Key → Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t m : ℕ) (hm : msgs.length = t + (m + 1))
    (A : SMView Msg Ct → SPComp Bool) :
    (trHybK C mix R G D msgs (t + 1)).bind A =
      (cka_mix C mix t m).bind (trCKARed mix R G D msgs t A) := by
  simp only [trHybK, cka_mix, trCKARed, smSampleRedOf, trCKAView, trCKAViewL,
    SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext i
  rw [hm, ckaRun_add_bind]
  apply ckaRun_bind_congr; intro p hp
  simp only [ckaRun, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext o
  rw [SPComp.isPure_bind_comm_left (SPComp.sample X) _ _ (SPComp.sample_isPure _)]
  congr 1; funext q
  rw [← SPComp.sample_bind_equiv (Fin.snocEquiv fun _ => X)]
  have he : ∀ (a : X) (v : Fin t → X), (Fin.snocEquiv fun _ => X) (a, v) =
      Fin.snoc (α := fun _ => X) v a := fun _ _ => rfl
  have hmk : ∀ (u : Fin t → X) (a : X) (k : Key) (l : List Key),
      mixKeys mix (List.ofFn u ++ [a]) (p.1.map Prod.snd ++ k :: l) =
        mixKeys mix (List.ofFn u) (p.1.map Prod.snd) ++ mix a k :: l :=
    fun u a k l => mixKeys_snoc mix _ _ _ _ _ (by simp [hp])
  simp only [List.map_append, List.map_cons, SPComp.sample_prod_eq, SPComp.bind_assoc,
    SPComp.pure_bind, he, ofFn_snoc, hmk]

/-! ## The root phase with partial key replacement -/

/-- Root hybrid `(t, r)` with the replacement `mix`: the FS-AEAD states of the first `t`
epochs are uniform; the keys of the next `r` epochs are the real keys with `mix` applied to
uniform values, and the root chain runs on them from a uniform root key. -/
noncomputable def trHybP (C : CKADef Sc Msg Key) (mix : X → Key → Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t r : ℕ) : SPComp (SMView Msg Ct) :=
  SPComp.bind C.init fun i =>
    SPComp.bind (ckaRun C msgs.length i.2.1 i.2.2) fun p =>
      SPComp.bind (SPComp.sample (Fin t → Sa)) fun us =>
        SPComp.bind (SPComp.sample (Fin r → X)) fun ws =>
          SPComp.bind (SPComp.sample RK) fun rk =>
            SPComp.pure ((i.1, p.1.map Prod.fst),
              smCts G D (List.ofFn us ++
                rootRun R rk (mixKeys mix (List.ofFn ws) ((p.1.map Prod.snd).drop t))) msgs)

/-- The public part of the root hop at epoch `t` with `r` epochs after it: the public value
and the messages of a CKA run, the keys of the epochs after `t`, and the key of epoch `t`. -/
noncomputable def trRootPub (C : CKADef Sc Msg Key) (t r : ℕ) :
    SPComp ((Msg × List Msg) × List Key × Key) :=
  SPComp.bind C.init fun i =>
    SPComp.bind (ckaRun C t i.2.1 i.2.2) fun p =>
      SPComp.bind (C.send p.2.1) fun o =>
        SPComp.bind (ckaRun C r (C.recv p.2.2 o.2.1).1 o.1) fun q =>
          SPComp.pure ((i.1, p.1.map Prod.fst ++ o.2.1 :: q.1.map Prod.fst),
            q.1.map Prod.snd, o.2.2)

/-- The view of the root hop, from the list `x.1` of the FS-AEAD states of the epochs before
the hop, the list `x.2` of the values of the replacement after it, the public part `c` and the
next root key and FS-AEAD state `y` of the epoch of the hop. Its arguments are first-order
data, so that its cost `trRootViewL.timedCost` is derived. -/
def trRootViewL (mix : X → Key → Key) (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (x : List Sa × List X)
    (c : (Msg × List Msg) × List Key × Key) (y : RK × Sa) : SMView Msg Ct :=
  (c.1, smCts G D (x.1 ++ y.2 :: rootRun R y.1 (mixKeys mix x.2 c.2.1)) msgs)

/-- The view of the root hop at epoch `t` with `r` epochs after it, from the uniform FS-AEAD
states `x.1` of the epochs before `t`, the uniform values `x.2` of the replacement after it,
the public part `c` and the next root key and FS-AEAD state `y` of epoch `t`. -/
def trRootView (mix : X → Key → Key) (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (x : (Fin t → Sa) × (Fin r → X)) (c : (Msg × List Msg) × List Key × Key) (y : RK × Sa) :
    SMView Msg Ct :=
  trRootViewL mix R G D msgs (List.ofFn x.1, List.ofFn x.2) c y

/-- The root hop at epoch `t`, real side: the root step on a uniform root key and the key of
epoch `t` with `mix` applied to a uniform value. -/
noncomputable def trRoot_real (C : CKADef Sc Msg Key) (mix : X → Key → Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t r : ℕ) : SPComp (SMView Msg Ct) :=
  SPComp.bind (trRootPub C t r) fun c =>
    SPComp.bind (SPComp.sample ((Fin t → Sa) × (Fin r → X))) fun x =>
      SPComp.bind (SPComp.sample (RK × X)) fun s =>
        SPComp.pure (trRootView mix R G D msgs t r x c (R.stretch (s.1, mix s.2 c.2.2)))

/-- The root hop at epoch `t`, ideal side: a uniform next root key and FS-AEAD state. -/
noncomputable def trRoot_ideal (C : CKADef Sc Msg Key) (mix : X → Key → Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t r : ℕ) : SPComp (SMView Msg Ct) :=
  SPComp.bind (trRootPub C t r) fun c =>
    SPComp.bind (SPComp.sample ((Fin t → Sa) × (Fin r → X))) fun x =>
      SPComp.bind (SPComp.sample (RK × Sa)) fun y =>
        SPComp.pure (trRootView mix R G D msgs t r x c y)

omit [SampleableType Ct] in
/-- CKA hybrid `n` is root hybrid `(0, n)`. -/
theorem trHybK_self (C : CKADef Sc Msg Key) (mix : X → Key → Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) :
    trHybK C mix R G D msgs msgs.length = trHybP C mix R G D msgs 0 msgs.length := by
  simp only [trHybK, trHybP, sample_bind_unique, List.ofFn_zero, List.nil_append,
    List.drop_zero]

omit [SampleableType Ct] in
/-- Root hybrid `(t, r + 1)` is the real side of the root hop at epoch `t`. -/
theorem trHybP_bind_eq_real (C : CKADef Sc Msg Key) (mix : X → Key → Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t r : ℕ) (hm : msgs.length = t + (r + 1))
    (A : SMView Msg Ct → SPComp Bool) :
    (trHybP C mix R G D msgs t (r + 1)).bind A = (trRoot_real C mix R G D msgs t r).bind A := by
  simp only [trHybP, trRoot_real, trRootPub, trRootView, trRootViewL, SPComp.bind_assoc,
    SPComp.pure_bind]
  congr 1; funext i
  rw [hm, ckaRun_add_bind]
  apply ckaRun_bind_congr; intro p hp
  simp only [ckaRun, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext o
  have hd : ∀ l : List (Msg × Key), List.drop t (List.map Prod.snd p.1 ++ o.2.2 ::
      List.map Prod.snd l) = o.2.2 :: List.map Prod.snd l := fun l =>
    List.drop_left' (by simp [hp])
  simp only [List.map_append, List.map_cons]
  simp only [hd]
  simp only [← SPComp.sample_bind_equiv (Fin.consEquiv fun _ => X)]
  have he : ∀ (a : X) (v : Fin r → X), (Fin.consEquiv fun _ => X) (a, v) =
      Fin.cons (α := fun _ => X) a v := fun _ _ => rfl
  simp only [SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind, he, ofFn_cons,
    mixKeys, rootRun]
  symm; bind_swap_nf

omit [SampleableType Ct] in
/-- Root hybrid `(t + 1, r)` is the ideal side of the root hop at epoch `t`. -/
theorem trHybP_succ_bind_eq_ideal (C : CKADef Sc Msg Key) (mix : X → Key → Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t r : ℕ) (hm : msgs.length = t + (r + 1))
    (A : SMView Msg Ct → SPComp Bool) :
    (trHybP C mix R G D msgs (t + 1) r).bind A =
      (trRoot_ideal C mix R G D msgs t r).bind A := by
  simp only [trHybP, trRoot_ideal, trRootPub, trRootView, trRootViewL, SPComp.bind_assoc,
    SPComp.pure_bind]
  congr 1; funext i
  rw [hm, ckaRun_add_bind]
  apply ckaRun_bind_congr; intro p hp
  simp only [ckaRun, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext o
  have hd : ∀ l : List (Msg × Key),
      List.drop (t + 1) (List.map Prod.snd p.1 ++ o.2.2 :: List.map Prod.snd l) =
        List.map Prod.snd l := fun l => by
    have hl : (List.map Prod.snd p.1).length = t := by simp [hp]
    rw [← hl, List.drop_append]; simp
  simp only [List.map_append, List.map_cons]
  simp only [hd]
  simp only [← SPComp.sample_bind_equiv (Fin.snocEquiv fun _ => Sa)]
  have he : ∀ (a : Sa) (v : Fin t → Sa), (Fin.snocEquiv fun _ => Sa) (a, v) =
      Fin.snoc (α := fun _ => Sa) v a := fun _ _ => rfl
  simp only [SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind, he, ofFn_snoc,
    List.append_assoc, List.singleton_append]
  symm; bind_swap_nf

/-- Root hybrid `(n, 0)` is FS-AEAD hybrid `(0, n)`. -/
theorem trHybP_self_bind (C : CKADef Sc Msg Key) (mix : X → Key → Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (A : SMView Msg Ct → SPComp Bool) :
    (trHybP C mix R G D msgs msgs.length 0).bind A =
      (smHybF C G D msgs 0 msgs.length).bind A := by
  have h : (trHybP C mix R G D msgs msgs.length 0).bind A =
      SPComp.bind C.init fun i =>
        SPComp.bind (ckaRun C msgs.length i.2.1 i.2.2) fun p =>
          SPComp.bind (SPComp.sample (Fin msgs.length → Sa)) fun us =>
            SPComp.bind (SPComp.sample RK) fun _ =>
              A ((i.1, p.1.map Prod.fst), smCts G D (List.ofFn us) msgs) := by
    simp only [trHybP, SPComp.bind_assoc, SPComp.pure_bind, sample_bind_unique,
      List.ofFn_zero]
    congr 1; funext i
    apply ckaRun_bind_congr; intro p hp
    rw [List.drop_eq_nil_of_le (by simp [hp])]
    simp only [mixKeys, rootRun, List.append_nil]
  rw [h]
  simp only [smHybF, ckaPub, SPComp.bind_assoc, SPComp.pure_bind, sample_bind_unique,
    List.ofFn_zero, ctsOf, List.nil_append, List.drop_zero]
  symm; bind_swap_nf

omit [Fintype Sa] [Nonempty Sa] [SampleableType Ct] in
/-- With the replacement `mix u _ = u` of whole keys, CKA hybrid `t ≤ n` is CKA hybrid `t` of
the double ratchet. -/
theorem trHybK_eq_smHybK [Fintype Key] [Nonempty Key] (C : CKADef Sc Msg Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t : ℕ) (ht : t ≤ msgs.length) :
    trHybK C (fun u _ => u) R G D msgs t = smHybK C R G D msgs t := by
  have hm : ∀ (us ks : List Key), us.length ≤ ks.length →
      mixKeys (fun u _ => u) us ks = us ++ ks.drop us.length := by
    intro us
    induction us with
    | nil => intro ks _; rfl
    | cons u us ih =>
      intro ks h
      cases ks with
      | nil => simp at h
      | cons k ks =>
        simp only [mixKeys, ih ks (by simpa using h), List.length_cons, List.drop_succ_cons,
          List.cons_append]
  simp only [trHybK, smHybK]
  congr 1; funext i
  apply ckaRun_bind_congr; intro p hp
  congr 1; funext u
  rw [hm _ _ (by simp [hp, ht]), List.length_ofFn]

end SM

/-! ## One-query oracle adversaries from distinguishers -/

section Bridge

/-- The output bit of a run of a Boolean computation: `b` for `some (b, h)`, and `false` for a
failed run. -/
def runBit : Option (Bool × Heap) → Bool
  | some (b, _) => b
  | none => false

/-- The oracle adversary that runs the computation `pre` from the empty heap, queries `q x` on
its result `x`, and runs the distinguisher `B x` on the answer from the heap left by `pre`. -/
noncomputable def oneQueryAdv {P Q R : Type} (pre : SPComp P) (q : P → Q)
    (B : P → R → SPComp Bool) : OracleAdv Q R Bool :=
  OracleAdv.rand (β := Option (P × Heap)) (pre Heap.empty) fun o => match o with
    | none => OracleAdv.ret false
    | some (x, h) => OracleAdv.query (q x) fun y =>
        OracleAdv.rand (β := Option (Bool × Heap)) (B x y h) fun o' => OracleAdv.ret (runBit o')

/-- The probability of `true` is the probability that `runBit` of a run is `true`. -/
theorem prTrue_eq_map_runBit (G : SPComp Bool) (h₀ : Heap) :
    prTrue G h₀ = PMF.map runBit (G h₀) true := by
  rw [PMF.map_apply, SDistr.tsum_option_eq_add, ENNReal.tsum_prod', tsum_fintype,
    Fintype.sum_bool]
  simp [runBit, prTrue]

/-- A run of `oneQueryAdv pre q B` against the oracle `O` from the state `s`, projected to its
output. -/
theorem run_oneQueryAdv {P Q R S : Type} (pre : SPComp P) (q : P → Q)
    (B : P → R → SPComp Bool) (O : S → Q → PMF (R × S)) (s : S) :
    (OracleAdv.run O (oneQueryAdv pre q B) s).map Prod.fst =
      PMF.bind (pre Heap.empty) fun o => match o with
        | none => PMF.pure false
        | some (x, h) => (O s (q x)).bind fun r => PMF.map runBit (B x r.1 h) := by
  simp only [oneQueryAdv, OracleAdv.run_rand, PMF.map_bind]
  congr 1; funext o
  rcases o with _ | ⟨x, h⟩
  · simp only [OracleAdv.run_ret, PMF.pure_map]
  · simp only [OracleAdv.run_query, OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind,
      PMF.pure_map]
    congr 1

/-- A computation followed by a lifted distribution and a distinguisher, from the empty heap,
with the output bit. -/
theorem map_runBit_bind_liftPMF {P K : Type} (pre : SPComp P) (Dx : P → PMF K)
    (B : P → K → SPComp Bool) :
    PMF.map runBit ((SPComp.bind pre fun x => SPComp.bind (liftPMF (Dx x)) (B x)) Heap.empty) =
      PMF.bind (pre Heap.empty) fun o => match o with
        | none => PMF.pure false
        | some (x, h) => (Dx x).bind fun k => PMF.map runBit (B x k h) := by
  rw [SPComp.bind_def]
  unfold SDistr.bind
  rw [PMF.map_bind]
  congr 1; funext o
  rcases o with _ | ⟨x, h⟩
  · simp [SDistr.fail, PMF.pure_map, runBit]
  · simp only [liftPMF_bind_apply, PMF.map_bind]

/-- The real adaptive PRF game against `oneQueryAdv pre q B` accepts with the probability of
the computation that runs `pre`, samples a key `k` and calls `B x` on `F k (q x)`. -/
theorem prTrue_realGame_oneQueryAdv {P Q R K : Type} [Fintype K] [Nonempty K]
    (F : K → Q → R) (pre : SPComp P) (q : P → Q) (B : P → R → SPComp Bool) :
    prTrue (realGame F (oneQueryAdv pre q B)) Heap.empty =
      prTrue (SPComp.bind pre fun x => SPComp.bind (SPComp.sample K) fun k => B x (F k (q x)))
        Heap.empty := by
  rw [realGame, prTrue_liftPMF, prTrue_eq_map_runBit, sample_eq_liftPMF,
    map_runBit_bind_liftPMF pre (fun _ => PMF.uniformFintype K) (fun x k => B x (F k (q x)))]
  simp only [run_oneQueryAdv, keyedOracle, PMF.pure_bind]
  rw [PMF.bind_comm]
  congr 2; funext o
  rcases o with _ | ⟨x, h⟩
  · simp only [PMF.bind_const]
  · rfl

/-- The random-function adaptive PRF game against `oneQueryAdv pre q B` accepts with the
probability of the computation that runs `pre`, samples a uniform answer `y` and calls
`B x y`. -/
theorem prTrue_rfGame_oneQueryAdv {P Q R : Type} [DecidableEq Q] [Fintype R] [Nonempty R]
    (pre : SPComp P) (q : P → Q) (B : P → R → SPComp Bool) :
    prTrue (rfGame (oneQueryAdv pre q B)) Heap.empty =
      prTrue (SPComp.bind pre fun x => SPComp.bind (SPComp.sample R) (B x)) Heap.empty := by
  rw [rfGame, prTrue_liftPMF, prTrue_eq_map_runBit, sample_eq_liftPMF,
    map_runBit_bind_liftPMF pre (fun _ => PMF.uniformFintype R) B]
  simp only [run_oneQueryAdv, rfOracle, List.lookup, PMF.bind_map]
  rfl

/-- **One-query PRF hop.** The distance between running `pre`, sampling a key `k` and calling
`B x` on `F k (q x)`, and running `pre`, sampling a uniform answer and calling `B x` on it, is
the adaptive PRF advantage of `F` at `oneQueryAdv pre q B`. -/
theorem advantage_oneQuery_eq {P Q R K : Type} [Fintype K] [Nonempty K] [DecidableEq Q]
    [Fintype R] [Nonempty R] (F : K → Q → R) (pre : SPComp P) (q : P → Q)
    (B : P → R → SPComp Bool) :
    Advantage (SPComp.bind pre fun x => SPComp.bind (SPComp.sample K) fun k => B x (F k (q x)))
        (SPComp.bind pre fun x => SPComp.bind (SPComp.sample R) (B x)) =
      PRF_q_Advantage F (oneQueryAdv pre q B) := by
  unfold PRF_q_Advantage Advantage
  rw [prTrue_realGame_oneQueryAdv, prTrue_rfGame_oneQueryAdv]

/-- A uniform sample whose value is not used can be removed. -/
theorem sample_bind_const {α β : Type} [Fintype α] [Nonempty α] (c : SPComp β) :
    SPComp.bind (SPComp.sample α) (fun _ => c) = c := by
  funext h
  simp only [SPComp.bind_def, SPComp.sample, SDistr.bind_assoc, SDistr.pure_bind,
    SDistr.uniform_bind_const]

end Bridge

/-! ## The root step from a dual PRF -/

section Root

variable {S₁ M₁ K₁ S₂ M₂ K₂ RK Sa W Ct : Type} [Fintype K₁] [Nonempty K₁] [Fintype K₂]
  [Nonempty K₂] [Fintype RK] [Nonempty RK] [Fintype Sa] [Nonempty Sa] [SampleableType W]
  [SampleableType Ct]

/-- The root step of the triple ratchet: from the root key `rk` and the epoch key `(k₁, k₂)`
of the Diffie–Hellman and the KEM components, the next root key and the FS-AEAD state of the
epoch are `F (rk, k₁) k₂`. -/
def trRoot (F : RK × K₁ → K₂ → RK × Sa) : PRGDef (RK × (K₁ × K₂)) (RK × Sa) where
  stretch x := F (x.1, x.2.1) x.2.2

/-- The computation of the left root reduction before its query: the public part of the root
hop and the lists of the uniform values of the epochs before and after `t`. -/
noncomputable def trRootPreL (C : CKADef (S₁ × S₂) (M₁ × M₂) (K₁ × K₂)) (t r : ℕ) :
    SPComp ((((M₁ × M₂) × List (M₁ × M₂)) × List (K₁ × K₂) × (K₁ × K₂)) ×
      (List Sa × List K₁)) :=
  SPComp.bind (trRootPub C t r) fun c =>
    SPComp.bind (SPComp.sample ((Fin t → Sa) × (Fin r → K₁))) fun x =>
      SPComp.pure (c, (List.ofFn x.1, List.ofFn x.2))

/-- **The dual-PRF reduction of the root hop, Diffie–Hellman side.** The left key of `F` is the
root key and the Diffie–Hellman key of epoch `t`; the reduction queries the KEM key of epoch
`t` and runs the secure-messaging adversary on the view built from the answer. The view reads
the first `t` FS-AEAD states and the first `r` keys of its input, all of them on the support
of `trRootPreL`, so that its cost is bounded on every input. -/
noncomputable def trRootRedL (C : CKADef (S₁ × S₂) (M₁ × M₂) (K₁ × K₂))
    (F : RK × K₁ → K₂ → RK × Sa) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t r : ℕ) (A : SMView (M₁ × M₂) Ct → SPComp Bool) :
    OracleAdv K₂ (RK × Sa) Bool :=
  oneQueryAdv (trRootPreL C t r) (fun z => z.1.2.2.2)
    (fun z y => A (trRootViewL mixLeft (trRoot F) G D msgs (z.2.1.take t, z.2.2)
      (z.1.1, z.1.2.1.take r, z.1.2.2) y))

/-- The computation of the right root reduction before its query: the public part of the root
hop, the lists of the uniform values of the epochs before and after `t`, and a uniform root
key. -/
noncomputable def trRootPreR (C : CKADef (S₁ × S₂) (M₁ × M₂) (K₁ × K₂)) (t r : ℕ) :
    SPComp ((((M₁ × M₂) × List (M₁ × M₂)) × List (K₁ × K₂) × (K₁ × K₂)) ×
      (List Sa × List K₂) × RK) :=
  SPComp.bind (trRootPub C t r) fun c =>
    SPComp.bind (SPComp.sample ((Fin t → Sa) × (Fin r → K₂))) fun x =>
      SPComp.bind (SPComp.sample RK) fun rk => SPComp.pure (c, (List.ofFn x.1, List.ofFn x.2), rk)

/-- **The dual-PRF reduction of the root hop, KEM side.** The right key of `F` is the KEM key
of epoch `t`; the reduction samples the root key, queries it with the Diffie–Hellman key of
epoch `t`, and runs the secure-messaging adversary on the view built from the answer. As in
`trRootRedL`, the view reads the first `t` FS-AEAD states and the first `r` keys. -/
noncomputable def trRootRedR (C : CKADef (S₁ × S₂) (M₁ × M₂) (K₁ × K₂))
    (F : RK × K₁ → K₂ → RK × Sa) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t r : ℕ) (A : SMView (M₁ × M₂) Ct → SPComp Bool) :
    OracleAdv (RK × K₁) (RK × Sa) Bool :=
  oneQueryAdv (trRootPreR C t r) (fun z => (z.2.2, z.1.2.2.1))
    (fun z y => A (trRootViewL mixRight (trRoot F) G D msgs (z.2.1.1.take t, z.2.1.2)
      (z.1.1, z.1.2.1.take r, z.1.2.2) y))

omit [Fintype K₁] [Nonempty K₁] [Fintype K₂] [Nonempty K₂] [Fintype RK] [Nonempty RK]
  [Fintype Sa] [Nonempty Sa] [SampleableType W] [SampleableType Ct] in
/-- The keys of the epochs after `t` in the public part of the root hop are `r` keys: two
continuations that agree on such public parts agree after `trRootPub`. -/
theorem trRootPub_bind_congr {β : Type} (C : CKADef (S₁ × S₂) (M₁ × M₂) (K₁ × K₂)) (t r : ℕ)
    (K K' : ((M₁ × M₂) × List (M₁ × M₂)) × List (K₁ × K₂) × (K₁ × K₂) → SPComp β)
    (h : ∀ c, c.2.1.length = r → K c = K' c) :
    SPComp.bind (trRootPub C t r) K = SPComp.bind (trRootPub C t r) K' := by
  simp only [trRootPub, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext i; congr 1; funext p; congr 1; funext o
  exact ckaRun_bind_congr C r _ _ _ _ fun q hq => h _ (by simp [hq])

omit [Fintype K₂] [Nonempty K₂] [SampleableType Ct] in
/-- The root hop of the Diffie–Hellman side is the dual-PRF game of `F` keyed by its left
argument, at `trRootRedL`. -/
theorem trRoot_left_advantage_eq [DecidableEq RK] [DecidableEq K₁] [DecidableEq K₂]
    [DecidableEq Sa] (C : CKADef (S₁ × S₂) (M₁ × M₂) (K₁ × K₂))
    (F : RK × K₁ → K₂ → RK × Sa) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t r : ℕ) (A : SMView (M₁ × M₂) Ct → SPComp Bool) :
    AdvantageA (trRoot_real C mixLeft (trRoot F) G D msgs t r)
        (trRoot_ideal C mixLeft (trRoot F) G D msgs t r) A =
      DualPRF_Left_Advantage F (trRootRedL C F G D msgs t r A) := by
  unfold DualPRF_Left_Advantage trRootRedL AdvantageA
  rw [← advantage_oneQuery_eq]
  simp only [trRoot_real, trRoot_ideal, trRootPreL, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1 <;> apply trRootPub_bind_congr <;> intro c hc <;>
    simp only [trRootView, List.length_ofFn, List.take_of_length_le, le_refl, hc]
  rfl

omit [Fintype K₁] [Nonempty K₁] [SampleableType Ct] in
/-- The root hop of the KEM side is the dual-PRF game of `F` keyed by its right argument, at
`trRootRedR`. -/
theorem trRoot_right_advantage_eq [DecidableEq RK] [DecidableEq K₁] [DecidableEq K₂]
    [DecidableEq Sa] (C : CKADef (S₁ × S₂) (M₁ × M₂) (K₁ × K₂))
    (F : RK × K₁ → K₂ → RK × Sa) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t r : ℕ) (A : SMView (M₁ × M₂) Ct → SPComp Bool) :
    AdvantageA (trRoot_real C mixRight (trRoot F) G D msgs t r)
        (trRoot_ideal C mixRight (trRoot F) G D msgs t r) A =
      DualPRF_Right_Advantage F (trRootRedR C F G D msgs t r A) := by
  unfold DualPRF_Right_Advantage trRootRedR AdvantageA
  rw [← advantage_oneQuery_eq]
  simp only [trRoot_real, trRoot_ideal, trRootPreR, SPComp.bind_assoc, SPComp.pure_bind,
    SPComp.sample_prod_eq (RK) (K₂), sample_bind_const]
  congr 1 <;> apply trRootPub_bind_congr <;> intro c hc <;>
    simp only [trRootView, List.length_ofFn, List.take_of_length_le, le_refl, hc]
  rfl

end Root

/-! ## The composition theorems -/

section Compose

variable {Sc Msg Key X RK Sa W Ct : Type} [Fintype Key] [Nonempty Key] [Fintype X] [Nonempty X]
  [Fintype RK] [Nonempty RK] [Fintype Sa] [Nonempty Sa] [SampleableType W] [SampleableType Ct]

omit [Fintype Key] [Nonempty Key] in
/-- **Confidentiality with partial key replacement.** For every CKA `C`, replacement `mix` and
adversary `A`, the secure-messaging advantage is at most the sum over the epochs `t` of the
distance between the real CKA game and the game `cka_mix` at `trCKARed`, of the root hop at
epoch `t`, and of the FS-AEAD advantage of epoch `t` at `smAEADRed`. With `mix` replacing one
component of a product key, the CKA terms are one-sided product hybrids, and the root hops
need only the uniformity of that component. -/
theorem sm_mix_advantage_le (C : CKADef Sc Msg Key) (mix : X → Key → Key)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (A : SMView Msg Ct → SPComp Bool) :
    SM_Advantage C R G D msgs A ≤
      ∑ t ∈ Finset.range msgs.length,
          AdvantageA (cka_real C t (msgs.length - (t + 1)))
            (cka_mix C mix t (msgs.length - (t + 1))) (trCKARed mix R G D msgs t A) +
        ∑ t ∈ Finset.range msgs.length,
          AdvantageA (trRoot_real C mix R G D msgs t (msgs.length - (t + 1)))
            (trRoot_ideal C mix R G D msgs t (msgs.length - (t + 1))) A +
        ∑ t ∈ Finset.range msgs.length,
          FSAEAD_Advantage G D (msgs.getD t [])
            (smAEADRed C G D msgs t (msgs.length - (t + 1)) A) := by
  have hK : AdvantageA (trHybK C mix R G D msgs 0) (trHybK C mix R G D msgs msgs.length) A ≤
      ∑ t ∈ Finset.range msgs.length,
        AdvantageA (cka_real C t (msgs.length - (t + 1)))
          (cka_mix C mix t (msgs.length - (t + 1))) (trCKARed mix R G D msgs t A) := by
    refine (HybridArgument.advantage_hybrid_dep (trHybK C mix R G D msgs) A msgs.length).trans
      (Finset.sum_le_sum fun t ht => le_of_eq ?_)
    have ht' := Finset.mem_range.mp ht
    unfold AdvantageA
    rw [trHybK_bind_eq_real C mix R G D msgs t (msgs.length - (t + 1)) (by omega),
      trHybK_succ_bind_eq_mix C mix R G D msgs t (msgs.length - (t + 1)) (by omega)]
  have hP : AdvantageA (trHybP C mix R G D msgs 0 msgs.length)
      (trHybP C mix R G D msgs msgs.length (msgs.length - msgs.length)) A ≤
      ∑ t ∈ Finset.range msgs.length,
        AdvantageA (trRoot_real C mix R G D msgs t (msgs.length - (t + 1)))
          (trRoot_ideal C mix R G D msgs t (msgs.length - (t + 1))) A := by
    refine (HybridArgument.advantage_hybrid_dep
      (fun i => trHybP C mix R G D msgs i (msgs.length - i)) A msgs.length).trans
      (Finset.sum_le_sum fun t ht => le_of_eq ?_)
    have ht' := Finset.mem_range.mp ht
    have hr : msgs.length - t = msgs.length - (t + 1) + 1 := by omega
    unfold AdvantageA
    rw [hr, trHybP_bind_eq_real C mix R G D msgs t _ (by omega),
      trHybP_succ_bind_eq_ideal C mix R G D msgs t _ (by omega)]
  have hF : AdvantageA (smHybF C G D msgs 0 msgs.length)
      (smHybF C G D msgs msgs.length (msgs.length - msgs.length)) A ≤
      ∑ t ∈ Finset.range msgs.length,
        FSAEAD_Advantage G D (msgs.getD t [])
          (smAEADRed C G D msgs t (msgs.length - (t + 1)) A) := by
    refine (HybridArgument.advantage_hybrid_dep
      (fun i => smHybF C G D msgs i (msgs.length - i)) A msgs.length).trans
      (Finset.sum_le_sum fun t ht => le_of_eq ?_)
    have ht' := Finset.mem_range.mp ht
    have hr : msgs.length - t = msgs.length - (t + 1) + 1 := by omega
    unfold FSAEAD_Advantage AdvantageA
    rw [hr, smHybF_bind_eq_real C G D msgs ht', smHybF_succ_bind_eq_ideal]
  have e2 : (trHybP C mix R G D msgs msgs.length (msgs.length - msgs.length)).bind A =
      (smHybF C G D msgs 0 msgs.length).bind A := by
    rw [Nat.sub_self]; exact trHybP_self_bind C mix R G D msgs A
  have e3 : smHybF C G D msgs msgs.length (msgs.length - msgs.length) = sm_ideal C msgs := by
    rw [Nat.sub_self]; exact smHybF_self C G D msgs
  unfold AdvantageA at hK hP hF
  rw [e3] at hF
  unfold SM_Advantage AdvantageA
  rw [← trHybK_zero C mix]
  refine (advantage_triangle _ ((trHybK C mix R G D msgs msgs.length).bind A) _).trans ?_
  rw [add_assoc]
  refine add_le_add hK ?_
  rw [trHybK_self]
  exact (advantage_triangle _ _ _).trans (add_le_add hP (e2 ▸ hF))

end Compose

/-! ## The triple ratchet -/

section Triple

variable (G : Type) [CG : CyclicGroup G] [DecidableEq G] {PK SK K E RK Sa W Ct : Type}
  [Fintype K] [Nonempty K] [Fintype E] [Nonempty E] [Inhabited K] [DecidableEq K]
  [Fintype RK] [Nonempty RK] [DecidableEq RK] [Fintype Sa] [Nonempty Sa] [DecidableEq Sa]
  [SampleableType W] [SampleableType Ct]

omit [Fintype K] [Nonempty K] [Fintype E] [Nonempty E] in
/-- **Confidentiality of the triple ratchet from DDH.** For every adversary `A`, the
secure-messaging advantage of the triple ratchet with the root step `trRoot F` is at most the
sum over the epochs of the DDH advantages of `ckaDDHRed` at the one-sided product reductions,
the dual-PRF advantages of `F` keyed by its left argument (the root key and the
Diffie–Hellman key) at `trRootRedL`, and the FS-AEAD advantages at `smAEADRed`. The KEM may
be insecure. -/
theorem tr_advantage_le_ddh (KEM : KEMScheme PK SK K E) (F : RK × G → K → RK × Sa)
    (G' : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W)))
    (A : SMView (G × (Option E × PK)) Ct → SPComp Bool) :
    SM_Advantage (prodCKA (dhCKA G) (kemCKA KEM)) (trRoot F) G' D msgs A ≤
      ∑ t ∈ Finset.range msgs.length,
          DDH_Advantage G (ckaDDHRed t (msgs.length - (t + 1))
            (prodCKARed₁ (kemCKA KEM) t (msgs.length - (t + 1))
              (trCKARed mixLeft (trRoot F) G' D msgs t A))) +
        ∑ t ∈ Finset.range msgs.length,
          DualPRF_Left_Advantage F
            (trRootRedL (prodCKA (dhCKA G) (kemCKA KEM)) F G' D msgs t (msgs.length - (t + 1)) A) +
        ∑ t ∈ Finset.range msgs.length,
          FSAEAD_Advantage G' D (msgs.getD t [])
            (smAEADRed (prodCKA (dhCKA G) (kemCKA KEM)) G' D msgs t (msgs.length - (t + 1)) A) := by
  have h := sm_mix_advantage_le (prodCKA (dhCKA G) (kemCKA KEM)) (mixLeft (K₂ := K)) (trRoot F)
    G' D msgs A
  simp only [prodCKA_left_advantage_eq _ _ (dhCKA_send_isPure G), cka_advantage_eq_ddh,
    trRoot_left_advantage_eq] at h
  exact h

/-- **Confidentiality of the triple ratchet from the KEM.** For a KEM whose key generation and
encapsulation do not touch the heap and every adversary `A`, the secure-messaging advantage of
the triple ratchet with the root step `trRoot F` is at most the sum over the epochs of the
KEM-CPA advantages of `kemCKARed` at the one-sided product reductions, the dual-PRF
advantages of `F` keyed by its right argument (the KEM key) at `trRootRedR`, and the FS-AEAD
advantages at `smAEADRed`. The Diffie–Hellman component may be insecure. -/
theorem tr_advantage_le_kem (KEM : KEMScheme PK SK K E) (hkgen : SPComp.IsPure KEM.kgen)
    (hencap : ∀ pk, SPComp.IsPure (KEM.encap pk)) (F : RK × G → K → RK × Sa)
    (G' : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W)))
    (A : SMView (G × (Option E × PK)) Ct → SPComp Bool) :
    SM_Advantage (prodCKA (dhCKA G) (kemCKA KEM)) (trRoot F) G' D msgs A ≤
      ∑ t ∈ Finset.range msgs.length,
          KEM_CPA_Advantage KEM (kemCKARed KEM t (msgs.length - (t + 1))
            (prodCKARedR (dhCKA G) t (msgs.length - (t + 1))
              (trCKARed mixRight (trRoot F) G' D msgs t A))) +
        ∑ t ∈ Finset.range msgs.length,
          DualPRF_Right_Advantage F
            (trRootRedR (prodCKA (dhCKA G) (kemCKA KEM)) F G' D msgs t (msgs.length - (t + 1)) A) +
        ∑ t ∈ Finset.range msgs.length,
          FSAEAD_Advantage G' D (msgs.getD t [])
            (smAEADRed (prodCKA (dhCKA G) (kemCKA KEM)) G' D msgs t (msgs.length - (t + 1)) A) := by
  have h := sm_mix_advantage_le (prodCKA (dhCKA G) (kemCKA KEM)) (mixRight (K₁ := G)) (trRoot F)
    G' D msgs A
  simp only [prodCKA_right_advantage_eq _ _ (dhCKA_init_isPure G) (dhCKA_send_isPure G),
    kemCKA_advantage_eq KEM hkgen hencap, trRoot_right_advantage_eq] at h
  exact h

/-- **Hybrid confidentiality of the triple ratchet.** For a KEM whose key generation and
encapsulation do not touch the heap and every adversary `A`, the secure-messaging advantage of
the triple ratchet is at most the minimum of the DDH chain of `tr_advantage_le_ddh` and the
KEM chain of `tr_advantage_le_kem`: the protocol is confidential if DDH holds in `G` or the
KEM is IND-CPA secure, given the dual-PRF security of the root step in the corresponding
argument and the FS-AEAD security of the symmetric ratchet. -/
theorem tr_advantage_le_min (KEM : KEMScheme PK SK K E) (hkgen : SPComp.IsPure KEM.kgen)
    (hencap : ∀ pk, SPComp.IsPure (KEM.encap pk)) (F : RK × G → K → RK × Sa)
    (G' : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W)))
    (A : SMView (G × (Option E × PK)) Ct → SPComp Bool) :
    SM_Advantage (prodCKA (dhCKA G) (kemCKA KEM)) (trRoot F) G' D msgs A ≤
      min
        (∑ t ∈ Finset.range msgs.length,
            DDH_Advantage G (ckaDDHRed t (msgs.length - (t + 1))
              (prodCKARed₁ (kemCKA KEM) t (msgs.length - (t + 1))
                (trCKARed mixLeft (trRoot F) G' D msgs t A))) +
          ∑ t ∈ Finset.range msgs.length,
            DualPRF_Left_Advantage F
              (trRootRedL (prodCKA (dhCKA G) (kemCKA KEM)) F G' D msgs t
                (msgs.length - (t + 1)) A) +
          ∑ t ∈ Finset.range msgs.length,
            FSAEAD_Advantage G' D (msgs.getD t [])
              (smAEADRed (prodCKA (dhCKA G) (kemCKA KEM)) G' D msgs t (msgs.length - (t + 1)) A))
        (∑ t ∈ Finset.range msgs.length,
            KEM_CPA_Advantage KEM (kemCKARed KEM t (msgs.length - (t + 1))
              (prodCKARedR (dhCKA G) t (msgs.length - (t + 1))
                (trCKARed mixRight (trRoot F) G' D msgs t A))) +
          ∑ t ∈ Finset.range msgs.length,
            DualPRF_Right_Advantage F
              (trRootRedR (prodCKA (dhCKA G) (kemCKA KEM)) F G' D msgs t
                (msgs.length - (t + 1)) A) +
          ∑ t ∈ Finset.range msgs.length,
            FSAEAD_Advantage G' D (msgs.getD t [])
              (smAEADRed (prodCKA (dhCKA G) (kemCKA KEM)) G' D msgs t (msgs.length - (t + 1)) A)) :=
  le_min (tr_advantage_le_ddh G KEM F G' D msgs A)
    (tr_advantage_le_kem G KEM hkgen hencap F G' D msgs A)

end Triple

/-! ## The costed reductions -/

section Timed

derive_timed oneQueryAdv

/-- **Time of the one-query oracle adversary.** With the query of cost at most `qc` and the
call of the distinguisher of cost at most `b`, the costed `oneQueryAdv` has time at most
`qc + b + 11`: two samples, one query and the case analysis of the run of `pre`. The cost of
`pre` itself is that of its computation tree, counted in `rootOracleRedOf.tree.timeBound_timed`.
-/
theorem oneQueryAdv.timeBound_timed {P Q R : Type} (pre : SPComp P) (q : P → Q)
    (qCost : P → ℕ) (B : P → R → SPComp Bool) (BCost : P → R → ℕ) {qc b : ℕ}
    (hq : ∀ x, qCost x ≤ qc) (hB : ∀ x y, BCost x y ≤ b) :
    OracleAdv.Timed.StepTimeBound (oneQueryAdv.timed pre q qCost B BCost) (qc + b + 11) := by
  unfold oneQueryAdv.timed
  refine ⟨by omega, by omega, fun o => ?_⟩
  rcases o with _ | ⟨x, h⟩
  · dsimp only
    exact ⟨by omega, trivial⟩
  · have := hq x
    dsimp only
    refine ⟨by omega, by omega, fun y => ?_⟩
    have := hB x y
    dsimp only
    exact ⟨by omega, by omega, fun _ => ⟨by dsimp only; omega, trivial⟩⟩

/-- The one-query distinguisher with an oracle `O`: it runs `pub`, calls the oracle on the
query `q x` of its result `x`, and runs `B x` on the answer. Its runs with the keyed oracle and
with a uniform oracle are the two games of `oneQueryAdv pub q B`
(`prTrue_realGame_oneQueryAdv_eq`, `prTrue_rfGame_oneQueryAdv_eq`). -/
noncomputable def rootOracleRedOf {P Q R : Type} (pub : SPComp P) (q : P → Q)
    (B : P → R → SPComp Bool) (O : Q → SPComp R) : SPComp Bool := do
  let x ← pub
  let y ← O (q x)
  B x y

derive_reduction rootOracleRedOf (adv := B O)

/-- The real adaptive PRF game against `oneQueryAdv pub q B` is the run of `rootOracleRedOf`
with the oracle `F k` for a uniform key `k`. -/
theorem prTrue_realGame_oneQueryAdv_eq {P Q R K : Type} [Fintype K] [Nonempty K]
    (F : K → Q → R) (pub : SPComp P) (q : P → Q) (B : P → R → SPComp Bool) :
    prTrue (realGame F (oneQueryAdv pub q B)) Heap.empty =
      prTrue (SPComp.bind (SPComp.sample K) fun k =>
        rootOracleRedOf pub q B fun d => SPComp.pure (F k d)) Heap.empty := by
  rw [prTrue_realGame_oneQueryAdv]
  simp only [rootOracleRedOf, SPComp.monad_bind_eq, SPComp.pure_bind]
  rw [SPComp.isPure_bind_comm_left (SPComp.sample K) pub _ (SPComp.sample_isPure _)]

/-- The random-function adaptive PRF game against `oneQueryAdv pub q B` is the run of
`rootOracleRedOf` with a uniform answer. -/
theorem prTrue_rfGame_oneQueryAdv_eq {P Q R : Type} [DecidableEq Q] [Fintype R] [Nonempty R]
    (pub : SPComp P) (q : P → Q) (B : P → R → SPComp Bool) :
    prTrue (rfGame (oneQueryAdv pub q B)) Heap.empty =
      prTrue (rootOracleRedOf pub q B fun _ => SPComp.sample R) Heap.empty := by
  rw [prTrue_rfGame_oneQueryAdv]
  simp only [rootOracleRedOf, SPComp.monad_bind_eq]

/-- **Time of the one-query distinguisher with an oracle.** With the costed computation of
`pub` of time at most `tp`, the query of cost at most `qc`, the oracle of time at most `To`
and call cost at most `oc`, and the distinguisher of time at most `T` and call cost at most
`b`, the costed tree has time at most `tp + To + T + qc + oc + b + 3`. -/
theorem rootOracleRedOf.tree.timeBound_timed {P Q R : Type} (pub : SPComp P) (q : P → Q)
    (qCost : P → ℕ) (B : P → R → SPTree.Timed Bool) (BCost : P → R → ℕ)
    (O : Q → SPTree.Timed R) (OCost : Q → ℕ) (pubT : SPTree.Timed P) {tp qc To oc T b : ℕ}
    (hp : pubT.time ≤ tp) (hq : ∀ x, qCost x ≤ qc) (hO : ∀ d, (O d).time ≤ To)
    (hOc : ∀ d, OCost d ≤ oc) (hB : ∀ x y, (B x y).time ≤ T) (hBc : ∀ x y, BCost x y ≤ b) :
    SPTree.Timed.stepTime (rootOracleRedOf.tree.timed pub q qCost B BCost O OCost pubT) ≤
      tp + To + T + qc + oc + b + 3 := by
  unfold rootOracleRedOf.tree.timed
  refine (SPTree.Timed.stepTime_bind_le pubT _ (To + T + qc + oc + b + 3) fun x => ?_).trans
    (by omega)
  rw [SPTree.Timed.stepTime_delay]
  have h2 := SPTree.Timed.stepTime_bind_le (O (q x))
    (fun y => (1 + BCost x y, B x y)) (T + b + 1) fun y => by
      have := hB x y; have := hBc x y
      simp only [SPTree.Timed.stepTime]; omega
  have := hO (q x); have := hOc (q x); have := hq x
  omega

variable {S₁ M₁ K₁ S₂ M₂ K₂ RK Sa W Ct : Type} [Fintype K₁] [Nonempty K₁] [Fintype K₂]
  [Nonempty K₂] [Fintype RK] [Nonempty RK] [Fintype Sa] [Nonempty Sa] [SampleableType W]
  [SampleableType Ct]

/-- A prefix of length at most `n` costs at most two units per element and one more. -/
theorem take_timedCost_le {α : Type} (n : ℕ) (l : List α) :
    List.take.timedCost n l ≤ 2 * n + 1 := by
  induction l generalizing n with
  | nil => cases n <;> simp [List.take.timedCost]
  | cons a l ih =>
    cases n
    · simp [List.take.timedCost]
    · have := ih ‹_›; simp [List.take.timedCost]; omega

derive_cost trRootViewL

derive_timed trRootRedL

omit [Fintype K₂] [Nonempty K₂] [Fintype RK] [Nonempty RK] [SampleableType Ct] in
/-- **Time of `trRootRedL`.** With the call cost of the adversary at most `a` and the derived
cost `trRootViewL.timedCost` of the view at most `tv` on every input, the derived costed
reduction has time at most `a + tv + 2 t + 2 r + 21`: the bound `qc + b + 11` of
`oneQueryAdv.timeBound_timed` with the query free and the call of the adversary on the view of
cost at most `a + tv + 2 t + 2 r + 7` (the two prefixes of lengths `t` and `r`), and three
units in front. -/
theorem trRootRedL.timeBound_timed (C : CKADef (S₁ × S₂) (M₁ × M₂) (K₁ × K₂))
    (F : RK × K₁ → K₂ → RK × Sa) (FCost : RK × K₁ → K₂ → ℕ) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (A : SMView (M₁ × M₂) Ct → SPComp Bool) (ACost : SMView (M₁ × M₂) Ct → ℕ)
    (trRoot_stretchCost : (RK × K₁ → K₂ → RK × Sa) → RK × K₁ × K₂ → ℕ)
    (stretchCost : Sa → ℕ) (encryptCost : W → W → W → ℕ) {a tv : ℕ}
    (hA : ∀ x, ACost x ≤ a)
    (hv : ∀ (z : (((M₁ × M₂) × List (M₁ × M₂)) × List (K₁ × K₂) × (K₁ × K₂)) ×
        (List Sa × List K₁)) (y : RK × Sa),
      trRootViewL.timedCost mixLeft (fun _ _ => 1) (trRoot F) G D msgs (z.2.1.take t, z.2.2)
        (z.1.1, z.1.2.1.take r, z.1.2.2) y (trRoot_stretchCost F) stretchCost encryptCost ≤ tv) :
    OracleAdv.Timed.StepTimeBound
      (trRootRedL.timed C F FCost G D msgs t r A ACost trRoot_stretchCost stretchCost
        encryptCost) (a + tv + 2 * t + 2 * r + 21) := by
  unfold trRootRedL.timed
  refine (OracleAdv.Timed.stepTimeBound_delay (oneQueryAdv.timeBound_timed _ _ _ _ _
    (qc := 0) (b := a + tv + 2 * t + 2 * r + 7) (fun _ => le_rfl) fun z y => ?_)).mono
    (by omega)
  have := hA (trRootViewL mixLeft (trRoot F) G D msgs (z.2.1.take t, z.2.2)
    (z.1.1, z.1.2.1.take r, z.1.2.2) y)
  have := hv z y
  have := take_timedCost_le t z.2.1
  have := take_timedCost_le r z.1.2.1
  omega

derive_timed trRootRedR

omit [Fintype K₁] [Nonempty K₁] [SampleableType Ct] in
/-- **Time of `trRootRedR`.** With the call cost of the adversary at most `a` and the derived
cost `trRootViewL.timedCost` of the view at most `tv` on every input, the derived costed
reduction has time at most `a + tv + 2 t + 2 r + 21`, as for `trRootRedL`. -/
theorem trRootRedR.timeBound_timed (C : CKADef (S₁ × S₂) (M₁ × M₂) (K₁ × K₂))
    (F : RK × K₁ → K₂ → RK × Sa) (FCost : RK × K₁ → K₂ → ℕ) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (A : SMView (M₁ × M₂) Ct → SPComp Bool) (ACost : SMView (M₁ × M₂) Ct → ℕ)
    (trRoot_stretchCost : (RK × K₁ → K₂ → RK × Sa) → RK × K₁ × K₂ → ℕ)
    (stretchCost : Sa → ℕ) (encryptCost : W → W → W → ℕ) {a tv : ℕ}
    (hA : ∀ x, ACost x ≤ a)
    (hv : ∀ (z : (((M₁ × M₂) × List (M₁ × M₂)) × List (K₁ × K₂) × (K₁ × K₂)) ×
        (List Sa × List K₂) × RK) (y : RK × Sa),
      trRootViewL.timedCost mixRight (fun _ _ => 1) (trRoot F) G D msgs
        (z.2.1.1.take t, z.2.1.2) (z.1.1, z.1.2.1.take r, z.1.2.2) y (trRoot_stretchCost F)
        stretchCost encryptCost ≤ tv) :
    OracleAdv.Timed.StepTimeBound
      (trRootRedR.timed C F FCost G D msgs t r A ACost trRoot_stretchCost stretchCost
        encryptCost) (a + tv + 2 * t + 2 * r + 21) := by
  unfold trRootRedR.timed
  refine (OracleAdv.Timed.stepTimeBound_delay (oneQueryAdv.timeBound_timed _ _ _ _ _
    (qc := 0) (b := a + tv + 2 * t + 2 * r + 7) (fun _ => le_rfl) fun z y => ?_)).mono
    (by omega)
  have := hA (trRootViewL mixRight (trRoot F) G D msgs (z.2.1.1.take t, z.2.1.2)
    (z.1.1, z.1.2.1.take r, z.1.2.2) y)
  have := hv z y
  have := take_timedCost_le t z.2.1.1
  have := take_timedCost_le r z.1.2.1
  omega

end Timed

section TimedCKA

variable {Sc Msg Key X RK Sa W Ct : Type} [Fintype X] [Nonempty X] [Fintype RK]
  [Nonempty RK] [SampleableType W]

derive_cost trCKAViewL

derive_reduction trCKARed (adv := A)

/-- The derived costed form of `trCKARed` erases and compiles to `trCKARed` at the erased
adversary. -/
theorem trCKARed.erase_timed (mix : X → Key → Key) (mixCost : X → Key → ℕ)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t : ℕ) (A : SMView Msg Ct → SPTree.Timed Bool)
    (ACost : SMView Msg Ct → ℕ) (v : CKAView Msg Key) (stretchCost : RK × Key → ℕ)
    (stretchCost' : Sa → ℕ) (encryptCost : W → W → W → ℕ) :
    (trCKARed.tree.timed mix mixCost R G D msgs t A ACost v stretchCost stretchCost'
        encryptCost).2.erase.compile =
      trCKARed mix R G D msgs t (fun x => (A x).erase.compile) v := by
  rw [trCKARed.tree.erase_timed, trCKARed.compile_tree]

/-- **Time of `trCKARed`.** With the costed adversary of time at most `T` and call cost at
most `a`, and the derived cost `trCKAViewL.timedCost` of the view of `v` at most `tv` for every
uniform value, the derived costed reduction at `v` has time at most `T + a + tv + 4 t + 11`:
one sample, the list of the `t` uniform values, the view and the adversary call. -/
theorem trCKARed.timeBound_timed (mix : X → Key → Key) (mixCost : X → Key → ℕ)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t : ℕ) (A : SMView Msg Ct → SPTree.Timed Bool)
    (ACost : SMView Msg Ct → ℕ) (v : CKAView Msg Key) (stretchCost : RK × Key → ℕ)
    (stretchCost' : Sa → ℕ) (encryptCost : W → W → W → ℕ) {T a tv : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hv : ∀ x : (Fin t → X) × RK, trCKAViewL.timedCost mix mixCost R G D msgs (List.ofFn x.1)
      x.2 v stretchCost stretchCost' encryptCost ≤ tv) :
    SPTree.Timed.stepTime (trCKARed.tree.timed mix mixCost R G D msgs t A ACost v stretchCost
      stretchCost' encryptCost) ≤ T + a + tv + 4 * t + 11 := by
  simp only [SPTree.Timed.stepTime, trCKARed.tree.timed, SPTree.Timed.time_sample]
  refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left
    (Finset.sup_le (a := T + a + tv + 4 * t + 10) fun b _ => ?_) 1) 0) (by omega)
  have := hA (trCKAView mix R G D msgs t b v)
  have := hAc (trCKAView mix R G D msgs t b v)
  have := hv b
  have := Fin.foldr.loop.timedCost_le t (fun i l => b.1 i :: l) (fun _ _ => 1) (k := 1)
    (fun _ _ => le_rfl) t le_rfl []
  omega

end TimedCKA

section TimedProd

variable {S₁ M₁ K₁ S₂ M₂ K₂ : Type}

/-- Zipping costs at most `k + 3` units per element of the second list and one more. -/
theorem zipWith_timedCost_le_right {α β γ : Type} (f : α → β → γ) (fCost : α → β → ℕ)
    {k : ℕ} (hf : ∀ a b, fCost a b ≤ k) (l₁ : List α) (l₂ : List β) :
    List.zipWith.timedCost f fCost l₁ l₂ ≤ (k + 3) * l₂.length + 1 := by
  induction l₂ generalizing l₁ with
  | nil => cases l₁ <;> simp [List.zipWith.timedCost]
  | cons b l₂ ih =>
    cases l₁ with
    | nil => simp [List.zipWith.timedCost]
    | cons a l₁ =>
      have := hf a b; have := ih l₁
      simp [List.zipWith.timedCost, Nat.mul_succ]; omega

/-- The step time of a step-prefixed costed tree `P` followed by `g`, with the step cost of `P`
in front, is at most the step time of `P` plus a bound on the step times of `g`. -/
theorem stepTime_delay_fst_bind_le {α β : Type} (P : ℕ × SPTree.Timed α)
    (g : α → ℕ × SPTree.Timed β) {G : ℕ} (hg : ∀ x, SPTree.Timed.stepTime (g x) ≤ G) :
    SPTree.Timed.stepTime (SPTree.Timed.delay P.1 (P.2.bind g)) ≤
      SPTree.Timed.stepTime P + G := by
  have := SPTree.Timed.stepTime_bind_le P.2 g G hg
  simp only [SPTree.Timed.stepTime, SPTree.Timed.delay] at this ⊢
  omega

/-- As `stepTime_delay_fst_bind_le`, with `c` further units in front. -/
theorem stepTime_delay_add_fst_bind_le {α β : Type} (c : ℕ) (P : ℕ × SPTree.Timed α)
    (g : α → ℕ × SPTree.Timed β) {G : ℕ} (hg : ∀ x, SPTree.Timed.stepTime (g x) ≤ G) :
    SPTree.Timed.stepTime (SPTree.Timed.delay (c + P.1) (P.2.bind g)) ≤
      c + SPTree.Timed.stepTime P + G := by
  have := SPTree.Timed.stepTime_bind_le P.2 g G hg
  simp only [SPTree.Timed.stepTime, SPTree.Timed.delay] at this ⊢
  omega

/-- The step time of a costed tree `A` followed by `g`, with `c` units in front, is at most
`c` plus the time of `A` plus a bound on the step times of `g`. -/
theorem stepTime_delay_bind_le_of {α β : Type} (c : ℕ) (A : SPTree.Timed α)
    (g : α → ℕ × SPTree.Timed β) {G : ℕ} (hg : ∀ x, SPTree.Timed.stepTime (g x) ≤ G) :
    SPTree.Timed.stepTime (SPTree.Timed.delay c (A.bind g)) ≤ c + A.time + G := by
  have := SPTree.Timed.stepTime_bind_le A g G hg
  rw [SPTree.Timed.stepTime_delay]
  omega

derive_reduction prodCKARedR (adv := A)

/-- **Time of the derived CKA run.** With the costed sending of time at most `ts` and call cost
at most `cs`, and the receiving of cost at most `cr`, the derived costed run of `n` epochs has
time at most `n (ts + cs + cr + 4) + 1`. -/
theorem ckaRun.tree.timeBound_timed {St Msg Key : Type} (C : CKADef St Msg Key)
    (recv : St → Msg → St × Key) (recvCost : St → Msg → ℕ)
    (send : St → SPTree.Timed (St × Msg × Key)) (sendCost : St → ℕ) {ts cs cr : ℕ}
    (hs : ∀ s, (send s).time ≤ ts) (hsc : ∀ s, sendCost s ≤ cs)
    (hrc : ∀ s m, recvCost s m ≤ cr) (n : ℕ) (s r : St) :
    SPTree.Timed.stepTime (ckaRun.tree.timed C n s r recv recvCost send sendCost) ≤
      n * (ts + cs + cr + 4) + 1 := by
  induction n generalizing s r with
  | zero =>
    simp [ckaRun.tree.timed, SPTree.Timed.delay, SPTree.Timed.stepTime, SPTree.Timed.time_ret]
  | succ n ih =>
    simp only [ckaRun.tree.timed]
    rw [SPTree.Timed.stepTime_delay]
    refine (Nat.add_le_add_left (stepTime_delay_bind_le_of _ _ _
      (G := n * (ts + cs + cr + 4) + cr + 3) fun x => ?_) 1).trans ?_
    · refine (stepTime_delay_add_fst_bind_le _ _ _ (G := 0) fun _ => by
        simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret]).trans ?_
      have := ih (recv r x.2.1).1 x.1
      have := hrc r x.2.1
      omega
    · have := hs s; have := hsc s
      rw [Nat.succ_mul]
      omega

/-- The derived costed form of `prodCKARedR`, with a costed initialisation and sending of `C₁`
that compile to those of `C₁`, erases and compiles to `prodCKARedR` at the erased
adversary. -/
theorem prodCKARedR.erase_timed (C₁ : CKADef S₁ M₁ K₁) (k m : ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPTree.Timed Bool)
    (ACost : CKAView (M₁ × M₂) (K₁ × K₂) → ℕ) (y : CKAView M₂ K₂)
    (recvCost : S₁ → M₁ → ℕ) (init : SPTree.Timed (M₁ × S₁ × S₁))
    (send : S₁ → SPTree.Timed (S₁ × M₁ × K₁)) (sendCost : S₁ → ℕ)
    (hinit : init.erase.compile = C₁.init) (hsend : ∀ s, (send s).erase.compile = C₁.send s) :
    (prodCKARedR.tree.timed C₁ k m A ACost y C₁.recv recvCost init send sendCost).2.erase.compile =
      prodCKARedR C₁ k m (fun x => (A x).erase.compile) y := by
  rw [prodCKARedR.tree.erase_timed, prodCKARedR.compile_tree _ _ _ _ _ _ _ hinit hsend]

/-- **Time of `prodCKARedR`.** With the costed adversary of time at most `T` and call cost at
most `a`, the costed initialisation of `C₁` of time at most `ti`, the costed sending of time at
most `ts` and call cost at most `cs`, and the receiving of cost at most `cr`, the derived
costed reduction at `y` has time at most
`T + a + ti + (k + m + 1) (ts + cs + cr + 4) + 3 (ℓ₁ + ℓ₂) + 10`, where `ℓ₁` and `ℓ₂` are the
numbers of epochs of `y` before and after its challenge epoch: the real game of `C₁`, the view
zipped with `y`, and the adversary call. -/
theorem prodCKARedR.timeBound_timed (C₁ : CKADef S₁ M₁ K₁) (k m : ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPTree.Timed Bool)
    (ACost : CKAView (M₁ × M₂) (K₁ × K₂) → ℕ) (y : CKAView M₂ K₂)
    (recv : S₁ → M₁ → S₁ × K₁) (recvCost : S₁ → M₁ → ℕ) (init : SPTree.Timed (M₁ × S₁ × S₁))
    (send : S₁ → SPTree.Timed (S₁ × M₁ × K₁)) (sendCost : S₁ → ℕ) {T a ti ts cs cr : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (hi : init.time ≤ ti)
    (hs : ∀ s, (send s).time ≤ ts) (hsc : ∀ s, sendCost s ≤ cs)
    (hrc : ∀ s m, recvCost s m ≤ cr) :
    SPTree.Timed.stepTime
        (prodCKARedR.tree.timed C₁ k m A ACost y recv recvCost init send sendCost) ≤
      T + a + ti + (k + m + 1) * (ts + cs + cr + 4) + 3 * (y.2.1.length + y.2.2.2.length) +
        10 := by
  have hk := ckaRun.tree.timeBound_timed C₁ recv recvCost send sendCost hs hsc hrc k
  have hm := ckaRun.tree.timeBound_timed C₁ recv recvCost send sendCost hs hsc hrc m
  unfold prodCKARedR.tree.timed
  refine (stepTime_delay_fst_bind_le _ _
    (G := T + a + 3 * (y.2.1.length + y.2.2.2.length) + 8) fun x => ?_).trans ?_
  · have := hA (zipView x y); have := hAc (zipView x y)
    have := zipWith_timedCost_le_right (fun a b => ((a.1, b.1), a.2, b.2))
      (fun _ _ => 0) (k := 0) (fun _ _ => le_rfl) x.2.1 y.2.1
    have := zipWith_timedCost_le_right (fun a b => ((a.1, b.1), a.2, b.2))
      (fun _ _ => 0) (k := 0) (fun _ _ => le_rfl) x.2.2.2 y.2.2.2
    simp only [SPTree.Timed.stepTime]
    omega
  · refine le_trans (Nat.add_le_add_right (SPTree.Timed.stepTime_bind_le init _
      (k * (ts + cs + cr + 4) + m * (ts + cs + cr + 4) + ts + cs + cr + 6) fun x => ?_) _) ?_
    · refine (stepTime_delay_add_fst_bind_le 1 _ _
        (G := m * (ts + cs + cr + 4) + ts + cs + cr + 4) fun x₁ => ?_).trans ?_
      · refine (stepTime_delay_bind_le_of _ _ _
          (G := m * (ts + cs + cr + 4) + cr + 3) fun x₂ => ?_).trans ?_
        · refine (stepTime_delay_add_fst_bind_le _ _ _ (G := 0) fun _ => by
            simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret]).trans ?_
          have := hm (recv x₁.2.2 x₂.2.1).1 x₂.1
          have := hrc x₁.2.2 x₂.2.1
          omega
        · have := hs x₁.2.1; have := hsc x₁.2.1
          omega
      · have := hk x.2.1 x.2.2
        omega
    · have e : (k + m + 1) * (ts + cs + cr + 4) =
          k * (ts + cs + cr + 4) + m * (ts + cs + cr + 4) + (ts + cs + cr + 4) := by ring
      omega

end TimedProd

end CatCrypt.Crypto.Messaging
