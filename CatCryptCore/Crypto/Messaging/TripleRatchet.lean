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

DOCSTRING
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

/-- The view of the CKA reduction at epoch `t` with the replacement `mix`, from the uniform
values `x.1` of the epochs before `t`, the root key `x.2` and the CKA view `v`. -/
def trCKAView (mix : X → Key → Key) (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t : ℕ) (x : (Fin t → X) × RK)
    (v : CKAView Msg Key) : SMView Msg Ct :=
  ((v.1, v.2.1.map Prod.fst ++ v.2.2.1.1 :: v.2.2.2.map Prod.fst),
    smCts G D (rootRun R x.2 (mixKeys mix (List.ofFn x.1) (v.2.1.map Prod.snd) ++
      v.2.2.1.2 :: v.2.2.2.map Prod.snd)) msgs)

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
  simp only [trHybK, cka_real, trCKARed, smSampleRedOf, trCKAView, SPComp.monad_bind_eq,
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
  simp only [trHybK, cka_mix, trCKARed, smSampleRedOf, trCKAView, SPComp.monad_bind_eq,
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

/-- The view of the root hop at epoch `t` with `r` epochs after it, from the uniform FS-AEAD
states `x.1` of the epochs before `t`, the uniform values `x.2` of the replacement after it,
the public part `c` and the next root key and FS-AEAD state `y` of epoch `t`. -/
def trRootView (mix : X → Key → Key) (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (x : (Fin t → Sa) × (Fin r → X)) (c : (Msg × List Msg) × List Key × Key) (y : RK × Sa) :
    SMView Msg Ct :=
  (c.1, smCts G D (List.ofFn x.1 ++ y.2 :: rootRun R y.1 (mixKeys mix (List.ofFn x.2) c.2.1))
    msgs)

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
  simp only [trHybP, trRoot_real, trRootPub, trRootView, SPComp.bind_assoc, SPComp.pure_bind]
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
  simp only [trHybP, trRoot_ideal, trRootPub, trRootView, SPComp.bind_assoc, SPComp.pure_bind]
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

end SM

end CatCrypt.Crypto.Messaging
