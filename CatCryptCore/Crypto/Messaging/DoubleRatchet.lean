/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.CKA
public import CatCryptCore.Crypto.Messaging.FSAEAD

/-!
# The double ratchet: confidentiality from CKA, the root KDF and FS-AEAD

The double ratchet of Alwen, Coretti and Dodis composes three primitives over epochs. In epoch
`t` the CKA scheme `C` produces a message `T_t`, sent in the clear, and a key `I_t`; the root
KDF `R : PRGDef (RK × Key) (RK × Sa)` maps the root key `rk_t` and `I_t` to the next root key
`rk_{t+1}` and the initial state `sa_t` of the FS-AEAD instance of the epoch; the FS-AEAD
instance encrypts the messages of the epoch under the outputs of the generator `G` from
`sa_t`.

The secure-messaging game `sm_real`/`sm_ideal` gives the adversary the public value of the CKA
initialisation, the CKA messages of the `n` epochs and the ciphertexts of all epochs; in the
ideal game the ciphertexts are uniform. This is the confidentiality of messages in epochs
without state compromise.

The proof has three hybrid phases: the CKA keys are replaced by uniform keys one epoch at a
time (CKA advantage of `smCKARed`), the outputs of the root KDF one epoch at a time (PRG
advantage of `smRootRed`), and the ciphertexts of each epoch under a uniform FS-AEAD state by
uniform ciphertexts (FS-AEAD advantage of `smAEADRed`).

## Main definitions

* `rootRun`, `encEpoch`, `smCts` — the root chain, and the ciphertexts of the epochs
* `ckaPub` — the public value and the messages of a CKA run
* `sm_real`, `sm_ideal`, `SM_Advantage` — the secure-messaging confidentiality game
* `smSampleRedOf`, `smPubRedOf` — the distinguishers that sample a uniform value, run the CKA
  where needed, and call the adversary on a view
* `smCKARed`, `smRootRed`, `smAEADRed` — the reductions of the three phases

## Main results

* `sm_advantage_le` — for every adversary `A`, the secure-messaging advantage is at most the
  sum over the epochs of the CKA advantages of `smCKARed`, the PRG advantages of the root KDF
  at `smRootRed` and the FS-AEAD advantages of `smAEADRed`
* `sm_dh_advantage_le` — with the Diffie–Hellman CKA `dhCKA`, the CKA terms are DDH advantages
  of `ckaDDHRed` at `smCKARed`
* `smCKARed.timeBound_timed`, `smRootRed.timeBound_timed`, `smAEADRed.timeBound_timed` — the
  times of the costed reductions

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §5 (Theorem 6, confidentiality)
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
  CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

/-! ## The deterministic part of the ratchet -/

section Det

variable {Msg Key RK Sa W Ct : Type} [SampleableType W] [SampleableType Ct]

/-- The FS-AEAD states of the epochs: from the root key `rk`, the root KDF `R` maps the root key
and the CKA key of each epoch to the next root key and the FS-AEAD state of the epoch. -/
def rootRun (R : PRGDef (RK × Key) (RK × Sa)) : RK → List Key → List Sa
  | _, [] => []
  | rk, I :: Is => (R.stretch (rk, I)).2 :: rootRun R (R.stretch (rk, I)).1 Is

/-- The ciphertexts of the messages `ms` of one epoch, encrypted under the outputs of the
generator `G` from the FS-AEAD state `sa`. -/
def encEpoch (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (sa : Sa) (ms : List (W × W)) :
    List Ct :=
  encAll D (fsprgRun G ms.length sa).1 ms

/-- The ciphertexts of the epochs from their FS-AEAD states `sas`, epoch by epoch. -/
def smCts (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (sas : List Sa)
    (msgs : List (List (W × W))) : List (List Ct) :=
  List.zipWith (encEpoch G D) sas msgs

/-- The number of messages of epoch `j`. -/
def epochLen (msgs : List (List (W × W))) (j : ℕ) : ℕ := (msgs.getD j []).length

/-- Uniform ciphertexts of the first `t` epochs: for each epoch `j < t`, one ciphertext per
message. -/
abbrev IdealCts (Ct : Type) (msgs : List (List (W × W))) (t : ℕ) : Type :=
  (j : Fin t) → Fin (epochLen msgs j) → Ct

/-- The ciphertext lists of the vector `v` of uniform ciphertexts. -/
def ctsOf {msgs : List (List (W × W))} {t : ℕ} (v : IdealCts Ct msgs t) : List (List Ct) :=
  List.ofFn fun j => List.ofFn (v j)

/-- The view of the secure-messaging adversary: the public value of the CKA initialisation and
the CKA messages, and the ciphertexts of the epochs. -/
abbrev SMView (Msg Ct : Type) := (Msg × List Msg) × List (List Ct)

end Det

/-! ## The secure-messaging game -/

variable {Sc Msg Key RK Sa W Ct : Type} [Fintype Key] [Nonempty Key] [Fintype RK]
  [Nonempty RK] [Fintype Sa] [Nonempty Sa] [SampleableType W] [SampleableType Ct]

/-- The public value of the initialisation and the messages of `n` epochs of `C`. -/
noncomputable def ckaPub (C : CKADef Sc Msg Key) (n : ℕ) : SPComp (Msg × List Msg) :=
  SPComp.bind C.init fun i =>
    SPComp.bind (ckaRun C n i.2.1 i.2.2) fun p => SPComp.pure (i.1, p.1.map Prod.fst)

/-- Secure-messaging real game over the epochs with the messages `msgs`: a CKA run of one
epoch per entry of `msgs`, a uniform initial root key, and the ciphertexts of the epochs. -/
noncomputable def sm_real (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) :
    SPComp (SMView Msg Ct) :=
  SPComp.bind C.init fun i =>
    SPComp.bind (ckaRun C msgs.length i.2.1 i.2.2) fun p =>
      SPComp.bind (SPComp.sample RK) fun rk =>
        SPComp.pure ((i.1, p.1.map Prod.fst), smCts G D (rootRun R rk (p.1.map Prod.snd)) msgs)

/-- Secure-messaging ideal game: the CKA run, and uniform ciphertexts. -/
noncomputable def sm_ideal (C : CKADef Sc Msg Key) (msgs : List (List (W × W))) :
    SPComp (SMView Msg Ct) :=
  SPComp.bind (ckaPub C msgs.length) fun c =>
    SPComp.bind (SPComp.sample (IdealCts Ct msgs msgs.length)) fun v =>
      SPComp.pure (c, ctsOf v)

/-- Secure-messaging confidentiality advantage of the distinguisher `A`. -/
noncomputable def SM_Advantage (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W)))
    (A : SMView Msg Ct → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (sm_real C R G D msgs) (sm_ideal C msgs) A

/-! ## The reductions -/

/-- The distinguisher with the view function `view`: on the challenge `y` it samples a uniform
`x` and calls `A` on `view x y`. -/
noncomputable def smSampleRedOf {X Y V : Type} [Fintype X] [Nonempty X] (view : X → Y → V)
    (A : V → SPComp Bool) (y : Y) : SPComp Bool := do
  let x ← SPComp.sample X
  A (view x y)

/-- The distinguisher with the public computation `pub` and the view function `view`: on the
challenge `y` it samples a uniform `x`, runs `pub` and calls `A` on its result and `view x y`. -/
noncomputable def smPubRedOf {X Y P L : Type} [Fintype X] [Nonempty X] (pub : SPComp P)
    (view : X → Y → L) (A : P × L → SPComp Bool) (y : Y) : SPComp Bool := do
  let x ← SPComp.sample X
  let c ← pub
  A (c, view x y)

/-- The view of the CKA reduction at epoch `t` with `m` epochs after it, from the uniform keys
`x.1` of the epochs before `t`, the root key `x.2` and the CKA view `v`. -/
def smCKAView (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t : ℕ) (x : (Fin t → Key) × RK) (v : CKAView Msg Key) :
    SMView Msg Ct :=
  ((v.1, v.2.1.map Prod.fst ++ v.2.2.1.1 :: v.2.2.2.map Prod.fst),
    smCts G D (rootRun R x.2 (List.ofFn x.1 ++ v.2.2.1.2 :: v.2.2.2.map Prod.snd)) msgs)

/-- The CKA distinguisher of epoch `t`: uniform keys for the epochs before `t`, the challenge
key for epoch `t`, the real keys after it. -/
noncomputable def smCKARed (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t : ℕ)
    (A : SMView Msg Ct → SPComp Bool) : CKAView Msg Key → SPComp Bool :=
  smSampleRedOf (smCKAView R G D msgs t) A

/-- The ciphertexts of the root-KDF reduction at epoch `t` with `r` epochs after it, from the
uniform FS-AEAD states `x.1` of the epochs before `t`, the uniform CKA keys `x.2` after it and
the challenge `y` of the next root key and the FS-AEAD state of epoch `t`. -/
def smRootView (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t r : ℕ) (x : (Fin t → Sa) × (Fin r → Key)) (y : RK × Sa) :
    List (List Ct) :=
  smCts G D (List.ofFn x.1 ++ y.2 :: rootRun R y.1 (List.ofFn x.2)) msgs

/-- The PRG distinguisher of the root KDF at epoch `t`. -/
noncomputable def smRootRed (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (A : SMView Msg Ct → SPComp Bool) : RK × Sa → SPComp Bool :=
  smPubRedOf (ckaPub C msgs.length) (smRootView R G D msgs t r) A

/-- The ciphertexts of the FS-AEAD reduction at epoch `t` with `r` epochs after it, from the
uniform ciphertexts `x.1` of the epochs before `t`, the uniform FS-AEAD states `x.2` after it
and the FS-AEAD challenge `y`. -/
def smAEADView (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W)))
    (t r : ℕ) (x : IdealCts Ct msgs t × (Fin r → Sa)) (y : List Ct × Sa) : List (List Ct) :=
  ctsOf x.1 ++ y.1 :: smCts G D (List.ofFn x.2) (msgs.drop (t + 1))

/-- The FS-AEAD distinguisher of epoch `t`. -/
noncomputable def smAEADRed (C : CKADef Sc Msg Key) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t r : ℕ) (A : SMView Msg Ct → SPComp Bool) :
    List Ct × Sa → SPComp Bool :=
  smPubRedOf (ckaPub C msgs.length) (smAEADView G D msgs t r) A

/-! ## Hybrids -/

/-- CKA hybrid `t`: the CKA keys of the first `t` epochs are uniform. -/
noncomputable def smHybK (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) (t : ℕ) :
    SPComp (SMView Msg Ct) :=
  SPComp.bind C.init fun i =>
    SPComp.bind (ckaRun C msgs.length i.2.1 i.2.2) fun p =>
      SPComp.bind (SPComp.sample (Fin t → Key)) fun u =>
        SPComp.bind (SPComp.sample RK) fun rk =>
          SPComp.pure ((i.1, p.1.map Prod.fst),
            smCts G D (rootRun R rk (List.ofFn u ++ (p.1.map Prod.snd).drop t)) msgs)

/-- Root hybrid `(t, r)`: the FS-AEAD states of the first `t` epochs are uniform, those of the
next `r` epochs come from the root chain from a uniform root key with uniform CKA keys. -/
noncomputable def smHybP (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ) :
    SPComp (SMView Msg Ct) :=
  SPComp.bind (SPComp.sample (Fin t → Sa)) fun u =>
    SPComp.bind (SPComp.sample (Fin r → Key)) fun ks =>
      SPComp.bind (SPComp.sample RK) fun rk =>
        SPComp.bind (ckaPub C msgs.length) fun c =>
          SPComp.pure (c, smCts G D (List.ofFn u ++ rootRun R rk (List.ofFn ks)) msgs)

/-- FS-AEAD hybrid `(t, r)`: the ciphertexts of the first `t` epochs are uniform, those of the
next `r` epochs are encryptions from uniform FS-AEAD states. -/
noncomputable def smHybF (C : CKADef Sc Msg Key) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (t r : ℕ) : SPComp (SMView Msg Ct) :=
  SPComp.bind (SPComp.sample (IdealCts Ct msgs t)) fun vc =>
    SPComp.bind (SPComp.sample (Fin r → Sa)) fun vs =>
      SPComp.bind (ckaPub C msgs.length) fun c =>
        SPComp.pure (c, ctsOf vc ++ smCts G D (List.ofFn vs) (msgs.drop t))

/-! ## Runs of the CKA -/

omit [Fintype Key] [Nonempty Key] in
/-- A run of `k + m` epochs is a run of `k` epochs followed by a run of `m` epochs. -/
theorem ckaRun_add_bind {β : Type} (C : CKADef Sc Msg Key) (k m : ℕ) (s r : Sc)
    (K : List (Msg × Key) × Sc × Sc → SPComp β) :
    SPComp.bind (ckaRun C (k + m) s r) K =
      SPComp.bind (ckaRun C k s r) fun p =>
        SPComp.bind (ckaRun C m p.2.1 p.2.2) fun q => K (p.1 ++ q.1, q.2) := by
  induction k generalizing s r K with
  | zero => simp only [Nat.zero_add, ckaRun, SPComp.pure_bind, List.nil_append]
  | succ k ih =>
    rw [Nat.succ_add]
    simp only [ckaRun, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext o
    rw [ih]
    simp only [List.cons_append]

omit [Fintype Key] [Nonempty Key] in
/-- The transcript of a run of `n` epochs has length `n`: continuations that agree on
transcripts of length `n` give the same computation. -/
theorem ckaRun_bind_congr {β : Type} (C : CKADef Sc Msg Key) (n : ℕ) (s r : Sc)
    (K K' : List (Msg × Key) × Sc × Sc → SPComp β) (h : ∀ p, p.1.length = n → K p = K' p) :
    SPComp.bind (ckaRun C n s r) K = SPComp.bind (ckaRun C n s r) K' := by
  induction n generalizing s r K K' with
  | zero => simp only [ckaRun, SPComp.pure_bind]; exact h _ rfl
  | succ n ih =>
    simp only [ckaRun, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext o
    exact ih _ _ _ _ fun p hp => h _ (by simp [hp])

/-! ## The CKA phase -/

omit [Fintype Sa] [Nonempty Sa] [SampleableType Ct] in
/-- CKA hybrid `0` is the real game. -/
theorem smHybK_zero (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) :
    smHybK C R G D msgs 0 = sm_real C R G D msgs := by
  simp only [smHybK, sm_real, sample_bind_unique, List.ofFn_zero, List.nil_append,
    List.drop_zero]

omit [Fintype Sa] [Nonempty Sa] [SampleableType Ct] in
/-- CKA hybrid `t` is the real CKA game at the challenge epoch `t` of `smCKARed`. -/
theorem smHybK_bind_eq_real (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) (t m : ℕ)
    (hm : msgs.length = t + (m + 1)) (A : SMView Msg Ct → SPComp Bool) :
    (smHybK C R G D msgs t).bind A = (cka_real C t m).bind (smCKARed R G D msgs t A) := by
  simp only [smHybK, cka_real, smCKARed, smSampleRedOf, smCKAView, SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext i
  rw [hm, ckaRun_add_bind]
  apply ckaRun_bind_congr; intro p hp
  simp only [ckaRun, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext o; congr 1; funext q
  have hd : List.drop t (List.map Prod.snd (p.1 ++ (o.2.1, o.2.2) :: q.1)) =
      o.2.2 :: List.map Prod.snd q.1 := by
    rw [List.map_append, List.drop_left' (by simp [hp])]; rfl
  rw [hd]
  simp only [List.map_append, List.map_cons, SPComp.sample_prod_eq, SPComp.bind_assoc,
    SPComp.pure_bind]

omit [Fintype Sa] [Nonempty Sa] [SampleableType Ct] in
/-- CKA hybrid `t + 1` is the ideal CKA game at the challenge epoch `t` of `smCKARed`. -/
theorem smHybK_succ_bind_eq_ideal (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) (t m : ℕ)
    (hm : msgs.length = t + (m + 1)) (A : SMView Msg Ct → SPComp Bool) :
    (smHybK C R G D msgs (t + 1)).bind A =
      (cka_ideal C t m).bind (smCKARed R G D msgs t A) := by
  simp only [smHybK, cka_ideal, smCKARed, smSampleRedOf, smCKAView, SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext i
  rw [hm, ckaRun_add_bind]
  apply ckaRun_bind_congr; intro p hp
  simp only [ckaRun, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext o
  rw [SPComp.isPure_bind_comm_left (SPComp.sample Key) _ _ (SPComp.sample_isPure _)]
  congr 1; funext q
  have hd : List.drop (t + 1) (List.map Prod.snd (p.1 ++ (o.2.1, o.2.2) :: q.1)) =
      List.map Prod.snd q.1 := by
    have hl : (List.map Prod.snd p.1).length = t := by simp [hp]
    rw [List.map_append, List.map_cons, ← hl, List.drop_append]; simp
  rw [hd, ← SPComp.sample_bind_equiv (Fin.snocEquiv fun _ => Key)]
  have he : ∀ (a : Key) (v : Fin t → Key), (Fin.snocEquiv fun _ => Key) (a, v) =
      Fin.snoc (α := fun _ => Key) v a := fun _ _ => rfl
  simp only [List.map_append, List.map_cons, SPComp.sample_prod_eq, SPComp.bind_assoc,
    SPComp.pure_bind, he, ofFn_snoc, List.append_assoc, List.singleton_append]

omit [SampleableType Ct] in
/-- CKA hybrid `n` is root hybrid `(0, n)`. -/
theorem smHybK_self_bind (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W)))
    (A : SMView Msg Ct → SPComp Bool) :
    (smHybK C R G D msgs msgs.length).bind A = (smHybP C R G D msgs 0 msgs.length).bind A := by
  have h : (smHybK C R G D msgs msgs.length).bind A =
      SPComp.bind C.init fun i =>
        SPComp.bind (ckaRun C msgs.length i.2.1 i.2.2) fun p =>
          SPComp.bind (SPComp.sample (Fin msgs.length → Key)) fun u =>
            SPComp.bind (SPComp.sample RK) fun rk =>
              A ((i.1, p.1.map Prod.fst), smCts G D (rootRun R rk (List.ofFn u)) msgs) := by
    simp only [smHybK, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext i
    apply ckaRun_bind_congr; intro p hp
    rw [List.drop_eq_nil_of_le (by simp [hp])]
    simp only [List.append_nil]
  rw [h]
  simp only [smHybP, ckaPub, SPComp.bind_assoc, SPComp.pure_bind, sample_bind_unique,
    List.ofFn_zero, List.nil_append]
  symm; bind_swap_nf

/-! ## The root phase -/

omit [SampleableType Ct] in
/-- Root hybrid `(t, r + 1)` is the real PRG game of `smRootRed`. -/
theorem smHybP_bind_eq_real (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (A : SMView Msg Ct → SPComp Bool) :
    (smHybP C R G D msgs t (r + 1)).bind A = (prg_real R).bind (smRootRed C R G D msgs t r A) := by
  simp only [smHybP, prg_real, smRootRed, smPubRedOf, smRootView, SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind]
  simp only [← SPComp.sample_bind_equiv (Fin.consEquiv fun _ => Key)]
  have he : ∀ (a : Key) (v : Fin r → Key), (Fin.consEquiv fun _ => Key) (a, v) =
      Fin.cons (α := fun _ => Key) a v := fun _ _ => rfl
  simp only [SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind, he, ofFn_cons,
    rootRun]
  symm; bind_swap_nf

omit [SampleableType Ct] in
/-- Root hybrid `(t + 1, r)` is the ideal PRG game of `smRootRed`. -/
theorem smHybP_succ_bind_eq_ideal (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (A : SMView Msg Ct → SPComp Bool) :
    (smHybP C R G D msgs (t + 1) r).bind A =
      (prg_ideal (Output := RK × Sa)).bind (smRootRed C R G D msgs t r A) := by
  simp only [smHybP, prg_ideal, smRootRed, SPComp.bind_assoc, SPComp.pure_bind]
  simp only [← SPComp.sample_bind_equiv (Fin.snocEquiv fun _ => Sa)]
  have he : ∀ (a : Sa) (v : Fin t → Sa), (Fin.snocEquiv fun _ => Sa) (a, v) =
      Fin.snoc (α := fun _ => Sa) v a := fun _ _ => rfl
  simp only [SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind, he, ofFn_snoc,
    List.append_assoc, List.singleton_append, smPubRedOf, smRootView, SPComp.monad_bind_eq]
  symm; bind_swap_nf

/-- Root hybrid `(n, 0)` is FS-AEAD hybrid `(0, n)`. -/
theorem smHybP_self_bind (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W)))
    (A : SMView Msg Ct → SPComp Bool) :
    (smHybP C R G D msgs msgs.length 0).bind A = (smHybF C G D msgs 0 msgs.length).bind A := by
  simp only [smHybP, smHybF, SPComp.bind_assoc, SPComp.pure_bind, sample_bind_unique,
    List.ofFn_zero, rootRun, List.append_nil, ctsOf, List.nil_append, List.drop_zero]
  bind_swap_nf

/-! ## The FS-AEAD phase -/

omit [Fintype Key] [Nonempty Key] [Fintype RK] [Nonempty RK] [Fintype Sa] [Nonempty Sa]
  [SampleableType Ct] in
/-- Uniform ciphertexts of `t + 1` epochs are those of epoch `t` and those of the first `t`
epochs. -/
def idealCtsSnoc (msgs : List (List (W × W))) (t : ℕ) :
    (Fin (msgs.getD t []).length → Ct) × IdealCts Ct msgs t ≃ IdealCts Ct msgs (t + 1) :=
  Fin.snocEquiv fun j : Fin (t + 1) => Fin (epochLen msgs j) → Ct

omit [Fintype Key] [Nonempty Key] [Fintype RK] [Nonempty RK] [Fintype Sa] [Nonempty Sa]
  [SampleableType W] [SampleableType Ct] in
/-- The ciphertext lists of uniform ciphertexts of `t + 1` epochs, split at the last epoch. -/
theorem ctsOf_idealCtsSnoc (msgs : List (List (W × W))) (t : ℕ)
    (a : Fin (msgs.getD t []).length → Ct) (v : IdealCts Ct msgs t) :
    ctsOf (idealCtsSnoc msgs t (a, v)) = ctsOf v ++ [List.ofFn a] := by
  have h : idealCtsSnoc msgs t (a, v) =
      Fin.snoc (α := fun j : Fin (t + 1) => Fin (epochLen msgs j) → Ct) v a := rfl
  rw [h, ctsOf, List.ofFn_succ_last]
  simp only [ctsOf, Fin.snoc, Fin.val_castSucc, Fin.is_lt, dite_eq_left, Fin.val_last, lt_irrefl,
    dite_eq_right, not_false_eq_true, cast_eq, Fin.castLT_castSucc]
  rfl

omit [Fintype Key] [Nonempty Key] in
/-- FS-AEAD hybrid `(t, r + 1)` is the real FS-AEAD game of epoch `t` of `smAEADRed`. -/
theorem smHybF_bind_eq_real (C : CKADef Sc Msg Key) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) {t : ℕ} (ht : t < msgs.length) (r : ℕ)
    (A : SMView Msg Ct → SPComp Bool) :
    (smHybF C G D msgs t (r + 1)).bind A =
      (fsaead_real G D (msgs.getD t [])).bind (smAEADRed C G D msgs t r A) := by
  have hd : msgs.drop t = msgs.getD t [] :: msgs.drop (t + 1) := by
    rw [List.drop_eq_getElem_cons ht]; simp [List.getD_eq_getElem?_getD, ht]
  simp only [smHybF, fsaead_real, smAEADRed, smPubRedOf, smAEADView, SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind]
  simp only [← SPComp.sample_bind_equiv (Fin.consEquiv fun _ => Sa)]
  have he : ∀ (a : Sa) (v : Fin r → Sa), (Fin.consEquiv fun _ => Sa) (a, v) =
      Fin.cons (α := fun _ => Sa) a v := fun _ _ => rfl
  simp only [SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind, he, ofFn_cons, hd,
    smCts, List.zipWith_cons_cons, encEpoch]
  symm; bind_swap_nf

omit [Fintype Key] [Nonempty Key] in
/-- FS-AEAD hybrid `(t + 1, r)` is the ideal FS-AEAD game of epoch `t` of `smAEADRed`. -/
theorem smHybF_succ_bind_eq_ideal (C : CKADef Sc Msg Key) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (A : SMView Msg Ct → SPComp Bool) :
    (smHybF C G D msgs (t + 1) r).bind A =
      (fsaead_ideal (St := Sa) (msgs.getD t [])).bind (smAEADRed C G D msgs t r A) := by
  simp only [smHybF, fsaead_ideal, smAEADRed, smPubRedOf, smAEADView, SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind]
  simp only [← SPComp.sample_bind_equiv (idealCtsSnoc (Ct := Ct) msgs t)]
  simp only [ctsOf_idealCtsSnoc, SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind,
    List.append_assoc, List.singleton_append]
  symm; bind_swap_nf

omit [Fintype Key] [Nonempty Key] in
/-- FS-AEAD hybrid `(n, 0)` is the ideal game. -/
theorem smHybF_self (C : CKADef Sc Msg Key) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) :
    smHybF C G D msgs msgs.length 0 = sm_ideal C msgs := by
  simp only [smHybF, sm_ideal, sample_bind_unique, List.ofFn_zero, List.drop_length, smCts,
    List.zipWith_nil_left, List.append_nil]
  symm; bind_swap_nf

/-! ## The composition theorem -/

/-- **Confidentiality of the double ratchet.** For every adversary `A` against the
secure-messaging game over the epochs with messages `msgs`, the advantage is at most the sum
over the epochs `t` of the CKA advantage of `smCKARed` at the challenge epoch `t`, the PRG
advantage of the root KDF `R` at `smRootRed`, and the FS-AEAD advantage of the messages of
epoch `t` at `smAEADRed` (Alwen, Coretti and Dodis, Theorem 6, confidentiality part). -/
theorem sm_advantage_le (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W)))
    (A : SMView Msg Ct → SPComp Bool) :
    SM_Advantage C R G D msgs A ≤
      ∑ t ∈ Finset.range msgs.length,
          CKA_Advantage C t (msgs.length - (t + 1)) (smCKARed R G D msgs t A) +
        ∑ t ∈ Finset.range msgs.length,
          PRG_Advantage R (smRootRed C R G D msgs t (msgs.length - (t + 1)) A) +
        ∑ t ∈ Finset.range msgs.length,
          FSAEAD_Advantage G D (msgs.getD t [])
            (smAEADRed C G D msgs t (msgs.length - (t + 1)) A) := by
  have hK : AdvantageA (smHybK C R G D msgs 0) (smHybK C R G D msgs msgs.length) A ≤
      ∑ t ∈ Finset.range msgs.length,
        CKA_Advantage C t (msgs.length - (t + 1)) (smCKARed R G D msgs t A) := by
    refine (HybridArgument.advantage_hybrid_dep (smHybK C R G D msgs) A msgs.length).trans
      (Finset.sum_le_sum fun t ht => le_of_eq ?_)
    have ht' := Finset.mem_range.mp ht
    unfold CKA_Advantage AdvantageA
    rw [smHybK_bind_eq_real C R G D msgs t (msgs.length - (t + 1)) (by omega),
      smHybK_succ_bind_eq_ideal C R G D msgs t (msgs.length - (t + 1)) (by omega)]
  have hP : AdvantageA (smHybP C R G D msgs 0 msgs.length)
      (smHybP C R G D msgs msgs.length (msgs.length - msgs.length)) A ≤
      ∑ t ∈ Finset.range msgs.length,
        PRG_Advantage R (smRootRed C R G D msgs t (msgs.length - (t + 1)) A) := by
    refine (HybridArgument.advantage_hybrid_dep
      (fun i => smHybP C R G D msgs i (msgs.length - i)) A msgs.length).trans
      (Finset.sum_le_sum fun t ht => le_of_eq ?_)
    have hr : msgs.length - t = msgs.length - (t + 1) + 1 := by
      have := Finset.mem_range.mp ht; omega
    unfold PRG_Advantage AdvantageA
    rw [hr, smHybP_bind_eq_real, smHybP_succ_bind_eq_ideal]
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
  have e2 : (smHybP C R G D msgs msgs.length (msgs.length - msgs.length)).bind A =
      (smHybF C G D msgs 0 msgs.length).bind A := by
    rw [Nat.sub_self]; exact smHybP_self_bind C R G D msgs A
  have e3 : smHybF C G D msgs msgs.length (msgs.length - msgs.length) = sm_ideal C msgs := by
    rw [Nat.sub_self]; exact smHybF_self C G D msgs
  unfold AdvantageA at hK hP hF
  rw [e3] at hF
  unfold SM_Advantage AdvantageA
  rw [← smHybK_zero]
  refine (advantage_triangle _ ((smHybK C R G D msgs msgs.length).bind A) _).trans ?_
  rw [add_assoc]
  refine add_le_add hK ?_
  rw [smHybK_self_bind]
  exact (advantage_triangle _ _ _).trans (add_le_add hP (e2 ▸ hF))

omit [Fintype Key] [Nonempty Key] in
/-- **Confidentiality of the double ratchet with the Diffie–Hellman CKA.** With the CKA
`dhCKA` over the cyclic group `G`, the CKA terms of `sm_advantage_le` are the DDH advantages
of `ckaDDHRed` at the reductions `smCKARed`. -/
theorem sm_dh_advantage_le (G : Type) [CG : CyclicGroup G]
    (R : PRGDef (RK × G) (RK × Sa)) (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) (A : SMView G Ct → SPComp Bool) :
    SM_Advantage (dhCKA G) R F D msgs A ≤
      ∑ t ∈ Finset.range msgs.length,
          DDH_Advantage G (ckaDDHRed t (msgs.length - (t + 1)) (smCKARed R F D msgs t A)) +
        ∑ t ∈ Finset.range msgs.length,
          PRG_Advantage R (smRootRed (dhCKA G) R F D msgs t (msgs.length - (t + 1)) A) +
        ∑ t ∈ Finset.range msgs.length,
          FSAEAD_Advantage F D (msgs.getD t [])
            (smAEADRed (dhCKA G) F D msgs t (msgs.length - (t + 1)) A) := by
  have h := sm_advantage_le (dhCKA G) R F D msgs A
  simp only [cka_advantage_eq_ddh] at h
  exact h

/-! ## The costed reductions -/

derive_reduction smSampleRedOf (adv := A)

derive_reduction smPubRedOf (adv := A)

/-- **Time of the sampling distinguisher.** With the costed adversary `A` of time at most `T`
and call cost at most `a`, and the view function of cost at most `tv`, the costed distinguisher
has time at most `T + a + tv + 3`: one sample, one view and one adversary call. -/
theorem smSampleRedOf.tree.timeBound_timed {X Y V : Type} [Fintype X] [Nonempty X]
    (view : X → Y → V) (viewCost : X → Y → ℕ) (A : V → SPTree.Timed Bool) (ACost : V → ℕ)
    {T a tv : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hv : ∀ x y, viewCost x y ≤ tv) (y : Y) :
    SPTree.Timed.stepTime (smSampleRedOf.tree.timed view viewCost A ACost y) ≤
      T + a + tv + 3 := by
  simp only [SPTree.Timed.stepTime, smSampleRedOf.tree.timed, SPTree.Timed.time_sample]
  have hs : (Finset.univ.sup fun b : X =>
      1 + (ACost (view b y) + (1 + viewCost b y)) + (A (view b y)).time) ≤ T + a + tv + 2 :=
    Finset.sup_le fun b _ => by
      have := hA (view b y); have := hAc (view b y); have := hv b y; omega
  omega

/-- **Time of the distinguisher with a public computation.** With the costed adversary `A` of
time at most `T` and call cost at most `a`, the view function of cost at most `tv`, and the
costed public computation `pubT` of time at most `tp`, the costed distinguisher has time at
most `T + a + tv + tp + 4`. -/
theorem smPubRedOf.tree.timeBound_timed {X Y P L : Type} [Fintype X] [Nonempty X]
    (pub : SPComp P) (view : X → Y → L) (viewCost : X → Y → ℕ) (A : P × L → SPTree.Timed Bool)
    (ACost : P × L → ℕ) {T a tv tp : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hv : ∀ x y, viewCost x y ≤ tv) (pubT : SPTree.Timed P) (hp : pubT.time ≤ tp) (y : Y) :
    SPTree.Timed.stepTime (smPubRedOf.tree.timed pub view viewCost A ACost y pubT) ≤
      T + a + tv + tp + 4 := by
  simp only [SPTree.Timed.stepTime, smPubRedOf.tree.timed, SPTree.Timed.time_sample]
  have hs : (Finset.univ.sup fun b : X =>
      (pubT.bind fun x => (1 + (ACost (x, view b y) + (1 + viewCost b y)), A (x, view b y))).1 +
        (pubT.bind fun x =>
          (1 + (ACost (x, view b y) + (1 + viewCost b y)), A (x, view b y))).2.time) ≤
      tp + (T + a + tv + 2) :=
    Finset.sup_le fun b _ => by
      refine (SPTree.Timed.stepTime_bind_le pubT _ (T + a + tv + 2) fun x => ?_).trans
        (by omega)
      have := hA (x, view b y); have := hAc (x, view b y); have := hv b y
      simp only [SPTree.Timed.stepTime]; omega
  omega

/-- The costed form of `smCKARed`: the costed tree of `smSampleRedOf` at the view `smCKAView`
of cost `viewCost`. -/
noncomputable def smCKARed.timed (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t : ℕ)
    (viewCost : (Fin t → Key) × RK → CKAView Msg Key → ℕ)
    (A : SMView Msg Ct → SPTree.Timed Bool) (ACost : SMView Msg Ct → ℕ) (v : CKAView Msg Key) :
    ℕ × SPTree.Timed Bool :=
  smSampleRedOf.tree.timed (smCKAView R G D msgs t) viewCost A ACost v

omit [Fintype Sa] [Nonempty Sa] [SampleableType Ct] in
/-- The costed form of `smCKARed` erases and compiles to `smCKARed` at the erased
adversary. -/
theorem smCKARed.erase_timed (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t : ℕ)
    (viewCost : (Fin t → Key) × RK → CKAView Msg Key → ℕ)
    (A : SMView Msg Ct → SPTree.Timed Bool) (ACost : SMView Msg Ct → ℕ) (v : CKAView Msg Key) :
    (smCKARed.timed R G D msgs t viewCost A ACost v).2.erase.compile =
      smCKARed R G D msgs t (fun x => (A x).erase.compile) v := by
  rw [smCKARed.timed, smSampleRedOf.tree.erase_timed, smSampleRedOf.compile_tree]
  rfl

omit [Fintype Sa] [Nonempty Sa] [SampleableType Ct] in
/-- **Time of `smCKARed`**, the bound of `smSampleRedOf.tree.timeBound_timed` at the view
`smCKAView` of cost at most `tv`; the view costs the root chain and the encryptions of the
epochs. -/
theorem smCKARed.timeBound_timed (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t : ℕ)
    (viewCost : (Fin t → Key) × RK → CKAView Msg Key → ℕ)
    (A : SMView Msg Ct → SPTree.Timed Bool) (ACost : SMView Msg Ct → ℕ) {T a tv : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (hv : ∀ x v, viewCost x v ≤ tv)
    (v : CKAView Msg Key) :
    SPTree.Timed.stepTime (smCKARed.timed R G D msgs t viewCost A ACost v) ≤ T + a + tv + 3 :=
  smSampleRedOf.tree.timeBound_timed _ viewCost A ACost hA hAc hv v

/-- The costed form of `smRootRed`: the costed tree of `smPubRedOf` at the view `smRootView`
of cost `viewCost`, with the costed CKA run `pubT`. -/
noncomputable def smRootRed.timed (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (viewCost : (Fin t → Sa) × (Fin r → Key) → RK × Sa → ℕ)
    (A : SMView Msg Ct → SPTree.Timed Bool) (ACost : SMView Msg Ct → ℕ)
    (pubT : SPTree.Timed (Msg × List Msg)) (y : RK × Sa) : ℕ × SPTree.Timed Bool :=
  smPubRedOf.tree.timed (ckaPub C msgs.length) (smRootView R G D msgs t r) viewCost A ACost y
    pubT

omit [Fintype RK] [Nonempty RK] [SampleableType Ct] in
/-- The costed form of `smRootRed` with a costed CKA run that compiles to `ckaPub` erases and
compiles to `smRootRed` at the erased adversary. -/
theorem smRootRed.erase_timed (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (viewCost : (Fin t → Sa) × (Fin r → Key) → RK × Sa → ℕ)
    (A : SMView Msg Ct → SPTree.Timed Bool) (ACost : SMView Msg Ct → ℕ)
    (pubT : SPTree.Timed (Msg × List Msg)) (hpub : pubT.erase.compile = ckaPub C msgs.length)
    (y : RK × Sa) :
    (smRootRed.timed C R G D msgs t r viewCost A ACost pubT y).2.erase.compile =
      smRootRed C R G D msgs t r (fun x => (A x).erase.compile) y := by
  rw [smRootRed.timed, smPubRedOf.tree.erase_timed, smPubRedOf.compile_tree _ _ _ _ _ hpub]
  rfl

omit [Fintype RK] [Nonempty RK] [SampleableType Ct] in
/-- **Time of `smRootRed`**, the bound of `smPubRedOf.tree.timeBound_timed` at the view
`smRootView` of cost at most `tv` and the costed CKA run of time at most `tp`. -/
theorem smRootRed.timeBound_timed (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (viewCost : (Fin t → Sa) × (Fin r → Key) → RK × Sa → ℕ)
    (A : SMView Msg Ct → SPTree.Timed Bool) (ACost : SMView Msg Ct → ℕ)
    (pubT : SPTree.Timed (Msg × List Msg)) {T a tv tp : ℕ} (hA : ∀ x, (A x).time ≤ T)
    (hAc : ∀ x, ACost x ≤ a) (hv : ∀ x y, viewCost x y ≤ tv) (hp : pubT.time ≤ tp)
    (y : RK × Sa) :
    SPTree.Timed.stepTime (smRootRed.timed C R G D msgs t r viewCost A ACost pubT y) ≤
      T + a + tv + tp + 4 :=
  smPubRedOf.tree.timeBound_timed _ _ viewCost A ACost hA hAc hv pubT hp y

/-- The costed form of `smAEADRed`: the costed tree of `smPubRedOf` at the view `smAEADView`
of cost `viewCost`, with the costed CKA run `pubT`. -/
noncomputable def smAEADRed.timed (C : CKADef Sc Msg Key) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (viewCost : IdealCts Ct msgs t × (Fin r → Sa) → List Ct × Sa → ℕ)
    (A : SMView Msg Ct → SPTree.Timed Bool) (ACost : SMView Msg Ct → ℕ)
    (pubT : SPTree.Timed (Msg × List Msg)) (y : List Ct × Sa) : ℕ × SPTree.Timed Bool :=
  smPubRedOf.tree.timed (ckaPub C msgs.length) (smAEADView G D msgs t r) viewCost A ACost y
    pubT

omit [Fintype Key] [Nonempty Key] in
/-- The costed form of `smAEADRed` with a costed CKA run that compiles to `ckaPub` erases and
compiles to `smAEADRed` at the erased adversary. -/
theorem smAEADRed.erase_timed (C : CKADef Sc Msg Key) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (viewCost : IdealCts Ct msgs t × (Fin r → Sa) → List Ct × Sa → ℕ)
    (A : SMView Msg Ct → SPTree.Timed Bool) (ACost : SMView Msg Ct → ℕ)
    (pubT : SPTree.Timed (Msg × List Msg)) (hpub : pubT.erase.compile = ckaPub C msgs.length)
    (y : List Ct × Sa) :
    (smAEADRed.timed C G D msgs t r viewCost A ACost pubT y).2.erase.compile =
      smAEADRed C G D msgs t r (fun x => (A x).erase.compile) y := by
  rw [smAEADRed.timed, smPubRedOf.tree.erase_timed, smPubRedOf.compile_tree _ _ _ _ _ hpub]
  rfl

omit [Fintype Key] [Nonempty Key] in
/-- **Time of `smAEADRed`**, the bound of `smPubRedOf.tree.timeBound_timed` at the view
`smAEADView` of cost at most `tv` and the costed CKA run of time at most `tp`. -/
theorem smAEADRed.timeBound_timed (C : CKADef Sc Msg Key) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (t r : ℕ)
    (viewCost : IdealCts Ct msgs t × (Fin r → Sa) → List Ct × Sa → ℕ)
    (A : SMView Msg Ct → SPTree.Timed Bool) (ACost : SMView Msg Ct → ℕ)
    (pubT : SPTree.Timed (Msg × List Msg)) {T a tv tp : ℕ} (hA : ∀ x, (A x).time ≤ T)
    (hAc : ∀ x, ACost x ≤ a) (hv : ∀ x y, viewCost x y ≤ tv) (hp : pubT.time ≤ tp)
    (y : List Ct × Sa) :
    SPTree.Timed.stepTime (smAEADRed.timed C G D msgs t r viewCost A ACost pubT y) ≤
      T + a + tv + tp + 4 :=
  smPubRedOf.tree.timeBound_timed _ _ viewCost A ACost hA hAc hv pubT hp y

end CatCrypt.Crypto.Messaging
