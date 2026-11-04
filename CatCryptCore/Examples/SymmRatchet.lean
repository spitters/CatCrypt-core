/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Package
public import CatCryptCore.Invariant
public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Relational.Rules
public import CatCryptCore.Relational.ForLoop
public import CatCryptCore.Tactics.Basic
public import CatCryptCore.Prob.XorBij
public import CatCryptCore.Tactics.Sim
public import CatCryptCore.Tactics.AutoMetrics
public import CatCryptCore.Crypto.Messaging.FSAEAD

/-!
# Symmetric Ratchet Security

This file formalizes Claim 5.10 of Rosulek, *The Joy of Cryptography* (p. 111): the
forward secrecy of the symmetric ratchet.

## Overview

A symmetric ratchet evolves a chain key with a PRG `G : W → W × W`: from the chain key `s_i`
it computes `(t_i, s_{i+1}) = G(s_i)`, encrypts the message `m_i` under the message key `t_i`
and keeps `s_{i+1}`. Forward secrecy asks that the ciphertexts of the messages, together with
the chain key reached after them, be indistinguishable from uniform ciphertexts and a uniform
chain key.

## Games

* `attack_real G E msgs` — a uniform initial chain key, the ciphertexts of `msgs` and the
  final chain key
* `attack_ideal msgs` — uniform ciphertexts and a uniform chain key
* `ctxt_real E m`, `ctxt_ideal m`, `CPA_Advantage` — one encryption of `m` under a uniform key
  against a uniform ciphertext
* `PRG_Stretch_Advantage` — the forward-secure PRG game of core `Messaging.FSPRG` at the
  generator `G.core`

The ratchet game is the forward-secure AEAD game of core `Messaging.FSAEAD` at the PRG
`G.core`, the scheme `E.aead` and the messages `ratchetMsgs msgs` (`attack_real_eq`,
`attack_ideal_eq`, `Ratchet_Advantage_eq_fsaead`).

## Main results

* `forward_secrecy_bound` — for every adversary `A`, the ratchet advantage is at most the sum
  over the steps of the PRG advantages of the reductions `Messaging.fsprgRed` plus the sum over
  the message positions of the CPA advantages of the reductions `Messaging.fsaeadRed`, which
  embed the challenge ciphertext at that position
* `forward_secrecy_wxor` — at the one-time pad `wxorEnc` the CPA terms vanish
* `forward_secrecy_wxor_stretch` — at the one-time pad, the ratchet advantage is at most the
  forward-secure PRG advantage of the reduction that encrypts the messages under its keys;
  `PRG_Stretch_Advantage_le` bounds that advantage by one-step PRG advantages

## References

* [Rosulek, The Joy of Cryptography, Claim 5.10]
* [Perrin & Marlinspike, The Double Ratchet Algorithm]
* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4
* SSProve Rocq: theories/Crypt/examples/SymmRatchet.v
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.SymmRatchet

open CatCrypt.Core
open CatCrypt.Package
open CatCrypt.Prob
open CatCrypt.Relational
open CatCrypt.Invariant
open CatCrypt.Crypto
open CatCrypt.Prob.XorBij
open CatCrypt.Tactics

/-! ## Type Definitions -/

/-- The word type of the Boolean instances `xorPRG` and `xorEnc`; the generic definitions are
    parameterized over `{W : Type} [CryptoWord W]`. -/
abbrev Word := Bool

/-! ## PRG and Encryption Primitives

The ratchet construction is parameterized by:
- A PRG: W → W × W (chain key → (message key, new chain key))
- An encryption function: W → W → W (key → message → ciphertext)
-/

/-- A PRG definition for the ratchet: stretches one word into two -/
structure PRGDef (W : Type) where
  /-- The PRG stretch function: seed → (output, new seed) -/
  stretch : W → W × W

/-- An encryption function definition -/
structure EncDef (W : Type) where
  /-- The encryption function: key → message → ciphertext -/
  enc : W → W → W

/-! ## Simple Implementations for Demonstration -/

/-- XOR-based PRG: PRG(s) = (s, ¬s)
    Note: This is NOT cryptographically secure but demonstrates the structure. -/
def xorPRG : PRGDef Bool where
  stretch := fun s => (s, !s)

/-- XOR-based encryption: Enc(k, m) = k ⊕ m
    This is perfectly secure for a single use (OTP). -/
def xorEnc : EncDef Bool where
  enc := fun k m => xor k m

variable {W : Type} [CryptoWord W]

/-- Generic XOR-based encryption using CryptoWord.wxor.
    This is the generic version of `xorEnc`, which is the Bool specialization. -/
def wxorEnc : EncDef W where
  enc k m := CryptoWord.wxor k m

/-! ## Loop Construction

The ratchet processes a list of messages iteratively.
We define a monadic loop combinator for this purpose.
-/

/-- Loop over a list, threading state and accumulating results.

    This is like `mapM` but threads an accumulator through each iteration:
    - `s`: input list
    - `a`: initial state
    - `f`: function that takes (element, state) and returns (result, new state)

    Returns: (accumulated results, final state) -/
noncomputable def mapLoop {T U A : Type} (s : List T) (a : A) (f : T → A → SPComp (U × A)) :
    SPComp (List U × A) :=
  match s with
  | [] => SPComp.pure ([], a)
  | t :: s' => do
    let ⟨u, a'⟩ ← f t a
    let ⟨us, a''⟩ ← mapLoop s' a' f
    SPComp.pure (u :: us, a'')

/-- Generalized bridge between `List.foldlM` (accumulating outputs by append)
    and `mapLoop` (collecting outputs by cons): an arbitrary prefix `acc`
    commutes with the loop. Auxiliary induction for `mapLoop_eq_foldlM`. -/
lemma foldlM_append_eq_mapLoop {T U A : Type} (s : List T)
    (f : T → A → SPComp (U × A)) (acc : List U) (a : A) :
    s.foldlM (fun (p : List U × A) t =>
        (f t p.2).bind fun ua => SPComp.pure (p.1 ++ [ua.1], ua.2)) (acc, a) =
    (mapLoop s a f).bind (fun p => SPComp.pure (acc ++ p.1, p.2)) := by
  induction s generalizing acc a with
  | nil =>
    simp only [List.foldlM_nil, mapLoop, SPComp.monad_pure_eq, SPComp.pure_bind,
      List.append_nil]
  | cons t s ih =>
    simp only [List.foldlM_cons, mapLoop, SPComp.monad_bind_eq, SPComp.bind_assoc,
      SPComp.pure_bind]
    congr 1
    simp_all

/-- `mapLoop` is a `List.foldlM` whose accumulator pairs the collected outputs
    with the threaded state. This bridges `mapLoop` into the loop-congruence
    rules `rHoare_foldlM`/`rHoare_foldlM_same` of `CatCrypt.Relational.ForLoop`. -/
lemma mapLoop_eq_foldlM {T U A : Type} (s : List T) (a : A)
    (f : T → A → SPComp (U × A)) :
    mapLoop s a f =
    s.foldlM (fun (p : List U × A) t =>
        (f t p.2).bind fun ua => SPComp.pure (p.1 ++ [ua.1], ua.2)) ([], a) := by
  rw [foldlM_append_eq_mapLoop]
  simp only [List.nil_append, Prod.mk.eta, SPComp.bind_pure]

/-- `mapLoop` is heap-independent when every step is. -/
theorem mapLoop_isPure {T U A : Type} (s : List T) (a : A) (f : T → A → SPComp (U × A))
    (hf : ∀ t a', SPComp.IsPure (f t a')) : SPComp.IsPure (mapLoop s a f) := by
  induction s generalizing a with
  | nil => exact SPComp.pure_isPure _
  | cons t ts ih =>
    simp only [mapLoop, SPComp.monad_bind_eq]
    apply SPComp.bind_isPure (hf t a)
    intro ⟨u, a'⟩
    apply SPComp.bind_isPure (ih a')
    intro ⟨us, a''⟩
    exact SPComp.pure_isPure _

/-! ## Embedding into the core games

The ratchet PRG is a core PRG with seeds in `W` and outputs in `W × W`; the encryption is a
core AEAD scheme that ignores the associated data and whose decryption rejects every
ciphertext (the confidentiality games use only encryption); a message `m` is the pair `(m, m)`
of a plaintext and associated data. -/

/-- The ratchet PRG as a core PRG. -/
def PRGDef.core (G : PRGDef W) : Assumptions.PRGDef W (W × W) := ⟨G.stretch⟩

/-- The encryption as a core AEAD scheme that ignores the associated data. -/
def EncDef.aead (E : EncDef W) : Assumptions.AEADDef W W :=
  ⟨fun k pt _ => E.enc k pt, fun _ _ _ => none⟩

/-- The messages as pairs of a plaintext and associated data, the associated data being the
plaintext. -/
def ratchetMsgs (msgs : List W) : List (W × W) := msgs.map fun m => (m, m)

/-- The core encryption of the messages `ratchetMsgs msgs` under `keys` is the encryption of
`msgs` position by position. -/
theorem encAll_ratchetMsgs (E : EncDef W) (keys msgs : List W) :
    Messaging.encAll E.aead keys (ratchetMsgs msgs) = List.zipWith E.enc keys msgs := by
  simp only [Messaging.encAll, ratchetMsgs, EncDef.aead, List.zipWith_map_right]

/-! ## CPA Encryption Security Games

One encryption of `m` under a uniform key against a uniform ciphertext. -/

/-- Real CPA game: sample a key, return Enc(k, m) -/
noncomputable def ctxt_real (E : EncDef W) (m : W) : SPComp W := do
  let k ← SPComp.sample W
  SPComp.pure (E.enc k m)

/-- Ideal CPA game: return a random ciphertext -/
noncomputable def ctxt_ideal (_m : W) : SPComp W :=
  SPComp.sample W

/-- CPA advantage -/
noncomputable def CPA_Advantage (E : EncDef W) (m : W) (A : W → SPComp Bool) : ENNReal :=
  AdvantageA (ctxt_real E m) (ctxt_ideal m) A

/-- The core AEAD advantage of `E.aead` at the plaintext `m` is the CPA advantage at `m`. -/
theorem CPA_Advantage_eq_aead (E : EncDef W) (m ad : W) (A : W → SPComp Bool) :
    Assumptions.AEAD_Advantage E.aead m ad A = CPA_Advantage E m A := by
  simp only [Assumptions.AEAD_Advantage, CPA_Advantage, AdvantageA,
    Assumptions.AEAD_Game_Real, Assumptions.AEAD_Game_Ideal, ctxt_real, ctxt_ideal,
    EncDef.aead, SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-! ## Forward-secure PRG game

The `k` message keys and the chain key reached after them, against `k` uniform keys and a
uniform chain key: the core forward-secure PRG game at `G.core`. -/

/-- Forward-secure PRG advantage of the ratchet PRG over `k` steps. -/
noncomputable def PRG_Stretch_Advantage (G : PRGDef W) (k : ℕ)
    (A : List W × W → SPComp Bool) : ENNReal :=
  Messaging.FSPRG_Advantage G.core k A

/-- The forward-secure PRG advantage over `k` steps is at most the sum of the one-step PRG
advantages of the reductions `Messaging.fsprgRed G.core k i A`. -/
theorem PRG_Stretch_Advantage_le (G : PRGDef W) (k : ℕ) (A : List W × W → SPComp Bool) :
    PRG_Stretch_Advantage G k A ≤
      ∑ i ∈ Finset.range k,
        Assumptions.PRG_Advantage G.core (Messaging.fsprgRed G.core k i A) :=
  Messaging.fsprg_advantage_le _ _ _

/-! ## Ratchet Attack Games -/

/-- Real ratchet attack game (ATTACK true):
    - Sample initial seed s₀
    - For each message m_i: (t_i, s_{i+1}) = PRG(s_i), c_i = Enc(t_i, m_i)
    - Return ciphertexts and final state -/
noncomputable def attack_real (G : PRGDef W) (E : EncDef W)
    (msgs : List W) : SPComp (List W × W) := do
  let s₀ ← SPComp.sample W
  mapLoop msgs s₀ (fun mi si =>
    let ⟨ti, s'⟩ := G.stretch si
    SPComp.pure (E.enc ti mi, s'))

/-- Ideal ratchet attack game (ATTACK false):
    - Sample random ciphertexts for each message
    - Sample random final state
    - Return ciphertexts and final state -/
noncomputable def attack_ideal (msgs : List W) : SPComp (List W × W) := do
  let ciphertexts ← mapLoop msgs () (fun _ _ => do
    let ci ← SPComp.sample W
    SPComp.pure (ci, ()))
  let sn ← SPComp.sample W
  SPComp.pure (ciphertexts.1, sn)

/-- Ratchet advantage -/
noncomputable def Ratchet_Advantage (G : PRGDef W) (E : EncDef W) (msgs : List W)
    (A : List W × W → SPComp Bool) : ENNReal :=
  AdvantageA (attack_real G E msgs) (attack_ideal msgs) A

/-- Intermediate game: the messages encrypted under uniform keys, and a uniform chain key. -/
noncomputable def attack_hyb (E : EncDef W) (msgs : List W) : SPComp (List W × W) := do
  let ciphertexts ← mapLoop msgs () (fun mi _ => do
    let ti ← SPComp.sample W
    SPComp.pure (E.enc ti mi, ()))
  let sn ← SPComp.sample W
  SPComp.pure (ciphertexts.1, sn)

/-! ## The ratchet games are the core FS-AEAD games -/

/-- The ratchet loop with deterministic steps is the encryption of the messages under the
outputs of `fsprgRun`. -/
theorem mapLoop_enc_eq (G : PRGDef W) (E : EncDef W) (msgs : List W) (s : W) :
    mapLoop msgs s (fun mi si =>
      let ⟨ti, s'⟩ := G.stretch si
      SPComp.pure (E.enc ti mi, s')) =
    SPComp.pure
      (Messaging.encAll E.aead (Messaging.fsprgRun G.core msgs.length s).1 (ratchetMsgs msgs),
        (Messaging.fsprgRun G.core msgs.length s).2) := by
  induction msgs generalizing s with
  | nil => rfl
  | cons m ms ih =>
    simp only [mapLoop, SPComp.monad_bind_eq, SPComp.pure_bind, ih]
    rfl

/-- The loop of uniform ciphertexts is a uniform vector of ciphertexts. -/
theorem mapLoop_sample_eq (msgs : List W) :
    mapLoop msgs () (fun _ _ =>
      SPComp.bind (SPComp.sample W) fun ci => SPComp.pure (ci, ())) =
    SPComp.bind (SPComp.sample (Fin msgs.length → W)) fun v =>
      SPComp.pure (List.ofFn v, ()) := by
  induction msgs with
  | nil => simp only [mapLoop, List.length_nil, Messaging.sample_bind_unique, List.ofFn_zero]
  | cons m ms ih =>
    change _ = SPComp.bind (SPComp.sample (Fin (ms.length + 1) → W))
      fun v => SPComp.pure (List.ofFn v, ())
    rw [← SPComp.sample_bind_equiv (Fin.consEquiv fun _ => W)]
    have he : ∀ (a : W) (v : Fin ms.length → W), (Fin.consEquiv fun _ => W) (a, v) =
        Fin.cons (α := fun _ => W) a v := fun _ _ => rfl
    simp only [mapLoop, SPComp.monad_bind_eq, ih, SPComp.sample_prod_eq, SPComp.bind_assoc,
      SPComp.pure_bind, he, Messaging.ofFn_cons]

/-- The real ratchet game is the core FS-AEAD real game. -/
theorem attack_real_eq (G : PRGDef W) (E : EncDef W) (msgs : List W) :
    attack_real G E msgs = Messaging.fsaead_real G.core E.aead (ratchetMsgs msgs) := by
  simp only [attack_real, Messaging.fsaead_real, SPComp.monad_bind_eq, mapLoop_enc_eq]
  simp only [ratchetMsgs, List.length_map]

/-- The ideal ratchet game is the core FS-AEAD ideal game. -/
theorem attack_ideal_eq (msgs : List W) :
    attack_ideal msgs = Messaging.fsaead_ideal (St := W) (C := W) (ratchetMsgs msgs) := by
  simp only [attack_ideal, Messaging.fsaead_ideal, SPComp.monad_bind_eq]
  rw [mapLoop_sample_eq]
  have h : msgs.length = (ratchetMsgs msgs).length := (List.length_map _).symm
  rw [← SPComp.sample_bind_equiv ((finCongr h).arrowCongr (Equiv.refl W))]
  simp only [SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext a
  have hv : List.ofFn (((finCongr h).arrowCongr (Equiv.refl W)) a) = List.ofFn a := by
    rw [List.ofFn_congr h.symm]
    rfl
  rw [hv]

/-- The ratchet advantage is the core FS-AEAD advantage of `G.core`, `E.aead` and
`ratchetMsgs msgs`. -/
theorem Ratchet_Advantage_eq_fsaead (G : PRGDef W) (E : EncDef W) (msgs : List W)
    (A : List W × W → SPComp Bool) :
    Ratchet_Advantage G E msgs A =
      Messaging.FSAEAD_Advantage G.core E.aead (ratchetMsgs msgs) A := by
  unfold Ratchet_Advantage Messaging.FSAEAD_Advantage
  rw [attack_real_eq, attack_ideal_eq]

/-! ## Forward Secrecy

This corresponds to Claim 5.10 in "The Joy of Cryptography" and
Lemma forward_secrecy_based_on_prg in the Rocq SymmRatchet.v. -/

/-- **Forward secrecy of the symmetric ratchet.** For every adversary `A`, the ratchet
advantage over the messages `msgs` of length `n` is at most the sum over the steps `i < n` of
the PRG advantages of the reductions `Messaging.fsprgRed G.core n i` (at the distinguisher
`Messaging.fsaeadPost`, which encrypts the messages under the received keys) plus the sum over
the positions `j < n` of the CPA advantages, at the message of position `j`, of the reductions
`Messaging.fsaeadRed`, which place the challenge ciphertext at position `j`. An instance of
core `Messaging.fsaead_advantage_le`. -/
theorem forward_secrecy_bound (G : PRGDef W) (E : EncDef W) (msgs : List W)
    (A : List W × W → SPComp Bool) :
    Ratchet_Advantage G E msgs A ≤
      ∑ i ∈ Finset.range msgs.length, Assumptions.PRG_Advantage G.core
          (Messaging.fsprgRed G.core msgs.length i
            (Messaging.fsaeadPost E.aead (ratchetMsgs msgs) A)) +
        ∑ j ∈ Finset.range msgs.length, CPA_Advantage E (msgs.getD j default)
          (Messaging.fsaeadRed E.aead (ratchetMsgs msgs) j (msgs.length - (j + 1)) A) := by
  have h := Messaging.fsaead_advantage_le G.core E.aead (ratchetMsgs msgs) A
  have hlen : (ratchetMsgs msgs).length = msgs.length := List.length_map _
  have hget : ∀ j, (ratchetMsgs msgs).getD j default =
      (msgs.getD j default, msgs.getD j default) := fun j => by
    simp only [ratchetMsgs, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases msgs[j]? <;> rfl
  simp only [hlen, hget, CPA_Advantage_eq_aead] at h
  rw [Ratchet_Advantage_eq_fsaead]
  exact h

/-! ## Security Lemmas for the One-Time Pad -/

/-- Generic wxor encryption with a random key is perfectly indistinguishable from random.
    This uses the bijection coupling technique via `wxorEquiv`. -/
theorem wxorEnc_cpa_perfect (m : W) :
    rHoare eqPre (ctxt_real wxorEnc m) (ctxt_ideal m) eqPost := by
  unfold ctxt_real ctxt_ideal wxorEnc
  ssprove_try_bij (wxorEquiv m)
  ssprove_sim_auto

/-- Perfect CPA security for generic wxor encryption implies zero advantage. -/
theorem wxorEnc_zero_cpa_advantage (m : W) :
    ∀ A, CPA_Advantage wxorEnc m A = 0 := by
  intro A
  unfold CPA_Advantage
  exact advantage_zero_of_rHoare _ _ (wxorEnc_cpa_perfect m) A

/-- Bool specialization of wxorEnc CPA security. -/
theorem xorEnc_cpa_perfect (m : Word) :
    rHoare eqPre (ctxt_real xorEnc m) (ctxt_ideal m) eqPost :=
  wxorEnc_cpa_perfect m

/-- Bool specialization of wxorEnc zero CPA advantage. -/
theorem xorEnc_zero_cpa_advantage (m : Word) :
    ∀ A, CPA_Advantage xorEnc m A = 0 :=
  wxorEnc_zero_cpa_advantage m

/-- **Forward secrecy at the one-time pad.** With `wxorEnc` the CPA terms of
`forward_secrecy_bound` vanish: the ratchet advantage is at most the sum of the PRG
advantages of the reductions `Messaging.fsprgRed`. -/
theorem forward_secrecy_wxor (G : PRGDef W) (msgs : List W)
    (A : List W × W → SPComp Bool) :
    Ratchet_Advantage G wxorEnc msgs A ≤
      ∑ i ∈ Finset.range msgs.length, Assumptions.PRG_Advantage G.core
        (Messaging.fsprgRed G.core msgs.length i
          (Messaging.fsaeadPost wxorEnc.aead (ratchetMsgs msgs) A)) := by
  refine (forward_secrecy_bound G wxorEnc msgs A).trans (le_of_eq ?_)
  simp only [wxorEnc_zero_cpa_advantage, Finset.sum_const_zero, add_zero]

/-- Bool specialization of `forward_secrecy_wxor`. -/
theorem forward_secrecy_xor (G : PRGDef Word) (msgs : List Word)
    (A : List Word × Word → SPComp Bool) :
    Ratchet_Advantage G xorEnc msgs A ≤
      ∑ i ∈ Finset.range msgs.length, Assumptions.PRG_Advantage G.core
        (Messaging.fsprgRed G.core msgs.length i
          (Messaging.fsaeadPost xorEnc.aead (ratchetMsgs msgs) A)) :=
  forward_secrecy_wxor G msgs A

/-- For wxor encryption, `attack_hyb` produces the same distribution as `attack_ideal`:
a uniform key XORed with the message is a uniform ciphertext. The proof is by induction on
the message list, with a bijection coupling at each step. -/
theorem attack_hyb_eq_attack_ideal_wxor (msgs : List W) :
    rHoare eqPre (attack_hyb wxorEnc msgs) (attack_ideal msgs) eqPost := by
  induction msgs with
  | nil =>
    intro h₁ h₂ hheq
    simp only [eqPre] at hheq
    subst hheq
    unfold attack_hyb attack_ideal mapLoop
    simp only [SPComp.monad_bind_eq]
    simp only [SPComp.pure_bind]
    apply liftR_mono _ (liftR_refl _)
    simp_all
  | cons m ms ih =>
    intro h₁ h₂ hheq
    simp only [eqPre] at hheq
    subst hheq
    unfold attack_hyb attack_ideal mapLoop
    simp only [SPComp.monad_bind_eq]
    ssprove_distr_simp
    -- Couple the key `a` on the left with the ciphertext `wxor a m` on the right.
    apply liftR_bind (liftR_uniform_bij (wxorEquiv m))
    intro a c hac
    simp only [wxorEquiv_apply] at hac
    have henc_eq : wxorEnc.enc a m = c := by unfold wxorEnc; exact hac
    -- The remaining loops are coupled through the foldlM bridge, one bijection per step.
    have hmapLoop_coupled : ∀ (msgs : List W) (h : Heap),
        liftR (fun p₁ p₂ => p₁.1 = p₂.1 ∧ p₁.2 = p₂.2)
          (mapLoop msgs () (fun mi _ => (SPComp.sample W).bind fun ti =>
            SPComp.pure (wxorEnc.enc ti mi, ())) h)
          (mapLoop msgs () (fun _ _ => (SPComp.sample W).bind fun ci =>
            SPComp.pure (ci, ())) h) := by
      intro msgs h
      rw [mapLoop_eq_foldlM, mapLoop_eq_foldlM]
      refine liftR_mono (fun p₁ p₂ hp => ⟨hp.2, hp.1⟩)
        (rHoare_foldlM_same (I := eqPre) (V := @Eq (List W × Unit)) msgs ?_ rfl h h rfl)
      rintro s₁ s₂ m' _ rfl
      simp only [SPComp.bind_assoc, SPComp.pure_bind]
      exact rHoare_bij_step (wxorEquiv m') fun ti =>
        rHoare_ret fun _ _ hh => ⟨hh, rfl⟩
    apply liftR_bind (hmapLoop_coupled ms h₁)
    intro ⟨cs₁, u₁⟩ ⟨cs₂, u₂⟩ ⟨hcs_eq, hu_eq⟩
    simp only at hcs_eq hu_eq
    apply liftR_bind liftR_uniform_same
    intro sn₁ sn₂ hsn_eq
    apply liftR_pure
    simp_all

/-- Bool specialization of `attack_hyb_eq_attack_ideal_wxor`. -/
theorem attack_hyb_eq_attack_ideal_xor (msgs : List Word) :
    rHoare eqPre (attack_hyb xorEnc msgs) (attack_ideal msgs) eqPost :=
  attack_hyb_eq_attack_ideal_wxor msgs

/-- For wxor encryption, the advantage between `attack_hyb` and `attack_ideal` is 0. -/
theorem attack_hyb_ideal_advantage_zero_wxor (msgs : List W)
    (A : List W × W → SPComp Bool) :
    AdvantageA (attack_hyb wxorEnc msgs) (attack_ideal msgs) A = 0 :=
  advantage_zero_of_rHoare _ _ (attack_hyb_eq_attack_ideal_wxor msgs) A

/-- Bool specialization of `attack_hyb_ideal_advantage_zero_wxor`. -/
theorem attack_hyb_ideal_advantage_zero_xor (msgs : List Word)
    (A : List Word × Word → SPComp Bool) :
    AdvantageA (attack_hyb xorEnc msgs) (attack_ideal msgs) A = 0 :=
  attack_hyb_ideal_advantage_zero_wxor msgs A

/-! ## Factorization through the forward-secure PRG game

`attack_real` and `attack_hyb` are the real and the ideal forward-secure PRG game followed by
the encryption of the messages under the received keys. -/

/-- Encryption post-processing: applies encryption to a list of keys paired with messages.
    This is the "wrapper" that converts PRG outputs to ratchet outputs. -/
noncomputable def encrypt_keys (E : EncDef W) (msgs : List W) (km : List W × W) :
    SPComp (List W × W) :=
  SPComp.pure ((List.zipWith (fun k m => E.enc k m) km.1 msgs), km.2)

/-- `mapLoop` with a step that ignores the list element depends only on the length of the
    list. -/
lemma mapLoop_eq_of_length {T T' U A : Type} (ts : List T) (ts' : List T') (init : A)
    (f : A → SPComp (U × A))
    (hlen : ts.length = ts'.length) :
    mapLoop ts init (fun _ st => f st) = mapLoop ts' init (fun _ st => f st) := by
  -- Bridge to `List.foldlM` and couple the two loops with `rHoare_foldlM`:
  -- the trivial pointwise relation `Forall₂ (fun _ _ => True)` carries exactly
  -- the length information, and the diagonal coupling forces equality.
  rw [mapLoop_eq_foldlM, mapLoop_eq_foldlM]
  funext h
  apply liftR_eq_implies_eq
  refine liftR_mono (fun p₁ p₂ hp => Prod.ext hp.2 hp.1)
    (rHoare_foldlM (R := fun (_ : T) (_ : T') => True) (V := @Eq (List U × A)) (I := eqPre)
      (List.forall₂_of_length_eq_of_get hlen fun _ _ _ => trivial) ?_ rfl h h rfl)
  rintro s₁ s₂ x y - rfl
  exact rHoare_mono_post (rHoare_refl _) fun _ _ _ _ hp => ⟨hp.2, hp.1⟩

/-- Factorization helper for random sampling: mapLoop with sample+encryption at each step
    equals mapLoop with just sample followed by zipWith encryption.

    Used by `attack_hyb_factors`. -/
lemma mapLoop_sample_enc_factors (E : EncDef W) (msgs : List W) (init : Unit) :
    mapLoop msgs init
      (fun mi _ => (SPComp.sample W).bind (fun ti => SPComp.pure (E.enc ti mi, ()))) =
    (mapLoop msgs init (fun _ _ => (SPComp.sample W).bind (fun ti => SPComp.pure (ti, ())))).bind
      (fun km => SPComp.pure (List.zipWith (fun k m => E.enc k m) km.1 msgs, km.2)) := by
  induction msgs generalizing init with
  | nil =>
    simp only [mapLoop, List.zipWith_nil_right, SPComp.pure_bind]
  | cons m ms ih =>
    simp only [mapLoop, SPComp.monad_bind_eq]
    funext h
    simp only [SPComp.bind_def, SPComp.pure_def, SPComp.sample, SDistr.bind_assoc, SDistr.pure_bind]
    have ih_h := congrFun (ih ()) h
    simp only [SPComp.bind_def, SPComp.pure_def] at ih_h
    congr 1
    funext ti
    rw [ih_h]
    simp only [SDistr.bind_assoc]
    congr 1
    funext ⟨⟨ks, _⟩, h'⟩
    simp_all [SDistr.bind, SDistr.pure]

/-- `attack_real` is the real forward-secure PRG game followed by `encrypt_keys`. -/
theorem attack_real_factors (G : PRGDef W) (E : EncDef W) (msgs : List W) :
    attack_real G E msgs =
    (Messaging.fsprg_real G.core msgs.length).bind (encrypt_keys E msgs) := by
  rw [attack_real_eq]
  simp only [Messaging.fsaead_real, Messaging.fsprg_real, encrypt_keys, SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind, encAll_ratchetMsgs]
  simp only [ratchetMsgs, List.length_map]

/-- `attack_hyb` is the ideal forward-secure PRG game followed by `encrypt_keys`. -/
theorem attack_hyb_factors (E : EncDef W) (msgs : List W) :
    attack_hyb E msgs =
    (Messaging.fsprg_ideal (St := W) msgs.length).bind (encrypt_keys E msgs) := by
  unfold attack_hyb
  simp only [SPComp.monad_bind_eq]
  rw [mapLoop_sample_enc_factors, mapLoop_sample_eq]
  simp only [Messaging.fsprg_ideal, encrypt_keys, SPComp.monad_bind_eq, SPComp.bind_assoc,
    SPComp.pure_bind]

/-- PRG reduction step: the advantage between `attack_real` and `attack_hyb` is the
forward-secure PRG advantage of the distinguisher that encrypts the messages under the
received keys and calls `A`. -/
theorem prg_reduction_step (G : PRGDef W) (E : EncDef W) (msgs : List W)
    (A : List W × W → SPComp Bool) :
    AdvantageA (attack_real G E msgs) (attack_hyb E msgs) A =
    PRG_Stretch_Advantage G msgs.length (fun km => (encrypt_keys E msgs km).bind A) := by
  rw [attack_real_factors, attack_hyb_factors, advantage_factorization]
  rfl

/-- **Forward secrecy at the one-time pad, through the forward-secure PRG game.** With
`wxorEnc`, the ratchet advantage is at most the forward-secure PRG advantage of the
distinguisher that encrypts the messages under the received keys; `PRG_Stretch_Advantage_le`
bounds it by one-step PRG advantages. -/
theorem forward_secrecy_wxor_stretch (G : PRGDef W) (msgs : List W)
    (A : List W × W → SPComp Bool) :
    Ratchet_Advantage G wxorEnc msgs A ≤
      PRG_Stretch_Advantage G msgs.length
        (fun km => (encrypt_keys wxorEnc msgs km).bind A) := by
  unfold Ratchet_Advantage
  refine (advantageA_triangle _ (attack_hyb wxorEnc msgs) _ A).trans (le_of_eq ?_)
  rw [prg_reduction_step, attack_hyb_ideal_advantage_zero_wxor, add_zero]

/-- Bool specialization of `forward_secrecy_wxor_stretch`. -/
theorem forward_secrecy_xor_stretch (G : PRGDef Word) (msgs : List Word)
    (A : List Word × Word → SPComp Bool) :
    Ratchet_Advantage G xorEnc msgs A ≤
      PRG_Stretch_Advantage G msgs.length (fun km => (encrypt_keys xorEnc msgs km).bind A) :=
  forward_secrecy_wxor_stretch G msgs A

/-! ### Helper Lemmas for Single-Message CPA Reduction -/

/-- Wrapper function that adds the final state to a ciphertext -/
noncomputable def wrap_single (c : W) : SPComp (List W × W) := do
  let sn ← SPComp.sample W
  SPComp.pure ([c], sn)

/-- The CPA adversary constructed from the ratchet adversary for single message.
    Given a ciphertext c, samples a random final state and runs A. -/
noncomputable def cpa_adv_single (A : List W × W → SPComp Bool) (c : W) : SPComp Bool := do
  let sn ← SPComp.sample W
  A ([c], sn)

/-- For single message, attack_hyb factors through ctxt_real -/
lemma attack_hyb_single (E : EncDef W) (m : W) :
    attack_hyb E [m] = (ctxt_real E m).bind wrap_single := by
  simp [attack_hyb, mapLoop, ctxt_real, wrap_single, SPComp.monad_bind_eq, SPComp.bind_assoc]

/-- For single message, attack_ideal factors through ctxt_ideal -/
lemma attack_ideal_single (m : W) :
    attack_ideal [m] = (ctxt_ideal m).bind wrap_single := by
  unfold wrap_single
  simp [attack_ideal, mapLoop, ctxt_ideal, SPComp.monad_bind_eq, SPComp.bind_assoc]

/-- Wrapping with wrap_single then binding A equals cpa_adv_single -/
lemma wrap_single_bind_eq (A : List W × W → SPComp Bool) (c : W) :
    (wrap_single c).bind A = cpa_adv_single A c := by
  unfold wrap_single cpa_adv_single
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-- CPA reduction for single message: EQUALITY version using correct adversary.
    The advantage exactly equals the CPA advantage with the properly composed adversary. -/
theorem cpa_reduction_single_eq (E : EncDef W) (m : W) (A : List W × W → SPComp Bool) :
    AdvantageA (attack_hyb E [m]) (attack_ideal [m]) A = CPA_Advantage E m (cpa_adv_single A) := by
  rw [attack_hyb_single, attack_ideal_single, advantage_factorization]
  unfold CPA_Advantage
  congr 1
  funext c
  exact wrap_single_bind_eq A c


/-- If A doesn't depend on the final state, the simplified bound holds exactly -/
theorem cpa_reduction_single_state_ind (E : EncDef W) (m : W)
    (A : List W × W → SPComp Bool)
    (hA : ∀ cs s s', A (cs, s) = A (cs, s')) :
    AdvantageA (attack_hyb E [m]) (attack_ideal [m]) A =
    CPA_Advantage E m (fun c => A ([c], default)) := by
  rw [cpa_reduction_single_eq]
  -- Show cpa_adv_single A = (fun c => A ([c], default)) under assumption hA
  have hadv_eq : cpa_adv_single A = fun c => A ([c], default) := by
    funext c
    unfold cpa_adv_single
    simp only [SPComp.monad_bind_eq]
    have heq : (fun sn => A ([c], sn)) = fun _ => A ([c], default) := by
      grind
    rw [heq]
    exact CatCrypt.Relational.dead_sample (α := W) (A ([c], default))
  simp_all

end CatCrypt.Examples.SymmRatchet
