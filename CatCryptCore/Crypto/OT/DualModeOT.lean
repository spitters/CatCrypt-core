/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.UC
import CatCryptCore.Crypto.SDist
import CatCryptCore.Examples.GroupParam

/-!
# Oblivious Transfer with Information-Theoretic Sender-Message Privacy

An oblivious-transfer protocol over an abstract discrete-log group in which the
sender encrypts each of its two messages under a public key and the receiver
recovers only the chosen one. Encryption is ElGamal-style: `dualEnc pk m r =
pk ^ r · m`.

## Scope of the security statement

The UC statement here covers **corrupt-receiver / sender-message privacy only**.
The ideal functionality `dualOT_ideal` *reveals the choice bit*: it hands the
simulator `(choice, chosen-ciphertext)`, so it does not hide which message the
receiver selected. Receiver privacy — hiding the choice bit from a corrupt
sender — is out of scope; see the closing note.

The simulator `dualOT_sim` reconstructs the two ciphertexts the real world leaks
from `(choice, chosen-ciphertext)` by sampling a **uniform group element** for
the unchosen slot. It does not use any CRS trapdoor.

## Why the unchosen ciphertext is uniform (information-theoretic)

For a public key `pk = g ^ s` with `s ≠ 0` — equivalently, any non-identity
element of the prime-order group — the map `r ↦ pk ^ r · m` is a bijection
`Scalar ≃ G`: it composes `r ↦ s · r` (a bijection because `s ≠ 0`), generator
exponentiation `x ↦ g ^ x` (a bijection by `exp_surj`/`exp_inj`), and right
translation `y ↦ y · m` (a bijection). Hence for uniform `r`, `dualEnc pk m r`
is *exactly* uniform on `G`. `dualEnc_uniform` proves this as an equality of
distributions, with **no computational assumption and no DDH reduction**;
`dualOT_uc_secure_zero` threads it into a perfect (`ε = 0`) UC statement whenever
both public keys are non-identity.

## Interface types

* `leak = G × G` — the real world leaks the two ciphertexts.
* `sim_if = Bool × G` — the ideal hands the simulator the choice bit and the
  chosen message's ciphertext; the simulator fakes the other ciphertext.
-/

namespace CatCrypt.Crypto.OT.DualModeOT

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Examples
open scoped ENNReal

set_option autoImplicit false

variable (gp : GroupParam)

/-! ## Public Keys and Encryption -/

/-- Public keys for the two message slots. `mode`, `sk`, and `pk_eq` record the
    trapdoor of a full dual-mode CRS (messy vs. decryption mode); they are not
    used by the sender-message-privacy statement below, which relies only on the
    two public keys being non-identity, and are retained for the future
    receiver-privacy extension (see the closing note). -/
structure DualModeCRS where
  /-- First public key. -/
  pk₀ : gp.G
  /-- Second public key. -/
  pk₁ : gp.G
  /-- Mode selector. -/
  mode : Bool
  /-- Secret key of the decryptable public key. -/
  sk : gp.Scalar
  /-- The selected public key is `g ^ sk`. -/
  pk_eq : (if mode then pk₀ else pk₁) = gp.exp sk

/-- Encrypt a group element `m` under a public key `pk` with randomness `r`:
    `pk ^ r · m`. -/
def dualEnc (pk : gp.G) (m : gp.G) (r : gp.Scalar) : gp.G :=
  gp.groupMul (gp.groupExp pk r) m

/-! ## OT Input -/

/-- OT input: the sender's two messages and the receiver's choice bit. -/
structure OTInput where
  /-- The sender's first message. -/
  m₀ : gp.G
  /-- The sender's second message. -/
  m₁ : gp.G
  /-- The receiver's choice bit. -/
  choice : Bool

/-! ## Protocol -/

/-- Real OT protocol: encrypt both messages under the two public keys. -/
noncomputable def dualOT_real (crs : DualModeCRS gp) :
    OTInput gp → SPComp (Unit ⊕ (gp.G × gp.G)) :=
  fun input =>
    SPComp.bind (SPComp.sample gp.Scalar) fun r₀ =>
    SPComp.bind (SPComp.sample gp.Scalar) fun r₁ =>
    let ct₀ := dualEnc gp crs.pk₀ input.m₀ r₀
    let ct₁ := dualEnc gp crs.pk₁ input.m₁ r₁
    SPComp.pure (.inr (ct₀, ct₁))

/-- Ideal OT: returns only the chosen message; the simulator interface provides the
    choice bit and the chosen message's ciphertext. -/
noncomputable def dualOT_ideal (crs : DualModeCRS gp) :
    OTInput gp → SPComp (Unit ⊕ (Bool × gp.G)) :=
  fun input =>
    SPComp.bind (SPComp.sample gp.Scalar) fun r =>
    let chosen := if input.choice then input.m₁ else input.m₀
    let ct := dualEnc gp (if input.choice then crs.pk₁ else crs.pk₀) chosen r
    SPComp.pure (.inr (input.choice, ct))

/-! ## Simulator -/

/-- OT simulator: from `(choice, ct_chosen)` produce a fake pair of ciphertexts,
    sampling a uniform group element for the unchosen slot. -/
noncomputable def dualOT_sim (_crs : DualModeCRS gp)
    (V : Type) (A : gp.G × gp.G → SPComp V) :
    Bool × gp.G → SPComp V :=
  fun (choice, ct_chosen) =>
    SPComp.bind (SPComp.sample gp.G) fun ct_other =>
    if choice then A (ct_other, ct_chosen) else A (ct_chosen, ct_other)

/-! ## UC Specification -/

/-- UC spec for the OT: honest input is an `OTInput`, the real world leaks the two
    ciphertexts, and the ideal hands the simulator `(choice, ciphertext)`. -/
noncomputable def dualOTSpec (V : Type) : UCSpec :=
  ⟨OTInput gp, Unit, gp.G × gp.G, Bool × gp.G, V⟩

/-! ## Information-Theoretic Ciphertext Uniformity

For a non-identity public key, encryption with uniform randomness is *exactly*
uniform on the group — an equality of distributions, not a computational bound.
The witness is the bijection `Scalar ≃ G` sending `r` to `pk ^ r · m`. -/

/-- In a prime-order group every non-identity element is a generator: any
    `pk ≠ 1` equals `g ^ s` for some `s ≠ 0`. -/
theorem exists_exp_of_ne_identity (pk : gp.G) (h : pk ≠ gp.identity) :
    ∃ s, s ≠ gp.scalarZero ∧ pk = gp.exp s := by
  obtain ⟨s, hs⟩ := gp.exp_surj pk
  refine ⟨s, ?_, hs.symm⟩
  intro h0; apply h; rw [← hs, h0, gp.exp_zero]

/-- The encryption map `r ↦ pk ^ r · m` as a bijection `Scalar ≃ G`, for a
    generator `pk = g ^ s` with `s ≠ 0`. It is the composite of `r ↦ s · r`,
    generator exponentiation, and right translation by `m`, each a bijection. -/
noncomputable def dualEncEquiv (s : gp.Scalar) (m : gp.G) (hs : s ≠ gp.scalarZero) :
    gp.Scalar ≃ gp.G :=
  (⟨fun r => gp.scalarMul s r, fun x => gp.scalarDiv x s,
     fun r => by dsimp only; rw [gp.scalarMul_comm]; exact gp.mul_div_cancel r s hs,
     fun x => by dsimp only; rw [gp.scalarMul_comm]; exact gp.div_mul_cancel x s hs⟩ :
      gp.Scalar ≃ gp.Scalar).trans
  ((Equiv.ofBijective gp.exp ⟨fun a b hab => gp.exp_inj a b hab, gp.exp_surj⟩).trans
   (⟨fun g => gp.groupMul g m, fun g => gp.groupMul g (gp.groupInv m),
     fun g => by dsimp only; rw [gp.groupMul_assoc, gp.groupMul_inv, gp.groupMul_identity],
     fun g => by dsimp only; rw [gp.groupMul_assoc, gp.inv_groupMul, gp.groupMul_identity]⟩ :
      gp.G ≃ gp.G))

@[simp] theorem dualEncEquiv_apply (s : gp.Scalar) (m : gp.G) (hs : s ≠ gp.scalarZero)
    (r : gp.Scalar) :
    dualEncEquiv gp s m hs r = gp.groupMul (gp.exp (gp.scalarMul s r)) m := by
  simp only [dualEncEquiv, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.ofBijective_apply]

/-- **Ciphertext uniformity.** For a non-identity public key `pk`, encrypting `m`
    with uniform randomness is *exactly* the uniform distribution on the group.
    Information-theoretic: no assumption, no reduction. -/
theorem dualEnc_uniform (pk m : gp.G) (h : pk ≠ gp.identity) :
    SPComp.bind (SPComp.sample gp.Scalar) (fun r => SPComp.pure (dualEnc gp pk m r))
      = SPComp.sample gp.G := by
  obtain ⟨s, hs, rfl⟩ := exists_exp_of_ne_identity gp pk h
  have key : (fun r => SPComp.pure (dualEnc gp (gp.exp s) m r))
           = (fun r => SPComp.pure (dualEncEquiv gp s m hs r)) := by
    funext r; simp only [dualEncEquiv_apply, dualEnc, gp.groupExp_exp]
  rw [key, SPComp.sample_bind_equiv (dualEncEquiv gp s m hs) SPComp.pure, SPComp.bind_pure]

/-- The `sdist` form of `dualEnc_uniform`: encryption under a non-identity key is
    at statistical distance `0` from a uniform group element. -/
theorem sdist_dualEnc_uniform (pk m : gp.G) (h : pk ≠ gp.identity) :
    sdist (fun _ : Unit => SPComp.bind (SPComp.sample gp.Scalar)
            (fun r => SPComp.pure (dualEnc gp pk m r)))
          (fun _ : Unit => SPComp.sample gp.G) = 0 := by
  rw [show (fun _ : Unit => SPComp.bind (SPComp.sample gp.Scalar)
        (fun r => SPComp.pure (dualEnc gp pk m r)))
        = (fun _ : Unit => SPComp.sample gp.G) from
      funext (fun _ => dualEnc_uniform gp pk m h)]
  exact sdist_self _

/-! ## Ciphertext Pseudorandomness (parametric form)

`CiphertextPseudorandom ε` is the `sdist` statement that encryption with uniform
randomness is `ε`-close to a uniform group element, for every key. It is an
*information-theoretic hiding* statement, not a DDH reduction: for any
non-identity key it holds at `ε = 0` (`sdist_dualEnc_uniform`). This parametric
predicate lets downstream compositions quantify over an abstract bound; the
honest, discharged instance is `dualOT_uc_secure_zero` below. -/

/-- Encryption of `m` under `pk` with uniform randomness is `sdist`-close to a
    uniform group element, within error `ε`. -/
noncomputable def CiphertextPseudorandom (ε : ℝ≥0∞) : Prop :=
  ∀ (pk : gp.G) (m : gp.G),
    sdist (fun (_ : Unit) => SPComp.bind (SPComp.sample gp.Scalar)
            (fun r => SPComp.pure (dualEnc gp pk m r)))
          (fun (_ : Unit) => SPComp.sample gp.G) ≤ ε

/-! ## Security Reduction -/

/-- The core reduction: given per-key bounds on the statistical distance between a
    real ciphertext and a uniform group element, the real and ideal OT views are
    within that bound. The two branches (`choice = false`/`true`) share the final
    step through the local `final` helper; they differ only in which slot carries
    the unchosen ciphertext. -/
theorem dualOT_reduction (crs : DualModeCRS gp) (V : Type) (ε : ℝ≥0∞)
    (hb0 : ∀ m, sdist (fun _ : Unit => SPComp.bind (SPComp.sample gp.Scalar)
              (fun r => SPComp.pure (dualEnc gp crs.pk₀ m r)))
            (fun _ : Unit => SPComp.sample gp.G) ≤ ε)
    (hb1 : ∀ m, sdist (fun _ : Unit => SPComp.bind (SPComp.sample gp.Scalar)
              (fun r => SPComp.pure (dualEnc gp crs.pk₁ m r)))
            (fun _ : Unit => SPComp.sample gp.G) ≤ ε) :
    UCEmulates ε (dualOTSpec gp V)
      (dualOT_real gp crs) (dualOT_ideal gp crs) := by
  intro A
  use dualOT_sim gp crs V A
  simp only [dualOTSpec] at A
  show sdist
    (fun a => SPComp.bind (dualOT_real gp crs a) (mapSum SPComp.pure A))
    (fun a => SPComp.bind (dualOT_ideal gp crs a)
      (mapSum SPComp.pure (dualOT_sim gp crs V A))) ≤ ε
  have heq_real : (fun a => SPComp.bind (dualOT_real gp crs a) (mapSum SPComp.pure A)) =
      fun a => SPComp.bind (SPComp.sample gp.Scalar) fun r₀ =>
        SPComp.bind (SPComp.sample gp.Scalar) fun r₁ =>
        SPComp.map Sum.inr (A (dualEnc gp crs.pk₀ a.m₀ r₀, dualEnc gp crs.pk₁ a.m₁ r₁)) := by
    funext a; simp only [dualOT_real, SPComp.bind_assoc, SPComp.pure_bind, mapSum_inr, SPComp.map]
  have heq_sim : (fun a => SPComp.bind (dualOT_ideal gp crs a)
        (mapSum SPComp.pure (dualOT_sim gp crs V A))) =
      fun a => SPComp.bind (SPComp.sample gp.Scalar) fun r =>
        SPComp.bind (SPComp.sample gp.G) fun ct_other =>
        let ct_chosen := dualEnc gp (if a.choice then crs.pk₁ else crs.pk₀)
          (if a.choice then a.m₁ else a.m₀) r
        SPComp.map Sum.inr
          (if a.choice then A (ct_other, ct_chosen) else A (ct_chosen, ct_other)) := by
    funext a; simp only [dualOT_ideal, dualOT_sim, SPComp.bind_assoc, SPComp.pure_bind,
      mapSum_inr, SPComp.map]
  simp only [heq_real, heq_sim]
  apply iSup_le; intro D
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  -- Shared closing step: bound the ciphertext-vs-uniform gap in the unchosen slot.
  have final : ∀ (pk m : gp.G) (K : gp.G → SPComp Bool),
      sdist (fun _ : Unit => SPComp.bind (SPComp.sample gp.Scalar)
              (fun r => SPComp.pure (dualEnc gp pk m r)))
            (fun _ : Unit => SPComp.sample gp.G) ≤ ε →
      absDiff (prTrue (SPComp.bind (SPComp.bind (SPComp.sample gp.Scalar)
                (fun r => SPComp.pure (dualEnc gp pk m r))) K) h₀)
              (prTrue (SPComp.bind (SPComp.sample gp.G) K) h₀) ≤ ε := by
    intro pk m K hb
    exact sdist_le_of_forall hb K () h₀
  cases hc : a.choice
  · -- choice = false: `(pk₀, m₀)` is chosen, `(pk₁, m₁)` is unchosen.
    have lhs_swap : SPComp.bind
        (SPComp.bind (SPComp.sample gp.Scalar) fun r₀ =>
          SPComp.bind (SPComp.sample gp.Scalar) fun r₁ =>
          SPComp.map Sum.inr (A (dualEnc gp crs.pk₀ a.m₀ r₀, dualEnc gp crs.pk₁ a.m₁ r₁))) D =
        SPComp.bind (SPComp.sample gp.Scalar) fun r₁ =>
          SPComp.bind (SPComp.sample gp.Scalar) fun r₀ =>
          SPComp.bind (SPComp.map Sum.inr (A (dualEnc gp crs.pk₀ a.m₀ r₀, dualEnc gp crs.pk₁ a.m₁ r₁))) D := by
      simp only [SPComp.bind_assoc]
      exact SPComp.isPure_bind_comm (SPComp.sample gp.Scalar) (SPComp.sample gp.Scalar)
        (fun r₀ r₁ => SPComp.bind (SPComp.map Sum.inr
          (A (dualEnc gp crs.pk₀ a.m₀ r₀, dualEnc gp crs.pk₁ a.m₁ r₁))) D)
        (SPComp.sample_isPure _) (SPComp.sample_isPure _)
    have rhs_swap : SPComp.bind
        (SPComp.bind (SPComp.sample gp.Scalar) fun r =>
          SPComp.bind (SPComp.sample gp.G) fun ct_other =>
          let ct_chosen := dualEnc gp (if a.choice then crs.pk₁ else crs.pk₀)
            (if a.choice then a.m₁ else a.m₀) r
          SPComp.map Sum.inr
            (if a.choice then A (ct_other, ct_chosen) else A (ct_chosen, ct_other))) D =
        SPComp.bind (SPComp.sample gp.G) fun ct =>
          SPComp.bind (SPComp.sample gp.Scalar) fun r =>
          SPComp.bind (SPComp.map Sum.inr (A (dualEnc gp crs.pk₀ a.m₀ r, ct))) D := by
      simp [SPComp.bind_assoc, hc]
      exact SPComp.isPure_bind_comm_left (SPComp.sample gp.Scalar) (SPComp.sample gp.G)
        _ (SPComp.sample_isPure _)
    rw [lhs_swap, rhs_swap]
    have lhs_factor : (SPComp.bind (SPComp.sample gp.Scalar) fun r₁ =>
        SPComp.bind (SPComp.sample gp.Scalar) fun r₀ =>
        SPComp.bind (SPComp.map Sum.inr (A (dualEnc gp crs.pk₀ a.m₀ r₀, dualEnc gp crs.pk₁ a.m₁ r₁))) D) =
        SPComp.bind (SPComp.bind (SPComp.sample gp.Scalar)
          (fun r => SPComp.pure (dualEnc gp crs.pk₁ a.m₁ r)))
          (fun ct => SPComp.bind (SPComp.sample gp.Scalar) fun r₀ =>
            SPComp.bind (SPComp.map Sum.inr (A (dualEnc gp crs.pk₀ a.m₀ r₀, ct))) D) := by
      simp only [SPComp.bind_assoc, SPComp.pure_bind]
    rw [lhs_factor]
    exact final crs.pk₁ a.m₁ _ (hb1 a.m₁)
  · -- choice = true: `(pk₁, m₁)` is chosen, `(pk₀, m₀)` is unchosen.
    have rhs_swap : SPComp.bind
        (SPComp.bind (SPComp.sample gp.Scalar) fun r =>
          SPComp.bind (SPComp.sample gp.G) fun ct_other =>
          let ct_chosen := dualEnc gp (if a.choice then crs.pk₁ else crs.pk₀)
            (if a.choice then a.m₁ else a.m₀) r
          SPComp.map Sum.inr
            (if a.choice then A (ct_other, ct_chosen) else A (ct_chosen, ct_other))) D =
        SPComp.bind (SPComp.sample gp.G) fun ct =>
          SPComp.bind (SPComp.sample gp.Scalar) fun r =>
          SPComp.bind (SPComp.map Sum.inr (A (ct, dualEnc gp crs.pk₁ a.m₁ r))) D := by
      simp [SPComp.bind_assoc, hc]
      exact SPComp.isPure_bind_comm_left (SPComp.sample gp.Scalar) (SPComp.sample gp.G)
        _ (SPComp.sample_isPure _)
    have lhs_factor : SPComp.bind
        (SPComp.bind (SPComp.sample gp.Scalar) fun r₀ =>
          SPComp.bind (SPComp.sample gp.Scalar) fun r₁ =>
          SPComp.map Sum.inr (A (dualEnc gp crs.pk₀ a.m₀ r₀, dualEnc gp crs.pk₁ a.m₁ r₁))) D =
        SPComp.bind (SPComp.bind (SPComp.sample gp.Scalar)
          (fun r => SPComp.pure (dualEnc gp crs.pk₀ a.m₀ r)))
          (fun ct => SPComp.bind (SPComp.sample gp.Scalar) fun r₁ =>
            SPComp.bind (SPComp.map Sum.inr (A (ct, dualEnc gp crs.pk₁ a.m₁ r₁))) D) := by
      simp only [SPComp.bind_assoc, SPComp.pure_bind]
    rw [lhs_factor, rhs_swap]
    exact final crs.pk₀ a.m₀ _ (hb0 a.m₀)

/-! ## Security Proof -/

/-- **Sender-message privacy, parametric.** For any per-key ciphertext-hiding
    bound `ε` (`CiphertextPseudorandom`), the OT is UC-secure with error `ε`
    against a corrupt receiver: the simulator `dualOT_sim` fakes the unchosen
    ciphertext with a uniform group element, and the gap between the real
    unchosen ciphertext and a uniform one is bounded by `ε`. For concrete
    non-identity keys this discharges at `ε = 0` — see `dualOT_uc_secure_zero`.
    (genuine UC) -/
theorem dualOT_uc_secure (crs : DualModeCRS gp)
    (ε : ℝ≥0∞) (hcpr : CiphertextPseudorandom gp ε) (V : Type) :
    UCEmulates ε (dualOTSpec gp V)
      (dualOT_real gp crs) (dualOT_ideal gp crs) :=
  dualOT_reduction gp crs V ε (fun m => hcpr crs.pk₀ m) (fun m => hcpr crs.pk₁ m)

/-- **Sender-message privacy, perfect.** When both public keys are non-identity
    (in a prime-order group, both are generators), the OT is *perfectly*
    UC-secure against a corrupt receiver: the simulator's uniform group element
    is exactly the distribution of the real unchosen ciphertext
    (`dualEnc_uniform`), so real and ideal views coincide. No assumption, no
    reduction. (genuine UC) -/
theorem dualOT_uc_secure_zero (crs : DualModeCRS gp)
    (h0 : crs.pk₀ ≠ gp.identity) (h1 : crs.pk₁ ≠ gp.identity) (V : Type) :
    UCEmulates 0 (dualOTSpec gp V)
      (dualOT_real gp crs) (dualOT_ideal gp crs) :=
  dualOT_reduction gp crs V 0
    (fun m => le_of_eq (sdist_dualEnc_uniform gp crs.pk₀ m h0))
    (fun m => le_of_eq (sdist_dualEnc_uniform gp crs.pk₁ m h1))

/-! ## Nice-to-have: the full dual-mode construction

The statement above is corrupt-receiver / sender-message privacy only, and its
simulator ignores the `DualModeCRS` trapdoor. The genuine Peikert–Vaikuntanathan–
Waters dual-mode OT would make the CRS load-bearing and additionally cover the
corrupt-sender / receiver-privacy direction:

* **Two indistinguishable CRS modes.** In *messy* mode one public key produces
  ciphertexts statistically independent of the plaintext (enabling extraction of
  the receiver's choice bit); in *decryption* mode both keys decrypt correctly
  (enabling extraction of both sender messages). The two modes are
  computationally indistinguishable under DDH — this is where a real DDH
  reduction enters, in contrast to the information-theoretic hiding used here.
* **Corrupt receiver (messy CRS).** The simulator reads off which key is messy,
  extracts the choice bit, forwards it to `F_OT`, and simulates the other
  ciphertext — using the trapdoor, rather than the `dualOT_ideal` leak of the
  choice bit assumed here.
* **Corrupt sender (decryption CRS).** The simulator decrypts both ciphertexts
  via `sk`, extracts both messages, and forwards them to `F_OT` — the case the
  present ideal functionality does not model at all.

Realizing this needs a genuine `dualOT_ideal` that hides the choice bit, a
CRS-mode-indistinguishability game, and per-mode simulators; it is not attempted
here.

This full account is developed in the larger CatCrypt UC development built on top
of this basis (outside this minimal-basis release): an `OT/` tree with the `F_OT`
functionality capturing both sender and receiver privacy (`FOT`), the extraction
machinery, and the plain-model impossibility (`PlainModelOTImpossibility`). This
file is the self-contained corrupt-receiver / sender-privacy exemplar. -/

end CatCrypt.Crypto.OT.DualModeOT
