/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UC
public import CatCryptCore.Examples.GroupParam

/-!
# Hiding of the Unchosen Sender Message under Two Public Keys

The sender's step of a two-key oblivious transfer over an abstract discrete-log
group: each of the two messages is encrypted under its own public key, with
ElGamal-style encryption `dualEnc pk m r = pk ^ r · m`. The real world
`dualOT_real` outputs the two ciphertexts; it has no receiver message and its
honest output is `Unit`. The ideal world `dualOT_ideal` hands the simulator the
choice bit and the ciphertext of the chosen message. The UC statement
`dualOT_uc_secure_zero` says that the ciphertext of the unchosen message is
simulated perfectly from this leak.

The complete Peikert–Vaikuntanathan–Waters dual-mode OT, with an ideal OT that
hides the choice bit, both corruption cases through the CRS trapdoors and the
DDH hop between the CRS modes, is `CatCryptCore.Crypto.OT.PVWOTSquare`.

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
both public keys are non-identity. `dualOT_reduction` gives the bound from
per-key statistical-distance hypotheses on `crs.pk₀` and `crs.pk₁`.

## Interface types

* `leak = G × G` — the real world leaks the two ciphertexts.
* `sim_if = Bool × G` — the ideal hands the simulator the choice bit and the
  chosen message's ciphertext; the simulator fakes the other ciphertext.
-/

@[expose] public section

namespace CatCrypt.Crypto.OT.DualModeOT

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Examples
open scoped ENNReal

set_option autoImplicit false

variable (gp : GroupParam)

/-! ## Public Keys and Encryption -/

/-- Public keys for the two message slots, with a mode bit and the secret key of
    the selected public key. The statement below uses only that both public keys
    are non-identity. -/
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

/-- Real world: encrypt both messages under the two public keys and leak both
    ciphertexts; the honest output is `Unit`. -/
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
  simp only [dualEncEquiv, Equiv.trans_apply, Equiv.coe_fn_mk]
  rfl

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
  simp_all [dualEnc_uniform, sdist_self]

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


end CatCrypt.Crypto.OT.DualModeOT
