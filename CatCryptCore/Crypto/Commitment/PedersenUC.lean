/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UC
public import CatCryptCore.Crypto.SDist
public import CatCryptCore.Examples.GroupParam
public import CatCryptCore.Tactics.BindVcgenSum

/-!
# Pedersen Commitment: Commit Phase and Commit-and-Open Equivalence

Pedersen commitment over an abstract discrete-log group with a CRS trapdoor.
Two statements, both at error `0` (perfect), for an honest committer against a
corrupt receiver:

* `pedersen_uc_commit_phase` — the commit phase. The real world leaks the
  commitment; the ideal functionality tells the simulator only that a
  commitment was made, and the simulator samples a uniform commitment. This is
  perfect hiding stated as a UC emulation.
* `pedersen_uc_commit_open` — commit and open together. The real world leaks
  the commitment and the opening randomness; the ideal functionality hands the
  simulator a uniform commitment exponent `s`, sampled independently of `m`,
  together with `m`, and the simulator opens `s` to `m` with the trapdoor
  (equivocation). The simulator receives `m`, so this statement alone does not
  express hiding; it states that equivocating a commitment made without `m`
  reproduces the joint distribution of commitment and opening.

`pedersen_uc_commit_open` is the former `pedersen_uc_secure`; the commit-phase
statement `pedersen_uc_commit_phase` is new.

Neither statement covers a corrupt committer (extraction and binding).
Perfectly hiding Pedersen has no extractor: a commitment carries no
information about the message.

## Modeling choice: reveal the exponent, not the group element

`pedersen_real` returns the exponent `s = dlog C = m + t · r` rather than the
group element `C = g ^ s` itself. For a fixed generator, `s ↦ g ^ s` is a
bijection, so the two carry the same information and the distributions are
equivalent; working with the exponent makes the change-of-variables comparison
against the ideal exponent direct.

## Protocol

For a cyclic group `G` with generator `g` and CRS `h = g ^ t`:

* `Commit(m)`: sample `r`, output `C = g ^ m · h ^ r` with decommitment `r`.
* `Open(m, r)`: the verifier checks `C = g ^ m · h ^ r`.

## UC security via the CRS trapdoor

The simulator knows the CRS trapdoor `t` (the discrete log of `h`):

* on commit, the ideal samples a uniform exponent `s` and sets `C = g ^ s`;
* on open of `m`, the simulator computes `r = (s - m) / t`, so that
  `m + t · r = s`.

In the real world the pair `(s, r)` with `s = m + t · r` is uniform because `r`
is uniform; in the ideal world `(s, r)` with `r = (s - m) / t` is uniform
because `s` is uniform and `s ↦ (s - m) / t` is a bijection (for `t ≠ 0`). The
two joint distributions coincide, so the views are identically distributed.

## Non-trivial simulator

`pedersen_sim` is not the adversary. Using the trapdoor `t` it computes fake
randomness `r` from the ideal exponent `s` and the message `m` — genuine
equivocation, retroactively opening a commitment produced without the message.

## Interface types

Commit phase (`pedersenCommitSpec`):
* `leak = Scalar` — the real world leaks the exponent `s = m + t·r`.
* `sim_if = Unit` — the ideal tells the simulator that a commitment was made.

Commit and open (`pedersenSpec`):
* `leak = Scalar × Scalar` — the real world leaks the exponent `s = m + t·r` and
  the randomness `r`.
* `sim_if = Scalar × Scalar` — the ideal hands the simulator the exponent `s` and
  the message `m`. The simulator turns `(s, m)` into a view indistinguishable
  from `(s, r)`.
-/

@[expose] public section

namespace CatCrypt.Crypto.Commitment.PedersenUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Examples
open scoped ENNReal

set_option autoImplicit false

variable (gp : GroupParam)

/-! ## CRS Setup -/

/-- CRS for Pedersen commitment: `h = g ^ trapdoor`. In the real protocol the
    trapdoor is unknown; the UC simulator knows it. -/
structure PedersenCRS where
  /-- The CRS public key `h`, a group element. -/
  h : gp.G
  /-- The trapdoor: the discrete log of `h` with respect to `g`. -/
  trapdoor : gp.Scalar
  /-- CRS correctness: `h = g ^ trapdoor`. -/
  h_eq : h = gp.exp trapdoor

/-! ## Protocol -/

/-- Pedersen commitment to `m` with randomness `r`: `C = g ^ m · h ^ r`. -/
def pedersen_commit (crs : PedersenCRS gp) (m r : gp.Scalar) : gp.G :=
  gp.groupMul (gp.exp m) (gp.groupExp crs.h r)

/-- Real protocol: commit to `m`, revealing the exponent `s = m + t · r` of
    `C = g ^ s` and the randomness `r`. Returning the exponent rather than the
    group element makes the distribution comparison direct. -/
noncomputable def pedersen_real (crs : PedersenCRS gp) :
    gp.Scalar → SPComp (Unit ⊕ (gp.Scalar × gp.Scalar)) :=
  fun m => do
    let r ← SPComp.sample gp.Scalar
    let s := gp.scalarAdd m (gp.scalarMul crs.trapdoor r)
    SPComp.pure (.inr (s, r))

/-- Ideal functionality: sample a uniform exponent `s` and reveal `(s, m)` on the
    simulator interface. -/
noncomputable def pedersen_ideal (_crs : PedersenCRS gp) :
    gp.Scalar → SPComp (Unit ⊕ (gp.Scalar × gp.Scalar)) :=
  fun m => do
    let s ← SPComp.sample gp.Scalar
    SPComp.pure (.inr (s, m))

/-! ## Non-Trivial Simulator -/

/-- The Pedersen simulator: from `(s, m)` it produces a fake `(s, r)` for the
    adversary using the CRS trapdoor `t`, computing `r = (s - m) / t` so that
    `m + t · r = s`. -/
noncomputable def pedersen_sim (crs : PedersenCRS gp)
    (view : Type) (A : gp.Scalar × gp.Scalar → SPComp view) :
    gp.Scalar × gp.Scalar → SPComp view :=
  fun (s, m) =>
    let r := gp.scalarDiv (gp.scalarSub s m) crs.trapdoor
    A (s, r)

/-! ## UC Specification -/

/-- UC spec for Pedersen commitment: honest input is a message, the real world
    leaks `(exponent, randomness)`, and the ideal world hands the simulator
    `(exponent, message)`. -/
noncomputable def pedersenSpec (V : Type) : UCSpec :=
  ⟨gp.Scalar, Unit, gp.Scalar × gp.Scalar, gp.Scalar × gp.Scalar, V⟩

/-! ## Security Proof -/

/-- The affine map `r ↦ m + t · r` is a bijection of `Scalar` when `t ≠ 0`. -/
noncomputable def affineEquiv (crs : PedersenCRS gp)
    (ht : crs.trapdoor ≠ gp.scalarZero) (m : gp.Scalar) :
    gp.Scalar ≃ gp.Scalar where
  toFun r := gp.scalarAdd m (gp.scalarMul crs.trapdoor r)
  invFun s := gp.scalarDiv (gp.scalarSub s m) crs.trapdoor
  left_inv := by
    intro r; simp only
    rw [gp.scalarSub_eq, gp.scalarAdd_assoc,
        gp.scalarAdd_comm (gp.scalarMul crs.trapdoor r) (gp.scalarNeg m),
        ← gp.scalarAdd_assoc, gp.scalarAdd_neg, gp.scalarZero_add,
        gp.scalarMul_comm]
    exact gp.mul_div_cancel r crs.trapdoor ht
  right_inv := by
    intro s; simp only
    rw [gp.scalarMul_comm, gp.div_mul_cancel _ _ ht, gp.scalarSub_eq,
        gp.scalarAdd_comm s (gp.scalarNeg m),
        ← gp.scalarAdd_assoc, gp.scalarAdd_neg, gp.scalarZero_add]

/-- The real and simulated views coincide pointwise: the change of variables
    `r ↦ m + t · r` couples the real randomness with the ideal exponent. -/
theorem pedersen_view_eq (crs : PedersenCRS gp)
    (ht : crs.trapdoor ≠ gp.scalarZero)
    (m : gp.Scalar) (view : Type) (A : gp.Scalar × gp.Scalar → SPComp view) :
    SPComp.bind (pedersen_real gp crs m) (mapSum SPComp.pure A) =
    SPComp.bind (pedersen_ideal gp crs m) (mapSum SPComp.pure (pedersen_sim gp crs view A)) := by
  let e := affineEquiv gp crs ht m
  unfold pedersen_real pedersen_ideal pedersen_sim
  bind_vcgen_sum using e
  rename_i r
  exact congrArg (fun c => SPComp.bind c (fun a => SPComp.pure (Sum.inr a)))
    (congrArg (fun y => A (e r, y)) (e.left_inv r).symm)

/-- The Pedersen commitment `C = g ^ m · h ^ r` varies with the committed message:
    for fixed randomness, distinct messages give distinct commitments (the
    generator has prime order, so `exp` is injective). Perfect hiding therefore
    comes from the uniform randomness `r`, not from the commit function ignoring
    the message. -/
theorem pedersen_commit_output_depends_on_message (crs : PedersenCRS gp)
    (m₀ m₁ r : gp.Scalar) (hm : m₀ ≠ m₁) :
    pedersen_commit gp crs m₀ r ≠ pedersen_commit gp crs m₁ r := by
  unfold pedersen_commit
  intro h
  apply hm
  apply gp.exp_inj
  have hc := congrArg (fun w => gp.groupMul w (gp.groupInv (gp.groupExp crs.h r))) h
  simpa only [gp.groupMul_assoc, gp.groupMul_inv, gp.groupMul_identity] using hc

/-- **Commit and open: equivocation at `ε = 0`.** The ideal functionality
    samples a commitment exponent `s` independently of `m` and hands `(s, m)` to
    the simulator `pedersen_sim`, which opens `s` to `m` with the trapdoor,
    `r = (s - m) / t`. The real and simulated views of commitment and opening
    coincide. The simulator receives `m`, so this statement does not express
    hiding; the commit phase alone is `pedersen_uc_commit_phase`. -/
theorem pedersen_uc_commit_open (crs : PedersenCRS gp)
    (ht : crs.trapdoor ≠ gp.scalarZero) (V : Type) :
    UCEmulates 0 (pedersenSpec gp V) (pedersen_real gp crs) (pedersen_ideal gp crs) := by
  intro A
  refine ⟨pedersen_sim gp crs V A, ?_⟩
  have h : ∀ a, SPComp.bind (pedersen_real gp crs a) (mapSum SPComp.pure A) =
      SPComp.bind (pedersen_ideal gp crs a) (mapSum SPComp.pure (pedersen_sim gp crs V A)) :=
    fun m => pedersen_view_eq gp crs ht m V A
  calc sdist (fun a => SPComp.bind (pedersen_real gp crs a) (mapSum SPComp.pure A))
             (fun a => SPComp.bind (pedersen_ideal gp crs a)
                (mapSum SPComp.pure (pedersen_sim gp crs V A)))
      = sdist (fun a => SPComp.bind (pedersen_ideal gp crs a)
                (mapSum SPComp.pure (pedersen_sim gp crs V A)))
              (fun a => SPComp.bind (pedersen_ideal gp crs a)
                (mapSum SPComp.pure (pedersen_sim gp crs V A))) := by
          congr 1; funext a; exact h a
    _ ≤ 0 := le_of_eq (sdist_self _)

/-! ## Commit phase -/

/-- Commit phase of the real protocol: commit to `m` and reveal the exponent
    `s = m + t · r` of the commitment `C = g ^ s`. -/
noncomputable def pedersen_commit_real (crs : PedersenCRS gp) :
    gp.Scalar → SPComp (Unit ⊕ gp.Scalar) :=
  fun m => do
    let r ← SPComp.sample gp.Scalar
    SPComp.pure (.inr (gp.scalarAdd m (gp.scalarMul crs.trapdoor r)))

/-- Commit phase of the ideal functionality: the simulator learns only that a
    commitment was made. -/
noncomputable def pedersen_commit_ideal (_crs : PedersenCRS gp) :
    gp.Scalar → SPComp (Unit ⊕ Unit) :=
  fun _m => SPComp.pure (.inr ())

/-- Commit-phase simulator: hand the adversary a uniform commitment exponent. -/
noncomputable def pedersen_commit_sim (view : Type) (A : gp.Scalar → SPComp view) :
    Unit → SPComp view :=
  fun _ => SPComp.bind (SPComp.sample gp.Scalar) A

/-- UC spec of the commit phase: honest input is a message, the real world
    leaks the commitment exponent, and the ideal world tells the simulator that
    a commitment was made. -/
noncomputable def pedersenCommitSpec (V : Type) : UCSpec :=
  ⟨gp.Scalar, Unit, gp.Scalar, Unit, V⟩

/-- The real and simulated views of the commit phase coincide pointwise: the
    change of variables `r ↦ m + t · r` maps the uniform randomness to the
    uniform commitment exponent. -/
theorem pedersen_commit_view_eq (crs : PedersenCRS gp)
    (ht : crs.trapdoor ≠ gp.scalarZero)
    (m : gp.Scalar) (view : Type) (A : gp.Scalar → SPComp view) :
    SPComp.bind (pedersen_commit_real gp crs m) (mapSum SPComp.pure A) =
    SPComp.bind (pedersen_commit_ideal gp crs m)
      (mapSum SPComp.pure (pedersen_commit_sim gp view A)) := by
  unfold pedersen_commit_real pedersen_commit_ideal pedersen_commit_sim
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind, mapSum_inr, SPComp.map]
  exact SPComp.sample_bind_equiv (affineEquiv gp crs ht m)
    (fun s => SPComp.bind (A s) fun v => SPComp.pure (Sum.inr v))

/-- **Commit phase at `ε = 0` (perfect hiding).** The commitment exponent
    `m + t · r` of a uniform `r` is uniform for `t ≠ 0`, so the simulator
    `pedersen_commit_sim`, which does not receive `m`, reproduces the
    adversary's view of the commit phase. -/
theorem pedersen_uc_commit_phase (crs : PedersenCRS gp)
    (ht : crs.trapdoor ≠ gp.scalarZero) (V : Type) :
    UCEmulates 0 (pedersenCommitSpec gp V)
      (pedersen_commit_real gp crs) (pedersen_commit_ideal gp crs) := by
  intro A
  refine ⟨pedersen_commit_sim gp V A, le_of_eq ?_⟩
  show sdist _ _ = 0
  exact (congrArg (sdist · _) (funext fun m => pedersen_commit_view_eq gp crs ht m V A)).trans
    (sdist_self _)

/-! ## Nice-to-have: the extraction direction

The complementary half — a corrupt committer, where the simulator extracts the
committed message from `C` and the commitment is binding — is out of reach for
this protocol, not merely unproved: plain Pedersen is perfectly hiding, so no
extractor exists. Closing the gap to full `F_commit` means changing the
primitive, not extending this proof: instantiate an extractable / dual-mode
commitment (e.g. a hiding+extractable CRS mode, or an El-Gamal-style commitment
whose CRS trapdoor is a decryption key), then state and prove the extraction
direction against it. That belongs in a separate file for the extractable
scheme; there is deliberately no extraction theorem here to fake.

This is not left open across CatCrypt: the full account — the `F_commit`
functionality with both equivocation and extraction, an extractable commitment
realizing it, and the plain-model impossibility — is developed in the larger
CatCrypt UC development built on top of this basis (a `Commitment/` tree with
`FCOM` / `Extraction` / `PlainModelImpossibility`), which is outside this
minimal-basis release. This file is the self-contained equivocation exemplar. -/

end CatCrypt.Crypto.Commitment.PedersenUC
