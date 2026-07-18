/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.UC
import CatCryptCore.Crypto.SDist
import CatCryptCore.Examples.GroupParam
import CatCryptCore.Tactics.BindVcgenSum

/-!
# Pedersen Commitment: UC Security via a Trapdoor Equivocator

Pedersen commitment over an abstract discrete-log group, proved UC-secure at
error `0` (perfect security) with a **non-trivial simulator**.

## Scope: the equivocation direction only

This file proves the **equivocation** direction of UC commitment: an honest
committer against a corrupt receiver. In that direction Pedersen is perfectly
hiding, and the CRS trapdoor lets the simulator produce a commitment before it
learns the message and open it consistently afterwards. The bound is exactly
`ε = 0`.

It does **not** cover the extraction direction (a corrupt committer, where the
simulator must extract the committed message and the commitment must be
binding). Perfectly-hiding Pedersen cannot provide that: hiding is
information-theoretic, so a commitment carries no information the simulator
could extract, and equivocation is the concrete witness that the same `C` opens
to every message given the trapdoor. Realizing the full `F_commit`
functionality — both directions — requires an *extractable* (equivalently,
mixed / dual-mode) commitment, not a plain perfectly-hiding one. So the result
here is one half of UC commitment, stated as such.

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

* `leak = Scalar × Scalar` — the real world leaks the exponent `s = m + t·r` and
  the randomness `r`.
* `sim_if = Scalar × Scalar` — the ideal hands the simulator the exponent `s` and
  the message `m`. The simulator turns `(s, m)` into a view indistinguishable
  from `(s, r)`.
-/

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

/-- **Pedersen commitment with a CRS trapdoor realizes the equivocation
    direction of UC commitment at `ε = 0`** (perfect), with a non-trivial
    simulator. This is the honest-committer / corrupt-receiver direction: given
    `(s, m)` from the ideal, the simulator `pedersen_sim` equivocates by
    computing `r = (s - m) / t` and passing `(s, r)` to the adversary.

    Scope: this does not cover the corrupt-committer / extraction direction —
    a perfectly-hiding commitment cannot be extractable, and full `F_commit`
    needs an extractable (mixed / dual-mode) commitment. (genuine UC) -/
theorem pedersen_uc_secure (crs : PedersenCRS gp)
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
