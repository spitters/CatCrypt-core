/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.Assumptions.DDH
public import CatCryptCore.Crypto.ForkingLemma
public import CatCryptCore.Tactics

/-!
# Computational Diffie-Hellman (CDH) Assumption

The CDH assumption: given `(g^a, g^b)`, compute the shared secret `g^{ab}`.
This is the computational analogue of DDH; DDH ⟹ CDH but not vice versa.

## Main definitions

* `CDH_Game` — the CDH game
* `CDH_Advantage` — probability of computing the shared secret
* `ddh_of_cdh` — DDH adversary from a CDH adversary
* `cdh_le_ddh` — `CDH_Advantage D A ≤ DDH_Advantage D (ddh_of_cdh A) + 1/|W|`
* `DL_Adversary_DDH` — discrete log adversary over `DDHDef`
* `DL_Game_DDH` — discrete log game over `DDHDef`
* `cdh_of_dl_ddh` — CDH adversary from DL adversary (CDH ⟹ DL reduction)
* `dl_le_cdh_ddh` — `DL_Advantage_DDH D A ≤ CDH_Advantage D (cdh_of_dl_ddh D A)`

The former predicate `CDHSecure D ε := ∀ A, CDH_Advantage D A ≤ ε` and its corollary
`cdh_secure_implies_dl_secure` are removed: the per-adversary reductions `cdh_le_ddh` and
`dl_le_cdh_ddh` state the same relations without an assumption over all adversaries.

## Cross-Validation

| Property | This file | Textbook |
|----------|-----------|----------|
| Challenge | `(g^a, g^b)` | Boneh-Shoup Def. 11.1 |
| Target | Compute `ecdh(a, g^b) = g^{ab}` | Compute `g^{ab}` |
| Group | `DDHDef W` | Cyclic group of prime order |
| CDH ⟹ DL | `cdh_of_dl_ddh` | BS Prop. 11.4 |

**Equivalent formalizations:**
- EasyCrypt: `CDH` theory in `theories/crypto/DiffieHellman.ec`
- SSProve (Rocq): not formalized (only DDH)

**Relationship to other assumptions:**
- DDH ⟹ CDH (if you can't distinguish, you can't compute)
- CDH ⟹ DL (if you can compute DH, you can compute discrete logs)
- co-CDH (in `CoCDH.lean`) is the Type-III bilinear variant

See also `CDH_DL.lean` for the CDH ⟹ DL reduction over `PairingGroup`.

## References

* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §11.3, Def. 11.1; §11.3 Prop. 11.4
* Diffie & Hellman, *New Directions in Cryptography*, IEEE-IT 1976
-/

@[expose] public section

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {W : Type} [SampleableType W] [DecidableEq W]

/-! ## CDH Game -/

/-- CDH adversary: given `(g^a, g^b)`, attempts to compute the shared
    secret `ecdh(a, g^b) = g^{ab}`. -/
abbrev CDH_Adversary (W : Type) := W → W → SPComp W

/-- CDH game: sample key pairs `(a, g^a)` and `(b, g^b)`, give `(g^a, g^b)`
    to adversary, check if output equals `ecdh(a, g^b)`.

    Returns `true` if the adversary computes the correct shared secret. -/
noncomputable def CDH_Game (D : DDHDef W) (A : CDH_Adversary W) : SPComp Bool := do
  let ⟨a, g_a⟩ ← D.keygen
  let ⟨_, g_b⟩ ← D.keygen
  let answer ← A g_a g_b
  let target := D.ecdh a g_b  -- = g^{ab}
  SPComp.pure (decide (answer = target))

/-- CDH advantage: probability that the adversary computes `g^{ab}`. -/
noncomputable def CDH_Advantage (D : DDHDef W) (A : CDH_Adversary W) : ℝ≥0∞ :=
  prTrue (CDH_Game D A) Heap.empty

/-! ## Reduction: DDH ⟹ CDH

If an adversary can compute `g^{ab}` (break CDH), it can also
distinguish `(g^a, g^b, g^{ab})` from `(g^a, g^b, random)` (break DDH),
by computing the answer and comparing. -/

/-- Construct a DDH adversary from a CDH adversary: compute the
    alleged shared secret and check if it matches the challenge. -/
noncomputable def ddh_of_cdh (A : CDH_Adversary W) : DDH_Adversary W :=
  fun g_a g_b challenge => do
    let answer ← A g_a g_b
    SPComp.pure (decide (answer = challenge))

/-- A continuation whose success probability is at most `ε` from every state keeps the
    success probability of the composed computation at most `ε`. -/
private theorem prTrue_bind_le_const {α : Type} (c : SPComp α) (k : α → SPComp Bool)
    (ε : ℝ≥0∞) (h₀ : Heap) (hk : ∀ a h', prTrue (k a) h' ≤ ε) :
    prTrue (c.bind k) h₀ ≤ ε :=
  (ForkingLemma.prTrue_bind_mono_const ε c k (fun _ => SPComp.pure true) h₀ fun a h' => by
      rw [ForkingLemma.prTrue_pure_bool]; simpa using hk a h').trans
    (mul_le_of_le_one_right' (prTrue_le_one _ _))

/-- A value computed by `c` equals a uniform `r ← W` sampled before `c` runs with
    probability at most `1/|W|`. -/
theorem prTrue_sample_guess (c : SPComp W) (h₀ : Heap) :
    prTrue ((SPComp.sample W).bind fun r => c.bind fun x => SPComp.pure (decide (x = r))) h₀
      ≤ (Fintype.card W : ℝ≥0∞)⁻¹ := by
  rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure W)]
  refine prTrue_bind_le_const _ _ _ _ fun x h' => ?_
  rw [ForkingLemma.prTrue_sample_pure_bool]
  simp [Finset.filter_eq]

/-- **DDH ⟹ CDH.** For every CDH adversary `A`,
    `CDH_Advantage D A ≤ DDH_Advantage D (ddh_of_cdh A) + 1/|W|`.
    The real DDH game with `ddh_of_cdh A` is the CDH game; in the ideal DDH game the
    challenge is uniform and independent of `A`'s answer, so `ddh_of_cdh A` outputs
    `true` there with probability at most `1/|W|`. -/
theorem cdh_le_ddh (D : DDHDef W) (A : CDH_Adversary W) :
    CDH_Advantage D A ≤ DDH_Advantage D (ddh_of_cdh A) + (Fintype.card W : ℝ≥0∞)⁻¹ := by
  have hreal : CDH_Advantage D A = prTrue (DDH_Game_Real D (ddh_of_cdh A)) Heap.empty := rfl
  have hideal : prTrue (DDH_Game_Ideal D (ddh_of_cdh A)) Heap.empty ≤
      (Fintype.card W : ℝ≥0∞)⁻¹ := by
    unfold DDH_Game_Ideal ddh_of_cdh
    simp only [SPComp.monad_bind_eq]
    refine prTrue_bind_le_const _ _ _ _ fun p _ => ?_
    obtain ⟨_, g_a⟩ := p
    refine prTrue_bind_le_const _ _ _ _ fun q _ => ?_
    obtain ⟨_, g_b⟩ := q
    exact prTrue_sample_guess (A g_a g_b) _
  rw [hreal]
  calc prTrue (DDH_Game_Real D (ddh_of_cdh A)) Heap.empty
      ≤ (prTrue (DDH_Game_Real D (ddh_of_cdh A)) Heap.empty -
          prTrue (DDH_Game_Ideal D (ddh_of_cdh A)) Heap.empty) +
        prTrue (DDH_Game_Ideal D (ddh_of_cdh A)) Heap.empty := le_tsub_add
    _ ≤ DDH_Advantage D (ddh_of_cdh A) + (Fintype.card W : ℝ≥0∞)⁻¹ :=
        add_le_add (le_max_left _ _) hideal

/-! ## IsPure Proofs -/

theorem CDH_Game_isPure (D : DDHDef W) (A : CDH_Adversary W)
    (hA : ∀ x y, SPComp.IsPure (A x y)) :
    SPComp.IsPure (CDH_Game D A) := by
  unfold CDH_Game
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨a, g_a⟩
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨_, g_b⟩
  simp_all [SPComp.bind_isPure, SPComp.pure_isPure]

/-! ## Reduction: CDH ⟹ DL (abstract DDHDef setting)

The standard direction: CDH hard implies DL hard (BS Prop. 11.4).
Equivalently, by contrapositive: if you can solve DL (find private keys
from public keys), you can solve CDH.

In the abstract `DDHDef` setting, a "discrete log adversary" receives a
public key `g^a` and returns a private key `a'` such that the corresponding
public key matches. We define this via `keygen`'s structure: the adversary
must recover the private component from the public component.

**Reduction.** Given a DL adversary that finds `a` from `g^a`:
1. Receive CDH challenge `(g^a, g^b)`
2. Run the DL adversary on `g^a` to recover `a`
3. Compute `ecdh(a, g^b) = g^{ab}`

This gives a CDH adversary whose advantage equals the DL advantage. -/

/-- DL adversary over abstract DDHDef: given a public key `g^a`,
    attempts to find the corresponding private key `a`. -/
abbrev DL_Adversary_DDH (W : Type) := W → SPComp W

/-- DL game over abstract DDHDef: sample a key pair `(a, g^a)`,
    give `g^a` to the adversary, check if the adversary's output `a'`
    yields the same public key (i.e., `ecdh(a', G) = g^a` conceptually,
    but since we only have `ecdh : W → W → W`, we check that the adversary
    can reproduce the DH shared secret).

    Concretely: sample `(a, g^a)` and `(b, g^b)`, give `g^a` to the
    adversary to get `a'`, then check `ecdh(a', g^b) = ecdh(a, g^b)`. -/
noncomputable def DL_Game_DDH (D : DDHDef W) (A : DL_Adversary_DDH W) : SPComp Bool := do
  let ⟨a, g_a⟩ ← D.keygen
  let ⟨_, g_b⟩ ← D.keygen
  let a' ← A g_a
  SPComp.pure (decide (D.ecdh a' g_b = D.ecdh a g_b))

/-- DL advantage over abstract DDHDef. -/
noncomputable def DL_Advantage_DDH (D : DDHDef W) (A : DL_Adversary_DDH W) : ℝ≥0∞ :=
  prTrue (DL_Game_DDH D A) Heap.empty

/-- Construct a CDH adversary from a DL adversary.

    Given a DL adversary that finds private keys from public keys:
    1. Receive `(g^a, g^b)`
    2. Run the DL adversary on `g^a` to get candidate private key `a'`
    3. Compute `ecdh(a', g^b)` as the alleged shared secret -/
noncomputable def cdh_of_dl_ddh (D : DDHDef W)
    (A_dl : DL_Adversary_DDH W) : CDH_Adversary W :=
  fun g_a _g_b => do
    let a' ← A_dl g_a
    SPComp.pure (D.ecdh a' _g_b)

/-- CDH ⟹ DL bound: any DL adversary yields a CDH adversary with
    at least as much advantage.

    `CDH_Advantage D (cdh_of_dl_ddh D A_dl) ≥ DL_Advantage_DDH D A_dl`

    Equivalently (for the standard "hardness implies hardness" direction):
    `DL_Advantage_DDH D A_dl ≤ CDH_Advantage D (cdh_of_dl_ddh D A_dl)` -/
theorem dl_le_cdh_ddh (D : DDHDef W)
    (A_dl : DL_Adversary_DDH W) :
    DL_Advantage_DDH D A_dl ≤ CDH_Advantage D (cdh_of_dl_ddh D A_dl) := by
  -- The two games are equal: both sample (a, g_a), (_, g_b), run A_dl(g_a)
  -- to get a', and check ecdh(a', g_b) = ecdh(a, g_b).
  -- CDH_Game inlines cdh_of_dl_ddh which does A_dl(g_a) >>= pure(ecdh(a', g_b)),
  -- then checks answer = target. After bind_assoc + pure_bind, this is identical.
  have hgame : DL_Game_DDH D A_dl = CDH_Game D (cdh_of_dl_ddh D A_dl) := by
    unfold DL_Game_DDH CDH_Game cdh_of_dl_ddh
    -- The CDH side has a nested bind: (A_dl g_a >>= fun a' => pure(ecdh a' g_b)) >>= fun answer => pure(decide(...))
    -- Flatten with bind_assoc then simplify pure_bind
    (simp only [CatCrypt.Core.SPComp.monad_bind_eq]; bind_vcgen)
  unfold DL_Advantage_DDH CDH_Advantage
  rw [hgame]

end CatCrypt.Crypto.Assumptions
