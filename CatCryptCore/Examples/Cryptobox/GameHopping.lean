/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.Cryptobox.Cryptobox

/-!
# Cryptobox Game-Hopping Chain

This file proves the game-hopping decomposition for the Cryptobox security proof,
replacing the monolithic `hdecomp` hypothesis with a transparent chain of game hops.

## Game-hopping chain

The proof proceeds through intermediate games:

```
  G₀ = PKAE(real)
  ≈ G₁ = PKAE_cc(real)         -- PKEY switching (FEL)
  ≈ G₂ = PKAE_cc(ideal)        -- NIKE + AE combined switch
  ≈ G₃ = PKAE(ideal)           -- PKEY unswitching (FEL)
```

where `PKAE_cc` uses collision-checking in the GEN oracle.

## Main results

* `PKAE_eq_PKEY_nocheck` - PKAE = PKEY(no-check) with reduction adversary (by rfl)
* `PKAE_cc_eq_PKEY_check` - PKAE_cc = PKEY(check) with reduction adversary (by rfl)
* `pkae_pkey_step` - PKEY switching step equals `pkeyAdvantage` of reduction
* `pkae_game_hopping` - Full three-step decomposition via triangle inequality
* `cryptobox_security_chain` - Main theorem with explicit game-hopping structure
* `cryptobox_security_full` - Full 4-component security bound

## Architecture

The **PKEY switching steps** (G₀ ↔ G₁ and G₂ ↔ G₃) are proved by showing
that PKAE and PKAE_cc are instances of the PKEY game with a reduction adversary.
These are **definitional equalities** — the reduction is the identity on oracle
structure, just routing enc/dec through the PKEY oracles.

The **middle step** (G₁ → G₂) combines NIKE switching and AE switching.
This is further decomposed into:
1. NIKE switching: replace real shared keys with random keys for honest-honest pairs
2. KEY structural: KEY(0) = KEY(1) when inputs are already random
3. AE switching: replace real encryption with ideal encryption (hybrid argument)

## References

* Dupressoir et al., "How Hard Can It Be?" (ASIACRYPT 2025)
* Dupressoir et al., "Bringing SSP to EasyCrypt" (CSF 2022)
* Myssenburg et al., Rocq SSProve Cryptobox
-/

namespace CatCrypt.Examples.Cryptobox

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable [CT : CryptoTypes] [LinearOrder CT.PK]

/-! ## PKAE with Collision-Checking GEN -/

/-- PKAE game with collision-checking GEN oracle.

    Identical to `PKAE` except `genOracle N true` is used instead of
    `genOracle N false`. This enables the FEL argument: PKAE and PKAE_cc
    agree unless a public key collision occurs during key generation. -/
noncomputable def PKAE_cc (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (b : Bool) (A : PKAEOracles → SPComp Bool) : SPComp Bool :=
  let pkeyO : PKEYOracles :=
    { gen := fun _ => genOracle N true,
      csetpk := csetpkOracle,
      getsk := getskOracle,
      honpk := honpkOracle }
  A { gen := pkeyO.gen,
      csetpk := pkeyO.csetpk,
      getsk := pkeyO.getsk,
      honpk := pkeyO.honpk,
      enc := pkaeEncOracle N E I b pkeyO,
      dec := pkaeDecOracle N E I b pkeyO }

/-! ## PKEY Reduction Adversary -/

/-- Reduction from PKAE to PKEY: wraps a PKAE adversary into a PKEY adversary.

    Given PKEY oracles (for key management), constructs the PKAE oracle interface
    by routing encryption/decryption through the given PKEY oracles.

    The parameter `b` controls whether encryption/decryption is real (`false`)
    or ideal (`true`).

    **Key property**: `PKEY N bGen (R_PKEY N E I bEnc A)` equals:
    - `PKAE N E I bEnc A` when `bGen = false` (no collision check)
    - `PKAE_cc N E I bEnc A` when `bGen = true` (collision check) -/
noncomputable def R_PKEY (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (b : Bool) (A : PKAEOracles → SPComp Bool) :
    PKEYOracles → SPComp Bool :=
  fun pkeyO =>
    A { gen := pkeyO.gen,
        csetpk := pkeyO.csetpk,
        getsk := pkeyO.getsk,
        honpk := pkeyO.honpk,
        enc := pkaeEncOracle N E I b pkeyO,
        dec := pkaeDecOracle N E I b pkeyO }

/-! ## Reduction Correctness

These show that PKAE and PKAE_cc are instances of the PKEY game
with the reduction adversary. The proofs are by definitional equality. -/

/-- PKAE = PKEY(no-check) with PKEY reduction adversary.

    This is the fundamental structural fact: `PKAE N E I b A` is exactly
    the PKEY game with no collision checking, where the adversary is
    `R_PKEY N E I b A`. -/
theorem PKAE_eq_PKEY_nocheck (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (b : Bool) (A : PKAEOracles → SPComp Bool) :
    PKAE N E I b A = PKEY N false (R_PKEY N E I b A) := by
  simp only [PKAE, PKEY, R_PKEY]

/-- PKAE_cc = PKEY(collision-check) with PKEY reduction adversary. -/
theorem PKAE_cc_eq_PKEY_check (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (b : Bool) (A : PKAEOracles → SPComp Bool) :
    PKAE_cc N E I b A = PKEY N true (R_PKEY N E I b A) := by
  simp only [PKAE_cc, PKEY, R_PKEY]

/-! ## PKEY Switching Steps -/

set_option linter.unusedSectionVars false in
/-- Advantage is symmetric: `Advantage G₀ G₁ = Advantage G₁ G₀`. -/
private theorem advantage_comm (G₀ G₁ : SPComp Bool) :
    Advantage G₀ G₁ = Advantage G₁ G₀ := by
  unfold Advantage; exact max_comm _ _

/-- The distance between PKAE and PKAE_cc equals the PKEY advantage
    of the reduction adversary.

    This is the key reduction: the PKEY switching step in the game-hopping
    chain is exactly the PKEY advantage for the appropriate adversary. -/
theorem pkae_pkey_step (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (b : Bool) (A : PKAEOracles → SPComp Bool) :
    Advantage (PKAE N E I b A) (PKAE_cc N E I b A) =
    pkeyAdvantage N (R_PKEY N E I b A) := by
  unfold pkeyAdvantage
  rw [PKAE_eq_PKEY_nocheck, PKAE_cc_eq_PKEY_check]

/-- The distance from PKAE_cc to PKAE is also the PKEY advantage (by symmetry). -/
theorem pkae_pkey_step_rev (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (b : Bool) (A : PKAEOracles → SPComp Bool) :
    Advantage (PKAE_cc N E I b A) (PKAE N E I b A) =
    pkeyAdvantage N (R_PKEY N E I b A) := by
  rw [advantage_comm, pkae_pkey_step]

/-! ## Game-Hopping Chain -/

/-- **Game-hopping decomposition for PKAE.**

    The PKAE advantage decomposes into three steps via triangle inequality:

    1. **PKEY switching (real side)**: `PKAE(real) → PKAE_cc(real)`
       Advantage = `pkeyAdvantage N (R_PKEY false A)` (collision bound)

    2. **Middle step (NIKE + AE)**: `PKAE_cc(real) → PKAE_cc(ideal)`
       Advantage captures both NIKE switching and AE switching

    3. **PKEY switching (ideal side)**: `PKAE_cc(ideal) → PKAE(ideal)`
       Advantage = `pkeyAdvantage N (R_PKEY true A)` (collision bound)

    The PKEY steps are proved reductions. The middle step is the
    "hard" part requiring NIKE and AE security arguments. -/
theorem pkae_game_hopping (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool) :
    pkaeAdvantage N E I A ≤
      pkeyAdvantage N (R_PKEY N E I false A) +
      Advantage (PKAE_cc N E I false A) (PKAE_cc N E I true A) +
      pkeyAdvantage N (R_PKEY N E I true A) := by
  unfold pkaeAdvantage
  calc Advantage (PKAE N E I false A) (PKAE N E I true A)
      ≤ Advantage (PKAE N E I false A) (PKAE_cc N E I false A)
        + Advantage (PKAE_cc N E I false A) (PKAE N E I true A) :=
        advantage_triangle _ _ _
    _ ≤ Advantage (PKAE N E I false A) (PKAE_cc N E I false A)
        + (Advantage (PKAE_cc N E I false A) (PKAE_cc N E I true A)
           + Advantage (PKAE_cc N E I true A) (PKAE N E I true A)) := by
        gcongr; exact advantage_triangle _ _ _
    _ = pkeyAdvantage N (R_PKEY N E I false A)
        + (Advantage (PKAE_cc N E I false A) (PKAE_cc N E I true A)
           + pkeyAdvantage N (R_PKEY N E I true A)) := by
        rw [pkae_pkey_step, pkae_pkey_step_rev]
    _ = _ := by rw [add_assoc]

/-! ## Main Security Theorem (Chain Version) -/

/-- **Cryptobox security theorem (game-hopping chain version).**

    The PKAE advantage is bounded by `2 * pkey_eps + middle_eps`, where:
    - `pkey_eps` bounds the PKEY advantage for both reduction adversaries
    - `middle_eps` bounds the NIKE + AE combined switching step

    Compared to `cryptobox_security`, this version:
    1. **Proves the PKEY reductions** (not hypothesized)
    2. **Makes the game-hopping structure explicit**
    3. **Isolates** the remaining proof obligations (PKEY FEL, NIKE+AE) -/
theorem cryptobox_security_chain
    (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool)
    (pkey_eps middle_eps : ℝ≥0∞)
    -- PKEY switching bounds (from FEL / collision bound)
    (h_pkey_real : pkeyAdvantage N (R_PKEY N E I false A) ≤ pkey_eps)
    (h_pkey_ideal : pkeyAdvantage N (R_PKEY N E I true A) ≤ pkey_eps)
    -- Middle step: NIKE + AE combined switching
    (h_middle : Advantage (PKAE_cc N E I false A) (PKAE_cc N E I true A) ≤ middle_eps) :
    pkaeAdvantage N E I A ≤ 2 * pkey_eps + middle_eps :=
  calc pkaeAdvantage N E I A
      ≤ pkeyAdvantage N (R_PKEY N E I false A)
        + Advantage (PKAE_cc N E I false A) (PKAE_cc N E I true A)
        + pkeyAdvantage N (R_PKEY N E I true A) :=
        pkae_game_hopping N E I A
    _ ≤ pkey_eps + middle_eps + pkey_eps :=
        add_le_add (add_le_add h_pkey_real h_middle) h_pkey_ideal
    _ = 2 * pkey_eps + middle_eps := by ring

/-! ## Middle Step Decomposition

The middle step `Advantage (PKAE_cc false) (PKAE_cc true)` captures the
combined NIKE switching and AE switching. It can be further decomposed
into NIKE and AE contributions.

### Conceptual decomposition

```
  PKAE_cc(real)
  ≈ PKAE_nikeSwitch           -- NIKE: real → random shared keys
  = PKAE_nikeSwitch           -- KEY structural: random input → KEY(0)=KEY(1)
  ≈ PKAE_cc(ideal)            -- AE: real → ideal encryption
```

### NIKE switching

In `PKAE_cc(real)`, the enc/dec oracles compute shared keys via `N.sharedkey`.
After NIKE switching, honest-honest pairs use uniformly random shared keys
instead. This requires:
- Storing sampled shared keys per session (using `nikeKeysLoc`)
- The NIKE advantage bounds the distinguishing probability

### AE switching (hybrid argument)

After NIKE switching, shared keys for honest-honest sessions are random.
The AE step switches from real encryption to ideal (log-based) encryption.
This is decomposed via a hybrid argument over sessions:
- Each session contributes at most `sae_eps(i)` distinguishing probability
- Total AE advantage ≤ `Σ sae_eps(i)` -/

/-- The middle step advantage: distance between collision-checking PKAE
    with real vs ideal enc/dec. -/
noncomputable def middleAdvantage (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (A : PKAEOracles → SPComp Bool) : ℝ≥0∞ :=
  Advantage (PKAE_cc N E I false A) (PKAE_cc N E I true A)

/-! ### NIKE-Switched Intermediate Game -/

/-- Get or sample a random shared key for a session.

    Looks up the shared key cache (`nikeKeysLoc`); if found, returns the
    cached key. Otherwise, samples a fresh random key, stores it, and
    returns it. This ensures each session gets a consistent random key
    across multiple enc/dec calls. -/
noncomputable def getOrSampleKey (sid : SID) : SPComp CT.SharedKey := do
  let keys ← SPComp.get nikeKeysLoc
  match keys sid with
  | some k => SPComp.pure k
  | none => do
    let k ← SPComp.sample CT.SharedKey
    SPComp.set nikeKeysLoc
      (Function.update keys sid (some k) : SID → Option CT.SharedKey)
    SPComp.pure k

/-- PKAE with collision-checking GEN and NIKE-switched shared keys.

    For **honest-honest** pairs: shared keys are sampled uniformly at random
    (cached per session via `nikeKeysLoc`), then used with real encryption
    (`E.enc`, `E.dec`).

    For **corrupt** pairs: shared keys are computed via `N.sharedkey` (real),
    then used with real encryption.

    This is the intermediate game between:
    - `PKAE_cc false` (all keys real, all enc real)
    - `PKAE_cc true` (honest keys unused, honest enc ideal)

    The NIKE switching step (`PKAE_cc false → PKAE_nikeSwitch`) replaces
    real shared keys with random keys for honest-honest pairs.
    The AE switching step (`PKAE_nikeSwitch → PKAE_cc true`) replaces
    real encryption with ideal encryption for honest sessions. -/
noncomputable def PKAE_nikeSwitch (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool) : SPComp Bool :=
  let pkeyO : PKEYOracles :=
    { gen := fun _ => genOracle N true,
      csetpk := csetpkOracle,
      getsk := getskOracle,
      honpk := honpkOracle }
  A { gen := pkeyO.gen,
      csetpk := pkeyO.csetpk,
      getsk := pkeyO.getsk,
      honpk := pkeyO.honpk,
      enc := fun pk_s pk_r m n => do
        let hon_s ← pkeyO.honpk pk_s
        let hon_r ← pkeyO.honpk pk_r
        let sk_s ← pkeyO.getsk pk_s
        if hon_s && hon_r then do
          let k ← getOrSampleKey (sortSID pk_s pk_r)
          E.enc (I.encode k) m n
        else do
          let k := N.sharedkey pk_r sk_s
          E.enc (I.encode k) m n,
      dec := fun pk_r pk_s c n => do
        let hon_s ← pkeyO.honpk pk_s
        let hon_r ← pkeyO.honpk pk_r
        let sk_r ← pkeyO.getsk pk_r
        if hon_s && hon_r then do
          let k ← getOrSampleKey (sortSID pk_s pk_r)
          E.dec (I.encode k) c n
        else do
          let k := N.sharedkey pk_s sk_r
          E.dec (I.encode k) c n }

/-- The middle step decomposes into NIKE switching + AE switching
    via the NIKE-switched intermediate game. -/
theorem middle_step_triangle (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (A : PKAEOracles → SPComp Bool) :
    middleAdvantage N E I A ≤
      Advantage (PKAE_cc N E I false A) (PKAE_nikeSwitch N E I A) +
      Advantage (PKAE_nikeSwitch N E I A) (PKAE_cc N E I true A) := by
  unfold middleAdvantage
  exact advantage_triangle _ _ _

/-- The NIKE switching advantage: distance between real shared keys
    and random shared keys for honest-honest pairs. -/
noncomputable def nikeStepAdvantage (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (A : PKAEOracles → SPComp Bool) : ℝ≥0∞ :=
  Advantage (PKAE_cc N E I false A) (PKAE_nikeSwitch N E I A)

/-- The AE switching advantage: distance between real encryption
    and ideal encryption when shared keys are already random. -/
noncomputable def aeStepAdvantage (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (A : PKAEOracles → SPComp Bool) : ℝ≥0∞ :=
  Advantage (PKAE_nikeSwitch N E I A) (PKAE_cc N E I true A)

/-- Middle step bounded by NIKE + AE step advantages. -/
theorem middle_bounded_by_steps
    (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool) :
    middleAdvantage N E I A ≤
      nikeStepAdvantage N E I A + aeStepAdvantage N E I A :=
  middle_step_triangle N E I A

/-! ## Full Decomposition

Combining the game-hopping chain with the middle step decomposition
gives the full security bound. -/

/-- **Full Cryptobox security bound with explicit game-hopping structure.**

    Decomposes PKAE advantage into:
    - `2 * pkey_eps`: Two PKEY switching steps (collision bounds)
    - `nike_eps`: NIKE switching (shared key indistinguishability)
    - `ae_eps`: AE switching (encryption indistinguishability)

    This is the most structured version of the Cryptobox security theorem.
    Each hypothesis corresponds to a single, well-defined proof obligation:

    1. `h_pkey_real/ideal`: Bound PKEY collision probability (FEL)
    2. `h_nike`: Bound NIKE advantage (DDH or similar assumption)
    3. `h_ae`: Bound AE advantage (hybrid argument over sessions) -/
theorem cryptobox_security_full
    (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool)
    (pkey_eps nike_eps ae_eps : ℝ≥0∞)
    -- PKEY collision bounds
    (h_pkey_real : pkeyAdvantage N (R_PKEY N E I false A) ≤ pkey_eps)
    (h_pkey_ideal : pkeyAdvantage N (R_PKEY N E I true A) ≤ pkey_eps)
    -- NIKE switching: real → random shared keys for honest-honest pairs
    (h_nike : nikeStepAdvantage N E I A ≤ nike_eps)
    -- AE switching: real → ideal encryption when keys are random
    (h_ae : aeStepAdvantage N E I A ≤ ae_eps) :
    pkaeAdvantage N E I A ≤ 2 * pkey_eps + nike_eps + ae_eps := by
  have h_middle : middleAdvantage N E I A ≤ nike_eps + ae_eps :=
    (middle_bounded_by_steps N E I A).trans (add_le_add h_nike h_ae)
  calc pkaeAdvantage N E I A
      ≤ 2 * pkey_eps + middleAdvantage N E I A :=
        cryptobox_security_chain N E I A pkey_eps (middleAdvantage N E I A)
          h_pkey_real h_pkey_ideal le_rfl
    _ ≤ 2 * pkey_eps + (nike_eps + ae_eps) :=
        add_le_add le_rfl h_middle
    _ = 2 * pkey_eps + nike_eps + ae_eps := by rw [add_assoc]

/-! ## Corollaries

Specializations of the full security theorem for common scenarios. -/

/-- When the PKEY collision bound is zero (e.g., infinite key space),
    the PKAE advantage reduces to just NIKE + AE advantages. -/
theorem cryptobox_security_no_collision
    (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool)
    (nike_eps ae_eps : ℝ≥0∞)
    (h_pkey_real : pkeyAdvantage N (R_PKEY N E I false A) = 0)
    (h_pkey_ideal : pkeyAdvantage N (R_PKEY N E I true A) = 0)
    (h_nike : nikeStepAdvantage N E I A ≤ nike_eps)
    (h_ae : aeStepAdvantage N E I A ≤ ae_eps) :
    pkaeAdvantage N E I A ≤ nike_eps + ae_eps := by
  have := cryptobox_security_full N E I A 0 nike_eps ae_eps
    (le_of_eq h_pkey_real) (le_of_eq h_pkey_ideal) h_nike h_ae
  simp only [mul_zero, zero_add] at this
  exact this

/-- When NIKE and AE are perfectly secure (e.g., information-theoretic),
    the PKAE advantage is bounded purely by the collision probability. -/
theorem cryptobox_security_collision_only
    (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool)
    (pkey_eps : ℝ≥0∞)
    (h_pkey_real : pkeyAdvantage N (R_PKEY N E I false A) ≤ pkey_eps)
    (h_pkey_ideal : pkeyAdvantage N (R_PKEY N E I true A) ≤ pkey_eps)
    (h_nike : nikeStepAdvantage N E I A = 0)
    (h_ae : aeStepAdvantage N E I A = 0) :
    pkaeAdvantage N E I A ≤ 2 * pkey_eps := by
  have := cryptobox_security_full N E I A pkey_eps 0 0
    h_pkey_real h_pkey_ideal (le_of_eq h_nike) (le_of_eq h_ae)
  simp only [add_zero] at this
  exact this

/-! ## Proof Obligation Summary

The `cryptobox_security_full` theorem reduces the PKAE security proof to
**four independent proof obligations**. Here we document what each requires:

### 1. PKEY collision bound (`h_pkey_real`, `h_pkey_ideal`)

**Statement**: `pkeyAdvantage N (R_PKEY N E I b A) ≤ pkey_eps`

**Proof approach**: FEL (Failure Event Lemma)
- Define bad event: a GEN call produces a pk that matches an existing honest/corrupt key
- Show `PKEY N false (R_PKEY b A)` and `PKEY N true (R_PKEY b A)` agree when no collision
- Bound collision probability: ≤ `q_gen * q_csetpk / |PK|` (birthday-type bound)
- Apply `advantage_le_prBad` from `FailureEvent.lean`

**Required infrastructure**: Oracle composition reasoning (shared prefix argument)

**Status**: Reduction proven (R_PKEY), FEL structure documented (PKEY.lean),
concrete probability bound requires oracle-level analysis.

### 2. NIKE switching (`h_nike`)

**Statement**: `nikeStepAdvantage N E I A ≤ nike_eps`

**Proof approach**: Reduction to NIKE game
- Construct adversary `R_NIKE` that uses NIKE sharedkey oracle for key computation
- Show `PKAE_cc false A` ≈ `GNIKE N false pkeyO (R_NIKE A)` (structural equivalence)
- Show `PKAE_nikeSwitch A` ≈ `GNIKE N true pkeyO (R_NIKE A)` (structural equivalence)
- Conclude: `nikeStepAdvantage ≤ nikeAdvantage N pkeyO (R_NIKE A)`

**Required infrastructure**: Shared key caching equivalence (real keys are deterministic,
so caching doesn't change behavior; random keys need consistency).

**Status**: PKAE_nikeSwitch defined with explicit caching mechanism.
Reduction requires structural equivalence between inline and cached key computation.

### 3. AE switching (`h_ae`)

**Statement**: `aeStepAdvantage N E I A ≤ ae_eps`

**Proof approach**: Hybrid argument over sessions
- Define hybrid game `H(i)`: first `i` honest sessions use ideal encryption,
  remaining use real encryption
- Show `H(0)` = PKAE_nikeSwitch, `H(q)` = PKAE_cc true (up to KEY structural equiv)
- Bound per-step: `Advantage H(i) H(i+1) ≤ saeAdvantage i`
- Apply triangle inequality: `ae_eps = Σ saeAdvantage(i)`

**Required infrastructure**: Per-session oracle isolation, AE→SAE reduction.

**Status**: ae_hybrid_bound proven in Cryptobox.lean (triangle + sum_le_sum).
Per-session SAE reduction defined (R_GSAE). Structural equivalences needed.
-/

/-! ### NIKE Reduction Architecture

The NIKE switching step (`PKAE_cc false → PKAE_nikeSwitch`) is proven via
reduction to the NIKE game:

```
  PKAE_cc false ≈ GNIKE N false pkeyO (R_NIKE A) ≈? GNIKE N true pkeyO (R_NIKE A) ≈ PKAE_nikeSwitch
                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                  This gap is the caching equivalence
```

The caching equivalence states that `GNIKE N false` (which caches deterministic
shared keys) produces the same adversary-observable behavior as inline computation
(which doesn't cache). This follows from:

1. `N.sharedkey` is a pure function → cache always contains the correct value
2. The extra heap writes to `nikeKeysLoc`/`nikeHonestLoc` don't affect any oracle
   the adversary can query (PKEY oracles read `pkHonestLoc`/`skStoreLoc`/`pkCorruptLoc`,
   not NIKE locations)

Formally proving this requires "heap frame" reasoning showing that oracle behavior
is independent of locations they don't read. This is left as future work.
-/

/-! ## NIKE Reduction Adversary -/

/-- Adapted NIKE reduction that properly threads PKEY oracles.

    Given PKEY oracles and a NIKE oracle, constructs a PKAE oracle interface.
    The enc/dec oracles check honesty:
    - If both parties are honest: query the NIKE oracle for the shared key
    - If either is corrupt: compute shared key directly via `N.sharedkey`

    This matches the structure of `PKAE_cc`/`PKAE_nikeSwitch`, where
    the honest-honest case uses a potentially different key source.

    Compare with `R_GNIKE` in `Cryptobox.lean`, which routes ALL pairs
    through the NIKE oracle (no honesty check). This adapted version
    is needed because the NIKE game only provides different behavior
    for honest-honest pairs; corrupt pairs always use `N.sharedkey`. -/
noncomputable def R_NIKE (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool) :
    PKEYOracles → NIKEOracles → SPComp Bool := fun pkeyO nikeO =>
  A { gen := pkeyO.gen,
      csetpk := pkeyO.csetpk,
      getsk := pkeyO.getsk,
      honpk := pkeyO.honpk,
      enc := fun pk_s pk_r m n => do
        let hon_s ← pkeyO.honpk pk_s
        let hon_r ← pkeyO.honpk pk_r
        let sk_s ← pkeyO.getsk pk_s
        if hon_s && hon_r then do
          let k ← nikeO.sharedkey pk_s pk_r
          E.enc (I.encode k) m n
        else do
          let k := N.sharedkey pk_r sk_s
          E.enc (I.encode k) m n,
      dec := fun pk_r pk_s c n => do
        let hon_s ← pkeyO.honpk pk_s
        let hon_r ← pkeyO.honpk pk_r
        let sk_r ← pkeyO.getsk pk_r
        if hon_s && hon_r then do
          let k ← nikeO.sharedkey pk_s pk_r
          E.dec (I.encode k) c n
        else do
          let k := N.sharedkey pk_s sk_r
          E.dec (I.encode k) c n }

/-! ## GNIKE Instantiation with R_NIKE -/

/-- `GNIKE N b pkeyO (R_NIKE N E I A pkeyO)` unfolds to `R_NIKE` applied to
    the `sharedkeyOracle N b pkeyO` — this is definitional.

    This confirms that the NIKE game with the reduction adversary correctly
    threads the PKEY oracles and the shared key oracle through the PKAE
    oracle interface constructed by `R_NIKE`. -/
theorem GNIKE_R_NIKE_unfold (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (A : PKAEOracles → SPComp Bool) (b : Bool)
    (pkeyO : PKEYOracles) :
    GNIKE N b pkeyO (R_NIKE N E I A) =
      R_NIKE N E I A pkeyO { sharedkey := sharedkeyOracle N b pkeyO } := by
  rfl

/-- The NIKE advantage of the reduction adversary `R_NIKE` measures
    the adversary's ability to distinguish real from random shared keys
    when routed through the PKAE oracle interface.

    This is the "right-hand side" of the NIKE reduction:
    `nikeStepAdvantage N E I A ≤ nikeAdvantage N pkeyO (R_NIKE N E I A)`
    modulo the caching equivalence gap. -/
noncomputable def nikeReductionAdvantage (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (A : PKAEOracles → SPComp Bool)
    (pkeyO : PKEYOracles) : ℝ≥0∞ :=
  nikeAdvantage N pkeyO (R_NIKE N E I A)

/-! ## Deterministic Caching Lemma -/

set_option linter.unusedSectionVars false in
/-- A general principle: if a function `f` is deterministic (pure),
    then caching its result doesn't change the return value.

    Specifically, for a map `cache : K → Option V` and a function `f : K → V`:
    - Cache miss: compute `f(k)`, store in cache, return `f(k)`
    - Cache hit: return `cache[k]`

    If `cache[k] = some (f k)` for all cached entries (invariant),
    then both paths return `f(k)`.

    This is the key reasoning principle for the NIKE caching equivalence:
    `N.sharedkey` is deterministic, so the `sharedkeyOracle N false`
    (which caches the result of `N.sharedkey`) returns the same value
    as inline computation of `N.sharedkey`. -/
theorem cache_hit_eq_compute {K V : Type} [DecidableEq K]
    (f : K → V) (cache : K → Option V) (k : K)
    (h_inv : ∀ k' v, cache k' = some v → v = f k') :
    (match cache k with
    | some v => v
    | none => f k) = f k := by
  cases h : cache k with | none => rfl | some v => exact h_inv k v h

set_option linter.unusedSectionVars false in
/-- Variant with `Option.getD`: looking up `k` in a cache that satisfies
    the invariant and defaulting to `f k` always yields `f k`. -/
theorem cache_getD_eq_compute {K V : Type} [DecidableEq K]
    (f : K → V) (cache : K → Option V) (k : K)
    (h_inv : ∀ k' v, cache k' = some v → v = f k') :
    (cache k).getD (f k) = f k := by
  cases h : cache k with | none => rfl | some v => exact h_inv k v h

/-! ## NIKE Reduction Structure -/

/-- The NIKE switching step is bounded by the NIKE reduction advantage plus a
    caching gap, obtained by inserting the two reduction games
    `GNIKE N false pkeyO (R_NIKE …)` and `GNIKE N true pkeyO (R_NIKE …)` into the
    chain and applying the triangle inequality twice:

    ```
      PKAE_cc false → GNIKE N false (R_NIKE) → GNIKE N true (R_NIKE) → PKAE_nikeSwitch
    ```

    The middle term is `nikeReductionAdvantage`. The two boundary terms are the
    caching gap: the distance between inline shared-key computation
    (`PKAE_cc false`, `PKAE_nikeSwitch`) and the cached computation with extra
    heap writes to `nikeKeysLoc`/`nikeHonestLoc` performed by
    `sharedkeyOracle`. Each boundary term is zero exactly when the extra heap
    writes are invisible to the adversary's PKEY oracle queries — for the ideal
    side (`GNIKE N true`) both games sample and cache random keys identically. -/
theorem nikeStep_structure (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (A : PKAEOracles → SPComp Bool)
    (pkeyO : PKEYOracles) :
    nikeStepAdvantage N E I A ≤
      Advantage (PKAE_cc N E I false A) (GNIKE N false pkeyO (R_NIKE N E I A))
        + nikeReductionAdvantage N E I A pkeyO
        + Advantage (GNIKE N true pkeyO (R_NIKE N E I A)) (PKAE_nikeSwitch N E I A) := by
  unfold nikeStepAdvantage nikeReductionAdvantage nikeAdvantage
  calc Advantage (PKAE_cc N E I false A) (PKAE_nikeSwitch N E I A)
      ≤ Advantage (PKAE_cc N E I false A) (GNIKE N true pkeyO (R_NIKE N E I A))
          + Advantage (GNIKE N true pkeyO (R_NIKE N E I A)) (PKAE_nikeSwitch N E I A) :=
        advantage_triangle _ _ _
    _ ≤ Advantage (PKAE_cc N E I false A) (GNIKE N false pkeyO (R_NIKE N E I A))
          + Advantage (GNIKE N false pkeyO (R_NIKE N E I A))
              (GNIKE N true pkeyO (R_NIKE N E I A))
          + Advantage (GNIKE N true pkeyO (R_NIKE N E I A)) (PKAE_nikeSwitch N E I A) := by
        gcongr
        exact advantage_triangle _ _ _

/-- The NIKE step advantage is bounded by the NIKE reduction advantage
    plus a "caching gap" term that accounts for the difference between
    inline computation and cached computation with extra heap writes.

    In the ideal case (GNIKE N true), the caching gap is zero because
    both `PKAE_nikeSwitch` and `GNIKE N true` via `R_NIKE` sample random
    keys and cache them in `nikeKeysLoc`.

    In the real case (GNIKE N false), the caching gap captures the
    difference between:
    - `PKAE_cc false`: computes `N.sharedkey pk_r sk_s` inline (no cache)
    - `GNIKE N false` via `R_NIKE`: computes `N.sharedkey pk_r sk_s`,
      caches in `nikeKeysLoc`, also writes `nikeHonestLoc`

    Since `N.sharedkey` is deterministic, the return values are identical;
    only the heap state differs. The caching gap is therefore bounded by
    the probability that the extra heap writes become observable. -/
theorem nikeStep_bounded (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (A : PKAEOracles → SPComp Bool)
    (pkeyO : PKEYOracles)
    (nike_eps caching_gap : ℝ≥0∞)
    -- NIKE advantage bound
    (h_nike : nikeReductionAdvantage N E I A pkeyO ≤ nike_eps)
    -- Caching gap: accounts for difference between inline and cached computation
    (h_cache : nikeStepAdvantage N E I A ≤
      nikeReductionAdvantage N E I A pkeyO + caching_gap) :
    nikeStepAdvantage N E I A ≤ nike_eps + caching_gap :=
  h_cache.trans (add_le_add h_nike le_rfl)

/-- When the caching gap is zero, the NIKE step advantage equals
    the NIKE reduction advantage. This is the expected case because:
    - `N.sharedkey` is deterministic → caching doesn't change return values
    - Extra heap writes to `nikeKeysLoc`/`nikeHonestLoc` are invisible
      to the adversary's PKEY oracle queries

    The hypothesis `h_cache_zero` formalizes "the caching gap is zero",
    meaning the NIKE game with `R_NIKE` exactly equals the direct games. -/
theorem nikeStep_eq_reduction (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (A : PKAEOracles → SPComp Bool)
    (pkeyO : PKEYOracles)
    (h_cache_zero : nikeStepAdvantage N E I A ≤
      nikeReductionAdvantage N E I A pkeyO) :
    nikeStepAdvantage N E I A ≤ nikeReductionAdvantage N E I A pkeyO :=
  h_cache_zero

/-! ## Full Security with NIKE Reduction

Combining `cryptobox_security_full` with the NIKE reduction gives a
version where the NIKE bound comes from a concrete reduction adversary. -/

/-- **Cryptobox security with explicit NIKE reduction.**

    This combines the full game-hopping decomposition with the NIKE reduction
    adversary, making explicit that the NIKE step advantage is bounded by
    the NIKE advantage of the reduction `R_NIKE`.

    Compared to `cryptobox_security_full`, this version:
    1. Names the NIKE reduction adversary explicitly
    2. Connects the abstract `nike_eps` to the concrete `nikeAdvantage`
    3. Includes the caching gap hypothesis that bridges the structural difference -/
theorem cryptobox_security_with_nike_reduction
    (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool)
    (pkeyO : PKEYOracles)
    (pkey_eps nike_eps caching_gap ae_eps : ℝ≥0∞)
    -- PKEY collision bounds
    (h_pkey_real : pkeyAdvantage N (R_PKEY N E I false A) ≤ pkey_eps)
    (h_pkey_ideal : pkeyAdvantage N (R_PKEY N E I true A) ≤ pkey_eps)
    -- NIKE reduction: bound via concrete adversary
    (h_nike : nikeReductionAdvantage N E I A pkeyO ≤ nike_eps)
    -- Caching equivalence: gap between inline and cached computation
    (h_cache : nikeStepAdvantage N E I A ≤
      nikeReductionAdvantage N E I A pkeyO + caching_gap)
    -- AE switching bound
    (h_ae : aeStepAdvantage N E I A ≤ ae_eps) :
    pkaeAdvantage N E I A ≤ 2 * pkey_eps + (nike_eps + caching_gap) + ae_eps := by
  have h_nike_step : nikeStepAdvantage N E I A ≤ nike_eps + caching_gap :=
    nikeStep_bounded N E I A pkeyO nike_eps caching_gap h_nike h_cache
  exact cryptobox_security_full N E I A pkey_eps (nike_eps + caching_gap) ae_eps
    h_pkey_real h_pkey_ideal h_nike_step h_ae

/-- **Simplified version when the caching gap is zero.**

    When `N.sharedkey` is deterministic and extra heap writes are provably
    invisible (the expected case), the caching gap vanishes and we get the
    clean four-component bound. -/
theorem cryptobox_security_with_nike_reduction_no_gap
    (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool)
    (pkeyO : PKEYOracles)
    (pkey_eps nike_eps ae_eps : ℝ≥0∞)
    -- PKEY collision bounds
    (h_pkey_real : pkeyAdvantage N (R_PKEY N E I false A) ≤ pkey_eps)
    (h_pkey_ideal : pkeyAdvantage N (R_PKEY N E I true A) ≤ pkey_eps)
    -- NIKE reduction: bound via concrete adversary
    (h_nike : nikeReductionAdvantage N E I A pkeyO ≤ nike_eps)
    -- Caching gap is zero (inline ≈ cached)
    (h_cache : nikeStepAdvantage N E I A ≤ nikeReductionAdvantage N E I A pkeyO)
    -- AE switching bound
    (h_ae : aeStepAdvantage N E I A ≤ ae_eps) :
    pkaeAdvantage N E I A ≤ 2 * pkey_eps + nike_eps + ae_eps := by
  have h_nike_step : nikeStepAdvantage N E I A ≤ nike_eps :=
    h_cache.trans h_nike
  exact cryptobox_security_full N E I A pkey_eps nike_eps ae_eps
    h_pkey_real h_pkey_ideal h_nike_step h_ae

end CatCrypt.Examples.Cryptobox
