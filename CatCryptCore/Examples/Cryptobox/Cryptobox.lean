/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.Cryptobox.Scheme
import CatCryptCore.Examples.Cryptobox.PKEY
import CatCryptCore.Examples.Cryptobox.NIKE
import CatCryptCore.Examples.Cryptobox.KEY
import CatCryptCore.Examples.Cryptobox.SAE
import CatCryptCore.Examples.Cryptobox.AE
import CatCryptCore.Crypto.Advantage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Cryptobox: Main Security Theorem

This file states the main security theorem for the Cryptobox construction
(NaCl's `crypto_box`), which combines a Non-Interactive Key Exchange (NIKE,
e.g., X25519) with a Nonce-Based Symmetric Encryption Scheme (NBSES,
e.g., XSalsa20-Poly1305) to achieve Public-Key Authenticated Encryption (PKAE).

## Game-hopping chain

The proof proceeds by a sequence of game hops:

```
  G0: PKAE(real)
    = PKEY(0) ∘ NIKE(0) ∘ KEY(0) ∘ AE(0)     -- decomposition
  ≈ PKEY(1) ∘ NIKE(0) ∘ KEY(0) ∘ AE(0)       -- Step 1: PKEY switching (FEL)
  ≈ PKEY(1) ∘ NIKE(1) ∘ KEY(0) ∘ AE(0)       -- Step 2: NIKE reduction
    = PKEY(1) ∘ NIKE(1) ∘ KEY(1) ∘ AE(0)     -- Step 3: KEY(0) = KEY(1) (structural)
  ≈ PKEY(1) ∘ NIKE(1) ∘ KEY(1) ∘ AE(1)       -- Step 4: AE hybrid argument
    = PKAE(ideal)                              -- recomposition
```

### Advantage bound

```
  Adv[PKAE] ≤ Adv[PKEY] + Adv[NIKE] + Adv[AE]
            ≤ 2 · q_gen · q_csetpk · (1 / |PK|)    -- FEL collision bound
              + nike_eps                              -- NIKE advantage
              + Σ_{i < q} sae_eps(i)                 -- hybrid sum of SAE advantages
```

## Architecture

The `hdecomp` hypothesis in the main theorem corresponds to the **three structural
equivalences that are ADMITTED in the Rocq SSProve formalization**:
1. PKAE(real) decomposes into PKEY(0) ∘ NIKE(0) ∘ KEY(0) ∘ AE(0)
2. PKAE(ideal) decomposes into PKEY(1) ∘ NIKE(1) ∘ KEY(1) ∘ AE(1)
3. KEY(0) = KEY(1) structurally

Given these decompositions (taken as hypotheses), the security bound follows from
the triangle inequality and monotonicity of addition — which we prove.

## Improved Version

The `cryptobox_security_full` theorem in `GameHopping.lean` improves on
`cryptobox_security` by:
- **Proving** the PKEY reductions (not hypothesized) via definitional equality
- Decomposing into 4 independent, transparent proof obligations
  (`h_pkey_real`, `h_pkey_ideal`, `h_nike`, `h_ae`)
- Making the game-hopping chain explicit with intermediate games

### Relationship

```
  cryptobox_security       -- monolithic hdecomp hypothesis (this file)
  cryptobox_security_full  -- 4 independent hypotheses, PKEY proven (GameHopping.lean)
    ← cryptobox_security_chain  -- 3-step game-hopping with triangle inequality
      ← pkae_game_hopping       -- PKEY reductions proven by definitional equality
        ← PKAE_eq_PKEY_nocheck  -- PKAE = PKEY(no-check) ∘ R_PKEY (by rfl)
        ← PKAE_cc_eq_PKEY_check -- PKAE_cc = PKEY(check) ∘ R_PKEY (by rfl)
```

See `GameHopping.lean` for the state-of-the-art version.

## References

* Dupressoir et al., "Bringing SSP to EasyCrypt — A Security Proof for
  Cryptobox" (CSF 2022)
* Dupressoir et al., "How Hard Can It Be?" (ASIACRYPT 2025)
* Myssenburg et al., Rocq SSProve Cryptobox (nominal-ssprove)
* Bernstein, Lange, Schwabe, "NaCl: Networking and Cryptography library"
-/

namespace CatCrypt.Examples.Cryptobox

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Crypto
open scoped ENNReal

variable [CT : CryptoTypes] [LinearOrder CT.PK]

/-! ## PKAE Oracle Interface

The target security notion. The PKAE game gives the adversary access to
PKEY oracles plus encryption/decryption parameterized by `b : Bool`:
- `b = false` (real): use the cryptobox construction
- `b = true` (ideal): encryption returns random ciphertexts, decryption
  uses a log -/

/-- Oracle interface for the PKAE game.
    Combines PKEY oracles with encryption/decryption. -/
structure PKAEOracles where
  gen : Unit → SPComp CT.PK
  csetpk : CT.PK → SPComp Unit
  getsk : CT.PK → SPComp CT.SK
  honpk : CT.PK → SPComp Bool
  enc : CT.PK → CT.PK → CT.M → CT.Nonce → SPComp CT.C
  dec : CT.PK → CT.PK → CT.C → CT.Nonce → SPComp (Option CT.M)

/-! ### PKAE Heap Locations -/

/-- Per-session encryption log for ideal PKAE, indexed by `(SID, Nonce)`. -/
@[reducible] noncomputable def pkaeLogLoc : Location :=
  ⟨600, (SID × CT.Nonce) → Option (CT.M × CT.C)⟩

/-! ### PKAE Oracle Definitions -/

/-- PKAE encryption oracle.
    - `b = false` (real): encrypt using the cryptobox construction
    - `b = true` (ideal): sample a random ciphertext and log the pair -/
noncomputable def pkaeEncOracle (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (b : Bool)
    (pkeyO : PKEYOracles) (pk_s pk_r : CT.PK) (m : CT.M) (n : CT.Nonce) :
    SPComp CT.C := do
  let hon_s ← pkeyO.honpk pk_s
  let hon_r ← pkeyO.honpk pk_r
  let sk_s ← pkeyO.getsk pk_s
  if b && hon_s && hon_r then do
    let sid := sortSID pk_s pk_r
    let log ← SPComp.get pkaeLogLoc
    let c ← SPComp.sample CT.C
    SPComp.set pkaeLogLoc
      (Function.update log (sid, n) (some (m, c)) :
        (SID × CT.Nonce) → Option (CT.M × CT.C))
    SPComp.pure c
  else do
    let k := N.sharedkey pk_r sk_s
    E.enc (I.encode k) m n

/-- PKAE decryption oracle.
    - `b = false` (real): decrypt using the cryptobox construction
    - `b = true` (ideal): look up `(sid, n)` in the log -/
noncomputable def pkaeDecOracle (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (b : Bool)
    (pkeyO : PKEYOracles) (pk_r pk_s : CT.PK) (c : CT.C) (n : CT.Nonce) :
    SPComp (Option CT.M) := do
  let hon_s ← pkeyO.honpk pk_s
  let hon_r ← pkeyO.honpk pk_r
  let sk_r ← pkeyO.getsk pk_r
  if b && hon_s && hon_r then do
    let sid := sortSID pk_s pk_r
    let log ← SPComp.get pkaeLogLoc
    match log (sid, n) with
    | some (m, c') =>
      if c == c' then SPComp.pure (some m)
      else SPComp.pure none
    | none => SPComp.pure none
  else do
    let k := N.sharedkey pk_s sk_r
    E.dec (I.encode k) c n

/-! ### PKAE Game -/

/-- PKAE game parameterized by `b`:
    - `b = false` (real): cryptobox construction
    - `b = true` (ideal): random ciphertexts for honest-honest sessions -/
noncomputable def PKAE (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (b : Bool) (A : PKAEOracles → SPComp Bool) : SPComp Bool :=
  let pkeyO : PKEYOracles :=
    { gen := fun _ => genOracle N false,
      csetpk := csetpkOracle,
      getsk := getskOracle,
      honpk := honpkOracle }
  A { gen := pkeyO.gen,
      csetpk := pkeyO.csetpk,
      getsk := pkeyO.getsk,
      honpk := pkeyO.honpk,
      enc := pkaeEncOracle N E I b pkeyO,
      dec := pkaeDecOracle N E I b pkeyO }

/-- PKAE advantage: distinguishing real from ideal PKAE. -/
noncomputable def pkaeAdvantage (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (A : PKAEOracles → SPComp Bool) : ℝ≥0∞ :=
  Advantage (PKAE N E I false A) (PKAE N E I true A)

/-! ## Reductions

Adversary wrappers that reduce the security of one game to another. -/

/-- NIKE reduction: wrap a PKAE adversary into one attacking the NIKE game.
    Routes encryption/decryption through the NIKE shared key oracle. -/
noncomputable def R_GNIKE (_N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool) :
    PKEYOracles → NIKEOracles → SPComp Bool := fun pkeyO nikeO =>
  A { gen := pkeyO.gen,
      csetpk := pkeyO.csetpk,
      getsk := pkeyO.getsk,
      honpk := pkeyO.honpk,
      enc := fun pk_s pk_r m n => do
        let k ← nikeO.sharedkey pk_s pk_r
        E.enc (I.encode k) m n,
      dec := fun pk_r pk_s c n => do
        let k ← nikeO.sharedkey pk_s pk_r
        E.dec (I.encode k) c n }

/-- SAE reduction at hybrid index `i`: wrap a PKAE adversary into one
    attacking the single-instance SAE game for session `i`.
    Routes session `i`'s encryption/decryption through the SAE oracle. -/
noncomputable def R_GSAE (_E : @NBSES CT) (_I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool) (_i : Nat) :
    SAEOracles → SPComp Bool := fun saeO => do
  saeO.sgen ()
  A { gen := fun _ => SPComp.fail,
      csetpk := fun _ => SPComp.fail,
      getsk := fun _ => SPComp.fail,
      honpk := fun _ => SPComp.pure false,
      enc := fun _ _ m n => saeO.senc m n,
      dec := fun _ _ c n => saeO.sdec c n }

/-! ## AE Hybrid Argument

The AE game switches from real to ideal encryption across multiple sessions.
This is decomposed via a hybrid argument: switch one session at a time, and
bound the total advantage by the sum of per-session SAE advantages.

The `i`-th hybrid game uses ideal encryption for sessions `0, ..., i-1` and
real encryption for sessions `i, ..., q-1`. -/

set_option linter.unusedSectionVars false in
/-- AE advantage bounded by sum of SAE advantages via hybrid argument.

    Takes a hybrid decomposition hypothesis `hdecomp` that decomposes the AE
    advantage into per-step contributions, and per-step bounds `hsteps`.
    The decomposition corresponds to the triangle inequality applied to:
    ```
      AE(real) = H(0) ≈ H(1) ≈ ... ≈ H(q) = AE(ideal)
    ``` -/
theorem ae_hybrid_bound (E : @NBSES CT) (I : @KeyInjection CT)
    (keyO : KEYOracles) (A : AEOracles → SPComp Bool)
    (q : Nat) (sae_eps : Nat → ℝ≥0∞)
    (step_adv : Nat → ℝ≥0∞)
    (hdecomp : aeAdvantage E I keyO A ≤ Finset.sum (Finset.range q) step_adv)
    (hsteps : ∀ i, i < q → step_adv i ≤ sae_eps i) :
    aeAdvantage E I keyO A ≤ Finset.sum (Finset.range q) sae_eps :=
  calc aeAdvantage E I keyO A
      ≤ Finset.sum (Finset.range q) step_adv := hdecomp
    _ ≤ Finset.sum (Finset.range q) sae_eps :=
        Finset.sum_le_sum fun i hi => hsteps i (Finset.mem_range.mp hi)

/-! ## Main Security Theorem -/

/-- **Cryptobox security theorem.**

    The PKAE advantage of any adversary `A` against the Cryptobox construction
    is bounded by the sum of:

    1. **PKEY switching** (FEL collision bound):
       `2 * q_gen * q_csetpk * (1 / |PK|)`

    2. **NIKE advantage**: `nike_eps`

    3. **AE hybrid sum**: `Σ_{i < q} sae_eps(i)`

    The `hdecomp` hypothesis encapsulates the game-hopping decomposition:
    ```
      PKAE(real) ≈_{PKEY} PKAE' ≈_{NIKE} PKAE'' ≈_{KEY} PKAE''' ≈_{AE} PKAE(ideal)
    ```
    This corresponds to the **three structural equivalences that are ADMITTED
    in the Rocq SSProve formalization** (package decomposition and recomposition).

    Given `hdecomp`, the bound follows from monotonicity of addition. -/
theorem cryptobox_security
    (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool)
    (q_gen q_csetpk q : Nat)
    (nike_eps : ℝ≥0∞) (sae_eps : Nat → ℝ≥0∞)
    -- Intermediate advantage values from the game-hopping chain
    (pkey_adv nike_adv ae_adv : ℝ≥0∞)
    -- Game decomposition: PKAE advantage ≤ sum of component advantages.
    -- This corresponds to the 3 ADMITTED structural equivalences in Rocq SSProve:
    --   (1) PKAE(real) = PKEY(0) ∘ NIKE(0) ∘ KEY(0) ∘ AE(0)
    --   (2) PKAE(ideal) = PKEY(1) ∘ NIKE(1) ∘ KEY(1) ∘ AE(1)
    --   (3) KEY(0) = KEY(1) structurally
    (hdecomp : pkaeAdvantage N E I A ≤ pkey_adv + nike_adv + ae_adv)
    -- Component bounds
    (hpkey : pkey_adv ≤ 2 * (q_gen * q_csetpk : ℕ) * (1 / Fintype.card CT.PK : ℝ≥0∞))
    (hnike : nike_adv ≤ nike_eps)
    (hae : ae_adv ≤ Finset.sum (Finset.range q) sae_eps) :
    pkaeAdvantage N E I A ≤
      2 * (q_gen * q_csetpk : ℕ) * (1 / Fintype.card CT.PK : ℝ≥0∞)
      + nike_eps
      + Finset.sum (Finset.range q) sae_eps :=
  calc pkaeAdvantage N E I A
      ≤ pkey_adv + nike_adv + ae_adv := hdecomp
    _ ≤ _ := add_le_add (add_le_add hpkey hnike) hae

/-! ## Instantiation: X25519 + XSalsa20-Poly1305

For concrete security, one would instantiate:
- `CT.PK = CT.SK = Fin (2^255 - 19)` (Curve25519 points)
- `CT.SharedKey = Fin (2^256)` (HSalsa20 output)
- `N.sharedkey = X25519`
- `E.enc/dec = XSalsa20-Poly1305`
- `I.encode = HSalsa20`

The NIKE advantage reduces to the CDH assumption on Curve25519.
The SAE advantage reduces to the PRF security of XSalsa20 and the
MAC security of Poly1305.

These concrete instantiations are left for future work. -/

end CatCrypt.Examples.Cryptobox
