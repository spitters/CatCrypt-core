/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.Cryptobox.GameHopping

/-!
# AE Hybrid Argument for Cryptobox

Hybrid games for the AE switching step in the Cryptobox security proof.
The AE step transitions session-by-session from real encryption (with random
shared keys) to ideal encryption (random ciphertext + log-based decryption).

## Overview

The `aeStepAdvantage` from `GameHopping.lean` captures the distance:
```
  Advantage(PKAE_nikeSwitch, PKAE_cc(true))
```

We decompose this via a hybrid argument over sessions. The hybrid game
`aeHybrid S` is parameterized by a set `S : Finset SID` of "switched" sessions:

- Sessions in `S`: ideal encryption (random ciphertext, log-based decryption)
- Sessions not in `S`: real encryption (with random cached key from `getOrSampleKey`)
- Corrupt sessions: always real encryption (with `N.sharedkey`)

## Boundary conditions

* `aeHybrid_empty` : `aeHybrid N E I {} A = PKAE_nikeSwitch N E I A`
* `aeHybrid_univ` : `aeHybrid N E I Finset.univ A = PKAE_cc N E I true A`

## Per-step structure

Each step switches a single session `sid` from real to ideal:
```
  Advantage(aeHybrid(S), aeHybrid(S ∪ {sid})) ≤ saeAdvantage E (R_sae sid A)
```

## Main results

* `aeHybrid` - Hybrid game parameterized by switched session set
* `aeHybridStepAdvantage` - Per-step advantage for switching one session
* `aeHybrid_empty` - Boundary: `aeHybrid {} = PKAE_nikeSwitch`
* `aeHybrid_univ` - Boundary: `aeHybrid univ = PKAE_cc true`
* `aeStep_triangle` - AE step advantage bounded by sum over hybrid steps

## References

* Dupressoir et al., "How Hard Can It Be?" (ASIACRYPT 2025)
* Dupressoir et al., "Bringing SSP to EasyCrypt" (CSF 2022)
* Myssenburg et al., Rocq SSProve Cryptobox
-/

namespace CatCrypt.Examples.Cryptobox

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable [CT : CryptoTypes] [LinearOrder CT.PK]

/-! ## Hybrid Encryption Oracle

The encryption oracle for the hybrid game. Parameterized by a set of switched
sessions `S : Finset SID`. For honest-honest sessions in `S`, we use ideal
encryption (sample random ciphertext + log). For honest-honest sessions NOT in
`S`, we use real encryption with a random cached key. For corrupt sessions,
we always use real encryption with the actual NIKE shared key. -/

/-- Hybrid encryption oracle parameterized by switched session set.

    - Honest-honest sessions in `switched`: ideal (sample random ciphertext, log it)
    - Honest-honest sessions not in `switched`: real (random cached key + `E.enc`)
    - Corrupt sessions: real (`N.sharedkey` + `E.enc`) -/
noncomputable def aeHybridEncOracle (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (switched : Finset SID)
    (pkeyO : PKEYOracles) (pk_s pk_r : CT.PK) (m : CT.M) (n : CT.Nonce) :
    SPComp CT.C := do
  let hon_s ← pkeyO.honpk pk_s
  let hon_r ← pkeyO.honpk pk_r
  let sk_s ← pkeyO.getsk pk_s
  let sid := sortSID pk_s pk_r
  if hon_s && hon_r then
    if sid ∈ switched then do
      -- Ideal: sample random ciphertext and log the (message, ciphertext) pair
      let log ← SPComp.get pkaeLogLoc
      let c ← SPComp.sample CT.C
      SPComp.set pkaeLogLoc
        (Function.update log (sid, n) (some (m, c)) :
          (SID × CT.Nonce) → Option (CT.M × CT.C))
      SPComp.pure c
    else do
      -- Real: use random cached key + real encryption
      let k ← getOrSampleKey sid
      E.enc (I.encode k) m n
  else do
    -- Corrupt: use N.sharedkey + real encryption
    let k := N.sharedkey pk_r sk_s
    E.enc (I.encode k) m n

/-! ## Hybrid Decryption Oracle

The decryption oracle for the hybrid game, following the same switching
logic as encryption. -/

/-- Hybrid decryption oracle parameterized by switched session set.

    - Honest-honest sessions in `switched`: ideal (log-based decryption)
    - Honest-honest sessions not in `switched`: real (random cached key + `E.dec`)
    - Corrupt sessions: real (`N.sharedkey` + `E.dec`) -/
noncomputable def aeHybridDecOracle (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (switched : Finset SID)
    (pkeyO : PKEYOracles) (pk_r pk_s : CT.PK) (c : CT.C) (n : CT.Nonce) :
    SPComp (Option CT.M) := do
  let hon_s ← pkeyO.honpk pk_s
  let hon_r ← pkeyO.honpk pk_r
  let sk_r ← pkeyO.getsk pk_r
  let sid := sortSID pk_s pk_r
  if hon_s && hon_r then
    if sid ∈ switched then do
      -- Ideal: log-based decryption
      let log ← SPComp.get pkaeLogLoc
      match log (sid, n) with
      | some (m, c') =>
        if c == c' then SPComp.pure (some m)
        else SPComp.pure none
      | none => SPComp.pure none
    else do
      -- Real: use random cached key + real decryption
      let k ← getOrSampleKey sid
      E.dec (I.encode k) c n
  else do
    -- Corrupt: use N.sharedkey + real decryption
    let k := N.sharedkey pk_s sk_r
    E.dec (I.encode k) c n

/-! ## Hybrid Game

The hybrid game composes the collision-checking PKEY oracles with the hybrid
encryption/decryption oracles. -/

/-- AE hybrid game parameterized by switched session set `S`.

    Uses collision-checking GEN (matching `PKAE_cc`) and routes encryption/decryption
    through the hybrid oracles. The set `S` controls which honest-honest sessions
    use ideal encryption:
    - `S = {}`: all honest sessions use real encryption (= `PKAE_nikeSwitch`)
    - `S = Finset.univ`: all honest sessions use ideal encryption (= `PKAE_cc true`) -/
noncomputable def aeHybrid (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (switched : Finset SID) (A : PKAEOracles → SPComp Bool) : SPComp Bool :=
  let pkeyO : PKEYOracles :=
    { gen := fun _ => genOracle N true,
      csetpk := csetpkOracle,
      getsk := getskOracle,
      honpk := honpkOracle }
  A { gen := pkeyO.gen,
      csetpk := pkeyO.csetpk,
      getsk := pkeyO.getsk,
      honpk := pkeyO.honpk,
      enc := aeHybridEncOracle N E I switched pkeyO,
      dec := aeHybridDecOracle N E I switched pkeyO }

/-! ## Boundary Theorems

The hybrid game at the two extremes matches the existing game definitions. -/

/-- **Empty boundary**: when no session is switched, the hybrid game equals
    `PKAE_nikeSwitch` — all honest-honest sessions use real encryption with
    random cached keys.

    Proof strategy: When `switched = {}`, the condition `sid ∈ switched` is always
    false, so the hybrid oracles always take the "real" branch. The real branch
    of the hybrid enc/dec oracles uses `getOrSampleKey` + `E.enc`/`E.dec`,
    which matches `PKAE_nikeSwitch`. -/
theorem aeHybrid_empty (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool) :
    aeHybrid N E I ∅ A = PKAE_nikeSwitch N E I A := by
  -- Both sides apply A to a PKAEOracles record. Show the records are equal.
  unfold aeHybrid PKAE_nikeSwitch aeHybridEncOracle aeHybridDecOracle
  simp only [Finset.notMem_empty, ite_false]

/-- **Universe boundary**: when all sessions are switched, the hybrid game equals
    `PKAE_cc true` — all honest-honest sessions use ideal encryption.

    Proof strategy: When `switched = Finset.univ`, the condition `sid ∈ switched`
    is always true for any `sid`, so the hybrid oracles always take the "ideal"
    branch for honest-honest sessions. The ideal branch matches `pkaeEncOracle`/
    `pkaeDecOracle` with `b = true`.

    The only subtlety is that `PKAE_cc true` uses `pkaeEncOracle` which checks
    `b && hon_s && hon_r` while the hybrid oracle checks `hon_s && hon_r` then
    `sid ∈ switched`. When `switched = univ` and both are honest, both branches
    produce the same ideal behavior. When either party is corrupt, both fall
    through to the real encryption with `N.sharedkey`. -/
theorem aeHybrid_univ (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool) :
    aeHybrid N E I Finset.univ A = PKAE_cc N E I true A := by
  -- Both sides apply A to a PKAEOracles record. Show the records are equal.
  -- After unfolding, the difference is:
  -- hybrid: checks `hon_s && hon_r` then `sid ∈ Finset.univ` (always true)
  -- PKAE_cc: checks `true && hon_s && hon_r` (= `hon_s && hon_r`)
  -- Both reduce to `if hon_s && hon_r then ideal else real`.
  unfold aeHybrid PKAE_cc aeHybridEncOracle aeHybridDecOracle
    pkaeEncOracle pkaeDecOracle
  simp only [Finset.mem_univ, ite_true, Bool.true_and]
  rfl

/-! ## Per-Step Advantage

The advantage of switching a single session from real to ideal encryption. -/

/-- Per-step advantage: the distinguishing distance when adding session `sid`
    to the switched set.

    This captures the cost of switching one session from real to ideal encryption.
    The reduction to single-instance SAE (saeAdvantage) requires showing that
    the per-session difference can be simulated by a single SAE adversary. -/
noncomputable def aeHybridStepAdvantage (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (S : Finset SID) (sid : SID)
    (A : PKAEOracles → SPComp Bool) : ℝ≥0∞ :=
  Advantage (aeHybrid N E I S A) (aeHybrid N E I (insert sid S) A)

/-- When `sid ∈ S`, inserting `sid` again does nothing, so the step advantage is 0.

    Proof strategy: `insert sid S = S` when `sid ∈ S`, so the two hybrid games
    are definitionally equal. -/
theorem aeHybridStepAdvantage_mem (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (S : Finset SID) (sid : SID)
    (A : PKAEOracles → SPComp Bool) (hmem : sid ∈ S) :
    aeHybridStepAdvantage N E I S sid A = 0 := by
  simp [aeHybridStepAdvantage, Finset.insert_eq_of_mem hmem, Advantage, tsub_self, max_self]

/-! ## SAE Reduction Adversary

The reduction adversary that converts a single-session SAE attacker into
a PKAE hybrid distinguisher. When the SAE game provides real encryption,
we get `aeHybrid S`; when it provides ideal encryption, we get
`aeHybrid (insert sid S)`. -/

/-- SAE reduction adversary for the hybrid step.

    Given SAE oracles for a single session, constructs PKAE oracles where:
    - Session `sid`: routes through SAE oracles (real or ideal depending on SAE game)
    - Other sessions in `switched`: ideal encryption (random ciphertext + log)
    - Other sessions not in `switched`: real encryption (random cached key)
    - Corrupt sessions: real encryption (N.sharedkey)

    When plugged into SAE(false), this gives `aeHybrid S`.
    When plugged into SAE(true), this gives `aeHybrid (insert sid S)`.

    This captures the core of the hybrid argument: the per-step advantage
    is bounded by the SAE advantage of this reduction adversary. -/
noncomputable def R_SAE_hybrid (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (switched : Finset SID) (targetSid : SID)
    (A : PKAEOracles → SPComp Bool) :
    SAEOracles → SPComp Bool := fun saeO => do
  -- Initialize the SAE key for the target session
  saeO.sgen ()
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
        let sid := sortSID pk_s pk_r
        if hon_s && hon_r then
          if sid = targetSid then
            -- Target session: route through SAE oracle
            saeO.senc m n
          else if sid ∈ switched then do
            -- Already switched: ideal encryption
            let log ← SPComp.get pkaeLogLoc
            let c ← SPComp.sample CT.C
            SPComp.set pkaeLogLoc
              (Function.update log (sid, n) (some (m, c)) :
                (SID × CT.Nonce) → Option (CT.M × CT.C))
            SPComp.pure c
          else do
            -- Not yet switched: real encryption with random key
            let k ← getOrSampleKey sid
            E.enc (I.encode k) m n
        else do
          -- Corrupt: use N.sharedkey + real encryption
          let k := N.sharedkey pk_r sk_s
          E.enc (I.encode k) m n,
      dec := fun pk_r pk_s c n => do
        let hon_s ← pkeyO.honpk pk_s
        let hon_r ← pkeyO.honpk pk_r
        let sk_r ← pkeyO.getsk pk_r
        let sid := sortSID pk_s pk_r
        if hon_s && hon_r then
          if sid = targetSid then
            -- Target session: route through SAE oracle
            saeO.sdec c n
          else if sid ∈ switched then do
            -- Already switched: ideal decryption (log-based)
            let log ← SPComp.get pkaeLogLoc
            match log (sid, n) with
            | some (m, c') =>
              if c == c' then SPComp.pure (some m)
              else SPComp.pure none
            | none => SPComp.pure none
          else do
            -- Not yet switched: real decryption with random key
            let k ← getOrSampleKey sid
            E.dec (I.encode k) c n
        else do
          -- Corrupt: use N.sharedkey + real decryption
          let k := N.sharedkey pk_s sk_r
          E.dec (I.encode k) c n }

/-! ## Hybrid Step Bound

The per-step advantage is bounded by the SAE advantage of the reduction. -/

/-- **Per-step reduction**: the hybrid step advantage for session `sid` is bounded
    by the SAE advantage of the reduction adversary `R_SAE_hybrid`.

    The two oracle alignment hypotheses capture the core of the reduction:
    - `h_real`: when SAE provides real encryption, the composed game equals
      the hybrid game without `sid` switched
    - `h_ideal`: when SAE provides ideal encryption, the composed game equals
      the hybrid game with `sid` switched

    Proving these alignments requires showing that routing the target session
    through SAE oracles produces identical distributions to the hybrid oracles.
    The main subtlety is aligning the SAE log (indexed by nonce) with the
    PKAE log (indexed by `(SID, Nonce)`) for the target session. -/
theorem aeHybrid_step_bound (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (S : Finset SID) (sid : SID) (_hns : sid ∉ S)
    (A : PKAEOracles → SPComp Bool)
    (h_real : aeHybrid N E I S A = SAE E false (R_SAE_hybrid N E I S sid A))
    (h_ideal : aeHybrid N E I (insert sid S) A =
      SAE E true (R_SAE_hybrid N E I S sid A)) :
    aeHybridStepAdvantage N E I S sid A ≤
      saeAdvantage E (R_SAE_hybrid N E I S sid A) := by
  simp [aeHybridStepAdvantage, saeAdvantage, h_real, h_ideal]

/-! ## Triangle Inequality over Hybrid Chain

Decomposing the AE step advantage into a sum of per-step advantages. -/

/-- Auxiliary: advantage of switching from `S` to `S ∪ T` is bounded by
    the sum of advantages of inserting each element of `T` one at a time.

    This follows from the triangle inequality applied iteratively:
    `Advantage(aeHybrid S, aeHybrid (S ∪ T))
       ≤ Σ_{sid ∈ T} Advantage(aeHybrid S_i, aeHybrid S_{i+1})`
    where `S_0 = S` and `S_{i+1} = insert t_i S_i`. -/
theorem aeHybrid_union_triangle (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool)
    (S : Finset SID) (sids : List SID) (hnodup : sids.Nodup)
    (hdisjoint : ∀ sid ∈ sids, sid ∉ S) :
    Advantage (aeHybrid N E I S A)
      (aeHybrid N E I (S ∪ sids.toFinset) A) ≤
    (sids.map fun sid =>
      aeHybridStepAdvantage N E I
        (S ∪ (sids.takeWhile (· ≠ sid)).toFinset) sid A).sum := by
  induction sids generalizing S with
  | nil =>
    simp [List.map_nil, List.toFinset_nil, Finset.union_empty, List.sum_nil,
      Advantage, tsub_self, max_self]
  | cons x xs ih =>
    have hx_not_xs : x ∉ xs := (List.nodup_cons.mp hnodup).1
    have hxs_nodup : xs.Nodup := (List.nodup_cons.mp hnodup).2
    have hx_not_S : x ∉ S := hdisjoint x List.mem_cons_self
    -- Rewrite: S ∪ (x :: xs).toFinset = insert x S ∪ xs.toFinset
    have h_union : S ∪ (x :: xs).toFinset = insert x S ∪ xs.toFinset := by
      simp only [List.toFinset_cons, Finset.union_comm S, Finset.insert_union]
    rw [h_union]
    -- IH hypotheses for xs with base set (insert x S)
    have hxs_disj : ∀ sid ∈ xs, sid ∉ insert x S := fun sid hmem => by
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun heq => absurd (heq ▸ hmem) hx_not_xs,
             hdisjoint sid (List.mem_cons_of_mem x hmem)⟩
    -- Apply triangle inequality
    calc Advantage (aeHybrid N E I S A)
          (aeHybrid N E I (insert x S ∪ xs.toFinset) A)
        ≤ Advantage (aeHybrid N E I S A) (aeHybrid N E I (insert x S) A)
          + Advantage (aeHybrid N E I (insert x S) A)
              (aeHybrid N E I (insert x S ∪ xs.toFinset) A) :=
          advantage_triangle _ _ _
      _ ≤ aeHybridStepAdvantage N E I S x A
          + (xs.map fun sid => aeHybridStepAdvantage N E I
              (insert x S ∪ (xs.takeWhile (· ≠ sid)).toFinset) sid A).sum :=
          add_le_add le_rfl (ih (insert x S) hxs_nodup hxs_disj)
      _ = ((x :: xs).map fun sid => aeHybridStepAdvantage N E I
              (S ∪ ((x :: xs).takeWhile (· ≠ sid)).toFinset) sid A).sum := by
          -- Expand cons map/sum and simplify head
          rw [List.map_cons, List.sum_cons]
          -- Head: takeWhile (· ≠ x) (x :: xs) = [] since (x ≠ x) = false
          have h_tw_nil : List.takeWhile (· ≠ x) (x :: xs) = [] :=
            List.takeWhile_cons_of_neg (by simp)
          rw [h_tw_nil, List.toFinset_nil, Finset.union_empty]
          -- Now both sides have same head. Show tail sums match.
          -- Prove the tail maps are equal element-wise
          have h_maps_eq : xs.map (fun sid => aeHybridStepAdvantage N E I
                (insert x S ∪ (xs.takeWhile (· ≠ sid)).toFinset) sid A)
              = xs.map (fun sid => aeHybridStepAdvantage N E I
                (S ∪ ((x :: xs).takeWhile (· ≠ sid)).toFinset) sid A) :=
            List.map_eq_map_iff.mpr fun sid hmem => by
              have hne : sid ≠ x := fun h => absurd (h ▸ hmem) hx_not_xs
              have h_tw : List.takeWhile (· ≠ sid) (x :: xs)
                  = x :: List.takeWhile (· ≠ sid) xs :=
                List.takeWhile_cons_of_pos (by simp [Ne.symm hne])
              simp only [h_tw, List.toFinset_cons,
                Finset.union_insert, Finset.insert_union]
          rw [h_maps_eq]

/-- **AE step triangle inequality**: the AE step advantage (from `PKAE_nikeSwitch`
    to `PKAE_cc true`) is bounded by the sum of per-step hybrid advantages
    over all sessions.

    Combined with `aeHybrid_step_bound`, this gives:
    `aeStepAdvantage ≤ Σ_{sid} saeAdvantage E (R_SAE_hybrid ... sid A)`

    Proof strategy:
    1. Rewrite `PKAE_nikeSwitch = aeHybrid ∅` via `aeHybrid_empty`
    2. Rewrite `PKAE_cc true = aeHybrid Finset.univ` via `aeHybrid_univ`
    3. Apply `aeHybrid_union_triangle` with `S = ∅` and `sids = all sessions`
    4. Simplify `∅ ∪ sids.toFinset = Finset.univ` -/
theorem aeStep_triangle (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool)
    (sids : List SID) (hnodup : sids.Nodup)
    (hcomplete : sids.toFinset = Finset.univ) :
    aeStepAdvantage N E I A ≤
    (sids.map fun sid =>
      aeHybridStepAdvantage N E I
        (sids.takeWhile (· ≠ sid)).toFinset sid A).sum := by
  unfold aeStepAdvantage
  rw [← aeHybrid_empty N E I A, ← aeHybrid_univ N E I A]
  simpa only [Finset.empty_union, hcomplete] using
    aeHybrid_union_triangle N E I A ∅ sids hnodup (by simp)

/-! ## Combined Bound

Putting together the triangle inequality and per-step SAE reduction. -/

/-- **AE hybrid bound**: the AE step advantage is bounded by the sum of
    SAE advantages of the per-session reduction adversaries.

    This is the main result of the hybrid argument:
    ```
      aeStepAdvantage N E I A ≤ Σ_{sid} saeAdvantage E (R_SAE_hybrid ... sid A)
    ```

    Combined with `cryptobox_security_full` from `GameHopping.lean`, this
    gives the complete Cryptobox security bound. -/
theorem aeStep_bounded_by_sae (N : @NIKEScheme CT) (E : @NBSES CT) (I : @KeyInjection CT)
    (A : PKAEOracles → SPComp Bool)
    (sids : List SID) (hnodup : sids.Nodup)
    (hcomplete : sids.toFinset = Finset.univ)
    (sae_eps : SID → ℝ≥0∞)
    (h_oracle_align : ∀ (S : Finset SID) (sid : SID), sid ∉ S →
      aeHybrid N E I S A = SAE E false (R_SAE_hybrid N E I S sid A) ∧
      aeHybrid N E I (insert sid S) A = SAE E true (R_SAE_hybrid N E I S sid A))
    (hsteps : ∀ sid ∈ sids,
      saeAdvantage E (R_SAE_hybrid N E I
        (sids.takeWhile (· ≠ sid)).toFinset sid A) ≤ sae_eps sid) :
    aeStepAdvantage N E I A ≤ (sids.map sae_eps).sum := by
  -- Chain: triangle inequality → per-step SAE reduction → hypothesized bound
  calc aeStepAdvantage N E I A
      ≤ (sids.map fun sid =>
          aeHybridStepAdvantage N E I
            (sids.takeWhile (· ≠ sid)).toFinset sid A).sum :=
          aeStep_triangle N E I A sids hnodup hcomplete
    _ ≤ (sids.map sae_eps).sum := by
        apply List.sum_le_sum
        intro sid hmem
        have hns : sid ∉ (sids.takeWhile (· ≠ sid)).toFinset := by
          rw [List.mem_toFinset]
          intro hmem_tw
          exact absurd ((List.all_eq_true.mp List.all_takeWhile) sid hmem_tw)
            (by simp)
        calc aeHybridStepAdvantage N E I
              (sids.takeWhile (· ≠ sid)).toFinset sid A
            ≤ saeAdvantage E (R_SAE_hybrid N E I
                (sids.takeWhile (· ≠ sid)).toFinset sid A) :=
              aeHybrid_step_bound N E I _ sid hns A
                (h_oracle_align _ sid hns).1 (h_oracle_align _ sid hns).2
          _ ≤ sae_eps sid := hsteps sid hmem

/-! ## Finset-Based Bound (Alternative Formulation)

An alternative formulation using `Finset.sum` instead of `List.map ... .sum`,
which is sometimes more convenient for downstream use. -/

/-- **AE hybrid bound (Finset version)**: the AE step advantage is bounded
    by the sum of per-session SAE advantages over all sessions.

    This takes the per-step bounds as hypotheses, matching the structure
    of `ae_hybrid_bound` from `Cryptobox.lean`. -/
theorem aeStep_bounded_by_sae_finset (N : @NIKEScheme CT) (E : @NBSES CT)
    (I : @KeyInjection CT) (A : PKAEOracles → SPComp Bool)
    (sae_eps : SID → ℝ≥0∞)
    (hsteps : ∀ (S : Finset SID) (sid : SID), sid ∉ S →
      aeHybridStepAdvantage N E I S sid A ≤ sae_eps sid) :
    aeStepAdvantage N E I A ≤ Finset.univ.sum sae_eps := by
  -- Rewrite using boundary conditions
  unfold aeStepAdvantage
  rw [← aeHybrid_empty N E I A, ← aeHybrid_univ N E I A]
  -- Prove by Finset induction: for any T, Advantage(H(∅), H(T)) ≤ T.sum sae_eps
  suffices h : ∀ (T : Finset SID),
      Advantage (aeHybrid N E I ∅ A) (aeHybrid N E I T A) ≤ T.sum sae_eps from
    h Finset.univ
  intro T
  refine Finset.induction_on T ?_ ?_
  · -- Base: Advantage(H(∅), H(∅)) = 0 ≤ 0 = ∅.sum
    simp [Finset.sum_empty, Advantage, tsub_self, max_self]
  · -- Step: insert a into s
    intro a s hns ih
    calc Advantage (aeHybrid N E I ∅ A) (aeHybrid N E I (insert a s) A)
        ≤ Advantage (aeHybrid N E I ∅ A) (aeHybrid N E I s A)
          + Advantage (aeHybrid N E I s A) (aeHybrid N E I (insert a s) A) :=
          advantage_triangle _ _ _
      _ ≤ s.sum sae_eps + sae_eps a :=
          add_le_add ih (hsteps s a hns)
      _ = (insert a s).sum sae_eps := by
          rw [Finset.sum_insert hns, add_comm]

end CatCrypt.Examples.Cryptobox
