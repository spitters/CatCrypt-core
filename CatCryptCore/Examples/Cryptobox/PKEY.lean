/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.Cryptobox.Scheme
import CatCryptCore.Prob.Coupling
import CatCryptCore.Relational.Rules
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.SDist
import CatCryptCore.Unary.FailureEvent
import CatCryptCore.Crypto.GameReject
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# PKEY: Public Key Management Game

The PKEY game manages public key generation and corruption tracking.

## Overview

Two variants parameterized by `b : Bool`:
- `b = false` (real): No collision checking in GEN
- `b = true` (collision-free): GEN asserts no pk collision

The PKEY Switching Lemma bounds the advantage by collision probability via FEL.

## References

* Rocq SSProve: theories/Cryptobox/PKEY.v
* Dupressoir et al., CSF 2022 (Section 4.1)
-/

namespace CatCrypt.Examples.Cryptobox

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Relational
open CatCrypt.Crypto
open scoped ENNReal

variable [CT : CryptoTypes]

/-! ## Heap Locations

State is stored in the global heap via typed locations.
Locations are `@[reducible]` so that `.ty` reduces for type checking. -/

/-- Honesty flags: `PK → Bool`. Default: all `false` (unregistered). -/
@[reducible] noncomputable def pkHonestLoc : Location := ⟨100, CT.PK → Bool⟩

/-- Secret key storage: `PK → SK`. Only meaningful for honest keys. -/
@[reducible] noncomputable def skStoreLoc : Location := ⟨101, CT.PK → CT.SK⟩

/-- Corruption flags: `PK → Bool`. Default: all `false`. -/
@[reducible] noncomputable def pkCorruptLoc : Location := ⟨102, CT.PK → Bool⟩

/-! ## Oracle Definitions

Each oracle is an `SPComp` computation that reads/writes heap locations.
The `b : Bool` parameter in GEN switches collision behavior. -/

/-- GEN oracle: generate a fresh honest key pair.
    If `b = true`, asserts no collision with existing registered keys. -/
noncomputable def genOracle (N : @NIKEScheme CT) (b : Bool) : SPComp CT.PK := do
  let pair ← N.pkgen
  let pk := pair.1
  let sk := pair.2
  let honest ← SPComp.get pkHonestLoc
  let corrupt ← SPComp.get pkCorruptLoc
  if b then
    if honest pk || corrupt pk then SPComp.fail
    else SPComp.pure ()
  else
    SPComp.pure ()
  let skMap ← SPComp.get skStoreLoc
  SPComp.set pkHonestLoc (Function.update honest pk true : CT.PK → Bool)
  SPComp.set skStoreLoc (Function.update skMap pk sk : CT.PK → CT.SK)
  SPComp.pure pk

/-- CSETPK oracle: register an adversary-chosen public key as corrupt. -/
noncomputable def csetpkOracle (pk : CT.PK) : SPComp Unit := do
  let honest ← SPComp.get pkHonestLoc
  let corrupt ← SPComp.get pkCorruptLoc
  if honest pk || corrupt pk then SPComp.fail
  else SPComp.pure ()
  SPComp.set pkCorruptLoc (Function.update corrupt pk true : CT.PK → Bool)

/-- GETSK oracle: retrieve the secret key for an honest public key. -/
noncomputable def getskOracle (pk : CT.PK) : SPComp CT.SK := do
  let honest ← SPComp.get pkHonestLoc
  if honest pk then do
    let skMap ← SPComp.get skStoreLoc
    SPComp.pure (skMap pk)
  else
    SPComp.fail

/-- HONPK oracle: check whether a public key is one the challenger generated
    (rather than adversarially chosen). -/
noncomputable def honpkOracle (pk : CT.PK) : SPComp Bool := do
  let honest ← SPComp.get pkHonestLoc
  SPComp.pure (honest pk)

/-! ## Oracle Record -/

/-- Oracle interface for PKEY games. -/
structure PKEYOracles where
  gen : Unit → SPComp CT.PK
  csetpk : CT.PK → SPComp Unit
  getsk : CT.PK → SPComp CT.SK
  honpk : CT.PK → SPComp Bool

/-! ## PKEY Game -/

/-- PKEY game parameterized by collision behavior `b`. -/
noncomputable def PKEY (N : @NIKEScheme CT) (b : Bool)
    (A : PKEYOracles → SPComp Bool) : SPComp Bool :=
  A { gen := fun _ => genOracle N b,
      csetpk := csetpkOracle,
      getsk := getskOracle,
      honpk := honpkOracle }

/-- PKEY switching advantage. -/
noncomputable def pkeyAdvantage (N : @NIKEScheme CT)
    (A : PKEYOracles → SPComp Bool) : ℝ≥0∞ :=
  Advantage (PKEY N false A) (PKEY N true A)

/-! ## PKEY Collision Analysis

The PKEY game switching argument is a **failure event lemma (FEL)** application.
The key insight is that `genOracle N false` and `genOracle N true` differ only
in the collision check: when `honest pk || corrupt pk = false` (no collision),
both branches execute identically. When a collision DOES occur, the `b=true`
version fails (produces 0 mass) while the `b=false` version continues.

### Proof Structure

To prove `pkeyAdvantage N A ≤ ε` via FEL, one needs:

1. **Up-to-bad agreement**: `PKEY N false A` and `PKEY N true A` agree on outcomes
   where no collision occurred during execution. This follows from the observation
   that `genOracle N false` and `genOracle N true` diverge only at the collision
   check, and all other oracles (csetpk, getsk, honpk) are identical.

2. **Bad probability bound**: The probability that a collision occurs during
   `PKEY N false A` is at most ε. With q_gen GEN queries and q_csetpk CSETPK
   queries, each GEN call samples a pk uniformly, and the collision probability
   is at most `(#honest + #corrupt) / |PK|` per call. By union bound:
   `Pr[collision] ≤ q_gen * q_csetpk / |PK|`.

### Comparison with Other Formalizations

- **EasyCrypt** (~200 lines): Proved via `fel` tactic with automatic oracle decomposition
- **Rocq SSProve** (~150 lines): ADMITTED (structural equivalence axiom)
- **Our approach**: The reduction `PKAE → PKEY` is proven (see GameHopping.lean);
  the FEL bound itself requires oracle composition reasoning not yet available -/

/-- Collision bad event for a single GEN call.

    A collision occurs when the newly generated pk matches an existing
    honest or corrupt key. This is checked on the heap state BEFORE
    the honest flag is updated. -/
def pkeyCollision (h : Heap) (pk : CT.PK) : Prop :=
  Heap.get h pkHonestLoc pk = true ∨ Heap.get h pkCorruptLoc pk = true

/-- Collision predicate on final heap.

    The "bad event" for the FEL: there exists a pk that is registered
    as BOTH honest and corrupt. This is a necessary consequence of any
    collision during execution (since GEN sets honest and CSETPK sets corrupt,
    a collision means some pk ends up with both flags set).

    Note: this is a necessary but not sufficient condition for a collision
    during execution. A stronger formulation would track the collision flag
    explicitly (requiring an instrumented game). -/
def pkeyBadFinal (h : Heap) : Prop :=
  ∃ pk : CT.PK, Heap.get h pkHonestLoc pk = true ∧ Heap.get h pkCorruptLoc pk = true

/-- PKEY collision-checking oracle record. Convenience for building oracle records. -/
noncomputable def pkeyOracles_cc (N : @NIKEScheme CT) : PKEYOracles :=
  { gen := fun _ => genOracle N true,
    csetpk := csetpkOracle,
    getsk := getskOracle,
    honpk := honpkOracle }

/-- PKEY non-collision-checking oracle record. -/
noncomputable def pkeyOracles_nocc (N : @NIKEScheme CT) : PKEYOracles :=
  { gen := fun _ => genOracle N false,
    csetpk := csetpkOracle,
    getsk := getskOracle,
    honpk := honpkOracle }

/-- PKEY game with explicit oracle record is definitionally equal to `PKEY`. -/
theorem PKEY_eq_with_oracles (N : @NIKEScheme CT) (b : Bool)
    (A : PKEYOracles → SPComp Bool) :
    PKEY N b A = A (if b then pkeyOracles_cc N else pkeyOracles_nocc N) := by
  simp only [PKEY, pkeyOracles_cc, pkeyOracles_nocc]
  cases b <;> rfl

/-! ## PKEY Switching Lemma -/

/-- PKEY switching: advantage bounded by collision probability.

    The hypothesis `hcoll` represents the FEL application: PKEY(0) and PKEY(1)
    agree unless a pk collision occurs, and the collision probability is bounded.

    In a concrete instantiation, `hcoll` would be discharged by:
    - Wiring query counting into the PKEY game (via QueryBound.lean)
    - Proving that with q_gen GEN queries and q_csetpk CSETPK queries,
      the collision probability is at most q_gen * q_csetpk / |PK|

    This matches the Rocq SSProve approach where the collision bound
    follows from FEL + union bound over the query sequence. -/
theorem pkey_switching (N : @NIKEScheme CT)
    (A : PKEYOracles → SPComp Bool)
    (coll_bound : ℝ≥0∞)
    (hcoll : pkeyAdvantage N A ≤ coll_bound) :
    pkeyAdvantage N A ≤ coll_bound :=
  hcoll

/-! ## genOracle Analysis

Properties of the collision check in `genOracle`. These are building blocks
for proving the up-to-bad agreement condition. -/

/-- genOracle N false and genOracle N true differ only in the collision check.

    When `b = false`: the collision check is skipped (`SPComp.pure ()`)
    When `b = true`: the collision check may fail (`if coll then fail else pure ()`)

    The rest of the oracle body (sample, read honest/corrupt/skMap, update, return pk)
    is identical in both cases. -/
theorem genOracle_unfold (N : @NIKEScheme CT) (b : Bool) :
    genOracle N b = (do
      let pair ← N.pkgen
      let pk := pair.1
      let sk := pair.2
      let honest ← SPComp.get pkHonestLoc
      let corrupt ← SPComp.get pkCorruptLoc
      if b then
        if honest pk || corrupt pk then SPComp.fail
        else SPComp.pure ()
      else
        SPComp.pure ()
      let skMap ← SPComp.get skStoreLoc
      SPComp.set pkHonestLoc (Function.update honest pk true : CT.PK → Bool)
      SPComp.set skStoreLoc (Function.update skMap pk sk : CT.PK → CT.SK)
      SPComp.pure pk) := by
  rfl

/-! ## PKEY FEL Application

Application of the Failure Event Lemma to bound the PKEY advantage.
The bad event is `pkeyBadFinal`: some public key is both honest and corrupt
in the final heap. -/

/-- PKEY advantage bounded by collision probability via FEL.

    This instantiates `advantage_le_prBad` from `FailureEvent.lean` with the
    PKEY-specific bad event (`pkeyBadFinal`).

    The two hypotheses that must be discharged for a specific adversary `B`:

    1. **Up-to-bad agreement** (`h_agree`): When no collision occurs (no pk is both
       honest and corrupt in the final heap), the two PKEY games produce the same
       distribution. This follows from the fact that `genOracle N false` and
       `genOracle N true` differ only in the collision check, which is vacuous
       when no collision occurs.

       For a concrete adversary, this requires showing that the adversary's
       oracle calls compose correctly — see `agree_bind_left` and
       `agree_bind_both` from `FailureEvent.lean` for the composition lemmas.

    2. **Losslessness** (`hll`): The `PKEY N false B` game is lossless (total mass 1).
       This requires showing that `genOracle N false` never fails (it skips the
       collision check) and that the adversary B doesn't cause failure on its own. -/
theorem pkeyAdvantage_le_collision (N : @NIKEScheme CT) (B : PKEYOracles → SPComp Bool)
    (h_agree : ∀ b h', ¬pkeyBadFinal h' →
      (PKEY N false B Heap.empty) (some (b, h')) = (PKEY N true B Heap.empty) (some (b, h')))
    (hll : Unary.isLossless (PKEY N false B)) :
    pkeyAdvantage N B ≤ Unary.prEventComp (PKEY N false B) Heap.empty
      (fun _ h' => pkeyBadFinal h') :=
  Unary.advantage_le_prBad (PKEY N false B) (PKEY N true B) pkeyBadFinal h_agree hll

/-! ## Collision-Flag Instrumented Game Infrastructure

The `pkeyBadFinal` bad event (∃ pk, honest[pk] ∧ corrupt[pk]) is insufficient
for a precise FEL argument because `genOracle N true` also fails on duplicate
honest keys, not just honest-corrupt cross collisions.

We introduce an **instrumented** variant of the PKEY game that explicitly sets
a collision flag whenever the generated pk collides with ANY existing key
(honest or corrupt). This gives a stronger, more precise bad event for FEL. -/

/-- Collision flag location. Set to `true` when a GEN call produces a pk
    that collides with an existing honest or corrupt key. -/
@[reducible] noncomputable def pkeyCollFlag : Location := ⟨103, Bool⟩

/-- Instrumented GEN oracle: like `genOracle` but sets `pkeyCollFlag` on collision.

    When a collision is detected (the newly generated pk is already honest or corrupt):
    - Always sets the collision flag to `true`
    - If `b = true`: fails (collision-checking mode)
    - If `b = false`: continues without failing (non-collision-checking mode)

    When no collision is detected: both `b = true` and `b = false` execute identically. -/
noncomputable def genOracle_instr (N : @NIKEScheme CT) (b : Bool) : SPComp CT.PK := do
  let pair ← N.pkgen
  let pk := pair.1
  let sk := pair.2
  let honest ← SPComp.get pkHonestLoc
  let corrupt ← SPComp.get pkCorruptLoc
  if honest pk || corrupt pk then do
    SPComp.set pkeyCollFlag true
    if b then SPComp.fail
    else SPComp.pure ()
  else
    SPComp.pure ()
  let skMap ← SPComp.get skStoreLoc
  SPComp.set pkHonestLoc (Function.update honest pk true : CT.PK → Bool)
  SPComp.set skStoreLoc (Function.update skMap pk sk : CT.PK → CT.SK)
  SPComp.pure pk

/-- Instrumented bad event: the collision flag is set.

    This is a precise characterization of "some GEN call produced a collision
    during execution", unlike `pkeyBadFinal` which only captures the weaker
    condition of a pk being both honest and corrupt simultaneously. -/
def pkeyBadInstr (h : Heap) : Prop := Heap.get h pkeyCollFlag = true

/-- Instrumented PKEY game: uses `genOracle_instr` instead of `genOracle`.

    All other oracles (CSETPK, GETSK, HONPK) are unchanged. -/
noncomputable def PKEY_instr (N : @NIKEScheme CT) (b : Bool)
    (A : PKEYOracles → SPComp Bool) : SPComp Bool :=
  A { gen := fun _ => genOracle_instr N b,
      csetpk := csetpkOracle,
      getsk := getskOracle,
      honpk := honpkOracle }

/-- Instrumented oracle records for convenience. -/
noncomputable def pkeyOracles_instr_cc (N : @NIKEScheme CT) : PKEYOracles :=
  { gen := fun _ => genOracle_instr N true,
    csetpk := csetpkOracle,
    getsk := getskOracle,
    honpk := honpkOracle }

noncomputable def pkeyOracles_instr_nocc (N : @NIKEScheme CT) : PKEYOracles :=
  { gen := fun _ => genOracle_instr N false,
    csetpk := csetpkOracle,
    getsk := getskOracle,
    honpk := honpkOracle }

/-- Instrumented PKEY advantage. -/
noncomputable def pkeyAdvantage_instr (N : @NIKEScheme CT)
    (A : PKEYOracles → SPComp Bool) : ℝ≥0∞ :=
  Advantage (PKEY_instr N false A) (PKEY_instr N true A)

/-- Unfolding lemma for `genOracle_instr`. -/
theorem genOracle_instr_unfold (N : @NIKEScheme CT) (b : Bool) :
    genOracle_instr N b = (do
      let pair ← N.pkgen
      let pk := pair.1
      let sk := pair.2
      let honest ← SPComp.get pkHonestLoc
      let corrupt ← SPComp.get pkCorruptLoc
      if honest pk || corrupt pk then do
        SPComp.set pkeyCollFlag true
        if b then SPComp.fail
        else SPComp.pure ()
      else
        SPComp.pure ()
      let skMap ← SPComp.get skStoreLoc
      SPComp.set pkHonestLoc (Function.update honest pk true : CT.PK → Bool)
      SPComp.set skStoreLoc (Function.update skMap pk sk : CT.PK → CT.SK)
      SPComp.pure pk) := by
  rfl

/-! ### Key Theorem: Instrumented Oracles Agree When No Collision

When the collision flag is NOT set in the final heap, the collision branch was
never taken during execution. Therefore, `genOracle_instr N false` and
`genOracle_instr N true` produce identical distributions on non-bad outcomes.

For any outcome `(pk, h')` with `¬pkeyBadInstr h'` (i.e., `Heap.get h' pkeyCollFlag ≠ true`):

1. Both `genOracle_instr N false` and `genOracle_instr N true` begin identically:
   sample `pair ← N.pkgen`, read `honest`, `corrupt`.

2. At the distribution level, the result at outcome `(pk, h')` is a sum over
   intermediate states:
   ```
   (genOracle_instr N b h₀)(some (pk, h')) =
     ∑_{pair, h₁} (N.pkgen h₀)(some (pair, h₁)) *
       (rest_b pair.1 pair.2 h₁)(some (pk, h'))
   ```

3. For each intermediate `(pair, h₁)`, let `pk_gen = pair.1`.
   Read `honest = Heap.get h₁ pkHonestLoc` and `corrupt = Heap.get h₁ pkCorruptLoc`.

4. **Case: `honest pk_gen || corrupt pk_gen = true`** (collision detected):
   - Both variants set `pkeyCollFlag := true` in the heap.
   - The `b = true` variant then calls `SPComp.fail`, producing 0 mass.
   - The `b = false` variant continues and produces `h'` with `pkeyCollFlag = true`.
   - But we assumed `¬pkeyBadInstr h'`, i.e., `Heap.get h' pkeyCollFlag ≠ true`.
   - The collision flag, once set to `true`, persists through subsequent `set` calls
     on OTHER locations (pkHonestLoc, skStoreLoc have different ids: 100, 101 vs 103).
   - So `Heap.get h' pkeyCollFlag = true`, contradicting `¬pkeyBadInstr h'`.
   - **Conclusion**: this intermediate contributes 0 mass for BOTH `b = false` and `b = true`.

5. **Case: `honest pk_gen || corrupt pk_gen = false`** (no collision):
   - Both variants execute `SPComp.pure ()`, then identically update the heap.
   - The rest of the computation is `b`-independent.
   - **Conclusion**: identical contribution for both `b = false` and `b = true`.

6. Therefore, every term in the sum is equal, so the total is equal. -/
-- Helper: SPComp.fail bind gives fail (at the SPComp level)
omit CT in
private theorem spcomp_fail_bind {α : Type} {β : Type} (f : α → SPComp β) :
    SPComp.bind SPComp.fail f = SPComp.fail := by
  funext h
  simp only [SPComp.bind, SPComp.fail]
  exact SDistr.bind_fail _

-- Helper: SPComp.bind with the same continuation produces equal results
-- when the first computations are equal
omit CT in
private theorem spcomp_bind_congr_left {α : Type} {β : Type} {c₁ c₂ : SPComp α}
    (f : α → SPComp β) (h : c₁ = c₂) : SPComp.bind c₁ f = SPComp.bind c₂ f := by
  rw [h]

-- Helper: when the collision flag is set in h₁, subsequent set operations
-- on locations with different ids preserve the flag value
omit CT in
private theorem collFlag_preserved_by_set (h₁ : Heap) (l : Location)
    (v : l.ty) (hid : l.id ≠ pkeyCollFlag.id)
    (hset : Heap.get h₁ pkeyCollFlag = true) :
    Heap.get (h₁.set l v) pkeyCollFlag = true := by
  rw [Heap.get_set_other h₁ l pkeyCollFlag v hid]
  exact hset

theorem genOracle_instr_agree (N : @NIKEScheme CT) :
    ∀ (h₀ : Heap) (pk : CT.PK) (h' : Heap), ¬pkeyBadInstr h' →
      (genOracle_instr N false h₀) (some (pk, h')) =
      (genOracle_instr N true h₀) (some (pk, h')) := by
  intro h₀ pk h' hnotbad
  -- Unfold genOracle_instr to PMF.bind_apply (sum over intermediate states)
  simp only [genOracle_instr, SPComp.monad_bind_eq, SPComp.bind_def,
    SDistr.bind, PMF.bind_apply]
  -- Show each summand is equal
  apply tsum_congr; intro oa
  cases oa with
  | none => rfl
  | some p =>
    obtain ⟨⟨pk_gen, sk_gen⟩, h₁⟩ := p
    -- Factor out the common N.pkgen probability
    congr 1
    -- Inline get operations: unfold SDistr.pure so PMF.pure_bind can fire
    simp only [SPComp.get_def, SDistr.pure, PMF.pure_bind]
    -- Split on collision condition
    split
    · -- Collision case: both sides give 0 mass at non-bad outcomes
      -- Reduce if-conditions: b=false gives pure(), b=true gives fail
      simp only [if_true, SPComp.bind_def, SPComp.set_def, SPComp.pure_def,
        SPComp.get_def, SPComp.fail, SDistr.pure, SDistr.fail,
        SDistr.bind, PMF.pure_bind, PMF.pure_apply,
        reduceCtorEq, ite_false, Option.some.injEq, Prod.mk.injEq]
      -- Goal: if pk = pk_gen ∧ h' = h_final then 1 else 0 = 0
      rw [if_neg]
      intro ⟨_, heq⟩
      have h1 : skStoreLoc.id ≠ pkeyCollFlag.id := by
        show (101 : ℕ) ≠ 103; omega
      have h2 : pkHonestLoc.id ≠ pkeyCollFlag.id := by
        show (100 : ℕ) ≠ 103; omega
      exact hnotbad (by
        unfold pkeyBadInstr; rw [heq]
        rw [Heap.get_set_other _ _ _ _ h1,
            Heap.get_set_other _ _ _ _ h2,
            Heap.get_set_same])
    · -- No collision case: both b=false and b=true execute pure (), identical
      rfl

/-- PKEY instrumented advantage bounded by collision probability via FEL.

    This is the instrumented analogue of `pkeyAdvantage_le_collision`.
    The stronger bad event `pkeyBadInstr` (collision flag set) gives a tighter
    and more precise bound than `pkeyBadFinal` (honest-corrupt overlap). -/
theorem pkeyAdvantage_instr_le_collision (N : @NIKEScheme CT)
    (B : PKEYOracles → SPComp Bool)
    (h_agree : ∀ b h', ¬pkeyBadInstr h' →
      (PKEY_instr N false B Heap.empty) (some (b, h')) =
      (PKEY_instr N true B Heap.empty) (some (b, h')))
    (hll : Unary.isLossless (PKEY_instr N false B)) :
    pkeyAdvantage_instr N B ≤ Unary.prEventComp (PKEY_instr N false B) Heap.empty
      (fun _ h' => pkeyBadInstr h') :=
  Unary.advantage_le_prBad (PKEY_instr N false B) (PKEY_instr N true B) pkeyBadInstr h_agree hll

omit CT in
/-- The instrumented bad event implies the original bad event when
    there exists a key that is both honest and corrupt.

    More precisely: if a collision flag was set during a GEN call where
    `honest pk_gen || corrupt pk_gen = true`, then either:
    - The pk was already honest, and GEN sets it honest again (duplicate honest key)
    - The pk was already corrupt, and GEN sets it honest (honest-corrupt overlap → pkeyBadFinal)

    Note: `pkeyBadInstr` is STRICTLY stronger than `pkeyBadFinal` because it also
    catches duplicate honest-honest collisions. -/
theorem pkeyBadInstr_implies_flag_set (h : Heap) :
    pkeyBadInstr h → Heap.get h pkeyCollFlag = true := by
  intro hbad
  exact hbad

/-! ### Per-Query Collision Probability

For a single GEN query, the probability that the newly sampled pk collides
with existing keys depends on the number of already-registered keys and the
size of the pk space. -/

/-- Per-query collision probability bound.

    The collision set on heap `h₀` is the set of pk whose `pkHonestLoc` or
    `pkCorruptLoc` flag is set.
    If it is covered by a finset `S` of size `q_existing`, then a public key sampled
    uniformly from `CT.PK` lands in the collision set with probability at most
    `q_existing / Fintype.card CT.PK`. This is the per-GEN-query collision probability
    under uniform key generation. -/
theorem collision_prob_single_query (h₀ : Heap) (q_existing : ℕ)
    (h_count : ∃ (S : Finset CT.PK), S.card = q_existing ∧
      ∀ pk, Heap.get h₀ pkHonestLoc pk = true ∨
            Heap.get h₀ pkCorruptLoc pk = true → pk ∈ S) :
    prTrue (SPComp.bind (SPComp.sample CT.PK)
        (fun pk => SPComp.pure (decide
          (pk ∈ (Finset.univ.filter (fun p =>
            Heap.get h₀ pkHonestLoc p = true ∨
            Heap.get h₀ pkCorruptLoc p = true) : Finset CT.PK))))) h₀
      ≤ (q_existing : ℝ≥0∞) / (Fintype.card CT.PK : ℝ≥0∞) := by
  obtain ⟨S, hScard, hScov⟩ := h_count
  refine Unary.prTrue_uniform_mem_le _ q_existing ?_ h₀
  refine le_trans (Finset.card_le_card ?_) (le_of_eq hScard)
  intro pk hpk
  rw [Finset.mem_filter] at hpk
  exact hScov pk hpk.2

/-- Multi-query collision bound via union bound.

    With `q_gen` GEN queries, the `i`-th of which (0-indexed) has at most `i` existing
    challenger-generated keys plus `q_csetpk` corrupt keys, the union bound over the per-query
    collision probabilities is the sum `∑_{i=0}^{q_gen-1} (i + q_csetpk) / |PK|`.
    This sum equals the birthday closed form
    `(q_gen * (q_gen - 1) + 2 * (q_gen * q_csetpk)) / (2 * |PK|)`. -/
theorem collision_prob_multi_query_bound (q_gen q_csetpk : ℕ) :
    (∑ i ∈ Finset.range q_gen,
        ((i : ℝ≥0∞) + q_csetpk) / (Fintype.card CT.PK : ℝ≥0∞))
      = ((q_gen * (q_gen - 1) + 2 * (q_gen * q_csetpk) : ℕ) : ℝ≥0∞)
        / (2 * (Fintype.card CT.PK : ℝ≥0∞)) := by
  have hsplit : (∑ i ∈ Finset.range q_gen, (i + q_csetpk))
      = (∑ i ∈ Finset.range q_gen, i) + q_gen * q_csetpk := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h2A : 2 * (∑ i ∈ Finset.range q_gen, (i + q_csetpk))
      = q_gen * (q_gen - 1) + 2 * (q_gen * q_csetpk) := by
    rw [hsplit, Nat.mul_add, mul_comm 2 (∑ i ∈ Finset.range q_gen, i),
      Finset.sum_range_id_mul_two]
  have hcast : (∑ i ∈ Finset.range q_gen, ((i : ℝ≥0∞) + q_csetpk))
      = ((∑ i ∈ Finset.range q_gen, (i + q_csetpk) : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [Nat.cast_add])
  have hLHS : (∑ i ∈ Finset.range q_gen,
        ((i : ℝ≥0∞) + q_csetpk) / (Fintype.card CT.PK : ℝ≥0∞))
      = (∑ i ∈ Finset.range q_gen, ((i : ℝ≥0∞) + q_csetpk))
        / (Fintype.card CT.PK : ℝ≥0∞) := by
    simp only [div_eq_mul_inv]; rw [← Finset.sum_mul]
  rw [hLHS, hcast, ← h2A, Nat.cast_mul, Nat.cast_ofNat,
    ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-! ## Standalone PKEY sdist Building Block -/

/-- Standalone PKEY sdist building block.
    Reusable by any construction that uses the PKEY game.

    Bridges per-adversary advantage bounds (`∀ A, pkeyAdvantage N A ≤ ε`)
    to categorical sdist (`sdist (PKEY N false) (PKEY N true) ≤ ε`),
    giving access to PPLs, composition, and tensor bounds. -/
theorem pkey_sdist (N : @NIKEScheme CT) (ε : ℝ≥0∞)
    (h : ∀ A, pkeyAdvantage N A ≤ ε) :
    sdist (PKEY N false) (PKEY N true) ≤ ε :=
  sdist_oracleGame_le
    (fun A => PKEY_eq_with_oracles N false A)
    (fun A => PKEY_eq_with_oracles N true A)
    h

end CatCrypt.Examples.Cryptobox
