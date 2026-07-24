/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.MAC
import CatCryptCore.Examples.PRF
import CatCryptCore.Prob.XorBij

/-!
# MAC from PRF Construction

This file formalizes Claim 10.4 from "The Joy of Cryptography" (p. 188):
constructing a secure MAC (Message Authentication Code) from a PRF
(Pseudorandom Function).

## Overview

The construction is simple:
- Given a PRF F_k: M → T, define:
  - GetTag(m) = F_k(m)
  - CheckTag(m, t) = (F_k(m) == t)

## Security Proof via Game Hopping

The security proof uses a sequence of game hops:

1. **TAG_real** (Real MAC game):
   - GetTag(m) = PRF(k, m) and CheckTag(m, t) = (PRF(k, m) == t)

2. **TAG_EVAL_tt ∘ EVAL_real** (Link with PRF real):
   - GetTag/CheckTag use the PRF lookup interface

3. **TAG_EVAL_tt ∘ EVAL_ideal** (Replace PRF with random):
   - Lookup returns random values (stored in table T)

4. **TAG_GUESS_real** (Intermediate via GUESS package):
   - CheckTag uses the GUESS interface

5. **TAG_GUESS_ideal** (Statistical gap):
   - GUESS returns based on stored table membership

6. **TAG_EVAL_ff ∘ EVAL_ideal** (Dual construction):
   - Uses set S to track (m, t) pairs

7. **TAG_EVAL_ff ∘ EVAL_real** (Back to PRF):
   - Statistical identical to TAG_ideal

8. **TAG_ideal** (Ideal MAC game):
   - GetTag stores (m, t) in set S, CheckTag checks membership

## Main Result

```
Advantage(TAG) ≤ prf_epsilon_1 + statistical_gap + prf_epsilon_2
```

where:
- `prf_epsilon_i` is the PRF advantage for adversary A ∘ TAG_EVAL_pkg_i
- `statistical_gap` is the GUESS distinguishing probability (negligible)

## References

* [Rosulek, The Joy of Cryptography, Claim 10.4]
* [SSProve PRFMAC.v](https://github.com/SSProve/ssprove/blob/main/theories/Crypt/examples/PRFMAC.v)
-/

namespace CatCrypt.Examples.PRFMAC

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Prob
open CatCrypt.Relational
open CatCrypt.Examples.MAC
open CatCrypt.Examples.PRF
open CatCrypt.Prob.XorBij
open scoped ENNReal

/-! ## Type Definitions

Following the Rocq development, we parameterize by:
- n: the security parameter (not used explicitly for Bool, but mirrors the structure)
- Word: the type for messages, tags, and keys (Bool for simplicity)
- PRF: the pseudorandom function family
-/

/-- For simplicity, we use Bool as the word type (represents Z_{2^n} with n=1) -/
abbrev Word := Bool

instance : Fintype Word := inferInstance
instance : Nonempty Word := ⟨false⟩
instance : DecidableEq Word := inferInstance

/-! ## PRF Function

We abstract over the PRF function. In the Rocq version, this is a parameter.
For our Bool instantiation, we use XOR (same as in PRF.lean and MAC.lean). -/

/-- The PRF function: key → message → tag.
    For Bool, we use XOR which is a bijection. -/
def prf (k : Word) (m : Word) : Word := xor k m

/-! ## Memory Locations

The proof uses several memory locations for state:
- k_loc: the PRF key (Option Word, None means not yet sampled)
- T_loc: random function table (Map Word Word)
- S_loc: set of (message, tag) pairs that have been issued

In Lean, we model these using the Heap abstraction from CatCrypt.Core.
For this example, we use simplified in-line state rather than explicit locations.
-/

/-! ## Operation Identifiers -/

def LOOKUP : ℕ := 3
def GETTAG : ℕ := 5
def CHECKTAG : ℕ := 6
def GUESS : ℕ := 7

/-! ## EVAL Package (PRF/Random Function)

The EVAL package provides a lookup interface that can be either:
- EVAL_real: Uses the PRF with a sampled key
- EVAL_ideal: Uses a truly random function (lazy-sampled table)
-/

/-- EVAL_real: lookup returns PRF(k, m) for a lazily-sampled key k.

    First call samples the key, subsequent calls use the same key.
    Models: lookup(m) = F_k(m) -/
noncomputable def EVAL_real (m : Word) : SPComp Word := do
  let k ← SPComp.sample Word  -- In full version, this would be memoized
  SPComp.pure (prf k m)

/-- EVAL_ideal: lookup returns a random value, maintaining consistency via table T.

    If T[m] exists, return it; otherwise sample fresh, store in T, return.
    Models a truly random function. -/
noncomputable def EVAL_ideal (T : Word → Option Word) (m : Word) : SPComp (Word × (Word → Option Word)) := do
  match T m with
  | some r => SPComp.pure (r, T)
  | none =>
    let r ← SPComp.sample Word
    let T' := fun m' => if m' = m then some r else T m'
    SPComp.pure (r, T')

/-! ## GUESS Package

The GUESS package is an intermediate abstraction that helps with the game hopping.
- GUESS_real: guess(m, t) checks if t equals the value in table T
- GUESS_ideal: guess(m, t) checks if t was previously returned by lookup(m)

The key insight is that these are statistically close when T is random.
-/

/-- GUESS_real: checks if guessed tag matches the random table value.
    Returns (t == T[m]) where T[m] is lazily sampled if needed. -/
noncomputable def GUESS_real (T : Word → Option Word) (m : Word) (t : Word)
    : SPComp (Bool × (Word → Option Word)) := do
  match T m with
  | some r => SPComp.pure (t == r, T)
  | none =>
    let r ← SPComp.sample Word
    let T' := fun m' => if m' = m then some r else T m'
    SPComp.pure (t == r, T')

/-- GUESS_ideal: checks if (m, t) was previously issued.
    Returns true iff some T[m] = t (i.e., t was the lookup result). -/
noncomputable def GUESS_ideal (T : Word → Option Word) (m : Word) (t : Word)
    : SPComp Bool := do
  SPComp.pure (T m == some t)

/-! ## TAG Package (MAC Interface)

The TAG package is the MAC construction we're proving secure.
- TAG_real: Uses PRF directly
- TAG_ideal: Uses a set S to track issued tags; CheckTag only succeeds for issued pairs
-/

/-- TAG_real: The real MAC game.
    - GetTag(m) = PRF(k, m)
    - CheckTag(m, t) = (t == PRF(k, m))

    Note: Key k is sampled lazily on first use. -/
noncomputable def TAG_real_gettag (m : Word) : SPComp Word := do
  let k ← SPComp.sample Word  -- Would be memoized in full version
  SPComp.pure (prf k m)

noncomputable def TAG_real_checktag (m : Word) (t : Word) : SPComp Bool := do
  let k ← SPComp.sample Word  -- Would be memoized in full version
  SPComp.pure (t == prf k m)

/-- TAG_ideal: The ideal MAC game with perfect unforgeability.
    - GetTag(m): computes t = PRF(k, m), stores (m, t) in set S, returns t
    - CheckTag(m, t): returns (m, t) ∈ S

    The adversary can only succeed on CheckTag for tags they've received. -/
noncomputable def TAG_ideal_gettag (S : Word × Word → Bool) (m : Word)
    : SPComp (Word × (Word × Word → Bool)) := do
  let k ← SPComp.sample Word  -- Would be memoized in full version
  let t := prf k m
  let S' := fun p => p == (m, t) || S p
  SPComp.pure (t, S')

noncomputable def TAG_ideal_checktag (S : Word × Word → Bool) (m : Word) (t : Word)
    : SPComp Bool := do
  SPComp.pure (S (m, t))

/-! ## Simplified Game Definitions

For the security proof, we define the games as SPComp computations.
We use a simplified model where state is threaded explicitly through the computations.
-/

/-- Real MAC game: given message m, return (tag, verification_result).
    Models the real-world behavior where CheckTag uses the actual PRF. -/
noncomputable def macReal (m m_check : Word) (t_guess : Word) : SPComp Bool := do
  -- Sample key (in full version, would be memoized)
  let k ← SPComp.sample Word
  -- GetTag: t = PRF(k, m)
  let _t := prf k m
  -- CheckTag: verify the guess
  SPComp.pure (t_guess == prf k m_check)

/-- Ideal MAC game: CheckTag only succeeds for previously issued tags.
    When m_check ≠ m (different message), forgery always fails. -/
noncomputable def macIdeal (m m_check : Word) (t_guess : Word) : SPComp Bool := do
  let k ← SPComp.sample Word
  let t := prf k m
  -- Ideal: only succeed if (m_check, t_guess) was issued
  -- Since we only issued (m, t), succeed iff m_check = m ∧ t_guess = t
  SPComp.pure (m_check == m && t_guess == t)

/-! ## Game Hopping Lemmas

The security proof proceeds by a sequence of game hops, relating:
TAG_real ≈ TAG_EVAL ∘ EVAL_real ≈ TAG_EVAL ∘ EVAL_ideal
         ≈ TAG_GUESS ∘ GUESS_real ≈ TAG_GUESS ∘ GUESS_ideal
         ≈ TAG_ideal

Each hop is either:
1. Perfect equivalence (code transformation)
2. Bounded by PRF advantage
3. Bounded by statistical gap (negligible)
-/

/-! ### Core Lemma: PRF output uniformity

When the key k is uniformly random, prf(k, m) = k XOR m is uniformly distributed.
This is the key property enabling the security reduction. -/

theorem prf_uniform (m : Word) :
    rHoare
      eqPre
      (do let k ← SPComp.sample Word; SPComp.pure (prf k m))
      (SPComp.sample Word)
      eqPost := by
  intro h₁ h₂ hheq
  simp only [eqPre] at hheq
  subst hheq
  -- Simplify both computations
  simp only [SPComp.monad_bind_eq]
  rw [SPComp.sample_bind_pure, SPComp.sample_bind_pure_id]
  -- Use bijection coupling: boolXorBij m : k ↦ k ⊕ m
  apply liftR_bind (liftR_uniform_bij (boolXorBij m))
  intro k r hkr
  -- hkr : boolXorBij m k = r, i.e., k ⊕ m = r
  apply liftR_pure
  simp only [eqPost, boolXorBij_apply, prf] at hkr ⊢
  exact ⟨hkr, trivial⟩

/-! ### Hop 1: TAG_real ≈ TAG_EVAL_tt ∘ EVAL_real

This is a perfect equivalence by construction: both compute PRF(k, m). -/

theorem hop1_equiv (m m_check : Word) (t_guess : Word) :
    macReal m m_check t_guess =
    (do let k ← SPComp.sample Word
        let _t := prf k m  -- GetTag via EVAL
        SPComp.pure (t_guess == prf k m_check)) := by
  rfl

/-! ### Statistical Gap Lemma

The key statistical insight: when T is a random function and (m, t) was not queried,
the probability that t = T[m] is 1/|Word| = 1/2 for Bool.

For GUESS_real vs GUESS_ideal:
- GUESS_real: returns (t == T[m]) where T[m] is random
- GUESS_ideal: returns (T m == some t), which is true iff t was the lookup result

When the adversary hasn't queried lookup(m), GUESS_real returns true with prob 1/2,
while GUESS_ideal returns false. This is the statistical gap.

For our simplified Bool case, we can show perfect security under certain conditions.
-/

/-- When m_check ≠ m (forgery attempt on different message),
    the verification result is uniformly distributed in the real game. -/
theorem forgery_diff_message_uniform (m m_check : Word) (t_guess : Word)
    (hdiff : m_check ≠ m) :
    rHoare
      eqPre
      (macReal m m_check t_guess)
      (SPComp.sample Bool)
      eqPost := by
  intro h₁ h₂ hheq
  simp only [eqPre] at hheq
  subst hheq
  -- Real game: sample k, return (t_guess == k ⊕ m_check)
  unfold macReal prf
  simp only [SPComp.monad_bind_eq]
  rw [SPComp.sample_bind_pure, SPComp.sample_bind_pure_id]
  -- The output is (t_guess == k ⊕ m_check) where k is uniform
  -- This is uniform over Bool because boolXorBij m_check is a bijection
  -- Specifically: k ↦ (t_guess == k ⊕ m_check) is a bijection
  let bij : Bool ≃ Bool := {
    toFun := fun k => t_guess == xor k m_check
    invFun := fun b => xor (if b then t_guess else !t_guess) m_check
    left_inv := by
      intro k
      cases k <;> cases t_guess <;> cases m_check <;> rfl
    right_inv := by
      intro b
      cases b <;> cases t_guess <;> cases m_check <;> rfl
  }
  apply liftR_bind (liftR_uniform_bij bij)
  intro k r hkr
  apply liftR_pure
  simp only [eqPost]
  exact ⟨hkr, trivial⟩

/-! ### Main Security Theorem

The MAC constructed from a PRF is secure. The advantage is bounded by:
- The PRF advantage (how distinguishable PRF is from random)
- The statistical gap (probability of successful guess on unqueried input)

For our simplified Bool model with XOR "PRF", both are zero, giving perfect security.
-/

/-!
### Why Perfect Indistinguishability Fails

The following theorem is **FALSE** and cannot be proven:

```
theorem prfmac_forgery_bound_FALSE (m m_check : Word) (t_guess : Word)
    (hdiff : m_check ≠ m) :
    rHoare eqPre (macReal m m_check t_guess) (macIdeal m m_check t_guess) eqPost
```

**Reason:** When m_check ≠ m (forgery on a different message):
- **Real game**: Returns uniform Bool (verification against PRF output)
- **Ideal game**: Always returns false (message wasn't queried)

These distributions ARE distinguishable with probability 1/2.

**This is precisely the statistical gap in the PRF-MAC security proof.**
- For Bool (n=1): gap = 1/2 (significant)
- For Word = {0,1}^n: gap = 1/2^n (negligible)

The correct security statement is an ADVANTAGE BOUND, not perfect equality.
-/

/-- The advantage in distinguishing real vs ideal MAC for forgery attempts.

    When m_check ≠ m, the distinguishing advantage equals the statistical gap:
    - Real: Pr[t_guess == PRF(k, m_check)] = 1/2 for uniform k
    - Ideal: Pr[false] = 0

    An adversary that outputs "real" when verification succeeds and "ideal"
    when it fails has advantage |1/2 - 0| = 1/2 for Bool.

    For the full security proof, this gap is bounded by 1/|Word| = 1/2^n,
    which is negligible for large n. -/
noncomputable def mac_forgery_advantage (m m_check : Word) (t_guess : Word)
    (A : Bool → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (macReal m m_check t_guess) (macIdeal m m_check t_guess) A

/-- When messages match (m_check = m), verification behaves identically in both games
    for the correct tag. This is the "no forgery needed" case. -/
theorem mac_same_message_correct_tag (m : Word) (k : Word) :
    (prf k m == prf k m) = true := by
  simp only [beq_self_eq_true]

/-- For same message, both games agree on correct tag verification. -/
theorem mac_same_message_coupling (m : Word) (t_guess : Word) :
    rHoare
      eqPre
      (macReal m m t_guess)
      (macIdeal m m t_guess)
      eqPost := by
  intro h₁ h₂ hheq
  simp only [eqPre] at hheq
  subst hheq
  unfold macReal macIdeal prf
  simp only [SPComp.monad_bind_eq, beq_self_eq_true, Bool.true_and]
  apply liftR_mono _ (liftR_refl _)
  intro p₁ p₂ heq
  simp only [eqPost]
  rw [heq]
  exact ⟨rfl, rfl⟩

/-! ## macIdeal Simplification -/

/-- When messages differ, the ideal MAC game always returns false.
    Since m_check ≠ m, the check `m_check == m` is false, making the
    entire conjunction false regardless of the key. -/
theorem macIdeal_diff_eq_pure_false (m m_check : Word) (t_guess : Word)
    (hdiff : m_check ≠ m) :
    macIdeal m m_check t_guess = SPComp.pure false := by
  funext h
  have hbeq : ∀ k : Word, (m_check == m && t_guess == xor k m) = false := by
    intro k; cases m_check <;> cases m <;> simp_all
  simp only [macIdeal, prf, SPComp.monad_bind_eq, SPComp.bind_def, SPComp.sample,
    SPComp.pure_def, SDistr.bind_assoc, SDistr.pure_bind, hbeq]
  exact SDistr.uniform_bind_const _

/-! ## Security Statement

The full security theorem would state:

```
Advantage_MAC(A) ≤ Advantage_PRF(A ∘ Wrapper₁) +
                   Statistical_Gap(A) +
                   Advantage_PRF(A ∘ Wrapper₂)
```

For our simplified Bool model:
- The PRF advantage is 0 (XOR with random key is perfectly random)
- The statistical gap is 1/2 for a single guess on Bool

In a proper cryptographic setting with security parameter n:
- Word = {0,1}^n (2^n elements)
- Statistical gap = 1/2^n per query (negligible)
- PRF advantage is negligible by assumption
-/

/-- The PRF epsilon: advantage in distinguishing PRF from random function.
    For our XOR construction over Bool, this is 0. -/
noncomputable def prf_epsilon (A : Word → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (do let k ← SPComp.sample Word; TAG_real_gettag k)
             (do let r ← SPComp.sample Word; SPComp.pure r) A

/-- The statistical gap: advantage in the GUESS game.
    For Bool, this represents the probability of a lucky guess. -/
noncomputable def statistical_gap (_m : Word) (_t : Word) : ℝ≥0∞ :=
  -- Pr[random key k : t = PRF(k, m)] = 1/2 for Bool
  -- This bounds the forgery probability on unqueried messages
  1 / 2

/-- Main security theorem: MAC forgery advantage is bounded.

    The advantage of any adversary A against the MAC scheme is bounded by
    the sum of PRF advantages and the statistical gap:

    ```
    mac_forgery_advantage ≤ prf_epsilon₁ + statistical_gap + prf_epsilon₂
    ```

    For the Bool/XOR construction:
    - PRF advantages are 0 (perfect PRF security)
    - Statistical gap is 1/2 per query

    In a proper crypto setting with security parameter n:
    - Statistical gap is 1/2^n (negligible)
    - PRF advantages are negligible by assumption

    **Proof Status:** The individual game hop lemmas are proved:
    - `prf_uniform`: PRF output is uniformly distributed (bijection coupling)
    - `mac_same_message_coupling`: same-message case is perfectly coupled
    - `forgery_diff_message_uniform`: different-message forgery is uniform

    The full chaining requires package composition (`link`) and the advantage
    triangle inequality. The shallow `RawPackage` layer does not support
    linking (see `RawPackage.link` WARNING). Use the deep embedding layer
    (`DeepPackage.link`, `runPkg_link`) for the complete proof. -/
theorem security_based_on_prf
    (m m_check : Word)                 -- Honest and forgery messages
    (t_guess : Word)                   -- Forgery attempt tag
    (hdiff : m_check ≠ m) :            -- Must be a different message
    mac_forgery_advantage m m_check t_guess ≤
      fun A => prf_epsilon A + statistical_gap m t_guess + prf_epsilon A := by
  intro A
  show AdvantageA (macReal m m_check t_guess) (macIdeal m m_check t_guess) A ≤ _
  -- Key facts
  have hideal : macIdeal m m_check t_guess = SPComp.pure false :=
    macIdeal_diff_eq_pure_false m m_check t_guess hdiff
  have h0 : AdvantageA (macReal m m_check t_guess) (SPComp.sample Bool) A = 0 :=
    advantage_zero_of_rHoare _ _ (forgery_diff_message_uniform m m_check t_guess hdiff) A
  have h12 : AdvantageA (SPComp.sample Bool) (macIdeal m m_check t_guess) A ≤ (2 : ℝ≥0∞)⁻¹ := by
    rw [show macIdeal m m_check t_guess = SPComp.pure false from hideal]
    exact advantage_sample_vs_pure_false A
  -- Triangle inequality through sample Bool, then pad with prf_epsilon ≥ 0
  calc AdvantageA (macReal m m_check t_guess) (macIdeal m m_check t_guess) A
      ≤ AdvantageA (macReal m m_check t_guess) (SPComp.sample Bool) A +
        AdvantageA (SPComp.sample Bool) (macIdeal m m_check t_guess) A := by
          unfold AdvantageA; exact advantage_triangle _ _ _
    _ ≤ 0 + (2 : ℝ≥0∞)⁻¹ := add_le_add (le_of_eq h0) h12
    _ = (2 : ℝ≥0∞)⁻¹ := zero_add _
    _ = statistical_gap m t_guess := by unfold statistical_gap; simp [one_div]
    _ ≤ prf_epsilon A + statistical_gap m t_guess + prf_epsilon A :=
        le_trans le_add_self le_self_add

/-! ## Discussion

### Relation to Rocq SSProve

The Rocq development (PRFMAC.v) proves the full security theorem with:

1. **Package Infrastructure**: Packages with interfaces, locations, and composition
2. **Game Hopping**: Using `ssprove triangle` tactic for advantage bounds
3. **Invariant Proofs**: Relational invariants for state correspondence

This Lean port demonstrates:
- The core game definitions (TAG, EVAL, GUESS packages as SPComp)
- The key bijection coupling technique for PRF uniformity
- The structure of the security argument

### What Would Complete the Port

1. **Package Linking**: Formal `link` operation for composing packages
2. **Advantage Bounds**: Triangle inequality for chaining game hops
3. **Stateful Invariants**: Formal invariants relating table T and set S
4. **Package Validity**: Proofs that adversary locations are disjoint from game state

### The Statistical Gap

The statistical gap arises from the GUESS game:
- GUESS_real: Returns (t == T[m]) for random T[m]
- GUESS_ideal: Returns (m,t) ∈ issued_tags

When the adversary queries CheckTag(m*, t*) for a fresh message m*:
- Real: t* matches a random value with probability 1/|Word|
- Ideal: Returns false (m* wasn't in issued messages)

This gap is 1/|Word| = 1/2^n, which is negligible in n.

### Comparison with Simple XOR MAC (MAC.lean)

MAC.lean shows that a simple XOR MAC is NOT secure: the adversary
can compute k from t = k ⊕ m and forge arbitrary tags.

PRFMAC demonstrates that using a PRF prevents this attack because:
1. The adversary cannot distinguish PRF from random
2. Random functions don't reveal the key from outputs
3. Forging requires guessing PRF outputs, which has negligible probability
-/

end CatCrypt.Examples.PRFMAC
