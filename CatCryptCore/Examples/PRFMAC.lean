/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.MAC
public import CatCryptCore.Examples.PRF
public import CatCryptCore.Prob.XorBij
public import CatCryptCore.Crypto.PRPPRFSwitching

/-!
# MAC from PRF Construction

This file formalizes Claim 10.4 of "The Joy of Cryptography" (online edition,
Chapter 10, Message Authentication Codes):
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

## Main Results

`prfMAC_euf_cma_adv_le`: for a keyed function `F : K → D → T` and every
adversary `A` of the adaptive EUF-CMA game with a tagging oracle, the forgery
probability against the MAC `m ↦ F k m` is at most the adaptive PRF advantage
of the reduction `prfMacRed A` against `F` plus `1/|T|`.
`prf_euf_cma_adv_le` instantiates it at `prf` over `Bool`, with `1/2`.

`mac_forgery_advantage_le_half`: for a forgery on an unqueried message, every
distinguisher has advantage at most `1/2 = 1/|Word|` between the real and the
ideal single-sample game. This is an information-theoretic bound over `Bool`.

## References

* [Rosulek, The Joy of Cryptography, online edition, Chapter 10, Claim 10.4]
* [SSProve PRFMAC.v](https://github.com/SSProve/ssprove/blob/main/theories/Crypt/examples/PRFMAC.v)
-/

@[expose] public section

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
  simp_all

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
  grind

/-! ### Main Security Theorem

The MAC constructed from a PRF is secure. The advantage is bounded by:
- The PRF advantage (how distinguishable PRF is from random)
- The statistical gap (probability of successful guess on unqueried input)

For our simplified Bool model with XOR "PRF", both are zero, giving perfect security.
-/

/-!
### Perfect indistinguishability fails on an unqueried message

When `m_check ≠ m`, the real game returns a uniform Boolean (the guess is checked
against the PRF output) and the ideal game returns `false`. The identity
distinguisher separates them with advantage `1/2`, so no equality coupling between
the two games exists (`not_rHoare_macReal_macIdeal_of_ne`). The gap is the
statistical term of the PRF-MAC bound: `1/2` over `Bool`, `1/2^n` over `{0,1}^n`.
The security statement is therefore an advantage bound (`mac_forgery_advantage_le_half`).
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
  simp_all

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
  simp_all [SDistr.uniform_bind_const]

/-- `prTrue` of a constant Boolean computation from the empty heap. -/
theorem prTrue_pure_empty (b : Bool) :
    prTrue (SPComp.pure b) Heap.empty = if b then 1 else 0 := by
  unfold prTrue SPComp.pure
  simp only [SDistr.pure, PMF.pure_apply, Option.some.injEq, Prod.mk.injEq]
  cases b with
  | true =>
    simp only [true_and, ite_true]
    simp_all [tsum_ite_eq]
  | false =>
    simp_all [false_and, tsum_zero]

/-- Refutation of perfect indistinguishability for a forgery on an unqueried
message: for `m_check ≠ m` there is no equality coupling between `macReal` and
`macIdeal`. The identity distinguisher has advantage `1/2`, while an equality
coupling forces advantage `0`. -/
theorem not_rHoare_macReal_macIdeal_of_ne (m m_check : Word) (t_guess : Word)
    (hdiff : m_check ≠ m) :
    ¬ rHoare eqPre (macReal m m_check t_guess) (macIdeal m m_check t_guess) eqPost := by
  intro hc
  have h1 := advantage_zero_of_rHoare _ _ hc SPComp.pure
  have h0 := advantage_zero_of_rHoare _ _
    (forgery_diff_message_uniform m m_check t_guess hdiff) SPComp.pure
  rw [macIdeal_diff_eq_pure_false m m_check t_guess hdiff] at h1
  have hzero : AdvantageA (SPComp.sample Bool) (SPComp.pure false) SPComp.pure = 0 := by
    apply le_antisymm _ zero_le
    have h0' : Advantage ((SPComp.sample Bool).bind SPComp.pure)
        ((macReal m m_check t_guess).bind SPComp.pure) = 0 := by
      rw [Advantage_sym]; exact h0
    calc AdvantageA (SPComp.sample Bool) (SPComp.pure false) SPComp.pure
        ≤ Advantage ((SPComp.sample Bool).bind SPComp.pure)
            ((macReal m m_check t_guess).bind SPComp.pure) +
          AdvantageA (macReal m m_check t_guess) (SPComp.pure false) SPComp.pure :=
          advantage_triangle _ _ _
      _ = 0 := by simp_all [add_zero]
  unfold AdvantageA Advantage at hzero
  rw [SPComp.pure_bind, prTrue_bind_sample_Bool, prTrue_pure_empty, prTrue_pure_empty]
    at hzero
  simp_all

/-! ## Security Statement

Over `Bool` with the XOR function, the only gap between the real and the ideal
game on an unqueried message is the probability of guessing the tag of that
message, which is `1/|Word| = 1/2`. The statement below is this single-sample,
information-theoretic bound. It contains no PRF term: the game exposes one tag
check to a fixed guess. The reduction of an adaptive forger to the PRF game
(Rosulek, Claim 10.4) is `prfMAC_euf_cma_adv_le` below.
-/

/-- **Forgery on an unqueried message, statistical bound.** For a forgery
attempt `(m_check, t_guess)` on a message `m_check ≠ m`, every distinguisher `A`
separates the real from the ideal MAC game with advantage at most `1/2`
(`= 1/|Word|`). The real game returns a uniform bit
(`forgery_diff_message_uniform`), the ideal game returns `false`
(`macIdeal_diff_eq_pure_false`), and a uniform bit is at distance `1/2` from a
constant. -/
theorem mac_forgery_advantage_le_half
    (m m_check : Word) (t_guess : Word) (hdiff : m_check ≠ m) (A : Bool → SPComp Bool) :
    mac_forgery_advantage m m_check t_guess A ≤ (2 : ℝ≥0∞)⁻¹ := by
  show AdvantageA (macReal m m_check t_guess) (macIdeal m m_check t_guess) A ≤ _
  have h0 : AdvantageA (macReal m m_check t_guess) (SPComp.sample Bool) A = 0 :=
    advantage_zero_of_rHoare _ _ (forgery_diff_message_uniform m m_check t_guess hdiff) A
  have h12 : AdvantageA (SPComp.sample Bool) (macIdeal m m_check t_guess) A ≤ (2 : ℝ≥0∞)⁻¹ := by
    rw [macIdeal_diff_eq_pure_false m m_check t_guess hdiff]
    grind [advantage_sample_vs_pure_false]
  calc AdvantageA (macReal m m_check t_guess) (macIdeal m m_check t_guess) A
      ≤ AdvantageA (macReal m m_check t_guess) (SPComp.sample Bool) A +
        AdvantageA (SPComp.sample Bool) (macIdeal m m_check t_guess) A := by
          unfold AdvantageA; exact advantage_triangle _ _ _
    _ ≤ 0 + (2 : ℝ≥0∞)⁻¹ := add_le_add (le_of_eq h0) h12
    _ = (2 : ℝ≥0∞)⁻¹ := zero_add _

/-! ## Adaptive EUF-CMA security by reduction to the PRF

For a keyed function `F : K → D → T`, the MAC `prfMACScheme F` tags `m` with
`F k m`. A forger `A` in the adaptive EUF-CMA game (`EUF_CMA_Adv`) is turned
into a PRF distinguisher `prfMacRed A`, which answers the tag queries of `A`
with its own oracle and checks the forgery with one more oracle query.
With the keyed oracle, the distinguisher outputs exactly the EUF-CMA outcome
(`run_keyedOracle_prfMacRedAux`). With the lazily sampled random function, the
forged message is fresh, its value is uniform, and the distinguisher outputs
`true` with probability at most `1/|T|` (`run_rfOracle_prfMacRedAux_le`).
-/

section Reduction

open CatCrypt.Crypto.PRPPRF CatCrypt.Crypto.SecurityDefs

variable {K D T : Type} [Fintype K] [Nonempty K] [DecidableEq D]
  [Fintype T] [Nonempty T] [DecidableEq T]

/-- The MAC of a keyed function `F`: the tag of `m` under `k` is `F k m`, and a
tag is verified by recomputation. -/
abbrev prfMACScheme (F : K → D → T) : MACScheme where
  Key := K
  Message := D
  Tag := T
  mac := F

/-- The PRF distinguisher run on a forger `A` that has queried the messages in
`log`: tag queries are forwarded to the distinguisher's oracle and recorded; on
the forgery `(m, t)` it returns `false` when `m` is in `log`, and otherwise
queries `m` and returns whether the answer equals `t`. -/
def prfMacRedAux : OracleAdv D T (D × T) → List D → OracleAdv D T Bool
  | .ret r, log => if r.1 ∈ log then .ret false else .query r.1 fun t' => .ret (r.2 == t')
  | .rand p k, log => .rand p fun b => prfMacRedAux (k b) log
  | .query d k, log => .query d fun t' => prfMacRedAux (k t') (d :: log)

/-- The PRF distinguisher built from an EUF-CMA forger `A`: it runs `A`,
answers each tag query with its own oracle, and returns `true` iff the forgery
is on an unqueried message and equals the oracle's answer on that message. -/
def prfMacRed (A : OracleAdv D T (D × T)) : OracleAdv D T Bool :=
  prfMacRedAux A []

/-- A bind is bounded at `b` by a bound on every continuation from the support. -/
private theorem bind_apply_le_of_support' {α β : Type} (p : PMF α) (f : α → PMF β)
    (b : β) (c : ℝ≥0∞) (h : ∀ a ∈ p.support, f a b ≤ c) : p.bind f b ≤ c := by
  rw [PMF.bind_apply]
  calc ∑' a, p a * f a b ≤ ∑' a, p a * c := ENNReal.tsum_le_tsum fun a => by
        by_cases ha : a ∈ p.support
        · exact mul_le_mul_right (h a ha) _
        · simp [(PMF.apply_eq_zero_iff p a).mpr ha]
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Against the keyed oracle `F k`, the distinguisher started with query list
`log` outputs the EUF-CMA outcome of `A` against the tagging oracle under `k`
started with `log`. -/
theorem run_keyedOracle_prfMacRedAux (F : K → D → T) (k : K)
    (A : OracleAdv D T (D × T)) (log : List D) :
    (OracleAdv.run (keyedOracle F k) (prfMacRedAux A log) ()).map Prod.fst =
      (OracleAdv.run (macTagOracle (prfMACScheme F) k) A log).map fun r =>
        (r.1.2 == F k r.1.1) && decide (r.1.1 ∉ r.2) := by
  induction A generalizing log with
  | ret r =>
    by_cases h : r.1 ∈ log
    · simp [prfMacRedAux, h, PMF.pure_map]
    · simp [prfMacRedAux, h, PMF.pure_map, keyedOracle]
  | rand p c ih => simp only [prfMacRedAux, OracleAdv.run_rand, PMF.map_bind, ih]
  | query d c ih =>
    simp [prfMacRedAux, keyedOracle, macTagOracle, ih]

/-- Against the lazily sampled random function, with every message outside
`log` absent from the table `t`, the distinguisher outputs `true` with
probability at most `1/|T|`. -/
theorem run_rfOracle_prfMacRedAux_le (A : OracleAdv D T (D × T)) (log : List D)
    (t : List (D × T)) (ht : ∀ d, d ∉ log → List.lookup d t = none) :
    ((OracleAdv.run rfOracle (prfMacRedAux A log) t).map Prod.fst) true ≤
      1 / (Fintype.card T : ℝ≥0∞) := by
  induction A generalizing log t with
  | ret r =>
    by_cases h : r.1 ∈ log
    · simp [prfMacRedAux, h, PMF.pure_map]
    · have hrun : (OracleAdv.run rfOracle (prfMacRedAux (.ret r) log) t).map Prod.fst =
          (PMF.uniformOfFintype T).map (fun a => r.2 == a) := by
        simp [prfMacRedAux, h, rfOracle, ht r.1 h, PMF.map_bind, PMF.bind_map, PMF.pure_map,
          Function.comp_def]
        rfl
      rw [hrun, PMF.map_apply, tsum_eq_single r.2]
      · simp
      · intro a ha
        simp [Ne.symm ha]
  | rand p c ih =>
    simp only [prfMacRedAux, OracleAdv.run_rand, PMF.map_bind]
    exact bind_apply_le_of_support' _ _ _ _ fun b _ => ih b log t ht
  | query d c ih =>
    simp only [prfMacRedAux, OracleAdv.run_query, PMF.map_bind]
    refine bind_apply_le_of_support' _ _ _ _ fun x hx => ih x.1 (d :: log) x.2 ?_
    intro d' hd'
    simp only [List.mem_cons, not_or] at hd'
    unfold rfOracle at hx
    split at hx <;> simp at hx
    · subst hx; exact ht d' hd'.2
    · obtain ⟨a, rfl⟩ := hx
      have hne : (d' == d) = false := by simpa using hd'.1
      simp [List.lookup, hne, ht d' hd'.2]

/-- **EUF-CMA security of the PRF MAC.** For every forger `A` in the adaptive
EUF-CMA game, the forgery probability against `prfMACScheme F` is at most the
adaptive PRF advantage of `prfMacRed A` against `F` plus `1/|T|`. -/
theorem prfMAC_euf_cma_adv_le (F : K → D → T) (A : EUF_CMA_Adversary (prfMACScheme F)) :
    EUF_CMA_Adv (prfMACScheme F) A ≤
      PRF_q_Advantage F (prfMacRed A) + 1 / (Fintype.card T : ℝ≥0∞) := by
  have hpmf : ∀ p : PMF Bool, prTrue (liftPMF p) Heap.empty = p true := fun p => by
    have h := prTrue_liftPMF_map p id Heap.empty
    rw [PMF.map_id] at h
    rw [h, show {x : Bool | id x = true} = {true} from by ext x; simp,
      PMF.toOuterMeasure_apply_singleton]
  have hreal : prTrue (realGame F (prfMacRed A)) Heap.empty =
      EUF_CMA_Adv (prfMACScheme F) A := by
    rw [realGame, hpmf, EUF_CMA_Adv, EUF_CMA_Real]
    congr 2
    funext k
    rw [prfMacRed, run_keyedOracle_prfMacRedAux]
    congr 1
    funext r
    simp
  have hideal : prTrue (rfGame (prfMacRed A)) Heap.empty ≤ 1 / (Fintype.card T : ℝ≥0∞) := by
    rw [rfGame, hpmf]
    exact run_rfOracle_prfMacRedAux_le A [] [] fun _ _ => rfl
  rw [← hreal]
  calc prTrue (realGame F (prfMacRed A)) Heap.empty
      ≤ (prTrue (realGame F (prfMacRed A)) Heap.empty -
            prTrue (rfGame (prfMacRed A)) Heap.empty)
          + prTrue (rfGame (prfMacRed A)) Heap.empty := le_tsub_add
    _ ≤ PRF_q_Advantage F (prfMacRed A) + 1 / (Fintype.card T : ℝ≥0∞) :=
        add_le_add le_sup_left hideal

/-- **EUF-CMA security of the PRF MAC over `Word`.** For `prf k m = k ⊕ m` on
`Bool`, every adaptive forger `A` wins with probability at most the adaptive PRF
advantage of `prfMacRed A` against `prf` plus `1/2`. -/
theorem prf_euf_cma_adv_le (A : EUF_CMA_Adversary (prfMACScheme prf)) :
    EUF_CMA_Adv (prfMACScheme prf) A ≤ PRF_q_Advantage prf (prfMacRed A) + 1 / 2 := by
  simpa using prfMAC_euf_cma_adv_le prf A

end Reduction

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
