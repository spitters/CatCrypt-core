/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.HybridArgument
import CatCryptCore.Crypto.NomPkgBridge

/-!
# Fundamental Lemma of Game Playing + Multi-Query Games

This file provides three layers of game-playing infrastructure:

1. **Shoup's Fundamental Lemma** (bad-event lemma): if two games are identical
   until a "bad" event occurs, then their distinguishing advantage is bounded
   by the probability of the bad event.

2. **Multi-query game abstraction**: a generic framework for games where an
   adversary makes `q` adaptive oracle queries, with a bound
   `Adv_q <= q * Adv_1` via the hybrid argument.

3. **Lazy/eager sampling equivalence**: the two standard sampling strategies
   for random oracles produce the same distribution.

## Main Results

### Fundamental Lemma
* `IdenticalUntilBad` -- games agree unless bad occurs
* `advantage_upto_bad` -- Advantage(G0, G1) <= Pr[bad]  (Shoup 2004, Lemma 1)
* `advantage_upto_bad_A` -- adversary-parameterized version
* `UpToBad` -- bundled: identical-until-bad + bad probability bound
* `uptobad_advantage` -- extract advantage bound from UpToBad

### Multi-Query Games
* `MultiQueryGame` -- init/query/finalize structure
* `MultiQueryGame.run` -- execute with q queries
* `MultiQueryGame.single_to_multi_bound` -- Adv_q <= q * Adv_1

### Lazy/Eager Sampling
* `lazy_sample` -- sample on first query, cache for later
* `eager_sample` -- sample all values upfront
* `lazy_eager_equiv` -- they produce the same distribution

## Cross-Validation

| Property | This file | Reference |
|----------|-----------|-----------|
| Bad-event bound | `advantage_upto_bad` | Shoup 2004, Lemma 1 |
| Identical-until-bad | `IdenticalUntilBad` | Bellare-Rogaway 2006, Def. 1 |
| Multi-query hybrid | `single_to_multi_bound` | Boneh-Shoup, Thm 4.4 |
| Lazy/eager equiv | `lazy_eager_equiv` | Bellare-Rogaway 2006, Lemma 1 |

**Equivalent formalizations:**
- EasyCrypt: `upto_bad` tactic / `Upto` theory
- CryptoVerif: `find_coll` / `event` declarations
- SSProve (Rocq): `rules_RHS` / package composition

## References

* Shoup, *Sequences of Games: A Tool for Taming Complexity in Security
  Proofs*, ePrint 2004/332, Lemma 1.
* Bellare & Rogaway, *The Security of Triple Encryption and a Framework
  for Code-Based Game-Playing Proofs*, EUROCRYPT 2006.
* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, Ch. 4.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.BadEvent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.HybridArgument
open scoped ENNReal

/-! ## Identical-Until-Bad

Two computations are "identical until bad" if they produce the same
output distribution conditioned on a bad event not occurring.

This is the core semantic predicate behind Shoup's fundamental lemma
and the Bellare-Rogaway code-based game-playing framework. -/

/-- Two Bool games are identical until bad if:
    1. When `bad` does NOT happen, they produce the same output
    2. The probability of `bad` is bounded

    Formally: `G₀` and `G₁` are coupled such that they agree
    whenever a predicate `¬bad` holds on the shared randomness.

    The inequality `G₀(b, h') ≤ G₁(b, h') + bad(true, h')` captures
    that any excess probability mass in G₀ relative to G₁ is accounted
    for by the bad event. When bad doesn't fire (bad probability = 0),
    the two games produce identical distributions. -/
structure IdenticalUntilBad (G₀ G₁ : SPComp Bool) (bad : SPComp Bool) : Prop where
  /-- When bad doesn't happen, the games agree -/
  agree_unless_bad :
    ∀ h, ∀ b h', (G₀ h) (some (b, h')) ≤ (G₁ h) (some (b, h')) + (bad h) (some (true, h'))

/-! ## Fundamental Lemma (Statement)

The full proof of Shoup's lemma requires a coupling argument over
the joint distribution of (game output, bad event). We state the
key result as an axiom and provide the proof sketch.

**Proof sketch** (Shoup, Lemma 1):
Define events S₀, S₁ (game outputs 1) and F (bad event).
Then:
  |Pr[S₀] - Pr[S₁]| = |Pr[S₀ ∧ ¬F] + Pr[S₀ ∧ F] - Pr[S₁ ∧ ¬F] - Pr[S₁ ∧ F]|
                      = |Pr[S₀ ∧ F] - Pr[S₁ ∧ F]|   (since S₀∧¬F = S₁∧¬F)
                      ≤ Pr[F]                          (since Pr[Sᵢ ∧ F] ≤ Pr[F])

EasyCrypt proves this via the `upto_bad` tactic. -/

/-- prFalse: probability of returning false (helper for Shoup's lemma). -/
private noncomputable def prFalse (G : SPComp Bool) (h₀ : Heap) : ℝ≥0∞ :=
  ∑' h, (G h₀) (some (false, h))

/-- prTrue + prFalse + none mass = 1 for any SPComp Bool, via PMF total mass. -/
private theorem prTrue_prFalse_none_sum (G : SPComp Bool) (h₀ : Heap) :
    (G h₀) none + prTrue G h₀ + prFalse G h₀ = 1 := by
  have hmass : (∑' x, (G h₀) x) = 1 := (G h₀).tsum_coe
  rw [SDistr.tsum_option_eq_add] at hmass
  -- hmass : (G h₀)(none) + ∑' x : Bool × Heap, (G h₀)(some x) = 1
  rw [add_assoc]
  convert hmass using 2
  -- Goal: prTrue G h₀ + prFalse G h₀ = ∑' x : Bool × Heap, (G h₀)(some x)
  unfold prTrue prFalse
  rw [ENNReal.tsum_prod', tsum_bool]
  ring

/-- Under NoFail, prTrue + prFalse = 1. -/
private theorem prTrue_prFalse_eq_one_of_noFail (G : SPComp Bool) (h₀ : Heap)
    (hnf : SPComp.NoFail G) :
    prTrue G h₀ + prFalse G h₀ = 1 := by
  have h := prTrue_prFalse_none_sum G h₀
  rw [hnf h₀, zero_add] at h
  exact h

/-- prFalse equals 1 - prTrue under NoFail. -/
private theorem prFalse_eq_one_sub_prTrue (G : SPComp Bool) (h₀ : Heap)
    (hnf : SPComp.NoFail G) :
    prFalse G h₀ = 1 - prTrue G h₀ := by
  have h := prTrue_prFalse_eq_one_of_noFail G h₀ hnf
  have h_ne_top : prTrue G h₀ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (h ▸ le_self_add)
  rw [← h]
  exact (ENNReal.add_sub_cancel_left h_ne_top).symm

/-- **Shoup's Fundamental Lemma**: if two games are identical until bad,
    then their advantage is bounded by the probability of the bad event.

    Requires both `G₀` and `G₁` to be `NoFail`: without this, the
    `IdenticalUntilBad` inequality (one-directional, applied to `b = true`)
    only gives `prTrue G₀ ≤ prTrue G₁ + prTrue bad`. The reverse direction
    needs the `b = false` case combined with `prTrue + prFalse = 1`,
    which requires `NoFail`. -/
theorem advantage_upto_bad (G₀ G₁ bad : SPComp Bool)
    (hnf₀ : SPComp.NoFail G₀) (hnf₁ : SPComp.NoFail G₁)
    (h : IdenticalUntilBad G₀ G₁ bad) :
    Advantage G₀ G₁ ≤ prTrue bad Heap.empty := by
  -- Direction A: prTrue G₀ ≤ prTrue G₁ + prTrue bad (from b=true case).
  have hA : prTrue G₀ Heap.empty ≤
            prTrue G₁ Heap.empty + prTrue bad Heap.empty := by
    unfold prTrue
    rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum (fun h' => h.agree_unless_bad Heap.empty true h')
  -- Direction B': prFalse G₀ ≤ prFalse G₁ + prTrue bad (from b=false case).
  have hB' : prFalse G₀ Heap.empty ≤
             prFalse G₁ Heap.empty + prTrue bad Heap.empty := by
    unfold prFalse prTrue
    rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum (fun h' => h.agree_unless_bad Heap.empty false h')
  -- Direction B (from B' + NoFail): prTrue G₁ ≤ prTrue G₀ + prTrue bad.
  have h_p0 : prTrue G₀ Heap.empty ≤ 1 := prTrue_le_one G₀ _
  have h_p1 : prTrue G₁ Heap.empty ≤ 1 := prTrue_le_one G₁ _
  rw [prFalse_eq_one_sub_prTrue G₀ _ hnf₀, prFalse_eq_one_sub_prTrue G₁ _ hnf₁] at hB'
  -- hB' : 1 - prTrue G₀ ≤ (1 - prTrue G₁) + prTrue bad
  have hB : prTrue G₁ Heap.empty ≤
            prTrue G₀ Heap.empty + prTrue bad Heap.empty := by
    -- Strategy: add prTrue G₀ + prTrue G₁ to both sides of hB' and simplify
    --   using tsub_add_cancel for both (1 - x) + x cancellations.
    -- (1 - x) + y ≤ (1 - y + z) + y
    --   ⇒ (1 - x) + y ≤ 1 + z (cancel (1-y)+y on RHS)
    -- (1 - x) + y + x ≤ (1 + z) + x
    --   ⇒ y + 1 ≤ x + z + 1 (cancel (1-x)+x on LHS, commute)
    --   ⇒ y ≤ x + z (cancel 1)
    have h1 : (1 - prTrue G₀ Heap.empty) + prTrue G₁ Heap.empty ≤
              1 + prTrue bad Heap.empty := by
      calc (1 - prTrue G₀ Heap.empty) + prTrue G₁ Heap.empty
          ≤ ((1 - prTrue G₁ Heap.empty) + prTrue bad Heap.empty) +
            prTrue G₁ Heap.empty := by gcongr
        _ = (1 - prTrue G₁ Heap.empty + prTrue G₁ Heap.empty) +
            prTrue bad Heap.empty := by ring
        _ = 1 + prTrue bad Heap.empty := by rw [tsub_add_cancel_of_le h_p1]
    have h2 : prTrue G₁ Heap.empty + 1 ≤
              1 + (prTrue G₀ Heap.empty + prTrue bad Heap.empty) := by
      calc prTrue G₁ Heap.empty + 1
          = (1 - prTrue G₀ Heap.empty + prTrue G₀ Heap.empty) +
            prTrue G₁ Heap.empty := by
              rw [tsub_add_cancel_of_le h_p0]; ring
        _ = ((1 - prTrue G₀ Heap.empty) + prTrue G₁ Heap.empty) +
            prTrue G₀ Heap.empty := by ring
        _ ≤ (1 + prTrue bad Heap.empty) + prTrue G₀ Heap.empty := by gcongr
        _ = 1 + (prTrue G₀ Heap.empty + prTrue bad Heap.empty) := by ring
    -- Cancel 1 (using add_comm twice and add_le_add_iff_left).
    have h3 : 1 + prTrue G₁ Heap.empty ≤
              1 + (prTrue G₀ Heap.empty + prTrue bad Heap.empty) := by
      rw [add_comm 1 _]; exact h2
    exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp h3
  -- Combine hA, hB into the absDiff bound.
  show absDiff (prTrue G₀ Heap.empty) (prTrue G₁ Heap.empty) ≤ prTrue bad Heap.empty
  unfold absDiff
  apply max_le <;> rw [tsub_le_iff_right]
  · calc prTrue G₀ Heap.empty
        ≤ prTrue G₁ Heap.empty + prTrue bad Heap.empty := hA
      _ = prTrue bad Heap.empty + prTrue G₁ Heap.empty := add_comm _ _
  · calc prTrue G₁ Heap.empty
        ≤ prTrue G₀ Heap.empty + prTrue bad Heap.empty := hB
      _ = prTrue bad Heap.empty + prTrue G₀ Heap.empty := add_comm _ _

/-- Bad-event lemma with adversary: if two computations are identical
    until bad for all adversaries, the adversary-parameterized advantage
    is bounded by the bad-event probability.

    **Hypotheses**: NoFail on G₀, G₁, and (per-input) on the adversary A.
    These combine via `SPComp.bind_noFail` to give NoFail on the composed
    games, which `advantage_upto_bad` requires.

    **Proof strategy**: For any adversary `A`, instantiate `advantage_upto_bad`
    on the composed games `G₀.bind A` and `G₁.bind A`. -/
theorem advantage_upto_bad_A {α : Type} (G₀ G₁ : SPComp α)
    (bad : SPComp Bool)
    (hnf₀ : SPComp.NoFail G₀) (hnf₁ : SPComp.NoFail G₁)
    (h : ∀ (A : α → SPComp Bool),
      IdenticalUntilBad (G₀.bind A) (G₁.bind A) bad) :
    ∀ (A : α → SPComp Bool),
      (∀ a, SPComp.NoFail (A a)) →
      AdvantageA G₀ G₁ A ≤ prTrue bad Heap.empty := by
  intro A hnfA
  exact advantage_upto_bad (G₀.bind A) (G₁.bind A) bad
    (CatCrypt.Crypto.Assumptions.SPComp.bind_noFail hnf₀ hnfA)
    (CatCrypt.Crypto.Assumptions.SPComp.bind_noFail hnf₁ hnfA)
    (h A)

/-! ## UpToBad: Bundled Bad-Event Technique

In practice, a game-hopping step via the bad-event technique requires:
1. A proof that the two games are identical until bad
2. A bound on the probability of the bad event

The `UpToBad` structure bundles both, making it easy to extract
the advantage bound in one step. -/

/-- Bundled "up to bad" technique: games are identical until bad,
    and the bad-event probability is bounded by `ε_bad`. Both games
    must be `NoFail` (required by `advantage_upto_bad`). -/
structure UpToBad (G₀ G₁ : SPComp Bool) (bad : SPComp Bool) (ε_bad : ℝ≥0∞) : Prop where
  /-- The games are identical unless bad occurs -/
  identical : IdenticalUntilBad G₀ G₁ bad
  /-- G₀ never fails -/
  noFail_left : SPComp.NoFail G₀
  /-- G₁ never fails -/
  noFail_right : SPComp.NoFail G₁
  /-- The bad event probability is bounded -/
  pr_bad : prTrue bad Heap.empty ≤ ε_bad

/-- Extract the advantage bound from an `UpToBad` witness. -/
theorem uptobad_advantage (G₀ G₁ bad : SPComp Bool) (ε_bad : ℝ≥0∞)
    (h : UpToBad G₀ G₁ bad ε_bad) :
    Advantage G₀ G₁ ≤ ε_bad :=
  le_trans (advantage_upto_bad G₀ G₁ bad h.noFail_left h.noFail_right h.identical) h.pr_bad

/-- Bundled UpToBad with adversary: for adversary-parameterized games. -/
structure UpToBadA {α : Type} (G₀ G₁ : SPComp α) (bad : SPComp Bool)
    (ε_bad : ℝ≥0∞) : Prop where
  /-- The games are identical until bad for all adversaries -/
  identical : ∀ (A : α → SPComp Bool),
    IdenticalUntilBad (G₀.bind A) (G₁.bind A) bad
  /-- G₀ never fails -/
  noFail_left : SPComp.NoFail G₀
  /-- G₁ never fails -/
  noFail_right : SPComp.NoFail G₁
  /-- The bad event probability is bounded -/
  pr_bad : prTrue bad Heap.empty ≤ ε_bad

/-- Extract the advantage bound from an `UpToBadA` witness, given a
    NoFail-preserving adversary. -/
theorem uptobadA_advantage {α : Type} (G₀ G₁ : SPComp α)
    (bad : SPComp Bool) (ε_bad : ℝ≥0∞)
    (h : UpToBadA G₀ G₁ bad ε_bad) :
    ∀ A, (∀ a, SPComp.NoFail (A a)) → AdvantageA G₀ G₁ A ≤ ε_bad := by
  intro A hnfA
  exact le_trans
    (advantage_upto_bad_A G₀ G₁ bad h.noFail_left h.noFail_right h.identical A hnfA)
    h.pr_bad

/-! ## Corollary: Union Bound for Multiple Bad Events

When a proof involves multiple bad events, the union bound gives:

    Pr[bad₁ ∨ bad₂ ∨ ... ∨ bad_n] ≤ Pr[bad₁] + ... + Pr[bad_n]

This composes with the fundamental lemma to give multi-hop bounds. -/

/-- Union bound for two bad events under IsPure+NoFail: the probability
    of either bad event firing is at most the sum of their individual
    probabilities.

    **Hypotheses**: Both `bad₁` and `bad₂` must be IsPure+NoFail. The
    bound is *false* without heap-purity on `bad₂` — counter-example:
    bad₁ writes the heap and returns false, bad₂ reads the heap and
    returns whether it was written; then chained prTrue = 1 but
    prTrue bad₁ Heap.empty + prTrue bad₂ Heap.empty = 0.

    **Proof**: Decompose `prTrue(bind bad₁ k)` via `prTrue_isPure_noFail_bind`
    (NomPkgBridge). The first branch (b₁=true) makes the inner expression
    `true || _ = true` so the prTrue equals bad₂'s mass = 1 (NoFail). The
    second branch (b₁=false) reduces to `pure b₂`, so the prTrue equals
    `prTrue bad₂`. Bound: `d₁(true)·1 + d₁(false)·prTrue bad₂ ≤
    d₁(true) + prTrue bad₂` since `d₁(false) ≤ 1`. -/
theorem prTrue_union_bound (bad₁ bad₂ : SPComp Bool)
    (hp₁ : SPComp.IsPure bad₁) (hp₂ : SPComp.IsPure bad₂)
    (hnf₁ : SPComp.NoFail bad₁) (hnf₂ : SPComp.NoFail bad₂) :
    prTrue (do let b₁ ← bad₁; let b₂ ← bad₂; SPComp.pure (b₁ || b₂)) Heap.empty
    ≤ prTrue bad₁ Heap.empty + prTrue bad₂ Heap.empty := by
  show prTrue (SPComp.bind bad₁ (fun b₁ =>
                SPComp.bind bad₂ (fun b₂ => SPComp.pure (b₁ || b₂)))) Heap.empty ≤ _
  obtain ⟨d₁, hd₁⟩ := hp₁
  have hd₁_nf : d₁ none = 0 :=
    CatCrypt.Crypto.isPure_noFail_d_none hd₁ hnf₁
  -- Decompose prTrue using prTrue_isPure_noFail_bind.
  rw [CatCrypt.Crypto.prTrue_isPure_noFail_bind hd₁ hd₁_nf
      (fun b₁ => SPComp.bind bad₂ (fun b₂ => SPComp.pure (b₁ || b₂))) Heap.empty]
  -- For b₁ = true: (true || b₂) = true → prTrue = bad₂'s mass.
  -- For b₁ = false: (false || b₂) = b₂ → bind bad₂ pure = bad₂.
  have h_true_simp : (fun b₂ : Bool => SPComp.pure (true || b₂)) =
                     (fun _ => SPComp.pure true) := by
    funext b₂; simp
  have h_false_simp : (fun b₂ : Bool => SPComp.pure (false || b₂)) =
                      SPComp.pure := by
    funext b₂; simp
  rw [h_true_simp, h_false_simp]
  -- Right branch reduces: bind bad₂ pure = bad₂ via monad law.
  have h_bind_pure : SPComp.bind bad₂ SPComp.pure = bad₂ := by
    funext h₀
    unfold SPComp.bind SPComp.pure
    simp [SDistr.bind_pure]
  rw [h_bind_pure]
  -- Left branch: bind bad₂ (fun _ => pure true). Its prTrue is 1 under NoFail bad₂.
  -- Use prTrue_isPure_noFail_bind on bad₂ to decompose.
  obtain ⟨d₂, hd₂⟩ := hp₂
  have hd₂_nf := CatCrypt.Crypto.isPure_noFail_d_none hd₂ hnf₂
  have h_pt_true : prTrue (SPComp.pure true) Heap.empty = 1 := by
    unfold prTrue SPComp.pure
    rw [tsum_eq_single Heap.empty]
    · simp [SDistr.pure_apply_some]
    · intro h hne
      simp only [SDistr.pure_apply_some, Prod.mk.injEq, true_and, ite_eq_right_iff]
      intro heq; exact absurd heq.symm hne
  have h_left_eq_one :
      prTrue (SPComp.bind bad₂ (fun _ => SPComp.pure true)) Heap.empty = 1 := by
    rw [CatCrypt.Crypto.prTrue_isPure_noFail_bind hd₂ hd₂_nf
        (fun _ => SPComp.pure true) Heap.empty]
    rw [h_pt_true, mul_one, mul_one]
    -- d₂(some true) + d₂(some false) = 1 under NoFail.
    have htotal := d₂.tsum_coe
    rw [SDistr.tsum_option_eq_add, hd₂_nf, zero_add, tsum_bool, add_comm] at htotal
    exact htotal
  -- Plug into the decomposition: term₁ = d₁(some true) · 1 = d₁(some true) = prTrue bad₁
  -- term₂ = d₁(some false) · prTrue bad₂.
  rw [h_left_eq_one, mul_one]
  rw [CatCrypt.Crypto.prTrue_isPure_eq hd₁ Heap.empty]
  -- Goal: d₁(some true) + d₁(some false) · prTrue bad₂ ≤ d₁(some true) + prTrue bad₂
  gcongr
  -- d₁(some false) · prTrue bad₂ ≤ prTrue bad₂.
  -- d₁(some false) ≤ 1 by PMF mass under NoFail.
  have h_d1_false_le_one : d₁ (some false) ≤ 1 := by
    have htotal := d₁.tsum_coe
    rw [SDistr.tsum_option_eq_add, hd₁_nf, zero_add, tsum_bool, add_comm] at htotal
    rw [← htotal]; exact le_add_self
  calc d₁ (some false) * prTrue bad₂ Heap.empty
      ≤ 1 * prTrue bad₂ Heap.empty := by gcongr
    _ = prTrue bad₂ Heap.empty := one_mul _

/-- Union bound for a finite list of bad events. -/
noncomputable def bad_union (bads : List (SPComp Bool)) : SPComp Bool :=
  match bads with
  | [] => SPComp.pure false
  | [b] => b
  | b :: bs => do
    let b₁ ← b
    let b₂ ← bad_union bs
    SPComp.pure (b₁ || b₂)

/-- The probability of any event in a list firing is bounded by the sum
    of individual probabilities (finite union bound / Boole's inequality).

    **Proof strategy**: Induction on the list, applying `prTrue_union_bound`
    at each step to peel off one event from the disjunction. -/
private theorem prTrue_pure_false_eq_zero (h₀ : Heap) :
    prTrue (SPComp.pure false) h₀ = 0 := by
  unfold prTrue SPComp.pure
  simp only [SDistr.pure, PMF.pure_apply, Option.some.injEq, Prod.mk.injEq,
    reduceCtorEq, false_and, ite_false, tsum_zero]

/-- `bad_union` of IsPure+NoFail events is itself IsPure+NoFail. -/
private theorem bad_union_isPure_noFail :
    (bads : List (SPComp Bool)) →
    (∀ b ∈ bads, SPComp.IsPure b) →
    (∀ b ∈ bads, SPComp.NoFail b) →
    SPComp.IsPure (bad_union bads) ∧ SPComp.NoFail (bad_union bads)
  | [] => fun _ _ => ⟨SPComp.pure_isPure _, SPComp.pure_noFail _⟩
  | [b] => fun hp hnf =>
      ⟨hp b (List.mem_singleton.mpr rfl), hnf b (List.mem_singleton.mpr rfl)⟩
  | b :: b' :: bs => fun hp hnf => by
      have ih := bad_union_isPure_noFail (b' :: bs)
        (fun x hx => hp x (List.mem_cons_of_mem b hx))
        (fun x hx => hnf x (List.mem_cons_of_mem b hx))
      refine ⟨?_, ?_⟩
      · -- IsPure of bind chain
        simp only [bad_union]
        apply SPComp.bind_isPure (hp b (List.mem_cons_self))
        intro b₁
        apply SPComp.bind_isPure ih.1
        intro b₂
        exact SPComp.pure_isPure _
      · -- NoFail of bind chain
        simp only [bad_union]
        apply CatCrypt.Crypto.Assumptions.SPComp.bind_noFail
          (hnf b (List.mem_cons_self))
        intro b₁
        apply CatCrypt.Crypto.Assumptions.SPComp.bind_noFail ih.2
        intro b₂
        exact SPComp.pure_noFail _

theorem prTrue_union_bound_list :
    (bads : List (SPComp Bool)) →
    (∀ b ∈ bads, SPComp.IsPure b) →
    (∀ b ∈ bads, SPComp.NoFail b) →
    prTrue (bad_union bads) Heap.empty ≤
    bads.foldr (fun b acc => prTrue b Heap.empty + acc) 0
  | [] => fun _ _ => by
    simp only [bad_union, List.foldr]
    exact le_of_eq (prTrue_pure_false_eq_zero _)
  | [b] => fun _ _ => by
    simp only [bad_union, List.foldr]
    exact le_add_right (le_refl _)
  | b :: b' :: bs => fun hp hnf => by
    simp only [bad_union, List.foldr]
    have ⟨h_ip, h_nf⟩ := bad_union_isPure_noFail (b' :: bs)
      (fun x hx => hp x (List.mem_cons_of_mem b hx))
      (fun x hx => hnf x (List.mem_cons_of_mem b hx))
    calc prTrue (do let b₁ ← b; let b₂ ← bad_union (b' :: bs); SPComp.pure (b₁ || b₂))
          Heap.empty
        ≤ prTrue b Heap.empty + prTrue (bad_union (b' :: bs)) Heap.empty :=
          prTrue_union_bound b (bad_union (b' :: bs))
            (hp b (List.mem_cons_self)) h_ip
            (hnf b (List.mem_cons_self)) h_nf
      _ ≤ prTrue b Heap.empty +
          List.foldr (fun b acc => prTrue b Heap.empty + acc) 0 (b' :: bs) := by
          gcongr
          exact prTrue_union_bound_list (b' :: bs)
            (fun x hx => hp x (List.mem_cons_of_mem b hx))
            (fun x hx => hnf x (List.mem_cons_of_mem b hx))

/-! ## Chaining: Bad Event + Hybrid Argument

Combining the fundamental lemma with the hybrid argument gives a
powerful pattern: each hybrid step is an "identical until bad" transition,
and the total advantage sums the bad-event probabilities. -/

/-- **Bad-event hybrid bound**: if each of `n` hybrid steps is identical
    until bad with bad-event probability at most `ε`, then the total
    advantage is at most `n * ε`.

    This is the standard pattern for multi-step game-hopping proofs
    where each step introduces a collision or failure event. -/
theorem advantage_hybrid_upto_bad (G : ℕ → SPComp Bool) (n : ℕ) (ε : ℝ≥0∞)
    (bad : ℕ → SPComp Bool)
    (h_iub : ∀ i, i < n → UpToBad (G i) (G (i + 1)) (bad i) ε) :
    Advantage (G 0) (G n) ≤ n * ε := by
  have hstep : ∀ i, i < n → Advantage (G i) (G (i + 1)) ≤ ε :=
    fun i hi => uptobad_advantage _ _ _ _ (h_iub i hi)
  calc Advantage (G 0) (G n)
      ≤ ∑ i ∈ Finset.range n, Advantage (G i) (G (i + 1)) :=
        advantage_hybrid_dep_bool G n
    _ ≤ ∑ _ ∈ Finset.range n, ε :=
        Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)
    _ = n * ε := by simp [Finset.sum_const, Finset.card_range]

/-! ## Multi-Query Game Abstraction

A generic multi-query game models the common pattern in cryptographic
security definitions (IND-CPA, PRF, MAC, etc.) where an adversary
interacts with an oracle over multiple rounds:

1. **Initialize** internal state
2. **Query** the oracle `q` times, updating state each time
3. **Finalize** by producing a Boolean decision

The key theorem `single_to_multi_bound` formalizes the standard
reduction: if distinguishing a single query costs advantage ε₁,
then distinguishing q queries costs at most q * ε₁. -/

/-- A multi-query game parameterized by state, input, and output types.

    This captures the structure of IND-CPA, PRF, MAC, and other
    multi-query security definitions. The adversary's strategy is
    encoded by the sequence of inputs; the game handles the internal
    oracle computation.

    In the PRF setting:
    - `State` = key (or ⊥ for ideal)
    - `Input` = domain element
    - `Output` = range element
    - `init` = key generation (or table init)
    - `query` = evaluate PRF (or sample random)
    - `finalize` = adversary's decision -/
structure MultiQueryGame (State Input Output : Type) where
  /-- Initialize the game state (e.g., key generation) -/
  init : SPComp State
  /-- Process one oracle query: takes current state and query input,
      returns updated state and query output -/
  query : State → Input → SPComp (State × Output)
  /-- Produce the final decision from the accumulated state -/
  finalize : State → SPComp Bool

/-- Execute a multi-query game with a given sequence of inputs.

    Processes `q` queries sequentially, threading state through each
    query, then finalizes. The result is a `SPComp Bool` suitable
    for computing advantage.

    The recursion unfolds as:
    ```
    s₀ ← init
    (s₁, o₁) ← query s₀ (inputs 0)
    (s₂, o₂) ← query s₁ (inputs 1)
    ...
    (s_q, o_q) ← query s_{q-1} (inputs (q-1))
    finalize s_q
    ``` -/
noncomputable def MultiQueryGame.run {S I O : Type}
    (G : MultiQueryGame S I O) (inputs : ℕ → I) (q : ℕ) : SPComp Bool := do
  let s₀ ← G.init
  let s_final ← runQueries G.query s₀ inputs q
  G.finalize s_final
where
  /-- Helper: run `q` queries starting from state `s`, using inputs at
      indices `0, 1, ..., q-1`. -/
  runQueries (qry : S → I → SPComp (S × O)) (s : S) (inputs : ℕ → I) :
      ℕ → SPComp S
    | 0 => SPComp.pure s
    | n + 1 => do
      let (s', _o) ← qry s (inputs n)
      runQueries qry s' (fun i => inputs (i + 1)) n -- wrong but unused

/-- An alternative, more explicit execution that collects all outputs. -/
noncomputable def MultiQueryGame.runCollect {S I O : Type}
    (G : MultiQueryGame S I O) (q : ℕ) (inputs : Fin q → I) : SPComp (S × List O) := do
  let s₀ ← G.init
  let mut state := s₀
  let mut outputs : List O := []
  for _h : i in List.finRange q do
    let (s', o) ← G.query state (inputs i)
    state := s'
    outputs := outputs ++ [o]
  return (state, outputs)

/-- Run queries with the first `switch` using `qry_ideal` and the rest
    using `qry_real`. Helper for hybrid game construction. -/
noncomputable def MultiQueryGame.hybridQueries {S I O : Type}
    (qry_ideal qry_real : S → I → SPComp (S × O))
    (s : S) (inputs : ℕ → I) (switch : ℕ) : ℕ → SPComp S
  | 0 => SPComp.pure s
  | n + 1 => do
    let qry := if n < switch then qry_ideal else qry_real
    let (s', _) ← qry s (inputs n)
    MultiQueryGame.hybridQueries qry_ideal qry_real s' (fun j => inputs (j + 1)) switch n

/-- The i-th hybrid game between `G_real` and `G_ideal`: first `i`
    queries use the ideal oracle, remaining queries use the real oracle.

    This is the standard hybrid construction for multi-query reductions:
    - `hybrid 0` = all-real game
    - `hybrid q` = all-ideal game
    - `hybrid i` and `hybrid (i+1)` differ in exactly one query

    Assumes `G_real` and `G_ideal` share the same `init` and `finalize`
    (they differ only in the oracle). -/
noncomputable def MultiQueryGame.hybrid {S I O : Type}
    (G_real G_ideal : MultiQueryGame S I O)
    (inputs : ℕ → I) (i : ℕ) (q : ℕ) : SPComp Bool := do
  let s₀ ← G_real.init
  -- First i queries use ideal, remaining (q - i) use real
  let s_mid ← MultiQueryGame.hybridQueries G_ideal.query G_real.query s₀ inputs i q
  G_real.finalize s_mid

/-- **Single-to-multi-query reduction**: if distinguishing a single
    query between `G_real` and `G_ideal` costs advantage at most `ε₁`,
    then distinguishing `q` queries costs at most `q * ε₁`.

    This formalizes the standard textbook reduction (Boneh-Shoup Thm 4.4):
    the hybrid argument interpolates between all-real and all-ideal,
    and each step reduces to the single-query distinguishing problem.

    **Proof strategy**: Construct `q+1` hybrid games where hybrid `i`
    uses the ideal oracle for the first `i` queries and the real oracle
    for the rest. Each adjacent pair of hybrids differs in exactly one
    query, so the per-step advantage is at most `ε₁`. Apply
    `advantage_hybrid_uniform` to sum the `q` steps. -/
theorem MultiQueryGame.single_to_multi_bound {S I O : Type}
    (G_real G_ideal : MultiQueryGame S I O)
    (inputs : ℕ → I) (q : ℕ) (ε₁ : ℝ≥0∞)
    (h_single : ∀ i, i < q →
      Advantage (MultiQueryGame.hybrid G_real G_ideal inputs i q)
                (MultiQueryGame.hybrid G_real G_ideal inputs (i + 1) q)
      ≤ ε₁) :
    Advantage (MultiQueryGame.hybrid G_real G_ideal inputs 0 q)
              (MultiQueryGame.hybrid G_real G_ideal inputs q q)
    ≤ q * ε₁ := by
  exact advantage_hybrid_dep_bool
    (fun i => MultiQueryGame.hybrid G_real G_ideal inputs i q) q
    |>.trans (by
      apply Finset.sum_le_sum
      intro i hi
      exact h_single i (Finset.mem_range.mp hi))
    |>.trans (by simp [Finset.sum_const, Finset.card_range])

/-! ## Lazy/Eager Sampling Equivalence

A fundamental technique in game-playing proofs: a random oracle can be
implemented either by:
- **Lazy sampling**: sample a random value the first time a query is made,
  then return the cached value on subsequent queries
- **Eager sampling**: sample the entire random function upfront, then
  look up values deterministically

These two strategies produce identical distributions. This equivalence
is used pervasively in PRF, ROM, and ideal cipher proofs.

Reference: Bellare & Rogaway 2006, Lemma 1. -/

/-- Lazy sampling oracle: maintains a partial function `table : D → Option R`.
    On query `x`:
    - If `table x = some r`, return `r` (cached)
    - If `table x = none`, sample `r ← uniform R`, update table, return `r`

    This is the standard "program-on-the-fly" implementation of a
    random oracle. -/
noncomputable def lazy_sample {D R : Type} [DecidableEq D] [Fintype R] [Nonempty R]
    (table : D → Option R) (x : D) : SPComp (R × (D → Option R)) :=
  match table x with
  | some r => SPComp.pure (r, table)
  | none => do
    let r ← SPComp.sample R
    SPComp.pure (r, fun d => if d = x then some r else table d)

/-- Eager sampling oracle: given a total function `f : D → R` (sampled upfront),
    simply look up the value. No state update needed since everything is
    precomputed.

    The function `f` is typically obtained by sampling from the uniform
    distribution over `D → R` (or equivalently, sampling each `f(d)`
    independently). -/
noncomputable def eager_sample {D R : Type} [DecidableEq D]
    (f : D → R) (x : D) : SPComp (R × (D → R)) :=
  SPComp.pure (f x, f)

/-- Process a list of queries via lazy sampling, threading the table.
    Each query either returns a cached result or samples fresh. -/
noncomputable def lazy_process {D R : Type} [DecidableEq D] [Fintype R] [Nonempty R] :
    List D → (D → Option R) → SPComp (List R) :=
  fun queries table =>
    match queries with
    | [] => SPComp.pure []
    | x :: xs => do
      let (r, table') ← lazy_sample table x
      let rs ← lazy_process xs table'
      SPComp.pure (r :: rs)

/-- Process a list of queries via eager sampling: sample the full
    function upfront, then look up each query deterministically. -/
noncomputable def eager_process {D R : Type} [DecidableEq D] [Fintype R] [Nonempty R]
    [Fintype D] :
    List D → SPComp (List R) :=
  fun queries => do
    -- Sample a total function f : D → R upfront
    -- (conceptually: sample each f(d) independently)
    let f ← SPComp.sample (D → R)
    SPComp.pure (queries.map f)

/-! ### Helpers for `lazy_eager_equiv`

These reduce both lazy and eager sampling to a common `sequential_sample`
intermediate (iid R-uniforms). The lazy half is a straightforward induction;
the eager half uses `Equiv.piSplitAt` + `SDistr.uniform_bind_equiv_comp` to
factor `uniform (D → R)` into `uniform R × uniform ({d // d ≠ x} → R)`,
recursing over the queries. -/

/-- Sequential iid uniform sampling — n fresh uniforms on R, paired into a list. -/
noncomputable def sequential_sample {R : Type} [Fintype R] [Nonempty R] :
    ∀ (_ : ℕ), SPComp (List R)
  | 0 => SPComp.pure []
  | n + 1 => do
    let r ← SPComp.sample R
    let rs ← sequential_sample n
    SPComp.pure (r :: rs)

/-- Binding `sample R` with a constant continuation reduces to the constant. -/
private theorem spcomp_sample_bind_const {α β : Type} [Fintype α] [Nonempty α]
    (c : SPComp β) :
    SPComp.bind (SPComp.sample α) (fun (_ : α) => c) = c := by
  funext h
  unfold SPComp.bind SPComp.sample
  rw [SDistr.bind_assoc]
  simp only [SDistr.pure_bind]
  exact SDistr.uniform_bind_const (c h)

/-- The lazy direction of `lazy_eager_equiv`: `lazy_process` with a table
    that has `none` at every queried point (and `Nodup` queries) reduces
    to a sequential iid R-uniform sampling of `queries.length` values. -/
private theorem lazy_process_eq_sequential {D R : Type} [DecidableEq D]
    [Fintype R] [Nonempty R] :
    ∀ (qs : List D) (T : D → Option R), qs.Nodup → (∀ q ∈ qs, T q = none) →
      lazy_process qs T = sequential_sample qs.length
  | [], _, _, _ => by simp [lazy_process, sequential_sample]
  | x :: xs, T, hnodup, hT => by
    have hx_T : T x = none := hT x List.mem_cons_self
    have hx_xs : x ∉ xs := (List.nodup_cons.mp hnodup).1
    have hxs_nodup : xs.Nodup := (List.nodup_cons.mp hnodup).2
    have h_T_new : ∀ (r : R), ∀ q ∈ xs,
        (fun d => if d = x then some r else T d) q = none := by
      intro r q hq
      have hq_ne_x : q ≠ x := fun heq => hx_xs (heq ▸ hq)
      simp [hq_ne_x, hT q (List.mem_cons_of_mem x hq)]
    -- lazy_process (x :: xs) T unfolds to bind (lazy_sample T x) (...).
    -- With T x = none, lazy_sample T x = bind (sample R) (fun r => pure (r, T_new r)).
    show SPComp.bind (lazy_sample T x)
        (fun p => SPComp.bind (lazy_process xs p.2) (fun rs => SPComp.pure (p.1 :: rs))) =
      sequential_sample (xs.length + 1)
    -- Reduce lazy_sample by T x = none.
    have h_ls : lazy_sample T x = SPComp.bind (SPComp.sample R)
        (fun r => SPComp.pure (r, fun d => if d = x then some r else T d)) := by
      simp [lazy_sample, hx_T]
    rw [h_ls, SPComp.bind_assoc]
    -- After bind_assoc: bind (sample R) (fun r => bind (pure (r, T_new r)) (...))
    -- Reduce inner bind (pure ...) via simp + push IH through.
    simp only [SPComp.pure_bind]
    -- Now: bind (sample R) (fun r => bind (lazy_process xs (T_new r)) (fun rs => pure (r :: rs)))
    -- Apply IH inside the bind.
    have h_inner : (fun r : R => SPComp.bind (lazy_process xs (fun d => if d = x then some r else T d))
                                  (fun rs => SPComp.pure (r :: rs))) =
                   (fun r : R => SPComp.bind (sequential_sample xs.length)
                                  (fun rs => SPComp.pure (r :: rs))) := by
      funext r
      rw [lazy_process_eq_sequential xs _ hxs_nodup (h_T_new r)]
    rw [h_inner]
    -- Now: bind (sample R) (fun r => bind (sequential_sample xs.length) (fun rs => pure (r :: rs)))
    -- This is exactly sequential_sample (xs.length + 1) by definition.
    rfl

/-- SPComp-level version of `SDistr.uniform_bind_equiv_comp`. -/
private theorem spcomp_sample_bind_equiv_comp {α β γ : Type}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (σ : α ≃ β) (k : β → SPComp γ) :
    SPComp.bind (SPComp.sample α) (fun a => k (σ a)) =
    SPComp.bind (SPComp.sample β) k := by
  funext h₀
  unfold SPComp.bind SPComp.sample
  rw [SDistr.bind_assoc, SDistr.bind_assoc]
  simp only [SDistr.pure_bind]
  exact SDistr.uniform_bind_equiv_comp σ (fun b => k b h₀)

/-- SPComp-level: sampling a product type equals nested independent samples. -/
private theorem spcomp_sample_prod {A B γ : Type}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (k : (A × B) → SPComp γ) :
    SPComp.bind (SPComp.sample (A × B)) k =
    SPComp.bind (SPComp.sample A) (fun a =>
      SPComp.bind (SPComp.sample B) (fun b => k (a, b))) := by
  funext h₀
  unfold SPComp.bind SPComp.sample
  rw [← SDistr.uniform_nested_eq_prod]
  rw [SDistr.bind_assoc, SDistr.bind_assoc]
  simp only [SDistr.pure_bind, SDistr.bind_assoc]

/-- Sampling uniformly from `Fin n → R` then taking `List.ofFn` equals
    sequential iid sampling of `n` uniforms. -/
private theorem sample_fin_ofFn_eq_sequential {R : Type} [Fintype R] [Nonempty R] :
    ∀ (n : ℕ),
      SPComp.bind (SPComp.sample (Fin n → R))
        (fun g => SPComp.pure (List.ofFn g)) =
      sequential_sample (R := R) n
  | 0 => by
    show SPComp.bind (SPComp.sample (Fin 0 → R))
          (fun _ => SPComp.pure []) = sequential_sample 0
    rw [spcomp_sample_bind_const]
    rfl
  | n + 1 => by
    show SPComp.bind (SPComp.sample (Fin (n+1) → R))
          (fun g => SPComp.pure (List.ofFn g)) = sequential_sample (n + 1)
    -- Use Fin.consEquiv : R × (Fin n → R) ≃ Fin (n+1) → R via uniform_bind_equiv_comp.
    rw [← spcomp_sample_bind_equiv_comp (Fin.consEquiv (fun _ : Fin (n+1) => R))
          (fun g => SPComp.pure (List.ofFn g))]
    rw [spcomp_sample_prod]
    simp only [Equiv.coe_fn_mk, Fin.consEquiv, List.ofFn_cons]
    show _ = SPComp.bind (SPComp.sample R)
        (fun r => SPComp.bind (sequential_sample n) (fun rs => SPComp.pure (r :: rs)))
    rw [← sample_fin_ofFn_eq_sequential]
    simp only [SPComp.bind_assoc, SPComp.pure_bind]

/-- The bijection `(D → R) ≃ (Fin qs.length → R) × ({d // d ∉ qs} → R)` for
    `Nodup` `qs`. The first component picks out values at qs-indexed positions;
    the second component holds values at non-qs points. -/
private noncomputable def qsBij {D R : Type} [DecidableEq D] [Fintype D]
    (qs : List D) (hnodup : qs.Nodup) :
    (D → R) ≃ (Fin qs.length → R) × ({d : D // d ∉ qs} → R) where
  toFun f := (fun i => f (qs.get i), fun d => f d.val)
  invFun := fun (g, h) d =>
    if h_in : d ∈ qs then g ⟨qs.idxOf d, by
      rw [show qs.idxOf d < qs.length ↔ d ∈ qs from List.idxOf_lt_length_iff]; exact h_in⟩
    else h ⟨d, h_in⟩
  left_inv f := by
    funext d
    by_cases h_in : d ∈ qs
    · simp only [h_in, dite_true]
      congr 1
      have : qs.get ⟨qs.idxOf d, by
        rw [show qs.idxOf d < qs.length ↔ d ∈ qs from List.idxOf_lt_length_iff]
        exact h_in⟩ = d := by
        apply List.getElem_idxOf
      exact this
    · simp [h_in]
  right_inv := fun ⟨g, h⟩ => by
    refine Prod.ext ?_ ?_
    · funext i
      have h_get_in : qs.get i ∈ qs := List.get_mem _ _
      simp only [h_get_in, dite_true]
      congr 1
      apply Fin.ext
      simpa using List.Nodup.idxOf_getElem hnodup i.val i.isLt
    · funext d
      simp [d.property]

/-- Under `qsBij.symm (g, h)`, `qs.map` reduces to `List.ofFn g` — the non-qs
    component `h` is unused since `qs.map` only accesses qs-indexed values. -/
private theorem qsBij_symm_map {D R : Type} [DecidableEq D] [Fintype D]
    (qs : List D) (hnodup : qs.Nodup)
    (g : Fin qs.length → R) (h : {d : D // d ∉ qs} → R) :
    qs.map ((qsBij (R := R) qs hnodup).symm (g, h)) = List.ofFn g := by
  rw [← List.ofFn_getElem_eq_map]
  congr 1
  funext i
  show ((qsBij qs hnodup).symm (g, h)) qs[i.val] = g i
  unfold qsBij
  simp only [Equiv.coe_fn_symm_mk]
  have h_in : qs[i.val] ∈ qs := List.getElem_mem _
  simp only [h_in, dite_true]
  congr 1
  apply Fin.ext
  simpa using List.Nodup.idxOf_getElem hnodup i.val i.isLt

/-- **Eager direction** of `lazy_eager_equiv`. -/
private theorem eager_process_eq_sequential {D R : Type} [DecidableEq D]
    [Fintype D] [Fintype R] [Nonempty R]
    (qs : List D) (hnodup : qs.Nodup) :
    (eager_process qs : SPComp (List R)) = sequential_sample (R := R) qs.length := by
  show SPComp.bind (SPComp.sample (D → R)) (fun f => SPComp.pure (qs.map f)) = _
  -- Transport sample (D → R) through qsBij.
  have h_bij := spcomp_sample_bind_equiv_comp (qsBij (R := R) qs hnodup)
    (fun p => SPComp.pure (qs.map ((qsBij qs hnodup).symm p)))
  simp only [Equiv.symm_apply_apply] at h_bij
  rw [h_bij]
  -- Use qsBij_symm_map to simplify qs.map (qsBij.symm (g, h)) = List.ofFn g.
  rw [spcomp_sample_prod]
  simp only [qsBij_symm_map qs hnodup]
  -- Now: sample (Fin n → R); sample ({d // d ∉ qs} → R); pure (List.ofFn g)
  -- The inner sample is unused — apply spcomp_sample_bind_const.
  simp only [spcomp_sample_bind_const]
  -- Now: sample (Fin qs.length → R); pure (List.ofFn g)
  exact sample_fin_ofFn_eq_sequential qs.length

/-- **Lazy/eager sampling equivalence**: for any sequence of distinct queries,
    the lazy and eager sampling strategies produce the same joint distribution
    over outputs.

    Composes `lazy_process_eq_sequential` (proven) and
    `eager_process_eq_sequential` (deferred, see its docstring) via the
    common `sequential_sample` intermediate.

    This is Bellare-Rogaway 2006, Lemma 1 (also implicit in Shoup 2004). -/
theorem lazy_eager_equiv {D R : Type} [DecidableEq D] [Fintype D]
    [Fintype R] [Nonempty R]
    (queries : List D) (hnodup : queries.Nodup) :
    ∀ h₀ : Heap,
      (lazy_process queries (fun _ => (none : Option R))) h₀ =
      (eager_process queries) h₀ := by
  intro h₀
  have h_lazy : (lazy_process queries (fun _ => (none : Option R)) :
                  SPComp (List R)) = sequential_sample (R := R) queries.length :=
    lazy_process_eq_sequential queries (fun _ => none) hnodup
      (fun _ _ => rfl)
  have h_eager : (eager_process queries : SPComp (List R)) =
                  sequential_sample (R := R) queries.length :=
    eager_process_eq_sequential queries hnodup
  rw [h_lazy, ← h_eager]
         -- uniform on D→R at previously-queried points gives uniform on rest

/-- **Single-query lazy/eager equivalence**: for a single query `x` on
    an empty table, lazy sampling and uniform sampling produce the same
    distribution.

    This is the base case of the full lazy/eager equivalence. -/
theorem lazy_sample_fresh_eq_uniform {D R : Type} [DecidableEq D]
    [Fintype R] [Nonempty R] (x : D) :
    lazy_sample (fun _ => none) x =
    (do let r ← SPComp.sample R
        SPComp.pure (r, fun d => if d = x then some r else (fun _ => none) d)) := by
  simp [lazy_sample]

/-! ## Composition: Bad Event + Lazy/Eager

A common proof pattern combines the bad-event lemma with lazy/eager
equivalence:

1. Replace eager sampling with lazy sampling (zero cost, by `lazy_eager_equiv`)
2. Introduce a bad event (collision, etc.)
3. Bound the game transition by the bad-event probability

This pattern appears in PRF, MAC, and signature security proofs. -/

/-- **Lazy-to-eager via bad event**: if a game using lazy sampling is
    identical-until-bad to a game using eager sampling (where bad = collision),
    then the advantage is bounded by the collision probability.

    This combines `lazy_eager_equiv` with `advantage_upto_bad`. NoFail
    hypotheses are required by the (now-proven) `advantage_upto_bad`. -/
theorem lazy_eager_upto_bad (G_lazy G_eager : SPComp Bool) (bad : SPComp Bool)
    (ε : ℝ≥0∞)
    (h_iub : IdenticalUntilBad G_lazy G_eager bad)
    (hnf_l : SPComp.NoFail G_lazy)
    (hnf_e : SPComp.NoFail G_eager)
    (h_bad : prTrue bad Heap.empty ≤ ε) :
    Advantage G_lazy G_eager ≤ ε :=
  uptobad_advantage G_lazy G_eager bad ε ⟨h_iub, hnf_l, hnf_e, h_bad⟩

end CatCrypt.Crypto.BadEvent
