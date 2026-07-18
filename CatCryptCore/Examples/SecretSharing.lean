/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Prob.XorBij
import CatCryptCore.Tactics
import CatCryptCore.Deep.ReflectUCHelpers

/-!
# 2-out-of-2 Additive Secret Sharing: Perfect Privacy

The 2-out-of-2 additive (XOR) secret-sharing scheme has *perfect privacy*: one
share alone is uniformly distributed and independent of the shared secret, so an
adversary holding a single share has advantage exactly `0` in distinguishing
which secret was shared. Following Rosulek, The Joy of Cryptography (secret
sharing).

This result is information-theoretic and self-contained — the cleanest possible
instance of the bijection-coupling technique.

## Overview

To share a secret bit `s`, sample a uniform bit `k` and hand out the two shares
```
share₁ = k        share₂ = k ⊕ s
```
Reconstruction is `share₁ ⊕ share₂ = k ⊕ (k ⊕ s) = s`, so the two shares together
determine `s`. Privacy is the statement that *either share on its own* reveals
nothing about `s`:

* `share₁ = k` is a uniform bit, manifestly independent of `s`;
* `share₂ = k ⊕ s` is XOR-by-`s` of a uniform key, hence again uniform and
  independent of `s` — exactly the one-time-pad argument.

The privacy game reveals the share held by the corrupted party (indexed by a bit
`i`) for one of two adversarially chosen secrets `s₀`, `s₁`. For any fixed `i`,
the two games couple through a single uniform sample — for `i = true` via
XOR-by-`(s₀ ⊕ s₁)`, for `i = false` via the identity — so `advantage_zero_of_rHoare`
collapses the advantage to `0`.

## Main definitions

* `shareXor` — the 2-of-2 XOR sharing of a bit: `k ↦ (k, k ⊕ s)`.
* `revealShare` — the share seen by the corrupted party `i`.
* `SS_Privacy_Game` / `SS_Privacy_Adv` — the one-share privacy game and its
  advantage.

## Main results

* `shareXor_reconstruct` — the two shares reconstruct the secret.
* `ss_privacy_coupling` — the two privacy games are equidistributed.
* `ss_perfect_privacy` — **perfect privacy**: `SS_Privacy_Adv i s₀ s₁ A = 0` for
  every corrupted party `i`, every pair of secrets, and every adversary `A`.

## References

* [Rosulek, The Joy of Cryptography, §3 (secret sharing)]
* [Shamir, How to Share a Secret, 1979]
-/

namespace CatCrypt.Examples.SecretSharing

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open CatCrypt.Crypto
open CatCrypt.Relational
open scoped ENNReal

/-! ## The 2-of-2 XOR Sharing -/

/-- The share held by corrupted party `i`, given key `k` and secret `s`:
    party `false` holds `share₁ = k`, party `true` holds `share₂ = k ⊕ s`. -/
def revealShare (i k s : Bool) : Bool := if i then xor k s else k

/-- The 2-out-of-2 additive (XOR) sharing of a secret bit `s`:
    sample a uniform key `k`; the shares are `(k, k ⊕ s)`. -/
noncomputable def shareXor (s : Bool) : SPComp (Bool × Bool) := do
  let k ← SPComp.sample Bool
  SPComp.pure (k, xor k s)

/-! ## Reconstruction -/

/-- The two shares reconstruct the secret: `share₁ ⊕ share₂ = s`. -/
theorem shareXor_reconstruct (k s : Bool) : xor k (xor k s) = s := by
  cases k <;> cases s <;> rfl

/-! ## The One-Share Privacy Game -/

/-- Privacy game for 2-of-2 XOR sharing. The corrupted party `i` is handed its
    single share of one of two adversarially chosen secrets:

    - `SS_Privacy_Game i s₀ s₁ true`  shares `s₀` (left/real)
    - `SS_Privacy_Game i s₀ s₁ false` shares `s₁` (right/ideal)

    The adversary sees only party `i`'s share and tries to tell the two apart. -/
noncomputable def SS_Privacy_Game (i s₀ s₁ : Bool) (b : Bool) : SPComp Bool := do
  let k ← SPComp.sample Bool
  SPComp.pure (revealShare i k (if b then s₀ else s₁))

/-- Privacy advantage: the corrupted party's distinguishing probability between
    a share of `s₀` and a share of `s₁`. -/
noncomputable def SS_Privacy_Adv (i s₀ s₁ : Bool) (A : Bool → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (SS_Privacy_Game i s₀ s₁ true) (SS_Privacy_Game i s₀ s₁ false) A

/-! ## Perfect Privacy -/

/-- The key-remap bijection coupling the two privacy games. For the corrupted
    party `i`, it maps the key used to share `s₀` to the key sharing `s₁` while
    keeping party `i`'s revealed share fixed: XOR-by-`(s₀ ⊕ s₁)` when `i = true`,
    the identity when `i = false`. -/
noncomputable def shareBij (i s₀ s₁ : Bool) : Bool ≃ Bool :=
  if i then boolXorBij (xor s₀ s₁) else Equiv.refl Bool

/-- Coupling: for a fixed corrupted party, the two privacy games are
    equidistributed. The revealed share over a uniform key is equidistributed
    with a plain uniform sample (XOR-by-a-fixed-value is a bijection of the key,
    the identity when the plain share is revealed), so the two games couple by
    transitivity through the uniform sample. -/
theorem ss_privacy_coupling (i s₀ s₁ : Bool) :
    rHoare eqPre
      (SS_Privacy_Game i s₀ s₁ true)
      (SS_Privacy_Game i s₀ s₁ false)
      eqPost := by
  simp only [SS_Privacy_Game, if_true, Bool.false_eq_true, if_false,
    SPComp.monad_bind_eq]
  ssprove_couple_bij (shareBij i s₀ s₁)
  cases i <;> cases s₀ <;> cases s₁ <;> simp [revealShare, shareBij, boolXorBij_apply]

/-- **2-of-2 XOR secret sharing has perfect privacy**: for either corrupted
    party `i`, any two secrets `s₀`, `s₁`, and any adversary `A`, the one-share
    privacy advantage is exactly `0`. A single share is uniform and independent
    of the secret. -/
theorem ss_perfect_privacy (i s₀ s₁ : Bool) (A : Bool → SPComp Bool) :
    SS_Privacy_Adv i s₀ s₁ A = 0 :=
  advantage_zero_of_rHoare _ _ (ss_privacy_coupling i s₀ s₁) A

/-! ## Reflection into the Package / UC Stack

The shallow `ss_perfect_privacy` bounds a single distinguisher applied to the two
privacy-game bodies. This section lifts it to a composable statement about deep
nominal packages linked with an arbitrary adversary package, following the stack
`shallow game → rawCode% → NomPackage.ofOracle → DeepNomAdvantage → sdist → UC`
via the shared `CatCryptCore.Deep.ReflectUCHelpers` combinators. The privacy game
is heap-independent, so the shallow coupling `ss_privacy_coupling` upgrades to a
full `SPComp` equality of the two reflected bodies (`spcomp_eq_of_isPure_coupling`),
and the whole stack follows with no purity bridge on the adversary. -/

open CatCrypt.Deep

/-- The reflected one-share privacy-game body for corrupted party `i` and bit `b`. -/
noncomputable def ssGameRaw (i s₀ s₁ b : Bool) : RawCode Bool :=
  rawCode% (SPComp.bind (SPComp.sample Bool)
    (fun k => SPComp.pure (revealShare i k (if b then s₀ else s₁))))

instance instValidSsGameRaw (i s₀ s₁ b : Bool) : IsValid (∅ : LocSet) (ssGameRaw i s₀ s₁ b) := by
  unfold ssGameRaw; infer_instance

/-- The reflected body evaluates back to the shallow privacy game. -/
theorem ssGameRaw_eval_shallow (i s₀ s₁ b : Bool) :
    (ssGameRaw i s₀ s₁ b).eval = SS_Privacy_Game i s₀ s₁ b := by
  simp [ssGameRaw, RawCode.eval, SS_Privacy_Game, SPComp.monad_bind_eq]

/-- The privacy game is heap-independent (a uniform sample then a pure reveal). -/
theorem ss_game_isPure (i s₀ s₁ b : Bool) : SPComp.IsPure (SS_Privacy_Game i s₀ s₁ b) := by
  unfold SS_Privacy_Game
  exact SPComp.bind_isPure (SPComp.sample_isPure _) (fun _ => SPComp.pure_isPure _)

/-- The two reflected bodies (share of `s₀` vs. `s₁`) have equal evaluations: the
    heap-independent coupling `ss_privacy_coupling` upgrades to `SPComp` equality. -/
theorem ssGameRaw_eval_eq (i s₀ s₁ : Bool) :
    (ssGameRaw i s₀ s₁ true).eval = (ssGameRaw i s₀ s₁ false).eval := by
  rw [ssGameRaw_eval_shallow, ssGameRaw_eval_shallow]
  exact spcomp_eq_of_isPure_coupling (ss_game_isPure i s₀ s₁ true)
    (ss_game_isPure i s₀ s₁ false) (ss_privacy_coupling i s₀ s₁)

/-- Real privacy game as an oracle-exporting nominal package (shares `s₀`). -/
noncomputable def ssGameTrue (i s₀ s₁ : Bool) : NomPackage :=
  NomPackage.ofOracle 1 Unit Bool (fun _ => ssGameRaw i s₀ s₁ true)

/-- Ideal privacy game as an oracle-exporting nominal package (shares `s₁`). -/
noncomputable def ssGameFalse (i s₀ s₁ : Bool) : NomPackage :=
  NomPackage.ofOracle 1 Unit Bool (fun _ => ssGameRaw i s₀ s₁ false)

/-- **Zero deep-nominal advantage against every adversary package.** -/
theorem ss_deepnom_zero (i s₀ s₁ : Bool) (A : NomPackage) :
    DeepNomAdvantage (ssGameTrue i s₀ s₁) (ssGameFalse i s₀ s₁) A = 0 :=
  deepNomAdvantage_ofOracle_zero _ _ (fun _ => ssGameRaw_eval_eq i s₀ s₁) A

/-- **Statistical distance zero** between the two linked-game families. -/
theorem ss_sdist_zero (i s₀ s₁ : Bool) :
    sdist (fun A : NomPackage => runPkg (DeepPackage.link A.pkg (ssGameTrue i s₀ s₁).pkg))
          (fun A : NomPackage => runPkg (DeepPackage.link A.pkg (ssGameFalse i s₀ s₁).pkg)) = 0 :=
  sdist_ofOracle_zero _ _ (fun _ => ssGameRaw_eval_eq i s₀ s₁)

/-- **Package-level perfect privacy** (`NomPkgSecure`). -/
theorem ss_nompkg_secure (i s₀ s₁ : Bool) :
    NomPkgSecure (ssGameTrue i s₀ s₁) (ssGameFalse i s₀ s₁) (fun _ => 0) :=
  nomPkgSecure_ofOracle _ _ (fun _ => ssGameRaw_eval_eq i s₀ s₁)

/-- **Perfect UC emulation** of the linked-game families over the trivial-leak
    interface (`out = Bool`, `leak = Empty`) with the identity simulator
    (composition plumbing). -/
theorem ss_uc (i s₀ s₁ : Bool) :
    UCEmulates 0 ⟨NomPackage, Bool, Empty, Empty, Bool⟩
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (ssGameTrue i s₀ s₁).pkg)))
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (ssGameFalse i s₀ s₁).pkg))) :=
  uc_ofOracle _ _ (fun _ => ssGameRaw_eval_eq i s₀ s₁)

/-- **Reflection mirrors the shallow game.** Against the forwarding adversary, the
    deep-nominal advantage equals the shallow privacy advantage under the identity
    distinguisher — which is `0` by `ss_perfect_privacy`. -/
theorem ss_deepnom_forward_eq_adv (i s₀ s₁ : Bool) :
    DeepNomAdvantage (ssGameTrue i s₀ s₁) (ssGameFalse i s₀ s₁) forwardAdv =
    SS_Privacy_Adv i s₀ s₁ SPComp.pure := by
  unfold DeepNomAdvantage ssGameTrue ssGameFalse
  rw [runPkg_link_forward (ssGameRaw i s₀ s₁ true),
      runPkg_link_forward (ssGameRaw i s₀ s₁ false),
      ssGameRaw_eval_shallow, ssGameRaw_eval_shallow, SS_Privacy_Adv, AdvantageA_pure]

end CatCrypt.Examples.SecretSharing
