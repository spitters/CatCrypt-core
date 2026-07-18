/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Prob.XorBij
import CatCryptCore.Prob.Support
import CatCryptCore.Examples.PRF
import CatCryptCore.Tactics
import CatCryptCore.Deep.ReflectUCHelpers

/-!
# CPA Security from a PRF: the Perfect Instantiation

The canonical construction of an IND-CPA-secure symmetric encryption scheme from
a pseudorandom function. Following Rosulek, The Joy of Cryptography, §7 (CPA
security).

Encrypt a message `m` as `(r, F(k, r) ⊕ m)` for a fresh uniform `r`: the keyed
value `F(k, r)` acts as a one-time pad on `m`. Decryption recomputes `F(k, r)`
from the transmitted `r` and un-pads. In the standard argument an IND-CPA
distinguisher reduces to a PRF distinguisher, so the IND-CPA advantage is bounded
by the PRF advantage.

## The perfect instantiation

Instantiating the PRF by a **bijection family** — for each input `r`, a bijection
`bij r : Key ≃ Output` — makes the underlying PRF perfect (`CatCrypt.Examples.PRF`,
`bijPRF_perfect`): over a uniform key, `F(k, r) = bij r k` is uniform on `Output`.
Consequently the pad `F(k, r) ⊕ m` is uniform regardless of `m`, and the two
IND-CPA games (encrypting `m₀` vs. `m₁`) are perfectly indistinguishable: the
IND-CPA advantage of *every* adversary is exactly `0`.

## Overview

The security argument is the bijection-coupling technique of the one-time pad
(`CatCrypt.Examples.OTP`), lifted through the fresh randomness `r`. First the two
independent samples (key and randomness) are reordered so `r` is drawn first
(`SPComp.swap_sample_sample`); then `r` is synchronized across the two games
(`rHoare_same_step`); finally, at each fixed `r`, the key is coupled by the
bijection `keyEquiv r m₀ m₁ : Key ≃ Key` chosen so that
`bij r k ⊕ m₀ = bij r (keyEquiv r m₀ m₁ k) ⊕ m₁`, forcing the two ciphertexts to
coincide (`rHoare_bij_step`).

## Main definitions

* `BijCPAScheme` — a symmetric scheme `(r, bij r k ⊕ m)` built from a bijection
  family together with an involutive XOR on the output space.
* `BijCPAScheme.toEncScheme` — the induced core `EncScheme`.
* `BijCPAScheme.toBijPRFFamily` — the underlying (perfect) bijection-family PRF.

## Main results

* `bijCPA_correct` — the scheme is correct (decryption recovers the message).
* `bijCPA_prf_perfect` — the underlying PRF has perfect PRF security.
* `bijCPA_indcpa_coupling` — the two IND-CPA games couple with `eqPost`.
* `bijCPA_perfect_indcpa` — **perfect IND-CPA security**:
  `INDCPA_Adv B.toEncScheme m₀ m₁ A = 0` for every adversary `A`.
* `boolXorCPA_perfect_indcpa` — the `Bool` instantiation `(r, (k ⊕ r) ⊕ m)`.

## References

* [Rosulek, The Joy of Cryptography, §7 (CPA security)]
-/

namespace CatCrypt.Examples.CPAFromPRF

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.SecurityDefs
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open CatCrypt.Relational
open CatCrypt.Examples.PRF

/-! ## The Bijection-Family CPA Scheme -/

/-- A symmetric encryption scheme encrypting `m` as `(r, (bij r k) ⊕ m)`.

`bij r : Key ≃ Output` is a family of key→output bijections (one per randomness
value `r`), and `xorOut` is an involutive combining operation on `Output` playing
the role of XOR. For a uniform key the pad `bij r k` is uniform, which is the
source of perfect security. -/
structure BijCPAScheme where
  /-- Key type -/
  Key : Type
  /-- Randomness / PRF-input type -/
  Input : Type
  /-- Output / message type -/
  Output : Type
  [finKey : Fintype Key]
  [neKey : Nonempty Key]
  [finInput : Fintype Input]
  [neInput : Nonempty Input]
  [finOutput : Fintype Output]
  [neOutput : Nonempty Output]
  /-- For each randomness value, a bijection from keys to outputs -/
  bij : Input → (Key ≃ Output)
  /-- The XOR-like combining operation on outputs -/
  xorOut : Output → Output → Output
  /-- `xorOut · b` is involutive: un-padding with the same pad recovers the value -/
  xorOut_cancel : ∀ a b, xorOut (xorOut a b) b = a
  /-- `xorOut a ·` is involutive: decryption recovers the message -/
  xorOut_cancel' : ∀ a b, xorOut a (xorOut a b) = b

attribute [instance] BijCPAScheme.finKey BijCPAScheme.neKey
  BijCPAScheme.finInput BijCPAScheme.neInput
  BijCPAScheme.finOutput BijCPAScheme.neOutput

/-- The core `EncScheme` induced by a bijection-family CPA scheme.

- `Key`, `Plaintext = Output`, `Ciphertext = Input × Output`
- `keyGen` samples a uniform key
- `encrypt k m = do r ← sample Input; pure (r, (bij r k) ⊕ m)`
- `decrypt k (r, c) = pure (some ((bij r k) ⊕ c))` -/
noncomputable def BijCPAScheme.toEncScheme (B : BijCPAScheme) : EncScheme where
  Key := B.Key
  Plaintext := B.Output
  Ciphertext := B.Input × B.Output
  finKey := inferInstance
  neKey := inferInstance
  finCt := inferInstance
  neCt := inferInstance
  keyGen := SPComp.sample B.Key
  encrypt := fun k m => do
    let r ← SPComp.sample B.Input
    SPComp.pure (r, B.xorOut (B.bij r k) m)
  decrypt := fun k c => SPComp.pure (some (B.xorOut (B.bij c.1 k) c.2))

/-- The underlying bijection-family PRF `F(k, r) = bij r k`. -/
def BijCPAScheme.toBijPRFFamily (B : BijCPAScheme) : BijPRFFamily where
  Key := B.Key
  Input := B.Input
  Output := B.Output
  bij := B.bij

/-! ## Correctness -/

/-- The scheme is correct: decrypting `(r, (bij r k) ⊕ m)` recovers `m`. -/
theorem bijCPA_correct (B : BijCPAScheme) : B.toEncScheme.Correct := by
  intro k m h ct h' hct result h'' hres
  simp only [BijCPAScheme.toEncScheme] at hct hres
  -- Extract the sampled randomness `r` (and intermediate heap) witnessing `ct`.
  obtain ⟨r, h₀, _, hPure⟩ := SDistr.bind_support_witness_pair hct
  simp only [SPComp.pure] at hPure
  rw [← SDistr.mem_support_iff, SDistr.mem_support_pure_iff, Prod.ext_iff] at hPure
  obtain ⟨hct_eq, hh_eq⟩ := hPure
  subst hct_eq
  -- Decryption is pure; it returns `some ((bij r k) ⊕ ((bij r k) ⊕ m)) = some m`.
  simp only [SPComp.pure] at hres
  have hpair : (some (B.xorOut (B.bij r k) (B.xorOut (B.bij r k) m)), h')
      = (result, h'') := (SDistr.mem_support_pure_iff _ _).mp hres
  have hres_eq : some (B.xorOut (B.bij r k) (B.xorOut (B.bij r k) m)) = result :=
    congrArg Prod.fst hpair
  rw [← hres_eq]
  exact congrArg some (B.xorOut_cancel' _ _)

/-! ## The Underlying PRF Is Perfect -/

/-- The bijection-family PRF underlying the scheme has perfect PRF security. -/
theorem bijCPA_prf_perfect (B : BijCPAScheme) (x : B.Input)
    (A : B.toBijPRFFamily.toPRFScheme.Output → SPComp Bool) :
    PRF_Adv B.toBijPRFFamily.toPRFScheme x A = 0 :=
  bijPRF_perfect B.toBijPRFFamily x A

/-! ## Perfect IND-CPA Security -/

/-- The key-space bijection coupling the two IND-CPA games at a fixed randomness
`r`: it maps `k` to the unique key whose pad differs from `bij r k` by
`m₀ ⊕ m₁`, so that `bij r k ⊕ m₀` and `bij r (keyEquiv r m₀ m₁ k) ⊕ m₁` agree. -/
def BijCPAScheme.keyEquiv (B : BijCPAScheme) (r : B.Input) (m₀ m₁ : B.Output) :
    B.Key ≃ B.Key where
  toFun k := (B.bij r).symm (B.xorOut (B.xorOut (B.bij r k) m₀) m₁)
  invFun k := (B.bij r).symm (B.xorOut (B.xorOut (B.bij r k) m₁) m₀)
  left_inv k := by
    simp only [Equiv.apply_symm_apply, B.xorOut_cancel, Equiv.symm_apply_apply]
  right_inv k := by
    simp only [Equiv.apply_symm_apply, B.xorOut_cancel, Equiv.symm_apply_apply]

/-- Reordered form of the IND-CPA game: sample the randomness `r` first, then the
key, then output `(r, (bij r k) ⊕ (if b then m₀ else m₁))`. -/
theorem bijCPA_game_eq (B : BijCPAScheme) (m₀ m₁ : B.Output) (b : Bool) :
    INDCPA_Game B.toEncScheme m₀ m₁ b =
      SPComp.bind (SPComp.sample B.Input) (fun r =>
        SPComp.bind (SPComp.sample B.Key) (fun k =>
          SPComp.pure (r, B.xorOut (B.bij r k) (if b then m₀ else m₁)))) := by
  funext h
  simp only [INDCPA_Game, BijCPAScheme.toEncScheme, SPComp.monad_bind_eq]
  exact SPComp.swap_sample_sample B.Key B.Input _
    (fun k r => SPComp.pure (r, B.xorOut (B.bij r k) (if b then m₀ else m₁))) h

/-- Coupling: the two IND-CPA games for the scheme are equidistributed.

At each fixed randomness `r`, over a uniform key the pad `bij r k` is uniform, so
`bij r k ⊕ m₀` and `bij r k ⊕ m₁` have the same distribution; `keyEquiv r m₀ m₁`
couples the two keys so the ciphertexts agree pointwise. -/
theorem bijCPA_indcpa_coupling (B : BijCPAScheme) (m₀ m₁ : B.Output) :
    rHoare eqPre
      (INDCPA_Game B.toEncScheme m₀ m₁ true)
      (INDCPA_Game B.toEncScheme m₀ m₁ false)
      eqPost := by
  rw [bijCPA_game_eq B m₀ m₁ true, bijCPA_game_eq B m₀ m₁ false]
  simp only [if_true, Bool.false_eq_true, if_false]
  ssprove_try_bij₂ (fun r => B.keyEquiv r m₀ m₁)
  congr 1
  -- `bij r (keyEquiv r m₀ m₁ k) = (bij r k ⊕ m₀) ⊕ m₁`, then cancel `⊕ m₁`.
  simp only [BijCPAScheme.keyEquiv, Equiv.coe_fn_mk, Equiv.apply_symm_apply]
  rw [B.xorOut_cancel]

/-- **The scheme has perfect IND-CPA security**: every adversary has IND-CPA
advantage exactly `0`. -/
theorem bijCPA_perfect_indcpa (B : BijCPAScheme) (m₀ m₁ : B.Output)
    (A : B.toEncScheme.Ciphertext → SPComp Bool) :
    INDCPA_Adv B.toEncScheme m₀ m₁ A = 0 :=
  INDCPA_Adv_zero_of_rHoare B.toEncScheme m₀ m₁ (bijCPA_indcpa_coupling B m₀ m₁) A

/-! ## Example: the XOR CPA scheme over `Bool`

`Enc(k, m) = (r, (k ⊕ r) ⊕ m)` with a fresh bit `r`, built from the XOR PRF
`F(k, r) = k ⊕ r` (`CatCrypt.Examples.PRF`, `boolXorPRF`). -/

/-- The XOR CPA scheme over `Bool`: `bij r = boolXorBij r`, `xorOut = xor`. -/
def boolXorCPA : BijCPAScheme where
  Key := Bool
  Input := Bool
  Output := Bool
  bij := boolXorBij
  xorOut := xor
  xorOut_cancel := fun a b => by cases a <;> cases b <;> rfl
  xorOut_cancel' := fun a b => by cases a <;> cases b <;> rfl

/-- The XOR CPA scheme over `Bool` is correct. -/
theorem boolXorCPA_correct : boolXorCPA.toEncScheme.Correct :=
  bijCPA_correct boolXorCPA

/-- **The XOR CPA scheme over `Bool` has perfect IND-CPA security.** -/
theorem boolXorCPA_perfect_indcpa (m₀ m₁ : Bool)
    (A : boolXorCPA.toEncScheme.Ciphertext → SPComp Bool) :
    INDCPA_Adv boolXorCPA.toEncScheme m₀ m₁ A = 0 :=
  bijCPA_perfect_indcpa boolXorCPA m₀ m₁ A

/-! ## Reflection into the Package / UC Stack

The shallow `bijCPA_perfect_indcpa` bounds a single distinguisher applied to the
two IND-CPA game bodies. This section lifts it to a composable statement about deep
nominal packages linked with an arbitrary adversary package, following the stack
`shallow game → rawCode% → NomPackage.ofOracle → DeepNomAdvantage → sdist → UC`
via the shared `CatCryptCore.Deep.ReflectUCHelpers` combinators. The IND-CPA game
samples the key and randomness then returns a pure ciphertext (heap-independent), so
the shallow coupling `bijCPA_indcpa_coupling` upgrades to a full `SPComp` equality of
the two reflected bodies (`spcomp_eq_of_isPure_coupling`), and the whole stack
follows with no purity bridge on the adversary. Applies verbatim to the `Bool`
instantiation `boolXorCPA`. -/

open CatCrypt.Deep

/-- The reflected IND-CPA game body for bit `b`: sample a key `k` and randomness
    `r`, then return the ciphertext `(r, (bij r k) ⊕ (if b then m₀ else m₁))`. -/
noncomputable def bijCpaGameRaw (B : BijCPAScheme) (m₀ m₁ : B.Output) (b : Bool) :
    RawCode (B.Input × B.Output) :=
  rawCode% (SPComp.bind (SPComp.sample B.Key) (fun k =>
    SPComp.bind (SPComp.sample B.Input) (fun r =>
      SPComp.pure (r, B.xorOut (B.bij r k) (if b then m₀ else m₁)))))

instance instValidBijCpaGameRaw (B : BijCPAScheme) (m₀ m₁ : B.Output) (b : Bool) :
    IsValid (∅ : LocSet) (bijCpaGameRaw B m₀ m₁ b) := by unfold bijCpaGameRaw; infer_instance

/-- The reflected body evaluates back to the shallow IND-CPA game. -/
theorem bijCpaGameRaw_eval_shallow (B : BijCPAScheme) (m₀ m₁ : B.Output) (b : Bool) :
    (bijCpaGameRaw B m₀ m₁ b).eval = INDCPA_Game B.toEncScheme m₀ m₁ b := by
  simp only [bijCpaGameRaw, RawCode.eval]; rfl

/-- The IND-CPA game is heap-independent (two uniform samples then a pure ciphertext). -/
theorem bijCpa_game_isPure (B : BijCPAScheme) (m₀ m₁ : B.Output) (b : Bool) :
    SPComp.IsPure (INDCPA_Game B.toEncScheme m₀ m₁ b) := by
  unfold INDCPA_Game BijCPAScheme.toEncScheme
  simp only [SPComp.monad_bind_eq]
  exact SPComp.bind_isPure (SPComp.sample_isPure _)
    (fun _ => SPComp.bind_isPure (SPComp.sample_isPure _) (fun _ => SPComp.pure_isPure _))

/-- The two reflected bodies (encrypting `m₀` vs. `m₁`) have equal evaluations: the
    heap-independent coupling `bijCPA_indcpa_coupling` upgrades to `SPComp` equality. -/
theorem bijCpaGameRaw_eval_eq (B : BijCPAScheme) (m₀ m₁ : B.Output) :
    (bijCpaGameRaw B m₀ m₁ true).eval = (bijCpaGameRaw B m₀ m₁ false).eval := by
  rw [bijCpaGameRaw_eval_shallow, bijCpaGameRaw_eval_shallow]
  exact spcomp_eq_of_isPure_coupling (bijCpa_game_isPure B m₀ m₁ true)
    (bijCpa_game_isPure B m₀ m₁ false) (bijCPA_indcpa_coupling B m₀ m₁)

/-- Real IND-CPA game as an oracle-exporting nominal package (encrypts `m₀`). -/
noncomputable def bijCpaGameTrue (B : BijCPAScheme) (m₀ m₁ : B.Output) : NomPackage :=
  NomPackage.ofOracle 1 Unit (B.Input × B.Output) (fun _ => bijCpaGameRaw B m₀ m₁ true)

/-- Ideal IND-CPA game as an oracle-exporting nominal package (encrypts `m₁`). -/
noncomputable def bijCpaGameFalse (B : BijCPAScheme) (m₀ m₁ : B.Output) : NomPackage :=
  NomPackage.ofOracle 1 Unit (B.Input × B.Output) (fun _ => bijCpaGameRaw B m₀ m₁ false)

/-- **Zero deep-nominal advantage against every adversary package.** -/
theorem bijCpa_deepnom_zero (B : BijCPAScheme) (m₀ m₁ : B.Output) (A : NomPackage) :
    DeepNomAdvantage (bijCpaGameTrue B m₀ m₁) (bijCpaGameFalse B m₀ m₁) A = 0 :=
  deepNomAdvantage_ofOracle_zero _ _ (fun _ => bijCpaGameRaw_eval_eq B m₀ m₁) A

/-- **Statistical distance zero** between the two linked-game families. -/
theorem bijCpa_sdist_zero (B : BijCPAScheme) (m₀ m₁ : B.Output) :
    sdist (fun A : NomPackage => runPkg (DeepPackage.link A.pkg (bijCpaGameTrue B m₀ m₁).pkg))
          (fun A : NomPackage => runPkg (DeepPackage.link A.pkg (bijCpaGameFalse B m₀ m₁).pkg)) = 0 :=
  sdist_ofOracle_zero _ _ (fun _ => bijCpaGameRaw_eval_eq B m₀ m₁)

/-- **Package-level perfect IND-CPA security** (`NomPkgSecure`). -/
theorem bijCpa_nompkg_secure (B : BijCPAScheme) (m₀ m₁ : B.Output) :
    NomPkgSecure (bijCpaGameTrue B m₀ m₁) (bijCpaGameFalse B m₀ m₁) (fun _ => 0) :=
  nomPkgSecure_ofOracle _ _ (fun _ => bijCpaGameRaw_eval_eq B m₀ m₁)

/-- **Perfect UC emulation** of the linked-game families over the trivial-leak
    interface (`out = Bool`, `leak = Empty`) with the identity simulator
    (composition plumbing). -/
theorem bijCpa_uc (B : BijCPAScheme) (m₀ m₁ : B.Output) :
    UCEmulates 0 ⟨NomPackage, Bool, Empty, Empty, Bool⟩
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (bijCpaGameTrue B m₀ m₁).pkg)))
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (bijCpaGameFalse B m₀ m₁).pkg))) :=
  uc_ofOracle _ _ (fun _ => bijCpaGameRaw_eval_eq B m₀ m₁)

/-! ## The Computational Reduction: IND-CPA ≤ PRF advantage

The perfect result above instantiates the PRF by a *bijection* family, making the
underlying PRF information-theoretically secure. We now give the genuine
**computational** result: for an *arbitrary* pseudorandom function `F`, the
encryption `Enc(k, m) = (r, F(k, r) ⊕ m)` is IND-CPA secure with advantage bounded
by the PRF advantage of `F`.

The argument is the standard single-reduction game hop through the *one-time-pad
world* `otpGame`, in which the keyed pad `F(k, r)` is replaced by a fresh uniform
output `u`:

| Step | Transition | Bound |
|------|-----------|-------|
| PRF-swap | `Enc` game ↔ `otpGame` (both worlds) | `ε_prf` (PRF assumption) |
| OTP | `otpGame m₀` ↔ `otpGame m₁` | `0` (one-time pad is perfect) |

The OTP hop is *perfect*: over a fresh uniform pad the two ciphertext
distributions coincide (`otp_advantage_zero`, proved by the `bind_vcgen`
change-of-variables tactic). The PRF-swap hop is the cryptographic reduction; its
soundness — that distinguishing the real encryption from the one-time-pad world is
no easier than distinguishing `F` from random — is taken as the hypothesis
`hswap`, bounded through the `PRFAssumption`. The two hops compose by the
advantage triangle inequality into `INDCPA_Adv ≤ ε_prf`.
-/

open CatCrypt.Tactic
open scoped ENNReal

/-- A PRF-based symmetric encryption scheme: `Enc(k, m) = (r, F.eval k r ⊕ m)` for
a fresh uniform `r`, where `⊕` is the involutive `xorOut` on outputs. Unlike
`BijCPAScheme`, the PRF `F` is *arbitrary* (no bijection assumption); security is
therefore computational, resting on a `PRFAssumption` for `F`. -/
structure PRFEncScheme where
  /-- The underlying pseudorandom function family. -/
  F : PRFScheme
  [finInput : Fintype F.Input]
  [neInput : Nonempty F.Input]
  /-- The XOR-like combining operation on outputs. -/
  xorOut : F.Output → F.Output → F.Output
  /-- `xorOut · b` is involutive: un-padding with the same pad recovers the value. -/
  xorOut_cancel : ∀ a b, xorOut (xorOut a b) b = a
  /-- `xorOut a ·` is involutive: decryption recovers the message. -/
  xorOut_cancel' : ∀ a b, xorOut a (xorOut a b) = b

attribute [instance] PRFEncScheme.finInput PRFEncScheme.neInput

/-- The core `EncScheme` induced by a PRF-based scheme: `Enc(k, m) = (r, F(k,r) ⊕ m)`. -/
noncomputable def PRFEncScheme.toEncScheme (P : PRFEncScheme) : EncScheme where
  Key := P.F.Key
  Plaintext := P.F.Output
  Ciphertext := P.F.Input × P.F.Output
  finKey := inferInstance
  neKey := inferInstance
  finCt := inferInstance
  neCt := inferInstance
  keyGen := SPComp.sample P.F.Key
  encrypt := fun k m => do
    let r ← SPComp.sample P.F.Input
    SPComp.pure (r, P.xorOut (P.F.eval k r) m)
  decrypt := fun k c => SPComp.pure (some (P.xorOut (P.F.eval k c.1) c.2))

/-- The **one-time-pad world**: the game obtained from the IND-CPA game by
replacing the keyed pad `F(k, r)` with a fresh uniform output `u`. Encrypting
`if b then m₀ else m₁` as `(r, u ⊕ (if b then m₀ else m₁))`. -/
noncomputable def PRFEncScheme.otpGame (P : PRFEncScheme) (m₀ m₁ : P.F.Output)
    (b : Bool) : SPComp (P.F.Input × P.F.Output) := do
  let r ← SPComp.sample P.F.Input
  let u ← SPComp.sample P.F.Output
  SPComp.pure (r, P.xorOut u (if b then m₀ else m₁))

/-- The involution `u ↦ xorOut u m` as a self-bijection of the output space (its
own inverse by `xorOut_cancel`). This is the change of variables that collapses a
uniform pad to a plain uniform sample. -/
def PRFEncScheme.xorEquiv (P : PRFEncScheme) (m : P.F.Output) : P.F.Output ≃ P.F.Output where
  toFun u := P.xorOut u m
  invFun u := P.xorOut u m
  left_inv u := P.xorOut_cancel u m
  right_inv u := P.xorOut_cancel u m

/-- Over a fresh uniform pad the padded ciphertext distribution is independent of
the message: the two one-time-pad worlds are the *same* `SPComp` computation.
Proved by the `bind_vcgen` run-to-completion tactic, feeding it the
change-of-variables `xorEquiv` that rewrites the uniform pad into a plain uniform
sample. -/
theorem PRFEncScheme.otpGame_true_eq_false (P : PRFEncScheme) (m₀ m₁ : P.F.Output) :
    P.otpGame m₀ m₁ true = P.otpGame m₀ m₁ false := by
  -- Each world independently collapses to the pad-free game via `xorEquiv`.
  have key : ∀ (m : P.F.Output) (r : P.F.Input),
      SPComp.bind (SPComp.sample P.F.Output) (fun u => SPComp.pure (r, P.xorOut u m))
        = SPComp.bind (SPComp.sample P.F.Output) (fun u => SPComp.pure (r, u)) := by
    intro m r
    bind_vcgen using (P.xorEquiv m)
  simp only [PRFEncScheme.otpGame, if_true, Bool.false_eq_true, if_false,
    SPComp.monad_bind_eq]
  refine congrArg (SPComp.bind (SPComp.sample P.F.Input)) (funext fun r => ?_)
  rw [key m₀ r, key m₁ r]

/-- **The OTP hop is perfect**: over a fresh uniform pad, no adversary distinguishes
the `m₀`- from the `m₁`-world. Its advantage is exactly `0`. -/
theorem PRFEncScheme.otp_advantage_zero (P : PRFEncScheme) (m₀ m₁ : P.F.Output)
    (A : (P.F.Input × P.F.Output) → SPComp Bool) :
    AdvantageA (P.otpGame m₀ m₁ true) (P.otpGame m₀ m₁ false) A = 0 := by
  simp only [AdvantageA, P.otpGame_true_eq_false, Advantage_self]

/-- **IND-CPA security from a PRF assumption** (the computational headline).

For the PRF-based encryption `Enc(k, m) = (r, F(k, r) ⊕ m)`, the IND-CPA advantage
of any adversary `A` is bounded by the PRF advantage `H.ε` of the underlying
function `F`.

The proof composes two hops by the advantage triangle inequality, routing through
the one-time-pad world `otpGame`:

* the **PRF-swap** hop `hswap` — the reduction's soundness: distinguishing the real
  encryption from the one-time-pad world (in both challenge worlds) is bounded by a
  single PRF distinguisher's advantage `PRF_Adv F x Ared`, hence by `H.ε` via the
  assumption; and
* the **perfect-OTP** hop `otp_advantage_zero` — a one-time pad on a fresh uniform
  pad leaks nothing, contributing `0`.

`x`/`Ared` are the reduction's PRF-distinguisher witness. The `hswap` hypothesis
packages the (large) explicit-reduction construction, exactly as the cascade bound
`CatCrypt.Examples.PRF.cascade_prf_bound` exposes its hop bounds as hypotheses. -/
theorem cpa_from_prf_bound (P : PRFEncScheme) (H : PRFAssumption P.F)
    (m₀ m₁ : P.F.Output) (A : (P.F.Input × P.F.Output) → SPComp Bool)
    (x : P.F.Input) (Ared : P.F.Output → SPComp Bool)
    (hswap :
      AdvantageA (INDCPA_Game P.toEncScheme m₀ m₁ true) (P.otpGame m₀ m₁ true) A
        + AdvantageA (P.otpGame m₀ m₁ false) (INDCPA_Game P.toEncScheme m₀ m₁ false) A
        ≤ PRF_Adv P.F x Ared) :
    INDCPA_Adv P.toEncScheme m₀ m₁ A ≤ H.ε := by
  have hotp := P.otp_advantage_zero m₀ m₁ A
  have htri1 := advantage_triangle
    ((INDCPA_Game P.toEncScheme m₀ m₁ true).bind A)
    ((P.otpGame m₀ m₁ true).bind A)
    ((INDCPA_Game P.toEncScheme m₀ m₁ false).bind A)
  have htri2 := advantage_triangle
    ((P.otpGame m₀ m₁ true).bind A)
    ((P.otpGame m₀ m₁ false).bind A)
    ((INDCPA_Game P.toEncScheme m₀ m₁ false).bind A)
  simp only [INDCPA_Adv, AdvantageA] at hotp hswap ⊢
  calc Advantage ((INDCPA_Game P.toEncScheme m₀ m₁ true).bind A)
          ((INDCPA_Game P.toEncScheme m₀ m₁ false).bind A)
      ≤ Advantage ((INDCPA_Game P.toEncScheme m₀ m₁ true).bind A)
            ((P.otpGame m₀ m₁ true).bind A)
          + Advantage ((P.otpGame m₀ m₁ true).bind A)
            ((INDCPA_Game P.toEncScheme m₀ m₁ false).bind A) := htri1
    _ ≤ Advantage ((INDCPA_Game P.toEncScheme m₀ m₁ true).bind A)
            ((P.otpGame m₀ m₁ true).bind A)
          + (Advantage ((P.otpGame m₀ m₁ true).bind A) ((P.otpGame m₀ m₁ false).bind A)
             + Advantage ((P.otpGame m₀ m₁ false).bind A)
                ((INDCPA_Game P.toEncScheme m₀ m₁ false).bind A)) :=
        add_le_add le_rfl htri2
    _ = Advantage ((INDCPA_Game P.toEncScheme m₀ m₁ true).bind A)
            ((P.otpGame m₀ m₁ true).bind A)
          + Advantage ((P.otpGame m₀ m₁ false).bind A)
            ((INDCPA_Game P.toEncScheme m₀ m₁ false).bind A) := by
        rw [hotp, zero_add]
    _ ≤ PRF_Adv P.F x Ared := hswap
    _ ≤ H.ε := H.bound x Ared

/-! ## The Synthesized Reduction: discharging the PRF-swap hop

`cpa_from_prf_bound` takes the PRF-swap soundness `hswap` as a hypothesis. We now
*build* the concrete PRF distinguisher and prove the swap hops outright, so the
computational IND-CPA bound rests only on the `PRFAssumption` — no assumed hop.

The single-challenge IND-CPA game samples a *fresh* randomness `r` and pads with
`F(k, r)`, whereas the single-query PRF game `PRF_Real F x` fixes its input `x`.
The two are reconciled by conditioning on `r`: after reordering the game so `r` is
sampled first (`indcpa_game_eq`), each fixed-`r` slice is *literally* a PRF
distinguishing experiment — the distinguisher is `cpaReduction r m A`, which pads
its oracle output with `m` at randomness `r` and runs `A`. This gives the exact
per-slice identity `slice_eq`; averaging over `r` with `advantageA_sample_bind`
bounds each swap hop by `H.ε` (`indcpa_otp_hop`).

The IND-CPA advantage then decomposes by the triangle inequality through the two
one-time-pad worlds into two such swap hops (plus the perfect OTP hop), yielding
the `2 · H.ε` bound of `cpa_from_prf_reduction_gamehop`. The factor two is the two
independent PRF replacements (one per challenge world) inherent to the left-right
advantage formulation, matching Rosulek §7. -/

/-- The **PRF-distinguisher reduction** built from the IND-CPA adversary `A`.

Given the challenge randomness `r` and message `m`, `cpaReduction r m A` is the
single-query PRF distinguisher that receives a candidate pad `y` — either the keyed
value `F(k, r)` in the PRF real game, or a fresh uniform output in the ideal game —
forms the challenge ciphertext `(r, y ⊕ m)`, runs `A` on it, and returns `A`'s
guess. With a real pad it reproduces the IND-CPA game at randomness `r`; with a
uniform pad, the one-time-pad world at `r`. -/
def PRFEncScheme.cpaReduction (P : PRFEncScheme) (r : P.F.Input) (m : P.F.Output)
    (A : (P.F.Input × P.F.Output) → SPComp Bool) : P.F.Output → SPComp Bool :=
  fun y => A (r, P.xorOut y m)

/-- Reordered form of the IND-CPA game for the PRF scheme: sample the randomness
`r` first, then the key `k`, then output `(r, F(k, r) ⊕ (if b then m₀ else m₁))`.
The reorder is the Fubini commutation of the two independent samples
(`SPComp.swap_sample_sample`). -/
theorem PRFEncScheme.indcpa_game_eq (P : PRFEncScheme) (m₀ m₁ : P.F.Output) (b : Bool) :
    INDCPA_Game P.toEncScheme m₀ m₁ b =
      SPComp.bind (SPComp.sample P.F.Input) (fun r =>
        SPComp.bind (SPComp.sample P.F.Key) (fun k =>
          SPComp.pure (r, P.xorOut (P.F.eval k r) (if b then m₀ else m₁)))) := by
  funext h
  simp only [INDCPA_Game, PRFEncScheme.toEncScheme, SPComp.monad_bind_eq]
  exact SPComp.swap_sample_sample P.F.Key P.F.Input _
    (fun k r => SPComp.pure (r, P.xorOut (P.F.eval k r) (if b then m₀ else m₁))) h

/-- **The per-randomness slice is exactly a PRF distinguishing advantage.**

At a fixed challenge randomness `r`, the advantage between the keyed-pad game
(`sample k; (r, F(k, r) ⊕ m)`) and the uniform-pad game (`sample u; (r, u ⊕ m)`)
against `A` *equals* the PRF advantage of the built distinguisher
`cpaReduction r m A`. This is a definitional identity: `A`'s view after either
game is exactly the reduction's view after the corresponding PRF game. -/
theorem PRFEncScheme.slice_eq (P : PRFEncScheme) (r : P.F.Input) (m : P.F.Output)
    (A : (P.F.Input × P.F.Output) → SPComp Bool) :
    AdvantageA
      (SPComp.bind (SPComp.sample P.F.Key) (fun k => SPComp.pure (r, P.xorOut (P.F.eval k r) m)))
      (SPComp.bind (SPComp.sample P.F.Output) (fun u => SPComp.pure (r, P.xorOut u m))) A
      = PRF_Adv P.F r (P.cpaReduction r m A) := by
  unfold PRFEncScheme.cpaReduction
  simp only [AdvantageA, PRF_Adv, PRF_Real, PRF_Ideal, ssprove_simpl]

/-- **The PRF-swap hop, discharged by the built reduction.**

For each challenge world `b`, distinguishing the real PRF encryption from the
one-time-pad world is bounded by `H.ε`: reorder so the randomness `r` is sampled
first (`indcpa_game_eq`), then average the per-`r` slices (`advantageA_sample_bind`),
each of which equals `PRF_Adv P.F r (cpaReduction r · A)` (`slice_eq`) and is hence
`≤ H.ε` by the PRF assumption. No hop is assumed. -/
theorem PRFEncScheme.indcpa_otp_hop (P : PRFEncScheme) (H : PRFAssumption P.F)
    (m₀ m₁ : P.F.Output) (A : (P.F.Input × P.F.Output) → SPComp Bool) (b : Bool) :
    AdvantageA (INDCPA_Game P.toEncScheme m₀ m₁ b) (P.otpGame m₀ m₁ b) A ≤ H.ε := by
  rw [P.indcpa_game_eq m₀ m₁ b]
  have hotp : P.otpGame m₀ m₁ b
      = SPComp.bind (SPComp.sample P.F.Input) (fun r =>
          SPComp.bind (SPComp.sample P.F.Output) (fun u =>
            SPComp.pure (r, P.xorOut u (if b then m₀ else m₁)))) := by
    simp only [PRFEncScheme.otpGame, SPComp.monad_bind_eq]
  rw [hotp]
  exact advantageA_sample_bind _ _ _ _ (fun r =>
    (P.slice_eq r (if b then m₀ else m₁) A).le.trans (H.bound r _))

/-- **IND-CPA security from a PRF, fully synthesized** (no assumed swap hop).

For the PRF-based encryption `Enc(k, m) = (r, F(k, r) ⊕ m)`, the IND-CPA advantage
of any adversary `A` is at most `2 · H.ε`, resting *only* on the `PRFAssumption`
`H`. The `adv_game_hop` tactic composes, by the advantage triangle inequality
through the two one-time-pad worlds:

* the two **PRF-swap** hops `indcpa_otp_hop` (each `≤ H.ε`), *proved* from the
  concrete distinguisher `cpaReduction` rather than assumed; and
* the **perfect-OTP** hop `otp_advantage_zero` (`= 0`).

The factor two is the two independent PRF replacements — one per challenge world —
that the left-right advantage genuinely requires; it cannot be collapsed to a
single `H.ε` without assuming a combined distinguisher whose advantage exceeds the
PRF bound (Rosulek §7). -/
theorem cpa_from_prf_reduction_gamehop (P : PRFEncScheme) (H : PRFAssumption P.F)
    (m₀ m₁ : P.F.Output) (A : (P.F.Input × P.F.Output) → SPComp Bool) :
    INDCPA_Adv P.toEncScheme m₀ m₁ A ≤ 2 * H.ε := by
  rw [show (2 : ℝ≥0∞) * H.ε = H.ε + 0 + H.ε by rw [two_mul, add_zero]]
  unfold INDCPA_Adv
  adv_game_hop [P.otpGame m₀ m₁ true, P.otpGame m₀ m₁ false]
  · exact P.indcpa_otp_hop H m₀ m₁ A true
  · exact le_of_eq (P.otp_advantage_zero m₀ m₁ A)
  · simpa only [AdvantageA, Advantage_sym] using P.indcpa_otp_hop H m₀ m₁ A false

end CatCrypt.Examples.CPAFromPRF
