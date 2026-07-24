/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Prob.XorBij
import CatCryptCore.Tactics
import CatCryptCore.Deep.ReflectUCHelpers

/-!
# Commitment Schemes: Perfect Hiding and Perfect Binding

A commitment scheme lets a sender *commit* to a message `m` — publishing a
commitment `c` that hides `m` — and later *open* it by revealing `m` together
with the randomness `r`. Following Rosulek, The Joy of Cryptography (Chapter on
commitment schemes), the two security goals are:

* **hiding** — the commitment `c` reveals nothing about the committed message;
* **binding** — the sender cannot open a single commitment to two different
  messages.

This file defines a minimal `CommScheme` structure, the hiding game (phrased over
the core `AdvantageA`), and the perfect-binding predicate, then instantiates two
schemes over `Bool`:

* `MaskComm` — the one-time-pad / masking commitment `commit(m; r) = m ⊕ r` with
  `r` uniform. A uniform mask makes the commitment uniform and independent of `m`,
  so the hiding advantage of *every* adversary is exactly `0` (perfect hiding).
* `IdComm` — the trivial deterministic commitment `commit(m; r) = m`, which is
  perfectly binding.

The two examples witness the information-theoretic tension Rosulek highlights: a
commitment scheme cannot be simultaneously perfectly hiding and perfectly
binding. `MaskComm` is the OTP argument on the hiding side; `IdComm` shows the
binding predicate is inhabited.

## Main definitions

* `CommScheme` — a commitment scheme (`commit`, `verify`, uniform randomness).
* `Hiding_Game` / `Hiding_Adv` — the hiding game and its advantage.
* `CommScheme.PerfectlyBinding` — no commitment opens to two distinct messages.
* `MaskComm`, `IdComm` — the masking and identity commitments over `Bool`.

## Main results

* `maskComm_correct` — an honest opening of a `MaskComm` commitment verifies.
* `maskComm_perfect_hiding` — **the masking commitment is perfectly hiding**:
  `Hiding_Adv MaskComm m₀ m₁ A = 0` for every adversary `A`.
* `idComm_perfectly_binding` — the identity commitment is perfectly binding.

## References

* [Rosulek, The Joy of Cryptography, Chapter on commitment schemes]
* [Shannon, Communication Theory of Secrecy Systems, 1949]
-/

namespace CatCrypt.Examples.Commitment

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open CatCrypt.Relational
open scoped ENNReal

/-! ## Commitment Scheme -/

/-- A (non-interactive) commitment scheme.

- `Message`, `Randomness`, `Commitment` are the data types.
- `commit r m` produces the commitment to message `m` under randomness `r`.
- `verify c m r` checks that `(m, r)` is a valid opening of the commitment `c`.

`Randomness` is required finite and nonempty so it can be sampled uniformly in
the hiding game. -/
structure CommScheme where
  /-- Message (committed value) type -/
  Message : Type
  /-- Randomness (opening) type -/
  Randomness : Type
  /-- Commitment type -/
  Commitment : Type
  /-- Randomness is finite (for uniform sampling) -/
  [finRand : Fintype Randomness]
  /-- Randomness is nonempty (for uniform sampling) -/
  [neRand : Nonempty Randomness]
  /-- Deterministic commitment function -/
  commit : Randomness → Message → Commitment
  /-- Opening verification: is `(m, r)` a valid opening of `c`? -/
  verify : Commitment → Message → Randomness → Bool

attribute [instance] CommScheme.finRand CommScheme.neRand

namespace CommScheme

variable (C : CommScheme)

/-- Correctness: an honestly produced commitment opens back to its message. -/
def Correct : Prop :=
  ∀ (r : C.Randomness) (m : C.Message), C.verify (C.commit r m) m r = true

/-- **Perfect binding**: no commitment can be opened to two distinct messages.
    That is, if `(m₀, r₀)` and `(m₁, r₁)` both verify against the same commitment
    `c`, then `m₀ = m₁`. -/
def PerfectlyBinding : Prop :=
  ∀ (c : C.Commitment) (m₀ m₁ : C.Message) (r₀ r₁ : C.Randomness),
    C.verify c m₀ r₀ = true → C.verify c m₁ r₁ = true → m₀ = m₁

end CommScheme

/-! ## Hiding Game -/

/-- The hiding game for a commitment scheme.

    The challenger samples fresh randomness `r` and returns the commitment to
    `m₀` (when `b = true`) or `m₁` (when `b = false`). The adversary is given the
    commitment and tries to guess `b`.

    - `Hiding_Game C m₀ m₁ true` — commits to `m₀` (left)
    - `Hiding_Game C m₀ m₁ false` — commits to `m₁` (right) -/
noncomputable def Hiding_Game (C : CommScheme) (m₀ m₁ : C.Message) (b : Bool) :
    SPComp C.Commitment := do
  let r ← SPComp.sample C.Randomness
  SPComp.pure (C.commit r (if b then m₀ else m₁))

/-- Hiding advantage: the probability with which an adversary distinguishes a
    commitment to `m₀` from a commitment to `m₁`. -/
noncomputable def Hiding_Adv (C : CommScheme) (m₀ m₁ : C.Message)
    (A : C.Commitment → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (Hiding_Game C m₀ m₁ true) (Hiding_Game C m₀ m₁ false) A

/-! ## Masking Commitment: Perfect Hiding

`commit(m; r) = m ⊕ r`, the one-time-pad commitment. -/

/-- The masking commitment over `Bool`: `commit r m = r ⊕ m`, opened by revealing
    `(m, r)`. This is the one-time-pad commitment. -/
noncomputable def MaskComm : CommScheme where
  Message := Bool
  Randomness := Bool
  Commitment := Bool
  finRand := inferInstance
  neRand := ⟨false⟩
  commit := fun r m => xor r m
  verify := fun c m r => decide (c = xor r m)

/-- The masking commitment is correct: an honest opening verifies. -/
theorem maskComm_correct : MaskComm.Correct := by
  simp [MaskComm, CommScheme.Correct]

/-- Coupling: the two hiding games for the masking commitment are
    equidistributed.

    For a uniform mask `r`, both `r ⊕ m₀` and `r ⊕ m₁` are uniformly distributed
    (XOR-by-a-fixed-bit is a bijection of the mask). The bijection
    `boolXorBij (m₀ ⊕ m₁)` re-labels the mask on the right so the two commitments
    coincide, coupling the games under `eqPost`. -/
theorem maskComm_hiding_coupling (m₀ m₁ : Bool) :
    rHoare eqPre
      (Hiding_Game MaskComm m₀ m₁ true)
      (Hiding_Game MaskComm m₀ m₁ false)
      eqPost := by
  simp only [Hiding_Game, MaskComm, if_true, Bool.false_eq_true, if_false,
    SPComp.monad_bind_eq]
  ssprove_couple_bij (boolXorBij (xor m₀ m₁))

/-- **The masking commitment is perfectly hiding**: every adversary has hiding
    advantage exactly `0`. -/
theorem maskComm_perfect_hiding (m₀ m₁ : Bool)
    (A : MaskComm.Commitment → SPComp Bool) :
    Hiding_Adv MaskComm m₀ m₁ A = 0 :=
  advantage_zero_of_rHoare _ _ (maskComm_hiding_coupling m₀ m₁) A

/-- The masking commitment's output varies with the committed message: for fixed
    randomness there are two messages whose commitments differ. Perfect hiding
    therefore comes from the uniform mask, not from the commit function ignoring
    the message. -/
theorem maskComm_output_depends_on_secret :
    ∃ (m₀ m₁ r : Bool), m₀ ≠ m₁ ∧ MaskComm.commit r m₀ ≠ MaskComm.commit r m₁ :=
  ⟨true, false, false, by decide, by simp [MaskComm]⟩

/-! ## Reflection into the Package / UC Stack

The shallow `maskComm_perfect_hiding` bounds a single distinguisher applied to the
two hiding-game bodies. This section lifts it to a composable statement about deep
nominal packages linked with an arbitrary adversary package, following the stack
`shallow game → rawCode% → NomPackage.ofOracle → DeepNomAdvantage → sdist → UC`
via the shared `CatCryptCore.Deep.ReflectUCHelpers` combinators. The masking
commitment `commit r m = r ⊕ m` is heap-independent, so the shallow coupling
`maskComm_hiding_coupling` upgrades to a full `SPComp` equality of the two reflected
bodies (`spcomp_eq_of_isPure_coupling`), and the whole stack follows with no purity
bridge on the adversary. -/

open CatCrypt.Deep

/-- The reflected masking-commitment hiding-game body for bit `b`: sample a uniform
    mask `r` and return the one-time-pad commitment `r ⊕ (if b then m₀ else m₁)`. -/
noncomputable def maskGameRaw (m₀ m₁ b : Bool) : RawCode Bool :=
  rawCode% (SPComp.bind (SPComp.sample Bool)
    (fun r => SPComp.pure (xor r (if b then m₀ else m₁))))

instance instValidMaskGameRaw (m₀ m₁ b : Bool) :
    IsValid (∅ : LocSet) (maskGameRaw m₀ m₁ b) := by unfold maskGameRaw; infer_instance

/-- The reflected body evaluates back to the shallow hiding game. -/
theorem maskGameRaw_eval_shallow (m₀ m₁ b : Bool) :
    (maskGameRaw m₀ m₁ b).eval = Hiding_Game MaskComm m₀ m₁ b := by
  rfl

/-- The hiding game is heap-independent (a uniform mask then a pure commitment). -/
theorem mask_game_isPure (m₀ m₁ b : Bool) : SPComp.IsPure (Hiding_Game MaskComm m₀ m₁ b) := by
  simp only [Hiding_Game, SPComp.monad_bind_eq]
  exact SPComp.bind_isPure (SPComp.sample_isPure _) (fun _ => SPComp.pure_isPure _)

/-- The two reflected bodies (commit to `m₀` vs. `m₁`) have equal evaluations: the
    heap-independent coupling `maskComm_hiding_coupling` upgrades to `SPComp`
    equality. -/
theorem maskGameRaw_eval_eq (m₀ m₁ : Bool) :
    (maskGameRaw m₀ m₁ true).eval = (maskGameRaw m₀ m₁ false).eval := by
  rw [maskGameRaw_eval_shallow, maskGameRaw_eval_shallow]
  exact spcomp_eq_of_isPure_coupling (mask_game_isPure m₀ m₁ true)
    (mask_game_isPure m₀ m₁ false) (maskComm_hiding_coupling m₀ m₁)

/-- Real hiding game as an oracle-exporting nominal package (commits to `m₀`). -/
noncomputable def maskGameTrue (m₀ m₁ : Bool) : NomPackage :=
  NomPackage.ofOracle 1 Unit Bool (fun _ => maskGameRaw m₀ m₁ true)

/-- Ideal hiding game as an oracle-exporting nominal package (commits to `m₁`). -/
noncomputable def maskGameFalse (m₀ m₁ : Bool) : NomPackage :=
  NomPackage.ofOracle 1 Unit Bool (fun _ => maskGameRaw m₀ m₁ false)

/-- **Zero deep-nominal advantage against every adversary package.** -/
theorem mask_deepnom_zero (m₀ m₁ : Bool) (A : NomPackage) :
    DeepNomAdvantage (maskGameTrue m₀ m₁) (maskGameFalse m₀ m₁) A = 0 :=
  deepNomAdvantage_ofOracle_zero _ _ (fun _ => maskGameRaw_eval_eq m₀ m₁) A

/-- **Statistical distance zero** between the two linked-game families. -/
theorem mask_sdist_zero (m₀ m₁ : Bool) :
    sdist (fun A : NomPackage => runPkg (DeepPackage.link A.pkg (maskGameTrue m₀ m₁).pkg))
          (fun A : NomPackage => runPkg (DeepPackage.link A.pkg (maskGameFalse m₀ m₁).pkg)) = 0 :=
  sdist_ofOracle_zero _ _ (fun _ => maskGameRaw_eval_eq m₀ m₁)

/-- **Package-level perfect hiding** (`NomPkgSecure`). -/
theorem mask_nompkg_secure (m₀ m₁ : Bool) :
    NomPkgSecure (maskGameTrue m₀ m₁) (maskGameFalse m₀ m₁) (fun _ => 0) :=
  nomPkgSecure_ofOracle _ _ (fun _ => maskGameRaw_eval_eq m₀ m₁)

/-- **Perfect UC emulation** of the linked-game families over the trivial-leak
    interface (`out = Bool`, `leak = Empty`) with the identity simulator
    (composition plumbing). -/
theorem mask_uc (m₀ m₁ : Bool) :
    UCEmulates 0 ⟨NomPackage, Bool, Empty, Empty, Bool⟩
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (maskGameTrue m₀ m₁).pkg)))
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (maskGameFalse m₀ m₁).pkg))) :=
  uc_ofOracle _ _ (fun _ => maskGameRaw_eval_eq m₀ m₁)

/-- **Reflection mirrors the shallow game.** Against the forwarding adversary, the
    deep-nominal advantage equals the shallow hiding advantage under the identity
    distinguisher — which is `0` by `maskComm_perfect_hiding`. -/
theorem mask_deepnom_forward_eq_adv (m₀ m₁ : Bool) :
    DeepNomAdvantage (maskGameTrue m₀ m₁) (maskGameFalse m₀ m₁) forwardAdv =
    Hiding_Adv MaskComm m₀ m₁ SPComp.pure := by
  unfold DeepNomAdvantage maskGameTrue maskGameFalse
  rw [runPkg_link_forward (maskGameRaw m₀ m₁ true),
      runPkg_link_forward (maskGameRaw m₀ m₁ false),
      maskGameRaw_eval_shallow, maskGameRaw_eval_shallow]
  exact (AdvantageA_pure _ _).symm

/-! ## Identity Commitment: Perfect Binding

`commit(m; r) = m` — a deterministic commitment that ignores its randomness. It
provides no hiding, but it is perfectly binding: the commitment *is* the message,
so it can only be opened to that one message. This witnesses the hiding/binding
tension: no scheme achieves both perfectly. -/

/-- The identity commitment over `Bool`: `commit r m = m`, opened by revealing
    `m` (the randomness is irrelevant). -/
noncomputable def IdComm : CommScheme where
  Message := Bool
  Randomness := Unit
  Commitment := Bool
  finRand := inferInstance
  neRand := inferInstance
  commit := fun _ m => m
  verify := fun c m _ => decide (c = m)

/-- The identity commitment is correct. -/
theorem idComm_correct : IdComm.Correct := by
  simp [IdComm, CommScheme.Correct]

/-- The identity commitment is perfectly binding: since the commitment equals the
    committed message, any two valid openings expose the same message. -/
theorem idComm_perfectly_binding : IdComm.PerfectlyBinding := by
  intro c m₀ m₁ r₀ r₁ h₀ h₁
  simp_all [IdComm]

end CatCrypt.Examples.Commitment
