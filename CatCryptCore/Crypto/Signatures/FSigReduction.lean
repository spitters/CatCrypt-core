/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.FSigSys
public import CatCryptCore.Crypto.Signatures.EUFCMAPMF
public import CatCryptCore.Crypto.UCOracleGame

/-!
# The signature functionality up to the EUF-CMA advantage of a forger

For a signature scheme `S` given by probability mass functions (`PSigScheme`), every
environment `Z` of the real signing system `realSig S.toSigScheme` defines a forger
`forger S Z`, an adaptive oracle adversary of the EUF-CMA game: on the public key `pk` it runs
`Z` from its initial heap, answers key generation with `pk`, signing queries with its signing
oracle and verifications with the verifier of `S`, and outputs the first verified pair of a
message never signed under `pk`.

## Main definitions

* `forgeAct`: one activation of the real signer, simulated by the forger.
* `forgeReduce`, `forger`: the forger of an environment.
* `forgeWin`: the winning condition of the EUF-CMA game for a final output and log.

## Main results

* `prBad_realSig_le_eufcma`: the probability of a forgery in the run of `Z` against
  `realSig S.toSigScheme` is at most the EUF-CMA advantage of `forger S Z`.
* `realSig_realizesSim_fsig_eufcma`: for a scheme consistent in relational form, the real
  signing system realizes `fsig` behind `fsigSim` with bound, at the environment `Z`, the
  EUF-CMA advantage of `forger S Z`.

The time certificate of the reduction `forger` is not part of this file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signatures.FSigSys

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCTransparent
open CatCrypt.Crypto.UCConcrete
open scoped ENNReal

variable {Msg PK SK Sig ζ : Type}

/-! ## Unfolding lemmas -/

/-- The signing algorithm of `S.toSigScheme` (unfolding lemma of `PSigScheme.toSigScheme`). -/
theorem toSigScheme_sign (S : PSigScheme Msg PK SK Sig) (sk : SK) (m : Msg) :
    S.toSigScheme.sign sk m = liftPMF (S.sign sk m) :=
  rfl

/-- A step of the real signer on the honest port (unfolding lemma of `realSig`). -/
theorem realSig_step_inl [DecidableEq Msg] [DecidableEq PK] (S : SigScheme Msg PK SK Sig)
    (t : RealSt Msg PK SK Sig) (e : SigEv Msg PK Sig) :
    (realSig S).step t (.inl e) = SPComp.map (fun q => (q.1, .inl q.2)) (realHonStep S t e) :=
  rfl

/-- A step of the real signer on the adversary port (unfolding lemma of `realSig`). -/
theorem realSig_step_inr [DecidableEq Msg] [DecidableEq PK] (S : SigScheme Msg PK SK Sig)
    (t : RealSt Msg PK SK Sig) (u : Unit) :
    (realSig S).step t (.inr u) = SPComp.map (fun q => (q.1, .inr q.2)) (SPComp.pure (t, ())) :=
  rfl

/-! ## The forger -/

section Forger

variable [DecidableEq Msg] [DecidableEq PK] [Inhabited Msg] [Inhabited Sig]

/-- The state of the forger: whether key generation has happened, and the signed pairs. -/
abbrev ForgeSt (Msg Sig : Type) := Bool × List (Msg × Sig)

/-- One activation of the real signer with public key `pk`, simulated by the forger from the
state `st`: key generation returns `pk`; after key generation, signing asks the signing oracle
and verification runs the verifier of `S`, except that a verification of a forgery ends the run
with the forgery (`inl`). Before key generation, signing and verification return `err`. -/
noncomputable def forgeAct (S : PSigScheme Msg PK SK Sig) (pk : PK) (st : ForgeSt Msg Sig) :
    SigEv Msg PK Sig ⊕ Unit →
      OracleAdv Msg Sig ((Msg × Sig) ⊕ (ForgeSt Msg Sig × (SigOut PK Sig ⊕ Unit)))
  | .inr u => .ret (.inr (st, .inr u))
  | .inl .keyGen => .ret (.inr ((true, st.2), .inl (.vk pk)))
  | .inl (.sign m) =>
    if st.1 then .query m fun σ => .ret (.inr ((true, (m, σ) :: st.2), .inl (.sig σ)))
    else .ret (.inr (st, .inl .err))
  | .inl (.verify m σ vk) =>
    if st.1 then
      if isForgery S.toSigScheme pk st.2 m σ vk then .ret (.inl (m, σ))
      else .ret (.inr (st, .inl (.result (S.verify vk m σ))))
    else .ret (.inr (st, .inl .err))

/-- The forger of the environment strategy `Z` with public key `pk`, for `n` remaining
activations from the environment state `z`, the forger state `st` and the heap `h`: it samples
the next event of `Z`, simulates the real signer on it (`forgeAct`), and gives the output to
`Z`. It outputs the first forgery, and `default` when no forgery occurs. -/
noncomputable def forgeReduce (S : PSigScheme Msg PK SK Sig)
    (Z : Strat ζ (SigEv Msg PK Sig ⊕ Unit) (SigOut PK Sig ⊕ Unit)) (pk : PK) :
    ℕ → ζ → ForgeSt Msg Sig → Heap → OracleAdv Msg Sig (Msg × Sig)
  | 0, _, _, _ => .ret default
  | n + 1, z, st, h => .rand (Z.next z h) fun o => match o with
    | none => .ret default
    | some ((z₁, e), h₁) => (forgeAct S pk st e).bind fun r => match r with
      | .inl f => .ret f
      | .inr (st', out) => .rand (Z.obs z₁ out h₁) fun o' => match o' with
        | none => .ret default
        | some (z₂, h₂) => forgeReduce S Z pk n z₂ st' h₂

/-- **The forger of the environment `Z`**: `forgeReduce` from the initial state of `Z`, before
key generation, from the initial heap of `Z`. -/
noncomputable def forger (S : PSigScheme Msg PK SK Sig)
    (Z : Env (Strat ζ (SigEv Msg PK Sig ⊕ Unit) (SigOut PK Sig ⊕ Unit)) ζ) (pk : PK) :
    OracleAdv Msg Sig (Msg × Sig) :=
  forgeReduce S Z.input pk Z.input.rounds Z.input.init (false, []) Z.heap

/-- The winning condition of the EUF-CMA game under the public key `pk`: the output verifies
and its message is not in the log. -/
def forgeWin (S : PSigScheme Msg PK SK Sig) (pk : PK) (x : (Msg × Sig) × List (Msg × Sig)) :
    Bool :=
  S.verify pk x.1.1 x.1.2 && !(x.2.map Prod.fst).contains x.1.1

omit [DecidableEq PK] [Inhabited Msg] [Inhabited Sig] in
/-- The output distribution of the EUF-CMA game is the average over key pairs of the winning
probability of the run against the signing oracle. -/
theorem eufDist_eq (S : PSigScheme Msg PK SK Sig) (B : PK → OracleAdv Msg Sig (Msg × Sig)) :
    eufDist S B = S.keyDist.bind fun ks =>
      (OracleAdv.run (signOracle S ks.2) (B ks.1) []).map (forgeWin S ks.1) := by
  rw [eufDist, PSigScheme.keyDist, PMF.bind_map]
  rfl

/-- The flag of a forgery in a run of `Z` against the real signer, from a state with key pair
`ks`, signed pairs `signed` and no forgery, is at most the probability that the forger with
public key `ks.1`, run against the signing oracle of `ks.2` from the log of `signed`, wins. -/
theorem prFlag_keyed_le (S : PSigScheme Msg PK SK Sig)
    (Z : Strat ζ (SigEv Msg PK Sig ⊕ Unit) (SigOut PK Sig ⊕ Unit)) (ks : PK × SK) :
    ∀ (n : ℕ) (z : ζ) (signed : List (Msg × Sig)) (h : Heap),
      prTrue (SPComp.bind (loop (realSig S.toSigScheme) (fun t => t.forged) Z n
          (z, ⟨some ks, signed, false⟩, false)) fun c => SPComp.pure c.2.2) h ≤
        ((OracleAdv.run (signOracle S ks.2) (forgeReduce S Z ks.1 n z (true, signed) h)
          signed.reverse).map (forgeWin S ks.1)) true := by
  intro n
  induction n with
  | zero =>
    intro z signed h
    simp [loop, ForkingLemma.prTrue_pure_bool]
  | succ n ih =>
    intro z signed h
    simp only [loop, SPComp.bind_assoc, forgeReduce]
    refine prTrue_bind_le_runRand _ _ _ _ _ _ _ fun a h₁ => ?_
    rcases a with ⟨z₁, (_ | m | ⟨m, σ, vk⟩) | u⟩
    · simp only [realSig_step_inl, realHonStep, SPComp.map,
        SPComp.pure_bind, forgeAct, OracleAdv.bind_ret, Bool.or_false]
      refine prTrue_bind_le_runRand _ _ _ _ _ _ _ fun z₂ h₂ => ?_
      exact ih z₂ signed h₂
    · simp only [realSig_step_inl, realHonStep, SPComp.map, SPComp.pure_bind,
        SPComp.bind_assoc, forgeAct, toSigScheme_sign, ite_true, OracleAdv.bind,
        OracleAdv.run_query, Bool.or_false]
      rw [prTrue_bind_liftPMF, signOracle, PMF.bind_map, PMF.map_bind, PMF.bind_apply]
      refine ENNReal.tsum_le_tsum fun σ => ?_
      gcongr
      refine prTrue_bind_le_runRand _ _ _ _ _ _ _ fun z₂ h₂ => ?_
      have hih := ih z₂ ((m, σ) :: signed) h₂
      rwa [List.reverse_cons] at hih
    · simp only [realSig_step_inl, realHonStep, SPComp.map, SPComp.pure_bind,
        forgeAct, ite_true, Bool.false_or]
      cases hfg : isForgery S.toSigScheme ks.1 signed m σ vk
      · simp only [Bool.false_eq_true, ite_false, OracleAdv.bind_ret]
        refine prTrue_bind_le_runRand _ _ _ _ _ _ _ fun z₂ h₂ => ?_
        exact ih z₂ signed h₂
      · have hw : forgeWin S ks.1 ((m, σ), signed.reverse) = true := by
          simp [forgeWin, isForgery, PSigScheme.toSigScheme] at hfg ⊢
          grind
        simp only [ite_true, OracleAdv.bind_ret, OracleAdv.run_ret, PMF.pure_map,
          PMF.pure_apply, hw]
        simpa using prTrue_le_one _ _
    · simp only [realSig_step_inr, SPComp.map,
        SPComp.pure_bind, forgeAct, OracleAdv.bind_ret, Bool.or_false]
      refine prTrue_bind_le_runRand _ _ _ _ _ _ _ fun z₂ h₂ => ?_
      exact ih z₂ signed h₂

/-- The flag of a forgery in a run of `Z` against the real signer before key generation is at
most the probability, averaged over the key pairs of `S`, that the forger with the public key
wins against the signing oracle of the secret key. -/
theorem prFlag_unkeyed_le (S : PSigScheme Msg PK SK Sig)
    (Z : Strat ζ (SigEv Msg PK Sig ⊕ Unit) (SigOut PK Sig ⊕ Unit)) :
    ∀ (n : ℕ) (z : ζ) (h : Heap),
      prTrue (SPComp.bind (loop (realSig S.toSigScheme) (fun t => t.forged) Z n
          (z, ⟨none, [], false⟩, false)) fun c => SPComp.pure c.2.2) h ≤
        (S.keyDist.bind fun ks => (OracleAdv.run (signOracle S ks.2)
          (forgeReduce S Z ks.1 n z (false, []) h) []).map (forgeWin S ks.1)) true := by
  intro n
  induction n with
  | zero =>
    intro z h
    simp [loop, ForkingLemma.prTrue_pure_bool]
  | succ n ih =>
    intro z h
    simp only [loop, SPComp.bind_assoc, forgeReduce, OracleAdv.run_rand, PMF.map_bind]
    rw [PMF.bind_comm]
    refine prTrue_bind_le_pmf_bind _ _ _ _ fun a h₁ => ?_
    rcases a with ⟨z₁, (_ | m | ⟨m, σ, vk⟩) | u⟩
    · simp only [realSig_step_inl, realHonStep, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind, forgeAct, OracleAdv.bind_ret, Bool.or_false,
        PSigScheme.toSigScheme_keygen]
      rw [prTrue_bind_liftPMF, PMF.bind_apply]
      refine ENNReal.tsum_le_tsum fun ks => ?_
      gcongr
      refine prTrue_bind_le_runRand _ _ _ _ _ _ _ fun z₂ h₂ => ?_
      exact prFlag_keyed_le S Z ks n z₂ [] h₂
    · simp only [realSig_step_inl, realHonStep, SPComp.map, SPComp.pure_bind, forgeAct,
        Bool.false_eq_true, ite_false, OracleAdv.bind_ret, OracleAdv.run_rand, PMF.map_bind,
        Bool.or_false]
      rw [PMF.bind_comm]
      exact prTrue_bind_le_pmf_bind _ _ _ _ fun z₂ h₂ => ih z₂ h₂
    · simp only [realSig_step_inl, realHonStep, SPComp.map, SPComp.pure_bind, forgeAct,
        Bool.false_eq_true, ite_false, OracleAdv.bind_ret, OracleAdv.run_rand, PMF.map_bind,
        Bool.or_false]
      rw [PMF.bind_comm]
      exact prTrue_bind_le_pmf_bind _ _ _ _ fun z₂ h₂ => ih z₂ h₂
    · simp only [realSig_step_inr, SPComp.map, SPComp.pure_bind, forgeAct,
        OracleAdv.bind_ret, OracleAdv.run_rand, PMF.map_bind, Bool.or_false]
      rw [PMF.bind_comm]
      exact prTrue_bind_le_pmf_bind _ _ _ _ fun z₂ h₂ => ih z₂ h₂

/-- **Forgeries are bounded by the EUF-CMA advantage of the forger.** The probability that the
run of the environment `Z` against the real signing system of `S` contains a verification that
accepts, under the signer's key, a message never signed is at most the EUF-CMA advantage of the
forger `forger S Z` against `S`. -/
theorem prBad_realSig_le_eufcma (S : PSigScheme Msg PK SK Sig)
    (Z : Env (Strat ζ (SigEv Msg PK Sig ⊕ Unit) (SigOut PK Sig ⊕ Unit)) ζ) :
    prBad (realSig S.toSigScheme) (fun t => t.forged) Z ≤
      eufcmaAdvantage S.toSigScheme (toEUFAdversary (forger S Z)) := by
  rw [eufcmaAdvantage_toEUFAdversary, eufDist_eq]
  exact prFlag_unkeyed_le S Z.input _ _ _

/-- **The real signing system realizes `F_SIG` up to the EUF-CMA advantage of a forger.** For a
signature scheme `S` given by probability mass functions and consistent in relational form
(`ConsistentOn`), the signer running `S` realizes the unstoppable signature functionality
`fsig` behind the opaque simulator `fsigSim`, with bound, at the environment `Z`, the EUF-CMA
advantage of the forger `forger S Z` against `S`. -/
theorem realSig_realizesSim_fsig_eufcma [DecidableEq Sig] (S : PSigScheme Msg PK SK Sig)
    (ok : PK × SK → Prop) (hcons : ConsistentOn S.toSigScheme ok) :
    RealizesSim (realSig S.toSigScheme) fsig
      (fsigSim S.toSigScheme (liftPMF_noFail _) fun _ _ => liftPMF_noFail _)
      (fun _ Z => eufcmaAdvantage S.toSigScheme (toEUFAdversary (forger S Z))) :=
  fun ζ Z => (realSig_realizesSim_fsig S.toSigScheme _ _ ok hcons ζ Z).trans
    (prBad_realSig_le_eufcma S Z)

end Forger

end CatCrypt.Crypto.Signatures.FSigSys
