/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.CKACorrupt
public import CatCryptCore.Crypto.Assumptions.DualPRF
import CatCryptCore.Tactics.AutoDispatchExt
import CatCryptCore.Tactics.DeriveTimed

/-!
# Secure messaging with state corruption

The confidentiality game of secure messaging with state corruption for the double ratchet of
Alwen, Coretti and Dodis (EUROCRYPT 2019), over a CKA `C`, the root KDF
`R : PRGDef (RK × Key) (RK × Sa)`, the chain generator `G : PRGDef Sa (W × Sa)` and the AEAD
`D : AEADDef W Ct`, and its modular proof from the CKA game with corruption of
`CatCryptCore.Crypto.Messaging.CKACorrupt`, a PRF-PRNG root step and a forward-secure AEAD
(ACD, Sections 4 and 5).

## The game

The parties alternate epochs as in the CKA game: `A` opens the odd epochs, `B` the even ones,
and each party has an epoch counter `t_P` (the CKA game state `CKAGameSt`). The state of a party
is its CKA state, its root key, its sending chain and its receiving chain (`SMSt`). The
adversary first draws the challenge epoch `t⋆`, then receives the public value of the CKA
initialisation and asks, adaptively,

* `ratchet P` — `P` opens a new epoch: the CKA sending algorithm gives the message `T` (returned)
  and the key `I`; the root step `(rk', sa) = R (rk_P, I)` gives the next root key of `P` and the
  sending chain `sa` of the epoch; `(rk', sa)` is in transit to the peer;
* `recv P` — `P` receives the epoch in transit: the CKA receiving algorithm on `T`, and the root
  key `rk'` and the receiving chain `sa` (the values that the receiver derives with its own CKA key
  and root key, by the correctness of the CKA and of the root chain);
* `send P m` — `P`, in its own epoch, encrypts the message `m` (a plaintext and associated data,
  chosen by the adversary) under the next key of its sending chain, and the chain moves on;
* `chall P m` — as `send P m`, once, by the sender of the challenge epoch while its counter is
  `t⋆`; in the ideal game the ciphertext is uniform;
* `corrupt P` — the full state of `P` (CKA state, root key, sending and receiving chain).

The advantage `SM_Corrupt_Advantage C R G D ΔFS ΔPCS A` is the distance between the real and the
ideal game.

In the game with an adaptive challenge epoch (`smAdOracle`, `sm_adaptive_game`,
`SM_Adaptive_Advantage`) the adversary does not announce the epoch: the challenge is answered
for the sender of any epoch `e` while its counter is `e`, once, and its epoch is recorded; the
windows are decided online from the record, as below.

## The windows

The corruption of `P` is answered exactly when the CKA corruption gate `ckaAllowCorr ΔFS ΔPCS t⋆`
allows it on the epoch counters:

* `max(t_A, t_B) + ΔPCS ≤ t⋆` — both parties are at least `ΔPCS` epochs before the challenge
  epoch (post-compromise security: the epochs between the corruption and the challenge heal the
  state), or
* `t⋆ + ΔFS ≤ t_P` — `P` is at least `ΔFS` epochs past the challenge epoch (forward secrecy).

In the game with an adaptive challenge epoch the same windows are decided online: a corruption
before the challenge is answered and raises the least allowed challenge epoch to
`max(t_A, t_B) + ΔPCS`; the challenge at the epoch `e` is answered only if `e` is at least this
bound; a corruption of `P` after a challenge at `e` is answered if `e + ΔFS ≤ t_P`.

The FS-AEAD epoch structure fixes the other window: the chains of the challenge epoch are held
by its sender from its opening until the sender opens the epoch `t⋆ + 2` (counters `t⋆` and
`t⋆ + 1`), and by its receiver from the receipt until it receives the epoch `t⋆ + 2` (counters
`t⋆` and `t⋆ + 1`). With `2 ≤ ΔFS` and `1 ≤ ΔPCS` the CKA windows contain the FS-AEAD windows: a
corruption that the gate allows never reveals a chain of the challenge epoch
(`not_allowCorr_of_window`). For `dhCKA` the delays are `ΔFS = ΔPCS = 2`
(`dhCKA_corrupt_advantage_eq_ddh`).

## Comparison with ACD, Definition 13

ACD's secure-messaging game has oracles for sending and delivering messages of both parties,
with immediate decryption of messages delivered out of order, injection of ciphertexts
(authenticity), corruption of the parties' states, sending with adversarial randomness, and
left-or-right challenges on any number of messages, whose epoch the adversary chooses
adaptively; trivial attacks are excluded by safety predicates with the parameter `Δ_SM`. The
game here is the confidentiality part, restricted as follows:

* the main game announces the challenge epoch before the interaction (the tree of
  `SMCorruptAdv` is chosen after `tStar`, as in the CKA game of `CKACorrupt`); the game with an
  adaptive challenge epoch reduces to it by guessing the epoch: its advantage is at most the sum
  over the epochs `e` of the advantages of the guessing reductions `smGuessAdv ΔFS ΔPCS A e`
  (`sm_adaptive_advantage_le`), the sum over the epochs of ACD's bound; for an adversary asking
  at most `q` queries the sum runs over the epochs `e ≤ q`
  (`sm_adaptive_advantage_le_of_isQueryBound`);
* one real-or-random challenge instead of left-or-right challenges on several messages;
* in-order delivery of the CKA messages; the receiver keeps the receiving chain of the epoch it
  received, and ciphertexts are not delivered (no decryption, no injection, no authenticity);
* no sending with adversarial or leaked randomness;
* the windows are those of the CKA game on the epoch counters, given above; in ACD's terms the
  game is `Δ`-secure with the delays `ΔFS` and `ΔPCS` of the CKA.

None of these restrictions is forced by the bookkeeping of the windows: the announced epoch of
the main game lets the corruption gate be decided at the time of the corruption, as in the CKA
game, and the reduction announces the same epoch to the CKA game; the adaptive game is recovered
by the guess, and the other items restrict the functionality (no authenticity, no immediate
decryption, no bad randomness, one challenge).

## The proof

The real game, the hybrid with a uniform CKA key at the challenge epoch, the hybrid with a
uniform root output at the challenge epoch, and the ideal game:

1. the CKA hop: the reduction `smcCKARed` plays the CKA game with corruption; the CKA corruption
   answers the secure-messaging corruptions, the reduction keeps the root keys and the chains
   (`smCKA_game_eq`);
2. the root hop: the reduction `smcRootRed` asks the root step of the challenge epoch to the `prf`
   oracle of the PRF-PRNG game; the PRF-PRNG game draws its key at the start, the hybrid at the
   opening of the challenge epoch (`sm_run_eager`, `smRoot_real_eq`, `smRoot_ideal_eq`);
3. the FS-AEAD hop: the reduction `smcFSRed` holds the chains of the challenge epoch in the FS-AEAD
   game with corruption; the invariant `FSInv` of the simulation keeps them away from every
   allowed corruption (`smFS_step`, `smFS_inv`, `smFS_game_eq`);

and the hops 2 and 1 back with the uniform challenge ciphertext.

## Main definitions

* `SMQuery`, `SMAns`, `SMLoc`, `SMSt`, `smOracleOf`, `SMCorruptAdv`, `sm_corrupt_game`,
  `SM_Corrupt_Advantage` — the game with corruption
* `PPQuery`, `ppOracle`, `pp_game`, `PRFPRNG_Advantage` — the PRF-PRNG game of the root step: a
  `prng` oracle (a uniform root state, inputs of the adversary) and a `prf` oracle (a uniform
  input, root states of the adversary)
* `FSQuery`, `fsOracle`, `fsaead_corrupt_game`, `FSAEAD_Corrupt_Advantage` — the FS-AEAD game
  with corruption
* `smcCKARed`, `smcRootRed`, `smcFSRed` — the reductions, from the oracle trees `smCKATreeOf`,
  `smRootTreeOf`, `smFSTreeOf` (costed forms by `derive_timed`); `ppRedR`, `ppRedL` — the
  dual-PRF reductions of the PRF-PRNG game
* `smPassiveAdv` — the passive adversary of one message, from the tree `smPassiveTreeOf`
* `SMAdRec`, `smAdOracle`, `sm_adaptive_game`, `SM_Adaptive_Advantage` — the game with an
  adaptive challenge epoch
* `guessImplOf`, `guessTreeOf`, `smGuessAdv` — the guessing reduction

## Main results

* `sm_corrupt_advantage_le` — with `2 ≤ ΔFS`, `1 ≤ ΔPCS`, the advantage with corruption is at most
  the CKA corruption advantages of `smcCKARed`, the PRF-PRNG advantages of `smcRootRed` (both for
  the two challenge modes) and the FS-AEAD advantage of `smcFSRed`
* `sm_dh_corrupt_advantage_le` — for `dhCKA` with `ΔFS = ΔPCS = 2`, the CKA terms are DDH
  advantages of `ckaCorruptDDHRed`
* `hkdfRoot_prfprng_le` — the HKDF-shaped root step is a PRF-PRNG under the dual-PRF assumption;
  `sm_dh_hkdf_corrupt_advantage_le` — the double ratchet with `dhCKA` and `hkdfRoot` from DDH,
  the dual-PRF assumption and FS-AEAD
* `sm_advantage_le_corrupt_passive` — the passive game `sm_real`/`sm_ideal` of
  `CatCryptCore.Crypto.Messaging.DoubleRatchet` from the game with corruption: the passive
  advantage is at most the sum over the messages of the advantages of the adversaries
  `smPassiveAdv`, which never corrupt
* `sm_adaptive_advantage_le` — the game with an adaptive challenge epoch from the game with an
  announced one, by guessing the epoch (identical until the guessed epoch is excluded,
  `OracleAdv.run_map_apply_eq_of_agree`; identical until the challenge, `smAd_nochall_eq`)
* `sm_adaptive_corrupt_advantage_le`, `sm_dh_adaptive_advantage_le`,
  `sm_dh_hkdf_adaptive_advantage_le` — the adaptive game: the sum over the epochs of the CKA
  (DDH), PRF-PRNG (dual-PRF) and FS-AEAD terms
* `sm_guess_game_eq_zero_of_lt`, `sm_guess_advantage_eq_zero_of_lt` — the horizon: for an
  adversary asking at most `q` queries, the guessing reduction at an epoch `e > q` never wins,
  since the challenge is answered at the counter of a party and every query raises each counter
  by at most one (`smAdOracle_t_le_succ`, `smAd_run_cE_le`, from the graded run invariant
  `OracleAdv.run_support_level`)
* `sm_adaptive_advantage_le_of_isQueryBound`, `sm_adaptive_corrupt_advantage_le_of_isQueryBound`,
  `sm_dh_adaptive_advantage_le_of_isQueryBound`,
  `sm_dh_hkdf_adaptive_advantage_le_of_isQueryBound` — the adaptive bounds for an adversary
  asking at most `q` queries, with the finite sum over the epochs `e ≤ q`
* `smCKATreeOf.erase_timed`, `smRootTreeOf.erase_timed`, `smFSTreeOf.erase_timed`,
  `ppRedR.erase_timed`, `ppRedL.erase_timed`, `smPassiveTreeOf.erase_timed`,
  `guessTreeOf.erase_timed` — the costed reductions (`derive_timed`)

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, Sections 4 and 5
* M. Bellare, *New Proofs for NMAC and HMAC: Security without Collision-Resistance*, CRYPTO 2006
  (HMAC as a dual PRF)
* M. Backendal, M. Bellare, F. Günther, M. Scarlata, *When Messages Are Keys: Is HMAC a
  Dual-PRF?*, CRYPTO 2023
-/

set_option autoImplicit false

@[expose] public section

/-! ## Runs of oracle adversaries: state maps under an invariant, and eager sampling -/

namespace CatCrypt.Crypto.OracleAdv

open scoped ENNReal

variable {S S' D R V α : Type}

/-- **State maps under an invariant.** A map `f` of oracle states that commutes with every
oracle call from the states satisfying `Inv`, an invariant kept on the support of every call,
commutes with every run from such a state. -/
theorem run_map_state_inv (O : S → D → PMF (R × S)) (O' : S' → D → PMF (R × S'))
    (f : S → S') (Inv : S → Prop)
    (hInv : ∀ s d, Inv s → ∀ x ∈ (O s d).support, Inv x.2)
    (hO : ∀ s d, Inv s → (O s d).map (Prod.map id f) = O' (f s) d)
    (A : OracleAdv D R α) (s : S) (hs : Inv s) :
    (run O A s).map (Prod.map id f) = run O' A (f s) := by
  induction A generalizing s with
  | ret a => simp [PMF.pure_map]
  | rand p k ih =>
    simp only [run_rand, PMF.map_bind]
    congr 1; funext b; exact ih b s hs
  | query d k ih =>
    simp only [run_query, PMF.map_bind]
    rw [← hO s d hs, PMF.bind_map]
    refine PMF.bind_congr_support _ _ _ fun x hx => ?_
    exact ih x.1 x.2 (hInv s d hs x hx)

/-- The outputs of the runs related by a state map under an invariant are equal. -/
theorem run_map_fst_of_map_state_inv (O : S → D → PMF (R × S)) (O' : S' → D → PMF (R × S'))
    (f : S → S') (Inv : S → Prop)
    (hInv : ∀ s d, Inv s → ∀ x ∈ (O s d).support, Inv x.2)
    (hO : ∀ s d, Inv s → (O s d).map (Prod.map id f) = O' (f s) d)
    (A : OracleAdv D R α) (s : S) (hs : Inv s) :
    (run O A s).map Prod.fst = (run O' A (f s)).map Prod.fst := by
  rw [← run_map_state_inv O O' f Inv hInv hO A s hs, PMF.map_comp]
  rfl

/-- After the critical step, the oracle with the value `v` drawn in advance is the lazy one. -/
theorem run_eager_of_done (O : S → D → PMF (R × S)) (Ov : S → D → PMF (R × S))
    (c : S → D → Bool) (hnc : ∀ s d, c s d = false → Ov s d = O s d) (N : S → Prop)
    (h2 : ∀ s d, N s → ∀ x ∈ (O s d).support, N x.2) (h3 : ∀ s d, N s → c s d = false)
    (A : OracleAdv D R α) (s : S) (hs : N s) : run Ov A s = run O A s :=
  run_eq_run_of_inv O Ov N h2 (fun s d hs => hnc s d (h3 s d hs)) A s hs

/-- **Eager sampling of a value drawn at a critical step.** Let the oracle `O` draw, at the
critical steps `c s d`, a value from `μ` and continue as the oracle `Ov v`, and agree with
`Ov v` elsewhere. If a critical step leads to the states `N`, which every step keeps and which
admit no critical step, then drawing the value in advance does not change the run. -/
theorem run_eq_bind_eager (O : S → D → PMF (R × S)) (Ov : V → S → D → PMF (R × S))
    (μ : PMF V) (c : S → D → Bool)
    (hc : ∀ s d, c s d = true → O s d = μ.bind fun v => Ov v s d)
    (hnc : ∀ v s d, c s d = false → Ov v s d = O s d) (N : S → Prop)
    (h1 : ∀ v s d, c s d = true → ∀ x ∈ (Ov v s d).support, N x.2)
    (h2 : ∀ s d, N s → ∀ x ∈ (O s d).support, N x.2) (h3 : ∀ s d, N s → c s d = false)
    (A : OracleAdv D R α) (s : S) :
    run O A s = μ.bind fun v => run (Ov v) A s :=
  run_eq_bind_run_of_trigger μ O Ov (fun _ => True) (fun s d => c s d = true) (fun _ => N)
    (fun s d _ h => hc s d h) (fun v s d _ h => hnc v s d (by simpa using h))
    (fun _ _ _ _ _ _ => Or.inl trivial) (fun v s d _ h => h1 v s d h) (fun _ => h2)
    (fun v s d hs => hnc v s d (h3 s d hs)) A s trivial

/-- From a bad state of an oracle whose bad states are kept by every call, a run reaches no
good outcome. -/
theorem run_apply_eq_zero_of_bad (O : S → D → PMF (R × S)) (bad : S → Bool)
    (hO : ∀ s d, bad s = true → ∀ y ∈ (O s d).support, bad y.2 = true)
    (A : OracleAdv D R α) (s : S) (hs : bad s = true) (y : α × S) (hy : bad y.2 = false) :
    run O A s y = 0 := by
  induction A generalizing s with
  | ret a =>
    rw [run_ret, PMF.pure_apply]
    split
    · rename_i h; rw [h] at hy; rw [hs] at hy; exact absurd hy (by decide)
    · rfl
  | rand p k ih =>
    rw [run_rand, PMF.bind_apply]
    exact ENNReal.tsum_eq_zero.mpr fun b => by rw [ih b s hs, mul_zero]
  | query d k ih =>
    rw [run_query, PMF.bind_apply]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    by_cases hx : x ∈ (O s d).support
    · rw [ih x.1 x.2 (hO s d hs x hx), mul_zero]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hx, zero_mul]

/-- **Identical until bad, along a state map.** Let `f` map the states of `O₂` to those of `O₁`,
with the bad states corresponding, kept by both oracles, and let `O₂` keep the invariant `Inv`.
If from good states with the invariant the calls of `O₂`, mapped by `f`, and of `O₁` agree on
every good outcome, then so do the runs. -/
theorem run_map_apply_eq_of_agree {S₁ S₂ : Type} (O₁ : S₁ → D → PMF (R × S₁))
    (O₂ : S₂ → D → PMF (R × S₂)) (f : S₂ → S₁) (bad₁ : S₁ → Bool) (bad₂ : S₂ → Bool)
    (Inv : S₂ → Prop) (hb : ∀ s, bad₁ (f s) = bad₂ s)
    (h₁ : ∀ s d, bad₁ s = true → ∀ y ∈ (O₁ s d).support, bad₁ y.2 = true)
    (h₂ : ∀ s d, bad₂ s = true → ∀ y ∈ (O₂ s d).support, bad₂ y.2 = true)
    (hInv : ∀ s d, Inv s → bad₂ s = false → ∀ y ∈ (O₂ s d).support, bad₂ y.2 = false →
      Inv y.2)
    (hagree : ∀ s d, Inv s → bad₂ s = false → ∀ y, bad₁ y.2 = false →
      (O₂ s d).map (Prod.map id f) y = O₁ (f s) d y)
    (A : OracleAdv D R α) (s : S₂) (hs : Inv s) (y : α × S₁) (hy : bad₁ y.2 = false) :
    (run O₂ A s).map (Prod.map id f) y = run O₁ A (f s) y := by
  have hzero : ∀ (B : OracleAdv D R α) (t : S₂), bad₂ t = true →
      (run O₂ B t).map (Prod.map id f) y = 0 := by
    intro B t ht
    rw [PMF.map_apply]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    split
    · rename_i hxy
      refine run_apply_eq_zero_of_bad O₂ bad₂ h₂ B t ht x ?_
      rw [← hb]; rw [hxy] at hy; exact hy
    · rfl
  induction A generalizing s with
  | ret a => simp only [run_ret, PMF.pure_map, Prod.map_apply, id_eq]
  | rand p k ih =>
    rw [run_rand, run_rand, PMF.map_bind, PMF.bind_apply, PMF.bind_apply]
    exact tsum_congr fun b => by rw [ih b s hs]
  | query d k ih =>
    by_cases hbs : bad₂ s = true
    · rw [hzero _ s hbs]
      exact (run_apply_eq_zero_of_bad O₁ bad₁ h₁ _ (f s) (by rw [hb]; exact hbs) y hy).symm
    · have hbs' : bad₂ s = false := by simpa using hbs
      rw [run_query, run_query, PMF.map_bind, PMF.bind_apply, PMF.bind_apply]
      have hA : ∀ x, O₂ s d x * (run O₂ (k x.1) x.2).map (Prod.map id f) y =
          O₂ s d x * run O₁ (k x.1) (f x.2) y := by
        intro x
        by_cases hx : x ∈ (O₂ s d).support
        · by_cases hbx : bad₂ x.2 = true
          · rw [hzero _ x.2 hbx, run_apply_eq_zero_of_bad O₁ bad₁ h₁ _ (f x.2)
              (by rw [hb]; exact hbx) y hy]
          · rw [ih x.1 x.2 (hInv s d hs hbs' x hx (by simpa using hbx))]
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hx, zero_mul, zero_mul]
      rw [tsum_congr hA]
      have hB : (∑' x, O₂ s d x * run O₁ (k x.1) (f x.2) y) =
          ∑' z, (O₂ s d).map (Prod.map id f) z * run O₁ (k z.1) z.2 y := by
        rw [← PMF.bind_apply, ← PMF.bind_apply, PMF.bind_map]
        rfl
      rw [hB]
      refine tsum_congr fun z => ?_
      by_cases hz : bad₁ z.2 = true
      · rw [run_apply_eq_zero_of_bad O₁ bad₁ h₁ _ z.2 hz y hy, mul_zero, mul_zero]
      · rw [hagree s d hs hbs' z (by simpa using hz)]

/-- **A graded invariant along a run with a query bound.** Let `L c` be state predicates,
increasing in `c`, such that every oracle call from a state of `L c` leads to states of
`L (c + 1)`. A run of an adversary asking at most `n` queries from a state of `L c` ends in a
state of `L (c + n)`. -/
theorem run_support_level (O : S → D → PMF (R × S)) (L : ℕ → S → Prop)
    (hL : ∀ c s, L c s → L (c + 1) s)
    (hO : ∀ c s d, L c s → ∀ x ∈ (O s d).support, L (c + 1) x.2) {A : OracleAdv D R α}
    {n : ℕ} (hA : A.IsQueryBound n) (c : ℕ) (s : S) (hs : L c s) :
    ∀ x ∈ (run O A s).support, L (c + n) x.2 := by
  induction A generalizing n c s with
  | ret a =>
    intro x hx
    rw [run_ret, PMF.mem_support_pure_iff] at hx
    subst hx
    clear hA
    induction n with
    | zero => exact hs
    | succ n ih => exact hL _ _ ih
  | rand p k ih =>
    intro x hx
    rw [run_rand, PMF.mem_support_bind_iff] at hx
    obtain ⟨b, -, hx⟩ := hx
    exact ih b (hA b) c s hs x hx
  | query d k ih =>
    cases n with
    | zero => exact hA.elim
    | succ n =>
      intro x hx
      rw [run_query, PMF.mem_support_bind_iff] at hx
      obtain ⟨y, hy, hx⟩ := hx
      rw [show c + (n + 1) = c + 1 + n by omega]
      exact ih y.1 (hA y.1) (c + 1) y.2 (hO c s d hs y hy) x hx

end CatCrypt.Crypto.OracleAdv

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
  CatCrypt.Crypto.PRPPRF CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

/-! ## The CKA game as a probability mass function -/

section CKAPMF

variable {St Msg Key Rand : Type}

/-- The oracle of the CKA corruption game of `C` as a probability mass function: the sending
algorithm draws its randomness and runs `CKACoins.sendR`. -/
noncomputable def ckaOracleP (C : CKADef St Msg Key) [CKACoins C Rand] [Fintype Key]
    [Nonempty Key] [Fintype Rand] [Nonempty Rand] (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s : CKAGameSt St Msg) : CKAQuery → PMF (CKAAns St Msg Key Rand × CKAGameSt St Msg)
  | .send p =>
    if s.canSend p then
      (PMF.uniformFintype Rand).bind fun r =>
        PMF.pure (.out (CKACoins.sendR (C := C) (s.st p) r).2.1
          (CKACoins.sendR (C := C) (s.st p) r).2.2,
          s.sent p (CKACoins.sendR (C := C) (s.st p) r).1
            (CKACoins.sendR (C := C) (s.st p) r).2.1)
    else PMF.pure (.none, s)
  | .recv p =>
    PMF.pure (if s.canRecv p then (.none, s.recvd p (C.recv (s.st p) s.msg).1) else (.none, s))
  | .chall p =>
    if s.canSend p && s.t p + 1 == t then
      (PMF.uniformFintype Rand).bind fun r =>
        (if ideal then PMF.uniformFintype Key
          else PMF.pure (CKACoins.sendR (C := C) (s.st p) r).2.2).bind fun k =>
          PMF.pure (.out (CKACoins.sendR (C := C) (s.st p) r).2.1 k,
            s.sent p (CKACoins.sendR (C := C) (s.st p) r).1
              (CKACoins.sendR (C := C) (s.st p) r).2.1)
    else PMF.pure (.none, s)
  | .corrupt p =>
    PMF.pure (if ckaAllowCorr ΔFS ΔPCS t s p then .state (s.st p) else .none, s)
  | .sendLeak p =>
    if ckaAllowLeak ΔPCS t s p then
      (PMF.uniformFintype Rand).bind fun r =>
        PMF.pure (.leak (CKACoins.sendR (C := C) (s.st p) r).2.1
          (CKACoins.sendR (C := C) (s.st p) r).2.2 r,
          s.sent p (CKACoins.sendR (C := C) (s.st p) r).1
            (CKACoins.sendR (C := C) (s.st p) r).2.1)
    else PMF.pure (.none, s)

/-- Under the soundness of the explicit-randomness sending algorithm, each oracle computation
of the CKA game is the lifted distribution `ckaOracleP`. -/
theorem ckaCorruptOracle_eq_liftPMF (C : CKADef St Msg Key) [CKACoins C Rand] [Fintype Key]
    [Nonempty Key] [Fintype Rand] [Nonempty Rand] (hS : CKACoins.Sound C) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool) (s : CKAGameSt St Msg) (q : CKAQuery) :
    ckaCorruptOracle C ΔFS ΔPCS t ideal s q = liftPMF (ckaOracleP C ΔFS ΔPCS t ideal s q) := by
  cases q with
  | send p =>
    simp only [ckaCorruptOracle, ckaOracleP]
    split
    · rw [hS]
      simp only [sample_eq_liftPMF, liftPMF_pure,
        liftPMF_bind_liftPMF, PMF.bind_bind, PMF.pure_bind]
    · exact liftPMF_pure _
  | recv p => exact liftPMF_pure _
  | chall p =>
    simp only [ckaCorruptOracle, ckaOracleP]
    split
    · rw [hS]
      cases ideal
      · simp only [sample_eq_liftPMF, liftPMF_pure,
          liftPMF_bind_liftPMF, Bool.false_eq_true, ite_false, PMF.bind_bind, PMF.pure_bind]
      · simp only [sample_eq_liftPMF, liftPMF_pure,
          liftPMF_bind_liftPMF, ite_true, PMF.bind_bind, PMF.pure_bind]
    · exact liftPMF_pure _
  | corrupt p => exact liftPMF_pure _
  | sendLeak p =>
    simp only [ckaCorruptOracle, ckaOracleP]
    split
    · simp only [sample_eq_liftPMF, liftPMF_pure, liftPMF_bind_liftPMF]
    · exact liftPMF_pure _

/-- **The CKA corruption game as a lifted distribution.** With an initialisation that is the
lift of `initP` and a sound explicit-randomness sending algorithm, the game is the lift of the
distribution that draws the challenge epoch and the initialisation and runs the adversary
against `ckaOracleP`. -/
theorem cka_corrupt_game_eq_liftPMF (C : CKADef St Msg Key) [CKACoins C Rand] [Fintype Key]
    [Nonempty Key] [Fintype Rand] [Nonempty Rand] (hS : CKACoins.Sound C)
    (initP : PMF (Msg × St × St)) (hinit : C.init = liftPMF initP) (ΔFS ΔPCS : ℕ)
    (ideal : Bool) {α : Type} (A : CKACorruptAdv St Msg Key Rand α) :
    cka_corrupt_game C ΔFS ΔPCS ideal A =
      liftPMF (A.tStar.bind fun t => initP.bind fun i =>
        (OracleAdv.run (ckaOracleP C ΔFS ΔPCS t ideal) (A.play t i.1)
          (CKAGameSt.init i.1 i.2.1 i.2.2)).map Prod.fst) := by
  unfold cka_corrupt_game
  simp only [hinit, OracleAdv.runSP_eq_liftPMF _ _ (ckaCorruptOracle_eq_liftPMF C hS ΔFS ΔPCS _
    ideal), liftPMF_bind_pure, liftPMF_bind_liftPMF]

end CKAPMF

/-! ## The secure-messaging game with state corruption -/

/-- The queries of the secure-messaging adversary. -/
inductive SMQuery (W : Type) where
  /-- The party opens a new epoch: it runs the CKA sending algorithm and the root step. -/
  | ratchet (p : CKAParty)
  /-- The party receives the CKA message of the epoch opened by its peer. -/
  | recv (p : CKAParty)
  /-- The party encrypts the message `m` (a plaintext and associated data) in its epoch. -/
  | send (p : CKAParty) (m : W × W)
  /-- As `send`, in the challenge epoch, with a uniform ciphertext in the ideal game. -/
  | chall (p : CKAParty) (m : W × W)
  /-- The full state of the party is returned, if the corruption gate allows it. -/
  | corrupt (p : CKAParty)

/-- The answers of the secure-messaging oracles. -/
inductive SMAns (Sc Msg RK Sa Ct : Type) where
  /-- A refused query, or a receive. -/
  | none
  /-- The CKA message of a new epoch. -/
  | msg (T : Msg)
  /-- A ciphertext. -/
  | ct (c : Ct)
  /-- The state of a corrupted party: CKA state, root key, sending and receiving chain. -/
  | state (γ : Sc) (rk : RK) (snd rcv : Option Sa)

/-- The part of the secure-messaging state outside the CKA: the root keys and the chain states
of the parties, the root output of the last opened epoch, in transit to the receiver, and
whether the challenge has been asked. -/
structure SMLoc (RK Sa : Type) where
  /-- The root keys of the parties. -/
  rk : CKAParty → RK
  /-- The sending chain states (FS-AEAD sender states) of the parties. -/
  snd : CKAParty → Option Sa
  /-- The receiving chain states (FS-AEAD receiver states) of the parties. -/
  rcv : CKAParty → Option Sa
  /-- The root output of the last opened epoch. -/
  out : Option (RK × Sa)
  /-- The challenge has been asked. -/
  done : Bool

namespace SMLoc

variable {RK Sa : Type}

/-- The initial state: both root keys are `rk`, no chains, nothing in transit. -/
def init (rk : RK) : SMLoc RK Sa := ⟨fun _ => rk, fun _ => none, fun _ => none, none, false⟩

/-- Party `p` opened an epoch with root output `y`: the next root key `y.1`, the sending chain
`y.2`, and `y` in transit. -/
def opened (l : SMLoc RK Sa) (p : CKAParty) (y : RK × Sa) : SMLoc RK Sa :=
  { l with rk := Function.update l.rk p y.1, snd := Function.update l.snd p (some y.2),
           out := some y }

/-- Party `p` received the root output `y`: it takes over the root key and the chain. -/
def recvY (l : SMLoc RK Sa) (p : CKAParty) (y : RK × Sa) : SMLoc RK Sa :=
  { l with rk := Function.update l.rk p y.1, rcv := Function.update l.rcv p (some y.2) }

/-- Party `p` received the epoch in transit: it takes over the root key and the chain. -/
def received (l : SMLoc RK Sa) (p : CKAParty) : SMLoc RK Sa :=
  match l.out with
  | some y => l.recvY p y
  | none => l

/-- The sending chain of party `p` moved to the state `sa`. -/
def advanced (l : SMLoc RK Sa) (p : CKAParty) (sa : Sa) : SMLoc RK Sa :=
  { l with snd := Function.update l.snd p (some sa) }

end SMLoc

/-- The state of the secure-messaging game: the CKA game state (party states, epoch counters,
CKA message in transit) and the rest. -/
structure SMSt (Sc Msg RK Sa : Type) where
  /-- The CKA part. -/
  ck : CKAGameSt Sc Msg
  /-- The root keys, chains, root output in transit and challenge flag. -/
  loc : SMLoc RK Sa

section Game

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- The challenge of party `p` is allowed in the local state `l` at the counter `e` of `p`. -/
def challOk (l : SMLoc RK Sa) (t e : ℕ) (p : CKAParty) : Bool :=
  !l.done && (ckaSender e == p) && (e == t)

/-- The distribution of the challenge ciphertext under the key `k`: the encryption of `m`, or a
uniform ciphertext in the ideal game. -/
noncomputable def challCt (D : AEADDef W Ct) (ideal : Bool) (k : W) (m : W × W) : PMF Ct :=
  if ideal then PMF.uniformFintype Ct else PMF.pure (D.encrypt k m.1 m.2)

/-- The oracle of the secure-messaging game with the challenge epoch `t`, the challenge mode
`ideal` and the root step `root` at the opening of epoch `t`; every other epoch uses the root
KDF `R`. The real game has `root rk I = pure (R (rk, I))`; the other choices are hybrids. -/
noncomputable def smOracleOf (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) (s : SMSt Sc Msg RK Sa) :
    SMQuery W → PMF (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa)
  | .ratchet p =>
    if s.ck.canSend p then
      (PMF.uniformFintype Rand).bind fun r =>
        (if s.ck.t p + 1 == t then root (s.loc.rk p) (CKACoins.sendR (C := C) (s.ck.st p) r).2.2
          else PMF.pure (R.stretch (s.loc.rk p, (CKACoins.sendR (C := C) (s.ck.st p) r).2.2))).bind
          fun y => PMF.pure (.msg (CKACoins.sendR (C := C) (s.ck.st p) r).2.1,
            ⟨s.ck.sent p (CKACoins.sendR (C := C) (s.ck.st p) r).1
              (CKACoins.sendR (C := C) (s.ck.st p) r).2.1, s.loc.opened p y⟩)
    else PMF.pure (.none, s)
  | .recv p =>
    if s.ck.canRecv p then
      PMF.pure (.none, ⟨s.ck.recvd p (C.recv (s.ck.st p) s.ck.msg).1, s.loc.received p⟩)
    else PMF.pure (.none, s)
  | .send p m =>
    match s.loc.snd p with
    | some sa =>
      if ckaSender (s.ck.t p) == p then
        PMF.pure (.ct (D.encrypt (G.stretch sa).1 m.1 m.2), ⟨s.ck, s.loc.advanced p (G.stretch sa).2⟩)
      else PMF.pure (.none, s)
    | none => PMF.pure (.none, s)
  | .chall p m =>
    match s.loc.snd p with
    | some sa =>
      if challOk s.loc t (s.ck.t p) p then
        (challCt D ideal (G.stretch sa).1 m).bind fun c =>
          PMF.pure (.ct c, ⟨s.ck, { s.loc.advanced p (G.stretch sa).2 with done := true }⟩)
      else PMF.pure (.none, s)
    | none => PMF.pure (.none, s)
  | .corrupt p =>
    PMF.pure (if ckaAllowCorr ΔFS ΔPCS t s.ck p then
      .state (s.ck.st p) (s.loc.rk p) (s.loc.snd p) (s.loc.rcv p) else .none, s)

/-- The root step of the real game: the root KDF. -/
noncomputable def realRoot (R : PRGDef (RK × Key) (RK × Sa)) (rk : RK) (I : Key) :
    PMF (RK × Sa) :=
  PMF.pure (R.stretch (rk, I))

/-- The initial state of the game from the CKA initialisation `i` and the root key `rk`. -/
def smInit (i : Msg × Sc × Sc) (rk : RK) : SMSt Sc Msg RK Sa :=
  ⟨CKAGameSt.init i.1 i.2.1 i.2.2, SMLoc.init rk⟩

end Game

/-- A secure-messaging adversary: a distribution `tStar` of the challenge epoch, and for each
challenge epoch and public value of the CKA initialisation an oracle tree. -/
structure SMCorruptAdv (Sc Msg RK Sa W Ct : Type) : Type 1 where
  /-- The choice of the challenge epoch. -/
  tStar : PMF ℕ
  /-- The interaction with the oracles. -/
  play : ℕ → Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool

section Game

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK]

/-- The secure-messaging game with the root step `root` at the challenge epoch: the adversary
chooses the challenge epoch `t`, the CKA is initialised, both parties get a uniform root key,
and the adversary interacts with the oracle. -/
noncomputable def sm_corrupt_gameOf (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa))
    (A : SMCorruptAdv Sc Msg RK Sa W Ct) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t =>
    SPComp.bind C.init fun i =>
      SPComp.bind (SPComp.sample RK) fun rk =>
        liftPMF ((OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal root) (A.play t i.1)
          (smInit i rk)).map Prod.fst)

/-- The secure-messaging game with state corruption; `ideal` selects the uniform challenge
ciphertext. -/
noncomputable def sm_corrupt_game (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct) : SPComp Bool :=
  sm_corrupt_gameOf C R G D ΔFS ΔPCS ideal (realRoot R) A

/-- **Secure-messaging advantage with state corruption** of the adversary `A`. -/
noncomputable def SM_Corrupt_Advantage (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (A : SMCorruptAdv Sc Msg RK Sa W Ct) : ℝ≥0∞ :=
  Advantage (sm_corrupt_game C R G D ΔFS ΔPCS false A) (sm_corrupt_game C R G D ΔFS ΔPCS true A)

end Game

/-! ## The structure of the game: monotone counters and the opening of the challenge epoch -/

section Structure

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- The opening of the challenge epoch `t`: a new epoch by a party that may send, whose counter
is one before `t`. -/
def smCrit (t : ℕ) (s : SMSt Sc Msg RK Sa) : SMQuery W → Bool
  | .ratchet p => s.ck.canSend p && (s.ck.t p + 1 == t)
  | _ => false

/-- The challenge epoch `t` has been opened: a counter has reached `t`. -/
def smOpened (t : ℕ) (s : SMSt Sc Msg RK Sa) : Prop := t ≤ s.ck.t .A ∨ t ≤ s.ck.t .B

/-- **Monotone counters.** Every oracle call leaves every epoch counter at least as large. -/
theorem smOracleOf_t_mono (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) (s : SMSt Sc Msg RK Sa)
    (q : SMQuery W) (x) (hx : x ∈ (smOracleOf C R G D ΔFS ΔPCS t ideal root s q).support)
    (P : CKAParty) : s.ck.t P ≤ x.2.ck.t P := by
  cases q with
  | ratchet p =>
    simp only [smOracleOf] at hx
    split at hx
    · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
        at hx
      obtain ⟨r, -, y, -, rfl⟩ := hx
      exact CKAGameSt.le_sent _ _ _ _ _
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
  | recv p =>
    simp only [smOracleOf] at hx
    split at hx <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hx <;> rw [hx]
    exact CKAGameSt.le_recvd _ _ _ _
  | send p m =>
    simp only [smOracleOf] at hx
    split at hx
    · split at hx <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hx <;> rw [hx]
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
  | chall p m =>
    simp only [smOracleOf] at hx
    split at hx
    · split at hx
      · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
          at hx
        obtain ⟨c, -, rfl⟩ := hx
        exact le_refl _
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
        rw [hx]
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
  | corrupt p =>
    simp only [smOracleOf, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]

/-- The opening of the challenge epoch leads to an opened state. -/
theorem smOracleOf_opened_of_crit (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) (s : SMSt Sc Msg RK Sa)
    (q : SMQuery W) (hc : smCrit t s q = true) (x)
    (hx : x ∈ (smOracleOf C R G D ΔFS ΔPCS t ideal root s q).support) : smOpened t x.2 := by
  cases q with
  | ratchet p =>
    simp only [smCrit, Bool.and_eq_true, beq_iff_eq] at hc
    simp only [smOracleOf, hc.1, ite_true] at hx
    simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨r, -, y, -, rfl⟩ := hx
    cases p
    · exact Or.inl (by simp [CKAGameSt.sent_t, hc.2])
    · exact Or.inr (by simp [CKAGameSt.sent_t, hc.2])
  | _ => simp [smCrit] at hc

/-- An opened state stays opened. -/
theorem smOracleOf_opened (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) (s : SMSt Sc Msg RK Sa)
    (q : SMQuery W) (hs : smOpened t s) (x)
    (hx : x ∈ (smOracleOf C R G D ΔFS ΔPCS t ideal root s q).support) : smOpened t x.2 := by
  rcases hs with h | h
  · exact Or.inl (h.trans (smOracleOf_t_mono C R G D ΔFS ΔPCS t ideal root s q x hx .A))
  · exact Or.inr (h.trans (smOracleOf_t_mono C R G D ΔFS ΔPCS t ideal root s q x hx .B))

omit [SampleableType W] in
/-- An opened state admits no opening of the challenge epoch. -/
theorem smCrit_of_opened (t : ℕ) (s : SMSt Sc Msg RK Sa) (hs : smOpened t s) (q : SMQuery W) :
    smCrit t s q = false := by
  cases q with
  | ratchet p =>
    simp only [smCrit, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    by_cases hc : s.ck.canSend p = true
    · right
      simp only [CKAGameSt.canSend, Bool.and_eq_true, beq_iff_eq] at hc
      have := hc.1
      cases p <;> rcases hs with h | h <;> omega
    · left; simpa using hc
  | _ => rfl

/-- Away from the opening of the challenge epoch, the oracle does not depend on the root step
at the challenge epoch. -/
theorem smOracleOf_root_congr (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root root' : RK → Key → PMF (RK × Sa))
    (s : SMSt Sc Msg RK Sa) (q : SMQuery W) (hc : smCrit t s q = false) :
    smOracleOf C R G D ΔFS ΔPCS t ideal root s q = smOracleOf C R G D ΔFS ΔPCS t ideal root' s q := by
  cases q with
  | ratchet p =>
    simp only [smCrit, Bool.and_eq_false_iff] at hc
    simp only [smOracleOf]
    rcases hc with h | h
    · simp [h]
    · simp [h]
  | _ => rfl

/-- **Eager sampling of the root step at the challenge epoch.** If the root step at the challenge
epoch draws `v` from `μ` and continues as `rootv v`, the run equals the run with `v` drawn in
advance. -/
theorem sm_run_eager (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) {V : Type} (μ : PMF V) (root : RK → Key → PMF (RK × Sa))
    (rootv : V → RK → Key → PMF (RK × Sa))
    (hroot : ∀ rk I, root rk I = μ.bind fun v => rootv v rk I) {α : Type}
    (A : OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) α) (s : SMSt Sc Msg RK Sa) :
    OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal root) A s =
      μ.bind fun v => OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal (rootv v)) A s := by
  refine OracleAdv.run_eq_bind_eager _ _ μ (smCrit t) ?_ ?_ (smOpened t) ?_ ?_ ?_ A s
  · intro s q hc
    cases q with
    | ratchet p =>
      simp only [smCrit, Bool.and_eq_true] at hc
      simp only [smOracleOf, hc.1, hc.2, ite_true, hroot, PMF.bind_bind]
      exact PMF.bind_comm _ _ _
    | _ => simp [smCrit] at hc
  · intro v s q hc
    exact smOracleOf_root_congr C R G D ΔFS ΔPCS t ideal _ _ s q hc
  · intro v s q hc x hx
    exact smOracleOf_opened_of_crit C R G D ΔFS ΔPCS t ideal _ s q hc x hx
  · intro s q hs x hx
    exact smOracleOf_opened C R G D ΔFS ΔPCS t ideal _ s q hs x hx
  · intro s q hs
    exact smCrit_of_opened t s hs q

end Structure

/-! ## PRF-PRNGs -/

section PRFPRNG

variable {RK Key Out : Type}

/-- The queries of the PRF-PRNG adversary. -/
inductive PPQuery (RK Key : Type) where
  /-- The root step on the hidden root state and the input `I` of the adversary. -/
  | prng (I : Key)
  /-- The root step on the root state `rk` of the adversary and the hidden input. -/
  | prf (rk : RK)

/-- The state of the PRF-PRNG game: the hidden root state, the hidden input, and the tables of
the two random functions of the ideal game. -/
structure PPSt (RK Key Out : Type) where
  /-- The hidden root state. -/
  rk : RK
  /-- The hidden input. -/
  key : Key
  /-- The table of the random function of the inputs. -/
  tL : List (Key × Out)
  /-- The table of the random function of the root states. -/
  tR : List (RK × Out)

variable [Fintype Out] [Nonempty Out] [DecidableEq RK] [DecidableEq Key]

/-- The oracle of the PRF-PRNG game of the root step `F`: `prng I` is `F rk I` on the hidden
root state `rk` (a lazily sampled random function of `I` if `idealL`), `prf rk'` is `F rk' I`
on the hidden input `I` (a lazily sampled random function of `rk'` if `idealR`). -/
noncomputable def ppOracle (F : RK → Key → Out) (idealL idealR : Bool) (s : PPSt RK Key Out) :
    PPQuery RK Key → PMF (Out × PPSt RK Key Out)
  | .prng I =>
    if idealL then (rfOracle s.tL I).map fun x => (x.1, { s with tL := x.2 })
    else PMF.pure (F s.rk I, s)
  | .prf rk =>
    if idealR then (rfOracle s.tR rk).map fun x => (x.1, { s with tR := x.2 })
    else PMF.pure (F rk s.key, s)

variable [Fintype RK] [Nonempty RK] [Fintype Key] [Nonempty Key]

/-- The PRF-PRNG game: a uniform hidden root state and a uniform hidden input, and the run of
the adversary against `ppOracle`. -/
noncomputable def pp_game (F : RK → Key → Out) (idealL idealR : Bool)
    (A : OracleAdv (PPQuery RK Key) Out Bool) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype RK).bind fun rk => (PMF.uniformFintype Key).bind fun k =>
    (OracleAdv.run (ppOracle F idealL idealR) A ⟨rk, k, [], []⟩).map Prod.fst)

/-- The root step of the root KDF `R` as a function of the root state and the input. -/
def rootFn (R : PRGDef (RK × Key) Out) (rk : RK) (I : Key) : Out := R.stretch (rk, I)

/-- **PRF-PRNG advantage** of the root KDF `R` (Alwen, Coretti and Dodis, §4.2): the distance
between the real game and the game in which both oracles are random functions. The `prng`
oracle is the PRNG property with adversarial inputs (a uniform root state gives pseudorandom
outputs whatever the inputs), the `prf` oracle the PRF property (a uniform input gives
pseudorandom outputs whatever the root state). -/
noncomputable def PRFPRNG_Advantage (R : PRGDef (RK × Key) Out)
    (A : OracleAdv (PPQuery RK Key) Out Bool) : ℝ≥0∞ :=
  Advantage (pp_game (rootFn R) false false A) (pp_game (rootFn R) true true A)

/-- The simulator of the right dual-PRF reduction with the root state `rk`: `prng` queries are
answered with `F rk`, `prf` queries are forwarded. -/
noncomputable def ppImplR (F : RK → Key → Out) (rk : RK) (u : Unit) (q : PPQuery RK Key) :
    OracleAdv RK Out (Out × Unit) :=
  match q with
  | .prng I => .ret (F rk I, u)
  | .prf r => .query r fun y => .ret (y, u)

/-- **The right dual-PRF reduction** of the PRF-PRNG game: a uniform root state, the `prng`
oracle computed with it, the `prf` oracle forwarded to the dual-PRF game keyed by the input. -/
noncomputable def ppRedR (F : RK → Key → Out) (A : OracleAdv (PPQuery RK Key) Out Bool) :
    OracleAdv RK Out Bool :=
  .rand (PMF.uniformFintype RK) fun rk =>
    (OracleAdv.simulate (ppImplR F rk) A ()).bind fun r => .ret r.1

/-- The simulator of the left dual-PRF reduction, with the table of a random function of the
root states: `prng` queries are forwarded, `prf` queries are answered by the table. -/
noncomputable def ppImplL (σ : List (RK × Out)) (q : PPQuery RK Key) :
    OracleAdv Key Out (Out × List (RK × Out)) :=
  match q with
  | .prng I => .query I fun y => .ret (y, σ)
  | .prf r =>
    match List.lookup r σ with
    | some y => .ret (y, σ)
    | none => .rand (PMF.uniformFintype Out) fun y => .ret (y, (r, y) :: σ)

/-- **The left dual-PRF reduction** of the PRF-PRNG game: the `prng` oracle forwarded to the
dual-PRF game keyed by the root state, the `prf` oracle a lazily sampled random function. -/
noncomputable def ppRedL (A : OracleAdv (PPQuery RK Key) Out Bool) : OracleAdv Key Out Bool :=
  (OracleAdv.simulate (ppImplL (Key := Key)) A []).bind fun r => .ret r.1

derive_timed ppRedR

derive_timed ppRedL

/-- The real PRF-PRNG game is the real right dual-PRF game of `ppRedR`. -/
theorem pp_real_eq (F : RK → Key → Out) (A : OracleAdv (PPQuery RK Key) Out Bool) :
    pp_game F false false A = realGame (Function.swap F) (ppRedR F A) := by
  unfold pp_game realGame ppRedR
  congr 1
  simp only [OracleAdv.run_rand, PMF.map_bind]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun k => congrArg _ (funext fun rk => ?_))
  rw [OracleAdv.run_simulate_fst]
  refine (OracleAdv.run_map_fst_of_map_state_inv _ _ (fun _ => (⟨rk, k, [], []⟩ : PPSt RK Key Out))
    (fun _ => True) (fun _ _ _ _ _ => trivial) ?_ A ((), ()) trivial).symm
  intro x q _
  cases q with
  | prng I => simp [OracleAdv.simOracle, ppImplR, ppOracle, PMF.pure_map]
  | prf r => simp [OracleAdv.simOracle, ppImplR, ppOracle, keyedOracle, PMF.pure_map]

/-- The PRF-PRNG game with a random function for `prf` is the ideal right dual-PRF game of
`ppRedR`. -/
theorem pp_mid_eq_rf (F : RK → Key → Out) (A : OracleAdv (PPQuery RK Key) Out Bool) :
    pp_game F false true A = rfGame (ppRedR F A) := by
  unfold pp_game rfGame ppRedR
  congr 1
  simp only [OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun rk => ?_)
  rw [OracleAdv.run_simulate_fst]
  have h : ∀ k : Key, (OracleAdv.run (ppOracle F false true) A ⟨rk, k, [], []⟩).map Prod.fst =
      (OracleAdv.run (OracleAdv.simOracle (ppImplR F rk) rfOracle) A ((), [])).map Prod.fst := by
    intro k
    refine (OracleAdv.run_map_fst_of_map_state_inv _ _ (fun x => (⟨rk, k, [], x.2⟩ : PPSt RK Key Out))
      (fun _ => True) (fun _ _ _ _ _ => trivial) ?_ A ((), []) trivial).symm
    intro x q _
    cases q with
    | prng I => simp [OracleAdv.simOracle, ppImplR, ppOracle, PMF.pure_map]
    | prf r => simp [OracleAdv.simOracle, ppImplR, ppOracle, PMF.map, Function.comp_def]
  simp only [h, PMF.bind_const]

/-- The PRF-PRNG game with a random function for `prf` is the real left dual-PRF game of
`ppRedL`. -/
theorem pp_mid_eq_real (F : RK → Key → Out) (A : OracleAdv (PPQuery RK Key) Out Bool) :
    pp_game F false true A = realGame F (ppRedL (Key := Key) A) := by
  unfold pp_game realGame ppRedL
  congr 1
  refine congrArg _ (funext fun rk => ?_)
  rw [OracleAdv.run_simulate_fst]
  have h : ∀ k : Key, (OracleAdv.run (ppOracle F false true) A ⟨rk, k, [], []⟩).map Prod.fst =
      (OracleAdv.run (OracleAdv.simOracle ppImplL (keyedOracle F rk)) A ([], ())).map
        Prod.fst := by
    intro k
    refine (OracleAdv.run_map_fst_of_map_state_inv _ _ (fun x => (⟨rk, k, [], x.1⟩ : PPSt RK Key Out))
      (fun _ => True) (fun _ _ _ _ _ => trivial) ?_ A ([], ()) trivial).symm
    intro x q _
    cases q with
    | prng I => simp [OracleAdv.simOracle, ppImplL, ppOracle, keyedOracle, PMF.pure_map]
    | prf r =>
      simp only [OracleAdv.simOracle, ppImplL, ppOracle, rfOracle, ite_true]
      cases List.lookup r x.1 <;>
        simp [PMF.map, Function.comp_def]
  simp only [h, PMF.bind_const]

/-- The ideal PRF-PRNG game is the ideal left dual-PRF game of `ppRedL`. -/
theorem pp_ideal_eq_rf (F : RK → Key → Out) (A : OracleAdv (PPQuery RK Key) Out Bool) :
    pp_game F true true A = rfGame (ppRedL (Key := Key) A) := by
  unfold pp_game rfGame ppRedL
  congr 1
  rw [OracleAdv.run_simulate_fst]
  have h : ∀ (rk : RK) (k : Key),
      (OracleAdv.run (ppOracle F true true) A ⟨rk, k, [], []⟩).map Prod.fst =
      (OracleAdv.run (OracleAdv.simOracle ppImplL rfOracle) A ([], [])).map Prod.fst := by
    intro rk k
    refine (OracleAdv.run_map_fst_of_map_state_inv _ _ (fun x => (⟨rk, k, x.2, x.1⟩ : PPSt RK Key Out))
      (fun _ => True) (fun _ _ _ _ _ => trivial) ?_ A ([], []) trivial).symm
    intro x q _
    cases q with
    | prng I => simp [OracleAdv.simOracle, ppImplL, ppOracle, PMF.map, Function.comp_def]
    | prf r =>
      simp only [OracleAdv.simOracle, ppImplL, ppOracle, rfOracle, ite_true]
      cases List.lookup r x.1 <;>
        simp [PMF.map, Function.comp_def]
  simp only [h, PMF.bind_const]

/-- **The HKDF-shaped root step is a PRF-PRNG under the dual-PRF assumption.** For every
adversary `A`, the PRF-PRNG advantage of `hkdfRoot F` is at most the dual-PRF advantage of `F`
keyed by its right argument at `ppRedR F A` plus the dual-PRF advantage keyed by its left
argument at `ppRedL A`. -/
theorem hkdfRoot_prfprng_le (F : RK → Key → Out) (A : OracleAdv (PPQuery RK Key) Out Bool) :
    PRFPRNG_Advantage (hkdfRoot F) A ≤
      DualPRF_Right_Advantage F (ppRedR F A) + DualPRF_Left_Advantage F (ppRedL (Key := Key) A) := by
  have hF : rootFn (hkdfRoot F) = F := funext fun _ => funext fun _ => rfl
  unfold PRFPRNG_Advantage DualPRF_Right_Advantage DualPRF_Left_Advantage PRF_q_Advantage
  rw [hF, ← pp_real_eq, ← pp_mid_eq_rf, ← pp_mid_eq_real, ← pp_ideal_eq_rf]
  exact advantage_triangle _ _ _

end PRFPRNG

/-! ## The CKA reduction -/

section CKARed

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK]

/-- The opening of an epoch by party `p` in the CKA simulator: a CKA send, or the CKA challenge
at the epoch `t`, followed by the root step on the returned key. -/
noncomputable def smCKARatchet (R : PRGDef (RK × Key) (RK × Sa)) (t : ℕ)
    (σ : SMLoc RK Sa × CKAGameSt Unit Unit) (p : CKAParty) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (SMAns Sc Msg RK Sa Ct × (SMLoc RK Sa × CKAGameSt Unit Unit)) :=
  if σ.2.canSend p then
    if σ.2.t p + 1 == t then
      .query (.chall p) fun a =>
        match a with
        | .out T I => .ret (.msg T, (σ.1.opened p (R.stretch (σ.1.rk p, I)), σ.2.sent p () ()))
        | .none => .ret (.none, σ)
        | .state _ => .ret (.none, σ)
        | .leak _ _ _ => .ret (.none, σ)
    else
      .query (.send p) fun a =>
        match a with
        | .out T I => .ret (.msg T, (σ.1.opened p (R.stretch (σ.1.rk p, I)), σ.2.sent p () ()))
        | .none => .ret (.none, σ)
        | .state _ => .ret (.none, σ)
        | .leak _ _ _ => .ret (.none, σ)
  else .ret (.none, σ)

/-- The receive of party `p` in the CKA simulator: a CKA receive. -/
noncomputable def smCKARecvT (σ : SMLoc RK Sa × CKAGameSt Unit Unit) (p : CKAParty) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (SMAns Sc Msg RK Sa Ct × (SMLoc RK Sa × CKAGameSt Unit Unit)) :=
  if σ.2.canRecv p then
    .query (.recv p) fun _ =>
      match σ.1.out with
      | some y => .ret (.none, (σ.1.recvY p y, σ.2.recvd p ()))
      | none => .ret (.none, (σ.1, σ.2.recvd p ()))
  else .ret (.none, σ)

/-- The send of party `p` in the CKA simulator, computed locally: the encryption of `m` under
the next key of the sending chain, if `p` sends in its epoch. -/
noncomputable def smCKASendT (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (σ : SMLoc RK Sa × CKAGameSt Unit Unit) (p : CKAParty) (m : W × W) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (SMAns Sc Msg RK Sa Ct × (SMLoc RK Sa × CKAGameSt Unit Unit)) :=
  match σ.1.snd p with
  | some sa =>
    if ckaSender (σ.2.t p) == p then
      .ret (.ct (D.encrypt (G.stretch sa).1 m.1 m.2), (σ.1.advanced p (G.stretch sa).2, σ.2))
    else .ret (.none, σ)
  | none => .ret (.none, σ)

/-- The challenge of party `p` in the CKA simulator, computed locally. -/
noncomputable def smCKAChallT (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (t : ℕ)
    (ideal : Bool) (σ : SMLoc RK Sa × CKAGameSt Unit Unit) (p : CKAParty) (m : W × W) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (SMAns Sc Msg RK Sa Ct × (SMLoc RK Sa × CKAGameSt Unit Unit)) :=
  match σ.1.snd p with
  | some sa =>
    if challOk σ.1 t (σ.2.t p) p then
      .rand (challCt D ideal (G.stretch sa).1 m) fun c =>
        .ret (.ct c, ({ σ.1.advanced p (G.stretch sa).2 with done := true }, σ.2))
    else .ret (.none, σ)
  | none => .ret (.none, σ)

/-- The corruption of party `p` in the CKA simulator: a CKA corruption, to which the root key
and the chains are added. -/
noncomputable def smCKACorrT (σ : SMLoc RK Sa × CKAGameSt Unit Unit) (p : CKAParty) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (SMAns Sc Msg RK Sa Ct × (SMLoc RK Sa × CKAGameSt Unit Unit)) :=
  .query (.corrupt p) fun a =>
    match a with
    | .state γ => .ret (.state γ (σ.1.rk p) (σ.1.snd p) (σ.1.rcv p), σ)
    | .none => .ret (.none, σ)
    | .out _ _ => .ret (.none, σ)
    | .leak _ _ _ => .ret (.none, σ)

/-- The simulator of the CKA reduction with the challenge epoch `t`. Its state is the part
`SMLoc` of the secure-messaging state and a shadow of the CKA game state that keeps the epoch
counters. -/
noncomputable def smCKAImplOf (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (t : ℕ) (ideal : Bool)
    (σ : SMLoc RK Sa × CKAGameSt Unit Unit) (q : SMQuery W) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (SMAns Sc Msg RK Sa Ct × (SMLoc RK Sa × CKAGameSt Unit Unit)) :=
  match q with
  | .ratchet p => smCKARatchet R t σ p
  | .recv p => smCKARecvT σ p
  | .send p m => smCKASendT G D σ p m
  | .chall p m => smCKAChallT G D t ideal σ p m
  | .corrupt p => smCKACorrT σ p

/-- **The CKA reduction** as an oracle tree: on the challenge epoch `t` and the public value
`pub`, it draws a uniform root key and runs the secure-messaging adversary against the
simulator `smCKAImplOf`. -/
noncomputable def smCKATreeOf (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ideal : Bool)
    (play : ℕ → Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) (t : ℕ) (pub : Msg) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand) Bool :=
  .rand (PMF.uniformFintype RK) fun rk =>
    (OracleAdv.simulate (smCKAImplOf R G D t ideal) (play t pub)
      (SMLoc.init rk, CKAGameSt.init () () ())).bind fun r => .ret r.1

derive_timed smCKAImplOf

derive_timed smCKATreeOf

end CKARed

/-! ## The CKA hop -/

section CKAHop

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Fintype Key] [Nonempty Key]

/-- The root step at the challenge epoch of the first hybrid: the root KDF on a uniform key. -/
noncomputable def unifKeyRoot (R : PRGDef (RK × Key) (RK × Sa)) (rk : RK) (_ : Key) :
    PMF (RK × Sa) :=
  (PMF.uniformFintype Key).bind fun k => PMF.pure (R.stretch (rk, k))

/-- The root step at the challenge epoch of the game simulated by the CKA reduction: the real
root step against the real CKA game, the root step on a uniform key against the ideal one. -/
noncomputable def ckaHopRoot (R : PRGDef (RK × Key) (RK × Sa)) (idealK : Bool) :
    RK → Key → PMF (RK × Sa) :=
  if idealK then unifKeyRoot R else realRoot R

/-- The shadow of a CKA game state, which keeps its epoch counters. -/
def ckaShadow (s : CKAGameSt Sc Msg) : CKAGameSt Unit Unit := ⟨fun _ => (), s.t, ()⟩

/-- The state of the CKA reduction and of the CKA game that a secure-messaging state
corresponds to. -/
def smCKAEmb (s : SMSt Sc Msg RK Sa) :
    (SMLoc RK Sa × CKAGameSt Unit Unit) × CKAGameSt Sc Msg :=
  ((s.loc, ckaShadow s.ck), s.ck)

theorem ckaShadow_sent (s : CKAGameSt Sc Msg) (p : CKAParty) (x : Sc) (T : Msg) :
    ckaShadow (s.sent p x T) = (ckaShadow s).sent p () () := by
  simp only [ckaShadow, CKAGameSt.sent]

theorem ckaShadow_recvd (s : CKAGameSt Sc Msg) (p : CKAParty) (x : Sc) :
    ckaShadow (s.recvd p x) = (ckaShadow s).recvd p () := by
  simp only [ckaShadow, CKAGameSt.recvd]

@[simp] theorem ckaShadow_canSend (s : CKAGameSt Sc Msg) (p : CKAParty) :
    (ckaShadow s).canSend p = s.canSend p :=
  CKAGameSt.canSend_eq_of_t rfl p

@[simp] theorem ckaShadow_canRecv (s : CKAGameSt Sc Msg) (p : CKAParty) :
    (ckaShadow s).canRecv p = s.canRecv p :=
  CKAGameSt.canRecv_eq_of_t rfl p

@[simp] theorem ckaShadow_t (s : CKAGameSt Sc Msg) : (ckaShadow s).t = s.t := rfl

omit [Fintype RK] [Nonempty RK] in
/-- **The CKA simulator is the secure-messaging oracle.** Each oracle call of the hybrid game
with the root step `ckaHopRoot R idealK`, mapped to the states of the reduction and of the CKA
game, is the call of the simulator `smCKAImplOf` against the CKA oracle with the challenge mode
`idealK`. -/
theorem smCKA_step (C : CKADef Sc Msg Key) [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ΔFS ΔPCS t : ℕ) (ideal idealK : Bool)
    (s : SMSt Sc Msg RK Sa) (q : SMQuery W) :
    (smOracleOf C R G D ΔFS ΔPCS t ideal (ckaHopRoot R idealK) s q).map
        (Prod.map id smCKAEmb) =
      OracleAdv.simOracle (smCKAImplOf R G D t ideal) (ckaOracleP C ΔFS ΔPCS t idealK)
        (smCKAEmb s) q := by
  cases q with
  | ratchet p =>
    simp only [smOracleOf, OracleAdv.simOracle, smCKAEmb, smCKAImplOf, smCKARatchet]
    by_cases h1 : s.ck.canSend p = true
    · by_cases h2 : (s.ck.t p + 1 == t) = true
      · cases idealK <;> simp [h1, h2, ckaHopRoot, realRoot, unifKeyRoot, ckaOracleP,
          OracleAdv.run_query, PMF.map_bind, PMF.bind_bind, PMF.pure_bind, PMF.pure_map,
          ckaShadow_sent, smCKAEmb]
      · simp [h1, h2, ckaOracleP, OracleAdv.run_query, PMF.map_bind, PMF.bind_bind,
          PMF.pure_bind, PMF.pure_map, ckaShadow_sent, smCKAEmb]
    · simp [h1, PMF.pure_map, smCKAEmb]
  | recv p =>
    simp only [smOracleOf, OracleAdv.simOracle, smCKAEmb, smCKAImplOf, smCKARecvT]
    by_cases h1 : s.ck.canRecv p = true
    · cases ho : s.loc.out <;>
        simp [h1, ho, ckaOracleP, SMLoc.received, PMF.pure_map, ckaShadow_recvd, smCKAEmb]
    · simp [h1, PMF.pure_map, smCKAEmb]
  | send p m =>
    simp only [smOracleOf, OracleAdv.simOracle, smCKAEmb, smCKAImplOf, smCKASendT]
    cases h : s.loc.snd p
    · simp [PMF.pure_map, smCKAEmb]
    · by_cases hc : ckaSender (s.ck.t p) = p <;> simp [hc, PMF.pure_map, smCKAEmb]
  | chall p m =>
    simp only [smOracleOf, OracleAdv.simOracle, smCKAEmb, smCKAImplOf, smCKAChallT]
    cases h : s.loc.snd p
    · simp [PMF.pure_map, smCKAEmb]
    · by_cases hc : challOk s.loc t (s.ck.t p) p = true <;>
        simp [hc, PMF.pure_map, PMF.map_bind, smCKAEmb]
  | corrupt p =>
    simp only [smOracleOf, OracleAdv.simOracle, smCKAEmb, smCKAImplOf, smCKACorrT]
    by_cases h1 : ckaAllowCorr ΔFS ΔPCS t s.ck p = true <;>
      simp [h1, ckaOracleP, PMF.pure_map, smCKAEmb]

theorem ckaShadow_init (pub : Msg) (sA sB : Sc) :
    ckaShadow (CKAGameSt.init pub sA sB) = CKAGameSt.init () () () := by
  simp only [ckaShadow, CKAGameSt.init]

/-- **The CKA reduction** `smcCKARed R G D ideal A`: the CKA adversary that keeps the challenge
epoch of `A` and plays the tree `smCKATreeOf`. -/
noncomputable def smcCKARed (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ideal : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    CKACorruptAdv Sc Msg Key Rand Bool where
  tStar := A.tStar
  play := smCKATreeOf R G D ideal A.play

omit [Fintype Key] [Nonempty Key] in
/-- The secure-messaging game with the root step `root` at the challenge epoch, as a lifted
distribution when the CKA initialisation is the lift of `initP`. -/
theorem sm_corrupt_gameOf_eq_liftPMF (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa))
    (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    sm_corrupt_gameOf C R G D ΔFS ΔPCS ideal root A =
      liftPMF (A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal root) (A.play t i.1)
          (smInit i rk)).map Prod.fst) := by
  unfold sm_corrupt_gameOf
  simp only [hinit, sample_eq_liftPMF, liftPMF_bind_liftPMF]

/-- **The CKA hop.** The CKA game with challenge mode `idealK` of the reduction `smcCKARed` is
the secure-messaging game with the root step `ckaHopRoot R idealK` at the challenge epoch: the
real game for the real CKA key, the first hybrid for the uniform one. -/
theorem smCKA_game_eq (C : CKADef Sc Msg Key) [CKACoins C Rand] (hS : CKACoins.Sound C)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal idealK : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    cka_corrupt_game C ΔFS ΔPCS idealK (smcCKARed R G D ideal A) =
      sm_corrupt_gameOf C R G D ΔFS ΔPCS ideal (ckaHopRoot R idealK) A := by
  rw [cka_corrupt_game_eq_liftPMF C hS initP hinit, sm_corrupt_gameOf_eq_liftPMF C initP hinit]
  congr 1
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => ?_))
  simp only [smcCKARed, smCKATreeOf, OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun rk => ?_)
  rw [OracleAdv.run_simulate_fst]
  have he : smCKAEmb (smInit (Sa := Sa) i rk) =
      ((SMLoc.init rk, CKAGameSt.init () () ()), CKAGameSt.init i.1 i.2.1 i.2.2) := by
    simp only [smCKAEmb, smInit, ckaShadow_init]
  rw [← he, ← OracleAdv.run_map_state _ _ smCKAEmb (smCKA_step C R G D ΔFS ΔPCS t ideal idealK),
    PMF.map_comp]
  rfl

end CKAHop

/-! ## The root hop -/

section RootRed

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- The opening of an epoch by party `p` in the simulator of the root hop: the CKA sending
algorithm on drawn randomness, and the root step, which at the challenge epoch `t` is a `prf`
query of the PRF-PRNG game at the root key of `p`. -/
noncomputable def smRootRatchet (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (t : ℕ) (s : SMSt Sc Msg RK Sa) (p : CKAParty) :
    OracleAdv (PPQuery RK Key) (RK × Sa) (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  if s.ck.canSend p then
    if s.ck.t p + 1 == t then
      .rand (PMF.uniformFintype Rand) fun r =>
        .query (.prf (s.loc.rk p)) fun y =>
          .ret (.msg (CKACoins.sendR (C := C) (s.ck.st p) r).2.1,
            ⟨s.ck.sent p (CKACoins.sendR (C := C) (s.ck.st p) r).1
              (CKACoins.sendR (C := C) (s.ck.st p) r).2.1, s.loc.opened p y⟩)
    else
      .rand (PMF.uniformFintype Rand) fun r =>
        .ret (.msg (CKACoins.sendR (C := C) (s.ck.st p) r).2.1,
          ⟨s.ck.sent p (CKACoins.sendR (C := C) (s.ck.st p) r).1
            (CKACoins.sendR (C := C) (s.ck.st p) r).2.1,
            s.loc.opened p (R.stretch (s.loc.rk p, (CKACoins.sendR (C := C) (s.ck.st p) r).2.2))⟩)
  else .ret (.none, s)

/-- The receive of party `p` in the simulator of the root hop. -/
noncomputable def smRootRecv {D' R' : Type} (C : CKADef Sc Msg Key) (s : SMSt Sc Msg RK Sa)
    (p : CKAParty) : OracleAdv D' R' (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  if s.ck.canRecv p then
    match s.loc.out with
    | some y => .ret (.none, ⟨s.ck.recvd p (C.recv (s.ck.st p) s.ck.msg).1, s.loc.recvY p y⟩)
    | none => .ret (.none, ⟨s.ck.recvd p (C.recv (s.ck.st p) s.ck.msg).1, s.loc⟩)
  else .ret (.none, s)

/-- The send of party `p` in a simulator with the full state. -/
noncomputable def smFullSend {D' R' : Type} (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (s : SMSt Sc Msg RK Sa) (p : CKAParty) (m : W × W) :
    OracleAdv D' R' (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  match s.loc.snd p with
  | some sa =>
    if ckaSender (s.ck.t p) == p then
      .ret (.ct (D.encrypt (G.stretch sa).1 m.1 m.2), ⟨s.ck, s.loc.advanced p (G.stretch sa).2⟩)
    else .ret (.none, s)
  | none => .ret (.none, s)

/-- The challenge of party `p` in a simulator with the full state. -/
noncomputable def smFullChall {D' R' : Type} (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (t : ℕ) (ideal : Bool) (s : SMSt Sc Msg RK Sa) (p : CKAParty) (m : W × W) :
    OracleAdv D' R' (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  match s.loc.snd p with
  | some sa =>
    if challOk s.loc t (s.ck.t p) p then
      .rand (challCt D ideal (G.stretch sa).1 m) fun c =>
        .ret (.ct c, ⟨s.ck, { s.loc.advanced p (G.stretch sa).2 with done := true }⟩)
    else .ret (.none, s)
  | none => .ret (.none, s)

/-- The corruption of party `p` in a simulator with the full state. -/
noncomputable def smFullCorr {D' R' : Type} (ΔFS ΔPCS t : ℕ) (s : SMSt Sc Msg RK Sa)
    (p : CKAParty) : OracleAdv D' R' (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  if ckaAllowCorr ΔFS ΔPCS t s.ck p then
    .ret (.state (s.ck.st p) (s.loc.rk p) (s.loc.snd p) (s.loc.rcv p), s)
  else .ret (.none, s)

/-- The simulator of the root hop with the challenge epoch `t`: the secure-messaging oracle of
the first hybrid, with the root step at the challenge epoch asked to the `prf` oracle of the
PRF-PRNG game. -/
noncomputable def smRootImplOf (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (s : SMSt Sc Msg RK Sa) (q : SMQuery W) :
    OracleAdv (PPQuery RK Key) (RK × Sa) (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  match q with
  | .ratchet p => smRootRatchet C R t s p
  | .recv p => smRootRecv C s p
  | .send p m => smFullSend G D s p m
  | .chall p m => smFullChall G D t ideal s p m
  | .corrupt p => smFullCorr ΔFS ΔPCS t s p

/-- **The PRF-PRNG reduction** as an oracle tree: it draws the challenge epoch of the adversary,
the CKA initialisation from `initP` and a uniform root key, and runs the adversary against the
simulator `smRootImplOf`. -/
noncomputable def smRootTreeOf (C : CKADef Sc Msg Key) [CKACoins C Rand] [Fintype RK]
    [Nonempty RK] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (initP : PMF (Msg × Sc × Sc)) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) :
    OracleAdv (PPQuery RK Key) (RK × Sa) Bool :=
  .rand tStar fun t =>
    .rand initP fun i =>
      .rand (PMF.uniformFintype RK) fun rk =>
        (OracleAdv.simulate (smRootImplOf C R G D ΔFS ΔPCS t ideal) (play t i.1)
          (smInit i rk)).bind fun r => .ret r.1

derive_timed smRootTreeOf

end RootRed

/-! ## The root hop: the game simulated by the PRF-PRNG reduction -/

section RootHop

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- Away from the opening of the challenge epoch, the simulator of the root hop asks no query
and answers as the secure-messaging oracle with any root step at the challenge epoch. -/
theorem smRoot_step_noncrit (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) {U : Type}
    (O' : U → PPQuery RK Key → PMF ((RK × Sa) × U)) (s : SMSt Sc Msg RK Sa) (u : U)
    (q : SMQuery W) (hc : smCrit t s q = false) :
    OracleAdv.simOracle (smRootImplOf C R G D ΔFS ΔPCS t ideal) O' (s, u) q =
      (smOracleOf C R G D ΔFS ΔPCS t ideal root s q).map fun y => (y.1, (y.2, u)) := by
  cases q with
  | ratchet p =>
    simp only [smCrit, Bool.and_eq_false_iff] at hc
    simp only [OracleAdv.simOracle, smRootImplOf, smRootRatchet, smOracleOf]
    rcases hc with h | h
    · simp [h, PMF.pure_map]
    · by_cases hs : s.ck.canSend p = true <;>
        simp [hs, h, PMF.map_bind, PMF.pure_bind, PMF.pure_map]
  | recv p =>
    simp only [OracleAdv.simOracle, smRootImplOf, smRootRecv, smOracleOf]
    by_cases h : s.ck.canRecv p = true
    · cases ho : s.loc.out <;> simp [h, ho, SMLoc.received, PMF.pure_map]
    · simp [h, PMF.pure_map]
  | send p m =>
    simp only [OracleAdv.simOracle, smRootImplOf, smFullSend, smOracleOf]
    cases h : s.loc.snd p
    · simp [PMF.pure_map]
    · by_cases hc : ckaSender (s.ck.t p) = p <;> simp [hc, PMF.pure_map]
  | chall p m =>
    simp only [OracleAdv.simOracle, smRootImplOf, smFullChall, smOracleOf]
    cases h : s.loc.snd p
    · simp [PMF.pure_map]
    · by_cases hc : challOk s.loc t (s.ck.t p) p = true <;>
        simp [hc, PMF.pure_map, PMF.map_bind]
  | corrupt p =>
    simp only [OracleAdv.simOracle, smRootImplOf, smFullCorr, smOracleOf]
    by_cases h : ckaAllowCorr ΔFS ΔPCS t s.ck p = true <;> simp [h, PMF.pure_map]

variable [Fintype RK] [Nonempty RK] [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa]
  [DecidableEq RK] [DecidableEq Key]

/-- The root step at the challenge epoch with the input `k` fixed in advance. -/
noncomputable def fixedKeyRoot (R : PRGDef (RK × Key) (RK × Sa)) (k : Key) (rk : RK) (_ : Key) :
    PMF (RK × Sa) :=
  PMF.pure (R.stretch (rk, k))

/-- The root step at the challenge epoch of the second hybrid: a uniform output. -/
noncomputable def unifRoot (_ : RK) (_ : Key) : PMF (RK × Sa) := PMF.uniformFintype (RK × Sa)

omit [Fintype Key] [Nonempty Key] in
/-- **The simulator against the real PRF-PRNG game.** With the hidden input `k`, each call of
the game with the root step `fixedKeyRoot R k` at the challenge epoch, with the PRF-PRNG state
attached, is the call of the simulator against the real PRF-PRNG oracle. -/
theorem smRoot_step_real (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (rk' : RK) (k : Key) (s : SMSt Sc Msg RK Sa)
    (q : SMQuery W) :
    (smOracleOf C R G D ΔFS ΔPCS t ideal (fixedKeyRoot R k) s q).map
        (Prod.map id fun s => (s, (⟨rk', k, [], []⟩ : PPSt RK Key (RK × Sa)))) =
      OracleAdv.simOracle (smRootImplOf C R G D ΔFS ΔPCS t ideal)
        (ppOracle (rootFn R) false false) (s, ⟨rk', k, [], []⟩) q := by
  cases hc : smCrit t s q
  · rw [smRoot_step_noncrit C R G D ΔFS ΔPCS t ideal (fixedKeyRoot R k) _ s _ q hc]
    rfl
  · cases q with
    | ratchet p =>
      simp only [smCrit, Bool.and_eq_true] at hc
      simp [OracleAdv.simOracle, smRootImplOf, smRootRatchet, smOracleOf, hc.1, hc.2,
        fixedKeyRoot, ppOracle, rootFn, PMF.map_bind, PMF.pure_bind, PMF.pure_map]
    | _ => simp [smCrit] at hc

omit [Fintype Key] [Nonempty Key] in
/-- **The simulator against the ideal PRF-PRNG game.** From a state whose table of the `prf`
oracle is empty unless the challenge epoch has been opened, each call of the simulator against
the ideal PRF-PRNG oracle, with the PRF-PRNG state dropped, is the call of the game with a
uniform root output at the challenge epoch. -/
theorem smRoot_step_ideal (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (s : SMSt Sc Msg RK Sa) (u : PPSt RK Key (RK × Sa))
    (hu : u.tR = [] ∨ smOpened t s) (q : SMQuery W) :
    (OracleAdv.simOracle (smRootImplOf C R G D ΔFS ΔPCS t ideal)
        (ppOracle (rootFn R) true true) (s, u) q).map (Prod.map id Prod.fst) =
      smOracleOf C R G D ΔFS ΔPCS t ideal unifRoot s q := by
  cases hc : smCrit t s q
  · rw [smRoot_step_noncrit C R G D ΔFS ΔPCS t ideal unifRoot _ s _ q hc, PMF.map_comp]
    exact PMF.map_id _
  · have hu' : u.tR = [] := by
      rcases hu with h | h
      · exact h
      · rw [smCrit_of_opened t s h q] at hc; exact absurd hc (by decide)
    cases q with
    | ratchet p =>
      simp only [smCrit, Bool.and_eq_true] at hc
      simp only [OracleAdv.simOracle, smRootImplOf, smRootRatchet, smOracleOf, hc.1, hc.2,
        ite_true, ppOracle, rfOracle, hu', List.lookup, OracleAdv.run_rand, OracleAdv.run_query,
        OracleAdv.run_ret, PMF.map_bind, PMF.bind_map, unifRoot]
      simp [Function.comp_def, PMF.pure_map]
    | _ => simp [smCrit] at hc

/-- **The PRF-PRNG reduction** `smcRootRed C R G D ΔFS ΔPCS ideal initP A`: the tree
`smRootTreeOf` at the challenge epoch and the interaction of `A`. -/
noncomputable def smcRootRed (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (initP : PMF (Msg × Sc × Sc))
    (A : SMCorruptAdv Sc Msg RK Sa W Ct) : OracleAdv (PPQuery RK Key) (RK × Sa) Bool :=
  smRootTreeOf C R G D ΔFS ΔPCS ideal initP A.tStar A.play

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq Key] in
/-- Running the PRF-PRNG reduction against an oracle is running the adversary against the
composed oracle from the drawn initial state. -/
theorem smcRootRed_run (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (initP : PMF (Msg × Sc × Sc))
    (A : SMCorruptAdv Sc Msg RK Sa W Ct) {U : Type}
    (O' : U → PPQuery RK Key → PMF ((RK × Sa) × U)) (u : U) :
    (OracleAdv.run O' (smcRootRed C R G D ΔFS ΔPCS ideal initP A) u).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (OracleAdv.simOracle (smRootImplOf C R G D ΔFS ΔPCS t ideal) O')
          (A.play t i.1) (smInit i rk, u)).map Prod.fst := by
  simp only [smcRootRed, smRootTreeOf, OracleAdv.run_rand, PMF.map_bind,
    OracleAdv.run_simulate_fst]

/-- **The real side of the root hop.** The real PRF-PRNG game of `smcRootRed` is the first
hybrid: the root step at the challenge epoch on a uniform key. -/
theorem smRoot_real_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    pp_game (rootFn R) false false (smcRootRed C R G D ΔFS ΔPCS ideal initP A) =
      sm_corrupt_gameOf C R G D ΔFS ΔPCS ideal (unifKeyRoot R) A := by
  rw [sm_corrupt_gameOf_eq_liftPMF C initP hinit]
  unfold pp_game
  congr 1
  have h1 : ∀ (rk' : RK) (k : Key),
      (OracleAdv.run (ppOracle (rootFn R) false false) (smcRootRed C R G D ΔFS ΔPCS ideal initP A)
        ⟨rk', k, [], []⟩).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal (fixedKeyRoot R k)) (A.play t i.1)
          (smInit i rk)).map Prod.fst := by
    intro rk' k
    rw [smcRootRed_run]
    refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ (funext fun rk => ?_)))
    rw [← OracleAdv.run_map_state _ _ (fun s => (s, (⟨rk', k, [], []⟩ : PPSt RK Key (RK × Sa))))
      (smRoot_step_real C R G D ΔFS ΔPCS t ideal rk' k), PMF.map_comp]
    rfl
  simp only [h1, PMF.bind_const]
  have h2 : ∀ (t : ℕ) (i : Msg × Sc × Sc) (rk : RK),
      (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal (unifKeyRoot R)) (A.play t i.1)
        (smInit i rk)).map Prod.fst =
      (PMF.uniformFintype Key).bind fun k =>
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal (fixedKeyRoot R k)) (A.play t i.1)
          (smInit i rk)).map Prod.fst := by
    intro t i rk
    rw [sm_run_eager C R G D ΔFS ΔPCS t ideal (PMF.uniformFintype Key) (unifKeyRoot R)
      (fixedKeyRoot R) (fun _ _ => rfl), PMF.map_bind]
  simp only [h2, PMF.bind_comm (PMF.uniformFintype Key)]

/-- **The ideal side of the root hop.** The ideal PRF-PRNG game of `smcRootRed` is the second
hybrid: a uniform root output at the challenge epoch. -/
theorem smRoot_ideal_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    pp_game (rootFn R) true true (smcRootRed C R G D ΔFS ΔPCS ideal initP A) =
      sm_corrupt_gameOf C R G D ΔFS ΔPCS ideal unifRoot A := by
  rw [sm_corrupt_gameOf_eq_liftPMF C initP hinit]
  unfold pp_game
  congr 1
  have h1 : ∀ (rk' : RK) (k : Key),
      (OracleAdv.run (ppOracle (rootFn R) true true) (smcRootRed C R G D ΔFS ΔPCS ideal initP A)
        ⟨rk', k, [], []⟩).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal unifRoot) (A.play t i.1)
          (smInit i rk)).map Prod.fst := by
    intro rk' k
    rw [smcRootRed_run]
    refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ (funext fun rk => ?_)))
    refine OracleAdv.run_map_fst_of_map_state_inv _ _ Prod.fst
      (fun x => x.2.tR = [] ∨ smOpened t x.1) ?_
      (fun x q hx => smRoot_step_ideal C R G D ΔFS ΔPCS t ideal x.1 x.2 hx q) _ _ (Or.inl rfl)
    intro x q hx y hy
    cases hc : smCrit t x.1 q
    · rw [smRoot_step_noncrit C R G D ΔFS ΔPCS t ideal unifRoot _ x.1 x.2 q hc] at hy
      simp only [PMF.support_map, Set.mem_image] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr (smOracleOf_opened C R G D ΔFS ΔPCS t ideal _ x.1 q h z hz)
    · have hm : (y.1, y.2.1) ∈ (smOracleOf C R G D ΔFS ΔPCS t ideal unifRoot x.1 q).support := by
        rw [← smRoot_step_ideal C R G D ΔFS ΔPCS t ideal x.1 x.2 hx q, PMF.support_map]
        exact ⟨y, hy, rfl⟩
      exact Or.inr (smOracleOf_opened_of_crit C R G D ΔFS ΔPCS t ideal _ x.1 q hc _ hm)
  simp only [h1, PMF.bind_const]

end RootHop

/-! ## Forward-secure AEAD with corruption -/

section FSAEADGame

variable {Sa W Ct : Type} [SampleableType W] [SampleableType Ct]

/-- The queries of the FS-AEAD adversary. -/
inductive FSQuery (W : Type) where
  /-- The sender encrypts the message `m` under the next key of its chain. -/
  | enc (m : W × W)
  /-- As `enc`, once, with a uniform ciphertext in the ideal game. -/
  | chall (m : W × W)
  /-- The state of the sender is returned. -/
  | corrupt

/-- The answers of the FS-AEAD oracles. -/
inductive FSAns (Sa Ct : Type) where
  /-- A refused query. -/
  | none
  /-- A ciphertext. -/
  | ct (c : Ct)
  /-- The state of the sender. -/
  | state (s : Sa)

/-- The state of the FS-AEAD game: the current state of the sender's chain, the initial state
of the epoch (the state of the receiver, which has no oracle in this confidentiality game), and
the flags of the challenge and of the corruption. -/
structure FSSt (Sa : Type) where
  /-- The current state of the sender. -/
  cur : Sa
  /-- The initial state of the epoch, held by the receiver. -/
  init : Sa
  /-- The challenge has been asked. -/
  done : Bool
  /-- The sender has been corrupted. -/
  corr : Bool

/-- The oracle of the FS-AEAD game of the generator `G` and the AEAD `D` (Alwen, Coretti and
Dodis, §4.3): `enc m` encrypts under the next key `(G cur).1` and moves the state to
`(G cur).2`; `chall m` does the same once, with a uniform ciphertext if `ideal`, and is refused
after a corruption; `corrupt` returns the current state. A corruption after the challenge is
allowed: the state has moved past the challenge key (forward secrecy). -/
noncomputable def fsOracle (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ideal : Bool)
    (s : FSSt Sa) : FSQuery W → PMF (FSAns Sa Ct × FSSt Sa)
  | .enc m => PMF.pure (.ct (D.encrypt (G.stretch s.cur).1 m.1 m.2), { s with cur := (G.stretch s.cur).2 })
  | .chall m =>
    if !s.done && !s.corr then
      (challCt D ideal (G.stretch s.cur).1 m).bind fun c =>
        PMF.pure (.ct c, { s with cur := (G.stretch s.cur).2, done := true })
    else PMF.pure (.none, s)
  | .corrupt => PMF.pure (.state s.cur, { s with corr := true })

variable [Fintype Sa] [Nonempty Sa]

/-- The FS-AEAD game with corruption: a uniform initial state of the epoch, and the run of the
adversary against `fsOracle`. -/
noncomputable def fsaead_corrupt_game (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ideal : Bool)
    (A : OracleAdv (FSQuery W) (FSAns Sa Ct) Bool) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype Sa).bind fun sa =>
    (OracleAdv.run (fsOracle G D ideal) A ⟨sa, sa, false, false⟩).map Prod.fst)

/-- **FS-AEAD advantage with corruption** of the adversary `A`. -/
noncomputable def FSAEAD_Corrupt_Advantage (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (A : OracleAdv (FSQuery W) (FSAns Sa Ct) Bool) : ℝ≥0∞ :=
  Advantage (fsaead_corrupt_game G D false A) (fsaead_corrupt_game G D true A)

end FSAEADGame

/-! ## The FS-AEAD reduction -/

section FSRed

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- Party `p` opened the challenge epoch with the next root key `rk`; its sending chain and the
root output in transit are held by the FS-AEAD game. -/
def SMLoc.openedX (l : SMLoc RK Sa) (p : CKAParty) (rk : RK) : SMLoc RK Sa :=
  { l with rk := Function.update l.rk p rk, snd := Function.update l.snd p none, out := none }

/-- Party `p` received the challenge epoch with the root key `rk`; its receiving chain is held
by the FS-AEAD game. -/
def SMLoc.recvX (l : SMLoc RK Sa) (p : CKAParty) (rk : RK) : SMLoc RK Sa :=
  { l with rk := Function.update l.rk p rk, rcv := Function.update l.rcv p none }

/-- The state of the FS-AEAD reduction: a secure-messaging state, and the marks of the chains
and of the root output that are held by the FS-AEAD game (those of the challenge epoch). -/
structure FSSim (Sc Msg RK Sa : Type) where
  /-- The secure-messaging state, with the held values left out. -/
  s : SMSt Sc Msg RK Sa
  /-- The sending chain of the party is the FS-AEAD sender. -/
  sndX : CKAParty → Bool
  /-- The receiving chain of the party is the initial state of the FS-AEAD game. -/
  rcvX : CKAParty → Bool
  /-- The root output in transit is the root key `rk⋆` with the initial FS-AEAD state. -/
  outX : Bool

/-- The opening of an epoch by party `p` in the FS-AEAD simulator; at the challenge epoch the
next root key is `rkS` and the chain is the FS-AEAD game's. -/
noncomputable def smFSRatchet (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (t : ℕ) (rkS : RK) (x : FSSim Sc Msg RK Sa) (p : CKAParty) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  if x.s.ck.canSend p then
    .rand (PMF.uniformFintype Rand) fun r =>
      if x.s.ck.t p + 1 == t then
        .ret (.msg (CKACoins.sendR (C := C) (x.s.ck.st p) r).2.1,
          ⟨⟨x.s.ck.sent p (CKACoins.sendR (C := C) (x.s.ck.st p) r).1
            (CKACoins.sendR (C := C) (x.s.ck.st p) r).2.1, x.s.loc.openedX p rkS⟩,
            Function.update x.sndX p true, x.rcvX, true⟩)
      else
        .ret (.msg (CKACoins.sendR (C := C) (x.s.ck.st p) r).2.1,
          ⟨⟨x.s.ck.sent p (CKACoins.sendR (C := C) (x.s.ck.st p) r).1
            (CKACoins.sendR (C := C) (x.s.ck.st p) r).2.1,
            x.s.loc.opened p (R.stretch (x.s.loc.rk p, (CKACoins.sendR (C := C) (x.s.ck.st p) r).2.2))⟩,
            Function.update x.sndX p false, x.rcvX, false⟩)
  else .ret (.none, x)

/-- The receive of party `p` in the FS-AEAD simulator. -/
noncomputable def smFSRecv (C : CKADef Sc Msg Key) (rkS : RK) (x : FSSim Sc Msg RK Sa)
    (p : CKAParty) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  if x.s.ck.canRecv p then
    if x.outX then
      .ret (.none, ⟨⟨x.s.ck.recvd p (C.recv (x.s.ck.st p) x.s.ck.msg).1, x.s.loc.recvX p rkS⟩,
        x.sndX, Function.update x.rcvX p true, x.outX⟩)
    else
      match x.s.loc.out with
      | some y =>
        .ret (.none, ⟨⟨x.s.ck.recvd p (C.recv (x.s.ck.st p) x.s.ck.msg).1, x.s.loc.recvY p y⟩,
          x.sndX, Function.update x.rcvX p false, x.outX⟩)
      | none =>
        .ret (.none, ⟨⟨x.s.ck.recvd p (C.recv (x.s.ck.st p) x.s.ck.msg).1, x.s.loc⟩,
          x.sndX, x.rcvX, x.outX⟩)
  else .ret (.none, x)

/-- The send of party `p` in the FS-AEAD simulator: forwarded to the FS-AEAD game on the chain
of the challenge epoch, computed locally otherwise. -/
noncomputable def smFSSend (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (x : FSSim Sc Msg RK Sa)
    (p : CKAParty) (m : W × W) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  if x.sndX p then
    if ckaSender (x.s.ck.t p) == p then
      .query (.enc m) fun a =>
        match a with
        | .ct c => .ret (.ct c, x)
        | .none => .ret (.none, x)
        | .state _ => .ret (.none, x)
    else .ret (.none, x)
  else
    match x.s.loc.snd p with
    | some sa =>
      if ckaSender (x.s.ck.t p) == p then
        .ret (.ct (D.encrypt (G.stretch sa).1 m.1 m.2),
          { x with s := ⟨x.s.ck, x.s.loc.advanced p (G.stretch sa).2⟩ })
      else .ret (.none, x)
    | none => .ret (.none, x)

/-- The challenge of party `p` in the FS-AEAD simulator: forwarded to the FS-AEAD game. -/
noncomputable def smFSChall (t : ℕ) (x : FSSim Sc Msg RK Sa) (p : CKAParty) (m : W × W) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  if x.sndX p then
    if challOk x.s.loc t (x.s.ck.t p) p then
      .query (.chall m) fun a =>
        match a with
        | .ct c => .ret (.ct c, { x with s := ⟨x.s.ck, { x.s.loc with done := true }⟩ })
        | .none => .ret (.none, x)
        | .state _ => .ret (.none, x)
    else .ret (.none, x)
  else .ret (.none, x)

/-- The corruption of party `p` in the FS-AEAD simulator. -/
noncomputable def smFSCorr (ΔFS ΔPCS t : ℕ) (x : FSSim Sc Msg RK Sa) (p : CKAParty) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  if ckaAllowCorr ΔFS ΔPCS t x.s.ck p then
    .ret (.state (x.s.ck.st p) (x.s.loc.rk p) (x.s.loc.snd p) (x.s.loc.rcv p), x)
  else .ret (.none, x)

/-- The simulator of the FS-AEAD reduction with the challenge epoch `t` and the root key `rkS`
of the challenge epoch: the secure-messaging oracle of the second hybrid with the root output
`(rkS, sa)` at the challenge epoch, where the FS-AEAD instance of the challenge epoch, from the
initial state `sa`, is the FS-AEAD game's. -/
noncomputable def smFSImplOf (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (rkS : RK) (x : FSSim Sc Msg RK Sa) (q : SMQuery W) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  match q with
  | .ratchet p => smFSRatchet C R t rkS x p
  | .recv p => smFSRecv C rkS x p
  | .send p m => smFSSend G D x p m
  | .chall p m => smFSChall t x p m
  | .corrupt p => smFSCorr ΔFS ΔPCS t x p

/-- **The FS-AEAD reduction** as an oracle tree: it draws the challenge epoch, the CKA
initialisation, the initial root key and the root key of the challenge epoch, and runs the
adversary against the simulator `smFSImplOf`. -/
noncomputable def smFSTreeOf (C : CKADef Sc Msg Key) [CKACoins C Rand] [Fintype RK]
    [Nonempty RK] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (initP : PMF (Msg × Sc × Sc)) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) Bool :=
  .rand tStar fun t =>
    .rand initP fun i =>
      .rand (PMF.uniformFintype RK) fun rk =>
        .rand (PMF.uniformFintype RK) fun rkS =>
          (OracleAdv.simulate (smFSImplOf C R G D ΔFS ΔPCS t rkS) (play t i.1)
            ⟨smInit i rk, fun _ => false, fun _ => false, false⟩).bind fun r => .ret r.1

derive_timed smFSTreeOf

end FSRed

/-! ## The FS-AEAD hop: invariants of the simulation -/

section FSInvSec

variable {Sc Msg RK Sa : Type}

/-- The epoch counters of a reachable CKA game state: equal, or the party ahead by one is the
sender of its epoch. -/
def ckaReach {St M : Type} (s : CKAGameSt St M) : Prop :=
  s.t .A = s.t .B ∨ (s.t .A = s.t .B + 1 ∧ ckaSender (s.t .A) = .A) ∨
    (s.t .B = s.t .A + 1 ∧ ckaSender (s.t .B) = .B)

theorem ckaReach_init {St M : Type} (pub : M) (sA sB : St) :
    ckaReach (CKAGameSt.init pub sA sB) := Or.inl rfl

theorem ckaSender_ne_succ (e : ℕ) : ckaSender (e + 1) ≠ ckaSender e := by
  rw [ckaSender_succ]; exact CKAParty.other_ne _

theorem ckaReach_sent {St M : Type} {s : CKAGameSt St M} {p : CKAParty}
    (hc : s.canSend p = true) (x : St) (T : M) : ckaReach (s.sent p x T) := by
  simp only [CKAGameSt.canSend, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨h1, h2⟩ := hc
  unfold ckaReach
  cases p
  · right; left
    simp only [CKAGameSt.sent_t, ite_true, reduceCtorEq, ite_false]
    exact ⟨by omega, h2⟩
  · right; right
    simp only [CKAGameSt.sent_t, ite_true, reduceCtorEq, ite_false]
    exact ⟨by omega, by rw [← h1]; exact h2⟩

theorem ckaReach_recvd {St M : Type} {s : CKAGameSt St M} {p : CKAParty}
    (hc : s.canRecv p = true) (x : St) : ckaReach (s.recvd p x) := by
  simp only [CKAGameSt.canRecv, beq_iff_eq] at hc
  left
  cases p <;> simp at hc ⊢ <;> omega

/-- In a reachable state, a party that may receive is one epoch behind its peer, and the peer
is the sender of its epoch. -/
theorem ckaReach_recv {St M : Type} {s : CKAGameSt St M} (h : ckaReach s) {p : CKAParty}
    (hc : s.canRecv p = true) : s.t p.other = s.t p + 1 ∧ ckaSender (s.t p.other) = p.other := by
  simp only [CKAGameSt.canRecv, beq_iff_eq] at hc
  refine ⟨hc.symm, ?_⟩
  unfold ckaReach at h
  cases p
  · simp only [CKAParty.other_A] at hc ⊢
    rcases h with h | ⟨h1, -⟩ | ⟨-, h2⟩
    · omega
    · omega
    · exact h2
  · simp only [CKAParty.other_B] at hc ⊢
    rcases h with h | ⟨-, h2⟩ | ⟨h1, -⟩
    · omega
    · exact h2
    · omega

/-- In a reachable state, a party that may send opens the epoch of its counter plus one, and
both counters are equal. -/
theorem ckaSend_spec {St M : Type} {s : CKAGameSt St M} {p : CKAParty}
    (hc : s.canSend p = true) : s.t p.other = s.t p ∧ ckaSender (s.t p + 1) = p := by
  simp only [CKAGameSt.canSend, Bool.and_eq_true, beq_iff_eq] at hc
  cases p
  · exact ⟨hc.1.symm, hc.2⟩
  · exact ⟨hc.1, by rw [← hc.1]; exact hc.2⟩

/-- **The corruption gates keep the chains of the challenge epoch hidden.** With
`2 ≤ ΔFS` and `1 ≤ ΔPCS`, a party whose counter is the challenge epoch or the one after it
cannot be corrupted. -/
theorem not_allowCorr_of_window {St M : Type} {ΔFS ΔPCS t : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 1 ≤ ΔPCS) {s : CKAGameSt St M} {p : CKAParty} (h1 : t ≤ s.t p)
    (h2 : s.t p ≤ t + 1) : ckaAllowCorr ΔFS ΔPCS t s p = false := by
  simp only [ckaAllowCorr, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le]
  constructor
  · have : s.t p ≤ max (s.t .A) (s.t .B) := by cases p <;> simp
    omega
  · omega

/-- The invariant of the FS-AEAD simulation with the challenge epoch `t` and the initial
FS-AEAD state `sa`. -/
structure FSInv (t : ℕ) (sa : Sa) (x : FSSim Sc Msg RK Sa × FSSt Sa) : Prop where
  corr : x.2.corr = false
  done : x.2.done = x.1.s.loc.done
  init : x.2.init = sa
  fresh : ¬ smOpened t x.1.s → x.2.cur = x.2.init
  reach : ckaReach x.1.s.ck
  snd : ∀ p, x.1.sndX p = true → p = ckaSender t ∧ t ≤ x.1.s.ck.t p ∧ x.1.s.ck.t p ≤ t + 1
  rcv : ∀ p, x.1.rcvX p = true → p ≠ ckaSender t ∧ t ≤ x.1.s.ck.t p ∧ x.1.s.ck.t p ≤ t + 1
  out : x.1.outX = true →
    x.1.s.ck.t .A ≤ t ∧ x.1.s.ck.t .B ≤ t ∧ x.1.s.ck.t (ckaSender t) = t
  empty : x.1.outX = false → x.1.s.loc.out = none → x.1.s.ck.t .A = 0 ∧ x.1.s.ck.t .B = 0
  chal : ∀ p, ckaSender (x.1.s.ck.t p) = p → x.1.s.ck.t p = t → x.1.s.loc.snd p = none

/-- The secure-messaging state that a state of the FS-AEAD simulation stands for: the held
chains are the current and the initial FS-AEAD state, the held root output is `(rkS, init)`. -/
def fsAbs (rkS : RK) (x : FSSim Sc Msg RK Sa × FSSt Sa) : SMSt Sc Msg RK Sa :=
  ⟨x.1.s.ck, { x.1.s.loc with
    snd := fun p => if x.1.sndX p then some x.2.cur else x.1.s.loc.snd p
    rcv := fun p => if x.1.rcvX p then some x.2.init else x.1.s.loc.rcv p
    out := if x.1.outX then some (rkS, x.2.init) else x.1.s.loc.out }⟩

end FSInvSec

section FSHop

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- The root step at the challenge epoch with the output `y` fixed in advance. -/
noncomputable def constRoot (y : RK × Sa) (_ : RK) (_ : Key) : PMF (RK × Sa) := PMF.pure y

/-- **The FS-AEAD simulator is the secure-messaging oracle.** Under the invariant, each call of
the simulator against the FS-AEAD oracle, mapped by `fsAbs`, is the call of the game with the
root output `(rkS, sa)` at the challenge epoch. -/
theorem smFS_step (C : CKADef Sc Msg Key) [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 1 ≤ ΔPCS) (t : ℕ) (ideal : Bool) (rkS : RK) (sa : Sa)
    (x : FSSim Sc Msg RK Sa × FSSt Sa) (hx : FSInv t sa x) (q : SMQuery W) :
    (OracleAdv.simOracle (smFSImplOf C R G D ΔFS ΔPCS t rkS) (fsOracle G D ideal) x q).map
        (Prod.map id (fsAbs rkS)) =
      smOracleOf C R G D ΔFS ΔPCS t ideal (constRoot (Key := Key) (rkS, sa)) (fsAbs rkS x) q := by
  obtain ⟨⟨⟨ck, l⟩, sX, rX, oX⟩, u⟩ := x
  have hsXw : ∀ q, sX q = true → t ≤ ck.t q ∧ ck.t q ≤ t + 1 := fun q h => (hx.snd q h).2
  have hrXw : ∀ q, rX q = true → t ≤ ck.t q ∧ ck.t q ≤ t + 1 := fun q h => (hx.rcv q h).2
  have hinit : u.init = sa := hx.init
  cases q with
  | ratchet p =>
    simp only [OracleAdv.simOracle, smFSImplOf, smFSRatchet, smOracleOf, fsAbs]
    by_cases hc : ck.canSend p = true
    · have hsp := ckaSend_spec hc
      by_cases ht : ck.t p + 1 = t
      · have hno : ∀ q, ck.t q < t := fun q => by
          rcases CKAParty.eq_or_eq_other q p with rfl | rfl <;> omega
        have hsX : ∀ q, sX q = false := fun q => by
          by_contra h; have := hsXw q (by simpa using h); have := hno q; omega
        have hrX : ∀ q, rX q = false := fun q => by
          by_contra h; have := hrXw q (by simpa using h); have := hno q; omega
        have hoX : oX = false := by
          by_contra h
          have h3 : ck.t (ckaSender t) = t := (hx.out (by simpa using h)).2.2
          have := hno (ckaSender t); omega
        have hcur : u.cur = sa := by
          refine (hx.fresh ?_).trans hx.init
          simp only [smOpened, not_or, not_le]
          exact ⟨hno .A, hno .B⟩
        simp only [hc, ht, beq_self_eq_true, ite_true, hsX, hrX, hoX, Bool.false_eq_true,
          ite_false, OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map,
          constRoot, PMF.pure_bind]
        refine congrArg _ (funext fun r => ?_)
        simp only [Prod.map_apply, id_eq, fsAbs, SMLoc.openedX, SMLoc.opened, hcur, hinit, hrX,
          Bool.false_eq_true, ite_false, ite_true]
        congr 4
        funext q
        by_cases hq : q = p
        · subst hq; simp
        · simp [hq, hsX]
      · have ht' : (ck.t p + 1 == t) = false := by simpa using ht
        simp only [hc, ht', ite_true, Bool.false_eq_true, ite_false, OracleAdv.run_rand,
          OracleAdv.run_ret, PMF.map_bind, PMF.pure_map, PMF.pure_bind]
        refine congrArg _ (funext fun r => ?_)
        simp only [Prod.map_apply, id_eq, fsAbs, SMLoc.opened, Bool.false_eq_true, ite_false]
        congr 4
        funext q
        by_cases hq : q = p
        · subst hq; simp
        · simp [hq]
    · simp [hc, PMF.pure_map, fsAbs]
  | recv p =>
    simp only [OracleAdv.simOracle, smFSImplOf, smFSRecv, smOracleOf]
    by_cases hc : ck.canRecv p = true
    · by_cases ho : oX = true
      · simp only [hc, ho, ite_true, OracleAdv.run_ret, PMF.pure_map, Prod.map_apply, id_eq,
          fsAbs, SMLoc.received, SMLoc.recvX, SMLoc.recvY, hinit]
        congr 4
        funext q
        by_cases hq : q = p
        · subst hq; simp
        · simp [hq]
      · have ho' : oX = false := by simpa using ho
        cases hl : l.out with
        | none =>
          have h0 := hx.empty ho' hl
          simp only [CKAGameSt.canRecv, beq_iff_eq] at hc
          cases p <;> simp_all
        | some y =>
          simp only [hc, ho', Bool.false_eq_true, ite_true, ite_false, hl, OracleAdv.run_ret,
            PMF.pure_map, Prod.map_apply, id_eq, fsAbs, SMLoc.received, SMLoc.recvY]
          congr 4
          funext q
          by_cases hq : q = p
          · subst hq; simp
          · simp [hq]
    · simp [hc, PMF.pure_map, fsAbs]
  | send p m =>
    simp only [OracleAdv.simOracle, smFSImplOf, smFSSend, smOracleOf]
    by_cases hs : sX p = true
    · have huniq : ∀ q, q ≠ p → sX q = false := fun q hq => by
        by_contra h
        exact hq ((hx.snd q (by simpa using h)).1.trans (hx.snd p hs).1.symm)
      by_cases hsd : ckaSender (ck.t p) = p
      · simp only [hs, hsd, beq_self_eq_true, ite_true, fsAbs, OracleAdv.run_query, fsOracle,
          PMF.pure_bind, OracleAdv.run_ret, PMF.pure_map, Prod.map_apply, id_eq,
          SMLoc.advanced]
        congr 4
        funext q
        by_cases hq : q = p
        · subst hq; simp [hs]
        · simp [hq, huniq q hq]
      · have hsd' : (ckaSender (ck.t p) == p) = false := by simpa using hsd
        simp [hs, hsd', fsAbs, PMF.pure_map]
    · have hs' : sX p = false := by simpa using hs
      cases hl : l.snd p with
      | none => simp [hs', hl, fsAbs, PMF.pure_map]
      | some sa' =>
        by_cases hsd : ckaSender (ck.t p) = p
        · simp only [hs', hl, hsd, beq_self_eq_true, Bool.false_eq_true, ite_true, ite_false,
            fsAbs, OracleAdv.run_ret, PMF.pure_map, Prod.map_apply, id_eq, SMLoc.advanced]
          congr 4
          funext q
          by_cases hq : q = p
          · subst hq; simp [hs']
          · simp [hq]
        · have hsd' : (ckaSender (ck.t p) == p) = false := by simpa using hsd
          simp [hs', hl, hsd', fsAbs, PMF.pure_map]
  | chall p m =>
    simp only [OracleAdv.simOracle, smFSImplOf, smFSChall, smOracleOf, challOk]
    by_cases hs : sX p = true
    · have huniq : ∀ q, q ≠ p → sX q = false := fun q hq => by
        by_contra h
        exact hq ((hx.snd q (by simpa using h)).1.trans (hx.snd p hs).1.symm)
      by_cases hok : (!l.done && (ckaSender (ck.t p) == p) && (ck.t p == t)) = true
      · have hd : l.done = false := by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
          exact hok.1.1
        have hfs : (!u.done && !u.corr) = true := by
          simp [show u.done = l.done from hx.done, hd, show u.corr = false from hx.corr]
        simp only [hs, hok, ite_true, fsAbs, OracleAdv.run_query, fsOracle, hfs,
          PMF.bind_bind, PMF.pure_bind, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map,
          Prod.map_apply, id_eq, SMLoc.advanced]
        refine congrArg _ (funext fun c => ?_)
        congr 4
        funext q
        by_cases hq : q = p
        · subst hq; simp [hs]
        · simp [hq, huniq q hq]
      · have hok' : (!l.done && (ckaSender (ck.t p) == p) && (ck.t p == t)) = false := by
          simpa using hok
        simp only [hs, hok', Bool.false_eq_true, ite_true,
          ite_false, fsAbs, OracleAdv.run_ret, PMF.pure_map, Prod.map_apply, id_eq]
    · have hs' : sX p = false := by simpa using hs
      cases hl : l.snd p with
      | none => simp [hs', hl, fsAbs, PMF.pure_map]
      | some sa' =>
        have hok : (!l.done && (ckaSender (ck.t p) == p) && (ck.t p == t)) = false := by
          by_contra h
          simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at h
          have := hx.chal p h.1.2 h.2
          simp only at this
          rw [hl] at this
          exact absurd this (by simp)
        simp only [hs', hl, hok, Bool.false_eq_true, ite_false, fsAbs,
          OracleAdv.run_ret, PMF.pure_map, Prod.map_apply, id_eq]
  | corrupt p =>
    simp only [OracleAdv.simOracle, smFSImplOf, smFSCorr, smOracleOf]
    by_cases hc : ckaAllowCorr ΔFS ΔPCS t ck p = true
    · have hs : sX p = false := by
        by_contra h
        have hw := hsXw p (by simpa using h)
        rw [not_allowCorr_of_window hFS hPCS hw.1 hw.2] at hc
        exact absurd hc (by decide)
      have hr : rX p = false := by
        by_contra h
        have hw := hrXw p (by simpa using h)
        rw [not_allowCorr_of_window hFS hPCS hw.1 hw.2] at hc
        exact absurd hc (by decide)
      simp [hc, hs, hr, fsAbs, PMF.pure_map]
    · simp [hc, fsAbs, PMF.pure_map]

theorem smOpened_of_le {t : ℕ} {s : SMSt Sc Msg RK Sa} {p : CKAParty} (h : t ≤ s.ck.t p) :
    smOpened t s := by
  cases p
  · exact Or.inl h
  · exact Or.inr h

/-- The invariant of the FS-AEAD simulation holds for a state whose secure-messaging part, marks
and FS-AEAD flags are those of a state with the invariant, when the FS-AEAD chain has only
moved after the opening of the challenge epoch. -/
theorem FSInv.of_cur {t : ℕ} {sa : Sa} {x : FSSim Sc Msg RK Sa × FSSt Sa} (hx : FSInv t sa x)
    (u : FSSt Sa) (hc : u.corr = false) (hd : u.done = x.2.done) (hi : u.init = x.2.init)
    (ho : smOpened t x.1.s) : FSInv t sa (x.1, u) :=
  ⟨hc, hd.trans hx.done, hi.trans hx.init, fun h => absurd ho h, hx.reach, hx.snd, hx.rcv, hx.out,
    hx.empty, hx.chal⟩

/-- **The invariant of the FS-AEAD simulation is kept** by every call of the simulator against
the FS-AEAD oracle. -/
theorem smFS_inv (C : CKADef Sc Msg Key) [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ΔFS ΔPCS t : ℕ) (ideal : Bool) (rkS : RK)
    (sa : Sa) (x : FSSim Sc Msg RK Sa × FSSt Sa) (hx : FSInv t sa x) (q : SMQuery W) (y)
    (hy : y ∈ (OracleAdv.simOracle (smFSImplOf C R G D ΔFS ΔPCS t rkS) (fsOracle G D ideal)
      x q).support) : FSInv t sa y.2 := by
  obtain ⟨⟨⟨ck, l⟩, sX, rX, oX⟩, u⟩ := x
  simp only [OracleAdv.simOracle, PMF.support_map, Set.mem_image] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hsXw : ∀ q, sX q = true → q = ckaSender t ∧ t ≤ ck.t q ∧ ck.t q ≤ t + 1 :=
    fun q h => hx.snd q h
  have hrXw : ∀ q, rX q = true → q ≠ ckaSender t ∧ t ≤ ck.t q ∧ ck.t q ≤ t + 1 :=
    fun q h => hx.rcv q h
  have hreach : ckaReach ck := hx.reach
  have hout : oX = true → ck.t .A ≤ t ∧ ck.t .B ≤ t ∧ ck.t (ckaSender t) = t := hx.out
  have hempty : oX = false → l.out = none → ck.t .A = 0 ∧ ck.t .B = 0 := hx.empty
  cases q with
  | ratchet p =>
    simp only [smFSImplOf, smFSRatchet] at hz
    by_cases hc : ck.canSend p = true
    · obtain ⟨hso, hsp⟩ := ckaSend_spec hc
      simp only [hc, ite_true, OracleAdv.run_rand, PMF.support_bind, Set.mem_iUnion] at hz
      obtain ⟨r, -, hz⟩ := hz
      by_cases ht : ck.t p + 1 = t
      · simp only [ht, beq_self_eq_true, ite_true, OracleAdv.run_ret, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        have hsp' : ckaSender t = p := ht ▸ hsp
        refine ⟨hx.corr, hx.done, hx.init, ?_, ckaReach_sent hc _ _, ?_, ?_, ?_, ?_, ?_⟩
        · intro h; exfalso; apply h
          cases p <;> simp [smOpened, CKAGameSt.sent_t] <;> omega
        · intro q hq
          by_cases hqp : q = p
          · subst hqp; simp only [CKAGameSt.sent_t, ite_true]; exact ⟨hsp'.symm, by omega, by omega⟩
          · have hq' : sX q = true := by simpa [Function.update_apply, hqp] using hq
            have := (hsXw q hq').2.1
            have : q = p.other := (CKAParty.eq_or_eq_other q p).resolve_left hqp
            subst this; omega
        · intro q hq
          have hq' : rX q = true := hq
          have h1 := (hrXw q hq').2.1
          by_cases hqp : q = p
          · subst hqp; omega
          · have : q = p.other := (CKAParty.eq_or_eq_other q p).resolve_left hqp
            subst this; omega
        · intro _
          simp only [CKAGameSt.sent_t, hsp']
          cases p <;> simp at hso ⊢ <;> omega
        · intro h; exact absurd h (by simp)
        · intro q _ hq2
          by_cases hqp : q = p
          · subst hqp; simp [SMLoc.openedX]
          · have : q = p.other := (CKAParty.eq_or_eq_other q p).resolve_left hqp
            subst this
            simp only [CKAGameSt.sent_t, hqp, ite_false] at hq2
            omega
      · have ht' : (ck.t p + 1 == t) = false := by simpa using ht
        simp only [ht', Bool.false_eq_true, ite_false, OracleAdv.run_ret, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨hx.corr, hx.done, hx.init, ?_, ckaReach_sent hc _ _, ?_, ?_, ?_, ?_, ?_⟩
        · intro h
          refine hx.fresh fun h' => h ?_
          rcases h' with h' | h'
          · exact Or.inl (h'.trans (CKAGameSt.le_sent _ _ _ _ _))
          · exact Or.inr (h'.trans (CKAGameSt.le_sent _ _ _ _ _))
        · intro q hq
          by_cases hqp : q = p
          · subst hqp; simp at hq
          · have hq' : sX q = true := by simpa [Function.update_apply, hqp] using hq
            simp only [CKAGameSt.sent_t, hqp, ite_false]
            exact hsXw q hq'
        · intro q hq
          have hq' : rX q = true := hq
          obtain ⟨h1, h2, h3⟩ := hrXw q hq'
          by_cases hqp : q = p
          · subst hqp
            simp only [CKAGameSt.sent_t, ite_true]
            refine ⟨h1, by omega, ?_⟩
            by_contra hlt
            have he : ck.t q = t + 1 := by omega
            rw [he, ckaSender_add_two] at hsp
            exact h1 hsp.symm
          · simp only [CKAGameSt.sent_t, hqp, ite_false]
            exact ⟨h1, h2, h3⟩
        · intro h; exact absurd h (by simp)
        · intro _ h; exact absurd h (by simp [SMLoc.opened])
        · intro q hq1 hq2
          by_cases hqp : q = p
          · subst hqp
            simp only [CKAGameSt.sent_t, ite_true] at hq2
            exact absurd hq2 ht
          · simp only [CKAGameSt.sent_t, hqp, ite_false] at hq1 hq2
            simp only [SMLoc.opened, Function.update_apply, hqp, ite_false]
            exact hx.chal q hq1 hq2
    · simp only [hc, Bool.false_eq_true, ite_false, OracleAdv.run_ret, PMF.support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hx
  | recv p =>
    simp only [smFSImplOf, smFSRecv] at hz
    by_cases hc : ck.canRecv p = true
    · obtain ⟨hto, hso⟩ := ckaReach_recv hreach hc
      by_cases ho : oX = true
      · simp only [hc, ho, ite_true, OracleAdv.run_ret, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        obtain ⟨hA, hB, hS⟩ := hout ho
        have hle : ∀ q, ck.t q ≤ t := fun q => by
          cases q
          · exact hA
          · exact hB
        have hpo : ckaSender t = p.other := by
          rcases CKAParty.eq_or_eq_other (ckaSender t) p with h | h
          · exfalso; rw [h] at hS
            have := hle p.other
            omega
          · exact h
        have htt : ck.t p.other = t := by rw [← hpo]; exact hS
        refine ⟨hx.corr, hx.done, hx.init, ?_, ckaReach_recvd hc _, ?_, ?_, ?_, ?_, ?_⟩
        · intro h; exfalso; apply h
          refine smOpened_of_le (p := p.other) ?_
          simp only [CKAGameSt.recvd_t, CKAParty.other_ne, ite_false]
          omega
        · intro q hq
          have hq' : sX q = true := hq
          obtain ⟨h1, h2, h3⟩ := hsXw q hq'
          by_cases hqp : q = p
          · subst hqp; rw [hpo] at h1; exact absurd h1 (CKAParty.ne_other q)
          · simp only [CKAGameSt.recvd_t, hqp, ite_false]; exact ⟨h1, h2, h3⟩
        · intro q hq
          by_cases hqp : q = p
          · subst hqp
            simp only [CKAGameSt.recvd_t, ite_true]
            exact ⟨by rw [hpo]; exact CKAParty.ne_other q, by omega, by omega⟩
          · have hq' : rX q = true := by simpa [Function.update_apply, hqp] using hq
            simp only [CKAGameSt.recvd_t, hqp, ite_false]
            exact hrXw q hq'
        · intro _
          have hpA := hle .A; have hpB := hle .B
          simp only [CKAGameSt.recvd_t, hpo, CKAParty.other_ne, ite_false]
          refine ⟨?_, ?_, htt⟩ <;> split <;> omega
        · intro h; exact absurd h (by simp)
        · intro q hq1 hq2
          by_cases hqp : q = p
          · subst hqp
            simp only [CKAGameSt.recvd_t, ite_true] at hq1
            rw [← hto, hso] at hq1
            exact absurd hq1 (CKAParty.other_ne q)
          · simp only [CKAGameSt.recvd_t, hqp, ite_false] at hq1 hq2
            simp only [SMLoc.recvX]
            exact hx.chal q hq1 hq2
      · have ho' : oX = false := by simpa using ho
        cases hl : l.out with
        | none =>
          have h0 := hempty ho' hl
          cases p <;> simp at hto <;> omega
        | some y =>
          simp only [hc, ho', Bool.false_eq_true, ite_true, ite_false, hl, OracleAdv.run_ret,
            PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          refine ⟨hx.corr, hx.done, hx.init, ?_, ckaReach_recvd hc _, ?_, ?_, ?_, ?_, ?_⟩
          · intro h
            refine hx.fresh fun h' => h ?_
            rcases h' with h' | h'
            · exact Or.inl (h'.trans (CKAGameSt.le_recvd _ _ _ _))
            · exact Or.inr (h'.trans (CKAGameSt.le_recvd _ _ _ _))
          · intro q hq
            have hq' : sX q = true := hq
            obtain ⟨h1, h2, h3⟩ := hsXw q hq'
            by_cases hqp : q = p
            · subst hqp
              simp only [CKAGameSt.recvd_t, ite_true]
              refine ⟨h1, by omega, ?_⟩
              by_contra hlt
              have he : ck.t q.other = t + 2 := by omega
              rw [he, ckaSender_add_two, ← h1] at hso
              exact CKAParty.ne_other q hso
            · simp only [CKAGameSt.recvd_t, hqp, ite_false]; exact ⟨h1, h2, h3⟩
          · intro q hq
            by_cases hqp : q = p
            · subst hqp; simp at hq
            · have hq' : rX q = true := by simpa [Function.update_apply, hqp] using hq
              simp only [CKAGameSt.recvd_t, hqp, ite_false]
              exact hrXw q hq'
          · intro h; exact absurd h (by simp)
          · intro _ h; exact absurd h (by simp [SMLoc.recvY, hl])
          · intro q hq1 hq2
            by_cases hqp : q = p
            · subst hqp
              simp only [CKAGameSt.recvd_t, ite_true] at hq1
              rw [← hto, hso] at hq1
              exact absurd hq1 (CKAParty.other_ne q)
            · simp only [CKAGameSt.recvd_t, hqp, ite_false] at hq1 hq2
              simp only [SMLoc.recvY]
              exact hx.chal q hq1 hq2
    · simp only [hc, Bool.false_eq_true, ite_false, OracleAdv.run_ret, PMF.support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hx
  | send p m =>
    simp only [smFSImplOf, smFSSend] at hz
    by_cases hs : sX p = true
    · by_cases hsd : ckaSender (ck.t p) = p
      · simp only [hs, hsd, beq_self_eq_true, ite_true, OracleAdv.run_query, fsOracle,
          PMF.pure_bind, OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact FSInv.of_cur hx _ hx.corr rfl rfl (smOpened_of_le (hsXw p hs).2.1)
      · have hsd' : (ckaSender (ck.t p) == p) = false := by simpa using hsd
        simp only [hs, hsd', Bool.false_eq_true, ite_true, ite_false, OracleAdv.run_ret,
          PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hx
    · have hs' : sX p = false := by simpa using hs
      cases hl : l.snd p with
      | none =>
        simp only [hs', hl, Bool.false_eq_true, ite_false, OracleAdv.run_ret, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; exact hx
      | some sa' =>
        by_cases hsd : ckaSender (ck.t p) = p
        · simp only [hs', hl, hsd, beq_self_eq_true, Bool.false_eq_true, ite_true, ite_false,
            OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          refine ⟨hx.corr, hx.done, hx.init, hx.fresh, hx.reach, hx.snd, hx.rcv, hx.out,
            hx.empty, ?_⟩
          intro q hq1 hq2
          by_cases hqp : q = p
          · subst hqp
            have := hx.chal q hq1 hq2
            simp only at this
            rw [hl] at this; exact absurd this (by simp)
          · simp only [SMLoc.advanced, Function.update_apply, hqp, ite_false]
            exact hx.chal q hq1 hq2
        · have hsd' : (ckaSender (ck.t p) == p) = false := by simpa using hsd
          simp only [hs', hl, hsd', Bool.false_eq_true, ite_false, OracleAdv.run_ret,
            PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hx
  | chall p m =>
    simp only [smFSImplOf, smFSChall] at hz
    by_cases hok : (sX p && challOk l t (ck.t p) p) = true
    · simp only [Bool.and_eq_true] at hok
      simp only [hok.1, hok.2, ite_true] at hz
      have hd : l.done = false := by
        have := hok.2
        simp only [challOk, Bool.and_eq_true, Bool.not_eq_true'] at this
        exact this.1.1
      have hfs : (!u.done && !u.corr) = true := by
        simp [show u.done = l.done from hx.done, hd, show u.corr = false from hx.corr]
      simp only [OracleAdv.run_query, fsOracle, hfs, ite_true,
        PMF.bind_bind, PMF.pure_bind, PMF.support_bind, Set.mem_iUnion, OracleAdv.run_ret,
        PMF.support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨c, -, rfl⟩ := hz
      have hop : smOpened t ⟨ck, l⟩ := smOpened_of_le (hsXw p hok.1).2.1
      exact ⟨hx.corr, rfl, hx.init, fun h => absurd hop h, hx.reach, hx.snd, hx.rcv, hx.out,
        hx.empty, hx.chal⟩
    · have hok' : (sX p && challOk l t (ck.t p) p) = false := by simpa using hok
      have hz' : z = ((SMAns.none, (⟨⟨ck, l⟩, sX, rX, oX⟩ : FSSim Sc Msg RK Sa)), u) := by
        by_cases hs : sX p = true
        · have hc : challOk l t (ck.t p) p = false := by simpa [hs] using hok
          simpa [hs, hc, OracleAdv.run_ret, PMF.support_pure] using hz
        · have hs' : sX p = false := by simpa using hs
          simpa [hs', OracleAdv.run_ret, PMF.support_pure] using hz
      subst hz'; exact hx
  | corrupt p =>
    simp only [smFSImplOf, smFSCorr] at hz
    split at hz <;> simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hz <;>
      subst hz <;> exact hx

/-- **The FS-AEAD reduction** `smcFSRed C R G D ΔFS ΔPCS initP A`: the tree `smFSTreeOf` at the
challenge epoch and the interaction of `A`. -/
noncomputable def smcFSRed [Fintype RK] [Nonempty RK] (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (initP : PMF (Msg × Sc × Sc)) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) Bool :=
  smFSTreeOf C R G D ΔFS ΔPCS initP A.tStar A.play

theorem fsAbs_init (rkS rk : RK) (i : Msg × Sc × Sc) (sa : Sa) :
    fsAbs rkS ((⟨smInit i rk, fun _ => false, fun _ => false, false⟩ : FSSim Sc Msg RK Sa),
      (⟨sa, sa, false, false⟩ : FSSt Sa)) = smInit i rk := by
  simp [fsAbs, smInit]

theorem fsInv_init (t : ℕ) (rk : RK) (i : Msg × Sc × Sc) (sa : Sa) :
    FSInv t sa ((⟨smInit i rk, fun _ => false, fun _ => false, false⟩ : FSSim Sc Msg RK Sa),
      (⟨sa, sa, false, false⟩ : FSSt Sa)) where
  corr := rfl
  done := rfl
  init := rfl
  fresh _ := rfl
  reach := ckaReach_init _ _ _
  snd p h := absurd h (by simp)
  rcv p h := absurd h (by simp)
  out h := absurd h (by simp)
  empty _ _ := ⟨rfl, rfl⟩
  chal _ _ _ := rfl

variable [Fintype RK] [Nonempty RK] [Fintype Sa] [Nonempty Sa]

/-- **The FS-AEAD hop.** With `2 ≤ ΔFS` and `1 ≤ ΔPCS`, the FS-AEAD game with corruption of the
reduction `smcFSRed`, with the challenge mode `ideal`, is the second hybrid with the same
challenge mode: a uniform root output at the challenge epoch. -/
theorem smFS_game_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (ideal : Bool)
    (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    fsaead_corrupt_game G D ideal (smcFSRed C R G D ΔFS ΔPCS initP A) =
      sm_corrupt_gameOf C R G D ΔFS ΔPCS ideal unifRoot A := by
  rw [sm_corrupt_gameOf_eq_liftPMF C initP hinit]
  unfold fsaead_corrupt_game
  congr 1
  have h1 : ∀ sa : Sa,
      (OracleAdv.run (fsOracle G D ideal) (smcFSRed C R G D ΔFS ΔPCS initP A)
        ⟨sa, sa, false, false⟩).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (PMF.uniformFintype RK).bind fun rkS =>
          (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal (constRoot (Key := Key) (rkS, sa)))
            (A.play t i.1) (smInit i rk)).map Prod.fst := by
    intro sa
    simp only [smcFSRed, smFSTreeOf, OracleAdv.run_rand, PMF.map_bind, OracleAdv.run_simulate_fst]
    refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ (funext fun rk =>
      congrArg _ (funext fun rkS => ?_))))
    rw [OracleAdv.run_map_fst_of_map_state_inv _ _ (fsAbs rkS) (FSInv t sa)
      (fun x q hx => smFS_inv C R G D ΔFS ΔPCS t ideal rkS sa x hx q)
      (fun x q hx => smFS_step C R G D hFS hPCS t ideal rkS sa x hx q) _ _
      (fsInv_init t rk i sa), fsAbs_init]
  simp only [h1]
  have h2 : ∀ (t : ℕ) (i : Msg × Sc × Sc) (rk : RK),
      (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal unifRoot) (A.play t i.1)
        (smInit i rk)).map Prod.fst =
      (PMF.uniformFintype RK).bind fun rkS => (PMF.uniformFintype Sa).bind fun sa =>
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal (constRoot (Key := Key) (rkS, sa)))
          (A.play t i.1) (smInit i rk)).map Prod.fst := by
    intro t i rk
    rw [sm_run_eager C R G D ΔFS ΔPCS t ideal (PMF.uniformFintype (RK × Sa)) unifRoot constRoot
      (fun _ _ => (PMF.bind_pure _).symm), PMF.map_bind, PMF.uniform_prod_eq_bind, PMF.bind_bind]
    refine congrArg _ (funext fun rkS => ?_)
    rw [PMF.bind_map]
    rfl
  simp only [h2, PMF.bind_comm (PMF.uniformFintype Sa)]

end FSHop

/-! ## The composition theorem -/

section Main

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Fintype Key] [Nonempty Key] [Fintype Sa]
  [Nonempty Sa] [DecidableEq RK] [DecidableEq Key]

/-- **Secure messaging with state corruption from CKA, PRF-PRNG and FS-AEAD security.** Let the
CKA `C` have a sound explicit-randomness sending algorithm and an initialisation that is the
lift of `initP`, and let the corruption delays satisfy `2 ≤ ΔFS` and `1 ≤ ΔPCS`. For every
secure-messaging adversary `A`, the advantage of `A` against the double ratchet of `C`, the root
KDF `R`, the chain generator `G` and the AEAD `D` is at most

* the CKA corruption advantages (with the same delays) of the reductions `smcCKARed R G D b A`,
* the PRF-PRNG advantages of `R` at the reductions `smcRootRed C R G D ΔFS ΔPCS b initP A`,

for the two challenge modes `b`, plus the FS-AEAD advantage with corruption of `G` and `D` at
the reduction `smcFSRed C R G D ΔFS ΔPCS initP A`. -/
theorem sm_corrupt_advantage_le (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    SM_Corrupt_Advantage C R G D ΔFS ΔPCS A ≤
      ∑ b : Bool, CKA_Corrupt_Advantage C ΔFS ΔPCS (smcCKARed R G D b A) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed C R G D ΔFS ΔPCS b initP A) +
        FSAEAD_Corrupt_Advantage G D (smcFSRed C R G D ΔFS ΔPCS initP A) := by
  have e0 : ∀ b, sm_corrupt_game C R G D ΔFS ΔPCS b A =
      cka_corrupt_real C ΔFS ΔPCS (smcCKARed R G D b A) := fun b =>
    (smCKA_game_eq C hS initP hinit R G D ΔFS ΔPCS b false A).symm
  have e1 : ∀ b, cka_corrupt_ideal C ΔFS ΔPCS (smcCKARed R G D b A) =
      pp_game (rootFn R) false false (smcRootRed C R G D ΔFS ΔPCS b initP A) := fun b =>
    (smCKA_game_eq C hS initP hinit R G D ΔFS ΔPCS b true A).trans
      (smRoot_real_eq C initP hinit R G D ΔFS ΔPCS b A).symm
  have e2 : ∀ b, pp_game (rootFn R) true true (smcRootRed C R G D ΔFS ΔPCS b initP A) =
      fsaead_corrupt_game G D b (smcFSRed C R G D ΔFS ΔPCS initP A) := fun b =>
    (smRoot_ideal_eq C initP hinit R G D ΔFS ΔPCS b A).trans
      (smFS_game_eq C initP hinit R G D hFS hPCS b A).symm
  have hK : ∀ b, Advantage (sm_corrupt_game C R G D ΔFS ΔPCS b A)
      (pp_game (rootFn R) false false (smcRootRed C R G D ΔFS ΔPCS b initP A)) =
      CKA_Corrupt_Advantage C ΔFS ΔPCS (smcCKARed R G D b A) := fun b => by
    rw [e0, ← e1]; rfl
  have hP : ∀ b, Advantage (pp_game (rootFn R) false false (smcRootRed C R G D ΔFS ΔPCS b initP A))
      (fsaead_corrupt_game G D b (smcFSRed C R G D ΔFS ΔPCS initP A)) =
      PRFPRNG_Advantage R (smcRootRed C R G D ΔFS ΔPCS b initP A) := fun b => by
    rw [← e2]; rfl
  unfold SM_Corrupt_Advantage
  simp only [Fintype.sum_bool]
  clear hinit e0 e1 e2
  hop_chain [hK false, hK true, hP false, hP true,
    (show Advantage (fsaead_corrupt_game G D false _) _ = FSAEAD_Corrupt_Advantage G D _ from rfl)]

end Main

/-! ## The Diffie–Hellman double ratchet -/

section DH

variable {RK Sa W Ct : Type} [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [Fintype Sa] [Nonempty Sa] [DecidableEq RK]

/-- The distribution of the initialisation of `dhCKA`. -/
noncomputable def dhInitP (G : Type) [CG : CyclicGroup G] : PMF (G × (G × CG.Exp) × (G × CG.Exp)) :=
  (PMF.uniformFintype CG.Exp).map fun x => (CG.pow x, (CG.pow x, x), (CG.pow x, x))

theorem dhCKA_init_eq (G : Type) [CG : CyclicGroup G] :
    (dhCKA G).init = liftPMF (dhInitP G) := by
  simp only [dhCKA, dhInitP, sample_eq_liftPMF, liftPMF_bind_pure]

variable (G : Type) [CG : CyclicGroup G] [DecidableEq G]

/-- **Secure messaging with state corruption for the Diffie–Hellman double ratchet.** With the
CKA `dhCKA` and the delays `ΔFS = 2`, `ΔPCS = 2`, the CKA terms of `sm_corrupt_advantage_le`
are the DDH advantages of the reductions `ckaCorruptDDHRed (smcCKARed R F D b A)`
(`dhCKA_corrupt_advantage_eq_ddh`). -/
theorem sm_dh_corrupt_advantage_le (R : PRGDef (RK × G) (RK × Sa)) (F : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (A : SMCorruptAdv (G × CG.Exp) G RK Sa W Ct) :
    SM_Corrupt_Advantage (dhCKA G) R F D 2 2 A ≤
      ∑ b : Bool, DDH_Advantage G (ckaCorruptDDHRed (smcCKARed (Rand := CG.Exp) R F D b A)) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKA G) R F D 2 2 b (dhInitP G) A) +
        FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKA G) R F D 2 2 (dhInitP G) A) := by
  have h := sm_corrupt_advantage_le (dhCKA G) (dhCKACoins_sound G) (dhInitP G)
    (dhCKA_init_eq G) R F D (ΔFS := 2) (ΔPCS := 2) (le_refl 2) (by norm_num) A
  simp only [dhCKA_corrupt_advantage_eq_ddh] at h
  exact h

/-- **The Diffie–Hellman double ratchet with the HKDF-shaped root step.** With the root step
`hkdfRoot H` of a dual PRF `H`, the PRF-PRNG terms of `sm_dh_corrupt_advantage_le` are at most
the dual-PRF advantages of `H` at the reductions `ppRedR` and `ppRedL`
(`hkdfRoot_prfprng_le`). -/
theorem sm_dh_hkdf_corrupt_advantage_le (H : RK → G → RK × Sa) (F : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (A : SMCorruptAdv (G × CG.Exp) G RK Sa W Ct) :
    SM_Corrupt_Advantage (dhCKA G) (hkdfRoot H) F D 2 2 A ≤
      ∑ b : Bool, DDH_Advantage G
          (ckaCorruptDDHRed (smcCKARed (Rand := CG.Exp) (hkdfRoot H) F D b A)) +
        ∑ b : Bool, (DualPRF_Right_Advantage H
            (ppRedR H (smcRootRed (dhCKA G) (hkdfRoot H) F D 2 2 b (dhInitP G) A)) +
          DualPRF_Left_Advantage H
            (ppRedL (Key := G) (smcRootRed (dhCKA G) (hkdfRoot H) F D 2 2 b (dhInitP G) A))) +
        FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKA G) (hkdfRoot H) F D 2 2 (dhInitP G) A) := by
  refine (sm_dh_corrupt_advantage_le G (hkdfRoot H) F D A).trans ?_
  gcongr with b
  exact hkdfRoot_prfprng_le H _

end DH

/-! ## The passive game as the instance without corruption: distributions -/

section PassiveDist

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- `n` epochs of the CKA `C` as a probability mass function, with the sending algorithm on
drawn randomness. -/
noncomputable def ckaRunP (C : CKADef Sc Msg Key) [CKACoins C Rand] :
    ℕ → Sc → Sc → PMF (List (Msg × Key) × Sc × Sc)
  | 0, s, r => PMF.pure ([], s, r)
  | n + 1, s, r =>
    (PMF.uniformFintype Rand).bind fun x =>
      (ckaRunP C n (C.recv r (CKACoins.sendR (C := C) s x).2.1).1
        (CKACoins.sendR (C := C) s x).1).map fun p =>
        (((CKACoins.sendR (C := C) s x).2.1, (CKACoins.sendR (C := C) s x).2.2) :: p.1, p.2)

/-- With a sound explicit-randomness sending algorithm, the CKA run is the lift of `ckaRunP`. -/
theorem ckaRun_eq_liftPMF (C : CKADef Sc Msg Key) [CKACoins C Rand] (hS : CKACoins.Sound C)
    (n : ℕ) (s r : Sc) : ckaRun C n s r = liftPMF (ckaRunP C n s r) := by
  induction n generalizing s r with
  | zero => exact liftPMF_pure _
  | succ n ih =>
    simp only [ckaRun, ckaRunP, ih, liftPMF_bind_pure]
    rw [hS]
    simp only [SPComp.bind_assoc, SPComp.pure_bind, sample_eq_liftPMF, liftPMF_bind_liftPMF]

/-- The transcript of a CKA run of `n` epochs has length `n`. -/
theorem ckaRunP_length (C : CKADef Sc Msg Key) [CKACoins C Rand] (n : ℕ) (s r : Sc) (q)
    (hq : q ∈ (ckaRunP (Rand := Rand) C n s r).support) : q.1.length = n := by
  induction n generalizing s r q with
  | zero =>
    simp only [ckaRunP, PMF.support_pure, Set.mem_singleton_iff] at hq
    rw [hq]; rfl
  | succ n ih =>
    simp only [ckaRunP, PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hq
    obtain ⟨x, -, p, hp, rfl⟩ := hq
    simp only [List.length_cons, ih _ _ _ hp]

/-- The ciphertexts of the messages `ms` of one epoch under the keys `keys`, the message of
global index `g` first: uniform below the threshold `k`, the encryption otherwise. -/
noncomputable def epochCtsDist (D : AEADDef W Ct) (k : ℕ) :
    ℕ → List W → List (W × W) → PMF (List Ct)
  | g, key :: keys, m :: ms =>
    (if g < k then PMF.uniformFintype Ct else PMF.pure (D.encrypt key m.1 m.2)).bind fun c =>
      (epochCtsDist D k (g + 1) keys ms).map (c :: ·)
  | _, _, _ => PMF.pure []

/-- The ciphertexts of the epochs with the FS-AEAD states `sas` and the messages `msgs`, the
first message of global index `g`: the messages of global index below `k` are uniform. -/
noncomputable def ctsDistAll (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (k : ℕ) :
    ℕ → List Sa → List (List (W × W)) → PMF (List (List Ct))
  | g, sa :: sas, ms :: msgs =>
    (epochCtsDist D k g (fsprgRun G ms.length sa).1 ms).bind fun cs =>
      (ctsDistAll G D k (g + ms.length) sas msgs).map (cs :: ·)
  | _, _, _ => PMF.pure []

theorem epochCtsDist_zero (D : AEADDef W Ct) (g : ℕ) (keys : List W) (ms : List (W × W)) :
    epochCtsDist D 0 g keys ms = PMF.pure (encAll D keys ms) := by
  induction keys generalizing g ms with
  | nil => cases ms <;> rfl
  | cons key keys ih =>
    cases ms with
    | nil => rfl
    | cons m ms =>
      simp only [epochCtsDist, Nat.not_lt_zero, ite_false, PMF.pure_bind, ih, PMF.pure_map,
        encAll, List.zipWith_cons_cons]

/-- Without uniform messages the ciphertexts are those of the double ratchet. -/
theorem ctsDistAll_zero (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (g : ℕ) (sas : List Sa)
    (msgs : List (List (W × W))) : ctsDistAll G D 0 g sas msgs = PMF.pure (smCts G D sas msgs) := by
  induction sas generalizing g msgs with
  | nil => cases msgs <;> rfl
  | cons sa sas ih =>
    cases msgs with
    | nil => rfl
    | cons ms msgs =>
      simp only [ctsDistAll, epochCtsDist_zero, PMF.pure_bind, ih, PMF.pure_map, smCts,
        List.zipWith_cons_cons, encEpoch]

/-- Uniform ciphertexts of the epochs `ms :: msgs` are uniform ciphertexts of `ms` and of
`msgs`. -/
def idealCtsCons (ms : List (W × W)) (msgs : List (List (W × W))) (n : ℕ) :
    (Fin ms.length → Ct) × IdealCts Ct msgs n ≃ IdealCts Ct (ms :: msgs) (n + 1) :=
  Fin.consEquiv fun j : Fin (n + 1) => Fin (epochLen (ms :: msgs) j) → Ct

omit [SampleableType W] [SampleableType Ct] in
theorem ctsOf_idealCtsCons (ms : List (W × W)) (msgs : List (List (W × W))) (n : ℕ)
    (x : (Fin ms.length → Ct) × IdealCts Ct msgs n) :
    ctsOf (idealCtsCons ms msgs n x) = List.ofFn x.1 :: ctsOf x.2 := by
  simp only [ctsOf, idealCtsCons, List.ofFn_succ]
  rfl

/-- When every message of the epoch is below the threshold, its ciphertexts are uniform. -/
theorem epochCtsDist_unif (D : AEADDef W Ct) (k g : ℕ) (keys : List W) (ms : List (W × W))
    (hk : g + ms.length ≤ k) (hl : keys.length = ms.length) :
    epochCtsDist D k g keys ms = (PMF.uniformFintype (Fin ms.length → Ct)).map List.ofFn := by
  induction ms generalizing g keys with
  | nil =>
    simp only [List.length_nil]
    rw [show (PMF.uniformFintype (Fin 0 → Ct)).map List.ofFn = PMF.pure [] by
      rw [show (List.ofFn : (Fin 0 → Ct) → List Ct) = fun _ => [] from funext fun _ => rfl]
      exact PMF.map_const _ _]
    cases keys <;> rfl
  | cons m ms ih =>
    cases keys with
    | nil => simp at hl
    | cons key keys =>
      simp only [List.length_cons] at hk hl
      have hg : g < k := by omega
      simp only [epochCtsDist, hg, ite_true, ih (g + 1) keys (by omega) (by omega)]
      rw [List.length_cons, ← PMF.uniformFintype_map_equiv (Fin.consEquiv fun _ => Ct), PMF.map_comp,
        PMF.uniform_prod_eq_bind, PMF.map_bind]
      refine congrArg _ (funext fun c => ?_)
      rw [PMF.map_comp, PMF.map_comp]
      congr 1
      funext v
      simp only [Function.comp_apply]
      exact (ofFn_cons v c).symm

/-- When every message is below the threshold, the ciphertexts of the epochs are uniform. -/
theorem ctsDistAll_unif (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (k g : ℕ) (sas : List Sa)
    (msgs : List (List (W × W))) (hk : g + (msgs.map List.length).sum ≤ k)
    (hl : sas.length = msgs.length) :
    ctsDistAll G D k g sas msgs =
      (PMF.uniformFintype (IdealCts Ct msgs msgs.length)).map ctsOf := by
  induction msgs generalizing g sas with
  | nil =>
    cases sas with
    | nil =>
      simp only [ctsDistAll, List.length_nil]
      rw [show (ctsOf : IdealCts Ct ([] : List (List (W × W))) 0 → List (List Ct)) = fun _ => []
        from funext fun _ => rfl]
      exact (PMF.map_const _ _).symm
    | cons sa sas => simp at hl
  | cons ms msgs ih =>
    cases sas with
    | nil => simp at hl
    | cons sa sas =>
      simp only [List.map_cons, List.sum_cons, List.length_cons] at hk hl
      simp only [ctsDistAll, epochCtsDist_unif D k g _ ms (by omega) (fsprgRun_length G _ sa),
        ih (g + ms.length) sas (by omega) (by omega), List.length_cons]
      rw [← PMF.uniformFintype_map_equiv (idealCtsCons ms msgs msgs.length), PMF.map_comp,
        PMF.uniform_prod_eq_bind, PMF.map_bind, PMF.bind_map]
      refine congrArg _ (funext fun v => ?_)
      rw [Function.comp_apply, PMF.map_comp, PMF.map_comp]
      refine congrArg (fun f => PMF.map f (PMF.uniformFintype (IdealCts Ct msgs msgs.length)))
        (funext fun w => ?_)
      simp only [Function.comp_apply, ctsOf_idealCtsCons]

end PassiveDist

/-! ## The passive adversaries -/

section Passive

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- The CKA message of an answer, or `d`. -/
def SMAns.msgOr (d : Msg) : SMAns Sc Msg RK Sa Ct → Msg
  | .msg T => T
  | _ => d

/-- The ciphertext of an answer, or the default ciphertext. -/
def SMAns.ctOr : SMAns Sc Msg RK Sa Ct → Ct
  | .ct c => c
  | _ => default

/-- The sends of party `P` of the messages `ms`, the first of global index `g`: the messages of
index below `k` are sent and their ciphertexts replaced by uniform ones, the message of index
`k` is the challenge, the others are sent. -/
noncomputable def pasMsgs (k : ℕ) (P : CKAParty) :
    ℕ → List (W × W) → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) (List Ct)
  | _, [] => .ret []
  | g, m :: ms =>
    if g < k then
      .query (.send P m) fun _ => .rand (PMF.uniformFintype Ct) fun c =>
        (pasMsgs k P (g + 1) ms).bind fun cs => .ret (c :: cs)
    else if g = k then
      .query (.chall P m) fun a => (pasMsgs k P (g + 1) ms).bind fun cs => .ret (a.ctOr :: cs)
    else
      .query (.send P m) fun a => (pasMsgs k P (g + 1) ms).bind fun cs => .ret (a.ctOr :: cs)

/-- The epochs `msgs` from the epoch `e`, the first message of global index `g`: the sender
opens the epoch, sends the messages, and the peer receives. The CKA messages and the
ciphertexts are collected. -/
noncomputable def pasEpochs (k : ℕ) (d : Msg) :
    ℕ → ℕ → List (List (W × W)) →
      OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) (List Msg × List (List Ct))
  | _, _, [] => .ret ([], [])
  | e, g, ms :: msgs =>
    .query (.ratchet (ckaSender (e + 1))) fun a =>
      (pasMsgs k (ckaSender (e + 1)) g ms).bind fun cs =>
        .query (.recv (ckaSender (e + 1)).other) fun _ =>
          (pasEpochs k d (e + 1) (g + ms.length) msgs).bind fun r =>
            .ret (a.msgOr d :: r.1, cs :: r.2)

/-- The epoch (counted from `e`) of the message of global index `k`, the first message of the
epochs `msgs` having index `g`. -/
def msgEpoch : ℕ → ℕ → List (List (W × W)) → ℕ → ℕ
  | e, _, [], _ => e
  | e, g, ms :: msgs, k => if k < g + ms.length then e else msgEpoch (e + 1) (g + ms.length) msgs k

/-- The bit of a run of a computation: its output, or `false` if it fails. -/
def optBit : Option (Bool × Heap) → Bool
  | some (b, _) => b
  | none => false

/-- The tree of the passive adversary of the message of global index `k`: the epochs `msgs`,
then the passive distinguisher `A` on the CKA messages and the ciphertexts. -/
noncomputable def smPassiveTreeOf (msgs : List (List (W × W))) (A : SMView Msg Ct → SPComp Bool)
    (k : ℕ) (pub : Msg) : OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool :=
  (pasEpochs k pub 0 0 msgs).bind fun r =>
    .rand (A ((pub, r.1), r.2) Heap.empty) fun o => .ret (optBit o)

derive_timed smPassiveTreeOf

/-- **The passive adversary** of the message of global index `k` against the corruption game:
the challenge epoch is the epoch of the message `k`; it runs the epochs `msgs` with the
messages before `k` replaced by uniform ciphertexts, the challenge at `k` and the messages after
it sent, and runs the passive distinguisher `A` on the CKA messages and the ciphertexts. It never
corrupts. -/
noncomputable def smPassiveAdv (msgs : List (List (W × W))) (A : SMView Msg Ct → SPComp Bool)
    (k : ℕ) : SMCorruptAdv Sc Msg RK Sa W Ct where
  tStar := PMF.pure (msgEpoch 0 0 msgs k + 1)
  play _ pub := smPassiveTreeOf msgs A k pub

/-- The threshold of the uniform messages after the challenge of the message `k`: `k` in the
real game, `k + 1` in the ideal one. -/
def pasThr (ideal : Bool) (k : ℕ) : ℕ := if ideal then k + 1 else k

/-- The part of a state that the passive adversary's later steps depend on. -/
def pasProj {α : Type} (x : α × SMSt Sc Msg RK Sa) :
    α × CKAGameSt Sc Msg × (CKAParty → RK) × Option (RK × Sa) × Bool :=
  (x.1, x.2.ck, x.2.loc.rk, x.2.loc.out, x.2.loc.done)

theorem run_bind_ret {D' R' S α β : Type} (O : S → D' → PMF (R' × S))
    (A : OracleAdv D' R' α) (f : α → β) (s : S) :
    OracleAdv.run O (A.bind fun a => .ret (f a)) s =
      (OracleAdv.run O A s).map fun x => (f x.1, x.2) := by
  rw [OracleAdv.run_bind]
  simp only [OracleAdv.run_ret]
  exact PMF.bind_pure_comp _ _

theorem run_bind_ret_cons {D' R' S α : Type} (O : S → D' → PMF (R' × S))
    (A : OracleAdv D' R' (List α)) (c : α) (s : S) :
    OracleAdv.run O (A.bind fun cs => .ret (c :: cs)) s =
      (OracleAdv.run O A s).map fun x => (c :: x.1, x.2) := by
  rw [OracleAdv.run_bind]
  simp only [OracleAdv.run_ret]
  exact PMF.bind_pure_comp _ _

/-- **The sends of an epoch.** From a state in which party `P` sends in its epoch with the
sending chain `sa`, the run of `pasMsgs` gives the ciphertexts of `epochCtsDist` with the
threshold of the challenge mode; the CKA state, the root keys and the root output in transit
are unchanged, and the challenge flag records whether the message `k` has been reached. -/
theorem pasMsgs_run (C : CKADef Sc Msg Key) [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (root : RK → Key → PMF (RK × Sa)) (k : ℕ) (P : CKAParty) (ms : List (W × W)) (g : ℕ)
    (sa : Sa) (s : SMSt Sc Msg RK Sa) (hsa : s.loc.snd P = some sa)
    (hP : ckaSender (s.ck.t P) = P) (hd : s.loc.done = decide (k < g))
    (ht : g ≤ k → k < g + ms.length → s.ck.t P = t) :
    (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal root) (pasMsgs k P g ms) s).map pasProj =
      (epochCtsDist D (pasThr ideal k) g (fsprgRun G ms.length sa).1 ms).map fun cs =>
        (cs, s.ck, s.loc.rk, s.loc.out, decide (k < g + ms.length)) := by
  induction ms generalizing g sa s with
  | nil =>
    simp only [pasMsgs, OracleAdv.run_ret, PMF.pure_map, pasProj, hd, List.length_nil,
      Nat.add_zero, fsprgRun, epochCtsDist]
  | cons m ms ih =>
    have hP' : (ckaSender (s.ck.t P) == P) = true := by simpa using hP
    have hlen : g + (ms.length + 1) = g + 1 + ms.length := by omega
    have hcont : ∀ (c : Ct) (l : SMLoc RK Sa), l.rk = s.loc.rk → l.out = s.loc.out →
        l.snd P = some (G.stretch sa).2 → l.done = decide (k < g + 1) →
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal root)
          ((pasMsgs k P (g + 1) ms).bind fun cs => .ret (c :: cs)) ⟨s.ck, l⟩).map pasProj =
        (epochCtsDist D (pasThr ideal k) (g + 1) (fsprgRun G ms.length (G.stretch sa).2).1
          ms).map fun cs => (c :: cs, s.ck, s.loc.rk, s.loc.out,
            decide (k < g + (ms.length + 1))) := by
      intro c l hrk hout hsnd hdone
      rw [run_bind_ret_cons, PMF.map_comp]
      have h := ih (g + 1) (G.stretch sa).2 ⟨s.ck, l⟩ hsnd hP hdone
        (fun h1 h2 => ht (by omega) (by simp only [List.length_cons]; omega))
      have hc : (pasProj ∘ fun x : List Ct × SMSt Sc Msg RK Sa => (c :: x.1, x.2)) =
          (fun y => (c :: y.1, y.2)) ∘ pasProj := funext fun _ => rfl
      rw [hc, ← PMF.map_comp, h, PMF.map_comp]
      refine congrArg (fun f => PMF.map f _) (funext fun cs => ?_)
      simp only [Function.comp_apply, hrk, hout, hlen]
    rcases Nat.lt_trichotomy g k with hg | hg | hg
    · have hthr : g < pasThr ideal k := by unfold pasThr; split <;> omega
      simp only [pasMsgs, hg, ite_true, OracleAdv.run_query, OracleAdv.run_rand, smOracleOf,
        hsa, hP', PMF.pure_bind, List.length_cons, fsprgRun_succ, epochCtsDist, hthr, PMF.map_bind]
      refine congrArg _ (funext fun c => ?_)
      rw [hcont c (s.loc.advanced P (G.stretch sa).2) rfl rfl (by simp [SMLoc.advanced])
        (by rw [show (s.loc.advanced P (G.stretch sa).2).done = s.loc.done from rfl, hd]; simp; omega),
        PMF.map_comp]
      rfl
    · subst hg
      have hthr : (g < pasThr ideal g) = ideal := by unfold pasThr; cases ideal <;> simp
      have hok : challOk s.loc t (s.ck.t P) P = true := by
        simp only [challOk, hd, lt_self_iff_false, decide_false, Bool.not_false, hP', Bool.true_and,
          beq_iff_eq]
        exact ht le_rfl (by simp)
      simp only [pasMsgs, lt_self_iff_false, ite_false, ite_true, OracleAdv.run_query, smOracleOf,
        hsa, hok, List.length_cons, fsprgRun_succ, epochCtsDist, PMF.bind_bind, PMF.pure_bind,
        PMF.map_bind]
      have hcc : (if g < pasThr ideal g then PMF.uniformFintype Ct
          else PMF.pure (D.encrypt (G.stretch sa).1 m.1 m.2)) = challCt D ideal (G.stretch sa).1 m := by
        unfold pasThr challCt; cases ideal <;> simp
      rw [hcc]
      refine congrArg _ (funext fun c => ?_)
      simp only [SMAns.ctOr]
      rw [hcont c { s.loc.advanced P (G.stretch sa).2 with done := true } rfl rfl
        (by simp [SMLoc.advanced]) (by simp), PMF.map_comp]
      rfl
    · have hthr : ¬ g < pasThr ideal k := by unfold pasThr; split <;> omega
      have hne : g ≠ k := by omega
      have hng : ¬ g < k := by omega
      simp only [pasMsgs, hng, hne, ite_false, OracleAdv.run_query, smOracleOf, hsa, hP',
        ite_true, PMF.pure_bind, List.length_cons, fsprgRun_succ, epochCtsDist, hthr,
        SMAns.ctOr]
      rw [hcont _ (s.loc.advanced P (G.stretch sa).2) rfl rfl (by simp [SMLoc.advanced])
        (by rw [show (s.loc.advanced P (G.stretch sa).2).done = s.loc.done from rfl, hd]; simp; omega),
        PMF.map_comp]
      rfl

/-- **The epochs of the passive adversary.** From a state after `e` epochs, with both counters
`e`, the next sender in the CKA state `σ₁` and its peer in `σ₂`, the next sender holding the root
key `ρ`, the run of `pasEpochs` gives the CKA messages of a CKA run from `(σ₁, σ₂)` and the
ciphertexts of `ctsDistAll` on the root chain from `ρ`. -/
theorem pasEpochs_run (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (k : ℕ) (d : Msg) (msgs : List (List (W × W)))
    (e g : ℕ) (σ₁ σ₂ : Sc) (ρ : RK) (s : SMSt Sc Msg RK Sa) (hA : s.ck.t .A = e)
    (hB : s.ck.t .B = e) (h1 : s.ck.st (ckaSender (e + 1)) = σ₁)
    (h2 : s.ck.st (ckaSender (e + 1)).other = σ₂) (hρ : s.loc.rk (ckaSender (e + 1)) = ρ)
    (hd : s.loc.done = decide (k < g))
    (ht : g ≤ k → k < g + (msgs.map List.length).sum → t = msgEpoch e g msgs k + 1) :
    (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal (realRoot R)) (pasEpochs k d e g msgs)
        s).map Prod.fst =
      (ckaRunP C msgs.length σ₁ σ₂).bind fun q =>
        (ctsDistAll G D (pasThr ideal k) g (rootRun R ρ (q.1.map Prod.snd)) msgs).map fun cts =>
          (q.1.map Prod.fst, cts) := by
  induction msgs generalizing e g σ₁ σ₂ ρ s with
  | nil =>
    simp only [pasEpochs, OracleAdv.run_ret, PMF.pure_map, List.length_nil, ckaRunP,
      PMF.pure_bind, List.map_nil, rootRun, ctsDistAll]
  | cons ms msgs ih =>
    have hcs : s.ck.canSend (ckaSender (e + 1)) = true := by
      simp [CKAGameSt.canSend, hA, hB]
    have hroot : ∀ I, (if s.ck.t (ckaSender (e + 1)) + 1 == t then
        realRoot R (s.loc.rk (ckaSender (e + 1))) I
        else PMF.pure (R.stretch (s.loc.rk (ckaSender (e + 1)), I))) =
          PMF.pure (R.stretch (ρ, I)) := by
      intro I; simp only [realRoot, ite_self, hρ]
    simp only [pasEpochs, OracleAdv.run_query, smOracleOf, hcs, ite_true, hroot, PMF.bind_bind,
      PMF.pure_bind, PMF.map_bind, List.length_cons, ckaRunP, h1]
    refine congrArg _ (funext fun r => ?_)
    have hP1 : (s.ck.sent (ckaSender (e + 1)) (CKACoins.sendR (C := C) σ₁ r).1
        (CKACoins.sendR (C := C) σ₁ r).2.1).t (ckaSender (e + 1)) = e + 1 := by
      simp only [CKAGameSt.sent_t, ite_true]
      cases h : ckaSender (e + 1)
      · rw [hA]
      · rw [hB]
    have hP2 : (s.ck.sent (ckaSender (e + 1)) (CKACoins.sendR (C := C) σ₁ r).1
        (CKACoins.sendR (C := C) σ₁ r).2.1).t (ckaSender (e + 1)).other = e := by
      simp only [CKAGameSt.sent_t, CKAParty.other_ne, ite_false]
      cases h : ckaSender (e + 1)
      · rw [CKAParty.other_A, hB]
      · rw [CKAParty.other_B, hA]
    have hm := pasMsgs_run C R G D ΔFS ΔPCS t ideal (realRoot R) k (ckaSender (e + 1)) ms g
      (R.stretch (ρ, (CKACoins.sendR (C := C) σ₁ r).2.2)).2
      ⟨s.ck.sent (ckaSender (e + 1)) (CKACoins.sendR (C := C) σ₁ r).1
        (CKACoins.sendR (C := C) σ₁ r).2.1,
        s.loc.opened (ckaSender (e + 1)) (R.stretch (ρ, (CKACoins.sendR (C := C) σ₁ r).2.2))⟩
      (by simp [SMLoc.opened]) (by rw [hP1]) hd (fun h1' h2' => by
        rw [hP1, ht h1' (by simp only [List.map_cons, List.sum_cons]; omega)]
        simp only [msgEpoch, h2', ite_true])
    rw [OracleAdv.run_bind, PMF.map_bind]
    refine (PMF.bind_congr_support _ _ (fun x =>
      ((ckaRunP C msgs.length (C.recv σ₂ (CKACoins.sendR (C := C) σ₁ r).2.1).1
          (CKACoins.sendR (C := C) σ₁ r).1).bind fun q =>
        (ctsDistAll G D (pasThr ideal k) (g + ms.length)
          (rootRun R (R.stretch (ρ, (CKACoins.sendR (C := C) σ₁ r).2.2)).1 (q.1.map Prod.snd))
          msgs).map fun cts => (q.1.map Prod.fst, cts)).map fun r' =>
        ((CKACoins.sendR (C := C) σ₁ r).2.1 :: r'.1, x.1 :: r'.2)) ?_).trans ?_
    · rintro ⟨cs, st⟩ hx
      have hpx := (PMF.mem_support_map_iff pasProj _ _).2 ⟨_, hx, rfl⟩
      rw [hm] at hpx
      simp only [PMF.mem_support_map_iff, pasProj, Prod.mk.injEq] at hpx
      obtain ⟨_, -, -, hck, hrk, hout, hdn⟩ := hpx
      have hcr : st.ck.canRecv (ckaSender (e + 1)).other = true := by
        rw [← hck]
        simp only [CKAGameSt.canRecv, CKAParty.other_other, hP1, hP2, beq_self_eq_true]
      simp only [OracleAdv.run_query, smOracleOf, hcr, ite_true, PMF.pure_bind, SMAns.msgOr]
      rw [run_bind_ret, PMF.map_comp]
      have hrecv : st.loc.received (ckaSender (e + 1)).other =
          st.loc.recvY (ckaSender (e + 1)).other (R.stretch (ρ, (CKACoins.sendR (C := C) σ₁ r).2.2)) := by
        rw [SMLoc.received, ← hout]; rfl
      have hs2 : ckaSender (e + 1 + 1) = (ckaSender (e + 1)).other := ckaSender_succ (e + 1)
      have hcnt : ∀ q, ((s.ck.sent (ckaSender (e + 1)) (CKACoins.sendR (C := C) σ₁ r).1
          (CKACoins.sendR (C := C) σ₁ r).2.1).recvd (ckaSender (e + 1)).other
          (C.recv ((s.ck.sent (ckaSender (e + 1)) (CKACoins.sendR (C := C) σ₁ r).1
            (CKACoins.sendR (C := C) σ₁ r).2.1).st (ckaSender (e + 1)).other)
            (s.ck.sent (ckaSender (e + 1)) (CKACoins.sendR (C := C) σ₁ r).1
              (CKACoins.sendR (C := C) σ₁ r).2.1).msg).1).t q = e + 1 := by
        intro q
        rw [CKAGameSt.recvd_t]
        split
        · rename_i hq; subst hq; rw [hP2]
        · rename_i hq
          have : q = ckaSender (e + 1) := (CKAParty.eq_or_eq_other q _).resolve_right hq
          subst this; exact hP1
      have hih := ih (e + 1) (g + ms.length) (C.recv σ₂ (CKACoins.sendR (C := C) σ₁ r).2.1).1
        (CKACoins.sendR (C := C) σ₁ r).1 (R.stretch (ρ, (CKACoins.sendR (C := C) σ₁ r).2.2)).1
        ⟨st.ck.recvd (ckaSender (e + 1)).other
          (C.recv (st.ck.st (ckaSender (e + 1)).other) st.ck.msg).1,
          st.loc.received (ckaSender (e + 1)).other⟩
        (by rw [← hck]; exact hcnt .A)
        (by rw [← hck]; exact hcnt .B)
        (by rw [hs2, ← hck]; simp [h2])
        (by rw [hs2, ← hck]; simp)
        (by rw [hs2, hrecv]; simp [SMLoc.recvY])
        (by rw [show (st.loc.received (ckaSender (e + 1)).other).done = st.loc.done by
              rw [SMLoc.received]; split <;> rfl, ← hdn])
        (fun h1' h2' => by
          have hnk : ¬ k < g + ms.length := by omega
          rw [ht (by omega) (by simp only [List.map_cons, List.sum_cons]; omega)]
          simp only [msgEpoch, hnk, ite_false])
      have hc : (Prod.fst ∘ fun x : (List Msg × List (List Ct)) × SMSt Sc Msg RK Sa =>
          (((CKACoins.sendR (C := C) σ₁ r).2.1 :: x.1.1, cs :: x.1.2), x.2)) =
          (fun r' => ((CKACoins.sendR (C := C) σ₁ r).2.1 :: r'.1, cs :: r'.2)) ∘ Prod.fst :=
        funext fun _ => rfl
      rw [hc, ← PMF.map_comp, hih]
    · rw [show (fun x : List Ct × SMSt Sc Msg RK Sa =>
          ((ckaRunP C msgs.length (C.recv σ₂ (CKACoins.sendR (C := C) σ₁ r).2.1).1
            (CKACoins.sendR (C := C) σ₁ r).1).bind fun q =>
            (ctsDistAll G D (pasThr ideal k) (g + ms.length)
              (rootRun R (R.stretch (ρ, (CKACoins.sendR (C := C) σ₁ r).2.2)).1
                (q.1.map Prod.snd)) msgs).map fun cts => (q.1.map Prod.fst, cts)).map fun r' =>
            ((CKACoins.sendR (C := C) σ₁ r).2.1 :: r'.1, x.1 :: r'.2)) =
          (fun z : List Ct × CKAGameSt Sc Msg × (CKAParty → RK) × Option (RK × Sa) × Bool =>
          ((ckaRunP C msgs.length (C.recv σ₂ (CKACoins.sendR (C := C) σ₁ r).2.1).1
            (CKACoins.sendR (C := C) σ₁ r).1).bind fun q =>
            (ctsDistAll G D (pasThr ideal k) (g + ms.length)
              (rootRun R (R.stretch (ρ, (CKACoins.sendR (C := C) σ₁ r).2.2)).1
                (q.1.map Prod.snd)) msgs).map fun cts => (q.1.map Prod.fst, cts)).map fun r' =>
            ((CKACoins.sendR (C := C) σ₁ r).2.1 :: r'.1, z.1 :: r'.2)) ∘ pasProj from rfl,
        ← PMF.bind_map, hm, PMF.bind_map]
      simp only [PMF.bind_map, Function.comp_def, List.map_cons, rootRun, ctsDistAll,
        PMF.map_bind, PMF.map_comp]
      rw [PMF.bind_comm]

end Passive

/-! ## The passive game as the instance without corruption -/

section PassiveMain

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Fintype Key] [Nonempty Key] [Fintype Sa]
  [Nonempty Sa]

/-- The views of the passive game with the messages of global index below `k` replaced by
uniform ciphertexts. -/
noncomputable def smPasDist (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (msgs : List (List (W × W))) (k : ℕ) : PMF (SMView Msg Ct) :=
  initP.bind fun i => (ckaRunP C msgs.length i.2.1 i.2.2).bind fun q =>
    (PMF.uniformFintype RK).bind fun rk =>
      (ctsDistAll G D k 0 (rootRun R rk (q.1.map Prod.snd)) msgs).map fun cts =>
        ((i.1, q.1.map Prod.fst), cts)

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] in
theorem sm_real_eq_pas (C : CKADef Sc Msg Key) [CKACoins C Rand] (hS : CKACoins.Sound C)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) :
    sm_real C R G D msgs = liftPMF (smPasDist C initP R G D msgs 0) := by
  unfold sm_real smPasDist
  simp only [hinit, ckaRun_eq_liftPMF C hS, sample_eq_liftPMF, liftPMF_bind_pure,
    liftPMF_bind_liftPMF, ctsDistAll_zero, PMF.pure_map]
  rfl

omit [Fintype RK] [Nonempty RK] [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] in
theorem rootRun_length (R : PRGDef (RK × Key) (RK × Sa)) (rk : RK) (Is : List Key) :
    (rootRun R rk Is).length = Is.length := by
  induction Is generalizing rk with
  | nil => rfl
  | cons I Is ih => simp only [rootRun, List.length_cons, ih]

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] in
theorem sm_ideal_eq_pas (C : CKADef Sc Msg Key) [CKACoins C Rand] (hS : CKACoins.Sound C)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (msgs : List (List (W × W))) :
    sm_ideal C msgs = liftPMF (smPasDist C initP R G D msgs (msgs.map List.length).sum) := by
  unfold sm_ideal ckaPub smPasDist
  simp only [hinit, ckaRun_eq_liftPMF C hS, sample_eq_liftPMF, liftPMF_bind_pure,
    liftPMF_bind_liftPMF]
  congr 1
  rw [PMF.bind_bind]
  refine congrArg _ (funext fun i => ?_)
  rw [PMF.bind_map]
  refine PMF.bind_congr_support _ _ _ fun q hq => ?_
  have hl := ckaRunP_length C msgs.length i.2.1 i.2.2 q hq
  have h : ∀ rk : RK, (ctsDistAll G D (msgs.map List.length).sum 0
      (rootRun R rk (q.1.map Prod.snd)) msgs) =
      (PMF.uniformFintype (IdealCts Ct msgs msgs.length)).map ctsOf := fun rk =>
    ctsDistAll_unif G D _ 0 _ msgs (by omega) (by rw [rootRun_length, List.length_map, hl])
  simp only [h, PMF.bind_const, PMF.map_comp]
  rw [← PMF.bind_pure_comp]
  rfl

theorem outBool_eq_optBit {α : Type} (A : α → SPComp Bool) (a : α) :
    outBool A a = (A a Heap.empty).map optBit := by
  unfold outBool
  congr 1

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] in
/-- **The game of the passive adversary.** The corruption game of `smPassiveAdv msgs A k` with
the challenge mode `ideal` accepts with the probability that `A` accepts on the passive views
with the messages below the threshold `pasThr ideal k` uniform. -/
theorem smPassive_game_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (msgs : List (List (W × W)))
    (A : SMView Msg Ct → SPComp Bool) (k : ℕ) :
    prTrue (sm_corrupt_game C R G D ΔFS ΔPCS ideal (smPassiveAdv msgs A k)) Heap.empty =
      prTrue ((liftPMF (smPasDist C initP R G D msgs (pasThr ideal k))).bind A) Heap.empty := by
  rw [sm_corrupt_game, sm_corrupt_gameOf_eq_liftPMF C initP hinit, prTrue_liftPMF,
    prTrue_liftPMF_bind]
  congr 1
  simp only [smPassiveAdv, smPassiveTreeOf, PMF.pure_bind, smPasDist, PMF.bind_bind]
  refine congrArg _ (funext fun i => ?_)
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun rk => ?_)
  rw [OracleAdv.run_bind, PMF.map_bind]
  simp only [OracleAdv.run_rand, OracleAdv.run_ret]
  have hrun := pasEpochs_run C R G D ΔFS ΔPCS (msgEpoch 0 0 msgs k + 1) ideal k i.1 msgs 0 0
    i.2.1 i.2.2 rk (smInit i rk) rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
  have h : ∀ x : (List Msg × List (List Ct)) × SMSt Sc Msg RK Sa,
      PMF.map Prod.fst (PMF.bind (A ((i.1, x.1.1), x.1.2) Heap.empty) fun o =>
        PMF.pure (optBit o, x.2)) = (A ((i.1, x.1.1), x.1.2) Heap.empty).map optBit := by
    intro x
    rw [PMF.map_bind]
    simp only [PMF.pure_map]
    exact PMF.bind_pure_comp _ _
  simp only [h]
  rw [show (fun x : (List Msg × List (List Ct)) × SMSt Sc Msg RK Sa =>
      (A ((i.1, x.1.1), x.1.2) Heap.empty).map optBit) =
      (fun r : List Msg × List (List Ct) => (A ((i.1, r.1), r.2) Heap.empty).map optBit) ∘
        Prod.fst from rfl, ← PMF.bind_map, hrun]
  simp only [PMF.bind_bind, PMF.bind_map]
  refine congrArg _ (funext fun q => congrArg _ (funext fun cts => ?_))
  simp only [Function.comp_apply, outBool_eq_optBit]

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] in
/-- **The passive secure-messaging game from the game with corruption.** For every passive
distinguisher `A` of the double-ratchet game `sm_real`/`sm_ideal` over the epochs `msgs`, and
any corruption delays, the passive advantage is at most the sum over the messages `k` (in the
order of the epochs) of the advantages with corruption of the adversaries
`smPassiveAdv msgs A k`, which never corrupt: hybrid `k` has the first `k` ciphertexts uniform,
and the adversary of message `k` challenges it. -/
theorem sm_advantage_le_corrupt_passive (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (msgs : List (List (W × W))) (A : SMView Msg Ct → SPComp Bool) :
    SM_Advantage C R G D msgs A ≤
      ∑ k ∈ Finset.range (msgs.map List.length).sum,
        SM_Corrupt_Advantage C R G D ΔFS ΔPCS (smPassiveAdv msgs A k) := by
  unfold SM_Advantage
  rw [sm_real_eq_pas C hS initP hinit R G D msgs, sm_ideal_eq_pas C hS initP hinit R G D msgs]
  refine (HybridArgument.advantage_hybrid_dep (fun k => liftPMF (smPasDist C initP R G D msgs k))
    A _).trans (Finset.sum_le_sum fun k _ => le_of_eq ?_)
  unfold AdvantageA SM_Corrupt_Advantage Advantage
  rw [smPassive_game_eq C initP hinit R G D ΔFS ΔPCS false msgs A k,
    smPassive_game_eq C initP hinit R G D ΔFS ΔPCS true msgs A k]
  simp only [pasThr, Bool.false_eq_true, ite_false, ite_true]

end PassiveMain

/-! ## The game with an adaptive challenge epoch -/

section Adaptive

/-- The record of the game with an adaptive challenge epoch: the epoch of the challenge, once it
has been answered, and the least epoch at which a challenge is allowed after the corruptions
before the challenge. -/
structure SMAdRec where
  /-- The epoch of the answered challenge. -/
  cE : Option ℕ
  /-- The least epoch allowed for the challenge. -/
  lo : ℕ

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- The oracle of the secure-messaging game with an adaptive challenge epoch. The epochs, the
receives and the sends are those of `smOracleOf` with the root KDF `R` at every epoch. The
challenge is answered by the sender of an epoch `e` while its counter is `e`, once, if `e` is at
least `lo`; its epoch is recorded. A corruption before the challenge is always answered and
raises `lo` to `max(t_A, t_B) + ΔPCS` (post-compromise security: a challenge is allowed only
`ΔPCS` epochs after every earlier corruption); a corruption of `P` after a challenge at `e` is
answered if `e + ΔFS ≤ t_P` (forward secrecy). -/
noncomputable def smAdOracle (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (x : SMSt Sc Msg RK Sa × SMAdRec) :
    SMQuery W → PMF (SMAns Sc Msg RK Sa Ct × (SMSt Sc Msg RK Sa × SMAdRec))
  | .ratchet p =>
    (smOracleOf C R G D ΔFS ΔPCS 0 ideal (realRoot R) x.1 (.ratchet p)).map fun y => (y.1, (y.2, x.2))
  | .recv p =>
    (smOracleOf C R G D ΔFS ΔPCS 0 ideal (realRoot R) x.1 (.recv p)).map fun y => (y.1, (y.2, x.2))
  | .send p m =>
    (smOracleOf C R G D ΔFS ΔPCS 0 ideal (realRoot R) x.1 (.send p m)).map fun y =>
      (y.1, (y.2, x.2))
  | .chall p m =>
    match x.1.loc.snd p with
    | some sa =>
      if x.2.cE = none ∧ x.1.loc.done = false ∧ x.2.lo ≤ x.1.ck.t p ∧
          ckaSender (x.1.ck.t p) = p then
        (challCt D ideal (G.stretch sa).1 m).bind fun c =>
          PMF.pure (.ct c, (⟨x.1.ck, { x.1.loc.advanced p (G.stretch sa).2 with done := true }⟩,
            ⟨some (x.1.ck.t p), x.2.lo⟩))
      else PMF.pure (.none, x)
    | none => PMF.pure (.none, x)
  | .corrupt p =>
    match x.2.cE with
    | none =>
      PMF.pure (.state (x.1.ck.st p) (x.1.loc.rk p) (x.1.loc.snd p) (x.1.loc.rcv p),
        (x.1, ⟨none, max x.2.lo (max (x.1.ck.t .A) (x.1.ck.t .B) + ΔPCS)⟩))
    | some e =>
      PMF.pure (if e + ΔFS ≤ x.1.ck.t p then
        .state (x.1.ck.st p) (x.1.loc.rk p) (x.1.loc.snd p) (x.1.loc.rcv p) else .none, x)

variable [Fintype RK] [Nonempty RK]

/-- The secure-messaging game with an adaptive challenge epoch: the CKA is initialised, both
parties get a uniform root key, and the adversary interacts with `smAdOracle`. -/
noncomputable def sm_adaptive_game (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (A : Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) :
    SPComp Bool :=
  SPComp.bind C.init fun i =>
    SPComp.bind (SPComp.sample RK) fun rk =>
      liftPMF ((OracleAdv.run (smAdOracle C R G D ΔFS ΔPCS ideal) (A i.1)
        (smInit i rk, ⟨none, 0⟩)).map Prod.fst)

/-- **Secure-messaging advantage with state corruption and an adaptive challenge epoch.** -/
noncomputable def SM_Adaptive_Advantage (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (A : Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) : ℝ≥0∞ :=
  Advantage (sm_adaptive_game C R G D ΔFS ΔPCS false A) (sm_adaptive_game C R G D ΔFS ΔPCS true A)

end Adaptive

/-! ## The guess of the challenge epoch -/

section Guess

/-- The state of the guessing reduction: the epoch counters (a shadow of the CKA game state),
whether each party holds a sending chain, whether the challenge has been asked, and the record
of the adaptive game. -/
structure GuessSt where
  /-- The epoch counters. -/
  sh : CKAGameSt Unit Unit
  /-- The party holds a sending chain. -/
  hs : CKAParty → Bool
  /-- The challenge has been asked. -/
  dn : Bool
  /-- The record of the adaptive game. -/
  ad : SMAdRec

variable {Sc Msg RK Sa W Ct : Type}

/-- The opening of an epoch in the guessing reduction: forwarded, with the counters and the
sending chain recorded. -/
noncomputable def guessRatchet (w : GuessSt) (p : CKAParty) :
    OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) (SMAns Sc Msg RK Sa Ct × GuessSt) :=
  if w.sh.canSend p then
    .query (.ratchet p) fun a =>
      .ret (a, { w with sh := w.sh.sent p () (), hs := Function.update w.hs p true })
  else .query (.ratchet p) fun a => .ret (a, w)

/-- The receive in the guessing reduction: forwarded, with the counters recorded. -/
noncomputable def guessRecv (w : GuessSt) (p : CKAParty) :
    OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) (SMAns Sc Msg RK Sa Ct × GuessSt) :=
  if w.sh.canRecv p then
    .query (.recv p) fun a => .ret (a, { w with sh := w.sh.recvd p () })
  else .query (.recv p) fun a => .ret (a, w)

/-- The adaptive game answers the challenge of party `p`: no challenge yet, the epoch of `p` is
allowed, `p` sends in its epoch and holds a sending chain. -/
def guessOk (w : GuessSt) (p : CKAParty) : Bool :=
  (w.ad.cE == none) && !w.dn && decide (w.ad.lo ≤ w.sh.t p) && (ckaSender (w.sh.t p) == p) &&
    w.hs p

/-- The challenge in the guessing reduction with the guess `e`: a challenge that the adaptive
game answers is forwarded at the epoch `e`; at another epoch it is recorded and not
answered. -/
noncomputable def guessChall (e : ℕ) (w : GuessSt) (p : CKAParty) (m : W × W) :
    OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) (SMAns Sc Msg RK Sa Ct × GuessSt) :=
  if guessOk w p then
    if w.sh.t p == e then
      .query (.chall p m) fun a => .ret (a, { w with dn := true, ad := ⟨some e, w.ad.lo⟩ })
    else .ret (.none, { w with dn := true, ad := ⟨some (w.sh.t p), w.ad.lo⟩ })
  else .ret (.none, w)

/-- The corruption in the guessing reduction with the guess `e`: before the challenge it is
forwarded if it keeps the epoch `e` allowed, and recorded otherwise; after the challenge it is
forwarded when the adaptive game answers it. -/
noncomputable def guessCorr (ΔFS ΔPCS e : ℕ) (w : GuessSt) (p : CKAParty) :
    OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) (SMAns Sc Msg RK Sa Ct × GuessSt) :=
  match w.ad.cE with
  | none =>
    if max (w.sh.t .A) (w.sh.t .B) + ΔPCS ≤ e then
      .query (.corrupt p) fun a =>
        .ret (a, { w with ad := ⟨none, max w.ad.lo (max (w.sh.t .A) (w.sh.t .B) + ΔPCS)⟩ })
    else .ret (.none, { w with ad := ⟨none, max w.ad.lo (max (w.sh.t .A) (w.sh.t .B) + ΔPCS)⟩ })
  | some e' =>
    if e' + ΔFS ≤ w.sh.t p then .query (.corrupt p) fun a => .ret (a, w)
    else .ret (.none, w)

/-- The simulator of the guessing reduction with the guess `e`. -/
noncomputable def guessImplOf (ΔFS ΔPCS e : ℕ) (w : GuessSt) (q : SMQuery W) :
    OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) (SMAns Sc Msg RK Sa Ct × GuessSt) :=
  match q with
  | .ratchet p => guessRatchet w p
  | .recv p => guessRecv w p
  | .send p m => .query (.send p m) fun a => .ret (a, w)
  | .chall p m => guessChall e w p m
  | .corrupt p => guessCorr ΔFS ΔPCS e w p

/-- The initial state of the guessing reduction. -/
def guessInit : GuessSt := ⟨CKAGameSt.init () () (), fun _ => false, false, ⟨none, 0⟩⟩

/-- **The guessing reduction** as an oracle tree: it runs the adaptive adversary against the
simulator `guessImplOf` and accepts if the adversary accepts and its challenge was at the epoch
`e`. -/
noncomputable def guessTreeOf (ΔFS ΔPCS e : ℕ)
    (A : Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) (pub : Msg) :
    OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool :=
  (OracleAdv.simulate (guessImplOf ΔFS ΔPCS e) (A pub) guessInit).bind fun r =>
    .ret (r.1 && (r.2.ad.cE == some e))

derive_timed guessTreeOf

/-- **The guessing reduction** `smGuessAdv ΔFS ΔPCS A e`: the adversary of the game with an
announced challenge epoch that announces `e`. -/
noncomputable def smGuessAdv (ΔFS ΔPCS : ℕ)
    (A : Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) (e : ℕ) :
    SMCorruptAdv Sc Msg RK Sa W Ct where
  tStar := PMF.pure e
  play _ pub := guessTreeOf ΔFS ΔPCS e A pub

end Guess

/-! ## The guess of the challenge epoch: the simulation -/

section GuessSim

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- The epoch `e` is excluded as the epoch of the challenge: a challenge at another epoch has
been answered, or the corruptions before the challenge exclude `e`. -/
def adBad (e : ℕ) (ad : SMAdRec) : Bool :=
  match ad.cE with
  | none => decide (e < ad.lo)
  | some e' => !(e' == e)

/-- The state of the guessing reduction that mirrors the state `s` with the record `ad`. -/
def guessMir (s : SMSt Sc Msg RK Sa) (ad : SMAdRec) : GuessSt :=
  ⟨ckaShadow s.ck, fun p => (s.loc.snd p).isSome, s.loc.done, ad⟩

/-- The states of the guessing reduction and of the game with announced challenge epoch that a
state of the adaptive game corresponds to. -/
def guessEmb (x : SMSt Sc Msg RK Sa × SMAdRec) : GuessSt × SMSt Sc Msg RK Sa :=
  (guessMir x.1 x.2, x.1)

@[simp] theorem SMLoc.received_snd {RK Sa : Type} (l : SMLoc RK Sa) (p : CKAParty) :
    (l.received p).snd = l.snd := by
  unfold SMLoc.received; split <;> rfl

@[simp] theorem SMLoc.received_done {RK Sa : Type} (l : SMLoc RK Sa) (p : CKAParty) :
    (l.received p).done = l.done := by
  unfold SMLoc.received; split <;> rfl

theorem guessMir_advanced (s : SMSt Sc Msg RK Sa) (ad : SMAdRec) (p : CKAParty) (sa sa' : Sa)
    (h : s.loc.snd p = some sa) :
    guessMir (Sc := Sc) (Msg := Msg) ⟨s.ck, s.loc.advanced p sa'⟩ ad = guessMir s ad := by
  simp only [guessMir, SMLoc.advanced, GuessSt.mk.injEq, and_true, true_and]
  funext q
  by_cases hq : q = p
  · subst hq; simp [h]
  · simp [hq]

/-- With the root KDF at every epoch, the oracle does not depend on the challenge epoch for the
openings of epochs. -/
theorem smOracleOf_realRoot_ratchet (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t t' : ℕ) (ideal : Bool) (s : SMSt Sc Msg RK Sa) (p : CKAParty) :
    smOracleOf C R G D ΔFS ΔPCS t ideal (realRoot R) s (.ratchet p) =
      smOracleOf C R G D ΔFS ΔPCS t' ideal (realRoot R) s (.ratchet p) := by
  simp only [smOracleOf, realRoot, ite_self]

/-- **One step of the guessing reduction.** From a state of the adaptive game in which `e` can
still be the challenge epoch, the simulator against the game with the announced epoch `e`
either answers as the adaptive oracle, with mirrored states, or both lead only to states in
which `e` is excluded as the challenge epoch. -/
theorem guess_step (C : CKADef Sc Msg Key) [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ΔFS ΔPCS e : ℕ)
    (ideal : Bool) (s : SMSt Sc Msg RK Sa) (ad : SMAdRec) (hb : adBad e ad = false)
    (q : SMQuery W) :
    OracleAdv.simOracle (guessImplOf ΔFS ΔPCS e)
        (smOracleOf C R G D ΔFS ΔPCS e ideal (realRoot R)) (guessEmb (s, ad)) q =
      (smAdOracle C R G D ΔFS ΔPCS ideal (s, ad) q).map (Prod.map id guessEmb) ∨
    ((∀ z ∈ (OracleAdv.simOracle (guessImplOf ΔFS ΔPCS e)
        (smOracleOf C R G D ΔFS ΔPCS e ideal (realRoot R)) (guessEmb (s, ad)) q).support,
        adBad e z.2.1.ad = true) ∧
      ∀ z ∈ (smAdOracle C R G D ΔFS ΔPCS ideal (s, ad) q).support, adBad e z.2.2 = true) := by
  cases q with
  | ratchet p =>
    left
    simp only [OracleAdv.simOracle, guessEmb, guessMir, guessImplOf, guessRatchet,
      ckaShadow_canSend, smAdOracle]
    rw [smOracleOf_realRoot_ratchet C R G D ΔFS ΔPCS 0 e]
    by_cases hc : s.ck.canSend p = true
    · simp only [hc, ite_true, OracleAdv.run_query, OracleAdv.run_ret, smOracleOf, PMF.map_bind,
        PMF.bind_bind, PMF.pure_bind, PMF.pure_map, realRoot, ite_self]
      refine congrArg _ (funext fun r => ?_)
      simp only [Prod.map_apply, id_eq, guessEmb, guessMir, ckaShadow_sent, SMLoc.opened]
      congr 4
      funext q
      by_cases hq : q = p
      · subst hq; simp
      · simp [hq]
    · have hc' : s.ck.canSend p = false := by simpa using hc
      simp [hc', OracleAdv.run_query, smOracleOf, PMF.pure_bind, PMF.pure_map, guessEmb,
        guessMir]
  | recv p =>
    left
    simp only [OracleAdv.simOracle, guessEmb, guessMir, guessImplOf, guessRecv,
      ckaShadow_canRecv, smAdOracle]
    by_cases hc : s.ck.canRecv p = true
    · simp [hc, OracleAdv.run_query, smOracleOf, PMF.pure_bind, PMF.pure_map, guessEmb,
        guessMir, ckaShadow_recvd]
    · have hc' : s.ck.canRecv p = false := by simpa using hc
      simp [hc', OracleAdv.run_query, smOracleOf, PMF.pure_bind, PMF.pure_map, guessEmb,
        guessMir]
  | send p m =>
    left
    simp only [OracleAdv.simOracle, guessEmb, guessImplOf, smAdOracle, OracleAdv.run_query,
      OracleAdv.run_ret, PMF.map_bind, PMF.map_comp]
    rw [← PMF.bind_pure_comp]
    simp only [smOracleOf]
    cases hsnd : s.loc.snd p with
    | none => simp [PMF.pure_bind, PMF.pure_map, guessEmb]
    | some sa =>
      by_cases hsd : ckaSender (s.ck.t p) = p
      · simp only [hsd, beq_self_eq_true, ite_true, PMF.pure_bind, PMF.pure_map,
          Function.comp_apply, Prod.map_apply, id_eq, guessEmb]
        rw [guessMir_advanced s ad p sa _ hsnd]
      · have hsd' : (ckaSender (s.ck.t p) == p) = false := by simpa using hsd
        simp [hsd', PMF.pure_bind, PMF.pure_map, guessEmb]
  | chall p m =>
    simp only [OracleAdv.simOracle, guessEmb, guessImplOf, guessChall, smAdOracle]
    cases hsnd : s.loc.snd p with
    | none =>
      left
      have hg : guessOk (guessMir s ad) p = false := by simp [guessOk, guessMir, hsnd]
      simp [hg, PMF.pure_map, guessEmb]
    | some sa =>
      by_cases hok : ad.cE = none ∧ s.loc.done = false ∧ ad.lo ≤ s.ck.t p ∧
          ckaSender (s.ck.t p) = p
      · obtain ⟨hcE, hdone, hlo, hsd⟩ := hok
        have hg : guessOk (guessMir s ad) p = true := by
          simp [guessOk, guessMir, hsnd, hcE, hdone, hlo, hsd, ckaShadow_t]
        dsimp only
        simp only [hcE, hdone, hlo, hsd, and_self, ite_true, hg]
        by_cases ht : s.ck.t p = e
        · left
          have hte : ((guessMir s ad).sh.t p == e) = true := by simp [guessMir, ckaShadow_t, ht]
          have hco : challOk s.loc e (s.ck.t p) p = true := by
            simp only [challOk, hdone, hsd, Bool.not_false, beq_self_eq_true, Bool.true_and,
              beq_iff_eq]
            exact ht
          have hann : smOracleOf C R G D ΔFS ΔPCS e ideal (realRoot R) s (.chall p m) =
              (challCt D ideal (G.stretch sa).1 m).bind fun c =>
                PMF.pure (.ct c, ⟨s.ck, { s.loc.advanced p (G.stretch sa).2 with done := true }⟩) := by
            simp only [smOracleOf, hsnd, hco, ite_true]
          simp only [hte, ite_true, OracleAdv.run_query, OracleAdv.run_ret, hann, PMF.bind_bind,
            PMF.pure_bind, PMF.map_bind, PMF.pure_map]
          refine congrArg _ (funext fun c => ?_)
          simp only [Prod.map_apply, id_eq, guessEmb, guessMir, ht, SMLoc.advanced]
          congr 4
          funext q
          by_cases hq : q = p
          · subst hq; simp [hsnd]
          · simp [hq]
        · right
          have hte : ((guessMir s ad).sh.t p == e) = false := by simp [guessMir, ckaShadow_t, ht]
          simp only [hte, Bool.false_eq_true, ite_false, OracleAdv.run_ret, PMF.pure_map]
          constructor
          · intro z hz
            simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
            subst hz
            simp [adBad, guessMir, ckaShadow_t, ht]
          · intro z hz
            simp only [PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
              at hz
            obtain ⟨c, -, rfl⟩ := hz
            simp [adBad, ht]
      · left
        have hg : guessOk (guessMir s ad) p = false := by
          by_contra h
          have h' : guessOk (guessMir s ad) p = true := by simpa using h
          simp only [guessOk, guessMir, ckaShadow_t, Bool.and_eq_true, Bool.not_eq_true',
            beq_iff_eq] at h'
          exact hok ⟨by simpa using h'.1.1.1.1, h'.1.1.1.2, of_decide_eq_true h'.1.1.2, h'.1.2⟩
        dsimp only
        simp only [hok, ite_false, hg, Bool.false_eq_true, OracleAdv.run_ret, PMF.pure_map,
          Prod.map_apply, id_eq, guessEmb]
  | corrupt p =>
    simp only [OracleAdv.simOracle, guessEmb, guessImplOf, guessCorr, smAdOracle, guessMir,
      ckaShadow_t]
    cases hcE : ad.cE with
    | none =>
      by_cases hm : max (s.ck.t .A) (s.ck.t .B) + ΔPCS ≤ e
      · left
        have hac : ckaAllowCorr ΔFS ΔPCS e s.ck p = true := by simp [ckaAllowCorr, hm]
        simp [hm, hac, OracleAdv.run_query, smOracleOf, PMF.pure_bind, PMF.pure_map, guessEmb,
          guessMir]
      · right
        have hlt : e < max ad.lo (max (s.ck.t .A) (s.ck.t .B) + ΔPCS) := by omega
        simp only [hm, ite_false, OracleAdv.run_ret, PMF.pure_map, PMF.support_pure,
          Set.mem_singleton_iff, forall_eq, adBad, decide_eq_true_eq]
        exact ⟨hlt, hlt⟩
    | some e' =>
      left
      have he : e' = e := by simpa [adBad, hcE] using hb
      subst he
      by_cases hf : e' + ΔFS ≤ s.ck.t p
      · have hac : ckaAllowCorr ΔFS ΔPCS e' s.ck p = true := by simp [ckaAllowCorr, hf]
        simp [hf, hac, OracleAdv.run_query, smOracleOf, PMF.pure_bind, PMF.pure_map, guessEmb,
          guessMir]
      · simp [hf, PMF.pure_map, guessEmb, guessMir]

/-- The adaptive game keeps the exclusion of the epoch `e`. -/
theorem smAd_bad_sticky (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS e : ℕ) (ideal : Bool) (x : SMSt Sc Msg RK Sa × SMAdRec)
    (hx : adBad e x.2 = true) (q : SMQuery W) (z)
    (hz : z ∈ (smAdOracle C R G D ΔFS ΔPCS ideal x q).support) : adBad e z.2.2 = true := by
  cases q with
  | ratchet p =>
    simp only [smAdOracle, PMF.support_map, Set.mem_image] at hz
    obtain ⟨y, -, rfl⟩ := hz; exact hx
  | recv p =>
    simp only [smAdOracle, PMF.support_map, Set.mem_image] at hz
    obtain ⟨y, -, rfl⟩ := hz; exact hx
  | send p m =>
    simp only [smAdOracle, PMF.support_map, Set.mem_image] at hz
    obtain ⟨y, -, rfl⟩ := hz; exact hx
  | chall p m =>
    simp only [smAdOracle] at hz
    split at hz
    · split at hz
      · rename_i hc
        simp only [PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
          at hz
        obtain ⟨c, -, rfl⟩ := hz
        obtain ⟨hcE, -, hlo, -⟩ := hc
        simp only [adBad, hcE, decide_eq_true_eq] at hx
        simp only [adBad, Bool.not_eq_true', beq_eq_false_iff_ne]
        omega
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hx
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hx
  | corrupt p =>
    simp only [smAdOracle] at hz
    split at hz
    · rename_i hcE
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      simp only [adBad, hcE, decide_eq_true_eq] at hx ⊢
      omega
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hx

omit [SampleableType W] [SampleableType Ct] in
/-- The guessing reduction keeps the exclusion of the epoch `e`, whatever it is run against. -/
theorem guess_bad_sticky (ΔFS ΔPCS e : ℕ)
    (O' : SMSt Sc Msg RK Sa → SMQuery W → PMF (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa))
    (x : GuessSt × SMSt Sc Msg RK Sa) (hx : adBad e x.1.ad = true) (q : SMQuery W) (z)
    (hz : z ∈ (OracleAdv.simOracle (guessImplOf ΔFS ΔPCS e) O' x q).support) :
    adBad e z.2.1.ad = true := by
  simp only [OracleAdv.simOracle, PMF.support_map, Set.mem_image] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  cases q with
  | ratchet p =>
    simp only [guessImplOf, guessRatchet] at hy
    split at hy <;>
    · simp only [OracleAdv.run_query, OracleAdv.run_ret, PMF.support_bind, PMF.support_pure,
        Set.mem_iUnion, Set.mem_singleton_iff] at hy
      obtain ⟨a, -, rfl⟩ := hy; exact hx
  | recv p =>
    simp only [guessImplOf, guessRecv] at hy
    split at hy <;>
    · simp only [OracleAdv.run_query, OracleAdv.run_ret, PMF.support_bind, PMF.support_pure,
        Set.mem_iUnion, Set.mem_singleton_iff] at hy
      obtain ⟨a, -, rfl⟩ := hy; exact hx
  | send p m =>
    simp only [guessImplOf, OracleAdv.run_query, OracleAdv.run_ret, PMF.support_bind,
      PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
    obtain ⟨a, -, rfl⟩ := hy; exact hx
  | chall p m =>
    simp only [guessImplOf, guessChall] at hy
    split at hy
    · rename_i hg
      simp only [guessOk, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
        decide_eq_true_eq] at hg
      obtain ⟨⟨⟨⟨hcE, -⟩, hlo⟩, -⟩, -⟩ := hg
      simp only [adBad, hcE, decide_eq_true_eq] at hx
      split at hy
      · rename_i ht
        simp only [beq_iff_eq] at ht
        omega
      · simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
        rw [hy]
        simp only [adBad, Bool.not_eq_true', beq_eq_false_iff_ne]
        omega
    · simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
      rw [hy]; exact hx
  | corrupt p =>
    simp only [guessImplOf, guessCorr] at hy
    split at hy
    · rename_i hcE
      simp only [adBad, hcE, decide_eq_true_eq] at hx
      split at hy
      · simp only [OracleAdv.run_query, OracleAdv.run_ret, PMF.support_bind, PMF.support_pure,
          Set.mem_iUnion, Set.mem_singleton_iff] at hy
        obtain ⟨a, -, rfl⟩ := hy
        simp only [adBad, decide_eq_true_eq]
        omega
      · simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
        rw [hy]
        simp only [adBad, decide_eq_true_eq]
        omega
    · split at hy
      · simp only [OracleAdv.run_query, OracleAdv.run_ret, PMF.support_bind, PMF.support_pure,
          Set.mem_iUnion, Set.mem_singleton_iff] at hy
        obtain ⟨a, -, rfl⟩ := hy; exact hx
      · simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
        rw [hy]; exact hx

/-- **The guessing reduction against the game with the announced epoch `e`.** It accepts with
the probability that the adversary accepts in the adaptive game and its challenge is at the
epoch `e`. -/
theorem guess_run_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS e : ℕ) (ideal : Bool) (A : OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool)
    (s₀ : SMSt Sc Msg RK Sa) :
    ((OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS e ideal (realRoot R))
        ((OracleAdv.simulate (guessImplOf ΔFS ΔPCS e) A (guessMir s₀ ⟨none, 0⟩)).bind fun r =>
          .ret (r.1 && (r.2.ad.cE == some e))) s₀).map Prod.fst) true =
      ((OracleAdv.run (smAdOracle C R G D ΔFS ΔPCS ideal) A (s₀, ⟨none, 0⟩)).map fun z =>
        z.1 && (z.2.2.cE == some e)) true := by
  have hL : (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS e ideal (realRoot R))
      ((OracleAdv.simulate (guessImplOf ΔFS ΔPCS e) A (guessMir s₀ ⟨none, 0⟩)).bind fun r =>
        .ret (r.1 && (r.2.ad.cE == some e))) s₀).map Prod.fst =
      ((OracleAdv.run (OracleAdv.simOracle (guessImplOf ΔFS ΔPCS e)
        (smOracleOf C R G D ΔFS ΔPCS e ideal (realRoot R))) A (guessEmb (s₀, ⟨none, 0⟩))).map
          (Prod.map id fun x : GuessSt × SMSt Sc Msg RK Sa => (x.2, x.1.ad))).map
        fun z : Bool × SMSt Sc Msg RK Sa × SMAdRec => z.1 && (z.2.2.cE == some e) := by
    rw [run_bind_ret, OracleAdv.run_simulate, PMF.map_comp, PMF.map_comp, PMF.map_comp]
    rfl
  rw [hL, PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun z => ?_
  split
  · rename_i hz
    have hbz : adBad e z.2.2 = false := by
      have : (z.2.2.cE == some e) = true := by
        cases h : z.1 <;> simp_all
      simp only [beq_iff_eq] at this
      simp [adBad, this]
    refine OracleAdv.run_map_apply_eq_of_agree (smAdOracle C R G D ΔFS ΔPCS ideal)
      (OracleAdv.simOracle (guessImplOf ΔFS ΔPCS e)
        (smOracleOf C R G D ΔFS ΔPCS e ideal (realRoot R))) (fun x => (x.2, x.1.ad))
      (fun x => adBad e x.2) (fun x => adBad e x.1.ad) (fun x => x.1 = guessMir x.2 x.1.ad)
      (fun _ => rfl) (fun x q hx z hz => smAd_bad_sticky C R G D ΔFS ΔPCS e ideal x hx q z hz)
      (fun x q hx z hz => guess_bad_sticky ΔFS ΔPCS e _ x hx q z hz) ?_ ?_ A _ rfl z hbz
    · intro x q hx hbx y hy hby
      have hxe : x = guessEmb (x.2, x.1.ad) := Prod.ext hx rfl
      rcases guess_step C R G D ΔFS ΔPCS e ideal x.2 x.1.ad hbx q with h | ⟨h1, -⟩
      · rw [hxe, h, PMF.support_map] at hy
        obtain ⟨y', -, rfl⟩ := hy
        rfl
      · rw [hxe] at hy
        rw [h1 y hy] at hby; exact absurd hby (by decide)
    · intro x q hx hbx y hby
      have hxe : x = guessEmb (x.2, x.1.ad) := Prod.ext hx rfl
      rcases guess_step C R G D ΔFS ΔPCS e ideal x.2 x.1.ad hbx q with h | ⟨h1, h2⟩
      · rw [hxe, h, PMF.map_comp]
        rw [show (Prod.map id (fun x : GuessSt × SMSt Sc Msg RK Sa => (x.2, x.1.ad)) ∘
            Prod.map (id : SMAns Sc Msg RK Sa Ct → SMAns Sc Msg RK Sa Ct) guessEmb) = id from
          funext fun _ => rfl, PMF.map_id]
        rfl
      · rw [hxe]
        rw [(PMF.apply_eq_zero_iff _ _).mpr, (PMF.apply_eq_zero_iff _ _).mpr]
        · intro hy
          rw [h2 y hy] at hby; exact absurd hby (by decide)
        · intro hy
          rw [PMF.support_map] at hy
          obtain ⟨y', hy', rfl⟩ := hy
          have := h1 y' hy'
          simp only [Prod.map_snd] at hby
          rw [this] at hby; exact absurd hby (by decide)
  · rfl

/-- The adaptive game keeps the challenge once asked. -/
theorem smAd_chall_sticky (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (x : SMSt Sc Msg RK Sa × SMAdRec)
    (hx : x.2.cE.isSome = true) (q : SMQuery W) (z)
    (hz : z ∈ (smAdOracle C R G D ΔFS ΔPCS ideal x q).support) : z.2.2.cE.isSome = true := by
  cases q with
  | ratchet p =>
    simp only [smAdOracle, PMF.support_map, Set.mem_image] at hz
    obtain ⟨y, -, rfl⟩ := hz; exact hx
  | recv p =>
    simp only [smAdOracle, PMF.support_map, Set.mem_image] at hz
    obtain ⟨y, -, rfl⟩ := hz; exact hx
  | send p m =>
    simp only [smAdOracle, PMF.support_map, Set.mem_image] at hz
    obtain ⟨y, -, rfl⟩ := hz; exact hx
  | chall p m =>
    simp only [smAdOracle] at hz
    split at hz
    · split at hz
      · simp only [PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
          at hz
        obtain ⟨c, -, rfl⟩ := hz
        rfl
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hx
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hx
  | corrupt p =>
    simp only [smAdOracle] at hz
    split at hz
    · rename_i hcE; rw [hcE] at hx; exact absurd hx (by decide)
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hx

/-- **Identical until the challenge.** Without a challenge the two challenge modes of the
adaptive game agree: the probability that the adversary accepts without having been answered a
challenge is the same in both. -/
theorem smAd_nochall_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (A : OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool)
    (s₀ : SMSt Sc Msg RK Sa) :
    ((OracleAdv.run (smAdOracle C R G D ΔFS ΔPCS true) A (s₀, ⟨none, 0⟩)).map fun z =>
        z.1 && z.2.2.cE.isNone) true =
      ((OracleAdv.run (smAdOracle C R G D ΔFS ΔPCS false) A (s₀, ⟨none, 0⟩)).map fun z =>
        z.1 && z.2.2.cE.isNone) true := by
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun z => ?_
  split
  · rename_i hz
    have hbz : z.2.2.cE.isSome = false := by
      cases h : z.2.2.cE <;> simp_all
    have h := OracleAdv.run_map_apply_eq_of_agree (smAdOracle C R G D ΔFS ΔPCS false)
      (smAdOracle C R G D ΔFS ΔPCS true) id (fun x => x.2.cE.isSome) (fun x => x.2.cE.isSome)
      (fun _ => True) (fun _ => rfl)
      (fun x q hx z hz => smAd_chall_sticky C R G D ΔFS ΔPCS false x hx q z hz)
      (fun x q hx z hz => smAd_chall_sticky C R G D ΔFS ΔPCS true x hx q z hz)
      (fun _ _ _ _ _ _ _ => trivial) ?_ A (s₀, ⟨none, 0⟩) trivial z hbz
    · rw [Prod.map_id, PMF.map_id] at h
      exact h
    · intro x q _ hbx y hby
      rw [Prod.map_id, PMF.map_id]
      cases q with
      | chall p m =>
        simp only [id_eq, smAdOracle]
        split
        · split
          · rename_i hc
            rw [(PMF.apply_eq_zero_iff _ _).mpr, (PMF.apply_eq_zero_iff _ _).mpr]
            all_goals
              intro hy
              simp only [PMF.support_bind, PMF.support_pure, Set.mem_iUnion,
                Set.mem_singleton_iff] at hy
              obtain ⟨c, -, rfl⟩ := hy
              simp at hby
          · rfl
        · rfl
      | _ => rfl
  · rfl

/-- The probability that the adversary accepts is the sum over the epochs `e` of the
probability that it accepts with the challenge at `e`, and the probability that it accepts
without a challenge. -/
theorem accept_eq_tsum_chall (P : PMF (Bool × SMSt Sc Msg RK Sa × SMAdRec)) :
    (P.map Prod.fst) true =
      (∑' e : ℕ, (P.map fun z => z.1 && (z.2.2.cE == some e)) true) +
        (P.map fun z => z.1 && z.2.2.cE.isNone) true := by
  simp only [PMF.map_apply]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_add]
  refine tsum_congr fun z => ?_
  rcases z with ⟨b, s, ⟨cE, lo⟩⟩
  cases b with
  | false => simp
  | true =>
    cases cE with
    | none => simp
    | some e₀ =>
      simp only [Bool.true_and, Option.isNone_some]
      rw [tsum_eq_single e₀]
      · simp
      · intro e he
        simp [Ne.symm he]

end GuessSim

/-! ## The horizon of the challenge epoch -/

section Horizon

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- **One epoch per query.** Every oracle call raises every epoch counter by at most one. -/
theorem smOracleOf_t_le_succ (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) (s : SMSt Sc Msg RK Sa)
    (q : SMQuery W) (x) (hx : x ∈ (smOracleOf C R G D ΔFS ΔPCS t ideal root s q).support)
    (P : CKAParty) : x.2.ck.t P ≤ s.ck.t P + 1 := by
  cases q with
  | ratchet p =>
    simp only [smOracleOf] at hx
    split at hx
    · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
        at hx
      obtain ⟨r, -, y, -, rfl⟩ := hx
      by_cases h : P = p <;> simp [h]
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]; exact Nat.le_succ _
  | recv p =>
    simp only [smOracleOf] at hx
    split at hx <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hx <;> rw [hx]
    · by_cases h : P = p <;> simp [h]
    · exact Nat.le_succ _
  | send p m =>
    simp only [smOracleOf] at hx
    split at hx
    · split at hx <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hx <;> rw [hx] <;>
        exact Nat.le_succ _
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]; exact Nat.le_succ _
  | chall p m =>
    simp only [smOracleOf] at hx
    split at hx
    · split at hx
      · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
          at hx
        obtain ⟨c, -, rfl⟩ := hx
        exact Nat.le_succ _
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
        rw [hx]; exact Nat.le_succ _
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]; exact Nat.le_succ _
  | corrupt p =>
    simp only [smOracleOf, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]; exact Nat.le_succ _

/-- Every call of the adaptive oracle raises every epoch counter by at most one. -/
theorem smAdOracle_t_le_succ (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (x : SMSt Sc Msg RK Sa × SMAdRec) (q : SMQuery W) (z)
    (hz : z ∈ (smAdOracle C R G D ΔFS ΔPCS ideal x q).support) (P : CKAParty) :
    z.2.1.ck.t P ≤ x.1.ck.t P + 1 := by
  cases q with
  | ratchet p =>
    simp only [smAdOracle, PMF.support_map, Set.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact smOracleOf_t_le_succ C R G D ΔFS ΔPCS 0 ideal (realRoot R) x.1 _ y hy P
  | recv p =>
    simp only [smAdOracle, PMF.support_map, Set.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact smOracleOf_t_le_succ C R G D ΔFS ΔPCS 0 ideal (realRoot R) x.1 _ y hy P
  | send p m =>
    simp only [smAdOracle, PMF.support_map, Set.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact smOracleOf_t_le_succ C R G D ΔFS ΔPCS 0 ideal (realRoot R) x.1 _ y hy P
  | chall p m =>
    simp only [smAdOracle] at hz
    split at hz
    · split at hz
      · simp only [PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
          at hz
        obtain ⟨c, -, rfl⟩ := hz
        exact Nat.le_succ _
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact Nat.le_succ _
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact Nat.le_succ _
  | corrupt p =>
    simp only [smAdOracle] at hz
    split at hz <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hz <;> rw [hz] <;>
      exact Nat.le_succ _

/-- A call of the adaptive oracle keeps the epoch of the answered challenge, or answers the
challenge at the counter of a party. -/
theorem smAdOracle_cE (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (x : SMSt Sc Msg RK Sa × SMAdRec) (q : SMQuery W) (z)
    (hz : z ∈ (smAdOracle C R G D ΔFS ΔPCS ideal x q).support) (e : ℕ)
    (he : z.2.2.cE = some e) : x.2.cE = some e ∨ ∃ P, e = x.1.ck.t P := by
  cases q with
  | ratchet p =>
    simp only [smAdOracle, PMF.support_map, Set.mem_image] at hz
    obtain ⟨y, -, rfl⟩ := hz; exact Or.inl he
  | recv p =>
    simp only [smAdOracle, PMF.support_map, Set.mem_image] at hz
    obtain ⟨y, -, rfl⟩ := hz; exact Or.inl he
  | send p m =>
    simp only [smAdOracle, PMF.support_map, Set.mem_image] at hz
    obtain ⟨y, -, rfl⟩ := hz; exact Or.inl he
  | chall p m =>
    simp only [smAdOracle] at hz
    split at hz
    · split at hz
      · simp only [PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
          at hz
        obtain ⟨c, -, rfl⟩ := hz
        simp only [Option.some.injEq] at he
        exact Or.inr ⟨p, he.symm⟩
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
        rw [hz] at he; exact Or.inl he
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
      rw [hz] at he; exact Or.inl he
  | corrupt p =>
    simp only [smAdOracle] at hz
    split at hz
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
      rw [hz] at he; exact absurd he (by simp)
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
      rw [hz] at he; exact Or.inl he

/-- **The horizon of the challenge.** In a run of an adversary asking at most `n` queries
against the adaptive oracle, from a state whose epoch counters and answered challenge epoch are
at most `c`, the challenge is answered at an epoch at most `c + n`. -/
theorem smAd_run_cE_le (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) {n : ℕ}
    {A : OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool} (hA : A.IsQueryBound n)
    (x : SMSt Sc Msg RK Sa × SMAdRec) (c : ℕ) (hxt : ∀ P, x.1.ck.t P ≤ c)
    (hxe : ∀ e, x.2.cE = some e → e ≤ c) (z)
    (hz : z ∈ (OracleAdv.run (smAdOracle C R G D ΔFS ΔPCS ideal) A x).support) (e : ℕ)
    (he : z.2.2.cE = some e) : e ≤ c + n := by
  refine (OracleAdv.run_support_level (smAdOracle C R G D ΔFS ΔPCS ideal)
    (fun c x => (∀ P, x.1.ck.t P ≤ c) ∧ ∀ e, x.2.cE = some e → e ≤ c)
    (fun c x hx => ⟨fun P => (hx.1 P).trans (Nat.le_succ c),
      fun e he => (hx.2 e he).trans (Nat.le_succ c)⟩) ?_ hA c x ⟨hxt, hxe⟩ z hz).2 e he
  intro c y q hy w hw
  refine ⟨fun P => ?_, fun e he => ?_⟩
  · have := smAdOracle_t_le_succ C R G D ΔFS ΔPCS ideal y q w hw P
    have := hy.1 P
    omega
  · rcases smAdOracle_cE C R G D ΔFS ΔPCS ideal y q w hw e he with h | ⟨P, rfl⟩
    · exact (hy.2 e h).trans (Nat.le_succ c)
    · exact (hy.1 P).trans (Nat.le_succ c)

end Horizon

/-! ## The adaptive game from the game with an announced challenge epoch -/

section AdaptiveMain

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK]

omit [Fintype RK] [Nonempty RK] in
theorem guessMir_init (i : Msg × Sc × Sc) (rk : RK) :
    guessMir (smInit (Sa := Sa) i rk) ⟨none, 0⟩ = guessInit := by
  simp only [guessMir, smInit, ckaShadow_init, guessInit, SMLoc.init, Option.isSome_none]

/-- The probability that the adaptive game accepts, given the initialisation and the root key. -/
theorem sm_adaptive_game_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (A : Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) :
    prTrue (sm_adaptive_game C R G D ΔFS ΔPCS ideal A) Heap.empty =
      ∑' i, initP i * ∑' rk, PMF.uniformFintype RK rk *
        ((OracleAdv.run (smAdOracle C R G D ΔFS ΔPCS ideal) (A i.1)
          (smInit i rk, ⟨none, 0⟩)).map Prod.fst) true := by
  unfold sm_adaptive_game
  simp only [hinit, sample_eq_liftPMF, liftPMF_bind_liftPMF, prTrue_liftPMF, PMF.bind_apply]

/-- The probability that the game with the announced epoch `e` accepts the guessing reduction,
given the initialisation and the root key. -/
theorem sm_guess_game_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (A : Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool)
    (e : ℕ) :
    prTrue (sm_corrupt_game C R G D ΔFS ΔPCS ideal (smGuessAdv ΔFS ΔPCS A e)) Heap.empty =
      ∑' i, initP i * ∑' rk, PMF.uniformFintype RK rk *
        ((OracleAdv.run (smAdOracle C R G D ΔFS ΔPCS ideal) (A i.1)
          (smInit i rk, ⟨none, 0⟩)).map fun z => z.1 && (z.2.2.cE == some e)) true := by
  rw [sm_corrupt_game, sm_corrupt_gameOf_eq_liftPMF C initP hinit, prTrue_liftPMF]
  simp only [smGuessAdv, PMF.pure_bind, PMF.bind_apply]
  refine tsum_congr fun i => congrArg _ (tsum_congr fun rk => congrArg _ ?_)
  rw [guessTreeOf, ← guessMir_init i rk]
  exact guess_run_eq C R G D ΔFS ΔPCS e ideal (A i.1) (smInit i rk)

/-- **The adaptive challenge epoch from the announced one.** For every adversary `A` of the
game with an adaptive challenge epoch, the advantage is at most the sum over the epochs `e` of
the advantages, in the game with the announced challenge epoch, of the guessing reductions
`smGuessAdv ΔFS ΔPCS A e`. -/
theorem sm_adaptive_advantage_le (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (A : Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) :
    SM_Adaptive_Advantage C R G D ΔFS ΔPCS A ≤
      ∑' e, SM_Corrupt_Advantage C R G D ΔFS ΔPCS (smGuessAdv ΔFS ΔPCS A e) := by
  set X : Bool → (Msg × Sc × Sc) → RK → PMF (Bool × SMSt Sc Msg RK Sa × SMAdRec) := fun b i rk =>
    OracleAdv.run (smAdOracle C R G D ΔFS ΔPCS b) (A i.1) (smInit i rk, ⟨none, 0⟩)
  have hP : ∀ b, prTrue (sm_adaptive_game C R G D ΔFS ΔPCS b A) Heap.empty =
      (∑' e, prTrue (sm_corrupt_game C R G D ΔFS ΔPCS b (smGuessAdv ΔFS ΔPCS A e)) Heap.empty) +
        ∑' i, initP i * ∑' rk, PMF.uniformFintype RK rk *
          ((X b i rk).map fun z => z.1 && z.2.2.cE.isNone) true := by
    intro b
    rw [sm_adaptive_game_eq C initP hinit]
    simp only [sm_guess_game_eq C initP hinit]
    simp only [X, accept_eq_tsum_chall, mul_add, ENNReal.tsum_add]
    congr 1
    simp_rw [← ENNReal.tsum_mul_left]
    conv_lhs => arg 1; ext i; rw [ENNReal.tsum_comm]
    rw [ENNReal.tsum_comm]
  have hc : (∑' i, initP i * ∑' rk, PMF.uniformFintype RK rk *
        ((X true i rk).map fun z => z.1 && z.2.2.cE.isNone) true) =
      ∑' i, initP i * ∑' rk, PMF.uniformFintype RK rk *
        ((X false i rk).map fun z => z.1 && z.2.2.cE.isNone) true := by
    refine tsum_congr fun i => congrArg _ (tsum_congr fun rk => congrArg _ ?_)
    exact smAd_nochall_eq C R G D ΔFS ΔPCS (A i.1) (smInit i rk)
  have key : ∀ (a b : ℕ → ℝ≥0∞) (c : ℝ≥0∞),
      ((∑' e, a e) + c) - ((∑' e, b e) + c) ≤ ∑' e, ((a e - b e) ⊔ (b e - a e)) := by
    intro a b c
    rw [tsub_le_iff_right]
    calc (∑' e, a e) + c ≤ (∑' e, ((a e - b e) ⊔ (b e - a e) + b e)) + c := by
          gcongr with e
          exact le_tsub_add.trans (add_le_add le_sup_left le_rfl)
      _ = (∑' e, ((a e - b e) ⊔ (b e - a e))) + ((∑' e, b e) + c) := by
          rw [ENNReal.tsum_add, add_assoc]
  unfold SM_Adaptive_Advantage SM_Corrupt_Advantage Advantage
  rw [hP false, hP true, hc]
  refine sup_le ?_ ?_
  · exact key _ _ _
  · refine (key _ _ _).trans (le_of_eq (tsum_congr fun e => ?_))
    exact sup_comm _ _

/-- **The horizon of the guess.** For an adversary asking at most `q` queries, the guessing
reduction at an epoch `e > q` never wins the game with the announced epoch `e`: the adaptive
game answers the challenge at the counter of a party, and every query raises each counter by
at most one. -/
theorem sm_guess_game_eq_zero_of_lt (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) {q e : ℕ}
    (A : Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool)
    (hA : ∀ T, (A T).IsQueryBound q) (he : q < e) :
    prTrue (sm_corrupt_game C R G D ΔFS ΔPCS ideal (smGuessAdv ΔFS ΔPCS A e)) Heap.empty = 0 := by
  rw [sm_guess_game_eq C initP hinit]
  refine ENNReal.tsum_eq_zero.mpr fun i => mul_eq_zero_of_right _ ?_
  refine ENNReal.tsum_eq_zero.mpr fun rk => mul_eq_zero_of_right _ ?_
  rw [PMF.map_apply]
  refine ENNReal.tsum_eq_zero.mpr fun z => ?_
  split
  · rename_i hz
    refine (PMF.apply_eq_zero_iff _ _).mpr fun hzs => ?_
    have hcE : z.2.2.cE = some e := by
      have h := hz.symm
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.2
    have h0t : ∀ P, (smInit (Sa := Sa) i rk, (⟨none, 0⟩ : SMAdRec)).1.ck.t P ≤ 0 := fun P =>
      le_of_eq rfl
    have h0e : ∀ e', (smInit (Sa := Sa) i rk, (⟨none, 0⟩ : SMAdRec)).2.cE = some e' → e' ≤ 0 :=
      fun e' h => absurd h (by simp)
    have := smAd_run_cE_le C R G D ΔFS ΔPCS ideal (hA i.1) _ 0 h0t h0e z hzs e hcE
    omega
  · rfl

/-- The guessing reduction at an epoch `e > q` of an adversary asking at most `q` queries has
advantage zero. -/
theorem sm_guess_advantage_eq_zero_of_lt (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) {q e : ℕ} (A : Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool)
    (hA : ∀ T, (A T).IsQueryBound q) (he : q < e) :
    SM_Corrupt_Advantage C R G D ΔFS ΔPCS (smGuessAdv ΔFS ΔPCS A e) = 0 := by
  simp only [SM_Corrupt_Advantage, Advantage,
    sm_guess_game_eq_zero_of_lt C initP hinit R G D ΔFS ΔPCS _ A hA he, tsub_self, max_self]

/-- **The adaptive challenge epoch from the announced one, for an adversary with a query
bound.** For every adversary `A` asking at most `q` queries, the advantage in the game with an
adaptive challenge epoch is at most the sum over the epochs `e ≤ q` of the advantages of the
guessing reductions `smGuessAdv ΔFS ΔPCS A e` (`sm_adaptive_advantage_le`, whose terms vanish
for `e > q` by `sm_guess_advantage_eq_zero_of_lt`). -/
theorem sm_adaptive_advantage_le_of_isQueryBound (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) {q : ℕ} (A : Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool)
    (hA : ∀ T, (A T).IsQueryBound q) :
    SM_Adaptive_Advantage C R G D ΔFS ΔPCS A ≤
      ∑ e ∈ Finset.range (q + 1),
        SM_Corrupt_Advantage C R G D ΔFS ΔPCS (smGuessAdv ΔFS ΔPCS A e) := by
  refine (sm_adaptive_advantage_le C initP hinit R G D ΔFS ΔPCS A).trans (le_of_eq ?_)
  refine tsum_eq_sum fun e he => ?_
  simp only [Finset.mem_range, not_lt] at he
  exact sm_guess_advantage_eq_zero_of_lt C initP hinit R G D ΔFS ΔPCS A hA (by omega)

/-- **Secure messaging with an adaptive challenge epoch from CKA, PRF-PRNG and FS-AEAD
security.** With `2 ≤ ΔFS` and `1 ≤ ΔPCS`, the advantage of every adversary `A` in the game with
an adaptive challenge epoch is at most the sum over the epochs `e` of the bound of
`sm_corrupt_advantage_le` at the guessing reduction `smGuessAdv ΔFS ΔPCS A e`. -/
theorem sm_adaptive_corrupt_advantage_le [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa]
    [DecidableEq RK] [DecidableEq Key] (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (A : Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) :
    SM_Adaptive_Advantage C R G D ΔFS ΔPCS A ≤
      ∑' e, (∑ b : Bool,
          CKA_Corrupt_Advantage C ΔFS ΔPCS (smcCKARed R G D b (smGuessAdv ΔFS ΔPCS A e)) +
        ∑ b : Bool,
          PRFPRNG_Advantage R (smcRootRed C R G D ΔFS ΔPCS b initP (smGuessAdv ΔFS ΔPCS A e)) +
        FSAEAD_Corrupt_Advantage G D (smcFSRed C R G D ΔFS ΔPCS initP (smGuessAdv ΔFS ΔPCS A e))) :=
  (sm_adaptive_advantage_le C initP hinit R G D ΔFS ΔPCS A).trans
    (ENNReal.tsum_le_tsum fun _ => sm_corrupt_advantage_le C hS initP hinit R G D hFS hPCS _)

/-- **Secure messaging with an adaptive challenge epoch, for an adversary with a query bound.**
With `2 ≤ ΔFS` and `1 ≤ ΔPCS`, the advantage of every adversary `A` asking at most `q` queries
in the game with an adaptive challenge epoch is at most the sum over the epochs `e ≤ q` of the
bound of `sm_corrupt_advantage_le` at the guessing reduction `smGuessAdv ΔFS ΔPCS A e`. -/
theorem sm_adaptive_corrupt_advantage_le_of_isQueryBound [Fintype Key] [Nonempty Key]
    [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq Key] (C : CKADef Sc Msg Key)
    [CKACoins C Rand] (hS : CKACoins.Sound C) (initP : PMF (Msg × Sc × Sc))
    (hinit : C.init = liftPMF initP) (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) {q : ℕ}
    (A : Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool)
    (hA : ∀ T, (A T).IsQueryBound q) :
    SM_Adaptive_Advantage C R G D ΔFS ΔPCS A ≤
      ∑ e ∈ Finset.range (q + 1), (∑ b : Bool,
          CKA_Corrupt_Advantage C ΔFS ΔPCS (smcCKARed R G D b (smGuessAdv ΔFS ΔPCS A e)) +
        ∑ b : Bool,
          PRFPRNG_Advantage R (smcRootRed C R G D ΔFS ΔPCS b initP (smGuessAdv ΔFS ΔPCS A e)) +
        FSAEAD_Corrupt_Advantage G D (smcFSRed C R G D ΔFS ΔPCS initP (smGuessAdv ΔFS ΔPCS A e))) :=
  (sm_adaptive_advantage_le_of_isQueryBound C initP hinit R G D ΔFS ΔPCS A hA).trans
    (Finset.sum_le_sum fun _ _ => sm_corrupt_advantage_le C hS initP hinit R G D hFS hPCS _)

end AdaptiveMain

section AdaptiveDH

variable {RK Sa W Ct : Type} [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [Fintype Sa] [Nonempty Sa] [DecidableEq RK] (G : Type) [CG : CyclicGroup G] [DecidableEq G]

/-- **The Diffie–Hellman double ratchet with an adaptive challenge epoch.** With `dhCKA` and
`ΔFS = ΔPCS = 2`, the advantage is at most the sum over the epochs `e` of the DDH advantages of
the CKA reductions, the PRF-PRNG advantages of the root reductions and the FS-AEAD advantage of
the FS-AEAD reduction, all at the guessing reduction `smGuessAdv 2 2 A e`. -/
theorem sm_dh_adaptive_advantage_le (R : PRGDef (RK × G) (RK × Sa)) (F : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (A : G → OracleAdv (SMQuery W) (SMAns (G × CG.Exp) G RK Sa Ct) Bool) :
    SM_Adaptive_Advantage (dhCKA G) R F D 2 2 A ≤
      ∑' e, (∑ b : Bool, DDH_Advantage G
          (ckaCorruptDDHRed (smcCKARed (Rand := CG.Exp) R F D b (smGuessAdv 2 2 A e))) +
        ∑ b : Bool,
          PRFPRNG_Advantage R (smcRootRed (dhCKA G) R F D 2 2 b (dhInitP G) (smGuessAdv 2 2 A e)) +
        FSAEAD_Corrupt_Advantage F D
          (smcFSRed (dhCKA G) R F D 2 2 (dhInitP G) (smGuessAdv 2 2 A e))) :=
  (sm_adaptive_advantage_le (dhCKA G) (dhInitP G) (dhCKA_init_eq G) R F D 2 2 A).trans
    (ENNReal.tsum_le_tsum fun _ => sm_dh_corrupt_advantage_le G R F D _)

/-- **The Diffie–Hellman double ratchet with the HKDF-shaped root step and an adaptive challenge
epoch**, from DDH, the dual-PRF assumption and FS-AEAD security. -/
theorem sm_dh_hkdf_adaptive_advantage_le (H : RK → G → RK × Sa) (F : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (A : G → OracleAdv (SMQuery W) (SMAns (G × CG.Exp) G RK Sa Ct) Bool) :
    SM_Adaptive_Advantage (dhCKA G) (hkdfRoot H) F D 2 2 A ≤
      ∑' e, (∑ b : Bool, DDH_Advantage G (ckaCorruptDDHRed
            (smcCKARed (Rand := CG.Exp) (hkdfRoot H) F D b (smGuessAdv 2 2 A e))) +
        ∑ b : Bool, (DualPRF_Right_Advantage H (ppRedR H
              (smcRootRed (dhCKA G) (hkdfRoot H) F D 2 2 b (dhInitP G) (smGuessAdv 2 2 A e))) +
            DualPRF_Left_Advantage H (ppRedL (Key := G)
              (smcRootRed (dhCKA G) (hkdfRoot H) F D 2 2 b (dhInitP G) (smGuessAdv 2 2 A e)))) +
        FSAEAD_Corrupt_Advantage F D
          (smcFSRed (dhCKA G) (hkdfRoot H) F D 2 2 (dhInitP G) (smGuessAdv 2 2 A e))) :=
  (sm_adaptive_advantage_le (dhCKA G) (dhInitP G) (dhCKA_init_eq G) (hkdfRoot H) F D 2 2 A).trans
    (ENNReal.tsum_le_tsum fun _ => sm_dh_hkdf_corrupt_advantage_le G H F D _)

/-- **The Diffie–Hellman double ratchet with an adaptive challenge epoch, for an adversary
with a query bound**: the bound of `sm_dh_adaptive_advantage_le` with the sum over the epochs
`e ≤ q`, for an adversary asking at most `q` queries. -/
theorem sm_dh_adaptive_advantage_le_of_isQueryBound (R : PRGDef (RK × G) (RK × Sa))
    (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {q : ℕ}
    (A : G → OracleAdv (SMQuery W) (SMAns (G × CG.Exp) G RK Sa Ct) Bool)
    (hA : ∀ T, (A T).IsQueryBound q) :
    SM_Adaptive_Advantage (dhCKA G) R F D 2 2 A ≤
      ∑ e ∈ Finset.range (q + 1), (∑ b : Bool, DDH_Advantage G
          (ckaCorruptDDHRed (smcCKARed (Rand := CG.Exp) R F D b (smGuessAdv 2 2 A e))) +
        ∑ b : Bool,
          PRFPRNG_Advantage R (smcRootRed (dhCKA G) R F D 2 2 b (dhInitP G) (smGuessAdv 2 2 A e)) +
        FSAEAD_Corrupt_Advantage F D
          (smcFSRed (dhCKA G) R F D 2 2 (dhInitP G) (smGuessAdv 2 2 A e))) :=
  (sm_adaptive_advantage_le_of_isQueryBound (dhCKA G) (dhInitP G) (dhCKA_init_eq G) R F D 2 2 A
    hA).trans (Finset.sum_le_sum fun _ _ => sm_dh_corrupt_advantage_le G R F D _)

/-- **The Diffie–Hellman double ratchet with the HKDF-shaped root step and an adaptive challenge
epoch, for an adversary with a query bound**: the bound of `sm_dh_hkdf_adaptive_advantage_le`
with the sum over the epochs `e ≤ q`, for an adversary asking at most `q` queries. -/
theorem sm_dh_hkdf_adaptive_advantage_le_of_isQueryBound (H : RK → G → RK × Sa)
    (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {q : ℕ}
    (A : G → OracleAdv (SMQuery W) (SMAns (G × CG.Exp) G RK Sa Ct) Bool)
    (hA : ∀ T, (A T).IsQueryBound q) :
    SM_Adaptive_Advantage (dhCKA G) (hkdfRoot H) F D 2 2 A ≤
      ∑ e ∈ Finset.range (q + 1), (∑ b : Bool, DDH_Advantage G (ckaCorruptDDHRed
            (smcCKARed (Rand := CG.Exp) (hkdfRoot H) F D b (smGuessAdv 2 2 A e))) +
        ∑ b : Bool, (DualPRF_Right_Advantage H (ppRedR H
              (smcRootRed (dhCKA G) (hkdfRoot H) F D 2 2 b (dhInitP G) (smGuessAdv 2 2 A e))) +
            DualPRF_Left_Advantage H (ppRedL (Key := G)
              (smcRootRed (dhCKA G) (hkdfRoot H) F D 2 2 b (dhInitP G) (smGuessAdv 2 2 A e)))) +
        FSAEAD_Corrupt_Advantage F D
          (smcFSRed (dhCKA G) (hkdfRoot H) F D 2 2 (dhInitP G) (smGuessAdv 2 2 A e))) :=
  (sm_adaptive_advantage_le_of_isQueryBound (dhCKA G) (dhInitP G) (dhCKA_init_eq G) (hkdfRoot H)
    F D 2 2 A hA).trans (Finset.sum_le_sum fun _ _ => sm_dh_hkdf_corrupt_advantage_le G H F D _)

end AdaptiveDH

end CatCrypt.Crypto.Messaging
