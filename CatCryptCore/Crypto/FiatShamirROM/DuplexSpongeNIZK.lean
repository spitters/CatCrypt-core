/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.NIZK
public import CatCryptCore.Crypto.FiatShamirROM.DuplexSponge

/-!
# The duplex-sponge Fiat–Shamir transform of a Σ-protocol

The duplex-sponge transform of draft-irtf-cfrg-fiat-shamir-03 of a Σ-protocol `P`, for a
sponge given by its output stream `xof`, the rate `R`, encodings of statements and
commitments, `L` challenge bytes and a challenge decoder `dec`. The prover initialises
the sponge with the session identifier, absorbs the instance and the commitment,
squeezes `L` bytes and decodes the challenge.

**The transform is the strong Fiat–Shamir transform.** `dsProve_eq` and `dsVerify_eq`:
the prover and the verifier are those of `Sigma.nizkProve` and `Sigma.nizkVerify` of
`FiatShamirROM.NIZK` for the oracle `DSParams.oracle`, which decodes the first `L` bytes
of the output on the absorbed string `sid ‖ zeros(R − 32) ‖ encode(x) ‖ encode(a)`.

**The random-oracle model.** The sponge is modelled as a random oracle on absorbed
strings: a lazily sampled table from absorbed strings to `L` uniform bytes.

* Knowledge soundness (`dsKsExtractProb_ge`): the adversary queries the challenge oracle
  at transcripts `(sid, x, a)`, answered by the decoding of the random-oracle bytes at
  the absorbed string. For prefix-free encodings the absorbed strings of distinct
  transcripts are distinct, so the game is the knowledge-soundness game of
  `FiatShamirROM.NIZK` with fresh challenges drawn from the decoding `ν` of uniform
  bytes. If `ν` has the minorant `(1 − β)·uniform`, each of the `qH + 1` queries moves
  the success probability by at most `β`, and the extractor of `ksExtractProb_ge`
  applies with the success probability decreased by `(qH + 1)·β`.
* Zero knowledge (`dsZkReal_le_zkSim`): the transform is the strong Fiat–Shamir
  transform of the Σ-protocol `DSParams.sigmaBytes` whose challenges are the `L` bytes,
  decoded by `dec` before the prover, the verifier and the simulator read them. Its
  random oracle is the random oracle of `L` bytes, its statistical HVZK distance and
  commitment bound are those of `P`, and `zkReal_le_zkSim` applies unchanged.

## Main definitions

* `Step.toPMFWith`, `toOracleWith` — an oracle whose fresh values are drawn from `ν`
* `DSParams`, `DSParams.absorbed`, `DSParams.state`, `DSParams.challenge`,
  `DSParams.oracle`, `dsProve`, `dsVerify` — the duplex-sponge transform
* `dsROStep`, `dsKsAccepts`, `dsKsAdvantage` — the knowledge-soundness game with the
  sponge as a random oracle on absorbed strings
* `DSParams.decB`, `DSParams.sigmaBytes` — the Σ-protocol with byte challenges

## Main results

* `run_toOracleWith_le` — a test of a run with at most `q` queries against fresh values
  from `ν` is at most the test against uniform fresh values plus `q·β`, when every test
  moves by at most `β` from uniform to `ν`
* `challenge_eq_oracle`, `dsProve_eq`, `dsVerify_eq` — the transform is the strong
  Fiat–Shamir transform for `DSParams.oracle`
* `dsKsAdvantage_le` — `dsKsAdvantage A ≤ ksAdvantage A + (qH + 1)·β`
* `dsKsExtractProb_ge` — with `ε = dsKsAdvantage A − (qH + 1)·β`,
  `ε·(ε/(qH + 1) − 1/|Ch|) ≤ ksExtractProb A`
* `minorant_decB_of_decodeUint` — for `dec = e ∘ DecodeUint M` the minorant holds with
  `β = M/256^L`
* `sigmaBytes_nizkProve`, `sigmaBytes_nizkVerify` — the strong Fiat–Shamir transform of
  `sigmaBytes` against the bytes of the sponge is the duplex-sponge transform
* `dsZkReal_le_zkSim` — `zkReal D ≤ zkSim D + qP·δ + qP·(qH + qP)·γ` for the
  transform with byte challenges

## References

* M. Orrù, *Fiat-Shamir transformation*, draft-irtf-cfrg-fiat-shamir-03.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking CatCrypt.Crypto.Constructions.ECBCPRF
open CatCrypt.Crypto.FiatShamirROM.DuplexSponge
open scoped ENNReal

/-! ## Oracles with fresh values from another distribution -/

section Biased

variable {D R S Ch α : Type} [Fintype Ch] [Nonempty Ch]

/-- The distribution of a transition whose fresh value is drawn from `ν`. -/
noncomputable def _root_.CatCrypt.Crypto.OracleForking.Step.toPMFWith (ν : PMF Ch) :
    Step R S Ch → PMF (R × S)
  | .plain p => p
  | .fresh f => ν.map f

/-- The stateful oracle given by the transitions `O`, with fresh values drawn from `ν`. -/
noncomputable def toOracleWith (ν : PMF Ch) (O : S → D → Step R S Ch) :
    S → D → PMF (R × S) :=
  fun s d => (O s d).toPMFWith ν

/-- **Fresh values from a nearly uniform distribution.** If every test with values in
`[0, 1]` has expectation under `ν` at most its uniform expectation plus `β`, then a test
of a run with at most `q` queries against fresh values from `ν` is at most the test of
the run against uniform fresh values plus `q·β`. -/
theorem run_toOracleWith_le (ν : PMF Ch) {β : ℝ≥0∞}
    (hν : ∀ g : Ch → ℝ≥0∞, (∀ c, g c ≤ 1) →
      ∑' c, ν c * g c ≤ ∑' c, PMF.uniformFintype Ch c * g c + β)
    (O : S → D → Step R S Ch) (A : OracleAdv D R α) (q : ℕ) (hA : A.IsQueryBound q)
    (s : S) (F : α × S → ℝ≥0∞) (hF : ∀ y, F y ≤ 1) :
    ∑' y, OracleAdv.run (toOracleWith ν O) A s y * F y ≤
      ∑' y, OracleAdv.run (toOracle O) A s y * F y + q * β := by
  induction A generalizing q s with
  | ret a =>
    simp only [OracleAdv.run_ret, tsum_pure_mul]
    exact le_self_add
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.tsum_bind_mul]
    calc _ ≤ ∑' b, p b * (∑' y, OracleAdv.run (toOracle O) (k b) s y * F y + q * β) :=
          ENNReal.tsum_le_tsum fun b => mul_le_mul_right (ih b q (hA b) s) _
      _ = _ := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    cases q with
    | zero => exact hA.elim
    | succ q =>
      simp only [OracleAdv.run_query, PMF.tsum_bind_mul]
      set Y : R × S → ℝ≥0∞ := fun o =>
        ∑' y, OracleAdv.run (toOracle O) (k o.1) o.2 y * F y with hYdef
      have hY : ∀ o, Y o ≤ 1 := fun o =>
        (ENNReal.tsum_le_tsum fun y => mul_le_of_le_one_right' (hF y)).trans
          (le_of_eq (PMF.tsum_coe _))
      have hstep : ∑' o, toOracleWith ν O s d o * Y o ≤ ∑' o, toOracle O s d o * Y o + β := by
        rcases hO : O s d with p | f
        · simp only [toOracleWith, toOracle, hO, Step.toPMFWith, Step.toPMF]
          exact le_self_add
        · simp only [toOracleWith, toOracle, hO, Step.toPMFWith, Step.toPMF]
          rw [← PMF.tsum_mul_comp_eq_map, ← PMF.tsum_mul_comp_eq_map]
          exact hν _ fun c => hY (f c)
      calc _ ≤ ∑' o, toOracleWith ν O s d o * (Y o + q * β) :=
            ENNReal.tsum_le_tsum fun o => mul_le_mul_right (ih o.1 q (hA o.1) o.2) _
        _ = ∑' o, toOracleWith ν O s d o * Y o + q * β := by
            simp only [mul_add]
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        _ ≤ ∑' o, toOracle O s d o * Y o + β + q * β := add_le_add hstep le_rfl
        _ = _ := by push_cast; ring

end Biased

/-! ## The duplex-sponge transform -/

variable (P : Sigma)

/-- The parameters of the duplex-sponge transform of `P`: the rate, the number of
challenge bytes, the encodings of statements and commitments, and the challenge
decoder. -/
structure DSParams where
  /-- The rate of the sponge in bytes. -/
  R : ℕ
  /-- The number of squeezed challenge bytes. -/
  L : ℕ
  /-- The encoding of statements. -/
  encX : P.Stmt → Bytes
  /-- The encoding of commitments. -/
  encA : P.Com → Bytes
  /-- The challenge decoder. -/
  dec : Bytes → P.Ch

variable {P} (Dp : DSParams P)

namespace DSParams

/-- The absorbed string of the transcript `(sid, x, a)`. -/
def absorbed (k : P.NizkInput SessionId) : Bytes := absorbedTranscript Dp.R Dp.encX Dp.encA k

/-- The sponge state after absorbing the instance `x` and the commitment `a` in the
session `sid`. -/
def state (sid : SessionId) (x : P.Stmt) (a : P.Com) : SpongeState :=
  absorb (Dp.encA a) (absorb (Dp.encX x) (init Dp.R sid.val))

/-- The challenge of the sponge `xof` for the commitment `a` on `x` in the session
`sid`: the decoding of the `L` squeezed bytes. -/
def challenge (xof : Bytes → ℕ → UInt8) (sid : SessionId) (x : P.Stmt) (a : P.Com) : P.Ch :=
  Dp.dec (squeeze xof Dp.L (Dp.state sid x a)).1

/-- The challenge oracle of the transform: the decoding of the first `L` bytes of the
output on the absorbed string. -/
def oracle (xof : Bytes → ℕ → UInt8) (k : P.NizkInput SessionId) : P.Ch :=
  Dp.dec (List.ofFn fun i : Fin Dp.L => xof (Dp.absorbed k) i)

/-- The decoding of `L` bytes given as a function. -/
def decB (b : Fin Dp.L → UInt8) : P.Ch := Dp.dec (List.ofFn b)

end DSParams

/-- The prover of the duplex-sponge transform. -/
def dsProve (xof : Bytes → ℕ → UInt8) (sid : SessionId) (x : P.Stmt) (w : P.Wit)
    (r : P.Rand) : Option P.NizkProof :=
  if P.accept (P.respond x w r (Dp.challenge xof sid x (P.commit x w r))) then
    some (P.commit x w r, P.respond x w r (Dp.challenge xof sid x (P.commit x w r)))
  else none

/-- The verifier of the duplex-sponge transform. -/
def dsVerify (xof : Bytes → ℕ → UInt8) (sid : SessionId) (x : P.Stmt) (π : P.NizkProof) :
    Bool :=
  P.verify x π.1 (Dp.challenge xof sid x π.1) π.2

/-- The challenge read from the sponge is the challenge oracle at the transcript. -/
theorem challenge_eq_oracle (xof : Bytes → ℕ → UInt8) (sid : SessionId) (x : P.Stmt)
    (a : P.Com) : Dp.challenge xof sid x a = Dp.oracle xof (sid, x, a) := by
  rw [DSParams.challenge, DSParams.state, absorb_absorb, squeeze_absorb_init,
    DSParams.oracle, DSParams.absorbed, absorbedTranscript]
  simp only [List.append_assoc]

/-- **The duplex-sponge prover is the strong Fiat–Shamir prover** for the challenge
oracle of the sponge. -/
theorem dsProve_eq (xof : Bytes → ℕ → UInt8) :
    dsProve Dp xof = P.nizkProve (Dp.oracle xof) := by
  funext sid x w r
  simp only [dsProve, Sigma.nizkProve, challenge_eq_oracle]

/-- **The duplex-sponge verifier is the strong Fiat–Shamir verifier** for the challenge
oracle of the sponge. -/
theorem dsVerify_eq (xof : Bytes → ℕ → UInt8) :
    dsVerify Dp xof = P.nizkVerify (Dp.oracle xof) := by
  funext sid x π
  simp only [dsVerify, Sigma.nizkVerify, challenge_eq_oracle]

/-! ## Knowledge soundness with the sponge as a random oracle -/

section Knowledge

variable [DecidableEq P.Stmt]

theorem lookupIn_map_fst {K K' C : Type} [DecidableEq K] [DecidableEq K'] {f : K → K'}
    (hf : Function.Injective f) (l : List (K × C)) (k : K) :
    lookupIn (l.map (Prod.map f id)) (f k) = lookupIn l k := by
  induction l with
  | nil => simp [lookupIn_nil]
  | cons p l ih =>
    rw [List.map_cons, lookupIn_cons, lookupIn_cons, ih]
    simp [hf.eq_iff]

theorem lookupIn_map_snd {K C C' : Type} [DecidableEq K] (g : C → C') (l : List (K × C))
    (k : K) : lookupIn (l.map (Prod.map id g)) k = (lookupIn l k).map g := by
  induction l with
  | nil => simp [lookupIn_nil]
  | cons p l ih =>
    rw [List.map_cons, lookupIn_cons, lookupIn_cons, ih]
    split_ifs <;> simp_all

/-- The sponge as a random oracle on absorbed strings: the table of `L` bytes recorded
at an absorbed string, or `L` fresh uniform bytes recorded there; the answer is their
decoding. -/
noncomputable def dsROStep (l : List (Bytes × (Fin Dp.L → UInt8))) (k : P.NizkInput SessionId) :
    Step P.Ch (List (Bytes × (Fin Dp.L → UInt8))) (Fin Dp.L → UInt8) :=
  match lookupIn l (Dp.absorbed k) with
  | some b => .plain (PMF.pure (Dp.decB b, l))
  | none => .fresh fun b => (Dp.decB b, l ++ [(Dp.absorbed k, b)])

/-- The output proof verifies against the decoding of the bytes recorded at the absorbed
string of its transcript. -/
def dsKsAccepts (y : (SessionId × P.Stmt × P.NizkProof) × List (Bytes × (Fin Dp.L → UInt8))) :
    Bool :=
  match lookupIn y.2 (Dp.absorbed (ksInput y.1)) with
  | some b => P.verify y.1.2.1 y.1.2.2.1 (Dp.decB b) y.1.2.2.2
  | none => false

/-- The probability that the adversary outputs a proof that verifies against the sponge
modelled as a random oracle on absorbed strings. -/
noncomputable def dsKsAdvantage {qH : ℕ} (A : KSAdversary P SessionId qH) : ℝ≥0∞ :=
  (OracleAdv.run (toOracle (dsROStep Dp)) (ksWithVerify A.run) []).toOuterMeasure
    {y | dsKsAccepts Dp y = true}

/-- The random oracle on transcripts with byte values. -/
noncomputable def dsMidStep (l : List (P.NizkInput SessionId × (Fin Dp.L → UInt8)))
    (k : P.NizkInput SessionId) :
    Step P.Ch (List (P.NizkInput SessionId × (Fin Dp.L → UInt8))) (Fin Dp.L → UInt8) :=
  match lookupIn l k with
  | some b => .plain (PMF.pure (Dp.decB b, l))
  | none => .fresh fun b => (Dp.decB b, l ++ [(k, b)])

/-- **The sponge as a random oracle against nearly uniform challenges.** For prefix-free
encodings, if the decoding `ν` of uniform bytes has the minorant `(1 − β)·uniform`, then
the knowledge-soundness advantage against the sponge is at most the advantage in the
game of `FiatShamirROM.NIZK` plus `(qH + 1)·β`. -/
theorem dsKsAdvantage_le (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA) {β : ℝ≥0∞}
    (hβ : ∀ c, (1 - β) * PMF.uniformFintype P.Ch c ≤
      (PMF.uniformFintype (Fin Dp.L → UInt8)).map Dp.decB c)
    {qH : ℕ} (A : KSAdversary P SessionId qH) :
    dsKsAdvantage Dp A ≤ ksAdvantage A + (qH + 1 : ℕ) * β := by
  set ν := (PMF.uniformFintype (Fin Dp.L → UInt8)).map Dp.decB with hνdef
  have hinj : Function.Injective Dp.absorbed := absorbedTranscript_injective Dp.R hX hA
  set f₁ : List (P.NizkInput SessionId × (Fin Dp.L → UInt8)) →
      List (Bytes × (Fin Dp.L → UInt8)) := List.map (Prod.map Dp.absorbed id) with hf₁
  set f₂ : List (P.NizkInput SessionId × (Fin Dp.L → UInt8)) →
      List (P.NizkInput SessionId × P.Ch) := List.map (Prod.map id Dp.decB) with hf₂
  have h₁ : ∀ l k, (toOracle (dsMidStep Dp) l k).map (Prod.map id f₁) =
      toOracle (dsROStep Dp) (f₁ l) k := by
    intro l k
    simp only [toOracle, dsROStep, hf₁, lookupIn_map_fst hinj]
    unfold dsMidStep
    rcases lookupIn l k with _ | b
    · simp [Step.toPMF, PMF.map_comp, Function.comp_def]
    · simp [Step.toPMF, PMF.pure_map]
  have h₂ : ∀ l k, (toOracle (dsMidStep Dp) l k).map (Prod.map id f₂) =
      toOracleWith ν ksStep (f₂ l) k := by
    intro l k
    simp only [toOracle, toOracleWith, ksStep, hf₂, lookupIn_map_snd]
    unfold dsMidStep
    rcases lookupIn l k with _ | b
    · simp [Step.toPMF, Step.toPMFWith, hνdef, PMF.map_comp, Function.comp_def]
    · simp [Step.toPMF, Step.toPMFWith, PMF.pure_map]
  have hev : ∀ y : (SessionId × P.Stmt × P.NizkProof) ×
      List (P.NizkInput SessionId × (Fin Dp.L → UInt8)),
      dsKsAccepts Dp (Prod.map id f₁ y) = ksAccepts (Prod.map id f₂ y) := by
    rintro ⟨y, l⟩
    simp only [dsKsAccepts, ksAccepts, Prod.map_fst, Prod.map_snd, id, hf₁, hf₂,
      lookupIn_map_snd, lookupIn_map_fst hinj]
    rcases lookupIn l (ksInput y) with _ | b <;> rfl
  have hR₁ := OracleAdv.run_map_state _ _ f₁ h₁ (ksWithVerify A.run) []
  have hR₂ := OracleAdv.run_map_state _ _ f₂ h₂ (ksWithVerify A.run) []
  have e₁ : dsKsAdvantage Dp A = (OracleAdv.run (toOracleWith ν ksStep)
      (ksWithVerify A.run) []).toOuterMeasure {y | ksAccepts y = true} := by
    have hpre : (Prod.map id f₁) ⁻¹' {y | dsKsAccepts Dp y = true} =
        (Prod.map id f₂) ⁻¹' {y | ksAccepts y = true} := by
      ext y
      simp [hev y]
    rw [dsKsAdvantage]
    change (OracleAdv.run (toOracle (dsROStep Dp)) (ksWithVerify A.run) (f₁ [])).toOuterMeasure
      _ = _
    rw [← hR₁, PMF.toOuterMeasure_map_apply, hpre, ← PMF.toOuterMeasure_map_apply, hR₂]
    rfl
  have hν : ∀ g : P.Ch → ℝ≥0∞, (∀ c, g c ≤ 1) →
      ∑' c, ν c * g c ≤ ∑' c, PMF.uniformFintype P.Ch c * g c + β := fun g hg =>
    (MLKEM.XOFMatrix.tsum_le_add_of_minorant ν _ β hβ g hg).1
  rw [e₁, ksAdvantage, toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite]
  exact run_toOracleWith_le ν hν ksStep (ksWithVerify A.run) (qH + 1)
    (isQueryBound_ksWithVerify A.run A.isQueryBound) [] _ fun y => by split_ifs <;> simp

/-- **Knowledge soundness of the duplex-sponge transform.** For a special-sound
Σ-protocol, prefix-free encodings and a decoding with the minorant `(1 − β)·uniform`,
every adversary with at most `qH` oracle queries satisfies, with
`ε = dsKsAdvantage A − (qH + 1)·β`,
`ε·(ε/(qH + 1) − 1/|Ch|) ≤ ksExtractProb A`. -/
theorem dsKsExtractProb_ge (hSS : P.SpecialSound) (hX : PrefixFree Dp.encX)
    (hA : PrefixFree Dp.encA) {β : ℝ≥0∞}
    (hβ : ∀ c, (1 - β) * PMF.uniformFintype P.Ch c ≤
      (PMF.uniformFintype (Fin Dp.L → UInt8)).map Dp.decB c)
    {qH : ℕ} (A : KSAdversary P SessionId qH) :
    (dsKsAdvantage Dp A - (qH + 1 : ℕ) * β) *
        ((dsKsAdvantage Dp A - (qH + 1 : ℕ) * β) / ((qH + 1 : ℕ) : ℝ≥0∞) -
          1 / Fintype.card P.Ch) ≤
      ksExtractProb A := by
  have hle : dsKsAdvantage Dp A - (qH + 1 : ℕ) * β ≤ ksAdvantage A :=
    tsub_le_iff_right.mpr (dsKsAdvantage_le Dp hX hA hβ A)
  refine le_trans ?_ (ksExtractProb_ge hSS A)
  gcongr

omit [DecidableEq P.Stmt] in
/-- For the decoder `e ∘ DecodeUint M` with an equivalence `e : Fin M ≃ Ch`, the
decoding of `L` uniform bytes has the minorant `(1 − M/256^L)·uniform`. -/
theorem minorant_decB_of_decodeUint (M : ℕ) [NeZero M] (e : Fin M ≃ P.Ch)
    (hdec : ∀ b, Dp.dec b = e (decodeUint M b)) (c : P.Ch) :
    (1 - (M : ℝ≥0∞) / (256 ^ Dp.L : ℕ)) * PMF.uniformFintype P.Ch c ≤
      (PMF.uniformFintype (Fin Dp.L → UInt8)).map Dp.decB c := by
  have hmap : (PMF.uniformFintype (Fin Dp.L → UInt8)).map Dp.decB =
      (decodeUintDist M Dp.L).map e := by
    rw [decodeUintDist, PMF.map_comp]
    congr 1
    funext b
    simp [DSParams.decB, hdec]
  have hU : PMF.uniformFintype P.Ch c = PMF.uniformFintype (Fin M) (e.symm c) := by
    simp [PMF.uniformFintype_apply, Fintype.card_congr e]
  have hv : ((decodeUintDist M Dp.L).map e) c = decodeUintDist M Dp.L (e.symm c) := by
    rw [PMF.map_apply, tsum_eq_single (e.symm c) fun b hb => by
      rw [ite_eq_right]; rintro rfl; exact hb (e.symm_apply_apply b).symm]
    simp
  rw [hmap, hv, hU]
  exact one_sub_mul_uniform_le_decodeUintDist M Dp.L (e.symm c)

end Knowledge

/-! ## Zero knowledge -/

namespace DSParams

/-- The Σ-protocol `P` with challenges of `L` bytes, decoded by `dec` before the prover,
the verifier, the simulator and the extractor read them. -/
@[reducible] noncomputable def sigmaBytes : Sigma where
  Stmt := P.Stmt
  Wit := P.Wit
  Com := P.Com
  Ch := Fin Dp.L → UInt8
  Resp := P.Resp
  Rand := P.Rand
  SimRand := P.SimRand
  rel := P.rel
  gen := P.gen
  commit := P.commit
  respond x w r b := P.respond x w r (Dp.decB b)
  verify x a b z := P.verify x a (Dp.decB b) z
  simulate x b s := P.simulate x (Dp.decB b) s
  extract x a b z b' z' := P.extract x a (Dp.decB b) z (Dp.decB b') z'
  accept := P.accept

end DSParams

/-- The strong Fiat–Shamir prover of `sigmaBytes` against the bytes of the sponge on the
absorbed strings is the duplex-sponge prover. -/
theorem sigmaBytes_nizkProve (xof : Bytes → ℕ → UInt8) (sid : SessionId) (x : P.Stmt)
    (w : P.Wit) (r : P.Rand) :
    Dp.sigmaBytes.nizkProve (fun k => fun i : Fin Dp.L => xof (Dp.absorbed k) i) sid x w r =
      dsProve Dp xof sid x w r := by
  rw [dsProve_eq]
  rfl

/-- The strong Fiat–Shamir verifier of `sigmaBytes` against the bytes of the sponge on
the absorbed strings is the duplex-sponge verifier. -/
theorem sigmaBytes_nizkVerify (xof : Bytes → ℕ → UInt8) (sid : SessionId) (x : P.Stmt)
    (π : P.NizkProof) :
    Dp.sigmaBytes.nizkVerify (fun k => fun i : Fin Dp.L => xof (Dp.absorbed k) i) sid x π =
      dsVerify Dp xof sid x π := by
  rw [dsVerify_eq]
  rfl

theorem statHVZKAt_sigmaBytes {x : P.Stmt} {w : P.Wit} {δ : ℝ≥0∞}
    (h : P.StatHVZKAt x w δ) : Dp.sigmaBytes.StatHVZKAt x w δ :=
  fun b g hg hrb => h (Dp.decB b) g hg hrb

theorem commitBoundAt_sigmaBytes {x : P.Stmt} {w : P.Wit} {γ : ℝ≥0∞}
    (h : P.CommitBoundAt x w γ) : Dp.sigmaBytes.CommitBoundAt x w γ :=
  h

/-- **Zero knowledge of the duplex-sponge transform.** For a Σ-protocol with statistical
HVZK distance `δ` and commitment bound `γ` at every pair of the relation, and every
distinguisher with at most `qH` random-oracle and `qP` proving queries against the
transform with byte challenges, `zkReal D ≤ zkSim D + qP·δ + qP·(qH + qP)·γ`. -/
theorem dsZkReal_le_zkSim [DecidableEq P.Stmt] {δ γ : ℝ≥0∞}
    (hZK : ∀ x w, P.rel x w → P.StatHVZKAt x w δ)
    (hγ : ∀ x w, P.rel x w → P.CommitBoundAt x w γ) {qH qP : ℕ}
    (Dz : ZKDistinguisher Dp.sigmaBytes SessionId qH qP) :
    zkReal Dz ≤ zkSim Dz + (qP * δ + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ) :=
  zkReal_le_zkSim (fun x w hxw => statHVZKAt_sigmaBytes Dp (hZK x w hxw))
    (fun x w hxw => commitBoundAt_sigmaBytes Dp (hγ x w hxw)) Dz

end CatCrypt.Crypto.FiatShamirROM
