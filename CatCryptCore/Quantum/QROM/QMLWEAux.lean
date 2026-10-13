/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QIndcpaAux
public import CatCryptCore.Crypto.MLKEM.CompressedPKE
public import CatCryptCore.NonUniform.Bernoulli

/-!
# Module-LWE against quantum distinguishers with oracle access

The IND-CPA game with oracle access `qIndcpaAux` of
`Quantum/QROM/QIndcpaAux.lean` is bounded, at the ML-KEM-512 K-PKE with
compressed ciphertexts, by module-LWE and extended module-LWE advantages of
quantum distinguishers that receive the same auxiliary oracles.

Averaged over the challenger's tables, the acceptance probability of an
IND-CPA distinguisher is a `[0, 1]`-valued function `indView` of its classical
view: the public key, its coins and the challenge ciphertext. The four game
hops of `MLWE_PKE_Stateful.main_theorem_st` hold for every such function
(`cpaExp_absDiff_le`); the proof applies them to the classical adversary
`bernAdv`, whose second stage outputs `1` with probability `v`. Each term of the
bound is then the advantage of a quantum reduction that computes a classical
view transform of its sample and runs the distinguisher once.

## Main definitions

* `sdExp d g` — the expectation of `g` under the sub-distribution `d`
* `mlweSample B b`, `extSample B b` — the module-LWE sample `(A, t)` and the
  extended sample `(A, t, u, v)`, real at `b = false` and uniform at `b = true`
* `encExp`, `extView` — the view transforms: the expectation of `v` at the
  encryption under a sample `(A, t)`, and at the ciphertext `(u, v + encode m)`
  built from an extended sample
* `cpaExp S msgs v b` — the expectation of `v` at the public key, the coins and
  the challenge ciphertext of the IND-CPA experiment with challenge bit `b`
* `QAuxDist ι X` — a quantum distinguisher on a classical input in `X` with
  coins in `ι` and access to the auxiliary oracles
* `tabAvg5 f` — the uniform average of `f` over the seed and the tables `G`,
  `J`, `Hq`, `T`
* `indView D` — the acceptance probability of an IND-CPA distinguisher `D` as a
  function of its classical view
* `qMLWEAux`, `qMLWEExtAux` — the module-LWE and extended module-LWE advantages
  of a distinguisher with oracle access
* `qRedEnc S D b`, `qRedExt B f D b` — the reductions

## Main results

* `cpaExp_absDiff_le` — the numeric transfer of the four game hops to an
  arbitrary `[0, 1]`-valued function of the view
* `qMLWEAux_qRedEnc`, `qMLWEExtAux_qRedExt` — the advantage of each reduction is
  the corresponding term of the transfer at `indView D`
* `qIndcpaAux_le_qMLWE_mapCiphertext` — the bound at `mapCiphertext (toScheme P) f g`
* `qIndcpaAux_le_qMLWE` — at `mlkem512CompressedScheme`:
  `qIndcpaAux D ≤ qMLWEAux (qRedEnc D true) + qMLWEExtAux (qRedExt D true) +
  qMLWEExtAux (qRedExt D false) + qMLWEAux (qRedEnc D false)`

## Scope

The code of `qRedEnc S D b` on a sample `(A, t)` is one encryption under
`(A, t)` of the message of `D` selected by `b`, with coins it draws, followed
by one run of `D`; the code of `qRedExt B f D b` on `(A, t, u, v)` is the
ciphertext `f (u, v + encode m)`, the compression `f` included, followed by one
run of `D`. Neither draws a table or computes a measurement distribution. The
assumption is module-LWE and extended module-LWE against quantum distinguishers
with the auxiliary oracles of `qIndcpaAux`: `auxOracle` at the public key
`(A, t)` of the sample, built from uniform tables drawn independently of the
sample, the decapsulation answers `decapsHq Hq p` and the value `Hq p` at a
point `p` the distinguisher chooses classically. The adversary `bernAdv` and
the coin `coinPMF` occur in proofs only.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme INDCPAAdversary indcpaGame indcpaAdvantage)
open CatCrypt.Crypto.MLKEM.CompressedPKE (mapCiphertext cpaReduction)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Expectations of a function of the classical view -/

section View

variable {PK SK M C R ι : Type} [Fintype PK] [Fintype SK] [Fintype R] [Fintype ι]

/-- The expectation of `g` under the sub-distribution `d`. -/
def sdExp {α : Type} (d : CatCrypt.Prob.SDistr α) (g : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, d (some x) * g x

/-- The average over the messages' coins `i` and the encryption coins `r` of `v`
at the public key `pk`, the coins and the encryption under `pk` of the message
selected by `b`. -/
def encExp (S : Scheme PK SK M C R) (msgs : PK → ι → M × M) (v : PK → ι → C → ℝ≥0∞)
    (b : Bool) (pk : PK) : ℝ≥0∞ :=
  ∑ i : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ r : R, (Fintype.card R : ℝ≥0∞)⁻¹ *
    v pk i (S.enc pk (if b then (msgs pk i).2 else (msgs pk i).1) r)

/-- The expectation of `v` in the IND-CPA experiment with challenge bit `b`. -/
def cpaExp (S : Scheme PK SK M C R) (msgs : PK → ι → M × M) (v : PK → ι → C → ℝ≥0∞)
    (b : Bool) : ℝ≥0∞ :=
  ∑ ks : PK × SK, S.keygen ks * encExp S msgs v b ks.1

end View

/-! ## The module-LWE samples -/

section Samples

open CatCrypt.Prob

variable (B : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.Params)

/-- The module-LWE sample: `A` uniform, and `t = A * s + e` with short `s`, `e` at
`b = false` and `t` uniform at `b = true`. -/
def mlweSample (b : Bool) : SDistr (B.Mat × B.Vec) := do
  let A ← SDistr.uniform B.Mat
  if b then do
    let u ← SDistr.uniform B.Vec
    pure (A, u)
  else do
    let s ← B.dshort_vec
    let e ← B.dshort_vec
    pure (A, B.vec_add (B.mat_vec_mul A s) e)

/-- The extended module-LWE sample: `A`, `t` uniform, and `u = Aᵀ r + e₁`,
`v = t·r + e₂` with short `r`, `e₁`, `e₂` at `b = false` and `u`, `v` uniform at
`b = true`. -/
def extSample (b : Bool) : SDistr (B.Mat × B.Vec × B.Vec × B.R) := do
  let A ← SDistr.uniform B.Mat
  let t ← SDistr.uniform B.Vec
  if b then do
    let u ← SDistr.uniform B.Vec
    let v ← SDistr.uniform B.R
    pure (A, t, u, v)
  else do
    let r ← B.dshort_vec
    let e1 ← B.dshort_vec2
    let e2 ← B.dshort_R
    pure (A, t, B.vec_add (B.mat_vec_mul (B.mat_transpose A) r) e1,
      B.ring_add (B.vec_dot t r) e2)

/-- The `true`-probability of a bind is the expectation of the `true`-probability
of the continuation. -/
theorem prTrue_bind {α : Type} (d : SDistr α) (k : α → SDistr Bool) :
    CatCrypt.Crypto.MLKEM.prTrue (d >>= k) =
      sdExp d fun x => CatCrypt.Crypto.MLKEM.prTrue (k x) := by
  change (SDistr.bind d k) (some true) = _
  rw [SDistr.bind, PMF.bind_apply, SDistr.tsum_option_eq_add]
  simp only [SDistr.fail_apply_some, mul_zero, zero_add]
  rfl

/-- The module-LWE game is the sample followed by the distinguisher. -/
theorem mlweGame_eq (adv : B.Mat → B.Vec → SDistr Bool) (b : Bool) :
    CatCrypt.Crypto.MLKEM.MLWE.Game B.toParams adv b =
      mlweSample B b >>= fun x => adv x.1 x.2 := by
  cases b <;> simp [CatCrypt.Crypto.MLKEM.MLWE.Game, mlweSample]

/-- The extended module-LWE game is the sample followed by the distinguisher. -/
theorem extGame_eq (adv : B.Mat → B.Vec → B.Vec → B.R → SDistr Bool) (b : Bool) :
    CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.MLWE_Ext_Game B adv b =
      extSample B b >>= fun x => adv x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  cases b <;> simp [CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.MLWE_Ext_Game, extSample]

end Samples

/-! ## The transfer to the module-LWE advantages -/

section Transfer

/-- The coin `CatCrypt.NonUniform.bernoulli p hp` as a total distribution. -/
def coinPMF (p : NNReal) (hp : p ≤ 1) : PMF Bool :=
  (ProbabilityTheory.bernoulliMeasure true false ⟨p, p.coe_nonneg, by exact_mod_cast hp⟩).toPMF

/-- `coinPMF p hp` comes up `true` with probability `p`. -/
theorem coinPMF_true (p : NNReal) (hp : p ≤ 1) : coinPMF p hp true = p := by
  have h := CatCrypt.NonUniform.bernoulli_apply_true p hp
  rwa [CatCrypt.NonUniform.bernoulli, CatCrypt.NonUniform.ofPMF_apply_some] at h

variable {PK SK M C R ι : Type} [Fintype ι] [Nonempty ι]

/-- The classical IND-CPA adversary whose first stage draws coins `i`, outputs the
messages `(msgs pk i).2`, `(msgs pk i).1` and keeps `(pk, i)`, and whose second
stage outputs `1` with probability `v pk i c`. It is a device of the proof of
`cpaExp_absDiff_le`. -/
def bernAdv (msgs : PK → ι → M × M) (v : PK → ι → C → ℝ≥0∞) (hv : ∀ pk i c, v pk i c ≤ 1) :
    INDCPAAdversary PK M C where
  St := PK × ι
  choose pk := (PMF.uniformOfFintype ι).map fun i => ((msgs pk i).2, (msgs pk i).1, (pk, i))
  guess st c := coinPMF (v st.1 st.2 c).toNNReal
    ((ENNReal.toNNReal_mono ENNReal.one_ne_top (hv _ _ _)).trans_eq ENNReal.toNNReal_one)

omit [Fintype ι] [Nonempty ι] in
/-- A value at most `1` is the coercion of its `toNNReal`. -/
theorem coe_toNNReal_of_le_one {v : PK → ι → C → ℝ≥0∞} (hv : ∀ pk i c, v pk i c ≤ 1)
    (pk : PK) (i : ι) (c : C) : ((v pk i c).toNNReal : ℝ≥0∞) = v pk i c :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hv pk i c))

/-- The `true`-probability of the IND-CPA experiment against `bernAdv` is
`cpaExp`. -/
theorem indcpaGame_bernAdv [Fintype PK] [Fintype SK] [Fintype R] [Nonempty R]
    (S : Scheme PK SK M C R) (msgs : PK → ι → M × M) (v : PK → ι → C → ℝ≥0∞)
    (hv : ∀ pk i c, v pk i c ≤ 1) (b : Bool) :
    indcpaGame S (bernAdv msgs v hv) b true = cpaExp S msgs v b := by
  simp only [indcpaGame, bernAdv, Scheme.encDist, PMF.bind_map, PMF.bind_apply, tsum_fintype,
    PMF.uniformOfFintype_apply, Function.comp_apply, coinPMF_true,
    coe_toNNReal_of_le_one hv, cpaExp, encExp]

omit [Fintype ι] [Nonempty ι] in
/-- A total distribution read as a sub-distribution has the same weight at
`some a`. -/
theorem map_some_apply_some {α : Type} (p : PMF α) (a : α) : p.map some (some a) = p a :=
  CatCrypt.NonUniform.ofPMF_apply_some p a

end Transfer

section TransferMLWE

open CatCrypt.Crypto.MLKEM

variable {C ι : Type} [Fintype ι] [Nonempty ι]

/-- The expectation of `v` at the public key `(A, t)`, the coins and the
ciphertext `f (u, v + encode m)` built from the extended sample
`(A, t, u, v)`, averaged over the coins. -/
def extView (B : MLWE_PKE_Basic.Params) (f : MLWE_PKE_Basic.CT B → C)
    (msgs : MLWE_PKE_Basic.PK B → ι → B.PT × B.PT) (v : MLWE_PKE_Basic.PK B → ι → C → ℝ≥0∞)
    (b : Bool) (x : B.Mat × B.Vec × B.Vec × B.R) : ℝ≥0∞ :=
  ∑ i : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ * v (x.1, x.2.1) i
    (f (x.2.2.1, B.ring_add x.2.2.2
      (B.m_encode (if b then (msgs (x.1, x.2.1) i).2 else (msgs (x.1, x.2.1) i).1))))

variable (P : MLWE_PKE_Scheme.Params) (f : MLWE_PKE_Basic.CT P.toBasic → C)
  (g : C → MLWE_PKE_Basic.CT P.toBasic)
  (msgs : MLWE_PKE_Basic.PK P.toBasic → ι → P.PT × P.PT)
  (v : MLWE_PKE_Basic.PK P.toBasic → ι → C → ℝ≥0∞)

/-- The `true`-probability of the first-hop module-LWE reduction of `bernAdv` at
`(A, t)` is `encExp` at `(A, t)`. -/
theorem prTrue_B1_st_bernAdv (hv : ∀ pk i c, v pk i c ≤ 1) (b : Bool) (A : P.Mat) (t : P.Vec) :
    prTrue (MLWE_PKE_Stateful.B1_st P.toBasic
        (FOFromMLWE.choose_st P (cpaReduction f (bernAdv msgs v hv)))
        (FOFromMLWE.guess_st P (cpaReduction f (bernAdv msgs v hv))) b A t) =
      encExp (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) msgs v b (A, t) := by
  simp only [MLWE_PKE_Stateful.B1_st, FOFromMLWE.choose_st, FOFromMLWE.guess_st,
    ← MLWE_PKE_Scheme.encDist_eq, MLWE_PKE_Scheme.sdistr_bind_eq,
    MLWE_PKE_Scheme.sdistr_bind_map_some, prTrue, cpaReduction, bernAdv, Scheme.encDist,
    PMF.bind_map, PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype_apply, Function.comp_apply,
    map_some_apply_some, coinPMF_true, coe_toNNReal_of_le_one hv, encExp, mapCiphertext]

/-- The `true`-probability of the second-hop extended module-LWE reduction of
`bernAdv` at `(A, t, u, v')` is `extView` there. -/
theorem prTrue_B2_ext_st_bernAdv (hv : ∀ pk i c, v pk i c ≤ 1) (b : Bool) (A : P.Mat) (t u : P.Vec) (v' : P.R) :
    prTrue (MLWE_PKE_Stateful.B2_ext_st P.toBasic
        (FOFromMLWE.choose_st P (cpaReduction f (bernAdv msgs v hv)))
        (FOFromMLWE.guess_st P (cpaReduction f (bernAdv msgs v hv))) b A t u v') =
      extView P.toBasic f msgs v b (A, t, u, v') := by
  simp only [MLWE_PKE_Stateful.B2_ext_st, FOFromMLWE.choose_st, FOFromMLWE.guess_st,
    MLWE_PKE_Scheme.sdistr_bind_eq, MLWE_PKE_Scheme.sdistr_bind_map_some, prTrue, cpaReduction,
    bernAdv, PMF.bind_map, PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype_apply,
    Function.comp_apply, map_some_apply_some, coinPMF_true, coe_toNNReal_of_le_one hv, extView]

/-- The numeric transfer: for every `[0, 1]`-valued function `v` of the public key,
the coins and the challenge ciphertext, the distance between the expectations of
`v` in the IND-CPA experiment of `mapCiphertext (toScheme P) f g` at the two
challenge bits is at most the sum of two module-LWE and two extended module-LWE
distances of the expectations of `v` composed with the view transforms
`encExp` and `extView`. -/
theorem cpaExp_absDiff_le (hv : ∀ pk i c, v pk i c ≤ 1) :
    absDiff (cpaExp (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) msgs v true)
        (cpaExp (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) msgs v false) ≤
      absDiff (sdExp (mlweSample P.toBasic false)
          (encExp (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) msgs v true))
        (sdExp (mlweSample P.toBasic true)
          (encExp (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) msgs v true)) +
      absDiff (sdExp (extSample P.toBasic false) (extView P.toBasic f msgs v true))
        (sdExp (extSample P.toBasic true) (extView P.toBasic f msgs v true)) +
      absDiff (sdExp (extSample P.toBasic false) (extView P.toBasic f msgs v false))
        (sdExp (extSample P.toBasic true) (extView P.toBasic f msgs v false)) +
      absDiff (sdExp (mlweSample P.toBasic false)
          (encExp (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) msgs v false))
        (sdExp (mlweSample P.toBasic true)
          (encExp (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) msgs v false)) := by
  have h := CompressedPKE.indcpaAdvantage_mapCiphertext_le_mlwe P f g (bernAdv msgs v hv)
  rw [indcpaAdvantage, MLWE_PKE_Scheme.advantage_pmfGame_eq_absDiff, indcpaGame_bernAdv,
    indcpaGame_bernAdv] at h
  refine h.trans_eq ?_
  simp only [MLWE.advantage, MLWE_PKE_Basic.MLWE_Ext_advantage, mlweGame_eq, extGame_eq,
    prTrue_bind, prTrue_B1_st_bernAdv P f g msgs v hv, prTrue_B2_ext_st_bernAdv P f msgs v hv]
  rfl

end TransferMLWE

/-! ## Quantum distinguishers with oracle access -/

/-- A distinguisher with coins in `ι` on a classical input in `X`: from the input
and its coins, a ciphertext point at which it receives the key and the
decapsulation answers, and from the input, the key and its coins, a multi-round
adversary, the index of the query before which it stops, and the projector whose
outcome `true` is the output `1`. -/
structure QAuxDist (ι X : Type) (m n W q k c a : ℕ) (C K : Type) where
  /-- The ciphertext point of the key and the decapsulation answers. -/
  point : X → ι → C
  /-- The multi-round adversary it runs. -/
  prog : X → K → ι → QAdvMR m n W q k c a
  /-- The query index at which the run stops. -/
  stop : X → K → ι → Fin (flatQ q k q)
  /-- The projector of the final measurement. -/
  final : X → K → ι → Matrix (Fin (m * n * ancW c k W)) (Fin (m * n * ancW c k W)) ℂ
  final_conjTranspose : ∀ x h i, (final x h i)ᴴ = final x h i
  final_mul_self : ∀ x h i, final x h i * final x h i = final x h i

section QGames

variable {m₁ m₂ n W q k c a : ℕ} {PK SK M C R K Hash Z ι X : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [DecidableEq Z] [Fintype K] [Nonempty K]
  [Fintype R] [Fintype C] [DecidableEq C] [DecidableEq Hash] [Fintype ι]
  (S : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- The uniform average of `f` over the seed and the tables `G`, `J`, `Hq`, `T`,
nested in the order of `auxTabAvg`. -/
def tabAvg5 (f : Z → (Fin m₁ → Fin n) → (Fin m₂ → Fin n) → (C → K) → (C → Fin n) → ℝ≥0∞) :
    ℝ≥0∞ :=
  ∑ z : Z, (Fintype.card Z : ℝ≥0∞)⁻¹ *
    ∑ G : Fin m₁ → Fin n, (Fintype.card (Fin m₁ → Fin n) : ℝ≥0∞)⁻¹ *
      ∑ J : Fin m₂ → Fin n, (Fintype.card (Fin m₂ → Fin n) : ℝ≥0∞)⁻¹ *
        ∑ Hq : C → K, (Fintype.card (C → K) : ℝ≥0∞)⁻¹ *
          ∑ T : C → Fin n, (Fintype.card (C → Fin n) : ℝ≥0∞)⁻¹ * f z G J Hq T

variable [NeZero n] [NeZero c]

/-- The probability that `E` with coins `i` on input `x` outputs `1` against the
challenger's tables: `E` receives `x`, its point `p` and `Hq p`, runs against
`auxOracle` at the public key `key x` with decapsulation answers
`decapsHq Hq p` up to its stop index and measures its final projector. -/
def qAuxRun (key : X → PK) (E : QAuxDist ι X (m₁ + m₂) n W q k c a C K) (x : X)
    (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z) (i : ι) :
    ℝ≥0∞ :=
  prOut (truncAdv (toQAdv (E.prog x (Hq (E.point x i)) i) (decapsHq eC eKa Hq (E.point x i)))
      (E.stop x (Hq (E.point x i)) i) (E.final x (Hq (E.point x i)) i)
      (E.final_conjTranspose x (Hq (E.point x i)) i) (E.final_mul_self x (Hq (E.point x i)) i))
    (auxOracle S hpk eG eJ eKR (key x) Hq G J T z)

/-- The probability that `E` outputs `1` on input `x`, its coins, the seed and
the tables uniform. -/
def qAuxAcc (key : X → PK) (E : QAuxDist ι X (m₁ + m₂) n W q k c a C K) (x : X) : ℝ≥0∞ :=
  ∑ i : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ *
    tabAvg5 fun z G J Hq T => qAuxRun S hpk eG eJ eKR eC eKa key E x Hq G J T z i

/-- The acceptance probability of `D` with coins `i` at the public key `pk` and
the challenge ciphertext `cst`, averaged over the seed and the tables. -/
def indView (D : QIndAuxAdv ι (m₁ + m₂) n W q k c a PK C K M) (pk : PK) (i : ι) (cst : C) :
    ℝ≥0∞ :=
  tabAvg5 fun z G J Hq T => qIndcpaAuxRun S hpk eG eJ eKR eC eKa D pk cst Hq G J T z i

omit [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M] [Fintype R]
  [Fintype ι] in
/-- `indView` is at most `1`. -/
theorem indView_le_one [Nonempty Z] (D : QIndAuxAdv ι (m₁ + m₂) n W q k c a PK C K M)
    (pk : PK) (i : ι)
    (cst : C) : indView S hpk eG eJ eKR eC eKa D pk i cst ≤ 1 := by
  have h1 : ∀ {α : Type} [Fintype α] [Nonempty α] (s : α → ℝ≥0∞), (∀ x, s x ≤ 1) →
      ∑ x : α, (Fintype.card α : ℝ≥0∞)⁻¹ * s x ≤ 1 := by
    intro α _ _ s hs
    calc ∑ x : α, (Fintype.card α : ℝ≥0∞)⁻¹ * s x ≤ ∑ _x : α, (Fintype.card α : ℝ≥0∞)⁻¹ * 1 :=
          Finset.sum_le_sum fun x _ => by gcongr; exact hs x
      _ = 1 := sum_inv_mul_const 1
  refine h1 _ fun z => h1 _ fun G => h1 _ fun J => h1 _ fun Hq => h1 _ fun T => ?_
  exact prTrue_Q_le_one _ _

omit [Fintype M] [DecidableEq M] [Nonempty M] in
/-- The IND-CPA advantage with oracle access is the distance of the expectations
of `indView` at the two challenge bits. -/
theorem qIndcpaAux_eq_cpaExp (D : QIndAuxAdv ι (m₁ + m₂) n W q k c a PK C K M) :
    qIndcpaAux S hpk eG eJ eKR eC eKa D =
      absDiff (cpaExp S D.msgs (indView S hpk eG eJ eKR eC eKa D) true)
        (cpaExp S D.msgs (indView S hpk eG eJ eKR eC eKa D) false) := rfl

end QGames

/-! ## The reductions -/

section Reductions

variable {m n W q k c a : ℕ} {PK SK M C R K ι : Type}

/-- The challenge ciphertext of the first-hop reduction: the encryption under
`pk` with coins `x.2` of the message of `D` at coins `x.1` selected by `b`. -/
def encPoint (S : Scheme PK SK M C R) (D : QIndAuxAdv ι m n W q k c a PK C K M) (b : Bool)
    (pk : PK) (x : ι × R) : C :=
  S.enc pk (if b then (D.msgs pk x.1).2 else (D.msgs pk x.1).1) x.2

/-- The first-hop reduction: on a module-LWE sample `pk = (A, t)` and coins
`(i, r)`, it encrypts the message of `D` selected by `b` under `pk` with coins
`r` and runs `D` with coins `i` on `pk` and that ciphertext. -/
def qRedEnc (S : Scheme PK SK M C R) (D : QIndAuxAdv ι m n W q k c a PK C K M) (b : Bool) :
    QAuxDist (ι × R) PK m n W q k c a C K where
  point := encPoint S D b
  prog pk h x := D.prog pk (encPoint S D b pk x) h x.1
  stop pk h x := D.stop pk (encPoint S D b pk x) h x.1
  final pk h x := D.final pk (encPoint S D b pk x) h x.1
  final_conjTranspose pk h x := D.final_conjTranspose pk (encPoint S D b pk x) h x.1
  final_mul_self pk h x := D.final_mul_self pk (encPoint S D b pk x) h x.1

variable (B : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.Params)

/-- The challenge ciphertext of the second-hop reduction: `f (u, v + encode m)`
on an extended sample `(A, t, u, v)`, with `m` the message of `D` at the public
key `(A, t)` and coins `i` selected by `b`. -/
def extPoint (f : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.CT B → C)
    (D : QIndAuxAdv ι m n W q k c a (CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.PK B) C K B.PT)
    (b : Bool) (x : B.Mat × B.Vec × B.Vec × B.R) (i : ι) : C :=
  f (x.2.2.1, B.ring_add x.2.2.2
    (B.m_encode (if b then (D.msgs (x.1, x.2.1) i).2 else (D.msgs (x.1, x.2.1) i).1)))

/-- The second-hop reduction: on an extended sample `(A, t, u, v)` and coins `i`,
it forms the ciphertext `f (u, v + encode m)` of the message of `D` selected by
`b` and runs `D` with coins `i` on the public key `(A, t)` and that ciphertext. -/
def qRedExt (f : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.CT B → C)
    (D : QIndAuxAdv ι m n W q k c a (CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.PK B) C K B.PT)
    (b : Bool) : QAuxDist ι (B.Mat × B.Vec × B.Vec × B.R) m n W q k c a C K where
  point := extPoint B f D b
  prog x h i := D.prog (x.1, x.2.1) (extPoint B f D b x i) h i
  stop x h i := D.stop (x.1, x.2.1) (extPoint B f D b x i) h i
  final x h i := D.final (x.1, x.2.1) (extPoint B f D b x i) h i
  final_conjTranspose x h i := D.final_conjTranspose (x.1, x.2.1) (extPoint B f D b x i) h i
  final_mul_self x h i := D.final_mul_self (x.1, x.2.1) (extPoint B f D b x i) h i

end Reductions

/-! ## The module-LWE games with oracle access -/

section QMLWE

variable {m₁ m₂ n W q k c a : ℕ} {SK C R K Hash Z ι : Type}
  [Fintype Z] [DecidableEq Z] [Fintype K] [Nonempty K] [Fintype C] [DecidableEq C]
  [DecidableEq Hash] [Fintype ι] (B : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.Params)
  (S : Scheme (CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.PK B) SK B.PT C R)
  (hpk : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.PK B → Hash) (eG : (B.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n] [NeZero c]

/-- The module-LWE advantage of a distinguisher `E` with oracle access:
`|Pr[1 | real] - Pr[1 | uniform]|`, where `E` receives the sample `(A, t)` of
`mlweSample` and runs against `auxOracle` at the public key `(A, t)` built from
uniform tables. -/
def qMLWEAux
    (E : QAuxDist ι (CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.PK B) (m₁ + m₂) n W q k c a C K) :
    ℝ≥0∞ :=
  absDiff (sdExp (mlweSample B false) (qAuxAcc S hpk eG eJ eKR eC eKa id E))
    (sdExp (mlweSample B true) (qAuxAcc S hpk eG eJ eKR eC eKa id E))

/-- The extended module-LWE advantage of a distinguisher `E` with oracle access:
`E` receives the sample `(A, t, u, v)` of `extSample` and runs against
`auxOracle` at the public key `(A, t)` built from uniform tables. -/
def qMLWEExtAux (E : QAuxDist ι (B.Mat × B.Vec × B.Vec × B.R) (m₁ + m₂) n W q k c a C K) :
    ℝ≥0∞ :=
  absDiff (sdExp (extSample B false) (qAuxAcc S hpk eG eJ eKR eC eKa (fun x => (x.1, x.2.1)) E))
    (sdExp (extSample B true) (qAuxAcc S hpk eG eJ eKR eC eKa (fun x => (x.1, x.2.1)) E))

variable [Fintype R] (D : QIndAuxAdv ι (m₁ + m₂) n W q k c a
  (CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.PK B) C K B.PT)

/-- The acceptance probability of `qRedEnc S D b` on the public key `pk` is
`encExp` of `indView` at `pk`. -/
theorem qAuxAcc_qRedEnc (b : Bool) :
    qAuxAcc S hpk eG eJ eKR eC eKa id (qRedEnc S D b) =
      encExp S D.msgs (indView S hpk eG eJ eKR eC eKa D) b := by
  funext pk
  simp only [qAuxAcc, encExp, Fintype.sum_prod_type, Fintype.card_prod, inv_natCast_mul,
    mul_assoc, Finset.mul_sum]
  rfl

omit [Fintype R] in
/-- The acceptance probability of `qRedExt B f D b` on an extended sample is
`extView` of `indView` there. -/
theorem qAuxAcc_qRedExt (f : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.CT B → C) (b : Bool) :
    qAuxAcc S hpk eG eJ eKR eC eKa (fun x => (x.1, x.2.1)) (qRedExt B f D b) =
      extView B f D.msgs (indView S hpk eG eJ eKR eC eKa D) b := rfl

/-- The module-LWE advantage of `qRedEnc S D b` is the module-LWE distance of the
expectations of `encExp` of `indView`. -/
theorem qMLWEAux_qRedEnc (b : Bool) :
    qMLWEAux B S hpk eG eJ eKR eC eKa (qRedEnc S D b) =
      absDiff (sdExp (mlweSample B false) (encExp S D.msgs (indView S hpk eG eJ eKR eC eKa D) b))
        (sdExp (mlweSample B true) (encExp S D.msgs (indView S hpk eG eJ eKR eC eKa D) b)) := by
  rw [qMLWEAux, qAuxAcc_qRedEnc]

omit [Fintype R] in
/-- The extended module-LWE advantage of `qRedExt B f D b` is the extended
module-LWE distance of the expectations of `extView` of `indView`. -/
theorem qMLWEExtAux_qRedExt (f : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.CT B → C) (b : Bool) :
    qMLWEExtAux B S hpk eG eJ eKR eC eKa (qRedExt B f D b) =
      absDiff (sdExp (extSample B false) (extView B f D.msgs (indView S hpk eG eJ eKR eC eKa D) b))
        (sdExp (extSample B true) (extView B f D.msgs (indView S hpk eG eJ eKR eC eKa D) b)) :=
  rfl

end QMLWE

/-! ## The bound -/

section Bound

open CatCrypt.Crypto.MLKEM

variable {m₁ m₂ n W q k c a : ℕ} {C K Hash Z ι : Type} [Fintype Z] [DecidableEq Z] [Nonempty Z]
  [Fintype K] [Nonempty K] [Fintype C] [DecidableEq C] [DecidableEq Hash] [Fintype ι]
  [NeZero n] [NeZero c]

/-- The IND-CPA advantage with oracle access against `mapCiphertext (toScheme P) f g`
is at most the sum of two module-LWE and two extended module-LWE advantages with
oracle access of the reductions `qRedEnc` and `qRedExt`. -/
theorem qIndcpaAux_le_qMLWE_mapCiphertext (P : MLWE_PKE_Scheme.Params)
    (f : MLWE_PKE_Basic.CT P.toBasic → C) (g : C → MLWE_PKE_Basic.CT P.toBasic)
    (hpk : MLWE_PKE_Basic.PK P.toBasic → Hash) (eG : (P.PT × Hash) ≃ Fin m₁)
    (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × P.Seed) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
    (D : QIndAuxAdv ι (m₁ + m₂) n W q k c a (MLWE_PKE_Basic.PK P.toBasic) C K P.PT) :
    qIndcpaAux (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) hpk eG eJ eKR eC eKa D ≤
      qMLWEAux P.toBasic (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) hpk eG eJ eKR eC eKa
          (qRedEnc (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) D true) +
        qMLWEExtAux P.toBasic (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) hpk eG eJ eKR eC
          eKa (qRedExt P.toBasic f D true) +
        qMLWEExtAux P.toBasic (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) hpk eG eJ eKR eC
          eKa (qRedExt P.toBasic f D false) +
        qMLWEAux P.toBasic (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) hpk eG eJ eKR eC eKa
          (qRedEnc (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) D false) := by
  rw [qIndcpaAux_eq_cpaExp, qMLWEAux_qRedEnc, qMLWEAux_qRedEnc, qMLWEExtAux_qRedExt,
    qMLWEExtAux_qRedExt]
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [cpaExp, encExp, absDiff]
  · exact cpaExp_absDiff_le P f g D.msgs _ (indView_le_one _ hpk eG eJ eKR eC eKa D)

open CompressedPKE (MLKEM512CT mlkem512Compress mlkem512CompressedScheme) in
open MLKEM512Instance (mlkem512Params) in
/-- The IND-CPA advantage with oracle access against the ML-KEM-512 K-PKE with
compressed ciphertexts is at most the sum of two module-LWE and two extended
module-LWE advantages with oracle access of the reductions `qRedEnc` and
`qRedExt`; the compression is part of the ciphertext each reduction forms.

References: Bos, Ducas, Kiltz, Lepoint, Lyubashevsky, Schanck, Schwabe, Seiler,
Stehlé, "CRYSTALS-Kyber: a CCA-secure module-lattice-based KEM", EuroS&P 2018
(the IND-CPA proof of the PKE from two module-LWE instances; `extSample` is
module-LWE with `k + 1` samples). -/
theorem qIndcpaAux_le_qMLWE (hpk : MLWE_PKE_Basic.PK mlkem512Params.toBasic → Hash)
    (eG : (mlkem512Params.PT × Hash) ≃ Fin m₁) (eJ : (Z × MLKEM512CT) ≃ Fin m₂)
    (eKR : (K × mlkem512Params.Seed) ≃ Fin n) (eC : MLKEM512CT ≃ Fin c) (eKa : K ≃ Fin a)
    (D : QIndAuxAdv ι (m₁ + m₂) n W q k c a (MLWE_PKE_Basic.PK mlkem512Params.toBasic)
      MLKEM512CT K mlkem512Params.PT) :
    qIndcpaAux mlkem512CompressedScheme hpk eG eJ eKR eC eKa D ≤
      qMLWEAux mlkem512Params.toBasic mlkem512CompressedScheme hpk eG eJ eKR eC eKa
          (qRedEnc mlkem512CompressedScheme D true) +
        qMLWEExtAux mlkem512Params.toBasic mlkem512CompressedScheme hpk eG eJ eKR eC eKa
          (qRedExt mlkem512Params.toBasic mlkem512Compress D true) +
        qMLWEExtAux mlkem512Params.toBasic mlkem512CompressedScheme hpk eG eJ eKR eC eKa
          (qRedExt mlkem512Params.toBasic mlkem512Compress D false) +
        qMLWEAux mlkem512Params.toBasic mlkem512CompressedScheme hpk eG eJ eKR eC eKa
          (qRedEnc mlkem512CompressedScheme D false) :=
  qIndcpaAux_le_qMLWE_mapCiphertext mlkem512Params mlkem512Compress
    CompressedPKE.mlkem512Decompress hpk eG eJ eKR eC eKa D

end Bound

end CatCrypt.Quantum.QROM
