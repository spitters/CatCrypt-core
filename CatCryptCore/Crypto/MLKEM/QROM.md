# ML-KEM-512 in the quantum random-oracle model

This document describes the machine-checked proof that ML-KEM-512 (FIPS 203) is
IND-CCA secure against quantum adversaries in the quantum random-oracle model
(QROM). Every term of the bound is either a proved number or the advantage of an
explicit reduction against quantum module-LWE. The proof uses the three standard
Lean axioms.

## 1. The theorems

Two headline theorems state the result.

| Theorem | What it states |
|---|---|
| [`mlkem512_qindcca_fips_two_pow`](MLKEM512QROMNumeric.lean) | IND-CCA security of the FIPS 203 KEM over the compressed ML-KEM-512 PKE, with key generation and noise taken from uniform seeds. |
| [`mlkem512_qindcca_prf_two_pow`](CollisionSpreadIdeal.lean) | The same with the matrix sampled from the XOF by rejection (FIPS 203 Algorithm 7) and the noise sampler `PRF_η` modelled as a quantum random oracle. |

**Adversary model** ([`KEMQAdv`](../../Quantum/QROM/KEMQuantumGame.lean),
[`QAdvMR`](../../Quantum/QROM/MultiRound.lean)):
- The adversary queries the hash oracles `G` and `J` in superposition through one
  merged, domain-separated oracle, with `q` queries per segment.
- It makes `k` classical decapsulation queries.
- Between queries it applies unitaries to the query and work registers, starts in
  a pure state, and ends with one projective measurement of its output bit. The
  work register has arbitrary dimension `w`.

After deferred measurement the adversary makes `q' = flatQ q k q` oracle queries
([`flatQ`](../../Quantum/QROM/MultiRound.lean)).

**The KEM** ([`fips203`](../KEM/FIPS203KEM.lean)) is the FO transform with
implicit rejection and re-encryption:
- `(K, r) = G(m, hpk pk)`;
- the rejection key is `J(z, c)`;
- `hpk` is an arbitrary function.

**The bound (FIPS form).** Write:
- `δ = corrWorst`;
- `q'' = flatQ (q + 4) k q`;
- `ε_b = qMLWEWorstBound (nfKEM A) b` for `b ∈ {true, false}`.

Then

```
Adv^{IND-CCA}(A) ≤ Σ_b 4·√(q' · 4q' · (ε_b + δ))
                 + 8q'√δ + δ + 2^-137 + 8q'√δ
                 + 2·(8q'·√(2^-256) + 8q''√δ + δ + 8q'√δ).
```

The terms are as follows.

- **Module-LWE.** [`qMLWEWorstBound`](MLKEM512QROMFinal.lean) is the sum of two
  quantum module-LWE advantages and two quantum extended module-LWE advantages,
  plus `|M|⁻¹` and `δ`. Each advantage is that of an explicit reduction built
  from `A` (`qRedPoly`, `qRedEnc`, `qRedExt`, `indRed`, `owRedQuery`, `nfKEM`).
  Extended module-LWE ([`extSample`](../../Quantum/QROM/QMLWEAux.lean)) is
  module-LWE with `k + 1` samples. No hypothesis bounds the advantage of any
  adversary.
- **Correctness.** `δ` is [`corrWorst`](../PKE/Games.lean), the scheme's
  decryption-failure probability: the expectation over key pairs of the largest
  failure probability over messages, the δ-correctness of
  Hofheinz–Hövelmanns–Kiltz. It is a defined quantity of the scheme. FIPS 203
  quotes `2^-139` for it, computed by numerical convolution of the noise
  distributions.
- **Coin collision.** `2^-137` bounds the key-averaged probability that two
  independent encryption seeds produce the same ciphertext (§3).
- **Implicit-rejection key.** `2^-256` is the probability of guessing the
  rejection seed `z`.

**The bound (PRF form).** The same chain, with the following changes:
- The collision term is `3·2^-256 + 2^-137 + xofHop`, which
  [`prfCollTerm_le_two_pow`](CollisionSpreadIdeal.lean) bounds by `2^-136`.
- The module-LWE terms carry `2·xofHop`.
- [`xofHop`](MLKEM512QROMPrf.lean)` = 4·C(560,255)·(767/4096)^305` is the
  statistical distance between the rejection-sampled matrix and the uniform
  matrix; [`xofHop_le_two_pow`](CollisionSpreadIdeal.lean) bounds it by `2^-170`.

## 2. The game sequence

Each row is one step of the chain. The loss is the amount the step adds to the
bound.

| Step | Lean | Loss | Literature |
|---|---|---|---|
| Normal form | [`qINDCCAAdvantage_nfKEM`](../../Quantum/QROM/KEMAdvNormalFormMR.lean) | none: the adversary `nfKEM A` in normal form has the advantage of `A` | |
| Rejection-key prefix | [`hopJ'`](../../Quantum/QROM/HopJPrefix.lean) | `8q'·|Z|^{-1/2}`: `J(z, ·)` is a random function to an adversary that does not know `z` | SXY18; HKSU20 |
| Decapsulation simulation | [`absDiff_prWinKEM'_prWinKEMHq_le_of_lam`](../../Quantum/QROM/NumericCorrectness.lean) | `8q''√δ + δ + 8q'√δ`: `G` is resampled to non-failing coins, after which real decapsulation equals the oracle that computes the key from the ciphertext | SXY18; JZCWM18 |
| Challenge key | [`prWinKEMK_indep`](../../Quantum/QROM/HopChallengeKey.lean) | none: the challenge key is replaced by an independent key | HHK17 |
| Coin reprogramming | [`hopCoin_o2h`](../../Quantum/QROM/HopCoinChallenge.lean) through [`o2h_semiclassical`](../../Quantum/QROM/O2HTheorem.lean) | `4√(q'·Pr[Find])` | AHU19, Theorem 1 (semi-classical one-way to hiding) |
| Find to one-wayness | [`prFindAvg_le_four_sum_guess`](../../Quantum/QROM/HopCoinChallenge.lean), [`prFindCoin_le_qOwcpaAux`](../../Quantum/QROM/QOwcpaAux.lean) | `Pr[Find] ≤ 4q'·(OW + δ)` | AHU19, Theorem 2 |
| Challenge-bit swap | [`absDiff_prWinKEMHq_le_numeric_of_lam_coll`](../../Quantum/QROM/CoinBadNumeric.lean) | `8q'√δ + δ + collWeight + 8q'√δ` | the derandomisation step of HHK17's `T` |
| One-wayness to indistinguishability | [`qOwcpaAux_le_qIndcpaAux`](../../Quantum/QROM/QIndcpaAux.lean) | `|M|⁻¹ + corrErr` | HHK17 |
| Indistinguishability to module-LWE | [`qIndcpaAux_le_qMLWE`](../../Quantum/QROM/QMLWEAux.lean) | two module-LWE and two extended module-LWE advantages per challenge bit | Bos et al. (CRYSTALS-Kyber) |
| Simulating the random oracles | [`qMLWEAux_eq_qMLWE_qRedPoly`](../../Quantum/QROM/PolyOracle.lean) | none: the reductions simulate the oracles by `2q`-wise independent polynomials, which is an equality of advantages | Zhandry 2012, Theorem 6.1 |
| Noise sampler (PRF form) | [`absDiff_prfReal_prfIdeal`](PRFOracle.lean), [`avg_collWeight_prfScheme_le`](PRFCoinWeak.lean) | seed-guessing terms in `2^-256` | AHU19 |
| Matrix sampling (PRF form) | [`kgX_close`](MLKEM512QROMPrf.lean) | `xofHop` | FIPS 203, Algorithm 7 |

One-way to hiding is proved on state vectors and projectors. It is a theorem in
this development, not a rule of a program logic. In
[`o2h_semiclassical`](../../Quantum/QROM/O2HTheorem.lean), `q` counts the oracle
applications of the adversary
([`QAdv`](../../Quantum/QROM/SemiClassicalOracle.lean)), so the constant is at
least as tight as the `d + 1` form of AHU19.

## 3. The collision term

The derandomisation step of the FO proofs (HHK17, TU16, HKSU20) uses worst-case
γ-spreadness: `max over pk, m, c of Pr_r[Enc(pk, m; r) = c] ≤ 2^-γ`. ML-KEM is
not usefully γ-spread, because a degenerate key (the zero matrix) is in the
support of key generation, and the worst case over keys is `2^-45`.

The step needs only the average over key generation of the probability that two
independent coins collide, [`collWeight`](../../Quantum/QROM/CollisionWeight.lean),
the analogue for spreadness of the key averaging in δ-correctness. For ML-KEM-512:

```
collWeight ≤ C(128,40)·20^160·64^352 / 64^512 + 7^256 / 3329^178 ≤ 2^-137
```

([`collWeight_mlkem512_le`](CollisionSpreadBound.lean),
[`collBound_le_two_pow`](MLKEM512QROMNumeric.lean)). The proof is a count in
[`CollisionSpreadLemmas`](CollisionSpreadLemmas.lean):
- a Compress₁₀ bucket holds at most 7 values;
- the NTT is a bijection, proved through a Vandermonde determinant;
- the second term is an anticoncentration bound over the uniform matrix;
- the point mass of the centred binomial distribution is `20/64`.

Every large power is bounded symbolically; none is evaluated.
[`CollisionSpreadIdeal`](CollisionSpreadIdeal.lean) transfers the bound from the
uniform matrix to the XOF-sampled matrix through `kgX_close`.

## 4. The modelled scheme

The theorem is about the following model of the scheme. Each item is part of the
statement.

- **Hash functions.** `G` and `J` are quantum random oracles. The equivalences
  `eG`, `eJ`, `eKR`, `eC`, `eKa` index their domains.
- **Key generation.** Keys come from uniform randomness. The derivation
  `(ρ, σ) = G(d ‖ z)` of ML-KEM.KeyGen is not modelled.
- **Matrix.** In the PRF form, the XOF is a random function that the adversary
  does not query. The matrix it produces is part of the public key.
- **Noise.** In the PRF form, `PRF_η` is a quantum random oracle. This is a
  stronger idealisation than the PRF assumption of the Kyber analysis. In the FIPS
  form, the noise comes from uniform seeds.
- **Assumptions.** There are two: quantum module-LWE and quantum extended
  module-LWE, as in the theorem of the Kyber paper.
- **Bound shape.** The bound has the `q√(ε + δ)` shape of the proofs based on
  AHU19 (HKSU20, BHHHP19). Measure-rewind-measure (KSSSS20) and
  measure-rewind-extract (GLX24) avoid the square root for bounds based on
  IND-CPA. Against `2^-128` module-LWE advantages, the square root costs about a
  factor `2^64`.

## 5. Module map

| Part | Modules |
|---|---|
| Games, adversaries, normal form | `Quantum/QROM/KEMQuantumGame`, `MultiRound`, `KEMAdvNormalFormMR` |
| One-way to hiding and search | `Quantum/QROM/SemiClassicalOracle`, `O2HTheorem`, `FindToGuess` |
| Hops | `Quantum/QROM/HopJPrefix`, `NumericCorrectness`, `HopChallengeKey`, `HopCoinChallenge`, `CoinBadNumeric` |
| Reductions to module-LWE | `Quantum/QROM/QOwcpaAux`, `QIndcpaAux`, `QMLWEAux`, `PolyOracle` |
| ML-KEM-512 instance | `Crypto/MLKEM/MLKEM512QROMFinal`, `MLKEM512FailureBound`, `MLKEM512QROMNumeric` |
| Collision term | `Quantum/QROM/CollisionWeight`, `Crypto/MLKEM/CollisionSpreadLemmas`, `CollisionSpreadBound` |
| PRF and XOF forms | `Crypto/MLKEM/PRFOracle`, `PRFCoinWeak`, `MLKEM512QROMPrf`, `CollisionSpreadIdeal` |

## 6. Other machine-checked proofs

- Almeida, Barbosa, Barthe, Grégoire et al. (CRYPTO 2024) prove IND-CCA security
  and correctness of ML-KEM in EasyCrypt in the classical random-oracle model, and
  connect the statement to the Jasmin implementation.
- Unruh (ASIACRYPT 2020) mechanises the generic FO transform in the QROM in
  qrhl-tool, and Barbosa et al. (CCS 2021) do so in EasyPQC. Both take one-way to
  hiding as a rule.

The present proof covers the ML-KEM-512 instance in the QROM, proves one-way to
hiding on the semantics, and computes the collision quantity instead of assuming
spreadness.

## References

- [AHU19] Ambainis, Hamburg, Unruh. Quantum security proofs using semi-classical oracles. CRYPTO 2019. ePrint 2018/904.
- [BHHHP19] Bindel, Hamburg, Hövelmanns, Hülsing, Persichetti. Tighter proofs of CCA security in the quantum random oracle model. TCC 2019. ePrint 2019/590.
- [Bos+18] Bos, Ducas, Kiltz, Lepoint, Lyubashevsky, Schanck, Schwabe, Seiler, Stehlé. CRYSTALS-Kyber: a CCA-secure module-lattice-based KEM. EuroS&P 2018.
- [BDFLSZ11] Boneh, Dagdelen, Fischlin, Lehmann, Schaffner, Zhandry. Random oracles in a quantum world. ASIACRYPT 2011. ePrint 2010/428.
- [GLX24] Ge, Liao, Xue. Measure-rewind-extract: tighter proofs of one-way to hiding and CCA security in the quantum random oracle model. ePrint 2024/777.
- [HHK17] Hofheinz, Hövelmanns, Kiltz. A modular analysis of the Fujisaki-Okamoto transformation. TCC 2017. ePrint 2017/604.
- [HKSU20] Hövelmanns, Kiltz, Schäge, Unruh. Generic authenticated key exchange in the quantum random oracle model. PKC 2020. ePrint 2018/928.
- [JZCWM18] Jiang, Zhang, Chen, Wang, Ma. IND-CCA-secure key encapsulation mechanism in the quantum random oracle model, revisited. CRYPTO 2018. ePrint 2017/1096.
- [KSSSS20] Kuchta, Sakzad, Stehlé, Steinfeld, Sun. Measure-rewind-measure: tighter quantum random oracle model proofs for one-way to hiding and CCA security. EUROCRYPT 2020. ePrint 2021/454.
- [SXY18] Saito, Xagawa, Yamakawa. Tightly-secure key encapsulation mechanism in the quantum random oracle model. EUROCRYPT 2018. ePrint 2017/1005.
- [TU16] Targhi, Unruh. Post-quantum security of the Fujisaki-Okamoto and OAEP transforms. TCC 2016. ePrint 2015/1210.
- Zhandry. Secure identity-based encryption in the quantum random oracle model. CRYPTO 2012. ePrint 2012/076.
- Almeida, Barbosa, Barthe, Grégoire et al. Formally verifying Kyber, Episode V. CRYPTO 2024. ePrint 2024/843.
- Unruh. Post-quantum verification of Fujisaki-Okamoto. ASIACRYPT 2020. ePrint 2020/962.
- Barbosa, Barthe, Fan, Grégoire, Hung, Katz, Strub, Wu, Zhou. EasyPQC: verifying post-quantum cryptography. CCS 2021. ePrint 2021/1253.
- NIST. FIPS 203: Module-Lattice-Based Key-Encapsulation Mechanism Standard. 2024.
