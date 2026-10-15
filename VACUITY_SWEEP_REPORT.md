# Vacuity sweep of CatCryptCore

Date: 2026-10-15. Base: `origin/main` at `ab01925`. Branch: `work/vacuity-sweep`.

This is a text audit. No Lean source was changed and nothing was elaborated. Line numbers refer to `ab01925`.

## Method

The sweep covered all 463 `.lean` files under `CatCryptCore/`, about 138k lines. It looked for five patterns:

- **(a)** definitions that hold trivially;
- **(b)** hypotheses that cannot be satisfied or that restate the conclusion, including `∀ A, Adv A ≤ ε` over unbounded adversaries for a computational game;
- **(c)** `axiom` or `opaque` constants;
- **(d)** UC statements whose two worlds coincide, or that use statistical UC for a computational protocol;
- **(e)** hypotheses that carry the content of the theorem.

Each finding was located by grep and then read in context. The findings marked **[verified]** were also re-read against the definition text by hand while writing this report. The others rest on reading the statements and proofs, without elaboration.

### Arguments used throughout

**Brute force.** Adversaries are arbitrary Lean functions, for example `A : G.Output → SPComp Bool`. They are not limited in running time. Take a finite group or a finite output type. Then a statement `∀ A, Adv_X A ≤ ε` for a computational notion X (DL, CDH, OWF, PRG with stretch, CR, …) is false for every ε below the advantage of exhaustive search, which is typically 1 or close to 1. A theorem that assumes such a statement therefore proves nothing for small ε.

Information-theoretic notions are not affected: perfect hiding, OTP, universal hashing, and statistical bounds. For those the `∀ A` form is correct.

**Existing system.** The library already has a working form of concrete reduction:

```
Adv_scheme A ≤ Σ_i Adv_prim_i (B_i A) + ε_stat
```

where each `B_i` is a named `def`. Examples are the ML-KEM headline, ElGamal, Fiat–Shamir/Schnorr, KZG, and `UCEmulatesCSim`. The repairs below all put statements into this form.

### Coverage summary

| Item | Result |
|---|---|
| `sorry` / `admit` / `native_decide` / `implemented_by` / `@[extern]` | none |
| `opaque` | none |
| `axiom` | three, all in `Crypto/KeyAgreement/Curve25519.lean` (finding 3) |
| ML-KEM-512 IND-CCA headline (`MLKEM512QROMNumeric.lean:246`) | not vacuous; one right-hand-side quantity is never bounded numerically (finding 1) |

---

## Severity 1: statements reachable from headline results

### 1. `corrWorst` in the ML-KEM headline is never bounded numerically (weak, not vacuous)

**Headline theorem.** `Crypto/MLKEM/MLKEM512QROMNumeric.lean:246`, `mlkem512_qindcca_fips_two_pow` **[verified]**.

**Hypotheses.** The theorem takes only these:
- `hpk`;
- the encodings `eG eJ eKR eC eKa`;
- `NeZero`, `Fintype` and `DecidableEq` instances;
- the adversary `A : KEMQAdv …`.

No hypothesis is of the form `∀ A`. No class carries a bound.

**Right-hand side.** It contains the following terms:
- `qMLWEWorstBound … (nfKEM A) b`. This is a sum of `qMLWE` and `qMLWEExt` advantages, each applied to an explicit reduction. The reductions are `qRedPoly`, `qRedEnc`, `qRedExt`, `indRed`, `owRedQuery` and `nfKEM`. All are `def`s; the files are `PolyOracle.lean`, `QMLWEAux.lean`, `QIndcpaAux.lean`, `QOwcpaAux.lean` and `KEMAdvNormalFormMR.lean`.
- The proved constants `(2^137)⁻¹` and `(2^256)⁻¹`.
- `mlkem512CompressedScheme.corrWorst` (`Crypto/PKE/Games.lean:105`). This is defined as `∑' ks, keygen ks * ⨆ m, failProb`. It is the correct HHK δ.

**What is weak.** No theorem bounds `corrWorst` by a number. `QROM.md` quotes FIPS 203's 2^-139, but the repository does not prove it. The headline is therefore a correct reduction with one quantity left unevaluated.

**Related theorems with a free δ_c.** These theorems instead take a hypothesis `hWorst : corrWorst ≤ decryptionFailureProb mlkem512Noise δ_c`:
- `mlkem512_qindcca_coll` (`MLKEM512QROM.lean:115`)
- `mlkem512_qindcca_numeric` (`MLKEM512QROMNumeric.lean:90`)
- `mlkem512_qindcca_prf_worst_coll` (`MLKEM512QROMPrf.lean:647`)
- `CollisionSpreadIdeal.lean:189` and `:254`
- `mlkem512Compressed_indcca` (`CompressedPKE.lean:329`)

Here `decryptionFailureProb P δ := P.n * δ` (`CorrectnessBounds.lean:413`, **[verified]**) is a renaming. The variable δ_c is unconstrained: δ_c = ∞ satisfies the hypothesis.

**Users.**
- `corrWorst`: 112 references in 15 files.
- `decryptionFailureProb`: 65 references in 7 files.

**Repair.**
- Prove `mlkem512CompressedScheme.corrWorst ≤ 2^-138`. This is a closed computation: decryption failure does not depend on the matrix (noise `e·r + e₂ − s·e₁` plus the compression error), so it is a tail bound over the CBD(η₁ = 3, η₂ = 2) convolution, combined with a union bound over the 256 coefficients.
- Until that proof exists, drop the free-δ_c variants, or state their hypothesis as `corrWorst ≤ 256 · Pr[|noise₀| > ⌈q/4⌋]`.

**Related, in `CorrectnessBounds.lean`.** Several lemmas are arithmetic only, although their docstrings describe failure bounds:
- `coeffFailureProb _P δ := δ` (:365);
- `fo_correctness_amplification` (:502), which proves `(qHK+1)·δ = (qHK+1)·δ`;
- `mlkem512_failure_from_coeff` (:443), which has no failure hypothesis.

Reword these docstrings, or replace the lemmas with the union bound above.

### 2. The X25519 ladder headline also holds for the output `(0,0)` (pattern a)

**Declarations.**
- `Crypto/KeyAgreement/MontgomeryXOnly.lean:253`: `ProjEquiv p q := p.1 * q.2 = q.1 * p.2` **[verified]**.
- Headlines: `x25519_ladder_correct` (`Curve25519.lean:328`) and `x25519_ladder_correct_basepoint` (`Curve25519.lean:749`) **[verified]**.

**Why it is weak.** `ProjEquiv (0,0) q` holds for every `q`. The conclusion `ProjEquiv (xladderFold …).1 (xProj (k•B))` would therefore also be proved for a ladder that returned `(0,0)`. `LadderNondeg` constrains the intermediate `xdbl`/`xdadd` values on the true inputs. The conclusion itself never says that the output is nondegenerate.

`class MontyCurveGroup` (:227) is also satisfied by `xProj := fun _ => (0,0)`. Abstract results about it therefore constrain nothing until it is instantiated. The concrete instance through `xProjW` is not degenerate.

**Users.** `ProjEquiv`: 45 references in 2 files. Nothing outside `KeyAgreement/` uses the headline.

**Repair.** Add the conjunct `(xladderFold …).1.1 ≠ 0 ∨ (xladderFold …).1.2 ≠ 0` to the conclusion. It should follow from `LadderNondeg` by induction. Alternatively, redefine `ProjEquiv p q := (p ≠ 0 ∧ q ≠ 0) ∧ p.1*q.2 = q.1*p.2`.

### 3. Axioms for the Curve25519 base point (pattern c)

**Declarations.** All in `Crypto/KeyAgreement/Curve25519.lean` **[verified]**:
- `curve25519_basepoint : Curve25519Point` (:432)
- `curve25519_basepoint_order_nsmul : l • B = 0` (:440)
- `curve25519_basepoint_ne_zero` (:446)

**Consistency.** The axioms are consistent if the curve y² = x³ + 486662x² + x over 𝔽_{2²⁵⁵−19} has a point of prime order l. It does, since the group order is 8l. They are therefore true statements, assumed rather than proved.

**Caveats.**
- They do not pin the base point to u = 9. The docstring states this.
- The cited Rocq source rests on an `Admitted` lemma, `scalarmult_l_eq_zero`.

**Users.** Only `x25519_ladder_correct_basepoint` and its auxiliary lemmas, all in `Curve25519.lean`.

**Repair.** Define `B := (9, y₀)` with a proved curve equation, and prove `l • B = 0` by a kernel-checked computation, for example by repeated doubling with `decide +kernel` on `ZMod`. Until then, the headline should be read as a statement about every point of order l.

### 4. `UpToBadA` has a hypothesis that forces G₀ = G₁ (pattern b)

**Declarations.** In `Crypto/BadEvent.lean` **[verified]**:
- `structure UpToBadA` (:279);
- `advantage_upto_bad_A` (:236);
- `uptobadA_advantage` (:293), `uptobadA_advantage_all` (:395), `sdist_le_of_uptobadA` (:405).

**Why it is vacuous.** The hypothesis is `identical : ∀ A, IdenticalUntilBad (G₀.bind A) (G₁.bind A) bad`, with one `bad : SPComp Bool` shared by all adversaries. `IdenticalUntilBad` (:99) is pointwise in the final heap:

```
G₀ h (b,h') ≤ G₁ h (b,h') + bad h (true,h')
```

Suppose G₀ puts δ more mass than G₁ on `(a,h')`. Then for each fresh location ℓₙ, the adversary "write ℓₙ when the input is `a`, return true" forces `bad h` to put mass at least δ on a different heap `h'[ℓₙ]`. Infinitely many such heaps exceed total mass 1.

So the hypothesis forces `G₀ h ≤ G₁ h` pointwise. The `NoFail` fields make both total masses equal to 1, so G₀ = G₁, and every conclusion has advantage 0. This argument is on paper and has not been machine-checked.

**Unaffected.** The Bool-level `UpToBad`/`uptobad_advantage` is satisfiable. Its users `Relational/Approx.lean:927` and `GameReject.lean:145` are not affected.

**Users.** 11 references in 2 files: `BadEvent.lean`, and `Tactics/UpToBad.lean`, where the `upto_bad` tactic builds on `uptobadA_advantage`. The README lists the up-to-bad layer as a main component. `Tactics/VC.lean:276` contains an example with this hypothesis for two games that differ, so that hypothesis is false.

**Repair.**
- Make the bad event depend on the adversary: `bad : (α → SPComp Bool) → SPComp Bool` and `pr_bad : ∀ A, prTrue (bad A) ∅ ≤ ε`.
- Better, use the flagged formulation:
  - `G₀ = map fst G₀b`, `G₁ = map fst G₁b`, with `G₀b G₁b : SPComp (α × Bool)` equal on `flag = false`;
  - `Pr[flag] ≤ ε` for both games.

  The `bind A` case then follows by associativity, and the bound `AdvantageA G₀ G₁ A ≤ ε` holds for every A, because the flag argument does not depend on A.

`lazy_eager_upto_bad` (:1055) is `uptobad_advantage` under another name and never uses `lazy_eager_equiv`. Rename it or connect it.

### 5. The computational UC layer has no computational content (patterns a, b, d)

The README presents the Complexity layer as giving "the computational distance over admissible distinguishers and three levels of UC emulation". Four points show that, as defined, this layer gives only statistical guarantees.

**5a. Every admissibility class contains every deterministic test.**
- Where: `Crypto/UCAdmClass.lean:72–87`, `class UCAdmClass` **[verified]**.
- Why: the fields `adm_pure` and `adm_precomp (f : α' → α) : adm g → adm (g ∘ f)`, with `f` arbitrary and possibly noncomputable, make `pure ∘ p` admissible for every predicate `p`. The repository records this in `adm_pure_predicate` (QueryBoundedUC) and `adm_pure_predicate_size` (`SizeBoundedUC.lean:224`).
- Consequence: in every instance, `ucCdist f g ≥ sup_{a,h} TV(output marginals)`. For example, `ucCdist PRG uniform ≥ 1 − |range|/|β|`. This contradicts the docstring of `ucCdist_comp_right`, which uses the PRG example to claim a small distance.
- Users: `ucCdist` has 168 references in 11 files, all in the framework. No concrete protocol uses L2, L3, Cdist or RCL3.
- Repair: restrict `adm_precomp` to `f` in a cost-bounded class (for example `SPTree` terms with a cost charged for `ret`, or a circuit-size model indexed by a security parameter). Add a non-triviality theorem stating that some `f, g` satisfy `ucCdist f g < ucSdist f g`, under a named assumption.

**5b. The global instances are the trivial class.**
- Where: `adm := fun _ => True` in `UCAdmClass/SPCompInstance.lean:44`, `UCAdmClass/SDistrInstance.lean:44` and `UCMonad/RoundMCompDist.lean:57` **[verified]**.
- Consequence: under instance resolution, `ucCdist = ucSdist`, and L2/L3 are equivalent to L1 (`L2_iff_L1_trivial`, `L3_iff_L1_trivial`, `L2_iff_L1_RoundM`). The "computational" witnesses in CompUCEquivalence §6 are statistical.
- Repair: turn these instances into named `def`s, as `queryBoundedCompDist` already is, so that a computational statement must name its class.

**5c. Cost models charge nothing for computation.**
- Where: `MonadCostModel.lean:55–68`. The field `cost_precomp` together with `cost_pure = 0` gives cost 0 for `pure ∘ f`. `cost := 0` satisfies every field.
- Also affected:
  - `spTreeQueryAdm` (:167), since `queryCost (.ret _) = 0`;
  - `spTreeSizeAdm` (`SizeBoundedUC.lean:152`), since `size (.ret _) = 1`;
  - `CTAdmClass` (`ct_precomp` :75, `ct_spComp` :204), which ignores pure computation;
  - expected cost (`Unary/ExpectedCost.lean:149`, `CostComp.lift c 0`), where the cost is chosen by the user.
- Repair: as in 5a, charge a cost for pure computation, or restrict `ret` to a term language with a cost.

**5d. Emulation definitions that quantify over unbounded adversaries.**
- `UCEmulatesL2` (`UCLevels.lean:68`) and `UCEmulatesL3` (:142) read `∀ (A : leak → T view), ∃ S, …` without `adm A`. An unbounded A can decode the leak, so L2(ε) for a computational protocol can be proved only with ε close to the statistical distance.
- `UCEmulatesParam` and `UCEmulatesNegl` (`ConcreteReductions.lean:146`, `:152`) are built on statistical `UCEmulates`. "Negligible UC" is therefore statistical.
  - The definition `IsNegligible f := ∀ c, ∃ N, ∀ n ≥ N, f n * n^c ≤ 1` is correct.
- `GameUCEmulates` (`UC.lean:267`) quantifies over all `A : OracleIf → SPComp Bool`.
- `UCEmulates_of_isPure_advantage` (`UCDSL.lean:90`) is documented as "Computational UC emulation" with a PRF example, but its `hAdv` ranges over all distinguishers.
- Users:
  - L2: 28 references; L3: 13 references; both framework only.
  - `UCEmulatesNegl`: no users outside its file.
  - `GameUCEmulates`: `UC.lean` and a table in `NomAdvantage.lean`.
- Repair:
  - Put `adm A ∧ adm S` into L2 and L3.
  - Define negligible UC over classes `Adm_n` indexed by n.
  - Relabel `GameUCEmulates` and `UCEmulates_of_isPure_advantage` as statistical.
  - For computational protocols, use `UCEmulatesCSim` with `bound x D = Adv_prim (B x D)`, as `Examples/ElGamalUCConcrete.lean` already does.

**Appropriate uses.** Every concrete protocol proved with numeric `UCEmulates` is information-theoretic, so the numeric form is correct for them:
- Pedersen;
- `dualOT_uc_secure_zero`;
- `sigma_uc_zk_secure`, apart from finding 13;
- ChaumPedersen, OTP, secret sharing, Shamir;
- `bijCpa_uc`, `mask_uc`.

The only computational protocol in UC form is ElGamal, and it correctly uses `UCEmulatesCSim` with explicit DDH reductions.

**Composition gap.** The UC composition theorems (`UCEmulates_compile`, `UCEmulates_par` and their CSim versions) take same-interface distance hypotheses. They do not take ∀A∃S emulation hypotheses. This is a gap in coverage, not vacuity.

### 6. The Cryptobox security chain bounds a game that every adversary wins (patterns a, b, e)

**Declarations.**
- `Examples/Cryptobox/Cryptobox.lean:106` (`PKAEOracles.getsk`) and `:189` (`pkaeAdvantage`).
- `Examples/Cryptobox/PKEY.lean:95` (`getskOracle`) **[verified]**.

**Why it is vacuous.** `getskOracle pk` returns the secret key of every *honest* `pk`, and fails only on dishonest keys. An adversary can:
1. generate two honest keys;
2. call `getsk pk1`;
3. encrypt with `enc pk1 pk2`;
4. decrypt locally.

This distinguishes real ciphertexts from the ideal random ones with advantage close to 1 for every correct scheme. `nikeAdvantage` (`NIKE.lean:111`) also exposes `getsk`, so the adversary can recompute `N.sharedkey`.

In addition, adversaries are `SPComp` computations and can `SPComp.get` any location, including `skStoreLoc`. No advantage definition imposes a disjointness condition on adversary locations.

**Affected theorems.**
- `cryptobox_security` and `cryptobox_security_full` (`GameHopping.lean:382`);
- `_with_nike_reduction` (:719) and `_no_gap` (:745);
- their hypotheses `h_nike` and `h_ae`, which are unsatisfiable for small ε.

**Hypotheses that restate the conclusion.**
- `nikeStep_eq_reduction` (`GameHopping.lean:696`) has the hypothesis `h_cache_zero`, which is the conclusion **[verified]**.
- `cryptobox_security` (`Cryptobox.lean:279`) takes `hdecomp : pkaeAdv ≤ pkey_adv + nike_adv + ae_adv`, with free variables not linked to any game.
- `ae_hybrid_bound` (:245) takes the same `hdecomp`.
- `aeStep_bounded_by_sae` (`HYBRID.lean:462`) assumes `h_oracle_align`.
- `R_GSAE` (`Cryptobox.lean:216`) ignores its hybrid index.

**Users.** `pkaeAdvantage`: 15 references in 3 files.

**Repair.**
1. Remove `getsk` from the adversary oracle record, or make it mark the key as corrupted and exclude such keys from challenges.
2. Add a location-disjointness side condition (a validity predicate on the adversary) to every stateful advantage.
3. Rebase the chain on `GPKAE`/`gpkaeAdvantage` (`PKAE.lean:158/184`).
4. Prove the two missing hop bounds:
   - `nikeStepAdvantage ≤ nikeAdvantage N realPkeyO (R_NIKE A)`;
   - `aeStepAdvantage ≤ Σ_i saeAdvantage (R_SAE_hybrid i A)`.

---

## Severity 2: unsatisfiable or broken definitions in the assumption and example layers

### 7. Assumption wrappers `XSecure ε := ∀ A, Adv_X A ≤ ε` for computational X (pattern b)

| Declaration | Why unsatisfiable for small ε | Users | Concrete version in the repository |
|---|---|---|---|
| `CDHSecure` (`Assumptions/CDH.lean:84`) | brute-force discrete log | `cdh_secure_implies_dl_secure` (:189) | `dl_le_cdh_ddh` (:170) |
| `CoCDHSecure` (`CoCDH.lean:82`) | brute force | none | — |
| `ODHSecure` (`ODH.lean:141`) | brute force | none | — |
| `OWFSecure` / `PRGSecure` (`OWF.lean:90/140`) | brute-force inversion; for a PRG with stretch, ε ≥ 1 − \|Seed\|/\|Out\| | `prg_secure_implies_owf_secure` | none (see 8) |
| `CRSearchSecure` (class, `CR.lean:114`), `TCRSecure` (:179), `PreSecure` (:202) | unkeyed hash: a constant adversary outputs a fixed collision, so ε ≥ 1 for a compressing h | `CRSecure_implies_TCRSecure` (:215), `CRSecure_implies_PreSecure` (:282) | partly (reduction built in a local `let`, CR.lean:226) |
| `BLSCoCDHSecure` / `BLSForgeSecure` (`BLSSig/Security.lean:130/163`) | brute force | `bls_forge_*` (:209, :215) | `blsForgeAdvantage_eq_cocdh` |
| `odh_of_ddh_prf` hypothesis `h_ddh` (`ODH.lean:212`) | ∀ B over DDH | catalogue only | none (see 15) |
| `ka_secure_under_ddh` hypothesis `h_ddh` (`Examples/DiffieHellman.lean:165`) | ∀ A over DDH | none | `ka_advantage_eq_ddh` |
| `PRGAssumption.bound` (field, `Examples/PRG.lean:200`) | `Seed → Seed × Seed` has stretch, so ε ≥ 1 − 1/\|Seed\| | `triple_prg_bound_of_assumption` (:364) | none (see 15) |
| `pkey_sdist` hypothesis (`Cryptobox/PKEY.lean:583`) | no bound on the number of queries | none | — |

**Statistical, not vacuous.** The single-sample "real vs uniform" games `PRF_Adv`, `PRFAssumption.bound`, `MAC_Advantage` and `AEAD_Advantage` show the adversary a single sample. The supremum over unbounded A is therefore a statistical distance. It is satisfiable, but only by statistically uniform constructions such as bijective families. Label these games as information-theoretic.

**Repair.** Delete the wrappers, or keep them only as notation. State each theorem per adversary:
- `CDH_Advantage D A ≤ DDH_Advantage D (ddh_of_cdh A) + 1/|W|`. `ddh_of_cdh` exists at `CDH.lean:95` but no theorem uses it.
- `TCR_Advantage h A ≤ CR_Search_Advantage h (tcrToCR A)`, with `tcrToCR` lifted to a top-level `def`.
- For CR, move to a keyed family `h : K → In → Out` with the key sampled in the game.

### 8. Classes whose only field is the conclusion (patterns b, e)

**`PRGImpliesOWF`** (`Assumptions/OWF.lean:192`) **[verified]**.
- Its field is the theorem `prg_implies_owf` (:197), which is a projection of the field.
- The field is false for every G with W nonempty. The exhaustive inverter has OWF advantage 1. The derived distinguisher has PRG advantage 1 − |im G|/|W| < 1.
- So `prg_secure_implies_owf_secure` (:206) is vacuous, yet the catalogue lists "PRG ⟹ OWF: Proved".
- Repair: prove `OWF_Advantage (owf_of_prg G) A ≤ PRG_Advantage G (prg_distinguisher_of_owf_inverter G A) + |Set.range G.stretch|/|W|`.

**`CRImpliesPre`** (`CR.lean:277`).
- Its field is the conclusion of `CRSecure_implies_PreSecure` (:282).
- Repair: in a keyed setting, prove `Pre_Advantage h A ≤ 2·CR_Search_Advantage h (preToCR A) + |Out|/|In|`, with `preToCR` a `def`.

### 9. Game definitions that every adversary wins (pattern a)

Every `def` named below should be a `def` in the repository.

| Declaration | Distinguishing adversary | Users | Repair |
|---|---|---|---|
| `AEAD_CCA_Advantage` (`Assumptions/AEAD.lean:170`) **[verified]** | the real decryption oracle always returns `some _` and the ideal one `none`; `(dec w w).map Option.isSome` wins with advantage 1 for every scheme | catalogue; `AEAD_CPA_le_CCA` | `Option`-valued `decrypt`; ideal decryption answers from the log of challenge ciphertexts |
| `SPRP_Advantage` (`PRP.lean:153`) | the ideal world uses two independent random functions; querying `enc x` twice gives advantage ≥ 1 − 1/\|W\| | catalogue | lazily sampled random permutation with an inverse table |
| `MAC_Keyed_Advantage` (`MAC.lean:137`), `AEAD_Keyed_Advantage` (`AEAD.lean:268`) | the real game outputs `(tag, key)`; recompute the tag from the key | catalogue | do not output the key |
| `CR_Dist_Advantage` (`CR.lean:155`) | the adversary receives (x, y) and recomputes H | catalogue | delete; use `CR_Search_Advantage` |
| `PKE_ROM.CPA_Adv` (`MLKEM/PKE_ROM.lean:121`) **[verified]** | `|Pr[CPA … true] − 1/2|` with the bit fixed to `true`; a constant adversary gets 1/2 against every scheme | none | `absDiff Pr[CPA true] Pr[CPA false]` with a stateful guess, as in `PKE/Games.indcpaAdvantage` |
| `MLWE.PRF_IND_Game` (`MLKEM/MLWE.lean:197–231`) | the ideal world samples a fresh output per query, so a repeated query distinguishes; `dout` is not required to be uniform | none | lazily sampled random function |

### 10. Weak or misnamed definitions (pattern a)

**`EUF_CMA_Real` / `EUF_CMA_Adv`** (`Crypto/SecurityDefs.lean:205/212`).
- Problem: the tag `_t` is computed but never passed to the adversary. The forgery `(m*, t*)` is a fixed parameter. The notion measures key guessing, not EUF-CMA.
- Same pattern: `uh_forge_real` (`Examples/UniversalHash.lean:75`).
- Users: `Examples/MAC.lean` (`bijMAC_euf_cma_adv`, `bijMAC_forgery_prob`).
- Repair: `A : (Message → SPComp Tag) → SPComp (Message × Tag)`, with a freshness check against the query log.

**`GapDHDef` / `GapDH_Advantage`** (`Assumptions/GapDH.lean:88/122`).
- Problem: there is no DDH oracle, so the game is the DDH game. The docstring "GapDH is strictly weaker than DDH" does not hold for this definition.
- Repair: give the adversary the oracle `(X, Y, Z) ↦ decide (Z = CDH(X,Y))`.

**`MLWE_PKE_Basic.CPA_Game` / `CPA_Adv`** (`MLKEM/MLWE_PKE_Basic.lean:131/140`).
- Problem: the guess stage sees neither pk nor any state.
- Status: superseded by `CPA_Adv_st`, which is what the FO chain uses. Mark it as superseded or remove it.

**`OW_CPA_perfect` / `ow_perfect`** (`MLKEM/PKE_ROM.lean:142/192`).
- Problem: the body equals `OW_CPA`, so `ow_perfect` is `0 ≤ …`.
- Users: none.
- Repair: add the decryption check `dec sk c = some m'` to `OW_CPA_perfect`.

**Pedersen UC ideal functionality** (`Commitment/PedersenUC.lean:122`, `pedersen_uc_secure` :209).
- Problem: the ideal world gives `m` to the simulator, so the statement says nothing about hiding.
- Repair: label it as a commit-and-open equivalence, or split the commit phase (simulator learns only that a commitment was made) from the open phase (simulator learns `m`), using a trapdoor-equivocating simulator.

**`ZK/SigmaUCZK.SHVZK`** (:142) **[verified]**: see finding 13.

**`PerfectKEM_CPA`** (`Examples/KEMDEM.lean:706/757/767`).
- Problem: for a correct KEM it forces |Key| = 1, so the corollaries with Key = Bool apply only to incorrect KEMs.
- Users: no instance exists.

### 11. `CiphertextPseudorandom` ranges over the identity key (pattern b)

- **Where:** `Crypto/OT/DualModeOT.lean:207`; theorem `dualOT_uc_secure` (:338) **[verified]**.
- **Why:** the definition quantifies over every `pk`, including the identity. There `dualEnc pk m r = pk^r · m = m` is deterministic, so the distance to uniform is at least 1 − 1/|G|.
- **Users:** none; there is a comment in `UCLeakageDecomp.lean:226`.
- **Repair:** quantify over `pk ≠ 1`, or delete it and keep `dualOT_uc_secure_zero` (:350).
- **Modelling issue:** the ciphertext has no `g^r` component, the receiver output is `Unit`, and there is no correctness statement.

### 12. A theorem whose hypothesis equals its conclusion (pattern b)

`correctness_theorem` (`MLKEM/MLWE_PKE_Basic.lean:449`) **[verified]**:

```
(h_fail : prTrue (Correctness_Game P find) ≤ fail_prob) :
    prTrue (Correctness_Game P find) ≤ fail_prob := h_fail
```

Users: none. Repair: delete it, or prove `prTrue (Correctness_Game P find) ≤ corrWorst`.

### 13. SHVZK without a relation precondition (pattern b)

- **Where:** `Crypto/ZK/SigmaUCZK.lean:142` (`SHVZK`) **[verified]**; theorem `sigma_uc_zk_secure` (:212).
- **Why:** the definition requires equality of the real and simulated transcripts for every `(x, w, e)`, including pairs with ¬relation x w. Standard Σ-protocols in the repository, such as `simpleSigma` and Schnorr, fail this on non-witness pairs. The theorem therefore has a hypothesis that these protocols do not meet.
- **Contrast:** `Examples/SigmaProtocol.lean` and `Sigma.lean:290` include the relation.
- **Repair:** `∀ x w e, sp.relation x w → …`, and make the real and ideal protocols return `.inl ()` when ¬relation.

### 14. Hybrid bounds that concern a game other than the construction (pattern e)

**`triple_prg_bound_of_assumption` / `triple_prg_uniform_bound`** (`Examples/PRG.lean:364/350`).
- Problem: `DoublePRG.hyb 0` (:306) uses independent seeds, so it is not `DoublePRG.triple` (:282), and no theorem mentions `triple`. The hop hypotheses `h_inner` and `h_outer` contain free adversaries.
- Repair: set H0 := `triple`, H1 := `(stretch a, b)` with a, b uniform, H2 := uniform. Prove `Adv(triple, uniform) A ≤ PRG_Adv inner (Bin A) + PRG_Adv inner (Bout A)`, with `Bin` and `Bout` as `def`s.

**`prg_decomp_security_bound`** (`Examples/PRFPRG.lean:696`).
- Problem: it bounds `gen_hyb_decomp 0` (independent seeds), not `gen_real` (:154). A PRF with one query cannot bound correlated outputs.
- Repair: use the q-query PRF game `PRPPRFSwitching.PRF_q_Advantage` with `gen_real`.

### 15. The content of the reduction sits in a hypothesis (pattern e)

| Declaration | Hypothesis that carries the content | Repair |
|---|---|---|
| `odh_of_ddh_prf` (`ODH.lean:210`) | `h_prf` is hop 2 itself; B is a local `let`; `h_ddh` is a ∀-hypothesis | prove `ODH_Advantage D A ≤ DDH_Advantage D.toDDHDef (ddhAdvOfODH D A) + E_label PRF_Advantage ⟨D.hash⟩ label (prfAdvOfODH D A)` with both B's as `def`s |
| `cascade_prf_bound` / `_of_assumption` (`Examples/PRF.lean:180/197`) | no cascade construction; all three hops assumed; h12 is assumed although `RF_RP_Advantage_le` proves it | define the cascade; derive h01 and h23 from named reductions and h12 from `RF_RP_Advantage_le` |
| `cbc_indcpa_bound` (`Examples/CBCMode.lean:312`), `ctr_indcpa_bound` (`CTRMode.lean:233`) | `F` is unrelated to the cipher; `hswap*` carry the content | F := ⟨Key, Block, Block, eval⟩; prove `INDCPA_Adv ≤ Σ_b E_iv PRF_Adv F … (cbcRed iv A)` |
| `cpa_from_prf_bound` (`Examples/CPAFromPRF.lean:453`) | `hswap` combines two hops with a free `Ared` | delete; `cpa_from_prf_reduction_gamehop` (:589) is the concrete version |
| `security_based_on_prf` (`Examples/PRFMAC.lean:512`) | `prf_epsilon A` is unused padding; the forgery is fixed | rename it as a statistical 1/2 bound, or add an adaptive game with a PRF reduction |
| `heg_indcpa_le_ddh` (`Examples/HashedElGamal.lean:203`) | `h_ideal_indep` carries the hash-uniformity hop | assume `PMF.map H uniform = uniform`, and prove the hop |
| `pkey_switching` / `pkeyAdvantage_le_collision` (`Cryptobox/PKEY.lean:275`) | `h_agree` and `hcoll` are assumed; `collision_prob_*` (:526/:550) are never used | add query bounds; prove `pkeyAdvantage N B ≤ (q_gen(q_gen−1) + 2 q_gen q_csetpk)/(2\|PK\|)` |

The generic triangle and hybrid combinators (`prf_prp_composition`, `HybridArgument`, `MultiQueryPRF`, `single_to_multi_bound`) take hop hypotheses by design. They are acceptable as library lemmas and are not counted as findings.

---

## Severity 3: reflexive, trivial or interface-only statements without downstream use

| Declaration | Pattern | Observation |
|---|---|---|
| `det_self_advantage_zero` (`Deep/DeterministicInterp.lean:105`) | a, e | conclusion `c.eval h = c.eval h` by `rfl`; `_hdet` unused |
| `lazyEval_fresh_equiv` (`Tactics/LazySampling.lean:176`) | a, e | same program on both sides, by `rHoare_refl`; `_h_fresh` unused |
| `lazyEval_fresh_pHoare` (:409) | a, e | postcondition `True`; `_h_fresh` unused; `lazyEval_fresh_value_uniform` (:198) holds the content |
| `BehavioralEquiv` (`Deep/HybridDemo.lean:72`) | a | compares `exports` only; `hybrid_transitivity` says nothing about behaviour; replace with `DeepPackage.BehavEquiv` |
| `ValidCode.embed` (`Deep/Package.lean:115`), `ValidCode.ofSPComp` (`EvalComplete.lean:67`) | a | any `SPComp` is valid for any L; location discipline and `sep` not enforced; no semantic theorem depends on it yet |
| `class ValidCode L I α c` (`Package/ValidPackage.lean:53`) | a | `I` in no field; `reads_in_L` constrains only the return value, so code can copy a location outside L into one inside L |
| `RawPackage.link P₁ _ := P₁`, `idPkg := empty` (`Package/RawPackage.lean:158/163`); `NomPackage.support`/`rename` (`Nominal/NomPackage.lean:48/122`) | a | stubs (marked with a WARNING); support is metadata not tied to the code |
| `class RelQ0` (`Relational/RelationalQ0.lean:35`) | a | satisfied by `liftR := True`; no adequacy field |
| `UCEmulates_of_dummy` (`UC.lean:189`) | naming | restates `UCEmulates_of_sdist`; the dummy-adversary result is `DummyAdversary.dummy_completeness` |
| `INDCCA_Adv_zero_of_rHoare` (`SecurityDefs.lean:235`) | b | docstring states that the hypothesis holds only degenerately; no users |
| `commitment_binding` (`Examples/SigmaProtocol.lean:317`) | weak | concludes `∃ w, relation x w`; not a probabilistic binding bound |
| `qForkSuccProbSimple` (`GeneralForkingLemma.lean:211/218`) | weak | the event does not require the output index to equal I; `_hq` unused; `qFork_success_ge` is the useful form |
| `r_get_vs_get'`, `r_get_put_vs_get_put` (`Relational/Sync.lean:50/134`) | e | `_hSync` unused; the conclusions are true without it |
| `_hcoin` parameters (`MLKEM/CoinBadNumeric.lean:680, 697, 756, 775, 939, 985`; `NumericCorrectness.lean:919`) | e | unused; statements less general than they could be; harmless |
| `qIndist` (`Quantum/QRHL.lean:523`) | a | vacuous at dimension 0; callers guard with `[NeZero d]` |
| `PRP_PRF_SwitchingBound`, `PRP_Full_Bound` (`PRP.lean:167/181`) | — | definitions never connected to a game |

---

## Checked and found sound

**Probability and relational layer.**
- `sdist`, `prTrue`, `Advantage`, `AdvantageA` and the triangle lemmas.
- `rHoare` (`Relational/Judgment.lean:53`): an exact-marginal coupling.
- `rHoareApprox` (`Approx.lean:794`): grade 0 equals `rHoare`.
- Frame and while rules; the birthday bound; Schwartz–Zippel.

**Forking lemmas.**
- `fork_success_ge`, `qFork_success_ge`, `bellare_neven_aggregation`;
- the `OracleForking` bounds;
- `TreeForking.acceptProb_le`.

Their hypotheses are satisfiable and their bounds are not trivial.

**ML-KEM and FO.**
- Games: `indcpa`, `indcca`, `owcpa`, `owpca`, `owpcva`, `romOWPCA`, `qOwcpaAux`, `qIndcpaAux`, `qMLWE(Ext)` are not trivial.
- Classical FO theorems (`tTransform_owpca`, `uNotBot_indcca`, `foNotBot_indcca*`, `fips203_indcca`, `foNotBot_indcca_mlwe`) have named reductions.
- All side conditions of the QROM chain are discharged before the headline: `ChainGood`, `hcoin`, `hlam`, `hcoll`, `IsTUFactoring`, `SamplerIsCbd`.
- `Lattice/` uses `decide +kernel`.

**Concrete reductions.**
- ElGamal: IND-CPA ≤ DDH, and the UC form through `UCEmulatesCSim`;
- `ka_advantage_eq_ddh`, `blsForgeAdvantage_eq_cocdh`, `dl_le_cdh_ddh`;
- `pke_security` (KEM/DEM, three named reductions);
- `fiatShamir_rom_eufcma`, `schnorr_fs_rom_eufcma`;
- `KZG_knowledge_sound`, `pedersen_binding_le_dlog`;
- `RF_RP_Advantage_le` and `PRF_q_Advantage_le`;
- `receiver_security` (OT);
- `cpa_from_prf_reduction_gamehop`, statistical as noted in finding 7.

**Information-theoretic statements, correctly stated with ∀ A.** OTP, secret sharing, Shamir, Pedersen hiding, `dualOT_uc_secure_zero`, ChaumPedersen UC, universal hashing.

**Negligibility.** `IsNegligible` and its closure lemmas.

## Modelling caveats (not vacuity)

**ML-KEM: oracle modelling.**
- `PRF_η ∘ G` is idealised as one random oracle.
- Key generation uses uniform seeds rather than `(ρ, σ) = G(d‖z)`.
- The PRF variant models `PRF_η` as a quantum random oracle.
- `QROM.md` records these choices.

**ML-KEM: adversary class.**
- Adversaries must start from a pure state.
- Mixed initial states are not covered by the KEM headline.

**General.**
- The efficiency of every reduction `B_i` is not formalised anywhere. This combines with finding 5: the library has no computational notion of efficiency that excludes exhaustive search.
