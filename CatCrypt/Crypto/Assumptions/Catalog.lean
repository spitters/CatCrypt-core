/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Assumptions.DDH
import CatCrypt.Crypto.Assumptions.CDH
import CatCrypt.Crypto.Assumptions.GapDH
import CatCrypt.Crypto.Assumptions.DL
import CatCrypt.Crypto.Assumptions.tSDH
import CatCrypt.Crypto.Assumptions.qSDH
import CatCrypt.Crypto.Assumptions.CoCDH
import CatCrypt.Crypto.Assumptions.AEAD
import CatCrypt.Crypto.Assumptions.MAC
import CatCrypt.Crypto.Assumptions.PRP
import CatCrypt.Crypto.Assumptions.RSA
import CatCrypt.Crypto.Assumptions.CR
import CatCrypt.Crypto.Assumptions.OWF
import CatCrypt.Crypto.Assumptions.ODH

/-!
# Cryptographic Assumption Catalog

Complete index of cryptographic assumptions used in security reductions.

Abstract theorems take these as hypotheses (they are reductions, not claims).
Concrete hardness beliefs (e.g., "DDH is hard for P-256") should be axiomatized
at the instantiation site, not here.

## Standard Assumptions

| Assumption | File | Reference |
|------------|------|-----------|
| `DDH_Advantage` | `Assumptions/DDH.lean` | Boneh-Shoup Def. 11.2 |
| `CDH_Advantage` | `Assumptions/CDH.lean` | Boneh-Shoup Def. 11.1 |
| `GapDH_Advantage` | `Assumptions/GapDH.lean` | OP01 Def. 5 (decisional formulation) |
| `DL_Advantage` | `Assumptions/DL.lean` | Boneh-Shoup Def. 10.6 |
| `tSDH_Advantage` | `Assumptions/tSDH.lean` | Boneh-Boyen, EUROCRYPT 2008 |
| `qSDH_Advantage` | `Assumptions/qSDH.lean` | Boneh-Boyen, EUROCRYPT 2008 |
| `CoCDH_Advantage` | `Assumptions/CoCDH.lean` | Boldyreva, PKC 2003 |
| `OMDL_Advantage` | `Assumptions/OMDL.lean` | Bellare et al., ASIACRYPT 2003 |
| `OMDL1_Advantage` | `Assumptions/OMDL.lean` | q=1 specialization for FROST |
| `AEAD_Advantage` | `Assumptions/AEAD.lean` | Rogaway, CCS 2002; Boneh-Shoup §9.5 (IND-CPA only) |
| `AEAD_CCA_Advantage` | `Assumptions/AEAD.lean` | Rogaway, CCS 2002 (IND-CCA2: enc + dec oracles) |
| `MAC_Advantage` | `Assumptions/MAC.lean` | Bellare-Kilian-Rogaway, JCSS 2000 |
| `PRP_Advantage` | `Assumptions/PRP.lean` | Boneh-Shoup §4.1 (ideal = random fn, not perm) |
| `SPRP_Advantage` | `Assumptions/PRP.lean` | Boneh-Shoup §4.2 (forward + inverse) |
| `PRF_Advantage` | `Assumptions/PRP.lean` | Boneh-Shoup §4.2 (single-query) |
| `RSA_Advantage` | `Assumptions/RSA.lean` | Boneh-Shoup §10.2 |
| `CR_Search_Advantage` | `Assumptions/CR.lean` | Rogaway-Shrimpton, FSE 2004 |
| `CR_Dist_Advantage` | `Assumptions/CR.lean` | Boneh-Shoup §8.1 (distinguishing) |
| `TCR_Advantage` | `Assumptions/CR.lean` | Rogaway-Shrimpton, FSE 2004 |
| `OWF_Advantage` | `Assumptions/OWF.lean` | Boneh-Shoup §8.1 / Katz-Lindell §8.1 |
| `OWP` | `Assumptions/OWF.lean` | Boneh-Shoup §8.2 (permutation variant) |
| `PRG_Advantage` | `Assumptions/OWF.lean` | Boneh-Shoup §3.1 |
| `ODH_Advantage` | `Assumptions/ODH.lean` | Abdalla-Bellare-Rogaway, CT-RSA 2001 |
| `Extract_Advantage` | `HKDF_UC.lean` | Krawczyk, CRYPTO 2010 |
| `Expand_Advantage` | `HKDF_UC.lean` | Krawczyk, CRYPTO 2010 |
| `Extract_IKM_Advantage` | `HKDF_UC.lean` | Krawczyk 2010 Thm 2 (dual PRF) |

## Non-Standard Assumptions

| Assumption | File | Variant Of | Non-Standard Property |
|------------|------|-----------|----------------------|
| `Expand_Composed_Advantage` | `HKDF_UC.lean` | Expand | KDM-PRF (`f : W → W`) |
| `Expand_Composed_Leak_Advantage` | `HKDF_UC.lean` | Expand | KDM-PRF + key leakage |
| `AEAD_Keyed_Advantage` | `Assumptions/AEAD.lean` | AEAD | KDM + key leakage |
| `MAC_Keyed_Advantage` | `Assumptions/MAC.lean` | MAC | KDM + key leakage |

## Protocol Usage Matrix

| Protocol | DDH | Extract_IKM | Expand | Expand_Composed_Leak | AEAD | AEAD_Keyed |
|----------|-----|-------------|--------|---------------------|------|------------|
| HPKE     | x   | x           | x      |                     | x    |            |
| EDHOC    | x   | x           |        | x                   |      | x          |
| TLS HS   |     |             | x      |                     |      |            |
| TLS Rec  |     |             |        |                     | x    |            |
| SSH      |     |             |        |                     |      | x          |
| Kerberos |     |             |        |                     |      | x          |

## Reduction Status

- PRG ⟹ OWF: Proved (`prg_implies_owf`) (`OWF.lean`)
- DDH + PRF ⟹ ODH: Reduction via `odh_of_ddh_prf` (`ODH.lean`)
- DDH ⟹ CDH: Reduction via `ddh_of_cdh` (`CDH.lean`)
- DDH ⟹ GapDH: Proved (`GapDHDef.ofDDH`)
- CDH ⟹ DL: Standard (not formalized; not needed by current protocols)
- HKDF ← Extract + Expand: Proved (`hkdf_advantage_bound`)
- Expand_Composed(const f) = Expand: Definitional equality
- PRP ← PRF + switching: `PRP_Full_Bound` (`PRP.lean`)
- Standard AEAD ⇏ AEAD_Keyed: KDM gap (no general reduction)
- Standard Expand ⇏ Expand_Composed: KDM-PRF gap (no general reduction)
- Expand_Composed ⇏ Expand_Composed_Leak: Leakage gap (no general reduction)
-/
