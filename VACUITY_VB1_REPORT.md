# Vacuity repairs VB1: findings 7, 8 and 15 (`odh_of_ddh_prf`)

Branch `work/vacuity-vb1`, created from `origin/work/auto-corpus`. Finding numbers refer to
`VACUITY_SWEEP_REPORT.md` on `origin/work/vacuity-sweep`. Scope of this branch: the assumption
wrappers and conclusion-only classes of findings 7 and 8 in `Crypto/Assumptions/{CDH,CoCDH,ODH,OWF,CR}.lean`
and `Crypto/BLSSig/Security.lean`, the `h_ddh` hypothesis of `ka_secure_under_ddh`
(`Examples/DiffieHellman.lean`), and `odh_of_ddh_prf` (finding 15). The other rows of the
finding 7 table (`PRGAssumption.bound`, `pkey_sdist`) are not part of this branch.

No declaration was kept as degenerate. No `sorry`, `native_decide` or axiom was added.

Every new reduction is stated per adversary, with each reduction a top-level `def`. The
only numeric terms are information-theoretic: `1/|W|`, `|im G|/|W|` and `|Output|/|Input|`.

## CDH (finding 7), `CatCryptCore/Crypto/Assumptions/CDH.lean`

Before:

```lean
def CDHSecure (D : DDHDef W) (ε : ℝ≥0∞) : Prop :=
  ∀ (A : CDH_Adversary W), CDH_Advantage D A ≤ ε

theorem cdh_secure_implies_dl_secure (D : DDHDef W)
    (ε : ℝ≥0∞) (h_cdh : CDHSecure D ε)
    (A_dl : DL_Adversary_DDH W) :
    DL_Advantage_DDH D A_dl ≤ ε
```

After (both declarations above are removed):

```lean
theorem prTrue_sample_guess (c : SPComp W) (h₀ : Heap) :
    prTrue ((SPComp.sample W).bind fun r => c.bind fun x => SPComp.pure (decide (x = r))) h₀
      ≤ (Fintype.card W : ℝ≥0∞)⁻¹

theorem cdh_le_ddh (D : DDHDef W) (A : CDH_Adversary W) :
    CDH_Advantage D A ≤ DDH_Advantage D (ddh_of_cdh A) + (Fintype.card W : ℝ≥0∞)⁻¹
```

- Reduction: `ddh_of_cdh` (an existing top-level `def` that no theorem used before).
- The existing per-adversary statement `dl_le_cdh_ddh` replaces `cdh_secure_implies_dl_secure`.
- A private helper `prTrue_bind_le_const` was added. The file now imports `CatCryptCore.Crypto.ForkingLemma`.
- Users: `cdh_secure_implies_dl_secure` was the only user of `CDHSecure`, and it was removed. `Catalog.lean` "Reduction Status" now names `cdh_le_ddh` and `dl_le_cdh_ddh`. The earlier line "CDH ⟹ DL: Standard (not formalized)" was wrong because `dl_le_cdh_ddh` exists.

## co-CDH (finding 7), `CatCryptCore/Crypto/Assumptions/CoCDH.lean`

Before:

```lean
def CoCDHSecure (ε : ℝ≥0∞) : Prop :=
  ∀ (A : CoCDH_Adversary P), CoCDH_Advantage P A ≤ ε
```

After: removed. It had no users and contained only the wrapper. The module docstring states
that it was removed and points to `BLSSig.blsForgeAdvantage_eq_cocdh` for the per-adversary
form.

## BLS (finding 7), `CatCryptCore/Crypto/BLSSig/Security.lean`

Before:

```lean
def BLSCoCDHSecure (ε : ℝ≥0∞) : Prop :=
  ∀ (A : BLSCoCDHAdversary P), BLSCoCDH_Advantage P A ≤ ε
def BLSForgeSecure (ε : ℝ≥0∞) : Prop :=
  ∀ (F : BLSForger P), blsForgeAdvantage P F ≤ ε
theorem bls_forge_reduces_to_cocdh (ε : ℝ≥0∞) (h : BLSCoCDHSecure P ε)
    (F : BLSForger P) : blsForgeAdvantage P F ≤ ε
theorem bls_forge_secure_of_cocdh (ε : ℝ≥0∞) (h : BLSCoCDHSecure P ε) :
    BLSForgeSecure P ε
```

After: all four are removed. The existing per-forger equality is the replacement, and the
module docstring now states it:

```lean
theorem blsForgeAdvantage_eq_cocdh (F : BLSForger P) :
    blsForgeAdvantage P F = BLSCoCDH_Advantage P (blsReduction P F)
```

- Reduction: `blsReduction` (existing `def`).
- Users: none in CatCrypt-core beyond the removed theorems.

## Diffie–Hellman key agreement (finding 7), `CatCryptCore/Examples/DiffieHellman.lean`

Before:

```lean
theorem ka_secure_under_ddh (ε : ℝ≥0∞)
    (h_ddh : ∀ A : DDH_Adversary P.G₁, DDH_Advantage (elgamalDDH P) A ≤ ε)
    (D : KA_Distinguisher P.G₁) :
    KA_Advantage P D ≤ ε
```

After: removed. The existing per-distinguisher equality is the replacement, and the module
docstring names it:

```lean
theorem ka_advantage_eq_ddh (D : KA_Distinguisher P.G₁) :
    KA_Advantage P D = DDH_Advantage (elgamalDDH P) (dhReduction D)
```

Users adapted:
- `CatCryptCore/Tactics/AutoArmsTest.lean:166`: the docstring now cites `ka_advantage_eq_ddh`.
- `blueprint/src/chapters/ch23_diffiehellman.tex`: the corollary `cor:ka-secure` (`\lean{…ka_secure_under_ddh}`) was removed. No other node used it.

## OWF / PRG (findings 7 and 8), `CatCryptCore/Crypto/Assumptions/OWF.lean`

Before:

```lean
def OWFSecure (F : OWFDef W) (ε : ℝ≥0∞) : Prop :=
  ∀ (A : OWF_Adversary W), OWF_Advantage F A ≤ ε
def PRGSecure (G : PRGDef Seed Output) (ε : ℝ≥0∞) : Prop :=
  ∀ (A : PRG_Adversary Output), PRG_Advantage G A ≤ ε
class PRGImpliesOWF (G : PRGDef W W) : Prop where
  bound : ∀ (A_owf : OWF_Adversary W),
    OWF_Advantage (owf_of_prg G.stretch) A_owf ≤
      PRG_Advantage G (prg_distinguisher_of_owf_inverter G A_owf)
theorem prg_implies_owf (G : PRGDef W W) [PRGImpliesOWF G] (A_owf : OWF_Adversary W) : …
theorem prg_secure_implies_owf_secure (G : PRGDef W W) [PRGImpliesOWF G]
    (ε : ℝ≥0∞) (h_prg : PRGSecure G ε) : OWFSecure (owf_of_prg G.stretch) ε
```

After (all five declarations above are removed):

```lean
theorem owf_game_eq_prg_real (G : PRGDef W W) (A_owf : OWF_Adversary W) :
    OWF_Game (owf_of_prg G.stretch) A_owf =
      (prg_real G).bind (prg_distinguisher_of_owf_inverter G A_owf)

theorem prTrue_prg_ideal_distinguisher_le (G : PRGDef W W) (A_owf : OWF_Adversary W) :
    prTrue ((prg_ideal (Output := W)).bind (prg_distinguisher_of_owf_inverter G A_owf))
        Heap.empty ≤
      ((Finset.univ.image G.stretch).card : ℝ≥0∞) / Fintype.card W

theorem owf_le_prg (G : PRGDef W W) (A_owf : OWF_Adversary W) :
    OWF_Advantage (owf_of_prg G.stretch) A_owf ≤
      PRG_Advantage G (prg_distinguisher_of_owf_inverter G A_owf) +
        ((Finset.univ.image G.stretch).card : ℝ≥0∞) / Fintype.card W
```

- The image term is `(Finset.univ.image G.stretch).card`, which is the cardinality of `Set.range G.stretch` written as a `Finset`.
- Reduction: `prg_distinguisher_of_owf_inverter` (existing `def`).
- Users: `Catalog.lean` "Reduction Status" now names `owf_le_prg` with its image term. The text "Proved (`prg_implies_owf`)" was removed.

## ODH (findings 7 and 15), `CatCryptCore/Crypto/Assumptions/ODH.lean`

Before:

```lean
def ODHSecure (D : ODHDef W) (ε : ℝ≥0∞) : Prop :=
  ∀ (A : ODH_Adversary W), ODH_Advantage D A ≤ ε

theorem odh_of_ddh_prf (D : ODHDef W) (A : ODH_Adversary W)
    (ε_ddh ε_prf : ℝ≥0∞)
    (h_ddh : ∀ (B : DDH_Adversary W), DDH_Advantage D.toDDHDef B ≤ ε_ddh)
    (h_prf : Advantage (ODH_Hybrid D A) (ODH_Game_Ideal D A) ≤ ε_prf) :
    ODH_Advantage D A ≤ ε_ddh + ε_prf
```

After (both declarations above are removed):

```lean
def ODHDef.toPRFDef (D : ODHDef W) : PRFDef W where
  eval := D.hash

noncomputable def ddhAdvOfODH (D : ODHDef W) (A : ODH_Adversary W) : DDH_Adversary W
noncomputable def prfAdvOfODH (D : ODHDef W) (A : ODH_Adversary W) : W → SPComp Bool

theorem odh_real_hybrid_eq_ddh (D : ODHDef W) (A : ODH_Adversary W) :
    Advantage (ODH_Game_Real D A) (ODH_Hybrid D A) =
      DDH_Advantage D.toDDHDef (ddhAdvOfODH D A)

theorem odh_hybrid_eq_prf_real (D : ODHDef W) (A : ODH_Adversary W) :
    ODH_Hybrid D A = (SPComp.sample W).bind fun label =>
      (PRF_Real D.toPRFDef label).bind (prfAdvOfODH D A)

theorem prTrue_odh_ideal_eq_prf_ideal (D : ODHDef W) (A : ODH_Adversary W) :
    prTrue (ODH_Game_Ideal D A) Heap.empty =
      prTrue ((SPComp.sample W).bind fun label =>
        (PRP_Ideal label).bind (prfAdvOfODH D A)) Heap.empty

theorem advantage_sample_bind_le_avg {α : Type} [Fintype α] [Nonempty α]
    (f g : α → SPComp Bool) :
    Advantage ((SPComp.sample α).bind f) ((SPComp.sample α).bind g) ≤
      ∑ x : α, (Fintype.card α : ℝ≥0∞)⁻¹ * Advantage (f x) (g x)

theorem odh_le_ddh_add_prf (D : ODHDef W) (A : ODH_Adversary W) :
    ODH_Advantage D A ≤ DDH_Advantage D.toDDHDef (ddhAdvOfODH D A) +
      ∑ label : W, (Fintype.card W : ℝ≥0∞)⁻¹ *
        PRF_Advantage D.toPRFDef label (prfAdvOfODH D A)
```

- Reductions: `ddhAdvOfODH` and `prfAdvOfODH`. Before, `ddhAdvOfODH` was a local `let` inside `odh_of_ddh_prf`. `prfAdvOfODH` is new.
- The PRF term averages the single-query PRF advantage (`Assumptions/PRP.lean`) over the uniformly sampled label, as the report specifies (`E_label`).
- The file now imports `CatCryptCore.Crypto.Assumptions.PRP`.

Users adapted:
- `Catalog.lean` "Reduction Status" now names `odh_le_ddh_add_prf`.
- `blueprint/src/chapters/ch07_assumptions.tex`, lemma `def:odh-reduction`: it now points to `odh_le_ddh_add_prf` and states the per-adversary bound.

## CR / TCR / Pre (findings 7 and 8), `CatCryptCore/Crypto/Assumptions/CR.lean`

Before (unkeyed hash `hash : Input → Output`):

```lean
class CRSearchSecure (h : HashScheme) (ε : ℝ≥0∞) : Prop where
  cr_bound : ∀ A, CR_Search_Advantage h A ≤ ε
class TCRSecure (h : HashScheme) [SampleableType h.Input] (ε : ℝ≥0∞) : Prop where
  tcr_bound : ∀ A, TCR_Advantage h A ≤ ε
class PreSecure (h : HashScheme) [SampleableType h.Input] (ε : ℝ≥0∞) : Prop where
  pre_bound : ∀ A, Pre_Advantage h A ≤ ε
theorem CRSecure_implies_TCRSecure (h : HashScheme) [SampleableType h.Input]
    (ε : ℝ≥0∞) [hCR : CRSearchSecure h ε] : TCRSecure h ε
class CRImpliesPre (h : HashScheme) [SampleableType h.Input] : Prop where
  bound : ∀ {ε} (h_compress : Fintype.card h.Input > Fintype.card h.Output)
    (hCR : CRSearchSecure h ε) (A : h.Output → SPComp h.Input),
    Pre_Advantage h A ≤ ε
theorem CRSecure_implies_PreSecure (h : HashScheme) [SampleableType h.Input] [CRImpliesPre h]
    (ε : ℝ≥0∞) [hCR : CRSearchSecure h ε]
    (h_compress : Fintype.card h.Input > Fintype.card h.Output) : PreSecure h ε
```

After: all six declarations above are removed. `HashScheme` is now a keyed family. Each game
samples `k ← Key` and gives `k` to the adversary.

```lean
structure HashScheme where
  Key : Type
  Input : Type
  Output : Type
  [instFintypeKey : Fintype Key]
  [instNeKey : Nonempty Key]
  [instFintypeOut : Fintype Output]
  [instNeOut : Nonempty Output]
  [instDecEqOut : DecidableEq Output]
  [instDecEqIn : DecidableEq Input]
  hash : Key → Input → Output

abbrev CR_Search_Adversary (h : HashScheme) := h.Key → SPComp (h.Input × h.Input)
abbrev TCR_Adversary := h.Key → h.Input → h.Output → SPComp h.Input
abbrev Pre_Adversary := h.Key → h.Output → SPComp h.Input

noncomputable def tcrToCR (A : TCR_Adversary h) : CR_Search_Adversary h
noncomputable def preToCR (A : Pre_Adversary h) : CR_Search_Adversary h

theorem tcr_eq_cr (A : TCR_Adversary h) :
    TCR_Advantage h A = CR_Search_Advantage h (tcrToCR h A)

theorem sum_prTrue_bind_eq_le_one (c : SPComp h.Input) (h₀ : Heap) :
    ∑ x : h.Input, prTrue (c.bind fun x' => SPComp.pure (decide (x' = x))) h₀ ≤ 1

theorem prTrue_bind_decide_le_add {α : Type} (c : SPComp α) (P Q R : α → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hPQR : ∀ a, P a → Q a ∨ R a) (h₀ : Heap) :
    prTrue (c.bind fun a => SPComp.pure (decide (P a))) h₀ ≤
      prTrue (c.bind fun a => SPComp.pure (decide (Q a))) h₀ +
        prTrue (c.bind fun a => SPComp.pure (decide (R a))) h₀

theorem pre_le_cr (A : Pre_Adversary h) :
    Pre_Advantage h A ≤ CR_Search_Advantage h (preToCR h A) +
      (Fintype.card h.Output : ℝ≥0∞) / Fintype.card h.Input
```

- In the TCR and Pre games, `h` carries the section variables `[Fintype h.Input] [Nonempty h.Input]`. The former `[SampleableType h.Input]` is gone, so the game no longer has a second `DecidableEq h.Input` instance.
- The TCR game keeps its former shape: the target `x` is sampled uniformly and the adversary receives `(k, x, hash k x)`. The docstrings call this second-preimage resistance on a random target.
- `pre_le_cr` proves a bound stronger than the `2·CR_Search_Advantage h (preToCR A) + |Out|/|In|` that the report asks for: the CR term has coefficient 1. The theorem needs no compression hypothesis, because the bound is at least 1 when `|Output| ≥ |Input|`.
- Reductions: `tcrToCR` (before: a local `let` in `CRSecure_implies_TCRSecure`) and `preToCR` (new).
- Users: no Lean declaration in CatCrypt-core used the removed classes or theorems. `Catalog.lean:52,54` name `CR_Search_Advantage` and `TCR_Advantage`, which still exist. The blueprint did not reference the removed names.

## Users outside CatCrypt-core

`VACUITY_SWEEP_REPORT.md` names no users outside CatCrypt-core for findings 7, 8 and 15
(`odh_of_ddh_prf`). Its tables list only users inside this repository, and those are
adapted above. This branch did not search other repositories.

## Builds

Environment: `bash /home/user/catcrypt-cloud-cache/cloud-setup.sh` exited 0. Lean 4.33.1.

The edited modules and their importers were found by computing the transitive closure of
`import` lines over `CatCryptCore/` (equivalent to `grep -rn`).

| Edited module | Importers (transitive) |
|---|---|
| `Crypto/Assumptions/CDH`, `CoCDH`, `ODH`, `OWF`, `CR` | `Crypto/Assumptions/Catalog`, `Crypto/BLSSig/Security` (CoCDH only), umbrella `CatCryptCore` |
| `Crypto/BLSSig/Security`, `Examples/DiffieHellman` | umbrella `CatCryptCore` |
| `Tactics/AutoArmsTest` (docstring only) | none |

Final command, run after the last commit:

```
lake build CatCryptCore.Crypto.Assumptions.CDH CatCryptCore.Crypto.Assumptions.CoCDH \
  CatCryptCore.Crypto.Assumptions.ODH CatCryptCore.Crypto.Assumptions.OWF \
  CatCryptCore.Crypto.Assumptions.CR CatCryptCore.Crypto.Assumptions.Catalog \
  CatCryptCore.Crypto.BLSSig.Security CatCryptCore.Examples.DiffieHellman \
  CatCryptCore.Tactics.AutoArmsTest
```

Result:
- Exit code 0: `Build completed successfully (2775 jobs).`
- No line `Built Mathlib.` appeared.
- The build printed no warnings or errors for the nine files listed.
- The base version of `CR.lean` had an unused-variable warning (`h_compress`). It is gone because that declaration was removed.
- Each module was also built on its own after its commit, with the same result.

The umbrella module `CatCryptCore` was not built, because `catcrypt-cloud-cache/CLOUD.md`
rules out aggregator targets in cloud sessions. It contains only `import` lines, and every
module it imports from the edited set was built above. The blueprint `.tex` changes were
not compiled.

## Commits

```
cfda0ae Vacuity 7: CDH per-adversary reduction cdh_le_ddh replaces CDHSecure [no-golf]
4a7b06e Vacuity 7: remove CoCDHSecure, BLSCoCDHSecure, BLSForgeSecure [no-golf]
5919c26 Vacuity 7: remove ka_secure_under_ddh (∀-DDH hypothesis) [no-golf]
756d746 Vacuity 7/8: OWF owf_le_prg replaces PRGImpliesOWF, OWFSecure, PRGSecure [no-golf]
507663e Vacuity 7/15: ODH per-adversary reduction odh_le_ddh_add_prf [no-golf]
b6d1ddb Vacuity 7/8: keyed CR family; tcr_eq_cr and pre_le_cr replace CR classes [no-golf]
```
