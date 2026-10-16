# Vacuity repairs, findings 9–13

Branch: `work/vacuity-vb2`, based on `origin/work/auto-corpus` at `7cf4a52`.
Finding numbers refer to `VACUITY_SWEEP_REPORT.md` on `work/vacuity-sweep`.
`CR_Dist_Advantage` (finding 9) is not edited here. `Crypto/Assumptions/{CDH,CoCDH,ODH,OWF,CR}.lean`, `BLSSig` and `Examples/PRG.lean` are not edited.

Commits:

| Commit | Content |
|---|---|
| `d693ddb` | Vacuity 9 |
| `e6b5f75` | Vacuity 10, and blueprint text for findings 9 and 10 |
| `f3b8597` | Vacuity 11 |
| `bc3e4ff` | Vacuity 12 |
| `10744ec` | Vacuity 13 |
| `cd2ef2a` | Module docstrings that name the replacements of removed declarations (findings 9, 10) |

No `sorry`, no `native_decide` and no axiom was added. No declaration is kept as degenerate.

Several games below take an adaptive adversary of type `OracleAdv D R α` (`Crypto/OracleAdversary.lean`), run with `OracleAdv.run` against a stateful oracle `S → D → PMF (R × S)`. The `SPComp` form of such a game is `PRPPRF.pmfGame` (`Crypto/PRPPRFSwitching.lean`). An `SPComp` function cannot keep oracle state that the adversary cannot also read and write, so the interfaces that need a query log or a lazily sampled table use `OracleAdv`.

---

## Finding 9: games every adversary wins

### 9a. `AEAD_CCA_Advantage` (`Crypto/Assumptions/AEAD.lean`)

Before:

```lean
structure AEADDef (W : Type) [SampleableType W] where
  encrypt : W → W → W → W
  decrypt : W → W → W → W

structure AEAD_CCA_Adversary (W : Type) where
  run : (W → W → SPComp W) → (W → W → SPComp (Option W)) → SPComp Bool

noncomputable def AEAD_CCA_Game_Real (D : AEADDef W) (A : AEAD_CCA_Adversary W) : SPComp Bool := do
  let key ← SPComp.sample W
  let enc_oracle : W → W → SPComp W := fun pt ad => SPComp.pure (D.encrypt key pt ad)
  let dec_oracle : W → W → SPComp (Option W) := fun ct ad =>
    SPComp.pure (some (D.decrypt key ct ad))
  A.run enc_oracle dec_oracle

noncomputable def AEAD_CCA_Game_Ideal (A : AEAD_CCA_Adversary W) : SPComp Bool := do
  let _key ← SPComp.sample W
  let enc_oracle : W → W → SPComp W := fun _pt _ad => SPComp.sample W
  let dec_oracle : W → W → SPComp (Option W) := fun _ct _ad => SPComp.pure none
  A.run enc_oracle dec_oracle

theorem AEAD_CPA_le_CCA (D : AEADDef W) (pt ad : W) (A : AEAD_Adversary W) :
    AEAD_Advantage D pt ad A ≤ AEAD_CCA_Advantage D (AEAD_CPA_to_CCA pt ad A)
```

After:

```lean
structure AEADDef (W : Type) [SampleableType W] (C : Type := W) where
  encrypt : W → W → W → C
  decrypt : W → C → W → Option W

abbrev AEAD_CCA_Query (W C : Type) := (W × W) ⊕ (C × W)
abbrev AEAD_CCA_Answer (W C : Type) := C ⊕ Option W
abbrev AEAD_CCA_Adversary (W C : Type) :=
  OracleAdv (AEAD_CCA_Query W C) (AEAD_CCA_Answer W C) Bool

noncomputable def aeadRealOracle (D : AEADDef W C) (key : W) :
    Unit → AEAD_CCA_Query W C → PMF (AEAD_CCA_Answer W C × Unit)
  | _, .inl (pt, ad) => PMF.pure (.inl (D.encrypt key pt ad), ())
  | _, .inr (ct, ad) => PMF.pure (.inr (D.decrypt key ct ad), ())

def aeadLogDecrypt (log : List ((W × W) × C)) (ct : C) (ad : W) : Option W :=
  (log.find? fun e => decide (e.2 = ct ∧ e.1.2 = ad)).map fun e => e.1.1

noncomputable def aeadIdealOracle :
    List ((W × W) × C) → AEAD_CCA_Query W C → PMF (AEAD_CCA_Answer W C × List ((W × W) × C))
  | log, .inl (pt, ad) =>
    match log.lookup (pt, ad) with
    | some ct => PMF.pure (.inl ct, log)
    | none => (PMF.uniformOfFintype C).map fun ct => (.inl ct, ((pt, ad), ct) :: log)
  | log, .inr (ct, ad) => PMF.pure (.inr (aeadLogDecrypt log ct ad), log)

noncomputable def AEAD_CCA_Game_Real (D : AEADDef W C) (A : AEAD_CCA_Adversary W C) : SPComp Bool :=
  PRPPRF.pmfGame ((PMF.uniformOfFintype W).bind fun key =>
    (OracleAdv.run (aeadRealOracle D key) A ()).map Prod.fst)

noncomputable def AEAD_CCA_Game_Ideal (A : AEAD_CCA_Adversary W C) : SPComp Bool :=
  PRPPRF.pmfGame ((OracleAdv.run aeadIdealOracle A []).map Prod.fst)

theorem AEAD_CPA_le_CCA (D : AEADDef W C) (pt ad : W) (A : C → PMF Bool) :
    AEAD_Advantage D pt ad (fun ct => PRPPRF.pmfGame (A ct)) ≤
    AEAD_CCA_Advantage D (AEAD_CPA_to_CCA pt ad A)
```

Two departures from the repair text, both needed for the game to be winnable by the scheme rather than by every adversary:

- **Ciphertext type.** With ciphertexts in `W`, a scheme whose decryption inverts encryption makes `encrypt key · ad` a bijection of `W`, so every ciphertext decrypts to `some _`. One decryption query on a ciphertext not returned by the encryption oracle then distinguishes the real game from any ideal game that rejects it. `AEADDef` therefore has a ciphertext type `C` with default `W`. The module docstring states that integrity needs `C` larger than `W`.
- **Consistent ideal encryption.** `encrypt` is deterministic. An ideal oracle that samples a fresh ciphertext on every query is distinguished by two equal queries. The ideal encryption oracle is a lazily sampled random function of `(pt, ad)`. This is the deterministic authenticated-encryption notion of Rogaway–Shrimpton (EUROCRYPT 2006), with consistent answers in place of query restrictions.

Ideal decryption answers from the log of encryption answers, as the repair text says.

The single-sample adversary in `AEAD_CPA_le_CCA` is now given as `C → PMF Bool`, lifted with `PRPPRF.pmfGame`. `AEAD_CPA_to_CCA pt ad A` is a top-level `def` that asks one encryption query. The proof shows that the two advantages are equal. Removed: `AEAD_CCA_Game_Real_isPure`, `AEAD_CCA_Game_Ideal_isPure`, `sample_bind_const`.

### 9b. `SPRP_Advantage` (`Crypto/Assumptions/PRP.lean`)

Before:

```lean
structure SPRP_Adversary (W : Type) where
  run : (enc_oracle : W → SPComp W) → (dec_oracle : W → SPComp W) → SPComp Bool

noncomputable def SPRP_Ideal (A : SPRP_Adversary W) : SPComp Bool :=
  A.run (fun _ => SPComp.sample W) (fun _ => SPComp.sample W)
```

After:

```lean
abbrev SPRP_Adversary (W : Type) := OracleAdv (W ⊕ W) W Bool

noncomputable def sprpOracle (t : List (W × W)) : W ⊕ W → PMF (W × List (W × W))
  | .inl x =>
    match t.lookup x with
    | some y => PMF.pure (y, t)
    | none => (PRPPRF.freshDist (PRPPRF.usedAnswers t)).map fun y => (y, (x, y) :: t)
  | .inr y =>
    match (t.find? fun e => decide (e.2 = y)) with
    | some e => PMF.pure (e.1, t)
    | none => (PRPPRF.freshDist (usedInputs t)).map fun x => (x, (x, y) :: t)

noncomputable def SPRP_Real (P : PRPDef W) (A : SPRP_Adversary W) : SPComp Bool :=
  PRPPRF.pmfGame ((PMF.uniformOfFintype W).bind fun k =>
    (OracleAdv.run (sprpKeyedOracle P k) A ()).map Prod.fst)

noncomputable def SPRP_Ideal (A : SPRP_Adversary W) : SPComp Bool :=
  PRPPRF.pmfGame ((OracleAdv.run sprpOracle A []).map Prod.fst)
```

The ideal oracles are a lazily sampled random permutation and its inverse, which share one table. `PRPPRF.freshDist` samples uniformly from the values not yet in the table.

### 9c. `MAC_Keyed_Advantage` (`MAC.lean`) and `AEAD_Keyed_Advantage` (`AEAD.lean`)

Before:

```lean
noncomputable def mac_keyed_real (D : MACDef W) (msg : W → W) : SPComp (W × W) :=
  SPComp.bind (SPComp.sample W) (fun key => SPComp.pure (D.mac key (msg key), key))
noncomputable def mac_keyed_ideal : SPComp (W × W) := SPComp.sample (W × W)

noncomputable def aead_keyed_real (D : AEADDef W) (pt ad : W → W) : SPComp (W × W) :=
  SPComp.bind (SPComp.sample W) (fun key =>
    SPComp.pure (D.encrypt key (pt key) (ad key), key))
noncomputable def aead_keyed_ideal : SPComp (W × W) := SPComp.sample (W × W)
```

After (the key is not output):

```lean
noncomputable def mac_keyed_real (D : MACDef W) (msg : W → W) : SPComp W :=
  SPComp.bind (SPComp.sample W) (fun key => SPComp.pure (D.mac key (msg key)))
noncomputable def mac_keyed_ideal : SPComp W := SPComp.sample W

noncomputable def aead_keyed_real (D : AEADDef W C) (pt ad : W → W) : SPComp C :=
  SPComp.bind (SPComp.sample W) (fun key =>
    SPComp.pure (D.encrypt key (pt key) (ad key)))
noncomputable def aead_keyed_ideal : SPComp C := SPComp.sample C
```

The advantages are `AdvantageA` of these games against `A : W → SPComp Bool` and `A : C → SPComp Bool`. They are single-sample games with key-dependent messages, and their docstrings say so.

### 9d. `PKE_ROM.CPA_Adv` (`Crypto/MLKEM/PKE_ROM.lean`)

Before:

```lean
noncomputable def CPA (choose : S.PK → SDistr (S.PT × S.PT))
    (guess : S.CT → SDistr Bool) (b : Bool) : SDistr Bool := ...
noncomputable def CPA_Adv (choose : S.PK → SDistr (S.PT × S.PT))
    (guess : S.CT → SDistr Bool) : ℝ≥0∞ :=
  UCMonad.SDistrUC.absDiffD
    (UCMonad.SDistrUC.prTrueD (CPA S choose guess true)) (ENNReal.ofReal (1/2))
```

After:

```lean
noncomputable def CPA {St : Type} (choose : S.PK → SDistr (S.PT × S.PT × St))
    (guess : St → S.CT → SDistr Bool) (b : Bool) : SDistr Bool := do
  let (pk, _sk) ← S.kg
  let (m0, m1, st) ← choose pk
  let c ← S.enc pk (if b then m1 else m0)
  guess st c

noncomputable def CPA_Adv {St : Type} (choose : S.PK → SDistr (S.PT × S.PT × St))
    (guess : St → S.CT → SDistr Bool) : ℝ≥0∞ :=
  UCMonad.SDistrUC.absDiffD
    (UCMonad.SDistrUC.prTrueD (CPA S choose guess true))
    (UCMonad.SDistrUC.prTrueD (CPA S choose guess false))
```

`CPA_L` and `CPA_R` take the same two-stage adversary. The docstring entries for `pr_CPA_LR` and for the adversary types `CPA_ADV`, `OW_CPA_ADV`, `OWL_CPA_ADV` and `CORR_ADV` named declarations that do not exist, and are removed.

### 9e. `MLWE.PRF_IND_Game` (`Crypto/MLKEM/MLWE.lean`)

Before:

```lean
structure PRF_Params where
  Key : Type
  Input : Type
  Output : Type
  dkey : SDistr Key
  dout : SDistr Output
  prf : Key → Input → Output

noncomputable def PRF_IND_Game (P : PRF_Params)
    (adv : (P.Input → SDistr P.Output) → SDistr Bool) (b : Bool) : SDistr Bool := do
  if b then adv (fun _ => P.dout)
  else do
    let k ← P.dkey
    adv (fun x => SDistr.pure (P.prf k x))
```

After:

```lean
structure PRF_Params where
  Key : Type
  Input : Type
  Output : Type
  [decInput : DecidableEq Input]
  [decOutput : DecidableEq Output]
  [finOutput : Fintype Output]
  [neOutput : Nonempty Output]
  dkey : SDistr Key
  prf : Key → Input → Output

noncomputable def PRF_IND_Game (P : PRF_Params)
    (adv : OracleAdv P.Input P.Output Bool) (b : Bool) : SDistr Bool :=
  if b then
    (OracleAdv.run PRPPRF.rfOracle adv []).map fun x => some x.1
  else
    P.dkey.bind fun k =>
      (OracleAdv.run (PRPPRF.keyedOracle P.prf k) adv ()).map fun x => some x.1
```

The ideal oracle is the lazily sampled random function `PRPPRF.rfOracle` with uniform values. The field `dout` is removed. `MLWE.lean` now imports `Crypto/PRPPRFSwitching.lean`.

**Reductions defined (finding 9):** `AEAD_CPA_to_CCA`.

**Users adapted in CatCrypt-core:** `Crypto/Assumptions/Catalog.lean` (table rows for `AEAD_CCA_Advantage`, `SPRP_Advantage`, `AEAD_Keyed_Advantage`, `MAC_Keyed_Advantage`) and `blueprint/src/chapters/ch07_assumptions.tex` (definitions `def:sprp` and `def:aead-cca`). `grep -rn` finds no other user of the changed declarations.

---

## Finding 10: weak or misnamed definitions

### 10a. `EUF_CMA_Real` / `EUF_CMA_Adv` (`Crypto/SecurityDefs.lean`)

Before:

```lean
noncomputable def EUF_CMA_Real (M : MACScheme) (m : M.Message) (m_star : M.Message)
    (t_star : M.Tag) : SPComp Bool := do
  let k ← SPComp.sample M.Key
  let _t := M.mac k m
  SPComp.pure (M.verify k m_star t_star)

noncomputable def EUF_CMA_Adv (M : MACScheme) (m m_star : M.Message) (t_star : M.Tag)
    (A : Bool → SPComp Bool) : ℝ≥0∞ :=
  prTrue (EUF_CMA_Real M m m_star t_star >>= A) Heap.empty
```

After:

```lean
noncomputable def macTagOracle (M : MACScheme) (k : M.Key) (log : List M.Message)
    (m : M.Message) : PMF (M.Tag × List M.Message) :=
  PMF.pure (M.mac k m, m :: log)

abbrev EUF_CMA_Adversary (M : MACScheme) := OracleAdv M.Message M.Tag (M.Message × M.Tag)

open Classical in
noncomputable def EUF_CMA_Real (M : MACScheme) (A : EUF_CMA_Adversary M) : PMF Bool :=
  (PMF.uniformOfFintype M.Key).bind fun k =>
    (OracleAdv.run (macTagOracle M k) A []).map fun r =>
      M.verify k r.1.1 r.1.2 && decide (r.1.1 ∉ r.2)

noncomputable def EUF_CMA_Adv (M : MACScheme) (A : EUF_CMA_Adversary M) : ℝ≥0∞ :=
  EUF_CMA_Real M A true
```

The adversary queries the tagging oracle adaptively. It wins with a valid tag on a message that is not in the query log.

User adapted: `Examples/MAC.lean`. The bijection-family MAC gives no bound after one tag query: for the XOR MAC, one tag determines the key. The adapted statement is the one that holds, for adversaries without tag queries:

```lean
theorem bijMAC_euf_cma_adv_of_isQueryBound_zero (B : BijMACFamily)
    (A : EUF_CMA_Adversary B.toMACScheme) (hA : A.IsQueryBound 0) :
    EUF_CMA_Adv B.toMACScheme A = 1 / (Fintype.card B.Tag : ℝ≥0∞)

theorem boolXorMAC_euf_cma_adv_of_isQueryBound_zero
    (A : EUF_CMA_Adversary boolXorMAC.toMACScheme) (hA : A.IsQueryBound 0) :
    EUF_CMA_Adv boolXorMAC.toMACScheme A = 1 / 2
```

These replace `bijMAC_forgery_prob`, `bijMAC_euf_cma_adv` and `boolXorMAC_forgery_prob`. The auxiliary lemma `bijMAC_forgery_prob_key` is new. Information-theoretic: numeric bounds, no reduction.

### 10b. `uh_forge_real` (`Examples/UniversalHash.lean`)

Before:

```lean
noncomputable def uh_forge_real (H : UHFamily) (_m m_star : H.MsgType)
    (t_star : H.TagType) : SPComp Bool := do
  let k ← SPComp.sample H.KeyType
  SPComp.pure (t_star == H.hash k m_star)

theorem boolHash_forge_advantage (m m_star : Bool) (t_star : Bool)
    (h_diff : m_star ≠ m) (A : Bool → SPComp Bool) :
    UH_Forgery_Advantage boolPairwiseHash m m_star t_star A ≤ (2 : ENNReal)⁻¹
```

After (one-time forgery game; the adversary sees the tag of `m`):

```lean
open Classical in
noncomputable def uh_forge_game (H : UHFamily) (m : H.MsgType)
    (A : H.TagType → SPComp (H.MsgType × H.TagType)) : SPComp Bool :=
  SPComp.bind (SPComp.sample H.KeyType) fun k =>
    SPComp.bind (A (H.hash k m)) fun f =>
      SPComp.pure (decide (f.1 ≠ m) && f.2 == H.hash k f.1)

noncomputable def UH_Forgery_Prob (H : UHFamily) (m : H.MsgType)
    (A : H.TagType → SPComp (H.MsgType × H.TagType)) : ENNReal :=
  prTrue (uh_forge_game H m A) Heap.empty

theorem boolHash_forge_prob_le (m : Bool) (A : Bool → SPComp (Bool × Bool)) :
    UH_Forgery_Prob boolPairwiseHash m A ≤ (2 : ENNReal)⁻¹

theorem boolPairwiseHash_mac_security (m : Bool) (A : Bool → SPComp (Bool × Bool)) :
    UH_Forgery_Prob boolPairwiseHash m A ≤ boolPairwiseHash.epsilon
```

The message `m` is a parameter, and the bound holds for every `m`. New auxiliary lemmas: `prTrue_bind_pure_test` and `prTrue_bind_pure_test_add_le`. Removed: `uh_forge_real`, `uh_forge_ideal`, `UH_Forgery_Advantage`, their purity lemmas, `forge_prTrue_eq` and `boolHash_forge_advantage`. Information-theoretic.

### 10c. `GapDHDef` / `GapDH_Advantage` (`Crypto/Assumptions/GapDH.lean`)

Before:

```lean
structure GapDHDef (W : Type) [SampleableType W] where
  dh : W → W → W
  keygen : SPComp (W × W)
  keygen_isPure : SPComp.IsPure keygen

abbrev GapDH_Adversary (W : Type) := W → W → W → SPComp Bool

noncomputable def GapDH_Advantage (G : GapDHDef W) (A : GapDH_Adversary W) : ℝ≥0∞ :=
  Advantage (GapDH_Game_Real G A) (GapDH_Game_Ideal G A)   -- DDH game, no oracle

def GapDHDef.ofDDH (D : DDHDef W) : GapDHDef W := ⟨D.ecdh, D.keygen, D.keygen_isPure⟩
```

After:

```lean
structure GapDHDef (W : Type) [SampleableType W] where
  dh : W → W → W
  cdh : W → W → W
  keygen : SPComp (W × W)
  keygen_isPure : SPComp.IsPure keygen

def ddhOracle (G : GapDHDef W) (X Y Z : W) : Bool := decide (Z = G.cdh X Y)

abbrev GapDH_Adversary (W : Type) := (W → W → W → Bool) → W → W → SPComp W

noncomputable def GapDH_Game (G : GapDHDef W) (A : GapDH_Adversary W) : SPComp Bool := do
  let ⟨_a, pub_a⟩ ← G.keygen
  let ⟨_b, pub_b⟩ ← G.keygen
  let Z ← A (ddhOracle G) pub_a pub_b
  pure (decide (Z = G.cdh pub_a pub_b))

noncomputable def GapDH_Advantage (G : GapDHDef W) (A : GapDH_Adversary W) : ℝ≥0∞ :=
  prTrue (GapDH_Game G A) Heap.empty
```

GapDH is now a search game with the oracle `(X, Y, Z) ↦ decide (Z = CDH(X, Y))`, as the repair text says. The oracle is deterministic, so it is passed as a function. Evaluating it on arbitrary triples needs the Diffie–Hellman function on public keys, so `GapDHDef` has the new field `cdh`; the structure states no relation between `cdh` and `dh`. `GapDHDef.ofDDH` is removed, because a DDH group does not provide `cdh`. The docstring claim that GapDH is implied by DDH is removed from `GapDH.lean`, `Catalog.lean` and `blueprint/src/chapters/ch07_assumptions.tex`. The game is computational and no bound is stated.

### 10d. `MLWE_PKE_Basic.CPA_Game` / `CPA_Adv` (`Crypto/MLKEM/MLWE_PKE_Basic.lean`)

The declarations are kept, because `MLWE_PKE_Stateful` uses them in `CPA_Game_eq_CPA_Game_st`, `CPA_Adv_eq_CPA_Adv_st` and `main_theorem_of_st`. Their docstrings and the docstring of `main_theorem` now say that the guess stage receives neither the public key nor a state. They also say that these declarations are superseded by `MLWE_PKE_Stateful.CPA_Game_st`, `CPA_Adv_st` and `main_theorem_st`. The module docstring says the same. The Lean statements are unchanged.

### 10e. `OW_CPA_perfect` / `ow_perfect` (`Crypto/MLKEM/PKE_ROM.lean`)

Before:

```lean
noncomputable def OW_CPA_perfect (find : S.PK → S.CT → SDistr (Option S.PT)) : SDistr Bool := do
  let (pk, _sk) ← S.kg
  let m ← SDistr.uniform S.PT
  let c ← S.enc pk m
  let m' ← find pk c
  SDistr.pure (m' == some m)                       -- identical to OW_CPA

noncomputable def BOWp (find : S.PK → S.CT → SDistr (Option S.PT)) :
    S.PK → S.SK → SDistr S.PT := ...               -- returned the output of find

theorem ow_perfect (find : S.PK → S.CT → SDistr (Option S.PT)) :
    absDiffD (prTrueD (OW_CPA S find)) (prTrueD (OW_CPA_perfect S find)) ≤
    prTrueD (Correctness_Adv S (BOWp S find))       -- proved via OW_CPA = OW_CPA_perfect
```

After:

```lean
noncomputable def OW_CPA_perfect (find : S.PK → S.CT → SDistr (Option S.PT)) : SDistr Bool := do
  let (pk, sk) ← S.kg
  let m ← SDistr.uniform S.PT
  let c ← S.enc pk m
  let m' ← find pk c
  let md ← S.dec sk c
  SDistr.pure (m' == md)

noncomputable def BOWp : S.PK → S.SK → SDistr S.PT := fun _pk _sk =>
  SDistr.uniform S.PT

theorem ow_perfect (hdec : ∀ sk c, S.dec sk c none = 0)
    (find : S.PK → S.CT → SDistr (Option S.PT)) :
    UCMonad.SDistrUC.absDiffD
      (UCMonad.SDistrUC.prTrueD (OW_CPA S find))
      (UCMonad.SDistrUC.prTrueD (OW_CPA_perfect S find)) ≤
    UCMonad.SDistrUC.prTrueD (Correctness_Adv S (BOWp S))
```

The bound is the decryption-failure probability of an honestly encrypted uniform plaintext.

- **Changed `BOWp`.** The previous `BOWp` returned the adversary's output. The correctness game then re-encrypts that output, so the bound does not follow from the difference of the two OW games. `BOWp` therefore returns a uniform plaintext.
- **Hypothesis `hdec`.** It says that decryption puts no mass on failure to terminate. Without it, the dummy decryption in the coupling changes the mass of `OW_CPA`: with `dec` of mass `0`, `OW_CPA_perfect` has probability `0` while `OW_CPA` does not.

The proof works pointwise, using three new auxiliary lemmas: `SDistr.bind_apply_le_add`, `SDistr.bind_const_apply_some_le` and `SDistr.bind_const_pure_apply_some`. They are declared in `PKE_ROM.lean` under the namespace `CatCrypt.Prob.SDistr`. `ow_perfect` has no users.

### 10f. Pedersen UC (`Crypto/Commitment/PedersenUC.lean`)

Before, a single theorem:

```lean
theorem pedersen_uc_secure (crs : PedersenCRS gp)
    (ht : crs.trapdoor ≠ gp.scalarZero) (V : Type) :
    UCEmulates 0 (pedersenSpec gp V) (pedersen_real gp crs) (pedersen_ideal gp crs)
```

After, the repair splits it into two statements:

```lean
-- the former pedersen_uc_secure, relabelled; the ideal hands (s, m) to the simulator
theorem pedersen_uc_commit_open (crs : PedersenCRS gp)
    (ht : crs.trapdoor ≠ gp.scalarZero) (V : Type) :
    UCEmulates 0 (pedersenSpec gp V) (pedersen_real gp crs) (pedersen_ideal gp crs)

noncomputable def pedersen_commit_real (crs : PedersenCRS gp) :
    gp.Scalar → SPComp (Unit ⊕ gp.Scalar) :=
  fun m => do
    let r ← SPComp.sample gp.Scalar
    SPComp.pure (.inr (gp.scalarAdd m (gp.scalarMul crs.trapdoor r)))

noncomputable def pedersen_commit_ideal (_crs : PedersenCRS gp) :
    gp.Scalar → SPComp (Unit ⊕ Unit) :=
  fun _m => SPComp.pure (.inr ())

noncomputable def pedersen_commit_sim (view : Type) (A : gp.Scalar → SPComp view) :
    Unit → SPComp view :=
  fun _ => SPComp.bind (SPComp.sample gp.Scalar) A

theorem pedersen_uc_commit_phase (crs : PedersenCRS gp)
    (ht : crs.trapdoor ≠ gp.scalarZero) (V : Type) :
    UCEmulates 0 (pedersenCommitSpec gp V)
      (pedersen_commit_real gp crs) (pedersen_commit_ideal gp crs)
```

- **`pedersen_uc_commit_phase`.** The simulator learns only that a commitment was made, so this statement expresses hiding.
- **`pedersen_uc_commit_open`.** Its docstring states that the simulator receives `m`, so the statement does not express hiding. It also states that the exponent `s` is sampled independently of `m` and that the simulator opens `s` to `m` with the trapdoor.

A single two-phase statement, in which the same simulator first produces the commitment and later opens it, cannot be expressed with `UCEmulates`: its adversary receives the leak in one step. `pedersen_commit_view_eq` is a new auxiliary lemma. The module docstring is rewritten accordingly. User adapted: a comment in `Crypto/UCMonad/UCLeakageDecomp.lean`. Information-theoretic.

### 10g. `PerfectKEM_CPA` (`Examples/KEMDEM.lean`)

`PerfectKEM_CPA` requires the real and ideal KEM games to be equal. For a correct KEM the encapsulated key is a function of `(pk, ek)` on the support, so equality with an independent uniform key forces `|Key| = 1`. The results that assumed it therefore applied only to incorrect KEMs or to `|Key| = 1`. These declarations are deleted:

- `PerfectKEM_CPA`;
- `pke_real_eq_hybrid1` and `hybrid2_eq_pke_ideal`;
- `pke_perfect_security`;
- `xorHybrid_perfect_security` and `xorHybrid_advantage_zero`.

Replacements, derived from `pke_security` (named reductions `ReductionKEM1`, `ReductionDEM`, `ReductionKEM2`):

```lean
theorem pke_security_of_perfectDEM ... (KEM : KEMScheme PKey SKey Key EKey)
    (DEM : DEMScheme Key Plain Cipher) (nullPlain : Plain)
    (hDEM : PerfectDEM_CPA DEM nullPlain) (m : Plain)
    (A : PKey × EKey × Cipher → SPComp Bool) :
    PKE_CPA_Advantage (HybridPKE KEM DEM) nullPlain m A ≤
      KEM_CPA_Advantage KEM (ReductionKEM1 DEM m A) +
      KEM_CPA_Advantage KEM (ReductionKEM2 DEM nullPlain A)

theorem xorHybrid_advantage_le ... (KEM : KEMScheme PKey SKey Bool EKey) (m : Bool)
    (A : PKey × EKey × Bool → SPComp Bool) :
    PKE_CPA_Advantage (HybridPKE KEM BoolXorDEM) false m A ≤
      KEM_CPA_Advantage KEM (ReductionKEM1 BoolXorDEM m A) +
      KEM_CPA_Advantage KEM (ReductionKEM2 BoolXorDEM false A)
```

`PerfectDEM_CPA` is satisfiable (`boolXorDEM_perfect`) and is kept, as is `hybrid1_eq_hybrid2`.

**Reductions defined (finding 10):** none new. `ReductionKEM1` and `ReductionKEM2` exist already.

**Users adapted in CatCrypt-core (finding 10):**

- `Examples/MAC.lean`;
- `Crypto/UCMonad/UCLeakageDecomp.lean` (comment);
- `Crypto/Assumptions/Catalog.lean`;
- `JoyOfCrypto.md` (rows 10 and 15);
- `blueprint/src/chapters/ch03_advantage.tex` (`def:eufcma-adv`);
- `ch07_assumptions.tex` (`def:gapdh`);
- `ch15_kemdem.tex` (`thm:kemdem-perfect`);
- `ch18_mac.tex` (`thm:bijmac-forgery`, `cor:xormac`);
- `ch27_symmetric_more.tex` (`thm:uhf-mac`).

---

## Finding 11: `CiphertextPseudorandom` (`Crypto/OT/DualModeOT.lean`)

Before:

```lean
noncomputable def CiphertextPseudorandom (ε : ℝ≥0∞) : Prop :=
  ∀ (pk : gp.G) (m : gp.G),
    sdist (fun (_ : Unit) => SPComp.bind (SPComp.sample gp.Scalar)
            (fun r => SPComp.pure (dualEnc gp pk m r)))
          (fun (_ : Unit) => SPComp.sample gp.G) ≤ ε

theorem dualOT_uc_secure (crs : DualModeCRS gp)
    (ε : ℝ≥0∞) (hcpr : CiphertextPseudorandom gp ε) (V : Type) :
    UCEmulates ε (dualOTSpec gp V) (dualOT_real gp crs) (dualOT_ideal gp crs)
```

After: both declarations are deleted.

- **Quantifying over `pk ≠ 1`.** This would give a hypothesis that holds at `ε = 0` for every group (`sdist_dualEnc_uniform`), so it adds nothing to the existing theorem.
- **Replacement.** The kept theorem is

  ```lean
  theorem dualOT_uc_secure_zero (crs : DualModeCRS gp)
      (h0 : crs.pk₀ ≠ gp.identity) (h1 : crs.pk₁ ≠ gp.identity) (V : Type) :
      UCEmulates 0 (dualOTSpec gp V) (dualOT_real gp crs) (dualOT_ideal gp crs)
  ```

- **Per-key bound.** `dualOT_reduction` is kept. It takes the per-key hypotheses on `crs.pk₀` and `crs.pk₁`.
- **Docstrings.** The module docstring names the replacement.

User adapted: a comment in `Crypto/UCMonad/UCLeakageDecomp.lean`.

The report's modelling remark about this file is not addressed: the ciphertext has no `g^r` component, the receiver output is `Unit`, and there is no correctness statement.

---

## Finding 12: `correctness_theorem` (`Crypto/MLKEM/MLWE_PKE_Basic.lean`)

Before:

```lean
theorem correctness_theorem (fail_prob : ℝ≥0∞)
    (find : PK P → SK P → SDistr P.PT)
    (h_fail : prTrue (Correctness_Game P find) ≤ fail_prob) :
    prTrue (Correctness_Game P find) ≤ fail_prob :=
  h_fail
```

After:

```lean
noncomputable def failProb (k : PK P × SK P) (m : P.PT) : ℝ≥0∞ :=
  prTrue (do
    let c ← enc P k.1 m
    let m' ← dec P k.2 c
    SDistr.pure (decide (m' ≠ some m)))

noncomputable def corrWorst : ℝ≥0∞ :=
  ⨆ (k : PK P × SK P) (m : P.PT), failProb P k m

theorem correctness_le_corrWorst (find : PK P → SK P → SDistr P.PT) :
    prTrue (Correctness_Game P find) ≤ corrWorst P
```

The adversarial correctness game is bounded by the worst-case failure probability, over all key pairs and messages, of the basic scheme. `corrWorst` is not bounded numerically here: `Params` has no norm or noise tail bound, as the removed docstring stated. The auxiliary lemma `SDistr.bind_apply_some_le_iSup` is new. The module docstring names the replacement. There were no users.

---

## Finding 13: `SHVZK` (`Crypto/ZK/SigmaUCZK.lean`)

Before:

```lean
def SHVZK : Prop :=
  ∀ (x : sp.Statement) (w : sp.Witness) (e : sp.Challenge),
    (do let a ← sp.commit x w
        let z ← sp.respond x w a e
        SPComp.pure (a, z)) =
    sp.simulate x e

noncomputable def sigma_real : sp.Statement × sp.Witness → SPComp (Unit ⊕ Transcript sp) :=
  fun ⟨x, w⟩ => do ...                                 -- runs for every (x, w)
noncomputable def sigma_ideal : sp.Statement × sp.Witness → SPComp (Unit ⊕ sp.Statement) :=
  fun ⟨x, _w⟩ => SPComp.pure (.inr x)
```

After:

```lean
def SHVZK : Prop :=
  ∀ (x : sp.Statement) (w : sp.Witness) (e : sp.Challenge), sp.relation x w →
    (do let a ← sp.commit x w
        let z ← sp.respond x w a e
        SPComp.pure (a, z)) =
    sp.simulate x e

open Classical in
noncomputable def sigma_real : sp.Statement × sp.Witness → SPComp (Unit ⊕ Transcript sp) :=
  fun ⟨x, w⟩ =>
    if sp.relation x w then do
      let a ← sp.commit x w
      let e ← SPComp.sample sp.Challenge
      let z ← sp.respond x w a e
      SPComp.pure (.inr ⟨a, e, z⟩)
    else SPComp.pure (.inl ())

open Classical in
noncomputable def sigma_ideal : sp.Statement × sp.Witness → SPComp (Unit ⊕ sp.Statement) :=
  fun ⟨x, w⟩ => if sp.relation x w then SPComp.pure (.inr x) else SPComp.pure (.inl ())
```

The proofs of `sigma_view_eq` and `sigma_uc_zk_secure` (unchanged statement: `SHVZK sp → UCEmulates 0 …`) split on the relation. New in this file:

```lean
theorem simpleSigma_SHVZK : SHVZK simpleSigma
theorem simpleSigma_uc_zk (V : Type) :
    UCEmulates 0 (sigmaUCZKSpec simpleSigma V) (sigma_real simpleSigma) (sigma_ideal simpleSigma)
```

These show that the repaired hypothesis holds for the XOR Σ-protocol of `Examples/SigmaProtocol.lean`. There were no other users. Information-theoretic.

---

## Users outside CatCrypt-core

`VACUITY_SWEEP_REPORT.md` names no user outside CatCrypt-core, with file and line, for findings 9–13. The only users it names are the catalogue (`Catalog.lean`, adapted) and `AEAD_CPA_le_CCA` (adapted).

The pre-repair docstrings in this repository mention protocol developments outside it that use some of the changed definitions. Their files were not available in this session, so no file:line can be given:

- `AEAD.lean`: EDHOC, SSH, Kerberos and HPKE multi-message use `AEAD_Keyed_Advantage`. These need the new `AEADDef` signature: `decrypt` returns `Option W`, there is a ciphertext type `C` with default `W`, and the keyed game no longer outputs the key.
- `MAC.lean`: SSH and Kerberos use `MAC_Keyed_Advantage`. The keyed game no longer outputs the key.
- `GapDH.lean`: WireGuard uses `GapDH_Advantage`. The game is now a search game, `GapDHDef` has the field `cdh`, and `GapDHDef.ofDDH` is removed.
- `Catalog.lean`: its protocol usage matrix lists EDHOC, SSH and Kerberos for `AEAD_Keyed`, and HPKE and TLS for `AEAD`.

## Builds

Setup: `bash /home/user/catcrypt-cloud-cache/cloud-setup.sh` exited with code 0. No build printed `Built Mathlib.`.

Builds ran from the repository root with `export PATH=$HOME/.elan/bin:$PATH`. A build counts as successful when it printed `Build completed successfully` and exited with code 0.

| Command | State | Result |
|---|---|---|
| `lake build CatCryptCore` | base `7cf4a52` | success, 3706 jobs |
| `lake build CatCryptCore.Crypto.MLKEM.MLWE` | finding 9, in progress | success, 2698 jobs |
| `lake build CatCryptCore` | finding 9 | success, 3706 jobs |
| `lake build CatCryptCore.Crypto.SecurityDefs CatCryptCore.Crypto.Assumptions.GapDH CatCryptCore.Examples.KEMDEM` | finding 10, in progress | success, 2698 jobs |
| `lake build CatCryptCore` | finding 10 | success, 3706 jobs |
| `lake build CatCryptCore` | finding 11 | success, 3706 jobs |
| `lake build CatCryptCore` | finding 12 | success, 3706 jobs |
| `lake build CatCryptCore.Crypto.MLKEM.MLWE_PKE_Basic` | finding 12, module docstring | success, 2700 jobs |
| `lake build CatCryptCore` | finding 13 | success, 3706 jobs |
| `lake build CatCryptCore` | `cd2ef2a` (HEAD before this report) | success, 3706 jobs |

`lake build CatCryptCore` builds the umbrella module and therefore every module of the library. This includes every module that imports an edited module, directly or transitively.

The lakefile passes `-E hasSorry`, so a declaration that reaches `sorryAx` fails the build.

For warnings, the warning messages of every edited `.lean` file in the final build were compared with those in the base build. The only warning in an edited file is the one that `PRP.lean` already had in the base build (unused variable `x` in `PRP_Ideal`). No edited file has a new warning.

The blueprint (`blueprint/`) and `JoyOfCrypto.md` were edited as text. They were not built.
