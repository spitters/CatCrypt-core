# Vacuity repairs vb3: findings 6, 14 and 15

Branch `work/vacuity-vb3`, based on `origin/work/auto-corpus`. Finding numbers refer to `VACUITY_SWEEP_REPORT.md` on `origin/work/vacuity-sweep`. Finding 15's row `odh_of_ddh_prf` is not part of this task and was not touched. `Crypto/Assumptions/{CDH,CoCDH,ODH,OWF,CR}.lean` and `BLSSig` were not edited.

All new statements are per-adversary. The only terms bounded by numbers are information-theoretic: the switching term, the collision term, the 1/2 forgery gap, and the hash-uniformity hypothesis. The single-sample game `PRF_Adv` appears on right-hand sides only as the advantage of named reductions.

## Finding 14: `triple_prg_bound_of_assumption` / `triple_prg_uniform_bound` (Examples/PRG.lean), and finding 7: `PRGAssumption.bound`

**Before.**
```lean
structure PRGAssumption (G : PRGScheme) where
  ε : ℝ≥0∞
  bound : ∀ (A : G.Output → SPComp Bool), PRG_Adv G A ≤ ε

theorem triple_prg_uniform_bound (G : DoublePRG) (ε : ℝ≥0∞)
    (A : (G.Seed × G.Seed × G.Seed) → SPComp Bool)
    (h_inner : AdvantageA (G.hyb 0) (G.hyb 1) A ≤ ε)
    (h_outer : AdvantageA (G.hyb 1) (G.hyb 2) A ≤ ε) :
    AdvantageA (G.hyb 0) (G.hyb 2) A ≤ 2 * ε

theorem triple_prg_bound_of_assumption (G : DoublePRG)
    (Hin : PRGAssumption G.toInnerPRG) (Hout : PRGAssumption G.toOuterPRG)
    (hε : Hout.ε ≤ Hin.ε) (A) (Ain) (Aout)
    (h_inner : AdvantageA (G.hyb 0) (G.hyb 1) A ≤ PRG_Adv G.toInnerPRG Ain)
    (h_outer : AdvantageA (G.hyb 1) (G.hyb 2) A ≤ PRG_Adv G.toOuterPRG Aout) :
    AdvantageA (G.hyb 0) (G.hyb 2) A ≤ 2 * Hin.ε
```
Here `G.hyb 0` used independent seeds and was not `G.triple`.

**After.**
```lean
theorem triple_prg_bound (G : DoublePRG) (A : G.Seed × G.Seed × G.Seed → SPComp Bool) :
    PRG_Adv G.toTriplePRG A ≤
      PRG_Adv G.toInnerPRG (G.tripleRedFirst A) + PRG_Adv G.toInnerPRG (G.tripleRedSecond A)
```
The games are H₀ = `PRG_Real G.toTriplePRG` (stretch := `G.triple`), H₁ = `tripleHyb` (`(G(a).1, G(a).2, b)`) and H₂ = `PRG_Ideal G.toTriplePRG`. Each hop is a game equality: `real_bind_eq_redFirst`, `ideal_bind_redFirst_eq`, `hyb_bind_eq_redSecond`, `ideal_bind_redSecond_eq`.

**Reductions defined.** These are new top-level defs:
- `DoublePRG.tripleRedFirst A := fun ab => A ((G.stretch ab.1).1, (G.stretch ab.1).2, ab.2)`
- `DoublePRG.tripleRedSecond A := fun cd => sample b; A (cd.1, cd.2, b)`

New definitions also include `DoublePRG.toTriplePRG` and `DoublePRG.tripleHyb`.

**Deleted:** `PRGAssumption`, `PRGAssumption.advantage_bound`, `PRGAssumption.of_perfect`, `bijPRG_assumption`, `DoublePRG.toOuterPRG`, `DoublePRG.hyb`, `DoublePRG.hyb_2_ideal`, `triple_prg_hybrid_bound`, `triple_prg_uniform_bound`, `triple_prg_bound_of_assumption` and `triple_prg_perfect`. The module docstring names `triple_prg_bound` as the replacement. `bijPRG_perfect` and `bijPRG_adv_zero_via_vcgen` remain.

**Users adapted.** None in Lean. `JoyOfCrypto.md` was updated: rows "Pseudorandom generators" and "PRG triple".

## Finding 14: `prg_decomp_security_bound` (Examples/PRFPRG.lean)

**Before.**
```lean
theorem prg_decomp_security_bound (F : PRFPRG_PRFDef) (A : PRGOutput → SPComp Bool) :
    AdvantageA (gen_hyb_decomp F 0) (gen_hyb_decomp F 2) A ≤
    prf_advantage F zero (wrapAdv_decomp0_snd F A) + prf_advantage F one (wrapAdv_snd A)
```
**After.** The statement is exact, and it is stated on `gen_real`:
```lean
theorem prg_advantage_eq_prf_q (F : PRFPRG_PRFDef) (A : PRGOutput → SPComp Bool) :
    prg_advantage F A = CatCrypt.Crypto.PRPPRF.PRF_q_Advantage F.f (prgOracleAdv A)
```
Here `prg_advantage F A = AdvantageA (gen_real F) gen_ideal A`. The proof goes through `prTrue_realGame_prgOracleAdv`, `run_rfOracle_prgOracleAdv` and `prTrue_rfGame_prgOracleAdv`.

**Reductions defined.**
- `prgOracleAdv A : OracleAdv Word Word Bool` queries `zero`, then `one`, then runs `A (y₀, y₁)` from the empty heap. It is built with `rand` and `ret` and returns the output bit through `outBit`.
- Helpers: `outBit`, `map_outBit_apply_true`, `map_fst_bind_outBit`, `prTrue_pmfGame`.

**Deleted:** `prg_decomp_security_bound`. The module docstring names the replacement. The `gen_hyb`/`gen_hyb_decomp` lemmas remain, and their documentation now states that they concern those games and not `gen_real`.

**Users adapted.** `JoyOfCrypto.md`, row "PRG from a PRF".

## Finding 15: `cascade_prf_bound` / `_of_assumption` (Examples/PRF.lean)

**Before.**
```lean
theorem cascade_prf_bound {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool)
    (ε_prf : ℝ≥0∞) (q N : ℕ)
    (h01 : AdvantageA (G 0) (G 1) A ≤ ε_prf)
    (h12 : AdvantageA (G 1) (G 2) A ≤ birthdayTerm q N)
    (h23 : AdvantageA (G 2) (G 3) A ≤ ε_prf) :
    AdvantageA (G 0) (G 3) A ≤ 2 * ε_prf + birthdayTerm q N
```
`cascade_prf_bound_of_assumption` had the same shape, with `PRFAssumption` values and free reduction adversaries.

**After.**
```lean
def cascade (F : K → D → D) : K × K → D → D := fun kk x => F kk.2 (F kk.1 x)

theorem cascade_prf_bound (F : K → D → D) (A : OracleAdv D D Bool) (q : ℕ)
    (hA : A.IsQueryBound q) :
    PRF_q_Advantage (cascade F) A ≤
      PRF_q_Advantage F (cascadeRedInner F A) + ↑(q * (q - 1) / 2) / ↑(Fintype.card D)
        + PRF_q_Advantage F (cascadeRedOuter A)
```
The game sequence is:
- G₀ = `realGame (cascade F) A`, which equals `realGame F (cascadeRedInner F A)`.
- G₁ = `rfGame (cascadeRedInner F A)`.
- G₂ = `rpGame (cascadeRedInner F A)`, which equals `realGame F (cascadeRedOuter A)`.
- `rfGame (cascadeRedOuter A)` equals `rfGame A` (G₃): a random function after a random injection is a random function.

The hop G₁ → G₂ is `RF_RP_Advantage_le`.

**Reductions defined.**
- `cascadeRedInner F A := rand (uniform K) fun k₂ => mapAns (F k₂) A`.
- `cascadeRedOuter A := simRP [] A`, which simulates a lazy random injection inside the adversary tree.

`cascadeRedOuter` does not use `F`. Supporting definitions and lemmas: `mapAns`, `run_mapAns`, `simRP`, `compOracle`, `run_simRP`, `run_map_state_of_inv`, `rfrpOracle`, `RfrpInv`, `run_compOracle_rfOracle`, and the query-bound lemmas `isQueryBound_cascadeRedInner` and `isQueryBound_cascadeRedOuter`.

**Deleted:** the hypothesis forms `cascade_prf_bound` (replaced by the statement of the same name), `cascade_prf_bound_of_assumption`, `cascade_prf_perfect` and `birthdayTerm`. The section docstring records this.

**Users adapted.**
- `Tactics/AutoDispatchTest.lean:111` and `Tactics/AutoDispatchExtTest.lean:76`: doc comments only. These tests state their own three-hop goal and do not use the theorem.
- `JoyOfCrypto.md`: rows "Pseudorandom functions" and "PRF cascade".

## Finding 15: `cbc_indcpa_bound` (Examples/CBCMode.lean) and `ctr_indcpa_bound` (Examples/CTRMode.lean)

**Before.**
```lean
theorem cbc_indcpa_bound (C : CBCBlockCipher) (eval : C.Key → C.Block → C.Block)
    (m₀ m₁ : C.Block) (A : C.toEncScheme.Ciphertext → SPComp Bool)
    {F : PRFScheme} (H : PRFAssumption F)
    (x₀ x₁ : F.Input) (A₀ A₁ : F.Output → SPComp Bool)
    (hswap0 : AdvantageA (INDCPA_Game (C.toRealScheme eval) m₀ m₁ true)
                (INDCPA_Game C.toEncScheme m₀ m₁ true) A ≤ PRF_Adv F x₀ A₀)
    (hswap1 : AdvantageA (INDCPA_Game C.toEncScheme m₀ m₁ false)
                (INDCPA_Game (C.toRealScheme eval) m₀ m₁ false) A ≤ PRF_Adv F x₁ A₁) :
    INDCPA_Adv (C.toRealScheme eval) m₀ m₁ A ≤ 2 * H.ε

theorem ctr_indcpa_bound (C : CTRBlockScheme) {F : PRFScheme} (H : PRFAssumption F)
    (m₀ m₁) (A) (x : F.Input) (Ared : F.Output → SPComp Bool)
    (hswap : AdvantageA (INDCPA_Game C.toEncScheme m₀ m₁ true) (ctrIdealGame C) A
              ≤ PRF_Adv F x Ared) :
    INDCPA_Adv C.toEncScheme m₀ m₁ A ≤ H.ε
```
**After.** In both statements `F` is the cipher.
```lean
theorem cbc_indcpa_bound (C : CBCBlockCipher) (eval : C.Key → C.Block → C.Block)
    (m₀ m₁ : C.Block) (A : C.Block × C.Block → SPComp Bool) :
    INDCPA_Adv (C.toRealScheme eval) m₀ m₁ A ≤
      ∑ iv, (↑(Fintype.card C.Block))⁻¹ * PRF_Adv (C.cipherPRF eval) (C.xorB iv m₀) (C.cbcRed iv A) +
        ∑ iv, (↑(Fintype.card C.Block))⁻¹ * PRF_Adv (C.cipherPRF eval) (C.xorB iv m₁) (C.cbcRed iv A)

theorem ctr_indcpa_bound (C : CTRBlockScheme) (m₀ m₁) (A) :
    INDCPA_Adv C.toEncScheme m₀ m₁ A ≤
      ∑ r, (↑(Fintype.card C.Block))⁻¹ * PRF_Adv C.cipherPRF r (C.toPRFEncScheme.cpaReduction r m₀ A) +
        ∑ r, (↑(Fintype.card C.Block))⁻¹ * PRF_Adv C.cipherPRF r (C.toPRFEncScheme.cpaReduction r m₁ A)
```
**Reductions defined.**
- `CBCBlockCipher.cbcRed iv A := fun y => A (iv, y)`.
- CTR uses `PRFEncScheme.cpaReduction` through `CTRBlockScheme.toPRFEncScheme`.

**Cipher families.**
- `CBCBlockCipher.cipherPRF eval := ⟨Key, Block, Block, eval⟩`.
- `CTRBlockScheme.cipherPRF := ⟨Key, Block, Block, fun k r => keystream r k⟩`.

**Further lemmas.** CBC: `CBCBlockCipher.uniformGame`, `cbc_real_game_eq`, `cbc_slice_eq` and `cbc_real_uniform_hop`. Shared: `advantageA_sample_bind_le_sum` in CPAFromPRF.lean, which bounds the advantage after a uniform prefix by the average over the prefix.

**Users adapted.** `JoyOfCrypto.md`, rows CTRMode and CBCMode.

## Finding 15: `cpa_from_prf_bound` (Examples/CPAFromPRF.lean)

**Before.**
```lean
theorem cpa_from_prf_bound (P : PRFEncScheme) (H : PRFAssumption P.F)
    (m₀ m₁) (A) (x : P.F.Input) (Ared : P.F.Output → SPComp Bool)
    (hswap : AdvantageA (INDCPA_Game P.toEncScheme m₀ m₁ true) (P.otpGame m₀ m₁ true) A
        + AdvantageA (P.otpGame m₀ m₁ false) (INDCPA_Game P.toEncScheme m₀ m₁ false) A
        ≤ PRF_Adv P.F x Ared) :
    INDCPA_Adv P.toEncScheme m₀ m₁ A ≤ H.ε
```
**After.** `cpa_from_prf_bound` is deleted in favour of the existing `cpa_from_prf_reduction_gamehop`. A per-adversary form was added:
```lean
theorem cpa_from_prf_reduction (P : PRFEncScheme) (m₀ m₁) (A) :
    INDCPA_Adv P.toEncScheme m₀ m₁ A ≤
      ∑ r, (↑(Fintype.card P.F.Input))⁻¹ * PRF_Adv P.F r (P.cpaReduction r m₀ A) +
        ∑ r, (↑(Fintype.card P.F.Input))⁻¹ * PRF_Adv P.F r (P.cpaReduction r m₁ A)
```
Its supporting lemma is `PRFEncScheme.indcpa_otp_hop_le_sum`. The module docstring names both replacements.

**Users.** There were none in Lean. `JoyOfCrypto.md` row "CPA security" was updated.

## Finding 15: `security_based_on_prf` (Examples/PRFMAC.lean)

**Before.**
```lean
theorem security_based_on_prf (m m_check : Word) (t_guess : Word) (hdiff : m_check ≠ m) :
    mac_forgery_advantage m m_check t_guess ≤
      fun A => prf_epsilon A + statistical_gap m t_guess + prf_epsilon A
```
**After.** The theorem is renamed and stated as the statistical bound:
```lean
theorem mac_forgery_advantage_le_half
    (m m_check : Word) (t_guess : Word) (hdiff : m_check ≠ m) (A : Bool → SPComp Bool) :
    mac_forgery_advantage m m_check t_guess A ≤ (2 : ℝ≥0∞)⁻¹
```
**Deleted:** `prf_epsilon`, which was unused padding, and `statistical_gap`, which was the constant 1/2. The module docstring names the replacement. No adaptive game with a PRF reduction was added.

**Users adapted.** `JoyOfCrypto.md`, row "MAC from a PRF".

## Finding 15: `heg_indcpa_le_ddh` (Examples/HashedElGamal.lean)

**Before.**
```lean
theorem heg_indcpa_le_ddh (H : G → Bool) (m₀ m₁ : Bool) (A : (G × Bool) → SPComp Bool)
    [DecidableEq G]
    (h_ideal_indep : (DDH_ideal G).bind (heg_ddh_reduction H m₀ A) =
                     (DDH_ideal G).bind (heg_ddh_reduction H m₁ A)) :
    AdvantageA (heg_real H m₀) (heg_real H m₁) A ≤
    DDH_Advantage G (heg_ddh_reduction H m₀ A) + DDH_Advantage G (heg_ddh_reduction H m₁ A)
```
**After.**
```lean
theorem heg_indcpa_le_ddh (H : G → Bool)
    (hH : SPComp.bind (SPComp.sample CG.Exp) (fun c => SPComp.pure (H (CG.pow c))) =
      SPComp.sample Bool)
    (m₀ m₁ : Bool) (A : (G × Bool) → SPComp Bool) :
    AdvantageA (heg_real H m₀) (heg_real H m₁) A ≤
    DDH_Advantage G (heg_ddh_reduction H m₀ A) + DDH_Advantage G (heg_ddh_reduction H m₁ A)
```
The former hypothesis is now proved as `heg_ddh_ideal_indep`, using `ddh_ideal_bind_red_eq`. `hH` states that `H ∘ pow` pushes the uniform exponent to the uniform bit, the `SPComp` form of `PMF.map H uniform = uniform`. The unused `[DecidableEq G]` was dropped. The reduction `heg_ddh_reduction` already existed.

**Users adapted.** `JoyOfCrypto.md`, row "Hashed ElGamal".

## Finding 15: `pkey_switching` / `pkeyAdvantage_le_collision` (Examples/Cryptobox/PKEY.lean)

**Before.**
```lean
theorem pkey_switching (N : @NIKEScheme CT) (B : PKEYOracles → SPComp Bool) (coll_bound : ℝ≥0∞)
    (h_agree : ∀ b h', ¬pkeyBadFinal h' →
      (PKEY N false B Heap.empty) (some (b, h')) = (PKEY N true B Heap.empty) (some (b, h')))
    (hll : Unary.isLossless (PKEY N false B))
    (hcoll : Unary.prEventComp (PKEY N false B) Heap.empty (fun _ h' => pkeyBadFinal h') ≤ coll_bound) :
    pkeyAdvantage N B ≤ coll_bound
```
In this game the adversary `B : PKEYOracles → SPComp Bool` has no query notion and can read and write every heap location. No query-bounded statement holds for it.

**After.** A new module, `Examples/Cryptobox/PKEYQ.lean`, is imported from `CatCryptCore.lean`:
```lean
theorem pkeyQAdvantage_le (kg : PMF (PK × SK)) (hkg : kg.map Prod.fst = PMF.uniformOfFintype PK)
    (A : OracleAdv (PKEYQuery PK) (PK × Bool) Bool) (q_gen q_csetpk : ℕ)
    (hA : IsPKEYBound A q_gen q_csetpk) :
    pkeyQAdvantage kg A ≤
      ((q_gen * (q_gen - 1) + 2 * (q_gen * q_csetpk) : ℕ) : ℝ≥0∞) / (2 * Fintype.card PK)
```
The game has the following properties:
- **Adversary.** The adversary is an oracle program with the queries `gen`, `csetpk pk` and `honpk pk`. There is no secret-key oracle.
- **Collision handling.** On a collision, game `false` registers the key and game `true` leaves the state unchanged. Both games set a flag.
- **Agreement.** The two games agree while the flag is cleared (`pkeyOracle_apply_false_eq`, `OracleAdv.run_apply_flag_false_eq`).
- **Flag bound.** `run_pkeyOracle_flag_le` bounds the probability of the flag.

**Kept, marked degenerate.** `pkeyAdvantage`, `pkeyAdvantage_le_collision`, `pkey_switching` and `pkey_sdist` (which has a `∀ A` hypothesis; see finding 7). Their docstrings say "Degenerate: see finding 15" (or 6 or 7) and point to `PKEYQ.pkeyQAdvantage_le`.

**Not done.** The Cryptobox chain is not rebased on `PKEYQ`, because the PKAE reductions `R_PKEY` are `SPComp` programs and not oracle programs.

## Finding 6: the Cryptobox security chain (Examples/Cryptobox/*)

**Not repaired. The declarations are kept, marked degenerate.** The repair the sweep describes has four parts:
1. remove `getsk` from the adversary interface;
2. add a location-disjointness condition on adversaries;
3. rebase the chain on `GPKAE`;
4. prove the NIKE and AE hops.

This amounts to redesigning the adversary model of the whole development, about 2,700 lines. In it `getsk` is shared between the scheme's own oracles and the adversary's interface, and every adversary is an `SPComp` program with heap access. This was not carried out.

**Marked degenerate.** Each declaration below has a docstring line "Degenerate: see finding 6 of the vacuity sweep" with the reason:

| Declaration | Reason |
|---|---|
| `PKAEOracles` (Cryptobox.lean) | the field `getsk` is exposed |
| `pkaeAdvantage` | every adversary that runs the scheme itself has advantage close to 1 |
| `R_GSAE` | ignores its hybrid index |
| `ae_hybrid_bound`, `cryptobox_security` | `hdecomp` with free variables |
| `cryptobox_security_chain`, `_full`, `_no_collision`, `_collision_only`, `_with_nike_reduction`, `_with_nike_reduction_no_gap` (GameHopping.lean) | bound `pkaeAdvantage` |
| `aeStep_bounded_by_sae`, `aeStep_bounded_by_sae_finset` (HYBRID.lean) | `h_oracle_align` |
| `nikeAdvantage` (NIKE.lean) | `getsk` and heap access |

The module docstrings of Cryptobox.lean and GameHopping.lean each gained a section "Degenerate statements (finding 6 of the vacuity sweep)".

**Deleted:** `nikeStep_eq_reduction` (GameHopping.lean). Its hypothesis `h_cache_zero` was its conclusion, and it had no users. The module docstring records the deletion.

## Users outside CatCrypt-core

The sweep report names no users outside CatCrypt-core for findings 6, 14 and 15. Nothing outside this repository was examined or edited.

## Builds

All builds were plain `lake build` runs. None printed `Built Mathlib.`

| Command | Result |
|---|---|
| `lake build CatCryptCore.Examples.PRG` | success |
| `lake build CatCryptCore.Examples.CPAFromPRF CatCryptCore.Examples.CBCMode CatCryptCore.Examples.CTRMode` | success |
| `lake build CatCryptCore.Examples.PRFMAC` | success |
| `lake build CatCryptCore.Examples.HashedElGamal` | success |
| `lake build CatCryptCore.Examples.PRFPRG` | success |
| `lake build CatCryptCore.Examples.PRF CatCryptCore.Examples.CPAFromPRF CatCryptCore.Examples.CBCMode CatCryptCore.Examples.CTRMode CatCryptCore.Examples.PRFMAC CatCryptCore.Examples.PRFPRG CatCryptCore.Tactics.AutoDispatchTest CatCryptCore.Tactics.AutoDispatchExtTest` | success |
| `lake build CatCryptCore.Examples.Cryptobox.GameHopping CatCryptCore.Examples.Cryptobox.HYBRID CatCryptCore.Examples.Cryptobox.PKAE CatCryptCore.Examples.Cryptobox.AE` | success |
| `lake build CatCryptCore.Examples.Cryptobox.PKEYQ CatCryptCore.Examples.Cryptobox.PKEY` | success |
| `lake build CatCryptCore` (the root module, which imports every module of the library) | success, 3710 jobs, 0 errors |

**Warnings.** In the final `lake build CatCryptCore` log, none of the edited or new files has a warning, with one exception: `Tactics/AutoDispatchTest.lean`. Its three warnings are at lines 2 and 75. These lines were not changed, and the only edit to that file is the doc comment at line 111.

**Diff check.** The diff adds no `sorry`, no `native_decide` and no `axiom`.
