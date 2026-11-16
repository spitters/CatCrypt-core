/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Schnorr
public import CatCryptCore.Crypto.Schnorr.ROMGame

/-!
# The Schnorr ROM game as the generic Fiat–Shamir game

The Schnorr EUF-CMA game of `Schnorr/ROMGame.lean` over group parameters `gp` is
the generic Fiat–Shamir game at `schnorrSigma gp`, so the generic theorem for
Schnorr (`FiatShamirROM.schnorr_fs_rom_eufcma`) bounds it.

## Main definitions

* `toGeneric A` — a Schnorr ROM adversary (`SchnorrROM.Adversary`) as an adversary
  against the generic Fiat–Shamir game

## Main results

* `eufcmaAdvantage_toGeneric` — the Schnorr ROM EUF-CMA advantage equals the
  generic Fiat–Shamir EUF-CMA advantage of `toGeneric A`
* `schnorr_rom_eufcma_of_generic` — for every Schnorr ROM adversary,
  `ε'·(ε'/(qH + 1) − 1/|Scalar|) ≤
    DL_Advantage (dlOfWitness (extractReduction (toGeneric A)))` with
  `ε' = SchnorrROM.eufcmaAdvantage A − qS·(qH + 1 + qS)/|Scalar|`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Examples.Schnorr
open CatCrypt.Crypto.OracleForking
open scoped ENNReal

variable {gp : GroupParam} {M : Type} [DecidableEq M] {qH qS : ℕ}

/-- An oracle adversary whose answers are read through `f`. -/
def mapAns {D R R' α : Type} (f : R' → R) : OracleAdv D R α → OracleAdv D R' α
  | .ret a => .ret a
  | .rand p k => .rand p fun b => mapAns f (k b)
  | .query d k => .query d fun r => mapAns f (k (f r))

omit [DecidableEq M] in
theorem isQueryBound₂_mapAns {D₁ D₂ R R' α : Type} (f : R' → R) (A : OracleAdv (D₁ ⊕ D₂) R α)
    (h q : ℕ) (hA : IsQueryBound₂ A h q) : IsQueryBound₂ (mapAns f A) h q := by
  induction A generalizing h q with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b h q (hA b)
  | query d k ih =>
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h => exact fun r => ih (f r) h q (hA (f r))
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q => exact fun r => ih (f r) h q (hA (f r))

omit [DecidableEq M] in
/-- Running an adversary whose answers are read through `f` against an oracle whose
answers and states are the images by `g` and `σ` of those of `O`, where `f`
inverts `g`, is the image by `σ` of running it against `O`. -/
theorem run_mapAns {D R R' S S' α : Type} (O : S → D → PMF (R × S))
    (O' : S' → D → PMF (R' × S')) (f : R' → R) (g : R → R') (σ : S → S')
    (hfg : ∀ r, f (g r) = r) (hO : ∀ s d, (O s d).map (Prod.map g σ) = O' (σ s) d)
    (A : OracleAdv D R α) (s : S) :
    (OracleAdv.run O A s).map (Prod.map id σ) = OracleAdv.run O' (mapAns f A) (σ s) := by
  induction A generalizing s with
  | ret a => simp [mapAns, PMF.pure_map]
  | rand p k ih => simp only [OracleAdv.run_rand, mapAns, PMF.map_bind, ih]
  | query d k ih =>
    simp only [OracleAdv.run_query, mapAns, PMF.map_bind, ← hO s d, PMF.bind_map]
    refine congrArg _ (funext fun x => ?_)
    simp only [Function.comp_apply, Prod.map, hfg]
    exact ih x.1 x.2

/-- A generic answer as a Schnorr ROM answer; the generic oracle at `schnorrSigma gp`
accepts every response, so the answer `inr none` does not occur. -/
noncomputable def ofAns : Answer (schnorrSigma gp) → SchnorrROM.Answer gp
  | .inl e => .inl e
  | .inr (some az) => .inr az
  | .inr none => .inl (Classical.arbitrary _)

/-- A Schnorr ROM answer as a generic answer. -/
def toAns : SchnorrROM.Answer gp → Answer (schnorrSigma gp)
  | .inl e => .inl e
  | .inr az => .inr (some az)

theorem ofAns_toAns (a : SchnorrROM.Answer gp) : ofAns (toAns a) = a := by
  cases a <;> rfl

/-- A Schnorr ROM adversary as an adversary against the generic Fiat–Shamir game
over `schnorrSigma gp`, reading the generic answers through `ofAns`. -/
noncomputable def toGeneric (A : SchnorrROM.Adversary gp M qH qS) :
    Adversary (schnorrSigma gp) M qH qS :=
  ⟨fun x => mapAns ofAns (A.run x), fun x => isQueryBound₂_mapAns _ _ _ _ (A.isQueryBound x)⟩

/-- The Schnorr ROM tables as generic tables. -/
def tablesMap (s : SchnorrROM.Tables gp M × Bool) : Tables (schnorrSigma gp) M × Bool :=
  (⟨s.1.hash, s.1.prog, s.1.signed, []⟩, s.2)

theorem tablesMap_lookup (s : SchnorrROM.Tables gp M × Bool) (k : gp.G × M) :
    (tablesMap s).1.lookup k = s.1.lookup k := rfl

theorem tablesMap_lookupAll (s : SchnorrROM.Tables gp M × Bool) (k : gp.G × M) :
    (tablesMap s).1.lookupAll k = s.1.lookup k := by
  unfold Protocol.Tables.lookupAll
  rw [show (tablesMap s).1.rej = [] from rfl]
  erw [lookupIn_nil, Option.or_none]
  rfl

theorem withVerify_eq (x : gp.G) (B : OracleAdv (SchnorrROM.Query gp M) (SchnorrROM.Answer gp)
    (SchnorrROM.Forgery gp M)) :
    mapAns ofAns (SchnorrROM.withVerify B) =
      withVerify (G := (schnorrSigma gp).toProtocol M) x (mapAns ofAns B) := by
  induction B with
  | ret y =>
    obtain ⟨m, a, z⟩ := y
    change OracleAdv.query _ _ = OracleAdv.query _ _
    congr 1
    funext r
    cases r <;> rfl
  | rand p k ih => simp only [SchnorrROM.withVerify, withVerify, mapAns, ih]; rfl
  | query d k ih => simp only [SchnorrROM.withVerify, withVerify, mapAns, ih]; rfl

theorem realStep_map_tablesMap (sk : gp.Scalar) (s : SchnorrROM.Tables gp M × Bool)
    (d : SchnorrROM.Query gp M) :
    (toOracle (SchnorrROM.realStep sk) s d).map (Prod.map toAns tablesMap) =
      toOracle (realStep (G := (schnorrSigma gp).toProtocol M) (gp.exp sk, sk)) (tablesMap s) d := by
  cases d with
  | inl k =>
    simp only [toOracle, SchnorrROM.realStep, realStep, SchnorrROM.hashStep, realHashStep,
      tablesMap_lookup]
    rw [show lookupIn (tablesMap s).1.rej k = none from lookupIn_nil k]
    cases s.1.lookup k with
    | some e => simp only [Step.toPMF, PMF.pure_map]; rfl
    | none => simp only [Step.toPMF, PMF.map_comp]; rfl
  | inr m =>
    simp only [toOracle, SchnorrROM.realStep, realStep, Step.toPMF, SchnorrROM.sample₂, sampleVec,
      PMF.map_bind, PMF.map_comp]
    rw [bind_uniformFintype_fin_one]
    simp only [← PMF.bind_pure_comp]
    refine (PMF.bind_comm _ _ _).trans ?_
    refine congrArg _ (funext fun e => congrArg _ (funext fun r => ?_))
    simp only [Function.comp_apply]
    congr 1
    have hl : (tablesMap s).1.lookupAll ((schnorrSigma gp).commit (gp.exp sk) sk r, m) =
        s.1.lookup (gp.exp r, m) := tablesMap_lookupAll s _
    have hv : ((schnorrSigma gp).toProtocol M).honestVals (tablesMap s).1.lookupAll
        (gp.exp sk) sk m r (fun _ => e) =
        fun _ => ((tablesMap s).1.lookupAll
          ((schnorrSigma gp).commit (gp.exp sk) sk r, m)).getD e :=
      funext fun i => effVal_eq _ _ (fun _ _ _ _ => rfl) _ i
    unfold SchnorrROM.realSignOut realSignOut
    beta_reduce
    rw [hv, hl]
    simp [Protocol.flagging, Protocol.evEntries, Protocol.pubEntries, Protocol.hidEntries,
      Protocol.entries, hashAll, List.finRange_succ, schnorrSigma, List.filter_cons]
    erw [hl]
    generalize s.1.lookup (gp.exp r, m) = L
    cases L <;> simp [tablesMap] <;> erw [List.append_nil, List.append_nil] <;> rfl

theorem eufcmaAdvantage_toGeneric (A : SchnorrROM.Adversary gp M qH qS) :
    SchnorrROM.eufcmaAdvantage A = eufcmaAdvantage (toGeneric A) := by
  unfold SchnorrROM.eufcmaAdvantage eufcmaAdvantage SchnorrROM.eufcmaGame eufcmaGame
  congr 2
  unfold SchnorrROM.gameDist gameDist
  change _ = ((PMF.uniformFintype gp.Scalar).map fun w => (gp.exp w, w)).bind _
  refine Eq.trans ?_ (PMF.bind_map (PMF.uniformFintype gp.Scalar)
    (fun w => (gp.exp w, w)) _).symm
  refine congrArg _ (funext fun sk => ?_)
  have hrun := run_mapAns _ _ ofAns toAns tablesMap ofAns_toAns (realStep_map_tablesMap sk)
    (SchnorrROM.withVerify (A.run (gp.exp sk))) (SchnorrROM.Tables.empty, false)
  rw [withVerify_eq (gp.exp sk)] at hrun
  change _ = PMF.map (wins (G := (schnorrSigma gp).toProtocol M) (gp.exp sk))
    (OracleAdv.run (toOracle (realStep (G := (schnorrSigma gp).toProtocol M) (gp.exp sk, sk)))
      (withVerify (G := (schnorrSigma gp).toProtocol M) (gp.exp sk)
        (mapAns ofAns (A.run (gp.exp sk))))
      (tablesMap (SchnorrROM.Tables.empty, false)))
  have hw : SchnorrROM.wins (M := M) (gp.exp sk) =
      wins (G := (schnorrSigma gp).toProtocol M) (gp.exp sk) ∘ Prod.map id tablesMap := by
    funext y
    obtain ⟨⟨m, a, z⟩, t, b⟩ := y
    change SchnorrROM.wins (gp.exp sk) ((m, a, z), t, b) =
      wins (G := (schnorrSigma gp).toProtocol M) (gp.exp sk) ((m, a, z), tablesMap (t, b))
    unfold SchnorrROM.wins wins
    dsimp only
    generalize hL : t.lookup (a, m) = L
    have hL' : (tablesMap (t, b)).1.lookup (a, m) = L := hL
    simp only [verifyVals, hL']
    cases L <;> rfl
  rw [hw]
  exact (PMF.map_comp _ _ (wins (G := (schnorrSigma gp).toProtocol M) (gp.exp sk))).symm.trans
    (congrArg (PMF.map (wins (G := (schnorrSigma gp).toProtocol M) (gp.exp sk))) hrun)

/-- **Schnorr EUF-CMA in the random-oracle model from the generic theorem.** For
every Schnorr ROM adversary `A` with at most `qH` hash and `qS` signing queries,
`ε'·(ε'/(qH + 1) − 1/|Scalar|) ≤ DL_Advantage (dlOfWitness (extractReduction (toGeneric A)))`
with `ε' = SchnorrROM.eufcmaAdvantage A − qS·(qH + 1 + qS)/|Scalar|`. The
discrete-logarithm adversary runs `A` at most twice and computes
`(z₁ − z₂)/(e₁ − e₂)`. -/
theorem schnorr_rom_eufcma_of_generic (A : SchnorrROM.Adversary gp M qH qS) :
    (SchnorrROM.eufcmaAdvantage A -
        ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) / Fintype.card gp.Scalar) *
        ((SchnorrROM.eufcmaAdvantage A -
            ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) / Fintype.card gp.Scalar) /
          ((qH + 1 : ℕ) : ℝ≥0∞) - 1 / Fintype.card gp.Scalar) ≤
      DL_Advantage gp (dlOfWitness gp (extractReduction (toGeneric A))) := by
  rw [eufcmaAdvantage_toGeneric]
  exact schnorr_fs_rom_eufcma (toGeneric A)

end CatCrypt.Crypto.FiatShamirROM
