/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KVAC.AlgMac
public import CatCryptCore.Crypto.KVAC.MacNHelpAGMAssembly
public import CatCryptCore.Crypto.OracleAdversaryRelabelTimed
public import CatCryptCore.Tactics.TimeCertTry

/-!
# Simulations of algebraic MACs and the transfer of suf-cmva-Help

A simulation `E.Sim M c` of an algebraic MAC `M` (the model) by an algebraic MAC `E` (an
implementation, for instance one given by extracted code) through encodings `c : Enc M E`:
isomorphisms of the parameters, issuer parameters, messages, tags and helper queries, and a map
of keys. The simulation states that the setup of `E` is the encoded setup of `M`, and that the
issuer parameters, the tag distribution of the MAC, verification and the helper predicate of
`E` at encoded arguments are the encodings of those of `M`.

An adversary against `E` is relabelled into an adversary against `M` (`Enc.comap`): it reads
encoded parameters and answers, and its queries and forgery are decoded. The suf-cmva-Help
advantage of `E` at `A` is the advantage of `M` at `c.comap A`
(`AlgMac.Sim.sufCmvaHelpAdvantage_eq`).

For a record `E` that simulates `MAC_n` (`AlgMac.macN G n`), an algebraic adversary
`A : AlgAdv G n` gives the adversary `c.algAdv A` against `E`, whose representations are
evaluated over the decoded received elements; its advantage is `sufCmvaHelpAGM_Advantage A`
(`AlgMac.Sim.sufCmvaHelpAdvantage_algAdv`), so the bound `macN_sufCmvaHelpAGM_le` holds for `E`
(`AlgMac.Sim.sufCmvaHelpAdvantage_algAdv_le`).

## Main definitions

* `AlgMac.Enc` — the encodings.
* `AlgMac.Sim` — the simulation.
* `AlgMac.Enc.comap`, `AlgMac.Enc.map` — adversaries against `E` as adversaries against `M` and
  back.
* `AlgMac.Enc.algAdv` — an algebraic adversary against `MAC_n` as an adversary against `E`.

## Main results

* `AlgMac.Sim.sufCmvaHelpGame_eq`, `AlgMac.Sim.sufCmvaHelpAdvantage_eq` — the transfer.
* `AlgMac.Enc.comap_map` — `comap` is a left inverse of `map`.
* `AlgMac.Sim.sufCmvaHelpAdvantage_algAdv`, `AlgMac.Sim.sufCmvaHelpAdvantage_algAdv_le` — the
  algebraic form and the bound of `macN_sufCmvaHelpAGM_le` for a simulating record.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KVAC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace AlgMac

/-! ## Encodings and simulations -/

/-- Encodings of the public types of an algebraic MAC `M` in those of `E`: isomorphisms of the
parameters, issuer parameters, messages, tags and helper queries, and a map of keys. -/
structure Enc (M E : AlgMac) where
  /-- The parameters. -/
  par : M.Par ≃ E.Par
  /-- The keys. -/
  key : M.Key → E.Key
  /-- The issuer parameters. -/
  pk : M.PK ≃ E.PK
  /-- The messages. -/
  msg : M.Msg ≃ E.Msg
  /-- The tags. -/
  tag : M.Tag ≃ E.Tag
  /-- The helper queries. -/
  helpQ : M.HelpQ ≃ E.HelpQ

/-- **Simulation of an algebraic MAC.** `E.Sim M c`: the setup of `E` (parameters and key) is
the setup of `M` encoded by `c`, and at encoded parameters and keys the issuer parameters, the
distribution of the tag of an encoded message, verification of encoded pairs and the helper
predicate at encoded queries are those of `M`, encoded. -/
structure Sim (E M : AlgMac) (c : Enc M E) : Prop where
  /-- The setup of `E` is the encoded setup of `M`. -/
  setup : E.setup.map (fun x => (x.1, E.keyGen x.1 x.2)) =
    M.setup.map fun x => (c.par x.1, c.key (M.keyGen x.1 x.2))
  /-- The issuer parameters. -/
  pk : ∀ par k, E.pk (c.par par) (c.key k) = c.pk (M.pk par k)
  /-- The distribution of the tag. -/
  mac : ∀ par k m, (PMF.uniformFintype E.MacCoins).map (E.mac (c.par par) (c.key k) (c.msg m)) =
    (PMF.uniformFintype M.MacCoins).map fun r => c.tag (M.mac par k m r)
  /-- Verification. -/
  verify : ∀ par k m σ, E.verify (c.par par) (c.key k) (c.msg m) (c.tag σ) = M.verify par k m σ
  /-- The helper predicate. -/
  help : ∀ par k q, E.help (c.par par) (c.key k) (c.helpQ q) = M.help par k q

namespace Enc

variable {M E : AlgMac} (c : Enc M E)

/-- The encoded MAC log. -/
def logEnc (log : M.Log) : E.Log := log.map (Prod.map c.msg c.tag)

/-- A query of `E` decoded. -/
def qryDec : E.HelpQry → M.HelpQry
  | .inl m => .inl (c.msg.symm m)
  | .inr (.inl q) => .inr (.inl (c.msg.symm q.1, c.tag.symm q.2))
  | .inr (.inr q) => .inr (.inr (c.helpQ.symm q))

/-- A query of `M` encoded. -/
def qryEnc : M.HelpQry → E.HelpQry
  | .inl m => .inl (c.msg m)
  | .inr (.inl q) => .inr (.inl (c.msg q.1, c.tag q.2))
  | .inr (.inr q) => .inr (.inr (c.helpQ q))

/-- An answer of `M` encoded. -/
def ansEnc : M.HelpAns → E.HelpAns
  | .inl σ => .inl (c.tag σ)
  | .inr b => .inr b

/-- An answer of `E` decoded. -/
def ansDec : E.HelpAns → M.HelpAns
  | .inl σ => .inl (c.tag.symm σ)
  | .inr b => .inr b

/-- A forgery of `E` decoded. -/
def outDec (o : E.Msg × E.Tag) : M.Msg × M.Tag := (c.msg.symm o.1, c.tag.symm o.2)

/-- A forgery of `M` encoded. -/
def outEnc (o : M.Msg × M.Tag) : E.Msg × E.Tag := (c.msg o.1, c.tag o.2)

/-- One run of an adversary against `E` as a run against `M`: queries and the forgery are
decoded, answers encoded. -/
def comapRun (B : OracleAdv E.HelpQry E.HelpAns (E.Msg × E.Tag)) :
    OracleAdv M.HelpQry M.HelpAns (M.Msg × M.Tag) :=
  (B.mapQueryAnswer c.qryDec c.ansEnc).bind fun o => .ret (c.outDec o)

/-- One run of an adversary against `M` as a run against `E`. -/
def mapRun (B : OracleAdv M.HelpQry M.HelpAns (M.Msg × M.Tag)) :
    OracleAdv E.HelpQry E.HelpAns (E.Msg × E.Tag) :=
  (B.mapQueryAnswer c.qryEnc c.ansDec).bind fun o => .ret (c.outEnc o)

/-- **The relabelled adversary.** An adversary against `E` as an adversary against `M`: it
receives the encoded parameters and issuer parameters, and its runs are relabelled by
`comapRun`. -/
def comap (A : E.Par → E.PK → OracleAdv E.HelpQry E.HelpAns (E.Msg × E.Tag)) :
    M.Par → M.PK → OracleAdv M.HelpQry M.HelpAns (M.Msg × M.Tag) :=
  fun par pk => c.comapRun (A (c.par par) (c.pk pk))

/-- An adversary against `M` as an adversary against `E`. -/
def map (A : M.Par → M.PK → OracleAdv M.HelpQry M.HelpAns (M.Msg × M.Tag)) :
    E.Par → E.PK → OracleAdv E.HelpQry E.HelpAns (E.Msg × E.Tag) :=
  fun par pk => c.mapRun (A (c.par.symm par) (c.pk.symm pk))

theorem mapQueryAnswer_id {D R α : Type} (B : OracleAdv D R α) :
    B.mapQueryAnswer id id = B := by
  induction B with
  | ret a => rfl
  | rand p k ih => simp only [OracleAdv.mapQueryAnswer, ih]
  | query d k ih => simp only [OracleAdv.mapQueryAnswer, id_eq, ih]

theorem bind_ret_right {D R α : Type} (B : OracleAdv D R α) : B.bind .ret = B := by
  induction B with
  | ret a => rfl
  | rand p k ih => simp only [OracleAdv.bind, ih]
  | query d k ih => simp only [OracleAdv.bind, ih]

/-- `comapRun` is a left inverse of `mapRun`. -/
theorem comapRun_mapRun (B : OracleAdv M.HelpQry M.HelpAns (M.Msg × M.Tag)) :
    c.comapRun (c.mapRun B) = B := by
  have hq : c.qryDec ∘ c.qryEnc = id := by
    funext d; rcases d with m | q | q <;> simp [qryDec, qryEnc]
  have ha : c.ansDec ∘ c.ansEnc = id := by
    funext a; rcases a with σ | b <;> simp [ansDec, ansEnc]
  simp only [comapRun, mapRun, OracleAdv.mapQueryAnswer_bind, OracleAdv.bind_assoc,
    OracleAdv.mapQueryAnswer_mapQueryAnswer, hq, ha, mapQueryAnswer_id, OracleAdv.mapQueryAnswer,
    OracleAdv.bind_ret, outDec, outEnc, Equiv.symm_apply_apply]
  exact bind_ret_right B

/-- `comap` is a left inverse of `map`. -/
theorem comap_map (A : M.Par → M.PK → OracleAdv M.HelpQry M.HelpAns (M.Msg × M.Tag)) :
    c.comap (c.map A) = A := by
  funext par pk
  simp only [comap, map, Equiv.symm_apply_apply, comapRun_mapRun]

end Enc

time_cert_try derive_timed Enc.comapRun

/-! ## The transfer -/

/-- The forgery game with the setup of the parameters and the key. -/
theorem forgeGame_eq_keySetup {Q Ans : Type} (M : AlgMac)
    (O : M.Par → M.Key → M.Log → Q → PMF (Ans × M.Log))
    (fresh : M.Msg × M.Tag → M.Log → Bool)
    (A : M.Par → M.PK → OracleAdv Q Ans (M.Msg × M.Tag)) :
    M.forgeGame O fresh A = liftPMF ((M.setup.map fun x => (x.1, M.keyGen x.1 x.2)).bind
      fun x => (OracleAdv.run (O x.1 x.2) (A x.1 (M.pk x.1 x.2)) []).map
        fun y => M.verify x.1 x.2 y.1.1 y.1.2 && fresh y.1 y.2) := by
  rw [PMF.bind_map]
  rfl

theorem macStep_eq (M : AlgMac) (par : M.Par) (k : M.Key) (log : M.Log) (m : M.Msg) :
    M.macStep par k log m =
      ((PMF.uniformFintype M.MacCoins).map (M.mac par k m)).map fun t => (t, (m, t) :: log) := by
  rw [macStep, PMF.map_comp]
  rfl

variable {E M : AlgMac} {c : Enc M E}

/-- One call of the helper oracle of `E` at encoded parameters, key and log is the call of the
oracle of `M` at the decoded query, with the answer and the log encoded. -/
theorem Sim.helpOracle_step (h : E.Sim M c) (par : M.Par) (k : M.Key) (log : M.Log)
    (d : E.HelpQry) :
    ((M.helpOracle par k log (c.qryDec d)).map fun x => (c.ansEnc x.1, x.2)).map
        (Prod.map id c.logEnc) =
      E.helpOracle (c.par par) (c.key k) (c.logEnc log) d := by
  rcases d with m | ⟨m, σ⟩ | q
  · obtain ⟨m0, rfl⟩ := c.msg.surjective m
    simp only [Enc.qryDec, Equiv.symm_apply_apply, helpOracle, macStep_eq, h.mac, PMF.map_comp]
    rfl
  · obtain ⟨m0, rfl⟩ := c.msg.surjective m
    obtain ⟨σ0, rfl⟩ := c.tag.surjective σ
    simp only [Enc.qryDec, Equiv.symm_apply_apply, helpOracle, h.verify, PMF.pure_map]
    rfl
  · obtain ⟨q0, rfl⟩ := c.helpQ.surjective q
    simp only [Enc.qryDec, Equiv.symm_apply_apply, helpOracle, h.help, PMF.pure_map]
    rfl

/-- The run of an adversary against the helper oracle of `E` at encoded parameters and key, with
the winning test of suf-cmva-Help, is the run of the relabelled adversary against `M`. -/
theorem Sim.run_helpOracle (h : E.Sim M c) (par : M.Par) (k : M.Key)
    (B : OracleAdv E.HelpQry E.HelpAns (E.Msg × E.Tag)) :
    (OracleAdv.run (E.helpOracle (c.par par) (c.key k)) B []).map
        (fun y => E.verify (c.par par) (c.key k) y.1.1 y.1.2 && E.strongFresh y.1 y.2) =
      (OracleAdv.run (M.helpOracle par k) (c.comapRun B) []).map
        fun y => M.verify par k y.1.1 y.1.2 && M.strongFresh y.1 y.2 := by
  have hrun := OracleAdv.run_map_state
    (fun s d => (M.helpOracle par k s (c.qryDec d)).map fun x => (c.ansEnc x.1, x.2))
    (E.helpOracle (c.par par) (c.key k)) c.logEnc (h.helpOracle_step par k) B []
  have hinj : Function.Injective (Prod.map c.msg c.tag) :=
    c.msg.injective.prodMap c.tag.injective
  rw [show c.logEnc [] = [] from rfl] at hrun
  rw [← hrun, Enc.comapRun, OracleAdv.run_bind, OracleAdv.run_mapQueryAnswer]
  simp only [OracleAdv.run_ret]
  rw [show (fun x : (E.Msg × E.Tag) × M.Log => PMF.pure (c.outDec x.1, x.2)) =
      PMF.pure ∘ fun x => (c.outDec x.1, x.2) from rfl, PMF.bind_pure_comp, PMF.map_comp,
    PMF.map_comp]
  refine congrArg (fun f => PMF.map f _) (funext fun y => ?_)
  obtain ⟨⟨m, σ⟩, s⟩ := y
  obtain ⟨m0, rfl⟩ := c.msg.surjective m
  obtain ⟨σ0, rfl⟩ := c.tag.surjective σ
  have hmem : (c.msg m0, c.tag σ0) ∈ c.logEnc s ↔ (m0, σ0) ∈ s :=
    List.mem_map_of_injective (a := (m0, σ0)) (l := s) hinj
  simp [Enc.outDec, h.verify, strongFresh, hmem]

/-- **Transfer of the suf-cmva-Help game along a simulation.** -/
theorem Sim.sufCmvaHelpGame_eq (h : E.Sim M c)
    (A : E.Par → E.PK → OracleAdv E.HelpQry E.HelpAns (E.Msg × E.Tag)) :
    E.sufCmvaHelpGame A = M.sufCmvaHelpGame (c.comap A) := by
  rw [sufCmvaHelpGame, sufCmvaHelpGame, forgeGame_eq_keySetup, forgeGame_eq_keySetup, h.setup,
    PMF.bind_map, PMF.bind_map]
  refine congrArg _ (congrArg _ (funext fun x => ?_))
  simp only [Function.comp_apply, h.pk, Enc.comap]
  exact h.run_helpOracle _ _ _

/-- **Transfer of the suf-cmva-Help advantage along a simulation.** The advantage of `E` at `A`
is the advantage of `M` at the relabelled adversary `c.comap A`. -/
theorem Sim.sufCmvaHelpAdvantage_eq (h : E.Sim M c)
    (A : E.Par → E.PK → OracleAdv E.HelpQry E.HelpAns (E.Msg × E.Tag)) :
    E.SUFCMVAHelp_Advantage A = M.SUFCMVAHelp_Advantage (c.comap A) := by
  rw [SUFCMVAHelp_Advantage, SUFCMVAHelp_Advantage, h.sufCmvaHelpGame_eq]

/-- The advantage of `E` at an adversary against `M` mapped to `E` is the advantage of `M`. -/
theorem Sim.sufCmvaHelpAdvantage_map (h : E.Sim M c)
    (A : M.Par → M.PK → OracleAdv M.HelpQry M.HelpAns (M.Msg × M.Tag)) :
    E.SUFCMVAHelp_Advantage (c.map A) = M.SUFCMVAHelp_Advantage A := by
  rw [h.sufCmvaHelpAdvantage_eq, c.comap_map]

/-! ## Records that simulate `MAC_n` in the algebraic group model -/

section AGM

open CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.OT CatCrypt.Crypto.Assumptions.KDL
open MacNHelpAGM

variable {G : Type} [CGR : CyclicGroupRing G] [DecidableEq G] [DecidableEq CGR.Exp] {n : ℕ}

attribute [local instance] expCommRing

/-- **An algebraic adversary against a record that simulates `MAC_n`.** The adversary of
`AlgAdv.toAdv A` mapped to `E`: its representations are evaluated over the decoded elements it
has received. -/
noncomputable def Enc.algAdv (c : Enc (macN G n) E) (A : AlgAdv G n) :
    E.Par → E.PK → OracleAdv E.HelpQry E.HelpAns (E.Msg × E.Tag) :=
  c.map A.toAdv

/-- **The algebraic form of the transfer.** For a record `E` that simulates `MAC_n`, the
advantage of `E` at the algebraic adversary `c.algAdv A` is `sufCmvaHelpAGM_Advantage A`. -/
theorem Sim.sufCmvaHelpAdvantage_algAdv {c : Enc (macN G n) E} (h : E.Sim (macN G n) c)
    (A : AlgAdv G n) : E.SUFCMVAHelp_Advantage (c.algAdv A) = sufCmvaHelpAGM_Advantage A :=
  h.sufCmvaHelpAdvantage_map _

/-- **suf-cmva-Help in the algebraic group model for a record that simulates `MAC_n`.** The
bound of `macN_sufCmvaHelpAGM_le` holds for the advantage of `E` at `c.algAdv A`. -/
theorem Sim.sufCmvaHelpAdvantage_algAdv_le {c : Enc (macN G n) E} (h : E.Sim (macN G n) c)
    (hgen : CGR.gen ≠ CGR.one) (qm : ℕ) (A : AlgAdv G n)
    (hA : ∀ p pk, (A p pk).IsQueryBoundBy macCost qm) (RF : RootFinder G) :
    E.SUFCMVAHelp_Advantage (c.algAdv A) ≤
      DL_Advantage (reductionZ A.toAdv) +
        KDL_Advantage G (qm + 2) (reductionAlg expOne RF.roots A) +
          ((qm + 2 + 3 : ℕ) : ℝ≥0∞) / (Fintype.card CGR.Exp : ℝ≥0∞) +
            ((qm * (qm - 1) : ℕ) : ℝ≥0∞) / (2 * (Fintype.card CGR.Exp : ℝ≥0∞)) := by
  rw [h.sufCmvaHelpAdvantage_algAdv]
  exact macN_sufCmvaHelpAGM_le hgen qm A hA RF

end AGM

end AlgMac

end CatCrypt.Crypto.KVAC
