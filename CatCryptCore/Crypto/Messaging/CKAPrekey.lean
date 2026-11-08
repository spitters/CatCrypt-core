/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.CKACorrupt

/-!
# The CKA corruption game at a given initial key pair

The CKA `C.atInit i` is the CKA `C` whose initialisation returns the fixed public value and
party states `i`. The corruption game of `C` is the average of the games of `C.atInit i` over the
initialisation of `C` (`cka_corrupt_game_eq_bind_atInit`).

For the Diffie–Hellman CKA `dhCKAOf G decE`, the pair `dhPairInit decE x₀` is the signed-prekey
pair of Signal's ratchet initialisation: the public value is `g^{x₀}`, the first sender `A` holds
only `g^{x₀}`, the first receiver `B` holds `g^{x₀}` and its secret key `x₀`. For adversaries
whose challenge epoch is at least `2`, the corruption advantage at this pair is at most the DDH
advantage of the reduction `ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS A` plus `4 c.δ`
(`dhCKAOf_atInit_corrupt_advantage_le`). The reduction runs the simulator
`ckaCorruptSimImplOf` from the given pair; the send of epoch `t* - 1 ≥ 1` carries the DDH
element `ga`.

## Main results

* `CKADef.atInit`, `CKADef.atInitCoins` — the CKA at a given initial pair
* `cka_corrupt_game_eq_bind_atInit` — the game as the average of the games at the pairs
* `ckaCorruptDDHTreeAt`, `ckaCorruptDDHRedAt` — the DDH reduction at a given pair
* `dhCKAOf_atInit_corrupt_advantage_le` — the DDH bound at the pair `dhPairInit decE x₀`
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

variable {St Msg Key Rand α : Type}

/-- The CKA `C` with the initialisation replaced by the fixed public value and party states
`i`. -/
noncomputable def CKADef.atInit (C : CKADef St Msg Key) (i : Msg × St × St) :
    CKADef St Msg Key :=
  { C with init := SPComp.pure i }

/-- The explicit-randomness sending algorithm of `C.atInit i` is that of `C`. -/
noncomputable instance CKADef.atInitCoins (C : CKADef St Msg Key) [CKACoins C Rand]
    (i : Msg × St × St) : CKACoins (C.atInit i) Rand where
  sendR := CKACoins.sendR (C := C)

/-- The soundness of the explicit-randomness sending algorithm passes to `C.atInit i`. -/
theorem CKACoins.Sound.atInit {C : CKADef St Msg Key} [CKACoins C Rand] [Fintype Rand]
    [Nonempty Rand] (h : CKACoins.Sound C) (i : Msg × St × St) :
    CKACoins.Sound (C.atInit i) :=
  fun s => h s

/-- **The corruption game as an average over the initial pairs.** If the initialisation of `C`
is the lifted distribution `initP`, the corruption game of `C` draws a pair `i` from `initP` and
runs the corruption game of `C.atInit i`. -/
theorem cka_corrupt_game_eq_bind_atInit (C : CKADef St Msg Key) [CKACoins C Rand]
    [Fintype Key] [Nonempty Key] [Fintype Rand] [Nonempty Rand] (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (A : CKACorruptAdv St Msg Key Rand α) (initP : PMF (Msg × St × St))
    (hinit : C.init = liftPMF initP) :
    cka_corrupt_game C ΔFS ΔPCS ideal A =
      SPComp.bind (liftPMF initP) fun i => cka_corrupt_game (C.atInit i) ΔFS ΔPCS ideal A := by
  unfold cka_corrupt_game
  rw [hinit, SPComp.isPure_bind_comm _ _ _ (liftPMF_isPure _) (liftPMF_isPure _)]
  simp only [CKADef.atInit, SPComp.pure_bind]
  rfl

/-! ### The Diffie–Hellman CKA at a given pair -/

section DHAt

variable {E Gr : Type} [Fintype E] [Nonempty E] [Fintype Gr] [Nonempty Gr]

/-- **The DDH reduction tree at the initial pair `i`.** On the triple `(ga, gb, z)` it draws the
challenge epoch `t` of the adversary and runs the adversary at the public value `i.1` against
the simulator `ckaCorruptSimImplOf` from the initial states `i.2.1`, `i.2.2`. -/
noncomputable def ckaCorruptDDHTreeAt (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS : ℕ)
    (tStar : PMF ℕ) (play : ℕ → Gr → OracleAdv CKAQuery (CKAAns (Gr × E) Gr Gr E) α)
    (i : Gr × (Gr × E) × (Gr × E)) (ga gb z : Gr) : OracleAdv Empty Unit α :=
  .rand tStar fun t =>
    (OracleAdv.simulate (ckaCorruptSimImplOf pow epow ΔFS ΔPCS t ga gb z)
      (play t i.1) (CKAGameSt.init i.1 i.2.1 i.2.2)).bind fun r => .ret r.1

omit [Fintype E] [Nonempty E] [Fintype Gr] [Nonempty Gr] in
/-- At a challenge epoch `t ≠ 1`, an initial state in which the first sender holds the public
value of the secret key of the first receiver is related to itself. -/
theorem dhRel_initAt (pow : E → Gr) {t : ℕ} (ht : t ≠ 1) (a : E)
    (i : Gr × (Gr × E) × (Gr × E)) (hi : i.2.1.1 = pow i.2.2.2) :
    DHRel pow a t (CKAGameSt.init i.1 i.2.1 i.2.2) (CKAGameSt.init i.1 i.2.1 i.2.2) := by
  refine ⟨rfl, rfl, fun _ => rfl, fun _ _ => rfl, Or.inl rfl, ?_, ?_, ?_⟩
  · intro _
    exact hi
  · intro p hp
    cases p <;> simp [CKAGameSt.init] at hp
  · intro h1 hlo _
    have : (CKAGameSt.init i.1 i.2.1 i.2.2 : CKAGameSt (Gr × E) Gr).t (ckaSender t).other = 0 :=
      rfl
    omega

/-- **The game at the pair as the simulation**, at a challenge epoch `t ≠ 1`, for commuting
exponentiations and the delays `2 ≤ ΔFS`, `2 ≤ ΔPCS`: the keys `va`, `vb` of the sends of the
epochs `t - 1` and `t` are drawn in advance and the simulator runs with the triple
`(pow va.1, pow vb.1, z)`. -/
theorem dhCKA_run_eq_sim_at (pow : E → Gr) (epow : Gr → E → Gr)
    (hcomm : ∀ x y, epow (pow x) y = epow (pow y) x) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 2 ≤ ΔPCS) {t : ℕ} (ht : t ≠ 1) (ideal : Bool) (i : Gr × (Gr × E) × (Gr × E))
    (hi : i.2.1.1 = pow i.2.2.2) (play : OracleAdv CKAQuery (CKAAns (Gr × E) Gr Gr E) α) :
    (OracleAdv.run (OracleAdv.nfOracle (dhDrawOf E Gr)
        (dhCKAStepOf pow epow ΔFS ΔPCS t ideal)) play
        (CKAGameSt.init i.1 i.2.1 i.2.2)).map Prod.fst =
      (dhDrawOf E Gr).bind fun va => (dhDrawOf E Gr).bind fun vb =>
        (OracleAdv.run (OracleAdv.nfOracle (dhDrawOf E Gr)
          (dhCKASimStepOf pow epow ΔFS ΔPCS t (pow va.1) (pow vb.1)
            (if ideal then vb.2 else epow (pow va.1) vb.1))) play
          (CKAGameSt.init i.1 i.2.1 i.2.2)).map Prod.fst := by
  rw [run_dhCKAStep_eager, PMF.map_bind]
  congr 1; funext va
  rw [PMF.map_bind]
  congr 1; funext vb
  exact OracleAdv.run_nf_map_fst_eq_of_rel (dhDrawOf E Gr) _ _ (DHRel pow va.1 t)
    (fun s σ h q e => dhRel_step pow epow hcomm hFS hPCS t ideal va vb _ rfl s σ h q e) _ _ _
    (dhRel_initAt pow ht va.1 i hi)

/-- The run of the reduction tree at the pair is the run of the adversary against the
simulation step. -/
theorem ckaCorruptDDHTreeAt_run (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS : ℕ)
    (tStar : PMF ℕ) (play : ℕ → Gr → OracleAdv CKAQuery (CKAAns (Gr × E) Gr Gr E) α)
    (i : Gr × (Gr × E) × (Gr × E)) (ga gb z : Gr) :
    (OracleAdv.run emptyOracle (ckaCorruptDDHTreeAt pow epow ΔFS ΔPCS tStar play i ga gb z)
        ()).map Prod.fst =
      tStar.bind fun t =>
        (OracleAdv.run (OracleAdv.nfOracle (dhDrawOf E Gr)
          (dhCKASimStepOf pow epow ΔFS ΔPCS t ga gb z))
          (play t i.1) (CKAGameSt.init i.1 i.2.1 i.2.2)).map Prod.fst := by
  unfold ckaCorruptDDHTreeAt
  simp only [OracleAdv.run_rand, PMF.map_bind]
  congr 1; funext t
  rw [OracleAdv.run_simulate_fst]
  have hsim : OracleAdv.simOracle (ckaCorruptSimImplOf pow epow ΔFS ΔPCS t ga gb z)
      emptyOracle = OracleAdv.nfOracle (dhDrawOf E Gr) (fun σu q e =>
        ((dhCKASimStepOf pow epow ΔFS ΔPCS t ga gb z σu.1 q e).1,
          ((dhCKASimStepOf pow epow ΔFS ΔPCS t ga gb z σu.1 q e).2, ()))) := by
    funext σu q
    simp only [OracleAdv.simOracle, ckaCorruptSimImplOf, OracleAdv.run_rand, OracleAdv.run_ret,
      OracleAdv.nfOracle, dhDrawOf_map, PMF.map_bind, PMF.pure_map]
  rw [hsim]
  exact OracleAdv.run_nf_map_fst_eq_of_rel (dhDrawOf E Gr) _ _ (fun σu σ => σu.1 = σ)
    (fun σu σ h q e => by subst h; exact ⟨rfl, rfl⟩) _ _ _ rfl

omit [Fintype E] [Nonempty E] [Fintype Gr] [Nonempty Gr] in
/-- Reordering of three draws behind a fourth. -/
private theorem bind_swap_front {X Y Z β : Type} (τ : PMF X) (μ : PMF Y) (ν : PMF Z)
    (F : X → Y → Z → PMF β) :
    (τ.bind fun t => μ.bind fun a => ν.bind fun b => F t a b) =
      μ.bind fun a => ν.bind fun b => τ.bind fun t => F t a b := by
  rw [PMF.bind_comm τ μ]
  congr 1; funext a
  exact PMF.bind_comm _ _ _

omit [Fintype E] [Nonempty E] [Fintype Gr] [Nonempty Gr] in
/-- Reordering of four draws. -/
private theorem bind_swap_front_three {X Y Z W β : Type} (τ : PMF X) (μ : PMF Y) (ν : PMF Z)
    (ρ : PMF W) (F : X → Y → Z → W → PMF β) :
    (τ.bind fun t => μ.bind fun a => ν.bind fun b => ρ.bind fun u => F t a b u) =
      μ.bind fun a => ν.bind fun b => ρ.bind fun u => τ.bind fun t => F t a b u := by
  rw [PMF.bind_comm τ μ]
  congr 1; funext a
  exact bind_swap_front τ ν ρ _

/-- The real game at the pair `i`, for challenge epochs `t ≠ 1`, as a distribution, is the
distribution of the triple `(pow a, pow b, epow (pow a) b)` of two uniform keys followed by the
reduction tree at `i`. -/
theorem dhCKAGameAt_real (pow : E → Gr) (epow : Gr → E → Gr)
    (hcomm : ∀ x y, epow (pow x) y = epow (pow y) x) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 2 ≤ ΔPCS) (tStar : PMF ℕ) (htS : ∀ t ∈ tStar.support, t ≠ 1)
    (play : ℕ → Gr → OracleAdv CKAQuery (CKAAns (Gr × E) Gr Gr E) α)
    (i : Gr × (Gr × E) × (Gr × E)) (hi : i.2.1.1 = pow i.2.2.2) :
    (tStar.bind fun t => (OracleAdv.run (OracleAdv.nfOracle (dhDrawOf E Gr)
        (dhCKAStepOf pow epow ΔFS ΔPCS t false)) (play t i.1)
        (CKAGameSt.init i.1 i.2.1 i.2.2)).map Prod.fst) =
      ((PMF.uniformFintype E).bind fun a => (PMF.uniformFintype E).bind fun b =>
        PMF.pure (pow a, pow b, epow (pow a) b)).bind fun tr =>
          (OracleAdv.run emptyOracle (ckaCorruptDDHTreeAt pow epow ΔFS ΔPCS tStar play i tr.1
            tr.2.1 tr.2.2) ()).map Prod.fst := by
  rw [PMF.bind_congr_support _ _ _ fun t ht =>
    dhCKA_run_eq_sim_at pow epow hcomm hFS hPCS (htS t ht) false i hi (play t i.1)]
  simp only [PMF.bind_bind, PMF.pure_bind, ckaCorruptDDHTreeAt_run, dhDrawOf_bind,
    PMF.bind_const, Bool.false_eq_true, ite_false]
  exact bind_swap_front _ _ _ _

/-- The ideal game at the pair `i`, for challenge epochs `t ≠ 1`, as a distribution, is the
distribution of the triple `(pow a, pow b, u)` of two uniform keys and a uniform group element
followed by the reduction tree at `i`. -/
theorem dhCKAGameAt_ideal (pow : E → Gr) (epow : Gr → E → Gr)
    (hcomm : ∀ x y, epow (pow x) y = epow (pow y) x) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 2 ≤ ΔPCS) (tStar : PMF ℕ) (htS : ∀ t ∈ tStar.support, t ≠ 1)
    (play : ℕ → Gr → OracleAdv CKAQuery (CKAAns (Gr × E) Gr Gr E) α)
    (i : Gr × (Gr × E) × (Gr × E)) (hi : i.2.1.1 = pow i.2.2.2) :
    (tStar.bind fun t => (OracleAdv.run (OracleAdv.nfOracle (dhDrawOf E Gr)
        (dhCKAStepOf pow epow ΔFS ΔPCS t true)) (play t i.1)
        (CKAGameSt.init i.1 i.2.1 i.2.2)).map Prod.fst) =
      ((PMF.uniformFintype E).bind fun a => (PMF.uniformFintype E).bind fun b =>
        (PMF.uniformFintype Gr).bind fun u => PMF.pure (pow a, pow b, u)).bind fun tr =>
          (OracleAdv.run emptyOracle (ckaCorruptDDHTreeAt pow epow ΔFS ΔPCS tStar play i tr.1
            tr.2.1 tr.2.2) ()).map Prod.fst := by
  rw [PMF.bind_congr_support _ _ _ fun t ht =>
    dhCKA_run_eq_sim_at pow epow hcomm hFS hPCS (htS t ht) true i hi (play t i.1)]
  simp only [PMF.bind_bind, PMF.pure_bind, ckaCorruptDDHTreeAt_run, dhDrawOf_bind,
    PMF.bind_const, ite_true]
  exact bind_swap_front_three _ _ _ _ _

end DHAt

section DHKeysAt

variable {G : Type} [CG : CyclicGroup G] {Sk : Type} [Fintype Sk] [Nonempty Sk]

/-- **The signed-prekey pair** of the key `x₀`: the public value `g^{x₀}`; the first sender `A`
holds the public value and the default key; the first receiver `B` holds the public value and
`x₀`. -/
def dhPairInit [Inhabited Sk] (decE : Sk → CG.Exp) (x₀ : Sk) : G × (G × Sk) × (G × Sk) :=
  (CG.pow (decE x₀), (CG.pow (decE x₀), default), (CG.pow (decE x₀), x₀))

/-- The corruption game of `dhCKAOf G decE` at the pair `i` is the lifted distribution of the
run from the states of `i` after the choice of the challenge epoch. -/
theorem dhCKAOf_atInit_game_eq (decE : Sk → CG.Exp) (i : G × (G × Sk) × (G × Sk))
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (A : CKACorruptAdv (G × Sk) G G Sk α) :
    cka_corrupt_game ((dhCKAOf G decE).atInit i) ΔFS ΔPCS ideal A =
      liftPMF (A.tStar.bind fun t => (OracleAdv.run (OracleAdv.nfOracle (dhDrawOf Sk G)
        (dhCKAStepOf (fun x => CG.pow (decE x)) (fun h x => CyclicGroup.elemPow h (decE x))
          ΔFS ΔPCS t ideal)) (A.play t i.1) (CKAGameSt.init i.1 i.2.1 i.2.2)).map Prod.fst) := by
  have hrun : ∀ t (B : OracleAdv CKAQuery (CKAAns (G × Sk) G G Sk) α) s,
      OracleAdv.runSP (ckaCorruptOracle ((dhCKAOf G decE).atInit i) ΔFS ΔPCS t ideal) B s =
        liftPMF (OracleAdv.run (OracleAdv.nfOracle (dhDrawOf Sk G)
          (dhCKAStepOf (fun x => CG.pow (decE x)) (fun h x => CyclicGroup.elemPow h (decE x))
            ΔFS ΔPCS t ideal)) B s) :=
    fun t B s => runSP_dhCKAOf decE ΔFS ΔPCS t ideal B s
  unfold cka_corrupt_game
  simp only [hrun]
  simp only [CKADef.atInit, SPComp.pure_bind, liftPMF_bind_pure, liftPMF_bind_liftPMF]

/-- **The DDH reduction at the signed-prekey pair** `ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS A`:
the tree `ckaCorruptDDHTreeAt` at the pair `dhPairInit decE x₀` with the exponentiations
`x ↦ g ^ decE x` and `(h, x) ↦ h ^ decE x`, run as a distribution. -/
noncomputable def ckaCorruptDDHRedAt [Inhabited Sk] (decE : Sk → CG.Exp) (x₀ : Sk)
    (ΔFS ΔPCS : ℕ) (A : CKACorruptAdv (G × Sk) G G Sk Bool) : G × G × G → SPComp Bool :=
  fun tr => liftPMF ((OracleAdv.run emptyOracle (ckaCorruptDDHTreeAt (fun x => CG.pow (decE x))
    (fun h x => CyclicGroup.elemPow h (decE x)) ΔFS ΔPCS A.tStar A.play (dhPairInit decE x₀)
    tr.1 tr.2.1 tr.2.2) ()).map Prod.fst)

/-- **The corruption game at the signed-prekey pair as a DDH game over a sampler.** With
`2 ≤ ΔFS`, `2 ≤ ΔPCS` and challenge epochs at least `2`, the corruption advantage of
`(dhCKAOf G decE).atInit (dhPairInit decE x₀)` equals the advantage of the reduction
`ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS A` against the DDH games `ddhSampledUnif G` whose two
exponents are drawn as `decE` of uniform keys. -/
theorem dhCKAOf_atInit_corrupt_advantage_eq_advAt [Inhabited Sk] (decE : Sk → CG.Exp)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS) (x₀ : Sk)
    (A : CKACorruptAdv (G × Sk) G G Sk Bool) (hA : ∀ t ∈ A.tStar.support, 2 ≤ t) :
    CKA_Corrupt_Advantage ((dhCKAOf G decE).atInit (dhPairInit decE x₀)) ΔFS ΔPCS A =
      (ddhSampledUnif G).advAt ((SDistr.uniform Sk).bind fun x => SDistr.pure (decE x))
        (ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS A) := by
  have hcomm : ∀ x y : Sk, CyclicGroup.elemPow (CG.pow (decE x)) (decE y) =
      CyclicGroup.elemPow (CG.pow (decE y)) (decE x) := fun x y => elemPow_pow_comm _ _
  have htS : ∀ t ∈ A.tStar.support, t ≠ 1 := fun t ht => by have := hA t ht; omega
  unfold CKA_Corrupt_Advantage SampledGame.advAt AdvantageA cka_corrupt_real cka_corrupt_ideal
    ckaCorruptDDHRedAt
  rw [dhCKAOf_atInit_game_eq, dhCKAOf_atInit_game_eq,
    dhCKAGameAt_real _ _ hcomm hFS hPCS _ htS _ _ rfl,
    dhCKAGameAt_ideal _ _ hcomm hFS hPCS _ htS _ _ rfl, ddhSampledUnif_realAt_keys,
    ddhSampledUnif_idealAt_keys]
  simp only [liftPMF_bind_liftPMF, CyclicGroup.elemPow_pow]

/-- **CKA security of the Diffie–Hellman CKA at the signed-prekey pair.** Let `c` be a sampler
certificate of the image of the uniform key of `Sk` under `decE` against the uniform exponent,
let `2 ≤ ΔFS`, `2 ≤ ΔPCS`, and let the challenge epochs of `A` be at least `2`. The corruption
advantage of `(dhCKAOf G decE).atInit (dhPairInit decE x₀)` is at most the DDH advantage of
the reduction `ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS A` plus `4 c.δ`. -/
theorem dhCKAOf_atInit_corrupt_advantage_le [Inhabited Sk] (decE : Sk → CG.Exp)
    (c : SamplerCert CG.Exp) (hμ : c.μ = (SDistr.uniform Sk).bind fun x => SDistr.pure (decE x))
    (hν : c.ν = SDistr.uniform CG.Exp) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS)
    (x₀ : Sk) (A : CKACorruptAdv (G × Sk) G G Sk Bool) (hA : ∀ t ∈ A.tStar.support, 2 ≤ t) :
    CKA_Corrupt_Advantage ((dhCKAOf G decE).atInit (dhPairInit decE x₀)) ΔFS ΔPCS A ≤
      DDH_Advantage G (ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS A) + 4 * c.δ := by
  rw [dhCKAOf_atInit_corrupt_advantage_eq_advAt decE hFS hPCS x₀ A hA, ← hμ,
    ← ddhSampledUnif_advAt_uniform, ← hν]
  refine ((ddhSampledUnif G).advAt_le c _).trans (le_of_eq ?_)
  norm_num [ddhSampledUnif]

end DHKeysAt

end CatCrypt.Crypto.Messaging
