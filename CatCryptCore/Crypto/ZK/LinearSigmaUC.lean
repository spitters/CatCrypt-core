/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.ZK.SigmaUCZK
public import CatCryptCore.Crypto.FiatShamirROM.Bridge
public import CatCryptCore.Crypto.FiatShamirROM.LinearRelation

/-!
# Honest-verifier UC zero knowledge of the Σ-protocols of linear relations

For a Σ-protocol `P` of the Fiat–Shamir development, perfect honest-verifier zero
knowledge at every pair of the relation (the honest `(commit, respond e)` on uniform
prover randomness and the simulator output on uniform simulator randomness have the
same distribution) gives `SHVZK` of the stateless protocol `P.toSigmaProtocol`, and
hence honest-verifier UC zero knowledge with error `0` through `sigma_uc_zk_secure`.

The Σ-protocol `linearSigma gp n m toRel gen` of a family of linear relations has
this property at every pair of the relation, for every generator `gen`: the
simulator does not read the witness, and the response map `r ↦ r + e·w` is a
bijection of the nonces.

The UC statement concerns the interactive protocol with an honest verifier. The
non-interactive Fiat–Shamir form of the same protocol is covered by the zero-knowledge
bounds of `CatCryptCore.Crypto.FiatShamirROM.NIZK` (`linearSigma_zkReal_le_zkSim`).

## Main results

* `Sigma.shvzk_toSigmaProtocol` — per-pair perfect HVZK gives `SHVZK P.toSigmaProtocol`
* `Sigma.toSigmaProtocol_uc_zk_secure` — per-pair perfect HVZK gives honest-verifier
  UC zero knowledge of `P.toSigmaProtocol` at `ε = 0`
* `linearSigma_shvzk`, `linearSigma_uc_zk_secure` — the same for `linearSigma`, with no
  hypothesis on the generator
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Examples
open CatCrypt.Examples.Sigma CatCrypt.Crypto.ZK.SigmaUCZK

namespace Sigma

variable (P : Sigma)

/-- Perfect honest-verifier zero knowledge at every pair of the relation gives
`SHVZK` of `P.toSigmaProtocol`: for `(x, w)` in the relation and every challenge `e`,
the honest `(commit, respond e)` equals the simulator `simulate x e` as computations. -/
theorem shvzk_toSigmaProtocol
    (h : ∀ x w, P.rel x w → ∀ e,
      (PMF.uniformFintype P.Rand).map (fun r => (P.commit x w r, P.respond x w r e)) =
        (PMF.uniformFintype P.SimRand).map (P.simulate x e)) :
    ZK.SigmaUCZK.SHVZK P.toSigmaProtocol := by
  intro (x : P.Stmt) (w : P.Wit) (e : P.Ch) hrel
  have hreal : (do
      let a ← P.toSigmaProtocol.commit x w
      let z ← P.toSigmaProtocol.respond x w a e
      SPComp.pure (a, z) : SPComp (P.Com × P.Resp)) =
      liftSDistr (((PMF.uniformFintype P.Rand).map
        (fun r => (P.commit x w r, P.respond x w r e))).map some) := by
    rw [map_pair_eq_bind_fibreDist]
    simp only [SPComp.monad_bind_eq]
    funext hp
    simp only [toSigmaProtocol, SPComp.bind, SPComp.pure, liftSDistr, SDistr.bind, SDistr.pure,
      respondDist, PMF.bind_map, PMF.map_bind, PMF.bind_bind, PMF.map_comp, Function.comp_def,
      PMF.pure_bind]
  refine hreal.trans ?_
  rw [h x w hrel e]
  rfl

/-- **Honest-verifier UC zero knowledge of `P.toSigmaProtocol` at `ε = 0`**, from
perfect honest-verifier zero knowledge at every pair of the relation.

* Ideal functionality `sigma_ideal`: on input `(x, w)` with `P.rel x w` it outputs
  the statement `x`; otherwise it aborts with `.inl ()`.
* Real world `sigma_real`: the honest prover commits to `a`, the verifier samples the
  challenge `e` uniformly, the prover responds with `z`, and the environment sees
  `(x, a, e, z)` through the transcript `(a, e, z)`.
* Simulator `sigma_uc_sim`: on `x` it samples `e` uniformly and runs `simulate x e` to
  obtain `(a, z)`, without the witness.

The verifier is honest; the non-interactive form is covered by the Fiat–Shamir
bounds of the same module chain. (genuine UC) -/
theorem toSigmaProtocol_uc_zk_secure
    (h : ∀ x w, P.rel x w → ∀ e,
      (PMF.uniformFintype P.Rand).map (fun r => (P.commit x w r, P.respond x w r e)) =
        (PMF.uniformFintype P.SimRand).map (P.simulate x e))
    (V : Type) :
    UCEmulates 0 (sigmaUCZKSpec P.toSigmaProtocol V) (sigma_real P.toSigmaProtocol)
      (sigma_ideal P.toSigmaProtocol) :=
  sigma_uc_zk_secure P.toSigmaProtocol (P.shvzk_toSigmaProtocol h) V

end Sigma

section Linear

variable {gp : GroupParam} {n m : ℕ} {S : Type} (toRel : S → LinearRelation gp n m)
  (gen : PMF (S × (Fin n → gp.Scalar)))

/-- The stateless protocol of `linearSigma` satisfies `SHVZK` for every generator. -/
theorem linearSigma_shvzk :
    ZK.SigmaUCZK.SHVZK (linearSigma gp n m toRel gen).toSigmaProtocol := by
  refine (linearSigma gp n m toRel gen).shvzk_toSigmaProtocol
    fun (s : S) (w : Fin n → gp.Scalar) hw c => ?_
  exact linearSigma_perfectHVZK (gen := PMF.pure (s, w)) toRel (fun s' w' hsw => by
    rw [PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsw
    obtain ⟨rfl, rfl⟩ := hsw
    exact hw) s w ((PMF.mem_support_pure_iff _ _).mpr rfl) c

/-- **Honest-verifier UC zero knowledge of the Σ-protocol of a linear relation at
`ε = 0`**, for every family of linear relations `toRel` and every generator `gen`.

* Ideal functionality `sigma_ideal`: on input `(s, w)` with `(toRel s).Holds w` it
  outputs the statement `s`; otherwise it aborts with `.inl ()`.
* Real world `sigma_real`: the honest prover commits to `a = map r` for uniform nonces
  `r`, the verifier samples the challenge `c` uniformly, the prover responds with
  `z = r + c·w`, and the environment sees `(s, a, c, z)` through the transcript.
* Simulator `sigma_uc_sim`: on `s` it samples `c` uniformly and runs the simulator of
  `linearSigma` (uniform `z`, `a = map z · image^(−c)`), without the witness.

The verifier is honest; the non-interactive form is covered by the Fiat–Shamir
bounds of the same module chain (`linearSigma_zkReal_le_zkSim`). (genuine UC) -/
theorem linearSigma_uc_zk_secure (V : Type) :
    UCEmulates 0 (sigmaUCZKSpec (linearSigma gp n m toRel gen).toSigmaProtocol V)
      (sigma_real (linearSigma gp n m toRel gen).toSigmaProtocol)
      (sigma_ideal (linearSigma gp n m toRel gen).toSigmaProtocol) :=
  sigma_uc_zk_secure _ (linearSigma_shvzk toRel gen) V

end Linear

end CatCrypt.Crypto.FiatShamirROM
