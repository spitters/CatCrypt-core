/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCConcrete
public import CatCryptCore.Examples.ElGamalDDH

@[expose] public section
set_option autoImplicit false

/-!
# ElGamal IND-CPA as Concrete UC Emulation from DDH

The ElGamal IND-CPA game pair, indexed by the message pair `(m₀, m₁)`, as a
concrete UC emulation whose bound is the DDH advantage of explicit reductions.
For every adversary `A` and environment `Z`, the gap is at most

`DDH_Advantage (Reduction m₀ (envReduction A Z)) + DDH_Advantage (Reduction m₁ (envReduction A Z))`

where `(m₀, m₁) = Z.input`, `envReduction A Z` runs `A` and then `Z`'s
distinguisher, and `Reduction` embeds a DDH triple as public key and
ciphertext (`ElGamalDDH.Reduction`).

## Main results

* `elgamalGameAdvBoundC` — the concrete game bound, from
  `elgamal_indcpa_security`.
* `elgamal_uc_concrete` — concrete UC emulation, obtained by instance search.
* `elgamal_uc_concrete_apply` — the same statement for a fixed adversary and
  environment, with the reductions written out.
-/

namespace CatCryptCore.Examples.ElGamalUCConcrete

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCDSL CatCrypt.Crypto.UCConcrete
open CatCryptCore.Examples.CyclicGroupDDH CatCryptCore.Examples.ElGamalDDH
open scoped ENNReal

variable (G : Type) [CG : CyclicGroup G]

/-- IND-CPA real game indexed by the message pair: encrypt `m₀`. -/
noncomputable def elgamalReal : G × G → SPComp (G × ElGamalScheme.Ciphertext G) :=
  fun m => ElGamal_INDCPA_real G m.1 m.2

/-- IND-CPA ideal game indexed by the message pair: encrypt `m₁`. -/
noncomputable def elgamalIdeal : G × G → SPComp (G × ElGamalScheme.Ciphertext G) :=
  fun m => ElGamal_INDCPA_ideal G m.1 m.2

/-- DDH bound of a distinguisher `D` on messages `m`: the DDH advantages of the
    two reductions embedding `m₀` and `m₁`. -/
noncomputable def elgamalDDHBound :
    G × G → (G × ElGamalScheme.Ciphertext G → SPComp Bool) → ℝ≥0∞ :=
  fun m D => DDH_Advantage G (Reduction G m.1 D) + DDH_Advantage G (Reduction G m.2 D)

/-- The real IND-CPA game does not read the heap. -/
theorem elgamalReal_isPure (m₀ m₁ : G) : SPComp.IsPure (ElGamal_INDCPA_real G m₀ m₁) := by
  rw [INDCPA_real_ignores_m1 G m₀ m₁ m₀, ElGamal_INDCPA_real_simplified]
  exact SPComp.bind_isPure (SPComp.sample_isPure _) fun _ =>
    SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _

instance : PureGame (elgamalReal G) :=
  ⟨fun m => elgamalReal_isPure G m.1 m.2⟩

instance : PureGame (elgamalIdeal G) :=
  ⟨fun m => by
    show SPComp.IsPure (ElGamal_INDCPA_ideal G m.1 m.2)
    rw [INDCPA_ideal_eq_real_m1]
    exact elgamalReal_isPure G m.2 m.2⟩

/-- Concrete game bound: IND-CPA advantage of `D` on `(m₀, m₁)` is at most the
    DDH advantages of the reductions built from `D`. -/
instance elgamalGameAdvBoundC :
    GameAdvBoundC (elgamalReal G) (elgamalIdeal G) (elgamalDDHBound G) :=
  ⟨fun m D => elgamal_indcpa_security G m.1 m.2 D⟩

/-- ElGamal IND-CPA as concrete UC emulation from DDH (composition plumbing,
    simulator `S = A`): the bound of adversary `A` and environment `Z` is the
    DDH advantage of the reductions of `envReduction A Z`. -/
theorem elgamal_uc_concrete (V : Type) :
    UCEmulatesCSim (UCSpec.ofGame (G × G) (G × ElGamalScheme.Ciphertext G) V)
      (UCProtocol.ofGame (elgamalReal G)) (UCProtocol.ofGame (elgamalIdeal G)) id
      (gameUCBound (elgamalDDHBound G)) :=
  UCFromGameC.uc

/-- `elgamal_uc_concrete` for a fixed adversary `A` and environment `Z`, with
    the DDH reductions written out. -/
theorem elgamal_uc_concrete_apply (V : Type)
    (A : G × ElGamalScheme.Ciphertext G → SPComp V)
    (Z : Env (G × G) (Unit ⊕ V)) :
    Env.gap (fun m => SPComp.bind (UCProtocol.ofGame (elgamalReal G) m) (mapSum SPComp.pure A))
      (fun m => SPComp.bind (UCProtocol.ofGame (elgamalIdeal G) m) (mapSum SPComp.pure A)) Z ≤
    DDH_Advantage G (Reduction G Z.input.1 (envReduction A Z)) +
      DDH_Advantage G (Reduction G Z.input.2 (envReduction A Z)) :=
  elgamal_uc_concrete G V A Z

end CatCryptCore.Examples.ElGamalUCConcrete
