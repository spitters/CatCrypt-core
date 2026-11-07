/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.DDHSampled
public import CatCryptCore.Tactics.BindSwap

/-!
# DDH hops with the replaced value drawn by key generation

A game that generates two key pairs `b` and `a`, computes the DH value `dh a.1 b.2` and runs a
continuation `k` on the two public keys and that value, against the game in which the DH value
is replaced by the public part of a fresh key pair: the advantage of a distinguisher `A`
between the two is the DDH advantage `DDH_AdvantageK` of an explicit reduction, which runs `k`
on its challenge and then `A`. In `ddhK_hop` a prefix `pre` runs before both key generations
and a computation `mid` between them; the reduction samples both itself.

## Main definitions

* `ddhRed₀ k A` — the reduction of a hop with no prefix
* `ddhRed pre mid k A` — the reduction of a hop with a prefix and a middle computation

## Main results

* `ddhK_hop₀` — the advantage of `A` between the two games with no prefix is
  `DDH_AdvantageK D (ddhRed₀ k A)`
* `ddhK_hop` — the advantage of `A` between the two games with a prefix and a middle
  computation is `DDH_AdvantageK D (ddhRed pre mid k A)`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## Reductions -/

/-- The DDH reduction of a DH hop: on the challenge `(g^a, g^b, z)` it samples the prefix
`pre` and the middle `mid`, runs the continuation `k` and calls `A` once. -/
noncomputable def ddhRed {P Q α : Type} (pre : SPComp P) (mid : P → W → SPComp Q)
    (k : P → Q → W → W → W → SPComp α) (A : α → SPComp Bool) : DDH_Adversary W :=
  fun ga gb z => SPComp.bind pre fun p => SPComp.bind (mid p gb) fun q => (k p q ga gb z).bind A

/-- The DDH reduction of a DH hop with no prefix: on the challenge `(g^a, g^b, z)` it runs the
continuation `k` and calls `A` once. -/
noncomputable def ddhRed₀ {α : Type} (k : W → W → W → SPComp α) (A : α → SPComp Bool) :
    DDH_Adversary W :=
  fun ga gb z => (k ga gb z).bind A

/-! ## Hops -/

/-- **DH hop with no prefix, the replaced value drawn by key generation**: the DH value
`dh a.1 b.2` of the key pairs `b` and `a`, generated first, replaced by the public part of a
fresh key pair. The advantage is the DDH advantage `DDH_AdvantageK` of `ddhRed₀ k A`. -/
theorem ddhK_hop₀ (D : DDHDef W) {α : Type} (k : W → W → W → SPComp α)
    (A : α → SPComp Bool) :
    AdvantageA
      (SPComp.bind D.keygen fun b => SPComp.bind D.keygen fun a => k a.2 b.2 (D.ecdh a.1 b.2))
      (SPComp.bind D.keygen fun b => SPComp.bind D.keygen fun a =>
        SPComp.bind D.keygen fun c => k a.2 b.2 c.2) A =
      DDH_AdvantageK D (ddhRed₀ k A) := by
  unfold AdvantageA DDH_AdvantageK DDH_Game_Real DDH_Game_IdealK DDH_ViewIdealK ddhRed₀
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1 <;> bind_swap_nf [D.keygen_isPure]

/-- **DH hop, the replaced value drawn by key generation**: the DH value `dh a.1 b.2` of the
key pairs `b` and `a`, generated after the prefix `pre` and around the middle `mid`, replaced
by the public part of a fresh key pair. The advantage is the DDH advantage `DDH_AdvantageK` of
`ddhRed pre mid k A`. -/
theorem ddhK_hop (D : DDHDef W) {P Q α : Type} (pre : SPComp P)
    (mid : P → W → SPComp Q) (k : P → Q → W → W → W → SPComp α) (A : α → SPComp Bool) :
    AdvantageA
      (SPComp.bind pre fun p => SPComp.bind D.keygen fun b =>
        SPComp.bind (mid p b.2) fun q => SPComp.bind D.keygen fun a =>
          k p q a.2 b.2 (D.ecdh a.1 b.2))
      (SPComp.bind pre fun p => SPComp.bind D.keygen fun b =>
        SPComp.bind (mid p b.2) fun q => SPComp.bind D.keygen fun a =>
          SPComp.bind D.keygen fun c => k p q a.2 b.2 c.2) A =
      DDH_AdvantageK D (ddhRed pre mid k A) := by
  unfold AdvantageA DDH_AdvantageK DDH_Game_Real DDH_Game_IdealK DDH_ViewIdealK ddhRed
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1 <;> bind_swap_nf [D.keygen_isPure]

end CatCrypt.Crypto.Assumptions
