/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.TripleRatchet
public import CatCryptCore.Crypto.UCConcrete

/-!
# UC Security of the Signal Triple Ratchet

The secure-messaging game of the Signal triple ratchet (`TripleRatchet.tr_real`/`tr_ideal`: the
Diffie–Hellman CKA and the KEM CKA side by side, the root dual PRF and the Signal symmetric
ratchet) is bounded per distinguisher: the advantage of `D` is at most `trHybridBound cfg msgs D`,
the minimum of the DDH chain and the KEM chain of explicit reductions built from `D`
(`tr_advantage_bound`, core `tr_advantage_le_min`). The UC statement `tr_uc_secure` is derived
by `UCFromGameC` instance search from the `PureGame` instances of the game families and the
`GameAdvBoundC` instance `instTRGameAdvBoundC`; `tr_distC` is the concrete distance of the
games wrapped by `UCProtocol.ofGame`.

## Main results

* `instTRGameAdvBoundC` — the per-distinguisher game bound
* `tr_uc_secure` — `UCEmulatesCSim` at `trHybridBound` of `envReduction A Z`
* `tr_distC` — concrete distance of the wrapped games at `trHybridBound` of
  `envReduction SPComp.pure Z`

## References

* Y. Dodis, D. Jost, S. Katsumata, T. Prest, R. Schmidt, *Triple Ratchet: A Bandwidth
  Efficient Hybrid-Secure Signal Protocol*, EUROCRYPT 2025
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.TripleRatchet_UC

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Prob CatCrypt.Crypto.UCDSL
open CatCrypt.Crypto.Signal.TripleRatchet
open CatCrypt.Crypto.UCConcrete
open CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

variable {G : Type} [CyclicGroup G] {PK SK K KC RK W : Type} [CryptoWord W] [Inhabited K]
  [Fintype K] [Nonempty K] [Fintype RK] [Nonempty RK]

/-- The triple ratchet real game family is pure. -/
instance (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W)) :
    PureGame (fun (_ : Unit) => tr_real G cfg msgs) :=
  ⟨fun _ => tr_real_isPure G cfg msgs⟩

/-- The triple ratchet ideal game family is pure. -/
instance (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W)) :
    PureGame (fun (_ : Unit) => tr_ideal G cfg msgs) :=
  ⟨fun _ => tr_ideal_isPure G cfg msgs⟩

variable [DecidableEq G] [Fintype KC] [Nonempty KC] [DecidableEq K] [DecidableEq RK]

/-- The per-distinguisher triple ratchet bound `trHybridBound cfg msgs D`, from
`tr_advantage_bound`. -/
instance instTRGameAdvBoundC (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W)) :
    GameAdvBoundC (fun (_ : Unit) => tr_real G cfg msgs) (fun _ => tr_ideal G cfg msgs)
      (fun _ D => trHybridBound G cfg msgs D) :=
  ⟨fun _ D => tr_advantage_bound G cfg msgs D⟩

/-- **UC security of the Signal triple ratchet**, derived by `UCFromGameC` instance search
(simulator `S = A`): the bound for adversary `A` and environment `Z` is
`trHybridBound cfg msgs (envReduction A Z)`, the minimum of the DDH chain and the KEM chain. -/
theorem tr_uc_secure (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W)) (V : Type) :
    UCEmulatesCSim (UCSpec.ofGame Unit (TRView G KC PK W) V)
      (UCProtocol.ofGame fun (_ : Unit) => tr_real G cfg msgs)
      (UCProtocol.ofGame fun (_ : Unit) => tr_ideal G cfg msgs) id
      (gameUCBound (fun _ D => trHybridBound G cfg msgs D)) :=
  (inferInstance : UCFromGameC (fun (_ : Unit) => tr_real G cfg msgs)
    (fun _ => tr_ideal G cfg msgs) V (fun _ D => trHybridBound G cfg msgs D)).uc

/-- **Concrete distance of the wrapped triple ratchet games**, on inputs of any type `α`: every
environment `Z` is charged `trHybridBound` at `envReduction SPComp.pure Z`. -/
theorem tr_distC {α : Type} (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W)) :
    DistC (fun _ : α => UCProtocol.ofGame (fun (_ : Unit) => tr_real G cfg msgs) ())
      (fun _ => UCProtocol.ofGame (fun (_ : Unit) => tr_ideal G cfg msgs) ())
      (fun Z => trHybridBound G cfg msgs (envReduction SPComp.pure Z)) :=
  DistC_ofGame (bound := fun _ D => trHybridBound G cfg msgs D) ()

end CatCrypt.Crypto.Signal.TripleRatchet_UC
