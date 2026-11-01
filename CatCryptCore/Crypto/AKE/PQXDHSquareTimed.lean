/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHSquare
public import CatCryptCore.Crypto.AKE.X3DHSquareTimed
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the PQXDH simulator

`derive_reduction` builds the costed form `simProtK.timed` of the multi-call simulator
`simProtK O G` of `PQXDHSquare.lean` over the KEM operations `O` and its erasure theorem. Key
generation `O.keygen` and encapsulation `O.encaps` are priced by their cost companions, and
decapsulation `O.decaps` by its cost companion. The steps `ltStep` and `roStep` shared with X3DH
are the costed forms of `X3DHSquareTimed.lean`.

No module imports this file.

## Main results

* `simProtK.timed`, `simProtK.erase_timed`: the costed multi-call simulator and its erasure.
* `simProtK.resume.tree.timeBound_timed`, `simProtK.finish.tree.timeBound_timed`: `resume` and
  `finish` cost at most two units.
* `simProtK.start_time`: the time of `start` on an event other than `complete` and `send`,
  linear in the time of key generation, the length of the key-derivation table and the number
  of notices.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.PQXDHSquare

open CatCrypt.Core

set_option maxHeartbeats 400000 in
-- The start step reflects thirteen event cases with nested record updates.
derive_reduction simProtK

derive_time_bound simProtK.resume.tree
derive_time_bound simProtK.finish.tree

section Time

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS]

/-- Whether an event of the real interface is `complete` or `send`, the two events on which the
simulator encapsulates or decapsulates. -/
def IsKemEvent : OEv W SS C → Bool
  | .inr (.complete _ _) | .inr (.send _ _ _ _) => true
  | _ => false

set_option maxHeartbeats 1600000 in
-- Eleven event cases, each consumed node by node by `time_bound`, above the default budget.
/-- **Time of the `start` step of the costed PQXDH simulator** on an event other than `complete`
and `send`: at most `100 + 20 t_coe + t_keygen` plus twenty units per entry of the
key-derivation table and per notice of the state, where `t_keygen` bounds the time of the
costed key generation. -/
theorem simProtK.start_time (O : KemOps PK SK SS C) (G : PAKE.DHExtract.DHGroup S W)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ) (decaps : SK → C → Option SS)
    (decapsCost : SK → C → ℕ) (keygen : SPTree.Timed (PK × SK))
    (encaps : PK → SPTree.Timed (SS × C)) (encapsCost : PK → ℕ) (expCost : W → S → ℕ)
    (toFunCost : S → ℕ) (s : SimSt S W K PK SK SS C) (e : OEv W SS C) (he : IsKemEvent e = false)
    {t_coeCost t_keygen : ℕ} (hcoe : ∀ a b, coeCost a b ≤ t_coeCost)
    (hkg : keygen.time ≤ t_keygen) :
    SPTree.Timed.stepTime
        (simProtK.start.tree.timed O G coe coeCost decaps decapsCost keygen encaps encapsCost s e
          expCost toFunCost) ≤
      100 + 20 * t_coeCost + t_keygen + 20 * s.1.ro.length + 20 * s.1.x.st.notices.length := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | x)
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · time_bound
  · simp [IsKemEvent] at he
  · simp [IsKemEvent] at he
  · time_bound

end Time

end CatCrypt.Crypto.AKE.PQXDHSquare
