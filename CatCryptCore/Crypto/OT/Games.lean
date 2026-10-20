/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage

/-!
# Oblivious transfer: semi-honest security games and correlation-robust hashing

An OT scheme (`OTScheme k M VS VR`) is a two-party protocol for `k` parallel 1-out-of-2
oblivious transfers of messages in `M`: the sender holds `k` message pairs, the receiver
`k` choice bits. A semi-honest execution returns the view of the sender (`VS`), the view
of the receiver (`VR`) and the receiver's output. The ideal functionality gives the
receiver the chosen messages (`otChoose`) and the sender nothing.

Security is simulation-based against a semi-honest adversary (`OTAdversary`) that draws
both parties' inputs and a state, and distinguishes the corrupted party's view together
with the receiver's output.

* Receiver privacy (corrupted sender): the sender's view is simulated from the sender's
  inputs (`otRecvPrivReal`, `otRecvPrivIdeal`, `otRecvPrivAdvantage`).
* Sender privacy (corrupted receiver): the receiver's view is simulated from its choices
  and its output (`otSendPrivReal`, `otSendPrivIdeal`, `otSendPrivAdvantage`).

A hash `H : Fin m → R → M` over an additive group `R` is correlation robust in the sense of
Ishai–Kilian–Nissim–Petrank when, for uniform `t : Fin m → R` and a uniform secret
`s : R`, the tuple `(t, (H j (t j + s))_j)` is indistinguishable from `(t, u)` with `u`
uniform (`crHashReal`, `crHashIdeal`, `CRHash_Advantage`).

## Main definitions

* `OTScheme`, `otChoose`, `OTAdversary`
* `otRecvPrivAdvantage`, `otSendPrivAdvantage` — the two semi-honest advantages
* `CRHash_Advantage` — the correlation-robust hash advantage of a distinguisher

## References

* Y. Ishai, J. Kilian, K. Nissim, E. Petrank, *Extending Oblivious Transfers
  Efficiently*, CRYPTO 2003, Definition 2.1 (correlation robustness)
* O. Goldreich, *Foundations of Cryptography II*, §7.2.2 (semi-honest security)
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace CatCrypt.Crypto.OT

/-! ## OT schemes and their semi-honest games -/

/-- A protocol for `k` parallel 1-out-of-2 oblivious transfers of messages in `M`: on the
sender's message pairs and the receiver's choice bits, a semi-honest execution returns the
sender's view, the receiver's view and the receiver's output. -/
structure OTScheme (k : ℕ) (M VS VR : Type) where
  /-- Semi-honest execution: sender's view, receiver's view, receiver's output. -/
  exec : (Fin k → M × M) → (Fin k → Bool) → SPComp (VS × VR × (Fin k → M))

/-- The output of the ideal OT functionality: the message of each pair selected by the
choice bit. -/
def otChoose {k : ℕ} {M : Type} (x : Fin k → M × M) (b : Fin k → Bool) : Fin k → M :=
  fun i => if b i then (x i).2 else (x i).1

/-- A semi-honest OT adversary with state `S` against the view `V` of the corrupted
party: it draws the sender's message pairs, the receiver's choices and a state, and
distinguishes the corrupted party's view together with the receiver's output. -/
structure OTAdversary (k : ℕ) (M V S : Type) where
  /-- The parties' inputs and the adversary's state. -/
  choose : SPComp ((Fin k → M × M) × (Fin k → Bool) × S)
  /-- The distinguisher on the state, the view and the receiver's output. -/
  guess : S → V × (Fin k → M) → SPComp Bool

variable {k : ℕ} {M VS VR S : Type}

/-- Receiver privacy, real game: the corrupted sender's view and the receiver's output
of an execution. -/
noncomputable def otRecvPrivReal (P : OTScheme k M VS VR) (A : OTAdversary k M VS S) :
    SPComp Bool :=
  SPComp.bind A.choose fun i =>
    SPComp.bind (P.exec i.1 i.2.1) fun e => A.guess i.2.2 (e.1, e.2.2)

/-- Receiver privacy, ideal game: the sender's view simulated from its inputs, and the
ideal output. -/
noncomputable def otRecvPrivIdeal (simS : (Fin k → M × M) → SPComp VS)
    (A : OTAdversary k M VS S) : SPComp Bool :=
  SPComp.bind A.choose fun i =>
    SPComp.bind (simS i.1) fun v => A.guess i.2.2 (v, otChoose i.1 i.2.1)

/-- Receiver-privacy advantage of `A` against the scheme `P` and the sender simulator
`simS`. -/
noncomputable def otRecvPrivAdvantage (P : OTScheme k M VS VR)
    (simS : (Fin k → M × M) → SPComp VS) (A : OTAdversary k M VS S) : ℝ≥0∞ :=
  Advantage (otRecvPrivReal P A) (otRecvPrivIdeal simS A)

/-- Sender privacy, real game: the corrupted receiver's view and output of an
execution. -/
noncomputable def otSendPrivReal (P : OTScheme k M VS VR) (A : OTAdversary k M VR S) :
    SPComp Bool :=
  SPComp.bind A.choose fun i =>
    SPComp.bind (P.exec i.1 i.2.1) fun e => A.guess i.2.2 (e.2.1, e.2.2)

/-- Sender privacy, ideal game: the receiver's view simulated from its choices and the
ideal output, and the ideal output. -/
noncomputable def otSendPrivIdeal (simR : (Fin k → Bool) → (Fin k → M) → SPComp VR)
    (A : OTAdversary k M VR S) : SPComp Bool :=
  SPComp.bind A.choose fun i =>
    SPComp.bind (simR i.2.1 (otChoose i.1 i.2.1)) fun v =>
      A.guess i.2.2 (v, otChoose i.1 i.2.1)

/-- Sender-privacy advantage of `A` against the scheme `P` and the receiver simulator
`simR`. -/
noncomputable def otSendPrivAdvantage (P : OTScheme k M VS VR)
    (simR : (Fin k → Bool) → (Fin k → M) → SPComp VR) (A : OTAdversary k M VR S) : ℝ≥0∞ :=
  Advantage (otSendPrivReal P A) (otSendPrivIdeal simR A)

/-! ## Correlation-robust hashing -/

section CRHash

variable {m : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [Nonempty R]
  [Fintype M] [Nonempty M]

/-- Correlation-robust hash, real game: uniform `t : Fin m → R` and secret `s : R`, and the
hashes `H j (t j + s)`. -/
noncomputable def crHashReal (H : Fin m → R → M) : SPComp ((Fin m → R) × (Fin m → M)) :=
  SPComp.bind (SPComp.sample (Fin m → R)) fun t =>
    SPComp.bind (SPComp.sample R) fun s => SPComp.pure (t, fun j => H j (t j + s))

/-- Correlation-robust hash, ideal game: uniform `t : Fin m → R` and uniform values. -/
noncomputable def crHashIdeal : SPComp ((Fin m → R) × (Fin m → M)) :=
  SPComp.bind (SPComp.sample (Fin m → R)) fun t =>
    SPComp.bind (SPComp.sample (Fin m → M)) fun u => SPComp.pure (t, u)

/-- Correlation-robust hash advantage of the distinguisher `D`. -/
noncomputable def CRHash_Advantage (H : Fin m → R → M)
    (D : (Fin m → R) × (Fin m → M) → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (crHashReal H) crHashIdeal D

end CRHash

end CatCrypt.Crypto.OT
