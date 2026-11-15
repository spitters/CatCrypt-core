/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.SealedSender.Anonymity
public import CatCryptCore.Crypto.Messaging.SignalStackSM

/-!
# Sealed Sender around a session of the Signal stack

A Sealed Sender envelope carries the sender certificate and the inner ciphertext of a session of
the Signal stack. This file states sender anonymity for that composition in the game form: the
server receives the recipient key, chooses two sender certificates and the associated data, the
inner ciphertext is the ciphertext of a session of the stack under a uniform session key, and the
server guesses from the envelope which certificate it carries.

The server of this game is a sender-anonymity adversary of `Signal.SealedSender.Anonymity` whose
inner ciphertext has type `Unit`: it chooses no inner ciphertext. The reduction
`overStackRed sess m₀ A` is the adversary of the anonymity game that runs the first stage of `A`,
draws the inner ciphertext from the session `sess` and passes it to the envelope, and runs the
second stage of `A` unchanged. Its advantage is the advantage of the composed game by definition.

The bound is `senderAnon_le_dhkem` at `overStackRed`. The anonymity game lets the adversary
choose the inner ciphertext, so the bound holds for every distribution of the inner ciphertext and
the session contributes no term: the strong-DH, key-schedule, INT-CTXT and IND-CPA advantages are
those of the envelope, at the reductions of `senderAnon_le_dhkem` applied to `overStackRed`. The
statement does not hide the session ciphertext from the server or bound what the server learns
from it; the session is the real view `smRealView` of `Messaging.SignalStackSM`, whose schedule
returns the ciphertext that the sender seals.

## Main definitions

* `sessCt`: the output distribution of a session from the empty heap.
* `stackSess`: the real session of the Signal stack under a uniform session key.
* `overStackRed`: the sender-anonymity adversary that seals the session ciphertext.

## Main results

* `senderAnon_overStack_le_dhkem`: the sender-anonymity advantage of the server against Sealed
  Sender with the ECIES envelope around a session of the Signal stack is at most the bound of
  `senderAnon_le_dhkem` at `overStackRed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.SealedSender.OverStack

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Messaging.SignalStackSM CatCrypt.Crypto.Signal.SealedSender.Anonymity
open CatCrypt.Crypto.KEM.Games CatCrypt.Crypto.HPKE.BaseCCA CatCrypt.Crypto.HPKE.DHKEM
open CatCrypt.Crypto.HPKE.BaseCCADHKEM
open scoped ENNReal

/-- The output distribution of the session `sess` run from the empty heap, `m₀` on failure. -/
noncomputable def sessCt {Inner : Type} (sess : SPComp Inner) (m₀ : Inner) : PMF Inner :=
  (sess Heap.empty).map fun r => match r with | some (m, _) => m | none => m₀

/-- **The real session of the Signal stack** under a uniform session key: the real view
`smRealView` of the schedule `Sch`, whose output is the ciphertext that the sender seals. -/
noncomputable def stackSess {K Sst Pub Rand Wd Ct Leak : Type} [Fintype K] [Nonempty K]
    [Fintype Rand] [Nonempty Rand] (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) Ct) (t n ΔFS ΔPCS : ℕ) :
    SPComp Ct :=
  SPComp.bind (SPComp.sample K) (smRealView M ini Sch t n ΔFS ΔPCS)

/-- **The adversary that seals the session ciphertext.** It runs the first stage of the server
`A`, which chooses two certificates, the associated data and no inner ciphertext, draws the inner
ciphertext from `sessCt sess m₀` and returns it with the choices of `A`; the second stage is that
of `A`. -/
noncomputable def overStackRed {PK C D H AD Cert Inner CT : Type} {qH qD : ℕ}
    (sess : SPComp Inner) (m₀ : Inner) (A : SenderAnonAdversary PK C D H AD Cert Unit CT qH qD) :
    SenderAnonAdversary PK C D H AD Cert Inner CT qH qD where
  St := A.St
  choose pk := (A.choose pk).bind fun x =>
    .rand (sessCt sess m₀) fun m => .ret (x.1, x.2.1, m, x.2.2.2.1, x.2.2.2.2)
  guess := A.guess
  isQueryBoundH₁ pk := OracleAdv.isQueryBoundBy_bind (b := 0) (A.isQueryBoundH₁ pk)
    fun _ _ => trivial
  isQueryBoundD₁ pk := OracleAdv.isQueryBoundBy_bind (b := 0) (A.isQueryBoundD₁ pk)
    fun _ _ => trivial
  isQueryBoundH₂ := A.isQueryBoundH₂
  isQueryBoundD₂ := A.isQueryBoundD₂

variable {Sc P K Kd AD Cert CT : Type} [Fintype Sc] [Nonempty Sc] [DecidableEq P]
  [Finite P] [Fintype K] [Nonempty K] [Fintype Kd] [Nonempty Kd] [DecidableEq AD]
  [DecidableEq CT]

/-- **Sealed Sender around a session of the Signal stack is sender-anonymous under strong
Diffie–Hellman.** For the ECIES envelope `hpkeDHKEM G sched aead`, a session `stackSess M ini Sch
t n ΔFS ΔPCS` of the stack under a uniform session key `Kₛ`, a fallback ciphertext `m₀` and every
server `A` that chooses two certificates and the associated data, the advantage of `A` against the
envelope around the session ciphertext, with `B = senderAnonReduction valid (overStackRed sess m₀
A)`, is at most the bound of `senderAnon_le_dhkem` at `B`. The session contributes no term. -/
theorem senderAnon_overStack_le_dhkem {Kₛ Sst Pub Rand Wd Ct Leak : Type} [Fintype Kₛ]
    [Nonempty Kₛ] [Fintype Rand] [Nonempty Rand] (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : Kₛ → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) Ct) (t n ΔFS ΔPCS : ℕ)
    (m₀ : Ct) (G : DHGroup Sc P) (sched : K → Kd) (aead : OTAEAD Kd AD (Cert × Ct) CT)
    (valid : Cert × Ct → Bool) {qH qD : ℕ}
    (A : SenderAnonAdversary P P (KDFDom P) K AD Cert Unit CT qH qD) :
    let B := senderAnonReduction valid (overStackRed (stackSess M ini Sch t n ΔFS ΔPCS) m₀ A)
    senderAnonAdvantage (hpkeDHKEM G sched aead) valid
        (overStackRed (stackSess M ini Sch t n ΔFS ΔPCS) m₀ A) ≤
      stdhAdvantage G (dhkemReduction (kemReduction (hpkeDHKEM G sched aead) B true)) +
        schedAdvantage sched (schedReduction (hpkeDHKEM G sched aead) B true) +
        otctxtAdvantage aead (ctxtReduction (hpkeDHKEM G sched aead) B true) +
        otcpaAdvantage aead (cpaReduction (hpkeDHKEM G sched aead) B) +
        otctxtAdvantage aead (ctxtReduction (hpkeDHKEM G sched aead) B false) +
        schedAdvantage sched (schedReduction (hpkeDHKEM G sched aead) B false) +
        stdhAdvantage G (dhkemReduction (kemReduction (hpkeDHKEM G sched aead) B false)) :=
  have := Fintype.ofFinite P
  senderAnon_le_dhkem G sched aead valid _

end CatCrypt.Crypto.Signal.SealedSender.OverStack
