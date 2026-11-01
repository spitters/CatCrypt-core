/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.PartyDerive
public import CatCryptCore.Crypto.Party.Protocols.PQXDH

/-!
# Tests of `party_derive`

The statements of the hand-written sampling, port-typing and time-bound lemmas of the PQXDH
simulator program (`CatCryptCore.Crypto.Party.Protocols.PQXDH`) and of the X3DH simulator program
(`CatCryptCore.Crypto.Party.Call`, `Derived`, `Timed`), each proved by `party_derive`.

Search words: party language, derivation tactic, port typing, time bound, tests.
-/

set_option autoImplicit false

/-! ## Tests on PQXDH -/

namespace CatCrypt.Crypto.Party.Protocols.PQXDH

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent.FAKE CatCrypt.Crypto.AKE.PQXDHSquare
open CatCrypt.Crypto.AKE.X3DHSquare (RSt ltStep roStep aliceInp bobInp opkOf ephPubOf Named FEv
  FOut subView)
open CatCrypt.Crypto.PAKE.DHExtract Prog

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [Countable PK] [Countable SK] [Countable SS]
  [Countable C] (O : KemOps PK SK SS C) (G : DHGroup S W)

/-! ### Sampling structure -/

example {E O : Type} (s : RSt S W K) (pid : PartyId) :
    Samples (ltP s pid : Prog E O _) (ltStep s pid) := by
  party_derive

example {E O D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    Samples (roP tb x : Prog E O _) (roStep tb x) := by
  party_derive

example (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS)) (x : Inst) (r : Rec K)
    (ip : PInp W SS) : Samples (deliverP s inp x r ip) (deliver s inp x r ip) := by
  party_derive

example (s : SimSt S W K PK SK SS C) (x : Inst) :
    Samples (simCompleteP O G s x) (simComplete O G s x) := by
  party_derive

example (s : SimSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) :
    Samples (simSendP O G s x e c) (simSend O G s x e c) := by
  party_derive

example (s : SimSt S W K PK SK SS C) (pid : PartyId) :
    Samples (simCorruptP s pid : P S W K PK SS C _) (simCorrupt s pid) := by
  party_derive

example (s : SimSt S W K PK SK SS C) (e : OEv W SS C) :
    Samples (simStartP O G s e) (simStart O G s e) := by
  party_derive

/-! ### Port typing and information flow -/

example {E O : Type} (s : RSt S W K) (pid : PartyId) : NoIO (ltP s pid : Prog E O _) := by
  party_derive

example {E O D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    NoIO (roP tb x : Prog E O _) := by
  party_derive

example (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS)) (x : Inst) (r : Rec K)
    (ip : PInp W SS) : NoIO (deliverP s inp x r ip) := by
  party_derive

example (s : SimSt S W K PK SK SS C) (x : Inst) : NoIO (simCompleteP O G s x) := by
  party_derive

example (s : SimSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) :
    NoIO (simSendP O G s x e c) := by
  party_derive

example (s : SimSt S W K PK SK SS C) (pid : PartyId) :
    NoIO (simCorruptP s pid : P S W K PK SS C _) := by
  party_derive

example (s : SimSt S W K PK SK SS C) (e : OEv W SS C) : NoIO (simStartP O G s e) := by
  party_derive

example (s : SimSt S W K PK SK SS C) (e : OEv W SS C) :
    ProgE.ViewRel (PubView.callView outerView subView) Eq (simStartP O G s e)
      (simStartP O G s e) := by
  party_derive

/-! ### Time bounds -/

example {E O : Type} (s : RSt S W K) (pid : PartyId) :
    ProgE.Bound (fun _ => 1) (ltP s pid : Prog E O _) 1 (fun _ => True) := by
  party_derive

example {E O D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    ProgE.Bound (fun _ => 1) (roP tb x : Prog E O _) 1
      (fun r => r.2.length ≤ tb.length + 1) := by
  party_derive

example (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS)) (x : Inst) (r : Rec K)
    (ip : PInp W SS) :
    ProgE.Bound (fun _ => 1) (deliverP s inp x r ip) 1
      (fun q => q.1.1.ro.length ≤ s.ro.length + 1) := by
  party_derive [pKeyed]

example (s : SimSt S W K PK SK SS C) (x : Inst) :
    ProgE.Bound (fun _ => 1) (simCompleteP O G s x) 4
      (fun q => q.1.1.ro.length ≤ s.1.ro.length + 1) := by
  party_derive [pKeyed]

example (s : SimSt S W K PK SK SS C) (x : Inst) (e : W) (c : C) :
    ProgE.Bound (fun _ => 1) (simSendP O G s x e c) 3
      (fun q => q.1.1.ro.length ≤ s.1.ro.length + 1) := by
  party_derive [pKeyed]

example (s : SimSt S W K PK SK SS C) (e : OEv W SS C) :
    ProgE.Bound (fun _ => 1) (simStartP O G s e) 4
      (fun q => q.1.1.ro.length ≤ s.1.ro.length + 1) := by
  party_derive [pKeyed]

example (s : SimSt S W K PK SK SS C) (e : OEv W SS C) :
    ProgE.Bound (fun _ => 1) (simStartP O G s e) 4
      (fun q => q.1.1.ro.length ≤ s.1.ro.length + 1) := by
  party_derive! [pKeyed]

example (q : SimSt S W K PK SK SS C × Dec S W K PK C) :
    ProgE.Bound (fun _ => 1) (simDecide q) 3 (fun s => s.1.ro = q.1.1.ro) := by
  party_derive

example (s : SimSt S W K PK SK SS C) :
    ProgE.Bound (fun _ => 1) (simBody O G s) 8
      (fun s' => s'.1.ro.length ≤ s.1.ro.length + 1) := by
  party_derive [pKeyed]

example (s : SimSt S W K PK SK SS C) :
    ∃ t, ProgE.Bound (fun _ => 1) (simBody O G s) t
      (fun s' => s'.1.ro.length ≤ s.1.ro.length + 1) := by
  party_derive [pKeyed]

end CatCrypt.Crypto.Party.Protocols.PQXDH

/-! ## Tests on X3DH -/

namespace CatCrypt.Crypto.Party.X3DHProg

open CatCrypt.Core CatCrypt.Crypto.UCTransparent
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract Prog

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

example (s : SimSt S W K) (x : Inst) : Samples (simCompleteP G s x) (simComplete G s x) := by
  party_derive

example (s : SimSt S W K) (x : Inst) (e : W) : Samples (simSendP G s x e) (simSend G s x e) := by
  party_derive

example (s : SimSt S W K) (e : OEv W) : Samples (simStartP G s e) (simStart G s e) := by
  party_derive

example (s : SimSt S W K) (x : Inst) : NoIO (simCompleteP G s x) := by
  party_derive

example (s : SimSt S W K) (e : OEv W) : NoIO (simStartP G s e) := by
  party_derive

example (s : SimSt S W K) (x : Inst) :
    ProgE.Bound (fun _ => 1) (simCompleteP G s x) 3
      (fun q => q.1.1.ro.length ≤ s.1.ro.length + 1) := by
  party_derive [keyed]

example (s : SimSt S W K) (e : OEv W) :
    ProgE.Bound (fun _ => 1) (simStartP G s e) 3
      (fun q => q.1.1.ro.length ≤ s.1.ro.length + 1) := by
  party_derive [keyed]

example (s : SimSt S W K) :
    ProgE.Bound (fun _ => 1) (simBody G s) 7 (fun s' => s'.1.ro.length ≤ s.1.ro.length + 1) := by
  party_derive [keyed]

end CatCrypt.Crypto.Party.X3DHProg
