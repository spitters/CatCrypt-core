/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Event signatures

An event signature `EventSig` describes the adversary interface of an interaction tree:
a type of events and, for each event, a type of responses. It is the record form of a
polynomial functor `PFunctor.{0, 0}`; `sigPF` gives the container `⟨E.Event, E.Resp⟩`, and
`emptyEvSig` is the signature without events.
-/

@[expose] public section

set_option autoImplicit false

namespace UCMonad.ITreeNUC

/-- An event signature describes the adversary interface. -/
structure EventSig where
  /-- The events the adversary can be asked. -/
  Event : Type
  /-- The responses to an event. -/
  Resp : Event → Type

/-- The empty event signature: no adversary interaction. -/
@[implicit_reducible]
def emptyEvSig : EventSig where
  Event := Empty
  Resp := Empty.elim

/-- The container of an event signature: shapes are events, positions at an event are its
responses. -/
abbrev sigPF (E : EventSig) : PFunctor.{0, 0} := ⟨E.Event, E.Resp⟩

end UCMonad.ITreeNUC
