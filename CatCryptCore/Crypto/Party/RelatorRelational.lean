/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Relator
public import CatCryptCore.Crypto.Party.Relational

/-!
# The relator and the relational judgment of party programs

The relation lifting `ProgE.relL V couplingQ RA` of party programs, at the relation
`ProgE.couplingQ` of exact couplings of samples at equal heaps, and the inductive relational
judgment `Prog.RelTriple V RA` relate the same pairs of programs
(`Prog.relTriple_iff_relProg`). The relator is the fixed point of a lifting over the program tree
and the relational judgment is the least relation closed under its rules; both read the same
clause at each node, so both directions go by induction on the left program tree.

Consequently the soundness results of either side (the coupling bisimulation of the denotations,
the bisimulation rule, emulation) apply to the programs related by the other.

Search words: relation lifting, relator, relational judgment, relational triple, coupling,
bisimulation, party language.

## Main results

* `Prog.relTriple_iff_relProg`: the relational judgment is the relator at exact couplings.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Relational CatCrypt.Crypto.UCTransparent

namespace Prog

variable {E O α β : Type}

/-- The relational judgment implies the relator at exact couplings of samples. -/
theorem RelTriple.relProg {V : PubView E O} {RA : α → β → Prop} {p : Prog E O α}
    {p' : Prog E O β} (h : RelTriple V RA p p') : ProgE.RelProg V ProgE.couplingQ RA p p' := by
  induction h with
  | ret h => exact ⟨_, rfl, h⟩
  | recv _ ih => exact ⟨_, rfl, ih⟩
  | send ho _ ih => exact ⟨_, _, rfl, Or.inr ⟨ho, ih⟩⟩
  | sample Φ hμ _ ih => exact ⟨_, _, Φ, rfl, hμ, ih⟩
  | fail => rfl

/-- The relator at exact couplings of samples implies the relational judgment. -/
theorem RelTriple.of_relProg {V : PubView E O} {RA : α → β → Prop} :
    ∀ {p : Prog E O α} {p' : Prog E O β}, ProgE.RelProg V ProgE.couplingQ RA p p' →
      RelTriple V RA p p'
  | .ret _, _, h => by
    obtain ⟨_, rfl, h⟩ := h
    exact RelTriple.ret h
  | .recv _, _, h => by
    obtain ⟨_, rfl, h⟩ := h
    exact RelTriple.recv fun e e' he => RelTriple.of_relProg (h e e' he)
  | .send _ _, _, h => by
    obtain ⟨_, _, rfl, h⟩ := h
    obtain ⟨ho, h⟩ := h.resolve_left id
    exact RelTriple.send ho (RelTriple.of_relProg h)
  | .opN _ _, _, h => by
    obtain ⟨_, _, Φ, rfl, hμ, h⟩ := h
    exact RelTriple.sample Φ hμ fun n n' hn => RelTriple.of_relProg (h n n' hn)
  | .fail, _, h => by
    subst h
    exact RelTriple.fail

/-- **The relational judgment is the relation lifting at exact couplings.** Two party programs
are related by the relational triple `RelTriple V RA` exactly when they are related by the
relator `ProgE.relL V couplingQ RA`, whose operation clause couples the samples exactly at equal
heaps. -/
theorem relTriple_iff_relProg {V : PubView E O} {RA : α → β → Prop} {p : Prog E O α}
    {p' : Prog E O β} : RelTriple V RA p p' ↔ ProgE.RelProg V ProgE.couplingQ RA p p' :=
  ⟨RelTriple.relProg, RelTriple.of_relProg⟩

end Prog

end CatCrypt.Crypto.Party
