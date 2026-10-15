/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UC
public import CatCryptCore.Crypto.ForkingLemma

/-!
# Dummy-adversary completeness and simulator uniformity

This file proves two facts about the `sdist`-graded emulation predicate
`CatCrypt.Crypto.UCEmulates` (`UC.lean`): emulation against the dummy adversary implies
emulation against every adversary and every view, and emulation with a per-adversary
simulator is equivalent to emulation with one uniform simulator construction. Both rest on
`sdist_dummy_absorb`: the simulator against `A` is `fun s => (S s).bind A`, the dummy
simulator post-composed with `A`, and `A` is absorbed into the distinguisher by
`sdist_comp_right`.

`UCEmulates ε ⟨hon, out, leak, sim_if, view⟩ π F` unfolds to
`∀ A : leak → SPComp view, ∃ S : sim_if → SPComp view,`
`  sdist (fun a => (π a).bind (mapSum pure A)) (fun a => (F a).bind (mapSum pure S)) ≤ ε`.
The dummy adversary `SPComp.pure : leak → SPComp leak` relays each leak message unchanged;
since `mapSum pure pure = pure`, the real world against it is `π`.

## Main definitions

* `EmulatesDummy ε π F` — emulation against the dummy adversary:
  `∃ S : sim_if → SPComp leak, sdist π (fun a => (F a).bind (mapSum pure S)) ≤ ε`
* `GeneralUCEmulates ε π F` — one uniform simulator construction
  `Sim : (leak → SPComp view) → (sim_if → SPComp view)` that works against every `A`

## Main results

* `emulatesDummy_of_ucEmulates` — emulation implies emulation against the dummy adversary
* `dummy_completeness`, `ucEmulates_iff_dummy` — emulation against the dummy adversary
  implies emulation against every adversary and every view
* `ucEmulates_of_general` — a uniform simulator construction gives per-adversary simulators
* `general_of_dummy` — the dummy simulator yields a uniform construction
* `specialized_iff_general` — the per-adversary and uniform forms are equivalent
* `sdist_dummy_absorb` — absorption of the adversary into the distinguisher

## Examples

`Example.emulatesDummy_perfect` is a perfect (`ε = 0`) dummy emulation whose simulator is not
the identity relay; `Example.identity_sim_fails` proves `1 ≤ sdist π F`, so the identity
simulator does not achieve it.

Relation to the literature: `CatCryptCore/Crypto/Complexity.md`.

## References

* Canetti, IACR ePrint 2000/067, version of 2020-02-11 — completeness of the dummy adversary
  (§4.3.1, Claim 11); per-adversary and black-box simulators (§4.3.2, Claim 13)
-/

@[expose] public section

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob

open scoped ENNReal

/-! ## Emulation against the dummy adversary -/

/-- Emulation against the **dummy adversary** `SPComp.pure` (the relay).

    Since `mapSum pure pure = pure` and `bind c pure = c`, the post-adversary real
    world is just `π`, so this is `UCEmulates` specialized to `A = pure`, `view = leak`. -/
def EmulatesDummy {hon out leak sim_if : Type} (ε : ℝ≥0∞)
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if)) : Prop :=
  ∃ S : sim_if → SPComp leak,
    sdist π (fun a => SPComp.bind (F a) (mapSum SPComp.pure S)) ≤ ε

/-- One uniform simulator construction defeating every adversary.

    `GeneralUCEmulates` differs from `UCEmulates` by pulling the simulator out of the
    `∀ A` quantifier: a single `Sim : (leak → SPComp view) → (sim_if → SPComp view)`
    works for all `A`. -/
def GeneralUCEmulates {hon out leak sim_if view : Type} (ε : ℝ≥0∞)
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if)) : Prop :=
  ∃ Sim : (leak → SPComp view) → (sim_if → SPComp view),
    ∀ A : leak → SPComp view,
      sdist (fun a => SPComp.bind (π a) (mapSum SPComp.pure A))
            (fun a => SPComp.bind (F a) (mapSum SPComp.pure (Sim A))) ≤ ε

/-! ## Absorption core -/

/-- The simulator-composition identity underlying absorption.

    Post-composing the leak channel with `A` and then routing through `mapSum` equals
    routing through `mapSum pure S` first and post-processing the whole `(out ⊕ leak)`
    channel with `mapSum pure A`. -/
theorem mapSum_pure_comp_absorb {out leak sim_if view : Type}
    (S : sim_if → SPComp leak) (A : leak → SPComp view) :
    (mapSum (SPComp.pure (α := out)) (fun s => SPComp.bind (S s) A))
      = (fun x => SPComp.bind (mapSum SPComp.pure S x) (mapSum SPComp.pure A)) := by
  funext x
  cases x with
  | inl o => simp [mapSum, SPComp.map, SPComp.pure_bind]
  | inr s => simp [mapSum, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- **Absorption.** If the dummy simulator `S` puts `π` within `ε` of the ideal world,
    then for any adversary `A` the composed simulator `fun s => (S s).bind A` keeps the
    real world (post-`A`) within `ε` of the ideal world (post-composed simulator). -/
theorem sdist_dummy_absorb {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if))
    (S : sim_if → SPComp leak) (A : leak → SPComp view)
    (hS : sdist π (fun a => SPComp.bind (F a) (mapSum SPComp.pure S)) ≤ ε) :
    sdist (fun a => SPComp.bind (π a) (mapSum SPComp.pure A))
          (fun a => SPComp.bind (F a)
            (mapSum SPComp.pure (fun s => SPComp.bind (S s) A))) ≤ ε := by
  have key :
      (fun a => SPComp.bind (F a)
        (mapSum SPComp.pure (fun s => SPComp.bind (S s) A)))
        = (fun a => SPComp.bind
            ((fun a => SPComp.bind (F a) (mapSum SPComp.pure S)) a)
            (mapSum SPComp.pure A)) := by
    funext a
    rw [mapSum_pure_comp_absorb S A, ← SPComp.bind_assoc]
  rw [key]
  exact le_trans
    (sdist_comp_right π (fun a => SPComp.bind (F a) (mapSum SPComp.pure S))
      (mapSum SPComp.pure A)) hS

/-! ## Theorem 1 — dummy-adversary completeness -/

/-- (⟹, trivial) The dummy form is the general form at the dummy adversary.

    Instantiating `UCEmulates` at `A = SPComp.pure` (`view = leak`) and collapsing
    `mapSum pure pure = pure`, `bind c pure = c` recovers `EmulatesDummy`. -/
theorem emulatesDummy_of_ucEmulates {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if))
    (h : UCEmulates ε ⟨hon, out, leak, sim_if, leak⟩ π F) :
    EmulatesDummy ε π F := by
  obtain ⟨S, hS⟩ := h SPComp.pure
  refine ⟨S, ?_⟩
  have hπ : (fun a => SPComp.bind (π a) (mapSum SPComp.pure SPComp.pure)) = π := by
    funext a; simp [mapSum_pure_pure, SPComp.bind_pure]
  rwa [hπ] at hS

/-- **Theorem 1 (dummy-adversary completeness).**

    Emulation against the dummy adversary implies emulation against **every** adversary
    and **every** environment view. The simulator against `A` is the dummy simulator
    post-composed with `A`; `A` is absorbed into the distinguisher.

    (composition plumbing) -/
theorem dummy_completeness {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if))
    (h : EmulatesDummy ε π F) :
    ∀ view : Type, UCEmulates ε ⟨hon, out, leak, sim_if, view⟩ π F := by
  obtain ⟨S, hS⟩ := h
  intro view A
  exact ⟨fun s => SPComp.bind (S s) A, sdist_dummy_absorb π F S A hS⟩

/-- Dummy-adversary completeness, packaged as an equivalence over all views. -/
theorem ucEmulates_iff_dummy {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if)) :
    (∀ view : Type, UCEmulates ε ⟨hon, out, leak, sim_if, view⟩ π F)
      ↔ EmulatesDummy ε π F :=
  ⟨fun h => emulatesDummy_of_ucEmulates π F (h leak), dummy_completeness π F⟩

/-! ## Theorem 2 — per-adversary vs uniform simulator -/

/-- (⟹, trivial) A uniform simulator construction yields the per-adversary form. -/
theorem ucEmulates_of_general {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if))
    (h : GeneralUCEmulates (view := view) ε π F) :
    UCEmulates ε ⟨hon, out, leak, sim_if, view⟩ π F := by
  obtain ⟨Sim, hSim⟩ := h
  intro A
  exact ⟨Sim A, hSim A⟩

/-- The dummy simulator is itself a *uniform* construction: `Sim A = fun s => (S s).bind A`.
    Built from Theorem 1's absorption. -/
theorem general_of_dummy {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if))
    (h : EmulatesDummy ε π F) :
    ∀ view : Type, GeneralUCEmulates (view := view) ε π F := by
  obtain ⟨S, hS⟩ := h
  intro view
  exact ⟨fun A s => SPComp.bind (S s) A, fun A => sdist_dummy_absorb π F S A hS⟩

/-- **Theorem 2 (per-adversary ⇔ uniform simulator).**

    The per-adversary simulator form and the uniform simulator-construction form are
    equivalent (quantifying over the environment view); cf. Canetti's black-box simulation,
    ePrint 2000/067, §4.3.2, Claim 13. The theorem name keeps the words "specialized" and
    "general"; Canetti's "specialized simulators" (§4.3.3) are a different notion, where
    the simulator may depend on the environment.
    The nontrivial ⟹ goes through the dummy simulator (Theorem 1); ⟸ is immediate. -/
theorem specialized_iff_general {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if)) :
    (∀ view : Type, UCEmulates ε ⟨hon, out, leak, sim_if, view⟩ π F)
      ↔ (∀ view : Type, GeneralUCEmulates (view := view) ε π F) := by
  constructor
  · intro h view
    exact general_of_dummy π F (emulatesDummy_of_ucEmulates π F (h leak)) view
  · simp_all [ucEmulates_of_general]

/-! ## Non-vacuity -/

namespace Example

/-- Real protocol: leaks the constant `true` on the adversary channel. -/
noncomputable def π : Unit → SPComp (Unit ⊕ Bool) := fun _ => SPComp.pure (.inr true)

/-- Ideal functionality: leaks the constant `false` on the simulator channel. -/
noncomputable def F : Unit → SPComp (Unit ⊕ Bool) := fun _ => SPComp.pure (.inr false)

/-- The dummy simulator: rewrites the ideal leak `false` to the real leak `true`.
    This is **not** the identity relay `SPComp.pure`. -/
noncomputable def Sdummy : Bool → SPComp Bool := fun _ => SPComp.pure true

/-- Perfect dummy emulation: with the transforming simulator `Sdummy`, the ideal world's
    leak channel is driven to `true`, matching `π` exactly. -/
theorem emulatesDummy_perfect : EmulatesDummy (0 : ℝ≥0∞) π F := by
  refine ⟨Sdummy, ?_⟩
  have : (fun a => SPComp.bind (F a) (mapSum SPComp.pure Sdummy)) = π := by
    funext a
    simp [F, π, Sdummy, mapSum, SPComp.map, SPComp.pure_bind]
  rw [this]; simp

/-- By Theorem 1, the perfect emulation holds against every adversary and view. -/
theorem perfect_all_adversaries :
    ∀ view : Type, UCEmulates (0 : ℝ≥0∞) ⟨Unit, Unit, Bool, Bool, view⟩ π F :=
  fun view => dummy_completeness π F emulatesDummy_perfect view

/-- By Theorem 2, a single uniform simulator construction defeats every adversary. -/
theorem perfect_general :
    ∀ view : Type, GeneralUCEmulates (view := view) (0 : ℝ≥0∞) π F :=
  fun view => general_of_dummy π F emulatesDummy_perfect view

/-- **It matters that the dummy simulator is not the identity.** The identity relay
    `SPComp.pure` would require `sdist π F ≤ 0`, but the distinguisher that reads the
    leaked bit separates `true` from `false`: `1 ≤ sdist π F`. Hence `UCEmulates_of_sdist`
    (which needs `S = A`) cannot prove this example — the absorption argument is essential. -/
theorem identity_sim_fails : (1 : ℝ≥0∞) ≤ sdist π F := by
  -- distinguisher reads the leaked Bool off the `.inr` channel
  set D : (Unit ⊕ Bool) → SPComp Bool :=
    fun x => match x with | .inl _ => SPComp.pure false | .inr b => SPComp.pure b with hD
  have hb : absDiff (prTrue (SPComp.bind (π ()) D) Heap.empty)
                    (prTrue (SPComp.bind (F ()) D) Heap.empty) = 1 := by
    have h1 : SPComp.bind (π ()) D = SPComp.pure true := by
      simp [π, hD, SPComp.pure_bind]
    have h2 : SPComp.bind (F ()) D = SPComp.pure false := by
      simp [F, hD, SPComp.pure_bind]
    simp [h1, h2, ForkingLemma.prTrue_pure_bool, absDiff]
  calc (1 : ℝ≥0∞) = absDiff (prTrue (SPComp.bind (π ()) D) Heap.empty)
                    (prTrue (SPComp.bind (F ()) D) Heap.empty) := hb.symm
    _ ≤ sdist π F := le_iSup₂_of_le D () (le_iSup_of_le Heap.empty le_rfl)

end Example

end CatCrypt.Crypto
