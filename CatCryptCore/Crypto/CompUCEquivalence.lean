/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLevels
public import CatCryptCore.Crypto.DummyAdversary
public import CatCryptCore.Crypto.UCAdmClass.SPCompInstance

/-!
# Computational dummy-adversary and constructive-cryptography equivalences

This file defines UC emulation over the computational distance `ucCdist` (`UCAdmClass.lean`)
quantified over admissible adversaries, proves the dummy-adversary theorem for it, and proves
it equivalent to a construction over `ucCdist` in the sense of Maurer (the security condition,
without the availability condition) for single-shot systems: the honest interfaces are merged
into one input, the adversary interface receives one leak and sends nothing, and the converter
post-processes that leak. The results are generic over `[UCMonadCompDist T]`;
`QueryBoundedUC.lean` and `SizeBoundedUC.lean` instantiate them on `SPComp`.

The absorption step uses `UCMonad.ucCdist_comp_right`, which absorbs an arrow `k` into the
distinguisher under the hypothesis `adm k`. Absorbing the adversary `A` needs
`adm (ucMapSum pure A)`, obtained from `adm A` by `adm_mapSum adm_pure`; the adversary
quantifier of `UCEmulatesCdist` therefore ranges over admissible arrows.

| Predicate | Metric | Adversary `A` | Simulator `S` |
|-----------|--------|---------------|----------------|
| `UCEmulatesL2` | `ucCdist` | ∀ | ∃ |
| `UCEmulatesCdist` | `ucCdist` | ∀ admissible | ∃ |
| `UCEmulatesL3` | `ucCdist` | ∀ | ∃ admissible |

## Main definitions

* `UCEmulatesCdist ε π F` — emulation over `ucCdist` against admissible adversaries
* `EmulatesDummyCdist ε π F` — emulation over `ucCdist` against the dummy adversary
* `CCConstructsCdist ε π F` — construction over `ucCdist` (Maurer, TOSCA 2011, Def. 3);
  definitionally `EmulatesDummyCdist`

## Main results

* `ucCdist_dummy_absorb` — absorption of an admissible adversary into the distinguisher
* `dummy_completeness_cdist`, `ucEmulatesCdist_iff_dummy` — the dummy-adversary theorem
  over `ucCdist`
* `ccConstructsCdist_iff_ucEmulatesCdist` — construction over `ucCdist` is equivalent to
  `UCEmulatesCdist`
* `ucEmulatesCdist_of_ucEmulates` — statistical emulation implies `UCEmulatesCdist`
* `ucEmulatesCdist_of_ucEmulatesL2` — level 2 emulation implies `UCEmulatesCdist`
* `adm_dummy_adversary` — the dummy adversary is admissible in every instance

## Examples

Over the `UCMonadCompDist SPComp` instance, `ccConstructsCdist_perfect_witness` is a perfect
(`ε = 0`) construction whose converter is not the identity relay, and
`ccConstructsCdist_identity_converter_fails` proves `1 ≤ ucCdist π F` for the identity
converter.

Relation to the literature: `CatCryptCore/Crypto/Complexity.md`.

## References

* Maurer, "Constructive Cryptography — A New Paradigm for Security Definitions and Proofs",
  TOSCA 2011, Def. 3
* Küsters, Datta, Mitchell, Ramanathan, "On the Relationships between Notions of
  Simulation-Based Security", J. Cryptology 21(4), 2008, Def. 6, Thm. 16
* Maurer, Renner, "Abstract Cryptography", ICS 2011, App. C.1
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.CompUCEquivalence

open UCMonad
open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

variable {T : Type → Type} [UCMonadCompDist T]

/-! ## Section 1: Computational-distance emulation predicates -/

/-- **Computational-distance UC emulation.** For every **admissible** adversary `A`
    there is a simulator `S` keeping the post-adversary real and ideal views within `ε`
    in the admissible-distinguisher distance `ucCdist`.

    The `adm A` hypothesis (absent in `UCEmulatesL2`) is what enables the dummy-adversary
    transport: absorbing `A` into the distinguisher needs `adm (ucMapSum pure A)`. -/
def UCEmulatesCdist (ε : ℝ≥0∞) {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if)) : Prop :=
  ∀ (A : leak → T view), adm A → ∃ (S : sim_if → T view),
    ucCdist (fun a => π a >>= UCMonadBase.ucMapSum pure A)
            (fun a => F a >>= UCMonadBase.ucMapSum pure S) ≤ ε

/-- **Computational emulation against the dummy adversary.** No adversary quantifier: the
    dummy adversary is the relay `pure`, so the post-adversary real world collapses to `π`
    itself and only the simulator `S` remains. -/
def EmulatesDummyCdist (ε : ℝ≥0∞) {hon out leak sim_if : Type}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if)) : Prop :=
  ∃ (S : sim_if → T leak),
    ucCdist π (fun a => F a >>= UCMonadBase.ucMapSum pure S) ≤ ε

/-- **Construction (Maurer, TOSCA 2011, Def. 3, security condition) over computational
    distance.** The converter `σ` turns
    `F`'s interface into `π`'s, keeping them within `ε` in `ucCdist`, with no adversary
    quantifier. Definitionally `EmulatesDummyCdist`. -/
def CCConstructsCdist (ε : ℝ≥0∞) {hon out leak sim_if : Type}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if)) : Prop :=
  ∃ (σ : sim_if → T leak),
    ucCdist π (fun a => F a >>= UCMonadBase.ucMapSum pure σ) ≤ ε

/-- The computational CC construction predicate is, on the nose, computational emulation
    against the dummy adversary. -/
theorem ccConstructsCdist_iff_emulatesDummy {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if)) :
    CCConstructsCdist ε π F ↔ EmulatesDummyCdist ε π F := Iff.rfl

/-! ## Section 2: The computational absorption core -/

/-- **Computational absorption (post-composition non-expansiveness).** If the dummy converter `S` puts `π` within
    `ε` of the ideal world in `ucCdist`, then for any **admissible** adversary `A` the
    composed simulator `fun s => S s >>= A` keeps the post-`A` real world within `ε` of the
    ideal world (post-composed simulator).

    The `adm A` hypothesis is discharged into the `adm k` obligation of
    `ucCdist_comp_right` as `adm_mapSum adm_pure hA : adm (ucMapSum pure A)`. -/
theorem ucCdist_dummy_absorb {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if))
    (S : sim_if → T leak) (A : leak → T view) (hA : adm A)
    (hS : ucCdist π (fun a => F a >>= UCMonadBase.ucMapSum pure S) ≤ ε) :
    ucCdist (fun a => π a >>= UCMonadBase.ucMapSum pure A)
            (fun a => F a >>= UCMonadBase.ucMapSum pure (fun s => S s >>= A)) ≤ ε := by
  have key :
      (fun a => F a >>= UCMonadBase.ucMapSum pure (fun s => S s >>= A))
        = (fun a => (F a >>= UCMonadBase.ucMapSum pure S)
            >>= UCMonadBase.ucMapSum pure A) := by
    funext a
    rw [bind_assoc, UCMonadBase.ucMapSum_pure_kleisli]
  rw [key]
  exact le_trans
    (ucCdist_comp_right π (fun a => F a >>= UCMonadBase.ucMapSum pure S)
      (UCMonadBase.ucMapSum pure A) (adm_mapSum adm_pure hA)) hS

/-! ## Section 3: The computational dummy-adversary theorem -/

/-- **Computational dummy-adversary completeness.** Emulation against the dummy adversary
    implies emulation against **every admissible** adversary and **every** environment
    view. The simulator against `A` is the dummy converter post-composed with `A`; `A` is
    absorbed into the distinguisher via `ucCdist_dummy_absorb` (post-composition non-expansiveness, `adm A`). -/
theorem dummy_completeness_cdist {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if))
    (h : EmulatesDummyCdist ε π F) :
    ∀ view : Type, UCEmulatesCdist (T := T) (view := view) ε π F := by
  obtain ⟨S, hS⟩ := h
  intro view A hA
  exact ⟨fun s => S s >>= A, ucCdist_dummy_absorb π F S A hA hS⟩

/-- (⟸, immediate) The dummy adversary `pure` is one admissible adversary (`adm_pure`), so
    computational emulation against all admissible adversaries specializes to the dummy
    form: `ucMapSum pure pure = pure` and `π a >>= pure = π a` collapse the real world. -/
theorem emulatesDummyCdist_of_ucEmulatesCdist {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if))
    (h : UCEmulatesCdist (T := T) (view := leak) ε π F) :
    EmulatesDummyCdist ε π F := by
  obtain ⟨S, hS⟩ := h pure adm_pure
  refine ⟨S, ?_⟩
  have hπ : (fun a => π a >>= UCMonadBase.ucMapSum (T := T) pure pure) = π := by
    funext a; simp [UCMonadBase.ucMapSum_pure_pure]
  rwa [hπ] at hS

/-- **Computational dummy-adversary theorem**, packaged as an equivalence over all views.
    The nontrivial ⟹ is the absorption argument; ⟸ picks the dummy adversary `pure`. -/
theorem ucEmulatesCdist_iff_dummy {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if)) :
    (∀ view : Type, UCEmulatesCdist (T := T) (view := view) ε π F)
      ↔ EmulatesDummyCdist ε π F :=
  ⟨fun h => emulatesDummyCdist_of_ucEmulatesCdist π F (h leak),
   dummy_completeness_cdist π F⟩

/-! ## Section 4: The computational Constructive-Cryptography equivalence -/

/-- **Computational CC ⟺ dummy-adversary UC.** A construction (Maurer, TOSCA 2011, Def. 3)
    within `ε` in the admissible-distinguisher distance is exactly computational UC emulation
    within `ε` against **every admissible** adversary and **every** environment view. The bridge is the
    computational dummy-adversary theorem `ucEmulatesCdist_iff_dummy`.

    (composition plumbing) -/
theorem ccConstructsCdist_iff_ucEmulatesCdist {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if)) :
    CCConstructsCdist ε π F ↔
      ∀ view : Type, UCEmulatesCdist (T := T) (view := view) ε π F :=
  (ccConstructsCdist_iff_emulatesDummy π F).trans (ucEmulatesCdist_iff_dummy π F).symm

/-! ## Section 5: Statistical ⟹ computational (the easy direction) -/

/-- The dummy adversary `pure` is admissible in every instance: `UCEmulatesCdist`'s
    obligation is never vacuous, ruling out an empty `adm` class. -/
theorem adm_dummy_adversary {leak : Type} : adm (pure : leak → T leak) := adm_pure

/-- Statistical emulation implies computational emulation: `ucCdist ≤ ucSdist`. Needs no
    admissibility on `A` — the statistical simulator is reused verbatim. This is the note
    that the strict content is the *converse* transport, gated on admissibility. -/
theorem ucEmulatesCdist_of_ucEmulates {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if))
    (h : UCMonad.UCEmulates (T := T) (view := view) ε π F) :
    UCEmulatesCdist (T := T) (view := view) ε π F := by
  intro A _hA
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, le_trans (ucCdist_le_ucSdist _ _) hS⟩

/-- Level-2 emulation (over all adversaries) implies the admissible-adversary form: drop
    the quantifier to admissible `A`. -/
theorem ucEmulatesCdist_of_ucEmulatesL2 {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if))
    (h : UCEmulatesL2 (T := T) (view := view) ε π F) :
    UCEmulatesCdist (T := T) (view := view) ε π F :=
  fun A _hA => h A

/-! ## Section 6: Non-vacuity over the concrete `SPComp` instance

The `UCMonadCompDist SPComp` instance uses trivial admissibility (`adm = fun _ => True`),
so `ucCdist = ucSdist` there. Reusing the concrete perfect example of `DummyAdversary.lean`
(the converter rewrites the ideal leak `false` to the real leak `true`), the computational
construction is witnessed by a **non-identity** converter, and the identity converter
provably fails. -/

open CatCrypt.Crypto in
/-- A concrete perfect (`ε = 0`) computational CC construction whose converter is **not**
    the identity relay. Reuses `Example.emulatesDummy_perfect` through `ucCdist ≤ ucSdist`. -/
theorem ccConstructsCdist_perfect_witness :
    CCConstructsCdist (T := SPComp) 0 Example.π Example.F := by
  obtain ⟨S, hS⟩ := Example.emulatesDummy_perfect
  exact ⟨S, le_trans (ucCdist_le_ucSdist _ _) hS⟩

open CatCrypt.Crypto in
/-- The identity converter cannot witness the construction even computationally: with
    trivial admissibility `ucCdist = ucSdist`, and the distinguisher reading the leaked bit
    separates the real leak `true` from the ideal leak `false`, so `1 ≤ ucCdist π F`. -/
theorem ccConstructsCdist_identity_converter_fails :
    (1 : ℝ≥0∞) ≤ ucCdist (T := SPComp) Example.π Example.F := by
  rw [ucCdist_eq_ucSdist_trivial]
  exact Example.identity_sim_fails

open CatCrypt.Crypto in
/-- The perfect construction, pushed through the computational correspondence, is
    computationally UC-secure against every admissible adversary and view. -/
theorem ccConstructsCdist_perfect_ucEmulatesCdist :
    ∀ view : Type, UCEmulatesCdist (T := SPComp) (view := view) 0 Example.π Example.F :=
  (ccConstructsCdist_iff_ucEmulatesCdist Example.π Example.F).mp
    ccConstructsCdist_perfect_witness

end CatCrypt.Crypto.CompUCEquivalence
