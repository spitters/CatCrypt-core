/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.WRP
public import CatCryptCore.Refinement.Programs

/-!
# `RRelPT` as the refinement of the refinement weakest precondition `wrp`

The refinement weakest precondition `wrp` of S. Graf's distillery, its concretizations, the
abstract programs `MonoPT` and the forward-simulation characterization `refines_optD_iff` are in
the package `refinement-wp` (`RefinementWP.WRP`), which depends only on the toolchain's
`Std.WP`. This module relates them to the relational refinement `RRelPT` of
`CatCryptCore.Refinement`, on which the judgements of the ascent are stated.

## Main definitions

* `AssnRel.toConc γ`: the concretization of a `Std.Do` assertion map between state assertions.

## Main results

* `rrelPT_optProg_iff_refines` (Theorem A): `RRelPT` of `optProg f` by `wpRel T` is refinement
  of `optD f` by every concrete program whose transformer at the exception postcondition `⊥` is
  the angelic transformer of `T`.
* `guardedRRelPT_iff_refines`, `corresRel_iff_refines`: the guarded form and the total forward
  simulation as refinements.
* `rrelPT_iff_refines` (Theorem B): for `Std.Do` transformers of state assertions that agree
  through `ULift.down` with `Std.WP` transformers, at exception maps onto the `Std.WP`
  exception postconditions, `RRelPT` at the exception relation `eps (ιEA E) ⊑ ιEC E'` is
  refinement at the concretization `AssnRel.toConc γ` and the exception map `eps`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Refinement.WRP

open Std.WP Lean.Order RefinementWP

/-! ## Theorem A: `RRelPT` of `optProg` by `wpRel` as refinement -/

section TheoremA

variable {σ A B α CProg CE : Type} [Assertion CE] [WP CProg α (σ → Prop) CE]

open Std.Do in
/-- **Theorem A.** `RRelPT` of `optProg f` by `wpRel T`, at the assertion map of `SR` with the
    abstract exception postcondition fixed to false, is refinement of `optD f` by every
    concrete program `c` whose transformer at the exception postcondition `⊥` is the angelic
    transformer of `T`. -/
theorem rrelPT_optProg_iff_refines {SR : σ → A → Prop} {Rv : B → α → Prop}
    {f : A → Option (B × A)} {T : σ → α → σ → Prop} (c : CProg)
    (hc : ∀ (Q : α → σ → Prop) (s : σ), Std.WP.wp c Q bot s ↔ ∃ v s', T s v s' ∧ Q v s') :
    RRelPT (AssnRel.ofStateRel (ε := PUnit) SR) (fun E (_ : Unit) => E = ExceptConds.false)
        Rv (fun Φ E => wp⟦optProg f⟧ (Φ, E)) (wpRel T) ↔
      Refines top (Concretization.ofStateRel SR) (fun _ : Unit => (bot : CE)) c (optD f)
        (fun v b _ => Rv b v) :=
  rrelPT_optProg_wpRel_iff.trans (refines_optD_iff c hc).symm

open Classical in
/-- The guarded form of Theorem A: `GuardedRRelPT SR P fa (wpRel T)` is refinement of the
    `optD` program of the guarded update by `c`. -/
theorem guardedRRelPT_iff_refines {SR : σ → A → Prop} {P : A → Prop} {fa : A → A}
    {T : σ → Unit → σ → Prop} {CProg' : Type} [WP CProg' Unit (σ → Prop) CE] (c : CProg')
    (hc : ∀ (Q : Unit → σ → Prop) (s : σ), wp c Q bot s ↔ ∃ v s', T s v s' ∧ Q v s') :
    GuardedRRelPT SR P fa (wpRel T) ↔
      Refines top (Concretization.ofStateRel SR) (fun _ : Unit => (bot : CE)) c
        (optD fun a => if P a then some ((), fa a) else none) (fun _ _ _ => True) :=
  rrelPT_optProg_iff_refines c hc

open Classical in
/-- The total forward simulation of the guarded update by a step relation `T` is refinement of
    its `optD` program by `c`, when the transformer of `c` at `⊥` is the angelic transformer
    of `T`. -/
theorem corresRel_iff_refines {SR : σ → A → Prop} {P : A → Prop} {fa : A → A}
    {T : σ → σ → Prop} {CProg' : Type} [WP CProg' Unit (σ → Prop) CE] (c : CProg')
    (hc : ∀ (Q : Unit → σ → Prop) (s : σ), wp c Q bot s ↔ ∃ s', T s s' ∧ Q () s') :
    (∀ s a, SR s a → P a → ∃ s', T s s' ∧ SR s' (fa a)) ↔
      Refines top (Concretization.ofStateRel SR) (fun _ : Unit => (bot : CE)) c
        (optD fun a => if P a then some ((), fa a) else none) (fun _ _ _ => True) :=
  (corresRel_iff_rrelPT SR P fa T).trans (guardedRRelPT_iff_refines c fun Q s =>
    (hc Q s).trans ⟨fun ⟨s', hT, hQ⟩ => ⟨(), s', hT, hQ⟩, fun ⟨_, s', hT, hQ⟩ => ⟨s', hT, hQ⟩⟩)

end TheoremA

/-! ## Theorem B: aligned exception layers over state predicates -/

section TheoremB

variable {A σ : Type}

/-- The concretization of an assertion map between state assertions: the `Std.Do` map `γ`
    read through `ULift.down` on both sides. -/
def _root_.CatCrypt.Refinement.AssnRel.toConc (γ : AssnRel (.arg A .pure) (.arg σ .pure)) :
    Concretization (σ → Prop) (A → Prop) where
  pred P s := (γ.γ (fun a => ULift.up (P a)) s).down
  pred_mono h s := γ.mono (fun a => h a) s

/-- **Theorem B.** For transformers `wa`, `wc` of `Std.Do` state assertions that agree through
    `ULift.down` with the `Std.WP` transformers of programs `ap` and `c`, at exception maps
    `ιEA`, `ιEC` onto the `Std.WP` exception postconditions, `RRelPT` at the exception relation
    `eps (ιEA E) ⊑ ιEC E'` is refinement of `ap` by `c` under `⊤` at the exception map `eps`. -/
theorem rrelPT_iff_refines {α α' ε ε' AProg CProg AE CE : Type} [Assertion AE] [Assertion CE]
    [WP AProg α (A → Prop) AE] [WP CProg α' (σ → Prop) CE]
    (γ : AssnRel (.arg A .pure) (.arg σ .pure)) (R : α → α' → Prop)
    {wa : (α → Std.Do.Assertion (.arg A .pure)) → ε → Std.Do.Assertion (.arg A .pure)}
    {wc : (α' → Std.Do.Assertion (.arg σ .pure)) → ε' → Std.Do.Assertion (.arg σ .pure)}
    (ap : AProg) (c : CProg) (eps : AE → CE) (ιEA : ε → AE) (ιEC : ε' → CE)
    (hEA : Function.Surjective ιEA) (hEC : Function.Surjective ιEC)
    (hA : ∀ Q E a0, (wa Q E a0).down ↔ Std.WP.wp ap (fun x a' => (Q x a').down) (ιEA E) a0)
    (hC : ∀ Q E s, (wc Q E s).down ↔ Std.WP.wp c (fun x s' => (Q x s').down) (ιEC E) s) :
    RRelPT γ (fun E E' => eps (ιEA E) ⊑ ιEC E') R wa wc ↔
      Refines top γ.toConc eps c ap (fun v b _ => R b v) := by
  constructor
  · intro h
    apply wrp_intro
    intro Qa Ea s hs
    obtain ⟨E, rfl⟩ := hEA Ea
    obtain ⟨E', hE'⟩ := hEC (eps (ιEA E))
    rw [meet_apply, meet_prop_eq_and] at hs
    have hw : wa (fun x a' => ULift.up (Qa x a')) E =
        fun a0 => ULift.up (Std.WP.wp ap Qa (ιEA E) a0) :=
      funext fun a0 => ULift.ext (propext (hA _ E a0))
    have key := @h (fun x a' => ULift.up (Qa x a'))
      (fun cv s' => ULift.up (γ.toConc.post (fun v b _ => R b v) Qa cv s'))
      (fun av cv hR s' hγ =>
        (Concretization.post_apply γ.toConc (fun v b (_ : σ) => R b v) Qa cv s').2 ⟨av, hR, hγ⟩)
      E E' (by change eps (ιEA E) ⊑ ιEC E'; rw [hE']) s
      (by rw [hw]; exact hs.2)
    have hc' := (hC _ E' s).1 key
    rw [hE'] at hc'
    exact hc'
  · intro h Q Q' hQ E E' hE s hs
    have t := wrp_transport h (fun x a' => (Q x a').down) (ιEA E) s
    rw [meet_apply, meet_prop_eq_and] at t
    have hw : wa Q E = fun a0 => ULift.up (Std.WP.wp ap (fun x a' => (Q x a').down) (ιEA E) a0) :=
      funext fun a0 => ULift.ext (propext (hA Q E a0))
    have t2 := t ⟨by simp only [top_apply, top_prop_eq], by rw [hw] at hs; exact hs⟩
    rw [hC]
    refine WP.wp_consequence_econs c _ _ _ _ ?_ hE s t2
    intro cv s' hp
    obtain ⟨av, hR, hγ⟩ := (Concretization.post_apply ..).1 hp
    exact hQ hR s' hγ

end TheoremB

end CatCrypt.Refinement.WRP
