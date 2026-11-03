/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCPullback
public import CatCryptCore.Crypto.Party.CompileFunctor
public import CatCryptCore.Crypto.UCOracleGame

/-!
# Change of semantics as a pullback between advantage theories

An *advantage theory* (`AdvTheory`) consists of systems, tests and the advantage of a test
between two systems; `x` realizes `y` with bound `b` (`AdvTheory.Realizes`) when every test `t`
has advantage at most `b t`. A *pullback* between advantage theories (`AdvPullback T T'`) is a
relation `Rel` from the systems of `T` to the systems of `T'` (the graph of a possibly partial
map of systems) and a map `pull` from the tests of `T'` to the tests of `T` such that, for related
pairs, the advantage of `t` between the images is the advantage of `pull t` between the sources.

**Pullback law** (`AdvPullback.realizes_rel`): a realization with bound `b` in `T` gives a
realization with bound `b ∘ pull` in `T'` between related systems. Pullbacks compose
(`AdvPullback.comp`, with `pull` composed contravariantly) with unit `AdvPullback.id`.

Instances of this change of semantics:

* `EnvPullback.toAdvPullback`: every environment pullback of `UCPullback` is a pullback of the
  environment theory `envTheory E O` (reactive systems tested by environments) into itself; the
  law there is `EnvPullback.realizes_map`.
* `stepEqPullback E O`: step equivalence of systems, with the identity as pull; compilation of
  party diagrams is an instance: the system representing the source of a compilable diagram and the
  system representing its compiled image represent the same morphism of `SysCat`
  (`compilePullback_rel`). Compilation is a relation, not a map of systems, since a system
  represents a diagram only up to step equivalence; this is the difference to `EnvPullback`.
  `realizesSim_compile` and `RealizesSim.ofCompiled` are instances of the law.
* `OProt.toAdvPullback`: the oracle-game semantics. A protocol `P` over an oracle interface maps
  oracle games (`gameTheory Q A`, tested by oracle adversaries with the game advantage) to
  reactive systems, and pulls an environment `Z` back to the oracle adversary `P.reduction Z`.
  The target of the pull is not an environment, so this is a pullback between two different
  advantage theories. `Realizes.ofOracleGame` is the law applied to the trivial realization
  of `G₀` by `G₁` with bound the game advantage.

Adversary absorption is an action on environments up to advantage: absorbing `A` and then `S`
gives the advantage of absorbing the composite adversary `S.comp A`, whose attachment has the
views of attaching `S` and then `A` (`AdvSys.view_attach_comp`, `AdvSys.adv_absorb_absorb`,
`AdvSys.view_absorb_absorb`); at the level of pullbacks, the composite
`S.toEnvPullback.comp A.toEnvPullback` pulls back environments with the advantages of
`(S.comp A).toEnvPullback`. Absorbing the forwarding adversary `AdvSys.dummy` leaves advantages
unchanged (`AdvSys.adv_absorb_dummy`).

## Main definitions

* `AdvTheory`, `AdvTheory.Realizes`, `envTheory`, `gameTheory`
* `AdvPullback`, `AdvPullback.id`, `AdvPullback.comp`
* `EnvPullback.toAdvPullback`, `stepEqPullback`, `OProt.toAdvPullback`
* `AdvSys.dummy`, `AdvSys.comp`: the forwarding adversary and the composite of adversaries.

## Main results

* `AdvPullback.realizes_rel`: the pullback law.
* `envTheory_realizes_iff`: realization in `envTheory` is `Realizes`.
* `compilePullback_rel`: source and compiled image of a compilable diagram are related.
* `AdvSys.view_attach_dummy`, `AdvSys.view_attach_comp`: views of the attached forwarding and
  composite adversaries.
* `AdvSys.adv_absorb_absorb`, `AdvSys.view_absorb_absorb`, `AdvSys.adv_absorb_dummy`:
  absorption as an action.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

universe u v u' v' u'' v''

/-! ## Advantage theories and their pullbacks -/

/-- An advantage theory: systems, tests, and the advantage of a test between two systems. -/
structure AdvTheory where
  /-- The systems. -/
  System : Type u
  /-- The tests. -/
  Test : Type v
  /-- The advantage of a test between two systems. -/
  adv : System → System → Test → ℝ≥0∞

/-- `x` realizes `y` with bound `b` in the advantage theory `T`: every test `t` has advantage at
most `b t`. -/
def AdvTheory.Realizes (T : AdvTheory.{u, v}) (x y : T.System) (b : T.Test → ℝ≥0∞) : Prop :=
  ∀ t, T.adv x y t ≤ b t

/-- A pullback from the advantage theory `T` to `T'`: a relation `Rel` from systems of `T` to
systems of `T'` and a map `pull` from tests of `T'` to tests of `T`, such that the advantage of a
test between related images is the advantage of the pulled-back test between the sources. -/
structure AdvPullback (T : AdvTheory.{u, v}) (T' : AdvTheory.{u', v'}) where
  /-- The relation from source systems to image systems. -/
  Rel : T.System → T'.System → Prop
  /-- The map of tests. -/
  pull : T'.Test → T.Test
  /-- The advantage of `t` between related images is the advantage of `pull t`. -/
  adv_rel : ∀ {x x' y y'}, Rel x x' → Rel y y' → ∀ t, T'.adv x' y' t = T.adv x y (pull t)

namespace AdvPullback

variable {T : AdvTheory.{u, v}} {T' : AdvTheory.{u', v'}} {T'' : AdvTheory.{u'', v''}}

/-- **Pullback law.** A realization with bound `b` gives a realization of the related images
with bound `b` at the pulled-back test. -/
theorem realizes_rel (F : AdvPullback T T') {x y : T.System} {x' y' : T'.System}
    (hx : F.Rel x x') (hy : F.Rel y y') {b : T.Test → ℝ≥0∞} (h : T.Realizes x y b) :
    T'.Realizes x' y' (fun t => b (F.pull t)) := fun t => by
  rw [F.adv_rel hx hy t]
  exact h _

/-- The identity pullback: equality on systems, the identity on tests. -/
def id (T : AdvTheory.{u, v}) : AdvPullback T T where
  Rel := Eq
  pull t := t
  adv_rel := by
    rintro _ _ _ _ rfl rfl t
    rfl

/-- The composite of pullbacks: the relational composite on systems, `F.pull` after `G.pull`
on tests. -/
def comp (F : AdvPullback T T') (G : AdvPullback T' T'') : AdvPullback T T'' where
  Rel x z := ∃ y, F.Rel x y ∧ G.Rel y z
  pull t := F.pull (G.pull t)
  adv_rel := by
    rintro _ _ _ _ ⟨_, hx, hx'⟩ ⟨_, hy, hy'⟩ t
    rw [G.adv_rel hx' hy' t, F.adv_rel hx hy]

end AdvPullback

/-! ## The environment theory -/

/-- The advantage theory of reactive systems with interface `(E, O)`, tested by environments
with the advantage `adv`. -/
noncomputable def envTheory (E O : Type) : AdvTheory.{1, 1} where
  System := Σ τ : Type, Sys τ E O
  Test := Σ ζ : Type, Env (Strat ζ E O) ζ
  adv X Y Z := adv X.2 Y.2 Z.2

/-- Realization in the environment theory is `Realizes`. -/
theorem envTheory_realizes_iff {τ υ E O : Type} {X : Sys τ E O} {Y : Sys υ E O}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} :
    (envTheory E O).Realizes ⟨τ, X⟩ ⟨υ, Y⟩ (fun Z => b Z.1 Z.2) ↔ Realizes X Y b :=
  ⟨fun h ζ Z => h ⟨ζ, Z⟩, fun h Z => h Z.1 Z.2⟩

/-- An environment pullback as a pullback of environment theories: its relation is the graph of
`F.map` on admissible systems, its map of tests is `F.pull`. -/
noncomputable def EnvPullback.toAdvPullback {E O E' O' : Type} (F : EnvPullback E O E' O') :
    AdvPullback (envTheory E O) (envTheory E' O') where
  Rel X X' := F.Adm X.2 ∧ X' = ⟨F.St X.1, F.map X.2⟩
  pull Z := ⟨F.Ctx Z.1, F.pull Z.2⟩
  adv_rel := by
    rintro ⟨_, X⟩ _ ⟨_, Y⟩ _ ⟨hX, rfl⟩ ⟨hY, rfl⟩ ⟨_, Z⟩
    exact F.adv_map hX hY Z

/-- `EnvPullback.realizes_map` is the law of `EnvPullback.toAdvPullback`. -/
example {τ υ E O E' O' : Type} (F : EnvPullback E O E' O') {X : Sys τ E O} {Y : Sys υ E O}
    (hX : F.Adm X) (hY : F.Adm Y) {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : Realizes X Y b) :
    Realizes (F.map X) (F.map Y) (fun ζ Z => b (F.Ctx ζ) (F.pull Z)) :=
  fun ζ Z => F.toAdvPullback.realizes_rel (x := ⟨τ, X⟩) (y := ⟨υ, Y⟩)
    (x' := ⟨F.St τ, F.map X⟩) (y' := ⟨F.St υ, F.map Y⟩) ⟨hX, rfl⟩ ⟨hY, rfl⟩
    (b := fun Z => b Z.1 Z.2) (fun Z => h Z.1 Z.2) ⟨ζ, Z⟩

/-! ## Compilation -/

/-- Step equivalence as a pullback of the environment theory into itself: related systems are
step equivalent, and the pull is the identity on environments. Compilation of party diagrams
relates source and image by it (`compilePullback_rel`). -/
noncomputable def stepEqPullback (E O : Type) :
    AdvPullback (envTheory E O) (envTheory E O) where
  Rel X X' := Sys.StepEq ⟨X.1, X.2⟩ ⟨X'.1, X'.2⟩
  pull Z := Z
  adv_rel := by
    rintro ⟨_, X⟩ ⟨_, X'⟩ ⟨_, Y⟩ ⟨_, Y'⟩ hX hY ⟨ζ, Z⟩
    have vX := UCLoopbackObservation.realizes_zero_iff_view_eq.1 (Sys.StepEq.realizes hX).2
    have vY := UCLoopbackObservation.realizes_zero_iff_view_eq.1 (Sys.StepEq.realizes hY).2
    change adv X' Y' Z = adv X Y Z
    rw [adv_eq, adv_eq, vX ζ Z.input, vY ζ Z.input]

end CatCrypt.Crypto.UCTransparent

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCTransparent
open CatCrypt.Crypto.UCConcrete CatCrypt.Category.TracedTerm
open scoped ENNReal

variable {E O : Type}

/-- **Compilation relates source and image.** The system `A` representing the source of a
compilable party diagram `f` and the system `B` representing its compiled image are related by
`stepEqPullback`. -/
theorem compilePullback_rel {f : (⟨⟨E⟩⟩ : CompiledPartyCat) ⟶ ⟨⟨O⟩⟩} {A B : SysObj E O}
    (hA : PartyCat.toSys.map (sourceFunctor.map f) = (⟦A⟧ : (⟨E⟩ : SysCat) ⟶ ⟨O⟩))
    (hB : (Diag.functor fun {X Y} => @CodeGen.den X Y).map (compileFunctor.map f) =
      (⟦B⟧ : (⟨E⟩ : SysCat) ⟶ ⟨O⟩)) :
    (stepEqPullback E O).Rel ⟨A.St, A.sys⟩ ⟨B.St, B.sys⟩ :=
  Quotient.exact (hA.symm.trans ((Diag.functor_map_relabel
    (g := CompGen.den (fun {X Y} => @PartyGen.den X Y) (fun {X Y} => @Compiles X Y))
    (fun x => x.src) (fun _ => rfl) f).trans ((Diag.functor_map_relabel
    (g := CompGen.den (fun {X Y} => @PartyGen.den X Y) (fun {X Y} => @Compiles X Y))
    (fun x => x.code) (fun x => x.compiles.den_eq) f).symm.trans hB)))

/-- `realizesSim_compile` is the law of `stepEqPullback`. -/
example {υ EG OG : Type} {V : PubView E O} {VG : PubView EG OG}
    {f : (⟨⟨E⟩⟩ : CompiledPartyCat) ⟶ ⟨⟨O⟩⟩} {A B : SysObj E O}
    (hA : PartyCat.toSys.map (sourceFunctor.map f) = (⟦A⟧ : (⟨E⟩ : SysCat) ⟶ ⟨O⟩))
    (hB : (Diag.functor fun {X Y} => @CodeGen.den X Y).map (compileFunctor.map f) =
      (⟦B⟧ : (⟨E⟩ : SysCat) ⟶ ⟨O⟩))
    {I : Sys υ EG OG} {S : Simulator E O EG OG V VG}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (hs : RealizesSim A.sys I S b) : RealizesSim B.sys I S b :=
  fun ζ Z => (stepEqPullback E O).realizes_rel (x := ⟨A.St, A.sys⟩) (x' := ⟨B.St, B.sys⟩)
    (y := ⟨_, S.withSub I⟩) (y' := ⟨_, S.withSub I⟩) (compilePullback_rel hA hB)
    (Relation.EqvGen.refl _) (b := fun Z => b Z.1 Z.2) (fun Z => hs Z.1 Z.2) ⟨ζ, Z⟩

/-- `RealizesSim.ofCompiled` is the law of `stepEqPullback` at a compiled step. -/
example {τ Cn : Type} {init : τ} {coins : τ → E → SPComp Cn} {δ : τ → E → Cn → τ × O}
    {code : τ → E → Cn → Option (τ × O)} {Inv : τ → Prop}
    (hc : CompiledStep δ code Inv) (h0 : Inv init) {υ EG OG : Type}
    {V : PubView E O} {VG : PubView EG OG} {I : Sys υ EG OG} {S : Simulator E O EG OG V VG}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (hs : RealizesSim (Sys.ofCore init coins δ) I S b) :
    RealizesSim (Sys.ofCode init coins code) I S b :=
  fun ζ Z => (stepEqPullback E O).realizes_rel (x := ⟨τ, Sys.ofCore init coins δ⟩)
    (x' := ⟨τ, Sys.ofCode init coins code⟩) (y := ⟨_, S.withSub I⟩) (y' := ⟨_, S.withSub I⟩)
    (compiledStep_stepEq hc h0) (Relation.EqvGen.refl _) (b := fun Z => b Z.1 Z.2)
    (fun Z => hs Z.1 Z.2) ⟨ζ, Z⟩

end CatCrypt.Crypto.Party

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-! ## Oracle games -/

/-- The advantage theory of oracle games with queries `Q` and answers `A`, tested by oracle
adversaries with the game advantage. -/
noncomputable def gameTheory (Q A : Type) : AdvTheory.{1, 1} where
  System := KeyedGame Q A
  Test := OracleAdv Q A Bool
  adv := KeyedGame.advantage

/-- The oracle-game semantics of the protocol `P` as a pullback from oracle games to the
environment theory: a game `G` is related to the system `P.sys G`, and an environment `Z` is
pulled back to the oracle adversary `P.reduction Z`. -/
noncomputable def OProt.toAdvPullback {τ E O Q A : Type} (P : OProt τ E O Q A) :
    AdvPullback (gameTheory Q A) (envTheory E O) where
  Rel G X := X = ⟨_, P.sys G⟩
  pull Z := P.reduction Z.2
  adv_rel := by
    rintro G _ G' _ rfl rfl ⟨_, Z⟩
    exact P.adv_sys G G' Z

/-- `Realizes.ofOracleGame` is the law of `OProt.toAdvPullback` applied to the realization of
`G₀` by `G₁` with bound the game advantage. -/
example {τ E O Q A : Type} (P : OProt τ E O Q A) (G₀ G₁ : KeyedGame Q A) :
    Realizes (P.sys G₀) (P.sys G₁) fun _ Z => KeyedGame.advantage G₀ G₁ (P.reduction Z) :=
  fun ζ Z => P.toAdvPullback.realizes_rel (x := G₀) (y := G₁) (x' := ⟨_, P.sys G₀⟩)
    (y' := ⟨_, P.sys G₁⟩) rfl rfl (b := KeyedGame.advantage G₀ G₁) (fun _ => le_rfl) ⟨ζ, Z⟩

/-- The oracle-game semantics followed by the absorption of an adversary system: the composite
pullback bounds the attached systems by the game advantage of the reduction of the absorbed
environment. -/
example {τ P Oh AI AP Lk Lk' Q A α : Type} (Pr : OProt τ (Event P AP) (Oh × Lk) Q A)
    (G₀ G₁ : KeyedGame Q A) (Ad : AdvSys α AI AP Lk Lk') :
    Realizes ((Pr.sys G₀).attach Ad) ((Pr.sys G₁).attach Ad)
      fun _ Z => KeyedGame.advantage G₀ G₁ (Pr.reduction (Z.absorb Ad)) :=
  fun ζ Z => (Pr.toAdvPullback.comp Ad.toEnvPullback.toAdvPullback).realizes_rel
    (x := G₀) (y := G₁) (x' := ⟨_, (Pr.sys G₀).attach Ad⟩) (y' := ⟨_, (Pr.sys G₁).attach Ad⟩)
    ⟨_, rfl, trivial, rfl⟩ ⟨_, rfl, trivial, rfl⟩
    (b := KeyedGame.advantage G₀ G₁) (fun _ => le_rfl) ⟨ζ, Z⟩

/-! ## Adversary absorption as an action -/

namespace AdvSys

variable {α σ γ τ υ ζ AI AM AF LF LM Lk' P Oh : Type}

/-- The forwarding (dummy) adversary: it relays each adversary event and each leakage
unchanged. -/
noncomputable def dummy (AP Lk : Type) : AdvSys Unit AP AP Lk Lk where
  init := ()
  act a i := SPComp.pure (a, i)
  out a l := SPComp.pure (a, l)
  act_noFail _ _ := SPComp.pure_noFail _
  out_noFail _ _ := SPComp.pure_noFail _

/-- The composite adversary system: `A` faces the environment, `S` faces the system, and the
system interface `AM`/`LM` of `A` is the environment interface of `S`. -/
noncomputable def comp (S : AdvSys σ AM AF LF LM) (A : AdvSys α AI AM LM Lk') :
    AdvSys (α × σ) AI AF LF Lk' where
  init := (A.init, S.init)
  act s i :=
    SPComp.bind (A.act s.1 i) fun a =>
      SPComp.bind (S.act s.2 a.2) fun b => SPComp.pure ((a.1, b.1), b.2)
  out s l :=
    SPComp.bind (S.out s.2 l) fun b =>
      SPComp.bind (A.out s.1 b.2) fun a => SPComp.pure ((a.1, b.1), a.2)
  act_noFail _ _ :=
    Assumptions.SPComp.bind_noFail (A.act_noFail _ _) fun _ =>
      Assumptions.SPComp.bind_noFail (S.act_noFail _ _) fun _ => SPComp.pure_noFail _
  out_noFail _ _ :=
    Assumptions.SPComp.bind_noFail (S.out_noFail _ _) fun _ =>
      Assumptions.SPComp.bind_noFail (A.out_noFail _ _) fun _ => SPComp.pure_noFail _

/-- Attaching the forwarding adversary does not change the view. -/
theorem view_attach_dummy (R : Sys τ (Event P AF) (Oh × LF))
    (Z : Strat ζ (Event P AF) (Oh × LF)) :
    view (R.attach (dummy AF LF)) Z = view R Z := by
  refine view_eq_of_stepMap _ R Prod.snd rfl ?_ Z
  intro t e
  cases e <;>
    simp [Sys.attach, Hybrid.withSub, AdvSys.toHybrid, AdvSys.pre, AdvSys.post, dummy,
      SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, SPComp.bind_pure]

/-- Attaching `S` and then `A` has the view of attaching the composite `S.comp A`. -/
theorem view_attach_comp (R : Sys τ (Event P AF) (Oh × LF))
    (S : AdvSys σ AM AF LF LM) (A : AdvSys α AI AM LM Lk')
    (Z : Strat ζ (Event P AI) (Oh × Lk')) :
    view ((R.attach S).attach A) Z = view (R.attach (S.comp A)) Z := by
  refine view_eq_of_stepMap _ _ (fun t => ((t.1, t.2.1), t.2.2)) rfl ?_ Z
  intro t e
  cases e <;>
    simp [Sys.attach, Hybrid.withSub, AdvSys.toHybrid, AdvSys.pre, AdvSys.post, comp,
      SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- **Absorption is an action, at the level of advantages.** Absorbing `A` and then `S` (the
composite pullback `S.toEnvPullback.comp A.toEnvPullback`) gives every pair of systems the
advantage of absorbing the composite adversary `S.comp A`. -/
theorem adv_absorb_absorb (S : AdvSys σ AM AF LF LM) (A : AdvSys α AI AM LM Lk')
    (R : Sys τ (Event P AF) (Oh × LF)) (I : Sys υ (Event P AF) (Oh × LF))
    (Z : Env (Strat ζ (Event P AI) (Oh × Lk')) ζ) :
    adv R I ((S.toEnvPullback.comp A.toEnvPullback).pull Z) =
      adv R I ((S.comp A).toEnvPullback.pull Z) := by
  change adv R I ((Z.absorb A).absorb S) = adv R I (Z.absorb (S.comp A))
  rw [← adv_attach R I S, ← adv_attach _ _ A, ← adv_attach R I (S.comp A), adv_eq, adv_eq,
    view_attach_comp R S A, view_attach_comp I S A]

/-- **Absorption is an action, at the level of views.** The view of `R` against `Z` with `A` and
then `S` absorbed, projected to the state of `Z`, is the view against `Z` with the composite
`S.comp A` absorbed, projected likewise. -/
theorem view_absorb_absorb (S : AdvSys σ AM AF LF LM) (A : AdvSys α AI AM LM Lk')
    (R : Sys τ (Event P AF) (Oh × LF)) (Z : Strat ζ (Event P AI) (Oh × Lk')) :
    SPComp.map (fun c => c.1.1) (view R ((Z.absorb A).absorb S)) =
      SPComp.map Prod.fst (view R (Z.absorb (S.comp A))) := by
  rw [← view_attach R (S.comp A), ← view_attach_comp R S A, view_attach, view_attach,
    SPComp.map_comp]
  rfl

/-- **Unit of the action.** Absorbing the forwarding adversary does not change the advantage of
any pair of systems. -/
theorem adv_absorb_dummy (R : Sys τ (Event P AF) (Oh × LF)) (I : Sys υ (Event P AF) (Oh × LF))
    (Z : Env (Strat ζ (Event P AF) (Oh × LF)) ζ) :
    adv R I ((dummy AF LF).toEnvPullback.pull Z) = adv R I Z := by
  change adv R I (Z.absorb (dummy AF LF)) = adv R I Z
  rw [← adv_attach R I (dummy AF LF), adv_eq, adv_eq, view_attach_dummy R, view_attach_dummy I]

end AdvSys

end CatCrypt.Crypto.UCTransparent
