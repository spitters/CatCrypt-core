/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Category
public import CatCryptCore.Crypto.UCTransport

/-!
# Compilation of party diagrams as a traced symmetric monoidal functor

A map `φ` of generators that preserves their denotation in a traced symmetric monoidal category
`C` relabels wiring diagrams: the functor `Diag.relabel φ h : Diag g ⥤ Diag g'` sends a class
of terms to the class of the relabelled terms. It is a strict traced symmetric monoidal functor
and commutes with the denotations (`Diag.functor_map_relabel`).

A compilation is a relation `K a k` between source generators `a` and code generators `k` whose
code denotes the source (`hK : K a k → c k = g a`). The compilable diagrams are the wiring
diagrams over the compiled generators `CompGen K` (a source generator with a code that compiles
it), `CompiledCat g K`. Compilation is the relabelling `Diag.compile hK` onto the wiring
diagrams of code generators, and `Diag.forget` sends a compilable diagram to its source diagram;
both commute with the denotation, so a compilable diagram and its compiled image denote the same
morphism of `C` (`Diag.functor_map_compile`). Compilation is defined on the subcategory of
compilable diagrams, since a source generator has a code only when its compiler accepts it.

**Functor transport.** Let `P` be an observation-preserving map of a setting to itself
(`UCTransport.ObsPreserving`) with the identity on tests, whose graph contains every pair of
systems that represent the same morphism of `C`. Then a statement about the observations of a
system representing a diagram transports to every system representing its image under a
relabelling functor (`Diag.relabel_transport`).

The classical instance has `C = SysCat`. The code generators are the code systems
`Sys.ofCode` of `UCCompiled` (`CodeGen`), and a code compiles a party generator when its
transition is a compiled step of a core system step-equivalent to the party (`Compiles`). A
compiled step gives a step map from the core system to the code system
(`compiledStep_stepMapOn`), so code systems denote their sources. The graph of step equivalence
is observation preserving (`stepEqObsPreserving`), and a realization behind a simulator of any
system representing a compilable party diagram is one of any system representing its compiled
image (`realizesSim_compile`); `RealizesSim.ofCompiled` is its instance at one generator. The
code of a parallel composition of programs is the tensor of the codes (`CodeCat.ofGen_par`),
and compilation preserves the trace (`compile_map_trace`).

The quantum instance has `C = QSysCat (Fin d × H)`. The code generators are core quantum
systems (`QCodeGen`), and a code compiles a quantum party generator when a step map sends a
source system denoting the generator to the code system (`QCompiles`). Step-equivalent systems
run from the same initial private basis state have the same views (`qview_eq_of_stepEq`), so
the graph of equality of views (`qViewObsPreserving`) contains every pair of systems that
represent the same morphism with the same initial basis state, and a quantum realization behind
a simulator transports to compiled quantum party diagrams (`qrealizesSim_compile`).

Search words: compilation functor, compiled party, traced monoidal functor, security transport,
observation preserving, relabelling, subcategory of compilable diagrams.

## Main definitions

* `Party.WTerm.relabel`, `Party.Diag.relabel`: relabelling of terms and of diagrams.
* `Party.CompGen`, `Party.CompiledCat`, `Party.Diag.compile`, `Party.Diag.forget`.
* `Party.stepEqObsPreserving`: step equivalence as an observation-preserving map.
* `Party.CodeGen`, `Party.Compiles`, `Party.CompiledPartyCat`, `Party.CodeCat`,
  `Party.compileFunctor`, `Party.sourceFunctor`.
* `Party.qViewObsPreserving`, `Party.QRep`, `Party.QCodeGen`, `Party.QCompiles`,
  `Party.QCompiledPartyCat`, `Party.QCodeCat`, `Party.qCompileFunctor`, `Party.qSourceFunctor`.

## Main results

* `Party.Diag.functor_map_relabel`, `Party.Diag.relabel_map_tensorHom`,
  `Party.Diag.relabel_map_trace`: the relabelling functor commutes with the denotation and is
  strict monoidal and traced; `Party.Diag.relabelBraided` is its symmetric monoidal structure.
* `Party.Diag.relabel_transport`: functor transport.
* `Party.compiledStep_stepMapOn`, `Party.compiledStep_stepEq`: compiled steps are step maps.
* `Party.realizesSim_compile`: security transport to compiled party diagrams.
* `Party.CodeCat.ofGen_par`: compilation preserves the parallel composition of programs.
* `Party.qview_eq_of_stepEq`: views are invariant under step equivalence.
* `Party.qrealizesSim_compile`: security transport to compiled quantum party diagrams.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

open CategoryTheory MonoidalCategory
open CatCrypt.Category.TracedTerm
open CatCrypt.Crypto.UCTransport

universe u v w w' u' v' w'' x'

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [TracedCategory C] {Gen : C → C → Type w} {Gen' : C → C → Type w'}

/-! ## Relabelling of wiring diagrams -/

namespace WTerm

/-- The wiring generator with its generator of `Gen` relabelled by `φ`. -/
def relabelGen (φ : ∀ {X Y : C}, Gen X Y → Gen' X Y) :
    {X Y : C} → SMGen Gen X Y → SMGen Gen' X Y
  | _, _, .gen a => .gen (φ a)
  | _, _, .assoc X Y Z => .assoc X Y Z
  | _, _, .assocInv X Y Z => .assocInv X Y Z
  | _, _, .lunit X => .lunit X
  | _, _, .lunitInv X => .lunitInv X
  | _, _, .runit X => .runit X
  | _, _, .runitInv X => .runitInv X
  | _, _, .braid X Y => .braid X Y

/-- The term with each generator relabelled by `φ`. -/
def relabel (φ : ∀ {X Y : C}, Gen X Y → Gen' X Y) {X Y : C} (t : WTerm Gen X Y) :
    WTerm Gen' X Y :=
  Term.bind (fun a => Term.gen (relabelGen φ a)) t

/-- **Relabelling preserves the denotation** when `φ` preserves the denotation of generators. -/
theorem den_relabel (g : ∀ {X Y : C}, Gen X Y → (X ⟶ Y))
    (g' : ∀ {X Y : C}, Gen' X Y → (X ⟶ Y)) (φ : ∀ {X Y : C}, Gen X Y → Gen' X Y)
    (h : ∀ {X Y : C} (a : Gen X Y), g' (φ a) = g a) {X Y : C} (t : WTerm Gen X Y) :
    WTerm.den g' (relabel φ t) = WTerm.den g t :=
  (compile_map_eq (CatCrypt.Category.TracedTerm.WTerm.interp g)
    (CatCrypt.Category.TracedTerm.WTerm.interp g') _ (fun f => f) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun a => by cases a <;> first | rfl | exact (h _).symm) t).symm

end WTerm

namespace Diag

variable {g : ∀ {X Y : C}, Gen X Y → (X ⟶ Y)} {g' : ∀ {X Y : C}, Gen' X Y → (X ⟶ Y)}
  (φ : ∀ {X Y : C}, Gen X Y → Gen' X Y) (h : ∀ {X Y : C} (a : Gen X Y), g' (φ a) = g a)

/-- **The relabelling functor**: a class of terms is sent to the class of the relabelled
terms. -/
def relabel : Diag g ⥤ Diag g' where
  obj X := ⟨X.obj⟩
  map f := Quotient.map (WTerm.relabel φ) (fun t t' e => by
    change WTerm.den g' _ = WTerm.den g' _
    rw [WTerm.den_relabel g g' φ h, WTerm.den_relabel g g' φ h]
    exact e) f
  map_id _ := rfl
  map_comp := by
    rintro X Y Z ⟨t⟩ ⟨t'⟩
    rfl

/-- Unfolding lemma of the relabelling functor on objects. -/
@[simp] theorem relabel_obj (X : Diag g) : ((relabel φ h).obj X).obj = X.obj :=
  rfl

/-- **The relabelling functor commutes with the denotation.** -/
@[simp] theorem functor_map_relabel {X Y : Diag g} (f : X ⟶ Y) :
    (functor g').map ((relabel φ h).map f) = (functor g).map f := by
  induction f using Quotient.inductionOn
  exact WTerm.den_relabel g g' φ h _

/-- **Strictness on the tensor.** -/
theorem relabel_map_tensorHom {X₁ Y₁ X₂ Y₂ : Diag g} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    (relabel φ h).map (f₁ ⊗ₘ f₂) = (relabel φ h).map f₁ ⊗ₘ (relabel φ h).map f₂ := by
  induction f₁ using Quotient.inductionOn
  induction f₂ using Quotient.inductionOn
  rfl

/-- **Strictness on the trace.** -/
theorem relabel_map_trace (U : Diag g) {X Y : Diag g} (f : X ⊗ U ⟶ Y ⊗ U) :
    (relabel φ h).map (TracedCategory.trace U f) =
      TracedCategory.trace ((relabel φ h).obj U) ((relabel φ h).map f) := by
  induction f using Quotient.inductionOn
  rfl

/-- The relabelling functor is strict monoidal: the tensorator and the unit are identities. -/
def relabelCoreMonoidal : (relabel φ h).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left f X' := by
    induction f using Quotient.inductionOn
    exact Quotient.sound (by
      change WTerm.den _ _ = WTerm.den _ _
      simp [WTerm.den_relabel g g' φ h])
  μIso_hom_natural_right X' f := by
    induction f using Quotient.inductionOn
    exact Quotient.sound (by
      change WTerm.den _ _ = WTerm.den _ _
      simp [WTerm.den_relabel g g' φ h])
  associativity X Y Z := Quotient.sound (by
    change WTerm.den _ _ = WTerm.den _ _
    simp [WTerm.relabel, WTerm.relabelGen, Term.bind])
  left_unitality X := Quotient.sound (by
    change WTerm.den _ _ = WTerm.den _ _
    simp [WTerm.relabel, WTerm.relabelGen, Term.bind])
  right_unitality X := Quotient.sound (by
    change WTerm.den _ _ = WTerm.den _ _
    simp [WTerm.relabel, WTerm.relabelGen, Term.bind])

/-- The relabelling functor is monoidal, with identity tensorator and unit. -/
instance relabelMonoidal : (relabel φ h).Monoidal :=
  (relabelCoreMonoidal φ h).toMonoidal

/-- **The relabelling functor is a strict symmetric monoidal functor.** -/
instance relabelBraided : (relabel φ h).Braided where
  braided X Y := Quotient.sound (by
    change WTerm.den _ _ = WTerm.den _ _
    simp [WTerm.relabel, WTerm.relabelGen, Term.bind])

end Diag

/-! ## Compilation -/

variable {Code : C → C → Type w'}

/-- A compiled generator: a source generator and a code generator that compiles it. -/
structure CompGen (K : ∀ {X Y : C}, Gen X Y → Code X Y → Prop) (X Y : C) :
    Type (max w w') where
  /-- The source generator. -/
  src : Gen X Y
  /-- The code generator. -/
  code : Code X Y
  /-- The code compiles the source. -/
  compiles : K src code

/-- The denotation of a compiled generator: the denotation of its source. -/
def CompGen.den (g : ∀ {X Y : C}, Gen X Y → (X ⟶ Y))
    (K : ∀ {X Y : C}, Gen X Y → Code X Y → Prop) :
    ∀ {X Y : C}, CompGen (K := @K) X Y → (X ⟶ Y) :=
  fun x => g x.src

/-- **The category of compilable diagrams**: wiring diagrams of compiled generators, denoted by
their sources. -/
abbrev CompiledCat (g : ∀ {X Y : C}, Gen X Y → (X ⟶ Y))
    (K : ∀ {X Y : C}, Gen X Y → Code X Y → Prop) : Type u :=
  Diag (CompGen.den g K)

namespace Diag

variable {g : ∀ {X Y : C}, Gen X Y → (X ⟶ Y)} {c : ∀ {X Y : C}, Code X Y → (X ⟶ Y)}
  {K : ∀ {X Y : C}, Gen X Y → Code X Y → Prop}

/-- The source diagram of a compilable diagram. -/
def forget : CompiledCat g K ⥤ Diag g :=
  relabel (g := CompGen.den g K) (fun x => x.src) fun _ => rfl

variable (hK : ∀ {X Y : C} {a : Gen X Y} {k : Code X Y}, K a k → c k = g a)

/-- **Compilation**: each compiled generator is replaced by its code. -/
def compile : CompiledCat g K ⥤ Diag c :=
  relabel (g := CompGen.den g K) (fun x => x.code)
    fun x => hK x.compiles

/-- **A compilable diagram and its compiled image denote the same morphism.** -/
theorem functor_map_compile {X Y : CompiledCat g K} (f : X ⟶ Y) :
    (functor c).map ((compile hK).map f) = (functor g).map (forget.map f) :=
  (functor_map_relabel (g := CompGen.den g K) (fun x => x.code) (fun x => hK x.compiles) f).trans
    (functor_map_relabel (g := CompGen.den g K) (fun x => x.src) (fun _ => rfl) f).symm

/-- Compilation preserves the trace. -/
theorem compile_map_trace (U : CompiledCat g K) {X Y : CompiledCat g K} (f : X ⊗ U ⟶ Y ⊗ U) :
    (compile hK).map (TracedCategory.trace U f) =
      TracedCategory.trace ((compile hK).obj U) ((compile hK).map f) :=
  relabel_map_trace (g := CompGen.den g K) (fun x => x.code) (fun x => hK x.compiles) U f

end Diag

/-! ## Functor transport -/

namespace Diag

variable {g : ∀ {X Y : C}, Gen X Y → (X ⟶ Y)} {g' : ∀ {X Y : C}, Gen' X Y → (X ⟶ Y)}

/-- **Functor transport.** Let `P` be an observation-preserving map of the setting `A` to itself
with the identity on tests, whose graph `Rel` is reflexive and contains every pair of systems
that represent (`Rep`) the same morphism of `C`. A statement `Q`, stable under the map of
observations, about the observations of a system `W` representing the denotation of a diagram
`f` and an ideal system transports to every system `W'` representing the denotation of the
image of `f` under a relabelling functor. -/
theorem relabel_transport (φ : ∀ {X Y : C}, Gen X Y → Gen' X Y)
    (h : ∀ {X Y : C} (a : Gen X Y), g' (φ a) = g a) {A : ObsSetting.{u', v', w'', x'}}
    {Rel : A.System → A.System → Prop} (P : ObsPreserving A A Rel _root_.id) {X Y : C}
    (Rep : A.System → (X ⟶ Y) → Prop) (hRel : ∀ W W' m, Rep W m → Rep W' m → Rel W W')
    (hRefl : ∀ W, Rel W W) {Q : (A.Test → A.Obs) → (A.Test → A.Obs) → Prop}
    (hQ : ∀ o o', Q o o' → Q (P.onObs ∘ o) (P.onObs ∘ o'))
    {f : (⟨X⟩ : Diag g) ⟶ ⟨Y⟩} {W W' ideal : A.System} (hW : Rep W ((functor g).map f))
    (hW' : Rep W' ((functor g').map ((relabel φ h).map f)))
    (hs : Q (A.obs W) (A.obs ideal)) : Q (A.obs W') (A.obs ideal) := by
  exact P.transport hQ
    (hRel W W' _ hW ((congrArg (Rep W') (functor_map_relabel φ h f)).mp hW')) (hRefl ideal) hs

end Diag

/-! ## The classical instance -/

section Classical

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCConcrete
open scoped ENNReal

variable {τ E O Cn : Type}

/-- **A compiled step is a step map.** Under `CompiledStep` and `Inv init`, the identity is a
step map on `Inv` from the core system to the code system. -/
theorem compiledStep_stepMapOn {init : τ} {coins : τ → E → SPComp Cn}
    {δ : τ → E → Cn → τ × O} {code : τ → E → Cn → Option (τ × O)} {Inv : τ → Prop}
    (hc : CompiledStep δ code Inv) (h0 : Inv init) :
    Sys.StepMapOn (Sys.ofCore init coins δ) (Sys.ofCode init coins code) Inv id where
  init_inv := h0
  init_map := rfl
  pres t e ht q hq := by
    obtain ⟨r, -, rfl⟩ := exists_of_isOutcome_map (h := δ t e) (c := coins t e) hq
    exact hc.inv t e r ht
  step t e ht := by
    simp only [Sys.ofCore, Sys.ofCode, id, hc.agree t e _ ht, Option.elim, Prod.mk.eta]
    exact SPComp.map_id _

/-- Under `CompiledStep` and `Inv init`, the core system and the code system are
step-equivalent. -/
theorem compiledStep_stepEq {init : τ} {coins : τ → E → SPComp Cn}
    {δ : τ → E → Cn → τ × O} {code : τ → E → Cn → Option (τ × O)} {Inv : τ → Prop}
    (hc : CompiledStep δ code Inv) (h0 : Inv init) :
    Sys.StepEq ⟨τ, Sys.ofCore init coins δ⟩ ⟨τ, Sys.ofCode init coins code⟩ :=
  (compiledStep_stepMapOn hc h0).stepEq

/-- **Step equivalence is observation preserving.** The graph of step equivalence, with the
identity on environments, closed systems and observations, preserves the cascade with every
environment test. -/
noncomputable def stepEqObsPreserving (E O : Type) :
    ObsPreserving (envSetting E O) (envSetting E O)
      (fun W W' => Sys.StepEq ⟨W.1, W.2⟩ ⟨W'.1, W'.2⟩) _root_.id where
  onClosed X := X
  onObs o := o
  cascade := by
    rintro ⟨τ, R⟩ ⟨υ, I⟩ ⟨ζ, Z⟩ hRI
    change (envSetting E O).obs _ ⟨ζ, Z⟩ = (envSetting E O).obs _ ⟨ζ, Z⟩
    rw [envSetting_obs, envSetting_obs,
      UCLoopbackObservation.realizes_zero_iff_view_eq.1 hRI.realizes.2 ζ Z.input]
  observation _ := rfl

/-- A code generator of the classical party category: a code system `Sys.ofCode` on the ports
of the objects. -/
structure CodeGen (X Y : SysCat) : Type 1 where
  /-- The state type. -/
  τ : Type
  /-- The coin type. -/
  C : Type
  /-- The initial state. -/
  init : τ
  /-- The coins of a step. -/
  coins : τ → X.P → SPComp C
  /-- The compiled transition. -/
  code : τ → X.P → C → Option (τ × Y.P)

/-- The denotation of a code generator: the class of its code system. -/
noncomputable def CodeGen.den {X Y : SysCat} (k : CodeGen X Y) : X ⟶ Y :=
  ⟦⟨k.τ, Sys.ofCode k.init k.coins k.code⟩⟧

/-- The code `k` compiles the party generator `a`: its transition is a compiled step of a
transition `δ` on an invariant holding initially, and `a` denotes the core system of `δ`. -/
def Compiles {X Y : SysCat} (a : PartyGen X Y) (k : CodeGen X Y) : Prop :=
  ∃ (δ : k.τ → X.P → k.C → k.τ × Y.P) (Inv : k.τ → Prop), CompiledStep δ k.code Inv ∧
    Inv k.init ∧ PartyGen.den a = ⟦⟨k.τ, Sys.ofCore k.init k.coins δ⟩⟧

/-- **A code denotes the party generator it compiles.** -/
theorem Compiles.den_eq {X Y : SysCat} {a : PartyGen X Y} {k : CodeGen X Y}
    (hk : Compiles a k) : CodeGen.den k = PartyGen.den a := by
  obtain ⟨δ, Inv, hc, h0, ha⟩ := hk
  rw [ha]
  exact Quotient.sound (Relation.EqvGen.symm _ _ (compiledStep_stepEq hc h0))

/-- **The category of compilable party diagrams.** -/
abbrev CompiledPartyCat : Type 1 :=
  CompiledCat (C := SysCat) (fun {X Y} => @PartyGen.den X Y) (fun {X Y} => @Compiles X Y)

/-- **The category of compiled parties**: wiring diagrams of code systems modulo step
equivalence of their denotations. -/
abbrev CodeCat : Type 1 :=
  Diag (C := SysCat) fun {X Y} => @CodeGen.den X Y

/-- **The compilation functor** from compilable party diagrams to compiled parties, a strict
traced symmetric monoidal functor. -/
noncomputable abbrev compileFunctor : CompiledPartyCat ⥤ CodeCat :=
  Diag.compile fun hk => Compiles.den_eq hk

/-- The source party diagram of a compilable diagram. -/
noncomputable abbrev sourceFunctor : CompiledPartyCat ⥤ PartyCat :=
  Diag.forget

/-- The morphism of a code generator in the category of compiled parties. -/
noncomputable def CodeCat.ofGen {X Y : SysCat} (k : CodeGen X Y) :
    (⟨X⟩ : CodeCat) ⟶ ⟨Y⟩ :=
  ⟦WTerm.ofGen k⟧

/-- **Compilation preserves parallel composition.** The code of the parallel composition
`ProgE.par p q` is the tensor of the codes of `p` and `q`. -/
theorem CodeCat.ofGen_par {E' O' α β : Type} {p : Prog E O α} {q : Prog E' O' β}
    {k : CodeGen ⟨E ⊕ E'⟩ ⟨O ⊕ O'⟩} {kp : CodeGen ⟨E⟩ ⟨O⟩} {kq : CodeGen ⟨E'⟩ ⟨O'⟩}
    (hk : Compiles (.prog (ProgE.par p q)) k) (hkp : Compiles (.prog p) kp)
    (hkq : Compiles (.prog q) kq) :
    CodeCat.ofGen k = CodeCat.ofGen kp ⊗ₘ CodeCat.ofGen kq := by
  apply Diag.hom_ext
  rw [Diag.map_tensorHom]
  change CodeGen.den k = CodeGen.den kp ⊗ₘ CodeGen.den kq
  rw [hk.den_eq, hkp.den_eq, hkq.den_eq]
  exact Quotient.sound (Prog.toSys_par p q)

/-- **Security transport to compiled party diagrams.** Let `f` be a compilable party diagram,
`A` a system representing its source and `B` a system representing its compiled image. A
realization of `I` behind the simulator `S` by `A` is a realization by `B`, with the same
simulator and bound. -/
theorem realizesSim_compile {υ EG OG : Type} {V : PubView E O} {VG : PubView EG OG}
    {f : (⟨⟨E⟩⟩ : CompiledPartyCat) ⟶ ⟨⟨O⟩⟩} {A B : SysObj E O}
    (hA : PartyCat.toSys.map (sourceFunctor.map f) = (⟦A⟧ : (⟨E⟩ : SysCat) ⟶ ⟨O⟩))
    (hB : (Diag.functor fun {X Y} => @CodeGen.den X Y).map (compileFunctor.map f) =
      (⟦B⟧ : (⟨E⟩ : SysCat) ⟶ ⟨O⟩))
    {I : Sys υ EG OG} {S : Simulator E O EG OG V VG}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (hs : RealizesSim A.sys I S b) : RealizesSim B.sys I S b := by
  unfold RealizesSim at hs ⊢
  rw [realizes_iff_envSetting] at hs ⊢
  exact Diag.relabel_transport (g := CompGen.den (fun {X Y} => @PartyGen.den X Y)
      (fun {X Y} => @Compiles X Y)) (fun x => x.code) (fun x => x.compiles.den_eq)
    (stepEqObsPreserving E O)
    (fun W m => (⟦⟨W.1, W.2⟩⟧ : (⟨E⟩ : SysCat) ⟶ ⟨O⟩) = m)
    (fun _ _ _ h₁ h₂ => Quotient.exact (h₁.trans h₂.symm)) (fun _ => Relation.EqvGen.refl _)
    (Q := fun o o' => ∀ (ζ : Type) (Z : Env (Strat ζ E O) ζ),
      absDiff (prTrue (o ⟨ζ, Z⟩) Z.heap) (prTrue (o' ⟨ζ, Z⟩) Z.heap) ≤ b ζ Z)
    (fun _ _ h => h) (f := f) (W := ⟨A.St, A.sys⟩) (W' := ⟨B.St, B.sys⟩)
    (hA.symm.trans (Diag.functor_map_relabel (g := CompGen.den _ _) (fun x => x.src)
      (fun _ => rfl) f)) hB.symm hs

/-- `RealizesSim.ofCompiled` for a party generator is the functor transport at the generator. -/
example {Cn : Type} {a : PartyGen ⟨E⟩ ⟨O⟩} {init : τ} {coins : τ → E → SPComp Cn}
    {δ : τ → E → Cn → τ × O} {code : τ → E → Cn → Option (τ × O)} {Inv : τ → Prop}
    (hc : CompiledStep δ code Inv) (h0 : Inv init)
    (ha : PartyGen.den a = ⟦⟨τ, Sys.ofCore init coins δ⟩⟧) {υ EG OG : Type}
    {V : PubView E O} {VG : PubView EG OG} {I : Sys υ EG OG} {S : Simulator E O EG OG V VG}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (hs : RealizesSim (Sys.ofCore init coins δ) I S b) :
    RealizesSim (Sys.ofCode init coins code) I S b :=
  realizesSim_compile (A := ⟨τ, Sys.ofCore init coins δ⟩) (B := ⟨τ, Sys.ofCode init coins code⟩)
    (f := ⟦WTerm.ofGen ⟨a, ⟨τ, Cn, init, coins, code⟩, δ, Inv, hc, h0, ha⟩⟧) ha rfl hs

end Classical

/-! ## The quantum instance -/

section Quantum

open CatCrypt.Quantum.ReactiveUC CatCrypt.Crypto.UCMonad.DiamondNorm
open scoped ENNReal

variable {d : ℕ} {H : Type} [Fintype H] {E O : Type}

/-- The core quantum system on `Fin d × H` with the steps of the bundled system `A` and the
initial private basis state `h₀`. -/
def qsysOfObj (A : QRSys.Obj (Fin d × H) E O) (h₀ : H) : QSys H A.St E O d :=
  ⟨A.sys.init, h₀, A.sys.step⟩

/-- **Views are invariant under step equivalence.** Step-equivalent systems on `Fin d × H`, run
from the same initial private basis state, have the same view against every environment. -/
theorem qview_eq_of_stepEq [DecidableEq H] {A B : QRSys.Obj (Fin d × H) E O}
    (h : QRSys.StepEq A B) (h₀ : H) {ζ : Type} (Z : QStrat ζ E O d) :
    qview (qsysOfObj A h₀) Z = qview (qsysOfObj B h₀) Z := by
  induction h with
  | rel A B h =>
    obtain ⟨f, hf⟩ := h
    exact QProg.qview_eq_of_stepMap (S₁ := qsysOfObj A h₀) (S₂ := qsysOfObj B h₀) rfl hf Z
  | refl A => rfl
  | symm A B _ ih => exact ih.symm
  | trans A B C _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The graph of equality of views on `qSetting` is observation preserving, with the identity on
environments, closed systems and observations. -/
noncomputable def qViewObsPreserving (E O : Type) (d : ℕ) (ζ : Type) :
    ObsPreserving (qSetting E O d ζ) (qSetting E O d ζ)
      (fun (W W' : QSysObj E O d) => ∀ Z : QStrat ζ E O d, qview W'.sys Z = qview W.sys Z)
      _root_.id where
  onClosed X := X
  onObs o := o
  cascade _ _ Z h := h Z
  observation _ := rfl

/-- The bundled system `W` is a core quantum system on `Fin d × H` with initial private basis
state `h₀` whose class in `QSysCat` is `m`. -/
def QRep [DecidableEq H] (h₀ : H) (W : QSysObj E O d)
    (m : (⟨E⟩ : QSysCat (Fin d × H)) ⟶ ⟨O⟩) : Prop :=
  ∃ (τ : Type) (S : QSys H τ E O d), S.initReg = h₀ ∧ W = QSysObj.mk H τ S ∧
    (⟦⟨τ, S.toQRSys⟩⟧ : (⟨E⟩ : QSysCat (Fin d × H)) ⟶ ⟨O⟩) = m

/-- Two systems representing the same morphism with the same initial private basis state have
the same views. -/
theorem QRep.view_eq [DecidableEq H] {h₀ : H} {W W' : QSysObj E O d}
    {m : (⟨E⟩ : QSysCat (Fin d × H)) ⟶ ⟨O⟩} (hW : QRep h₀ W m) (hW' : QRep h₀ W' m) {ζ : Type}
    (Z : QStrat ζ E O d) :
    qview W'.sys Z = qview W.sys Z := by
  obtain ⟨τ, ⟨i, r, st⟩, rfl, rfl, hm⟩ := hW
  obtain ⟨τ', ⟨i', r', st'⟩, hr, rfl, hm'⟩ := hW'
  subst hr
  exact (qview_eq_of_stepEq (Quotient.exact (hm.trans hm'.symm)) r' Z).symm

/-- A quantum code generator on `Fin d × H`: a core quantum system on the ports of the
objects. -/
structure QCodeGen (d : ℕ) (H : Type) [Fintype H] (X Y : QSysCat (Fin d × H)) : Type 1 where
  /-- The state type. -/
  τ : Type
  /-- The code system. -/
  sys : QSys H τ X.P Y.P d

/-- The denotation of a quantum code generator: the class of its system. -/
noncomputable def QCodeGen.den {X Y : QSysCat (Fin d × H)} (k : QCodeGen d H X Y) : X ⟶ Y :=
  ⟦⟨k.τ, k.sys.toQRSys⟩⟧

/-- The quantum code `k` compiles the quantum party generator `a`: a source system denoting `a`
is sent to the code system by a step map. -/
def QCompiles {X Y : QSysCat (Fin d × H)} (a : QPartyGen (Fin d × H) X Y)
    (k : QCodeGen d H X Y) : Prop :=
  ∃ (υ : Type) (src : QSys H υ X.P Y.P d) (f : υ → k.τ),
    QRSys.StepMap src.toQRSys k.sys.toQRSys f ∧ QPartyGen.den a = ⟦⟨υ, src.toQRSys⟩⟧

/-- **A quantum code denotes the generator it compiles.** -/
theorem QCompiles.den_eq {X Y : QSysCat (Fin d × H)} {a : QPartyGen (Fin d × H) X Y}
    {k : QCodeGen d H X Y} (hk : QCompiles a k) : QCodeGen.den k = QPartyGen.den a := by
  obtain ⟨υ, src, f, hf, ha⟩ := hk
  rw [ha]
  exact Quotient.sound (Relation.EqvGen.symm _ _ hf.stepEq)

variable (d H) in
/-- **The category of compilable quantum party diagrams** on `Fin d × H`. -/
abbrev QCompiledPartyCat : Type 1 :=
  CompiledCat (C := QSysCat (Fin d × H)) (fun {X Y} => @QPartyGen.den (Fin d × H) _ X Y)
    (fun {X Y} => @QCompiles d H _ X Y)

variable (d H) in
/-- **The category of compiled quantum parties**: wiring diagrams of quantum code systems
modulo step equivalence of their denotations. -/
abbrev QCodeCat : Type 1 :=
  Diag (C := QSysCat (Fin d × H)) fun {X Y} => @QCodeGen.den d H _ X Y

variable (d H) in
/-- **The quantum compilation functor**, a strict traced symmetric monoidal functor. -/
noncomputable abbrev qCompileFunctor : QCompiledPartyCat d H ⥤ QCodeCat d H :=
  Diag.compile fun hk => QCompiles.den_eq hk

variable (d H) in
/-- The source quantum party diagram of a compilable diagram. -/
noncomputable abbrev qSourceFunctor : QCompiledPartyCat d H ⥤ QPartyCat (Fin d × H) :=
  Diag.forget

/-- **Security transport to compiled quantum party diagrams.** Let `f` be a compilable quantum
party diagram, `A` a core quantum system representing its source and `B` one representing its
compiled image, with the same initial private basis state. A realization of `I` behind the
simulator `S` at distance `ε` by `A` is one by `B`. -/
theorem qrealizesSim_compile [DecidableEq H] {τ τ' υ σ EG OG : Type} {H' : Type} [Fintype H']
    [DecidableEq H']
    {f : (⟨⟨E⟩⟩ : QCompiledPartyCat d H) ⟶ ⟨⟨O⟩⟩} {A : QSys H τ E O d} {B : QSys H τ' E O d}
    (hr : A.initReg = B.initReg)
    (hA : (QPartyCat.toQRSys (Fin d × H)).map ((qSourceFunctor d H).map f) =
      (⟦⟨τ, A.toQRSys⟩⟧ : (⟨E⟩ : QSysCat (Fin d × H)) ⟶ ⟨O⟩))
    (hB : (Diag.functor fun {X Y} => @QCodeGen.den d H _ X Y).map ((qCompileFunctor d H).map f) =
      (⟦⟨τ', B.toQRSys⟩⟧ : (⟨E⟩ : QSysCat (Fin d × H)) ⟶ ⟨O⟩))
    {I : QSys H' υ EG OG d} {S : QSim σ E O EG OG d} {ε : ℝ≥0∞}
    (hs : QRealizesSim A I S ε) : QRealizesSim B I S ε := by
  intro ζ
  exact Diag.relabel_transport (g := CompGen.den (fun {X Y} => @QPartyGen.den (Fin d × H) _ X Y)
      (fun {X Y} => @QCompiles d H _ X Y)) (fun x => x.code) (fun x => x.compiles.den_eq)
    (qViewObsPreserving E O d ζ) (QRep A.initReg) (fun _ _ _ h₁ h₂ Z => QRep.view_eq h₁ h₂ Z)
    (fun _ _ => rfl)
    (Q := fun (o _ : QStrat ζ E O d → CatCrypt.Quantum.CPComp d ζ) =>
      QUCEmulatesDiamond ε (fun Z => (o Z).toQComp)
        (fun Z => (simView I S Z).toQComp) (fun Z => CatCrypt.Quantum.CPComp.branch_cp (o Z))
        (fun Z => CatCrypt.Quantum.CPComp.branch_cp (simView I S Z)))
    (fun _ _ h => h) (f := f) (W := QSysObj.mk H τ A) (W' := QSysObj.mk H τ' B)
    (ideal := QSysObj.mk H τ A)
    ⟨τ, A, rfl, rfl, hA.symm.trans (Diag.functor_map_relabel (g := CompGen.den _ _)
      (fun x => x.src) (fun _ => rfl) f)⟩
    ⟨τ', B, hr.symm, rfl, hB.symm⟩ (hs ζ)

end Quantum

end CatCrypt.Crypto.Party
