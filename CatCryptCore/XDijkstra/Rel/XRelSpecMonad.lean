/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XPostShape
public import CatCryptCore.XDijkstra.Rel.XRelQ0
public import CatCryptCore.XDijkstra.Rel.XSDistrSoundness


@[expose] public section
set_option autoImplicit false

/-!
# `XRelSpecMonad`: the relational coupling-spec-monad (`bind = liftR_bind`)

This module builds the relational coupling-spec-monad — a graded Dijkstra monad over
pairs of programs whose `bind` is the coupling composition
`Couples_bind`/`RelQ0.liftR_bind`, so couplings compose as the spec threads through
`bind`. It is the relational Dijkstra monad of *"The Next 700 Relational Program
Logics"* (Maillard–Hriţcu–Rivas–Van Muylder): a monad whose objects are pairs of
computations and whose Kleisli composition glues their couplings.

## Relation to the product `xprod`

The extended-PostShape core (`XPostShape.lean`) carries a relational axis, the product
`xprod`/`xseq`: `xprod t₁ t₂` runs the two transformers independently and pairs the
results — a coupling only for the relation `R = fun _ _ => True`.
`XSDistrSoundness.couplingPT_xseq_apply_blind` makes this precise: the product's WP
`(xseq (couplingPT ε R c c') (couplingPT δ S d d')).apply Q` reduces to
`XRelTripleQ0 ε R c c'`, dropping `δ`, the second relation `S`, and both continuations.
Only the grade `ε + δ` threads through the product (`couplingPT_xseq_grade`).

A cryptographic hybrid needs the coupling relation itself to compose, not just its error
grade. A monad-over-pairs whose bind is `liftR_bind` provides this: binding two coupled
steps produces a coupling of the bound programs, at grade `ε + δ`, carrying the
post-relation `S`. This module packages that bind as the spec monad `RelPT`, so the
coupling and its grade compose in one object. Contrast `XHybridExample.hybrid3_bound`,
which composes couplings by horizontal transitivity `xrelQ0_trans_eq` and sums grades in
a separate `xseq` chain.

## Principal declarations

* `RelPT ε α β` — the spec monad over pairs: a pair of programs `⟨fst, snd⟩` graded by the
  coupling error `ε` (in the type index, as a graded monad). `RelSpec w R` reads its
  coupling specification at a post-relation `R` — the coupling condition
  `RelQ0.liftR ε R w.fst w.snd`.
* `relPure` (grade `0`, `liftR_pure`) and `relBind`, whose composition is `liftR_bind`:
  `relBind (δ := δ) m k₁ k₂ : RelPT (ε + δ) α' β'`, grades add, and `relBind_spec` proves
  its specification is the composed coupling at `ε + δ` carrying the continuation relation
  `S`.
* `RelSpecTriple ε R c c' := RelQ0.liftR ε R c c'` and `relSpec_seq` — the relational
  triple and its sequencing rule, composing two coupled steps into one at grade `ε + δ`
  through the bind law (`liftR_bind`). `relSpec_seq` is `relBind_spec` read on the two
  program legs.
* `product_xseq_blind` vs `relBind_carries_S` — the `xprod` contrast: the product's WP is
  blind to `S`/`δ` (re-exporting `couplingPT_xseq_apply_blind`), while `relBind`'s spec
  carries `S` at grade `ε + δ`.
* `relSpec3_auto` / `relDemo3_sdistr` / `relDemo3_pmf` — three coupled hops compose into
  `XRelTripleQ0 (ε₁ + ε₂ + ε₃)` on `SDistr` (and, with vacuous grade, exact `Couples` on
  `PMF`), the couplings gluing via `relBind_spec = liftR_bind` and the grades summing in
  the composed `RelPT`'s index.

The instance `SDistr` (`instRelQ0SDistr`) runs the monad on the cryptographic
sub-distribution effect; `PMF` (`instRelQ0PMF`) is the qualitative (`ε`-vacuous) fragment
where `RelPT`'s bind is `Couples_bind`.

`XRelMvcgen.lean` provides the `relmvcgen` tactic, which fires `relBind_spec` at each
`bind` node of a coupled program, reducing an end-to-end coupling goal to the per-hop
leaves and the summed grade; the composition rule and demos below are its semantic
content.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt CatCrypt.Prob

variable {T : Type → Type} [RelQ0 T]

/-! ## 1. The relational spec monad over pairs

`RelPT ε α β` is the computation component of the relational Dijkstra monad over pairs: a
pair of programs `⟨fst, snd⟩` on the coupling-equipped monad `T`, graded by the coupling
error `ε` (carried in the type index; `relBind` adds grades). `RelSpec w R` reads off its
specification component: the coupling condition `RelQ0.liftR ε R w.fst w.snd` at a
post-relation `R`. -/

/-- **The relational spec-monad object over pairs.** A pair of `T`-programs graded by the
coupling error `ε`. The two legs run independently (a coupling relates them); the grade
`ε` lives in the index and accumulates under `relBind`. -/
structure RelPT (ε : ℝ≥0∞) (α β : Type) where
  /-- The left program. -/
  fst : T α
  /-- The right program. -/
  snd : T β

/-- **The coupling specification of a `RelPT`.** `RelSpec w R` is the coupling condition
`RelQ0.liftR ε R w.fst w.snd`: the two legs are `ε`-coupled on the support of `R`. -/
def RelSpec {ε : ℝ≥0∞} {α β : Type} (w : RelPT (T := T) ε α β) (R : α → β → Prop) : Prop :=
  RelQ0.liftR ε R w.fst w.snd

/-- **The relational triple** (`RelSpec` on explicit legs). `RelSpecTriple ε R c c'` is
`RelQ0.liftR ε R c c'` — definitionally `XRelTripleQ0`, phrased on a pair to feed the spec
monad. -/
def RelSpecTriple {α β : Type} (ε : ℝ≥0∞) (R : α → β → Prop) (c : T α) (c' : T β) : Prop :=
  RelQ0.liftR ε R c c'

/-- The triple on the legs of a `RelPT` is its spec. -/
theorem relSpec_eq_relSpecTriple {ε : ℝ≥0∞} {α β : Type}
    (w : RelPT (T := T) ε α β) (R : α → β → Prop) :
    RelSpec w R = RelSpecTriple ε R w.fst w.snd := rfl

/-- **`RelSpecTriple` is `XRelTripleQ0`.** The relational triple of the spec monad and the
graded relational triple of `XRelQ0` are the same object — both are `RelQ0.liftR`. -/
theorem relSpecTriple_eq_xrelTripleQ0 {α β : Type}
    (ε : ℝ≥0∞) (R : α → β → Prop) (c : T α) (c' : T β) :
    RelSpecTriple ε R c c' = XRelTripleQ0 ε R c c' := rfl

/-! ## 2. The monad structure: `relPure` and `relBind = liftR_bind`

`relPure` is the grade-`0` unit (`liftR_pure`). `relBind` is the coupling composition: its
two legs are the two `bind`s, its grade is the sum `ε + δ`, and `relBind_spec` proves its
specification is the composed coupling `RelQ0.liftR_bind`. -/

/-- **Relational return.** The pair of point programs `⟨pure a, pure b⟩` at grade `0`. -/
def relPure {α β : Type} (a : α) (b : β) : RelPT (T := T) 0 α β :=
  ⟨RelQ0.pure' a, RelQ0.pure' b⟩

/-- **Relational bind — the coupling composition.** Binds each leg with its own Kleisli
continuation (`k₁` left, `k₂` right — a relational Kleisli arrow is a pair of arrows, the
sides running independently) and adds the grade to `ε + δ`. Its specification is
`liftR_bind` (`relBind_spec`), the pRHL coupling composition. -/
def relBind {ε δ : ℝ≥0∞} {α β α' β' : Type}
    (m : RelPT (T := T) ε α β) (k₁ : α → T α') (k₂ : β → T β') :
    RelPT (T := T) (ε + δ) α' β' :=
  ⟨RelQ0.bind' m.fst k₁, RelQ0.bind' m.snd k₂⟩

@[simp] theorem relBind_fst {ε δ : ℝ≥0∞} {α β α' β' : Type}
    (m : RelPT (T := T) ε α β) (k₁ : α → T α') (k₂ : β → T β') :
    (relBind (δ := δ) m k₁ k₂).fst = RelQ0.bind' m.fst k₁ := rfl

@[simp] theorem relBind_snd {ε δ : ℝ≥0∞} {α β α' β' : Type}
    (m : RelPT (T := T) ε α β) (k₁ : α → T α') (k₂ : β → T β') :
    (relBind (δ := δ) m k₁ k₂).snd = RelQ0.bind' m.snd k₂ := rfl

/-- **Coupling `return` law.** `R`-related points give the zero-error spec — `liftR_pure`,
the spec-monad `return` rule. -/
theorem relPure_spec {α β : Type} {a : α} {b : β} {R : α → β → Prop} (h : R a b) :
    RelSpec (relPure (T := T) a b) R :=
  RelQ0.liftR_pure h

/-- **Coupling `bind` law.** From the prefix spec `RelSpec m R` and, at every `R`-related
pair, a `δ`-triple on the continuation legs, obtain the spec of the bound pair at grade
`ε + δ`, carrying the post-relation `S`. This is `RelQ0.liftR_bind`; the output grade
`ε + δ` is read off `relBind`'s type index, with no separate accumulation. -/
theorem relBind_spec {ε δ : ℝ≥0∞} {α β α' β' : Type}
    {R : α → β → Prop} {S : α' → β' → Prop}
    {m : RelPT (T := T) ε α β} {k₁ : α → T α'} {k₂ : β → T β'}
    (h : RelSpec m R)
    (hk : ∀ a b, R a b → RelSpecTriple δ S (k₁ a) (k₂ b)) :
    RelSpec (relBind (δ := δ) m k₁ k₂) S :=
  RelQ0.liftR_bind h hk

/-- **The bound spec unfolds to the composed coupling.** Definitionally, `relBind`'s spec
at `S` is the coupling of the two bound programs at grade `ε + δ`; the grade sum lives in
the object. -/
theorem relBind_grade_add {ε δ : ℝ≥0∞} {α β α' β' : Type}
    (m : RelPT (T := T) ε α β) (k₁ : α → T α') (k₂ : β → T β') (S : α' → β' → Prop) :
    RelSpec (relBind (δ := δ) m k₁ k₂) S
      = RelQ0.liftR (ε + δ) S (RelQ0.bind' m.fst k₁) (RelQ0.bind' m.snd k₂) := rfl

/-- **Grade monotonicity of the spec.** A larger error budget still holds. -/
theorem relSpec_mono_eps {ε ε' : ℝ≥0∞} {α β : Type}
    {w : RelPT (T := T) ε α β} {w' : RelPT (T := T) ε' α β} {R : α → β → Prop}
    (hww : w.fst = w'.fst ∧ w.snd = w'.snd) (hε : ε ≤ ε') (h : RelSpec w R) :
    RelSpec w' R := by
  obtain ⟨h1, h2⟩ := hww
  have : RelSpec w' R = RelQ0.liftR ε' R w.fst w.snd := by
    rw [RelSpec, h1, h2]
  rw [this]
  exact RelQ0.liftR_mono_eps hε h

/-- **Relation weakening of the spec.** A coupling on `R` is a coupling on any weaker
`S ⊇ R`, at the same grade — `liftR_mono_rel`. -/
theorem relSpec_mono_rel {ε : ℝ≥0∞} {α β : Type}
    {w : RelPT (T := T) ε α β} {R S : α → β → Prop}
    (hRS : ∀ a b, R a b → S a b) (h : RelSpec w R) : RelSpec w S :=
  RelQ0.liftR_mono_rel hRS h

/-! ## 3. The relational triple's sequencing rule

`relSpec_seq` composes two coupled steps into one through the bind law; it is
`relBind_spec` read on explicit program legs. Its output grade `ε + δ` is the composed
coupling error, carried with the post-relation `S`. §4 contrasts this with the product
`xseq`. -/

/-- **The coupling-sequencing rule.** From an `ε`-triple on the prefixes and, at every
`R`-related pair, a `δ`-triple on the continuations, obtain a triple on the bound programs
at grade `ε + δ`, carrying `S`, via the bind law `RelQ0.liftR_bind`. This is `relBind_spec`
on the two legs of `⟨c, c'⟩`. -/
theorem relSpec_seq {ε δ : ℝ≥0∞} {α β α' β' : Type}
    {R : α → β → Prop} {S : α' → β' → Prop}
    {c : T α} {c' : T β} {k₁ : α → T α'} {k₂ : β → T β'}
    (h : RelSpecTriple ε R c c')
    (hk : ∀ a b, R a b → RelSpecTriple δ S (k₁ a) (k₂ b)) :
    RelSpecTriple (ε + δ) S (RelQ0.bind' c k₁) (RelQ0.bind' c' k₂) :=
  RelQ0.liftR_bind h hk

/-- `relSpec_seq` is `relBind_spec` on `⟨c, c'⟩`: the triple sequencing rule and the spec
monad's bind law are definitionally the same. -/
theorem relSpec_seq_eq_relBind_spec {ε δ : ℝ≥0∞} {α β α' β' : Type}
    {S : α' → β' → Prop}
    (c : T α) (c' : T β) (k₁ : α → T α') (k₂ : β → T β') :
    RelSpecTriple (ε + δ) S (RelQ0.bind' c k₁) (RelQ0.bind' c' k₂)
      = RelSpec (relBind (δ := δ) (⟨c, c'⟩ : RelPT (T := T) ε α β) k₁ k₂) S := rfl

/-! ## 4. Contrast with the product `xprod`/`xseq`

The product-based relational axis of the extended core is blind to the coupling relation.
`product_xseq_blind` re-exports `couplingPT_xseq_apply_blind`: the sequenced product's WP
keeps only the first (`ε`, `R`) coupling and discards `δ`, `S`, and both continuations.
`relBind_carries_S` is the contrast: `relBind`'s spec is the coupling at the second
relation `S` and the summed grade `ε + δ`, built from both continuation legs. Only the
grade threads through `xseq`; the whole coupling threads through `relBind`. -/

/-- **The product `xseq` is blind to the second coupling.** `couplingPT_xseq_apply_blind`:
the sequenced product's WP reduces to `XRelTripleQ0 ε R c c'`, dropping `δ`, `S`, `d`, `d'`.
The product composes only the grade, not the coupling relation. -/
theorem product_xseq_blind {α β α' β' : Type}
    (ε δ : ℝ≥0∞) (R : α → β → Prop) (S : α' → β' → Prop)
    (c : T α) (c' : T β) (d : T α') (d' : T β')
    (Q : XPostCond (α' × β') (.graded ℝ≥0∞ .pure) Prop) :
    (xseq (couplingPT ε R c c') (couplingPT δ S d d')).apply Q = XRelTripleQ0 ε R c c' :=
  couplingPT_xseq_apply_blind ε δ R S c c' d d' Q

/-- **`relBind` carries the relation.** Unlike the blind product, `relBind`'s spec is the
coupling at the continuation relation `S`, at grade `ε + δ`, using both legs `k₁`, `k₂` of
the continuation — the coupling composition `xseq` cannot express. -/
theorem relBind_carries_S {ε δ : ℝ≥0∞} {α β α' β' : Type}
    {R : α → β → Prop} {S : α' → β' → Prop}
    {m : RelPT (T := T) ε α β} {k₁ : α → T α'} {k₂ : β → T β'}
    (h : RelSpec m R)
    (hk : ∀ a b, R a b → RelSpecTriple δ S (k₁ a) (k₂ b)) :
    RelSpec (relBind (δ := δ) m k₁ k₂) S :=
  relBind_spec h hk

/-! ## 5. Three coupled hops compose

A three-step coupled computation — a prefix `⟨m₁, m₂⟩` and two relational Kleisli
continuations `⟨k₁, k₂⟩`, `⟨l₁, l₂⟩`, each hop a coupling leaf — composes to a single
coupling of the bound programs, with the grades summing in the composed `RelPT`'s index
`(ε₁ + ε₂) + ε₃` and the post-relation `R₂` carried through. The composition is two
applications of `relBind_spec`. Contrast `XHybridExample.hybrid3_bound`, which composes
couplings by a separate horizontal transitivity (`xrelQ0_trans_eq`, at a fixed `Eq`) and
sums the grades in a separate `xseq`/`xmvcgen` pass; here the coupling and its grade
compose in one object, at different per-hop relations. -/

section Demo
variable {α₀ β₀ α₁ β₁ α₂ β₂ : Type}

/-- **Three coupled hops compose (generic `RelQ0`).** The couplings glue via
`relBind_spec = RelQ0.liftR_bind`; the grade sums to `(ε₁ + ε₂) + ε₃` in the spec of the
doubly-bound pair, carrying the final relation `R₂`. The proof is a single nested
`relBind_spec`. -/
theorem relSpec3_auto {ε₁ ε₂ ε₃ : ℝ≥0∞}
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {m₁ : T α₀} {m₂ : T β₀}
    {k₁ : α₀ → T α₁} {k₂ : β₀ → T β₁}
    {l₁ : α₁ → T α₂} {l₂ : β₁ → T β₂}
    (h₁ : RelSpecTriple ε₁ R₀ m₁ m₂)
    (h₂ : ∀ a b, R₀ a b → RelSpecTriple ε₂ R₁ (k₁ a) (k₂ b))
    (h₃ : ∀ a b, R₁ a b → RelSpecTriple ε₃ R₂ (l₁ a) (l₂ b)) :
    RelSpecTriple ((ε₁ + ε₂) + ε₃) R₂
      (RelQ0.bind' (RelQ0.bind' m₁ k₁) l₁) (RelQ0.bind' (RelQ0.bind' m₂ k₂) l₂) :=
  relSpec_seq (relSpec_seq h₁ h₂) h₃

/-- The same composition read as a spec of the doubly-`relBind`'d pair — the grade
`(ε₁ + ε₂) + ε₃` is the type index of the composed `RelPT`, produced by the two `relBind`s.
-/
theorem relSpec3_auto_via_relBind {ε₁ ε₂ ε₃ : ℝ≥0∞}
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {m₁ : T α₀} {m₂ : T β₀}
    {k₁ : α₀ → T α₁} {k₂ : β₀ → T β₁}
    {l₁ : α₁ → T α₂} {l₂ : β₁ → T β₂}
    (h₁ : RelSpecTriple ε₁ R₀ m₁ m₂)
    (h₂ : ∀ a b, R₀ a b → RelSpecTriple ε₂ R₁ (k₁ a) (k₂ b))
    (h₃ : ∀ a b, R₁ a b → RelSpecTriple ε₃ R₂ (l₁ a) (l₂ b)) :
    RelSpec
      (relBind (δ := ε₃)
        (relBind (δ := ε₂) (⟨m₁, m₂⟩ : RelPT (T := T) ε₁ α₀ β₀) k₁ k₂) l₁ l₂) R₂ :=
  relBind_spec (relBind_spec h₁ h₂) h₃

end Demo

/-! ### 3-hop composition on `SDistr`

At `SDistr` (`liftR := liftRApprox`, the `ε`-approximate sub-coupling), `relSpec3_auto`
lands in `XRelTripleQ0 (T := SDistr) (ε₁ + ε₂ + ε₃)` — the end-to-end coupling of a
three-step coupled reduction, grades summed and relation carried, from the three per-hop
leaves. This is the vertical (bind) counterpart of `XHybridExample.hybrid3_bound`, through
the coupling-spec-monad bind rather than a separate transitivity + `xseq` pass. -/

section SDistrDemo
variable {α₀ β₀ α₁ β₁ α₂ β₂ : Type}

/-- **3-hop coupling on `SDistr`.** Three coupled hops — prefix `⟨m₁, m₂⟩` and two
relational Kleisli continuations — compose to the end-to-end coupling
`XRelTripleQ0 (ε₁ + ε₂ + ε₃)` of the bound programs, the couplings gluing via
`relBind_spec` and the advantages summing. -/
theorem relDemo3_sdistr {ε₁ ε₂ ε₃ : ℝ≥0∞}
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {m₁ : SDistr α₀} {m₂ : SDistr β₀}
    {k₁ : α₀ → SDistr α₁} {k₂ : β₀ → SDistr β₁}
    {l₁ : α₁ → SDistr α₂} {l₂ : β₁ → SDistr β₂}
    (h₁ : XRelTripleQ0 (T := SDistr) ε₁ R₀ m₁ m₂)
    (h₂ : ∀ a b, R₀ a b → XRelTripleQ0 (T := SDistr) ε₂ R₁ (k₁ a) (k₂ b))
    (h₃ : ∀ a b, R₁ a b → XRelTripleQ0 (T := SDistr) ε₃ R₂ (l₁ a) (l₂ b)) :
    XRelTripleQ0 (T := SDistr) (ε₁ + ε₂ + ε₃) R₂
      (RelQ0.bind' (RelQ0.bind' m₁ k₁) l₁) (RelQ0.bind' (RelQ0.bind' m₂ k₂) l₂) :=
  relSpec3_auto (T := SDistr) h₁ h₂ h₃

end SDistrDemo

/-! ### The qualitative fragment on `PMF`: bind is `Couples_bind`

On `PMF` (`instRelQ0PMF`) the lifting ignores the grade — `liftR ε R = Couples · · R` — so
`relBind`'s spec is the exact coupling composition `Couples_bind`. Three exact couplings
compose to an exact coupling of the bound programs, the relation carried through, the grade
vacuous. This is the `ε`-collapsed shadow of the graded monad above. -/

section PMFDemo
variable {α₀ β₀ α₁ β₁ α₂ β₂ : Type}

/-- **3-hop exact coupling on `PMF`.** Three `Couples` leaves compose to a `Couples` of the
bound programs via `relBind_spec` (= `Couples_bind`), the relation `R₂` carried through;
the grade is vacuous (`PMF`'s `liftR` ignores `ε`). The spec-monad bind is here `XRelatorPMF`'s
coupling bind. -/
theorem relDemo3_pmf
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {m₁ : PMF α₀} {m₂ : PMF β₀}
    {k₁ : α₀ → PMF α₁} {k₂ : β₀ → PMF β₁}
    {l₁ : α₁ → PMF α₂} {l₂ : β₁ → PMF β₂}
    (h₁ : Couples m₁ m₂ R₀)
    (h₂ : ∀ a b, R₀ a b → Couples (k₁ a) (k₂ b) R₁)
    (h₃ : ∀ a b, R₁ a b → Couples (l₁ a) (l₂ b) R₂) :
    Couples (PMF.bind (PMF.bind m₁ k₁) l₁) (PMF.bind (PMF.bind m₂ k₂) l₂) R₂ :=
  relSpec3_auto (T := PMF) (ε₁ := 0) (ε₂ := 0) (ε₃ := 0) h₁ h₂ h₃

end PMFDemo

end CatCrypt.XDijkstra
