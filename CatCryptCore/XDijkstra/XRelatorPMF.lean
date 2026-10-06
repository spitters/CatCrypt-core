/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Distributions.Uniform
public import CatCryptCore.XDijkstra.XPostShape


@[expose] public section
set_option autoImplicit false

/-!
# `T̂`: the probabilistic relational lifting (coupling monad) at `PMF`

This is **Phase 3** of the extended-PostShape Dijkstra framework
(`XPostShape.lean`). Phase 1 gave the relational axis its *deterministic*
witness: `xprod t₁ t₂` runs two transformers **independently** and pairs the
results, and `xrel_seq` closes the relational sequencing rule over that
independent product. That is exactly the right object on the deterministic
fragment — but the independent product of two *random* programs is **not** a
coupling. A relational judgment such as

```
x ← unif; y ← unif; assume x = y
```

is only witnessed by a **joint** distribution whose two marginals are the two
sampling distributions and whose support lies on the relation (`x = y`). The
independent product `μ ⊗ ν` puts mass on every `(x, y)`, so it can never live on
the diagonal. Phase 3 supplies the missing object: the **relational lifting**
`T̂ R`, the set of couplings, here made concrete at Mathlib's probability monad
`PMF`.

## What this module proves

* `IsCoupling μ ν R κ` — `κ : PMF (α × β)` is a coupling of `μ` and `ν` for `R`:
  its two marginals are `μ`/`ν` and its support lies on `R`.
* `Couples μ ν R := ∃ κ, IsCoupling μ ν R κ` — the relational lifting `T̂ R` at
  `PMF` (existence of a witnessing coupling).
* `Couples_pure` / `Couples_bind` — the monad-compatibility of the relator: the
  coupling `return` and the coupling `bind`. `Couples_bind` is the heart of pRHL
  — it composes a coupling of the prefixes with pointwise couplings of the
  continuations, using `PMF.bindOnSupport` to pick a sub-coupling exactly where
  the prefix coupling has mass (i.e. where `R` holds).
* `Couples_same μ : Couples μ μ (· = ·)` — the **diagonal** coupling
  `μ.map (fun a => (a, a))`: two identical samplings coupled to agree. This is
  the `x ← unif; y ← unif; assume x = y` witness the independent product cannot
  provide.
* `Couples_indep μ ν : Couples μ ν (fun _ _ => True)` — the **independent
  product** `indepProd` is a coupling, but only for the trivial relation `True`.
  This is the PMF-analogue of `xprod`: `xprod` = the trivial
  (independent) coupling; `T̂` (`Couples`) is its proper generalization, adding
  the marginal-and-support discipline the independent product lacks.
* `XRelTriplePMF` / `XRelTriplePMF_seq` — the probabilistic relational Hoare
  triple whose post-relation is established by a coupling, and its sequencing
  rule. This is `xrel_seq` (Phase 1's deterministic relational sequencing) lifted
  from the deterministic product to the coupling `bind`.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal

variable {α β γ α' β' : Type*}

/-! ## 1. The coupling relation — `T̂ R` at `PMF`

`IsCoupling μ ν R κ` says the joint distribution `κ` on `α × β` witnesses the
relational lifting `T̂ R` between `μ` and `ν`: pushing `κ` forward along the two
projections recovers the marginals `μ` and `ν`, and every point in `κ`'s support
is related by `R`. `Couples μ ν R` is the existential — the relational lifting
proper. -/

/-- `κ : PMF (α × β)` is a **coupling** of `μ` and `ν` for the relation `R`: its
first marginal is `μ`, its second marginal is `ν`, and its support lies on `R`. -/
structure IsCoupling (μ : PMF α) (ν : PMF β) (R : α → β → Prop) (κ : PMF (α × β)) :
    Prop where
  /-- The first marginal of `κ` is `μ`. -/
  marg_fst : κ.map Prod.fst = μ
  /-- The second marginal of `κ` is `ν`. -/
  marg_snd : κ.map Prod.snd = ν
  /-- `κ` is supported on the relation `R`. -/
  supp : ∀ p ∈ κ.support, R p.1 p.2

/-- **The relational lifting `T̂ R` at `PMF`.** `Couples μ ν R` holds iff there is
a coupling of `μ` and `ν` for `R`. -/
def Couples (μ : PMF α) (ν : PMF β) (R : α → β → Prop) : Prop :=
  ∃ κ, IsCoupling μ ν R κ

/-! ## 2. A `map`-through-`bindOnSupport` helper

The coupling `bind` (`Couples_bind`) binds the prefix coupling `κ` with a
*partial* continuation defined only where `κ` has mass (`bindOnSupport`); its
marginals are computed by pushing `Prod.fst`/`Prod.snd` through that partial
bind. This helper commutes `map` past `bindOnSupport`, the one PMF identity not
already in Mathlib in this shape. -/

/-- `map` commutes with `bindOnSupport`: pushing `g` through the partial bind maps
each partial branch. Proved by re-expressing `map` as `bind (pure ∘ ·)`,
converting to `bindOnSupport`, and applying `bindOnSupport_bindOnSupport`. -/
theorem map_bindOnSupport {p : PMF α} (f : ∀ a ∈ p.support, PMF β) (g : β → γ) :
    (p.bindOnSupport f).map g = p.bindOnSupport (fun a ha => (f a ha).map g) := by
  simp only [← PMF.bind_pure_comp]
  rw [← PMF.bindOnSupport_eq_bind (p.bindOnSupport f) (PMF.pure ∘ g),
    PMF.bindOnSupport_bindOnSupport]
  simp only [PMF.bindOnSupport_eq_bind]

/-! ## 3. Lifting laws — the coupling monad

`Couples_pure` and `Couples_bind` are the `return` and `bind` of the relational
lifting. `Couples_pure` is the diagonal `pure (a, b)`. `Couples_bind` is the
substantive one: given a coupling `κ` of the prefixes and, at every related
prefix pair, a coupling of the continuations, the witness is
`κ.bindOnSupport k` — bind the prefix coupling with the sub-coupling chosen at
each in-support (hence `R`-related) pair. Its marginals reduce to `μ.bind f` and
`ν.bind g` by pushing the projections through, and its support inherits `S` from
the sub-couplings. -/

/-- **Coupling `return`.** Related points lift to the diagonal coupling
`pure (a, b)`. -/
theorem Couples_pure {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    Couples (PMF.pure a) (PMF.pure b) R := by
  refine ⟨PMF.pure (a, b), ?_, ?_, ?_⟩
  · rw [PMF.pure_map]
  · rw [PMF.pure_map]
  · intro q hq
    rw [PMF.mem_support_pure_iff] at hq
    subst hq
    exact hab

/-- **Coupling `bind` — the heart of pRHL.** From a coupling of the prefixes `μ`,
`ν` for `R`, and, for every `R`-related pair `(a, b)`, a coupling of the
continuations `f a`, `g b` for `S`, obtain a coupling of `μ.bind f` and
`ν.bind g` for `S`. The witness binds the prefix coupling with the pointwise
sub-couplings via `bindOnSupport` (the sub-coupling is chosen exactly where the
prefix coupling has mass, where `R` holds). -/
theorem Couples_bind {μ : PMF α} {ν : PMF β} {R : α → β → Prop}
    {f : α → PMF α'} {g : β → PMF β'} {S : α' → β' → Prop}
    (h : Couples μ ν R)
    (hf : ∀ a b, R a b → Couples (f a) (g b) S) :
    Couples (μ.bind f) (ν.bind g) S := by
  obtain ⟨κ, hκ⟩ := h
  -- At each in-support pair `p` (where `R p.1 p.2` holds), pick a sub-coupling.
  set k : ∀ p ∈ κ.support, PMF (α' × β') :=
    fun p hp => (hf p.1 p.2 (hκ.supp p hp)).choose with hk
  have hkspec : ∀ p (hp : p ∈ κ.support),
      IsCoupling (f p.1) (g p.2) S (k p hp) :=
    fun p hp => (hf p.1 p.2 (hκ.supp p hp)).choose_spec
  refine ⟨κ.bindOnSupport k, ?_, ?_, ?_⟩
  · -- first marginal: `(κ.bindOnSupport k).map Prod.fst = μ.bind f`
    rw [map_bindOnSupport]
    have hfun : κ.bindOnSupport (fun p hp => (k p hp).map Prod.fst)
        = κ.bindOnSupport (fun (p : α × β) (_ : p ∈ κ.support) => f p.1) := by
      congr 1; funext p; funext hp; exact (hkspec p hp).marg_fst
    rw [hfun, PMF.bindOnSupport_eq_bind, ← hκ.marg_fst, PMF.bind_map]
    rfl
  · -- second marginal: `(κ.bindOnSupport k).map Prod.snd = ν.bind g`
    rw [map_bindOnSupport]
    have hfun : κ.bindOnSupport (fun p hp => (k p hp).map Prod.snd)
        = κ.bindOnSupport (fun (p : α × β) (_ : p ∈ κ.support) => g p.2) := by
      congr 1; funext p; funext hp; exact (hkspec p hp).marg_snd
    rw [hfun, PMF.bindOnSupport_eq_bind, ← hκ.marg_snd, PMF.bind_map]
    rfl
  · -- support: every point of the composed coupling is `S`-related
    intro q hq
    rw [PMF.mem_support_bindOnSupport_iff] at hq
    obtain ⟨p, hp, hqp⟩ := hq
    exact (hkspec p hp).supp q hqp

/-! ## 4. The diagonal (sampling) coupling

`Couples_same` is the coupling witnessing that two *identical* samplings can be
coupled to agree: the diagonal `μ.map (fun a => (a, a))` has both marginals `μ`
and lives entirely on the diagonal `{(a, a)}`. This is the
`x ← unif; y ← unif; assume x = y` case — impossible for the independent
product, immediate for `T̂`. -/

/-- **The diagonal coupling.** Two identical samplings from `μ` are coupled to
agree: `μ.map (fun a => (a, a))` couples `μ` with `μ` for equality. -/
theorem Couples_same (μ : PMF α) : Couples μ μ (· = ·) := by
  refine ⟨μ.map (fun a => (a, a)), ?_, ?_, ?_⟩
  · rw [PMF.map_comp]; show μ.map id = μ; rw [PMF.map_id]
  · rw [PMF.map_comp]; show μ.map id = μ; rw [PMF.map_id]
  · intro q hq
    rw [PMF.mem_support_map_iff] at hq
    obtain ⟨a, _, ha⟩ := hq
    subst ha
    rfl

/-! ## 5. The independent product — `xprod` as the trivial coupling

`indepProd μ ν = μ.bind (fun a => ν.map (a, ·))` is the ordinary product
distribution: sample `a` from `μ`, then `b` from `ν`, independently. It is *a*
coupling — but only for the trivial relation `True` (`Couples_indep`). This is
precisely the probabilistic shadow of `xprod`, which sequences two
transformers **independently**. `T̂` (`Couples`) generalizes it: for any
non-trivial `R` (e.g. the diagonal), a proper coupling is needed, and the
independent product does not supply one. -/

/-- **The independent product** of two distributions: sample the two components
independently and pair them. The `PMF` analogue of `xprod`. -/
noncomputable def indepProd (μ : PMF α) (ν : PMF β) : PMF (α × β) :=
  μ.bind (fun a => ν.map (fun b => (a, b)))

/-- **The independent product is the trivial coupling.** `indepProd μ ν` couples
`μ` and `ν` for the trivial relation `fun _ _ => True`. It is *not* a coupling
for a non-trivial relation in general — that is the gap `T̂` fills, and the
sense in which `xprod` (independent product) is the trivial instance of the
relational lifting. -/
theorem Couples_indep (μ : PMF α) (ν : PMF β) :
    Couples μ ν (fun _ _ => True) := by
  refine ⟨indepProd μ ν, ?_, ?_, fun _ _ => trivial⟩
  · -- first marginal collapses to `μ` (the second sample is projected away)
    rw [indepProd, PMF.map_bind]
    have key : (fun a => (ν.map (fun b => (a, b))).map Prod.fst)
        = (fun a : α => (PMF.pure a : PMF α)) := by
      funext a
      rw [PMF.map_comp]
      show ν.map (Function.const β a) = PMF.pure a
      exact PMF.map_const ν a
    rw [key, PMF.bind_pure]
  · -- second marginal collapses to `ν` (the first sample is a constant)
    rw [indepProd, PMF.map_bind]
    have key : (fun a => (ν.map (fun b => (a, b))).map Prod.snd)
        = (fun _ : α => ν) := by
      funext a
      rw [PMF.map_comp]
      show ν.map id = ν
      rw [PMF.map_id]
    rw [key, PMF.bind_const]

/-! ## 6. The probabilistic relational triple — extending `xrel_seq`

`XRelTriplePMF c₁ c₂ Φ Ψ` is the probabilistic relational Hoare judgment: for
inputs related by `Φ`, the two output distributions `c₁ i`, `c₂ j` are coupled by
a coupling supported on `Ψ`. Where `XRelTriple` uses the deterministic
independent product `xprod`, this uses `T̂` (`Couples`); `XRelTriplePMF_seq` is
the exact analogue of `xrel_seq`, threading through the coupling `bind`
(`Couples_bind`) instead of the deterministic product. -/

/-- **The probabilistic relational Hoare judgment.** For every pair of inputs
related by `Φ`, the two output distributions are coupled by `Ψ` (i.e. `T̂ Ψ`
holds between them). The `PMF` analogue of `XRelTriple`, with the
coupling lifting `T̂` in place of the independent product `xprod`. -/
def XRelTriplePMF {I J : Type*} (c₁ : I → PMF α) (c₂ : J → PMF β)
    (Φ : I → J → Prop) (Ψ : α → β → Prop) : Prop :=
  ∀ i j, Φ i j → Couples (c₁ i) (c₂ j) Ψ

/-- **The relational sequencing rule (probabilistic coupling).** From a triple on
the prefixes (`Φ ⟹ Rmid`) and, at every `Rmid`-related pair, a coupling of the
continuations (`Rmid ⟹ Ψ`), obtain a triple on the sequenced programs. This is
`xrel_seq` lifted from the deterministic product to the coupling `bind`
`Couples_bind`. -/
theorem XRelTriplePMF_seq {I J : Type*}
    {c₁ : I → PMF α} {c₂ : J → PMF β} {Φ : I → J → Prop} {Rmid : α → β → Prop}
    {f : α → PMF α'} {g : β → PMF β'} {Ψ : α' → β' → Prop}
    (h₁ : XRelTriplePMF c₁ c₂ Φ Rmid)
    (h₂ : ∀ a b, Rmid a b → Couples (f a) (g b) Ψ) :
    XRelTriplePMF (fun i => (c₁ i).bind f) (fun j => (c₂ j).bind g) Φ Ψ :=
  fun i j hij => Couples_bind (h₁ i j hij) h₂

/-! ## 7. Worked demo — the sampling coupling `x ← unif; y ← unif; assume x = y`

Two fair-coin samplings, coupled to agree. The independent product would spread
mass over `(false, true)` and `(true, false)`; the diagonal coupling
(`Couples_same`) lives on `{(false, false), (true, true)}`, so the post-relation
`x = y` holds with probability one. This is the concrete `T̂` witness for the case,
which the independent product `xprod` does not provide. -/

/-- **Demo (sampling coupling).** A fair coin coupled with itself to agree:
`Couples unif unif (· = ·)` via the diagonal coupling. This is the
`x ← unif; y ← unif; assume x = y` case made concrete. -/
theorem demo_coin_coupling :
    Couples (PMF.uniformOfFintype Bool) (PMF.uniformOfFintype Bool) (· = ·) :=
  Couples_same _

end CatCrypt.XDijkstra
