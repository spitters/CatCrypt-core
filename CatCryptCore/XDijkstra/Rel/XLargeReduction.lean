/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.Rel.XRelSpecMonad
public import CatCryptCore.XDijkstra.Rel.XHybridExample


@[expose] public section
set_option autoImplicit false

/-!
# `XLargeReduction`: the coupling-spec-monad on a larger (5+ hop, general-`n`) reduction

The relational coupling-spec-monad of `XRelSpecMonad.lean` (`RelPT`, `relBind`, and its
crux law `relBind_spec = RelQ0.liftR_bind`) applied to a multi-hop reduction on the
crypto sub-distribution monad `SDistr`, beyond the 3-hop demonstrator `relSpec3_auto`.
The couplings compose through the spec-monad bind — the grade sums in the `RelPT` type
index and the post-relation is carried — with no separate transitivity or `xseq`
grade-bookkeeping pass. One nested `relBind_spec` at three hops is one nested
`relBind_spec` at five, and one `induction` at arbitrary `n`.

## What this module provides

* **`relSpec5_auto` / `large5_reduction`** — a five-hop coupled reduction (a prefix and four
  relational Kleisli continuations, each hop a coupling leaf at its *own* per-hop relation
  `Rᵢ` and advantage `εᵢ`) composed by four nested `relSpec_seq` into a single triple at the
  summed grade `((((ε₁+ε₂)+ε₃)+ε₄)+ε₅)` carrying the final relation `R₄` — modelled on a
  multi-query `PRF`/`IND-CPA` hybrid where each hop replaces one oracle query's output.
  `relDemo5_sdistr` lands it on `SDistr`.

* **`largeN_reduction_uniform` and `largeN_reduction_varying`** — the general-`n` chain, the
  arbitrary-length reduction that is painful to compose by hand. Here it is one `induction`
  over `relSpec_seq`: the `n`-fold Kleisli iterate `iterK`/`iterKV` composes to a triple at
  grade `ε₀ + n • ε` (uniform hops) or `ε₀ + ∑_{i<n} εᵢ` (varying per-hop advantages), the
  invariant relation `R` carried through every hop.

* **Library tie-in.** `SDistr.uniform (Fin 256)` — a uniform random byte — with the proven
  reflexive coupling `xrelQ0_refl_eq` (from `XHybridExample`) instantiates one concrete hop
  of the abstract chains: `resampleHybrid_bound` is the general-`n` re-randomisation hybrid
  built from the sampler, and `large5_reduction_real` plants the uniform leaf as the prefix
  of the five-hop chain. The composition touches an `SDistr` library object, not only
  abstract games `Gᵢ`.

The remaining hops of the five-hop chain are stand-ins (opaque games at per-hop relations)
for a named multi-query hybrid; porting a specific protocol's concrete game sequence into
these leaves is the follow-on. This module establishes the composition mechanism, on the
concrete monad, at scale.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt CatCrypt.Prob

variable {T : Type → Type} [RelQ0 T]

/-! ## 1. A five-hop coupled reduction — couplings compose automatically at grade sum

A multi-query hybrid: a prefix `⟨m₁, m₂⟩` and four relational Kleisli continuations, each
hop a coupling leaf at its own per-hop relation `Rᵢ` and advantage `εᵢ` (the per-hop
primitive-security assumption of a reduction). The five hops compose to a *single*
coupling of the fourfold-bound programs at the summed grade `((((ε₁+ε₂)+ε₃)+ε₄)+ε₅)`,
carrying the final relation `R₄` — four nested `relSpec_seq`, nothing else. This is
`relSpec3_auto` scaled from three hops to five, with different per-hop relations.
-/

section FiveHop
variable {α₀ β₀ α₁ β₁ α₂ β₂ α₃ β₃ α₄ β₄ : Type}

/-- **Five coupled hops compose automatically (generic `RelQ0`).** The couplings glue via
`relSpec_seq = relBind_spec = RelQ0.liftR_bind`; the grade sums to `((((ε₁+ε₂)+ε₃)+ε₄)+ε₅)`
in the spec of the fourfold-bound pair, carrying the final relation `R₄`. The proof is four
nested `relSpec_seq`; there is no separate grade-accumulation or transitivity pass. -/
theorem relSpec5_auto {ε₁ ε₂ ε₃ ε₄ ε₅ : ℝ≥0∞}
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {R₃ : α₃ → β₃ → Prop} {R₄ : α₄ → β₄ → Prop}
    {m₁ : T α₀} {m₂ : T β₀}
    {k₁ : α₀ → T α₁} {k₂ : β₀ → T β₁}
    {l₁ : α₁ → T α₂} {l₂ : β₁ → T β₂}
    {p₁ : α₂ → T α₃} {p₂ : β₂ → T β₃}
    {q₁ : α₃ → T α₄} {q₂ : β₃ → T β₄}
    (h₁ : RelSpecTriple ε₁ R₀ m₁ m₂)
    (h₂ : ∀ a b, R₀ a b → RelSpecTriple ε₂ R₁ (k₁ a) (k₂ b))
    (h₃ : ∀ a b, R₁ a b → RelSpecTriple ε₃ R₂ (l₁ a) (l₂ b))
    (h₄ : ∀ a b, R₂ a b → RelSpecTriple ε₄ R₃ (p₁ a) (p₂ b))
    (h₅ : ∀ a b, R₃ a b → RelSpecTriple ε₅ R₄ (q₁ a) (q₂ b)) :
    RelSpecTriple (T := T) ((((ε₁ + ε₂) + ε₃) + ε₄) + ε₅) R₄
      (RelQ0.bind' (RelQ0.bind' (RelQ0.bind' (RelQ0.bind' m₁ k₁) l₁) p₁) q₁)
      (RelQ0.bind' (RelQ0.bind' (RelQ0.bind' (RelQ0.bind' m₂ k₂) l₂) p₂) q₂) :=
  relSpec_seq (relSpec_seq (relSpec_seq (relSpec_seq h₁ h₂) h₃) h₄) h₅

/-- The same five-hop composition read as a spec of the fourfold-`relBind`'d pair: the grade
`((((ε₁+ε₂)+ε₃)+ε₄)+ε₅)` is the type index of the composed `RelPT`, produced by the four
`relBind`s — the grade sum lives in the object. -/
theorem large5_reduction {ε₁ ε₂ ε₃ ε₄ ε₅ : ℝ≥0∞}
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {R₃ : α₃ → β₃ → Prop} {R₄ : α₄ → β₄ → Prop}
    {m₁ : T α₀} {m₂ : T β₀}
    {k₁ : α₀ → T α₁} {k₂ : β₀ → T β₁}
    {l₁ : α₁ → T α₂} {l₂ : β₁ → T β₂}
    {p₁ : α₂ → T α₃} {p₂ : β₂ → T β₃}
    {q₁ : α₃ → T α₄} {q₂ : β₃ → T β₄}
    (h₁ : RelSpecTriple ε₁ R₀ m₁ m₂)
    (h₂ : ∀ a b, R₀ a b → RelSpecTriple ε₂ R₁ (k₁ a) (k₂ b))
    (h₃ : ∀ a b, R₁ a b → RelSpecTriple ε₃ R₂ (l₁ a) (l₂ b))
    (h₄ : ∀ a b, R₂ a b → RelSpecTriple ε₄ R₃ (p₁ a) (p₂ b))
    (h₅ : ∀ a b, R₃ a b → RelSpecTriple ε₅ R₄ (q₁ a) (q₂ b)) :
    RelSpec
      (relBind (T := T) (δ := ε₅)
        (relBind (δ := ε₄)
          (relBind (δ := ε₃)
            (relBind (δ := ε₂) (⟨m₁, m₂⟩ : RelPT (T := T) ε₁ α₀ β₀) k₁ k₂) l₁ l₂) p₁ p₂)
        q₁ q₂) R₄ :=
  relBind_spec (relBind_spec (relBind_spec (relBind_spec h₁ h₂) h₃) h₄) h₅

end FiveHop

/-! ### The crypto witness: 5-hop composition on `SDistr`

Instantiated at `SDistr` (the `ε`-approximate sub-coupling `liftRApprox`), the five-hop
chain lands in `XRelTripleQ0 (T := SDistr) (ε₁+ε₂+ε₃+ε₄+ε₅)` — the end-to-end coupling of
a five-step reduction, grades summed and relation carried, from the five per-hop leaves
alone. -/

section SDistrFiveHop
variable {α₀ β₀ α₁ β₁ α₂ β₂ α₃ β₃ α₄ β₄ : Type}

/-- **5-hop coupling on the crypto monad `SDistr`.** Five coupled hops compose
to the end-to-end coupling `XRelTripleQ0 (ε₁+ε₂+ε₃+ε₄+ε₅)` of the fourfold-bound programs,
the couplings gluing via `relSpec_seq` and the advantages summing in the index.
-/
theorem relDemo5_sdistr {ε₁ ε₂ ε₃ ε₄ ε₅ : ℝ≥0∞}
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {R₃ : α₃ → β₃ → Prop} {R₄ : α₄ → β₄ → Prop}
    {m₁ : SDistr α₀} {m₂ : SDistr β₀}
    {k₁ : α₀ → SDistr α₁} {k₂ : β₀ → SDistr β₁}
    {l₁ : α₁ → SDistr α₂} {l₂ : β₁ → SDistr β₂}
    {p₁ : α₂ → SDistr α₃} {p₂ : β₂ → SDistr β₃}
    {q₁ : α₃ → SDistr α₄} {q₂ : β₃ → SDistr β₄}
    (h₁ : XRelTripleQ0 (T := SDistr) ε₁ R₀ m₁ m₂)
    (h₂ : ∀ a b, R₀ a b → XRelTripleQ0 (T := SDistr) ε₂ R₁ (k₁ a) (k₂ b))
    (h₃ : ∀ a b, R₁ a b → XRelTripleQ0 (T := SDistr) ε₃ R₂ (l₁ a) (l₂ b))
    (h₄ : ∀ a b, R₂ a b → XRelTripleQ0 (T := SDistr) ε₄ R₃ (p₁ a) (p₂ b))
    (h₅ : ∀ a b, R₃ a b → XRelTripleQ0 (T := SDistr) ε₅ R₄ (q₁ a) (q₂ b)) :
    XRelTripleQ0 (T := SDistr) ((((ε₁ + ε₂) + ε₃) + ε₄) + ε₅) R₄
      (RelQ0.bind' (RelQ0.bind' (RelQ0.bind' (RelQ0.bind' m₁ k₁) l₁) p₁) q₁)
      (RelQ0.bind' (RelQ0.bind' (RelQ0.bind' (RelQ0.bind' m₂ k₂) l₂) p₂) q₂) :=
  relSpec5_auto (T := SDistr) h₁ h₂ h₃ h₄ h₅

end SDistrFiveHop

/-! ## 2. General-`n` reduction — the scaling win

An arbitrary-length hybrid, composed by a single `induction` over `relSpec_seq` rather than
`n` hand-written transitivity steps. `iterK`/`iterKV` are the `n`-fold left-nested Kleisli
iterates (append one step on the outside); the coupling of the whole iterate is proved by
induction, the grade accumulating in the index — `ε₀ + n • ε` for uniform hops,
`ε₀ + ∑_{i<n} εᵢ` for varying per-hop advantages. The relation `R` is a hop invariant,
carried through every step. -/

section GeneralN
variable {α : Type}

/-- **Uniform `n`-fold Kleisli iterate.** `iterK k m n` applies the step `k` `n` times,
left-nested: `iterK k m (n+1) = bind (iterK k m n) k`. -/
def iterK (k : α → T α) (m : T α) : ℕ → T α
  | 0 => m
  | n + 1 => RelQ0.bind' (iterK k m n) k

@[simp] theorem iterK_zero (k : α → T α) (m : T α) : iterK k m 0 = m := rfl

@[simp] theorem iterK_succ (k : α → T α) (m : T α) (n : ℕ) :
    iterK k m (n + 1) = RelQ0.bind' (iterK k m n) k := rfl

/-- **General-`n` uniform-hop reduction — one induction.** From a base coupling at `ε₀` and a
single per-hop coupling at `ε` that preserves the invariant relation `R`, the `n`-fold
iterate is coupled at grade `ε₀ + n • ε`, carrying `R`. The whole arbitrary-length
composition is the successor step `relSpec_seq _ hstep`; the grade `n • ε` accumulates in
the index (`succ_nsmul`). -/
theorem largeN_reduction_uniform {ε₀ ε : ℝ≥0∞} {R : α → α → Prop}
    {m₁ m₂ : T α} {k₁ k₂ : α → T α}
    (hbase : RelSpecTriple ε₀ R m₁ m₂)
    (hstep : ∀ a b, R a b → RelSpecTriple ε R (k₁ a) (k₂ b)) :
    ∀ n, RelSpecTriple (T := T) (ε₀ + n • ε) R (iterK k₁ m₁ n) (iterK k₂ m₂ n)
  | 0 => by simpa using hbase
  | n + 1 => by
      have hcomp := relSpec_seq (largeN_reduction_uniform hbase hstep n) hstep
      have hgrade : ε₀ + (n + 1) • ε = (ε₀ + n • ε) + ε := by
        rw [succ_nsmul, add_assoc]
      rw [iterK_succ, iterK_succ, hgrade]
      exact hcomp

/-- **Varying `n`-fold Kleisli iterate.** `iterKV k m n` applies step `k i` at level `i`. -/
def iterKV (k : ℕ → α → T α) (m : T α) : ℕ → T α
  | 0 => m
  | n + 1 => RelQ0.bind' (iterKV k m n) (k n)

@[simp] theorem iterKV_zero (k : ℕ → α → T α) (m : T α) : iterKV k m 0 = m := rfl

@[simp] theorem iterKV_succ (k : ℕ → α → T α) (m : T α) (n : ℕ) :
    iterKV k m (n + 1) = RelQ0.bind' (iterKV k m n) (k n) := rfl

/-- **General-`n` reduction with varying per-hop advantages — one induction.** Each hop `i`
has its own advantage `ε i` (and its own step `k · i`), preserving the invariant relation
`R`. The `n`-fold iterate is coupled at grade `ε₀ + ∑_{i<n} ε i`, carrying `R`. The grade is
a `Finset.range` sum accumulated by `Finset.sum_range_succ` at each successor step — the
varying-`εᵢ` fold is no harder than the uniform one. -/
theorem largeN_reduction_varying {ε₀ : ℝ≥0∞} {ε : ℕ → ℝ≥0∞} {R : α → α → Prop}
    {m₁ m₂ : T α} {k₁ k₂ : ℕ → α → T α}
    (hbase : RelSpecTriple ε₀ R m₁ m₂)
    (hstep : ∀ i a b, R a b → RelSpecTriple (ε i) R (k₁ i a) (k₂ i b)) :
    ∀ n, RelSpecTriple (T := T) (ε₀ + ∑ i ∈ Finset.range n, ε i) R
        (iterKV k₁ m₁ n) (iterKV k₂ m₂ n)
  | 0 => by simpa using hbase
  | n + 1 => by
      have hcomp := relSpec_seq (largeN_reduction_varying hbase hstep n) (hstep n)
      have hgrade : ε₀ + ∑ i ∈ Finset.range (n + 1), ε i
          = (ε₀ + ∑ i ∈ Finset.range n, ε i) + ε n := by
        rw [Finset.sum_range_succ, add_assoc]
      rw [iterKV_succ, iterKV_succ, hgrade]
      exact hcomp

end GeneralN

/-! ## 3. Real-library tie-in: the uniform sampler `SDistr.uniform (Fin 256)`

The abstract chains above are instantiated on an `SDistr` library object: a uniform
random byte `SDistr.uniform (Fin 256)` — with the proven reflexive coupling
`xrelQ0_refl_eq` supplying every leaf. The coupling of the uniform sampler with itself is
the library lemma `liftRApprox_refl_eq`, discharged by the min-diagonal witness
(`tvMargin_self`). -/

section RealTieIn

/-- A concrete cryptographic step: **re-sample a fresh uniform byte**, ignoring the
previous value — the rerandomisation step at the heart of a `PRG`/`PRF` hybrid. An
`SDistr` program built from the library sampler `SDistr.uniform (Fin 256)`. -/
noncomputable def resampleByte : Fin 256 → SDistr (Fin 256) :=
  fun _ => SDistr.uniform (Fin 256)

/-- Each re-sampling hop is an error-`0` coupling on `SDistr`: both sides are the
identical uniform sampler, so `xrelQ0_refl_eq` (a proven library lemma) couples them at `Eq`. -/
theorem resampleByte_coupled (a b : Fin 256) (_h : a = b) :
    XRelTripleQ0 (T := SDistr) 0 Eq (resampleByte a) (resampleByte b) :=
  xrelQ0_refl_eq (SDistr.uniform (Fin 256))

/-- **The `n`-fold re-randomisation hybrid on the uniform sampler.** `largeN` at the
library leaf: the `n`-fold iterate of `resampleByte` from a uniform-byte base is coupled to
itself at grade `0 + n • 0 = 0`, the relation `Eq` carried through all `n` hops. Every hop is
the library coupling `xrelQ0_refl_eq (SDistr.uniform (Fin 256))`; the whole chain is
built from an `SDistr` object, composed by the one induction of `largeN_reduction_uniform`.
-/
theorem resampleHybrid_bound (n : ℕ) :
    XRelTripleQ0 (T := SDistr) (0 + n • 0) Eq
      (iterK resampleByte (SDistr.uniform (Fin 256)) n)
      (iterK resampleByte (SDistr.uniform (Fin 256)) n) :=
  largeN_reduction_uniform (T := SDistr)
    (xrelQ0_refl_eq (SDistr.uniform (Fin 256)))
    (fun a b h => resampleByte_coupled a b h) n

/-- **The uniform leaf planted as the prefix of a five-hop chain.** Hop 1 is the
library coupling of `SDistr.uniform (Fin 256)` with itself (advantage `0`, relation `Eq`);
hops 2–5 are abstract game leaves at their own per-hop relations and advantages. The five
compose to the end-to-end coupling at grade `((((0+ε₂)+ε₃)+ε₄)+ε₅)`, carrying `R₄` — a
five-hop reduction whose first leaf touches an `SDistr` object. -/
theorem large5_reduction_real {α₂ β₂ α₃ β₃ α₄ β₄ : Type}
    {ε₂ ε₃ ε₄ ε₅ : ℝ≥0∞}
    {R₂ : α₂ → β₂ → Prop} {R₃ : α₃ → β₃ → Prop} {R₄ : α₄ → β₄ → Prop}
    {k₁ : Fin 256 → SDistr (Fin 256)} {k₂ : Fin 256 → SDistr (Fin 256)}
    {l₁ : Fin 256 → SDistr α₂} {l₂ : Fin 256 → SDistr β₂}
    {p₁ : α₂ → SDistr α₃} {p₂ : β₂ → SDistr β₃}
    {q₁ : α₃ → SDistr α₄} {q₂ : β₃ → SDistr β₄}
    (h₂ : ∀ a b, a = b → XRelTripleQ0 (T := SDistr) ε₂ Eq (k₁ a) (k₂ b))
    (h₃ : ∀ a b, Eq a b → XRelTripleQ0 (T := SDistr) ε₃ R₂ (l₁ a) (l₂ b))
    (h₄ : ∀ a b, R₂ a b → XRelTripleQ0 (T := SDistr) ε₄ R₃ (p₁ a) (p₂ b))
    (h₅ : ∀ a b, R₃ a b → XRelTripleQ0 (T := SDistr) ε₅ R₄ (q₁ a) (q₂ b)) :
    XRelTripleQ0 (T := SDistr) ((((0 + ε₂) + ε₃) + ε₄) + ε₅) R₄
      (RelQ0.bind' (RelQ0.bind'
        (RelQ0.bind' (RelQ0.bind' (SDistr.uniform (Fin 256)) k₁) l₁) p₁) q₁)
      (RelQ0.bind' (RelQ0.bind'
        (RelQ0.bind' (RelQ0.bind' (SDistr.uniform (Fin 256)) k₂) l₂) p₂) q₂) :=
  relDemo5_sdistr (xrelQ0_refl_eq (SDistr.uniform (Fin 256))) h₂ h₃ h₄ h₅

end RealTieIn

end CatCrypt.XDijkstra
