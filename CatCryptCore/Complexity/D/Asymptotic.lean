/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.TimeAdm
public import CatCryptCore.Complexity.D.Reflect
public import CatCryptCore.Crypto.ConcreteReductions

/-!
# Asymptotic security over D

A security-parameter family of arrows `A : ∀ n, Val (a n) → SPComp (Val (b n))` is
polynomial-time (`PolyTimeFam O A`) when a polynomially bounded `p : ℕ → ℕ` (`IsPolyBound p`,
`p n ≤ c * (n + 1) ^ d`) bounds its members in the time class of D: `TimeAdm O (p n) (A n)`
for every `n`, each member realized by a closed D-term within `p n` steps. This is the class
of probabilistic polynomial-time adversaries over D. It is closed under the graded laws of
`TimeAdm`: `pure`, Kleisli composition and precomposition by a polynomial-time family.

## Hypotheses quantify over polynomial-time families

A hypothesis `∀ A, Adv A ≤ ε` on a computational game, with `A` ranging over all `SPComp`
arrows, is unsatisfiable: a Lean adversary is not bounded in time. Every asymptotic security
predicate of this module (`AsymSecure`, `UCTimeNegl`) quantifies over the families realized
by closed D-terms within a polynomial time bound only. The transfer theorems take a concrete
bound as their input and derive the asymptotic statement from it.

## Reductions

A time reduction (`TimeReduction`) maps the arrows of one game to those of another and sends
an arrow admissible at time `t` to one admissible at time `time t`. Precomposition and
postcomposition by an arrow admissible at time `s` are time reductions with
`time t = s + t + 3` (`TimeReduction.pre`, `TimeReduction.post`), and time reductions
compose (`TimeReduction.comp`). An open D-term with the adversary as a free variable, whose cost
is at most `time k` when each call of the adversary costs at most `k`, is a time reduction of
time `t + 2 + time t` (`TimeReduction.ofOpen`).

The transfer theorem `polyTime_transfer` takes a concrete reduction: for every adversary `A`
and every `n`, `AdvP n A ≤ Σ_{i < k n} AdvQ n (B n i A) + ε n`, each `B n i` a time reduction
whose time is at most `Q (n + t)` at input time `t` for one polynomially bounded `Q`. For a
polynomial-time family `A` the reduced families `B n i (A n)` are polynomial-time, uniformly
in `i`. Its corollary `asymSecure_of_reduction`: when `k` is polynomially bounded and
positive and `ε` is negligible, asymptotic security of the primitive game gives asymptotic
security of the protocol game.

## The computational UC level

`UCTimeNegl O f g` states that `ucCdistTime O (p n) (f n) (g n)` is negligible in `n` for
every polynomially bounded `p`: the families are indistinguishable by polynomial-time
distinguishers of D. It is reflexive, symmetric and transitive, follows from a negligible
statistical distance, and is preserved by pre-composition and by post-composition with a
polynomial-time family. At first-order result types it is equivalent to the asymptotic
security of the distinguishing game (`ucTimeNegl_iff_asymSecure`): the supremum over the
distinguishers at each `n` is negligible exactly when every polynomial-time family of
distinguishers has negligible advantage.

## Worked instance

`addTwo` (`x + 1 + 1` on bytes) is reflected into D by `reflect_d`; `TimeRealizer.ofBody`
turns its D-term into a realizer at time `3`. Post-processing two families of byte
computations by `addTwo` is a protocol game whose distinguishing advantage reduces, by the
committed equality `spcomp_distComp_bind_right`, to the distinguishing advantage of the two
families at the precomposed distinguisher. `addTwo_asymSecure` carries this reduction
through `asymSecure_of_reduction`.

## Main definitions

* `IsPolyBound`, `PolyTimeFam`, `TimeReduction`, `AsymSecure`, `UCTimeNegl`.

## Main results

* `polyTimeFam_pure`, `PolyTimeFam.bind`, `PolyTimeFam.precomp`: closure of the class.
* `polyTime_transfer`, `asymSecure_of_reduction`: from concrete to asymptotic security.
* `UCTimeNegl.refl`, `UCTimeNegl.symm`, `UCTimeNegl.trans`, `UCTimeNegl.of_sdist`,
  `UCTimeNegl.comp_left`, `UCTimeNegl.comp_right`, `ucTimeNegl_iff_asymSecure`.
* `addTwo_asymSecure`: the worked instance.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core CatCrypt.Crypto UCMonad
open scoped ENNReal

/-! ## Polynomial bounds -/

/-- `p` is bounded by a polynomial: `p n ≤ c * (n + 1) ^ d` for all `n`. -/
def IsPolyBound (p : ℕ → ℕ) : Prop :=
  ∃ c d : ℕ, ∀ n, p n ≤ c * (n + 1) ^ d

theorem isPolyBound_const (m : ℕ) : IsPolyBound fun _ => m :=
  ⟨m, 0, fun n => by simp⟩

theorem isPolyBound_id : IsPolyBound fun n => n :=
  ⟨1, 1, fun n => by simp⟩

theorem IsPolyBound.of_le {p q : ℕ → ℕ} (hq : IsPolyBound q) (h : ∀ n, p n ≤ q n) :
    IsPolyBound p := by
  obtain ⟨c, d, hcd⟩ := hq
  exact ⟨c, d, fun n => (h n).trans (hcd n)⟩

theorem IsPolyBound.add {p q : ℕ → ℕ} (hp : IsPolyBound p) (hq : IsPolyBound q) :
    IsPolyBound fun n => p n + q n := by
  obtain ⟨c, d, hp⟩ := hp
  obtain ⟨c', d', hq⟩ := hq
  refine ⟨c + c', max d d', fun n => ?_⟩
  have h1 : (n + 1) ^ d ≤ (n + 1) ^ max d d' := by
    gcongr <;> omega
  have h2 : (n + 1) ^ d' ≤ (n + 1) ^ max d d' := by
    gcongr <;> omega
  have := hp n
  have := hq n
  nlinarith

theorem IsPolyBound.comp {p q : ℕ → ℕ} (hp : IsPolyBound p) (hq : IsPolyBound q) :
    IsPolyBound fun n => q (p n) := by
  obtain ⟨c, d, hp⟩ := hp
  obtain ⟨c', d', hq⟩ := hq
  refine ⟨c' * (c + 1) ^ d', d * d', fun n => ?_⟩
  have h1 : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have h2 : p n + 1 ≤ (c + 1) * (n + 1) ^ d := by
    have := hp n
    nlinarith
  calc q (p n) ≤ c' * (p n + 1) ^ d' := hq (p n)
    _ ≤ c' * ((c + 1) * (n + 1) ^ d) ^ d' := by gcongr
    _ = c' * (c + 1) ^ d' * (n + 1) ^ (d * d') := by
      rw [mul_pow, ← pow_mul]
      ring

/-! ## Negligible functions -/

/-- A polynomially bounded multiple of a negligible function is negligible. -/
theorem isNegligible_polyBound_mul {k : ℕ → ℕ} {f : ℕ → ℝ≥0∞} (hk : IsPolyBound k)
    (hf : IsNegligible f) : IsNegligible fun n => (k n : ℝ≥0∞) * f n := by
  obtain ⟨c, d, hcd⟩ := hk
  have h1 : IsNegligible fun n => (n : ℝ≥0∞) ^ d * f n :=
    isNegligible_poly_mul d (fun n => (n : ℝ≥0∞) ^ d) (fun _ => le_refl _) hf
  have h2 := isNegligible_mul_const h1 (c * 2 ^ d)
  refine isNegligible_of_le_eventually h2 ⟨1, fun n hn => ?_⟩
  have hk : k n ≤ c * 2 ^ d * n ^ d := by
    have h3 := hcd n
    have h4 : (n + 1) ^ d ≤ (2 * n) ^ d := by gcongr; omega
    rw [mul_pow] at h4
    nlinarith
  rw [← mul_assoc]
  gcongr
  exact_mod_cast hk

/-! ## Polynomial-time families -/

section Families

variable (O : CTree.Oracle)

/-- A security-parameter family of arrows is polynomial-time over D: a polynomially bounded
`p` bounds the time of each member, `TimeAdm O (p n) (A n)`. -/
def PolyTimeFam {a b : ℕ → Ty} (A : ∀ n, Val (a n) → SPComp (Val (b n))) : Prop :=
  ∃ p : ℕ → ℕ, IsPolyBound p ∧ ∀ n, TimeAdm O (p n) (A n)

variable {O}

theorem polyTimeFam_pure {a : ℕ → Ty} (ha : ∀ n, (a n).FO) :
    PolyTimeFam O (fun n (x : Val (a n)) => SPComp.pure x) :=
  ⟨fun _ => 1, isPolyBound_const 1, fun n => timeAdm_pure O (ha n)⟩

theorem PolyTimeFam.bind {a b c : ℕ → Ty} {A : ∀ n, Val (a n) → SPComp (Val (b n))}
    {G : ∀ n, Val (b n) → SPComp (Val (c n))} (hA : PolyTimeFam O A)
    (hG : PolyTimeFam O G) : PolyTimeFam O (fun n x => A n x >>= G n) := by
  obtain ⟨p, hp, hpA⟩ := hA
  obtain ⟨q, hq, hqG⟩ := hG
  exact ⟨fun n => p n + q n + 3, (hp.add hq).add (isPolyBound_const 3),
    fun n => timeAdm_bind (hpA n) (hqG n)⟩

theorem PolyTimeFam.precomp {a b c : ℕ → Ty} {φ : ∀ n, Val (a n) → Val (b n)}
    {G : ∀ n, Val (b n) → SPComp (Val (c n))}
    (hφ : PolyTimeFam O (fun n x => SPComp.pure (φ n x))) (hG : PolyTimeFam O G) :
    PolyTimeFam O (fun n => G n ∘ φ n) := by
  obtain ⟨p, hp, hpφ⟩ := hφ
  obtain ⟨q, hq, hqG⟩ := hG
  exact ⟨fun n => p n + q n + 3, (hp.add hq).add (isPolyBound_const 3),
    fun n => timeAdm_precomp (hpφ n) (hqG n)⟩

theorem PolyTimeFam.mono {a b : ℕ → Ty} {A : ∀ n, Val (a n) → SPComp (Val (b n))}
    {p : ℕ → ℕ} (hA : ∀ n, TimeAdm O (p n) (A n)) (hp : IsPolyBound p) :
    PolyTimeFam O A :=
  ⟨p, hp, hA⟩

end Families

/-! ## Time reductions -/

/-- A reduction from the arrows `Val a → SPComp (Val b)` of one game to the arrows
`Val c → SPComp (Val d)` of another, sending an arrow admissible at time `t` to one admissible
at time `time t`. -/
structure TimeReduction (O : CTree.Oracle) (a b c d : Ty) where
  /-- The reduction. -/
  red : (Val a → SPComp (Val b)) → (Val c → SPComp (Val d))
  /-- The time of the reduced arrow, as a function of the time of the input arrow. -/
  time : ℕ → ℕ
  adm : ∀ t A, TimeAdm O t A → TimeAdm O (time t) (red A)

namespace TimeReduction

variable {O : CTree.Oracle}

/-- Precomposition by an arrow `k` admissible at time `s`. -/
noncomputable def pre {a b c : Ty} {s : ℕ} (k : Val c → SPComp (Val a))
    (hk : TimeAdm O s k) : TimeReduction O a b c b where
  red A := fun x => k x >>= A
  time t := s + t + 3
  adm _ _ hA := timeAdm_bind hk hA

/-- Postcomposition by an arrow `k` admissible at time `s`. -/
noncomputable def post {a b d : Ty} {s : ℕ} (k : Val b → SPComp (Val d))
    (hk : TimeAdm O s k) : TimeReduction O a b a d where
  red A := fun x => A x >>= k
  time t := t + s + 3
  adm _ _ hA := timeAdm_bind hA hk

/-- The composite of two time reductions. -/
def comp {a b c d e f : Ty} (R₂ : TimeReduction O c d e f) (R₁ : TimeReduction O a b c d) :
    TimeReduction O a b e f where
  red A := R₂.red (R₁.red A)
  time t := R₂.time (R₁.time t)
  adm t A hA := R₂.adm _ _ (R₁.adm t A hA)

/-- A time reduction from an open D-term: `body` has the adversary as its outer variable and the
input as its inner one, its cost is at most `time k` when every call of the adversary costs at
most `k`, and its evaluation means `red A` when the adversary variable means `A`. The realizer of
`red A` is `letE r.term (lam body)` for a realizer `r` of `A`: its evaluation takes the steps of
`r.term` and one β-step, and its calls cost at most `time t`, so the reduced time is
`t + 2 + time t`. -/
noncomputable def ofOpen (O : CTree.Oracle) {a b c d : Ty}
    (hc : c.FO) (hd : d.FO) (body : Tm [c, .arr a b] d)
    (red : (Val a → SPComp (Val b)) → Val c → SPComp (Val d))
    (time : ℕ → ℕ) (htime : Monotone time)
    (hcost : ∀ (g : Val (.arr a b)) (k : ℕ), (∀ v, (g v).cost ≤ k) →
      ∀ u, body.cost ((Env.nil.cons g).cons u) ≤ time k)
    (hden : ∀ (A : Val a → SPComp (Val b)) (g : Val (.arr a b)), (∀ v, (g v).run O = A v) →
      ∀ u, (body.eval ((Env.nil.cons g).cons u)).run O = red A u) :
    TimeReduction O a b c d where
  red := red
  time t := t + 2 + time t
  adm t A hA := ⟨hc, hd, hA.2.2.elim fun r => ⟨{
    term := .letE r.term (.lam body)
    evalCost := r.evalCost + 1
    callCost := time t
    closure := fun u => body.eval ((Env.nil.cons r.closure).cons u)
    evals := by
      show (Tm.letE r.term (.lam body)).eval Env.nil = _
      rw [Tm.eval_letE, show r.term.eval Env.nil = _ from r.evals, stepN_tick_bind, stepN_add]
      rfl
    call_le := fun u =>
      (hcost r.closure r.callCost r.call_le u).trans (htime (by have := r.time_le; omega))
    time_le := by have := r.time_le; omega
    run_eq := hden A r.closure r.run_eq }⟩⟩

end TimeReduction

/-! ## Asymptotic security and the transfer theorem -/

section Transfer

variable (O : CTree.Oracle)

/-- Asymptotic security of a game with advantage `Adv`: every polynomial-time family over D
has negligible advantage. -/
def AsymSecure {a b : ℕ → Ty} (Adv : ∀ n, (Val (a n) → SPComp (Val (b n))) → ℝ≥0∞) :
    Prop :=
  ∀ A : ∀ n, Val (a n) → SPComp (Val (b n)), PolyTimeFam O A →
    IsNegligible fun n => Adv n (A n)

variable {O}

/-- From concrete to asymptotic security, the time half: under a concrete reduction to
`k n` primitive advantages through time reductions of polynomially bounded time, every
polynomial-time family `A` has its protocol advantage bounded by the primitive advantages of
families that are polynomial-time uniformly in the index `i`. -/
theorem polyTime_transfer {a b c d : ℕ → Ty}
    (AdvP : ∀ n, (Val (a n) → SPComp (Val (b n))) → ℝ≥0∞)
    (AdvQ : ∀ n, (Val (c n) → SPComp (Val (d n))) → ℝ≥0∞)
    (k : ℕ → ℕ) (B : ∀ n, Fin (k n) → TimeReduction O (a n) (b n) (c n) (d n))
    (ε : ℕ → ℝ≥0∞)
    (hconc : ∀ n A, AdvP n A ≤ ∑ i, AdvQ n ((B n i).red A) + ε n)
    (hB : ∃ Q : ℕ → ℕ, IsPolyBound Q ∧ ∀ n i t, (B n i).time t ≤ Q (n + t))
    (A : ∀ n, Val (a n) → SPComp (Val (b n))) (hA : PolyTimeFam O A) :
    ∃ p : ℕ → ℕ, IsPolyBound p ∧ (∀ n i, TimeAdm O (p n) ((B n i).red (A n))) ∧
      ∀ n, AdvP n (A n) ≤ ∑ i, AdvQ n ((B n i).red (A n)) + ε n := by
  obtain ⟨Q, hQ, hBQ⟩ := hB
  obtain ⟨p, hp, hpA⟩ := hA
  refine ⟨fun n => Q (n + p n), IsPolyBound.comp (IsPolyBound.add isPolyBound_id hp) hQ,
    fun n i => ?_,
    fun n => hconc n (A n)⟩
  exact ((B n i).adm _ _ (hpA n)).mono (hBQ n i _)

/-- From concrete to asymptotic security: under a concrete reduction to `k n` primitive
advantages, `k` polynomially bounded and positive, through time reductions of polynomially
bounded time, with a negligible statistical term, asymptotic security of the primitive game
gives asymptotic security of the protocol game. -/
theorem asymSecure_of_reduction {a b c d : ℕ → Ty}
    (AdvP : ∀ n, (Val (a n) → SPComp (Val (b n))) → ℝ≥0∞)
    (AdvQ : ∀ n, (Val (c n) → SPComp (Val (d n))) → ℝ≥0∞)
    (k : ℕ → ℕ) (B : ∀ n, Fin (k n) → TimeReduction O (a n) (b n) (c n) (d n))
    (ε : ℕ → ℝ≥0∞)
    (hconc : ∀ n A, AdvP n A ≤ ∑ i, AdvQ n ((B n i).red A) + ε n)
    (hB : ∃ Q : ℕ → ℕ, IsPolyBound Q ∧ ∀ n i t, (B n i).time t ≤ Q (n + t))
    (hk : IsPolyBound k) (hk0 : ∀ n, 0 < k n) (hε : IsNegligible ε)
    (hQ : AsymSecure O AdvQ) : AsymSecure O AdvP := by
  intro A hA
  obtain ⟨p, hp, hpB, hbound⟩ := polyTime_transfer AdvP AdvQ k B ε hconc hB A hA
  -- the index of the largest primitive advantage at each `n`
  have hmax : ∀ n, ∃ i : Fin (k n), ∀ j, AdvQ n ((B n j).red (A n)) ≤
      AdvQ n ((B n i).red (A n)) := by
    intro n
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ
      (fun j : Fin (k n) => AdvQ n ((B n j).red (A n))) ⟨⟨0, hk0 n⟩, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
  choose i hi using hmax
  have hfam : PolyTimeFam O (fun n => (B n (i n)).red (A n)) :=
    ⟨p, hp, fun n => hpB n (i n)⟩
  have hneg := isNegligible_add (isNegligible_polyBound_mul hk (hQ _ hfam)) hε
  refine isNegligible_of_le_eventually hneg ⟨0, fun n _ => (hbound n).trans ?_⟩
  gcongr
  calc ∑ j, AdvQ n ((B n j).red (A n))
      ≤ Finset.univ.card • AdvQ n ((B n (i n)).red (A n)) :=
        Finset.sum_le_card_nsmul _ _ _ fun j _ => hi n j
    _ = _ := by simp [nsmul_eq_mul]

end Transfer

/-! ## The computational UC level over the time class -/

section UCLevel

variable (O : CTree.Oracle)

/-- Asymptotic computational indistinguishability over D: at every polynomially bounded time
`p`, the time-bounded computational distance of the members at `n` is negligible in `n`. -/
def UCTimeNegl {α : ℕ → Type} {b : ℕ → Ty} (f g : ∀ n, α n → SPComp (Val (b n))) : Prop :=
  ∀ p : ℕ → ℕ, IsPolyBound p → IsNegligible fun n => ucCdistTime O (p n) (f n) (g n)

variable {O}

theorem UCTimeNegl.refl {α : ℕ → Type} {b : ℕ → Ty} (f : ∀ n, α n → SPComp (Val (b n))) :
    UCTimeNegl O f f := by
  intro p _
  simpa only [ucCdistTime_self] using isNegligible_zero

theorem UCTimeNegl.symm {α : ℕ → Type} {b : ℕ → Ty} {f g : ∀ n, α n → SPComp (Val (b n))}
    (h : UCTimeNegl O f g) : UCTimeNegl O g f := by
  intro p hp
  simpa only [ucCdistTime_sym] using h p hp

theorem UCTimeNegl.trans {α : ℕ → Type} {b : ℕ → Ty}
    {f g h : ∀ n, α n → SPComp (Val (b n))} (h₁ : UCTimeNegl O f g)
    (h₂ : UCTimeNegl O g h) : UCTimeNegl O f h := by
  intro p hp
  exact isNegligible_of_le_eventually (isNegligible_add (h₁ p hp) (h₂ p hp))
    ⟨0, fun n _ => ucCdistTime_triangle _ _ _ _⟩

/-- A negligible statistical distance gives asymptotic computational indistinguishability. -/
theorem UCTimeNegl.of_sdist {α : ℕ → Type} {b : ℕ → Ty}
    {f g : ∀ n, α n → SPComp (Val (b n))} (h : IsNegligible fun n => sdist (f n) (g n)) :
    UCTimeNegl O f g := fun _ _ =>
  isNegligible_of_le_eventually h ⟨0, fun _ _ => ucCdistTime_le_sdist _ _ _⟩

/-- Pre-composition by any family preserves asymptotic indistinguishability. -/
theorem UCTimeNegl.comp_left {α β : ℕ → Type} {c : ℕ → Ty} (f : ∀ n, α n → SPComp (β n))
    {g₁ g₂ : ∀ n, β n → SPComp (Val (c n))} (h : UCTimeNegl O g₁ g₂) :
    UCTimeNegl O (fun n x => SPComp.bind (f n x) (g₁ n))
      (fun n x => SPComp.bind (f n x) (g₂ n)) := fun p hp =>
  isNegligible_of_le_eventually (h p hp) ⟨0, fun _ _ => ucCdistTime_comp_left _ _ _ _⟩

/-- Post-composition by a polynomial-time family preserves asymptotic indistinguishability. -/
theorem UCTimeNegl.comp_right {α : ℕ → Type} {b c : ℕ → Ty}
    {f g : ∀ n, α n → SPComp (Val (b n))} {k : ∀ n, Val (b n) → SPComp (Val (c n))}
    (hk : PolyTimeFam O k) (h : UCTimeNegl O f g) :
    UCTimeNegl O (fun n x => SPComp.bind (f n x) (k n))
      (fun n x => SPComp.bind (g n x) (k n)) := by
  obtain ⟨s, hs, hsk⟩ := hk
  intro p hp
  refine isNegligible_of_le_eventually
    (h (fun n => s n + p n + 3) ((hs.add hp).add (isPolyBound_const 3))) ⟨0, fun n _ => ?_⟩
  exact ucCdistTime_comp_right (p n) (f n) (g n) (k n) (hsk n)

/-- The constant distinguisher `λx. true`, admissible at time `1`. -/
theorem timeAdm_const_true {b : Ty} (hb : b.FO) :
    TimeAdm (b := .bool) O 1 (fun _ : Val b => SPComp.pure true) :=
  ⟨hb, trivial, ⟨TimeRealizer.ofBody (b := .bool) O hb trivial (.lit .bool true) 0 (fun _ => le_refl _) _
    (fun _ => rfl)⟩⟩

/-- At first-order result types, asymptotic indistinguishability is the asymptotic security
of the distinguishing game: the supremum over the distinguishers is negligible exactly when
every polynomial-time family of distinguishers has negligible advantage. -/
theorem ucTimeNegl_iff_asymSecure {α : ℕ → Type} {b : ℕ → Ty} (hb : ∀ n, (b n).FO)
    (f g : ∀ n, α n → SPComp (Val (b n))) :
    UCTimeNegl O f g ↔
      AsymSecure (b := fun _ => .bool) O (fun n D => spcomp_distComp (f n) (g n) D) := by
  classical
  constructor
  · rintro h D ⟨p, hp, hD⟩
    exact isNegligible_of_le_eventually (h p hp) ⟨0, fun n _ =>
      le_iSup₂ (f := fun D (_ : TimeAdm (b := .bool) O (p n) D) =>
        spcomp_distComp (f n) (g n) D) (D n) (hD n)⟩
  · intro h p hp c
    -- at each `n`, a distinguisher above the threshold `1 / n ^ c` if there is one
    let D : ∀ n, Val (b n) → SPComp (Val .bool) := fun n =>
      if hex : ∃ E : Val (b n) → SPComp (Val .bool), TimeAdm (b := .bool) O (p n) E ∧
          1 < spcomp_distComp (f n) (g n) E * (n : ℝ≥0∞) ^ c then hex.choose
      else fun _ => SPComp.pure true
    have hD : ∀ n, TimeAdm (b := .bool) O (p n + 1) (D n) := by
      intro n
      by_cases hex : ∃ E : Val (b n) → SPComp (Val .bool), TimeAdm (b := .bool) O (p n) E ∧
          1 < spcomp_distComp (f n) (g n) E * (n : ℝ≥0∞) ^ c
      · simp only [D, dite_eq_left hex]
        exact hex.choose_spec.1.mono (by omega)
      · simp only [D, dite_eq_right hex]
        exact (timeAdm_const_true (hb n)).mono (by omega)
    obtain ⟨N, hN⟩ := h D ⟨fun n => p n + 1, hp.add (isPolyBound_const 1), hD⟩ c
    refine ⟨N, fun n hn => ?_⟩
    unfold ucCdistTime
    rw [ENNReal.iSup_mul]
    refine iSup_le fun E => ?_
    rw [ENNReal.iSup_mul]
    refine iSup_le fun hE => ?_
    by_contra hlt
    have hex : ∃ E : Val (b n) → SPComp (Val .bool), TimeAdm (b := .bool) O (p n) E ∧
        1 < spcomp_distComp (f n) (g n) E * (n : ℝ≥0∞) ^ c := ⟨E, hE, not_le.mp hlt⟩
    have h1 := hN n hn
    simp only [D, dite_eq_left hex] at h1
    exact absurd h1 (not_le.mpr hex.choose_spec.2)

end UCLevel

/-! ## Worked instance -/

section Instance

/-- Two increments of a byte. -/
def addTwo (x : BitVec 8) : BitVec 8 := x + 1 + 1

reflect_d addTwo

/-- `addTwo` as an arrow of `SPComp` on the bytes of D. -/
noncomputable def addTwoArrow (x : Val (.word 8)) : SPComp (Val (.word 8)) :=
  SPComp.pure (addTwo x)

/-- `addTwoArrow` is admissible at time `3`: the reflected body costs two word additions and
the application one β-step. -/
theorem timeAdm_addTwo (O : CTree.Oracle) : TimeAdm O 3 addTwoArrow :=
  ⟨trivial, trivial, ⟨TimeRealizer.ofBody (a := .word 8) (b := .word 8) O trivial trivial
    addTwo.d 2 (fun _ => le_of_eq rfl) addTwoArrow
    (fun x => by simp only [Tm.denote, addTwo.d_den x]; rfl)⟩⟩

/-- The distinguishing advantage of a pair of families of byte computations post-processed
by `addTwo`. -/
noncomputable def addTwoAdv {α : ℕ → Type} (f₀ f₁ : ∀ n, α n → SPComp (Val (.word 8)))
    (n : ℕ) (D : Val (.word 8) → SPComp (Val .bool)) : ℝ≥0∞ :=
  spcomp_distComp (fun x => SPComp.bind (f₀ n x) addTwoArrow)
    (fun x => SPComp.bind (f₁ n x) addTwoArrow) D

/-- If the families `f₀` and `f₁` are asymptotically indistinguishable by polynomial-time
distinguishers of D, so are their post-processings by `addTwo`: the concrete reduction
`spcomp_distComp_bind_right`, through the time reduction `TimeReduction.pre` of time `t ↦ t + 6`. -/
theorem addTwo_asymSecure (O : CTree.Oracle) {α : ℕ → Type}
    (f₀ f₁ : ∀ n, α n → SPComp (Val (.word 8)))
    (h : AsymSecure (b := fun _ => .bool) O (fun n D => spcomp_distComp (f₀ n) (f₁ n) D)) :
    AsymSecure (b := fun _ => .bool) O (addTwoAdv f₀ f₁) := by
  refine asymSecure_of_reduction (a := fun _ => .word 8) (b := fun _ => .bool)
    (c := fun _ => .word 8) (d := fun _ => .bool) (addTwoAdv f₀ f₁)
    (fun n D => spcomp_distComp (f₀ n) (f₁ n) D) (fun _ => 1)
    (fun _ _ => TimeReduction.pre (b := .bool) addTwoArrow (timeAdm_addTwo O)) (fun _ => 0)
    ?_ ?_ (isPolyBound_const 1) (fun _ => Nat.one_pos) isNegligible_zero h
  · intro n D
    simp only [addTwoAdv, TimeReduction.pre, Finset.univ_unique, Finset.sum_singleton,
      add_zero]
    exact (spcomp_distComp_bind_right _ _ _ _).le
  · exact ⟨fun n => n + 10, isPolyBound_id.add (isPolyBound_const 10),
      fun n i t => by simp [TimeReduction.pre]; omega⟩

/-- Post-processing by the reflected `addTwo` as a time reduction from an open term: the body
calls the adversary on the input and applies `addTwo.d` to the result. -/
noncomputable example (O : CTree.Oracle) :
    TimeReduction O (.word 8) (.word 8) (.word 8) (.word 8) :=
  TimeReduction.ofOpen O trivial trivial
    (.app (Tm.weaken (.lam addTwo.d)) (.app (.var (.there .here)) (.var .here)))
    (fun A u => SPComp.bind (A u) addTwoArrow) (fun k => k + 4)
    (fun _ _ h => Nat.add_le_add_right h 4)
    (fun g k hg u => by
      change ((CTree.tick (g u)).bind
        fun v => CTree.tick (addTwo.d.eval (Env.nil.cons v))).cost ≤ k + 4
      have h1 := CTree.cost_bind_le (CTree.tick (g u))
        (fun v => CTree.tick (addTwo.d.eval (Env.nil.cons v))) 3
        (CTree.AllRet.of_forall (fun _ => le_of_eq rfl) _)
      have h2 := hg u
      rw [CTree.cost_tick] at h1
      omega)
    (fun A g hg u => by
      change CTree.run O ((CTree.tick (g u)).bind
        fun v => CTree.tick (addTwo.d.eval (Env.nil.cons v))) = _
      rw [CTree.run_bind]
      change SPComp.bind ((g u).run O) _ = _
      rw [hg]
      refine congrArg _ (funext fun v => ?_)
      change (addTwo.d.eval (Env.nil.cons v)).run O = _
      rw [Tm.run_eval O addTwo.d trivial (by simp [Ty.FO])]
      simp only [Tm.denote, addTwo.d_den v]
      rfl)

end Instance

end CatCrypt.Complexity.D
