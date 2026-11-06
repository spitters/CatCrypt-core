/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AdvantageMap
public import CatCryptCore.Crypto.ForkingLemma
public import CatCryptCore.NonUniform.Product

/-!
# Games over a sampler and their transfer through an encoding

A decisional game whose randomness is a fixed number of independent draws from one sampler,
made before anything else, is a `SampledGame`: the real and the ideal view as functions of the
draws. Its advantage `advAt μ A` is taken at a sampler `μ : SDistr X`; at the uniform sampler it
is the advantage of the usual game. Encoding the views by `enc : V → W` gives the game
`G.map enc`, and a distinguisher `A` of encoded views is the distinguisher `encodedRed enc A`
of the views.

A search game draws its randomness and computes from it a view and its solution; the encoded
game encodes the view by `encV` and the solution by `encS`, and the reduction `searchRed`
decodes the answer of the adversary by a left inverse `decS` of `encS`.

## Main definitions

* `SampledGame`, `SampledGame.realAt`, `SampledGame.idealAt`, `SampledGame.advAt`
* `SampledGame.map`, `encodedRed` — the encoded game and the reduction to the unencoded one
* `Realizes P Q G μ enc` — the pair `P`, `Q` is the encoded game `G` at the sampler `μ`
* `SearchGame`, `SearchGame.winAt`, `SearchGame.map`, `searchRed`

## Main results

* `sampleFrom_replicateFin_zero_bind`, `sampleFrom_replicateFin_succ_bind` — `n` draws from
  `μ` are one draw followed by `n - 1` draws
* `sampleFrom_uniform_map_bind`, `sampleFrom_replicateFin_uniform_map_bind` — draws from the
  image of the uniform sampler on `S` under `f` are uniform draws from `S` followed by `f`
* `SampledGame.advAt_map` — `(G.map enc).advAt μ A = G.advAt μ (encodedRed enc A)`
* `Realizes.advantageA_eq` — the advantage of `A` between a realized pair is the advantage of
  `encodedRed enc A` against the game
* `SearchGame.winAt_map_le` — the winning probability against the encoded search game is at
  most the winning probability of `searchRed encV decS A` against the search game
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob CatCrypt.NonUniform
open scoped ENNReal

/-! ## Repeated draws -/

/-- Zero draws are the empty family. -/
theorem sampleFrom_replicateFin_zero_bind {X V : Type} (μ : SDistr X)
    (k : (Fin 0 → X) → SPComp V) :
    (sampleFrom (replicateFin 0 μ)).bind k = k Fin.elim0 := by
  funext h
  simp only [sampleFrom_bind_apply, replicateFin, piFin_zero, SDistr.pure_bind]

/-- `n + 1` draws are one draw followed by `n` draws. -/
theorem sampleFrom_replicateFin_succ_bind {X V : Type} (n : ℕ) (μ : SDistr X)
    (k : (Fin (n + 1) → X) → SPComp V) :
    (sampleFrom (replicateFin (n + 1) μ)).bind k =
      (sampleFrom μ).bind fun x =>
        (sampleFrom (replicateFin n μ)).bind fun xs => k (Fin.cons x xs) := by
  funext h
  simp only [sampleFrom_bind_apply, replicateFin, piFin_succ, SDistr.bind_assoc,
    SDistr.pure_bind]

/-- One draw from the image of the uniform sampler on `S` under `f` is a uniform draw from `S`
followed by `f`. -/
theorem sampleFrom_uniform_map_bind {S X V : Type} [Fintype S] [Nonempty S] (f : S → X)
    (k : X → SPComp V) :
    (sampleFrom ((SDistr.uniform S).bind fun s => SDistr.pure (f s))).bind k =
      (SPComp.sample S).bind fun s => k (f s) := by
  rw [← sampleFrom_bind_sampleFrom, sampleFrom_uniform, SPComp.bind_assoc]
  simp only [sampleFrom_pure, SPComp.pure_bind]

/-- `n` draws from the image of the uniform sampler on `S` under `f` are a uniform draw from
`Fin n → S` followed by `f` at each draw. -/
theorem sampleFrom_replicateFin_uniform_map_bind {S X V : Type} [Fintype S] [Nonempty S]
    (f : S → X) : ∀ (n : ℕ) (k : (Fin n → X) → SPComp V),
    (sampleFrom (replicateFin n ((SDistr.uniform S).bind fun s => SDistr.pure (f s)))).bind k =
      (SPComp.sample (Fin n → S)).bind fun v => k (f ∘ v)
  | 0, k => by
    have hk : (fun v : Fin 0 → S => k (f ∘ v)) = fun _ => k Fin.elim0 :=
      funext fun _ => congrArg k (funext fun i => i.elim0)
    rw [sampleFrom_replicateFin_zero_bind, hk]
    funext h
    simp only [SPComp.bind_def, SPComp.sample, SDistr.bind_assoc, SDistr.pure_bind,
      SDistr.uniform_bind_const]
  | n + 1, k => by
    rw [sampleFrom_replicateFin_succ_bind, sampleFrom_uniform_map_bind,
      ← SPComp.sample_bind_equiv (Fin.consEquiv fun _ => S), SPComp.sample_prod_eq]
    simp only [SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext s
    rw [sampleFrom_replicateFin_uniform_map_bind f n]
    congr 1; funext v
    exact congrArg k (funext fun i => Fin.cases rfl (fun _ => rfl) i)

/-! ## Decisional games over a sampler -/

/-- A decisional game whose randomness is `nR` (real) and `nI` (ideal) independent draws
from one sampler on `X`, made before anything else. -/
structure SampledGame (X V : Type) where
  /-- The number of draws of the real game. -/
  nR : ℕ
  /-- The number of draws of the ideal game. -/
  nI : ℕ
  /-- The real view as a function of the draws. -/
  real : (Fin nR → X) → SPComp V
  /-- The ideal view as a function of the draws. -/
  ideal : (Fin nI → X) → SPComp V

namespace SampledGame

variable {X V W : Type}

/-- The real game at the sampler `μ`. -/
noncomputable def realAt (G : SampledGame X V) (μ : SDistr X) : SPComp V :=
  (sampleFrom (replicateFin G.nR μ)).bind G.real

/-- The ideal game at the sampler `μ`. -/
noncomputable def idealAt (G : SampledGame X V) (μ : SDistr X) : SPComp V :=
  (sampleFrom (replicateFin G.nI μ)).bind G.ideal

/-- The advantage of `A` between the real and the ideal game at the sampler `μ`. -/
noncomputable def advAt (G : SampledGame X V) (μ : SDistr X) (A : V → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (G.realAt μ) (G.idealAt μ) A

/-- The encoded game: the same randomness, the views encoded. -/
noncomputable def map (enc : V → W) (G : SampledGame X V) : SampledGame X W :=
  ⟨G.nR, G.nI, fun xs => (G.real xs).map enc, fun xs => (G.ideal xs).map enc⟩

/-- The real game of the encoded game is the encoded real game. -/
theorem realAt_map (enc : V → W) (G : SampledGame X V) (μ : SDistr X) :
    (G.map enc).realAt μ = (G.realAt μ).map enc := by
  simp only [realAt, map, SPComp.map, SPComp.bind_assoc]

/-- The ideal game of the encoded game is the encoded ideal game. -/
theorem idealAt_map (enc : V → W) (G : SampledGame X V) (μ : SDistr X) :
    (G.map enc).idealAt μ = (G.idealAt μ).map enc := by
  simp only [idealAt, map, SPComp.map, SPComp.bind_assoc]

end SampledGame

/-- The adversary against the game of views built from one against the encoded game. -/
def encodedRed {V W : Type} (enc : V → W) (A : W → SPComp Bool) : V → SPComp Bool :=
  fun v => A (enc v)

namespace SampledGame

variable {X V W : Type}

/-- The advantage against the encoded game is the advantage of `encodedRed enc A` against the
game. -/
theorem advAt_map (enc : V → W) (G : SampledGame X V) (μ : SDistr X)
    (A : W → SPComp Bool) :
    (G.map enc).advAt μ A = G.advAt μ (encodedRed enc A) := by
  rw [advAt, realAt_map, idealAt_map, advantageA_map]
  rfl

end SampledGame

/-- A game pair is the image of `G` at the sampler `μ` under `enc`. -/
structure Realizes {X V W : Type} (P Q : SPComp W) (G : SampledGame X V) (μ : SDistr X)
    (enc : V → W) : Prop where
  /-- The first game is the encoded real game. -/
  real : P = (G.realAt μ).map enc
  /-- The second game is the encoded ideal game. -/
  ideal : Q = (G.idealAt μ).map enc

/-- The advantage of `A` between a realized pair is the advantage of `encodedRed enc A`
against the game at the sampler. -/
theorem Realizes.advantageA_eq {X V W : Type} {P Q : SPComp W} {G : SampledGame X V}
    {μ : SDistr X} {enc : V → W} (h : Realizes P Q G μ enc) (A : W → SPComp Bool) :
    AdvantageA P Q A = G.advAt μ (encodedRed enc A) := by
  rw [h.real, h.ideal, advantageA_map]
  rfl

/-! ## Search games over a sampler -/

/-- A search game: `n` draws determine a view and its solution. -/
structure SearchGame (X V S : Type) where
  /-- The number of draws. -/
  n : ℕ
  /-- The view and the solution as a function of the draws. -/
  inst : (Fin n → X) → V × S

namespace SearchGame

variable {X V S W T : Type}

/-- The probability that `A` outputs the solution of the view, at the sampler `μ`. -/
noncomputable def winAt [DecidableEq S] (G : SearchGame X V S) (μ : SDistr X)
    (A : V → SPComp S) : ℝ≥0∞ :=
  prTrue ((sampleFrom (replicateFin G.n μ)).bind fun xs =>
    (A (G.inst xs).1).bind fun s => SPComp.pure (decide (s = (G.inst xs).2))) Heap.empty

/-- The encoded search game: the view encoded by `encV`, the solution by `encS`. -/
def map (encV : V → W) (encS : S → T) (G : SearchGame X V S) : SearchGame X W T :=
  ⟨G.n, fun xs => (encV (G.inst xs).1, encS (G.inst xs).2)⟩

end SearchGame

/-- The adversary against the search game built from one against the encoded search game:
its answer decoded by `decS`. -/
noncomputable def searchRed {V W S T : Type} (encV : V → W) (decS : T → S)
    (A : W → SPComp T) : V → SPComp S :=
  fun v => (A (encV v)).map decS

/-- The winning probability against the encoded search game is at most that of
`searchRed encV decS A` against the search game, for a left inverse `decS` of `encS`. -/
theorem SearchGame.winAt_map_le {X V S W T : Type} [DecidableEq S] [DecidableEq T]
    (encV : V → W) (encS : S → T) (decS : T → S) (hdec : ∀ s, decS (encS s) = s)
    (G : SearchGame X V S) (μ : SDistr X) (A : W → SPComp T) :
    (G.map encV encS).winAt μ A ≤ G.winAt μ (searchRed encV decS A) := by
  simp only [winAt, map, searchRed, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  refine ForkingLemma.prTrue_bind_mono _ _ _ _ fun xs _ =>
    ForkingLemma.prTrue_bind_mono _ _ _ _ fun t h =>
      ForkingLemma.prTrue_pure_decide_mono ?_ h
  rintro rfl
  exact hdec _

end CatCrypt.Crypto
