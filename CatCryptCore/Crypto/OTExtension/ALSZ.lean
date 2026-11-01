/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.ALSZPull
public import CatCryptCore.Crypto.GeneralForkingLemma

/-!
# ALSZ: IKNP with the base OTs on seeds

**Ideal system.** The IKNP wake parties of `OTExtension/IKNPWake.lean` with their own draw
(`IKNPWake.partyLazy`) over the `κ` scheduled column OTs `baseG κ m` beside the secure channel
for the masked messages (`iknpOver`), the real system of `IKNPPVW.iknpLazy_realizesSim`, which
`IKNPWake` relates to `FOTSched otChoose` and `FOTSchedSH otChoose leak`.

**Real protocol.** ALSZ (Asharov, Lindell, Schneider and Zohner, CCS 2013): the IKNP wake
parties whose randomness is a seed pair `(k₀ᵢ, k₁ᵢ)` per base OT and the sender's secret `s`,
drawn at the first input of a party (`alszLazy`). The matrix `T` of the receiver has the column
`i` equal to `G k₀ᵢ` for the PRG `G : PRGDef Seed (Fin m → Bool)`; the receiver gives the seed
pair and its choices `r` to the base OT `i` (`alszPartyW`, the IKNP parties with relabelled
calls), which transfers the seeds through a scheduled seed OT and the correction string
`G k₀ᵢ + G k₁ᵢ + r` on a secure channel (`ALSZPull.lean`); the sender obtains the column
`G k_{sᵢ} + sᵢ · u = Tᵢ + sᵢ · r`. A corruption event is answered by the IKNP view of the party,
with the matrix of PRG outputs (`alszSeed`).

**Simulator.** `simALSZ`: the forwarding of the parties' port beside the indexed copies of the
simulator `simA` of one base OT and the forwarding of the IKNP channel's adversary port.

**Bound.** The sum over the columns `i < κ` of the PRG advantage of the explicit reduction
`alszPrgRed G i`, at the environment reduced through the extended simulator
(`alsz_realizes_iknpWake`).

**Proof.** With the key `K`, the ALSZ parties over the functionality of the base OTs
`FOTSchedPar (Fin κ) (alszOut G)` are the IKNP parties with the key `tOf G K` over the column OTs,
by a state map that replaces each input by its column pair (`view_alszK`, through
`MultiHybrid.withSub_callMap_on`: the IKNP parties call a base OT only with the column of their
matrix). Both systems with their own draw are the average over the key of the systems with the
key (`MultiHybrid.view_lazyKey_tensor`), so the distance is that of `κ` PRG outputs from `κ`
uniform columns, at most the sum of `κ` PRG advantages (`prg_pi_hybrid`, the hybrid argument
over the columns). Modular composition with the channel (`RealizesSim.modular_withChan`)
substitutes the base OTs of ALSZ, which realize their functionality at distance `0`
(`alszBase_realizesSim`).

## Main definitions

* `prgHybRed`: the reduction of the hop `i` of the PRG hybrids.
* `MultiHybrid.mapCalls`: a multi-call hybrid with relabelled calls.
* `AKey`, `tOf`, `liftCall`, `alszPartyW`, `alszLazy`: the ALSZ key, its IKNP matrix, the
  relabelled calls and the parties.
* `alszOver`, `iknpOver`, `alszSeed`: ALSZ over the functionality of its base OTs, IKNP over the
  column OTs, and ALSZ over the seed OTs.
* `alszWorld`, `alszDist`, `alszRed`, `alszPrgRed`: the reduction to the PRG.
* `simALSZ`: the simulator.

## Main results

* `prg_pi_hybrid`: `κ` PRG outputs against `κ` uniform values, by `κ` hops.
* `MultiHybrid.withSub_callMap_on`, `MultiHybrid.view_lazyKey_tensor`: relabelled calls under a
  state map, and the averaging of a drawing hybrid over its key.
* `view_alszK`: with a fixed key, ALSZ is IKNP with the matrix of PRG outputs.
* `alszOver_realizes`: ALSZ over the functionality of its base OTs realizes IKNP over the column
  OTs, with the PRG bound.
* `alsz_realizes_iknpWake`: ALSZ over the seed OTs realizes IKNP over the column OTs behind
  `simALSZ`, with the PRG bound.
-/

@[expose] public section

set_option autoImplicit false

/-! ## Relabelled calls of a multi-call hybrid -/

namespace CatCrypt.Crypto.UCTransparent.MultiHybrid

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.NonUniform

variable {σ τ υ E O EG EG' OG : Type}

/-- **Relabelled calls.** The hybrid `π` whose calls are relabelled by `c`. -/
noncomputable def mapCalls (π : MultiHybrid σ E O EG OG) (c : EG → EG') :
    MultiHybrid σ E O EG' OG where
  init := π.init
  fuel := π.fuel
  start s e := SPComp.map (fun r => (r.1, Sum.map c id r.2)) (π.start s e)
  resume s o := SPComp.map (fun r => (r.1, Sum.map c id r.2)) (π.resume s o)
  finish := π.finish
  start_noFail _ _ :=
    Assumptions.SPComp.bind_noFail (π.start_noFail _ _) fun _ => SPComp.pure_noFail _
  resume_noFail _ _ :=
    Assumptions.SPComp.bind_noFail (π.resume_noFail _ _) fun _ => SPComp.pure_noFail _
  finish_noFail := π.finish_noFail

/-- A deterministic decision whose call, if any, satisfies `Q`. -/
def EmitsQ (c : SPComp (σ × (EG ⊕ O))) (Q : EG → Prop) : Prop :=
  ∃ r : σ × (EG ⊕ O), c = SPComp.pure r ∧ ∀ g, r.2 = .inl g → Q g

/-- The rest of an activation of `π₁`, whose decisions are those of `π₂` with the calls
relabelled by `c`, against `X` commutes with a state map `F` to `Y` that commutes with the steps
on the relabelled calls satisfying `Q`, when `π₂` decides deterministically on calls satisfying
`Q`. -/
theorem drive_callMap_on (π₁ : MultiHybrid σ E O EG' OG) (π₂ : MultiHybrid σ E O EG OG)
    (c : EG → EG') (Q : EG → Prop)
    (hres : ∀ s o, π₁.resume s o = SPComp.map (fun r => (r.1, Sum.map c id r.2)) (π₂.resume s o))
    (hfin : ∀ s o, π₁.finish s o = π₂.finish s o)
    (hQ : ∀ s o, EmitsQ (π₂.resume s o) Q)
    (X : Sys τ EG' OG) (Y : Sys υ EG OG) (F : τ → υ)
    (hX : ∀ t g, Q g → SPComp.map (fun p => (F p.1, p.2)) (X.step t (c g)) = Y.step (F t) g) :
    ∀ n s d t, (∀ g, d = .inl g → Q g) →
      SPComp.map (fun p => (p.1, F p.2.1, p.2.2)) (π₁.drive X n s (Sum.map c id d) t) =
        π₂.drive Y n s d (F t) := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) t hd
    · simp only [Sum.map_inl, drive, ← hX t g (hd g rfl), hfin, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
    · simp [drive, SPComp.map, SPComp.pure_bind]
  | succ n ih =>
    rintro s (g | o) t hd
    · simp only [Sum.map_inl, drive, ← hX t g (hd g rfl), SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
      congr 1
      funext q
      obtain ⟨r, hr, hrQ⟩ := hQ s q.2
      have h := ih r.1 r.2 q.1 hrQ
      simp only [SPComp.map] at h
      rw [hres, hr]
      simp only [SPComp.map, SPComp.pure_bind]
      exact h
    · simp [drive, SPComp.map, SPComp.pure_bind]

/-- **Relabelled calls under a state map.** A step of `π₁`, whose decisions are those of `π₂` with
the calls relabelled by `c`, against `X` commutes with a state map `F` to `Y` that commutes with
the steps on the relabelled calls satisfying `Q`, when `π₂` decides deterministically on calls
satisfying `Q`. -/
theorem withSub_callMap_on (π₁ : MultiHybrid σ E O EG' OG) (π₂ : MultiHybrid σ E O EG OG)
    (c : EG → EG') (Q : EG → Prop) (hfuel : π₁.fuel = π₂.fuel)
    (hstart : ∀ s e, π₁.start s e = SPComp.map (fun r => (r.1, Sum.map c id r.2)) (π₂.start s e))
    (hres : ∀ s o, π₁.resume s o = SPComp.map (fun r => (r.1, Sum.map c id r.2)) (π₂.resume s o))
    (hfin : ∀ s o, π₁.finish s o = π₂.finish s o)
    (hQs : ∀ s e, EmitsQ (π₂.start s e) Q) (hQr : ∀ s o, EmitsQ (π₂.resume s o) Q)
    (X : Sys τ EG' OG) (Y : Sys υ EG OG) (F : τ → υ)
    (hX : ∀ t g, Q g → SPComp.map (fun p => (F p.1, p.2)) (X.step t (c g)) = Y.step (F t) g)
    (t : σ × τ) (e : E) :
    SPComp.map (fun p => ((p.1.1, F p.1.2), p.2)) ((π₁.withSub X).step t e) =
      (π₂.withSub Y).step (t.1, F t.2) e := by
  obtain ⟨r, hr, hrQ⟩ := hQs t.1 e
  have h := drive_callMap_on π₁ π₂ c Q hres hfin hQr X Y F hX π₂.fuel r.1 r.2 t.2 hrQ
  simp only [SPComp.map] at h
  simp only [withSub, hstart, hr, hfuel, SPComp.map, SPComp.pure_bind, SPComp.bind_assoc]
  rw [← h]
  simp only [SPComp.bind_assoc, SPComp.pure_bind]

/-- The tensor of a hybrid with relabelled calls decides as the tensor with the calls of the
left component relabelled. -/
theorem tensor_mapCalls_start {σ' E' O' EA OA : Type} (π : MultiHybrid σ E O EG OG)
    (ρ : MultiHybrid σ' E' O' EA OA) (c : EG → EG') (s : σ × σ') (e : E ⊕ E') :
    ((π.mapCalls c).tensor ρ).start s e =
      SPComp.map (fun r => (r.1, Sum.map (Sum.map c id) id r.2)) ((π.tensor ρ).start s e) := by
  rcases e with e | e <;>
    simp only [tensor, mapCalls, Sum.elim_inl, Sum.elim_inr, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind] <;>
    congr 1 <;> funext r <;> rcases r with ⟨_, _ | _⟩ <;> rfl

/-- The resumption of the tensor of a hybrid with relabelled calls. -/
theorem tensor_mapCalls_resume {σ' E' O' EA OA : Type} (π : MultiHybrid σ E O EG OG)
    (ρ : MultiHybrid σ' E' O' EA OA) (c : EG → EG') (s : σ × σ') (o : OG ⊕ OA) :
    ((π.mapCalls c).tensor ρ).resume s o =
      SPComp.map (fun r => (r.1, Sum.map (Sum.map c id) id r.2)) ((π.tensor ρ).resume s o) := by
  rcases o with o | o <;>
    simp only [tensor, mapCalls, Sum.elim_inl, Sum.elim_inr, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind] <;>
    congr 1 <;> funext r <;> rcases r with ⟨_, _ | _⟩ <;> rfl

/-- **The key drawn in the hybrid, averaged.** The drawing hybrid beside the forwarding of the
adversary port, over a subroutine that answers each event on its port, has the view of the
average over `k ← μ` of the hybrids `π k` beside the forwarding, when the hybrids of the family
have the same fuel and initial state, and an activation that does not read the key outputs at
once, the same for every key. -/
theorem view_lazyKey_tensor {K : Type} (π : K → MultiHybrid σ E O EG OG) (k₀ : K) (μ : PMF K)
    (u : σ → E → Bool) {EA OA ζ : Type} (X : Sys τ (EG ⊕ EA) (OG ⊕ OA)) (hX : X.PortTyped)
    (hfuel : ∀ k, (π k).fuel = (π k₀).fuel) (hinit : ∀ k, (π k).init = (π k₀).init)
    (hind : ∀ k s e, u s e = false → ∃ r : σ × O,
      (π k).start s e = SPComp.pure (r.1, .inr r.2) ∧
        (π k₀).start s e = SPComp.pure (r.1, .inr r.2))
    (Z : Strat ζ (E ⊕ EA) (O ⊕ OA)) :
    view (((lazyKey π k₀ μ u).tensor (idSim EA OA)).withSub X) Z =
      SPComp.bind (sampleFrom (ofPMF μ)) fun k =>
        view (((π k).tensor (idSim EA OA)).withSub X) Z := by
  obtain ⟨XL, XR, hL, hR⟩ := hX
  have h1 : view (((lazyKey π k₀ μ u).tensor (idSim EA OA)).withSub X) Z =
      view ((lazyKey (fun k => (π k).tensor (idSim EA OA)) k₀ μ (tensorUses u)).withSub X) Z :=
    view_eq_of_stepMap _ _ (fun t => ((t.1.1.1, (t.1.1.2, t.1.2)), t.2)) rfl
      (fun t e => lazyKey_tensor_withSub_step π (idSim EA OA) k₀ μ u X t e) Z
  have hfuel' : ∀ k, ((π k).tensor (idSim EA OA)).fuel = ((π k₀).tensor (idSim EA OA)).fuel :=
    fun k => by simp only [tensor, hfuel]
  have hind' : ∀ k t e,
      (keyedWithSub (fun k => (π k).tensor (idSim EA OA)) k₀ (tensorUses u) X).uses t e = false →
      (keyedWithSub (fun k => (π k).tensor (idSim EA OA)) k₀ (tensorUses u) X).step k t e =
        (keyedWithSub (fun k => (π k).tensor (idSim EA OA)) k₀ (tensorUses u) X).step₀ t e := by
    rintro k ⟨⟨s, ⟨⟩⟩, t⟩ (e | a) hu
    · obtain ⟨r, hk, hk₀⟩ := hind k s e hu
      simp only [keyedWithSub]
      rw [tensor_withSub_step_inl _ _ X XL hL, tensor_withSub_step_inl _ _ X XL hL]
      simp only [stepFuel, hk, hk₀, SPComp.pure_bind, drive]
    · simp only [keyedWithSub]
      rw [tensor_withSub_step_inr _ _ X XR hR, tensor_withSub_step_inr _ _ X XR hR, hfuel]
  rw [h1, view_lazyKey_withSub _ k₀ μ _ hfuel' X Z, KeyedSys.view_lazy _ μ hind' Z]
  congr 1
  funext k
  exact view_eq_of_stepMap
    ((keyedWithSub (fun k => (π k).tensor (idSim EA OA)) k₀ (tensorUses u) X).withKey k)
    (((π k).tensor (idSim EA OA)).withSub X) id
    (by simp [keyedWithSub, KeyedSys.withKey, withSub, tensor, hinit])
    (fun t e => by simp [keyedWithSub, KeyedSys.withKey, SPComp.map]) Z

end CatCrypt.Crypto.UCTransparent.MultiHybrid

namespace CatCrypt.Crypto.OT.ALSZ

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-! ## `κ` PRG outputs against `κ` uniform values -/

section Hybrid

variable {κ : ℕ} {Seed Out : Type} [Fintype Seed] [Nonempty Seed] [Fintype Out] [Nonempty Out]

/-- The values of the hybrid `i`: uniform `U j` below `i`, the PRG output `G (k j)` from `i` on. -/
def hybCols (G : PRGDef Seed Out) (i : ℕ) (k : Fin κ → Seed) (U : Fin κ → Out) : Fin κ → Out :=
  fun j => if j.val < i then U j else G.stretch (k j)

/-- The hybrid game `i`: the distinguisher `D` on the values of the hybrid `i`. -/
noncomputable def hybGame (G : PRGDef Seed Out) (D : (Fin κ → Out) → SPComp Bool) (i : ℕ) :
    SPComp Bool :=
  SPComp.bind (SPComp.sample (Fin κ → Seed)) fun k =>
    SPComp.bind (SPComp.sample (Fin κ → Out)) fun U => D (hybCols G i k U)

/-- **The reduction of the hop `i` to the PRG game.** On a challenge `y`, sample the seeds and the
uniform values, put `y` at the position `i` of the values of the hybrid `i`, and run `D`. -/
noncomputable def prgHybRed (G : PRGDef Seed Out) (D : (Fin κ → Out) → SPComp Bool) (i : Fin κ)
    (y : Out) : SPComp Bool :=
  SPComp.bind (SPComp.sample (Fin κ → Seed)) fun k =>
    SPComp.bind (SPComp.sample (Fin κ → Out)) fun U => D (Function.update (hybCols G i k U) i y)

omit [Fintype Seed] [Nonempty Seed] [Fintype Out] [Nonempty Out] in
/-- The PRG output at the position `i` of the hybrid `i` is the output of the updated seed. -/
theorem update_hybCols_stretch (G : PRGDef Seed Out) (i : Fin κ) (k : Fin κ → Seed)
    (U : Fin κ → Out) (s : Seed) :
    Function.update (hybCols G i k U) i (G.stretch s) = hybCols G i (Function.update k i s) U := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [hybCols]
  · simp [hybCols, Function.update_of_ne h]

omit [Fintype Seed] [Nonempty Seed] [Fintype Out] [Nonempty Out] in
/-- A uniform value at the position `i` of the hybrid `i` gives the hybrid `i + 1`. -/
theorem update_hybCols_succ (G : PRGDef Seed Out) (i : Fin κ) (k : Fin κ → Seed)
    (U : Fin κ → Out) (y : Out) :
    Function.update (hybCols G i k U) i y = hybCols G (i + 1) k (Function.update U i y) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [hybCols]
  · have hv : j.val ≠ i.val := fun e => h (Fin.ext e)
    by_cases hj : j.val < i.val
    · simp [hybCols, Function.update_of_ne h, hj, Nat.lt_succ_of_lt hj]
    · have hj' : ¬ j.val < i.val + 1 := by omega
      simp [hybCols, Function.update_of_ne h, hj, hj']

/-- The real PRG game against the reduction of the hop `i` is the hybrid `i`. -/
theorem prg_real_bind_prgHybRed (G : PRGDef Seed Out) (D : (Fin κ → Out) → SPComp Bool)
    (i : Fin κ) : SPComp.bind (prg_real G) (prgHybRed G D i) = hybGame G D i := by
  unfold prg_real prgHybRed
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind, update_hybCols_stretch]
  rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)]
  unfold hybGame
  exact GeneralForkingLemma.sample_update_eq_sample i fun k =>
    SPComp.bind (SPComp.sample (Fin κ → Out)) fun U => D (hybCols G i k U)

/-- The ideal PRG game against the reduction of the hop `i` is the hybrid `i + 1`. -/
theorem prg_ideal_bind_prgHybRed (G : PRGDef Seed Out) (D : (Fin κ → Out) → SPComp Bool)
    (i : Fin κ) : SPComp.bind prg_ideal (prgHybRed G D i) = hybGame G D (i + 1) := by
  unfold prg_ideal prgHybRed
  simp only [update_hybCols_succ]
  rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)]
  unfold hybGame
  congr 1
  funext k
  rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)]
  exact GeneralForkingLemma.sample_update_eq_sample i fun U => D (hybCols G (i + 1) k U)

/-- The hybrid `0` is `D` on the PRG outputs of uniform seeds. -/
theorem hybGame_zero (G : PRGDef Seed Out) (D : (Fin κ → Out) → SPComp Bool) :
    hybGame G D 0 = SPComp.bind (SPComp.sample (Fin κ → Seed)) fun k => D (G.stretch ∘ k) := by
  have h : ∀ (k : Fin κ → Seed) (U : Fin κ → Out), hybCols G 0 k U = G.stretch ∘ k := fun k U => by
    funext j
    simp [hybCols]
  simp only [hybGame, h]
  congr 1
  funext k
  exact Relational.dead_sample _

/-- The hybrid `κ` is `D` on uniform values. -/
theorem hybGame_last (G : PRGDef Seed Out) (D : (Fin κ → Out) → SPComp Bool) :
    hybGame G D κ = SPComp.bind (SPComp.sample (Fin κ → Out)) D := by
  have h : ∀ (k : Fin κ → Seed) (U : Fin κ → Out), hybCols G κ k U = U := fun k U => by
    funext j
    simp [hybCols, j.isLt]
  simp only [hybGame, h]
  exact Relational.dead_sample (α := Fin κ → Seed) _

/-- The distance of the hybrids `0` and `n` is at most the sum of the distances of the hybrids
`i` and `i + 1` for `i < n`. -/
theorem absDiff_hybGame_le (G : PRGDef Seed Out) (D : (Fin κ → Out) → SPComp Bool) (h₀ : Heap) :
    ∀ n : ℕ, absDiff (prTrue (hybGame G D 0) h₀) (prTrue (hybGame G D n) h₀) ≤
      ∑ i ∈ Finset.range n,
        absDiff (prTrue (hybGame G D i) h₀) (prTrue (hybGame G D (i + 1)) h₀) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (absDiff_triangle _ _ _).trans (add_le_add ih le_rfl)

/-- **`κ` PRG outputs against `κ` uniform values.** The distinguisher `D` tells the PRG outputs
of `κ` uniform seeds from `κ` uniform values with probability at most the sum over the positions
`i` of the PRG advantage of the explicit reduction `prgHybRed G D i`, from the empty heap. -/
theorem prg_pi_hybrid (G : PRGDef Seed Out) (D : (Fin κ → Out) → SPComp Bool) :
    absDiff
      (prTrue (SPComp.bind (SPComp.sample (Fin κ → Seed)) fun k => D (G.stretch ∘ k)) Heap.empty)
      (prTrue (SPComp.bind (SPComp.sample (Fin κ → Out)) D) Heap.empty) ≤
      ∑ i : Fin κ, PRG_Advantage G (prgHybRed G D i) := by
  rw [← hybGame_zero G D, ← hybGame_last G D]
  refine (absDiff_hybGame_le G D Heap.empty κ).trans (le_of_eq ?_)
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PRG_Advantage, AdvantageA, Advantage, ← prg_real_bind_prgHybRed G D i,
    ← prg_ideal_bind_prgHybRed G D i, absDiff]

end Hybrid

/-! ## The ALSZ base OTs and parties -/

section Parties

open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.OT.IKNPWake CatCrypt.Crypto.OT.IKNPSquare

variable {κ m : ℕ} {M Seed : Type}

/-- The key of the ALSZ parties: the receiver's seed pairs `(k₀, k₁)` and the sender's secret. -/
abbrev AKey (κ : ℕ) (Seed : Type) := ((Fin κ → Seed) × (Fin κ → Seed)) × (Fin κ → Bool)

/-- The IKNP key of an ALSZ key: the matrix whose column `i` is `G k₀ᵢ`, and the secret. -/
def tOf (G : PRGDef Seed (Fin m → Bool)) (K : AKey κ Seed) : IKNPKey κ m :=
  (fun j i => G.stretch (K.1.1 i) j, K.2)

/-- The call of the ALSZ receiver for a call of the IKNP receiver: the column pair `(T, T + r)`
for the base OT `i` is replaced by the seed pair `(k₀ᵢ, k₁ᵢ)` and `r`. -/
def liftCall (K : AKey κ Seed) :
    HEv κ m ⊕ ChanHEv (Msg m M) → AHEv κ Seed m ⊕ ChanHEv (Msg m M)
  | .inl (.inl (i, p)) => .inl (.inl (i, ((K.1.1 i, K.1.2 i), p.1 + p.2)))
  | .inl (.inr c) => .inl (.inr c)
  | .inr c => .inr c

/-- The ALSZ base-OT state that stands for an IKNP base-OT state: the input replaced by its
column pair. -/
def stMap (G : PRGDef Seed (Fin m → Bool)) (t : SchedSt (AIn Seed m) Bool (Fin m → Bool)) :
    SchedSt (BPair m) Bool (Fin m → Bool) :=
  ⟨t.sent.map (colPair G), t.chosen, t.inbox, t.dRecv, t.dSend⟩

/-- `stMap` commutes with a sender activation. -/
theorem stMap_sendStep (G : PRGDef Seed (Fin m → Bool))
    (t : SchedSt (AIn Seed m) Bool (Fin m → Bool)) (x : AIn Seed m) :
    (stMap G (FOTSched.sendStep t x).1, (FOTSched.sendStep t x).2) =
      FOTSched.sendStep (stMap G t) (colPair G x) := by
  rcases t with ⟨_ | _, _, _, _, _⟩ <;> rfl

/-- `stMap` commutes with a receiver activation. -/
theorem stMap_recvStep (G : PRGDef Seed (Fin m → Bool))
    (t : SchedSt (AIn Seed m) Bool (Fin m → Bool)) (b : Bool) :
    (stMap G (FOTSched.recvStep t b).1, (FOTSched.recvStep t b).2) =
      FOTSched.recvStep (stMap G t) b := by
  rcases t with ⟨_, _ | _, _, _, _⟩ <;> rfl

/-- `stMap` commutes with an adversary activation. -/
theorem stMap_schedStep (G : PRGDef Seed (Fin m → Bool))
    (t : SchedSt (AIn Seed m) Bool (Fin m → Bool)) (a : SchedEv) :
    (stMap G (FOTSched.schedStep (alszOut G) t a).1, (FOTSched.schedStep (alszOut G) t a).2) =
      FOTSched.schedStep baseOut (stMap G t) a := by
  rcases t with ⟨_ | x, _ | c, _, _ | _, _⟩ <;> cases a <;>
    simp [FOTSched.schedStep, stMap, alszOut_eq]

/-- The column pair of a lifted call: when the first column of `p` is `G k₀`, the input
`((k₀, k₁), p.1 + p.2)` stands for `p`. -/
theorem colPair_lift (G : PRGDef Seed (Fin m → Bool)) (k₀ k₁ : Seed) (p : BPair m)
    (h : p.1 = G.stretch k₀) : colPair G ((k₀, k₁), p.1 + p.2) = p := by
  obtain ⟨p₁, p₂⟩ := p
  subst h
  refine Prod.ext rfl ?_
  funext j
  simp only [colPair, Pi.add_apply]
  cases G.stretch k₀ j <;> cases p₂ j <;> decide

/-- The calls of the IKNP parties with the matrix `T` to the base OTs: a column pair for the base
OT `i` has the column `i` of `T` first. -/
def colCall (T : Fin m → Fin κ → Bool) (g : (HEv κ m ⊕ ChanHEv (Msg m M)) ⊕ AEv κ m M) : Prop :=
  ∀ i p, g = .inl (.inl (.inl (i, p))) → p.1 = fun j => T j i

section Party

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) {P L LS LR : Type}
  (φS : IKNPSenderView κ m Unit → LS) (φR : IKNPReceiverView κ m M Unit × (Fin m → M) → LR)
  (ans : Option LS → Option LR → P → L) (G : PRGDef Seed (Fin m → Bool)) [NeZero κ]

/-- **The ALSZ parties with the key `K = ((k₀, k₁), s)`.** The IKNP parties of `partyW` whose
matrix has the column `i` equal to `G k₀ᵢ`, the receiver giving the seed pair `(k₀ᵢ, k₁ᵢ)` and
its choices to the base OT `i` in place of the column pair. -/
noncomputable def alszPartyW (K : AKey κ Seed) :
    MultiHybrid (PSt κ m M) ((InEv m M ⊕ WakeEv κ) ⊕ P) (InOut m M ⊕ L)
      (AHEv κ Seed m ⊕ ChanHEv (Msg m M)) (HOut m ⊕ ChanHOut (Msg m M)) :=
  (partyW H φS φR ans (tOf G K)).mapCalls (liftCall K)


/-- A first step of the parties calls a base OT with the column of the matrix. -/
theorem pStart_colCall (k : IKNPKey κ m) (st : PSt κ m M) (e : (InEv m M ⊕ WakeEv κ) ⊕ P)
    (i : Fin κ) (p : BPair m) (h : (pStart H φS φR ans k st e).2 = .inl (.inl (.inl (i, p)))) :
    p.1 = fun j => k.1 j i := by
  rcases st with ⟨xo, ro, cols, ys, yr, ph⟩
  rcases e with ((x | r) | (w | _)) | q <;> cases xo <;> cases ro <;>
    simp [pStart, sCall, rCall, iknpBaseIn] at h <;>
    (obtain ⟨rfl, rfl⟩ := h; rfl)


omit [NeZero κ] in
/-- A step on an answer calls a base OT with the column of the matrix. -/
theorem pResume_colCall (k : IKNPKey κ m) (st : PSt κ m M) (o : HOut m ⊕ ChanHOut (Msg m M))
    (i : Fin κ) (p : BPair m)
    (h : (pResume (L := L) H k st o).2 = .inl (.inl (.inl (i, p)))) :
    p.1 = fun j => k.1 j i := by
  rcases st with ⟨xo, ro, cols, ys, yr, ph⟩
  rcases ph with _ | j | j | i' | _ | _ <;> simp only [pResume] at h
  · simp at h
  · split at h <;> simp [sCall] at h
  · split at h
    · simp only [rCall, Prod.mk.injEq, Sum.inl.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · simp at h
  · rcases o with (_ | _ | q) | _ <;> simp at h
    · simp only [pFetch] at h
      split at h
      · split at h <;> simp at h
      · simp at h
  · simp at h
  · rcases o with _ | (_ | _ | _) <;> simp at h

/-- The IKNP parties beside the forwarding of the adversary port decide deterministically, and call
a base OT with the column of the matrix. -/
theorem partyW_tensor_start_emits (k : IKNPKey κ m) (s : PSt κ m M × Unit)
    (e : ((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M) :
    MultiHybrid.EmitsQ (((partyW H φS φR ans k).tensor
      (MultiHybrid.idSim (AEv κ m M) (AOut m M))).start s e) (colCall k.1) := by
  rcases e with e | a
  · refine ⟨(((pStart H φS φR ans k s.1 e).1, s.2),
      Sum.map Sum.inl Sum.inl (pStart H φS φR ans k s.1 e).2),
      by simp [MultiHybrid.tensor, SPComp.map, SPComp.pure_bind], ?_⟩
    intro g hg i p hgp
    subst hgp
    rcases hd : (pStart H φS φR ans k s.1 e).2 with (g' | o)
    · simp only [hd, Sum.map_inl, Sum.inl.injEq] at hg
      subst hg
      exact pStart_colCall H φS φR ans k s.1 e i p hd
    · simp [hd] at hg
  · refine ⟨((s.1, ()), .inl (.inr a)),
      by simp [MultiHybrid.tensor, MultiHybrid.idSim, SPComp.map, SPComp.pure_bind], ?_⟩
    intro g hg i p hgp
    subst hgp
    simp at hg

/-- The resumptions of the IKNP parties beside the forwarding of the adversary port decide
deterministically, and call a base OT with the column of the matrix. -/
theorem partyW_tensor_resume_emits (k : IKNPKey κ m) (s : PSt κ m M × Unit)
    (o : (HOut m ⊕ ChanHOut (Msg m M)) ⊕ AOut m M) :
    MultiHybrid.EmitsQ (((partyW H φS φR ans k).tensor
      (MultiHybrid.idSim (AEv κ m M) (AOut m M))).resume s o) (colCall k.1) := by
  rcases o with o | a
  · refine ⟨(((pResume (L := L) H k s.1 o).1, s.2),
      Sum.map Sum.inl Sum.inl (pResume (L := L) H k s.1 o).2),
      by simp [MultiHybrid.tensor, SPComp.map, SPComp.pure_bind], ?_⟩
    intro g hg i p hgp
    subst hgp
    rcases hd : (pResume (L := L) H k s.1 o).2 with (g' | o')
    · simp only [hd, Sum.map_inl, Sum.inl.injEq] at hg
      subst hg
      exact pResume_colCall H k s.1 o i p hd
    · simp [hd] at hg
  · refine ⟨((s.1, ()), .inr (.inr a)),
      by simp [MultiHybrid.tensor, MultiHybrid.idSim, SPComp.map, SPComp.pure_bind], ?_⟩
    intro g hg i p hgp
    subst hgp
    simp at hg

omit [AddCommGroup M] [NeZero κ] in
/-- The ALSZ base OTs beside the channel, on the lifted calls, commute with `stMap` to the IKNP
base OTs beside the channel, on the calls with the columns of the matrix of `tOf G K`. -/
theorem sub_stMap (K : AKey κ Seed)
    (t : (Fin κ → SchedSt (AIn Seed m) Bool (Fin m → Bool)) × ChanSt (Msg m M))
    (g : (HEv κ m ⊕ ChanHEv (Msg m M)) ⊕ AEv κ m M) (hg : colCall (tOf G K).1 g) :
    SPComp.map (fun p => ((stMap G ∘ p.1.1, p.1.2), p.2))
        (((FOTSchedPar (Fin κ) (alszOut G)).withChan (chanC m M)).step t
          (Sum.map (liftCall K) id g)) =
      ((baseG κ m).withChan (chanC m M)).step (stMap G ∘ t.1, t.2) g := by
  obtain ⟨t, u⟩ := t
  rcases g with ((⟨i, p⟩ | ⟨i, b⟩) | ch) | (⟨i, a⟩ | d)
  · have hp : p.1 = G.stretch (K.1.1 i) := hg i p rfl
    have h := stMap_sendStep G (t i) ((K.1.1 i, K.1.2 i), p.1 + p.2)
    rw [colPair_lift G _ _ p hp] at h
    simp only [Sys.withChan, Sys.mapPorts, Sys.relabel, chanEv, chanOut, Sum.map_inl, liftCall,
      Sys.par_step_inl, FOTSchedPar, baseG, Sys.ofPorts_step_inl, Sys.indexed_step,
      FOTSched.sendSys, SPComp.map, SPComp.pure_bind, Function.comp_update,
      Function.comp_apply, ← h]
  · have h := stMap_recvStep G (t i) b
    simp only [Sys.withChan, Sys.mapPorts, Sys.relabel, chanEv, chanOut, Sum.map_inl,
      liftCall, Sys.par_step_inl, FOTSchedPar, baseG, Sys.ofPorts_step_inl, Sys.ofPorts_step_inr,
      Sys.indexed_step, FOTSched.recvSys, SPComp.map, SPComp.pure_bind,
      Function.comp_update, Function.comp_apply, ← h]
  · simp [Sys.withChan, Sys.mapPorts, Sys.relabel, chanEv, chanOut, liftCall, SPComp.map,
      SPComp.pure_bind, SPComp.bind_assoc]
  · have h := stMap_schedStep G (t i) a
    simp only [Sys.withChan, Sys.mapPorts, Sys.relabel, chanEv, chanOut, Sum.map_inr, id,
      Sys.par_step_inl, FOTSchedPar, baseG, Sys.ofPorts_step_inr, Sys.indexed_step,
      FOTSched.schedSys, SPComp.map, SPComp.pure_bind, Function.comp_update,
      Function.comp_apply, ← h]
  · simp [Sys.withChan, Sys.mapPorts, Sys.relabel, chanEv, chanOut, SPComp.map,
      SPComp.pure_bind, SPComp.bind_assoc]

/-- The ALSZ parties with the key `K` over the ALSZ base OTs beside the channel. -/
noncomputable abbrev alszK (K : AKey κ Seed) :=
  ((alszPartyW H φS φR ans G K).tensor (MultiHybrid.idSim (AEv κ m M) (AOut m M))).withSub
    ((FOTSchedPar (Fin κ) (alszOut G)).withChan (chanC m M))

/-- The IKNP parties with the key `k` over the IKNP base OTs beside the channel. -/
noncomputable abbrev iknpK (k : IKNPKey κ m) :=
  ((partyW H φS φR ans k).tensor (MultiHybrid.idSim (AEv κ m M) (AOut m M))).withSub
    ((baseG κ m).withChan (chanC m M))

/-- **The ALSZ parties are the IKNP parties with the matrix of PRG outputs.** With the key `K`,
the ALSZ parties over the ALSZ base OTs beside the channel have the view of the IKNP parties with
the key `tOf G K` over the IKNP base OTs beside the channel. -/
theorem view_alszK {ζ : Type} (K : AKey κ Seed)
    (Z : Strat ζ (((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M) ((InOut m M ⊕ L) ⊕ AOut m M)) :
    view (alszK H φS φR ans G K) Z = view (iknpK H φS φR ans (tOf G K)) Z :=
  view_eq_of_stepMap _ _ (fun t => (t.1, (stMap G ∘ t.2.1, t.2.2))) rfl
    (fun t e => MultiHybrid.withSub_callMap_on _ _ (Sum.map (liftCall K) id)
      (colCall (tOf G K).1) rfl
      (MultiHybrid.tensor_mapCalls_start _ _ _) (MultiHybrid.tensor_mapCalls_resume _ _ _)
      (fun _ _ => rfl) (partyW_tensor_start_emits H φS φR ans _)
      (partyW_tensor_resume_emits H φS φR ans _)
      ((FOTSchedPar (Fin κ) (alszOut G)).withChan (chanC m M)) ((baseG κ m).withChan (chanC m M))
      (fun t => (stMap G ∘ t.1, t.2)) (sub_stMap G K) t e) Z

/-- An activation of the parties that reads no randomness outputs at once, the same for every
key. -/
theorem pStart_indep (k k' : IKNPKey κ m) (st : PSt κ m M) (e : (InEv m M ⊕ WakeEv κ) ⊕ P)
    (hu : partyUses st e = false) :
    ∃ r : PSt κ m M × (InOut m M ⊕ L), pStart H φS φR ans k st e = (r.1, .inr r.2) ∧
      pStart H φS φR ans k' st e = (r.1, .inr r.2) := by
  rcases st with ⟨xo, ro, cols, ys, yr, ph⟩
  rcases e with ((x | r) | (w | _)) | q
  · simp [partyUses] at hu
  · simp [partyUses] at hu
  all_goals
    simp only [partyUses, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at hu
    obtain ⟨rfl, rfl⟩ := hu
  · exact ⟨(⟨none, none, cols, ys, yr, ph⟩, .inl (.inl false)), rfl, rfl⟩
  · exact ⟨(⟨none, none, cols, ys, yr, ph⟩, .inl (.inr none)), rfl, rfl⟩
  · exact ⟨(⟨none, none, cols, ys, yr, ph⟩, .inr (ans none none q)), rfl, rfl⟩

end Party

section Lazy

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) {P L LS LR : Type}
  (φS : IKNPSenderView κ m Unit → LS) (φR : IKNPReceiverView κ m M Unit × (Fin m → M) → LR)
  (ans : Option LS → Option LR → P → L) (G : PRGDef Seed (Fin m → Bool)) [NeZero κ]
  [Fintype Seed] [Inhabited Seed]

/-- **The ALSZ parties with their own draw**: the parties of `alszPartyW` whose key, the seed
pairs and the secret, is drawn uniformly in their state at the first input of a party. -/
noncomputable def alszLazy :
    MultiHybrid (Option (AKey κ Seed) × PSt κ m M) ((InEv m M ⊕ WakeEv κ) ⊕ P) (InOut m M ⊕ L)
      (AHEv κ Seed m ⊕ ChanHEv (Msg m M)) (HOut m ⊕ ChanHOut (Msg m M)) :=
  MultiHybrid.lazyKey (alszPartyW H φS φR ans G) default (PMF.uniformFintype _) partyUses

/-- ALSZ over the `κ` ALSZ base OTs `FOTSchedPar (Fin κ) (alszOut G)` beside the channel, the
adversary ports forwarded. -/
noncomputable abbrev alszOver :=
  ((alszLazy H φS φR ans G).tensor (MultiHybrid.idSim (AEv κ m M) (AOut m M))).withSub
    ((FOTSchedPar (Fin κ) (alszOut G)).withChan (chanC m M))

/-- IKNP over the `κ` column OTs beside the channel, the adversary ports forwarded: the real
system of `IKNPPVW.iknpLazy_realizesSim`. -/
noncomputable abbrev iknpOver :=
  ((partyLazy H φS φR ans).tensor (MultiHybrid.idSim (AEv κ m M) (AOut m M))).withSub
    ((baseG κ m).withChan (chanC m M))

/-- The view of `alszOver` is the average over the uniform key of the views with the key. -/
theorem view_alszOver {ζ : Type}
    (Z : Strat ζ (((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M) ((InOut m M ⊕ L) ⊕ AOut m M)) :
    view (alszOver H φS φR ans G) Z =
      SPComp.bind (SPComp.sample (AKey κ Seed)) fun K => view (alszK H φS φR ans G K) Z := by
  have hind : ∀ K st e, partyUses st e = false → ∃ r : PSt κ m M × (InOut m M ⊕ L),
      (alszPartyW H φS φR ans G K).start st e = SPComp.pure (r.1, .inr r.2) ∧
        (alszPartyW H φS φR ans G default).start st e = SPComp.pure (r.1, .inr r.2) := by
    intro K st e hu
    obtain ⟨r, h, h'⟩ := pStart_indep H φS φR ans (tOf G K) (tOf G default) st e hu
    exact ⟨r, by simp [alszPartyW, MultiHybrid.mapCalls, h, SPComp.map, SPComp.pure_bind],
      by simp [alszPartyW, MultiHybrid.mapCalls, h', SPComp.map, SPComp.pure_bind]⟩
  have h := MultiHybrid.view_lazyKey_tensor (alszPartyW H φS φR ans G) default
    (PMF.uniformFintype (AKey κ Seed)) partyUses (EA := AEv κ m M) (OA := AOut m M)
    ((FOTSchedPar (Fin κ) (alszOut G)).withChan (chanC m M))
    (Sys.withChan_portTyped (FOTSchedPar_portTyped _) (FChan_portTyped _ _)) (fun _ => rfl)
    (fun _ => rfl) hind Z
  rw [NonUniform.ofPMF_uniformFintype, NonUniform.sampleFrom_uniform] at h
  exact h

/-- The view of `iknpOver` is the average over the uniform key of the views with the key. -/
theorem view_iknpOver {ζ : Type}
    (Z : Strat ζ (((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M) ((InOut m M ⊕ L) ⊕ AOut m M)) :
    view (iknpOver H φS φR ans) Z =
      SPComp.bind (SPComp.sample (IKNPKey κ m)) fun k => view (iknpK H φS φR ans k) Z := by
  have hind : ∀ k st e, partyUses st e = false → ∃ r : PSt κ m M × (InOut m M ⊕ L),
      (partyW H φS φR ans k).start st e = SPComp.pure (r.1, .inr r.2) ∧
        (partyW H φS φR ans default).start st e = SPComp.pure (r.1, .inr r.2) := by
    intro k st e hu
    obtain ⟨r, h, h'⟩ := pStart_indep H φS φR ans k default st e hu
    exact ⟨r, by simp [h], by simp [h']⟩
  have h := MultiHybrid.view_lazyKey_tensor (partyW H φS φR ans) default
    (PMF.uniformFintype (IKNPKey κ m)) partyUses (EA := AEv κ m M) (OA := AOut m M)
    ((baseG κ m).withChan (chanC m M))
    (Sys.withChan_portTyped (FOTSchedPar_portTyped _) (FChan_portTyped _ _)) (fun _ => rfl)
    (fun _ => rfl) hind Z
  rw [NonUniform.ofPMF_uniformFintype, NonUniform.sampleFrom_uniform] at h
  exact h

/-- The world of the environment `Z` with the key `k`: `Z`, from its heap, against IKNP with the
key `k`, and its distinguisher. -/
noncomputable def alszWorld {ζ : Type}
    (Z : Env (Strat ζ (((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M) ((InOut m M ⊕ L) ⊕ AOut m M)) ζ) :
    IKNPKey κ m → SPComp Bool :=
  fixHeap Z.heap fun k => SPComp.bind (view (iknpK H φS φR ans k) Z.input) Z.dist

/-- The distinguisher of the PRG hybrids for the keyed world `W`: on the columns `U` of the
matrix, draw the secret and run `W` with the matrix of columns `U` and the secret. -/
noncomputable def alszDist (W : IKNPKey κ m → SPComp Bool) (U : Fin κ → Fin m → Bool) :
    SPComp Bool :=
  SPComp.bind (SPComp.sample (Fin κ → Bool)) fun s => W (fun j i => U i j, s)

/-- **The reduction of ALSZ to the PRG** for the hop `i`, over the keyed world `W`: on a
challenge `y`, draw the seeds `k₀` and uniform columns, form the columns `U j` uniform for
`j < i`, `y` at `i` and `G k₀ⱼ` for `j > i`, and run `alszDist W`. -/
noncomputable def alszRed (i : Fin κ) (W : IKNPKey κ m → SPComp Bool) :
    (Fin m → Bool) → SPComp Bool :=
  prgHybRed G (alszDist W) i

/-- **The reduction of ALSZ to the PRG** for the hop `i` and the environment `Z`: `alszRed` over
the world of `Z`. -/
noncomputable def alszPrgRed {ζ : Type} (i : Fin κ)
    (Z : Env (Strat ζ (((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M) ((InOut m M ⊕ L) ⊕ AOut m M)) ζ) :
    (Fin m → Bool) → SPComp Bool :=
  alszRed G i (alszWorld H φS φR ans Z)

/-- The transposition of a matrix. -/
def transposeEquiv (κ m : ℕ) : (Fin κ → Fin m → Bool) ≃ (Fin m → Fin κ → Bool) where
  toFun U j i := U i j
  invFun T i j := T j i
  left_inv _ := rfl
  right_inv _ := rfl

/-- **ALSZ over the ALSZ base OTs realizes IKNP over the column OTs.** The ALSZ parties with
their own draw over the `κ` base OTs `FOTSchedPar (Fin κ) (alszOut G)` beside the channel
realize the IKNP parties with their own draw over the `κ` column OTs `baseG κ m` beside the
channel, on the same interface, with bound the sum over the columns `i < κ` of the PRG advantage
of `alszPrgRed G i Z`: the ALSZ parties are the IKNP parties whose matrix has the columns
`G k₀ᵢ` (`view_alszK`), and the `κ` PRG outputs replace the uniform columns one by one
(`prg_pi_hybrid`). -/
theorem alszOver_realizes :
    Realizes (alszOver H φS φR ans G) (iknpOver H φS φR ans)
      (fun _ Z => ∑ i : Fin κ, PRG_Advantage G (alszPrgRed H φS φR ans G i Z)) := by
  intro ζ Z
  change absDiff _ _ ≤ _
  rw [view_alszOver, view_iknpOver]
  simp only [view_alszK, SPComp.bind_assoc]
  rw [prTrue_bind_fixHeap (SPComp.sample_isPure _) _ Z.heap,
    prTrue_bind_fixHeap (SPComp.sample_isPure _) _ Z.heap]
  have hA : SPComp.bind (SPComp.sample (AKey κ Seed))
      (fixHeap Z.heap fun K => SPComp.bind (view (iknpK H φS φR ans (tOf G K)) Z.input) Z.dist) =
      SPComp.bind (SPComp.sample (Fin κ → Seed)) fun k₀ =>
        alszDist (alszWorld H φS φR ans Z) (G.stretch ∘ k₀) := by
    simp only [SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1
    funext k₀
    exact Relational.dead_sample (α := Fin κ → Seed)
      (alszDist (alszWorld H φS φR ans Z) (G.stretch ∘ k₀))
  have hI : SPComp.bind (SPComp.sample (IKNPKey κ m))
      (fixHeap Z.heap fun k => SPComp.bind (view (iknpK H φS φR ans k) Z.input) Z.dist) =
      SPComp.bind (SPComp.sample (Fin κ → Fin m → Bool))
        (alszDist (alszWorld H φS φR ans Z)) := by
    simp only [SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind]
    exact (SPComp.sample_bind_equiv (transposeEquiv κ m) _).symm
  rw [hA, hI]
  exact prg_pi_hybrid G (alszDist (alszWorld H φS φR ans Z))

end Lazy

/-! ## ALSZ over the seed OTs -/

section Compose

open CatCrypt.Crypto.OT.IKNPPVW

/-- The adversary events of the ALSZ base OTs beside the IKNP channel. -/
abbrev AEvA (κ m : ℕ) (M : Type) := (Fin κ × OAEv m) ⊕ ChanAEv (Msg m M)

/-- The adversary outputs of the ALSZ base OTs beside the IKNP channel. -/
abbrev AOutA (m : ℕ) (M : Type) := OAOut m ⊕ ChanAOut (Msg m M) Unit

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) {P L LS LR : Type}
  (φS : IKNPSenderView κ m Unit → LS) (φR : IKNPReceiverView κ m M Unit × (Fin m → M) → LR)
  (ans : Option LS → Option LR → P → L) (G : PRGDef Seed (Fin m → Bool)) [NeZero κ]
  [Fintype Seed] [Inhabited Seed]

/-- **ALSZ over the `κ` scheduled seed OTs**: the ALSZ parties with their own draw over the `κ`
base OTs of ALSZ (each a scheduled seed OT beside the secure channel for its correction string)
beside the IKNP channel, the adversary ports forwarded. -/
noncomputable abbrev alszSeed :=
  ((alszLazy H φS φR ans G).tensor (MultiHybrid.idSim (AEvA κ m M) (AOutA m M))).withSub
    ((alszBase κ G).withChan (chanC m M))

variable (κ m M P L) in
/-- **The simulator of ALSZ over the seed OTs**: the forwarding of the parties' port beside the
indexed copies `simKeepA` of the simulator of one base OT and the forwarding of the IKNP
channel's adversary port, over the IKNP parties over the column OTs. -/
noncomputable def simALSZ :
    Simulator (((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEvA κ m M) ((InOut m M ⊕ L) ⊕ AOutA m M)
      (((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M) ((InOut m M ⊕ L) ⊕ AOut m M)
      ((vF κ m M P L).sum (((PubView.eqView : PubView (OAEv m) (OAOut m)).indexed (Fin κ)).sum
        PubView.eqView))
      ((vF κ m M P L).sum (((PubView.eqView : PubView SchedEv SchedOut).indexed (Fin κ)).sum
        PubView.eqView)) :=
  Simulator.ofMultiHybrid
    (MultiHybrid.extendFwd ((InEv m M ⊕ WakeEv κ) ⊕ P) (InOut m M ⊕ L)
      ((simKeepA κ m).tensor (MultiHybrid.idSim (ChanAEv (Msg m M)) (ChanAOut (Msg m M) Unit))))
    (MultiHybrid.Opaque.extendFwd (vF κ m M P L)
      (((MultiHybrid.opaque_eqView (simA m)).indexedKeep (ι := Fin κ)).tensor
        (MultiHybrid.idSim_opaque PubView.eqView)))

/-- **ALSZ realizes the IKNP wake parties over the column OTs** (genuine UC). Over the `κ`
scheduled seed OTs (`FOTSched seedOut`, each beside the secure channel for its correction
string), the ALSZ parties with their own draw realize the IKNP wake parties with their own draw
over the `κ` scheduled column OTs `baseG κ m`, both beside the IKNP channel, behind `simALSZ`,
which simulates each base OT of ALSZ from the scheduler of the column OT (`simA`). The bound is
the sum over the columns `i < κ` of the PRG advantage of the explicit reduction
`alszPrgRed G i`, at the environment reduced through the extended simulator: the base OTs of
ALSZ realize `FOTSchedPar (Fin κ) (alszOut G)` at distance `0` (`alszBase_realizesSim`), and the
ALSZ parties over them realize the IKNP parties over the column OTs with the PRG bound
(`alszOver_realizes`), composed by `RealizesSim.modular_withChan`. The corruption events of
both are answered by the IKNP views of the parties, in which the matrix has the columns
`G k₀ᵢ`. -/
theorem alsz_realizes_iknpWake :
    RealizesSim (alszSeed H φS φR ans G) (iknpOver H φS φR ans) (simALSZ κ m M P L)
      (fun _ Z => ∑ i : Fin κ, PRG_Advantage G (alszPrgRed H φS φR ans G i
        ((MultiHybrid.extendFwd ((InEv m M ⊕ WakeEv κ) ⊕ P) (InOut m M ⊕ L)
          ((simKeepA κ m).tensor
            (MultiHybrid.idSim (ChanAEv (Msg m M)) (ChanAOut (Msg m M) Unit)))).reduceEnv
          (.inr (.inr .idle)) Z))) := by
  have hmod := RealizesSim.modular_withChan (VF := vF κ m M P L) (VC := PubView.eqView)
    (VD := PubView.eqView) (alszLazy H φS φR ans G) (simKeepA κ m)
    ((MultiHybrid.opaque_eqView _).indexedKeep) (alszBase κ G) (FOTSchedPar (Fin κ) (alszOut G))
    (FOTSchedPar_portTyped _) (chanC m M) (FChan_portTyped _ _) (FChan_noFail _ _)
    (iknpOver H φS φR ans) (Simulator.id _ _ _) (.inr (default, .inl .idle))
    (.inr (.inr .idle)) (.inr (.inr .idle)) (.inr (.inr .idle)) ⟨_, alszBase_idleAt G⟩
    ⟨_, simKeepA_idleAt G⟩ ⟨_, fun t => withChan_idle _ t⟩
    ⟨_, idleAt_tensor_tensor_fwd _ _ _ _ _ fun t => withChan_idle _ t⟩
    ⟨_, idleAt_tensor_fwd _ _ _ _ fun t => withChan_idle _ t⟩
    ⟨_, idleAt_tensor_fwd _ _ _ _ fun t => withChan_idle _ t⟩ (alszBase_realizesSim G)
    (alszOver_realizes H φS φR ans G)
  exact fun ζ Z => le_of_le_of_eq (hmod ζ Z) (zero_add _)

end Compose

end Parties

end CatCrypt.Crypto.OT.ALSZ
