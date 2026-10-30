/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.FOTSched
public import CatCryptCore.Crypto.UCParallel
public import CatCryptCore.Crypto.UCRoundHybrid

/-!
# Realizations of indexed copies

The system `X.indexed` (`Sys.indexed`) runs one independent copy of `X` for each index; the event
`(i, e)` is the event `e` of the copy `i`. If `X` realizes `X'` with bound `b`, then `κ` copies of
`X` realize `κ` copies of `X'` with the sum over the copies `j < κ` of `b` at the environment
reduced through the context `indexedCtx X' X (· < j) j` (`realizes_indexed`). The proof is a
hybrid over the copies: in the hybrid world `j` the copies below `j` run `X'` and the others run
`X` (`Sys.indexedMix`); the worlds `j` and `j + 1` differ in the copy `j` only, and each is the
context `indexedCtx` of the copy `j` over the subroutine `X` or `X'`.

The indexed simulator `S.indexed` (`MultiHybrid.indexed`) runs one copy of the multi-call
simulator `S` for each index and records the index of the active copy, to which it passes the
answers of the subroutine. Over the indexed subroutine it is the indexed copies of `S` over the
subroutine (`MultiHybrid.realizes_indexed_withSub`), and it is opaque for the indexed views when
`S` is opaque (`MultiHybrid.Opaque.indexed`). Together these give the realization behind the
indexed simulator (`RealizesSim.indexed`).

## Main definitions

* `Sys.indexedMix`: the copies satisfying a predicate run one system, the others another.
* `MultiHybrid.indexedCtx`: the context of one copy in a mixed family.
* `MultiHybrid.indexed`: the indexed copies of a multi-call simulator.
* `PubView.indexed`: the view of the indexed interface.

## Main results

* `realizes_indexedMix_hop`: one step of the hybrid over the copies.
* `realizes_indexed`: realizations of indexed copies, with the sum of the bounds of the copies.
* `MultiHybrid.realizes_indexed_withSub`, `MultiHybrid.Opaque.indexed`: the indexed simulator.
* `RealizesSim.indexed`: realization behind the indexed simulator.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete CatCrypt.Relational
open scoped ENNReal

/-! ## Mixed families of copies -/

namespace Sys

variable {ι τ τ' E O : Type} [DecidableEq ι]

/-- The copies `i` with `P i` run `X'` on the first family of states, the others run `X` on the
second family; the event `(i, e)` is the event `e` of the copy `i`. -/
noncomputable def indexedMix (X' : Sys τ' E O) (X : Sys τ E O) (P : ι → Prop)
    [DecidablePred P] : Sys ((ι → τ') × (ι → τ)) (ι × E) O where
  init := (fun _ => X'.init, fun _ => X.init)
  step s e := if P e.1 then
      SPComp.map (fun q => ((Function.update s.1 e.1 q.1, s.2), q.2)) (X'.step (s.1 e.1) e.2)
    else SPComp.map (fun q => ((s.1, Function.update s.2 e.1 q.1), q.2)) (X.step (s.2 e.1) e.2)

/-- A mixed family of lossless systems is lossless. -/
theorem indexedMix_noFail {X' : Sys τ' E O} {X : Sys τ E O} (P : ι → Prop) [DecidablePred P]
    (hX' : ∀ t e, SPComp.NoFail (X'.step t e)) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    (s : (ι → τ') × (ι → τ)) (e : ι × E) : SPComp.NoFail ((indexedMix X' X P).step s e) := by
  by_cases h : P e.1
  · simp only [indexedMix, h, ↓reduceIte]
    exact Assumptions.SPComp.bind_noFail (hX' _ _) fun _ => SPComp.pure_noFail _
  · simp only [indexedMix, h, ↓reduceIte]
    exact Assumptions.SPComp.bind_noFail (hX _ _) fun _ => SPComp.pure_noFail _

end Sys

/-! ## The context of one copy -/

namespace MultiHybrid

variable {ι τ τ' E O : Type} [DecidableEq ι]

/-- The context of the copy `j` in the mixed family `Sys.indexedMix X' X P`: an event of the copy
`j` is passed to the subroutine and its answer returned; an event of another copy is answered by
the mixed family inside the activation. -/
noncomputable def indexedCtx (X' : Sys τ' E O) (X : Sys τ E O) (P : ι → Prop) [DecidablePred P]
    (hX' : ∀ t e, SPComp.NoFail (X'.step t e)) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    (j : ι) : MultiHybrid ((ι → τ') × (ι → τ)) (ι × E) O E O where
  init := (Sys.indexedMix X' X P).init
  fuel := 0
  start s e := if e.1 = j then SPComp.pure (s, .inl e.2)
    else SPComp.map (fun q => (q.1, .inr q.2)) ((Sys.indexedMix X' X P).step s e)
  resume s o := SPComp.pure (s, .inr o)
  finish s o := SPComp.pure (s, o)
  start_noFail s e := by
    by_cases h : e.1 = j
    · simp only [h, ↓reduceIte]
      exact SPComp.pure_noFail _
    · simp only [h, ↓reduceIte]
      exact Assumptions.SPComp.bind_noFail (Sys.indexedMix_noFail P hX' hX s e)
        fun _ => SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

variable {X' : Sys τ' E O} {X : Sys τ E O} {P : ι → Prop} [DecidablePred P]
  {hX' : ∀ t e, SPComp.NoFail (X'.step t e)} {hX : ∀ t e, SPComp.NoFail (X.step t e)}

/-- The context of the copy `j` over `X` is the mixed family in which the copy `j` runs `X`, with
the subroutine state at the place `j` of the second family. -/
theorem indexedCtx_withSub_step_real {j : ι} (hj : ¬ P j) (s : (ι → τ') × (ι → τ)) (x : τ)
    (e : ι × E) :
    SPComp.map (fun p => ((p.1.1.1, Function.update p.1.1.2 j p.1.2), p.2))
        (((indexedCtx X' X P hX' hX j).withSub X).step (s, x) e) =
      (Sys.indexedMix X' X P).step (s.1, Function.update s.2 j x) e := by
  obtain ⟨i, e⟩ := e
  obtain ⟨s₁, s₂⟩ := s
  by_cases hi : i = j
  · subst hi
    simp [withSub, indexedCtx, drive, Sys.indexedMix, hj, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
  · by_cases hPi : P i
    · simp [withSub, indexedCtx, drive, Sys.indexedMix, hi, hPi, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
    · simp [withSub, indexedCtx, drive, Sys.indexedMix, hi, hPi, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind, Function.update_comm hi]

/-- The context of the copy `j` over `X'` is the mixed family for `P'` in which the copy `j` runs
`X'`, with the subroutine state at the place `j` of the first family, when `P'` agrees with `P`
on the other copies. -/
theorem indexedCtx_withSub_step_ideal {P' : ι → Prop} [DecidablePred P'] {j : ι} (hj : P' j)
    (hP : ∀ i, i ≠ j → (P' i ↔ P i)) (s : (ι → τ') × (ι → τ)) (x : τ') (e : ι × E) :
    SPComp.map (fun p => ((Function.update p.1.1.1 j p.1.2, p.1.1.2), p.2))
        (((indexedCtx X' X P hX' hX j).withSub X').step (s, x) e) =
      (Sys.indexedMix X' X P').step (Function.update s.1 j x, s.2) e := by
  obtain ⟨i, e⟩ := e
  obtain ⟨s₁, s₂⟩ := s
  by_cases hi : i = j
  · subst hi
    simp [withSub, indexedCtx, drive, Sys.indexedMix, hj, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
  · by_cases hPi : P i
    · have hP'i : P' i := (hP i hi).2 hPi
      simp [withSub, indexedCtx, drive, Sys.indexedMix, hi, hPi, hP'i, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind, Function.update_comm hi]
    · have hP'i : ¬ P' i := fun h => hPi ((hP i hi).1 h)
      simp [withSub, indexedCtx, drive, Sys.indexedMix, hi, hPi, hP'i, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind]

end MultiHybrid

/-! ## The hybrid over the copies -/

section Hybrid

variable {ι τ τ' E O : Type} [DecidableEq ι]

open MultiHybrid

/-- **One step of the hybrid over the copies.** If `X` realizes `X'` with bound `b`, both idle
at `idle`, then the mixed family for `P` realizes the mixed family for `P'` with bound `b` at the
environment reduced through the context of the copy `j`, when the copy `j` runs `X` in the first
family and `X'` in the second and the two predicates agree on the other copies. -/
theorem realizes_indexedMix_hop {X' : Sys τ' E O} {X : Sys τ E O}
    (hX' : ∀ t e, SPComp.NoFail (X'.step t e)) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    (P P' : ι → Prop) [DecidablePred P] [DecidablePred P'] (j : ι) (hj : ¬ P j) (hj' : P' j)
    (hP : ∀ i, i ≠ j → (P' i ↔ P i)) (idle : E) {oX oX' : O}
    (hXi : IdleAt X idle oX) (hX'i : IdleAt X' idle oX')
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes X X' b) :
    Realizes (Sys.indexedMix X' X P) (Sys.indexedMix X' X P')
      (fun ζ Z => b (RState ((ι → τ') × (ι → τ)) ζ E O)
        ((indexedCtx X' X P hX' hX j).reduceEnv idle Z)) := by
  intro ζ Z
  have h₁ : (view ((indexedCtx X' X P hX' hX j).withSub X) : Strat ζ (ι × E) O → SPComp ζ) =
      view (Sys.indexedMix X' X P) :=
    funext (view_eq_of_stepMap _ _ (fun p => (p.1.1, Function.update p.1.2 j p.2))
      (by simp [withSub, indexedCtx, Sys.indexedMix])
      (fun t e => indexedCtx_withSub_step_real hj t.1 t.2 e))
  have h₂ : (view ((indexedCtx X' X P hX' hX j).withSub X') : Strat ζ (ι × E) O → SPComp ζ) =
      view (Sys.indexedMix X' X P') :=
    funext (view_eq_of_stepMap _ _ (fun p => (Function.update p.1.1 j p.2, p.1.2))
      (by simp [withSub, indexedCtx, Sys.indexedMix])
      (fun t e => indexedCtx_withSub_step_ideal hj' hP t.1 t.2 e))
  change Env.gap _ _ Z ≤ _
  rw [← h₁, ← h₂]
  have ha := adv_withSub (indexedCtx X' X P hX' hX j) idle oX oX' X X' hXi hX'i Z
  unfold adv at ha
  rw [ha]
  exact h _ _

/-- **Realization of indexed copies.** If `X` realizes `X'` with bound `b`, both lossless and
idle at `idle`, then `κ` copies of `X` realize `κ` copies of `X'` with the sum over the copies
`j` of `b` at the environment reduced through the context of the copy `j` in the hybrid world
whose copies below `j` run `X'`. -/
theorem realizes_indexed {κ : ℕ} {X' : Sys τ' E O} {X : Sys τ E O}
    (hX' : ∀ t e, SPComp.NoFail (X'.step t e)) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    (idle : E) {oX oX' : O} (hXi : IdleAt X idle oX) (hX'i : IdleAt X' idle oX')
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes X X' b) :
    Realizes (X.indexed (ι := Fin κ)) (X'.indexed (ι := Fin κ))
      (fun ζ Z => ∑ j : Fin κ, b (RState ((Fin κ → τ') × (Fin κ → τ)) ζ E O)
        ((indexedCtx X' X (fun i : Fin κ => i.val < j.val) hX' hX j).reduceEnv idle Z)) := by
  let H : ℕ → Sys ((Fin κ → τ') × (Fin κ → τ)) (Fin κ × E) O :=
    fun n => Sys.indexedMix X' X (fun i : Fin κ => i.val < n)
  let c : ℕ → (ζ : Type) → Env (Strat ζ (Fin κ × E) O) ζ → ℝ≥0∞ := fun n ζ Z =>
    if hn : n < κ then b (RState ((Fin κ → τ') × (Fin κ → τ)) ζ E O)
      ((indexedCtx X' X (fun i : Fin κ => i.val < n) hX' hX ⟨n, hn⟩).reduceEnv idle Z)
    else 0
  have hhop : ∀ n < κ, Realizes (H n) (H (n + 1)) (c n) := by
    intro n hn
    have := realizes_indexedMix_hop hX' hX (fun i : Fin κ => i.val < n)
      (fun i : Fin κ => i.val < n + 1) ⟨n, hn⟩ (by simp) (by simp)
      (fun i hi => by
        have : i.val ≠ n := fun h' => hi (Fin.ext h')
        omega) idle hXi hX'i h
    intro ζ Z
    simp only [c, hn, ↓reduceDIte]
    exact this ζ Z
  have hmid := Realizes.hybrid H c κ hhop
  have h₀ : Realizes (X.indexed (ι := Fin κ)) (H 0) (fun _ _ => 0) :=
    realizes_zero_of_stepMap _ _ (fun t => (fun _ => X'.init, t)) rfl fun t ⟨i, e⟩ => by
      simp [H, Sys.indexedMix, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have h₁ : Realizes (H κ) (X'.indexed (ι := Fin κ)) (fun _ _ => 0) :=
    realizes_zero_of_stepMap _ _ Prod.fst rfl fun t ⟨i, e⟩ => by
      simp [H, Sys.indexedMix, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  intro ζ Z
  have := ((h₀.trans hmid).trans h₁) ζ Z
  simpa [c, Finset.sum_range] using this

end Hybrid

/-! ## The indexed simulator -/

namespace MultiHybrid

variable {ι σ τ E O EG OG : Type} [DecidableEq ι] [Inhabited ι]

/-- The indexed copies of the multi-call simulator `π`: the event `(i, e)` starts the copy `i`,
whose subroutine events go to the copy `i` of the subroutine; the state records the copy last
started, whose state the answers of the subroutine resume. -/
noncomputable def indexed (π : MultiHybrid σ E O EG OG) :
    MultiHybrid ((ι → σ) × ι) (ι × E) O (ι × EG) OG where
  init := (fun _ => π.init, default)
  fuel := π.fuel
  start s e := SPComp.map
    (fun r => ((Function.update s.1 e.1 r.1, e.1), Sum.map (Prod.mk e.1) id r.2))
    (π.start (s.1 e.1) e.2)
  resume s o := SPComp.map
    (fun r => ((Function.update s.1 s.2 r.1, s.2), Sum.map (Prod.mk s.2) id r.2))
    (π.resume (s.1 s.2) o)
  finish s o := SPComp.map (fun r => ((Function.update s.1 s.2 r.1, s.2), r.2))
    (π.finish (s.1 s.2) o)
  start_noFail _ _ :=
    Assumptions.SPComp.bind_noFail (π.start_noFail _ _) fun _ => SPComp.pure_noFail _
  resume_noFail _ _ :=
    Assumptions.SPComp.bind_noFail (π.resume_noFail _ _) fun _ => SPComp.pure_noFail _
  finish_noFail _ _ :=
    Assumptions.SPComp.bind_noFail (π.finish_noFail _ _) fun _ => SPComp.pure_noFail _

/-- Unfolding lemma of `MultiHybrid.indexed`: `start` on the event `(i, e)`. -/
@[simp] theorem indexed_start (π : MultiHybrid σ E O EG OG) (s : (ι → σ) × ι) (i : ι) (e : E) :
    π.indexed.start s (i, e) = SPComp.map
      (fun r => ((Function.update s.1 i r.1, i), Sum.map (Prod.mk i) id r.2))
      (π.start (s.1 i) e) := rfl

/-- Unfolding lemma of `MultiHybrid.indexed`: `resume` from the state `(ss, i)`. -/
@[simp] theorem indexed_resume (π : MultiHybrid σ E O EG OG) (ss : ι → σ) (i : ι) (o : OG) :
    π.indexed.resume (ss, i) o = SPComp.map
      (fun r => ((Function.update ss i r.1, i), Sum.map (Prod.mk i) id r.2))
      (π.resume (ss i) o) := rfl

/-- Unfolding lemma of `MultiHybrid.indexed`: `finish` from the state `(ss, i)`. -/
@[simp] theorem indexed_finish (π : MultiHybrid σ E O EG OG) (ss : ι → σ) (i : ι) (o : OG) :
    π.indexed.finish (ss, i) o =
      SPComp.map (fun r => ((Function.update ss i r.1, i), r.2)) (π.finish (ss i) o) := rfl

/-- The rest of an activation of the indexed simulator over the indexed subroutine, on the copy
`i`, is the rest of the activation of the copy `i` over the copy `i` of the subroutine. -/
theorem drive_indexed (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) :
    ∀ (n : ℕ) (ss : ι → σ) (i : ι) (d : EG ⊕ O) (ts : ι → τ),
      π.indexed.drive (X.indexed (ι := ι)) n (ss, i) (Sum.map (Prod.mk i) id d) ts =
        SPComp.map (fun p => ((Function.update ss i p.1, i), Function.update ts i p.2.1, p.2.2))
          (π.drive X n (ss i) d (ts i)) := by
  intro n
  induction n with
  | zero =>
    rintro ss i (g | o) ts
    · simp [drive, indexed, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp [drive, SPComp.map, SPComp.pure_bind]
  | succ n ih =>
    rintro ss i (g | o) ts
    · simp only [drive, Sum.map_inl, Sys.indexed_step, indexed_resume, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind, ih, Function.update_self, Function.update_idem]
    · simp [drive, SPComp.map, SPComp.pure_bind]

/-- The indexed simulator over the indexed subroutine and the indexed copies of the simulator
over the subroutine realize each other at distance `0`. -/
theorem realizes_indexed_withSub (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) :
    Realizes ((π.indexed (ι := ι)).withSub (X.indexed (ι := ι)))
      ((π.withSub X).indexed (ι := ι)) (fun _ _ => 0) := by
  refine realizes_zero_of_stepMap _ _ (fun s k => (s.1.1 k, s.2 k)) rfl ?_
  rintro ⟨⟨ss, a⟩, ts⟩ ⟨i, e⟩
  simp only [withSub, Sys.indexed_step, indexed_start, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind, drive_indexed, Function.update_self, Function.update_idem]
  have hu : ∀ (x : σ) (y : τ), Function.update (fun k => (ss k, ts k)) i (x, y) =
      fun k => (Function.update ss i x k, Function.update ts i y k) := by
    intro x y
    funext k
    rcases eq_or_ne k i with rfl | hk <;> simp [*]
  simp only [hu]
  rfl

end MultiHybrid

/-! ## Opacity of the indexed simulator -/

namespace PubView

variable {ι E O EG OG : Type}

/-- The view of the indexed interface `(ι × E, O)`: events of the same copy related by `V.ev`,
and outputs related by `V.out`. -/
def indexed (V : PubView E O) (ι : Type) : PubView (ι × E) O where
  ev e e' := e.1 = e'.1 ∧ V.ev e.2 e'.2
  out := V.out

/-- Related decisions tagged with one copy are related decisions of the indexed views. -/
theorem stepRel_indexed {V : PubView E O} {W : PubView EG OG} {d d' : EG ⊕ O} (i : ι)
    (h : StepRel V W d d') :
    StepRel (V.indexed ι) (W.indexed ι) (Sum.map (Prod.mk i) id d)
      (Sum.map (Prod.mk i) id d') := by
  rcases d with g | o <;> rcases d' with g' | o'
  · exact ⟨rfl, h⟩
  · exact h.elim
  · exact h.elim
  · exact h

end PubView

namespace MultiHybrid

variable {ι σ E O EG OG : Type} [DecidableEq ι] [Inhabited ι]
  {π : MultiHybrid σ E O EG OG} {V : PubView E O} {W : PubView EG OG}

omit [Inhabited ι] in
/-- A relation that holds pointwise holds pointwise after updating both families at one place
with related values. -/
private theorem forall_update {α β : Type} {R : α → β → Prop} {f : ι → α} {g : ι → β}
    (hfg : ∀ k, R (f k) (g k)) (i : ι) {a : α} {b : β} (hab : R a b) :
    ∀ k, R (Function.update f i a k) (Function.update g i b k) := by
  intro k
  rcases eq_or_ne k i with rfl | hk
  · simpa using hab
  · simpa [hk] using hfg k

/-- The unwinding relation of the indexed simulator: the same active copy, and the copies
pointwise related. -/
theorem Unwinding.indexed {R : σ → σ → Prop} (hR : Unwinding π V W R) :
    Unwinding (π.indexed (ι := ι)) (V.indexed ι) (W.indexed ι)
      (fun s s' => s.2 = s'.2 ∧ ∀ i, R (s.1 i) (s'.1 i)) where
  init := ⟨rfl, fun _ => hR.init⟩
  start := by
    rintro ⟨ss, a⟩ ⟨ss', a'⟩ ⟨i, e⟩ ⟨i', e'⟩ ⟨-, hs⟩ ⟨hi, he⟩
    dsimp only at hi
    subst hi
    rw [indexed_start, indexed_start]
    refine rHoare_bind (hR.start _ _ _ _ (hs i) he) fun _ _ =>
      rHoare_ret fun _ _ hp => ?_
    exact ⟨hp.1, ⟨rfl, forall_update hs i hp.2.1⟩, PubView.stepRel_indexed i hp.2.2⟩
  resume := by
    rintro ⟨ss, a⟩ ⟨ss', a'⟩ o o' ⟨ha, hs⟩ ho
    dsimp only at ha
    subst ha
    rw [indexed_resume, indexed_resume]
    refine rHoare_bind (hR.resume _ _ _ _ (hs a) ho) fun _ _ =>
      rHoare_ret fun _ _ hp => ?_
    exact ⟨hp.1, ⟨rfl, forall_update hs a hp.2.1⟩, PubView.stepRel_indexed a hp.2.2⟩
  finish := by
    rintro ⟨ss, a⟩ ⟨ss', a'⟩ o o' ⟨ha, hs⟩ ho
    dsimp only at ha
    subst ha
    rw [indexed_finish, indexed_finish]
    refine rHoare_bind (hR.finish _ _ _ _ (hs a) ho) fun _ _ =>
      rHoare_ret fun _ _ hp => ?_
    exact ⟨hp.1, ⟨rfl, forall_update hs a hp.2.1⟩, hp.2.2⟩

/-- **Opacity of the indexed simulator**: the indexed copies of a simulator opaque from `W` to
`V` are opaque from the indexed view of `W` to the indexed view of `V`. -/
theorem Opaque.indexed (h : π.Opaque V W) :
    (π.indexed (ι := ι)).Opaque (V.indexed ι) (W.indexed ι) := by
  obtain ⟨_, hR⟩ := h
  exact ⟨_, hR.indexed⟩

end MultiHybrid

/-! ## Realization behind the indexed simulator -/

open MultiHybrid in
/-- **Realization behind the indexed simulator.** If `X` realizes `I` behind the opaque
multi-call simulator `S` with bound `b`, then `κ` copies of `X` realize `κ` copies of `I` behind
the indexed simulator `S.indexed`, with the bound of `realizes_indexed` for `X` and `S` running
with `I`. -/
theorem RealizesSim.indexed {κ : ℕ} [NeZero κ] {σ τ υ E O EG OG : Type} {V : PubView E O}
    {W : PubView EG OG} {X : Sys τ E O} {I : Sys υ EG OG} (S : MultiHybrid σ E O EG OG)
    (hS : S.Opaque V W) (hX : ∀ t e, SPComp.NoFail (X.step t e))
    (hSI : ∀ t e, SPComp.NoFail ((S.withSub I).step t e)) (idle : E) {oX oSI : O}
    (hXi : IdleAt X idle oX) (hSIi : IdleAt (S.withSub I) idle oSI)
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : RealizesSim X I (Simulator.ofMultiHybrid S hS) b) :
    RealizesSim (X.indexed (ι := Fin κ)) (I.indexed (ι := Fin κ))
      (Simulator.ofMultiHybrid (S.indexed (ι := Fin κ)) hS.indexed)
      (fun ζ Z => ∑ j : Fin κ, b (RState ((Fin κ → σ × υ) × (Fin κ → τ)) ζ E O)
        ((indexedCtx (S.withSub I) X (fun i : Fin κ => i.val < j.val) hSI hX j).reduceEnv
          idle Z)) := by
  have h₁ := realizes_indexed (κ := κ) hSI hX idle hXi hSIi h
  have h₂ := realizes_indexed_withSub (ι := Fin κ) S I
  exact fun ζ => ((h₁ ζ).triangle (h₂ ζ).symm).mono fun _ => by simp

end CatCrypt.Crypto.UCTransparent
