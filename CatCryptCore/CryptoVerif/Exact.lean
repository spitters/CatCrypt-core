/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.CryptoVerif.Secret

/-!
# Exact game transformations of CryptoVerif

The transformations of CryptoVerif's `remove_assign`, `SArename`, `expand`, `move`,
`merge_branches`, `merge_arrays` and simplification without collisions change a game without
changing its probabilities: a game `G` is mapped by a function of states to `G'`, step by step
on the reachable states, or `G` and `G'` have the same states and their calls agree on the
states of an invariant. CryptoVerif's `success` proves an event absent, and proves bit secrecy
of a game that does not depend on the bit; both have bound 0.

## Main results

* `CvGame.withCall`, `CvGame.CallKeeps` — a game with its body replaced, and the property of
  a body that its outcomes keep an invariant and execute only allowed events.
* `CvGame.realizes_of_map_on` —`G ≈_0 G'` when a state map sends the calls of `G` to those of `G'`
  on an invariant; `remove_assign` — the same without an invariant.
* `simplify_exact`, `merge_branches`, `merge_arrays` — equal calls on an invariant, a branch
  whose sides agree where its condition holds, and arrays of disjoint definitions read as one.
* `success_event` — an event that no reachable call executes has probability 0.
* `success_secret` — a game equal at both values of the bit proves bit secrecy with bound 0.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.CryptoVerifLogic

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open scoped ENNReal

variable {I : CvIface}

/-- The game `G` with the body of its oracles replaced by `call'`; the states, the initial state
and the availability are those of `G`. -/
def CvGame.withCall (G : CvGame I)
    (call' : G.State → (o : I.Orc) → I.Idx o → I.Arg o →
      SPComp (G.State × CvRet (I.Res o) × List I.Ev)) : CvGame I :=
  { G with call := call' }

/-- From every state satisfying `Inv`, a call is a deterministic post-processing of a
computation, and each of its images has a state satisfying `Inv` and executes only events
satisfying `Ok`. -/
def CvGame.CallKeeps (G : CvGame I) (Inv : G.State → Prop) (Ok : I.Ev → Prop) : Prop :=
  ∀ s o i a, Inv s → ∃ (α : Type) (c : SPComp α) (g : α → G.State × CvRet (I.Res o) × List I.Ev),
    G.call s o i a = SPComp.bind c (fun x => SPComp.pure (g x)) ∧
      ∀ x, Inv (g x).1 ∧ ∀ e ∈ (g x).2.2, Ok e

/-- The configuration of `G` with the game state mapped to a state of `G'`. -/
def CvConf.mapSt {G G' : CvGame I} (f : G.State → G'.State) (c : CvConf G) : CvConf G' :=
  ⟨f c.st, c.used, c.log, c.stopped⟩

/-- A step of the system of `G` at a configuration whose state satisfies `Inv`, for a body
keeping `Inv`, is a post-processing of a computation whose images keep `Inv` on the state and
add only events satisfying `Ok`. -/
theorem CvGame.sys_step_factor {G : CvGame I} {Inv : G.State → Prop} {Ok : I.Ev → Prop}
    (hkeep : G.CallKeeps Inv Ok) (c : CvConf G) (a : CvCall I) (hc : Inv c.st) :
    ∃ (α : Type) (k : SPComp α) (g : α → CvConf G × CvOut I),
      G.sys.step c a = SPComp.bind k (fun x => SPComp.pure (g x)) ∧
        ∀ x, Inv (g x).1.st ∧ ∀ e ∈ (g x).1.log, e ∈ c.log ∨ Ok e := by
  by_cases hb : G.blocked c a = true
  · refine ⟨Unit, SPComp.pure (), fun _ => (c, (none, [])), ?_, fun _ => ⟨hc, fun e he => .inl he⟩⟩
    simp [CvGame.sys, CvGame.kernel_blocked G c a hb, SPComp.map, SPComp.pure_bind, CvGame.next,
      CvGame.out]
  · obtain ⟨α, k, g, hk, hg⟩ := hkeep c.st a.1 a.2.1 a.2.2 hc
    refine ⟨α, k, fun x => (G.next c a (some ((g x).1, ⟨a.1, (g x).2.1⟩, (g x).2.2)),
      G.out (some ((g x).1, ⟨a.1, (g x).2.1⟩, (g x).2.2))), ?_, fun x => ⟨(hg x).1, fun e he => ?_⟩⟩
    · simp only [CvGame.sys, CvGame.kernel, hb, Bool.false_eq_true, ↓reduceIte, hk, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind]
    · simp only [CvGame.next, List.mem_append] at he
      exact he.imp id ((hg x).2 e)

/-- **State map on an invariant.** If a map of states sends the initial state to the initial
state, preserves availability, and commutes with the calls on the states of an invariant, then
`G` and `G'` are indistinguishable with bound 0. -/
theorem CvGame.realizes_of_map_on {G G' : CvGame I} (Inv : G.State → Prop)
    (f : G.State → G'.State)
    (h0 : Inv G.init) (hinit : f G.init = G'.init)
    (havail : ∀ s o i, Inv s → G'.avail (f s) o i = G.avail s o i)
    (hkeep : G.CallKeeps Inv fun _ => True)
    (hstep : ∀ s o i a, Inv s →
      SPComp.map (fun r => (f r.1, r.2)) (G.call s o i a) = G'.call (f s) o i a) :
    Realizes G.sys G'.sys fun _ _ => 0 := by
  refine realizes_zero_of_stepMap_on G.sys G'.sys (fun c => Inv c.st) (CvConf.mapSt f) h0 ?_ ?_ ?_
  · simp [CvGame.sys, CvConf.mapSt, hinit]
  · intro c a hc
    obtain ⟨α, k, g, hk, hg⟩ := CvGame.sys_step_factor hkeep c a hc
    exact ⟨α, k, g, hk, fun x => (hg x).1⟩
  · intro c a hc
    have hbl : G'.blocked (CvConf.mapSt f c) a = G.blocked c a := by
      simp [CvGame.blocked, CvConf.mapSt, havail c.st a.1 a.2.1 hc]
    simp only [CvGame.sys]
    by_cases hb : G.blocked c a = true
    · rw [CvGame.kernel_blocked G c a hb, CvGame.kernel_blocked G' _ a (hbl.trans hb)]
      simp [SPComp.map, SPComp.pure_bind, CvGame.next, CvGame.out, CvConf.mapSt]
    · have hb' : G'.blocked (CvConf.mapSt f c) a = false := by
        rw [hbl]; simpa using hb
      simp only [CvGame.kernel, hb, Bool.false_eq_true, ↓reduceIte, hb']
      rw [show (CvConf.mapSt f c).st = f c.st from rfl, ← hstep c.st a.1 a.2.1 a.2.2 hc]
      simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      rfl

/-- CryptoVerif's `remove_assign`, `SArename`, `expand` and `move`: a map of states commuting
with the calls gives bound 0. -/
theorem remove_assign {G G' : CvGame I} (f : G.State → G'.State) (hinit : f G.init = G'.init)
    (havail : ∀ s o i, G'.avail (f s) o i = G.avail s o i)
    (hstep : ∀ s o i a,
      SPComp.map (fun r => (f r.1, r.2)) (G.call s o i a) = G'.call (f s) o i a) :
    Realizes G.sys G'.sys fun _ _ => 0 :=
  CvGame.realizes_of_map_on (fun _ => True) f trivial hinit (fun s o i _ => havail s o i)
    (fun s o i a _ => ⟨_, G.call s o i a, id, by simp [SPComp.bind_pure],
      fun _ => ⟨trivial, by simp⟩⟩)
    fun s o i a _ => hstep s o i a

/-- CryptoVerif's simplification without collisions: the calls of `G` and of `G` with the body
`call'` agree on the states of an invariant kept by `G`. -/
theorem simplify_exact (G : CvGame I)
    (call' : G.State → (o : I.Orc) → I.Idx o → I.Arg o →
      SPComp (G.State × CvRet (I.Res o) × List I.Ev))
    (Inv : G.State → Prop) (h0 : Inv G.init) (hkeep : G.CallKeeps Inv fun _ => True)
    (hstep : ∀ s o i a, Inv s → G.call s o i a = call' s o i a) :
    Realizes G.sys (G.withCall call').sys fun _ _ => 0 :=
  CvGame.realizes_of_map_on (G' := G.withCall call') Inv _root_.id h0 rfl (fun _ _ _ _ => rfl) hkeep
    fun s o i a hs => by
      simp only [CvGame.withCall, ← hstep s o i a hs, SPComp.map, Prod.mk.eta, id_eq,
        SPComp.bind_pure]

/-- CryptoVerif's `merge_branches`: a body that branches on `c` between `P` and `P'`, whose two
branches agree on the states of an invariant where `c` holds, is the body `P'`. -/
theorem merge_branches (G : CvGame I)
    (c : G.State → (o : I.Orc) → I.Idx o → I.Arg o → Bool)
    (P P' : G.State → (o : I.Orc) → I.Idx o → I.Arg o →
      SPComp (G.State × CvRet (I.Res o) × List I.Ev))
    (hG : ∀ s o i a, G.call s o i a = if c s o i a then P s o i a else P' s o i a)
    (Inv : G.State → Prop) (h0 : Inv G.init) (hkeep : G.CallKeeps Inv fun _ => True)
    (hsame : ∀ s o i a, Inv s → c s o i a = true → P s o i a = P' s o i a) :
    Realizes G.sys (G.withCall P').sys fun _ _ => 0 :=
  simplify_exact G P' Inv h0 hkeep fun s o i a hs => by
    rw [hG]
    split_ifs with hc
    · exact hsame s o i a hs hc
    · rfl

section MergeArrays

variable {n : ℕ} {J V : Type}

/-- The merge of `n` arrays over `J`: at an index, the entry of the first array that is defined
there. -/
def mergedArr (arr : Fin n → J → Option V) (j : J) : Option V :=
  (List.finRange n).findSome? (arr · j)

/-- When no array is defined at `j`, defining array `k` at `j` defines the merged array at `j`,
and leaves it at every other index. -/
theorem mergedArr_update [DecidableEq J] (arr : Fin n → J → Option V) (k : Fin n) (j : J) (v : V)
    (hnone : ∀ l, arr l j = none) :
    mergedArr (Function.update arr k (Function.update (arr k) j (some v))) =
      Function.update (mergedArr arr) j (some v) := by
  funext j'
  by_cases hj : j' = j
  · subst hj
    have hdef : ∀ l, Function.update arr k (Function.update (arr k) j' (some v)) l j' =
        if l = k then some v else none := by
      intro l
      by_cases hl : l = k
      · subst hl; simp
      · simp [hl, hnone]
    simp only [mergedArr, hdef, Function.update_self]
    rw [List.findSome?_eq_some_iff]
    obtain ⟨l₁, l₂, h, hl⟩ : ∃ l₁ l₂, List.finRange n = l₁ ++ k :: l₂ ∧ k ∉ l₁ := by
      have := List.append_of_mem (List.mem_finRange k)
      obtain ⟨l₁, l₂, h⟩ := this
      refine ⟨l₁, l₂, h, fun hk => ?_⟩
      have hnd := List.nodup_finRange n
      rw [h] at hnd
      exact (List.nodup_append.1 hnd).2.2 k hk k (List.mem_cons_self) rfl
    refine ⟨l₁, k, l₂, h, by simp, fun l hl' => ?_⟩
    simp [show l ≠ k from fun hlk => hl (hlk ▸ hl')]
  · have hdef : ∀ l, Function.update arr k (Function.update (arr k) j (some v)) l j' =
        arr l j' := by
      intro l
      by_cases hl : l = k
      · subst hl; simp [hj]
      · simp [hl]
    simp [mergedArr, hdef, Function.update_of_ne hj]

/-- The map of states of `merge_arrays`: the arrays read through `mergedArr`, the rest kept. -/
def mergeSt {ρ : Type} (s : (Fin n → J → Option V) × ρ) : (J → Option V) × ρ :=
  (mergedArr s.1, s.2)

/-- CryptoVerif's `merge_arrays`: a game with the arrays `x₁, …, xₙ` beside its other state is
read as a game with one array through `mergeSt`. The map is exact on an invariant, which
expresses that the definitions of the arrays are disjoint (`mergedArr_update` is the fact the
step equation uses). -/
theorem merge_arrays {ρ : Type} (init : (Fin n → J → Option V) × ρ)
    (avail : ((Fin n → J → Option V) × ρ) → (o : I.Orc) → I.Idx o → Bool)
    (call : ((Fin n → J → Option V) × ρ) → (o : I.Orc) → I.Idx o → I.Arg o →
      SPComp (((Fin n → J → Option V) × ρ) × CvRet (I.Res o) × List I.Ev))
    (avail' : ((J → Option V) × ρ) → (o : I.Orc) → I.Idx o → Bool)
    (call' : ((J → Option V) × ρ) → (o : I.Orc) → I.Idx o → I.Arg o →
      SPComp (((J → Option V) × ρ) × CvRet (I.Res o) × List I.Ev))
    (Inv : ((Fin n → J → Option V) × ρ) → Prop) (h0 : Inv init)
    (havail : ∀ s o i, Inv s → avail' (mergeSt s) o i = avail s o i)
    (hkeep : CvGame.CallKeeps ⟨_, init, avail, call⟩ Inv fun _ => True)
    (hstep : ∀ s o i a, Inv s →
      SPComp.map (fun r => (mergeSt r.1, r.2)) (call s o i a) = call' (mergeSt s) o i a) :
    Realizes (CvGame.sys (I := I) ⟨_, init, avail, call⟩)
      (CvGame.sys (I := I) ⟨_, mergeSt init, avail', call'⟩) fun _ _ => 0 :=
  CvGame.realizes_of_map_on (G :=⟨_, init, avail, call⟩) (G' := ⟨_, mergeSt init, avail', call'⟩) Inv
    mergeSt h0 rfl havail hkeep hstep

end MergeArrays

section Success

variable {τ ζ E O : Type}

/-- For a system whose steps from `Inv` are post-processings with images in `Inv` that are not
bad, a run from a good flag does not set the flag. -/
theorem prTrue_loop_flag_zero (S : Sys τ E O) (bad : τ → Bool) (Inv : τ → Prop) (Z : Strat ζ E O)
    (hkeep : ∀ t e, Inv t → ∃ (α : Type) (k : SPComp α) (g : α → τ × O),
      S.step t e = SPComp.bind k (fun x => SPComp.pure (g x)) ∧
        ∀ x, Inv (g x).1 ∧ bad (g x).1 = false) :
    ∀ (n : ℕ) (z : ζ) (t : τ) (h : Heap), Inv t →
      prTrue (SPComp.bind (loop S bad Z n (z, t, false)) fun c => SPComp.pure c.2.2) h = 0 := by
  intro n
  induction n with
  | zero =>
    intro z t h _
    simp [loop, SPComp.pure_bind, prTrue_pure]
  | succ n ih =>
    intro z t h ht
    simp only [loop, SPComp.bind_assoc]
    rw [prTrue_bind_eq_weighted, ENNReal.tsum_eq_zero]
    rintro (_ | ⟨⟨z₁, e⟩, h₁⟩)
    · simp
    · obtain ⟨α, k, g, hk, hg⟩ := hkeep t e ht
      simp only [hk, SPComp.bind_assoc, SPComp.pure_bind]
      refine mul_eq_zero_of_right _ ?_
      rw [prTrue_bind_eq_weighted, ENNReal.tsum_eq_zero]
      rintro (_ | ⟨x, h₂⟩)
      · simp
      · refine mul_eq_zero_of_right _ ?_
        dsimp only
        rw [prTrue_bind_eq_weighted, ENNReal.tsum_eq_zero]
        rintro (_ | ⟨z₂, h₃⟩)
        · simp
        · refine mul_eq_zero_of_right _ ?_
          simpa [(hg x).2] using ih z₂ (g x).1 h₃ (hg x).1

end Success

/-- CryptoVerif's `success` for an event: when the body keeps an invariant and no outcome from
it executes `e`, the event has probability 0. -/
theorem success_event (G : CvGame I) (e : I.Ev) (Inv : G.State → Prop) (h0 : Inv G.init)
    (hkeep : G.CallKeeps Inv fun e' => e' ≠ e) :
    CvEventBound G e fun _ _ => 0 := by
  intro ζ Z
  refine le_of_eq ?_
  unfold prBad run
  have hb : G.evBad e G.sys.init = false := by simp [CvGame.evBad, CvGame.sys]
  rw [hb]
  refine prTrue_loop_flag_zero G.sys (G.evBad e) (fun c => Inv c.st ∧ e ∉ c.log) Z.input ?_ _ _ _ _
    ⟨h0, by simp [CvGame.sys]⟩
  rintro c a ⟨hc, hl⟩
  obtain ⟨α, k, g, hk, hg⟩ := CvGame.sys_step_factor hkeep c a hc
  have hnot : ∀ x, e ∉ (g x).1.log := fun x he =>
    ((hg x).2 e he).elim hl fun h => h rfl
  exact ⟨α, k, g, hk, fun x => ⟨⟨(hg x).1, hnot x⟩, by simp [CvGame.evBad, hnot x]⟩⟩

/-- CryptoVerif's `success` for bit secrecy: a game that is the same at both values of the bit
proves bit secrecy with bound 0. -/
theorem success_secret (G : Bool → CvGame I) (h : G false = G true) :
    CvSecretBit G fun _ _ => 0 := by
  unfold CvSecretBit
  rw [h]
  exact (realizes_zero_of_step_eq (G true).sys (G true).sys rfl fun _ _ => rfl).1

end CatCrypt.Crypto.CryptoVerifLogic
