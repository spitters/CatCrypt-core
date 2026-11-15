/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.CryptoVerif.Exact
public import CatCryptCore.Crypto.OracleGameUpToBad
public import CatCryptCore.Crypto.SPCompPMF
public import CatCryptCore.NonUniform.Sample

/-!
# Games given by probability mass functions and contexts over an oracle

Games whose bodies are probability mass functions, a state map on an invariant over
configurations between such games, `success` on such an invariant, contexts over an oracle with
their game and protocol, and a keyed game with its key drawn at the first query.

## Main results

* `pGame`, `CvGame.realizes_of_map_conf`, `success_event_conf` — games given by probability mass
  functions, a state map on an invariant over configurations, and `success` on such an invariant.
* `CvCtx`, `CvCtx.over`, `CvCtx.prot`, `CvCtx.realizes_over` — a context over an oracle, its game
  and protocol, and their equality of views.
* `lazyOrc`, `lazyGame`, `accept_lazyGame` — a keyed game with its key drawn at the first query.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.CryptoVerifLogic

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open scoped ENNReal

variable {I : CvIface}

/-! ## Games given by probability mass functions -/

/-- The restriction of a probability mass function to its support. -/
noncomputable def pmfAttach {α : Type} (p : PMF α) : PMF {a // a ∈ p.support} :=
  ⟨fun a => p a.1, by
    have h : (∑' a : {a // a ∈ p.support}, p a.1) = 1 := by
      rw [tsum_subtype_eq_of_support_subset (f := p) (s := p.support) (fun a ha => ha)]
      exact p.tsum_coe
    exact h ▸ ENNReal.summable.hasSum⟩

/-- The restriction of a distribution to its support maps back to the distribution. -/
theorem pmfAttach_map {α : Type} (p : PMF α) : (pmfAttach p).map Subtype.val = p := by
  ext a
  simp only [PMF.map_apply]
  by_cases ha : a ∈ p.support
  · rw [tsum_eq_single (⟨a, ha⟩ : {a // a ∈ p.support})]
    · simp only [↓reduceIte]
      rfl
    · rintro ⟨b, hb⟩ hne
      have : a ≠ b := fun h => hne (Subtype.ext h.symm)
      simp [this]
  · have h0 : p a = 0 := by simpa [PMF.mem_support_iff] using ha
    rw [h0]
    refine ENNReal.tsum_eq_zero.2 ?_
    rintro ⟨b, hb⟩
    have : a ≠ b := fun h => ha (h ▸ hb)
    simp [this]

/-- A game whose bodies are probability mass functions. -/
noncomputable abbrev pGame (σ : Type) (init : σ) (avail : σ → (o : I.Orc) → I.Idx o → Bool)
    (p : σ → (o : I.Orc) → I.Idx o → I.Arg o → PMF (σ × CvRet (I.Res o) × List I.Ev)) :
    CvGame I :=
  ⟨σ, init, avail, fun s o i a => liftPMF (p s o i a)⟩

section PGame

variable {σ σ' : Type} {init : σ} {init' : σ'}
  {avail : σ → (o : I.Orc) → I.Idx o → Bool} {avail' : σ' → (o : I.Orc) → I.Idx o → Bool}
  {p : σ → (o : I.Orc) → I.Idx o → I.Arg o → PMF (σ × CvRet (I.Res o) × List I.Ev)}
  {p' : σ' → (o : I.Orc) → I.Idx o → I.Arg o → PMF (σ' × CvRet (I.Res o) × List I.Ev)}

/-- The successor configuration and output of an answered call of a game, from the outcome of
its body. -/
def CvGame.ans (G : CvGame I) (c : CvConf G) (a : CvCall I)
    (r : G.State × CvRet (I.Res a.1) × List I.Ev) : CvConf G × CvOut I :=
  (G.next c a (some (r.1, ⟨a.1, r.2.1⟩, r.2.2)), G.out (some (r.1, ⟨a.1, r.2.1⟩, r.2.2)))

/-- A step of a game given by probability mass functions, at an unblocked call. -/
theorem pGame_step_unblocked (c : CvConf (pGame σ init avail p)) (a : CvCall I)
    (hb : (pGame σ init avail p).blocked c a = false) :
    (pGame σ init avail p).sys.step c a =
      liftPMF ((p c.st a.1 a.2.1 a.2.2).map ((pGame σ init avail p).ans c a)) := by
  simp only [CvGame.sys, CvGame.kernel, hb, Bool.false_eq_true, ↓reduceIte, SPComp.map,
    SPComp.bind_assoc, SPComp.pure_bind]
  exact liftPMF_bind_pure _ _

/-- A step of a game given by probability mass functions, at an unblocked call, as a
post-processing of the draw restricted to the support of its body. -/
theorem pGame_step_attach (c : CvConf (pGame σ init avail p)) (a : CvCall I)
    (hb : (pGame σ init avail p).blocked c a = false) :
    (pGame σ init avail p).sys.step c a =
      SPComp.bind (liftPMF (pmfAttach (p c.st a.1 a.2.1 a.2.2)))
        fun x => SPComp.pure ((pGame σ init avail p).ans c a x.1) := by
  have hq : (p c.st a.1 a.2.1 a.2.2).map ((pGame σ init avail p).ans c a) =
      (pmfAttach (p c.st a.1 a.2.1 a.2.2)).map fun x => (pGame σ init avail p).ans c a x.1 := by
    conv_lhs => rw [← pmfAttach_map (p c.st a.1 a.2.1 a.2.2)]
    rw [PMF.map_comp]
    rfl
  exact (pGame_step_unblocked c a hb).trans ((congrArg liftPMF hq).trans
    (liftPMF_bind_pure _ _).symm)

/-- A step of a game at a blocked call. -/
theorem sys_step_blocked (G : CvGame I) (c : CvConf G) (a : CvCall I)
    (hb : G.blocked c a = true) : G.sys.step c a = SPComp.pure (c, (none, [])) := by
  simp [CvGame.sys, CvGame.kernel_blocked G c a hb, SPComp.map, SPComp.pure_bind, CvGame.next,
    CvGame.out]

/-- **State map on an invariant over configurations.** Between games given by probability mass
functions, a map of states commuting with the unblocked calls at the configurations of an
invariant, kept on the support of the bodies, gives bound 0. -/
theorem CvGame.realizes_of_map_conf (Inv : CvConf (pGame σ init avail p) → Prop) (f : σ → σ')
    (h0 : Inv (pGame σ init avail p).sys.init) (hinit : f init = init')
    (havail : ∀ c o i, Inv c → avail' (f c.st) o i = avail c.st o i)
    (hkeep : ∀ c a, Inv c → (pGame σ init avail p).blocked c a = false →
      ∀ r ∈ (p c.st a.1 a.2.1 a.2.2).support, Inv ((pGame σ init avail p).ans c a r).1)
    (hstep : ∀ c a, Inv c → (pGame σ init avail p).blocked c a = false →
      (p c.st a.1 a.2.1 a.2.2).map (fun r => (f r.1, r.2)) = p' (f c.st) a.1 a.2.1 a.2.2) :
    Realizes (pGame σ init avail p).sys (pGame σ' init' avail' p').sys fun _ _ => 0 := by
  refine realizes_zero_of_stepMap_on _ _ Inv (CvConf.mapSt f) h0 (by simp [CvGame.sys, CvConf.mapSt,
    pGame, hinit]) ?_ ?_
  · intro c a hc
    by_cases hb : (pGame σ init avail p).blocked c a = true
    · exact ⟨Unit, SPComp.pure (), fun _ => (c, (none, [])), by
        rw [sys_step_blocked _ c a hb]; simp [SPComp.pure_bind], fun _ => hc⟩
    · have hb' : (pGame σ init avail p).blocked c a = false := by simpa using hb
      exact ⟨_, liftPMF (pmfAttach (p c.st a.1 a.2.1 a.2.2)),
        fun x => (pGame σ init avail p).ans c a x.1, pGame_step_attach c a hb',
        fun x => hkeep c a hc hb' _ x.2⟩
  · intro c a hc
    have hbl : (pGame σ' init' avail' p').blocked (CvConf.mapSt f c) a =
        (pGame σ init avail p).blocked c a := by
      have := havail c a.1 a.2.1 hc
      simp [CvGame.blocked, CvConf.mapSt, this]
    by_cases hb : (pGame σ init avail p).blocked c a = true
    · rw [sys_step_blocked _ c a hb, sys_step_blocked _ _ a (hbl.trans hb)]
      simp [SPComp.map, SPComp.pure_bind, CvConf.mapSt]
    · have hb' : (pGame σ init avail p).blocked c a = false := by simpa using hb
      refine Eq.trans ?_ (pGame_step_unblocked (p := p') (CvConf.mapSt f c) a (hbl.trans hb')).symm
      rw [pGame_step_unblocked c a hb']
      simp only [SPComp.map]
      refine (liftPMF_bind_pure _ _).trans (congrArg liftPMF ?_)
      refine Eq.trans ?_ (congrArg (PMF.map _) (hstep c a hc hb'))
      rw [PMF.map_comp, PMF.map_comp]
      rfl

/-- **`success` on an invariant over configurations.** For a game given by probability mass
functions, if an invariant on configurations is kept on the support of the unblocked bodies and
those bodies do not execute `e`, the event `e` has probability 0. -/
theorem success_event_conf (e : I.Ev) (Inv : CvConf (pGame σ init avail p) → Prop)
    (h0 : Inv (pGame σ init avail p).sys.init)
    (hkeep : ∀ c a, Inv c → (pGame σ init avail p).blocked c a = false →
      ∀ r ∈ (p c.st a.1 a.2.1 a.2.2).support,
        Inv ((pGame σ init avail p).ans c a r).1 ∧ e ∉ r.2.2) :
    CvEventBound (pGame σ init avail p) e fun _ _ => 0 := by
  intro ζ Z
  refine le_of_eq ?_
  unfold prBad run
  have hb : (pGame σ init avail p).evBad e (pGame σ init avail p).sys.init = false := by
    simp [CvGame.evBad, CvGame.sys]
  rw [hb]
  refine prTrue_loop_flag_zero (pGame σ init avail p).sys ((pGame σ init avail p).evBad e)
    (fun c => Inv c ∧ e ∉ c.log) Z.input ?_ _ _ _ _ ⟨h0, by simp [CvGame.sys]⟩
  rintro c a ⟨hc, hl⟩
  by_cases hbl : (pGame σ init avail p).blocked c a = true
  · exact ⟨Unit, SPComp.pure (), fun _ => (c, (none, [])), by
      rw [sys_step_blocked _ c a hbl]; simp [SPComp.pure_bind],
      fun _ => ⟨⟨hc, hl⟩, by simp [CvGame.evBad, hl]⟩⟩
  · have hb' : (pGame σ init avail p).blocked c a = false := by simpa using hbl
    refine ⟨_, liftPMF (pmfAttach (p c.st a.1 a.2.1 a.2.2)),
      fun x => (pGame σ init avail p).ans c a x.1, pGame_step_attach c a hb', fun x => ?_⟩
    have hk := hkeep c a hc hb' x.1 x.2
    have hlog : e ∉ ((pGame σ init avail p).ans c a x.1).1.log := by
      simp [CvGame.ans, CvGame.next, hl, hk.2]
    exact ⟨⟨hk.1, hlog⟩, by simp [CvGame.evBad, hlog]⟩

end PGame

/-! ## Contexts over an oracle -/

/-- `sampleFrom` of a total distribution is its lift. -/
theorem sampleFrom_ofPMF_eq_liftPMF {α : Type} (p : PMF α) : sampleFrom (ofPMF p) = liftPMF p := by
  funext h
  simpa [sampleFrom_apply, ofPMF, liftPMF, Function.comp_def, SDistr.pure] using
    (sdistr_bind_map_some p id fun a => SDistr.pure (a, h)).trans (PMF.bind_pure_comp _ _)

/-- An oracle as a keyed game with a trivial key. -/
noncomputable abbrev keylessGame {Q A S : Type} (orc : S → Q → PMF (A × S)) (s₀ : S) :
    KeyedGame Q A :=
  ⟨Unit, S, PMF.pure (), fun _ => orc, s₀⟩

/-- A CryptoVerif context over an oracle with queries `Q` and answers `A`: a game whose bodies
are oracle programs. -/
structure CvCtx (I : CvIface) (Q A : Type) where
  /-- The state of the context. -/
  State : Type
  /-- The initial state. -/
  init : State
  /-- The instances available at a state. -/
  avail : State → (o : I.Orc) → I.Idx o → Bool
  /-- The body of an instance as an oracle program. -/
  body : State → (o : I.Orc) → I.Idx o → I.Arg o →
    OracleAdv Q A (State × CvRet (I.Res o) × List I.Ev)

namespace CvCtx

variable {Q A S : Type} (C : CvCtx I Q A)

/-- The game with the states and availability of the context and failing bodies; its
configurations are the states of the protocol of the context. -/
noncomputable abbrev skel : CvGame I :=
  ⟨C.State, C.init, C.avail, fun _ _ _ _ => SPComp.fail⟩

/-- The protocol of a context: it refuses as the system of a game does, and runs the body of an
unblocked call as an oracle program. -/
noncomputable def prot : OProt (CvConf C.skel) (CvCall I) (CvOut I) Q A where
  init := C.skel.sys.init
  step c a :=
    if C.skel.blocked c a then .ret (c, (none, []))
    else (C.body c.st a.1 a.2.1 a.2.2).bind fun r => .ret (C.skel.ans c a r)

/-- The context over a stateful oracle, as a game. -/
noncomputable abbrev over (orc : S → Q → PMF (A × S)) (s₀ : S) : CvGame I :=
  pGame (C.State × S) (C.init, s₀) (fun s => C.avail s.1)
    fun s o i a => (OracleAdv.run orc (C.body s.1 o i a) s.2).map fun x => ((x.1.1, x.2), x.1.2)

/-- The system of the protocol of a context over a keyless game has the views of the context
over its oracle. -/
theorem realizes_over (orc : S → Q → PMF (A × S)) (s₀ : S) :
    Realizes (C.prot.sys (keylessGame orc s₀)) (C.over orc s₀).sys fun _ _ => 0 := by
  have hg : ∀ (c : CvConf C.skel) (s : S) (a : CvCall I),
      SPComp.map (fun p => ((⟨(p.1.1.st, p.1.2), p.1.1.used, p.1.1.log, p.1.1.stopped⟩ :
        CvConf (C.over orc s₀)), p.2)) (C.prot.plugStep orc (c, s) a) =
      (C.over orc s₀).sys.step ⟨(c.st, s), c.used, c.log, c.stopped⟩ a := by
    intro c s a
    by_cases hb : C.skel.blocked c a = true
    · have hb' : (C.over orc s₀).blocked ⟨(c.st, s), c.used, c.log, c.stopped⟩ a = true := hb
      rw [sys_step_blocked _ _ a hb']
      simp [OProt.plugStep, prot, hb, sampleFrom_ofPMF_eq_liftPMF, SPComp.map, ← liftPMF_pure,
        SPComp.pure_bind]
    · have hb' : (C.over orc s₀).blocked ⟨(c.st, s), c.used, c.log, c.stopped⟩ a = false :=
        Bool.eq_false_of_ne_true hb
      rw [pGame_step_unblocked _ a hb']
      simp only [OProt.plugStep, prot, hb, Bool.false_eq_true, ↓reduceIte,
        sampleFrom_ofPMF_eq_liftPMF, liftPMF_bind_pure, SPComp.map, OracleAdv.run_bind,
        OracleAdv.run_ret, PMF.map_bind, PMF.pure_map]
      congr 1
      rw [PMF.map_comp]
      rfl
  refine realizes_zero_of_stepMap _ _
    (fun t => (⟨(t.2.1.st, t.2.2), t.2.1.used, t.2.1.log, t.2.1.stopped⟩ :
      CvConf (C.over orc s₀))) rfl ?_
  rintro ⟨_ | k, c, s⟩ a
  · have h := hg c s a
    simp only [SPComp.map] at h
    simp only [OProt.sys, OProt.keyed, KeyedSys.lazy, KeyedSys.lazyStep, ↓reduceIte, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind, sampleFrom_ofPMF_eq_liftPMF, ← liftPMF_pure]
    exact h
  · have h := hg c s a
    simp only [SPComp.map] at h
    simp only [OProt.sys, OProt.keyed, KeyedSys.lazy, KeyedSys.lazyStep, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
    exact h

end CvCtx

/-! ## A key drawn at the first query -/

section LazyKey

variable {Q A : Type} (G : KeyedGame Q A)

/-- The oracle of the keyed game `G` whose key is drawn at the first query. -/
noncomputable def lazyOrc (s : Option G.Key × G.State) (q : Q) :
    PMF (A × (Option G.Key × G.State)) :=
  match s.1 with
  | some k => (G.oracle k s.2 q).map fun r => (r.1, (some k, r.2))
  | none => G.keyDist.bind fun k => (G.oracle k s.2 q).map fun r => (r.1, (some k, r.2))

/-- The keyed game `G` with its key drawn at the first query, as a keyless game. -/
noncomputable abbrev lazyGame : KeyedGame Q A := keylessGame (lazyOrc G) (none, G.init)

/-- Drawing the key at the first query does not change the acceptance probability. -/
theorem accept_lazyGame (B : OracleAdv Q A Bool) : (lazyGame G).accept B = G.accept B := by
  have key : ∀ (k : G.Key) (s : Option G.Key × G.State) (B : OracleAdv Q A Bool),
      (OracleAdv.run (fun s d => lazyOrc G (some k, s.2) d) B s).map Prod.fst =
        (OracleAdv.run (G.oracle k) B s.2).map Prod.fst := by
    intro k s B
    induction B generalizing s with
    | ret _ => simp [PMF.pure_map]
    | rand p K ih => simp only [OracleAdv.run_rand, PMF.map_bind, ih]
    | query d K ih =>
      simp only [OracleAdv.run_query, lazyOrc, PMF.bind_map, PMF.map_bind, Function.comp_def]
      exact congrArg _ (funext fun r => ih r.1 _)
  have h := OracleAdv.run_map_fst_lazyKey G.keyDist (lazyOrc G) (fun k s => (some k, s.2))
    (none, G.init) (fun _ => rfl)
    (fun k s d x hx => by
      obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
      rfl) B
  simp only [KeyedGame.accept, PMF.pure_bind, h]
  exact congrFun (congrArg DFunLike.coe (congrArg G.keyDist.bind (funext fun k => key k _ B))) true

end LazyKey

end CatCrypt.Crypto.CryptoVerifLogic
