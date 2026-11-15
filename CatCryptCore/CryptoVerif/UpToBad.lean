/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.CryptoVerif.Exact

/-!
# The up-to-bad transformation of CryptoVerif

CryptoVerif's `insert_event e` replaces a branch of a game by `event_abort e`; the bound of the
step is the probability of `e`. Here `G` and the same game with its body replaced by `call'`
are indistinguishable up to the probability that the run of `G` reaches a bad configuration,
when they agree on the transitions into good configurations from good configurations.

## Main results

* `CvGame.NoFailCall` — the bodies of a game do not fail.
* `CvGame.sysOf` — the system of `G` with its body replaced, on the configurations of `G`.
* `insert_event` — the rule at the level of configurations.
* `insert_event_state` — the rule for a bad predicate of the game state, stated on the calls.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.CryptoVerifLogic

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open scoped ENNReal

variable {I : CvIface}

/-- The bodies of a game do not fail. -/
def CvGame.NoFailCall (G : CvGame I) : Prop :=
  ∀ s o i a, SPComp.NoFail (G.call s o i a)

/-- The system with the configurations and steps of `G.withCall call'`, on the configurations
of `G`. -/
noncomputable def CvGame.sysOf (G : CvGame I)
    (call' : G.State → (o : I.Orc) → I.Idx o → I.Arg o →
      SPComp (G.State × CvRet (I.Res o) × List I.Ev)) :
    Sys (CvConf G) (CvCall I) (CvOut I) where
  init := G.sys.init
  step c a := SPComp.map (fun r => (G.next c a r, G.out r)) (
    if G.blocked c a then SPComp.pure none
    else SPComp.map (fun r => some (r.1, ⟨a.1, r.2.1⟩, r.2.2)) (call' c.st a.1 a.2.1 a.2.2))

/-- Steps of a game whose body does not fail do not fail. -/
theorem CvGame.sysOf_noFail (G : CvGame I)
    (call' : G.State → (o : I.Orc) → I.Idx o → I.Arg o →
      SPComp (G.State × CvRet (I.Res o) × List I.Ev))
    (h : ∀ s o i a, SPComp.NoFail (call' s o i a)) (c : CvConf G) (a : CvCall I) :
    SPComp.NoFail ((G.sysOf call').step c a) := by
  simp only [CvGame.sysOf, SPComp.map]
  refine CatCrypt.Crypto.Assumptions.SPComp.bind_noFail ?_ fun _ => SPComp.pure_noFail _
  split_ifs
  · exact SPComp.pure_noFail _
  · exact CatCrypt.Crypto.Assumptions.SPComp.bind_noFail (h _ _ _ _) fun _ => SPComp.pure_noFail _

/-- The system `G.sysOf call'` realizes the system of `G.withCall call'` with bound 0. -/
theorem CvGame.sysOf_realizes (G : CvGame I)
    (call' : G.State → (o : I.Orc) → I.Idx o → I.Arg o →
      SPComp (G.State × CvRet (I.Res o) × List I.Ev)) :
    Realizes (G.sysOf call') (G.withCall call').sys fun _ _ => 0 :=
  realizes_zero_of_stepMap _ _ (CvConf.mapSt (G' := G.withCall call') _root_.id) rfl fun c a => by
    simp only [CvGame.sysOf, CvGame.sys, CvGame.kernel, CvGame.withCall, CvGame.blocked,
      CvConf.mapSt, _root_.id, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1
    funext r
    cases r <;> rfl

/-- **CryptoVerif's `insert_event`, on configurations.** If the bodies of `G` and `G` with
`call'` do not fail and, from configurations that are not bad, the transitions into
configurations that are not bad of the two systems agree, then `G` and `G.withCall call'` are
indistinguishable with bound the probability `prBad G.sys bad`. -/
theorem insert_event (G : CvGame I)
    (call' : G.State → (o : I.Orc) → I.Idx o → I.Arg o →
      SPComp (G.State × CvRet (I.Res o) × List I.Ev))
    (bad : CvConf G → Bool) (hG : G.NoFailCall) (hcall' : ∀ s o i a, SPComp.NoFail (call' s o i a))
    (hagree : ∀ c a, bad c = false →
      SPComp.bind (G.sys.step c a) (goodK bad) =
        SPComp.bind ((G.sysOf call').step c a) (goodK bad)) :
    Realizes G.sys (G.withCall call').sys fun _ Z => prBad G.sys bad Z := by
  have h₁ : Realizes G.sys (G.sysOf call') fun _ Z => prBad G.sys bad Z := fun ζ Z =>
    adv_le_prBad G.sys (G.sysOf call') bad rfl (G.sysOf_noFail G.call hG)
      (G.sysOf_noFail call' hcall') hagree Z
  exact fun ζ => (h₁.trans (G.sysOf_realizes call') ζ).mono fun Z => by simp

/-- **CryptoVerif's `insert_event`, on game states.** If the bodies do not fail and, from
states that are not bad, the outcomes in states that are not bad of the two bodies agree, then
`G` and `G.withCall call'` are indistinguishable with bound the probability that the run of `G`
reaches a bad state. -/
theorem insert_event_state (G : CvGame I)
    (call' : G.State → (o : I.Orc) → I.Idx o → I.Arg o →
      SPComp (G.State × CvRet (I.Res o) × List I.Ev))
    (bad : G.State → Bool) (hG : G.NoFailCall) (hcall' : ∀ s o i a, SPComp.NoFail (call' s o i a))
    (hagree : ∀ s o i a, bad s = false →
      SPComp.bind (G.call s o i a) (goodK bad) = SPComp.bind (call' s o i a) (goodK bad)) :
    Realizes G.sys (G.withCall call').sys fun _ Z => prBad G.sys (fun c => bad c.st) Z := by
  refine insert_event G call' (fun c => bad c.st) hG hcall' fun c a hc => ?_
  simp only [CvGame.sysOf, CvGame.sys, CvGame.kernel]
  split_ifs with hb
  · rfl
  · have key : ∀ (C : (o : I.Orc) → I.Idx o → I.Arg o →
        SPComp (G.State × CvRet (I.Res o) × List I.Ev)),
        SPComp.bind (SPComp.map (fun r => (G.next c a r, G.out r))
          (SPComp.map (fun r => some (r.1, (⟨a.1, r.2.1⟩ : (o : I.Orc) × CvRet (I.Res o)), r.2.2))
            (C a.1 a.2.1 a.2.2))) (goodK fun c => bad c.st) =
        SPComp.bind (SPComp.bind (C a.1 a.2.1 a.2.2) (goodK bad)) fun r =>
          SPComp.pure (G.next c a (some (r.1, ⟨a.1, r.2.1⟩, r.2.2)),
            G.out (some (r.1, ⟨a.1, r.2.1⟩, r.2.2))) := by
      intro C
      simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      congr 1
      funext r
      by_cases hr : bad r.1 = true
      · simp [goodK, CvGame.next, hr, SPComp.fail_bind]
      · simp [goodK, CvGame.next, hr, SPComp.pure_bind]
    rw [key (G.call c.st), key (call' c.st), hagree c.st a.1 a.2.1 a.2.2 hc]

end CatCrypt.Crypto.CryptoVerifLogic
