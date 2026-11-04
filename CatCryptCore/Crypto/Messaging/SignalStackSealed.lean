/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStack
public import CatCryptCore.Crypto.UCFeedbackLaws
public import CatCryptCore.Crypto.TraceEqLaws
public import CatCryptCore.Unary.Lossless

/-!
# Key secrecy of `F_AKE` behind the X3DH simulator

The Signal stack theorem `signal_stack_advantage_le` bounds the distance of the real and the
ideal Signal stacks by three terms; the second, `keyRORAdv (x3dhIdeal G) Z sel D`, compares the
key `sel z` with a fresh uniform key in the world of `F_AKE` behind the X3DH simulator. This
module shows that the term is `0` for an environment that does not read the key of the selected
session before the end of its run, and states the stack theorem without it.

**The statement for a selection from the state of the environment.** In `keyRORAdv`, the key
`sel z` is a function of the final state `z` of the environment, and the distinguisher sees `z`.
The term is therefore not `0` for any environment and selection when the key space has two
elements or more: the distinguisher `D (z, k) = (k = sel z)` accepts the real game with
probability `1` and the random game with probability `1 / |K|`. An environment that does not
read the key cannot hold it in its state, and an environment that holds it in its state shows it
to the distinguisher. The true statement separates the two roles of the state: the environment
`Z` runs sealed (it never asks for a key of the protocol session of the selected session `x₀`),
then the environment `readKey Z x₀` reads the key of `x₀` once, at the end, into a component of
its state that the distinguisher of the stack does not see. The selection is that component.

**The predicate.** `Sealed sid₀ Z`: every event that `Z.next` can choose, from every state, is
an event of `SealedEv sid₀`, that is, not `getKey sid₀ pid` for any `pid`. It is a condition on
the possible outcomes of the choice of the strategy at each activation, as
`X3DHSquareGDH.NamesIn` is on the queries of every path of an oracle adversary; `SealedEv` is
decidable, and `sealed_of_next_eq` checks it for a strategy whose events are fixed functions of
its state. The selected session must also receive a key chosen by `F_AKE`, not one of the
adversary: `CompletesAt G x₀ Z` states that on every possible outcome of the run of `Z` against
`F_AKE` behind the simulator, the record of `x₀` has status `completed` (`selKey`). This part
depends on the scheduling of the adversary port by `Z` and is a condition on the run.

**The coupling.** A permutation `π` of the keys acts on the states of `F_AKE` by `keyPerm sid₀ π`,
applying `π` to the keys of the completed sessions of `sid₀`. At every event other than
`getKey sid₀ _` this action commutes with the step of `F_AKE` (`F_AKE_step_keyPerm`): a fresh
key of `sid₀` is a uniform sample, which `π` maps to a uniform sample; a partner copies the
permuted key; an exposed session keeps the key of the adversary, which the action does not
touch; the outputs of the adversary port carry no key. The simulator calls `F_AKE` on its honest
port only with the honest event of the environment (`simStart_decOk`), so the action commutes
with the steps of the world `x3dhIdeal G` at the events of a sealed environment
(`simWorld_step_keyPerm`), and the law of the final states of the run is invariant
(`runW_map_of_equivariant`). Averaging over a uniform permutation, which maps every key to a
uniform key (`map_apply_sample_perm`), gives `x3dhIdeal_key_secrecy`.

## Main definitions

* `keyPerm`: the action of a permutation of the keys on the states of `F_AKE`.
* `SealedF`, `SealedEv`, `Sealed`: the events that do not read a key of a protocol session, and
  the sealing predicate of a strategy.
* `selKey`, `CompletesAt`: the key of a completed session, and the completion of the selected
  session on every run.
* `runW`, `keySelGame`, `keyRandGame`: the run with the final states of both parties, and the
  games of the selected and of a random key.
* `thenAsk`, `readKey`: a strategy followed by one event, and the environment that reads the key
  of `x₀` at the end.

## Main results

* `bind_sel_eq_of_perm_invariant`: real-or-random from invariance under permutations.
* `runW_map_of_equivariant`, `withSub_step_map_of_equivariant`: invariance of a run, and
  equivariance through a multi-call hybrid.
* `F_AKE_step_keyPerm`, `simWorld_step_keyPerm`: equivariance of `F_AKE` and of the simulated
  world at the sealed events.
* `x3dhIdeal_key_secrecy`, `x3dhIdeal_key_secrecy_advantage`: **key secrecy of `F_AKE` behind
  the X3DH simulator**.
* `keyRORAdv_readKey_eq_zero`: the real-or-random term of the stack is `0` for `readKey Z x₀`.
* `signal_stack_advantage_le_sealed`, `signal_stack_advantage_le_sealed_primitives`,
  `signal_stack_advantage_le_sealed_dh`: **the Signal stack theorem for a sealed environment**,
  with the gap Diffie–Hellman term and the secure-messaging term only.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging.SignalStack

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.Assumptions CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareGDH
open scoped ENNReal

/-! ## Uniform permutations -/

section Perm

variable {K : Type} [Fintype K] [Nonempty K] [DecidableEq K]

/-- A uniform sample bound to a continuation that does not read it is the continuation. -/
theorem sample_bind_const {α β : Type} [Fintype α] [Nonempty α] (c : SPComp β) :
    SPComp.bind (SPComp.sample α) (fun _ => c) = c :=
  SPComp.isPure_bind_discard _ c (SPComp.sample_isPure α) Unary.lossless_sample

/-- **The image of a point under a uniform permutation is uniform.** -/
theorem map_apply_sample_perm (a : K) :
    SPComp.map (fun π : Equiv.Perm K => π a) (SPComp.sample (Equiv.Perm K)) = SPComp.sample K := by
  have hD : ∀ b c : K, SPComp.map (fun π : Equiv.Perm K => π b) (SPComp.sample (Equiv.Perm K)) =
      SPComp.map (fun π : Equiv.Perm K => π c) (SPComp.sample (Equiv.Perm K)) := by
    intro b c
    unfold SPComp.map
    rw [← SPComp.sample_bind_equiv (Equiv.mulRight (Equiv.swap c b))
      (fun π : Equiv.Perm K => SPComp.pure (π b))]
    congr 1
    funext π
    simp [Equiv.swap_apply_right]
  have h₁ : SPComp.sample K = SPComp.bind (SPComp.sample (Equiv.Perm K)) fun π =>
      SPComp.bind (SPComp.sample K) fun k => SPComp.pure (π k) := by
    refine (sample_bind_const (α := Equiv.Perm K) (SPComp.sample K)).symm.trans ?_
    congr 1
    funext π
    rw [SPComp.sample_bind_equiv π (fun k => SPComp.pure k), SPComp.bind_pure]
  rw [h₁, SPComp.isPure_bind_comm_right _ _ _ (SPComp.sample_isPure K)]
  have h₂ : (fun k : K => SPComp.bind (SPComp.sample (Equiv.Perm K))
      fun π => SPComp.pure (π k)) = fun _ =>
        SPComp.map (fun π : Equiv.Perm K => π a) (SPComp.sample (Equiv.Perm K)) := by
    funext k
    exact hD k a
  rw [h₂, sample_bind_const]

/-- **Real-or-random from invariance under permutations of the key.** Let `μ` be a
computation of a pair `(z, w)` whose law is invariant under the action `g π` of every
permutation `π` of the keys on `w`, and let `sel` select an optional key from `w`, equivariant
for the action. Then `(z, the selected key)`, with a fresh uniform key in place of a missing
one, has the law of `(z, a fresh uniform key)`. -/
theorem bind_sel_eq_of_perm_invariant {ζ W : Type} (μ : SPComp (ζ × W))
    (g : Equiv.Perm K → W → W) (sel : W → Option K)
    (hμ : ∀ π, SPComp.map (fun w => (w.1, g π w.2)) μ = μ)
    (hsel : ∀ π w, sel (g π w) = (sel w).map π) :
    SPComp.bind μ (fun w => SPComp.map (fun k => (w.1, (sel w.2).getD k)) (SPComp.sample K)) =
      SPComp.bind μ (fun w => SPComp.map (fun k => (w.1, k)) (SPComp.sample K)) := by
  set f : ζ × W → SPComp (ζ × K) :=
    fun w => SPComp.map (fun k => (w.1, (sel w.2).getD k)) (SPComp.sample K) with hf
  have e₁ : SPComp.bind μ f = SPComp.bind (SPComp.sample (Equiv.Perm K)) fun π =>
      SPComp.bind μ fun w => f (w.1, g π w.2) := by
    rw [← sample_bind_const (α := Equiv.Perm K) (SPComp.bind μ f)]
    congr 1
    funext π
    conv_lhs => rw [← hμ π]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  rw [e₁, ← SPComp.isPure_bind_comm_right _ _ _ (SPComp.sample_isPure _)]
  congr 1
  funext w
  simp only [hf, hsel]
  rcases hs : sel w.2 with _ | a
  · simp only [Option.map_none, Option.getD_none]
    exact sample_bind_const _
  · simp only [Option.map_some, Option.getD_some]
    have h₃ : (fun π : Equiv.Perm K => SPComp.map (fun _ : K => (w.1, π a)) (SPComp.sample K)) =
        fun π => SPComp.pure (w.1, π a) := by
      funext π
      exact sample_bind_const _
    rw [h₃]
    have h₄ := congrArg (SPComp.map (fun k : K => (w.1, k))) (map_apply_sample_perm a)
    simp only [SPComp.map_comp] at h₄
    exact h₄

end Perm

/-! ## Equivariant systems and sealed strategies -/

section Equivariant

variable {τ ζ E O : Type}

/-- **Equivariance of a run.** If the map `g` of states commutes with every step of `X` at the
events of `Ok`, and every event the strategy `Z` chooses satisfies `Ok`, then `g` commutes with
every number of rounds of the run without flag. -/
theorem loop_map_of_equivariant (X : Sys τ E O) (g : τ → τ) (Ok : E → Prop)
    (hX : ∀ t e, Ok e → SPComp.map (fun p => (g p.1, p.2)) (X.step t e) = X.step (g t) e)
    (Z : Strat ζ E O) (hZ : ∀ z a, IsOutcome (Z.next z) a → Ok a.2) :
    ∀ n (c : ζ × τ × Bool), SPComp.map (fun c => (c.1, g c.2.1, c.2.2))
        (loop X (fun _ => false) Z n c) = loop X (fun _ => false) Z n (c.1, g c.2.1, c.2.2) := by
  intro n
  induction n with
  | zero => intro c; simp only [loop, SPComp.map_pure]
  | succ n ih =>
    intro c
    simp only [loop, SPComp.map, SPComp.bind_assoc]
    refine bind_congr_isOutcome fun a ha => ?_
    rw [← hX c.2.1 a.2 (hZ c.1 a ha)]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext p; congr 1; funext z
    exact ih (z, p.1, c.2.2 || false)

/-- The run without flag, with the final states of the strategy and of the system. -/
noncomputable def runW (X : Sys τ E O) (Z : Strat ζ E O) : SPComp (ζ × τ) :=
  SPComp.map (fun c => (c.1, c.2.1)) (run X (fun _ => false) Z)

/-- **Invariance of the run.** A map of states that fixes the initial state and commutes with
the steps at the events the strategy chooses leaves the law of the final pair invariant. -/
theorem runW_map_of_equivariant (X : Sys τ E O) (g : τ → τ) (Ok : E → Prop)
    (hX : ∀ t e, Ok e → SPComp.map (fun p => (g p.1, p.2)) (X.step t e) = X.step (g t) e)
    (hinit : g X.init = X.init)
    (Z : Strat ζ E O) (hZ : ∀ z a, IsOutcome (Z.next z) a → Ok a.2) :
    SPComp.map (fun w => (w.1, g w.2)) (runW X Z) = runW X Z := by
  have h := loop_map_of_equivariant X g Ok hX Z hZ Z.rounds (Z.init, X.init, false)
  simp only [hinit] at h
  unfold runW run
  conv_rhs => rw [← h]
  simp only [SPComp.map_comp]
  rfl

end Equivariant

/-! ## The permutation of the keys of a protocol session -/

section KeyPerm

variable {K : Type}

/-- The permutation `π` applied to the key of the record `r` of the session `x`, when `x` is in
the protocol session `sid₀` and completed (its key was chosen by the functionality). -/
def keyPermRec (sid₀ : SessionId) (π : Equiv.Perm K) (x : Inst) (r : Rec K) : Rec K :=
  if x.1 = sid₀ ∧ r.status = .completed then { r with key := r.key.map π } else r

/-- **The permutation of the completed keys of `sid₀`** on the state of `F_AKE`. -/
def keyPerm (sid₀ : SessionId) (π : Equiv.Perm K) (t : St K) : St K :=
  { t with recs := fun x => (t.recs x).map (keyPermRec sid₀ π x) }

variable (sid₀ : SessionId) (π : Equiv.Perm K)

theorem keyPermRec_peer (x : Inst) (r : Rec K) : (keyPermRec sid₀ π x r).peer = r.peer := by
  unfold keyPermRec; split <;> rfl

theorem keyPermRec_role (x : Inst) (r : Rec K) : (keyPermRec sid₀ π x r).role = r.role := by
  unfold keyPermRec; split <;> rfl

theorem keyPermRec_status (x : Inst) (r : Rec K) :
    (keyPermRec sid₀ π x r).status = r.status := by
  unfold keyPermRec; split <;> rfl

theorem keyPermRec_key_isNone (x : Inst) (r : Rec K) :
    (keyPermRec sid₀ π x r).key.isNone = r.key.isNone := by
  unfold keyPermRec; split <;> simp

theorem keyPermRec_of_key_none (x : Inst) (r : Rec K) (h : r.key = none) :
    keyPermRec sid₀ π x r = r := by
  unfold keyPermRec; split <;> (cases r; simp_all)

theorem keyPermRec_of_ne (x : Inst) (r : Rec K) (h : x.1 ≠ sid₀) :
    keyPermRec sid₀ π x r = r := by
  unfold keyPermRec; simp [h]

theorem keyPerm_initSt : keyPerm sid₀ π (initSt : St K) = initSt := rfl

theorem keyPerm_setRec (t : St K) (x : Inst) (r : Rec K) :
    keyPerm sid₀ π (setRec t x r) = setRec (keyPerm sid₀ π t) x (keyPermRec sid₀ π x r) := by
  simp only [keyPerm, setRec, St.mk.injEq, and_true]
  funext y
  by_cases h : y = x
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem keyPerm_addSession (t : St K) (x : Inst) (peer : PartyId) (role : Role) :
    keyPerm sid₀ π (addSession t x peer role) = addSession (keyPerm sid₀ π t) x peer role := by
  unfold addSession
  by_cases h : (t.recs x).isSome
  · have h' : ((keyPerm sid₀ π t).recs x).isSome := by simpa [keyPerm] using h
    simp only [h, h', ↓reduceIte]
  · have h' : ¬ ((keyPerm sid₀ π t).recs x).isSome := by simpa [keyPerm] using h
    simp only [h, h', ↓reduceIte, Bool.false_eq_true]
    simp only [keyPerm, St.mk.injEq, and_true]
    funext y
    by_cases hy : y = x
    · subst hy; simp [keyPermRec_of_key_none]
    · simp [Function.update_of_ne hy]

theorem keyOf_keyPerm_of_ne (t : St K) (x : Inst) (h : x.1 ≠ sid₀) :
    keyOf (keyPerm sid₀ π t) x = keyOf t x := by
  simp only [keyOf, keyPerm]
  cases t.recs x <;> simp [keyPermRec_of_ne _ _ _ _ h]

theorem pollStep_keyPerm (t : St K) :
    pollStep (keyPerm sid₀ π t) = (keyPerm sid₀ π (pollStep t).1, (pollStep t).2) := by
  unfold pollStep
  split <;> simp_all [keyPerm]

theorem keyPerm_corruptStep (t : St K) (pid : PartyId) :
    keyPerm sid₀ π (corruptStep t pid) = corruptStep (keyPerm sid₀ π t) pid := rfl

theorem exposed_keyPerm (t : St K) (x : Inst) (r : Rec K) :
    Exposed (keyPerm sid₀ π t) x (keyPermRec sid₀ π x r) ↔ Exposed t x r := by
  simp only [Exposed, keyPerm, keyPermRec_peer, keyPermRec_status]

theorem partner_keyPerm (x y : Inst) (r p : Rec K) :
    Partner x r (keyPermRec sid₀ π y p) ↔ Partner x r p := by
  simp only [Partner, keyPermRec_peer, keyPermRec_role, keyPermRec_status]

/-- The fresh sample seen through the permutation: `π kf` in `sid₀`, `kf` elsewhere. -/
def kfPerm (x : Inst) (kf : K) : K := if x.1 = sid₀ then π kf else kf

theorem keyPerm_newKeyStep (t : St K) (x : Inst) (k kf : K) :
    keyPerm sid₀ π (newKeyStep t x k kf) =
      newKeyStep (keyPerm sid₀ π t) x k (kfPerm sid₀ π x kf) := by
  unfold newKeyStep
  rcases hr : t.recs x with _ | r
  · have : (keyPerm sid₀ π t).recs x = none := by simp [keyPerm, hr]
    simp only [this]
  · have h1 : (keyPerm sid₀ π t).recs x = some (keyPermRec sid₀ π x r) := by
      simp [keyPerm, hr]
    simp only [h1, keyPermRec_key_isNone]
    by_cases hk : r.key.isNone
    · have hk' : r.key = none := Option.isNone_iff_eq_none.mp hk
      simp only [hk, ↓reduceIte, keyPerm_setRec, keyPermRec_of_key_none _ _ _ _ hk']
      congr 1
      have hE := exposed_keyPerm sid₀ π t x r
      rw [keyPermRec_of_key_none _ _ _ _ hk'] at hE
      unfold newKeyVal
      simp only [hE]
      by_cases he : Exposed t x r
      · simp [keyPermRec, he]
      · simp only [he, ↓reduceIte]
        have hp : (keyPerm sid₀ π t).recs (x.1, r.peer) =
            (t.recs (x.1, r.peer)).map (keyPermRec sid₀ π (x.1, r.peer)) := rfl
        rw [hp]
        by_cases hs : x.1 = sid₀
        · rcases t.recs (x.1, r.peer) with _ | p
          · simp [keyPermRec, kfPerm, hs]
          · by_cases hpc : p.status = .completed <;>
              simp_all [keyPermRec, kfPerm, Partner, Option.getD_map, apply_ite]
        · rcases t.recs (x.1, r.peer) with _ | p
          · simp [keyPermRec, kfPerm, hs]
          · simp [keyPermRec, kfPerm, hs]
    · simp only [hk, ↓reduceIte, Bool.false_eq_true]

theorem keyPerm_newKeyFreshStep (t : St K) (x : Inst) (k kf : K) :
    keyPerm sid₀ π (newKeyFreshStep t x k kf) =
      newKeyFreshStep (keyPerm sid₀ π t) x k (kfPerm sid₀ π x kf) := by
  unfold newKeyFreshStep
  rcases hr : t.recs x with _ | r
  · have : (keyPerm sid₀ π t).recs x = none := by simp [keyPerm, hr]
    simp only [this]
  · have h1 : (keyPerm sid₀ π t).recs x = some (keyPermRec sid₀ π x r) := by
      simp [keyPerm, hr]
    simp only [h1, keyPermRec_key_isNone]
    by_cases hk : r.key.isNone
    · have hk' : r.key = none := Option.isNone_iff_eq_none.mp hk
      simp only [hk, ↓reduceIte, keyPerm_setRec, keyPermRec_of_key_none _ _ _ _ hk']
      congr 1
      have hE := exposed_keyPerm sid₀ π t x r
      rw [keyPermRec_of_key_none _ _ _ _ hk'] at hE
      simp only [hE]
      by_cases he : Exposed t x r
      · simp [keyPermRec, he]
      · by_cases hs : x.1 = sid₀ <;> simp [keyPermRec, kfPerm, he, hs]
    · simp only [hk, ↓reduceIte, Bool.false_eq_true]

end KeyPerm

/-! ## Equivariance of `F_AKE` -/

section FAKEEquiv

variable {K : Type} [Fintype K] [Nonempty K] (sid₀ : SessionId) (π : Equiv.Perm K)

/-- **The events of `F_AKE` that do not read a key of `sid₀`**: every event except `getKey` at
a session of `sid₀`. -/
def SealedF (sid₀ : SessionId) : HEv ⊕ AEv K → Prop
  | .inl (.getKey sid _) => sid ≠ sid₀
  | _ => True

/-- The uniform fresh sample seen through the permutation is the uniform fresh sample. -/
theorem map_kfPerm_sample {β : Type} (x : Inst) (f : K → β) :
    SPComp.map (fun kf => f (kfPerm sid₀ π x kf)) (SPComp.sample K) =
      SPComp.map f (SPComp.sample K) := by
  unfold kfPerm SPComp.map
  by_cases hs : x.1 = sid₀
  · simp only [hs, ↓reduceIte]
    exact SPComp.sample_bind_equiv π (fun k => SPComp.pure (f k))
  · simp only [hs, ↓reduceIte]

/-- **Equivariance of `F_AKE`**: at every event that does not read a key of `sid₀`, the
permutation of the completed keys of `sid₀` commutes with the step and leaves the output
unchanged. -/
theorem F_AKE_step_keyPerm (unlinked : Bool) (t : St K) (e : HEv ⊕ AEv K)
    (he : SealedF sid₀ e) :
    SPComp.map (fun p => (keyPerm sid₀ π p.1, p.2)) ((F_AKE (SPComp.sample K) unlinked).step t e) =
      (F_AKE (SPComp.sample K) unlinked).step (keyPerm sid₀ π t) e := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | a
  · simp [F_AKE, honSys, FAKE.honStep, keyPerm_addSession]
  · simp only [SealedF] at he
    simp [F_AKE, honSys, FAKE.honStep, keyOf_keyPerm_of_ne _ _ _ (sid, pid) he]
  · cases a with
    | idle => simp [F_AKE, advSys]
    | poll => simp [F_AKE, advSys, pollStep_keyPerm]
    | corrupt pid => simp [F_AKE, advSys, keyPerm_corruptStep]
    | impersonate sid pid => simp [F_AKE, advSys]
    | newKey sid pid k =>
      simp only [F_AKE, Sys.ofPorts_step_inr, advSys, SPComp.map_comp]
      refine Eq.trans ?_ (map_kfPerm_sample sid₀ π (sid, pid) _)
      congr 1
      funext kf
      simp [keyPerm_newKeyStep]
    | newKeyUnlinked sid pid k =>
      simp only [F_AKE, Sys.ofPorts_step_inr, advSys, SPComp.map_comp]
      refine Eq.trans ?_ (map_kfPerm_sample sid₀ π (sid, pid) _)
      congr 1
      funext kf
      cases unlinked <;> simp [keyPerm_newKeyStep, keyPerm_newKeyFreshStep]

end FAKEEquiv

/-! ## Equivariance through a multi-call simulator -/

section MultiEquiv

variable {σ τ E O EG OG : Type}

/-- A decision of a multi-call hybrid satisfies `Ok` when it is a call at an event of `Ok`. -/
def DecOk (Ok : EG → Prop) : EG ⊕ O → Prop := Sum.elim Ok fun _ => True

/-- The rest of an activation commutes with an equivariant map of the subroutine states, when
the calls the hybrid makes after an answer satisfy `Ok`. -/
theorem drive_map_of_equivariant (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) (g : τ → τ)
    (Ok : EG → Prop)
    (hX : ∀ t e, Ok e → SPComp.map (fun p => (g p.1, p.2)) (X.step t e) = X.step (g t) e)
    (hres : ∀ s o r, IsOutcome (π.resume s o) r → DecOk Ok r.2) :
    ∀ n s (d : EG ⊕ O) t, DecOk Ok d →
      SPComp.map (fun p => (p.1, g p.2.1, p.2.2)) (π.drive X n s d t) = π.drive X n s d (g t) := by
  intro n
  induction n with
  | zero =>
    rintro s (e | o) t hd
    · simp only [MultiHybrid.drive, ← hX t e hd, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
    · simp only [MultiHybrid.drive, SPComp.map_pure]
  | succ n ih =>
    rintro s (e | o) t hd
    · simp only [MultiHybrid.drive, ← hX t e hd, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
      congr 1; funext q
      exact bind_congr_isOutcome fun r hr => ih r.1 r.2 q.1 (hres s q.2 r hr)
    · simp only [MultiHybrid.drive, SPComp.map_pure]

/-- **Equivariance through a multi-call hybrid.** If the hybrid calls the subroutine only at
events of `Ok` when it starts at an event of `OkE` and when it resumes, an equivariant map of
the subroutine states commutes with the steps of the composed system at the events of `OkE`. -/
theorem withSub_step_map_of_equivariant (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    (g : τ → τ) (Ok : EG → Prop) (OkE : E → Prop)
    (hX : ∀ t e, Ok e → SPComp.map (fun p => (g p.1, p.2)) (X.step t e) = X.step (g t) e)
    (hstart : ∀ s e r, OkE e → IsOutcome (π.start s e) r → DecOk Ok r.2)
    (hres : ∀ s o r, IsOutcome (π.resume s o) r → DecOk Ok r.2) (t : σ × τ) (e : E)
    (he : OkE e) :
    SPComp.map (fun p => ((p.1.1, g p.1.2), p.2)) ((π.withSub X).step t e) =
      (π.withSub X).step (t.1, g t.2) e := by
  simp only [MultiHybrid.withSub, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  refine bind_congr_isOutcome fun r hr => ?_
  rw [← drive_map_of_equivariant π X g Ok hX hres π.fuel r.1 r.2 t.2 (hstart t.1 e r he hr)]
  simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end MultiEquiv

/-! ## Equivariance of the world of `F_AKE` -/

section World

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W)

/-- **The events of the environment that do not read a key of `sid₀`**: every event except
`getKey` at a session of `sid₀`. The condition is decidable. -/
def SealedEv (sid₀ : SessionId) : OEv W → Prop
  | .inl (.getKey sid _) => sid ≠ sid₀
  | _ => True

instance (sid₀ : SessionId) (e : OEv W) : Decidable (SealedEv sid₀ e) := by
  rcases e with (_ | _) | _ <;> simp only [SealedEv] <;> infer_instance

omit [Field S] [Fintype S] in
theorem deliver_decOk (sid₀ : SessionId) (rs : RSt S W K) (inp : Inst → Option (Inp W))
    (x : Inst) (r : Rec K) (ip : Inp W) :
    ∀ q, IsOutcome (deliver rs inp x r ip) q → DecOk (SealedF sid₀) q.2 := by
  unfold deliver
  split
  · exact forall_isOutcome_map.mpr fun _ _ => trivial
  · exact forall_isOutcome_pure.mpr trivial

/-- The simulator calls `F_AKE` on its honest port only with the honest event of the
environment: at an event of `SealedEv sid₀` it makes calls of `SealedF sid₀` only. -/
theorem simStart_decOk (sid₀ : SessionId) (s : SimSt S W K) (e : OEv W)
    (he : SealedEv sid₀ e) :
    ∀ q, IsOutcome (simStart G s e) q → DecOk (SealedF sid₀) q.2 := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)
  · simp only [simStart]
    split
    · exact forall_isOutcome_map.mpr fun _ _ => trivial
    · exact forall_isOutcome_pure.mpr trivial
  · exact forall_isOutcome_pure.mpr he
  · exact forall_isOutcome_pure.mpr trivial
  · exact forall_isOutcome_pure.mpr trivial
  · exact forall_isOutcome_map.mpr fun _ _ => trivial
  · exact forall_isOutcome_pure.mpr trivial
  · simp only [simStart, simCorrupt]
    split
    · exact forall_isOutcome_pure.mpr trivial
    · exact forall_isOutcome_map.mpr fun _ _ => trivial
  · simp only [simStart, simComplete]
    repeat' split
    all_goals first
      | exact forall_isOutcome_pure.mpr trivial
      | exact forall_isOutcome_bind fun _ _ => forall_isOutcome_bind fun _ _ =>
          deliver_decOk _ _ _ _ _ _
  · simp only [simStart, simSend]
    repeat' split
    all_goals first
      | exact forall_isOutcome_pure.mpr trivial
      | exact forall_isOutcome_bind fun _ _ => forall_isOutcome_bind fun _ _ =>
          deliver_decOk _ _ _ _ _ _
  · exact forall_isOutcome_map.mpr fun _ _ => trivial

/-- **Equivariance of the world of `F_AKE`**: at every event of the environment that does not
read a key of `sid₀`, the permutation of the completed keys of `sid₀` in the state of `F_AKE`
commutes with the step of `F_AKE` behind the X3DH simulator. -/
theorem simWorld_step_keyPerm (sid₀ : SessionId) (π : Equiv.Perm K)
    (t : SimSt S W K × St K) (e : OEv W) (he : SealedEv sid₀ e) :
    SPComp.map (fun p => ((p.1.1, keyPerm sid₀ π p.1.2), p.2))
        (((simProt (K := K) G).withSub (F_AKE (SPComp.sample K) true)).step t e) =
      ((simProt (K := K) G).withSub (F_AKE (SPComp.sample K) true)).step
        (t.1, keyPerm sid₀ π t.2) e :=
  withSub_step_map_of_equivariant _ _ _ (SealedF sid₀) (SealedEv sid₀)
    (fun t e h => F_AKE_step_keyPerm sid₀ π true t e h)
    (fun s e r h hr => simStart_decOk G sid₀ s e h r hr)
    (fun _ _ r hr => by
      have := isOutcome_pure hr
      subst this
      trivial) t e he

end World

/-! ## Key secrecy of `F_AKE` behind the simulator -/

section Secrecy

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W)

/-- **The selected key** of the session `x₀` in a state of `F_AKE`: its key when the session
is completed (it received a key chosen by the functionality, not exposed at delivery), and
nothing otherwise. -/
def selKey (x₀ : Inst) (t : St K) : Option K :=
  match t.recs x₀ with
  | some r => if r.status = .completed then r.key else none
  | none => none

omit [Fintype K] [Nonempty K] [Inhabited K] in
theorem selKey_keyPerm (x₀ : Inst) (π : Equiv.Perm K) (t : St K) :
    selKey x₀ (keyPerm x₀.1 π t) = (selKey x₀ t).map π := by
  unfold selKey keyPerm
  rcases hr : t.recs x₀ with _ | r
  · simp [hr]
  · by_cases hc : r.status = .completed <;> simp [hr, keyPermRec, hc]

omit [Fintype K] [Nonempty K] [Inhabited K] in
theorem keyOf_of_selKey {x₀ : Inst} {t : St K} {a : K} (h : selKey x₀ t = some a) :
    keyOf t x₀ = some a := by
  unfold selKey at h
  unfold keyOf
  rcases hr : t.recs x₀ with _ | r
  · simp [hr] at h
  · simp only [hr] at h
    split at h
    · simpa using h
    · simp at h

/-- **The sealing predicate**: every event that the strategy `Z` can choose, from every state,
is an event of `SealedEv sid₀`; `Z` never asks for the key of a session of `sid₀`. It is a
condition on the possible outcomes of the choice `Z.next` alone, as `X3DHSquareGDH.NamesIn` is
a condition on the queries of every path of an oracle adversary; `SealedEv` is decidable. -/
def Sealed {ζ : Type} (sid₀ : SessionId) (Z : Strat ζ (OEv W) (OOut S W K)) : Prop :=
  ∀ z a, IsOutcome (Z.next z) a → SealedEv sid₀ a.2

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- A strategy whose choice is a deterministic event of `SealedEv sid₀` after a choice of its
next state is sealed. -/
theorem sealed_of_next_eq {ζ : Type} {sid₀ : SessionId} (Z : Strat ζ (OEv W) (OOut S W K))
    (c : ζ → SPComp ζ) (ev : ζ → OEv W) (hev : ∀ z, SealedEv sid₀ (ev z))
    (hn : ∀ z, Z.next z = SPComp.map (fun z' => (z', ev z)) (c z)) :
    Sealed (K := K) (S := S) sid₀ Z := fun z a ha => by
  rw [hn z] at ha
  obtain ⟨_, _, rfl⟩ := isOutcome_map_iff.mp ha
  exact hev z

/-- The game of the selected key: the run of `Z` against `X`, then the final state of `Z` and
the key `sel` selects from the final state of `X`, a fresh uniform key when it selects none. -/
noncomputable def keySelGame {τ ζ E O : Type} (X : Sys τ E O) (Z : Strat ζ E O)
    (sel : τ → Option K) : SPComp (ζ × K) :=
  SPComp.bind (runW X Z) fun w => SPComp.map (fun k => (w.1, (sel w.2).getD k)) (SPComp.sample K)

/-- The game of a random key: the run of `Z` against `X`, then the final state of `Z` and a
fresh uniform key. -/
noncomputable def keyRandGame {τ ζ E O : Type} (X : Sys τ E O) (Z : Strat ζ E O) :
    SPComp (ζ × K) :=
  SPComp.bind (runW X Z) fun w => SPComp.map (fun k => (w.1, k)) (SPComp.sample K)

/-- **Key secrecy of `F_AKE` behind the X3DH simulator.** For every strategy `Z` sealed for
the protocol session of `x₀` (it never asks for a key of that protocol session), the final
state of `Z` and the key of `x₀` when `F_AKE` completed it (a fresh uniform key otherwise)
have the law of the final state of `Z` and a fresh uniform key.

The proof is a coupling by symmetry: every permutation `π` of the keys, applied to the keys of
the completed sessions of the protocol session of `x₀`, commutes with every step of `F_AKE` at
the events of the simulator (`F_AKE_step_keyPerm`, `simWorld_step_keyPerm`), since `F_AKE`
draws these keys uniformly and outputs them only on `getKey`; the law of the run is invariant
(`runW_map_of_equivariant`), and a uniform permutation sends the selected key to a uniform key
(`bind_sel_eq_of_perm_invariant`). -/
theorem x3dhIdeal_key_secrecy {ζ : Type} (x₀ : Inst) (Z : Strat ζ (OEv W) (OOut S W K))
    (hZ : Sealed x₀.1 Z) :
    keySelGame (x3dhIdeal G) Z (fun t => selKey x₀ t.2) = keyRandGame (x3dhIdeal G) Z := by
  classical
  exact bind_sel_eq_of_perm_invariant (runW (x3dhIdeal G) Z)
    (fun π w => (w.1, keyPerm x₀.1 π w.2)) (fun w => selKey x₀ w.2)
    (fun π => runW_map_of_equivariant (x3dhIdeal G) (fun w => (w.1, keyPerm x₀.1 π w.2))
      (SealedEv x₀.1) (fun t e he => simWorld_step_keyPerm G x₀.1 π t e he) rfl Z hZ)
    (fun π w => selKey_keyPerm x₀ π w.2)

/-- **The real-or-random advantage of the selected key is `0`**: no distinguisher of the final
state of a sealed `Z` and a key tells the key of `x₀` (when completed) from a fresh one. -/
theorem x3dhIdeal_key_secrecy_advantage {ζ : Type} (x₀ : Inst) (Z : Strat ζ (OEv W) (OOut S W K))
    (hZ : Sealed x₀.1 Z) (D : ζ × K → SPComp Bool) :
    AdvantageA (keySelGame (x3dhIdeal G) Z fun t => selKey x₀ t.2)
      (keyRandGame (x3dhIdeal G) Z) D = 0 := by
  rw [x3dhIdeal_key_secrecy G x₀ Z hZ]
  exact Advantage_self _

end Secrecy

/-! ## The environment that reads the key at the end -/

section ThenAsk

variable {τ ζ E O Kk : Type}

/-- The choice of `thenAsk`: the choice of `Z` for its rounds, then `e₀`. -/
noncomputable def thenAskNext (Z : Strat ζ E O) (e₀ : E) (c : ζ × ℕ × Kk) :
    SPComp ((ζ × ℕ × Kk) × E) :=
  if c.2.1 < Z.rounds then SPComp.map (fun a => ((a.1, c.2.1 + 1, c.2.2), a.2)) (Z.next c.1)
  else SPComp.pure ((c.1, c.2.1 + 1, c.2.2), e₀)

/-- The observation of `thenAsk`: the observation of `Z` for its rounds, then the value read
from the last output. -/
noncomputable def thenAskObs (Z : Strat ζ E O) (rd : O → Kk) (c : ζ × ℕ × Kk) (o : O) :
    SPComp (ζ × ℕ × Kk) :=
  if c.2.1 ≤ Z.rounds then SPComp.map (fun z => (z, c.2.1, c.2.2)) (Z.obs c.1 o)
  else SPComp.pure (c.1, c.2.1, rd o)

/-- **The strategy `Z` followed by one event `e₀`**: the state is the state of `Z`, the number of
activations so far and the value `rd o` read from the output `o` of the last activation; `Z`
runs for its rounds, then the extra activation sends `e₀`. -/
noncomputable def thenAsk (Z : Strat ζ E O) (e₀ : E) (rd : O → Kk) (k₀ : Kk) :
    Strat (ζ × ℕ × Kk) E O where
  rounds := Z.rounds + 1
  init := (Z.init, 0, k₀)
  next := thenAskNext Z e₀
  obs := thenAskObs Z rd
  next_noFail c := by
    unfold thenAskNext
    split
    · exact Assumptions.SPComp.bind_noFail (Z.next_noFail _) fun _ => SPComp.pure_noFail _
    · exact SPComp.pure_noFail _
  obs_noFail c o := by
    unfold thenAskObs
    split
    · exact Assumptions.SPComp.bind_noFail (Z.obs_noFail _ _) fun _ => SPComp.pure_noFail _
    · exact SPComp.pure_noFail _

/-- The last activation of `thenAsk`: the step of `X` at `e₀` and the value read from its
output. -/
noncomputable def askStep (X : Sys τ E O) (e₀ : E) (rd : O → Kk) (n : ℕ) (c : ζ × τ × Bool) :
    SPComp ((ζ × ℕ × Kk) × τ × Bool) :=
  SPComp.bind (X.step c.2.1 e₀) fun p => SPComp.pure ((c.1, n, rd p.2), p.1, c.2.2 || false)

theorem loop_thenAsk (X : Sys τ E O) (Z : Strat ζ E O) (e₀ : E) (rd : O → Kk) (k₀ : Kk) :
    ∀ m (z : ζ) (t : τ) (b : Bool) (k : Kk), m ≤ Z.rounds →
      loop X (fun _ => false) (thenAsk Z e₀ rd k₀) (m + 1) ((z, Z.rounds - m, k), t, b) =
        SPComp.bind (loop X (fun _ => false) Z m (z, t, b))
          (askStep X e₀ rd (Z.rounds + 1)) := by
  intro m
  induction m with
  | zero =>
    intro z t b k _
    simp only [loop, thenAsk, thenAskNext, thenAskObs, Nat.sub_zero, lt_self_iff_false,
      ↓reduceIte, SPComp.pure_bind, askStep,
      show ¬ (Z.rounds + 1 ≤ Z.rounds) by omega]
  | succ m ih =>
    intro z t b k hm
    have h1 : Z.rounds - (m + 1) < Z.rounds := by omega
    have h2 : Z.rounds - (m + 1) + 1 ≤ Z.rounds := by omega
    have h3 : Z.rounds - (m + 1) + 1 = Z.rounds - m := by omega
    rw [loop]
    simp only [thenAsk, thenAskNext, thenAskObs, h1, h2, ↓reduceIte, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]
    rw [loop]
    simp only [SPComp.bind_assoc]
    congr 1; funext a; congr 1; funext p; congr 1; funext z'
    rw [h3]
    exact ih z' p.1 (b || false) k (by omega)

/-- The run of `thenAsk` is the run of `Z` followed by the last activation. -/
theorem run_thenAsk (X : Sys τ E O) (Z : Strat ζ E O) (e₀ : E) (rd : O → Kk) (k₀ : Kk) :
    run X (fun _ => false) (thenAsk Z e₀ rd k₀) =
      SPComp.bind (run X (fun _ => false) Z) (askStep X e₀ rd (Z.rounds + 1)) := by
  have h := loop_thenAsk X Z e₀ rd k₀ Z.rounds Z.init X.init false k₀ le_rfl
  simp only [Nat.sub_self] at h
  exact h

end ThenAsk

/-! ## The Signal stack with a sealed environment -/

section Stack

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W)

/-- The key read from an output: the key of a `key (some k)` output of the honest port, and the
default key otherwise. -/
def readOut : OOut S W K → K
  | .inl (.key (some k)) => k
  | _ => default

/-- **The environment `Z` that reads the key of `x₀` at the end**: `Z`, then one activation that
asks for the key of `x₀` on the honest port and stores it in the last component of the state. -/
noncomputable def readKey {ζ : Type} (Z : Strat ζ (OEv W) (OOut S W K)) (x₀ : Inst) :
    Strat (ζ × ℕ × K) (OEv W) (OOut S W K) :=
  thenAsk Z (.inl (.getKey x₀.1 x₀.2)) readOut default

/-- **Completion of the selected session**: on every possible outcome of the run of `Z`
against `F_AKE` behind the simulator, `F_AKE` completed the session `x₀` (it delivered to it a
key of its own choice, not exposed at delivery). -/
def CompletesAt {ζ : Type} (x₀ : Inst) (Z : Strat ζ (OEv W) (OOut S W K)) : Prop :=
  ∀ w, IsOutcome (runW (x3dhIdeal G) Z) w → (selKey x₀ w.2.2).isSome

/-- The step of the world of `F_AKE` at `getKey`: the key of the session from `F_AKE`. -/
theorem x3dhIdeal_step_getKey (s : SimSt S W K) (t : St K) (sid : SessionId) (pid : PartyId) :
    (x3dhIdeal G).step (s, t) (.inl (.getKey sid pid)) =
      SPComp.pure (((s.1, s.2.1, .fwd), t), .inl (.key (keyOf t (sid, pid)))) := by
  show ((simProt (K := K) G).withSub (F_AKE (SPComp.sample K) true)).step _ _ = _
  simp [MultiHybrid.withSub, simProt, simStart, MultiHybrid.drive, F_AKE, honSys, FAKE.honStep,
    simOut, SPComp.map, SPComp.pure_bind]

/-- The view of `readKey Z x₀` against the world of `F_AKE`: the final state of `Z` and the key
of `x₀` in the final state of `F_AKE`. -/
theorem view_x3dhIdeal_readKey {ζ : Type} (Z : Strat ζ (OEv W) (OOut S W K)) (x₀ : Inst) :
    view (x3dhIdeal G) (readKey Z x₀) = SPComp.map
      (fun w => (w.1, Z.rounds + 1, (keyOf w.2.2 x₀).getD default)) (runW (x3dhIdeal G) Z) := by
  unfold view readKey runW
  rw [run_thenAsk]
  simp only [askStep, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext c
  obtain ⟨z, ⟨s, t⟩, b⟩ := c
  erw [x3dhIdeal_step_getKey G s t x₀.1 x₀.2, SPComp.pure_bind]
  rcases keyOf t x₀ with _ | k <;> rfl

/-- **The real-or-random term of the stack vanishes for a sealed environment.** Let `Z` be
sealed for the protocol session of `x₀` and complete `x₀` on every run against `F_AKE` behind
the simulator. For the environment `readKey Z x₀`, the selection of the key it reads and every
distinguisher `D` of the final state of `Z` and the key, `keyRORAdv` is `0`. -/
theorem keyRORAdv_readKey_eq_zero {ζ : Type} (Z : Strat ζ (OEv W) (OOut S W K)) (x₀ : Inst)
    (hZ : Sealed x₀.1 Z) (hdone : CompletesAt G x₀ Z) (D : ζ × K → SPComp Bool) :
    keyRORAdv (x3dhIdeal G) (readKey Z x₀) (fun z => z.2.2) (fun p => D (p.1.1, p.2)) = 0 := by
  have hsec := congrArg (fun c => SPComp.bind c D) (x3dhIdeal_key_secrecy G x₀ Z hZ)
  simp only [keySelGame, keyRandGame, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind] at hsec
  unfold keyRORAdv AdvantageA
  have e₁ : SPComp.bind (stackGame (x3dhIdeal G) (readKey Z x₀) fun z => SPComp.pure z.2.2)
      (fun p => D (p.1.1, p.2)) = SPComp.bind (runW (x3dhIdeal G) Z) fun w =>
        SPComp.bind (SPComp.sample K) fun k => D (w.1, (selKey x₀ w.2.2).getD k) := by
    simp only [stackGame, view_x3dhIdeal_readKey, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
    refine bind_congr_isOutcome fun w hw => ?_
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hdone w hw)
    rw [ha, keyOf_of_selKey ha]
    exact (sample_bind_const _).symm
  have e₂ : SPComp.bind (stackGame (x3dhIdeal G) (readKey Z x₀) fun _ => SPComp.sample K)
      (fun p => D (p.1.1, p.2)) = SPComp.bind (runW (x3dhIdeal G) Z) fun w =>
        SPComp.bind (SPComp.sample K) fun k => D (w.1, k) := by
    simp only [stackGame, view_x3dhIdeal_readKey, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
  rw [e₁, e₂, hsec]
  exact Advantage_self _

variable {Sc Msg Key Sa M Ct : Type} [SampleableType M] [SampleableType Ct] [Fintype Key]
  [Nonempty Key] [Fintype Sa] [Nonempty Sa]

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] in
/-- **The Signal stack theorem for a sealed environment.** Let the CKA `C` neither touch the
heap nor fail. Let `Z` be an environment of the X3DH protocol that never asks for a key of the
protocol session of `x₀` (`Sealed`) and whose run against `F_AKE` behind the X3DH simulator
completes `x₀` (`CompletesAt`). The environment `readKey Z x₀` runs `Z` and then reads the
session key of `x₀` on the honest port. For every finite set of parties `P` and every
distinguisher `A` of the final state of `Z` and the view of the ratchet, the distance between
* the real stack: `readKey Z x₀` against the real X3DH protocol, then the double ratchet
  `smRealAt` with the root key read for `x₀`, and
* the ideal stack: `readKey Z x₀` against `F_AKE` behind the X3DH simulator, then `sm_ideal`,

is at most the gap Diffie–Hellman bound of the X3DH square at the environment `stackEnv` and
the secure-messaging advantage of the reduction `stackSMRed`: the real-or-random term of
`signal_stack_advantage_le` is `0` (`keyRORAdv_readKey_eq_zero`). -/
theorem signal_stack_advantage_le_sealed (P : Finset PartyId) {C : CKADef Sc Msg Key}
    (hC : CKAPureNF C) (R : PRGDef (K × Key) (K × Sa)) (Gp : PRGDef Sa (M × Sa))
    (D : AEADDef M Ct) (msgs : List (List (M × M))) {ζ : Type}
    (Z : Strat ζ (OEv W) (OOut S W K)) (x₀ : Inst) (hZ : Sealed x₀.1 Z)
    (hdone : CompletesAt G x₀ Z) (A : ζ × SMView Msg Ct → SPComp Bool) :
    AdvantageA
        (stackGame (x3dhReal (K := K) G) (readKey Z x₀) fun z => smRealAt C R Gp D msgs z.2.2)
        (stackGame (x3dhIdeal G) (readKey Z x₀) fun _ => sm_ideal C msgs)
        (fun p => A (p.1.1, p.2)) ≤
      gdhBound G P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction
          (stackEnv (readKey Z x₀) (fun z => smRealAt C R Gp D msgs z.2.2)
            (fun p => A (p.1.1, p.2)))) +
        SM_Advantage C R Gp D msgs (stackSMRed (x3dhIdeal G) (readKey Z x₀)
          (fun p => A (p.1.1, p.2))) := by
  have h := signal_stack_advantage_le G P hC R Gp D msgs (readKey Z x₀) (fun z => z.2.2)
    (fun p => A (p.1.1, p.2))
  have h0 : keyRORAdv (x3dhIdeal G) (readKey Z x₀) (fun z => z.2.2)
      (stackRORDist (smRealAt C R Gp D msgs) fun p => A (p.1.1, p.2)) = 0 :=
    keyRORAdv_readKey_eq_zero G Z x₀ hZ hdone (stackRORDist (smRealAt C R Gp D msgs) A)
  rw [h0, add_zero] at h
  exact h

/-- **The Signal stack theorem for a sealed environment, at the primitives.** The bound of
`signal_stack_advantage_le_sealed` with the secure-messaging advantage expanded by
`sm_advantage_le`: over the epochs `t`, the CKA advantages of `smCKARed`, the PRG advantages of
the root KDF at `smRootRed` and the FS-AEAD advantages of `smAEADRed`. -/
theorem signal_stack_advantage_le_sealed_primitives (P : Finset PartyId) {C : CKADef Sc Msg Key}
    (hC : CKAPureNF C) (R : PRGDef (K × Key) (K × Sa)) (Gp : PRGDef Sa (M × Sa))
    (D : AEADDef M Ct) (msgs : List (List (M × M))) {ζ : Type}
    (Z : Strat ζ (OEv W) (OOut S W K)) (x₀ : Inst) (hZ : Sealed x₀.1 Z)
    (hdone : CompletesAt G x₀ Z) (A : ζ × SMView Msg Ct → SPComp Bool) :
    AdvantageA
        (stackGame (x3dhReal (K := K) G) (readKey Z x₀) fun z => smRealAt C R Gp D msgs z.2.2)
        (stackGame (x3dhIdeal G) (readKey Z x₀) fun _ => sm_ideal C msgs)
        (fun p => A (p.1.1, p.2)) ≤
      gdhBound G P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction
          (stackEnv (readKey Z x₀) (fun z => smRealAt C R Gp D msgs z.2.2)
            (fun p => A (p.1.1, p.2)))) +
        (∑ t ∈ Finset.range msgs.length,
            CKA_Advantage C t (msgs.length - (t + 1))
              (smCKARed R Gp D msgs t (stackSMRed (x3dhIdeal G) (readKey Z x₀)
                (fun p => A (p.1.1, p.2)))) +
          ∑ t ∈ Finset.range msgs.length,
            PRG_Advantage R
              (smRootRed C R Gp D msgs t (msgs.length - (t + 1))
                (stackSMRed (x3dhIdeal G) (readKey Z x₀) (fun p => A (p.1.1, p.2)))) +
          ∑ t ∈ Finset.range msgs.length,
            FSAEAD_Advantage Gp D (msgs.getD t [])
              (smAEADRed C Gp D msgs t (msgs.length - (t + 1))
                (stackSMRed (x3dhIdeal G) (readKey Z x₀) (fun p => A (p.1.1, p.2))))) :=
  (signal_stack_advantage_le_sealed G P hC R Gp D msgs Z x₀ hZ hdone A).trans
    (add_le_add le_rfl (sm_advantage_le C R Gp D msgs _))

omit [Fintype Key] [Nonempty Key] in
/-- **The Signal stack theorem for a sealed environment with the Diffie–Hellman CKA.** With the
CKA `dhCKA Gc`, the CKA terms of `signal_stack_advantage_le_sealed_primitives` are the DDH
advantages of `ckaDDHRed` at `smCKARed` (`sm_dh_advantage_le`). -/
theorem signal_stack_advantage_le_sealed_dh (P : Finset PartyId) (Gc : Type) [CyclicGroup Gc]
    (R : PRGDef (K × Gc) (K × Sa)) (Gp : PRGDef Sa (M × Sa)) (D : AEADDef M Ct)
    (msgs : List (List (M × M))) {ζ : Type} (Z : Strat ζ (OEv W) (OOut S W K)) (x₀ : Inst)
    (hZ : Sealed x₀.1 Z) (hdone : CompletesAt G x₀ Z) (A : ζ × SMView Gc Ct → SPComp Bool) :
    AdvantageA
        (stackGame (x3dhReal (K := K) G) (readKey Z x₀)
          fun z => smRealAt (dhCKA Gc) R Gp D msgs z.2.2)
        (stackGame (x3dhIdeal G) (readKey Z x₀) fun _ => sm_ideal (dhCKA Gc) msgs)
        (fun p => A (p.1.1, p.2)) ≤
      gdhBound G P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction
          (stackEnv (readKey Z x₀) (fun z => smRealAt (dhCKA Gc) R Gp D msgs z.2.2)
            (fun p => A (p.1.1, p.2)))) +
        (∑ t ∈ Finset.range msgs.length,
            DDH_Advantage Gc (ckaDDHRed t (msgs.length - (t + 1))
              (smCKARed R Gp D msgs t (stackSMRed (x3dhIdeal G) (readKey Z x₀)
                (fun p => A (p.1.1, p.2))))) +
          ∑ t ∈ Finset.range msgs.length,
            PRG_Advantage R (smRootRed (dhCKA Gc) R Gp D msgs t (msgs.length - (t + 1))
              (stackSMRed (x3dhIdeal G) (readKey Z x₀) (fun p => A (p.1.1, p.2)))) +
          ∑ t ∈ Finset.range msgs.length,
            FSAEAD_Advantage Gp D (msgs.getD t [])
              (smAEADRed (dhCKA Gc) Gp D msgs t (msgs.length - (t + 1))
                (stackSMRed (x3dhIdeal G) (readKey Z x₀) (fun p => A (p.1.1, p.2))))) :=
  (signal_stack_advantage_le_sealed G P (dhCKA_pureNF Gc) R Gp D msgs Z x₀ hZ hdone A).trans
    (add_le_add le_rfl (sm_dh_advantage_le Gc R Gp D msgs _))

end Stack

end CatCrypt.Crypto.Messaging.SignalStack
