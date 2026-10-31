/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Prog
public import CatCryptCore.Crypto.UCLoopbackMonoidal
public import CatCryptCore.Crypto.AKE.X3DHSquare

/-!
# Party programs with subroutine calls

A party with outer events `E`, outer outputs `O`, subroutine calls `Q` and subroutine answers
`A` is a program `Party.Prog (E ⊕ A) (Q ⊕ O) α`: the party language on the sum interface. The
party language (classical and quantum party) is one generic tree `Party.ProgE` with two effect
handlers, and the programs of this module are its classical instance. A call `Prog.call q k`
emits `inl q` and waits for an answer `inr a`, continuing with `k a`; `Prog.outE o` emits the
outer output `inr o`; `Prog.recvO` waits for an outer event `inl e`. Answers are events, so they
live in `Type`, and sampling between calls uses the codes of `Prog.sampleN`.

The denotation of such a program is a multi-call hybrid `MultiHybrid` of
`CatCryptCore.Crypto.UCTransparentMulti`. A system `X` on the sum interface gives the multi-call
hybrid `MultiHybrid.ofSys X n` with fuel `n`: `start` is the step of `X` on `inl e`, `resume`
and `finish` its step on `inr a`, so one activation makes as many calls as the program issues
before its outer output, at most `n + 1`. A step that may fail (a failing program, a call beyond
the fuel at `finish`) is replaced by the default output; this keeps the fields of `MultiHybrid`
free of failure. The loop of a body `body` is `Prog.loopMulti body s₀ n`, the multi-call hybrid
of `Prog.loopSys body s₀`.

Two multi-call hybrids are compared by an embedding of states (`MultiHybrid.Embeds π π' b c`):
`b` maps the states of `π` at activation boundaries and `c` the states with a call pending, and
`start`, `resume` and `finish` of `π'` at the embedded states are the images of those of `π`.
An embedding makes `π.withSub X` and `π'.withSub X` step-equivalent for every subroutine `X`
(`MultiHybrid.Embeds.stepEq`). The loop theorem `Prog.loopMulti_stepEq` derives the embedding
from per-step hypotheses on the activations of the body.

The worked example is the X3DH simulator `X3DHSquare.simProt` written as a program
(`X3DHProg.simBody`): the start of each activation is the program transcription of `simStart`,
which samples exactly `simStart` (`X3DHProg.simStartP_samples`), and the answer of `F_AKE` is
handled by the continuation of the call, so the phase field of the hand-written state is not
read by the program. The loop of the program running with any subroutine is step-equivalent to
the hand-written simulator running with it (`X3DHProg.simProt_stepEq_simLoop`).

## Main definitions

* `MultiHybrid.liftDec`, `MultiHybrid.Embeds`: embeddings of multi-call hybrids.
* `MultiHybrid.guardNF`, `MultiHybrid.ofSys`: the multi-call hybrid of a system on the sum
  interface.
* `Party.Prog.recvO`, `Party.Prog.recvA`, `Party.Prog.outE`, `Party.Prog.call`,
  `Party.Prog.callE`: the operations of programs with calls.
* `Party.Prog.loopMulti`: the multi-call hybrid of a loop.
* `Party.Prog.Samples`: a program that samples a computation and emits nothing.
* `X3DHProg.simStartP`, `X3DHProg.simBody`, `X3DHProg.simLoop`: the X3DH simulator as a program.

## Main results

* `MultiHybrid.Embeds.drive`, `MultiHybrid.Embeds.withSub_step`: an embedding commutes with
  the interaction with a subroutine.
* `MultiHybrid.Embeds.stepEq`: an embedding gives step equivalence over every subroutine.
* `MultiHybrid.ofSys_embeds`: an embedding into `ofSys X` from per-step equations of `X`.
* `Party.Prog.call_bind`, `Party.Prog.emitK_call`, `Party.Prog.emitK_outE_bind`,
  `Party.Prog.awaitK_recvO_bind`, `Party.Prog.emitK_callK`: the steps of the operations.
* `Party.Prog.Samples.emitK_bind`: a sampling program followed by `f` in the emit phase.
* `Party.Prog.loopMulti_stepEq`: a loop with calls is step-equivalent to the hand-written
  multi-call hybrid under the per-step hypotheses.
* `X3DHProg.simProt_stepEq_simLoop`: the program form of the X3DH simulator.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.MultiHybrid

open CatCrypt.Core

variable {σ σ' τ E O Q A : Type}

/-! ## Embeddings of multi-call hybrids -/

/-- The image of a decision of `π` from its state after the decision: a pending call is mapped
by `c`, an outer output by `b`. -/
def liftDec (b c : σ → σ') (q : σ × (Q ⊕ O)) : σ' × (Q ⊕ O) :=
  (match q.2 with
    | .inl _ => c q.1
    | .inr _ => b q.1, q.2)

/-- Unfolding lemma of `liftDec`: the decision is unchanged. -/
@[simp] theorem liftDec_snd (b c : σ → σ') (q : σ × (Q ⊕ O)) : (liftDec b c q).2 = q.2 := rfl

/-- Unfolding lemma of `liftDec` at a call. -/
@[simp] theorem liftDec_inl (b c : σ → σ') (s : σ) (g : Q) :
    liftDec (O := O) b c (s, .inl g) = (c s, .inl g) := rfl

/-- Unfolding lemma of `liftDec` at an output. -/
@[simp] theorem liftDec_inr (b c : σ → σ') (s : σ) (o : O) :
    liftDec (Q := Q) b c (s, .inr o) = (b s, .inr o) := rfl

/-- `π'` embeds `π` along `b` (states at activation boundaries) and `c` (states with a call
pending): the initial states and the fuels agree, and `start`, `resume` and `finish` of `π'` at
embedded states are the images of those of `π`. -/
structure Embeds (π : MultiHybrid σ E O Q A) (π' : MultiHybrid σ' E O Q A) (b c : σ → σ') :
    Prop where
  /-- The initial state of `π'` is the image of that of `π`. -/
  init : π'.init = b π.init
  /-- The fuels agree. -/
  fuel : π'.fuel = π.fuel
  /-- `start` commutes with the embedding. -/
  start : ∀ s e, π'.start (b s) e = SPComp.map (liftDec b c) (π.start s e)
  /-- `resume` commutes with the embedding. -/
  resume : ∀ s a, π'.resume (c s) a = SPComp.map (liftDec b c) (π.resume s a)
  /-- `finish` commutes with the embedding. -/
  finish : ∀ s a, π'.finish (c s) a = SPComp.map (fun q => (b q.1, q.2)) (π.finish s a)

namespace Embeds

variable {π : MultiHybrid σ E O Q A} {π' : MultiHybrid σ' E O Q A} {b c : σ → σ'}

/-- **The interaction with a subroutine commutes with an embedding.** -/
theorem drive (h : Embeds π π' b c) (X : Sys τ Q A) :
    ∀ n (q : σ × (Q ⊕ O)) t, π'.drive X n (liftDec b c q).1 q.2 t =
      SPComp.map (fun p => (b p.1, p.2)) (π.drive X n q.1 q.2 t) := by
  intro n
  induction n with
  | zero =>
    rintro ⟨s, g | o⟩ t
    · simp only [liftDec_inl, MultiHybrid.drive, h.finish, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
    · simp only [liftDec_inr, MultiHybrid.drive, SPComp.map_pure]
  | succ n ih =>
    rintro ⟨s, g | o⟩ t
    · simp only [liftDec_inl, MultiHybrid.drive, h.resume, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind, liftDec_snd, ih]
    · simp only [liftDec_inr, MultiHybrid.drive, SPComp.map_pure]

/-- **A step of the composite with a subroutine commutes with an embedding.** -/
theorem withSub_step (h : Embeds π π' b c) (X : Sys τ Q A) (s : σ) (t : τ) (e : E) :
    (π'.withSub X).step (b s, t) e =
      SPComp.map (fun p => ((b p.1.1, p.1.2), p.2)) ((π.withSub X).step (s, t) e) := by
  simp only [withSub, h.start, h.fuel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind,
    liftDec_snd, h.drive X]

/-- **An embedding gives step equivalence over every subroutine.** -/
theorem stepEq (h : Embeds π π' b c) (X : Sys τ Q A) :
    Sys.StepEq ⟨σ × τ, π.withSub X⟩ ⟨σ' × τ, π'.withSub X⟩ :=
  (Sys.StepMapOn.of_step (fun p => (b p.1, p.2)) (by simp [withSub, h.init])
    fun t e => (h.withSub_step X t.1 t.2 e).symm).stepEq

end Embeds

/-! ## The multi-call hybrid of a system on the sum interface -/

/-- `c` when it never fails, and the point mass at `d` otherwise. -/
noncomputable def guardNF {β : Type} (c : SPComp β) (d : β) : SPComp β := by
  classical exact if SPComp.NoFail c then c else SPComp.pure d

/-- `guardNF` never fails. -/
theorem guardNF_noFail {β : Type} (c : SPComp β) (d : β) : SPComp.NoFail (guardNF c d) := by
  unfold guardNF
  split
  · assumption
  · exact SPComp.pure_noFail _

/-- `guardNF` is the identity on computations that never fail. -/
theorem guardNF_of_noFail {β : Type} {c : SPComp β} (d : β) (h : SPComp.NoFail c) :
    guardNF c d = c := by
  unfold guardNF
  simp [h]

/-- A mapped computation that never fails. -/
theorem noFail_map {β γ : Type} {c : SPComp β} (f : β → γ) (h : SPComp.NoFail c) :
    SPComp.NoFail (SPComp.map f c) :=
  Assumptions.SPComp.bind_noFail h fun _ => SPComp.pure_noFail _

/-- The outer output of a final decision: an output ends the activation, a call fails. -/
noncomputable def toOut {β : Type} : β × (Q ⊕ O) → SPComp (β × O)
  | (t, .inr o) => SPComp.pure (t, o)
  | (_, .inl _) => SPComp.fail

/-- The multi-call hybrid of a system `X` on the sum interface, with fuel `n`: `start` is the
step on an outer event `inl e`, `resume` the step on an answer `inr a`, and `finish` the step on
an answer that must give an outer output. A step that may fail gives the default output. -/
noncomputable def ofSys [Inhabited O] (X : Sys τ (E ⊕ A) (Q ⊕ O)) (n : ℕ) :
    MultiHybrid τ E O Q A where
  init := X.init
  fuel := n
  start t e := guardNF (X.step t (.inl e)) (t, .inr default)
  resume t a := guardNF (X.step t (.inr a)) (t, .inr default)
  finish t a := guardNF (SPComp.bind (X.step t (.inr a)) toOut) (t, default)
  start_noFail _ _ := guardNF_noFail _ _
  resume_noFail _ _ := guardNF_noFail _ _
  finish_noFail _ _ := guardNF_noFail _ _

/-- **Embedding into the multi-call hybrid of a system.** When the steps of `X` at embedded
states are the images of `start`, `resume` and `finish` of `π`, `ofSys X π.fuel` embeds `π`. -/
theorem ofSys_embeds [Inhabited O] (π : MultiHybrid σ E O Q A) (X : Sys τ (E ⊕ A) (Q ⊕ O))
    (b c : σ → τ) (hinit : X.init = b π.init)
    (hs : ∀ s e, X.step (b s) (.inl e) = SPComp.map (liftDec b c) (π.start s e))
    (hr : ∀ s a, X.step (c s) (.inr a) = SPComp.map (liftDec b c) (π.resume s a))
    (hf : ∀ s a, X.step (c s) (.inr a) =
      SPComp.map (fun q => (b q.1, Sum.inr q.2)) (π.finish s a)) :
    Embeds π (ofSys X π.fuel) b c where
  init := hinit
  fuel := rfl
  start s e := by
    simp only [ofSys, hs]
    exact guardNF_of_noFail _ (noFail_map _ (π.start_noFail s e))
  resume s a := by
    simp only [ofSys, hr]
    exact guardNF_of_noFail _ (noFail_map _ (π.resume_noFail s a))
  finish s a := by
    have he : SPComp.bind (X.step (c s) (.inr a)) toOut =
        SPComp.map (fun q => (b q.1, q.2)) (π.finish s a) := by
      simp only [hf, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, toOut]
    simp only [ofSys, he]
    exact guardNF_of_noFail _ (noFail_map _ (π.finish_noFail s a))

end CatCrypt.Crypto.UCTransparent.MultiHybrid

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Crypto.UCTransparent

namespace Prog

variable {E O Q A α β σ ρ τ γ : Type}

/-! ## The operations of programs with calls -/

/-- Wait for the next activation by an outer event and return it; an answer fails. -/
def recvO : Prog (E ⊕ A) (Q ⊕ O) E :=
  .recv fun
    | .inl e => .ret e
    | .inr _ => .fail

/-- The continuation of a call: wait for the answer `a` and continue with `k a`; an outer event
fails. -/
def callK (k : A → Prog (E ⊕ A) (Q ⊕ O) α) : Prog (E ⊕ A) (Q ⊕ O) α :=
  .recv fun
    | .inr a => k a
    | .inl _ => .fail

/-- Wait for an answer and return it. -/
def recvA : Prog (E ⊕ A) (Q ⊕ O) A := callK .ret

/-- Call the subroutine with `q` and continue with its answer. -/
def call (q : Q) (k : A → Prog (E ⊕ A) (Q ⊕ O) α) : Prog (E ⊕ A) (Q ⊕ O) α :=
  .send (.inl q) (callK k)

/-- Call the subroutine with `q` and return its answer. -/
def callE (q : Q) : Prog (E ⊕ A) (Q ⊕ O) A := call q .ret

/-- Emit the outer output `o`. -/
def outE (o : O) : Prog (E ⊕ A) (Q ⊕ O) Unit := .send (.inr o) (.ret ())

/-- `call` commutes with `bind`. -/
theorem call_bind (q : Q) (k : A → Prog (E ⊕ A) (Q ⊕ O) α) (f : α → Prog (E ⊕ A) (Q ⊕ O) β) :
    ProgE.bind (call q k) f = call q fun a => ProgE.bind (k a) f := by
  simp only [call, callK, ProgE.bind]
  congr 1; congr 1; funext e
  cases e <;> rfl

/-- A call in the emit phase emits `inl q` and leaves the continuation of the call. -/
theorem emitK_call (s : Q ⊕ O → Prog (E ⊕ A) (Q ⊕ O) α → SPComp γ) (r : α → SPComp γ) (q : Q)
    (k : A → Prog (E ⊕ A) (Q ⊕ O) α) :
    emitK s r (call q k) = s (.inl q) (callK k) := rfl

/-- An outer output in the emit phase emits `inr o` and leaves the rest. -/
theorem emitK_outE_bind (s : Q ⊕ O → Prog (E ⊕ A) (Q ⊕ O) α → SPComp γ) (r : α → SPComp γ)
    (o : O) (f : Unit → Prog (E ⊕ A) (Q ⊕ O) α) :
    emitK s r (ProgE.bind (outE o) f) = s (.inr o) (f ()) := rfl

/-- An outer event in the await phase is fed to `recvO`. -/
theorem awaitK_recvO_bind (e : E) (s : Q ⊕ O → Prog (E ⊕ A) (Q ⊕ O) α → SPComp γ)
    (rA rE : α → SPComp γ) (f : E → Prog (E ⊕ A) (Q ⊕ O) α) :
    awaitK (.inl e) s rA rE (ProgE.bind (recvO (A := A)) f) = emitK s rE (f e) := rfl

/-- An answer in the await phase is fed to the continuation of the call. -/
theorem emitK_callK (a : A) (s : Q ⊕ O → Prog (E ⊕ A) (Q ⊕ O) α → SPComp γ)
    (rA rE : α → SPComp γ) (k : A → Prog (E ⊕ A) (Q ⊕ O) α) :
    awaitK (.inr a) s rA rE (callK (E := E) k) = emitK s rE (k a) := rfl

/-! ## Sampling programs -/

/-- `p` samples `c`: in the emit phase it performs the samples of `c` and returns, without a
`recv` or a `send`. -/
def Samples (p : Prog E O α) (c : SPComp α) : Prop :=
  ∀ (γ : Type) (s : O → Prog E O α → SPComp γ) (r : α → SPComp γ), emitK s r p = SPComp.bind c r

namespace Samples

/-- A return samples the point mass. -/
theorem ret (a : α) : Samples (.ret a : Prog E O α) (SPComp.pure a) := fun _ _ _ => by
  simp only [emitK_ret, SPComp.pure_bind]

/-- A sampling program followed by `f` in the emit phase. -/
theorem emitK_bind {p : Prog E O α} {c : SPComp α} (h : Samples p c)
    (s : O → Prog E O β → SPComp γ) (r : β → SPComp γ) (f : α → Prog E O β) :
    emitK s r (ProgE.bind p f) = SPComp.bind c fun a => emitK s r (f a) := by
  rw [Prog.emitK_bind]
  exact h _ _ _

/-- Sampling programs compose by `bind`. -/
theorem bind {p : Prog E O α} {c : SPComp α} {f : α → Prog E O β} {d : α → SPComp β}
    (hp : Samples p c) (hf : ∀ a, Samples (f a) (d a)) :
    Samples (ProgE.bind p f) (SPComp.bind c d) :=
  fun _ s r => by
    rw [hp.emitK_bind, SPComp.bind_assoc]
    congr 1; funext a
    exact hf a _ _ _

/-- A sampling program followed by a return samples the mapped computation. -/
theorem map {p : Prog E O α} {c : SPComp α} (hp : Samples p c) (f : α → β) :
    Samples (ProgE.bind p fun a => .ret (f a)) (SPComp.map f c) :=
  hp.bind fun a => ret (f a)

/-- Sampling from a countable type. -/
theorem sample [Countable β] {μ : SPComp β} {k : β → Prog E O α} {d : β → SPComp α}
    (hk : ∀ b, Samples (k b) (d b)) : Samples (Prog.sample μ k) (SPComp.bind μ d) :=
  fun _ s r => by
    rw [emitK_sample, SPComp.bind_assoc]
    congr 1; funext b
    exact hk b _ _ _

/-- Sampling from a countable type followed by a return samples the mapped computation. -/
theorem sample_map [Countable β] (μ : SPComp β) (f : β → α) :
    Samples (Prog.sample μ fun b => (.ret (f b) : Prog E O α)) (SPComp.map f μ) :=
  sample fun b => ret (f b)

/-- A conditional of sampling programs samples the conditional. -/
theorem ite {P : Prop} [Decidable P] {p q : Prog E O α} {c d : SPComp α} (hp : Samples p c)
    (hq : Samples q d) : Samples (if P then p else q) (if P then c else d) := by
  by_cases hP : P
  · simpa only [hP, ↓reduceIte] using hp
  · simpa only [hP, ↓reduceIte] using hq

end Samples

/-! ## Loops with calls -/

/-- The multi-call hybrid of the loop of `body` from `s₀`, with fuel `n`. -/
noncomputable def loopMulti [Inhabited O] (body : σ → Prog (E ⊕ A) (Q ⊕ O) σ) (s₀ : σ)
    (n : ℕ) : MultiHybrid (Prog (E ⊕ A) (Q ⊕ O) σ) E O Q A :=
  MultiHybrid.ofSys (loopSys body s₀) n

/-- **Loops with calls.** Let `π` be a multi-call hybrid with states `ρ`, `proj` a map to the
states of the loop, and `k s` the continuation of the call pending at `s`. When the activation of
`body (proj s)` on an outer event is the image of `π.start s`, and the continuation `k s` on an
answer is the image of `π.resume s` and of `π.finish s`, the loop of `body` from `proj π.init`
running with any subroutine is step-equivalent to `π` running with it. -/
theorem loopMulti_stepEq [Inhabited O] (π : MultiHybrid ρ E O Q A)
    (body : σ → Prog (E ⊕ A) (Q ⊕ O) σ) (proj : ρ → σ)
    (k : ρ → A → Prog (E ⊕ A) (Q ⊕ O) σ)
    (hs : ∀ s e, act (body (proj s)) (.inl e) =
      SPComp.map (MultiHybrid.liftDec (fun s => .ret (proj s)) fun s => callK (k s))
        (π.start s e))
    (hr : ∀ s a, act (callK (k s)) (.inr a) =
      SPComp.map (MultiHybrid.liftDec (fun s => .ret (proj s)) fun s => callK (k s))
        (π.resume s a))
    (hf : ∀ s a, act (callK (k s)) (.inr a) =
      SPComp.map (fun q => (.ret (proj q.1), Sum.inr q.2)) (π.finish s a))
    (X : Sys τ Q A) :
    Sys.StepEq ⟨ρ × τ, π.withSub X⟩
      ⟨Prog (E ⊕ A) (Q ⊕ O) σ × τ, (loopMulti body (proj π.init) π.fuel).withSub X⟩ :=
  (MultiHybrid.ofSys_embeds π (loopSys body (proj π.init)) (fun s => .ret (proj s))
    (fun s => callK (k s)) rfl hs hr hf).stepEq X

end Prog

/-! ## Example: the X3DH simulator as a program -/

namespace X3DHProg

open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract Prog

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- Programs of the X3DH simulator: outer interface `(OEv W, OOut S W K)`, calls to `F_AKE`. -/
abbrev P (S W K : Type) (α : Type) := Prog (OEv W ⊕ FOut K) (FEv K ⊕ OOut S W K) α

/-- The default outer output of the simulator. -/
instance : Inhabited (OOut S W K) := ⟨.inr .ack⟩

/-- `ltStep` as a program. -/
noncomputable def ltP (s : RSt S W K) (pid : PartyId) : P S W K ((S × S) × RSt S W K) :=
  match s.lt pid with
  | some l => .ret (l, s)
  | none => Prog.sample (SPComp.sample (S × S)) fun l =>
      .ret (l, { s with lt := Function.update s.lt pid (some l) })

/-- `roStep` as a program. -/
noncomputable def roP {D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    P S W K (K × List (D × K)) :=
  match tb.lookup x with
  | some v => .ret (v, tb)
  | none => Prog.sample (SPComp.sample K) fun v => .ret (v, (x, v) :: tb)

/-- `deliver` as a program. -/
noncomputable def deliverP (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst)
    (r : Rec K) (ip : Inp W) : P S W K (SimSt S W K × Dec S W K) :=
  if Exposed rs.st x r then
    ProgE.bind (roP rs.ro ip) fun p => .ret ((keyed rs x r p.1 p.2, Function.update inp x (some ip),
      .out .ack), .inl (.inr (.newKey x.1 x.2 p.1)))
  else
    .ret ((keyed rs x r default rs.ro, Function.update inp x (some ip), .out .ack),
      .inl (.inr (if (inp (x.1, r.peer)).all (· = ip) then .newKey x.1 x.2 default
        else .newKeyUnlinked x.1 x.2 default)))

/-- `simComplete` as a program. -/
noncomputable def simCompleteP (s : SimSt S W K) (x : Inst) :
    P S W K (SimSt S W K × Dec S W K) :=
  match s.1.st.recs x, s.1.eph x with
  | some r, some ek =>
    match opkOf s.1 x.1 r.peer with
    | some opk =>
      if r.role = .initiator ∧ r.key.isNone then
        ProgE.bind (ltP s.1 x.2) fun la => ProgE.bind (ltP la.2 r.peer) fun lb =>
          deliverP lb.2 s.2.1 x r
            (aliceInp G x.1 x.2 r.peer la.1.1 ek (G.pub lb.1.1) (G.pub lb.1.2) (G.pub opk))
      else .ret ((s.1, s.2.1, .fwd), .inr (.inr .ack))
    | none => .ret ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => .ret ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- `simSend` as a program. -/
noncomputable def simSendP (s : SimSt S W K) (x : Inst) (e : W) :
    P S W K (SimSt S W K × Dec S W K) :=
  match s.1.st.recs x, s.1.eph x with
  | some r, some opk =>
    if r.role = .responder ∧ r.key.isNone then
      ProgE.bind (ltP s.1 x.2) fun lb => ProgE.bind (ltP lb.2 r.peer) fun la =>
        deliverP la.2 s.2.1 x r (bobInp G x.1 r.peer x.2 (G.pub la.1.1) e lb.1.1 lb.1.2 opk)
    else .ret ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => .ret ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- `simCorrupt` as a program. -/
noncomputable def simCorruptP (s : SimSt S W K) (pid : PartyId) :
    P S W K (SimSt S W K × Dec S W K) :=
  if Named s.1.st pid then .ret ((s.1, s.2.1, .fwd), .inr (.inr (.secret none))) else
    ProgE.bind (ltP s.1 pid) fun l =>
      .ret (({ l.2 with st := corruptStep l.2.st pid }, s.2.1, .out (.secret (some l.1))),
        .inl (.inr (.corrupt pid)))

/-- `simStart` as a program. -/
noncomputable def simStartP (s : SimSt S W K) : OEv W → P S W K (SimSt S W K × Dec S W K)
  | .inl (.newSession sid pid peer role) =>
    if (s.1.st.recs (sid, pid)).isNone then
      Prog.sample (SPComp.sample S) fun y =>
        .ret (({ s.1 with st := addSession s.1.st (sid, pid) peer role,
                          eph := Function.update s.1.eph (sid, pid) (some y) }, s.2.1, .fwd),
          .inl (.inl (.newSession sid pid peer role)))
    else .ret ((s.1, s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
  | .inl (.getKey sid pid) => .ret ((s.1, s.2.1, .fwd), .inl (.inl (.getKey sid pid)))
  | .inr .idle => .ret ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | .inr .poll => .ret (({ s.1 with st := (pollStep s.1.st).1 }, s.2.1, .fwd),
      .inr (.inr (.notice (pollStep s.1.st).2)))
  | .inr (.pub pid) => ProgE.bind (ltP s.1 pid) fun l =>
      .ret ((l.2, s.2.1, .fwd), .inr (.inr (.pub (G.pub l.1.1) (G.pub l.1.2))))
  | .inr (.ephPub sid pid) =>
    .ret ((s.1, s.2.1, .fwd), .inr (.inr (.eph (ephPubOf G s.1 (sid, pid)))))
  | .inr (.corrupt pid) => simCorruptP s pid
  | .inr (.complete sid pid) => simCompleteP G s (sid, pid)
  | .inr (.send sid pid e) => simSendP G s (sid, pid) e
  | .inr (.kdf x) => ProgE.bind (roP s.1.ro x) fun p =>
      .ret (({ s.1 with ro := p.2 }, s.2.1, .fwd), .inr (.inr (.hash p.1)))

/-- The continuation of the call pending at `s`: output the answer of `F_AKE` as `simOut` does
in the phase of `s`, and return. -/
def simK (s : SimSt S W K) (a : FOut K) : P S W K (SimSt S W K) :=
  ProgE.bind (outE (simOut s.2.2 a)) fun _ => .ret (s.1, s.2.1, .fwd)

/-- The end of an activation after the decision of `simStartP`: a call to `F_AKE` with the
continuation `simK`, or the outer output. -/
def simDecide (q : SimSt S W K × Dec S W K) : P S W K (SimSt S W K) :=
  match q.2 with
  | .inl f => call f (simK q.1)
  | .inr o => ProgE.bind (outE o) fun _ => .ret q.1

/-- **The X3DH simulator as a program**: one iteration per activation. -/
noncomputable def simBody (s : SimSt S W K) : P S W K (SimSt S W K) :=
  ProgE.bind recvO fun e => ProgE.bind (simStartP G s e) simDecide

/-- The loop of `simBody` as a multi-call hybrid over `F_AKE`, with fuel `0`. -/
noncomputable def simLoop :
    MultiHybrid (P S W K (SimSt S W K)) (OEv W) (OOut S W K) (FEv K) (FOut K) :=
  loopMulti (simBody G) (rInit, fun _ => none, .fwd) 0

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `ltP` samples `ltStep`. -/
theorem ltP_samples (s : RSt S W K) (pid : PartyId) :
    Samples (ltP s pid : P S W K _) (ltStep s pid) := by
  unfold ltP ltStep
  cases s.lt pid with
  | some l => exact Samples.ret _
  | none => exact Samples.sample_map _ _

omit [Field S] [Fintype S] [DecidableEq W] [Inhabited K] in
/-- `roP` samples `roStep`. -/
theorem roP_samples {D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    Samples (roP tb x : P S W K _) (roStep tb x) := by
  unfold roP roStep
  cases tb.lookup x with
  | some v => exact Samples.ret _
  | none => exact Samples.sample_map _ _

omit [Field S] [Fintype S] in
/-- `deliverP` samples `deliver`. -/
theorem deliverP_samples (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst)
    (r : Rec K) (ip : Inp W) : Samples (deliverP rs inp x r ip) (deliver rs inp x r ip) := by
  unfold deliverP deliver
  exact Samples.ite ((roP_samples _ _).map _) (Samples.ret _)

/-- `simCompleteP` samples `simComplete`. -/
theorem simCompleteP_samples (s : SimSt S W K) (x : Inst) :
    Samples (simCompleteP G s x) (simComplete G s x) := by
  unfold simCompleteP simComplete
  cases s.1.st.recs x with
  | none => exact Samples.ret _
  | some r =>
    cases s.1.eph x with
    | none => exact Samples.ret _
    | some ek =>
      dsimp only
      cases opkOf s.1 x.1 r.peer with
      | none => exact Samples.ret _
      | some opk =>
        exact Samples.ite ((ltP_samples _ _).bind fun _ => (ltP_samples _ _).bind fun _ =>
          deliverP_samples _ _ _ _ _) (Samples.ret _)

/-- `simSendP` samples `simSend`. -/
theorem simSendP_samples (s : SimSt S W K) (x : Inst) (e : W) :
    Samples (simSendP G s x e) (simSend G s x e) := by
  unfold simSendP simSend
  cases s.1.st.recs x with
  | none => exact Samples.ret _
  | some r =>
    cases s.1.eph x with
    | none => exact Samples.ret _
    | some opk =>
      exact Samples.ite ((ltP_samples _ _).bind fun _ => (ltP_samples _ _).bind fun _ =>
        deliverP_samples _ _ _ _ _) (Samples.ret _)

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `simCorruptP` samples `simCorrupt`. -/
theorem simCorruptP_samples (s : SimSt S W K) (pid : PartyId) :
    Samples (simCorruptP s pid) (simCorrupt s pid) := by
  unfold simCorruptP simCorrupt
  exact Samples.ite (Samples.ret _) ((ltP_samples _ _).map _)

/-- **`simStartP` samples `simStart`.** -/
theorem simStartP_samples (s : SimSt S W K) (e : OEv W) :
    Samples (simStartP G s e) (simStart G s e) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)
  · exact Samples.ite (Samples.sample_map (SPComp.sample S) _) (Samples.ret _)
  · exact Samples.ret _
  · exact Samples.ret _
  · exact Samples.ret _
  · exact (ltP_samples _ _).map _
  · exact Samples.ret _
  · exact simCorruptP_samples _ _
  · exact simCompleteP_samples G _ _
  · exact simSendP_samples G _ _ _
  · exact (roP_samples _ _).map _

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The end of an activation in the emit phase is the embedded decision. -/
theorem emitK_simDecide (q : SimSt S W K × Dec S W K) :
    emitK (fun o p => SPComp.pure (p, o)) (fun _ => SPComp.fail) (simDecide q) =
      SPComp.pure (MultiHybrid.liftDec (fun s => .ret s) (fun s => callK (simK s)) q) := by
  rcases q with ⟨s, f | o⟩ <;> rfl

/-- **The X3DH simulator and its program form are step-equivalent** over every subroutine, in
particular over `F_AKE`. -/
theorem simProt_stepEq_simLoop {τ : Type} (X : Sys τ (FEv K) (FOut K)) :
    Sys.StepEq ⟨SimSt S W K × τ, (simProt G).withSub X⟩
      ⟨P S W K (SimSt S W K) × τ, (simLoop G).withSub X⟩ := by
  refine loopMulti_stepEq (simProt G) (simBody G) id simK (fun s e => ?_) (fun s a => ?_)
    (fun s a => ?_) X
  · change emitK (fun o p => SPComp.pure (p, o)) (fun _ => SPComp.fail)
      (ProgE.bind (simStartP G s e) simDecide) = _
    rw [(simStartP_samples G s e).emitK_bind]
    simp only [emitK_simDecide, SPComp.map]
    rfl
  · simp only [simProt, SPComp.map_pure]
    rfl
  · simp only [simProt, SPComp.map_pure]
    rfl

end X3DHProg

end CatCrypt.Crypto.Party
