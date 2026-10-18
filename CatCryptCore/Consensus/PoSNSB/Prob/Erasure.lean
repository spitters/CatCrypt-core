/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob.Uniform

/-!
# PoS-NSB: the execution of a uniform protocol without the hash function in its state

The global state of an execution (`GS`) has local states whose tree type depends on the hash
function, so its type depends on the random oracle. For a protocol with uniform tree types
(`Protocol.ofUniform`), the trees of party `p` have the type `(U L p).T` for every oracle. The
hash-free global state `XSt` stores these trees directly, and `emb f` reinterprets a hash-free
state as a global state over the oracle `f`, attaching the tree type `(U L p).at` of every
party; the tree types agree by `rfl`, so no cast is involved.

The hash-free steps `XSt.rcv`, `XSt.bake` and `XSt.phase` take the extension and the
chain-selection rule of the trees, the hash function of blocks and the adversary functions as
arguments; the oracle `f` enters the hash-free phase `xPhase f` only through the
chain-selection rule `(U L p).bestChain`, the hash of the parent block in honest baking and the
adversary functions of the execution.

## Main definitions

* `XSt` — the hash-free global state
* `XSt.rcv`, `XSt.bake`, `XSt.phase` — the hash-free steps
* `emb`, `x₀`, `xPhase` — the embedding into the execution over `f`, the hash-free initial
  state and the hash-free phase of a uniform protocol
* `XSt.HistInv` — the history invariant on hash-free states

## Main results

* `N0_eq_emb`, `sPhase_emb` — the initial state and the phases commute with `emb f`
* `sTrace_eq_emb` — the trace of the execution over `f` is the image under `emb f` of the
  hash-free trace
* `histInv_emb_iff` — `HistInv` of `emb f x` is `XSt.HistInv` of `x`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution
open CatCrypt.Crypto.Signatures

/-! ## Hash-free global states -/

section XSt

variable {Tx Hash : Type} {np : ℕ}

/-- The hash-free global state: the fields of `GlobalState`, with the tree `trees p : T p` of
every party in place of its local state. -/
structure XSt (Tx Hash : Type) (np : ℕ) (T : Fin np → Type) (AdvState : Type) where
  /-- The current slot. -/
  t_now : Slot
  /-- The messages that still have to be delivered. -/
  msg_buff : MessagePool Tx Hash (Fin np)
  /-- The tree of each party. -/
  trees : (p : Fin np) → Option (T p)
  /-- All messages broadcast so far. -/
  history : History Tx Hash (Fin np)
  /-- The state of the adversary. -/
  adv_state : AdvState
  /-- The execution order of the parties in the next round. -/
  exec_order : List (Fin np)
  /-- How far the current round has progressed. -/
  progress : Progress

namespace XSt

variable {T : Fin np → Type} {AdvState : Type}

/-- Honest broadcast of a message (`flood_msg`). -/
def flood (m : Message Tx Hash (Fin np)) (x : XSt Tx Hash np T AdvState) :
    XSt Tx Hash np T AdvState :=
  { x with msg_buff := x.exec_order.map (fun r => ⟨m, r, 1⟩) ++ x.msg_buff
           history := m :: x.history }

/-- Adversarial broadcast of a message (`flood_msg_adv`). -/
def floodAdv (m : Message Tx Hash (Fin np)) (φ : DelayMap (Fin np))
    (x : XSt Tx Hash np T AdvState) : XSt Tx Hash np T AdvState :=
  { x with msg_buff := x.exec_order.map (fun r => ⟨m, r, (φ r).1⟩) ++ x.msg_buff
           history := m :: x.history }

/-- Honest broadcast of several messages (`flood_msgs`). -/
def floods (msgs : Messages Tx Hash (Fin np)) (x : XSt Tx Hash np T AdvState) :
    XSt Tx Hash np T AdvState :=
  msgs.foldr flood x

/-- Adversarial broadcast of several messages (`flood_msgs_adv`). -/
def floodsAdv (msgs : List (Message Tx Hash (Fin np) × DelayMap (Fin np)))
    (x : XSt Tx Hash np T AdvState) : XSt Tx Hash np T AdvState :=
  msgs.foldr (fun mφ => floodAdv mφ.1 mφ.2) x

/-- Fetch the messages for `r` whose delay has run out (`fetch_msgs`). -/
def fetch (r : Fin np) (x : XSt Tx Hash np T AdvState) :
    Messages Tx Hash (Fin np) × XSt Tx Hash np T AdvState :=
  ((x.msg_buff.filter (fun mt => mt.cd == 0 && decide (mt.rcv = r))).map MessageTuple.msg,
    { x with msg_buff := x.msg_buff.filter (fun mt => !(mt.cd == 0 && decide (mt.rcv = r))) })

/-- Replace the tree of `p`. -/
def updTree (p : Fin np) (t : T p) (x : XSt Tx Hash np T AdvState) : XSt Tx Hash np T AdvState :=
  { x with trees := Function.update x.trees p (some t) }

/-- Decrease all delays by one round and advance the slot (`inc_round ∘ round_tick`). -/
def tick (x : XSt Tx Hash np T AdvState) : XSt Tx Hash np T AdvState :=
  { x with msg_buff := x.msg_buff.map (fun m => { m with cd := m.cd - 1 })
           t_now := x.t_now + 1 }

variable [Corruption (Fin np)]

/-- The hash-free receiving step of party `p` (`party_rcv_step_world`), for the tree extension
`ext` and the adversary function `adv`. -/
def rcv (ext : (p : Fin np) → T p → Block Tx Hash (Fin np) → T p)
    (adv : Messages Tx Hash (Fin np) → Slot → History Tx Hash (Fin np) →
      MessagePool Tx Hash (Fin np) →
        State AdvState (List (Message Tx Hash (Fin np) × DelayMap (Fin np))))
    (p : Fin np) (x : XSt Tx Hash np T AdvState) : XSt Tx Hash np T AdvState :=
  match x.trees p with
  | some t =>
    let r := x.fetch p
    if !is_corrupt p then
      r.2.updTree p (r.1.foldr (fun m t => ext p t (get_block m)) t)
    else
      let a := adv r.1 r.2.t_now r.2.history r.2.msg_buff r.2.adv_state
      { r.2.floodsAdv a.1 with adv_state := a.2 }
  | none => x

/-- The hash-free baking step of party `p` (`party_bake_step_world`), for the lottery `win`,
the tree extension `ext`, the chain-selection rule `best`, the block hash `h`, the genesis
block `GB`, the transaction selection `txSel` and the adversary function `adv`. -/
def bake (win : Fin np → Slot → Bool)
    (ext : (p : Fin np) → T p → Block Tx Hash (Fin np) → T p)
    (best : (p : Fin np) → Slot → T p → Chain Tx Hash (Fin np))
    (h : Block Tx Hash (Fin np) → Hash) (GB : Block Tx Hash (Fin np))
    (txSel : Slot → Fin np → Tx)
    (adv : Slot → History Tx Hash (Fin np) → MessagePool Tx Hash (Fin np) →
      State AdvState (List (Message Tx Hash (Fin np) × DelayMap (Fin np))))
    (p : Fin np) (x : XSt Tx Hash np T AdvState) : XSt Tx Hash np T AdvState :=
  match x.trees p with
  | some t =>
    if !is_corrupt p then
      if win p x.t_now then
        let b : Block Tx Hash (Fin np) :=
          ⟨x.t_now, txSel x.t_now p, h ((best p (x.t_now - 1) t).headD GB), p⟩
        (x.updTree p (ext p t b)).floods [Message.BlockMsg b]
      else (x.updTree p t).floods []
    else
      let a := adv x.t_now x.history x.msg_buff x.adv_state
      { x.floodsAdv a.1 with adv_state := a.2 }
  | none => x

/-- One hash-free phase (`phaseStep`) for the receiving steps `rcvS` and the baking steps
`bakeS`. -/
def phase (rcvS bakeS : Fin np → XSt Tx Hash np T AdvState → XSt Tx Hash np T AdvState)
    (x : XSt Tx Hash np T AdvState) : XSt Tx Hash np T AdvState :=
  match x.progress with
  | .Ready => { x.exec_order.foldr rcvS x with progress := .Delivered }
  | .Delivered => { x.exec_order.foldr bakeS x with progress := .Baked }
  | .Baked => { x.tick with progress := .Ready }

end XSt

end XSt

/-! ## The embedding into the execution of a uniform protocol -/

section Embed

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [Sch.Deterministic]
  (IP : List (Fin np)) (h0 : Fin np) (GB : Block Tx Hash (Fin np))
  (U : (L : Fin n → Option (Fin np)) → Fin np →
    @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
  (txSel : Slot → Fin np → Tx) (L : Fin n → Option (Fin np)) (ks : Fin np → PK × SK)
  (A : Adversary Tx Hash np n Hz PK Sig)

/-- The hash-free global states of the uniform protocol for the leader string `L` and the
adversary `A`. -/
abbrev XS := XSt Tx Hash np
  (fun p => @UTreeType.T Tx Hash (Fin np) (leaderParams IP h0 L) GB (U L p)) A.AdvState

/-- The seed with leader string `L`, oracle `f` and key pairs `ks`. -/
abbrev uSeed (f : BlockDom Tx Hash np Hz → Hash) : Seed Tx Hash np n Hz PK SK := ⟨L, f, ks⟩

/-- The global state over the oracle `f` of a hash-free state: party `p` with tree `t` has the
local state with tree type `(U L p).at` over the block hash `b ↦ f (encB Hz b)`, key `p` and
tree `t`. -/
def emb (f : BlockDom Tx Hash np Hz → Hash) (x : XS IP h0 GB U L A) :
    GS (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f) A :=
  letI := leaderParams IP h0 L
  letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
  { t_now := x.t_now
    msg_buff := x.msg_buff
    state_map := fun p => (x.trees p).map fun t =>
      ⟨(Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel).trees L f p, p, t⟩
    history := x.history
    adv_state := x.adv_state
    exec_order := x.exec_order
    progress := x.progress }

/-- The hash-free initial state: slot `1`, every initial party with the initial tree. -/
def x₀ : XS IP h0 GB U L A :=
  letI := leaderParams IP h0 L
  { t_now := 1
    msg_buff := []
    trees := fun p => if p ∈ IP then some (U L p).tree0 else none
    history := []
    adv_state := A.st0
    exec_order := IP
    progress := .Ready }

/-- The hash-free receiving step of party `p` of the execution over `f`. -/
def xRcv (ideal : Bool) (f : BlockDom Tx Hash np Hz → Hash) :
    Fin np → XS IP h0 GB U L A → XS IP h0 GB U L A :=
  letI := leaderParams IP h0 L
  XSt.rcv (fun p => (U L p).extendTree)
    (mkExec Sch ideal (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f)
      A).AdversarialRcv

/-- The hash-free baking step of party `p` of the execution over `f`. -/
def xBake (ideal : Bool) (f : BlockDom Tx Hash np Hz → Hash) :
    Fin np → XS IP h0 GB U L A → XS IP h0 GB U L A :=
  letI := leaderParams IP h0 L
  XSt.bake (leaderParams IP h0 L).Winner (fun p => (U L p).extendTree)
    (fun p => (U L p).bestChain fun b => f (encB Hz b)) (fun b => f (encB Hz b)) GB txSel
    (mkExec Sch ideal (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f)
      A).AdversarialBake

/-- One hash-free phase of the real (`ideal = false`) or the ideal execution over `f`. -/
def xPhase (ideal : Bool) (f : BlockDom Tx Hash np Hz → Hash) :
    XS IP h0 GB U L A → XS IP h0 GB U L A :=
  XSt.phase (xRcv Sch IP h0 GB U txSel L ks A ideal f) (xBake Sch IP h0 GB U txSel L ks A ideal f)

theorem emb_floodsAdv (f : BlockDom Tx Hash np Hz → Hash)
    (msgs : List (Message Tx Hash (Fin np) × DelayMap (Fin np))) (x : XS IP h0 GB U L A) :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    flood_msgs_adv msgs (emb IP h0 GB U txSel L ks A f x) =
      emb IP h0 GB U txSel L ks A f (x.floodsAdv msgs) := by
  let _ := leaderParams IP h0 L
  let _ : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
  induction msgs with
  | nil => rfl
  | cons m ms ih =>
    exact (congrArg (flood_msg_adv m.1 m.2) ih).trans rfl

theorem emb_floods (f : BlockDom Tx Hash np Hz → Hash) (msgs : Messages Tx Hash (Fin np))
    (x : XS IP h0 GB U L A) :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    flood_msgs msgs (emb IP h0 GB U txSel L ks A f x) =
      emb IP h0 GB U txSel L ks A f (x.floods msgs) := by
  let _ := leaderParams IP h0 L
  let _ : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
  induction msgs with
  | nil => rfl
  | cons m ms ih =>
    exact (congrArg (flood_msg m) ih).trans rfl

theorem emb_updTree (f : BlockDom Tx Hash np Hz → Hash) (p : Fin np)
    (t : @UTreeType.T Tx Hash (Fin np) (leaderParams IP h0 L) GB (U L p))
    (x : XS IP h0 GB U L A) :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    upd_local p ⟨(Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel).trees L f p, p, t⟩
        (emb IP h0 GB U txSel L ks A f x) =
      emb IP h0 GB U txSel L ks A f (x.updTree p t) := by
  simp only [upd_local, emb, XSt.updTree, GlobalState.mk.injEq, and_true, true_and]
  funext q
  by_cases hq : q = p
  · subst hq; simp only [Function.update_self]; rfl
  · simp [Function.update_of_ne hq]

theorem foldr_process_msg (f : BlockDom Tx Hash np Hz → Hash) (p : Fin np)
    (ms : Messages Tx Hash (Fin np))
    (t : @UTreeType.T Tx Hash (Fin np) (leaderParams IP h0 L) GB (U L p)) :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    ms.foldr process_msg
        (⟨(Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel).trees L f p, p, t⟩ :
          LocalState Tx Hash (Fin np)) =
      ⟨(Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel).trees L f p, p,
        ms.foldr (fun m t => (U L p).extendTree t (get_block m)) t⟩ := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rw [List.foldr_cons, ih]
    cases m
    rfl

section Fields

variable (f : BlockDom Tx Hash np Hz → Hash) (x : XS IP h0 GB U L A)

theorem emb_t_now :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    (emb IP h0 GB U txSel L ks A f x).t_now = x.t_now := rfl

theorem emb_history :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    (emb IP h0 GB U txSel L ks A f x).history = x.history := rfl

theorem emb_msg_buff :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    (emb IP h0 GB U txSel L ks A f x).msg_buff = x.msg_buff := rfl

theorem emb_adv_state :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    (emb IP h0 GB U txSel L ks A f x).adv_state = x.adv_state := rfl

theorem emb_progress :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    (emb IP h0 GB U txSel L ks A f x).progress = x.progress := rfl

theorem emb_fetch (p : Fin np) :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    fetch_msgs p (emb IP h0 GB U txSel L ks A f x) =
      ((x.fetch p).1, emb IP h0 GB U txSel L ks A f (x.fetch p).2) := rfl

end Fields

/-- A receiving step of the execution over `f` from an embedded state is the embedding of the
hash-free receiving step. -/
theorem sRcv_emb (ideal : Bool) (f : BlockDom Tx Hash np Hz → Hash) (p : Fin np)
    (x : XS IP h0 GB U L A) :
    sRcv Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f) A ideal p
        (emb IP h0 GB U txSel L ks A f x) =
      emb IP h0 GB U txSel L ks A f (xRcv Sch IP h0 GB U txSel L ks A ideal f p x) := by
  let _ := leaderParams IP h0 L
  let _ : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
  unfold sRcv xRcv XSt.rcv party_rcv_step_world
  rw [show (emb IP h0 GB U txSel L ks A f x).state_map p = (x.trees p).map fun t =>
    ⟨(Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel).trees L f p, p, t⟩ from rfl]
  rw [emb_fetch]
  cases hx : x.trees p with
  | none => rfl
  | some t =>
    simp only [Option.map_some]
    cases is_corrupt p
    · simp only [Bool.not_false, if_true, honest_rcv, process_msgs, State.modify]
      exact (congrArg (fun l => upd_local p l _)
        (foldr_process_msg IP h0 GB U txSel L f p _ t)).trans
        (emb_updTree IP h0 GB U txSel L ks A f p _ _)
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      rw [emb_t_now, emb_history, emb_msg_buff, emb_adv_state, emb_floodsAdv]
      rfl

/-- A baking step of the execution over `f` from an embedded state is the embedding of the
hash-free baking step. -/
theorem sBake_emb (ideal : Bool) (f : BlockDom Tx Hash np Hz → Hash) (p : Fin np)
    (x : XS IP h0 GB U L A) :
    sBake Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f) A ideal p
        (emb IP h0 GB U txSel L ks A f x) =
      emb IP h0 GB U txSel L ks A f (xBake Sch IP h0 GB U txSel L ks A ideal f p x) := by
  let _ := leaderParams IP h0 L
  let _ : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
  unfold sBake xBake XSt.bake party_bake_step_world
  rw [show (emb IP h0 GB U txSel L ks A f x).state_map p = (x.trees p).map fun t =>
    ⟨(Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel).trees L f p, p, t⟩ from rfl]
  cases hx : x.trees p with
  | none => rfl
  | some t =>
    simp only [Option.map_some]
    rw [emb_t_now]
    cases is_corrupt p
    · simp only [Bool.not_false, if_true]
      have hb := honest_bake_eq x.t_now (txSel x.t_now p)
        (⟨(Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel).trees L f p, p, t⟩ :
          LocalState Tx Hash (Fin np))
      by_cases hw : Winner p x.t_now = true
      · have e := hb.trans (if_pos hw)
        simp only [if_pos hw]
        refine (congrArg₂ (fun ms l => flood_msgs ms (upd_local p l
          (emb IP h0 GB U txSel L ks A f x))) (congrArg Prod.fst e) (congrArg Prod.snd e)).trans ?_
        exact (congrArg (flood_msgs _) (emb_updTree IP h0 GB U txSel L ks A f p _ x)).trans
          (emb_floods IP h0 GB U txSel L ks A f _ _)
      · have e := hb.trans (if_neg hw)
        simp only [if_neg hw]
        refine (congrArg₂ (fun ms l => flood_msgs ms (upd_local p l
          (emb IP h0 GB U txSel L ks A f x))) (congrArg Prod.fst e) (congrArg Prod.snd e)).trans ?_
        exact (congrArg (flood_msgs _) (emb_updTree IP h0 GB U txSel L ks A f p t x)).trans
          (emb_floods IP h0 GB U txSel L ks A f _ _)
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      rw [emb_history, emb_msg_buff, emb_adv_state, emb_floodsAdv]
      rfl

theorem foldr_emb {f : BlockDom Tx Hash np Hz → Hash}
    {g : Fin np → GS (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f) A →
      GS (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f) A}
    {g' : Fin np → XS IP h0 GB U L A → XS IP h0 GB U L A}
    (hg : ∀ p x, g p (emb IP h0 GB U txSel L ks A f x) = emb IP h0 GB U txSel L ks A f (g' p x))
    (l : List (Fin np)) (x : XS IP h0 GB U L A) :
    l.foldr g (emb IP h0 GB U txSel L ks A f x) = emb IP h0 GB U txSel L ks A f (l.foldr g' x) := by
  induction l with
  | nil => rfl
  | cons p ps ih => rw [List.foldr_cons, List.foldr_cons, ih, hg]

/-- **The phase equation.** A phase of the execution over `f` from an embedded state is the
embedding of the hash-free phase. -/
theorem sPhase_emb (ideal : Bool) (f : BlockDom Tx Hash np Hz → Hash) (x : XS IP h0 GB U L A) :
    sPhase Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f) A ideal
        (emb IP h0 GB U txSel L ks A f x) =
      emb IP h0 GB U txSel L ks A f (xPhase Sch IP h0 GB U txSel L ks A ideal f x) := by
  let _ := leaderParams IP h0 L
  let _ : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
  rw [sPhase_def]
  unfold xPhase XSt.phase
  obtain ⟨t_now, mb, trees, hist, st, ord, prog⟩ := x
  cases prog with
  | Ready =>
    dsimp only
    rw [foldr_emb IP h0 GB U txSel L ks A (sRcv_emb Sch IP h0 GB U txSel L ks A ideal f)]
    rfl
  | Delivered =>
    dsimp only
    rw [foldr_emb IP h0 GB U txSel L ks A (sBake_emb Sch IP h0 GB U txSel L ks A ideal f)]
    rfl
  | Baked => rfl

/-- The initial state of the execution over `f` is the embedding of the hash-free initial
state. -/
theorem N0_eq_emb (ideal : Bool) (f : BlockDom Tx Hash np Hz → Hash) :
    sTrace Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f) A ideal 0 =
      emb IP h0 GB U txSel L ks A f (x₀ IP h0 GB U L A) := by
  let _ := leaderParams IP h0 L
  let _ : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
  simp only [sTrace, runTrace, Function.iterate_zero, id, N0, emb, x₀,
    GlobalState.mk.injEq, and_true, true_and]
  refine ⟨?_, rfl, rfl⟩
  funext p
  by_cases hp : p ∈ IP
  · rw [if_pos hp]
    exact (if_pos hp).symm ▸ rfl
  · rw [if_neg hp]
    exact (if_neg hp).symm ▸ rfl

/-- **Erasure of the hash function from the state.** The trace of the execution of a uniform
protocol over the oracle `f` is the image under `emb f` of the hash-free trace. -/
theorem sTrace_eq_emb (ideal : Bool) (f : BlockDom Tx Hash np Hz → Hash) (k : ℕ) :
    sTrace Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f) A ideal k =
      emb IP h0 GB U txSel L ks A f
        ((xPhase Sch IP h0 GB U txSel L ks A ideal f)^[k] (x₀ IP h0 GB U L A)) := by
  induction k with
  | zero => exact N0_eq_emb Sch IP h0 GB U txSel L ks A ideal f
  | succ k ih =>
    rw [sTrace_succ, ih, sPhase_emb, Function.iterate_succ_apply']

/-! ## The history invariant on hash-free states -/

/-- The history invariant `HistInv` on hash-free states: every message in transit has been
broadcast, and every block of a tree is the genesis block or a broadcast block. -/
structure XSt.HistInv (x : XS IP h0 GB U L A) : Prop where
  buff : ∀ mt ∈ x.msg_buff, mt.msg ∈ x.history
  state : ∀ p t, x.trees p = some t →
    ∀ b ∈ @UTreeType.allBlocks Tx Hash (Fin np) (leaderParams IP h0 L) GB (U L p) t,
    b ∈ GB :: x.history.map get_block

/-- `HistInv` of an embedded state is the history invariant of the hash-free state. -/
theorem histInv_emb_iff (f : BlockDom Tx Hash np Hz → Hash) (x : XS IP h0 GB U L A) :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    letI := mkExec Sch false (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f) A
    HistInv (emb IP h0 GB U txSel L ks A f x) ↔ XSt.HistInv IP h0 GB U L A x := by
  let _ := leaderParams IP h0 L
  let _ : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
  constructor
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun p t ht b hbt => hs p
      ⟨(Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel).trees L f p, p, t⟩ ?_ b hbt⟩
    show (x.trees p).map _ = _
    rw [ht]
    rfl
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun p l hl b hbl => ?_⟩
    change (x.trees p).map _ = _ at hl
    cases ht : x.trees p with
    | none => rw [ht] at hl; cases hl
    | some t =>
      rw [ht] at hl
      cases hl
      exact hs p t ht b hbl

end Embed

end CatCryptCore.Consensus.PoSNSB
