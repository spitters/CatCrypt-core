/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Basic

/-!
# PoS-NSB: the protocol and execution model

This file ports the model of the Coq development PoS-NSB (Thomsen and Spitters,
*Formalizing Nakamoto-style proof of stake*, CSF 2021, https://github.com/AU-COBRA/PoS-NSB).
Each section names the Coq file it ports:

* `Protocol/Parameters.v`: transactions, hashes, parties, slots, the lottery `Winner`;
* `Protocol/Blocks.v`: blocks and chains, the genesis block and the hash function `HashB`;
* `Protocol/Messages.v`: messages;
* `Protocol/BlockTree.v`: valid chains and the interface `TreeType` of a block tree with
  a chain-selection rule `bestChain`;
* `Protocol/LocalState.v`, `Protocol/StateMonad.v`, `Protocol/Protocol.v`: the local state
  of a party and the honest protocol (`honest_bake`, `honest_rcv`);
* `Model/MessageTuple.v`, `Model/GlobalState.v`, `Model/Network.v`, `Model/Schedule.v`:
  the network, global states, party steps, the step relation `SingleStep` and its
  reflexive-transitive closure `BigStep`;
* the characteristic string of the lottery (`charString`), from which the slot conditions
  of `Properties/CG.v`, `Properties/CQ.v` and `Properties/CP.v` are read off.

The Coq `Parameter`s become fields of the classes `Parameters` and `Execution`; the types
of transactions, hashes, parties and adversarial states are type parameters. Hash and
lottery functions stay abstract. The Coq `Axiom`s are not part of the model: the theorems
that use them take them as hypotheses.

## Departures from the Coq model

* The map from parties to local states is a function `Party → Option LocalState` instead
  of a `finMap`; lookup `.[? p]` becomes application and `setf` becomes
  `Function.update`. The initial map sends each party of `InitParties` to its initial
  state, which is what the Coq `foldr` of `setf` over `InitParties` computes.
* `valid_chain` is a proposition. `decreasing_slots` is `List.Pairwise`, which for the
  transitive relation `lt_slots` is equivalent to the Coq `sorted`.
* The chain-selection rule of a `TreeType` comes with the properties that do not fix the
  rule (`best_chain_valid`, `best_chain_in_all`); the Coq field `best_chain_best`, which
  says that `bestChain` is a longest valid chain, is the separate predicate
  `TreeType.LongestChainRule`. Theorems that need it take it as a hypothesis, so that
  other selection rules can reuse the model.
* The adversarial delay `seq_sub [:: 1; 2]` of `Model/Network.v` is the subtype
  `AdvDelay` of natural numbers equal to `1` or `2`; the name `Delay` is kept for the
  natural-number delay of `Protocol/Parameters.v`.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

universe u v w

/-! ## `Protocol/Parameters.v` and `Protocol/Blocks.v` -/

/-- Slots are natural numbers. The name is a scoped notation for `ℕ`, so that `omega` sees
slots as natural numbers. -/
scoped notation "Slot" => ℕ

/-- The first slot. -/
def SlotZero : Slot := 0

/-- Delays of messages in the network are natural numbers (a scoped notation for `ℕ`). -/
scoped notation "Delay" => ℕ

/-- A block: its slot, its transactions, the hash of its predecessor and its baker. -/
structure Block (Tx Hash Party : Type) where
  /-- The slot in which the block was baked. -/
  sl : Slot
  /-- The transactions of the block. -/
  txs : Tx
  /-- The hash of the predecessor block. -/
  pred : Hash
  /-- The party that baked the block. -/
  bid : Party

/-- A chain is a list of blocks, newest first. -/
abbrev Chain (Tx Hash Party : Type) := List (Block Tx Hash Party)

/-- A block pool is a list of blocks. -/
abbrev BlockPool (Tx Hash Party : Type) := List (Block Tx Hash Party)

/-- Honesty of a party. -/
inductive Honesty where
  | Honest
  | Corrupt
  deriving DecidableEq

/-- The parameters of `Protocol/Parameters.v`: the initial parties and the slot lottery. -/
class Parameters (Party : Type) where
  /-- The parties present from the start. -/
  InitParties : List Party
  /-- `Winner p sl`: party `p` is a slot leader of slot `sl`. -/
  Winner : Party → Slot → Bool

/-- The parameters of `Protocol/Blocks.v`: the genesis block and the block hash function. -/
class BlockParameters (Tx Hash Party : Type) where
  /-- The genesis block. -/
  GenesisBlock : Block Tx Hash Party
  /-- The hash of a block. -/
  HashB : Block Tx Hash Party → Hash

/-- The static corruption status of each party (`CorruptionStatus` of `Model/Schedule.v`). -/
class Corruption (Party : Type) where
  /-- The corruption status of each party. -/
  CorruptionStatus : Party → Honesty

open Parameters BlockParameters Corruption

/-! ## `Protocol/Messages.v` -/

/-- Messages carry blocks. -/
inductive Message (Tx Hash Party : Type) where
  | BlockMsg : Block Tx Hash Party → Message Tx Hash Party

/-- Lists of messages. -/
abbrev Messages (Tx Hash Party : Type) := List (Message Tx Hash Party)

/-- The block of a message (`get_block` of `Properties/CG.v`). -/
def get_block {Tx Hash Party : Type} : Message Tx Hash Party → Block Tx Hash Party
  | .BlockMsg b => b

/-! ## `Protocol/BlockTree.v` -/

section BlockTree

variable {Tx Hash Party : Type} [Parameters Party] [BlockParameters Tx Hash Party]

/-- A block is correct when its baker wins the lottery of its slot. -/
def correct_block (b : Block Tx Hash Party) : Prop := Winner b.bid b.sl = true

/-- All blocks of the chain are correct. -/
def correct_blocks (c : Chain Tx Hash Party) : Prop := ∀ b ∈ c, correct_block b

/-- `linked b b'`: the predecessor hash of `b` is the hash of `b'`. -/
def linked (b b' : Block Tx Hash Party) : Prop := b.pred = HashB b'

/-- Consecutive blocks are linked and the last block is the genesis block. -/
def properly_linked : Chain Tx Hash Party → Prop
  | [] => False
  | [b] => b = GenesisBlock
  | b :: b' :: bs => linked b b' ∧ properly_linked (b' :: bs)

/-- `lt_slots b b'`: block `b` has a larger slot than `b'`. -/
def lt_slots (b b' : Block Tx Hash Party) : Prop := b'.sl < b.sl

/-- The slots of the chain decrease strictly from head to tail. -/
def decreasing_slots (c : Chain Tx Hash Party) : Prop := c.Pairwise lt_slots

/-- A valid chain: correct blocks, properly linked down to genesis, strictly decreasing
slots. -/
def valid_chain (c : Chain Tx Hash Party) : Prop :=
  correct_blocks c ∧ properly_linked c ∧ decreasing_slots c

variable (Tx Hash Party) in
/-- The interface of a block tree (`BlockTree.mixin_of` of `Protocol/BlockTree.v`): a type
of trees with extension by a block, the set of blocks of a tree, the initial tree holding
the genesis block, and a chain-selection rule `bestChain` that returns, for a slot `s`, a
valid chain of blocks of the tree with slots at most `s`. -/
structure TreeType where
  /-- The carrier of trees. -/
  T : Type
  /-- Add a block to a tree. -/
  extendTree : T → Block Tx Hash Party → T
  /-- The chain-selection rule: the chain a party adopts at slot `s`. -/
  bestChain : Slot → T → Chain Tx Hash Party
  /-- The blocks of a tree. -/
  allBlocks : T → BlockPool Tx Hash Party
  /-- The initial tree. -/
  tree0 : T
  all_tree0 : ∀ b, b ∈ allBlocks tree0 ↔ b ∈ [GenesisBlock]
  all_extend : ∀ t b b', b' ∈ allBlocks (extendTree t b) ↔ b' ∈ allBlocks t ++ [b]
  best_chain_valid : ∀ t s, valid_chain (bestChain s t)
  best_chain_in_all : ∀ s t, ∀ b ∈ bestChain s t,
    b ∈ (allBlocks t).filter (fun b => decide (b.sl ≤ s))

/-- The longest-chain rule (the field `best_chain_best` of `Protocol/BlockTree.v`): the
selected chain is at least as long as every valid chain of blocks of the tree with slots at
most `s`. -/
def TreeType.LongestChainRule (tT : TreeType Tx Hash Party) : Prop :=
  ∀ (c : Chain Tx Hash Party) (s : Slot) (t : tT.T), valid_chain c →
    (∀ b ∈ c, b ∈ (tT.allBlocks t).filter (fun b => decide (b.sl ≤ s))) →
      c.length ≤ (tT.bestChain s t).length

end BlockTree

/-! ## `Protocol/LocalState.v` and `Protocol/StateMonad.v` -/

/-- The local state of a party: a tree type, the party's key and its block tree. -/
structure LocalState (Tx Hash Party : Type) [Parameters Party] [BlockParameters Tx Hash Party] where
  /-- The tree type used by the party. -/
  tT : TreeType Tx Hash Party
  /-- The party's identity. -/
  pk : Party
  /-- The party's block tree. -/
  tree : tT.T

/-- The blocks of a party's tree (`allBlocks (tree l)` in Coq). -/
abbrev LocalState.blocks {Tx Hash Party : Type} [Parameters Party] [BlockParameters Tx Hash Party]
    (l : LocalState Tx Hash Party) : BlockPool Tx Hash Party :=
  l.tT.allBlocks l.tree

/-- The state monad. -/
def State (s : Type u) (a : Type v) : Type (max u v) := s → a × s

namespace State

/-- Read the state. -/
def get {s : Type u} : State s s := fun i => (i, i)
/-- Read a function of the state. -/
def gets {s : Type u} {a : Type v} (f : s → a) : State s a := fun i => (f i, i)
/-- Replace the state. -/
def put {s : Type u} (x : s) : State s PUnit.{v + 1} := fun _ => (PUnit.unit, x)
/-- Modify the state. -/
def modify {s : Type u} (f : s → s) : State s PUnit.{v + 1} := fun i => (PUnit.unit, f i)
/-- Return a value. -/
def pure {s : Type u} {a : Type v} (x : a) : State s a := fun st => (x, st)
/-- Sequence two computations. -/
def bind {s : Type u} {a : Type v} {b : Type w} (m1 : State s a) (f : a → State s b) :
    State s b :=
  fun st => f (m1 st).1 (m1 st).2

end State

/-! ## `Protocol/Protocol.v` -/

section Protocol

variable {Tx Hash Party : Type} [Parameters Party] [BlockParameters Tx Hash Party]

/-- Extend the tree of a local state by a block. -/
def extend_tree_l (l : LocalState Tx Hash Party) (b : Block Tx Hash Party) :
    LocalState Tx Hash Party :=
  ⟨l.tT, l.pk, l.tT.extendTree l.tree b⟩

/-- Process a received message: add its block to the tree. -/
def process_msg (m : Message Tx Hash Party) (l : LocalState Tx Hash Party) :
    LocalState Tx Hash Party :=
  match m with
  | .BlockMsg b => extend_tree_l l b

/-- Process a list of received messages. -/
def process_msgs (msgs : Messages Tx Hash Party) :
    State (LocalState Tx Hash Party) PUnit.{1} :=
  State.modify (fun l => msgs.foldr process_msg l)

/-- The honest baking step: if the party wins slot `sl`, it bakes a block on top of its
best chain at slot `sl - 1`, adds the block to its own tree and returns the message to
broadcast. -/
def honest_bake (sl : Slot) (txs : Tx) :
    State (LocalState Tx Hash Party) (Messages Tx Hash Party) :=
  State.bind State.get fun local_state =>
    if Winner local_state.pk sl then
      let bestChain := local_state.tT.bestChain (sl - 1) local_state.tree
      let hashPrev := HashB (bestChain.headD GenesisBlock)
      let newBlock : Block Tx Hash Party := ⟨sl, txs, hashPrev, local_state.pk⟩
      State.bind (State.modify.{1, 0} fun l => extend_tree_l l newBlock) fun _ =>
        State.pure [Message.BlockMsg newBlock]
    else State.pure []

/-- The honest receiving step: process the delivered messages. -/
def honest_rcv (msgs : Messages Tx Hash Party) (_sl : Slot) :
    State (LocalState Tx Hash Party) PUnit.{1} :=
  process_msgs msgs

end Protocol

/-! ## `Model/MessageTuple.v` and `Model/GlobalState.v` -/

/-- A message in transit: the message, its receiver and its remaining delay. -/
structure MessageTuple (Tx Hash Party : Type) where
  /-- The message. -/
  msg : Message Tx Hash Party
  /-- The receiver. -/
  rcv : Party
  /-- The remaining delay. -/
  cd : Delay

/-- The pool of messages in transit. -/
abbrev MessagePool (Tx Hash Party : Type) := List (MessageTuple Tx Hash Party)

/-- How far the current round has progressed. -/
inductive Progress where
  | Ready
  | Delivered
  | Baked
  deriving DecidableEq

/-- The history of all broadcast messages. -/
abbrev History (Tx Hash Party : Type) := Messages Tx Hash Party

/-- The local states of the parties. -/
abbrev StateMap (Tx Hash Party : Type) [Parameters Party] [BlockParameters Tx Hash Party] :=
  Party → Option (LocalState Tx Hash Party)

/-- The adversarial delay of a message: `1` or `2` rounds (`Delay` of `Model/Network.v`). -/
def AdvDelay : Type := {n : ℕ // n = 1 ∨ n = 2}

/-- The adversary's choice of delay for each receiver. -/
def DelayMap (Party : Type) : Type := Party → AdvDelay

/-- The global state of an execution. -/
structure GlobalState (Tx Hash Party AdvState : Type) [Parameters Party] [BlockParameters Tx Hash Party] where
  /-- The current slot. -/
  t_now : Slot
  /-- The messages that still have to be delivered. -/
  msg_buff : MessagePool Tx Hash Party
  /-- The local state of each party. -/
  state_map : StateMap Tx Hash Party
  /-- All messages broadcast so far. -/
  history : History Tx Hash Party
  /-- The state of the adversary. -/
  adv_state : AdvState
  /-- The execution order of the parties in the next round. -/
  exec_order : List Party
  /-- How far the current round has progressed. -/
  progress : Progress

/-- The parameters of an execution (the `Parameter`s of `Model/GlobalState.v` and
`Model/Schedule.v`): the initial adversarial state, the tree type of each party, the
two adversary functions and the selection of
transactions. -/
class Execution (Tx Hash Party AdvState : Type) [Parameters Party] [BlockParameters Tx Hash Party] where
  /-- The initial state of the adversary. -/
  AdvState0 : AdvState
  /-- The tree type each party uses. -/
  TreeTypeMap : Party → TreeType Tx Hash Party
  /-- The adversary's action when a corrupt party bakes. -/
  AdversarialBake : Slot → History Tx Hash Party → MessagePool Tx Hash Party →
    State AdvState (List (Message Tx Hash Party × DelayMap Party))
  /-- The adversary's action when a corrupt party receives messages. -/
  AdversarialRcv : Messages Tx Hash Party → Slot → History Tx Hash Party →
    MessagePool Tx Hash Party → State AdvState (List (Message Tx Hash Party × DelayMap Party))
  /-- The transactions an honest party includes in a block. -/
  TxSelection : Slot → Party → Tx

open Execution

section GlobalState

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState]

variable (AdvState) in
/-- The initial local state of a party: the initial tree of its tree type. -/
def init_local (pk : Party) : LocalState Tx Hash Party :=
  ⟨TreeTypeMap (AdvState := AdvState) pk, pk, (TreeTypeMap (AdvState := AdvState) pk).tree0⟩

variable (AdvState) in
/-- The initial global state: slot `1`, no messages, every initial party in its initial
state, executing in the order `InitParties`. -/
def N0 [DecidableEq Party] : GlobalState Tx Hash Party AdvState where
  t_now := 1
  msg_buff := []
  state_map := fun p => if p ∈ InitParties then
    some (init_local AdvState p) else none
  history := []
  adv_state := AdvState0 Tx Hash Party
  exec_order := InitParties
  progress := .Ready

end GlobalState

/-! ## `Model/Network.v` -/

section Network

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]

/-- Honest broadcast: the message reaches every party of the execution order after one
round. -/
def flood_msg (m : Message Tx Hash Party) (N : GlobalState Tx Hash Party AdvState) :
    GlobalState Tx Hash Party AdvState :=
  { N with msg_buff := N.exec_order.map (fun r => ⟨m, r, 1⟩) ++ N.msg_buff
           history := m :: N.history }

/-- Adversarial broadcast: the adversary chooses a delay of one or two rounds for each
receiver. -/
def flood_msg_adv (m : Message Tx Hash Party) (φ : DelayMap Party)
    (N : GlobalState Tx Hash Party AdvState) : GlobalState Tx Hash Party AdvState :=
  { N with msg_buff := N.exec_order.map (fun r => ⟨m, r, (φ r).1⟩) ++ N.msg_buff
           history := m :: N.history }

/-- The messages for `r` whose delay has run out. -/
def collect_zero_pairs (r : Party) (N : GlobalState Tx Hash Party AdvState)
    [DecidableEq Party] : MessagePool Tx Hash Party :=
  N.msg_buff.filter (fun mt => mt.cd == 0 && decide (mt.rcv = r))

/-- Remove the messages for `r` whose delay has run out. -/
def rmv_zero_msgs [DecidableEq Party] (r : Party) (N : GlobalState Tx Hash Party AdvState) :
    GlobalState Tx Hash Party AdvState :=
  { N with msg_buff := N.msg_buff.filter (fun mt => !(mt.cd == 0 && decide (mt.rcv = r))) }

/-- Fetch the messages for `r` whose delay has run out. -/
def fetch_msgs [DecidableEq Party] (r : Party) (N : GlobalState Tx Hash Party AdvState) :
    Messages Tx Hash Party × GlobalState Tx Hash Party AdvState :=
  ((collect_zero_pairs r N).map MessageTuple.msg, rmv_zero_msgs r N)

/-- Decrease all delays by one round. -/
def round_tick (N : GlobalState Tx Hash Party AdvState) : GlobalState Tx Hash Party AdvState :=
  { N with msg_buff := N.msg_buff.map (fun m => { m with cd := m.cd - 1 }) }

end Network

/-! ## `Model/Schedule.v` -/

section Schedule

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState] [Corruption Party] [DecidableEq Party]

/-- Replace the local state of `p`. -/
def upd_local (p : Party) (l : LocalState Tx Hash Party) (N : GlobalState Tx Hash Party AdvState) :
    GlobalState Tx Hash Party AdvState :=
  { N with state_map := Function.update N.state_map p (some l) }

/-- Honest broadcast of several messages. -/
def flood_msgs (msgs : Messages Tx Hash Party) (N : GlobalState Tx Hash Party AdvState) :
    GlobalState Tx Hash Party AdvState :=
  msgs.foldr flood_msg N

/-- Adversarial broadcast of several messages. -/
def flood_msgs_adv (msgs : List (Message Tx Hash Party × DelayMap Party))
    (N : GlobalState Tx Hash Party AdvState) : GlobalState Tx Hash Party AdvState :=
  msgs.foldr (fun mφ => flood_msg_adv mφ.1 mφ.2) N

/-- The party is corrupt. -/
def is_corrupt (p : Party) : Bool := decide (CorruptionStatus p = .Corrupt)

/-- The party is honest. -/
def is_honest (p : Party) : Bool := decide (CorruptionStatus p = .Honest)

/-- The baking step of party `p`: an honest party runs `honest_bake` and broadcasts the
result; for a corrupt party the adversary function `AdversarialBake` decides the messages
and their delays. -/
def party_bake_step_world (p : Party) (N : GlobalState Tx Hash Party AdvState) :
    GlobalState Tx Hash Party AdvState :=
  match N.state_map p with
  | some l =>
    if !is_corrupt p then
      let r := honest_bake N.t_now (TxSelection (Hash := Hash) (AdvState := AdvState) N.t_now p) l
      flood_msgs r.1 (upd_local p r.2 N)
    else
      let r := AdversarialBake N.t_now N.history N.msg_buff N.adv_state
      { flood_msgs_adv r.1 N with adv_state := r.2 }
  | none => N

/-- The receiving step of party `p`: the party fetches its delivered messages; an honest
party processes them with `honest_rcv`, for a corrupt party the adversary function
`AdversarialRcv` decides which messages to send. -/
def party_rcv_step_world (p : Party) (N : GlobalState Tx Hash Party AdvState) :
    GlobalState Tx Hash Party AdvState :=
  match N.state_map p with
  | some l =>
    let f := fetch_msgs p N
    if !is_corrupt p then
      let r := honest_rcv f.1 f.2.t_now l
      upd_local p r.2 f.2
    else
      let r := AdversarialRcv f.1 f.2.t_now f.2.history f.2.msg_buff f.2.adv_state
      { flood_msgs_adv r.1 f.2 with adv_state := r.2 }
  | none => N

/-- Advance the slot. -/
def inc_round (N : GlobalState Tx Hash Party AdvState) : GlobalState Tx Hash Party AdvState :=
  { N with t_now := N.t_now + 1 }

/-- One step of the execution: delivery to all parties, baking by all parties, the
next round, or a permutation of the execution order or of the message buffer (the
adversary's scheduling choices). -/
inductive SingleStep : GlobalState Tx Hash Party AdvState → GlobalState Tx Hash Party AdvState →
    Prop where
  | Deliver (N : GlobalState Tx Hash Party AdvState) : N.progress = .Ready →
      SingleStep N { N.exec_order.foldr party_rcv_step_world N with progress := .Delivered }
  | Bake (N : GlobalState Tx Hash Party AdvState) : N.progress = .Delivered →
      SingleStep N { N.exec_order.foldr party_bake_step_world N with progress := .Baked }
  | NextRound (N : GlobalState Tx Hash Party AdvState) : N.progress = .Baked →
      SingleStep N { inc_round (round_tick N) with progress := .Ready }
  | PermParties (N : GlobalState Tx Hash Party AdvState) (ps : List Party) :
      N.exec_order.Perm ps → SingleStep N { N with exec_order := ps }
  | PermMsgs (N : GlobalState Tx Hash Party AdvState) (mb : MessagePool Tx Hash Party) :
      N.msg_buff.Perm mb → SingleStep N { N with msg_buff := mb }

/-- The reflexive-transitive closure of `SingleStep`. -/
def BigStep (N N' : GlobalState Tx Hash Party AdvState) : Prop :=
  Relation.ReflTransGen SingleStep N N'

@[inherit_doc] infix:50 " ⤳ " => SingleStep
@[inherit_doc] infix:50 " ⇓ " => BigStep

end Schedule

/-! ## The characteristic string -/

section CharString

variable {Party : Type} [Parameters Party] [Corruption Party] [Fintype Party]

/-- The letter of a slot in the characteristic string: the number of honest slot leaders
among the initial parties, and whether some corrupt party is a slot leader. -/
structure SlotLetter where
  /-- The number of honest slot leaders among `InitParties`. -/
  honest : ℕ
  /-- Some corrupt party is a slot leader. -/
  adversarial : Bool
  deriving DecidableEq

/-- The characteristic string of the lottery: the letter of each slot. -/
def charString (sl : Slot) : SlotLetter where
  honest := (InitParties : List Party).countP
    (fun p => Winner p sl && is_honest p)
  adversarial := decide (∃ p : Party, Winner p sl = true ∧
    is_corrupt p = true)

end CharString

end CatCryptCore.Consensus.PoSNSB
