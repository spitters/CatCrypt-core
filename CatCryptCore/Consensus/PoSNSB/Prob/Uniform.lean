/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob
public import CatCryptCore.Consensus.PoSNSB.Prob.Time
public import CatCryptCore.Crypto.OracleEval

/-!
# PoS-NSB: tree types and adversaries uniform in the hash function

The tree type of a party (`TreeType`) is a structure over a fixed block hash function, so the
type of its trees may depend on the random oracle. A `UTreeType` has a carrier, an extension
and a set of blocks that do not mention the hash function; only its chain-selection rule
`bestChain h` takes the hash function `h`, and its value on a tree `t` depends only on `h` at
the blocks of `t` (`bestChain_local`). `UTreeType.at h` is the tree type over `h`, and a
protocol whose tree types are uniform (`Protocol.ofUniform`) has trees of the same type for
every random oracle.

An oracle adversary (`OAdversary`) receives the leader string and the verification keys, but
not the hash function; each of its calls is an `OracleAdv` that queries the hash function as
an oracle. `OAdversary.toAdversary` evaluates the calls against the hash function of the
public information.

## Main definitions

* `UTreeType`, `UTreeType.at`, `UTreeType.LongestChainRule`
* `Protocol.ofUniform` — the protocol whose tree type for `L`, `f`, `p` is `(U L p).at`
  applied to `b ↦ f (encB Hz b)`
* `ulongestTree` — the uniform tree type of longest valid chains
* `OAdversary`, `OAdversary.toAdversary`, `OAdversary.Bounded`

## Main results

* `Protocol.trees_ofUniform_T` — the trees of `Protocol.ofUniform` do not depend on the
  oracle
* `ProtocolHyp.ofUniform` — the hypotheses on the protocol from those on the uniform tree
  types
* `properly_linked_local`, `Cand_local` — linkage and candidate chains depend only on the hash
  function at the blocks involved
* `ulongestTree_longest` — `ulongestTree` follows the longest-chain rule for every hash
  function
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption
open CatCrypt.Crypto

/-! ## Uniform tree types -/

section UTree

variable {Tx Hash Party : Type} [Parameters Party]

variable (Tx Hash Party) in
/-- A tree type uniform in the hash function: carrier, extension, blocks and initial tree do
not depend on the hash function; the chain-selection rule `bestChain h` returns, for every
hash function `h`, a valid chain over `h` of blocks of the tree with slots at most `s`, and
depends only on `h` at the blocks of the tree. -/
structure UTreeType (GB : Block Tx Hash Party) where
  /-- The carrier of trees. -/
  T : Type
  /-- Add a block to a tree. -/
  extendTree : T → Block Tx Hash Party → T
  /-- The chain-selection rule over the hash function `h`. -/
  bestChain : (Block Tx Hash Party → Hash) → Slot → T → Chain Tx Hash Party
  /-- The blocks of a tree. -/
  allBlocks : T → BlockPool Tx Hash Party
  /-- The initial tree. -/
  tree0 : T
  all_tree0 : ∀ b, b ∈ allBlocks tree0 ↔ b ∈ [GB]
  all_extend : ∀ t b b', b' ∈ allBlocks (extendTree t b) ↔ b' ∈ allBlocks t ++ [b]
  best_chain_valid : ∀ h t s,
    @valid_chain Tx Hash Party _ ⟨GB, h⟩ (bestChain h s t)
  best_chain_in_all : ∀ h s t, ∀ b ∈ bestChain h s t,
    b ∈ (allBlocks t).filter (fun b => decide (b.sl ≤ s))
  /-- The selected chain depends only on the hash function at the blocks of the tree. -/
  bestChain_local : ∀ h h' s t, (∀ b ∈ allBlocks t, h b = h' b) →
    bestChain h s t = bestChain h' s t

variable {GB : Block Tx Hash Party}

/-- The tree type over the hash function `h` of a uniform tree type. -/
def UTreeType.at (U : UTreeType Tx Hash Party GB) (h : Block Tx Hash Party → Hash) :
    @TreeType Tx Hash Party _ ⟨GB, h⟩ :=
  letI : BlockParameters Tx Hash Party := ⟨GB, h⟩
  { T := U.T
    extendTree := U.extendTree
    bestChain := U.bestChain h
    allBlocks := U.allBlocks
    tree0 := U.tree0
    all_tree0 := U.all_tree0
    all_extend := U.all_extend
    best_chain_valid := fun t s => U.best_chain_valid h t s
    best_chain_in_all := U.best_chain_in_all h }

/-- A uniform tree type follows the longest-chain rule when its tree type over every hash
function does. -/
def UTreeType.LongestChainRule (U : UTreeType Tx Hash Party GB) : Prop :=
  ∀ h : Block Tx Hash Party → Hash,
    @TreeType.LongestChainRule Tx Hash Party _ ⟨GB, h⟩ (U.at h)

/-- Linkage of a chain depends only on the hash function at the blocks of the chain. -/
theorem properly_linked_local {h h' : Block Tx Hash Party → Hash} :
    ∀ c : Chain Tx Hash Party, (∀ b ∈ c, h b = h' b) →
      (@properly_linked Tx Hash Party ⟨GB, h⟩ c ↔
        @properly_linked Tx Hash Party ⟨GB, h'⟩ c)
  | [], _ => Iff.rfl
  | [_], _ => Iff.rfl
  | b :: b' :: bs, hh => by
    have ih := properly_linked_local (b' :: bs) fun x hx => hh x (List.mem_cons_of_mem _ hx)
    show (b.pred = h b' ∧ _) ↔ (b.pred = h' b' ∧ _)
    rw [hh b' (by simp)]
    exact and_congr_right' ih

/-- Candidate chains of a block list depend only on the hash function at its blocks. -/
theorem Cand_local {h h' : Block Tx Hash Party → Hash} {t : List (Block Tx Hash Party)}
    (s : Slot) (hh : ∀ b ∈ t, h b = h' b) :
    @Cand Tx Hash Party _ ⟨GB, h⟩ t s = @Cand Tx Hash Party _ ⟨GB, h'⟩ t s := by
  funext c
  apply propext
  have hc : ∀ (hin : ∀ b ∈ c, b ∈ t ∧ b.sl ≤ s), ∀ b ∈ c, h b = h' b :=
    fun hin b hb => hh b (hin b hb).1
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, hin⟩
    exact ⟨⟨h1, (properly_linked_local c (hc hin)).1 h2, h3⟩, hin⟩
  · rintro ⟨⟨h1, h2, h3⟩, hin⟩
    exact ⟨⟨h1, (properly_linked_local c (hc hin)).2 h2, h3⟩, hin⟩

/-- The predicate of a longest candidate chain of `t` with slots at most `s` over `h`. -/
def IsBest (GB : Block Tx Hash Party) (h : Block Tx Hash Party → Hash)
    (t : List (Block Tx Hash Party)) (s : Slot) (c : Chain Tx Hash Party) : Prop :=
  @Cand Tx Hash Party _ ⟨GB, h⟩ t s c ∧ c.length = @bestLen Tx Hash Party _ ⟨GB, h⟩ t s

theorem IsBest_local {h h' : Block Tx Hash Party → Hash} {t : List (Block Tx Hash Party)}
    (s : Slot) (hh : ∀ b ∈ t, h b = h' b) : IsBest GB h t s = IsBest GB h' t s := by
  unfold IsBest bestLen
  rw [Cand_local s hh]

/-- The uniform tree type whose trees are lists of blocks containing `GB` and whose
chain-selection rule over `h` picks a longest valid chain over `h` of blocks of the tree with
slots at most `s`. -/
noncomputable def ulongestTree (GB : Block Tx Hash Party)
    (hGB : ∀ h : Block Tx Hash Party → Hash, @valid_chain Tx Hash Party _ ⟨GB, h⟩ [GB])
    (hsl : GB.sl = 0) : UTreeType Tx Hash Party GB where
  T := {t : List (Block Tx Hash Party) // GB ∈ t}
  extendTree t b := ⟨t.1 ++ [b], List.mem_append_left _ t.2⟩
  bestChain h s t := Classical.epsilon (IsBest GB h t.1 s)
  allBlocks t := t.1
  tree0 := ⟨[GB], List.mem_singleton_self _⟩
  all_tree0 _ := Iff.rfl
  all_extend _ _ _ := Iff.rfl
  best_chain_valid h t s :=
    (Classical.epsilon_spec (p := IsBest GB h t.1 s)
      (@exists_best Tx Hash Party _ ⟨GB, h⟩ (hGB h) hsl t.1 t.2 s)).1.1
  best_chain_in_all h s t b hb := by
    have := (Classical.epsilon_spec (p := IsBest GB h t.1 s)
      (@exists_best Tx Hash Party _ ⟨GB, h⟩ (hGB h) hsl t.1 t.2 s)).1.2 b hb
    exact List.mem_filter.2 ⟨this.1, decide_eq_true this.2⟩
  bestChain_local h h' s t hh := by
    simp only [IsBest_local s hh]

/-- `ulongestTree` follows the longest-chain rule for every hash function. -/
theorem ulongestTree_longest (GB : Block Tx Hash Party)
    (hGB : ∀ h : Block Tx Hash Party → Hash, @valid_chain Tx Hash Party _ ⟨GB, h⟩ [GB])
    (hsl : GB.sl = 0) : (ulongestTree GB hGB hsl).LongestChainRule := by
  classical
  rintro h c s ⟨t, ht⟩ hc hall
  let _ : BlockParameters Tx Hash Party := ⟨GB, h⟩
  have hcand : Cand t s c := ⟨hc, fun b hb => by
    have := List.mem_filter.1 (hall b hb)
    exact ⟨this.1, by simpa using this.2⟩⟩
  have hspec := Classical.epsilon_spec (p := IsBest GB h t s)
    (@exists_best Tx Hash Party _ ⟨GB, h⟩ (hGB h) hsl t ht s)
  show c.length ≤ (Classical.epsilon (IsBest GB h t s)).length
  rw [hspec.2]
  exact Nat.le_findGreatest hcand.length_le ⟨c, hcand, rfl⟩

end UTree

/-! ## Protocols with uniform tree types -/

section Protocol

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ}

/-- The protocol with initial parties `IP`, padding leader `h0`, genesis block `GB`, uniform
tree types `U L p` and transaction selection `txSel`: the tree type of party `p` for the leader
string `L` and the oracle `f` is `(U L p).at` applied to the block hash `b ↦ f (encB Hz b)`. -/
def Protocol.ofUniform (IP : List (Fin np)) (h0 : Fin np) (GB : Block Tx Hash (Fin np))
    (U : (L : Fin n → Option (Fin np)) → Fin np →
      @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
    (txSel : Slot → Fin np → Tx) : Protocol Tx Hash np n Hz where
  IP := IP
  h0 := h0
  GB := GB
  trees L f p := @UTreeType.at Tx Hash (Fin np) (leaderParams IP h0 L) GB (U L p)
    (fun b => f (encB Hz b))
  txSel := txSel

/-- The trees of a protocol with uniform tree types do not depend on the oracle. -/
theorem Protocol.trees_ofUniform_T (IP : List (Fin np)) (h0 : Fin np)
    (GB : Block Tx Hash (Fin np))
    (U : (L : Fin n → Option (Fin np)) → Fin np →
      @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
    (txSel : Slot → Fin np → Tx) (L : Fin n → Option (Fin np))
    (f : BlockDom Tx Hash np Hz → Hash) (p : Fin np) :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    ((Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel).trees L f p).T = (U L p).T := rfl

/-- The hypotheses on a protocol with uniform tree types follow from the hypotheses on its
parties and genesis block and the longest-chain rule of every uniform tree type. -/
theorem ProtocolHyp.ofUniform {IP : List (Fin np)} {h0 : Fin np} {GB : Block Tx Hash (Fin np)}
    {U : (L : Fin n → Option (Fin np)) → Fin np →
      @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB}
    {txSel : Slot → Fin np → Tx} (nodup : IP.Nodup) (leader : LeaderHyp IP h0)
    (longest : ∀ L p, @UTreeType.LongestChainRule Tx Hash (Fin np) (leaderParams IP h0 L) GB
      (U L p))
    (genesis_honest : honest_block GB = true) (genesis_slot : GB.sl ≤ 1) :
    ProtocolHyp (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) :=
  ⟨nodup, leader, fun L _ p => longest L p _, genesis_honest, genesis_slot⟩

end Protocol

/-! ## Oracle adversaries -/

section OAdversary

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK Sig : Type}

/-- An adversary against the signed protocol that queries the hash function as an oracle. Its
calls receive the leader string and the verification keys, the inputs of the calls of an
`Adversary` and the signatures of the honest blocks of the history; each call is an oracle
adversary with queries in `BlockDom` and answers in `Hash`. -/
structure OAdversary (Tx Hash : Type) (np n Hz : ℕ) (PK Sig : Type) where
  /-- The state of the adversary. -/
  AdvState : Type
  /-- The initial state. -/
  st0 : AdvState
  /-- The action when a corrupt party bakes. -/
  bake : (Fin n → Option (Fin np)) × (Fin np → PK) → Slot → History Tx Hash (Fin np) →
    List (Block Tx Hash (Fin np) × Sig) → MessagePool Tx Hash (Fin np) → AdvState →
      OracleAdv (BlockDom Tx Hash np Hz) Hash (AdvOut Tx Hash np Sig × AdvState)
  /-- The action when a corrupt party receives messages. -/
  rcv : (Fin n → Option (Fin np)) × (Fin np → PK) → Messages Tx Hash (Fin np) → Slot →
    History Tx Hash (Fin np) → List (Block Tx Hash (Fin np) × Sig) →
      MessagePool Tx Hash (Fin np) → AdvState →
        OracleAdv (BlockDom Tx Hash np Hz) Hash (AdvOut Tx Hash np Sig × AdvState)

/-- The adversary whose calls evaluate the oracle calls of `A` against the hash function of the
public information. -/
noncomputable def OAdversary.toAdversary (A : OAdversary Tx Hash np n Hz PK Sig) :
    Adversary Tx Hash np n Hz PK Sig where
  AdvState := A.AdvState
  st0 := A.st0
  bake pub sl hist tbl mb st := ((A.bake (pub.1, pub.2.2) sl hist tbl mb st).evalOn pub.2.1).1
  rcv pub ms sl hist tbl mb st :=
    ((A.rcv (pub.1, pub.2.2) ms sl hist tbl mb st).evalOn pub.2.1).1

/-- Every call of `A` asks at most `qc` oracle queries, and every call of `A.toAdversary`
outputs at most `m` messages. -/
def OAdversary.Bounded (A : OAdversary Tx Hash np n Hz PK Sig) (qc m : ℕ) : Prop :=
  ((∀ pub sl hist tbl mb st, (A.bake pub sl hist tbl mb st).IsQueryBound qc) ∧
    ∀ pub ms sl hist tbl mb st, (A.rcv pub ms sl hist tbl mb st).IsQueryBound qc) ∧
  A.toAdversary.OutputBound m

end OAdversary

end CatCryptCore.Consensus.PoSNSB
