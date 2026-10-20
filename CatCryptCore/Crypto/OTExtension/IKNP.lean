/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.Games
public import Mathlib.Algebra.Ring.BooleanRing
public import CatCryptCore.Tactics.DeriveReduction

/-!
# IKNP OT extension: semi-honest security from base OT and correlation-robust hashing

The IKNP extension (`iknp B H`) builds `m` 1-out-of-2 OTs of messages in an additive group
`M` from `κ` base OTs `B` of `m`-bit strings and a hash `H : Fin m → (Fin κ → Bool) → M`.
Bits are the Boolean ring `Bool`, whose addition is exclusive or.

1. The receiver, with choices `r : Fin m → Bool`, draws a matrix `T` with rows
   `T j : Fin κ → Bool`. The sender draws `s : Fin κ → Bool`.
2. With the roles swapped, the receiver acts as base-OT sender on the column pairs
   `(tⁱ, tⁱ + r)` (`iknpBaseIn`), and the sender as base-OT receiver with choices `s`. The
   sender obtains the matrix `Q` whose rows are `q j = T j + r j · s`.
3. The sender sends `y j = (x j.1 + H j (q j), x j.2 + H j (q j + s))`
   (`iknpSenderMsg`), and the receiver outputs `y j` at `r j` minus `H j (T j)`
   (`iknpRecvOut`).

Receiver privacy reduces to the sender privacy of the base OTs, with no further loss: the
columns the sender obtains from the ideal base OT are a uniform matrix. Sender privacy
reduces to the receiver privacy of the base OTs and the correlation robustness of `H`: once
the base OTs are ideal, the unchosen pads are `H j (T j + s)` with `s` hidden.

## Main definitions

* `iknp` — the extended OT scheme; `iknpSimS`, `iknpSimR` — its simulators
* `iknpSenderRed`, `iknpReceiverRed` — the base-OT reductions, with `iknpRedChoose`,
  `iknpSenderGuess`, `iknpReceiverGuess`
* `iknpCRRed` — the correlation-robust hash reduction
* `iknpRedChooseOf`, `iknpGuessOf`, `iknpCRRedOf` — the reductions over their data maps,
  with costed forms `….tree.timed` from `derive_reduction`

## Main results

* `iknp_recvPriv_eq` — the receiver-privacy advantage of `A` against `iknp B H` equals the
  sender-privacy advantage of `iknpSenderRed H A` against `B`
* `iknp_sendPriv_le` — the sender-privacy advantage of `A` against `iknp B H` is at most the
  receiver-privacy advantage of `iknpReceiverRed H A` against `B` plus the
  correlation-robust hash advantage of `iknpCRRed simSB H A.choose A.guess`
* `iknpRedChooseOf.tree.timeBound_timed`, `iknpGuessOf.tree.timeBound_timed`,
  `iknpCRRedOf.tree.timeBound_timed` — the times of the costed reductions
* `iknpRedChoose.erase_timed`, `iknpSenderGuess.erase_timed`,
  `iknpReceiverGuess.erase_timed`, `iknpCRRed.erase_timed` — the costed forms erase to
  the reductions

## References

* Y. Ishai, J. Kilian, K. Nissim, E. Petrank, *Extending Oblivious Transfers
  Efficiently*, CRYPTO 2003, §3 (semi-honest protocol and its proof)
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace CatCrypt.Crypto.OT

variable {κ m : ℕ} {M VSB VRB S : Type}

/-! ## The protocol -/

/-- The base-OT message pairs of the receiver: the columns of `T` and the columns of `T`
plus the choice vector. -/
def iknpBaseIn (T : Fin m → Fin κ → Bool) (r : Fin m → Bool) :
    Fin κ → (Fin m → Bool) × (Fin m → Bool) :=
  fun i => (fun j => T j i, fun j => T j i + r j)

/-- The rows `r j · s` by which the sender's matrix differs from `T`. -/
def iknpShift (r : Fin m → Bool) (s : Fin κ → Bool) : Fin m → Fin κ → Bool :=
  fun j => if r j then s else 0

section Protocol

variable [AddCommGroup M]

/-- The sender's masked message pairs from its columns `q` and its secret `s`. -/
def iknpSenderMsg (H : Fin m → (Fin κ → Bool) → M) (x : Fin m → M × M)
    (s : Fin κ → Bool) (q : Fin κ → Fin m → Bool) : Fin m → M × M :=
  fun j => ((x j).1 + H j (fun i => q i j), (x j).2 + H j ((fun i => q i j) + s))

/-- The receiver's output: the masked message at its choice minus the hash of its row. -/
def iknpRecvOut (H : Fin m → (Fin κ → Bool) → M) (r : Fin m → Bool)
    (T : Fin m → Fin κ → Bool) (y : Fin m → M × M) : Fin m → M :=
  fun j => (if r j then (y j).2 else (y j).1) - H j (T j)

/-- The view of the IKNP sender: its secret, its view as base-OT receiver, and the columns
it obtained. -/
abbrev IKNPSenderView (κ m : ℕ) (VRB : Type) :=
  (Fin κ → Bool) × VRB × (Fin κ → Fin m → Bool)

/-- The view of the IKNP receiver: its matrix, its view as base-OT sender, and the masked
message pairs. -/
abbrev IKNPReceiverView (κ m : ℕ) (M VSB : Type) :=
  (Fin m → Fin κ → Bool) × VSB × (Fin m → M × M)

/-- **The IKNP OT extension** of the base OTs `B` with the hash `H`. -/
noncomputable def iknp (B : OTScheme κ (Fin m → Bool) VSB VRB)
    (H : Fin m → (Fin κ → Bool) → M) :
    OTScheme m M (IKNPSenderView κ m VRB) (IKNPReceiverView κ m M VSB) where
  exec x r :=
    SPComp.bind (SPComp.sample (Fin m → Fin κ → Bool)) fun T =>
      SPComp.bind (SPComp.sample (Fin κ → Bool)) fun s =>
        SPComp.bind (B.exec (iknpBaseIn T r) s) fun e =>
          SPComp.pure ((s, e.2.1, e.2.2), (T, e.1, iknpSenderMsg H x s e.2.2),
            iknpRecvOut H r T (iknpSenderMsg H x s e.2.2))

/-- The sender simulator: a uniform secret, a uniform matrix of columns, and the base-OT
receiver simulator `simRB` on them. -/
noncomputable def iknpSimS (simRB : (Fin κ → Bool) → (Fin κ → Fin m → Bool) → SPComp VRB)
    (_x : Fin m → M × M) : SPComp (IKNPSenderView κ m VRB) :=
  SPComp.bind (SPComp.sample (Fin κ → Bool)) fun s =>
    SPComp.bind (SPComp.sample (Fin m → Fin κ → Bool)) fun T =>
      SPComp.bind (simRB s fun i j => T j i) fun v => SPComp.pure (s, v, fun i j => T j i)

/-- The receiver simulator: a uniform matrix `T`, the base-OT sender simulator `simSB` on
the column pairs, the received message `z j + H j (T j)` at the choice and a uniform value
at the other position. -/
noncomputable def iknpSimR
    (simSB : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → SPComp VSB)
    (H : Fin m → (Fin κ → Bool) → M) [Fintype M] [Nonempty M]
    (r : Fin m → Bool) (z : Fin m → M) : SPComp (IKNPReceiverView κ m M VSB) :=
  SPComp.bind (SPComp.sample (Fin m → Fin κ → Bool)) fun T =>
    SPComp.bind (simSB (iknpBaseIn T r)) fun v =>
      SPComp.bind (SPComp.sample (Fin m → M)) fun u =>
        SPComp.pure (T, v, fun j =>
          if r j then (u j, z j + H j (T j)) else (z j + H j (T j), u j))

/-! ## Correctness on the ideal base OT -/

omit [AddCommGroup M] in
/-- The columns selected by the ideal base OT are the columns of `T + iknpShift r s`. -/
theorem otChoose_iknpBaseIn (T : Fin m → Fin κ → Bool) (r : Fin m → Bool)
    (s : Fin κ → Bool) :
    otChoose (iknpBaseIn T r) s = fun i j => (T + iknpShift r s) j i := by
  funext i j
  simp only [otChoose, iknpBaseIn, iknpShift, Pi.add_apply]
  by_cases hr : r j <;> by_cases hs : s i <;> simp [hr, hs] <;> rfl

/-- On the ideal base OT, the sender's message pairs carry the hash of `T j` at the choice
`r j` and the hash of `T j + s` at the other position. -/
theorem iknpSenderMsg_otChoose (H : Fin m → (Fin κ → Bool) → M) (x : Fin m → M × M)
    (T : Fin m → Fin κ → Bool) (r : Fin m → Bool) (s : Fin κ → Bool) :
    iknpSenderMsg H x s (otChoose (iknpBaseIn T r) s) = fun j =>
      if r j then ((x j).1 + H j (T j + s), (x j).2 + H j (T j))
      else ((x j).1 + H j (T j), (x j).2 + H j (T j + s)) := by
  rw [otChoose_iknpBaseIn]
  funext j
  by_cases hr : r j <;> simp only [iknpSenderMsg, iknpShift, hr, Pi.add_apply,
    if_true, if_false, Bool.false_eq_true] <;> congr 3 <;> funext i <;>
    simp only [Pi.add_apply, Pi.zero_apply] <;> cases T j i <;> cases s i <;> rfl

/-- On the ideal base OT, the receiver outputs the chosen messages. -/
theorem iknpRecvOut_otChoose (H : Fin m → (Fin κ → Bool) → M) (x : Fin m → M × M)
    (T : Fin m → Fin κ → Bool) (r : Fin m → Bool) (s : Fin κ → Bool) :
    iknpRecvOut H r T (iknpSenderMsg H x s (otChoose (iknpBaseIn T r) s)) = otChoose x r := by
  rw [iknpSenderMsg_otChoose]
  funext j
  by_cases hr : r j <;> simp [iknpRecvOut, otChoose, hr]

end Protocol

/-! ## The reductions -/

/-- The state of the base-OT reductions: the adversary's state, the sender's messages, the
receiver's choices, the matrix `T` and the secret `s`. -/
abbrev IKNPRedState (κ m : ℕ) (M S : Type) :=
  S × (Fin m → M × M) × (Fin m → Bool) × (Fin m → Fin κ → Bool) × (Fin κ → Bool)

/-- Inputs of the base-OT reductions over the column-pair map `bIn`: run the adversary's
input choice `c`, draw `T` and `s`, and give the base OTs the pairs `bIn T r` and the
choices `s`. -/
noncomputable def iknpRedChooseOf
    (bIn : (Fin m → Fin κ → Bool) → (Fin m → Bool) → Fin κ → (Fin m → Bool) × (Fin m → Bool))
    (c : SPComp ((Fin m → M × M) × (Fin m → Bool) × S)) :
    SPComp ((Fin κ → (Fin m → Bool) × (Fin m → Bool)) × (Fin κ → Bool) × IKNPRedState κ m M S) :=
  SPComp.bind c fun i =>
    SPComp.bind (SPComp.sample (Fin m → Fin κ → Bool)) fun T =>
      SPComp.bind (SPComp.sample (Fin κ → Bool)) fun s =>
        SPComp.pure (bIn T i.2.1, s, (i.2.2, i.1, i.2.1, T, s))

/-- Inputs of the base-OT reductions: `iknpRedChooseOf` at the column pairs `iknpBaseIn`. -/
noncomputable def iknpRedChoose (c : SPComp ((Fin m → M × M) × (Fin m → Bool) × S)) :
    SPComp ((Fin κ → (Fin m → Bool) × (Fin m → Bool)) × (Fin κ → Bool) × IKNPRedState κ m M S) :=
  iknpRedChooseOf iknpBaseIn c

/-- Distinguisher of a base-OT reduction over the view map `fin`: run `g` on the adversary's
state and on `fin` of the reduction state and the base-OT view and output. -/
noncomputable def iknpGuessOf {E V O : Type} (fin : IKNPRedState κ m M S → E → V × O)
    (g : S → V × O → SPComp Bool) (st : IKNPRedState κ m M S) (e : E) : SPComp Bool :=
  g st.1 (fin st e)

section Reductions

variable [AddCommGroup M]

/-- The IKNP sender's view and the receiver's output, completed from the reduction state
and the base-OT receiver's view and columns. -/
def iknpSenderFinish (H : Fin m → (Fin κ → Bool) → M) (st : IKNPRedState κ m M S)
    (e : VRB × (Fin κ → Fin m → Bool)) : IKNPSenderView κ m VRB × (Fin m → M) :=
  ((st.2.2.2.2, e.1, e.2),
    iknpRecvOut H st.2.2.1 st.2.2.2.1 (iknpSenderMsg H st.2.1 st.2.2.2.2 e.2))

/-- The IKNP receiver's view and output, completed from the reduction state and the
base-OT sender's view and the columns. -/
def iknpReceiverFinish (H : Fin m → (Fin κ → Bool) → M) (st : IKNPRedState κ m M S)
    (e : VSB × (Fin κ → Fin m → Bool)) : IKNPReceiverView κ m M VSB × (Fin m → M) :=
  ((st.2.2.2.1, e.1, iknpSenderMsg H st.2.1 st.2.2.2.2 e.2),
    iknpRecvOut H st.2.2.1 st.2.2.2.1 (iknpSenderMsg H st.2.1 st.2.2.2.2 e.2))

/-- Distinguisher of the sender-privacy reduction: `iknpGuessOf` at `iknpSenderFinish`. -/
noncomputable def iknpSenderGuess (H : Fin m → (Fin κ → Bool) → M)
    (g : S → IKNPSenderView κ m VRB × (Fin m → M) → SPComp Bool) :
    IKNPRedState κ m M S → VRB × (Fin κ → Fin m → Bool) → SPComp Bool :=
  iknpGuessOf (iknpSenderFinish H) g

/-- Distinguisher of the receiver-privacy reduction: `iknpGuessOf` at
`iknpReceiverFinish`. -/
noncomputable def iknpReceiverGuess (H : Fin m → (Fin κ → Bool) → M)
    (g : S → IKNPReceiverView κ m M VSB × (Fin m → M) → SPComp Bool) :
    IKNPRedState κ m M S → VSB × (Fin κ → Fin m → Bool) → SPComp Bool :=
  iknpGuessOf (iknpReceiverFinish H) g

/-- **Reduction to base-OT sender privacy.** The corrupted IKNP sender is the corrupted
base-OT receiver. -/
noncomputable def iknpSenderRed (H : Fin m → (Fin κ → Bool) → M)
    (A : OTAdversary m M (IKNPSenderView κ m VRB) S) :
    OTAdversary κ (Fin m → Bool) VRB (IKNPRedState κ m M S) :=
  ⟨iknpRedChoose A.choose, iknpSenderGuess H A.guess⟩

/-- **Reduction to base-OT receiver privacy.** The corrupted IKNP receiver is the corrupted
base-OT sender. -/
noncomputable def iknpReceiverRed (H : Fin m → (Fin κ → Bool) → M)
    (A : OTAdversary m M (IKNPReceiverView κ m M VSB) S) :
    OTAdversary κ (Fin m → Bool) VSB (IKNPRedState κ m M S) :=
  ⟨iknpRedChoose A.choose, iknpReceiverGuess H A.guess⟩

/-- The correlation-robust hash reduction over the column-pair map `bIn` and the view map
`view`: on a challenge `th`, run the input choice `c`, simulate the base-OT sender view on
the pairs `bIn th.1 r`, and run `g` on `view` of the inputs, the challenge and the
simulated view. -/
noncomputable def iknpCRRedOf {V O : Type}
    (bIn : (Fin m → Fin κ → Bool) → (Fin m → Bool) → Fin κ → (Fin m → Bool) × (Fin m → Bool))
    (view : (Fin m → M × M) × (Fin m → Bool) × S → (Fin m → Fin κ → Bool) × (Fin m → M) →
      VSB → V × O)
    (simSB : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → SPComp VSB)
    (c : SPComp ((Fin m → M × M) × (Fin m → Bool) × S)) (g : S → V × O → SPComp Bool)
    (th : (Fin m → Fin κ → Bool) × (Fin m → M)) : SPComp Bool :=
  SPComp.bind c fun i =>
    SPComp.bind (simSB (bIn th.1 i.2.1)) fun v => g i.2.2 (view i th v)

/-- The IKNP receiver's view in the correlation-robust hash reduction: the message pairs
carry `H j (T j)` at the choice and the challenge value `h j` at the other position; the
output is the ideal one. -/
def iknpCRView (H : Fin m → (Fin κ → Bool) → M) (i : (Fin m → M × M) × (Fin m → Bool) × S)
    (th : (Fin m → Fin κ → Bool) × (Fin m → M)) (v : VSB) :
    IKNPReceiverView κ m M VSB × (Fin m → M) :=
  ((th.1, v, fun j =>
    if i.2.1 j then ((i.1 j).1 + th.2 j, (i.1 j).2 + H j (th.1 j))
    else ((i.1 j).1 + H j (th.1 j), (i.1 j).2 + th.2 j)), otChoose i.1 i.2.1)

/-- **Reduction to correlation-robust hashing.** On a challenge `(T, h)`, run the input
choice `c`, simulate the base-OT sender view on the column pairs of `T`, and run `g` on the
message pairs with `H j (T j)` at the choice and `h j` at the other position, and the
ideal output. -/
noncomputable def iknpCRRed
    (simSB : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → SPComp VSB)
    (H : Fin m → (Fin κ → Bool) → M)
    (c : SPComp ((Fin m → M × M) × (Fin m → Bool) × S))
    (g : S → IKNPReceiverView κ m M VSB × (Fin m → M) → SPComp Bool) :
    (Fin m → Fin κ → Bool) × (Fin m → M) → SPComp Bool :=
  iknpCRRedOf iknpBaseIn (iknpCRView H) simSB c g

end Reductions

/-! ## Costed reductions -/

derive_reduction iknpRedChooseOf (adv := c)

derive_reduction iknpGuessOf (adv := g)

derive_reduction iknpCRRedOf (adv := c g)

/-- **Time of the input choice of the base-OT reductions**: the time of the costed input
choice `c` plus the two sample nodes drawing `T` and `s`. -/
theorem iknpRedChooseOf.tree.timeBound_timed
    (bIn : (Fin m → Fin κ → Bool) → (Fin m → Bool) → Fin κ → (Fin m → Bool) × (Fin m → Bool))
    (bInCost : (Fin m → Fin κ → Bool) → (Fin m → Bool) → Fin κ → ℕ)
    (c : SPTree.Timed ((Fin m → M × M) × (Fin m → Bool) × S)) :
    SPTree.Timed.stepTime (iknpRedChooseOf.tree.timed bIn bInCost c) ≤ c.time + 2 := by
  refine SPTree.Timed.stepTime_bind_le c _ 2 fun x => ?_
  simp [SPTree.Timed.stepTime, SPTree.Timed.time_sample, SPTree.Timed.time_ret,
    Finset.sup_const]

/-- **Time of the distinguisher of the base-OT reductions**: with `g` of time at most `T`
and call cost at most `a`, and the view map of cost at most `tf`, the costed distinguisher
has time at most `T + a + tf + 2`. -/
theorem iknpGuessOf.tree.timeBound_timed {E V O : Type}
    (fin : IKNPRedState κ m M S → E → V × O) (finCost : IKNPRedState κ m M S → E → ℕ)
    (g : S → V × O → SPTree.Timed Bool) (gCost : S → V × O → ℕ) {T a tf : ℕ}
    (hg : ∀ s y, (g s y).time ≤ T) (hgc : ∀ s y, gCost s y ≤ a)
    (hf : ∀ st e, finCost st e ≤ tf) (st : IKNPRedState κ m M S) (e : E) :
    SPTree.Timed.stepTime (iknpGuessOf.tree.timed fin finCost g gCost st e) ≤
      T + a + tf + 2 := by
  simp only [SPTree.Timed.stepTime, iknpGuessOf.tree.timed]
  have := hg st.1 (fin st e); have := hgc st.1 (fin st e); have := hf st e
  omega

/-- **Time of the correlation-robust hash reduction**: with the costed input choice `c`,
the costed base-OT sender simulator of time at most `Ts` and call cost at most `ts`, `g` of
time at most `T` and call cost at most `a`, and the view map of cost at most `tv`, the
costed reduction has time at most `c.time + Ts + ts + T + a + tv + 3`. -/
theorem iknpCRRedOf.tree.timeBound_timed {V O : Type}
    (bIn : (Fin m → Fin κ → Bool) → (Fin m → Bool) → Fin κ → (Fin m → Bool) × (Fin m → Bool))
    (bInCost : (Fin m → Fin κ → Bool) → (Fin m → Bool) → Fin κ → ℕ)
    (view : (Fin m → M × M) × (Fin m → Bool) × S → (Fin m → Fin κ → Bool) × (Fin m → M) →
      VSB → V × O)
    (viewCost : (Fin m → M × M) × (Fin m → Bool) × S → (Fin m → Fin κ → Bool) × (Fin m → M) →
      VSB → ℕ)
    (simSB : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → SPComp VSB)
    (simSBCost : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → ℕ)
    (c : SPTree.Timed ((Fin m → M × M) × (Fin m → Bool) × S))
    (g : S → V × O → SPTree.Timed Bool) (gCost : S → V × O → ℕ)
    (th : (Fin m → Fin κ → Bool) × (Fin m → M)) (fstCost : Fin m → Fin κ → ℕ)
    (simT : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → SPTree.Timed VSB)
    (simTCost : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → ℕ) {Ts ts T a tv : ℕ}
    (hs : ∀ p, (simT p).time ≤ Ts) (hsc : ∀ p, simTCost p ≤ ts)
    (hg : ∀ s y, (g s y).time ≤ T) (hgc : ∀ s y, gCost s y ≤ a)
    (hv : ∀ i t v, viewCost i t v ≤ tv) :
    SPTree.Timed.stepTime (iknpCRRedOf.tree.timed bIn bInCost view viewCost simSB simSBCost
      c g gCost th th.1 fstCost simT simTCost) ≤ c.time + Ts + ts + T + a + tv + 3 := by
  simp only [iknpCRRedOf.tree.timed]
  refine (SPTree.Timed.stepTime_bind_le c _ (Ts + ts + T + a + tv + 3) fun x => ?_).trans
    (by omega)
  rw [SPTree.Timed.stepTime_delay]
  have hb := SPTree.Timed.stepTime_bind_le (simT (bIn th.1 x.2.1))
    (fun y => (1 + (gCost x.2.2 (view x th y) + (1 + viewCost x th y)), g x.2.2 (view x th y)))
    (T + a + tv + 2) fun y => by
      simp only [SPTree.Timed.stepTime]
      have := hg x.2.2 (view x th y); have := hgc x.2.2 (view x th y); have := hv x th y
      omega
  have := hs (bIn th.1 x.2.1); have := hsc (bIn th.1 x.2.1)
  omega

/-- The costed input choice at `iknpBaseIn` erases and compiles to `iknpRedChoose` at the
erased input choice. -/
theorem iknpRedChoose.erase_timed
    (bInCost : (Fin m → Fin κ → Bool) → (Fin m → Bool) → Fin κ → ℕ)
    (c : SPTree.Timed ((Fin m → M × M) × (Fin m → Bool) × S)) :
    (iknpRedChooseOf.tree.timed iknpBaseIn bInCost c).2.erase.compile =
      iknpRedChoose c.erase.compile := by
  rw [iknpRedChooseOf.tree.erase_timed, iknpRedChooseOf.compile_tree]
  rfl

section CostedReductions

variable [AddCommGroup M]

/-- The costed distinguisher at `iknpSenderFinish H` erases and compiles to
`iknpSenderGuess H` at the erased distinguisher. -/
theorem iknpSenderGuess.erase_timed (H : Fin m → (Fin κ → Bool) → M)
    (finCost : IKNPRedState κ m M S → VRB × (Fin κ → Fin m → Bool) → ℕ)
    (g : S → IKNPSenderView κ m VRB × (Fin m → M) → SPTree.Timed Bool)
    (gCost : S → IKNPSenderView κ m VRB × (Fin m → M) → ℕ) (st : IKNPRedState κ m M S)
    (e : VRB × (Fin κ → Fin m → Bool)) :
    (iknpGuessOf.tree.timed (iknpSenderFinish H) finCost g gCost st e).2.erase.compile =
      iknpSenderGuess H (fun s y => (g s y).erase.compile) st e := by
  rw [iknpGuessOf.tree.erase_timed, iknpGuessOf.compile_tree]
  rfl

/-- The costed distinguisher at `iknpReceiverFinish H` erases and compiles to
`iknpReceiverGuess H` at the erased distinguisher. -/
theorem iknpReceiverGuess.erase_timed (H : Fin m → (Fin κ → Bool) → M)
    (finCost : IKNPRedState κ m M S → VSB × (Fin κ → Fin m → Bool) → ℕ)
    (g : S → IKNPReceiverView κ m M VSB × (Fin m → M) → SPTree.Timed Bool)
    (gCost : S → IKNPReceiverView κ m M VSB × (Fin m → M) → ℕ) (st : IKNPRedState κ m M S)
    (e : VSB × (Fin κ → Fin m → Bool)) :
    (iknpGuessOf.tree.timed (iknpReceiverFinish H) finCost g gCost st e).2.erase.compile =
      iknpReceiverGuess H (fun s y => (g s y).erase.compile) st e := by
  rw [iknpGuessOf.tree.erase_timed, iknpGuessOf.compile_tree]
  rfl

/-- The costed correlation-robust hash reduction at `iknpBaseIn` and `iknpCRView H`, with a
costed simulator `simT` that compiles to `simSB`, erases and compiles to `iknpCRRed` at the
erased input choice and distinguisher. -/
theorem iknpCRRed.erase_timed (H : Fin m → (Fin κ → Bool) → M)
    (bInCost : (Fin m → Fin κ → Bool) → (Fin m → Bool) → Fin κ → ℕ)
    (viewCost : (Fin m → M × M) × (Fin m → Bool) × S → (Fin m → Fin κ → Bool) × (Fin m → M) →
      VSB → ℕ)
    (simSB : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → SPComp VSB)
    (simSBCost : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → ℕ)
    (c : SPTree.Timed ((Fin m → M × M) × (Fin m → Bool) × S))
    (g : S → IKNPReceiverView κ m M VSB × (Fin m → M) → SPTree.Timed Bool)
    (gCost : S → IKNPReceiverView κ m M VSB × (Fin m → M) → ℕ)
    (th : (Fin m → Fin κ → Bool) × (Fin m → M)) (fstCost : Fin m → Fin κ → ℕ)
    (simT : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → SPTree.Timed VSB)
    (simTCost : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → ℕ)
    (hsim : ∀ p, (simT p).erase.compile = simSB p) :
    (iknpCRRedOf.tree.timed iknpBaseIn bInCost (iknpCRView H) viewCost simSB simSBCost c g
      gCost th th.1 fstCost simT simTCost).2.erase.compile =
      iknpCRRed simSB H c.erase.compile (fun s y => (g s y).erase.compile) th := by
  rw [iknpCRRedOf.tree.erase_timed, iknpCRRedOf.compile_tree _ _ _ _ _ _ _ hsim]
  rfl

end CostedReductions

/-! ## Security -/

section Security

variable [AddCommGroup M] [Fintype M] [Nonempty M]

omit [Fintype M] [Nonempty M] in
/-- **Receiver privacy of IKNP.** For every adversary `A` corrupting the sender, the
receiver-privacy advantage against `iknp B H` with the simulator `iknpSimS simRB` equals the
sender-privacy advantage of `iknpSenderRed H A` against the base OTs `B` with the
simulator `simRB`. -/
theorem iknp_recvPriv_eq (B : OTScheme κ (Fin m → Bool) VSB VRB)
    (simRB : (Fin κ → Bool) → (Fin κ → Fin m → Bool) → SPComp VRB)
    (H : Fin m → (Fin κ → Bool) → M) (A : OTAdversary m M (IKNPSenderView κ m VRB) S) :
    otRecvPrivAdvantage (iknp B H) (iknpSimS simRB) A =
      otSendPrivAdvantage B simRB (iknpSenderRed H A) := by
  have hreal : otRecvPrivReal (iknp B H) A = otSendPrivReal B (iknpSenderRed H A) := by
    simp only [otRecvPrivReal, otSendPrivReal, iknp, iknpSenderRed, iknpRedChoose,
      iknpRedChooseOf, iknpSenderGuess, iknpGuessOf, iknpSenderFinish, SPComp.bind_assoc,
      SPComp.pure_bind]
  have hideal :
      otRecvPrivIdeal (iknpSimS simRB) A = otSendPrivIdeal simRB (iknpSenderRed H A) := by
    simp only [otRecvPrivIdeal, otSendPrivIdeal, iknpSimS, iknpSenderRed, iknpRedChoose,
      iknpRedChooseOf, iknpSenderGuess, iknpGuessOf, iknpSenderFinish, SPComp.bind_assoc,
      SPComp.pure_bind, iknpRecvOut_otChoose]
    simp only [otChoose_iknpBaseIn]
    congr 1
    funext i
    rw [SPComp.isPure_bind_comm (SPComp.sample (Fin m → Fin κ → Bool))
      (SPComp.sample (Fin κ → Bool)) _ (SPComp.sample_isPure _) (SPComp.sample_isPure _)]
    congr 1
    funext s
    exact (SPComp.sample_bind_equiv (Equiv.addRight (iknpShift i.2.1 s)) fun T =>
      SPComp.bind (simRB s fun a b => T b a) fun v =>
        A.guess i.2.2 ((s, v, fun a b => T b a), otChoose i.1 i.2.1)).symm
  unfold otRecvPrivAdvantage otSendPrivAdvantage
  rw [hreal, hideal]

/-- **Sender privacy of IKNP.** For every adversary `A` corrupting the receiver, the
sender-privacy advantage against `iknp B H` with the simulator `iknpSimR simSB H` is at
most the receiver-privacy advantage of `iknpReceiverRed H A` against the base OTs `B` with
the simulator `simSB`, plus the correlation-robust hash advantage of
`iknpCRRed simSB H A.choose A.guess`. -/
theorem iknp_sendPriv_le (B : OTScheme κ (Fin m → Bool) VSB VRB)
    (simSB : (Fin κ → (Fin m → Bool) × (Fin m → Bool)) → SPComp VSB)
    (H : Fin m → (Fin κ → Bool) → M) (A : OTAdversary m M (IKNPReceiverView κ m M VSB) S) :
    otSendPrivAdvantage (iknp B H) (iknpSimR simSB H) A ≤
      otRecvPrivAdvantage B simSB (iknpReceiverRed H A) +
        CRHash_Advantage H (iknpCRRed simSB H A.choose A.guess) := by
  have hreal : otSendPrivReal (iknp B H) A = otRecvPrivReal B (iknpReceiverRed H A) := by
    simp only [otRecvPrivReal, otSendPrivReal, iknp, iknpReceiverRed, iknpRedChoose,
      iknpRedChooseOf, iknpReceiverGuess, iknpGuessOf, iknpReceiverFinish, SPComp.bind_assoc,
      SPComp.pure_bind]
  have hmid : otRecvPrivIdeal simSB (iknpReceiverRed H A) =
      SPComp.bind (crHashReal H) (iknpCRRed simSB H A.choose A.guess) := by
    simp only [otRecvPrivIdeal, crHashReal, iknpReceiverRed, iknpRedChoose, iknpRedChooseOf,
      iknpReceiverGuess, iknpGuessOf, iknpReceiverFinish, iknpCRRed, iknpCRRedOf, iknpCRView,
      SPComp.bind_assoc, SPComp.pure_bind, iknpRecvOut_otChoose]
    simp only [iknpSenderMsg_otChoose,
      SPComp.isPure_bind_comm_left _ A.choose _ (SPComp.sample_isPure _)]
  have hideal : otSendPrivIdeal (iknpSimR simSB H) A =
      SPComp.bind crHashIdeal (iknpCRRed simSB H A.choose A.guess) := by
    simp only [otSendPrivIdeal, crHashIdeal, iknpSimR, iknpCRRed, iknpCRRedOf, iknpCRView,
      SPComp.bind_assoc,
      SPComp.pure_bind, SPComp.isPure_bind_comm_left _ A.choose _ (SPComp.sample_isPure _)]
    simp only [SPComp.isPure_bind_comm_left (SPComp.sample (Fin m → M)) _ _
      (SPComp.sample_isPure _)]
    congr 1
    funext i
    congr 1
    funext T
    congr 1
    funext v
    rw [← SPComp.sample_bind_equiv
      (Equiv.addLeft fun j => if i.2.1 j then (i.1 j).1 else (i.1 j).2)]
    congr 1
    funext h
    congr 4
    funext j
    by_cases hr : i.2.1 j <;> simp [hr, otChoose]
  unfold otSendPrivAdvantage otRecvPrivAdvantage CRHash_Advantage AdvantageA
  rw [hreal, hideal, ← hmid]
  exact advantage_triangle _ _ _

end Security

end CatCrypt.Crypto.OT
