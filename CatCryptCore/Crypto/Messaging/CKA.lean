/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.CyclicGroupDDH
public import CatCryptCore.Crypto.Messaging.FSPRG

/-!
# Continuous key agreement

A continuous key agreement (CKA) scheme is a two-party protocol run in epochs: in each epoch
one party sends a message `T` and derives a key `I`, the other party receives `T` and derives
the same key, and the roles alternate (Alwen, Coretti and Dodis, Definition 12). The CKA game
gives the adversary the public value of the initialisation, the transcript of `k` epochs, the
message of the challenge epoch together with either its key or a uniform key, and the
transcript of `m` further epochs.

The Diffie–Hellman instance `dhCKA` over a cyclic group is the asymmetric ratchet of Signal:
the sender samples an exponent `x`, sends `g^x` and derives `h^x` from the last public value
`h` of the peer. Its CKA advantage equals the DDH advantage of the reduction `ckaDDHRed`.

## Main definitions

* `CKADef` — a CKA scheme: initialisation, sending and receiving
* `ckaRun` — the transcript and the final states of a run of epochs
* `cka_real`, `cka_ideal`, `CKA_Advantage` — the CKA game with challenge epoch `k + 1`
* `dhCKA` — the Diffie–Hellman CKA scheme
* `dhChain`, `dhChainTo`, `dhPreView` — the transcripts of `dhCKA` as functions of the
  exponents
* `ckaDDHView`, `ckaDDHRedOf`, `ckaDDHRed` — the DDH distinguisher built from a CKA adversary

## Main results

* `dhCKA_recv_key` — correctness: the receiver derives the key of the sender
* `ckaRun_dh_pre`, `ckaRun_dh_tail` — runs of `dhCKA` sample one exponent per epoch
* `cka_real_dh`, `cka_ideal_dh` — the games of `dhCKA` sample the exponents of all epochs
* `cka_real_dh_bind`, `cka_ideal_dh_bind` — the CKA games of `dhCKA` are the DDH games of
  `ckaDDHRed`
* `cka_advantage_eq_ddh` — for every adversary `A`, the CKA advantage of `dhCKA` equals the
  DDH advantage of `ckaDDHRed k m A`
* `ckaDDHRedOf.tree.timeBound_timed` — the time of the costed reduction

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4.2 and §5.1
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

/-! ## CKA schemes and the CKA game -/

/-- A continuous key agreement scheme with party states `St`, messages `Msg` and keys `Key`.

* `init` — the public value of the initialisation and the initial states of the first sender
  and of the first receiver;
* `send` — the sender's next state, the message and the key of the epoch;
* `recv` — the receiver's next state and the key it derives from the message. -/
structure CKADef (St Msg Key : Type) where
  /-- Initialisation: public value, state of the first sender, state of the first receiver. -/
  init : SPComp (Msg × St × St)
  /-- Sending: next state, message, key. -/
  send : St → SPComp (St × Msg × Key)
  /-- Receiving: next state and key from the received message. -/
  recv : St → Msg → St × Key

/-- The view of the CKA adversary: the public value of the initialisation, the transcript of
the epochs before the challenge, the challenge message and key, and the transcript of the
epochs after the challenge. -/
abbrev CKAView (Msg Key : Type) := Msg × List (Msg × Key) × (Msg × Key) × List (Msg × Key)

variable {St Msg Key : Type}

/-- `n` epochs of `C` from the sender state `s` and the receiver state `r`: the messages and
keys of the epochs, and the states of the next sender and of the next receiver. The receiver
of an epoch sends in the next one. -/
noncomputable def ckaRun (C : CKADef St Msg Key) :
    ℕ → St → St → SPComp (List (Msg × Key) × St × St)
  | 0, s, r => SPComp.pure ([], s, r)
  | n + 1, s, r =>
    SPComp.bind (C.send s) fun o =>
      SPComp.bind (ckaRun C n (C.recv r o.2.1).1 o.1) fun p =>
        SPComp.pure ((o.2.1, o.2.2) :: p.1, p.2)

/-- CKA real game: `k` epochs, the challenge epoch with its key, `m` epochs. -/
noncomputable def cka_real (C : CKADef St Msg Key) (k m : ℕ) : SPComp (CKAView Msg Key) :=
  SPComp.bind C.init fun i =>
    SPComp.bind (ckaRun C k i.2.1 i.2.2) fun p =>
      SPComp.bind (C.send p.2.1) fun o =>
        SPComp.bind (ckaRun C m (C.recv p.2.2 o.2.1).1 o.1) fun q =>
          SPComp.pure (i.1, p.1, (o.2.1, o.2.2), q.1)

/-- CKA ideal game: the key of the challenge epoch is uniform. -/
noncomputable def cka_ideal [Fintype Key] [Nonempty Key] (C : CKADef St Msg Key) (k m : ℕ) :
    SPComp (CKAView Msg Key) :=
  SPComp.bind C.init fun i =>
    SPComp.bind (ckaRun C k i.2.1 i.2.2) fun p =>
      SPComp.bind (C.send p.2.1) fun o =>
        SPComp.bind (SPComp.sample Key) fun u =>
          SPComp.bind (ckaRun C m (C.recv p.2.2 o.2.1).1 o.1) fun q =>
            SPComp.pure (i.1, p.1, (o.2.1, u), q.1)

/-- CKA advantage of the distinguisher `A` at the challenge epoch `k + 1`, with `m` epochs
after it. -/
noncomputable def CKA_Advantage [Fintype Key] [Nonempty Key] (C : CKADef St Msg Key)
    (k m : ℕ) (A : CKAView Msg Key → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (cka_real C k m) (cka_ideal C k m) A

/-! ## The Diffie–Hellman instance -/

section DH

variable (G : Type) [CG : CyclicGroup G]

/-- The Diffie–Hellman CKA scheme. A party state `(h, y)` holds the last public value `h` of
the peer, used when sending, and the own last exponent `y`, used when receiving. Sending
samples `x` and outputs `g^x` with the key `h^x`; receiving `T` derives `T^y`. -/
noncomputable def dhCKA : CKADef (G × CG.Exp) G G where
  init := SPComp.bind (SPComp.sample CG.Exp) fun x =>
    SPComp.pure (CG.pow x, (CG.pow x, x), (CG.pow x, x))
  send s := SPComp.bind (SPComp.sample CG.Exp) fun x =>
    SPComp.pure ((s.1, x), CG.pow x, CyclicGroup.elemPow s.1 x)
  recv r T := ((T, r.2), CyclicGroup.elemPow T r.2)

variable {G}

/-- Exponentiation of group elements commutes: `(g^x)^y = (g^y)^x`. -/
theorem elemPow_pow_comm (x y : CG.Exp) :
    CyclicGroup.elemPow (CG.pow x) y = CyclicGroup.elemPow (CG.pow y) x := by
  rw [CyclicGroup.elemPow_pow, CyclicGroup.elemPow_pow, CG.pow_comm]

/-- **Correctness of `dhCKA`.** The receiver with exponent `y` derives from the message
`g^x` the key `(g^y)^x` that a sender holding the public value `g^y` derives. -/
theorem dhCKA_recv_key (h : G) (x y : CG.Exp) :
    ((dhCKA G).recv (h, y) (CG.pow x)).2 = CyclicGroup.elemPow (CG.pow y) x :=
  elemPow_pow_comm x y

/-- The transcript of `dhCKA` epochs from a sender that holds the public value `h`, with the
fresh exponents `xs` of the senders. -/
noncomputable def dhChain : G → List CG.Exp → List (G × G)
  | _, [] => []
  | h, x :: xs => (CG.pow x, CyclicGroup.elemPow h x) :: dhChain (CG.pow x) xs

/-- The last exponent of the list `y :: xs`. -/
def lastExp {E : Type} : E → List E → E
  | y, [] => y
  | _, x :: xs => lastExp x xs

/-- The transcript of `dhCKA` epochs from the exponent `y` with the fresh exponents `xs`,
followed by the epoch whose message is `A`: its key is `A^z` for the last exponent `z` of
`y :: xs`. -/
noncomputable def dhChainTo : CG.Exp → List CG.Exp → G → List (G × G)
  | y, [], A => [(A, CyclicGroup.elemPow A y)]
  | y, x :: xs, A => (CG.pow x, CyclicGroup.elemPow (CG.pow y) x) :: dhChainTo x xs A

/-- The public value of the initialisation and the transcript of the epochs before the
challenge, when the exponents of the initialisation and of these epochs are `u` followed by
an exponent with public value `A`. -/
noncomputable def dhPreView (A : G) : List CG.Exp → G × List (G × G)
  | [] => (A, [])
  | x :: xs => (CG.pow x, dhChainTo x xs A)

/-- The view of the CKA adversary built from the DDH triple `(g^a, g^b, z)`, the exponents `u`
of the initialisation and of the first `k - 1` epochs, and the exponents `w` of the `m`
epochs after the challenge. -/
noncomputable def ckaDDHView (k m : ℕ) (u : Fin k → CG.Exp) (w : Fin m → CG.Exp)
    (t : G × G × G) : CKAView G G :=
  ((dhPreView t.1 (List.ofFn u)).1, (dhPreView t.1 (List.ofFn u)).2, (t.2.1, t.2.2),
    dhChain t.2.1 (List.ofFn w))

/-- The distinguisher with the view function `view`: on the challenge `t` it samples two
uniform vectors `u` and `w` and calls `A` on `view u w t`. -/
noncomputable def ckaDDHRedOf {E T V : Type} [Fintype E] [Nonempty E] {k m : ℕ}
    (view : (Fin k → E) → (Fin m → E) → T → V) (A : V → SPComp Bool) (t : T) :
    SPComp Bool := do
  let u ← SPComp.sample (Fin k → E)
  let w ← SPComp.sample (Fin m → E)
  A (view u w t)

/-- The DDH distinguisher built from the CKA adversary `A`: on the triple `(g^a, g^b, z)` it
samples the exponents of the initialisation and of the first `k - 1` epochs, uses `g^a` as the
message of epoch `k`, `(g^b, z)` as the challenge, and samples the exponents of the `m` epochs
after it. -/
noncomputable def ckaDDHRed (k m : ℕ) (A : CKAView G G → SPComp Bool) :
    G × G × G → SPComp Bool :=
  ckaDDHRedOf (ckaDDHView k m) A

/-- The epochs after the challenge: the transcript of `m` epochs of `dhCKA` depends on the
sender state only through its public value, and is `dhChain` of `m` uniform exponents. -/
theorem ckaRun_dh_tail {β : Type} (m : ℕ) (s r : G × CG.Exp)
    (K : List (G × G) → SPComp β) :
    SPComp.bind (ckaRun (dhCKA G) m s r) (fun q => K q.1) =
      SPComp.bind (SPComp.sample (Fin m → CG.Exp)) (fun w => K (dhChain s.1 (List.ofFn w))) := by
  induction m generalizing s r K with
  | zero =>
    simp only [ckaRun, SPComp.pure_bind, sample_bind_unique, List.ofFn_zero, dhChain]
  | succ n ih =>
    rw [← SPComp.sample_bind_equiv (Fin.consEquiv fun _ => CG.Exp)]
    have he : ∀ (a : CG.Exp) (v : Fin n → CG.Exp), (Fin.consEquiv fun _ => CG.Exp) (a, v) =
        Fin.cons (α := fun _ => CG.Exp) a v := fun _ _ => rfl
    simp only [ckaRun, dhCKA, SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind, he,
      ofFn_cons, dhChain]
    congr 1; funext x
    exact ih (CG.pow x, r.2) (s.1, x) (fun l => K ((CG.pow x, CyclicGroup.elemPow s.1 x) :: l))

/-- The epochs before the challenge: from a sender holding `g^y` and a receiver holding `y`,
the transcript of `k` epochs of `dhCKA`, the public value of the next sender and the exponent
of the next receiver are given by `k` uniform exponents. -/
theorem ckaRun_dh_pre {β : Type} (k : ℕ) (s r : G × CG.Exp) (hs : s.1 = CG.pow r.2)
    (K : List (G × G) → G → CG.Exp → SPComp β) :
    SPComp.bind (ckaRun (dhCKA G) k s r) (fun p => K p.1 p.2.1.1 p.2.2.2) =
      SPComp.bind (SPComp.sample (Fin k → CG.Exp)) (fun v =>
        K (dhChain s.1 (List.ofFn v)) (CG.pow (lastExp r.2 (List.ofFn v)))
          (lastExp r.2 (List.ofFn v))) := by
  induction k generalizing s r K with
  | zero =>
    simp only [ckaRun, SPComp.pure_bind, sample_bind_unique, List.ofFn_zero, dhChain, lastExp,
      hs]
  | succ n ih =>
    rw [← SPComp.sample_bind_equiv (Fin.consEquiv fun _ => CG.Exp)]
    have he : ∀ (a : CG.Exp) (v : Fin n → CG.Exp), (Fin.consEquiv fun _ => CG.Exp) (a, v) =
        Fin.cons (α := fun _ => CG.Exp) a v := fun _ _ => rfl
    simp only [ckaRun, dhCKA, SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind, he,
      ofFn_cons, dhChain, lastExp]
    congr 1; funext x
    exact ih (CG.pow x, r.2) (s.1, x) rfl
      (fun l h y => K ((CG.pow x, CyclicGroup.elemPow s.1 x) :: l) h y)

/-- The real CKA game of `dhCKA` samples the exponents of the initialisation, of the `k`
epochs before the challenge, of the challenge and of the `m` epochs after it. -/
theorem cka_real_dh (k m : ℕ) :
    cka_real (dhCKA G) k m =
      SPComp.bind (SPComp.sample CG.Exp) fun x₀ =>
        SPComp.bind (SPComp.sample (Fin k → CG.Exp)) fun v =>
          SPComp.bind (SPComp.sample CG.Exp) fun x =>
            SPComp.bind (SPComp.sample (Fin m → CG.Exp)) fun w =>
              SPComp.pure (CG.pow x₀, dhChain (CG.pow x₀) (List.ofFn v),
                (CG.pow x, CyclicGroup.elemPow (CG.pow (lastExp x₀ (List.ofFn v))) x),
                dhChain (CG.pow x) (List.ofFn w)) := by
  simp only [cka_real, dhCKA, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext x₀
  refine Eq.trans ?_ (ckaRun_dh_pre k (CG.pow x₀, x₀) (CG.pow x₀, x₀) rfl
    (fun l h _ => SPComp.bind (SPComp.sample CG.Exp) fun x =>
      SPComp.bind (SPComp.sample (Fin m → CG.Exp)) fun w =>
        SPComp.pure (CG.pow x₀, l, (CG.pow x, CyclicGroup.elemPow h x),
          dhChain (CG.pow x) (List.ofFn w))))
  congr 1; funext p; congr 1; funext x
  exact ckaRun_dh_tail m _ _
    (fun l => SPComp.pure (CG.pow x₀, p.1, (CG.pow x, CyclicGroup.elemPow p.2.1.1 x), l))

/-- The ideal CKA game of `dhCKA`: as `cka_real_dh` with a uniform challenge key. -/
theorem cka_ideal_dh (k m : ℕ) :
    cka_ideal (dhCKA G) k m =
      SPComp.bind (SPComp.sample CG.Exp) fun x₀ =>
        SPComp.bind (SPComp.sample (Fin k → CG.Exp)) fun v =>
          SPComp.bind (SPComp.sample CG.Exp) fun x =>
            SPComp.bind (SPComp.sample G) fun z =>
              SPComp.bind (SPComp.sample (Fin m → CG.Exp)) fun w =>
                SPComp.pure (CG.pow x₀, dhChain (CG.pow x₀) (List.ofFn v), (CG.pow x, z),
                  dhChain (CG.pow x) (List.ofFn w)) := by
  simp only [cka_ideal, dhCKA, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext x₀
  refine Eq.trans ?_ (ckaRun_dh_pre k (CG.pow x₀, x₀) (CG.pow x₀, x₀) rfl
    (fun l _ _ => SPComp.bind (SPComp.sample CG.Exp) fun x =>
      SPComp.bind (SPComp.sample G) fun z =>
        SPComp.bind (SPComp.sample (Fin m → CG.Exp)) fun w =>
          SPComp.pure (CG.pow x₀, l, (CG.pow x, z), dhChain (CG.pow x) (List.ofFn w))))
  congr 1; funext p; congr 1; funext x; congr 1; funext z
  exact ckaRun_dh_tail m _ _ (fun l => SPComp.pure (CG.pow x₀, p.1, (CG.pow x, z), l))

/-- The epoch with message `g^a` closes the chain of the exponents `xs` from `y`. -/
theorem dhChain_append_singleton (y a : CG.Exp) (xs : List CG.Exp) :
    dhChain (CG.pow y) (xs ++ [a]) = dhChainTo y xs (CG.pow a) := by
  induction xs generalizing y with
  | nil => simp only [List.nil_append, dhChain, dhChainTo, elemPow_pow_comm]
  | cons x xs ih => simp only [List.cons_append, dhChain, dhChainTo, ih]

/-- The last exponent of `y :: xs ++ [a]` is `a`. -/
theorem lastExp_append_singleton {E : Type} (y a : E) (xs : List E) :
    lastExp y (xs ++ [a]) = a := by
  induction xs generalizing y with
  | nil => rfl
  | cons x xs ih => exact ih x

/-- The exponents `x₀ :: vs = u ++ [a]` give the view `dhPreView (g^a) u`, and their last
exponent is `a`. -/
theorem dhPreView_eq (u : List CG.Exp) (a x₀ : CG.Exp) (vs : List CG.Exp)
    (h : x₀ :: vs = u ++ [a]) :
    dhPreView (CG.pow a) u = (CG.pow x₀, dhChain (CG.pow x₀) vs) ∧ lastExp x₀ vs = a := by
  cases u with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | cons u₀ us =>
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp only [dhPreView, dhChain_append_singleton], lastExp_append_singleton _ _ _⟩

omit CG in
/-- Sampling a first element and a vector of `k` further elements is sampling a vector of `k`
elements and a last element: the pair `(x₀, v)` is the split at the front of `Fin.snoc u a`. -/
theorem bind_sample_split_snoc {E β : Type} [Fintype E] [Nonempty E] (k : ℕ)
    (F : E → (Fin k → E) → SPComp β) :
    SPComp.bind (SPComp.sample E) (fun x₀ =>
        SPComp.bind (SPComp.sample (Fin k → E)) fun v => F x₀ v) =
      SPComp.bind (SPComp.sample E) fun a =>
        SPComp.bind (SPComp.sample (Fin k → E)) fun u =>
          F ((Fin.consEquiv fun _ => E).symm (Fin.snoc (α := fun _ => E) u a)).1
            ((Fin.consEquiv fun _ => E).symm (Fin.snoc (α := fun _ => E) u a)).2 := by
  have h := SPComp.sample_bind_equiv
    ((Fin.snocEquiv fun _ => E).trans (Fin.consEquiv fun _ => E).symm) (fun p => F p.1 p.2)
  simp only [SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind] at h
  exact h.symm

omit CG in
/-- The front split `(x₀, v)` of a vector `f` of length `k + 1` lists as `f`. -/
theorem cons_ofFn_consEquiv_symm {E : Type} {k : ℕ} (f : Fin (k + 1) → E) :
    ((Fin.consEquiv fun _ => E).symm f).1 :: List.ofFn ((Fin.consEquiv fun _ => E).symm f).2 =
      List.ofFn f := by
  rw [← ofFn_cons]
  exact congrArg List.ofFn ((Fin.consEquiv fun _ => E).apply_symm_apply f)

/-- The real CKA game of `dhCKA` is the real DDH game of `ckaDDHRed`. -/
theorem cka_real_dh_bind (k m : ℕ) (A : CKAView G G → SPComp Bool) :
    (cka_real (dhCKA G) k m).bind A = (DDH_real G).bind (ckaDDHRed k m A) := by
  rw [cka_real_dh]
  simp only [SPComp.bind_assoc, SPComp.pure_bind]
  refine (bind_sample_split_snoc k _).trans ?_
  simp only [DDH_real, ckaDDHRed, ckaDDHRedOf, ckaDDHView, SPComp.monad_bind_eq,
    SPComp.monad_pure_eq,
    SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext a
  rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure (Fin k → CG.Exp))]
  congr 1; funext x; congr 1; funext u; congr 1; funext w
  obtain ⟨h1, h2⟩ := dhPreView_eq (List.ofFn u) a _ _
    ((cons_ofFn_consEquiv_symm _).trans (ofFn_snoc u a))
  simp only [h1, h2, CyclicGroup.elemPow_pow]

/-- The ideal CKA game of `dhCKA` is the ideal DDH game of `ckaDDHRed`. -/
theorem cka_ideal_dh_bind (k m : ℕ) (A : CKAView G G → SPComp Bool) :
    (cka_ideal (dhCKA G) k m).bind A = (DDH_ideal G).bind (ckaDDHRed k m A) := by
  rw [cka_ideal_dh]
  simp only [SPComp.bind_assoc, SPComp.pure_bind]
  refine (bind_sample_split_snoc k _).trans ?_
  simp only [DDH_ideal, ckaDDHRed, ckaDDHRedOf, ckaDDHView, SPComp.monad_bind_eq,
    SPComp.monad_pure_eq,
    SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext a
  rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure (Fin k → CG.Exp))]
  congr 1; funext x
  rw [SPComp.isPure_bind_comm_left (SPComp.sample CG.Exp) (SPComp.sample (Fin k → CG.Exp)) _
    (SPComp.sample_isPure _)]
  congr 1; funext u
  rw [← SPComp.sample_bind_equiv (Equiv.ofBijective CG.pow CG.pow_bij)]
  simp only [Equiv.ofBijective_apply]
  congr 1; funext c; congr 1; funext w
  obtain ⟨h1, -⟩ := dhPreView_eq (List.ofFn u) a _ _
    ((cons_ofFn_consEquiv_symm _).trans (ofFn_snoc u a))
  simp only [h1]

/-- **CKA security of `dhCKA` from DDH.** For every adversary `A`, challenge epoch `k + 1` and
`m` epochs after it, the CKA advantage of `dhCKA` equals the DDH advantage of
`ckaDDHRed k m A`. -/
theorem cka_advantage_eq_ddh (k m : ℕ) (A : CKAView G G → SPComp Bool) :
    CKA_Advantage (dhCKA G) k m A = DDH_Advantage G (ckaDDHRed k m A) := by
  unfold CKA_Advantage DDH_Advantage AdvantageA
  rw [cka_real_dh_bind, cka_ideal_dh_bind]

end DH

/-! ## The costed reduction -/

derive_reduction ckaDDHRedOf (adv := A)

/-- **Time of the DDH reduction.** With the costed adversary `A` of time at most `T` and call
cost at most `a`, and the view function of cost at most `tv`, the costed reduction has time at
most `T + a + tv + 4`: two samples of exponent vectors, one view and one adversary call. For
`ckaDDHRed k m A` the view is `ckaDDHView k m`, whose cost is that of the exponentiations of
`k + m + 1` epochs. -/
theorem ckaDDHRedOf.tree.timeBound_timed {E T' V : Type} [Fintype E] [Nonempty E] {k m : ℕ}
    (view : (Fin k → E) → (Fin m → E) → T' → V)
    (viewCost : (Fin k → E) → (Fin m → E) → T' → ℕ)
    (A : V → SPTree.Timed Bool) (ACost : V → ℕ)
    {T a tv : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hv : ∀ u w t, viewCost u w t ≤ tv) (t : T') :
    SPTree.Timed.stepTime (ckaDDHRedOf.tree.timed view viewCost A ACost t) ≤
      T + a + tv + 4 := by
  simp only [SPTree.Timed.stepTime, ckaDDHRedOf.tree.timed, zero_add]
  refine (timedSample_time_le _ _ _ _ _ (T + a + tv + 3) fun u => ?_).trans
    (by omega)
  rw [zero_add]
  refine (timedSample_time_le _ _ _ _ _ (T + a + tv + 2) fun w => ?_).trans
    (by omega)
  have := hA (view u w t); have := hAc (view u w t); have := hv u w t
  omega

/-- The costed form of `ckaDDHRed k m`: the costed tree of `ckaDDHRedOf` at the view
`ckaDDHView k m` of cost `viewCost`. -/
noncomputable def ckaDDHRed.timed {G : Type} [CG : CyclicGroup G] (k m : ℕ)
    (viewCost : (Fin k → CG.Exp) → (Fin m → CG.Exp) → G × G × G → ℕ)
    (A : CKAView G G → SPTree.Timed Bool) (ACost : CKAView G G → ℕ) (t : G × G × G) :
    ℕ × SPTree.Timed Bool :=
  ckaDDHRedOf.tree.timed (ckaDDHView k m) viewCost A ACost t

/-- The costed form of `ckaDDHRed` erases and compiles to `ckaDDHRed` at the erased
adversary. -/
theorem ckaDDHRed.erase_timed {G : Type} [CG : CyclicGroup G] (k m : ℕ)
    (viewCost : (Fin k → CG.Exp) → (Fin m → CG.Exp) → G × G × G → ℕ)
    (A : CKAView G G → SPTree.Timed Bool) (ACost : CKAView G G → ℕ) (t : G × G × G) :
    (ckaDDHRed.timed k m viewCost A ACost t).2.erase.compile =
      ckaDDHRed k m (fun x => (A x).erase.compile) t := by
  rw [ckaDDHRed.timed, ckaDDHRedOf.tree.erase_timed, ckaDDHRedOf.compile_tree]
  rfl

/-- **Time of `ckaDDHRed`**, the bound of `ckaDDHRedOf.tree.timeBound_timed` at the view
`ckaDDHView k m` of cost at most `tv`. -/
theorem ckaDDHRed.timeBound_timed {G : Type} [CG : CyclicGroup G] (k m : ℕ)
    (viewCost : (Fin k → CG.Exp) → (Fin m → CG.Exp) → G × G × G → ℕ)
    (A : CKAView G G → SPTree.Timed Bool) (ACost : CKAView G G → ℕ) {T a tv : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (hv : ∀ u w t, viewCost u w t ≤ tv)
    (t : G × G × G) :
    SPTree.Timed.stepTime (ckaDDHRed.timed k m viewCost A ACost t) ≤ T + a + tv + 4 :=
  ckaDDHRedOf.tree.timeBound_timed _ viewCost A ACost hA hAc hv t

end CatCrypt.Crypto.Messaging
