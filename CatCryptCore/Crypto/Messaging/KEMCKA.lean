/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.CKA
public import CatCryptCore.Examples.KEMDEM

/-!
# Continuous key agreement from a KEM, and the product of two CKA schemes

The KEM CKA `kemCKA KEM` follows Alwen, Coretti and Dodis, §4.1: a party state holds the last
encapsulation key of the peer, used when sending, and the own last decapsulation key, used
when receiving; sending encapsulates a key under the peer's encapsulation key and sends the
encapsulation together with a fresh encapsulation key. Its CKA advantage equals the KEM-CPA
advantage (`CatCrypt.Examples.KEMDEM.KEM_CPA_Advantage`) of the reduction `kemCKARed`, which
embeds the challenge encapsulation key as the fresh key of the epoch before the challenge.

The product `prodCKA C₁ C₂` runs two CKA schemes side by side; its messages and keys are
pairs. Its CKA advantage is at most the CKA advantage of `C₁` at `prodCKARed₁` plus that of
`C₂` at `prodCKARed₂` (a hybrid over the two components of the challenge key). A bound by one
component alone does not hold for a pair key: the adversary sees both components.

## Main definitions

* `ckaPubRedOf` — the distinguisher that runs a public computation and calls the adversary on
  a view of its result and of the challenge
* `kemCKA` — the CKA of a KEM
* `kemRun`, `kemPre`, `kemPreRaw`, `kemPreView` — the public transcript of `kemCKA` runs
* `kemCKAPub`, `kemCKAView`, `kemCKARed` — the KEM-CPA reduction
* `prodCKA` — two CKA schemes side by side
* `zipT`, `zipView` — the transcripts and views of the product
* `prodHyb` — the hybrid game: ideal game of `C₁`, real game of `C₂`
* `prodCKARed₁`, `prodCKARed₂` — the reductions of the product to its components

## Main results

* `kemCKA_advantage_eq` — for every adversary `A`, the CKA advantage of `kemCKA KEM` equals
  the KEM-CPA advantage of `kemCKARed KEM k m A`, for a KEM whose key generation and
  encapsulation do not touch the heap
* `prodCKA_advantage_le` — for every adversary `A`, the CKA advantage of `prodCKA C₁ C₂` is at
  most the CKA advantage of `C₁` at `prodCKARed₁` plus that of `C₂` at `prodCKARed₂`, when the
  initialisation and sending of `C₁` do not touch the heap
* `dhKemCKA_advantage_le` — for every adversary `A`, the CKA advantage of
  `prodCKA (dhCKA G) (kemCKA KEM)` is at most the DDH advantage of
  `ckaDDHRed k m (prodCKARed₁ (kemCKA KEM) k m A)` plus the KEM-CPA advantage of
  `kemCKARed KEM k m (prodCKARed₂ (dhCKA G) k m A)`
* `ckaRun_kem`, `cka_real_kem`, `cka_ideal_kem`, `ckaRun_prod`, `cka_real_prod`,
  `cka_ideal_prod` — the games of `kemCKA` and of the product
* `dhCKA_init_isPure`, `dhCKA_send_isPure` — the Diffie–Hellman CKA does not touch the heap
* `ckaPubRedOf.tree.timeBound_timed`, `kemCKARed.timeBound_timed`,
  `prodCKARed₁.timeBound_timed`, `prodCKARed₂.timeBound_timed` — the times of the costed
  reductions

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4.1 (CKA from KEM)
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Examples.KEMDEM
open scoped ENNReal

/-! ## The distinguisher with a public computation -/

/-- The distinguisher with the public computation `pub` and the view function `view`: on the
challenge `y` it runs `pub` and calls `A` on `view c y` for its result `c`. -/
noncomputable def ckaPubRedOf {Y P V : Type} (pub : SPComp P) (view : P → Y → V)
    (A : V → SPComp Bool) (y : Y) : SPComp Bool := do
  let c ← pub
  A (view c y)

derive_reduction ckaPubRedOf (adv := A)

/-- **Time of the distinguisher with a public computation.** With the costed adversary `A` of
time at most `T` and call cost at most `a`, the view function of cost at most `tv`, and the
costed public computation `pubT` of time at most `tp`, the costed distinguisher has time at
most `T + a + tv + tp + 2`. -/
theorem ckaPubRedOf.tree.timeBound_timed {Y P V : Type} (pub : SPComp P) (view : P → Y → V)
    (viewCost : P → Y → ℕ) (A : V → SPTree.Timed Bool) (ACost : V → ℕ) {T a tv tp : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (hv : ∀ c y, viewCost c y ≤ tv)
    (pubT : SPTree.Timed P) (hp : pubT.time ≤ tp) (y : Y) :
    SPTree.Timed.stepTime (ckaPubRedOf.tree.timed pub view viewCost A ACost y pubT) ≤
      T + a + tv + tp + 2 := by
  simp only [ckaPubRedOf.tree.timed]
  refine (SPTree.Timed.stepTime_bind_le pubT _ (T + a + tv + 2) fun x => ?_).trans (by omega)
  have := hA (view x y); have := hAc (view x y); have := hv x y
  simp only [SPTree.Timed.stepTime]; omega

/-! ## Runs of CKA schemes that do not touch the heap -/

variable {St Msg Key : Type}

/-- A run of a CKA scheme whose sending does not touch the heap does not touch the heap. -/
theorem ckaRun_isPure (C : CKADef St Msg Key) (hs : ∀ s, SPComp.IsPure (C.send s)) :
    ∀ (n : ℕ) (s r : St), SPComp.IsPure (ckaRun C n s r) := by
  intro n
  induction n with
  | zero => intro s r; exact SPComp.pure_isPure _
  | succ n ih =>
    intro s r
    exact SPComp.bind_isPure (hs s) fun o => SPComp.bind_isPure (ih _ _) fun p =>
      SPComp.pure_isPure _

/-! ## The CKA of a KEM -/

section KEM

variable {PK SK K E : Type}

/-- The CKA of the KEM `KEM` with encapsulation keys `PK`, decapsulation keys `SK`, keys `K`
and encapsulations `E`. A party state `(pk, sk)` holds the last encapsulation key `pk` of the
peer and the own last decapsulation key `sk`. The public value of the initialisation is a
fresh encapsulation key; sending encapsulates a key under `pk` and sends the encapsulation with
a fresh encapsulation key; receiving decapsulates with `sk`. -/
noncomputable def kemCKA [Inhabited K] (KEM : KEMScheme PK SK K E) :
    CKADef (PK × SK) (Option E × PK) K where
  init := SPComp.bind KEM.kgen fun ks => SPComp.pure ((none, ks.1), ks, ks)
  send s := SPComp.bind (KEM.encap s.1) fun ke => SPComp.bind KEM.kgen fun ks =>
    SPComp.pure ((s.1, ks.2), (some ke.2, ks.1), ke.1)
  recv r T := ((T.2, r.2), T.1.elim default (KEM.decap r.2))

/-- The public transcript of `n` epochs of `kemCKA KEM` from a sender holding the encapsulation
key `h` of the peer: the messages and keys of the epochs, and the encapsulation key held by the
next sender. -/
noncomputable def kemRun (KEM : KEMScheme PK SK K E) :
    ℕ → PK → SPComp (List ((Option E × PK) × K) × PK)
  | 0, h => SPComp.pure ([], h)
  | n + 1, h => SPComp.bind (KEM.encap h) fun ke => SPComp.bind KEM.kgen fun ks =>
      SPComp.bind (kemRun KEM n ks.1) fun q => SPComp.pure (((some ke.2, ks.1), ke.1) :: q.1, q.2)

/-- A run of `kemCKA KEM` depends on the states only through the encapsulation key held by
the sender, and its transcript and the key of the next sender are those of `kemRun`. -/
theorem ckaRun_kem [Inhabited K] (KEM : KEMScheme PK SK K E) {β : Type} (n : ℕ)
    (s r : PK × SK) (F : List ((Option E × PK) × K) → PK → SPComp β) :
    SPComp.bind (ckaRun (kemCKA KEM) n s r) (fun p => F p.1 p.2.1.1) =
      SPComp.bind (kemRun KEM n s.1) (fun q => F q.1 q.2) := by
  induction n generalizing s r F with
  | zero => simp only [ckaRun, kemRun, SPComp.pure_bind]
  | succ n ih =>
    simp only [ckaRun, kemRun, kemCKA, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext ke; congr 1; funext ks
    exact ih (ks.1, r.2) (s.1, ks.2) (fun l h => F (((some ke.2, ks.1), ke.1) :: l) h)

/-- The last epoch of `kemRun KEM (n + 1)`. -/
theorem kemRun_succ (KEM : KEMScheme PK SK K E) (n : ℕ) (h : PK) :
    kemRun KEM (n + 1) h =
      SPComp.bind (kemRun KEM n h) fun q => SPComp.bind (KEM.encap q.2) fun ke =>
        SPComp.bind KEM.kgen fun ks => SPComp.pure (q.1 ++ [((some ke.2, ks.1), ke.1)], ks.1) := by
  induction n generalizing h with
  | zero => simp only [kemRun, SPComp.pure_bind, List.nil_append]
  | succ n ih =>
    conv_lhs => rw [kemRun]
    conv_rhs => rw [kemRun]
    simp only [ih, SPComp.bind_assoc, SPComp.pure_bind, List.cons_append]

/-- The public value of the initialisation of `kemCKA KEM`, the transcript of `k` epochs and
the encapsulation key held by the sender of the next epoch. -/
noncomputable def kemPre (KEM : KEMScheme PK SK K E) (k : ℕ) :
    SPComp ((Option E × PK) × List ((Option E × PK) × K) × PK) :=
  SPComp.bind KEM.kgen fun ks => SPComp.bind (kemRun KEM k ks.1) fun q =>
    SPComp.pure ((none, ks.1), q.1, q.2)

/-- The part of `kemPre KEM k` before the last key generation: nothing for `k = 0`, and
otherwise `kemPre KEM (k - 1)` with the encapsulation of epoch `k`. -/
noncomputable def kemPreRaw (KEM : KEMScheme PK SK K E) :
    ℕ → SPComp (Option (((Option E × PK) × List ((Option E × PK) × K) × PK) × (K × E)))
  | 0 => SPComp.pure none
  | k + 1 => SPComp.bind (kemPre KEM k) fun v => SPComp.bind (KEM.encap v.2.2) fun ke =>
      SPComp.pure (some (v, ke))

/-- The public value and the transcript of `kemPre` from the part `w` before the last key
generation and the encapsulation key `pk` it generates. -/
def kemPreView :
    Option (((Option E × PK) × List ((Option E × PK) × K) × PK) × (K × E)) → PK →
      (Option E × PK) × List ((Option E × PK) × K)
  | none, pk => ((none, pk), [])
  | some (v, ke), pk => (v.1, v.2.1 ++ [((some ke.2, pk), ke.1)])

/-- `kemPre KEM k` generates the encapsulation key of the next sender last. -/
theorem kemPre_split (KEM : KEMScheme PK SK K E) (hkgen : SPComp.IsPure KEM.kgen)
    (hencap : ∀ pk, SPComp.IsPure (KEM.encap pk)) (k : ℕ) :
    kemPre KEM k = SPComp.bind KEM.kgen fun ks => SPComp.bind (kemPreRaw KEM k) fun w =>
      SPComp.pure ((kemPreView w ks.1).1, (kemPreView w ks.1).2, ks.1) := by
  cases k with
  | zero => simp only [kemPre, kemPreRaw, kemRun, kemPreView, SPComp.pure_bind]
  | succ k =>
    simp only [kemPre, kemPreRaw, kemRun_succ, kemPreView, SPComp.bind_assoc, SPComp.pure_bind]
    bind_swap_nf [hkgen, hencap]

/-- The real CKA game of `kemCKA KEM`: the run up to the challenge, the challenge
encapsulation under the key held by its sender, a fresh key generation and the run after the
challenge. -/
theorem cka_real_kem [Inhabited K] (KEM : KEMScheme PK SK K E) (k m : ℕ) :
    cka_real (kemCKA KEM) k m =
      SPComp.bind (kemPre KEM k) fun v => SPComp.bind (KEM.encap v.2.2) fun ke =>
        SPComp.bind KEM.kgen fun ks => SPComp.bind (kemRun KEM m ks.1) fun q =>
          SPComp.pure (v.1, v.2.1, ((some ke.2, ks.1), ke.1), q.1) := by
  have hi : (kemCKA KEM).init =
      SPComp.bind KEM.kgen fun ks => SPComp.pure ((none, ks.1), ks, ks) := rfl
  have hs : ∀ s, (kemCKA KEM).send s = SPComp.bind (KEM.encap s.1) fun ke =>
      SPComp.bind KEM.kgen fun ks => SPComp.pure ((s.1, ks.2), (some ke.2, ks.1), ke.1) :=
    fun _ => rfl
  simp only [cka_real, hi, hs, kemPre, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext ks₀
  refine Eq.trans ?_ (ckaRun_kem KEM k ks₀ ks₀ fun l h =>
    SPComp.bind (KEM.encap h) fun ke => SPComp.bind KEM.kgen fun ks =>
      SPComp.bind (kemRun KEM m ks.1) fun q =>
        SPComp.pure ((none, ks₀.1), l, ((some ke.2, ks.1), ke.1), q.1))
  congr 1; funext p; congr 1; funext ke; congr 1; funext ks
  exact ckaRun_kem KEM m _ _ fun l _ =>
    SPComp.pure ((none, ks₀.1), p.1, ((some ke.2, ks.1), ke.1), l)

/-- The ideal CKA game of `kemCKA KEM`: as `cka_real_kem` with a uniform challenge key. -/
theorem cka_ideal_kem [Fintype K] [Nonempty K] [Inhabited K] (KEM : KEMScheme PK SK K E)
    (k m : ℕ) :
    cka_ideal (kemCKA KEM) k m =
      SPComp.bind (kemPre KEM k) fun v => SPComp.bind (KEM.encap v.2.2) fun ke =>
        SPComp.bind KEM.kgen fun ks => SPComp.bind (SPComp.sample K) fun u =>
          SPComp.bind (kemRun KEM m ks.1) fun q =>
            SPComp.pure (v.1, v.2.1, ((some ke.2, ks.1), u), q.1) := by
  have hi : (kemCKA KEM).init =
      SPComp.bind KEM.kgen fun ks => SPComp.pure ((none, ks.1), ks, ks) := rfl
  have hs : ∀ s, (kemCKA KEM).send s = SPComp.bind (KEM.encap s.1) fun ke =>
      SPComp.bind KEM.kgen fun ks => SPComp.pure ((s.1, ks.2), (some ke.2, ks.1), ke.1) :=
    fun _ => rfl
  simp only [cka_ideal, hi, hs, kemPre, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext ks₀
  refine Eq.trans ?_ (ckaRun_kem KEM k ks₀ ks₀ fun l h =>
    SPComp.bind (KEM.encap h) fun ke => SPComp.bind KEM.kgen fun ks =>
      SPComp.bind (SPComp.sample K) fun u => SPComp.bind (kemRun KEM m ks.1) fun q =>
        SPComp.pure ((none, ks₀.1), l, ((some ke.2, ks.1), u), q.1))
  congr 1; funext p; congr 1; funext ke; congr 1; funext ks; congr 1; funext u
  exact ckaRun_kem KEM m _ _ fun l _ =>
    SPComp.pure ((none, ks₀.1), p.1, ((some ke.2, ks.1), u), l)

/-- The public computation of the KEM-CPA reduction at challenge epoch `k + 1` with `m` epochs
after it: the part of the run before the last key generation preceding the challenge, a fresh
key generation and the run after the challenge. -/
noncomputable def kemCKAPub (KEM : KEMScheme PK SK K E) (k m : ℕ) :
    SPComp (Option (((Option E × PK) × List ((Option E × PK) × K) × PK) × (K × E)) × PK ×
      List ((Option E × PK) × K)) :=
  SPComp.bind (kemPreRaw KEM k) fun w => SPComp.bind KEM.kgen fun ks =>
    SPComp.bind (kemRun KEM m ks.1) fun q => SPComp.pure (w, ks.1, q.1)

/-- The view of the CKA adversary built from the result `c` of `kemCKAPub` and the KEM-CPA
challenge `(pk, ek, key)`: `pk` is the fresh encapsulation key of the epoch before the challenge
(the public value of the initialisation when `k = 0`), and `(ek, key)` the encapsulation and key
of the challenge epoch. -/
def kemCKAView
    (c : Option (((Option E × PK) × List ((Option E × PK) × K) × PK) × (K × E)) × PK ×
      List ((Option E × PK) × K))
    (y : PK × E × K) : CKAView (Option E × PK) K :=
  ((kemPreView c.1 y.1).1, (kemPreView c.1 y.1).2, ((some y.2.1, c.2.1), y.2.2), c.2.2)

/-- The KEM-CPA distinguisher built from the CKA adversary `A` at challenge epoch `k + 1` with
`m` epochs after it: it runs `kemCKAPub KEM k m` and calls `A` on `kemCKAView`. -/
noncomputable def kemCKARed (KEM : KEMScheme PK SK K E) (k m : ℕ)
    (A : CKAView (Option E × PK) K → SPComp Bool) : PK × E × K → SPComp Bool :=
  ckaPubRedOf (kemCKAPub KEM k m) kemCKAView A

/-- The real CKA game of `kemCKA KEM` is the real KEM-CPA game of `kemCKARed`. -/
theorem cka_real_kem_bind [Fintype K] [Nonempty K] [Fintype E] [Nonempty E] [Inhabited K]
    (KEM : KEMScheme PK SK K E) (hkgen : SPComp.IsPure KEM.kgen)
    (hencap : ∀ pk, SPComp.IsPure (KEM.encap pk)) (k m : ℕ)
    (A : CKAView (Option E × PK) K → SPComp Bool) :
    (cka_real (kemCKA KEM) k m).bind A = (KEM_CPA_real KEM).bind (kemCKARed KEM k m A) := by
  rw [cka_real_kem, kemPre_split KEM hkgen hencap]
  simp only [KEM_CPA_real, kemCKARed, kemCKAPub]
  bind_swap_nf [hkgen, hencap, ckaPubRedOf, kemCKAView]

/-- The ideal CKA game of `kemCKA KEM` is the ideal KEM-CPA game of `kemCKARed`. -/
theorem cka_ideal_kem_bind [Fintype K] [Nonempty K] [Fintype E] [Nonempty E] [Inhabited K]
    (KEM : KEMScheme PK SK K E) (hkgen : SPComp.IsPure KEM.kgen)
    (hencap : ∀ pk, SPComp.IsPure (KEM.encap pk)) (k m : ℕ)
    (A : CKAView (Option E × PK) K → SPComp Bool) :
    (cka_ideal (kemCKA KEM) k m).bind A = (KEM_CPA_ideal KEM).bind (kemCKARed KEM k m A) := by
  rw [cka_ideal_kem, kemPre_split KEM hkgen hencap]
  simp only [KEM_CPA_ideal, kemCKARed, kemCKAPub]
  bind_swap_nf [hkgen, hencap, ckaPubRedOf, kemCKAView]

/-- **CKA security of `kemCKA` from KEM-CPA security.** For a KEM whose key generation and
encapsulation do not touch the heap, every adversary `A`, challenge epoch `k + 1` and `m`
epochs after it, the CKA advantage of `kemCKA KEM` equals the KEM-CPA advantage of
`kemCKARed KEM k m A`. -/
theorem kemCKA_advantage_eq [Fintype K] [Nonempty K] [Fintype E] [Nonempty E] [Inhabited K]
    (KEM : KEMScheme PK SK K E) (hkgen : SPComp.IsPure KEM.kgen)
    (hencap : ∀ pk, SPComp.IsPure (KEM.encap pk)) (k m : ℕ)
    (A : CKAView (Option E × PK) K → SPComp Bool) :
    CKA_Advantage (kemCKA KEM) k m A = KEM_CPA_Advantage KEM (kemCKARed KEM k m A) := by
  unfold CKA_Advantage KEM_CPA_Advantage AdvantageA
  rw [cka_real_kem_bind KEM hkgen hencap, cka_ideal_kem_bind KEM hkgen hencap]

/-- The costed form of `kemCKARed`: the costed tree of `ckaPubRedOf` at the view `kemCKAView`
of cost `viewCost`, with the costed public computation `pubT`. -/
noncomputable def kemCKARed.timed (KEM : KEMScheme PK SK K E) (k m : ℕ)
    (viewCost : Option (((Option E × PK) × List ((Option E × PK) × K) × PK) × (K × E)) × PK ×
      List ((Option E × PK) × K) → PK × E × K → ℕ)
    (A : CKAView (Option E × PK) K → SPTree.Timed Bool) (ACost : CKAView (Option E × PK) K → ℕ)
    (pubT : SPTree.Timed (Option (((Option E × PK) × List ((Option E × PK) × K) × PK) × (K × E)) ×
      PK × List ((Option E × PK) × K)))
    (y : PK × E × K) : ℕ × SPTree.Timed Bool :=
  ckaPubRedOf.tree.timed (kemCKAPub KEM k m) kemCKAView viewCost A ACost y pubT

/-- The costed form of `kemCKARed` with a costed public computation that compiles to
`kemCKAPub` erases and compiles to `kemCKARed` at the erased adversary. -/
theorem kemCKARed.erase_timed (KEM : KEMScheme PK SK K E) (k m : ℕ)
    (viewCost : Option (((Option E × PK) × List ((Option E × PK) × K) × PK) × (K × E)) × PK ×
      List ((Option E × PK) × K) → PK × E × K → ℕ)
    (A : CKAView (Option E × PK) K → SPTree.Timed Bool) (ACost : CKAView (Option E × PK) K → ℕ)
    (pubT : SPTree.Timed (Option (((Option E × PK) × List ((Option E × PK) × K) × PK) × (K × E)) ×
      PK × List ((Option E × PK) × K)))
    (hpub : pubT.erase.compile = kemCKAPub KEM k m) (y : PK × E × K) :
    (kemCKARed.timed KEM k m viewCost A ACost pubT y).2.erase.compile =
      kemCKARed KEM k m (fun x => (A x).erase.compile) y := by
  rw [kemCKARed.timed, ckaPubRedOf.tree.erase_timed, ckaPubRedOf.compile_tree _ _ _ _ _ hpub]
  rfl

/-- **Time of `kemCKARed`**, the bound of `ckaPubRedOf.tree.timeBound_timed` at the view
`kemCKAView` of cost at most `tv` and the costed public computation of time at most `tp`; the
public computation costs the key generations and encapsulations of `k + m` epochs. -/
theorem kemCKARed.timeBound_timed (KEM : KEMScheme PK SK K E) (k m : ℕ)
    (viewCost : Option (((Option E × PK) × List ((Option E × PK) × K) × PK) × (K × E)) × PK ×
      List ((Option E × PK) × K) → PK × E × K → ℕ)
    (A : CKAView (Option E × PK) K → SPTree.Timed Bool) (ACost : CKAView (Option E × PK) K → ℕ)
    (pubT : SPTree.Timed (Option (((Option E × PK) × List ((Option E × PK) × K) × PK) × (K × E)) ×
      PK × List ((Option E × PK) × K)))
    {T a tv tp : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hv : ∀ c y, viewCost c y ≤ tv) (hp : pubT.time ≤ tp) (y : PK × E × K) :
    SPTree.Timed.stepTime (kemCKARed.timed KEM k m viewCost A ACost pubT y) ≤
      T + a + tv + tp + 2 :=
  ckaPubRedOf.tree.timeBound_timed _ _ viewCost A ACost hA hAc hv pubT hp y

end KEM

/-! ## The product of two CKA schemes -/

section Prod

variable {S₁ M₁ K₁ S₂ M₂ K₂ : Type}

/-- The CKA schemes `C₁` and `C₂` run side by side: states, messages and keys are pairs. -/
noncomputable def prodCKA (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂) :
    CKADef (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) where
  init := SPComp.bind C₁.init fun i₁ => SPComp.bind C₂.init fun i₂ =>
    SPComp.pure ((i₁.1, i₂.1), (i₁.2.1, i₂.2.1), (i₁.2.2, i₂.2.2))
  send s := SPComp.bind (C₁.send s.1) fun o₁ => SPComp.bind (C₂.send s.2) fun o₂ =>
    SPComp.pure ((o₁.1, o₂.1), (o₁.2.1, o₂.2.1), (o₁.2.2, o₂.2.2))
  recv r T :=
    (((C₁.recv r.1 T.1).1, (C₂.recv r.2 T.2).1), ((C₁.recv r.1 T.1).2, (C₂.recv r.2 T.2).2))

/-- The transcript of the product from the transcripts of the components. -/
def zipT (l₁ : List (M₁ × K₁)) (l₂ : List (M₂ × K₂)) : List ((M₁ × M₂) × (K₁ × K₂)) :=
  List.zipWith (fun a b => ((a.1, b.1), (a.2, b.2))) l₁ l₂

/-- `zipT` of two non-empty transcripts. -/
theorem zipT_cons (a : M₁ × K₁) (b : M₂ × K₂) (l₁ : List (M₁ × K₁)) (l₂ : List (M₂ × K₂)) :
    zipT (a :: l₁) (b :: l₂) = ((a.1, b.1), (a.2, b.2)) :: zipT l₁ l₂ := rfl

/-- The CKA view of the product from the views of the components. -/
def zipView (v₁ : CKAView M₁ K₁) (v₂ : CKAView M₂ K₂) : CKAView (M₁ × M₂) (K₁ × K₂) :=
  ((v₁.1, v₂.1), zipT v₁.2.1 v₂.2.1, ((v₁.2.2.1.1, v₂.2.2.1.1), (v₁.2.2.1.2, v₂.2.2.1.2)),
    zipT v₁.2.2.2 v₂.2.2.2)

/-- A run of the product is a run of `C₁` followed by a run of `C₂`, when sending in `C₁`
does not touch the heap. -/
theorem ckaRun_prod (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂)
    (h₁ : ∀ s, SPComp.IsPure (C₁.send s)) {β : Type} (n : ℕ) (s r : S₁ × S₂)
    (F : List ((M₁ × M₂) × (K₁ × K₂)) × (S₁ × S₂) × (S₁ × S₂) → SPComp β) :
    SPComp.bind (ckaRun (prodCKA C₁ C₂) n s r) F =
      SPComp.bind (ckaRun C₁ n s.1 r.1) fun p₁ => SPComp.bind (ckaRun C₂ n s.2 r.2) fun p₂ =>
        F (zipT p₁.1 p₂.1, (p₁.2.1, p₂.2.1), (p₁.2.2, p₂.2.2)) := by
  have hs : ∀ s, (prodCKA C₁ C₂).send s = SPComp.bind (C₁.send s.1) fun o₁ =>
      SPComp.bind (C₂.send s.2) fun o₂ =>
        SPComp.pure ((o₁.1, o₂.1), (o₁.2.1, o₂.2.1), (o₁.2.2, o₂.2.2)) := fun _ => rfl
  have hr : ∀ r T, (prodCKA C₁ C₂).recv r T =
      (((C₁.recv r.1 T.1).1, (C₂.recv r.2 T.2).1), ((C₁.recv r.1 T.1).2, (C₂.recv r.2 T.2).2)) :=
    fun _ _ => rfl
  induction n generalizing s r F with
  | zero => simp only [ckaRun, SPComp.pure_bind]; rfl
  | succ n ih =>
    simp only [ckaRun, hs, hr, ih, SPComp.bind_assoc, SPComp.pure_bind, zipT_cons]
    congr 1; funext o₁
    exact SPComp.isPure_bind_comm_right _ _ _ (ckaRun_isPure C₁ h₁ _ _ _)

/-- The real CKA game of the product runs the real CKA games of `C₁` and of `C₂`, when the
sending in `C₁` does not touch the heap. -/
theorem cka_real_prod (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂)
    (h₁ : ∀ s, SPComp.IsPure (C₁.send s)) (k m : ℕ) :
    cka_real (prodCKA C₁ C₂) k m =
      SPComp.bind (cka_real C₁ k m) fun v₁ => SPComp.bind (cka_real C₂ k m) fun v₂ =>
        SPComp.pure (zipView v₁ v₂) := by
  have hi : (prodCKA C₁ C₂).init = SPComp.bind C₁.init fun i₁ => SPComp.bind C₂.init fun i₂ =>
      SPComp.pure ((i₁.1, i₂.1), (i₁.2.1, i₂.2.1), (i₁.2.2, i₂.2.2)) := rfl
  have hs : ∀ s, (prodCKA C₁ C₂).send s = SPComp.bind (C₁.send s.1) fun o₁ =>
      SPComp.bind (C₂.send s.2) fun o₂ =>
        SPComp.pure ((o₁.1, o₂.1), (o₁.2.1, o₂.2.1), (o₁.2.2, o₂.2.2)) := fun _ => rfl
  have hr : ∀ r T, (prodCKA C₁ C₂).recv r T =
      (((C₁.recv r.1 T.1).1, (C₂.recv r.2 T.2).1), ((C₁.recv r.1 T.1).2, (C₂.recv r.2 T.2).2)) :=
    fun _ _ => rfl
  have hrun : ∀ n s r, SPComp.IsPure (ckaRun C₁ n s r) := ckaRun_isPure C₁ h₁
  simp only [cka_real, hi, hs, hr, ckaRun_prod C₁ C₂ h₁, SPComp.bind_assoc, SPComp.pure_bind]
  simp only [SPComp.isPure_bind_comm_right _ (ckaRun C₁ _ _ _) _ (hrun _ _ _),
    SPComp.isPure_bind_comm_right _ (C₁.send _) _ (h₁ _)]
  rfl

/-- The ideal CKA game of the product runs the ideal CKA games of `C₁` and of `C₂`, when
sending in `C₁` does not touch the heap. -/
theorem cka_ideal_prod [Fintype K₁] [Nonempty K₁] [Fintype K₂] [Nonempty K₂]
    (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂) (h₁ : ∀ s, SPComp.IsPure (C₁.send s))
    (k m : ℕ) :
    cka_ideal (prodCKA C₁ C₂) k m =
      SPComp.bind (cka_ideal C₁ k m) fun v₁ => SPComp.bind (cka_ideal C₂ k m) fun v₂ =>
        SPComp.pure (zipView v₁ v₂) := by
  have hi : (prodCKA C₁ C₂).init = SPComp.bind C₁.init fun i₁ => SPComp.bind C₂.init fun i₂ =>
      SPComp.pure ((i₁.1, i₂.1), (i₁.2.1, i₂.2.1), (i₁.2.2, i₂.2.2)) := rfl
  have hs : ∀ s, (prodCKA C₁ C₂).send s = SPComp.bind (C₁.send s.1) fun o₁ =>
      SPComp.bind (C₂.send s.2) fun o₂ =>
        SPComp.pure ((o₁.1, o₂.1), (o₁.2.1, o₂.2.1), (o₁.2.2, o₂.2.2)) := fun _ => rfl
  have hr : ∀ r T, (prodCKA C₁ C₂).recv r T =
      (((C₁.recv r.1 T.1).1, (C₂.recv r.2 T.2).1), ((C₁.recv r.1 T.1).2, (C₂.recv r.2 T.2).2)) :=
    fun _ _ => rfl
  have hrun : ∀ n s r, SPComp.IsPure (ckaRun C₁ n s r) := ckaRun_isPure C₁ h₁
  simp only [cka_ideal, hi, hs, hr, ckaRun_prod C₁ C₂ h₁, SPComp.sample_prod_eq,
    SPComp.bind_assoc, SPComp.pure_bind]
  simp only [SPComp.isPure_bind_comm_right _ (ckaRun C₁ _ _ _) _ (hrun _ _ _),
    SPComp.isPure_bind_comm_right _ (C₁.send _) _ (h₁ _)]
  simp only [SPComp.isPure_bind_comm_right _ (SPComp.sample K₁) _ (SPComp.sample_isPure _)]
  rfl

/-- The ideal CKA game of a scheme whose initialisation and sending do not touch the heap does
not touch the heap. -/
theorem cka_ideal_isPure [Fintype K₁] [Nonempty K₁] (C₁ : CKADef S₁ M₁ K₁)
    (h₀ : SPComp.IsPure C₁.init) (h₁ : ∀ s, SPComp.IsPure (C₁.send s)) (k m : ℕ) :
    SPComp.IsPure (cka_ideal C₁ k m) :=
  SPComp.bind_isPure h₀ fun _ => SPComp.bind_isPure (ckaRun_isPure C₁ h₁ _ _ _) fun _ =>
    SPComp.bind_isPure (h₁ _) fun _ => SPComp.bind_isPure (SPComp.sample_isPure _) fun _ =>
      SPComp.bind_isPure (ckaRun_isPure C₁ h₁ _ _ _) fun _ => SPComp.pure_isPure _

/-- The hybrid game of the product: the ideal game of `C₁` and the real game of `C₂`. -/
noncomputable def prodHyb [Fintype K₁] [Nonempty K₁] (C₁ : CKADef S₁ M₁ K₁)
    (C₂ : CKADef S₂ M₂ K₂) (k m : ℕ) : SPComp (CKAView (M₁ × M₂) (K₁ × K₂)) :=
  SPComp.bind (cka_ideal C₁ k m) fun v₁ => SPComp.bind (cka_real C₂ k m) fun v₂ =>
    SPComp.pure (zipView v₁ v₂)

/-- The CKA distinguisher against `C₁` built from the CKA adversary `A` against the product:
it runs the real CKA game of `C₂` and calls `A` on the view of the product. -/
noncomputable def prodCKARed₁ (C₂ : CKADef S₂ M₂ K₂) (k m : ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPComp Bool) : CKAView M₁ K₁ → SPComp Bool :=
  ckaPubRedOf (cka_real C₂ k m) (fun v₂ v₁ => zipView v₁ v₂) A

/-- The CKA distinguisher against `C₂` built from the CKA adversary `A` against the product:
it runs the ideal CKA game of `C₁` and calls `A` on the view of the product. -/
noncomputable def prodCKARed₂ [Fintype K₁] [Nonempty K₁] (C₁ : CKADef S₁ M₁ K₁) (k m : ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPComp Bool) : CKAView M₂ K₂ → SPComp Bool :=
  ckaPubRedOf (cka_ideal C₁ k m) (fun v₁ v₂ => zipView v₁ v₂) A

/-- **CKA security of the product.** When the initialisation and sending of `C₁` do not touch
the heap, for every adversary `A`, challenge epoch `k + 1` and `m` epochs after it, the CKA
advantage of `prodCKA C₁ C₂` is at most the CKA advantage of `C₁` at `prodCKARed₁ C₂ k m A`
plus the CKA advantage of `C₂` at `prodCKARed₂ C₁ k m A`. -/
theorem prodCKA_advantage_le [Fintype K₁] [Nonempty K₁] [Fintype K₂] [Nonempty K₂]
    (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂) (h₀ : SPComp.IsPure C₁.init)
    (h₁ : ∀ s, SPComp.IsPure (C₁.send s)) (k m : ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPComp Bool) :
    CKA_Advantage (prodCKA C₁ C₂) k m A ≤
      CKA_Advantage C₁ k m (prodCKARed₁ C₂ k m A) +
        CKA_Advantage C₂ k m (prodCKARed₂ C₁ k m A) := by
  have e₁ : (cka_real (prodCKA C₁ C₂) k m).bind A =
      (cka_real C₁ k m).bind (prodCKARed₁ C₂ k m A) := by
    rw [cka_real_prod C₁ C₂ h₁]
    unfold prodCKARed₁ ckaPubRedOf
    simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  have e₂ : (prodHyb C₁ C₂ k m).bind A = (cka_ideal C₁ k m).bind (prodCKARed₁ C₂ k m A) := by
    unfold prodHyb prodCKARed₁ ckaPubRedOf
    simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  have e₃ : (prodHyb C₁ C₂ k m).bind A = (cka_real C₂ k m).bind (prodCKARed₂ C₁ k m A) := by
    unfold prodHyb prodCKARed₂ ckaPubRedOf
    simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
    exact SPComp.isPure_bind_comm_left _ _ _ (cka_ideal_isPure C₁ h₀ h₁ k m)
  have e₄ : (cka_ideal (prodCKA C₁ C₂) k m).bind A =
      (cka_ideal C₂ k m).bind (prodCKARed₂ C₁ k m A) := by
    rw [cka_ideal_prod C₁ C₂ h₁]
    unfold prodCKARed₂ ckaPubRedOf
    simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
    exact SPComp.isPure_bind_comm_left _ _ _ (cka_ideal_isPure C₁ h₀ h₁ k m)
  unfold CKA_Advantage AdvantageA
  rw [e₁, e₄]
  refine (advantage_triangle _ ((prodHyb C₁ C₂ k m).bind A) _).trans ?_
  rw [← e₂, ← e₃]

/-- The costed form of `prodCKARed₁`, with the costed real game `pubT` of `C₂`. -/
noncomputable def prodCKARed₁.timed (C₂ : CKADef S₂ M₂ K₂) (k m : ℕ)
    (viewCost : CKAView M₂ K₂ → CKAView M₁ K₁ → ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPTree.Timed Bool)
    (ACost : CKAView (M₁ × M₂) (K₁ × K₂) → ℕ) (pubT : SPTree.Timed (CKAView M₂ K₂))
    (y : CKAView M₁ K₁) : ℕ × SPTree.Timed Bool :=
  ckaPubRedOf.tree.timed (cka_real C₂ k m) (fun v₂ v₁ => zipView v₁ v₂) viewCost A ACost y pubT

/-- The costed form of `prodCKARed₁` with a costed game that compiles to `cka_real C₂ k m`
erases and compiles to `prodCKARed₁` at the erased adversary. -/
theorem prodCKARed₁.erase_timed (C₂ : CKADef S₂ M₂ K₂) (k m : ℕ)
    (viewCost : CKAView M₂ K₂ → CKAView M₁ K₁ → ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPTree.Timed Bool)
    (ACost : CKAView (M₁ × M₂) (K₁ × K₂) → ℕ) (pubT : SPTree.Timed (CKAView M₂ K₂))
    (hpub : pubT.erase.compile = cka_real C₂ k m) (y : CKAView M₁ K₁) :
    (prodCKARed₁.timed C₂ k m viewCost A ACost pubT y).2.erase.compile =
      prodCKARed₁ C₂ k m (fun x => (A x).erase.compile) y := by
  rw [prodCKARed₁.timed, ckaPubRedOf.tree.erase_timed, ckaPubRedOf.compile_tree _ _ _ _ _ hpub]
  rfl

/-- **Time of `prodCKARed₁`**: with the costed adversary of time at most `T` and call cost at
most `a`, the view of cost at most `tv` and the costed real game of `C₂` of time at most `tp`,
at most `T + a + tv + tp + 2`. -/
theorem prodCKARed₁.timeBound_timed (C₂ : CKADef S₂ M₂ K₂) (k m : ℕ)
    (viewCost : CKAView M₂ K₂ → CKAView M₁ K₁ → ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPTree.Timed Bool)
    (ACost : CKAView (M₁ × M₂) (K₁ × K₂) → ℕ) (pubT : SPTree.Timed (CKAView M₂ K₂))
    {T a tv tp : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hv : ∀ c y, viewCost c y ≤ tv) (hp : pubT.time ≤ tp) (y : CKAView M₁ K₁) :
    SPTree.Timed.stepTime (prodCKARed₁.timed C₂ k m viewCost A ACost pubT y) ≤
      T + a + tv + tp + 2 :=
  ckaPubRedOf.tree.timeBound_timed _ _ viewCost A ACost hA hAc hv pubT hp y

/-- The costed form of `prodCKARed₂`, with the costed ideal game `pubT` of `C₁`. -/
noncomputable def prodCKARed₂.timed [Fintype K₁] [Nonempty K₁] (C₁ : CKADef S₁ M₁ K₁)
    (k m : ℕ) (viewCost : CKAView M₁ K₁ → CKAView M₂ K₂ → ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPTree.Timed Bool)
    (ACost : CKAView (M₁ × M₂) (K₁ × K₂) → ℕ) (pubT : SPTree.Timed (CKAView M₁ K₁))
    (y : CKAView M₂ K₂) : ℕ × SPTree.Timed Bool :=
  ckaPubRedOf.tree.timed (cka_ideal C₁ k m) (fun v₁ v₂ => zipView v₁ v₂) viewCost A ACost y pubT

/-- The costed form of `prodCKARed₂` with a costed game that compiles to `cka_ideal C₁ k m`
erases and compiles to `prodCKARed₂` at the erased adversary. -/
theorem prodCKARed₂.erase_timed [Fintype K₁] [Nonempty K₁] (C₁ : CKADef S₁ M₁ K₁) (k m : ℕ)
    (viewCost : CKAView M₁ K₁ → CKAView M₂ K₂ → ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPTree.Timed Bool)
    (ACost : CKAView (M₁ × M₂) (K₁ × K₂) → ℕ) (pubT : SPTree.Timed (CKAView M₁ K₁))
    (hpub : pubT.erase.compile = cka_ideal C₁ k m) (y : CKAView M₂ K₂) :
    (prodCKARed₂.timed C₁ k m viewCost A ACost pubT y).2.erase.compile =
      prodCKARed₂ C₁ k m (fun x => (A x).erase.compile) y := by
  rw [prodCKARed₂.timed, ckaPubRedOf.tree.erase_timed, ckaPubRedOf.compile_tree _ _ _ _ _ hpub]
  rfl

/-- **Time of `prodCKARed₂`**: with the costed adversary of time at most `T` and call cost at
most `a`, the view of cost at most `tv` and the costed ideal game of `C₁` of time at most
`tp`, at most `T + a + tv + tp + 2`. -/
theorem prodCKARed₂.timeBound_timed [Fintype K₁] [Nonempty K₁] (C₁ : CKADef S₁ M₁ K₁)
    (k m : ℕ) (viewCost : CKAView M₁ K₁ → CKAView M₂ K₂ → ℕ)
    (A : CKAView (M₁ × M₂) (K₁ × K₂) → SPTree.Timed Bool)
    (ACost : CKAView (M₁ × M₂) (K₁ × K₂) → ℕ) (pubT : SPTree.Timed (CKAView M₁ K₁))
    {T a tv tp : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hv : ∀ c y, viewCost c y ≤ tv) (hp : pubT.time ≤ tp) (y : CKAView M₂ K₂) :
    SPTree.Timed.stepTime (prodCKARed₂.timed C₁ k m viewCost A ACost pubT y) ≤
      T + a + tv + tp + 2 :=
  ckaPubRedOf.tree.timeBound_timed _ _ viewCost A ACost hA hAc hv pubT hp y

end Prod

/-! ## The hybrid Diffie–Hellman and KEM CKA -/

section Hybrid

open CatCryptCore.Examples.CyclicGroupDDH

variable (G : Type) [CG : CyclicGroup G]

/-- The initialisation of `dhCKA` does not touch the heap. -/
theorem dhCKA_init_isPure : SPComp.IsPure (dhCKA G).init := by
  simp only [dhCKA]
  exact SPComp.bind_isPure (SPComp.sample_isPure CG.Exp) fun _ => SPComp.pure_isPure _

/-- Sending in `dhCKA` does not touch the heap. -/
theorem dhCKA_send_isPure (s : G × CG.Exp) : SPComp.IsPure ((dhCKA G).send s) := by
  simp only [dhCKA]
  exact SPComp.bind_isPure (SPComp.sample_isPure CG.Exp) fun _ => SPComp.pure_isPure _

/-- **CKA security of the hybrid DH and KEM CKA from DDH and KEM-CPA.** For a KEM whose key
generation and encapsulation do not touch the heap, every adversary `A`, challenge epoch
`k + 1` and `m` epochs after it, the CKA advantage of `prodCKA (dhCKA G) (kemCKA KEM)` is at
most the DDH advantage of `ckaDDHRed k m (prodCKARed₁ (kemCKA KEM) k m A)` plus the KEM-CPA
advantage of `kemCKARed KEM k m (prodCKARed₂ (dhCKA G) k m A)`. -/
theorem dhKemCKA_advantage_le {PK SK K E : Type} [Fintype K] [Nonempty K] [Fintype E]
    [Nonempty E] [Inhabited K] (KEM : KEMScheme PK SK K E) (hkgen : SPComp.IsPure KEM.kgen)
    (hencap : ∀ pk, SPComp.IsPure (KEM.encap pk)) (k m : ℕ)
    (A : CKAView (G × (Option E × PK)) (G × K) → SPComp Bool) :
    CKA_Advantage (prodCKA (dhCKA G) (kemCKA KEM)) k m A ≤
      DDH_Advantage G (ckaDDHRed k m (prodCKARed₁ (kemCKA KEM) k m A)) +
        KEM_CPA_Advantage KEM (kemCKARed KEM k m (prodCKARed₂ (dhCKA G) k m A)) := by
  rw [← cka_advantage_eq_ddh, ← kemCKA_advantage_eq KEM hkgen hencap]
  exact prodCKA_advantage_le _ _ (dhCKA_init_isPure G) (dhCKA_send_isPure G) k m A

end Hybrid

end CatCrypt.Crypto.Messaging
