/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.TLSSquare
public import CatCryptCore.Crypto.AKE.X3DHSquareSigned

/-!
# The TLS 1.3 handshake up to forgery of CertificateVerify

**Ideal functionality.** `F_AKEImp (SPComp.sample (TKey Sec)) srvImp true`: the multi-session key
exchange with adversarial key delivery, adaptive corruption, uniform keys in `TKey Sec` (CATS,
SATS, EMS, RMS) and the impersonation predicate `srvImp` of unilateral authentication.

**Real protocol.** `tlsRealOf A`: the full 1-RTT handshake of `TLSSquare`, in which a client
accepts the server flight when the CertificateVerify signature verifies under the registered key
of its peer and the server Finished is the key-derivation value at its transcript. Corruption is
adaptive: `corrupt p` reveals the signing key of `p`, except while `Pending` refuses it.

**Simulator.** `tlsSim A` of `TLSSquare`.

**The signed layer.** The real game `realGameK lazyKDF A` and the filtered game
`filtGameK lazyKDF A` differ at one transition: a client accepts a CertificateVerify signature
that verifies under the key of its uncorrupted peer `q` on a transcript that `q` did not sign
(`BadAt`). The forger `tlsForgeRed A p B` of the server `p` runs `B` against the filtered game
with the challenge key in place of the key of `p`, answers the CertificateVerify of `p` by the
signing oracle, and outputs the first such transcript and signature at `p`. The bound
`tlsSigBound A P B` is the sum over the servers `p` of `P` of the EUF-CMA advantages of these
forgers, when `B` names only servers of `P`.

## Main definitions

* `SrvIn`, `SrvNamesIn`: the events that name only servers of a finite set.
* `BadAt`: the transition at which the real and the filtered game differ, at a server.
* `forgeStep`, `forgeryAt`, `forgeLoop`, `tlsForgeRed`: the forger.
* `tlsSigBound`: the bound of the signatures.

## Main results

* `real_eq_filt`: the two games agree off the forbidden transitions.
* `flag_le_eufcma`: a forbidden transition at `p` is a forgery against the key of `p`.
* `advantage_real_filt_le`: the advantage between the real and the filtered game is at most
  `tlsSigBound`.
* `tls_realizesSim_oracleGame`: the real TLS protocol realizes `F_AKEImp … srvImp true` behind
  `tlsSim`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.TLSSquareSigned

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.Signatures
open CatCrypt.Crypto.AKE.X3DHSquare (KDFOp lazyKDF FEv FOut subView)
open CatCrypt.Crypto.AKE.TLSSquare
open CatCrypt.Crypto.AKE.X3DHSquareSigned (stopRed run_flagWhen_le_of_inv_on run_flagWhen_false
  run_flagWhen_union_le run_map_obs_eq_bind_run_set_of_trigger)
open CatCrypt.Crypto.AKE.X3DHSquareGDH (AllQ toOuterMeasure_le_one)
open CatCrypt.Crypto.PAKE.CPaceSquare (roAt)
open scoped ENNReal

/-! ## Gates and transitions -/

section Defs

variable {S W Tr VK SK Sig Sec T : Type}

/-- The state with the key pair `v` of the party `p`. -/
def modLt (p : PartyId) (v : Option (VK × SK)) (s : TRStT S W Tr VK SK Sec T) :
    TRStT S W Tr VK SK Sec T :=
  { s with lt := Function.update s.lt p v }

/-- The server session `x` answers a `srvRecv`. -/
def SrvGate (s : TRStT S W Tr VK SK Sec T) (x : Inst) : Prop :=
  ∃ r, s.st.recs x = some r ∧ r.role = .responder ∧ r.key = none ∧ s.srv x = none

/-- The client session `x`, with peer `q`, checks a `cliRecv`. -/
def CliGate (s : TRStT S W Tr VK SK Sec T) (x : Inst) (q : PartyId) : Prop :=
  ∃ r xs, s.st.recs x = some r ∧ s.eph x = some xs ∧ r.role = .initiator ∧ r.key = none ∧
    r.peer = q

/-- The events at which a step from `s` reads the key pair of `p`. -/
def TrigAt (p : PartyId) (s : TRStT S W Tr VK SK Sec T) : TOEv W Tr Sig Sec → Prop
  | .inr (.pub q) => q = p
  | .inr (.corrupt q) => q = p ∧ Pending s p = false
  | .inr (.srvRecv sid q _) => q = p ∧ SrvGate s (sid, q)
  | .inr (.cliRecv sid pid _ _ _) => CliGate s (sid, pid) p
  | _ => False

/-- The events at which a step from `s` reads the signing key of `p`. -/
def SignAt (p : PartyId) (s : TRStT S W Tr VK SK Sec T) : TOEv W Tr Sig Sec → Prop
  | .inr (.corrupt q) => q = p ∧ Pending s p = false
  | .inr (.srvRecv sid q _) => q = p ∧ SrvGate s (sid, q)
  | _ => False

/-- **A forbidden acceptance at the server `q`**: a client session with peer `q` receives a
CertificateVerify signature that verifies under the key of `q` after the step, on a transcript
that `q` did not sign, while `q` is not corrupt. -/
def BadAt (A : TLSAlg S W Tr VK SK Sig Sec) (q : PartyId) (s : TRStT S W Tr VK SK Sec T)
    (e : TOEv W Tr Sig Sec) (x : TOOut W VK SK Sig Sec × TRStT S W Tr VK SK Sec T) : Prop :=
  ∃ sid pid Y σ sf r xs kp, e = .inr (.cliRecv sid pid Y σ sf) ∧
    s.st.recs (sid, pid) = some r ∧ s.eph (sid, pid) = some xs ∧ r.role = .initiator ∧
    r.key = none ∧ r.peer = q ∧ x.2.lt q = some kp ∧
    A.sig.verify kp.1 (A.trCert (A.tr1 sid pid q (A.pub xs) Y) kp.1) σ = true ∧
    s.st.corrupt q = false ∧ A.trCert (A.tr1 sid pid q (A.pub xs) Y) kp.1 ∉ s.log q

/-- A forbidden acceptance at some server. -/
def RealBad (A : TLSAlg S W Tr VK SK Sig Sec) (s : TRStT S W Tr VK SK Sec T)
    (e : TOEv W Tr Sig Sec) (x : TOOut W VK SK Sig Sec × TRStT S W Tr VK SK Sec T) : Prop :=
  ∃ q, BadAt A q s e x

/-- The events that start client sessions only with servers of `P` and server sessions only of
parties of `P`. -/
def SrvIn (P : Finset PartyId) : TOEv W Tr Sig Sec → Prop
  | .inl (.newSession _ _ peer .initiator) => peer ∈ P
  | .inl (.newSession _ pid _ .responder) => pid ∈ P
  | _ => True

/-- `SrvNamesIn P B`: on every path, the oracle adversary `B` starts client sessions only with
servers of `P` and server sessions only of parties of `P`. -/
def SrvNamesIn {α : Type} (P : Finset PartyId)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) α) : Prop :=
  AllQ (SrvIn P) B

end Defs

/-! ## The forger -/

section Forger

variable {S W Tr VK SK Sig Sec : Type} [Fintype S] [Nonempty S] [DecidableEq W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec]

/-- The step of the filtered protocol with the lazily sampled key derivation. -/
noncomputable abbrev filtO (A : TLSAlg S W Tr VK SK Sig Sec) :
    TRSt S W Tr VK SK Sec → TOEv W Tr Sig Sec →
      PMF (TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec) :=
  (filtGameK lazyKDF A).oracle ()

/-- The step of the real protocol with the lazily sampled key derivation. -/
noncomputable abbrev realO (A : TLSAlg S W Tr VK SK Sig Sec) :
    TRSt S W Tr VK SK Sec → TOEv W Tr Sig Sec →
      PMF (TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec) :=
  (realGameK lazyKDF A).oracle ()

/-- A signing key of the scheme of `A`: the key generation at some coins. -/
noncomputable def skDummy (A : TLSAlg S W Tr VK SK Sig Sec) : SK :=
  (A.sig.keygen (Classical.arbitrary A.sig.KR)).2

/-- The server flight of the session `(sid, p)` with the record `r` on the share `X`, signed by a
query to the signing oracle, with the verification key `pk`. -/
noncomputable def srvQ (A : TLSAlg S W Tr VK SK Sig Sec) (pk : VK)
    (s : TRSt S W Tr VK SK Sec) (sid : SessionId) (p : PartyId) (r : Rec (TKey Sec)) (X : W) :
    OracleAdv Tr Sig (TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec) :=
  .rand (PMF.uniformFintype S) fun y =>
    .query (A.trCert (A.tr1 sid r.peer p X (A.pub y)) pk) fun σ =>
      .rand ((roAt s.ro ⟨.sfin, A.trCV (A.trCert (A.tr1 sid r.peer p X (A.pub y)) pk) σ,
          A.dh y X⟩).bind fun sf =>
        (roAt sf.2 ⟨.cfin, A.trSF (A.trCV (A.trCert (A.tr1 sid r.peer p X (A.pub y)) pk) σ)
          sf.1, A.dh y X⟩).map fun cf =>
          ((Sum.inr (.srvMsg (some (A.pub y, pk, σ, sf.1))) : TOOut W VK SK Sig Sec),
            { s with
              srv := Function.update s.srv (sid, p) (some (A.trSF (A.trCV (A.trCert
                (A.tr1 sid r.peer p X (A.pub y)) pk) σ) sf.1, A.dh y X, cf.1))
              log := Function.update s.log p
                (A.trCert (A.tr1 sid r.peer p X (A.pub y)) pk :: s.log p)
              ro := cf.2 })) .ret

/-- The step of the filtered protocol run by the forger of `p` with the key pair `(pk, sk₀)` in
place of the key pair of `p`, which is removed from the state afterwards. -/
noncomputable def genStep (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId) (pk : VK)
    (s : TRSt S W Tr VK SK Sec) (e : TOEv W Tr Sig Sec) :
    OracleAdv Tr Sig (TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec) :=
  .rand (filtO A (modLt p (some (pk, skDummy A)) s) e) fun y => .ret (y.1, modLt p none y.2)

/-- **A step of the filtered world simulated by the forger of `p`** with the challenge key `pk`:
the CertificateVerify of a server session of `p` is a query to the signing oracle; every other
event is `genStep`. -/
noncomputable def forgeStep (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId) (pk : VK)
    (s : TRSt S W Tr VK SK Sec) (e : TOEv W Tr Sig Sec) :
    OracleAdv Tr Sig (TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec) :=
  match e with
  | .inr (.srvRecv sid q X) =>
    match s.st.recs (sid, q) with
    | some r =>
      if q = p ∧ r.role = .responder ∧ r.key.isNone ∧ (s.srv (sid, q)).isNone then
        srvQ A pk s sid p r X
      else genStep A p pk s e
    | none => genStep A p pk s e
  | _ => genStep A p pk s e

/-- The forgery found at a step: a transcript and a CertificateVerify signature that verifies
under `pk`, delivered to a client session with peer `p`, `p` not corrupt, on a transcript that
`p` did not sign. -/
noncomputable def forgeryAt (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId) (pk : VK)
    (s : TRSt S W Tr VK SK Sec) : TOEv W Tr Sig Sec → Option (Tr × Sig)
  | .inr (.cliRecv sid pid Y σ _) =>
    match s.st.recs (sid, pid), s.eph (sid, pid) with
    | some r, some xs =>
      if r.role = .initiator ∧ r.key = none ∧ r.peer = p ∧
          A.sig.verify pk (A.trCert (A.tr1 sid pid p (A.pub xs) Y) pk) σ = true ∧
          s.st.corrupt p = false ∧ A.trCert (A.tr1 sid pid p (A.pub xs) Y) pk ∉ s.log p then
        some (A.trCert (A.tr1 sid pid p (A.pub xs) Y) pk, σ)
      else none
    | _, _ => none
  | _ => none

/-- **The loop of the forger** of `p` with the challenge key `pk`: it runs the oracle adversary
`B` against the simulated filtered world and stops at the first forgery; without a forgery it
asks the signing oracle at `m₀` and outputs the answer. -/
noncomputable def forgeLoop (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId) (pk : VK) (m₀ : Tr) :
    OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool → TRSt S W Tr VK SK Sec →
      OracleAdv Tr Sig (Tr × Sig) :=
  stopRed (forgeStep A p pk) (fun t e => forgeryAt A p pk t e)
    (.query m₀ fun σ => .ret (m₀, σ))

/-- **The forger of the server `p`** against the signature scheme of `A`, for the oracle
adversary `B` of the real protocol: on the verification key `pk` it runs `forgeLoop` from the
initial state. -/
noncomputable def tlsForgeRed (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) (vk : VK) :
    OracleAdv Tr Sig (Tr × Sig) :=
  forgeLoop A p vk (A.tr1 0 0 0 (A.pub (Classical.arbitrary S)) (A.pub (Classical.arbitrary S)))
    B (tInitK lazyKDF)

open Classical in
/-- **The bound of the signatures** at the oracle adversary `B` and the finite set of servers
`P`: the sum over `P` of the EUF-CMA advantages of the forgers, when `B` names only servers of
`P`, and `⊤` otherwise. -/
noncomputable def tlsSigBound (A : TLSAlg S W Tr VK SK Sig Sec) (P : Finset PartyId)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) : ℝ≥0∞ :=
  if SrvNamesIn P B then
    ∑ p ∈ P, eufcmaAdvantage A.sig.toSigScheme (toEUFAdversary (tlsForgeRed A p B))
  else ⊤

/-! ## Up to forgery -/

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- `ltAt` changes only the key pair of `q`, which it sets to its answer. -/
theorem ltAt_support {T : Type} (A : TLSAlg S W Tr VK SK Sig Sec) (s : TRStT S W Tr VK SK Sec T)
    (q : PartyId) (l : (VK × SK) × TRStT S W Tr VK SK Sec T) (hl : l ∈ (ltAt A s q).support) :
    l.2 = { s with lt := Function.update s.lt q (some l.1) } ∧
      ∀ v, s.lt q = some v → l.1 = v := by
  unfold ltAt at hl
  split at hl
  · rename_i v hv
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hl
    subst hl
    refine ⟨?_, fun w hw => by rw [hv] at hw; exact Option.some.inj hw⟩
    cases s
    simp only [TRStT.mk.injEq, true_and]
    grind
  · rename_i hv
    simp only [PMF.support_map, Set.mem_image] at hl
    obtain ⟨v, -, rfl⟩ := hl
    exact ⟨rfl, fun w hw => by rw [hv] at hw; cases hw⟩

/-- The state `s'` extends `s`: every record of `s'` has the peer and role of a record of `s`, and
the corrupt parties, the signed transcripts and the key pairs of `s` persist. -/
def Grows {T : Type} (s s' : TRStT S W Tr VK SK Sec T) : Prop :=
  (∀ y r', s'.st.recs y = some r' → ∃ r, s.st.recs y = some r ∧ r.peer = r'.peer ∧
      r.role = r'.role) ∧
    (∀ q, s.st.corrupt q = true → s'.st.corrupt q = true) ∧
    (∀ q m, m ∈ s.log q → m ∈ s'.log q) ∧ (∀ q v, s.lt q = some v → s'.lt q = some v)

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- Every state extends itself. -/
theorem Grows.refl {T : Type} (s : TRStT S W Tr VK SK Sec T) : Grows s s :=
  ⟨fun _ r h => ⟨r, h, rfl, rfl⟩, fun _ h => h, fun _ _ h => h, fun _ _ h => h⟩

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- Extension is transitive. -/
theorem Grows.trans {T : Type} {s₁ s₂ s₃ : TRStT S W Tr VK SK Sec T} (h₁ : Grows s₁ s₂)
    (h₂ : Grows s₂ s₃) : Grows s₁ s₃ := by
  obtain ⟨a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := h₂
  refine ⟨fun y r' h => ?_, fun q h => b₂ q (b₁ q h), fun q m h => c₂ q m (c₁ q m h),
    fun q v h => d₂ q v (d₁ q v h)⟩
  obtain ⟨r, hr, hp, hro⟩ := a₂ y r' h
  obtain ⟨r₀, hr₀, hp₀, hro₀⟩ := a₁ y r hr
  exact ⟨r₀, hr₀, hp₀.trans hp, hro₀.trans hro⟩

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- A state with the same records, corruptions and key pairs and longer logs extends `s`. -/
theorem grows_of_eq {T : Type} {s s' : TRStT S W Tr VK SK Sec T} (h₁ : s'.st = s.st)
    (h₂ : s'.lt = s.lt) (h₃ : ∀ q m, m ∈ s.log q → m ∈ s'.log q) : Grows s s' := by
  refine ⟨fun y r' h => ⟨r', by rw [← h₁]; exact h, rfl, rfl⟩, fun q h => by rw [h₁]; exact h,
    h₃, fun q v h => by rw [h₂]; exact h⟩

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- `ltAt` extends the state. -/
theorem grows_ltAt {T : Type} (A : TLSAlg S W Tr VK SK Sig Sec) (s : TRStT S W Tr VK SK Sec T)
    (q : PartyId) (l : (VK × SK) × TRStT S W Tr VK SK Sec T) (hl : l ∈ (ltAt A s q).support) :
    Grows s l.2 := by
  obtain ⟨h₁, h₂⟩ := ltAt_support A s q l hl
  refine ⟨fun y r' h => ⟨r', by rw [h₁] at h; exact h, rfl, rfl⟩,
    fun q' h => by rw [h₁]; exact h, fun q' m h => by rw [h₁]; exact h, fun q' v h => ?_⟩
  rw [h₁]
  by_cases hq : q' = q
  · subst hq
    simp [h₂ v h]
  · simp [Function.update_of_ne hq, h]

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- `setKey` extends the state. -/
theorem grows_setKey {T : Type} (s : TRStT S W Tr VK SK Sec T) (x : Inst) (k : TKey Sec)
    (ro : T) : Grows s (setKey s x k ro) := by
  refine ⟨fun y r' h => ?_, fun q h => ?_, fun _ _ h => h, fun _ _ h => h⟩
  · simp only [setKey] at h
    split at h
    · rename_i r hr
      simp only [setRec] at h
      by_cases hy : y = x
      · subst hy
        simp only [Function.update_self, Option.some.injEq] at h
        subst h
        exact ⟨r, hr, rfl, rfl⟩
      · rw [Function.update_of_ne hy] at h
        exact ⟨r', h, rfl, rfl⟩
    · exact ⟨r', h, rfl, rfl⟩
  · simp only [setKey]
    split
    · exact h
    · exact h

/-- **A step of the filtered protocol extends the state**, but for a new session. -/
theorem filtO_support (A : TLSAlg S W Tr VK SK Sig Sec) (s : TRSt S W Tr VK SK Sec)
    (e : TOEv W Tr Sig Sec) (x : TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec)
    (hx : x ∈ (filtO A s e).support) :
    Grows s x.2 ∨ ∃ sid pid peer role, e = .inl (.newSession sid pid peer role) ∧
      x.2.st = addSession s.st (sid, pid) peer role ∧ x.2.lt = s.lt ∧ x.2.log = s.log := by
  rcases e with h | a
  · cases h with
    | newSession sid pid peer role =>
      simp only [filtO, filtGameK, gameK, realHonK, PMF.support_map, Set.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      split_ifs at hy
      · simp only [lazyKDF, PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact Or.inr ⟨sid, pid, peer, role, rfl, rfl, rfl, rfl⟩
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact Or.inl (Grows.refl _)
    | getKey sid pid =>
      simp only [filtO, filtGameK, gameK, realHonK, PMF.pure_map, PMF.support_pure,
        Set.mem_singleton_iff] at hx
      subst hx
      exact Or.inl (Grows.refl _)
  · left
    simp only [filtO, filtGameK, gameK, PMF.support_map, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change Grows s y.2
    cases a with
    | idle =>
      simp only [realAdvK, PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact Grows.refl _
    | poll =>
      simp only [realAdvK, PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨fun y r' h => ⟨r', ?_, rfl, rfl⟩, fun q h => ?_, fun _ _ h => h, fun _ _ h => h⟩
      · simp only [pollStep] at h
        split at h <;> exact h
      · simp only [pollStep]
        split <;> exact h
    | pub q =>
      simp only [realAdvK, PMF.support_map, Set.mem_image] at hy
      obtain ⟨l, hl, rfl⟩ := hy
      exact grows_ltAt A s q l hl
    | corrupt q =>
      simp only [realAdvK, corruptK] at hy
      split at hy
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact Grows.refl _
      simp only [PMF.support_map, Set.mem_image] at hy
      obtain ⟨l, hl, rfl⟩ := hy
      refine (grows_ltAt A s q l hl).trans ⟨fun y r' h => ⟨r', h, rfl, rfl⟩, fun q' h => ?_,
        fun _ _ h => h, fun _ _ h => h⟩
      simp only [corruptStep]
      by_cases hq : q' = q
      · subst hq; simp
      · simp [Function.update_of_ne hq, h]
    | hello sid pid =>
      simp only [realAdvK, helloStep] at hy
      split at hy
      · split_ifs at hy
        · split at hy
          · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
            subst hy
            exact Grows.refl _
          · simp only [PMF.support_map, Set.mem_image] at hy
            obtain ⟨_, -, rfl⟩ := hy
            exact grows_of_eq rfl rfl fun _ _ h => h
        · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
          subst hy
          exact Grows.refl _
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact Grows.refl _
    | srvRecv sid pid X =>
      simp only [realAdvK, srvRecvK] at hy
      split at hy
      · split_ifs at hy
        · simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hy
          obtain ⟨l, hl, _, -, _, -, _, -, _, -, rfl⟩ := hy
          refine (grows_ltAt A s pid l hl).trans (grows_of_eq rfl rfl fun q m h => ?_)
          by_cases hq : q = pid
          · subst hq; simp [h]
          · simp [Function.update_of_ne hq, h]
        · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
          subst hy
          exact Grows.refl _
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact Grows.refl _
    | cliRecv sid pid Y σ sf =>
      simp only [realAdvK, PMF.support_bind, Set.mem_iUnion] at hy
      obtain ⟨c, hc, hy⟩ := hy
      have hc' : Grows s c.2 := by
        simp only [cliCheckK] at hc
        split at hc
        · split_ifs at hc
          · simp only [PMF.support_bind, Set.mem_iUnion] at hc
            obtain ⟨l, hl, sv, -, hc⟩ := hc
            refine (grows_ltAt A s _ l hl).trans ?_
            split_ifs at hc
            · simp only [PMF.support_map, Set.mem_image] at hc
              obtain ⟨_, -, rfl⟩ := hc
              exact grows_of_eq rfl rfl fun _ _ h => h
            · simp only [PMF.support_pure, Set.mem_singleton_iff] at hc
              subst hc
              exact grows_of_eq rfl rfl fun _ _ h => h
          · simp only [PMF.support_pure, Set.mem_singleton_iff] at hc
            subst hc
            exact Grows.refl _
        · simp only [PMF.support_pure, Set.mem_singleton_iff] at hc
          subst hc
          exact Grows.refl _
      split at hy
      · simp only [PMF.support_map, Set.mem_image] at hy
        obtain ⟨k, -, rfl⟩ := hy
        exact hc'.trans (grows_setKey _ _ _ _)
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact hc'
    | srvFin sid pid cf =>
      simp only [realAdvK] at hy
      split at hy
      · simp only [PMF.support_map, Set.mem_image] at hy
        obtain ⟨k, -, rfl⟩ := hy
        exact grows_setKey _ _ _ _
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact Grows.refl _
    | kdf z =>
      simp only [realAdvK, PMF.support_map, Set.mem_image] at hy
      obtain ⟨_, -, rfl⟩ := hy
      exact grows_of_eq rfl rfl fun _ _ h => h

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- `ltAt` at a party with a key pair answers it. -/
theorem ltAt_of_some {T : Type} (A : TLSAlg S W Tr VK SK Sig Sec) (s : TRStT S W Tr VK SK Sec T)
    (q : PartyId) (kp : VK × SK) (h : s.lt q = some kp) : ltAt A s q = PMF.pure (kp, s) := by
  simp [ltAt, h]

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- `ltAt` at another party commutes with the change of the key pair of `p`. -/
theorem ltAt_modLt_ne {T : Type} (A : TLSAlg S W Tr VK SK Sig Sec)
    (s : TRStT S W Tr VK SK Sec T) (p q : PartyId) (v : Option (VK × SK)) (hq : q ≠ p) :
    ltAt A (modLt p v s) q = (ltAt A s q).map (Prod.map id (modLt p v)) := by
  unfold ltAt
  have h : (modLt p v s).lt q = s.lt q := by simp [modLt, Function.update_of_ne hq]
  rw [h]
  split
  · rw [PMF.pure_map]
    rfl
  · rw [PMF.map_comp]
    congr 1
    funext l
    simp only [Function.comp_apply, Prod.map_apply, id_eq, modLt, Prod.mk.injEq, true_and]
    congr 1
    exact Function.update_comm (Ne.symm hq) _ _ _

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- `setKey` commutes with the change of a key pair. -/
theorem setKey_modLt {T : Type} (s : TRStT S W Tr VK SK Sec T) (p : PartyId)
    (v : Option (VK × SK)) (x : Inst) (k : TKey Sec) (ro : T) :
    setKey (modLt p v s) x k ro = modLt p v (setKey s x k ro) := rfl

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- The fields of `modLt` other than the key pairs: unfolding lemma. -/
@[simp] theorem modLt_fields {T : Type} (s : TRStT S W Tr VK SK Sec T) (p : PartyId)
    (v : Option (VK × SK)) :
    (modLt p v s).st = s.st ∧ (modLt p v s).eph = s.eph ∧ (modLt p v s).srv = s.srv ∧
      (modLt p v s).log = s.log ∧ (modLt p v s).ro = s.ro :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- The refusal of a corruption does not read the key pairs. -/
@[simp] theorem pending_modLt {T : Type} (s : TRStT S W Tr VK SK Sec T) (p q : PartyId)
    (v : Option (VK × SK)) : Pending (modLt p v s) q = Pending s q :=
  rfl

/-- **The step does not depend on the signing key of `p` at an event that does not read it**: a
change of the key pair of `p` that keeps the verification key commutes with the step, and so does
any change at an event that does not read the key pair of `p`. -/
theorem filtO_modLt (A : TLSAlg S W Tr VK SK Sig Sec) (s : TRSt S W Tr VK SK Sec) (p : PartyId)
    (v : Option (VK × SK)) (e : TOEv W Tr Sig Sec)
    (hC : ¬ TrigAt p s e ∨ ∃ kp kp', s.lt p = some kp ∧ v = some kp' ∧ kp.1 = kp'.1 ∧
      ¬ SignAt p s e) :
    filtO A (modLt p v s) e = (filtO A s e).map (Prod.map id (modLt p v)) := by
  rcases e with h | a
  · simp only [filtO, filtGameK, gameK, PMF.map_comp]
    cases h with
    | newSession sid pid peer role =>
      simp only [realHonK, lazyKDF, modLt_fields]
      split_ifs <;> simp only [PMF.pure_map] <;> rfl
    | getKey sid pid =>
      simp only [realHonK, PMF.pure_map]
      rfl
  · simp only [filtO, filtGameK, gameK, PMF.map_comp]
    cases a with
    | idle => simp only [realAdvK, PMF.pure_map]; rfl
    | poll => simp only [realAdvK, PMF.pure_map]; rfl
    | kdf z => simp only [realAdvK, PMF.map_comp]; rfl
    | pub q =>
      simp only [realAdvK, PMF.map_comp]
      by_cases hq : q = p
      · subst hq
        rcases hC with hC | ⟨kp, kp', hk, rfl, h1, -⟩
        · exact absurd rfl hC
        rw [ltAt_of_some A _ q kp' (by simp [modLt]), ltAt_of_some A _ q kp hk]
        simp only [PMF.pure_map, Function.comp_apply, Prod.map_apply, id_eq, h1]
      · rw [ltAt_modLt_ne A s p q v hq, PMF.map_comp]
        rfl
    | corrupt q =>
      simp only [realAdvK, corruptK, pending_modLt]
      by_cases hP : Pending s q = true
      · simp only [hP, ↓reduceIte, PMF.pure_map]
        rfl
      · simp only [hP, Bool.false_eq_true, ↓reduceIte]
        by_cases hq : q = p
        · subst hq
          rcases hC with hC | ⟨kp, kp', -, -, -, hS⟩
          · exact absurd ⟨rfl, by simpa using hP⟩ hC
          · exact absurd ⟨rfl, by simpa using hP⟩ hS
        · rw [ltAt_modLt_ne A s p q v hq]
          simp only [PMF.map_comp]
          rfl
    | hello sid pid =>
      simp only [realAdvK, helloStep, modLt_fields]
      split
      · split_ifs
        · split <;> simp only [PMF.pure_map, PMF.map_comp] <;> rfl
        · simp only [PMF.pure_map]
          rfl
      · simp only [PMF.pure_map]
        rfl
    | srvRecv sid q X =>
      simp only [realAdvK, srvRecvK, modLt_fields]
      split
      · rename_i r hr
        split_ifs with hg
        · by_cases hq : q = p
          · subst hq
            have hT : SrvGate s (sid, q) :=
              ⟨r, hr, hg.1, by simpa using hg.2.1, by simpa using hg.2.2⟩
            rcases hC with hC | ⟨kp, kp', -, -, -, hS⟩
            · exact absurd ⟨rfl, hT⟩ hC
            · exact absurd ⟨rfl, hT⟩ hS
          · rw [ltAt_modLt_ne A s p q v hq]
            simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
            rfl
        · simp only [PMF.pure_map]
          rfl
      · simp only [PMF.pure_map]
        rfl
    | cliRecv sid pid Y σ sf =>
      simp only [realAdvK, cliCheckK, modLt_fields]
      split
      · rename_i r xs hr he
        split_ifs with hg
        · by_cases hq : r.peer = p
          · rcases hC with hC | ⟨kp, kp', hk, rfl, h1, -⟩
            · exact absurd ⟨r, xs, hr, he, hg.1, by simpa using hg.2, hq⟩ hC
            · rw [hq, ltAt_of_some A _ p kp' (by simp [modLt]), ltAt_of_some A _ p kp hk]
              simp only [PMF.pure_bind, PMF.bind_bind, PMF.map_bind, h1]
              congr 1
              funext sv
              simp only [modLt_fields]
              split_ifs
              · simp only [PMF.bind_map]
                congr 1
                funext cf
                simp only [Function.comp_apply, PMF.map_comp]
                rfl
              · simp only [PMF.pure_bind, PMF.pure_map]
                rfl
          · rw [ltAt_modLt_ne A s p r.peer v hq]
            simp only [PMF.bind_map, PMF.bind_bind, PMF.map_bind]
            congr 1
            funext l
            simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, modLt_fields,
              PMF.bind_bind]
            congr 1
            funext sv
            split_ifs
            · simp only [PMF.bind_map]
              congr 1
              funext cf
              simp only [Function.comp_apply, PMF.map_comp]
              rfl
            · simp only [PMF.pure_bind, PMF.pure_map]
              rfl
        · simp only [PMF.pure_bind, PMF.pure_map]
          rfl
      · simp only [PMF.pure_bind, PMF.pure_map]
        rfl
    | srvFin sid pid cf =>
      simp only [realAdvK]
      have hf : srvFinCheck (modLt p v s) (sid, pid) cf = srvFinCheck s (sid, pid) cf := rfl
      rw [hf]
      rcases srvFinCheck s (sid, pid) cf with _ | c
      · simp only [PMF.pure_map]
        rfl
      · simp only [PMF.map_comp]
        rfl

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- The first use of the key pair of `p` draws its key coins. -/
theorem ltAt_none {T : Type} (A : TLSAlg S W Tr VK SK Sig Sec) (s : TRStT S W Tr VK SK Sec T)
    (p : PartyId) (hk : s.lt p = none) :
    ltAt A s p = (PMF.uniformFintype A.sig.KR).bind fun kr =>
      ltAt A (modLt p (some (A.sig.keygen kr)) s) p := by
  unfold ltAt
  rw [hk]
  simp only [modLt, Function.update_self, PSigScheme.keyDist, PMF.map_comp]
  rw [PMF.map]
  rfl

/-- **The key pair of `p` drawn at its first use.** At an event that reads the key pair of `p`,
from a state without one, the step is the draw of the key coins followed by the step from the
state with the key pair of the coins in place. -/
theorem filtO_trigger (A : TLSAlg S W Tr VK SK Sig Sec) (s : TRSt S W Tr VK SK Sec) (p : PartyId)
    (e : TOEv W Tr Sig Sec) (hk : s.lt p = none) (he : TrigAt p s e) :
    filtO A s e = (PMF.uniformFintype A.sig.KR).bind fun kr =>
      filtO A (modLt p (some (A.sig.keygen kr)) s) e := by
  rcases e with h | a
  · exact he.elim
  simp only [filtO, filtGameK, gameK]
  cases a with
  | pub q =>
    obtain rfl : q = p := he
    simp only [realAdvK]
    rw [ltAt_none A s q hk]
    simp only [PMF.map_bind]
  | corrupt q =>
    obtain ⟨rfl, hP⟩ := he
    simp only [realAdvK, corruptK, pending_modLt, hP, Bool.false_eq_true, ↓reduceIte]
    rw [ltAt_none A s q hk]
    simp only [PMF.map_bind]
  | srvRecv sid q X =>
    obtain ⟨rfl, r, hr, h1, h2, h3⟩ := he
    simp only [realAdvK, srvRecvK, modLt_fields, hr, h1, h2, h3, Option.isNone_none, and_self,
      ↓reduceIte]
    rw [ltAt_none A s q hk]
    simp only [PMF.bind_bind, PMF.map_bind]
  | cliRecv sid pid Y σ sf =>
    obtain ⟨r, xs, hr, he', h1, h2, rfl⟩ := he
    simp only [realAdvK, cliCheckK, modLt_fields, hr, he', h1, h2, Option.isNone_none, and_self,
      ↓reduceIte]
    rw [ltAt_none A s r.peer hk]
    simp only [PMF.bind_bind, PMF.map_bind]
  | _ => exact he.elim

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- Setting the key pair of `p` to its value leaves the state unchanged. -/
theorem modLt_eq_self {T : Type} (s : TRStT S W Tr VK SK Sec T) (p : PartyId)
    (v : Option (VK × SK)) (h : s.lt p = v) : modLt p v s = s := by
  cases s
  simp only [modLt, TRStT.mk.injEq, and_true, true_and]
  subst h
  exact Function.update_eq_self _ _

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- The last change of the key pair of `p` wins. -/
@[simp] theorem modLt_modLt {T : Type} (s : TRStT S W Tr VK SK Sec T) (p : PartyId)
    (v w : Option (VK × SK)) : modLt p v (modLt p w s) = modLt p v s := by
  simp [modLt]

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- The key pair of `p` after `modLt p v` is `v`. -/
@[simp] theorem modLt_lt_self {T : Type} (s : TRStT S W Tr VK SK Sec T) (p : PartyId)
    (v : Option (VK × SK)) : (modLt p v s).lt p = v := by
  simp [modLt]

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- A forbidden acceptance at `p` reads the key pair of `p`. -/
theorem trigAt_of_badAt {T : Type} (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId)
    (s : TRStT S W Tr VK SK Sec T) (e : TOEv W Tr Sig Sec)
    (x : TOOut W VK SK Sig Sec × TRStT S W Tr VK SK Sec T) (h : BadAt A p s e x) :
    TrigAt p s e := by
  obtain ⟨sid, pid, Y, σ, sf, r, xs, kp, rfl, hr, he, hro, hk, hpe, -⟩ := h
  exact ⟨r, xs, hr, he, hro, hk, hpe⟩

/-- A step at an event that does not read the key pair of `p` keeps it. -/
theorem filtO_lt_of_not_trig (A : TLSAlg S W Tr VK SK Sig Sec) (s : TRSt S W Tr VK SK Sec)
    (p : PartyId) (e : TOEv W Tr Sig Sec) (he : ¬ TrigAt p s e)
    (x : TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec) (hx : x ∈ (filtO A s e).support) :
    x.2.lt p = s.lt p := by
  have h := filtO_modLt A s p (s.lt p) e (Or.inl he)
  rw [modLt_eq_self s p _ rfl] at h
  rw [h, PMF.support_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  simp

open Classical in
/-- **The key pair of `p` drawn at the start.** The probability that the filtered world makes a
forbidden acceptance at `p` is the average over the key coins of that probability from the state
with the key pair of the coins in place for `p`. -/
theorem flag_lazy (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A)) B
        (tInitK lazyKDF, false)).toOuterMeasure {y | y.2.2 = true} =
      ∑' kr, PMF.uniformFintype A.sig.KR kr *
        (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A)) B
          (modLt p (some (A.sig.keygen kr)) (tInitK lazyKDF), false)).toOuterMeasure
          {y | y.2.2 = true} := by
  have h := run_map_obs_eq_bind_run_set_of_trigger (PMF.uniformFintype A.sig.KR)
    (OracleAdv.flagWhen (BadAt A p) (filtO A))
    (fun kr (s : TRSt S W Tr VK SK Sec × Bool) => (modLt p (some (A.sig.keygen kr)) s.1, s.2))
    Prod.snd (fun _ _ => rfl) (fun s => s.1.lt p = none) (fun s d => TrigAt p s.1 d)
    (fun s d hs hcs => by
      simp only [OracleAdv.flagWhen]
      rw [filtO_trigger A s.1 p d hs hcs, PMF.map_bind]
      rfl)
    (fun k s d hs hcs => by
      simp only [OracleAdv.flagWhen]
      rw [filtO_modLt A s.1 p _ d (Or.inl hcs), PMF.map_comp, PMF.map_comp]
      congr 1
      funext x
      have h1 : ¬ BadAt A p s.1 d x := fun h => hcs (trigAt_of_badAt A p _ _ _ h)
      have h2 : ¬ BadAt A p (modLt p (some (A.sig.keygen k)) s.1) d
          (x.1, modLt p (some (A.sig.keygen k)) x.2) := fun h =>
        hcs (trigAt_of_badAt A p _ _ _ h)
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, h1, decide_false,
        Bool.or_false]
      simp only [Prod.map, id_eq] at h2 ⊢
      simp [h2])
    (fun s d hs hcs x hx => by
      simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (filtO_lt_of_not_trig A s.1 p d hcs y hy).trans hs)
    B (tInitK lazyKDF, false) rfl
  have hm : ∀ s, (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A)) B
      s).toOuterMeasure {y | y.2.2 = true} =
      ((OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A)) B s).map
        fun y => (y.1, y.2.2)).toOuterMeasure {z | z.2 = true} := fun s => by
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  rw [hm, h, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun kr => ?_
  rw [hm]

/-- The signing log of the forger of `p` with the key `pk` after a step from `s` at `e` with
answer `x.1`: the CertificateVerify of a server session of `p` is appended to `L`. -/
def logNext (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId) (pk : VK)
    (s : TRSt S W Tr VK SK Sec) (L : List (Tr × Sig)) (e : TOEv W Tr Sig Sec)
    (x : TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec) : List (Tr × Sig) :=
  match e, x.1 with
  | .inr (.srvRecv sid q X), .inr (.srvMsg (some (Y, _, σ, _))) =>
    match s.st.recs (sid, q) with
    | some r =>
      if q = p ∧ r.role = .responder ∧ r.key.isNone ∧ (s.srv (sid, q)).isNone then
        L ++ [(A.trCert (A.tr1 sid r.peer p X Y) pk, σ)]
      else L
    | none => L
  | _, _ => L

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- The gate of `srvRecv` as the condition of `srvRecvK`. -/
theorem srvGate_iff {T : Type} (s : TRStT S W Tr VK SK Sec T) (x : Inst) (r : Rec (TKey Sec))
    (hr : s.st.recs x = some r) :
    SrvGate s x ↔ r.role = .responder ∧ r.key.isNone = true ∧ (s.srv x).isNone = true := by
  simp [SrvGate, hr, Option.isNone_iff_eq_none]

/-- Off the signing of `p`, the forger runs `genStep`. -/
theorem forgeStep_of_not_signAt (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId) (pk : VK)
    (s : TRSt S W Tr VK SK Sec) (e : TOEv W Tr Sig Sec) (he : ¬ SignAt p s e) :
    forgeStep A p pk s e = genStep A p pk s e := by
  rcases e with h | a
  · rfl
  cases a with
  | srvRecv sid q X =>
    simp only [forgeStep]
    rcases hr : s.st.recs (sid, q) with _ | r
    · rfl
    simp only
    split_ifs with hc
    · obtain ⟨rfl, hg⟩ := hc
      exact absurd ⟨rfl, (srvGate_iff s _ r hr).mpr hg⟩ he
    · rfl
  | _ => rfl

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec]
  [Nonempty Sec] in
/-- Off the signing of `p`, the log of the forger is unchanged. -/
theorem logNext_of_not_signAt (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId) (pk : VK)
    (s : TRSt S W Tr VK SK Sec) (L : List (Tr × Sig)) (e : TOEv W Tr Sig Sec)
    (x : TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec) (he : ¬ SignAt p s e) :
    logNext A p pk s L e x = L := by
  unfold logNext
  split
  · rename_i sid q X Y _ σ _ _
    split
    · rename_i r hr
      split_ifs with hc
      · obtain ⟨rfl, hg⟩ := hc
        exact absurd ⟨rfl, (srvGate_iff s _ r hr).mpr hg⟩ he
      · rfl
    · rfl
  · rfl

/-- **The forger simulates the filtered world.** From a state without a key pair for `p`, at an
event other than an unrefused `corrupt p`, the step of the forger against the signing oracle of
`sk` is the step of the filtered world with the key pair `(pk, sk)` in place for `p`, the key pair
removed afterwards, and the signing log extended by `logNext`. -/
theorem run_forgeStep (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId) (pk : VK) (sk : SK)
    (t : TRSt S W Tr VK SK Sec) (e : TOEv W Tr Sig Sec) (L : List (Tr × Sig))
    (hk : t.lt p = none) (he : ¬ (e = .inr (.corrupt p) ∧ Pending t p = false)) :
    OracleAdv.run (signOracle A.sig sk) (forgeStep A p pk t e) L =
      (filtO A (modLt p (some (pk, sk)) t) e).map fun x =>
        ((x.1, modLt p none x.2), logNext A p pk t L e x) := by
  by_cases hS : SignAt p t e
  · rcases e with h | a
    · exact hS.elim
    cases a with
    | srvRecv sid q X =>
      obtain ⟨rfl, r, hr, h1, h2, h3⟩ := hS
      have hg : r.role = .responder ∧ r.key.isNone = true ∧ (t.srv (sid, q)).isNone = true :=
        (srvGate_iff t _ r hr).mp ⟨r, hr, h1, h2, h3⟩
      simp only [forgeStep, hr, hg, and_self, ↓reduceIte, filtO, filtGameK, gameK, realAdvK,
        srvRecvK, modLt_fields]
      rw [ltAt_of_some A _ q (pk, sk) (modLt_lt_self _ _ _)]
      simp only [srvQ, OracleAdv.run_rand, OracleAdv.run_query, OracleAdv.run_ret, signOracle,
        PMF.pure_bind, PMF.map_bind, PMF.bind_map, PMF.bind_bind, lazyKDF]
      congr 1
      funext y
      congr 1
      funext σ
      simp only [Function.comp_apply, PMF.map_comp]
      congr 1
      funext sf
      rw [← PMF.bind_pure_comp]
      congr 1
      funext cf
      simp only [Function.comp_apply, logNext, hr, hg, and_self, ↓reduceIte]
      simp [modLt, ← hk]
    | corrupt q =>
      obtain ⟨rfl, hP⟩ := hS
      exact absurd ⟨rfl, hP⟩ he
    | _ => exact hS.elim
  · rw [forgeStep_of_not_signAt A p pk t e hS]
    have hm : modLt p (some (pk, sk)) t =
        modLt p (some (pk, sk)) (modLt p (some (pk, skDummy A)) t) := by simp
    rw [hm, filtO_modLt A (modLt p (some (pk, skDummy A)) t) p (some (pk, sk)) e
      (Or.inr ⟨(pk, skDummy A), (pk, sk), modLt_lt_self _ _ _, rfl, rfl, hS⟩), PMF.map_comp]
    simp only [genStep, OracleAdv.run_rand, OracleAdv.run_ret]
    rw [← PMF.bind_pure_comp]
    congr 1
    funext y
    simp [logNext_of_not_signAt A p pk t L e _ hS]

/-- A step keeps every key pair. -/
theorem filtO_lt (A : TLSAlg S W Tr VK SK Sig Sec) (s : TRSt S W Tr VK SK Sec)
    (e : TOEv W Tr Sig Sec) (x : TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec)
    (hx : x ∈ (filtO A s e).support) (q : PartyId) (v : VK × SK) (h : s.lt q = some v) :
    x.2.lt q = some v := by
  rcases filtO_support A s e x hx with hg | ⟨-, -, -, -, -, -, hlt, -⟩
  · exact hg.2.2.2 q v h
  · rw [hlt]
    exact h

/-- A step keeps every corruption. -/
theorem filtO_corrupt (A : TLSAlg S W Tr VK SK Sig Sec) (s : TRSt S W Tr VK SK Sec)
    (e : TOEv W Tr Sig Sec) (x : TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec)
    (hx : x ∈ (filtO A s e).support) (q : PartyId) (h : s.st.corrupt q = true) :
    x.2.st.corrupt q = true := by
  rcases filtO_support A s e x hx with hg | ⟨sid, pid, peer, role, -, hst, -, -⟩
  · exact hg.2.1 q h
  · rw [hst]
    simp only [addSession]
    split_ifs
    · exact h
    · exact h

open Classical in
/-- **After the corruption of `p` no forbidden acceptance at `p` happens.** -/
theorem flag_zero_of_corrupt (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool)
    (s : TRSt S W Tr VK SK Sec) (hs : s.st.corrupt p = true) :
    (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A)) B (s, false)).toOuterMeasure
      {y | y.2.2 = true} = 0 := by
  refine le_antisymm ?_ zero_le
  refine (OracleAdv.run_flagWhen_le_of_inv (filtO A) (BadAt A p) (fun _ _ _ => False)
    (fun t => t.st.corrupt p = true) (fun t d ht x hx => Or.inr ⟨?_, ?_⟩) B s hs).trans
      (run_flagWhen_false (filtO A) B s).le
  · rintro ⟨sid, pid, Y, σ, sf, r, xs, kp, -, -, -, -, -, -, -, -, hc, -⟩
    rw [ht] at hc
    cases hc
  · exact filtO_corrupt A t d x hx p ht

omit [Fintype S] [Nonempty S] [DecidableEq W] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] in
/-- A forgery found at a step is an acceptance at a client with peer `p` of a transcript that
`p` did not sign, with a signature that verifies under `pk`. -/
theorem forgeryAt_some (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId) (pk : VK)
    (s : TRSt S W Tr VK SK Sec) (e : TOEv W Tr Sig Sec) (f : Tr × Sig)
    (h : forgeryAt A p pk s e = some f) :
    ∃ sid pid Y σ sf, e = .inr (.cliRecv sid pid Y σ sf) ∧ f.2 = σ ∧
      A.sig.verify pk f.1 f.2 = true ∧ f.1 ∉ s.log p := by
  rcases e with h' | a
  · simp [forgeryAt] at h
  cases a with
  | cliRecv sid pid Y σ sf =>
    simp only [forgeryAt] at h
    split at h
    · split_ifs at h with hc
      cases h
      exact ⟨sid, pid, Y, σ, sf, rfl, rfl, hc.2.2.2.1, hc.2.2.2.2.2⟩
    · cases h
  | _ => simp [forgeryAt] at h

/-- A forbidden acceptance at `p` from a state with the key pair `(pk, sk)` of `p` is a forgery
found by the forger. -/
theorem forgeryAt_of_badAt (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId) (pk : VK) (sk : SK)
    (t : TRSt S W Tr VK SK Sec) (e : TOEv W Tr Sig Sec)
    (x : TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec)
    (hx : x ∈ (filtO A (modLt p (some (pk, sk)) t) e).support)
    (h : BadAt A p (modLt p (some (pk, sk)) t) e x) : forgeryAt A p pk t e ≠ none := by
  obtain ⟨sid, pid, Y, σ, sf, r, xs, kp, rfl, hr, he, hro, hk, hpe, hlt, hv, hc, hn⟩ := h
  have hkp : kp = (pk, sk) := by
    have := filtO_lt A _ _ x hx p (pk, sk) (modLt_lt_self _ _ _)
    rw [hlt] at this
    exact Option.some.inj this
  subst hkp hpe
  simp only [modLt_fields] at hr he hc hn
  simp [forgeryAt, hr, he, hro, hk, hv, hc, hn]

/-- **The signing log of the forger stays inside the log of `p`.** -/
theorem logNext_mem (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId) (pk : VK) (sk : SK)
    (t : TRSt S W Tr VK SK Sec) (e : TOEv W Tr Sig Sec) (L : List (Tr × Sig))
    (hL : ∀ y ∈ L, y.1 ∈ t.log p) (he : ¬ (e = .inr (.corrupt p) ∧ Pending t p = false))
    (x : TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec)
    (hx : x ∈ (filtO A (modLt p (some (pk, sk)) t) e).support) :
    ∀ y ∈ logNext A p pk t L e x, y.1 ∈ x.2.log p := by
  have hgrow : ∀ m, m ∈ t.log p → m ∈ x.2.log p := by
    intro m hm
    rcases filtO_support A _ e x hx with hg | ⟨-, -, -, -, -, -, -, hlog⟩
    · exact hg.2.2.1 p m hm
    · rw [hlog]
      exact hm
  by_cases hS : SignAt p t e
  · rcases e with h | a
    · exact hS.elim
    cases a with
    | srvRecv sid q X =>
      obtain ⟨rfl, r, hr, h1, h2, h3⟩ := hS
      have hg : r.role = .responder ∧ r.key.isNone = true ∧ (t.srv (sid, q)).isNone = true :=
        (srvGate_iff t _ r hr).mp ⟨r, hr, h1, h2, h3⟩
      simp only [filtO, filtGameK, gameK, realAdvK, srvRecvK, modLt_fields, hr, hg, and_self,
        ↓reduceIte] at hx
      rw [ltAt_of_some A _ q (pk, sk) (modLt_lt_self _ _ _)] at hx
      simp only [PMF.pure_bind, PMF.support_map, PMF.support_bind, Set.mem_iUnion,
        Set.mem_image] at hx
      obtain ⟨_, ⟨y, -, σ, -, sf, -, cf, -, rfl⟩, rfl⟩ := hx
      intro z hz
      simp only [logNext, hr, hg, and_self, ↓reduceIte, List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · simp [hL z hz]
      · simp
    | corrupt q =>
      obtain ⟨rfl, hP⟩ := hS
      exact absurd ⟨rfl, hP⟩ he
    | _ => exact hS.elim
  · rw [logNext_of_not_signAt A p pk t L e x hS]
    exact fun y hy => hgrow _ (hL y hy)

open Classical in
/-- **The forger simulates the filtered world.** From a state without a key pair for `p`, with
the signing log `L` of transcripts all signed by `p`, the probability that the filtered world with
the key pair `(pk, sk)` in place for `p` makes a forbidden acceptance at `p` is at most the
probability that the loop of the forger, run against the signing oracle of `sk` from `L`, outputs
a fresh message with a signature that verifies under `pk`. -/
theorem flag_le_forge (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId) (pk : VK) (sk : SK)
    (m₀ : Tr) (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool)
    (t : TRSt S W Tr VK SK Sec) (L : List (Tr × Sig)) (hk : t.lt p = none)
    (hL : ∀ y ∈ L, y.1 ∈ t.log p) :
    (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A)) B
        (modLt p (some (pk, sk)) t, false)).toOuterMeasure {y | y.2.2 = true} ≤
      (OracleAdv.run (signOracle A.sig sk) (forgeLoop A p pk m₀ B t) L).toOuterMeasure
        {x | (A.sig.verify pk x.1.1 x.1.2 && !(x.2.map Prod.fst).contains x.1.1) = true} := by
  induction B generalizing t L with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    simp
  | rand μ k ih =>
    rw [OracleAdv.run_rand, forgeLoop, stopRed, ← forgeLoop, OracleAdv.run_rand,
      PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    exact ENNReal.tsum_le_tsum fun b => mul_le_mul_right (ih b t L hk hL) _
  | query e k ih =>
    by_cases hc : e = .inr (.corrupt p) ∧ Pending t p = false
    · obtain ⟨rfl, hP⟩ := hc
      refine le_of_eq_of_le ?_ zero_le
      rw [OracleAdv.run_query, PMF.toOuterMeasure_bind_apply]
      refine ENNReal.tsum_eq_zero.mpr fun x => ?_
      by_cases hx : x ∈ (OracleAdv.flagWhen (BadAt A p) (filtO A)
        (modLt p (some (pk, sk)) t, false) (.inr (.corrupt p))).support
      · simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have hb : ¬ BadAt A p (modLt p (some (pk, sk)) t) (.inr (.corrupt p)) y := by
          rintro ⟨sid, pid, Y, σ, sf, r, xs, kp, h, -⟩
          cases h
        have hcor : y.2.st.corrupt p = true := by
          simp only [filtO, filtGameK, gameK, realAdvK, corruptK, pending_modLt, hP,
            Bool.false_eq_true, ↓reduceIte, PMF.support_map, Set.mem_image] at hy
          obtain ⟨_, ⟨l, -, rfl⟩, rfl⟩ := hy
          simp [corruptStep]
        simp only [hb, decide_false, Bool.or_false]
        rw [flag_zero_of_corrupt A p (k y.1) y.2 hcor, mul_zero]
      · rw [PMF.apply_eq_zero_iff _ _ |>.mpr hx, zero_mul]
    rw [OracleAdv.run_query, forgeLoop, stopRed, ← forgeLoop, OracleAdv.run_bind,
      run_forgeStep A p pk sk t e L hk hc, PMF.bind_map]
    rcases hf : forgeryAt A p pk t e with _ | f
    · simp only [OracleAdv.flagWhen, PMF.bind_map]
      rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : x ∈ (filtO A (modLt p (some (pk, sk)) t) e).support
      · refine mul_le_mul_right ?_ _
        have hb : ¬ BadAt A p (modLt p (some (pk, sk)) t) e x := fun h =>
          forgeryAt_of_badAt A p pk sk t e x hx h hf
        have hxk := filtO_lt A _ e x hx p (pk, sk) (modLt_lt_self _ _ _)
        have hx2 : modLt p (some (pk, sk)) (modLt p none x.2) = x.2 := by
          rw [modLt_modLt, modLt_eq_self _ _ _ hxk]
        have := ih x.1 (modLt p none x.2) (logNext A p pk t L e x) (modLt_lt_self _ _ _)
          (logNext_mem A p pk sk t e L hL hc x hx)
        rw [hx2] at this
        simpa [hb] using this
      · rw [PMF.apply_eq_zero_iff _ _ |>.mpr hx, zero_mul, zero_mul]
    · obtain ⟨sid, pid, Y, σ, sf, rfl, -, hv, hs⟩ := forgeryAt_some A p pk t _ f hf
      have hnot : ∀ σ', (f.1, σ') ∉ L := fun σ' h => hs (hL (f.1, σ') h)
      refine (toOuterMeasure_le_one _ _).trans (le_of_eq ?_)
      rw [eq_comm, PMF.toOuterMeasure_apply_eq_one_iff]
      intro y hy
      simp only [PMF.mem_support_bind_iff, OracleAdv.run_ret] at hy
      obtain ⟨x, -, hy⟩ := hy
      simp only [Function.comp_apply, PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simp [logNext, hv, hnot]

open Classical in
/-- **A forbidden acceptance at `p` is a forgery.** -/
theorem flag_le_eufcma (A : TLSAlg S W Tr VK SK Sig Sec) (p : PartyId)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A)) B
        (tInitK lazyKDF, false)).toOuterMeasure {y | y.2.2 = true} ≤
      eufcmaAdvantage A.sig.toSigScheme (toEUFAdversary (tlsForgeRed A p B)) := by
  rw [flag_lazy, eufcmaAdvantage_toEUFAdversary, eufDist, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun kr => mul_le_mul_right ?_ _
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  exact flag_le_forge A p _ _ _ B (tInitK lazyKDF) [] rfl (by simp)

/-- **The real and the filtered game agree off the forbidden acceptances.** -/
theorem real_eq_filt (A : TLSAlg S W Tr VK SK Sig Sec) (s : TRSt S W Tr VK SK Sec)
    (e : TOEv W Tr Sig Sec) (x : TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec)
    (hx : ¬ RealBad A s e x) : realO A s e x = filtO A s e x := by
  rcases e with h | a
  · rfl
  cases a with
  | cliRecv sid pid Y σ sf =>
    simp only [realO, filtO, realGameK, filtGameK, gameK, realAdvK, cliCheckK]
    rcases hr : s.st.recs (sid, pid) with _ | r
    · rfl
    rcases he : s.eph (sid, pid) with _ | xs
    · rfl
    simp only
    split_ifs with hg
    swap
    · rfl
    simp only [PMF.bind_bind, PMF.map_bind]
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun l => ?_
    by_cases hl : l ∈ (ltAt A s r.peer).support
    swap
    · rw [PMF.apply_eq_zero_iff _ _ |>.mpr hl, zero_mul, zero_mul]
    congr 1
    obtain ⟨hl2, -⟩ := ltAt_support A s r.peer l hl
    by_cases hb : A.sig.verify l.1.1 (A.trCert (A.tr1 sid pid r.peer (A.pub xs) Y) l.1.1) σ =
        true ∧ s.st.corrupt r.peer = false ∧
        A.trCert (A.tr1 sid pid r.peer (A.pub xs) Y) l.1.1 ∉ s.log r.peer
    · have hne : x.2.lt r.peer ≠ some l.1 := fun h =>
        hx ⟨r.peer, sid, pid, Y, σ, sf, r, xs, l.1, rfl, hr, he,
          by simpa using hg.1, by simpa using hg.2, rfl, h, hb⟩
      have hz : ∀ (μ : PMF (TOOut W VK SK Sig Sec × TRSt S W Tr VK SK Sec)),
          (∀ y ∈ μ.support, y.2.lt = l.2.lt) → μ x = 0 := fun μ hμ =>
        (PMF.apply_eq_zero_iff _ _).mpr fun h =>
          hne (by rw [hμ x h, hl2]; simp)
      rw [hz, hz]
      all_goals
        intro y hy
        simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hy
        obtain ⟨i, -, j, hj, z, hz', rfl⟩ := hy
        have hj' : j.2.lt = l.2.lt := by
          split_ifs at hj
          · simp only [PMF.support_map, Set.mem_image] at hj
            obtain ⟨c, -, rfl⟩ := hj
            rfl
          · simp only [PMF.support_pure, Set.mem_singleton_iff] at hj
            subst hj
            rfl
        split at hz'
        · simp only [PMF.support_map, Set.mem_image] at hz'
          obtain ⟨k, -, rfl⟩ := hz'
          exact hj'
        · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz'
          subst hz'
          exact hj'
    · have hc : ∀ sv : Sec × List (TInp Tr W × Sec),
          (A.sig.verify l.1.1 (A.trCert (A.tr1 sid pid r.peer (A.pub xs) Y) l.1.1) σ = true ∧
            sf = sv.1 ∧ (!false || l.2.st.corrupt r.peer ||
              decide (A.trCert (A.tr1 sid pid r.peer (A.pub xs) Y) l.1.1 ∈ l.2.log r.peer)) =
                true) ↔
          (A.sig.verify l.1.1 (A.trCert (A.tr1 sid pid r.peer (A.pub xs) Y) l.1.1) σ = true ∧
            sf = sv.1 ∧ (!true || l.2.st.corrupt r.peer ||
              decide (A.trCert (A.tr1 sid pid r.peer (A.pub xs) Y) l.1.1 ∈ l.2.log r.peer)) =
                true) := by
        intro sv
        rw [hl2]
        simp only [Bool.not_false, Bool.true_or, Bool.not_true, Bool.false_or, Bool.or_eq_true,
          decide_eq_true_eq, and_true]
        grind
      simp only [hc]
  | _ => rfl

open Classical in
/-- **The forbidden acceptances happen at servers of `P`** when the adversary names only servers
of `P`. -/
theorem realBad_flag_le (A : TLSAlg S W Tr VK SK Sig Sec) (P : Finset PartyId)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) (hB : SrvNamesIn P B) :
    (OracleAdv.run (OracleAdv.flagWhen (RealBad A) (filtO A)) B
        (tInitK lazyKDF, false)).toOuterMeasure {y | y.2.2 = true} ≤
      (OracleAdv.run (OracleAdv.flagWhen (fun s d x => ∃ q ∈ P, BadAt A q s d x) (filtO A)) B
        (tInitK lazyKDF, false)).toOuterMeasure {y | y.2.2 = true} := by
  refine run_flagWhen_le_of_inv_on (filtO A) (SrvIn P)
    (fun t => ∀ y r, t.st.recs y = some r → r.role = .initiator → r.peer ∈ P) (RealBad A)
    (fun s d x => ∃ q ∈ P, BadAt A q s d x) ?_ B hB _ ?_ |>.trans_eq ?_
  rotate_left 2
  · congr
  · intro s d hs hd x hx
    by_cases hb : ∃ q ∈ P, BadAt A q s d x
    · exact Or.inl hb
    refine Or.inr ⟨fun ⟨q, hq⟩ => hb ⟨q, ?_, hq⟩, ?_⟩
    · obtain ⟨sid, pid, Y, σ, sf, r, xs, kp, -, hr, -, hro, -, hpe, -⟩ := hq
      exact hpe ▸ hs _ _ hr hro
    intro y r' hy hro
    rcases filtO_support A s d x hx with hg | ⟨sid, pid, peer, role, rfl, hst, -, -⟩
    · obtain ⟨r, hr, hp, hrr⟩ := hg.1 y r' hy
      rw [← hp]
      exact hs y r hr (hrr ▸ hro)
    · rw [hst] at hy
      simp only [addSession] at hy
      split_ifs at hy
      · exact hs y r' hy hro
      · by_cases hyx : y = (sid, pid)
        · subst hyx
          simp only [Function.update_self, Option.some.injEq] at hy
          subst hy
          cases role
          · exact hd
          · cases hro
        · grind
  · intro y r h
    simp [tInitK, initSt] at h

/-- **The real and the filtered game, up to forgery.** For every oracle adversary `B` and every
finite set of servers `P`, the advantage of `B` between the real game and the filtered game is
at most `tlsSigBound A P B`. -/
theorem advantage_real_filt_le (A : TLSAlg S W Tr VK SK Sig Sec) (P : Finset PartyId)
    (B : OracleAdv (TOEv W Tr Sig Sec) (TOOut W VK SK Sig Sec) Bool) :
    KeyedGame.advantage (realGameK lazyKDF A) (filtGameK lazyKDF A) B ≤ tlsSigBound A P B := by
  classical
  unfold tlsSigBound
  split_ifs with hN
  swap
  · exact le_top
  have hgap := OracleAdv.run_gap_le_flagWhen (RealBad A) (realO A) (filtO A)
    (fun s d x hx => real_eq_filt A s d x hx) B (tInitK lazyKDF) {true}
  change absDiff (((PMF.pure ()).bind fun _ =>
      (OracleAdv.run (realO A) B (tInitK lazyKDF)).map Prod.fst) true)
    (((PMF.pure ()).bind fun _ => (OracleAdv.run (filtO A) B (tInitK lazyKDF)).map Prod.fst)
      true) ≤ _
  simp only [PMF.pure_bind]
  rw [OracleGameUpToBad.map_fst_apply_true, OracleGameUpToBad.map_fst_apply_true]
  refine hgap.trans ((realBad_flag_le A P B hN).trans ?_)
  refine (run_flagWhen_union_le (filtO A) (fun q => BadAt A q) P B _).trans ?_
  exact Finset.sum_le_sum fun p _ => flag_le_eufcma A p B

end Forger

/-! ## The square -/

section Main

variable {S W Tr VK SK Sig Sec : Type} [Fintype S] [Nonempty S] [DecidableEq W]
  [DecidableEq Tr] [DecidableEq Sec] [Fintype Sec] [Nonempty Sec] [Inhabited Sec]

/-- **The real TLS protocol realizes `F_AKEImp … srvImp` behind `tlsSim`, in oracle-game
form.** Ideal functionality: `F_AKEImp (SPComp.sample (TKey Sec)) srvImp true`, the unilaterally
authenticated key exchange with uniform four-component keys and adaptive corruption. Real world:
the real protocol `tlsRealOf A`, in which a client accepts CertificateVerify under the key of its
peer. Simulator: `tlsSim A`. For every finite set of servers `P` and every environment `Z`, the
distance is at most `tlsSigBound A P` at the oracle reduction of `Z` (the EUF-CMA advantages of
the forgers `tlsForgeRed A p`, `p ∈ P`, when the reduction names only servers of `P`) plus the
advantage of the reduction between the filtered game `filtGameK lazyKDF A` and the simulated
game `simGame A`. -/
theorem tls_realizesSim_oracleGame (A : TLSAlg S W Tr VK SK Sig Sec) (P : Finset PartyId) :
    RealizesSim (tlsRealOf A) (F_AKEImp (SPComp.sample (TKey Sec)) srvImp true) (tlsSim A)
      (fun _ Z =>
        tlsSigBound A P
          ((OProt.oracle (Q := TOEv W Tr Sig Sec) (A := TOOut W VK SK Sig Sec)).reduction Z) +
        KeyedGame.advantage (filtGameK lazyKDF A) (simGame A)
          ((OProt.oracle (Q := TOEv W Tr Sig Sec) (A := TOOut W VK SK Sig Sec)).reduction Z)) :=
  Realizes.trans
    (fun _ Z => (Realizes.ofOracleGame OProt.oracle (realGameK lazyKDF A) (filtGameK lazyKDF A)
      _ Z).trans (advantage_real_filt_le A P _))
    (tls_filt_realizesSim_oracleGame A)

end Main

end CatCrypt.Crypto.AKE.TLSSquareSigned
