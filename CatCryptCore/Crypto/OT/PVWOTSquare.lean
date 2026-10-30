/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.DualModeOT
public import CatCryptCore.Crypto.OTExtension.IKNPSquare
public import CatCryptCore.Examples.CyclicGroupDDH
public import CatCryptCore.Crypto.UCSimulator
public import CatCryptCore.Crypto.UCChannel
public import CatCryptCore.Crypto.UCOracleGame
public import CatCryptCore.Crypto.OT.FOTSched

/-!
# The Peikert–Vaikuntanathan–Waters dual-mode OT as squares against `F_OT`

The DDH-based dual-mode oblivious transfer of Peikert, Vaikuntanathan and Waters (CRYPTO 2008)
for `m` parallel transfers of messages in `M`, encoded into the group by `code : M → G` and
decoded by `decode : G → M`, against a corrupt receiver and against a corrupt sender.

**CRS.** A CRS has two branches `(g₀, h₀)` and `(g₁, h₁)`. In *messy mode* (`MessyTD`, trapdoor
`(x₀, x₁)`) `h_b = g_b ^ x_b` with `x₀ ≠ x₁`; in *decryption mode* (`DecTD`, trapdoor `y ≠ 0`)
`(g₁, h₁) = (g₀ ^ y, h₀ ^ y)`. The CRS of a Diffie–Hellman tuple is in decryption mode
(`decCRS_td`), that of a random tuple in messy mode outside `b = 0` and `c = a b` (`randCRS_td`).

**Ideal functionality.** `F_OT` with adversarially scheduled delivery (`FOTSched.lean`) for `m`
transfers: the sender's input is the vector of `m` message pairs, the receiver's choice the
vector `Fin m → Bool`, and the receiver's output `otChoose x c`. The receiver obtains its output,
and the sender the completion notice, only after the adversary delivers them. `FOTSchedR
otChoose` places the sender on the honest port and the receiver beside the scheduler on the
adversary port, `FOTSchedS otChoose` the receiver on the honest port and the sender beside the
scheduler on the adversary port.

**Real protocol.** The receiver with choice `c` and randomness `r` sends the key
`(g_c ^ r, h_c ^ r)` (`recvMsg`). The sender answers a key `(g, h)` with
`(g_b ^ s · h_b ^ t, g ^ s · h ^ t · code m_b)` on each branch `b` (`senderMsg`), and the
receiver decrypts the chosen branch with `r` (`recvOut`; correctness `recvOut_senderMsg`). The
sender answers only keys with `g ≠ 1`. Against a corrupt receiver (`realR`, port-typed), the
first activation of the receiver's port with a stored key after the sender's input outputs the
sender's message, and every sender activation tells the sender whether it has answered.
Against a corrupt sender (`realS`, port-typed), the sender obtains the receiver's message by an
activation `inl ()` once the receiver has chosen, and its first message `inr ct` after that is
decrypted at the next receiver activation.

**Simulators.** Both forward the honest port, read no honest value, and drive the scheduling
port so that `F_OT` delivers when the real protocol's message arrives. Against a corrupt
receiver in messy mode, `pvwSimRecv` extracts each choice as the branch `b` with `h = g ^ x_b`
(`extract`) from the first well-formed key, sends the choices to `F_OT`, delivers the receiver's
output and the sender's completion notice, and encrypts the chosen messages on the extracted
branches and the identity on the others. Against a corrupt sender in decryption mode,
`pvwSimSend` polls `F_OT` at a delivery request and, once the receiver has chosen, sends keys of
branch `0` with its own randomness `ρ`; it decrypts both branches of the first sender's message
after delivery, branch `0` with `ρ` and branch `1` with `ρ / y` (`extractS`), sends both
messages of each pair to `F_OT` and delivers the receiver's output.

**Proofs.** Against a corrupt receiver the encryption on the branch other than the extracted
choice is a shift of the encryption of the identity (`elEnc_messy_shift`), so the real and
simulated sender's messages have the same distribution (`senderMsg_sample`): distance `0`.
Against a corrupt sender the receiver's message is the simulated one at the randomness
`rhoEquiv td c r`, a bijection (`recvMsg_eq_simKey`), and the receiver's output is the chosen
messages of the extracted pairs (`otChoose_extractS`): distance `0`, after the hop that draws
the receiver's randomness at delivery (`realS_realizes_late`). The two modes are related by the
DDH game for every system family indexed by the CRS (`crs_ddh_hop`), with the explicit
reduction `ddhEnvRed`.

## Main results

* `pvw_realizesSim_corruptReceiver` — in messy mode, `realR crs code` realizes
  `FOTSchedR otChoose` behind `pvwSimRecv td code` at distance `0`.
* `pvw_realizesSim_corruptSender` — in decryption mode, `realS crs decode` realizes
  `FOTSchedS otChoose` behind `pvwSimSend td decode` at distance `0`.
* `crs_ddh_hop` — a system family with the CRS of a Diffie–Hellman tuple realizes it with the
  CRS of a random tuple, with bound the DDH advantage of `ddhEnvRed S t₀ Z`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT.PVW

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform CatCrypt.Examples
open scoped ENNReal

variable (gp : GroupParam)

/-! ## Scalar and group algebra -/

/-- The scalars of `gp` as a commutative ring. -/
abbrev scalarCommRing : CommRing gp.Scalar where
  add := gp.scalarAdd
  add_assoc := gp.scalarAdd_assoc
  zero := gp.scalarZero
  zero_add := gp.scalarZero_add
  add_zero := gp.scalarAdd_zero
  nsmul := @nsmulRec _ ⟨gp.scalarZero⟩ ⟨gp.scalarAdd⟩
  add_comm := gp.scalarAdd_comm
  mul := gp.scalarMul
  left_distrib := gp.scalarMul_add
  right_distrib := gp.scalarAdd_mul
  zero_mul := gp.scalarZero_mul
  mul_zero := gp.scalarMul_zero
  mul_assoc := gp.scalarMul_assoc
  one := gp.scalarOne
  one_mul a := (gp.scalarMul_comm gp.scalarOne a).trans (gp.scalarMul_one a)
  mul_one := gp.scalarMul_one
  neg := gp.scalarNeg
  sub := gp.scalarSub
  sub_eq_add_neg := gp.scalarSub_eq
  zsmul := @zsmulRec _ ⟨gp.scalarZero⟩ ⟨gp.scalarAdd⟩ ⟨gp.scalarNeg⟩
    (@nsmulRec _ ⟨gp.scalarZero⟩ ⟨gp.scalarAdd⟩)
  neg_add_cancel := gp.scalarNeg_add
  mul_comm := gp.scalarMul_comm

attribute [local instance] scalarCommRing

variable {gp}

/-- Generator exponentiation of a sum is the product (`GroupParam.exp_add`). -/
theorem exp_add' (a b : gp.Scalar) : gp.exp (a + b) = gp.groupMul (gp.exp a) (gp.exp b) :=
  gp.exp_add a b

/-- Exponentiation of `g ^ w` by `e` is `g ^ (w * e)` (`GroupParam.groupExp_exp`). -/
theorem groupExp_exp' (w e : gp.Scalar) : gp.groupExp (gp.exp w) e = gp.exp (w * e) :=
  gp.groupExp_exp w e

/-- The inverse of `g ^ a` is `g ^ (-a)`. -/
theorem groupInv_exp (a : gp.Scalar) : gp.groupInv (gp.exp a) = gp.exp (-a) := by
  rw [gp.groupExp_generator, gp.groupInv_groupExp, ← gp.groupExp_generator]
  rfl

/-- The identity is `g ^ 0`. -/
theorem identity_eq_exp : gp.identity = gp.exp 0 :=
  gp.exp_zero.symm

/-- Generator exponentiation is injective. -/
theorem exp_eq_iff (a b : gp.Scalar) : gp.exp a = gp.exp b ↔ a = b :=
  ⟨gp.exp_inj a b, fun h => h ▸ rfl⟩

/-- Exponentiation twice multiplies the exponents. -/
theorem groupExp_groupExp (a : gp.G) (x y : gp.Scalar) :
    gp.groupExp (gp.groupExp a x) y = gp.groupExp a (x * y) := by
  obtain ⟨α, rfl⟩ := gp.exp_surj a
  simp only [groupExp_exp', mul_assoc]

/-! ## The common reference string and its modes -/

variable (gp) in
/-- A common reference string of the dual-mode OT: two branches `(g₀, h₀)` and `(g₁, h₁)`. -/
structure CRS where
  /-- The generator of branch `0`. -/
  g₀ : gp.G
  /-- The second element of branch `0`. -/
  h₀ : gp.G
  /-- The generator of branch `1`. -/
  g₁ : gp.G
  /-- The second element of branch `1`. -/
  h₁ : gp.G

/-- The generator of branch `b`. -/
def CRS.gb (crs : CRS gp) (b : Bool) : gp.G := if b then crs.g₁ else crs.g₀

/-- The second element of branch `b`. -/
def CRS.hb (crs : CRS gp) (b : Bool) : gp.G := if b then crs.h₁ else crs.h₀

/-- **Messy mode** with trapdoor `(x₀, x₁)`: `h_b = g_b ^ x_b` for both branches, `x₀ ≠ x₁`. -/
structure MessyTD (crs : CRS gp) where
  /-- The exponent of branch `0`. -/
  x₀ : gp.Scalar
  /-- The exponent of branch `1`. -/
  x₁ : gp.Scalar
  /-- `h₀ = g₀ ^ x₀`. -/
  h₀_eq : crs.h₀ = gp.groupExp crs.g₀ x₀
  /-- `h₁ = g₁ ^ x₁`. -/
  h₁_eq : crs.h₁ = gp.groupExp crs.g₁ x₁
  /-- The two exponents differ. -/
  x_ne : x₀ ≠ x₁

/-- **Decryption mode** with trapdoor `y`: branch `1` is branch `0` raised to `y ≠ 0`. -/
structure DecTD (crs : CRS gp) where
  /-- The exponent relating the branches. -/
  y : gp.Scalar
  /-- `y ≠ 0`. -/
  y_ne : y ≠ 0
  /-- `g₁ = g₀ ^ y`. -/
  g₁_eq : crs.g₁ = gp.groupExp crs.g₀ y
  /-- `h₁ = h₀ ^ y`. -/
  h₁_eq : crs.h₁ = gp.groupExp crs.h₀ y

/-- The exponent of branch `b` of a messy trapdoor. -/
def MessyTD.xb {crs : CRS gp} (td : MessyTD crs) (b : Bool) : gp.Scalar :=
  if b then td.x₁ else td.x₀

/-- In messy mode, `h_b = g_b ^ x_b` for each branch `b`. -/
theorem MessyTD.hb_eq {crs : CRS gp} (td : MessyTD crs) (b : Bool) :
    crs.hb b = gp.groupExp (crs.gb b) (td.xb b) := by
  cases b
  · exact td.h₀_eq
  · exact td.h₁_eq

/-! ## The protocol -/

/-- The receiver's key for branch `b` with randomness `r`: `(g_b ^ r, h_b ^ r)`. -/
def recvKey (crs : CRS gp) (b : Bool) (r : gp.Scalar) : gp.G × gp.G :=
  (gp.groupExp (crs.gb b) r, gp.groupExp (crs.hb b) r)

/-- Encryption of the group element `μ` under the key `pk = (g, h)` on the branch
`(gb, hb)` with randomness `(s, t)`: `(gb ^ s · hb ^ t, g ^ s · h ^ t · μ)`. -/
def elEnc (gb hb : gp.G) (pk : gp.G × gp.G) (μ : gp.G) (st : gp.Scalar × gp.Scalar) :
    gp.G × gp.G :=
  (gp.groupMul (gp.groupExp gb st.1) (gp.groupExp hb st.2),
    gp.groupMul (gp.groupMul (gp.groupExp pk.1 st.1) (gp.groupExp pk.2 st.2)) μ)

/-- Decryption of the ciphertext `(u, v)` with the key randomness `r`: `v · (u ^ r)⁻¹`. -/
def elDec (r : gp.Scalar) (ct : gp.G × gp.G) : gp.G :=
  gp.groupMul ct.2 (gp.groupInv (gp.groupExp ct.1 r))

/-- **Correctness of one branch.** Decrypting with `r` an encryption under the key
`(gb ^ r, hb ^ r)` on the branch `(gb, hb)` gives the plaintext. -/
theorem elDec_elEnc (gb hb μ : gp.G) (r : gp.Scalar) (st : gp.Scalar × gp.Scalar) :
    elDec r (elEnc gb hb (gp.groupExp gb r, gp.groupExp hb r) μ st) = μ := by
  obtain ⟨β, rfl⟩ := gp.exp_surj gb
  obtain ⟨η, rfl⟩ := gp.exp_surj hb
  obtain ⟨e, rfl⟩ := gp.exp_surj μ
  simp only [elDec, elEnc, groupExp_exp', ← exp_add', groupInv_exp, exp_eq_iff]
  ring

/-- **Messy branch.** If the key `(g, h)` has `h ≠ g ^ x` on the branch `(gb, gb ^ x)`, the
encryption of `μ` is the encryption of the identity at randomness shifted by a constant. -/
theorem elEnc_messy_shift (gb : gp.G) (x : gp.Scalar) (pk : gp.G × gp.G)
    (hpk : pk.2 ≠ gp.groupExp pk.1 x) (μ : gp.G) :
    ∃ δ : gp.Scalar × gp.Scalar, ∀ st,
      elEnc gb (gp.groupExp gb x) pk μ st =
        elEnc gb (gp.groupExp gb x) pk gp.identity (st + δ) := by
  obtain ⟨g, h⟩ := pk
  obtain ⟨β, rfl⟩ := gp.exp_surj gb
  obtain ⟨γ, rfl⟩ := gp.exp_surj g
  obtain ⟨η, rfl⟩ := gp.exp_surj h
  obtain ⟨e, rfl⟩ := gp.exp_surj μ
  have hd : η - γ * x ≠ 0 := fun h0 => hpk (by
    simp only [groupExp_exp', exp_eq_iff]; exact sub_eq_zero.mp h0)
  have hc : gp.scalarDiv e (η - γ * x) * (η - γ * x) = e := gp.div_mul_cancel _ _ hd
  refine ⟨(-(x * gp.scalarDiv e (η - γ * x)), gp.scalarDiv e (η - γ * x)), fun st => ?_⟩
  simp only [elEnc, groupExp_exp', ← exp_add', identity_eq_exp, Prod.fst_add, Prod.snd_add,
    Prod.mk.injEq, exp_eq_iff]
  constructor
  · ring
  · linear_combination -hc

/-- On a key `(g, h)` with `g ≠ 1`, `h` equals `g ^ x` for at most one exponent `x`. -/
theorem groupExp_ne_of_ne (g : gp.G) (hg : g ≠ gp.identity) {x₀ x₁ : gp.Scalar}
    (hx : x₀ ≠ x₁) : gp.groupExp g x₀ ≠ gp.groupExp g x₁ := by
  obtain ⟨γ, rfl⟩ := gp.exp_surj g
  have hγ : γ ≠ 0 := fun h0 => hg (by rw [h0, identity_eq_exp])
  simp only [groupExp_exp', ne_eq, exp_eq_iff]
  intro h
  apply hx
  have h₀ : gp.scalarDiv (γ * x₀) γ = x₀ := by rw [mul_comm]; exact gp.mul_div_cancel x₀ γ hγ
  have h₁ : gp.scalarDiv (γ * x₁) γ = x₁ := by rw [mul_comm]; exact gp.mul_div_cancel x₁ γ hγ
  rw [← h₀, ← h₁, h]

variable {m : ℕ} {M : Type}

variable (gp m) in
/-- The receiver's message for `m` transfers: one key per transfer. -/
abbrev Key := Fin m → gp.G × gp.G

variable (gp m) in
/-- The sender's message for `m` transfers: one ciphertext per branch and transfer. -/
abbrev Cts := Fin m → (gp.G × gp.G) × (gp.G × gp.G)

variable (gp m) in
/-- The sender's randomness for `m` transfers: one pair of scalars per branch and transfer. -/
abbrev SRand := Fin m → (gp.Scalar × gp.Scalar) × (gp.Scalar × gp.Scalar)

/-- The receiver's message with choices `c` and randomness `r`. -/
def recvMsg (crs : CRS gp) (c : Fin m → Bool) (r : Fin m → gp.Scalar) : Key gp m :=
  fun j => recvKey crs (c j) (r j)

/-- The sender's answer to one key `pk` with the message pair `xj`, encoded into the group by
`code`: the first message on branch `0`, the second on branch `1`. -/
def sendOne (crs : CRS gp) (code : M → gp.G) (pk : gp.G × gp.G) (xj : M × M)
    (st : (gp.Scalar × gp.Scalar) × (gp.Scalar × gp.Scalar)) : (gp.G × gp.G) × (gp.G × gp.G) :=
  (elEnc (crs.gb false) (crs.hb false) pk (code xj.1) st.1,
    elEnc (crs.gb true) (crs.hb true) pk (code xj.2) st.2)

/-- The sender's message for the receiver's message `k` and the message pairs `x`. -/
def senderMsg (crs : CRS gp) (code : M → gp.G) (k : Key gp m) (x : Fin m → M × M)
    (ρ : SRand gp m) : Cts gp m :=
  fun j => sendOne crs code (k j) (x j) (ρ j)

/-- The receiver's output with choices `c` and randomness `r` from the sender's message `ct`:
the decryption of the chosen branch, decoded by `decode`. -/
def recvOut (decode : gp.G → M) (c : Fin m → Bool) (r : Fin m → gp.Scalar) (ct : Cts gp m) :
    Fin m → M :=
  fun j => decode (elDec (r j) (if c j then (ct j).2 else (ct j).1))

/-- **Correctness.** When `decode` inverts `code`, the receiver outputs the chosen messages. -/
theorem recvOut_senderMsg (crs : CRS gp) (code : M → gp.G) (decode : gp.G → M)
    (hcode : ∀ a, decode (code a) = a) (c : Fin m → Bool) (r : Fin m → gp.Scalar)
    (x : Fin m → M × M) (ρ : SRand gp m) :
    recvOut decode c r (senderMsg crs code (recvMsg crs c r) x ρ) = otChoose x c := by
  funext j
  cases hc : c j <;>
    simp [recvOut, senderMsg, sendOne, recvMsg, recvKey, hc, elDec_elEnc, hcode, otChoose]

/-- A receiver's message is well formed when every key has a non-identity first element. -/
def KeyOK (k : Key gp m) : Prop := ∀ j, (k j).1 ≠ gp.identity

variable (gp m) in
/-- Well-formed receiver messages. -/
abbrev VKey := {k : Key gp m // KeyOK k}

/-- The stored receiver message after the message `k`: the first well-formed one. -/
noncomputable def storeKey (ko : Option (VKey gp m)) (k : Key gp m) : Option (VKey gp m) :=
  open Classical in ko.or (if h : KeyOK k then some ⟨k, h⟩ else none)

/-! ## Against a corrupt receiver, in messy mode -/

section CorruptReceiver

variable (gp m M) in
/-- The state of the protocol against a corrupt receiver: the receiver's first well-formed
message, the sender's first message pairs, and whether the sender has answered. -/
abbrev RState := Option (VKey gp m) × Option (Fin m → M × M) × Bool

/-- The honest sender's port: the first message pairs are kept, and the sender learns whether it
has answered the receiver. -/
noncomputable def realRSend : Sys (RState gp m M) (Fin m → M × M) Bool where
  init := (none, none, false)
  step t x := SPComp.pure ((t.1, t.2.1.or (some x), t.2.2), t.2.2)

/-- The corrupt receiver's port: a receiver message is stored if it is the first well-formed
one; once the sender holds a receiver message and its message pairs, the first such activation
outputs the sender's message with fresh randomness. -/
noncomputable def realRRecv (crs : CRS gp) (code : M → gp.G) :
    Sys (RState gp m M) (Key gp m) (Option (Cts gp m)) where
  init := (none, none, false)
  step t k :=
    match storeKey t.1 k, t.2.1, t.2.2 with
    | some v, some x, false => SPComp.bind (SPComp.sample (SRand gp m)) fun ρ =>
        SPComp.pure ((some v, some x, true), some (senderMsg crs code v.1 x ρ))
    | ko, xo, d => SPComp.pure ((ko, xo, d), none)

/-- **The dual-mode OT against a corrupt receiver**, with the CRS `crs`: the sender on the honest
port, the receiver on the adversary port. -/
noncomputable def realR (crs : CRS gp) (code : M → gp.G) :
    Sys (RState gp m M) ((Fin m → M × M) ⊕ Key gp m) (Bool ⊕ Option (Cts gp m)) :=
  Sys.ofPorts realRSend (realRRecv crs code)

/-- `realR` answers each event on the port of the event. -/
theorem realR_portTyped (crs : CRS gp) (code : M → gp.G) :
    (realR (m := m) crs code).PortTyped :=
  Sys.ofPorts_portTyped _ _

variable {crs : CRS gp}

/-- The choice extracted from one key `(g, h)` with the messy trapdoor: `1` unless
`h = g ^ x₀`. -/
def extractOne (td : MessyTD crs) (pk : gp.G × gp.G) : Bool :=
  open Classical in decide (pk.2 ≠ gp.groupExp pk.1 td.x₀)

/-- The choices extracted from a receiver message with the messy trapdoor. -/
def extract (td : MessyTD crs) (k : Key gp m) : Fin m → Bool :=
  fun j => extractOne td (k j)

/-- The simulated answer to one key `pk` with extracted choice `b` and chosen message `zj`: the
chosen message on branch `b`, the identity on the other branch. -/
def simOne (crs : CRS gp) (code : M → gp.G) (b : Bool) (pk : gp.G × gp.G) (zj : M)
    (st : (gp.Scalar × gp.Scalar) × (gp.Scalar × gp.Scalar)) : (gp.G × gp.G) × (gp.G × gp.G) :=
  (elEnc (crs.gb false) (crs.hb false) pk (if b then gp.identity else code zj) st.1,
    elEnc (crs.gb true) (crs.hb true) pk (if b then code zj else gp.identity) st.2)

/-- In messy mode, the answer to a well-formed key is the simulated answer at randomness shifted
by a constant: the branch other than the extracted choice is messy. -/
theorem sendOne_shift (td : MessyTD crs) (code : M → gp.G) (pk : gp.G × gp.G)
    (hpk : pk.1 ≠ gp.identity) (xj : M × M) :
    ∃ δ, ∀ st, sendOne crs code pk xj st =
      simOne crs code (extractOne td pk) pk (if extractOne td pk then xj.2 else xj.1)
        (st + δ) := by
  have h0 := td.hb_eq false
  have h1 := td.hb_eq true
  by_cases hx : pk.2 = gp.groupExp pk.1 td.x₀
  · have hne : pk.2 ≠ gp.groupExp pk.1 td.x₁ := hx ▸ groupExp_ne_of_ne _ hpk td.x_ne
    obtain ⟨δ, hδ⟩ := elEnc_messy_shift (crs.gb true) (td.xb true) pk hne (code xj.2)
    refine ⟨(0, δ), fun st => ?_⟩
    simp only [sendOne, simOne, extractOne, hx, ne_eq, not_true_eq_false, decide_false,
      Bool.false_eq_true, ite_false, Prod.fst_add, Prod.snd_add, add_zero]
    rw [h1, hδ]
  · obtain ⟨δ, hδ⟩ := elEnc_messy_shift (crs.gb false) (td.xb false) pk hx (code xj.1)
    refine ⟨(δ, 0), fun st => ?_⟩
    simp only [sendOne, simOne, extractOne, hx, ne_eq, not_false_eq_true, decide_true,
      ite_true, Prod.fst_add, Prod.snd_add, add_zero]
    rw [h0, hδ]

/-- The simulated sender's message with extracted choices `c` and chosen messages `z`. -/
def simCts (crs : CRS gp) (code : M → gp.G) (c : Fin m → Bool) (k : Key gp m)
    (z : Fin m → M) (ρ : SRand gp m) : Cts gp m :=
  fun j => simOne crs code (c j) (k j) (z j) (ρ j)

/-- **Messy-mode lossiness.** In messy mode, the sender's message to a well-formed receiver
message with uniform randomness is distributed as the simulated message, which carries only the
messages at the extracted choices. -/
theorem senderMsg_sample {β : Type} (td : MessyTD crs) (code : M → gp.G) (v : VKey gp m)
    (x : Fin m → M × M) (G : Cts gp m → β) :
    SPComp.bind (SPComp.sample (SRand gp m)) (fun ρ => SPComp.pure (G (senderMsg crs code v.1 x ρ)))
      = SPComp.bind (SPComp.sample (SRand gp m)) (fun ρ => SPComp.pure
          (G (simCts crs code (extract td v.1) v.1 (otChoose x (extract td v.1)) ρ))) := by
  choose δ hδ using fun j => sendOne_shift td code (v.1 j) (v.2 j) (x j)
  have hρ : ∀ ρ : SRand gp m, senderMsg crs code v.1 x ρ =
      simCts crs code (extract td v.1) v.1 (otChoose x (extract td v.1)) (Equiv.addRight δ ρ) := by
    intro ρ; funext j; exact hδ j (ρ j)
  simp only [hρ]
  exact SPComp.sample_bind_equiv (Equiv.addRight δ) fun ρ => SPComp.pure
    (G (simCts crs code (extract td v.1) v.1 (otChoose x (extract td v.1)) ρ))

variable (gp m) in
/-- The state of the simulator against a corrupt receiver: the stored receiver message and the
phase of the current activation. -/
abbrev SimRSt := Option (VKey gp m) × ℕ

/-- The adversary-port answer of the simulator against a corrupt receiver: from the stored
receiver message and the receiver's output from `F_OT`, the simulated sender's message. -/
noncomputable def simRFinish (td : MessyTD crs) (code : M → gp.G) :
    Option (VKey gp m) → Option (Fin m → M) ⊕ SchedOut → SPComp (SimRSt gp m × Option (Cts gp m))
  | some v, .inl (some z) => SPComp.bind (SPComp.sample (SRand gp m)) fun ρ =>
      SPComp.pure ((some v, 0), some (simCts crs code (extract td v.1) v.1 z ρ))
  | s, _ => SPComp.pure ((s, 0), none)

/-- `simRFinish` never fails. -/
theorem simRFinish_noFail (td : MessyTD crs) (code : M → gp.G) (s : Option (VKey gp m))
    (o : Option (Fin m → M) ⊕ SchedOut) : SPComp.NoFail (simRFinish td code s o) := by
  rcases s with _ | v <;> rcases o with (_ | z) | o <;> simp only [simRFinish] <;>
    first
    | exact SPComp.pure_noFail _
    | exact Assumptions.SPComp.bind_noFail Assumptions.SPComp.sample_noFail
        fun _ => SPComp.pure_noFail _

/-- The adversary-port start of the simulator against a corrupt receiver: the first well-formed
receiver message is stored and its extracted choices are sent to `F_OT`; without a stored
message the answer is empty. -/
noncomputable def simRStart (td : MessyTD crs) (s : Option (VKey gp m)) (k : Key gp m) :
    SimRSt gp m × (((Fin m → Bool) ⊕ SchedEv) ⊕ Option (Cts gp m)) :=
  match storeKey s k with
  | some v => ((some v, 1), .inl (.inl (extract td v.1)))
  | none => ((none, 0), .inr none)

/-- The next call of the simulator against a corrupt receiver after the call of phase `n`: the
delivery of the receiver's output, the delivery of the completion notice to the sender, and the
receiver's activation that obtains its output. -/
noncomputable def simRNext (td : MessyTD crs) :
    SimRSt gp m → SimRSt gp m × (((Fin m → Bool) ⊕ SchedEv) ⊕ Option (Cts gp m))
  | (some v, 1) => ((some v, 2), .inl (.inr .deliverRecv))
  | (some v, 2) => ((some v, 3), .inl (.inr .deliverSend))
  | (some v, _) => ((some v, 0), .inl (.inl (extract td v.1)))
  | (none, _) => ((none, 0), .inr none)

/-- The simulator against a corrupt receiver on the adversary port: four calls of `F_OT` per
activation with a stored receiver message (the choices, the two deliveries, the receiver's
output). -/
noncomputable def simRAdv (td : MessyTD crs) (code : M → gp.G) :
    MultiHybrid (SimRSt gp m) (Key gp m) (Option (Cts gp m)) ((Fin m → Bool) ⊕ SchedEv)
      (Option (Fin m → M) ⊕ SchedOut) where
  init := (none, 0)
  fuel := 3
  start s k := SPComp.pure (simRStart td s.1 k)
  resume s _ := SPComp.pure (simRNext td s)
  finish s o := simRFinish td code s.1 o
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail s o := simRFinish_noFail td code s.1 o

/-- The simulator against a corrupt receiver as a multi-call simulator: forwarding on the
sender's port, `simRAdv` on the receiver's and the scheduler's port. -/
noncomputable def simProtR (td : MessyTD crs) (code : M → gp.G) :
    MultiHybrid (Unit × SimRSt gp m) ((Fin m → M × M) ⊕ Key gp m)
      (Bool ⊕ Option (Cts gp m)) ((Fin m → M × M) ⊕ ((Fin m → Bool) ⊕ SchedEv))
      (Bool ⊕ (Option (Fin m → M) ⊕ SchedOut)) :=
  (MultiHybrid.idSim (Fin m → M × M) Bool).tensor (simRAdv td code)

/-- **The simulator against a corrupt receiver.** It forwards the honest sender's events and
outputs; it extracts the choices from the first well-formed receiver message with the messy
trapdoor, sends them to `F_OT`, delivers the receiver's output and the sender's completion
notice, and answers with encryptions of the chosen messages from `F_OT` on the extracted
branches and of the identity on the other branches. It reads no honest value. Opaque for
`hidView.sum eqView`. -/
noncomputable def pvwSimRecv (td : MessyTD crs) (code : M → gp.G) :
    Simulator ((Fin m → M × M) ⊕ Key gp m) (Bool ⊕ Option (Cts gp m))
      ((Fin m → M × M) ⊕ ((Fin m → Bool) ⊕ SchedEv)) (Bool ⊕ (Option (Fin m → M) ⊕ SchedOut))
      (IKNPSquare.hidView.sum PubView.eqView) (IKNPSquare.hidView.sum PubView.eqView) :=
  Simulator.ofMultiHybrid (simProtR td code)
    (MultiHybrid.Opaque.tensor (MultiHybrid.idSim_opaque _) (MultiHybrid.opaque_eqView _))

/-- The stored receiver message never changes once set. -/
theorem storeKey_some (ko : Option (VKey gp m)) (k : Key gp m) (v : VKey gp m)
    (hv : storeKey ko k = some v) (v₀ : VKey gp m) (h₀ : ko = some v₀) : v = v₀ := by
  subst h₀
  simp only [storeKey] at hv
  exact (Option.some_injective _ hv).symm

/-- **The dual-mode OT against a corrupt receiver in messy mode as a square.** Ideal
functionality: `FOTSchedR otChoose`, `F_OT` with scheduled delivery for `m` transfers, with the
sender on the honest port and the receiver beside the scheduler on the adversary port. Real
protocol: `realR crs code`, whose sender answers the first well-formed receiver message with the
encryptions of both messages, the first on branch `0` and the second on branch `1`, and tells
the honest sender whether it has answered. CRS: messy mode with trapdoor `td`. Simulator:
`pvwSimRecv td code`, which extracts the choices with the messy trapdoor and delivers both
outputs of `F_OT` at the activation at which the real sender answers. Distance `0`: on the branch
other than the extracted choice, the encryption is independent of the message
(`senderMsg_sample`). Corrupt receiver, one transfer of `m` message pairs. -/
theorem pvw_realizesSim_corruptReceiver (td : MessyTD crs) (code : M → gp.G) :
    RealizesSim (realR crs code) (FOTSchedR otChoose) (pvwSimRecv (m := m) td code)
      fun _ _ => 0 := by
  refine realizes_zero_of_stepMap _ ((simProtR td code).withSub (FOTSchedR otChoose))
    (fun t => (((), (t.1, 0)),
      (⟨t.2.1, t.1.map (fun v => extract td v.1), none, t.2.2, t.2.2⟩ :
        SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M)))) rfl ?_
  rintro ⟨ko, xo, d⟩ (x | k)
  · rw [simProtR, MultiHybrid.tensor_withSub_step_inl _ _ (FOTSchedR otChoose) FOTSched.sendSys
      (fun _ _ => rfl), MultiHybrid.idSim_stepFuel]
    simp [realR, realRSend, FOTSched.sendSys, FOTSched.sendStep, SPComp.map, SPComp.pure_bind]
  · rw [simProtR, MultiHybrid.tensor_withSub_step_inr _ _ (FOTSchedR otChoose)
      (Sys.ofPorts FOTSched.recvSys (FOTSched.schedSys otChoose)) (fun _ _ => rfl)]
    have hko : ∀ v₀ : VKey gp m, storeKey (some v₀) k = some v₀ := fun _ => rfl
    rcases ko with _ | v₀
    · by_cases hk : KeyOK k
      · have hs : storeKey none k = some ⟨k, hk⟩ := by simp [storeKey, hk]
        rcases xo with _ | x <;> rcases d with _ | _
        case some.false =>
          simp only [SPComp.map, realR, realRRecv, Sys.ofPorts_step_inr, hs, SPComp.bind_assoc,
            SPComp.pure_bind, Option.map_subtype, Option.unattach_some, Option.map_some,
            MultiHybrid.stepFuel, simRAdv, simRStart, simRNext, simRFinish, FOTSched.recvSys,
            FOTSched.recvStep, Option.or_some, FOTSched.schedSys, FOTSched.schedStep,
            MultiHybrid.idSim, zero_le, sup_of_le_right, Option.map_none, MultiHybrid.drive,
            Sys.ofPorts_step_inl, Option.getD_none, Option.getD_some]
          exact senderMsg_sample td code ⟨k, hk⟩ x fun w =>
            ((((), some (⟨k, hk⟩ : VKey gp m), 0),
              (⟨some x, some (extract td k), none, true, true⟩ :
                SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M))),
              (Sum.inr (some w) : Bool ⊕ Option (Cts gp m)))
        all_goals simp [realR, realRRecv, hs, simRAdv, simRStart, simRNext, simRFinish,
          MultiHybrid.stepFuel, MultiHybrid.idSim, MultiHybrid.drive, FOTSched.recvSys,
          FOTSched.recvStep, FOTSched.schedSys, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]
      · have hs : storeKey (m := m) none k = none := by simp [storeKey, hk]
        simp [realR, realRRecv, hs, simRAdv, simRStart, MultiHybrid.stepFuel, MultiHybrid.idSim,
          MultiHybrid.drive, SPComp.map, SPComp.pure_bind]
    · rcases xo with _ | x <;> rcases d with _ | _
      case some.false =>
        simp only [SPComp.map, realR, realRRecv, Sys.ofPorts_step_inr, hko, SPComp.bind_assoc,
          SPComp.pure_bind, Option.map_subtype, Option.unattach_some, Option.map_some,
          MultiHybrid.stepFuel, simRAdv, simRStart, simRNext, simRFinish, FOTSched.recvSys,
          FOTSched.recvStep, Option.or_some, FOTSched.schedSys, FOTSched.schedStep,
          MultiHybrid.idSim, zero_le, sup_of_le_right, MultiHybrid.drive,
          Sys.ofPorts_step_inl, Option.getD_some]
        exact senderMsg_sample td code v₀ x fun w =>
          ((((), some v₀, 0),
            (⟨some x, some (extract td v₀.1), none, true, true⟩ :
              SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M))),
            (Sum.inr (some w) : Bool ⊕ Option (Cts gp m)))
      all_goals simp [realR, realRRecv, hko, simRAdv, simRStart, simRNext, simRFinish,
        MultiHybrid.stepFuel, MultiHybrid.idSim, MultiHybrid.drive, FOTSched.recvSys,
        FOTSched.recvStep, FOTSched.schedSys, FOTSched.schedStep, SPComp.map, SPComp.pure_bind]

end CorruptReceiver

/-! ## Keyed systems on two ports -/

namespace KeyedSys

variable {K τ E O E' O' : Type}

/-- The keyed system with the state of `SL` and `SR`, which steps as `SL` on a left event and as
`SR` on a right event, the output on the port of the event. -/
noncomputable def ofPorts (SL : KeyedSys K τ E O) (SR : KeyedSys K τ E' O') :
    KeyedSys K τ (E ⊕ E') (O ⊕ O') where
  init := SL.init
  step k t := Sum.elim (fun e => SPComp.map (fun q => (q.1, .inl q.2)) (SL.step k t e))
    (fun e => SPComp.map (fun q => (q.1, .inr q.2)) (SR.step k t e))
  step₀ t := Sum.elim (fun e => SPComp.map (fun q => (q.1, .inl q.2)) (SL.step₀ t e))
    (fun e => SPComp.map (fun q => (q.1, .inr q.2)) (SR.step₀ t e))
  uses t := Sum.elim (SL.uses t) (SR.uses t)

/-- Sampling the key lazily commutes with the composition on two ports. -/
theorem lazy_ofPorts (SL : KeyedSys K τ E O) (SR : KeyedSys K τ E' O')
    (μ : PMF K) : (ofPorts SL SR).lazy μ = Sys.ofPorts (SL.lazy μ) (SR.lazy μ) := by
  simp only [KeyedSys.lazy, Sys.ofPorts, ofPorts, Sys.mk.injEq, true_and]
  funext ⟨ko, t⟩ e
  rcases ko with _ | k <;> rcases e with e | e
  all_goals first
    | (simp [KeyedSys.lazyStep, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]; done)
    | (cases hu : SL.uses t e <;>
        simp [KeyedSys.lazyStep, hu, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind])
    | (cases hu : SR.uses t e <;>
        simp [KeyedSys.lazyStep, hu, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind])

/-- A lazily keyed system with deterministic steps `D` preserves an invariant `Inv` when each
activation does: with the key, at every key when the key is drawn, and without the key
otherwise. The step is then a draw followed by a point mass into `Inv`. -/
theorem lazy_pres_det (S : KeyedSys K τ E O) (μ : PMF K) (D : Option K → τ → E → τ × O)
    (hS : ∀ k t e, S.step k t e = SPComp.pure (D (some k) t e))
    (hS₀ : ∀ t e, S.step₀ t e = SPComp.pure (D none t e)) (Inv : Option K × τ → Prop)
    (hsome : ∀ k t e, Inv (some k, t) → Inv (some k, (D (some k) t e).1))
    (huses : ∀ t e, Inv (none, t) → S.uses t e = true → ∀ k, Inv (some k, (D (some k) t e).1))
    (hnone : ∀ t e, Inv (none, t) → S.uses t e = false → Inv (none, (D none t e).1))
    (t : Option K × τ) (e : E) (hI : Inv t) :
    ∃ (α : Type) (c : SPComp α) (g : α → (Option K × τ) × O),
      (S.lazy μ).step t e = SPComp.bind c (fun a => SPComp.pure (g a)) ∧ ∀ a, Inv (g a).1 := by
  obtain ⟨ko, t⟩ := t
  rcases ko with _ | k
  · cases hu : S.uses t e
    · exact ⟨Unit, SPComp.pure (), fun _ => ((none, (D none t e).1), (D none t e).2),
        by simp [KeyedSys.lazy, KeyedSys.lazyStep, hu, hS₀, SPComp.pure_bind],
        fun _ => hnone t e hI hu⟩
    · exact ⟨K, sampleFrom (ofPMF μ), fun k => ((some k, (D (some k) t e).1), (D (some k) t e).2),
        by simp [KeyedSys.lazy, KeyedSys.lazyStep, hu, hS, SPComp.pure_bind],
        fun k => huses t e hI hu k⟩
  · exact ⟨Unit, SPComp.pure (), fun _ => ((some k, (D (some k) t e).1), (D (some k) t e).2),
      by simp [KeyedSys.lazy, KeyedSys.lazyStep, hS, SPComp.pure_bind],
      fun _ => hsome k t e hI⟩

end KeyedSys

/-! ## Against a corrupt sender, in decryption mode -/

section CorruptSender

variable (gp m) in
/-- The state of the protocol against a corrupt sender: the receiver's first choices, whether the
receiver's message is delivered, the sender's first message after delivery, and whether the
receiver has output. -/
abbrev SState := Option (Fin m → Bool) × Bool × Option (Cts gp m) × Bool

/-- The honest receiver's activation with choices `c'` and, when it reads it, the randomness
`ro`: the first choices are kept; after the sender's message, the first activation outputs the
decryption of the chosen branches. -/
def sStepR (decode : gp.G → M) (ro : Option (Fin m → gp.Scalar)) (t : SState gp m)
    (c' : Fin m → Bool) : SState gp m × Option (Fin m → M) :=
  match t, ro with
  | (none, dl, cto, o), _ => ((some c', dl, cto, o), none)
  | (some c, dl, some ct, false), some r =>
    ((some c, dl, some ct, true), some (recvOut decode c r ct))
  | t, _ => (t, none)

/-- The corrupt sender's activation: `inl ()` delivers the receiver's message once the receiver
has chosen; `inr ct` stores the first sender's message after delivery. -/
def sStepA (crs : CRS gp) (ro : Option (Fin m → gp.Scalar)) (t : SState gp m) :
    Unit ⊕ Cts gp m → SState gp m × Option (Key gp m)
  | .inl _ =>
    match t, ro with
    | (some c, _, cto, o), some r => ((some c, true, cto, o), some (recvMsg crs c r))
    | t, _ => (t, none)
  | .inr ct =>
    match t with
    | (co, true, none, o) => ((co, true, some ct, o), none)
    | t => (t, none)

/-- The honest receiver's port, keyed by its randomness. The randomness is read at the output;
it is drawn at the first choice when `early` holds and at the first read otherwise. -/
noncomputable def keyedSR (decode : gp.G → M) (early : Bool) :
    KeyedSys (Fin m → gp.Scalar) (SState gp m) (Fin m → Bool) (Option (Fin m → M)) where
  init := (none, false, none, false)
  step r t c := SPComp.pure (sStepR decode (some r) t c)
  step₀ t c := SPComp.pure (sStepR decode none t c)
  uses t _ := (early && t.1.isNone) || (t.1.isSome && t.2.2.1.isSome && !t.2.2.2)

/-- The corrupt sender's port, keyed by the receiver's randomness, read at the delivery of the
receiver's message. -/
noncomputable def keyedSA (crs : CRS gp) :
    KeyedSys (Fin m → gp.Scalar) (SState gp m) (Unit ⊕ Cts gp m) (Option (Key gp m)) where
  init := (none, false, none, false)
  step r t e := SPComp.pure (sStepA crs (some r) t e)
  step₀ t e := SPComp.pure (sStepA crs none t e)
  uses t e := e.isLeft && t.1.isSome

/-- The protocol against a corrupt sender as one keyed system. -/
noncomputable def keyedS (crs : CRS gp) (decode : gp.G → M) (early : Bool) :
    KeyedSys (Fin m → gp.Scalar) (SState gp m) ((Fin m → Bool) ⊕ (Unit ⊕ Cts gp m))
      (Option (Fin m → M) ⊕ Option (Key gp m)) :=
  KeyedSys.ofPorts (keyedSR decode early) (keyedSA crs)

/-- **The dual-mode OT against a corrupt sender**, with the CRS `crs`: the receiver on the honest
port, the sender on the adversary port. The receiver draws its randomness at its first choice;
the sender obtains the receiver's message by `inl ()` and answers by `inr ct`. -/
noncomputable def realS (crs : CRS gp) (decode : gp.G → M) :
    Sys (Option (Fin m → gp.Scalar) × SState gp m) ((Fin m → Bool) ⊕ (Unit ⊕ Cts gp m))
      (Option (Fin m → M) ⊕ Option (Key gp m)) :=
  Sys.ofPorts ((keyedSR decode true).lazy (PMF.uniformFintype _))
    ((keyedSA crs).lazy (PMF.uniformFintype _))

/-- `realS` answers each event on the port of the event. -/
theorem realS_portTyped (crs : CRS gp) (decode : gp.G → M) :
    (realS (m := m) crs decode).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- An activation of `keyedS` that does not read the key does not depend on it. -/
theorem keyedS_hind (crs : CRS gp) (decode : gp.G → M) (early : Bool) (r : Fin m → gp.Scalar)
    (t : SState gp m) (e : (Fin m → Bool) ⊕ (Unit ⊕ Cts gp m))
    (hu : (keyedS crs decode early).uses t e = false) :
    (keyedS crs decode early).step r t e = (keyedS crs decode early).step₀ t e := by
  obtain ⟨co, dl, cto, o⟩ := t
  rcases e with c' | (u | ct)
  · rcases co with _ | c <;> rcases cto with _ | ct <;> rcases o with _ | _ <;>
      simp_all [keyedS, KeyedSys.ofPorts, keyedSR, sStepR]
  · rcases co with _ | c <;> simp_all [keyedS, KeyedSys.ofPorts, keyedSA, sStepA]
  · simp [keyedS, KeyedSys.ofPorts, keyedSA, sStepA]

/-- Hop 1: drawing the receiver's randomness at its first choice and at the delivery of its
message give the same views: no activation in between reads it. -/
theorem realS_realizes_late (crs : CRS gp) (decode : gp.G → M) :
    Realizes (realS (m := m) crs decode)
      ((keyedS crs decode false).lazy (PMF.uniformFintype _)) fun _ _ => 0 := by
  intro ζ Z
  have hv : view (realS (m := m) crs decode) Z.input =
      view ((keyedS crs decode false).lazy (PMF.uniformFintype _)) Z.input := by
    rw [realS, ← KeyedSys.lazy_ofPorts, ← keyedS,
      KeyedSys.view_lazy _ _ (keyedS_hind crs decode true),
      KeyedSys.view_lazy _ _ (keyedS_hind crs decode false)]
    rfl
  simp [Env.gap, hv]

variable {crs : CRS gp}

/-- Multiplication by `y ≠ 0` as a bijection of the scalars. -/
def mulEquiv (y : gp.Scalar) (hy : y ≠ 0) : gp.Scalar ≃ gp.Scalar where
  toFun r := y * r
  invFun ρ := gp.scalarDiv ρ y
  left_inv r := by
    change gp.scalarDiv (y * r) y = r
    rw [mul_comm]; exact gp.mul_div_cancel r y hy
  right_inv ρ := by
    change y * gp.scalarDiv ρ y = ρ
    rw [mul_comm]; exact gp.div_mul_cancel ρ y hy

/-- The simulator's randomness for the receiver's randomness: multiplied by the trapdoor `y` at
the transfers with choice `1`. -/
def rhoEquiv (td : DecTD crs) (c : Fin m → Bool) : (Fin m → gp.Scalar) ≃ (Fin m → gp.Scalar) :=
  Equiv.piCongrRight fun j => if c j then mulEquiv td.y td.y_ne else Equiv.refl _

/-- The simulated receiver's message: the keys of branch `0` with randomness `ρ`. -/
def simKey (crs : CRS gp) (ρ : Fin m → gp.Scalar) : Key gp m :=
  recvMsg crs (fun _ => false) ρ

/-- The message pairs extracted from the sender's message `ct` with the decryption trapdoor: the
key with randomness `ρ j` decrypts branch `0`, and with randomness `ρ j / y` branch `1`. -/
def extractS (td : DecTD crs) (decode : gp.G → M) (ρ : Fin m → gp.Scalar) (ct : Cts gp m) :
    Fin m → M × M :=
  fun j => (decode (elDec (ρ j) (ct j).1), decode (elDec (gp.scalarDiv (ρ j) td.y) (ct j).2))

/-- **Receiver privacy in decryption mode.** The receiver's message with choices `c` is the
simulated message at the randomness `rhoEquiv td c r`. -/
theorem recvMsg_eq_simKey (td : DecTD crs) (c : Fin m → Bool) (r : Fin m → gp.Scalar) :
    recvMsg crs c r = simKey crs (rhoEquiv td c r) := by
  funext j
  cases hc : c j <;>
    simp [recvMsg, simKey, recvKey, rhoEquiv, hc, CRS.gb, CRS.hb, td.g₁_eq, td.h₁_eq,
      groupExp_groupExp, mulEquiv]

/-- **Extraction in decryption mode.** The chosen messages of the extracted message pairs are the
receiver's output. -/
theorem otChoose_extractS (td : DecTD crs) (decode : gp.G → M) (c : Fin m → Bool)
    (r : Fin m → gp.Scalar) (ct : Cts gp m) :
    otChoose (extractS td decode (rhoEquiv td c r) ct) c = recvOut decode c r ct := by
  funext j
  have hy : gp.scalarDiv (td.y * r j) td.y = r j := (mulEquiv td.y td.y_ne).left_inv (r j)
  cases hc : c j <;> simp [otChoose, extractS, recvOut, rhoEquiv, hc, mulEquiv, hy]

variable (gp m) in
/-- The state of the simulator against a corrupt sender: the vector of its scalars once drawn,
and whether it has sent message pairs to `F_OT`. -/
abbrev SimS := Option (Vector gp.Scalar m) × Bool

/-- The start of an activation of the simulator against a corrupt sender: a delivery request
polls `F_OT`; the first sender's message after delivery is decrypted with the decryption
trapdoor and the message pairs are sent to `F_OT`; any other sender's message is answered with
nothing. -/
def simSStart (td : DecTD crs) (decode : gp.G → M) (s : SimS gp m) :
    Unit ⊕ Cts gp m → SimS gp m × (((Fin m → M × M) ⊕ SchedEv) ⊕ Option (Key gp m))
  | .inl _ => (s, .inl (.inr .poll))
  | .inr ct =>
    match s with
    | (some v, false) => ((some v, true), .inl (.inl (extractS td decode v.get ct)))
    | s => (s, .inr none)

variable (crs) in
/-- The simulated receiver's message at a delivery after the receiver has chosen, with
randomness drawn at the first delivery. -/
noncomputable def simSKey : SimS gp m → SPComp (SimS gp m × Option (Key gp m))
  | (some v, sb) => SPComp.pure ((some v, sb), some (simKey crs v.get))
  | (none, sb) => SPComp.bind (SPComp.sample (Fin m → gp.Scalar)) fun ρ =>
      SPComp.pure ((some (Vector.ofFn ρ), sb), some (simKey crs ρ))

variable (crs) in
/-- The continuation of the simulator against a corrupt sender on an answer of `F_OT`: after the
message pairs are sent, the delivery of the receiver's output; after a poll that reports the
receiver's choice, the simulated receiver's message; otherwise nothing. -/
noncomputable def simSResume (s : SimS gp m) :
    Bool ⊕ SchedOut → SPComp (SimS gp m × (((Fin m → M × M) ⊕ SchedEv) ⊕ Option (Key gp m)))
  | .inl _ => SPComp.pure (s, .inl (.inr .deliverRecv))
  | .inr (.status _ true) => SPComp.map (fun p => (p.1, .inr p.2)) (simSKey crs s)
  | .inr _ => SPComp.pure (s, .inr none)

/-- `simSResume` never fails. -/
theorem simSResume_noFail (s : SimS gp m) (o : Bool ⊕ SchedOut) :
    SPComp.NoFail (simSResume (M := M) crs s o) := by
  obtain ⟨_ | ρ, sb⟩ := s <;> rcases o with b | (_ | ⟨_, _ | _⟩) <;>
    simp only [simSResume, simSKey, SPComp.map] <;>
    first
    | exact SPComp.pure_noFail _
    | exact Assumptions.SPComp.bind_noFail (SPComp.pure_noFail _) fun _ => SPComp.pure_noFail _
    | exact Assumptions.SPComp.bind_noFail (Assumptions.SPComp.bind_noFail
        Assumptions.SPComp.sample_noFail fun _ => SPComp.pure_noFail _)
        fun _ => SPComp.pure_noFail _

/-- The simulator against a corrupt sender on the adversary port: at most two calls of `F_OT`
per activation (a poll, or the message pairs and the delivery of the receiver's output). -/
noncomputable def simSAdv (td : DecTD crs) (decode : gp.G → M) :
    MultiHybrid (SimS gp m) (Unit ⊕ Cts gp m) (Option (Key gp m)) ((Fin m → M × M) ⊕ SchedEv)
      (Bool ⊕ SchedOut) where
  init := (none, false)
  fuel := 1
  start s e := SPComp.pure (simSStart td decode s e)
  resume s o := simSResume crs s o
  finish s _ := SPComp.pure (s, none)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail s o := simSResume_noFail s o
  finish_noFail _ _ := SPComp.pure_noFail _

/-- The simulator against a corrupt sender as a multi-call simulator: forwarding on the
receiver's port, `simSAdv` on the sender's and the scheduler's port. -/
noncomputable def simProtS (td : DecTD crs) (decode : gp.G → M) :
    MultiHybrid (Unit × SimS gp m) ((Fin m → Bool) ⊕ (Unit ⊕ Cts gp m))
      (Option (Fin m → M) ⊕ Option (Key gp m)) ((Fin m → Bool) ⊕ ((Fin m → M × M) ⊕ SchedEv))
      (Option (Fin m → M) ⊕ (Bool ⊕ SchedOut)) :=
  (MultiHybrid.idSim (Fin m → Bool) (Option (Fin m → M))).tensor (simSAdv td decode)

/-- **The simulator against a corrupt sender.** It forwards the honest receiver's events and
outputs; at a delivery after a poll of `F_OT` reports that the receiver has chosen, it answers
with keys of branch `0` with its own randomness; it decrypts the first sender's message after
delivery on both branches with the decryption trapdoor, sends the message pairs to `F_OT` and
delivers the receiver's output. It reads no honest value. Opaque for `hidView.sum eqView`. -/
noncomputable def pvwSimSend (td : DecTD crs) (decode : gp.G → M) :
    Simulator ((Fin m → Bool) ⊕ (Unit ⊕ Cts gp m)) (Option (Fin m → M) ⊕ Option (Key gp m))
      ((Fin m → Bool) ⊕ ((Fin m → M × M) ⊕ SchedEv)) (Option (Fin m → M) ⊕ (Bool ⊕ SchedOut))
      (IKNPSquare.hidView.sum PubView.eqView) (IKNPSquare.hidView.sum PubView.eqView) :=
  Simulator.ofMultiHybrid (simProtS td decode)
    (MultiHybrid.Opaque.tensor (MultiHybrid.idSim_opaque _) (MultiHybrid.opaque_eqView _))

/-- The simulator's scalars for the receiver's randomness `ko` and choices `co`. -/
def simRho (td : DecTD crs) (ko : Option (Fin m → gp.Scalar)) (co : Option (Fin m → Bool)) :
    Option (Vector gp.Scalar m) :=
  match ko, co with
  | some r, some c => some (Vector.ofFn (rhoEquiv td c r))
  | _, _ => none

/-- The message pairs extracted by the simulator with scalars `ρo` from the stored sender's
message `cto`. -/
def simX (td : DecTD crs) (decode : gp.G → M) (ρo : Option (Vector gp.Scalar m))
    (cto : Option (Cts gp m)) : Option (Fin m → M × M) :=
  match ρo, cto with
  | some v, some ct => some (extractS td decode v.get ct)
  | _, _ => none

/-- The entries of the vector of the values of `f` are the values of `f`. -/
private theorem vector_get_ofFn {α : Type} (f : Fin m → α) : (Vector.ofFn f).get = f :=
  funext fun _ => Vector.getElem_ofFn _

/-- The output of `F_OT` delivered to the receiver and not yet obtained, for the extracted
message pairs `xo`, the choices `co` and whether the receiver has output. -/
def simInbox (xo : Option (Fin m → M × M)) (co : Option (Fin m → Bool)) (o : Bool) :
    Option (Fin m → M) :=
  match xo, co, o with
  | some x, some c, false => some (otChoose x c)
  | _, _, _ => none

/-- The state of the simulator over `F_OT` for a state of the protocol against a corrupt
sender. -/
def sMap (td : DecTD crs) (decode : gp.G → M) (t : Option (Fin m → gp.Scalar) × SState gp m) :
    (Unit × SimS gp m) × SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M) :=
  (((), (simRho td t.1 t.2.1, t.2.2.2.1.isSome)),
    ⟨simX td decode (simRho td t.1 t.2.1) t.2.2.2.1, t.2.1,
      simInbox (simX td decode (simRho td t.1 t.2.1) t.2.2.2.1) t.2.1 t.2.2.2.2,
      t.2.2.2.1.isSome || t.2.2.2.2, false⟩)

/-- The invariant of the protocol against a corrupt sender with late randomness: the randomness
is drawn exactly when the receiver's message is delivered, delivery follows the choice, and the
sender's message follows delivery. -/
def SInv (t : Option (Fin m → gp.Scalar) × SState gp m) : Prop :=
  t.1.isSome = t.2.2.1 ∧ (t.2.2.1 = true → t.2.1.isSome) ∧ (t.2.2.2.1.isSome → t.2.2.1 = true)

/-- The deterministic activation of `keyedS` with the randomness `ro` when it is read. -/
def sStep (crs : CRS gp) (decode : gp.G → M) (ro : Option (Fin m → gp.Scalar))
    (t : SState gp m) :
    (Fin m → Bool) ⊕ (Unit ⊕ Cts gp m) → SState gp m × (Option (Fin m → M) ⊕ Option (Key gp m))
  | .inl c => ((sStepR decode ro t c).1, .inl (sStepR decode ro t c).2)
  | .inr e => ((sStepA crs ro t e).1, .inr (sStepA crs ro t e).2)

/-- A receiver activation keeps the delivery flag and the sender's message, and leaves the
choices set. -/
theorem sStepR_fst (decode : gp.G → M) (ro : Option (Fin m → gp.Scalar)) (t : SState gp m)
    (c : Fin m → Bool) :
    (sStepR decode ro t c).1.1.isSome = true ∧ (sStepR decode ro t c).1.2.1 = t.2.1 ∧
      (sStepR decode ro t c).1.2.2.1 = t.2.2.1 := by
  obtain ⟨co, dl, cto, o⟩ := t
  rcases co with _ | c₀
  · simp [sStepR]
  · rcases cto with _ | ct <;> rcases o with _ | _ <;> rcases ro with _ | r <;> simp [sStepR]

/-- A sender activation keeps the choices, never clears the delivery flag, sets it only with
the randomness and the choices, and stores a sender's message only after delivery. -/
theorem sStepA_fst (crs : CRS gp) (ro : Option (Fin m → gp.Scalar)) (t : SState gp m)
    (e : Unit ⊕ Cts gp m) :
    (sStepA crs ro t e).1.1 = t.1 ∧ (t.2.1 = true → (sStepA crs ro t e).1.2.1 = true) ∧
      ((sStepA crs ro t e).1.2.1 = true → t.2.1 = true ∨ (ro.isSome ∧ t.1.isSome)) ∧
      ((sStepA crs ro t e).1.2.2.1.isSome = true →
        t.2.2.1.isSome = true ∨ (sStepA crs ro t e).1.2.1 = true) := by
  obtain ⟨co, dl, cto, o⟩ := t
  rcases e with u | ct
  · rcases co with _ | c <;> rcases ro with _ | r <;> simp [sStepA, imp_or]
  · rcases dl with _ | _ <;> rcases cto with _ | ct₀ <;> simp [sStepA]

/-- Every activation of the protocol against a corrupt sender with late randomness preserves
`SInv`. -/
theorem late_pres (crs : CRS gp) (decode : gp.G → M) (t : Option (Fin m → gp.Scalar) × SState gp m)
    (e : (Fin m → Bool) ⊕ (Unit ⊕ Cts gp m)) (hI : SInv t) :
    ∃ (α : Type) (c : SPComp α)
      (g : α → (Option (Fin m → gp.Scalar) × SState gp m) ×
        (Option (Fin m → M) ⊕ Option (Key gp m))),
      ((keyedS crs decode false).lazy (PMF.uniformFintype _)).step t e =
          SPComp.bind c (fun a => SPComp.pure (g a)) ∧ ∀ a, SInv (g a).1 := by
  refine KeyedSys.lazy_pres_det _ _ (sStep crs decode) ?_ ?_ SInv ?_ ?_ ?_ t e hI
  · intro k t e
    cases e <;> simp [keyedS, KeyedSys.ofPorts, keyedSR, keyedSA, sStep, SPComp.map,
      SPComp.pure_bind]
  · intro t e
    cases e <;> simp [keyedS, KeyedSys.ofPorts, keyedSR, keyedSA, sStep, SPComp.map,
      SPComp.pure_bind]
  · rintro k t (c | e) ⟨h₁, h₂, h₃⟩
    · obtain ⟨hc, hd, hct⟩ := sStepR_fst decode (some k) t c
      simp only [SInv, sStep, Option.isSome_some] at h₁ ⊢
      exact ⟨by rw [hd, ← h₁], fun _ => hc, fun h => by rw [hd, ← h₁]⟩
    · obtain ⟨hc, hd, _, _⟩ := sStepA_fst crs (some k) t e
      simp only [SInv, sStep, Option.isSome_some] at h₁ ⊢
      have hd' := hd h₁.symm
      exact ⟨hd'.symm, fun _ => hc ▸ h₂ h₁.symm, fun _ => hd'⟩
  · rintro t (c | e) ⟨h₁, h₂, h₃⟩ hu k
    · obtain ⟨-, hd, hct⟩ := sStepR_fst decode (some k) t c
      simp only [Option.isSome_none] at h₁
      simp only [keyedS, KeyedSys.ofPorts, keyedSR, Sum.elim_inl, Bool.false_and,
        Bool.false_or, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hu
      exact absurd (h₃ hu.1.2) (by rw [← h₁]; simp)
    · obtain ⟨hc, -, hd, -⟩ := sStepA_fst crs (some k) t e
      rcases e with u | ct
      · simp only [keyedS, KeyedSys.ofPorts, keyedSA, Sum.elim_inr, Sum.isLeft_inl,
          Bool.true_and] at hu
        have hdl : (sStepA crs (some k) t (.inl u)).1.2.1 = true := by
          obtain ⟨co, dl, cto, o⟩ := t
          rcases co with _ | c
          · simp at hu
          · simp [sStepA]
        simp only [SInv, sStep, Option.isSome_some]
        exact ⟨hdl.symm, fun _ => hc ▸ hu, fun _ => hdl⟩
      · simp [keyedS, KeyedSys.ofPorts, keyedSA] at hu
  · rintro t (c | e) ⟨h₁, h₂, h₃⟩ _
    · obtain ⟨-, hd, hct⟩ := sStepR_fst decode none t c
      simp only [SInv, sStep, Option.isSome_none] at h₁ ⊢
      exact ⟨by rw [hd, h₁], fun h => absurd (h₁.trans (hd.symm.trans h)) (by simp),
        fun h => by rw [hct] at h; exact hd ▸ h₃ h⟩
    · obtain ⟨-, -, hd, hct⟩ := sStepA_fst crs none t e
      simp only [SInv, sStep, Option.isSome_none] at h₁ ⊢
      have hdf : (sStepA crs none t e).1.2.1 = false := by
        cases h : (sStepA crs none t e).1.2.1
        · rfl
        · rcases hd h with h' | h'
          · exact absurd (h₁.trans h') (by simp)
          · simp at h'
      refine ⟨hdf.symm, fun h => absurd (hdf.symm.trans h) (by simp), fun h => ?_⟩
      rcases hct h with h' | h'
      · exact absurd (h₁.trans (h₃ h')) (by simp)
      · exact h'

/-- Hop 2: the protocol against a corrupt sender with late randomness realizes the simulator
against a corrupt sender over `FOTSchedS otChoose` at distance `0`. The receiver's message
couples with the simulated one at the delivery that draws the randomness (`recvMsg_eq_simKey`),
and the receiver's output is the chosen messages of the extracted pairs (`otChoose_extractS`). -/
theorem late_realizes_sim (td : DecTD crs) (decode : gp.G → M) :
    Realizes ((keyedS (m := m) crs decode false).lazy (PMF.uniformFintype _))
      ((simProtS td decode).withSub (FOTSchedS otChoose)) fun _ _ => 0 := by
  refine realizes_zero_of_stepMap_on _ _ SInv (sMap td decode)
    (by simp [SInv, KeyedSys.lazy, keyedS, KeyedSys.ofPorts, keyedSR]) rfl
    (fun t e hI => late_pres crs decode t e hI) ?_
  rintro ⟨ko, co, dl, cto, o⟩ (c' | (u | ct)) ⟨h₁, h₂, h₃⟩
  · rw [simProtS, MultiHybrid.tensor_withSub_step_inl _ _ (FOTSchedS otChoose) FOTSched.recvSys
      (fun _ _ => rfl), MultiHybrid.idSim_stepFuel]
    simp only at h₁ h₂ h₃
    rcases co with _ | c
    · have hdl : dl = false := by cases dl <;> simp_all
      subst hdl
      have hko : ko = none := by cases ko <;> simp_all
      have hct : cto = none := by cases cto <;> simp_all
      subst hko hct
      simp [KeyedSys.lazy, KeyedSys.lazyStep, keyedS, KeyedSys.ofPorts, keyedSR, sStepR,
        FOTSched.recvSys, FOTSched.recvStep, sMap, simInbox, simRho, simX, SPComp.map,
        SPComp.pure_bind]
    · rcases cto with _ | ct
      · rcases ko with _ | r <;> rcases o with _ | _ <;>
          simp [KeyedSys.lazy, KeyedSys.lazyStep, keyedS, KeyedSys.ofPorts, keyedSR, sStepR,
            FOTSched.recvSys, FOTSched.recvStep, sMap, simInbox, simRho, simX, SPComp.map,
            SPComp.pure_bind]
      · have hdl : dl = true := h₃ rfl
        subst hdl
        obtain ⟨r, rfl⟩ : ∃ r, ko = some r := Option.isSome_iff_exists.mp h₁
        rcases o with _ | _ <;>
          simp [KeyedSys.lazy, KeyedSys.lazyStep, keyedS, KeyedSys.ofPorts, keyedSR, sStepR,
            FOTSched.recvSys, FOTSched.recvStep, sMap, simInbox, simRho, simX, SPComp.map,
            SPComp.pure_bind, vector_get_ofFn, otChoose_extractS]
  · rw [simProtS, MultiHybrid.tensor_withSub_step_inr _ _ (FOTSchedS otChoose)
      (Sys.ofPorts FOTSched.sendSys (FOTSched.schedSys otChoose)) (fun _ _ => rfl)]
    simp only at h₁ h₂ h₃
    rcases co with _ | c
    · have hdl : dl = false := by cases dl <;> simp_all
      subst hdl
      have hko : ko = none := by cases ko <;> simp_all
      subst hko
      simp [KeyedSys.lazy, KeyedSys.lazyStep, keyedS, KeyedSys.ofPorts, keyedSA, sStepA,
        simSAdv, simSStart, simSResume, MultiHybrid.stepFuel, MultiHybrid.idSim,
        MultiHybrid.drive, FOTSched.schedSys, FOTSched.schedStep, sMap, simInbox, simRho, simX,
        SPComp.map, SPComp.pure_bind]
    · rcases ko with _ | r
      · have hdl : dl = false := by cases dl <;> simp_all
        subst hdl
        have hct : cto = none := by cases cto <;> simp_all
        subst hct
        simp only [SPComp.map, KeyedSys.lazy, keyedS, KeyedSys.ofPorts, keyedSA, sStepA,
          recvMsg_eq_simKey td, SPComp.pure_bind, KeyedSys.lazyStep, Option.isSome_some,
          Bool.and_true, Sum.elim_inr, Sum.isLeft_inl, ↓reduceIte, ofPMF_uniformFintype,
          sampleFrom_uniform, sMap, simRho, simX, simInbox, SPComp.bind_assoc,
          MultiHybrid.stepFuel, simSAdv, simSStart, simSResume, simSKey, FOTSched.schedSys,
          FOTSched.schedStep, MultiHybrid.idSim, zero_le, sup_of_le_right, MultiHybrid.drive,
          Sys.ofPorts_step_inr, Option.isSome_none, Bool.false_or]
        exact SPComp.sample_bind_equiv (rhoEquiv td c) fun ρ =>
          SPComp.pure ((((), some (Vector.ofFn ρ), false),
            (⟨none, some c, none, o, false⟩ :
              SchedSt (Fin m → M × M) (Fin m → Bool) (Fin m → M))),
            (Sum.inr (some (simKey crs ρ)) : Option (Fin m → M) ⊕ Option (Key gp m)))
      · have hdl : dl = true := by cases dl <;> simp_all
        subst hdl
        simp [KeyedSys.lazy, KeyedSys.lazyStep, keyedS, KeyedSys.ofPorts, keyedSA, sStepA,
          simSAdv, simSStart, simSResume, simSKey, MultiHybrid.stepFuel, MultiHybrid.idSim,
          MultiHybrid.drive, FOTSched.schedSys, FOTSched.schedStep, sMap, simInbox, simRho, simX,
          vector_get_ofFn,
          SPComp.map, SPComp.pure_bind, recvMsg_eq_simKey td]
  · rw [simProtS, MultiHybrid.tensor_withSub_step_inr _ _ (FOTSchedS otChoose)
      (Sys.ofPorts FOTSched.sendSys (FOTSched.schedSys otChoose)) (fun _ _ => rfl)]
    simp only at h₁ h₂ h₃
    rcases dl with _ | _
    · have hko : ko = none := by cases ko <;> simp_all
      have hct : cto = none := by cases cto <;> simp_all
      subst hko hct
      rcases co with _ | c <;>
        simp [KeyedSys.lazy, KeyedSys.lazyStep, keyedS, KeyedSys.ofPorts, keyedSA, sStepA,
          simSAdv, simSStart, MultiHybrid.stepFuel, MultiHybrid.idSim,
          MultiHybrid.drive, sMap, simInbox, simRho, simX, SPComp.map, SPComp.pure_bind]
    · obtain ⟨r, rfl⟩ : ∃ r, ko = some r := Option.isSome_iff_exists.mp h₁
      obtain ⟨c, rfl⟩ : ∃ c, co = some c := Option.isSome_iff_exists.mp (h₂ rfl)
      rcases cto with _ | ct₀ <;> rcases o with _ | _ <;>
        simp [KeyedSys.lazy, KeyedSys.lazyStep, keyedS, KeyedSys.ofPorts, keyedSA, sStepA,
          simSAdv, simSStart, simSResume, MultiHybrid.stepFuel, MultiHybrid.idSim,
          MultiHybrid.drive, FOTSched.sendSys, FOTSched.sendStep, FOTSched.schedSys,
          FOTSched.schedStep, sMap, simInbox, simRho, simX, SPComp.map, SPComp.pure_bind]

/-- **The dual-mode OT against a corrupt sender in decryption mode as a square.** Ideal
functionality: `FOTSchedS otChoose`, `F_OT` with scheduled delivery for `m` transfers, with the
receiver on the honest port and the sender beside the scheduler on the adversary port. Real
protocol: `realS crs decode`, whose receiver sends keys of the chosen branches and outputs the
decoded decryptions of the chosen branches of the sender's message. CRS: decryption mode with
trapdoor `td`. Simulator: `pvwSimSend td decode`, which sends keys of branch `0`, extracts both
messages of each pair with the decryption trapdoor, and delivers the receiver's output at the
activation at which the real sender's message arrives. Distance `0`: in decryption mode the
receiver's message does not depend on its choices (`recvMsg_eq_simKey`). Corrupt sender, one
transfer of `m` message pairs. -/
theorem pvw_realizesSim_corruptSender (td : DecTD crs) (decode : gp.G → M) :
    RealizesSim (realS crs decode) (FOTSchedS otChoose) (pvwSimSend (m := m) td decode)
      fun _ _ => 0 :=
  fun ζ Z =>
    le_of_le_of_eq ((Realizes.trans (realS_realizes_late crs decode)
      (late_realizes_sim td decode)) ζ Z) (add_zero _)

end CorruptSender

/-! ## Mode indistinguishability -/

section Modes

open CatCryptCore.Examples.CyclicGroupDDH (CyclicGroup DDH_real DDH_ideal DDH_Advantage)

/-- Multiplication in a prime-order group is commutative. -/
theorem groupMul_comm' (a b : gp.G) : gp.groupMul a b = gp.groupMul b a := by
  obtain ⟨α, rfl⟩ := gp.exp_surj a
  obtain ⟨β, rfl⟩ := gp.exp_surj b
  rw [← exp_add', ← exp_add', add_comm]

variable (gp) in
/-- The group of `gp` as a cyclic group, for the DDH games of `CyclicGroupDDH`. -/
@[instance_reducible]
noncomputable def cyclicGroup : CyclicGroup gp.G where
  Exp := gp.Scalar
  finG := gp.finG
  neG := gp.neG
  finExp := gp.finScalar
  neExp := gp.neScalar
  gen := gp.generator
  pow := gp.exp
  mul := gp.groupMul
  inv := gp.groupInv
  expMul := gp.scalarMul
  expNeg := gp.scalarNeg
  one := gp.identity
  pow_comm a b := by rw [gp.scalarMul_comm]
  mul_assoc := gp.groupMul_assoc
  mul_comm := groupMul_comm'
  mul_inv := gp.groupMul_inv
  mul_one := gp.groupMul_identity
  pow_bij := ⟨fun a b h => gp.exp_inj a b h, gp.exp_surj⟩

/-- The CRS of a Diffie–Hellman tuple `(g, g ^ a, g ^ b, g ^ (a b))`: decryption mode. -/
def decCRS (k : gp.Scalar × gp.Scalar) : CRS gp :=
  ⟨gp.generator, gp.exp k.1, gp.exp k.2, gp.exp (k.1 * k.2)⟩

/-- The CRS of a random tuple `(g, g ^ a, g ^ b, g ^ c)`: messy mode unless `b = 0` or
`c = a b`. -/
def randCRS (k : gp.Scalar × gp.Scalar × gp.Scalar) : CRS gp :=
  ⟨gp.generator, gp.exp k.1, gp.exp k.2.1, gp.exp k.2.2⟩

/-- A Diffie–Hellman CRS with `b ≠ 0` is in decryption mode with trapdoor `b`. -/
def decCRS_td (a b : gp.Scalar) (hb : b ≠ 0) : DecTD (decCRS (a, b)) where
  y := b
  y_ne := hb
  g₁_eq := gp.groupExp_generator b
  h₁_eq := (groupExp_exp' a b).symm

/-- A random CRS with `b ≠ 0` and `c ≠ a b` is in messy mode with trapdoor `(a, c / b)`. -/
def randCRS_td (a b c : gp.Scalar) (hb : b ≠ 0) (hc : c ≠ a * b) :
    MessyTD (randCRS (a, b, c)) where
  x₀ := a
  x₁ := gp.scalarDiv c b
  h₀_eq := gp.groupExp_generator a
  h₁_eq := by
    change gp.exp c = gp.groupExp (gp.exp b) (gp.scalarDiv c b)
    rw [groupExp_exp', mul_comm]
    exact congrArg gp.exp (gp.div_mul_cancel c b hb).symm
  x_ne h := hc (by rw [h]; exact (gp.div_mul_cancel c b hb).symm)

variable {τ E O : Type}

/-- The keyed system that runs `S crs` from the state `t₀` with the CRS `crsOf k` of the key. -/
noncomputable def crsKeyed {K : Type} (crsOf : K → CRS gp) (S : CRS gp → Sys τ E O) (t₀ : τ) :
    KeyedSys K τ E O where
  init := t₀
  step k := (S (crsOf k)).step
  step₀ _ _ := SPComp.fail
  uses _ _ := true

/-- The system `S crs` from the state `t₀` with the CRS `crsOf k` for a uniform key `k`, drawn at
the first activation. -/
noncomputable def crsSys {K : Type} [Fintype K] [Nonempty K] (crsOf : K → CRS gp)
    (S : CRS gp → Sys τ E O) (t₀ : τ) : Sys (Option K × τ) E O :=
  (crsKeyed crsOf S t₀).lazy (PMF.uniformFintype K)

/-- **Reduction to DDH.** On a triple `(A, B, C)`, run the environment `Z`, from its initial
heap, against `S` with the CRS `(g, A, B, C)` from the state `t₀`, and output the bit of its
distinguisher. -/
noncomputable def ddhEnvRed (S : CRS gp → Sys τ E O) (t₀ : τ) {ζ : Type}
    (Z : Env (Strat ζ E O) ζ) : gp.G × gp.G × gp.G → SPComp Bool :=
  fixHeap Z.heap fun tr =>
    SPComp.bind (view ((crsKeyed id S t₀).withKey ⟨gp.generator, tr.1, tr.2.1, tr.2.2⟩) Z.input)
      Z.dist

/-- **Mode indistinguishability.** For every family `S` of systems indexed by the CRS, running
`S` with a CRS of a Diffie–Hellman tuple (decryption mode) and with a CRS of a random tuple
(messy mode when `b ≠ 0` and `c ≠ a b`, `randCRS_td`) differ by the DDH advantage of the
explicit reduction `ddhEnvRed S t₀ Z` of the environment. -/
theorem crs_ddh_hop (S : CRS gp → Sys τ E O) (t₀ : τ) :
    Realizes (crsSys decCRS S t₀) (crsSys randCRS S t₀) fun _ Z =>
      DDH_Advantage (CG := cyclicGroup gp) gp.G
        (ddhEnvRed S t₀ Z) := by
  intro ζ Z
  have hu : ∀ {K : Type} (crsOf : K → CRS gp) (k : K) (t : τ) (e : E),
      (crsKeyed crsOf S t₀).uses t e = false →
        (crsKeyed crsOf S t₀).step k t e = (crsKeyed crsOf S t₀).step₀ t e :=
    fun _ _ _ _ h => by simp [crsKeyed] at h
  have hr : view (crsSys decCRS S t₀) Z.input =
      SPComp.bind (DDH_real (CG := cyclicGroup gp) gp.G) fun tr =>
        view ((crsKeyed id S t₀).withKey ⟨gp.generator, tr.1, tr.2.1, tr.2.2⟩) Z.input := by
    rw [crsSys, KeyedSys.view_lazy _ _ (hu _) Z.input, ofPMF_uniformFintype, sampleFrom_uniform,
      SPComp.sample_prod_eq]
    simp only [DDH_real, SPComp.monad_bind_eq,
      SPComp.monad_pure_eq, SPComp.bind_assoc, SPComp.pure_bind]
    rfl
  have hi : view (crsSys randCRS S t₀) Z.input =
      SPComp.bind (DDH_ideal (CG := cyclicGroup gp) gp.G) fun tr =>
        view ((crsKeyed id S t₀).withKey ⟨gp.generator, tr.1, tr.2.1, tr.2.2⟩) Z.input := by
    rw [crsSys, KeyedSys.view_lazy _ _ (hu _) Z.input, ofPMF_uniformFintype, sampleFrom_uniform,
      SPComp.sample_prod_eq, SPComp.sample_prod_eq]
    simp only [DDH_ideal, SPComp.monad_bind_eq,
      SPComp.monad_pure_eq, SPComp.bind_assoc, SPComp.pure_bind]
    rfl
  change absDiff _ _ ≤ _
  rw [hr, hi, SPComp.bind_assoc, SPComp.bind_assoc,
    IKNPSquare.prTrue_bind_fixHeap (G := DDH_real
      (CG := cyclicGroup gp) gp.G) (by
      unfold DDH_real
      aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })) _ Z.heap,
    IKNPSquare.prTrue_bind_fixHeap (G := DDH_ideal
      (CG := cyclicGroup gp) gp.G) (by
      unfold DDH_ideal
      aesop (rule_sets := [CatCryptRel]) (config := { terminal := true })) _ Z.heap]
  exact le_rfl

end Modes

end CatCrypt.Crypto.OT.PVW
