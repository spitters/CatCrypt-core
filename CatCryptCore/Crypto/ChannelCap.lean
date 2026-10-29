/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Order.Basic

/-!
# Channel capabilities

A channel capability names the powers of a network adversary on a communication: reading the
plaintext, dropping (or delaying, reordering) the message, and tampering with (or injecting) it.
The three named levels are F_NET (`insecure`), F_AUTH (`auth`) and F_SC (`secure`). The
capability order relates `c₁ ≤ c₂` when `c₁` grants no more powers than `c₂`; fewer powers is a
stronger channel, so `secure ≤ auth ≤ insecure`.

## Main definitions

* `ChannelCap`: a triple `⟨read, drop, tamper⟩` of adversary powers.
* `ChannelCap.insecure`, `ChannelCap.auth`, `ChannelCap.secure`: the three named levels.
* `ChannelCap.le`: the capability order.
* `ChannelCap.wireLeak`: the adversary's observation of one message, the plaintext if `read`
  and otherwise its leakage.

## Main results

* `secure_le_auth`, `auth_le_insecure`, `secure_le_insecure`, `auth_lt_insecure`: the order of
  the named levels.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Choreography

/-- The powers an active network adversary has on a communication.

    - `read`: the adversary reads the plaintext off the wire.
    - `drop`: the adversary can drop, delay, or reorder the message.
    - `tamper`: the adversary can modify or inject the message. -/
structure ChannelCap where
  /-- The adversary reads the plaintext. -/
  read : Bool
  /-- The adversary drops, delays, or reorders the message. -/
  drop : Bool
  /-- The adversary modifies or injects the message. -/
  tamper : Bool
deriving DecidableEq, Repr

/-- F_NET: fully insecure channel — the adversary reads, drops, and tampers. -/
def ChannelCap.insecure : ChannelCap := ⟨true, true, true⟩

/-- F_AUTH: authenticated channel — the adversary reads and drops, but the
    delivered message has integrity (no tampering). -/
def ChannelCap.auth : ChannelCap := ⟨true, true, false⟩

/-- F_SC / F_SMT: secure channel — the adversary may drop, and observes only the
    leakage (length), with no plaintext read and no tampering. -/
def ChannelCap.secure : ChannelCap := ⟨false, true, false⟩

/-- The capability order: `c₁ ≤ c₂` iff every power of `c₁` is a power of `c₂`.
    Fewer adversary powers is a stronger channel, so `secure ≤ auth ≤ insecure`. -/
def ChannelCap.le (c₁ c₂ : ChannelCap) : Prop :=
  (c₁.read = true → c₂.read = true) ∧
  (c₁.drop = true → c₂.drop = true) ∧
  (c₁.tamper = true → c₂.tamper = true)

instance : LE ChannelCap := ⟨ChannelCap.le⟩

instance : PartialOrder ChannelCap where
  le := ChannelCap.le
  le_refl _ := ⟨id, id, id⟩
  le_trans _ _ _ hab hbc :=
    ⟨hbc.1 ∘ hab.1, hbc.2.1 ∘ hab.2.1, hbc.2.2 ∘ hab.2.2⟩
  le_antisymm a b hab hba := by
    obtain ⟨ra, da, ta⟩ := a
    obtain ⟨rb, db, tb⟩ := b
    obtain ⟨h1, h2, h3⟩ := hab
    obtain ⟨g1, g2, g3⟩ := hba
    have e1 : ra = rb := by cases ra <;> cases rb <;> simp_all
    have e2 : da = db := by cases da <;> cases db <;> simp_all
    have e3 : ta = tb := by cases ta <;> cases tb <;> simp_all
    subst e1; subst e2; subst e3; rfl

/-- `secure` grants no more powers than `auth`. -/
theorem secure_le_auth : ChannelCap.secure ≤ ChannelCap.auth :=
  ⟨fun _ => rfl, fun _ => rfl, fun h => h⟩

/-- `auth` grants no more powers than `insecure`. -/
theorem auth_le_insecure : ChannelCap.auth ≤ ChannelCap.insecure :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- `secure` grants no more powers than `insecure`. -/
theorem secure_le_insecure : ChannelCap.secure ≤ ChannelCap.insecure :=
  le_trans secure_le_auth auth_le_insecure

/-- `insecure` grants strictly more powers than `auth`. -/
theorem auth_lt_insecure : ChannelCap.auth < ChannelCap.insecure :=
  lt_of_le_of_ne auth_le_insecure (by decide)

/-- The adversary's observation of one message under `cap`: the plaintext if
    `read`, otherwise only the leakage `ℓ m`. -/
def ChannelCap.wireLeak (cap : ChannelCap) {Val Leak : Type} (ℓ : Val → Leak)
    (m : Val) : Val ⊕ Leak :=
  bif cap.read then Sum.inl m else Sum.inr (ℓ m)

end CatCrypt.Crypto.Choreography
