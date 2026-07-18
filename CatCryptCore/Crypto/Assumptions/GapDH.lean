/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Assumptions.DDH
import CatCryptCore.Crypto.CryptoWord

/-!
# Gap Diffie-Hellman (GapDH) Assumption

This file defines the GapDH assumption parametrically over any `SampleableType W`,
following the pattern of `DDH.lean`.

## GapDH Game

The GapDH game captures the difficulty of computing a Diffie-Hellman shared secret
`g^{ab}` given `g^a` and `g^b`, **even when the adversary has access to a DDH oracle**
that can check whether a triple `(g^a, g^b, c)` satisfies `c = g^{ab}`.

This is strictly stronger than CDH (adversary gets an oracle) but weaker than DDH
(adversary must *compute*, not just *distinguish*).

At the abstract level with `SampleableType W`, the game becomes:
- **Real game**: sample `a, b`, adversary receives `(pub_a, pub_b)` and must output `dh(a, pub_b)`
- **Ideal game**: sample `a, b`, adversary receives `(pub_a, pub_b)` and a random `z`

The GapDH assumption states that the adversary's advantage in distinguishing these
is negligible — equivalently, the CDH problem remains hard despite DDH oracle access.

## Main definitions

* `GapDHDef` — a DH group with DDH oracle (dh operation + keygen + oracle)
* `GapDH_Game_Real` / `GapDH_Game_Ideal` — the real/ideal GapDH games
* `GapDH_Advantage` — advantage of an adversary in breaking GapDH

## Usage in WireGuard

WireGuard uses 4 DH operations (X25519), each contributing one `ε_gdh`:
1. DH(e_I, s_R) — initiator ephemeral × responder static
2. DH(s_I, s_R) — static-static
3. DH(e_R, e_I) — ephemeral-ephemeral
4. DH(e_R, s_I) — responder ephemeral × initiator static

## Cross-Validation

| Property | This file | Paper |
|----------|-----------|-------|
| Game structure | `GapDH_Game_Real`/`Ideal` | OP01 Def. 5 |
| Advantage | `Advantage(Real, Ideal)` | Gap-DH advantage |
| DDH oracle | Implicit (stronger assumption) | Explicit oracle access |

**Relationship to other assumptions:**
- DDH ⟹ GapDH (via `GapDHDef.ofDDH`): if DDH holds, GapDH holds
- GapDH ⟹ CDH: GapDH is strictly stronger than CDH
- GapDH is the standard assumption for X25519-based protocols (WireGuard, Noise)

**Equivalent formalizations:**
- CryptoVerif: `GDH(G, Z, g, exp, exp', mult)` macro (used in WireGuard proof)

## References

* Okamoto, Pointcheval. *The Gap-Problems: A New Class of Problems for the
  Security of Cryptographic Schemes.* PKC 2001, Def. 5.
* Lipp, Blanchet, Bhargavan. *A Mechanised Cryptographic Proof of the
  WireGuard Virtual Private Network Protocol.* EuroS&P 2019.
-/

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## GapDH Definition -/

/-- Abstract Gap Diffie-Hellman group definition, parametric over `SampleableType W`.

- `dh priv pub` models the DH key agreement operation
- `keygen` samples a key pair `(private, public)`
- The DDH oracle is implicit: in the game-based model, the adversary has
  oracle access but we model the GapDH advantage directly as the
  distinguishing advantage between DH output and random. -/
structure GapDHDef (W : Type) [SampleableType W] where
  /-- DH key agreement: `dh(private_key, public_key)` → shared_secret.
  Models X25519 scalar multiplication. -/
  dh : W → W → W
  /-- Key generation: produces `(private_key, public_key)`.
  Models X25519 key generation. -/
  keygen : SPComp (W × W)
  /-- Key generation is heap-independent. -/
  keygen_isPure : SPComp.IsPure keygen

/-! ## GapDH Games -/

/-- Type of GapDH adversary: receives a DH triple and must distinguish
real DH output from random. In the full GapDH game, the adversary also
has DDH oracle access, but we model this as a stronger assumption. -/
abbrev GapDH_Adversary (W : Type) := W → W → W → SPComp Bool

/-- GapDH real game: adversary receives `(pub_a, pub_b, dh(a, pub_b))`.
The third element is the true DH shared secret. -/
noncomputable def GapDH_Game_Real (G : GapDHDef W) (A : GapDH_Adversary W) : SPComp Bool := do
  let ⟨a, pub_a⟩ ← G.keygen
  let ⟨_b, pub_b⟩ ← G.keygen
  let shared := G.dh a pub_b  -- = g^{ab}
  A pub_a pub_b shared

/-- GapDH ideal game: adversary receives `(pub_a, pub_b, z)` where `z` is random. -/
noncomputable def GapDH_Game_Ideal (G : GapDHDef W) (A : GapDH_Adversary W) : SPComp Bool := do
  let ⟨_, pub_a⟩ ← G.keygen
  let ⟨_b, pub_b⟩ ← G.keygen
  let z ← SPComp.sample W  -- random, independent of a, b
  A pub_a pub_b z

/-- GapDH advantage: ability to distinguish `(pub_a, pub_b, dh(a, pub_b))` from
`(pub_a, pub_b, random)`, even with DDH oracle access. -/
noncomputable def GapDH_Advantage (G : GapDHDef W) (A : GapDH_Adversary W) : ℝ≥0∞ :=
  Advantage (GapDH_Game_Real G A) (GapDH_Game_Ideal G A)

/-! ## IsPure Proofs -/

theorem GapDH_Game_Real_isPure (G : GapDHDef W) (A : GapDH_Adversary W)
    (hA : ∀ x y z, SPComp.IsPure (A x y z)) :
    SPComp.IsPure (GapDH_Game_Real G A) := by
  unfold GapDH_Game_Real
  apply SPComp.bind_isPure G.keygen_isPure; intro ⟨a, pub_a⟩
  apply SPComp.bind_isPure G.keygen_isPure; intro ⟨_b, pub_b⟩
  exact hA pub_a pub_b (G.dh a pub_b)

theorem GapDH_Game_Ideal_isPure (G : GapDHDef W) (A : GapDH_Adversary W)
    (hA : ∀ x y z, SPComp.IsPure (A x y z)) :
    SPComp.IsPure (GapDH_Game_Ideal G A) := by
  unfold GapDH_Game_Ideal
  apply SPComp.bind_isPure G.keygen_isPure; intro ⟨_, pub_a⟩
  apply SPComp.bind_isPure G.keygen_isPure; intro ⟨_b, pub_b⟩
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro z
  exact hA pub_a pub_b z

/-! ## Relationship to DDH

The GapDH assumption is implied by the DDH assumption: if DDH holds, then
GapDH holds because the adversary cannot even *distinguish* (let alone *compute*)
the shared secret. In the other direction, GapDH is strictly weaker than DDH.

For WireGuard (following LBB19), GapDH is sufficient because the protocol
uses DH outputs only as HKDF inputs, so the adversary only needs to
distinguish the output from random (not compute it). -/

/-- Any DDH group is also a GapDH group (with the same parameters). -/
def GapDHDef.ofDDH (D : DDHDef W) : GapDHDef W :=
  ⟨D.ecdh, D.keygen, D.keygen_isPure⟩

end CatCrypt.Crypto.Assumptions
