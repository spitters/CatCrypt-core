/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KVAC.AlgMac

/-!
# The algebraic MAC of the Signal private group system (CPZ20 §3.1)

The MAC `MAC_n` of Chase, Perrin and Zaverucha on `n` attributes `M_1, …, M_n ∈ G`, as an
instance `AlgMac.macN G n` of the record `AlgMac`, over a cyclic group `G` with exponent ring.

* The parameters are `(G_w, G_{w'}, G_{x0}, G_{x1}, G_V, (G_{y_i})_i, (G_{m_i})_i)`, sampled
  uniformly (the scheme derives them with `HashToG`; in the random-oracle model they are uniform).
* The key is `(w, w', x0, x1, (y_i)_i)`, uniform, with `W = G_w^w`.
* The issuer parameters are `C_W = G_w^w G_{w'}^{w'}` and
  `I = G_V / (G_{x0}^{x0} G_{x1}^{x1} Π G_{y_i}^{y_i})`.
* `MAC(sk, M)` with coins `(t, U)` is `(t, U, V)`, `V = W U^{x0 + x1 t} Π M_i^{y_i}`.
* `Verify(sk, M, (t, U, V))` recomputes `V`; as in the paper, it does not test `U ≠ 1`.
* The helper predicate at `(A0, A1, A, Z)` tests `Z = W A0^{x0} A1^{x1} Π A_i^{y_i}`: the test the
  verifier of a presentation performs on the commitments `(C_{x0}, C_{x1}, C_{y_i})` and
  `C_V / Z`. At `(U, U^t, M, V)` it is verification (`macN_help_eq_verify`).

A scalar attribute `m` at position `i` enters as the group attribute `G_{m_i}^m` (`scalarAttr`);
which positions hold scalar attributes is fixed per key and matters only for the presentation
proofs, so the MAC is defined on group attributes.

## The deployed variant (libsignal `zkcredential`)

libsignal's `zkcredential` crate (`credentials.rs`) implements this MAC with these differences
from CPZ20 §3.1:

* Slot 0 holds the public attributes, hashed to a point with `ShoHmacSha256` keyed by the
  credential label; at most 7 attribute points.
* The public key holds one `I_n` for each arity `n = 2, …, 7` instead of one `I` for the
  maximal arity, and the coefficient of slot 0 depends on the arity. In `StandardMode`,
  `y_0(n) = ShoHmacSha256("Signal_ZKCredential_SlotZeroBlinding_20260805", y[0], n)` for
  `n ≥ 3` and `y_0(2) = y[0]`; `I_n = G_V - x0 G_{x0} - x1 G_{x1} - Σ_{i=1}^{n-1} y_i G_{y_i}
  - y_0(n) G_{y_0}`, and the MAC and the verifier use `y_0(n)` for the arity `n` of the
  credential. In `LegacyMode`, `y_0(n) = y[0]` for every `n`, which the crate documents as weaker.
* Neither the MAC nor the presentation verification tests `U ≠ 1`.

`macN G n` is the MAC at one fixed arity `n`, the setting of CPZ20 Theorem 14; the per-arity
`y_0(n)` is an independent key component at each arity when `ShoHmacSha256` is modelled as a
random oracle.

## Main definitions

* `AlgMac.MacN.iparams`, `AlgMac.MacN.macV`, `AlgMac.MacN.helpV` — the issuer parameters, the
  tag component `V` and the helper equation.
* `AlgMac.macN` — the record instance.

## Main results

* `AlgMac.macN_correct` — correctness.
* `AlgMac.macN_help_eq_verify` — the helper predicate at `(U, U^t, M, V)` is verification.

## Targets of later work

CPZ20 Theorem 14 for `macN`, stated in the module docstring of `AlgMac`: Lemma 3 (cmva to cma,
factor `q_v + 1`), the Type 1 reduction to `UFCMA_Advantage (macGGM G)`, and the Type 2/3 DDH
reduction with a guess among the `q_m` MAC queries. `SUFCMVAHelp_Advantage (macN G n)` is the
target of the algebraic-group-model analysis following Orrù 2024.

## References

* M. Chase, T. Perrin, G. Zaverucha, *The Signal Private Group System and Anonymous
  Credentials Supporting Efficient Verifiable Encryption*, CCS 2020, §3.1 and Theorem 14.
  <https://eprint.iacr.org/2019/1416>
* M. Orrù, *Revisiting Keyed-Verification Anonymous Credentials*, 2024.
  <https://eprint.iacr.org/2024/1552>
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KVAC

open CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.OT

namespace AlgMac.MacN

variable {G : Type} [CGR : CyclicGroupRing G]

/-- The product of a list of group elements. -/
def gprod (l : List G) : G := l.foldr CGR.mul CGR.one

variable {n : ℕ}

/-- `Π_i M_i^{y_i}`. -/
noncomputable def attrProd (M : Fin n → G) (y : Fin n → CGR.Exp) : G :=
  gprod (List.ofFn fun i => CyclicGroup.elemPow (M i) (y i))

/-- The parameters `(G_w, G_{w'}, G_{x0}, G_{x1}, G_V, (G_{y_i})_i, (G_{m_i})_i)`. -/
abbrev Par (G : Type) [CyclicGroupRing G] (n : ℕ) :=
  G × G × G × G × G × (Fin n → G) × (Fin n → G)

/-- The key `(w, w', x0, x1, (y_i)_i)`. -/
abbrev Key (G : Type) [CGR : CyclicGroupRing G] (n : ℕ) :=
  CGR.Exp × CGR.Exp × CGR.Exp × CGR.Exp × (Fin n → CGR.Exp)

/-- `G_w`. -/ abbrev gw (p : Par G n) : G := p.1
/-- `G_{w'}`. -/ abbrev gw' (p : Par G n) : G := p.2.1
/-- `G_{x0}`. -/ abbrev gx0 (p : Par G n) : G := p.2.2.1
/-- `G_{x1}`. -/ abbrev gx1 (p : Par G n) : G := p.2.2.2.1
/-- `G_V`. -/ abbrev gV (p : Par G n) : G := p.2.2.2.2.1
/-- `G_{y_i}`. -/ abbrev gy (p : Par G n) : Fin n → G := p.2.2.2.2.2.1
/-- `G_{m_i}`. -/ abbrev gm (p : Par G n) : Fin n → G := p.2.2.2.2.2.2

/-- `w`. -/ abbrev w (k : Key G n) : CGR.Exp := k.1
/-- `w'`. -/ abbrev w' (k : Key G n) : CGR.Exp := k.2.1
/-- `x0`. -/ abbrev x0 (k : Key G n) : CGR.Exp := k.2.2.1
/-- `x1`. -/ abbrev x1 (k : Key G n) : CGR.Exp := k.2.2.2.1
/-- `(y_i)_i`. -/ abbrev y (k : Key G n) : Fin n → CGR.Exp := k.2.2.2.2

/-- `W = G_w^w`. -/
noncomputable def bigW (p : Par G n) (k : Key G n) : G := CyclicGroup.elemPow (gw p) (w k)

/-- The scalar attribute `m` at position `i`, encoded as `G_{m_i}^m`. -/
noncomputable def scalarAttr (p : Par G n) (i : Fin n) (m : CGR.Exp) : G :=
  CyclicGroup.elemPow (gm p i) m

/-- The issuer parameters `C_W = G_w^w G_{w'}^{w'}` and
`I = G_V / (G_{x0}^{x0} G_{x1}^{x1} Π G_{y_i}^{y_i})`. -/
noncomputable def iparams (p : Par G n) (k : Key G n) : G × G :=
  (CGR.mul (bigW p k) (CyclicGroup.elemPow (gw' p) (w' k)),
    CGR.mul (gV p) (CGR.inv (CGR.mul (CGR.mul (CyclicGroup.elemPow (gx0 p) (x0 k))
      (CyclicGroup.elemPow (gx1 p) (x1 k))) (attrProd (gy p) (y k)))))

/-- `V = W U^{x0 + x1 t} Π M_i^{y_i}`. -/
noncomputable def macV (p : Par G n) (k : Key G n) (M : Fin n → G) (t : CGR.Exp) (U : G) : G :=
  CGR.mul (CGR.mul (bigW p k) (CyclicGroup.elemPow U (CGR.expAdd (x0 k) (CGR.expMul (x1 k) t))))
    (attrProd M (y k))

/-- The helper equation `Z = W A0^{x0} A1^{x1} Π A_i^{y_i}`. -/
noncomputable def helpV (p : Par G n) (k : Key G n) (A0 A1 : G) (A : Fin n → G) : G :=
  CGR.mul (CGR.mul (CGR.mul (bigW p k) (CyclicGroup.elemPow A0 (x0 k)))
    (CyclicGroup.elemPow A1 (x1 k))) (attrProd A (y k))

/-- `U^{x0 + x1 t} = U^{x0} (U^t)^{x1}`. -/
theorem elemPow_ggmExp (U : G) (a b t : CGR.Exp) :
    CyclicGroup.elemPow U (CGR.expAdd a (CGR.expMul b t)) =
      CGR.mul (CyclicGroup.elemPow U a) (CyclicGroup.elemPow (CyclicGroup.elemPow U t) b) := by
  rw [CyclicGroupRing.elemPow_add, ← CyclicGroupRing.elemPow_mul, CGR.expMul_comm']

/-- At `(U, U^t, M)` the helper equation is the equation of verification. -/
theorem helpV_eq_macV (p : Par G n) (k : Key G n) (M : Fin n → G) (t : CGR.Exp) (U : G) :
    helpV p k U (CyclicGroup.elemPow U t) M = macV p k M t U := by
  rw [helpV, macV, elemPow_ggmExp, CGR.mul_assoc (bigW p k)]

end AlgMac.MacN

namespace AlgMac

open MacN

variable (G : Type) [CGR : CyclicGroupRing G] [DecidableEq G] [DecidableEq CGR.Exp]

/-- **The algebraic MAC of CPZ20 §3.1 (`MAC_n`)** on `n` group attributes, with the
parameters, key, issuer parameters, tag and helper predicate of the module docstring. -/
noncomputable def macN (n : ℕ) : AlgMac where
  Par := MacN.Par G n
  KeyCoins := MacN.Key G n
  Key := MacN.Key G n
  PK := G × G
  Msg := Fin n → G
  MacCoins := CGR.Exp × G
  Tag := CGR.Exp × G × G
  HelpQ := G × G × (Fin n → G) × G
  keyGen _ kc := kc
  pk := iparams
  mac p k M r := (r.1, r.2, macV p k M r.1 r.2)
  verify p k M σ := decide (σ.2.2 = macV p k M σ.1 σ.2.1)
  help p k q := decide (q.2.2.2 = helpV p k q.1 q.2.1 q.2.2.1)

/-- **Correctness of `MAC_n`.** Every tag `(t, U, V)` of the MAC algorithm verifies. -/
theorem macN_correct (n : ℕ) : (macN G n).Correct := by
  intro p kc M r
  simp [macN]

/-- The helper predicate at `(U, U^t, M, V)` answers verification of `(t, U, V)` on `M`. -/
theorem macN_help_eq_verify (n : ℕ) (p : MacN.Par G n) (k : MacN.Key G n) (M : Fin n → G)
    (t : CGR.Exp) (U V : G) :
    (macN G n).help p k (U, CyclicGroup.elemPow U t, M, V) = (macN G n).verify p k M (t, U, V) := by
  simp [macN, helpV_eq_macV]

end AlgMac

end CatCrypt.Crypto.KVAC
