/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KVAC.MacN
public import CatCryptCore.Crypto.OracleSimulation

/-!
# `MAC_n` with the helper oracle in the algebraic group model

The suf-cmva-Help game of `AlgMac.macN G n` (CPZ20 §3.1, group attributes) for algebraic
adversaries (Fuchsbauer, Kiltz, Loss 2018), and the two reductions of its security proof.

## Algebraic adversaries

An algebraic adversary gives every group element it sends (attributes, tag components, helper
arguments, the forgery) as a representation: a list of exponents over the list of group
elements it has received, in order of receipt. The list starts with the generator, the
parameters `(G_w, G_{w'}, G_{x0}, G_{x1}, G_V, (G_{y_i}), (G_{m_i}))` and the issuer parameters
`(C_W, I)` (`basis0`), and each answer `(t, U, V)` of the MAC oracle appends `U` and `V`
(`extend`). `toAdv` evaluates the representations and turns an algebraic adversary into an
adversary of `AlgMac.sufCmvaHelpGame`; an adversary that outputs an element together with a
representation of it (the formulation of FKL18, Definition 2.1) is of this form. The class is
`AlgAdv G n`, and its advantage is `sufCmvaHelpAGM_Advantage`, the advantage of
`AlgMac.SUFCMVAHelp_Advantage (macN G n)` at the evaluated adversary.

## The reductions

* `reductionZ A`: a DL adversary. On the challenge `X = g^x` it sets `G_{x0} = g^{γ0}` for a
  uniform `γ0` and `G_{x1} = X`, samples the remaining parameters and the whole key, runs `A`
  against the honest oracles and outputs `γ0 · t*`. It solves DL when
  `t* = log_{G_{x0}} G_{x1}`.
* `reductionAlg one roots A`: a `D`-DL adversary. On `(g, g^χ, …, g^{χ^D})` it writes every
  secret exponent `v ∈ {w, w', x0, x1, y_1, …, y_n, u_1, …}` as `v = a_v + b_v χ` with uniform
  `a_v, b_v`, samples the parameters as `g^γ` with known `γ`, keeps the exponent of every
  received element as a polynomial in `χ` (`simO`), answers MAC queries with group elements
  computed from these polynomials, answers verification and helper queries by testing whether
  the polynomial of the equation vanishes at `χ`, and at the end returns the root of the
  polynomial `ψ*` of the forgery equation whose power of `g` is `g^χ`. The argument `roots`
  is a root-finding algorithm for polynomials over the exponent field and `one` is the unit
  of the exponent ring.

## Target theorem

For an algebraic adversary `A` that makes at most `q_m` MAC queries
(`OracleAdv.IsQueryBoundBy macCost`), and `D = q_m + 2`:

`sufCmvaHelpAGM_Advantage A ≤ DL_Adv (reductionZ (AlgAdv.toAdv A))`
`  + kDL_Adv D (reductionAlg one roots A) + (D + 3) / p + q_m (q_m - 1) / (2 p)`,

where `p` is the group order, `DL_Adv` and `kDL_Adv D` are the DL and `D`-DL advantages of the
group (row U1), `roots` returns every root of a non-zero polynomial, and `one` is the unit. The
statistical terms are: `D / p` for the event that the forgery polynomial is non-zero while its
substitution `v ↦ a_v + b_v χ` vanishes (Schwartz–Zippel on its top-degree part at the hidden
`b`), `3 / p` for `G_w`, `G_{w'}` or `G_{x0}` being the identity, and `q_m (q_m - 1) / (2 p)` for
two MAC answers with the same `t`. The proof (rows U3, U4) rests on the algebraic lemma: if the
verification equation of the forgery holds as a polynomial identity in
`w, w', x0, x1, y_1, …, y_n, u_1, …, u_{q_m}`, the `t_j` are pairwise distinct,
`t* ≠ log_{G_{x0}} G_{x1}` and `G_w, G_{w'}, G_{x0} ≠ 1`, then the forgery equals a MAC answer
`(M_j, (t_j, U_j, V_j))`. The degree `D = q_m + 2` comes from attributes that contain earlier
`V_k`: an attribute of nesting depth `ℓ` raises the degree of `V` to `ℓ + 2`.

## References

* G. Fuchsbauer, E. Kiltz, J. Loss, *The Algebraic Group Model and its Applications*,
  CRYPTO 2018. <https://eprint.iacr.org/2017/620>
* M. Chase, T. Perrin, G. Zaverucha, *The Signal Private Group System and Anonymous
  Credentials Supporting Efficient Verifiable Encryption*, CCS 2020, §3.1, Theorem 14.
  <https://eprint.iacr.org/2019/1416>
* M. Orrù, *Revisiting Keyed-Verification Anonymous Credentials*, 2024, Theorem 5.1,
  Lemmas 5.4, 5.5, Claims 5.6, 5.7. <https://eprint.iacr.org/2024/1552>
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KVAC.MacNHelpAGM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.OT
open AlgMac AlgMac.MacN
open scoped ENNReal

variable (G : Type) [CGR : CyclicGroupRing G] [DecidableEq G] [DecidableEq CGR.Exp]

/-! ## Representations and symbolic queries -/

/-- A representation: exponents over the list of received group elements. -/
abbrev Rep := List CGR.Exp

/-- The element `Π_e b_e^{c_e}` of the representation `c` over the basis `b` (entries beyond
the shorter list are dropped). -/
noncomputable def evalRep (b : List G) (c : Rep G) : G :=
  gprod (List.zipWith CyclicGroup.elemPow b c)

/-- An attribute vector given by representations. -/
abbrev SymMsg (n : ℕ) := Fin n → Rep G

/-- A tag `(t, U, V)` with `U` and `V` given by representations. -/
abbrev SymTag := CGR.Exp × Rep G × Rep G

/-- Queries of an algebraic adversary: MAC, verification and helper queries. -/
abbrev SymQ (n : ℕ) :=
  SymMsg G n ⊕ (SymMsg G n × SymTag G) ⊕ (Rep G × Rep G × SymMsg G n × Rep G)

/-- The forgery of an algebraic adversary. -/
abbrev SymOut (n : ℕ) := SymMsg G n × SymTag G

/-- Answers of the suf-cmva-Help oracle of `macN`: a tag, a verification bit, a helper bit. -/
abbrev Ans := (CGR.Exp × G × G) ⊕ Bool ⊕ Bool

variable {G}

/-- The attribute vector of a symbolic attribute vector. -/
noncomputable def evalMsg {n : ℕ} (b : List G) (M : SymMsg G n) : Fin n → G :=
  fun i => evalRep G b (M i)

/-- The tag of a symbolic tag. -/
noncomputable def evalTag (b : List G) (σ : SymTag G) : CGR.Exp × G × G :=
  (σ.1, evalRep G b σ.2.1, evalRep G b σ.2.2)

/-- The query of `AlgMac.helpOracle (macN G n)` denoted by a symbolic query. -/
noncomputable def evalQ {n : ℕ} (b : List G) : SymQ G n → (macN G n).HelpQry
  | .inl M => .inl (evalMsg b M)
  | .inr (.inl q) => .inr (.inl (evalMsg b q.1, evalTag b q.2))
  | .inr (.inr q) =>
      .inr (.inr (evalRep G b q.1, evalRep G b q.2.1, evalMsg b q.2.2.1, evalRep G b q.2.2.2))

/-- The basis after an answer: a MAC answer `(t, U, V)` appends `U` and `V`. -/
def extend (b : List G) : Ans G → List G
  | .inl σ => b ++ [σ.2.1, σ.2.2]
  | .inr _ => b

/-- The elements received at the start: the generator, the parameters and the issuer
parameters `(C_W, I)`. -/
def basis0 {n : ℕ} (p : MacN.Par G n) (pk : G × G) : List G :=
  [CGR.gen, gw p, gw' p, gx0 p, gx1 p, gV p] ++ List.ofFn (gy p) ++ List.ofFn (gm p) ++
    [pk.1, pk.2]

/-- The adversary of the suf-cmva-Help game that evaluates the representations of a symbolic
adversary over the basis `b`, extended by the MAC answers. -/
noncomputable def toAdv {n : ℕ} :
    List G → OracleAdv (SymQ G n) (Ans G) (SymOut G n) →
      OracleAdv (macN G n).HelpQry (macN G n).HelpAns ((macN G n).Msg × (macN G n).Tag)
  | b, .ret o => .ret (evalMsg b o.1, evalTag b o.2)
  | b, .rand p k => .rand p fun x => toAdv b (k x)
  | b, .query d k => .query (evalQ b d) fun a => toAdv (extend b a) (k a)

variable (G)

/-- **Algebraic adversary against suf-cmva-Help of `MAC_n`.** On the parameters and the issuer
parameters, an oracle adversary whose queries and forgery give every group element by its
representation over the received elements. -/
abbrev AlgAdv (n : ℕ) := MacN.Par G n → G × G → OracleAdv (SymQ G n) (Ans G) (SymOut G n)

variable {G}

/-- The adversary of `AlgMac.sufCmvaHelpGame (macN G n)` denoted by an algebraic adversary. -/
noncomputable def AlgAdv.toAdv {n : ℕ} (A : AlgAdv G n) :
    MacN.Par G n → G × G →
      OracleAdv (macN G n).HelpQry (macN G n).HelpAns ((macN G n).Msg × (macN G n).Tag) :=
  fun p pk => MacNHelpAGM.toAdv (basis0 p pk) (A p pk)

/-- **suf-cmva-Help advantage of an algebraic adversary against `MAC_n`.** -/
noncomputable def sufCmvaHelpAGM_Advantage {n : ℕ} (A : AlgAdv G n) : ℝ≥0∞ :=
  (macN G n).SUFCMVAHelp_Advantage A.toAdv

/-- The cost of a query for the MAC-query bound: one for a MAC query, zero otherwise. -/
def macCost {n : ℕ} : SymQ G n → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-! ## The reduction to DL -/

/-- **The reduction `B_z` to DL.** On the challenge `X`, set `G_{x0} = g^{γ0}` for a uniform
`γ0` and `G_{x1} = X`, sample the other parameters and the key, run `A` against the helper
oracle of `macN` and output `γ0 · t*`, which is `log_g X` when `t* = log_{G_{x0}} G_{x1}`. -/
noncomputable def reductionZ {n : ℕ}
    (A : MacN.Par G n → G × G →
      OracleAdv (macN G n).HelpQry (macN G n).HelpAns ((macN G n).Msg × (macN G n).Tag))
    (X : G) : PMF CGR.Exp :=
  (PMF.uniformFintype (MacN.Par G n)).bind fun p =>
    (PMF.uniformFintype CGR.Exp).bind fun γ0 =>
      (PMF.uniformFintype (MacN.Key G n)).bind fun k =>
        let p' : MacN.Par G n :=
          (gw p, gw' p, CyclicGroup.elemPow CGR.gen γ0, X, gV p, gy p, gm p)
        (OracleAdv.run ((macN G n).helpOracle p' k) (A p' (iparams p' k)) []).map
          fun y => CGR.expMul γ0 (y.1.2 : CGR.Exp × G × G).1

/-! ## Polynomials in the challenge exponent -/

variable (G) in
/-- A polynomial in `χ` over the exponent ring, as its list of coefficients. -/
abbrev Poly := List CGR.Exp

/-- Sum of polynomials. -/
def padd : Poly G → Poly G → Poly G
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => CGR.expAdd a b :: padd p q

/-- Scalar multiple of a polynomial. -/
def pscale (c : CGR.Exp) (p : Poly G) : Poly G := p.map (CGR.expMul c)

/-- Negation of a polynomial. -/
def pneg (p : Poly G) : Poly G := p.map CGR.expNeg

/-- Product of polynomials. -/
def pmul : Poly G → Poly G → Poly G
  | [], _ => []
  | a :: p, q => padd (pscale a q) (CGR.expZero :: pmul p q)

/-- Sum of a list of polynomials. -/
def psum (l : List (Poly G)) : Poly G := l.foldr padd []

/-- The polynomial of a representation, from the polynomials of the basis. -/
def polyRep (P : List (Poly G)) (c : Rep G) : Poly G :=
  psum (List.zipWith pscale c P)

/-- The group element `Π_e ch_e^{c_e}` of a polynomial `c` at the challenge
`ch = (g, g^χ, …, g^{χ^D})`, that is `g^{c(χ)}` when `c` has degree at most `D`. -/
noncomputable def elemOf (ch : List G) (c : Poly G) : G :=
  gprod (List.zipWith CyclicGroup.elemPow ch c)

/-- The polynomials of the secret key `(w, w', x0, x1, (y_i))`. -/
structure KeyPolys (G : Type) [CyclicGroupRing G] (n : ℕ) where
  /-- `w`. -/
  w : Poly G
  /-- `w'`. -/
  w' : Poly G
  /-- `x0`. -/
  x0 : Poly G
  /-- `x1`. -/
  x1 : Poly G
  /-- `y_i`. -/
  y : Fin n → Poly G

/-- The key polynomials `v = a_v + b_v χ`. -/
def keyPolys {n : ℕ} (a b : MacN.Key G n) : KeyPolys G n where
  w := [w a, w b]
  w' := [w' a, w' b]
  x0 := [x0 a, x0 b]
  x1 := [x1 a, x1 b]
  y i := [y a i, y b i]

/-- The polynomial of `W A0^{x0} A1^{x1} Π A_i^{y_i}` from the polynomials of `A0`, `A1`, `A`,
with `γ_w = log_g G_w`: the right-hand side of the MAC, verification and helper equations. -/
def macPoly {n : ℕ} (γw : CGR.Exp) (kp : KeyPolys G n) (pA0 pA1 : Poly G)
    (pA : Fin n → Poly G) : Poly G :=
  padd (padd (padd (pscale γw kp.w) (pmul kp.x0 pA0)) (pmul kp.x1 pA1))
    (psum (List.ofFn fun i => pmul (kp.y i) (pA i)))

variable (G) in
/-- The exponents `γ = log_g` of the parameters, in the layout of `MacN.Par`. -/
abbrev ParExp (n : ℕ) :=
  CGR.Exp × CGR.Exp × CGR.Exp × CGR.Exp × CGR.Exp × (Fin n → CGR.Exp) × (Fin n → CGR.Exp)

/-- The parameters `g^γ` of the exponents `γ`. -/
noncomputable def parOf {n : ℕ} (γ : ParExp G n) : MacN.Par G n :=
  (CyclicGroup.elemPow CGR.gen γ.1, CyclicGroup.elemPow CGR.gen γ.2.1,
    CyclicGroup.elemPow CGR.gen γ.2.2.1, CyclicGroup.elemPow CGR.gen γ.2.2.2.1,
    CyclicGroup.elemPow CGR.gen γ.2.2.2.2.1,
    fun i => CyclicGroup.elemPow CGR.gen (γ.2.2.2.2.2.1 i),
    fun i => CyclicGroup.elemPow CGR.gen (γ.2.2.2.2.2.2 i))

/-- The polynomials of the starting basis `basis0`: the generator, the parameters,
`C_W = G_w^w G_{w'}^{w'}` and `I = G_V / (G_{x0}^{x0} G_{x1}^{x1} Π G_{y_i}^{y_i})`. -/
def basisPolys0 {n : ℕ} (one : CGR.Exp) (γ : ParExp G n) (kp : KeyPolys G n) :
    List (Poly G) :=
  [[one], [γ.1], [γ.2.1], [γ.2.2.1], [γ.2.2.2.1], [γ.2.2.2.2.1]] ++
    List.ofFn (fun i => [γ.2.2.2.2.2.1 i]) ++ List.ofFn (fun i => [γ.2.2.2.2.2.2 i]) ++
    [padd (pscale γ.1 kp.w) (pscale γ.2.1 kp.w'),
      padd [γ.2.2.2.2.1] (pneg (padd (padd (pscale γ.2.2.1 kp.x0) (pscale γ.2.2.2.1 kp.x1))
        (psum (List.ofFn fun i => pscale (γ.2.2.2.2.2.1 i) (kp.y i)))))]

/-- Whether the polynomial `c` vanishes at `χ`, tested on the challenge. -/
noncomputable def vanishes (ch : List G) (c : Poly G) : Bool :=
  decide (elemOf ch c = CGR.one)

/-- **The oracle of `reductionAlg`.** The state is the list of polynomials of the received
elements. A MAC query samples `t` and `u = a_u + b_u χ` and answers
`(t, g^{u(χ)}, g^{V(χ)})` with `V = macPoly γ_w kp u (t u) M`; verification and helper
queries answer whether the polynomial of their equation vanishes at `χ`. -/
noncomputable def simO {n : ℕ} (ch : List G) (γw : CGR.Exp) (kp : KeyPolys G n)
    (P : List (Poly G)) : SymQ G n → PMF (Ans G × List (Poly G))
  | .inl M =>
      (PMF.uniformFintype (CGR.Exp × CGR.Exp × CGR.Exp)).map fun r =>
        let pU : Poly G := [r.2.1, r.2.2]
        let pV := macPoly γw kp pU (pscale r.1 pU) fun i => polyRep P (M i)
        (.inl (r.1, elemOf ch pU, elemOf ch pV), P ++ [pU, pV])
  | .inr (.inl q) =>
      let pU := polyRep P q.2.2.1
      PMF.pure (.inr (.inl (vanishes ch (padd (polyRep P q.2.2.2)
        (pneg (macPoly γw kp pU (pscale q.2.1 pU) fun i => polyRep P (q.1 i)))))), P)
  | .inr (.inr q) =>
      PMF.pure (.inr (.inr (vanishes ch (padd (polyRep P q.2.2.2)
        (pneg (macPoly γw kp (polyRep P q.1) (polyRep P q.2.1)
          fun i => polyRep P (q.2.2.1 i)))))), P)

/-- The polynomial `ψ*` of the verification equation of a forgery. -/
def forgeryPoly {n : ℕ} (γw : CGR.Exp) (kp : KeyPolys G n) (P : List (Poly G))
    (o : SymOut G n) : Poly G :=
  let pU := polyRep P o.2.2.1
  padd (polyRep P o.2.2.2) (pneg (macPoly γw kp pU (pscale o.2.1 pU) fun i => polyRep P (o.1 i)))

/-- **The reduction `B_alg` to `D`-DL.** On the challenge `ch = (g, g^χ, …, g^{χ^D})`, sample
the parameter exponents `γ` and the key coefficients `a, b`, run the algebraic adversary on
`(g^γ, (g^{C_W(χ)}, g^{I(χ)}))` against `simO`, and return the root `r` of the forgery
polynomial `ψ*` with `g^r = g^χ` (the exponent `0` when `roots ψ*` holds none). -/
noncomputable def reductionAlg {n : ℕ} (one : CGR.Exp) (roots : Poly G → List CGR.Exp)
    (A : AlgAdv G n) (ch : List G) : PMF CGR.Exp :=
  (PMF.uniformFintype (ParExp G n)).bind fun γ =>
    (PMF.uniformFintype (MacN.Key G n × MacN.Key G n)).bind fun ab =>
      let kp := keyPolys ab.1 ab.2
      let P0 := basisPolys0 one γ kp
      let pk : G × G := (elemOf ch (P0.getD (6 + 2 * n) []), elemOf ch (P0.getD (7 + 2 * n) []))
      (OracleAdv.run (simO ch γ.1 kp) (A (parOf γ) pk) P0).map fun y =>
        ((roots (forgeryPoly γ.1 kp y.2 y.1)).find? fun r =>
          decide (CyclicGroup.elemPow CGR.gen r = ch.getD 1 CGR.one)).getD CGR.expZero

end CatCrypt.Crypto.KVAC.MacNHelpAGM
