/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KVAC.MacNHelpAGMProof
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# `MAC_n` in the algebraic group model: the security theorem

The third part of the security proof of `MAC_n` with the helper oracle for algebraic
adversaries (`CatCrypt.Crypto.KVAC.MacNHelpAGM`), with the target theorem
`macN_sufCmvaHelpAGM_le`: for a generator `g ≠ 1`, an algebraic adversary `A` with at most
`q_m` MAC queries and a root finder `RF`,

`Adv ≤ Adv^dl(reductionZ A.toAdv) + Adv^{(q_m+2)-dl}(reductionAlg expOne RF.roots A)`
`  + (q_m + 5) / p + q_m (q_m - 1) / (2 p)`.

## The formal MAC log

`simF` is the oracle `simO` of `reductionAlg` whose state is the list of MAC queries with their
coins: the representations of the attributes, `t` and the coefficients `(a_u, b_u)` of
`u = a_u + b_u χ` (`FEntry`). The polynomials of the received elements (`polysOf`) and the MAC
log of `simOL` (`stateOf`) are functions of it, and `simO`, `simOL` are images of `simF`
(`run_simF_stateOf`, `run_simF_polysOf`).

## Evaluation

With the formal variables of `Formal` (the key and the `u_k`), the received polynomials are the
polynomials `Formal.basis` of the logged representations at the substitution
`v ↦ a_v + b_v X` (`map_peval_polysOf`): at every point `x`, the list polynomial evaluates to
the formal polynomial at `v ↦ a_v + b_v x`. The forgery polynomial `ψ*` evaluates to the formal
forgery equation `forgeryForm` (`peval_forgeryPoly`).

## The experiment

`experiment` samples `χ`, `γ` and the key coefficients `(a, b)` and runs `simF`. The game is the
experiment at the parameters `g^γ` and the key `kp(χ)` (`game_eq_experiment`, from
`run_helpOracle_eq_simOL` and the setup coupling `uniform_parKey_coupling`). A winning outcome
with `t* ≠ log_{G_{x0}} G_{x1}` lies in one of four events (`win_cases`, from the algebraic lemma
`Formal.forgery_poly_identity_not_fresh`): `reductionAlg` finds `χ` (`kdlEvent_le`), a parameter
exponent is `0` (`badPar_le`), two MAC answers share `t` (`tColl_le`), or the Schwartz–Zippel
event (`forgeryPoly_ne_zero_prob`).

## The Schwartz–Zippel step

With `a = v - b χ`, the answers of `simF` depend on the view `(v, t, v_u)` only
(`simF_inr_attachL`, `simF_inl_attachL`), so the coefficients `b`, sampled one per MAC query,
are uniform given the view. `jDist_sz_le` averages over them by induction on the adversary, and
at the end the point `v + b` of the forgery equation is uniform (`sz_shift_le`, from Mathlib's
`MvPolynomial.schwartz_zippel_totalDegree` via `uniform_eval_eq_zero_le`); the equation has
total degree at most `q_m + 2` (`totalDegree_forgeryForm_le`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KVAC.MacNHelpAGM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions.KDL
open CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.OT AlgMac AlgMac.MacN
open scoped ENNReal

variable {G : Type} [CGR : CyclicGroupRing G]

attribute [local instance] expCommRing

variable {n : ℕ}

/-! ## The formal MAC log -/

variable (G) in
/-- An entry of the formal MAC log: the representations of the attributes, `t`, and the
coefficients `(a_u, b_u)` of the exponent `u = a_u + b_u χ` of `U`. -/
abbrev FEntry (n : ℕ) := SymMsg G n × CGR.Exp × CGR.Exp × CGR.Exp

/-- The polynomial `[a_u, b_u]` of `U` of a log entry. -/
def uPoly (e : FEntry G n) : Poly G := [e.2.2.1, e.2.2.2]

/-- The polynomial of `V` of a log entry over the polynomials `P` received before it. -/
def vPolyL (γw : CGR.Exp) (kp : KeyPolys G n) (P : List (Poly G)) (e : FEntry G n) : Poly G :=
  macPoly γw kp (uPoly e) (pscale e.2.1 (uPoly e)) fun i => polyRep P (e.1 i)

/-- One MAC answer in the state of `simOL`: append `U` and `V`, log the symbolic entry. -/
def stepS (γw : CGR.Exp) (kp : KeyPolys G n) (s : List (Poly G) × List (SymEntry G n))
    (e : FEntry G n) : List (Poly G) × List (SymEntry G n) :=
  (s.1 ++ [uPoly e, vPolyL γw kp s.1 e],
    ((fun i => polyRep s.1 (e.1 i)), e.2.1, uPoly e, vPolyL γw kp s.1 e) :: s.2)

/-- The state of `simOL` after the MAC queries of the formal log `F`. -/
def stateOf (P0 : List (Poly G)) (γw : CGR.Exp) (kp : KeyPolys G n) (F : List (FEntry G n)) :
    List (Poly G) × List (SymEntry G n) :=
  F.foldl (stepS γw kp) (P0, [])

/-- The state of `simO` after the MAC queries of the formal log `F`. -/
def polysOf (P0 : List (Poly G)) (γw : CGR.Exp) (kp : KeyPolys G n) (F : List (FEntry G n)) :
    List (Poly G) :=
  (stateOf P0 γw kp F).1

/-- Unfolding lemma of `stateOf` at a log extended by one entry. -/
theorem stateOf_append (P0 : List (Poly G)) (γw : CGR.Exp) (kp : KeyPolys G n)
    (F : List (FEntry G n)) (e : FEntry G n) :
    stateOf P0 γw kp (F ++ [e]) = stepS γw kp (stateOf P0 γw kp F) e := by
  simp [stateOf, List.foldl_append]

variable [DecidableEq G]

/-- **The oracle `simO` with the formal MAC log.** A MAC query samples `(t, a_u, b_u)`, answers
as `simO` and logs the representations of the attributes with the coins; the other queries
are answered by `simO` over the polynomials of the log. -/
noncomputable def simF (ch : List G) (γw : CGR.Exp) (kp : KeyPolys G n) (P0 : List (Poly G))
    (F : List (FEntry G n)) : SymQ G n → PMF (Ans G × List (FEntry G n))
  | .inl M =>
      (PMF.uniformFintype (CGR.Exp × CGR.Exp × CGR.Exp)).map fun r =>
        (.inl (r.1, elemOf ch (uPoly (M, r)), elemOf ch (vPolyL γw kp (polysOf P0 γw kp F) (M, r))),
          F ++ [(M, r)])
  | .inr q => (simO ch γw kp (polysOf P0 γw kp F) (.inr q)).map fun x => (x.1, F)

/-- `simOL` is the image of `simF` under `stateOf`. -/
theorem simF_map_stateOf (ch : List G) (γw : CGR.Exp) (kp : KeyPolys G n) (P0 : List (Poly G))
    (F : List (FEntry G n)) (d : SymQ G n) :
    (simF ch γw kp P0 F d).map (Prod.map id (stateOf P0 γw kp)) =
      simOL ch γw kp (stateOf P0 γw kp F) d := by
  rcases d with M | q | q
  · simp only [simF, simOL, PMF.map_comp]
    congr 1
    funext r
    simp [stateOf_append, stepS, polysOf, uPoly, vPolyL]
  · simp [simF, simOL, simO, polysOf, PMF.pure_map]
  · simp [simF, simOL, simO, polysOf, PMF.pure_map]

/-- **`simOL` from `simF`.** The run against `simOL` is the run against `simF` with the state
mapped by `stateOf`. -/
theorem run_simF_stateOf {α : Type} (ch : List G) (γw : CGR.Exp) (kp : KeyPolys G n)
    (P0 : List (Poly G)) (A : OracleAdv (SymQ G n) (Ans G) α) (F : List (FEntry G n)) :
    (OracleAdv.run (simF ch γw kp P0) A F).map (Prod.map id (stateOf P0 γw kp)) =
      OracleAdv.run (simOL ch γw kp) A (stateOf P0 γw kp F) :=
  OracleAdv.run_map_state _ _ _ (simF_map_stateOf ch γw kp P0) A F

/-- **`simO` from `simF`.** The run against `simO` is the run against `simF` with the state
mapped by `polysOf`. -/
theorem run_simF_polysOf {α : Type} (ch : List G) (γw : CGR.Exp) (kp : KeyPolys G n)
    (P0 : List (Poly G)) (A : OracleAdv (SymQ G n) (Ans G) α) (F : List (FEntry G n)) :
    (OracleAdv.run (simF ch γw kp P0) A F).map (Prod.map id (polysOf P0 γw kp)) =
      OracleAdv.run (simO ch γw kp) A (polysOf P0 γw kp F) := by
  have h := congrArg (PMF.map (Prod.map id Prod.fst)) (run_simF_stateOf ch γw kp P0 A F)
  rw [PMF.map_comp] at h
  refine h.trans ?_
  exact OracleAdv.run_map_state _ _ Prod.fst (fun s d => simOL_map_fst ch γw kp s d) A _

/-! ## Evaluation of the received polynomials -/

/-- The logarithms of the parameters in the layout of `Formal.ParLog`. -/
def parLog (γ : ParExp G n) : Formal.ParLog CGR.Exp n :=
  ⟨γ.1, γ.2.1, γ.2.2.1, γ.2.2.2.1, γ.2.2.2.2.1, γ.2.2.2.2.2.1, γ.2.2.2.2.2.2⟩

/-- The tag values `t_k` of a formal log (`0` beyond its end). -/
noncomputable def tOf (F : List (FEntry G n)) (k : ℕ) : CGR.Exp := (F[k]?.map fun e => e.2.1).getD 0

/-- The attribute representations `M_k` of a formal log (empty beyond its end). -/
def MOf (F : List (FEntry G n)) (k : ℕ) : SymMsg G n := (F[k]?.map fun e => e.1).getD fun _ => []

/-- The point `v ↦ a_v + b_v x` of the formal variables: the key coefficients `a, b` and the
coefficients `(a_u, b_u)` of the log (`0` beyond its end). -/
noncomputable def valsAt (x : CGR.Exp) (a b : MacN.Key G n) (F : List (FEntry G n)) :
    Formal.Var n → CGR.Exp
  | .w => a.1 + x * b.1
  | .w' => a.2.1 + x * b.2.1
  | .x0 => a.2.2.1 + x * b.2.2.1
  | .x1 => a.2.2.2.1 + x * b.2.2.2.1
  | .y i => a.2.2.2.2 i + x * b.2.2.2.2 i
  | .u k => (F[k]?.map fun e => e.2.2.1 + x * e.2.2.2).getD 0

omit [DecidableEq G] in
/-- Evaluation of the polynomial of a representation. -/
theorem eval_rep (f : Formal.Var n → CGR.Exp) :
    ∀ (B : List (MvPolynomial (Formal.Var n) CGR.Exp)) (c : Rep G),
      MvPolynomial.eval f (Formal.rep B c) = expDot (B.map (MvPolynomial.eval f)) c
  | [], c => by cases c <;> simp [Formal.rep, expDot]
  | _ :: _, [] => by simp [Formal.rep, expDot]
  | p :: B, a :: c => by
    have ih := eval_rep f B c
    simp only [Formal.rep] at ih ⊢
    simp only [List.zipWith_cons_cons, List.sum_cons, map_add, map_mul, MvPolynomial.eval_C,
      ih, List.map_cons, expDot]
    ring

omit [DecidableEq G] in
/-- Evaluation of the MAC polynomial at the key polynomials `a + b X`. -/
theorem peval_macPoly (x γw : CGR.Exp) (a b : MacN.Key G n) (pA0 pA1 : Poly G)
    (pA : Fin n → Poly G) :
    peval (macPoly γw (keyPolys a b) pA0 pA1 pA) x =
      γw * (a.1 + x * b.1) + (a.2.2.1 + x * b.2.2.1) * peval pA0 x +
        (a.2.2.2.1 + x * b.2.2.2.1) * peval pA1 x +
          ∑ i, (a.2.2.2.2 i + x * b.2.2.2.2 i) * peval (pA i) x := by
  simp only [macPoly, peval_padd, peval_pscale, peval_pmul, peval_psum, List.map_ofFn,
    List.sum_ofFn, Function.comp_def, keyPolys, peval_cons, peval_nil]
  ring_nf

omit [DecidableEq G] in
/-- **Evaluation of the received polynomials.** Over the start polynomials of `reductionAlg`,
the polynomials of the formal log `F` evaluate at every point `x` to the formal basis of the
logged representations at `v ↦ a_v + b_v x`, for every extension `F'` of the log. -/
theorem map_peval_polysOf (x : CGR.Exp) (γ : ParExp G n) (a b : MacN.Key G n) :
    ∀ (F F' : List (FEntry G n)),
      (polysOf (basisPolys0 expOne γ (keyPolys a b)) γ.1 (keyPolys a b) F).map (peval · x) =
        (Formal.basis (parLog γ) (tOf (F ++ F')) (MOf (F ++ F')) F.length).map
          (MvPolynomial.eval (valsAt x a b (F ++ F'))) := by
  intro F
  induction F using List.reverseRecOn with
  | nil =>
    intro F'
    simp only [polysOf, stateOf, List.foldl_nil, List.length_nil, Formal.basis, Formal.basis0,
      basisPolys0, List.map_append, List.map_cons, List.map_nil, List.map_ofFn]
    simp only [Function.comp_def, peval_cons, peval_nil, MvPolynomial.eval_C, map_one, expOne_eq,
      parLog, Formal.cwPoly, Formal.iPoly, MvPolynomial.eval_X, valsAt, keyPolys, peval_padd,
      peval_pscale, peval_pneg, peval_psum, List.map_ofFn, List.sum_ofFn, map_sub, map_sum,
      map_add, map_mul, mul_zero, add_zero, w, w', x0, x1, y]
    congr 3
    ring
  | append_singleton F e ih =>
    intro F'
    have hF : F ++ [e] ++ F' = F ++ e :: F' := by simp
    have ih' := ih (e :: F')
    have ht : tOf (F ++ e :: F') F.length = e.2.1 := by simp [tOf]
    have hM : MOf (F ++ e :: F') F.length = e.1 := by simp [MOf]
    have hrep : ∀ c : Rep G, peval (polyRep (polysOf (basisPolys0 expOne γ (keyPolys a b)) γ.1
        (keyPolys a b) F) c) x = MvPolynomial.eval (valsAt x a b (F ++ e :: F'))
          (Formal.rep (Formal.basis (parLog γ) (tOf (F ++ e :: F')) (MOf (F ++ e :: F'))
            F.length) c) := fun c => by
      rw [peval_polyRep, ih', eval_rep]
    rw [hF, List.length_append, List.length_singleton, Formal.basis_succ, List.map_append, ← ih',
      polysOf, stateOf_append, stepS, List.map_append, ← polysOf]
    congr 1
    simp only [List.map_cons, List.map_nil, MvPolynomial.eval_X, vPolyL, peval_macPoly,
      Formal.vPoly, Formal.mPoly, Formal.lin, map_add, map_mul, map_sum, MvPolynomial.eval_C, ht,
      hM, hrep, uPoly, peval_cons, peval_nil, peval_pscale, valsAt, parLog,
      List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some, List.cons.injEq, and_true]
    constructor <;> ring

omit [DecidableEq G] in
/-- The polynomial of a representation over the received polynomials evaluates to the formal
polynomial of the representation. -/
theorem peval_polyRep_polysOf (x : CGR.Exp) (γ : ParExp G n) (a b : MacN.Key G n)
    (F F' : List (FEntry G n)) (c : Rep G) :
    peval (polyRep (polysOf (basisPolys0 expOne γ (keyPolys a b)) γ.1 (keyPolys a b) F) c) x =
      MvPolynomial.eval (valsAt x a b (F ++ F'))
        (Formal.rep (Formal.basis (parLog γ) (tOf (F ++ F')) (MOf (F ++ F')) F.length) c) := by
  rw [peval_polyRep, map_peval_polysOf x γ a b F F', eval_rep]

omit [DecidableEq G] in
/-- The polynomial of `U` of a log entry evaluates to `a_u + b_u x`. -/
theorem peval_uPoly (x : CGR.Exp) (e : FEntry G n) : peval (uPoly e) x = e.2.2.1 + x * e.2.2.2 := by
  simp [uPoly]

omit [DecidableEq G] in
/-- The value of `u_j` at a point is the value of the polynomial of `U_j`. -/
theorem valsAt_u (x : CGR.Exp) (a b : MacN.Key G n) (F : List (FEntry G n)) (j : ℕ)
    (hj : j < F.length) : valsAt x a b F (.u j) = peval (uPoly F[j]) x := by
  simp [valsAt, peval_uPoly, List.getElem?_eq_getElem hj]

omit [DecidableEq G] in
/-- The polynomial of `V` of the log entry after `F` evaluates to the formal `V_{|F|}`. -/
theorem peval_vPolyL (x : CGR.Exp) (γ : ParExp G n) (a b : MacN.Key G n)
    (F : List (FEntry G n)) (e : FEntry G n) (F' : List (FEntry G n)) :
    peval (vPolyL γ.1 (keyPolys a b) (polysOf (basisPolys0 expOne γ (keyPolys a b)) γ.1
        (keyPolys a b) F) e) x =
      MvPolynomial.eval (valsAt x a b (F ++ e :: F'))
        (Formal.vPoly (parLog γ) (tOf (F ++ e :: F')) (MOf (F ++ e :: F')) F.length) := by
  have ht : tOf (F ++ e :: F') F.length = e.2.1 := by simp [tOf]
  have hM : MOf (F ++ e :: F') F.length = e.1 := by simp [MOf]
  simp only [vPolyL, peval_macPoly, Formal.vPoly, Formal.mPoly, Formal.lin, map_add, map_mul,
    map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X, ht, hM, peval_polyRep_polysOf x γ a b F
      (e :: F'), uPoly, peval_cons, peval_nil, peval_pscale, valsAt, parLog,
    List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero, Option.map_some,
    Option.getD_some]
  ring

/-- **The formal forgery equation** `V* - (γ_w w + U* (x0 + t* x1) + Σ y_i M*_i)` of a symbolic
forgery over the formal basis of the log `F`. -/
noncomputable def forgeryForm (γ : ParExp G n) (F : List (FEntry G n)) (o : SymOut G n) :
    MvPolynomial (Formal.Var n) CGR.Exp :=
  Formal.rep (Formal.basis (parLog γ) (tOf F) (MOf F) F.length) o.2.2.2 -
    (MvPolynomial.C γ.1 * MvPolynomial.X .w +
      Formal.rep (Formal.basis (parLog γ) (tOf F) (MOf F) F.length) o.2.2.1 * Formal.lin o.2.1 +
      ∑ i, MvPolynomial.X (.y i) * Formal.rep (Formal.basis (parLog γ) (tOf F) (MOf F) F.length)
        (o.1 i))

omit [DecidableEq G] in
/-- **The forgery polynomial.** `ψ*` evaluates at every point `x` to the formal forgery
equation at `v ↦ a_v + b_v x`. -/
theorem peval_forgeryPoly (x : CGR.Exp) (γ : ParExp G n) (a b : MacN.Key G n)
    (F : List (FEntry G n)) (o : SymOut G n) :
    peval (forgeryPoly γ.1 (keyPolys a b) (polysOf (basisPolys0 expOne γ (keyPolys a b)) γ.1
        (keyPolys a b) F) o) x = MvPolynomial.eval (valsAt x a b F) (forgeryForm γ F o) := by
  have h := peval_polyRep_polysOf x γ a b F []
  rw [List.append_nil] at h
  simp only [forgeryPoly, forgeryForm, peval_padd, peval_pneg, peval_macPoly, peval_pscale, h,
    map_sub, map_add, map_mul, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X, valsAt,
    Formal.lin]
  ring

omit [DecidableEq G] in
/-- Each MAC query of the formal log has its symbolic entry in the log of `simOL`. -/
theorem mem_stateOf (P0 : List (Poly G)) (γw : CGR.Exp) (kp : KeyPolys G n) :
    ∀ (F : List (FEntry G n)) (j : ℕ) (hj : j < F.length),
      ((fun i => polyRep (polysOf P0 γw kp (F.take j)) (F[j].1 i)), F[j].2.1, uPoly F[j],
        vPolyL γw kp (polysOf P0 γw kp (F.take j)) F[j]) ∈ (stateOf P0 γw kp F).2 := by
  intro F
  induction F using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton F e ih =>
    intro j hj
    rw [stateOf_append, stepS]
    rcases Nat.lt_or_ge j F.length with h | h
    · refine List.mem_cons_of_mem _ ?_
      have := ih j h
      simpa [List.take_append_of_le_length h.le, List.getElem_append_left h] using this
    · have hjF : j = F.length := by simp at hj; omega
      subst hjF
      simp [polysOf]

/-! ## The setup coupling -/

omit [DecidableEq G] in
/-- The key `kp(χ)` of the key polynomials `a + b X` is `a` shifted by the key `b χ`. -/
theorem keyAt_keyPolys (a b : MacN.Key G n) (χ : CGR.Exp) :
    keyAt (keyPolys a b) χ = a + keyAt (keyPolys 0 b) χ := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a
  simp only [keyAt, keyPolys, peval_cons, peval_nil, w, w', x0, x1, y, Prod.mk_add_mk,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_add, mul_zero, add_zero]
  rfl

omit [DecidableEq G] in
/-- For fixed `b` and `χ`, the key `kp(χ)` of uniform `a` is uniform. -/
theorem uniform_map_keyAt (b : MacN.Key G n) (χ : CGR.Exp) :
    (PMF.uniformFintype (MacN.Key G n)).map (fun a => keyAt (keyPolys a b) χ) =
      PMF.uniformFintype (MacN.Key G n) := by
  have h : (fun a => keyAt (keyPolys a b) χ) = Equiv.addRight (keyAt (keyPolys 0 b) χ) :=
    funext fun a => keyAt_keyPolys a b χ
  rw [h, PMF.uniformFintype_map_equiv]

omit [DecidableEq G] in
/-- For a generator `g ≠ 1`, the parameters `g^γ` of uniform exponents `γ` are uniform. -/
theorem uniform_map_parOf (hgen : CGR.gen ≠ CGR.one) :
    (PMF.uniformFintype (ParExp G n)).map parOf = PMF.uniformFintype (MacN.Par G n) := by
  let e : CGR.Exp ≃ G := Equiv.ofBijective _ (elemPow_gen_bijective hgen)
  let E : ParExp G n ≃ MacN.Par G n :=
    e.prodCongr (e.prodCongr (e.prodCongr (e.prodCongr (e.prodCongr
      ((Equiv.piCongrRight fun _ => e).prodCongr (Equiv.piCongrRight fun _ => e))))))
  have h : (parOf : ParExp G n → MacN.Par G n) = E := rfl
  rw [h, PMF.uniformFintype_map_equiv]

omit [DecidableEq G] in
/-- **The setup coupling.** Uniform parameters and a uniform key are the parameters `g^γ` and
the key `kp(χ)` of uniform `χ`, `γ` and key polynomials `a + b X`. -/
theorem uniform_parKey_coupling (hgen : CGR.gen ≠ CGR.one) {β : Type}
    (H : MacN.Par G n → MacN.Key G n → PMF β) :
    (PMF.uniformFintype (MacN.Par G n)).bind
        (fun p => (PMF.uniformFintype (MacN.Key G n)).bind (H p)) =
      (PMF.uniformFintype CGR.Exp).bind fun χ => (PMF.uniformFintype (ParExp G n)).bind fun γ =>
        (PMF.uniformFintype (MacN.Key G n × MacN.Key G n)).bind fun ab =>
          H (parOf γ) (keyAt (keyPolys ab.1 ab.2) χ) := by
  have hk : ∀ (χ : CGR.Exp) (p : MacN.Par G n),
      (PMF.uniformFintype (MacN.Key G n × MacN.Key G n)).bind
          (fun ab => H p (keyAt (keyPolys ab.1 ab.2) χ)) =
        (PMF.uniformFintype (MacN.Key G n)).bind (H p) := by
    intro χ p
    have h2 : ∀ b, (PMF.uniformFintype (MacN.Key G n)).bind
        (fun a => H p (keyAt (keyPolys a b) χ)) = (PMF.uniformFintype (MacN.Key G n)).bind (H p) :=
      fun b => by
        conv_rhs => rw [← uniform_map_keyAt b χ]
        rw [PMF.bind_map]
        rfl
    rw [PMF.uniform_prod_eq_bind, PMF.bind_bind]
    simp only [PMF.bind_map, Function.comp_def]
    rw [PMF.bind_comm]
    simp only [h2, PMF.bind_const]
  simp only [hk, PMF.bind_const]
  rw [← uniform_map_parOf hgen, PMF.bind_map]
  rfl

/-! ## The experiment of `reductionAlg` with the formal log -/

variable [DecidableEq CGR.Exp]

/-- The run of the algebraic adversary against `simF` at the challenge exponent `χ`, the
parameter exponents `γ` and the key polynomials `a + b X`, on the parameters `g^γ` and the
issuer parameters of the key `kp(χ)`. -/
noncomputable def runF (D : ℕ) (A : AlgAdv G n) (χ : CGR.Exp) (γ : ParExp G n)
    (ab : MacN.Key G n × MacN.Key G n) : PMF (SymOut G n × List (FEntry G n)) :=
  OracleAdv.run (simF (kDLChallenge G D χ) γ.1 (keyPolys ab.1 ab.2)
      (basisPolys0 expOne γ (keyPolys ab.1 ab.2)))
    (A (parOf γ) (iparams (parOf γ) (keyAt (keyPolys ab.1 ab.2) χ))) []

variable (G) in
/-- The outcomes of the experiment: `χ`, `γ`, the key coefficients `(a, b)`, the symbolic
forgery and the formal log. -/
abbrev Outcome (n : ℕ) :=
  CGR.Exp × ParExp G n × (MacN.Key G n × MacN.Key G n) × (SymOut G n × List (FEntry G n))

/-- **The experiment.** Uniform `χ`, `γ` and key coefficients, then the run `runF`. -/
noncomputable def experiment (D : ℕ) (A : AlgAdv G n) : PMF (Outcome G n) :=
  (PMF.uniformFintype CGR.Exp).bind fun χ => (PMF.uniformFintype (ParExp G n)).bind fun γ =>
    (PMF.uniformFintype (MacN.Key G n × MacN.Key G n)).bind fun ab =>
      (runF D A χ γ ab).map fun y => (χ, γ, ab, y)

/-- The forgery and the MAC log of the suf-cmva-Help game denoted by an outcome: the symbolic
forgery and the symbolic log evaluated at `χ`. -/
noncomputable def gameOut (ω : Outcome G n) :
    ((macN G n).Msg × (macN G n).Tag) × (macN G n).Log :=
  ((evalMsg ((stateOf (basisPolys0 expOne ω.2.1 (keyPolys ω.2.2.1.1 ω.2.2.1.2)) ω.2.1.1
        (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.2.2.2.2).1.map (evP ω.1)) ω.2.2.2.1.1,
      evalTag ((stateOf (basisPolys0 expOne ω.2.1 (keyPolys ω.2.2.1.1 ω.2.2.1.2)) ω.2.1.1
        (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.2.2.2.2).1.map (evP ω.1)) ω.2.2.2.1.2),
    (stateOf (basisPolys0 expOne ω.2.1 (keyPolys ω.2.2.1.1 ω.2.2.1.2)) ω.2.1.1
      (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.2.2.2.2).2.map (evEntry ω.1))

/-- **The game run from `runF`.** For a generator `g ≠ 1` and an adversary with at most `q_m`
MAC queries, the run of the evaluated adversary against the helper oracle of `macN` at the
parameters `g^γ` and the key `kp(χ)` is `runF` with the forgery and the log evaluated. -/
theorem run_toAdv_eq_runF (hgen : CGR.gen ≠ CGR.one) (qm : ℕ) (A : AlgAdv G n)
    (hA : ∀ p pk, (A p pk).IsQueryBoundBy macCost qm) (χ : CGR.Exp) (γ : ParExp G n)
    (ab : MacN.Key G n × MacN.Key G n) :
    OracleAdv.run ((macN G n).helpOracle (parOf γ) (keyAt (keyPolys ab.1 ab.2) χ))
        (A.toAdv (parOf γ) (iparams (parOf γ) (keyAt (keyPolys ab.1 ab.2) χ))) [] =
      (runF (qm + 2) A χ γ ab).map fun y => gameOut (χ, γ, ab, y) := by
  have h := run_helpOracle_eq_simOL hgen (qm + 2) χ γ (keyPolys ab.1 ab.2)
    (keyPolys_lin _ _) (A (parOf γ) (iparams (parOf γ) (keyAt (keyPolys ab.1 ab.2) χ))) qm 0
    (basisPolys0 expOne γ (keyPolys ab.1 ab.2)) [] (hA _ _)
    (fun p hp => basisPolys0_length expOne γ _ _ p hp) (by omega)
  refine Eq.trans ?_ (h.trans ?_)
  · rw [map_evP_basisPolys0]
    rfl
  · have h2 := run_simF_stateOf (kDLChallenge G (qm + 2) χ) γ.1 (keyPolys ab.1 ab.2)
      (basisPolys0 expOne γ (keyPolys ab.1 ab.2))
      (A (parOf γ) (iparams (parOf γ) (keyAt (keyPolys ab.1 ab.2) χ))) []
    exact (congrArg (PMF.map _) h2.symm).trans (PMF.map_comp _ _ _)

/-- **The game in the experiment.** For a generator `g ≠ 1` and an adversary with at most `q_m`
MAC queries, the probability of an event of the suf-cmva-Help game of `macN` is the
probability of the event at `g^γ`, `kp(χ)` and the evaluated forgery and log of the
experiment. -/
theorem game_eq_experiment (hgen : CGR.gen ≠ CGR.one) (qm : ℕ) (A : AlgAdv G n)
    (hA : ∀ p pk, (A p pk).IsQueryBoundBy macCost qm)
    (f : MacN.Par G n → MacN.Key G n → ((macN G n).Msg × (macN G n).Tag) × (macN G n).Log →
      Bool) :
    ((macN G n).setup.bind fun x =>
        (OracleAdv.run ((macN G n).helpOracle x.1 x.2) (A.toAdv x.1 (iparams x.1 x.2)) []).map
          (f x.1 x.2)) true =
      (experiment (qm + 2) A).toOuterMeasure
        {ω | f (parOf ω.2.1) (keyAt (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.1) (gameOut ω) = true} := by
  have hs : {ω : Outcome G n | f (parOf ω.2.1) (keyAt (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.1)
      (gameOut ω) = true} = (fun ω : Outcome G n => f (parOf ω.2.1)
        (keyAt (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.1) (gameOut ω)) ⁻¹' {true} := rfl
  rw [hs, ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
  congr 1
  rw [AlgMac.setup, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  refine (uniform_parKey_coupling hgen (fun p k =>
    (OracleAdv.run ((macN G n).helpOracle p k) (A.toAdv p (iparams p k)) []).map (f p k))).trans ?_
  simp only [experiment, PMF.map_bind, PMF.map_comp, run_toAdv_eq_runF hgen qm A hA]
  rfl

/-! ## The events of an outcome -/

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The logged entry `j` of `simOL`, evaluated at `χ`, is the formal MAC answer `j` at
`v ↦ a_v + b_v χ`. -/
theorem evEntry_entry (χ : CGR.Exp) (γ : ParExp G n) (a b : MacN.Key G n)
    (F : List (FEntry G n)) (j : ℕ) (hj : j < F.length) :
    evEntry χ ((fun i => polyRep (polysOf (basisPolys0 expOne γ (keyPolys a b)) γ.1
        (keyPolys a b) (F.take j)) (F[j].1 i)), F[j].2.1, uPoly F[j],
        vPolyL γ.1 (keyPolys a b) (polysOf (basisPolys0 expOne γ (keyPolys a b)) γ.1
          (keyPolys a b) (F.take j)) F[j]) =
      ((fun i => CyclicGroup.elemPow CGR.gen (MvPolynomial.eval (valsAt χ a b F)
          (Formal.mPoly (parLog γ) (tOf F) (MOf F) j i))), tOf F j,
        CyclicGroup.elemPow CGR.gen (valsAt χ a b F (.u j)),
        CyclicGroup.elemPow CGR.gen (MvPolynomial.eval (valsAt χ a b F)
          (Formal.vPoly (parLog γ) (tOf F) (MOf F) j))) := by
  have hF : F.take j ++ F[j] :: F.drop (j + 1) = F := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hl : (F.take j).length = j := by simp; omega
  have hM : MOf F j = F[j].1 := by simp [MOf, List.getElem?_eq_getElem hj]
  have ht : tOf F j = F[j].2.1 := by simp [tOf, List.getElem?_eq_getElem hj]
  have hrep := peval_polyRep_polysOf χ γ a b (F.take j) (F[j] :: F.drop (j + 1))
  have hv := peval_vPolyL χ γ a b (F.take j) F[j] (F.drop (j + 1))
  rw [hF, hl] at hrep hv
  simp only [evEntry, evP, hrep, hv, Formal.mPoly, hM, ht, valsAt_u χ a b F j hj]

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- A list polynomial without a nonzero coefficient evaluates to zero everywhere. -/
theorem peval_eq_zero_of_not_nonzero (p : Poly G) (hp : ¬ PolyNonzero p) (x : CGR.Exp) :
    peval p x = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have ha : a = 0 := by
      by_contra h
      exact hp ⟨a, List.mem_cons_self, h⟩
    have hp' : ¬ PolyNonzero p := fun ⟨c, hc, hc0⟩ => hp ⟨c, List.mem_cons_of_mem _ hc, hc0⟩
    rw [peval_cons, ih hp', ha, mul_zero, add_zero]

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- For a generator `g ≠ 1` the exponent ring is nontrivial. -/
theorem exp_nontrivial (hgen : CGR.gen ≠ CGR.one) : Nontrivial CGR.Exp := by
  refine ⟨⟨0, 1, fun h => hgen ?_⟩⟩
  rw [← elemPow_one' CGR.gen, ← h, elemPow_zero']

/-- The forgery polynomial `ψ*` of an outcome. -/
noncomputable def psiOf (ω : Outcome G n) : Poly G :=
  forgeryPoly ω.2.1.1 (keyPolys ω.2.2.1.1 ω.2.2.1.2)
    (polysOf (basisPolys0 expOne ω.2.1 (keyPolys ω.2.2.1.1 ω.2.2.1.2)) ω.2.1.1
      (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.2.2.2.2) ω.2.2.2.1

/-- The event of `reductionAlg`: the forgery polynomial is nonzero and has the root `χ`. -/
def KDLEvent (ω : Outcome G n) : Prop := PolyNonzero (psiOf ω) ∧ peval (psiOf ω) ω.1 = 0

/-- The event of a parameter exponent `γ_w`, `γ_{w'}` or `γ_0` equal to `0`. -/
def BadPar (ω : Outcome G n) : Prop := ω.2.1.1 = 0 ∨ ω.2.1.2.1 = 0 ∨ ω.2.1.2.2.1 = 0

/-- The event of two MAC answers with the same `t`. -/
def TColl (ω : Outcome G n) : Prop := ¬ (ω.2.2.2.2.map fun e => e.2.1).Nodup

/-- **The Schwartz–Zippel event.** The formal forgery equation is nonzero and vanishes at
`v ↦ a_v + b_v (χ + 1)`. -/
def SZEvent (ω : Outcome G n) : Prop :=
  forgeryForm ω.2.1 ω.2.2.2.2 ω.2.2.2.1 ≠ 0 ∧
    MvPolynomial.eval (valsAt (ω.1 + 1) ω.2.2.1.1 ω.2.2.1.2 ω.2.2.2.2)
      (forgeryForm ω.2.1 ω.2.2.2.2 ω.2.2.2.1) = 0

/-- **The events of a win.** For a generator `g ≠ 1`, a forgery of an outcome that verifies, is
fresh and has `t* ≠ log_{G_{x0}} G_{x1}` lies in one of the events: `reductionAlg` finds `χ`,
a bad parameter exponent, two equal `t`, or the Schwartz–Zippel event. The remaining case, a
forgery equation that vanishes as a polynomial, is excluded by the algebraic lemma
`Formal.forgery_poly_identity_not_fresh`. -/
theorem win_cases (hgen : CGR.gen ≠ CGR.one) (ω : Outcome G n)
    (hwin : ((macN G n).verify (parOf ω.2.1) (keyAt (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.1)
        (gameOut ω).1.1 (gameOut ω).1.2 &&
          (macN G n).strongFresh (gameOut ω).1 (gameOut ω).2) = true)
    (hz : ¬ CyclicGroup.elemPow (gx0 (parOf ω.2.1)) ω.2.2.2.1.2.1 = gx1 (parOf ω.2.1)) :
    KDLEvent ω ∨ BadPar ω ∨ TColl ω ∨ SZEvent ω := by
  obtain ⟨χ, γ, ⟨a, b⟩, o, F⟩ := ω
  have hinj := (elemPow_gen_bijective (G := G) hgen).1
  simp only [Bool.and_eq_true] at hwin
  obtain ⟨hver, hfresh⟩ := hwin
  simp only [macN, gameOut, evalTag, evalMsg_map_evP, evalRep_map_evP, decide_eq_true_eq]
    at hver
  rw [← evP_macPoly_macV] at hver
  have hψ : peval (psiOf (χ, γ, (a, b), o, F)) χ = 0 := by
    have := hinj hver
    simp only [psiOf, forgeryPoly, peval_padd, peval_pneg]
    exact add_neg_eq_zero.mpr this
  by_cases hnz : PolyNonzero (psiOf (χ, γ, (a, b), o, F))
  · exact Or.inl ⟨hnz, hψ⟩
  right
  have hφx : MvPolynomial.eval (valsAt (χ + 1) a b F) (forgeryForm γ F o) = 0 := by
    rw [← peval_forgeryPoly]
    exact peval_eq_zero_of_not_nonzero _ hnz _
  by_cases hφ : forgeryForm γ F o = 0
  swap
  · exact Or.inr (Or.inr ⟨hφ, hφx⟩)
  by_contra hcon
  simp only [BadPar, TColl, not_or, not_not] at hcon
  obtain ⟨⟨hγw, hγw', hγ0⟩, hnd, -⟩ := hcon
  have := exp_nontrivial hgen
  have := expIsDomain (G := G)
  have hz' : (parLog γ).g0 * o.2.1 ≠ (parLog γ).g1 := fun h => hz (by
    simp only [parOf, gx0, gx1, elemPow_elemPow]
    exact congrArg _ h)
  have ht : ∀ j < F.length, ∀ j' < F.length, tOf F j = tOf F j' → j = j' := by
    intro j hj j' hj' h
    simp only [tOf, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', Option.map_some,
      Option.getD_some] at h
    exact (hnd.getElem_inj_iff (i := j) (j := j') (hi := by simpa using hj)
      (hj := by simpa using hj')).mp (by simpa using h)
  obtain ⟨j, hj, hts, hU, hV, hM⟩ := Formal.forgery_poly_identity_not_fresh (hγw := hγw)
    (hγw' := hγw') (hγ0 := hγ0) hz' ht (sub_eq_zero.mp hφ)
  simp only [AlgMac.strongFresh, macN, decide_eq_true_eq] at hfresh
  apply hfresh
  have hmem := List.mem_map_of_mem (f := evEntry χ) (mem_stateOf (basisPolys0 expOne γ
    (keyPolys a b)) γ.1 (keyPolys a b) F j hj)
  rw [evEntry_entry χ γ a b F j hj] at hmem
  have hrep := peval_polyRep_polysOf χ γ a b F []
  rw [List.append_nil] at hrep
  simp only [polysOf] at hrep
  have heq : (gameOut (χ, γ, (a, b), o, F)).1 = ((fun i => CyclicGroup.elemPow CGR.gen
      (MvPolynomial.eval (valsAt χ a b F) (Formal.mPoly (parLog γ) (tOf F) (MOf F) j i))),
      tOf F j, CyclicGroup.elemPow CGR.gen (valsAt χ a b F (.u j)),
      CyclicGroup.elemPow CGR.gen (MvPolynomial.eval (valsAt χ a b F)
        (Formal.vPoly (parLog γ) (tOf F) (MOf F) j))) := by
    simp only [gameOut, evalTag, evalMsg_map_evP, evalRep_map_evP, evP, hrep, hU, hV, hM, hts,
      MvPolynomial.eval_X]
    rfl
  rw [heq]
  exact hmem

/-! ## The reduction to `D`-DL and the parameter event -/

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The issuer parameters given to the adversary by `reductionAlg` on the `D`-DL challenge are
the issuer parameters of the key `kp(χ)`. -/
theorem reductionAlg_pk (D : ℕ) (hD : 1 ≤ D) (χ : CGR.Exp) (γ : ParExp G n)
    (a b : MacN.Key G n) :
    ((elemOf (kDLChallenge G D χ) ((basisPolys0 expOne γ (keyPolys a b)).getD (6 + 2 * n) [])),
      elemOf (kDLChallenge G D χ) ((basisPolys0 expOne γ (keyPolys a b)).getD (7 + 2 * n) [])) =
      iparams (parOf γ) (keyAt (keyPolys a b) χ) := by
  have hlen : (basisPolys0 expOne γ (keyPolys a b)).length = 8 + 2 * n := by
    simp [basisPolys0]
    omega
  have hb := map_evP_basisPolys0 χ γ (keyPolys a b)
  have hi : ∀ i (hi : i < 8 + 2 * n), elemOf (kDLChallenge G D χ)
      ((basisPolys0 expOne γ (keyPolys a b)).getD i []) =
        (basis0 (parOf γ) (iparams (parOf γ) (keyAt (keyPolys a b) χ)))[i]'(by
          rw [← hb, List.length_map, hlen]; exact hi) := by
    intro i hi
    have hi' : i < (basisPolys0 expOne γ (keyPolys a b)).length := hlen ▸ hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some,
      elemOf_kDLChallenge D χ _ (by
        have := basisPolys0_length expOne γ a b _ (List.getElem_mem hi')
        omega)]
    simp only [← hb, List.getElem_map]
  rw [hi _ (by omega), hi _ (by omega)]
  simp only [basis0, List.cons_append, List.append_assoc, List.nil_append]
  grind

/-- **The `D`-DL event.** For a generator `g ≠ 1` and a root finder `RF`, the probability of the
event that the forgery polynomial is nonzero with the root `χ` is at most the `D`-DL advantage
of `reductionAlg`. -/
theorem kdlEvent_le (hgen : CGR.gen ≠ CGR.one) (qm : ℕ) (A : AlgAdv G n) (RF : RootFinder G) :
    (experiment (qm + 2) A).toOuterMeasure {ω | KDLEvent ω} ≤
      KDL_Advantage G (qm + 2) (reductionAlg expOne RF.roots A) := by
  classical
  rw [KDL_Advantage, KDL_Game, prTrue_liftPMF]
  have hs : {ω : Outcome G n | KDLEvent ω} = (fun ω => decide (KDLEvent ω)) ⁻¹' {true} := by
    ext ω
    simp
  rw [hs, ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
  simp only [experiment, PMF.map_bind, PMF.map_comp]
  refine pmf_bind_apply_mono _ _ _ _ fun χ => ?_
  simp only [reductionAlg, PMF.map_bind]
  refine pmf_bind_apply_mono _ _ _ _ fun γ => ?_
  refine pmf_bind_apply_mono _ _ _ _ fun ab => ?_
  have h2 : OracleAdv.run (simO (kDLChallenge G (qm + 2) χ) γ.1 (keyPolys ab.1 ab.2))
      (A (parOf γ) (iparams (parOf γ) (keyAt (keyPolys ab.1 ab.2) χ)))
      (basisPolys0 expOne γ (keyPolys ab.1 ab.2)) =
        (runF (qm + 2) A χ γ ab).map (Prod.map id (polysOf (basisPolys0 expOne γ
          (keyPolys ab.1 ab.2)) γ.1 (keyPolys ab.1 ab.2))) :=
    (run_simF_polysOf _ _ _ _ _ []).symm
  rw [reductionAlg_pk (qm + 2) (by omega) χ γ ab.1 ab.2, h2, PMF.map_comp, PMF.map_comp]
  refine pmf_map_true_mono _ _ _ fun y hy => ?_
  simp only [Function.comp_apply, decide_eq_true_eq] at hy ⊢
  obtain ⟨hnz, hroot⟩ := hy
  have hχ := RF.complete _ hnz χ hroot
  have hch : (kDLChallenge G (qm + 2) χ).getD 1 CGR.one = CyclicGroup.elemPow CGR.gen χ :=
    kDLChallenge_getD_one (qm + 1) χ _
  simp only [Prod.map, id, psiOf] at hχ ⊢
  rw [hch]
  cases h : (RF.roots _).find? (fun r => decide (CyclicGroup.elemPow CGR.gen r =
      CyclicGroup.elemPow CGR.gen χ)) with
  | none =>
    exact absurd (List.find?_eq_none.mp h χ hχ) (by simp)
  | some r =>
    have := List.find?_some h
    simp only [decide_eq_true_eq] at this
    exact (elemPow_gen_bijective hgen).1 this

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- A uniform exponent is `0` with probability `1 / p`. -/
theorem uniform_eq_zero_le :
    (PMF.uniformFintype CGR.Exp).toOuterMeasure {x | x = 0} ≤
      (1 : ℝ≥0∞) * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by
  classical
  have := PMF.uniform_mem_list_le (A := CGR.Exp) [0]
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.length_cons, List.length_nil,
    zero_add, Nat.cast_one] at this
  exact this

omit [DecidableEq CGR.Exp] in
/-- **The parameter event.** `γ_w`, `γ_{w'}` or `γ_0` is `0` with probability at most `3 / p`. -/
theorem badPar_le (D : ℕ) (A : AlgAdv G n) :
    (experiment D A).toOuterMeasure {ω | BadPar ω} ≤
      (3 : ℝ≥0∞) * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by
  have hc : ∀ (γ : ParExp G n) (μ : PMF (SymOut G n × List (FEntry G n))),
      μ.map (fun _ => γ) = PMF.pure γ := fun γ μ => PMF.map_const μ γ
  have hm : (experiment D A).map (fun ω => ω.2.1) = PMF.uniformFintype (ParExp G n) := by
    simp only [experiment, PMF.map_bind, PMF.map_comp, Function.comp_def, hc, PMF.bind_const]
    exact PMF.bind_pure _
  have hs : {ω : Outcome G n | BadPar ω} = (fun ω : Outcome G n => ω.2.1) ⁻¹'
      ({γ | γ.1 = 0} ∪ {γ | γ.2.1 = 0} ∪ {γ | γ.2.2.1 = 0}) := by
    ext ω
    simp [BadPar, or_assoc]
  rw [hs, ← PMF.toOuterMeasure_map_apply, hm]
  have h1 : (PMF.uniformFintype (ParExp G n)).toOuterMeasure {γ | γ.1 = 0} ≤
      1 * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ :=
    (PMF.uniform_prod_fst_apply (S := {x | x = 0})).le.trans uniform_eq_zero_le
  have h2 : (PMF.uniformFintype (ParExp G n)).toOuterMeasure {γ | γ.2.1 = 0} ≤
      1 * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by
    refine (PMF.uniform_prod_snd_apply (S := {c : CGR.Exp × CGR.Exp × CGR.Exp × CGR.Exp ×
      (Fin n → CGR.Exp) × (Fin n → CGR.Exp) | c.1 = 0})).le.trans ?_
    exact (PMF.uniform_prod_fst_apply (S := {x | x = 0})).le.trans uniform_eq_zero_le
  have h3 : (PMF.uniformFintype (ParExp G n)).toOuterMeasure {γ | γ.2.2.1 = 0} ≤
      1 * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by
    refine (PMF.uniform_prod_snd_apply (S := {c : CGR.Exp × CGR.Exp × CGR.Exp × CGR.Exp ×
      (Fin n → CGR.Exp) × (Fin n → CGR.Exp) | c.2.1 = 0})).le.trans ?_
    refine (PMF.uniform_prod_snd_apply (S := {c : CGR.Exp × CGR.Exp × CGR.Exp ×
      (Fin n → CGR.Exp) × (Fin n → CGR.Exp) | c.1 = 0})).le.trans ?_
    exact (PMF.uniform_prod_fst_apply (S := {x | x = 0})).le.trans uniform_eq_zero_le
  calc _ ≤ (PMF.uniformFintype (ParExp G n)).toOuterMeasure ({γ | γ.1 = 0} ∪ {γ | γ.2.1 = 0}) +
        (PMF.uniformFintype (ParExp G n)).toOuterMeasure {γ | γ.2.2.1 = 0} :=
        MeasureTheory.measure_union_le _ _
    _ ≤ ((PMF.uniformFintype (ParExp G n)).toOuterMeasure {γ | γ.1 = 0} +
        (PMF.uniformFintype (ParExp G n)).toOuterMeasure {γ | γ.2.1 = 0}) +
        (PMF.uniformFintype (ParExp G n)).toOuterMeasure {γ | γ.2.2.1 = 0} := by
        gcongr
        exact MeasureTheory.measure_union_le _ _
    _ ≤ (1 * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ + 1 * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹) +
        1 * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by gcongr
    _ = 3 * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by ring

/-! ## Equal tag values -/

omit [DecidableEq CGR.Exp] in
/-- **Equal tag values in a run.** Against `simF`, an adversary with at most `m` MAC queries,
started from a log with distinct `t`, ends with two equal `t` with probability at most
`Σ_{j < m} (|F| + j) / p`. -/
theorem run_simF_tColl_le (ch : List G) (γw : CGR.Exp) (kp : KeyPolys G n)
    (P0 : List (Poly G)) :
    ∀ (A : OracleAdv (SymQ G n) (Ans G) (SymOut G n)) (m : ℕ) (F : List (FEntry G n)),
      A.IsQueryBoundBy macCost m → (F.map fun e => e.2.1).Nodup →
      (OracleAdv.run (simF ch γw kp P0) A F).toOuterMeasure
          {y | ¬ (y.2.map fun e => e.2.1).Nodup} ≤
        ((∑ j ∈ Finset.range m, (F.length + j) : ℕ) : ℝ≥0∞) *
          (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by
  intro A
  induction A with
  | ret o =>
    intro m F _ hF
    simp [PMF.toOuterMeasure_pure_apply, hF]
  | rand p k ih =>
    intro m F hA hF
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (OracleAdv.run (simF ch γw kp P0) (k b) F).toOuterMeasure
          {y | ¬ (y.2.map fun e => e.2.1).Nodup}
        ≤ ∑' b, p b * (((∑ j ∈ Finset.range m, (F.length + j) : ℕ) : ℝ≥0∞) *
          (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹) :=
          ENNReal.tsum_le_tsum fun b => by gcongr; exact ih b m F (hA b) hF
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    intro m F hA hF
    obtain ⟨hc, hk⟩ := hA
    rcases d with M | q | q
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp only [macCost] at hc; omega⟩
      rw [OracleAdv.run_query, simF, PMF.bind_map, PMF.toOuterMeasure_bind_apply]
      have hstep : (PMF.uniformFintype (CGR.Exp × CGR.Exp × CGR.Exp)).toOuterMeasure
          {r | r.1 ∈ F.map fun e => e.2.1} ≤
            (F.length : ℝ≥0∞) * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by
        classical
        refine (PMF.uniform_prod_fst_apply (A := CGR.Exp) (B := CGR.Exp × CGR.Exp)
          (S := {t | t ∈ F.map fun e => e.2.1})).le.trans ?_
        simpa using PMF.uniform_mem_list_le (F.map fun e => e.2.1)
      calc _ ≤ ∑' r, ({r : CGR.Exp × CGR.Exp × CGR.Exp | r.1 ∈ F.map fun e => e.2.1}.indicator
            (PMF.uniformFintype (CGR.Exp × CGR.Exp × CGR.Exp)) r +
            PMF.uniformFintype (CGR.Exp × CGR.Exp × CGR.Exp) r *
              (((∑ j ∈ Finset.range m', (F.length + 1 + j) : ℕ) : ℝ≥0∞) *
                (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹)) := by
            refine ENNReal.tsum_le_tsum fun r => ?_
            by_cases hr : r.1 ∈ F.map fun e => e.2.1
            · rw [Set.indicator_of_mem (show r ∈ {r : CGR.Exp × CGR.Exp × CGR.Exp |
                r.1 ∈ F.map fun e => e.2.1} from hr)]
              refine (mul_le_of_le_one_right' ?_).trans le_self_add
              exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
                ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))
            · rw [Set.indicator_of_notMem (show r ∉ {r : CGR.Exp × CGR.Exp × CGR.Exp |
                r.1 ∈ F.map fun e => e.2.1} from hr), zero_add]
              gcongr
              have hF' : ((F ++ [(M, r)]).map fun e => e.2.1).Nodup := by
                simp only [List.map_append, List.map_cons, List.map_nil]
                exact hF.append (List.nodup_singleton _) (by simpa using hr)
              refine le_of_le_of_eq (ih _ m' (F ++ [(M, r)]) (by simpa [macCost] using hk _) hF') ?_
              simp [add_assoc]
        _ = (PMF.uniformFintype (CGR.Exp × CGR.Exp × CGR.Exp)).toOuterMeasure
              {r | r.1 ∈ F.map fun e => e.2.1} +
            ((∑ j ∈ Finset.range m', (F.length + 1 + j) : ℕ) : ℝ≥0∞) *
              (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
              PMF.toOuterMeasure_apply]
        _ ≤ (F.length : ℝ≥0∞) * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ +
            ((∑ j ∈ Finset.range m', (F.length + 1 + j) : ℕ) : ℝ≥0∞) *
              (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by gcongr
        _ = _ := by
            rw [← add_mul, Finset.sum_range_succ']
            push_cast
            congr 1
            rw [add_zero, add_comm]
            congr 1
            exact Finset.sum_congr rfl fun j _ => by ring
    · rw [OracleAdv.run_query]
      simp only [simF, simO, PMF.pure_map, PMF.pure_bind]
      exact ih _ m F (by simpa [macCost] using hk _) hF
    · rw [OracleAdv.run_query]
      simp only [simF, simO, PMF.pure_map, PMF.pure_bind]
      exact ih _ m F (by simpa [macCost] using hk _) hF

omit [DecidableEq G] in
/-- An event of probability at most `C` under every continuation has probability at most `C`
under the bind. -/
theorem bind_toOuterMeasure_le {α β : Type} (μ : PMF α) (f : α → PMF β) (S : Set β)
    (C : ℝ≥0∞) (h : ∀ a, (f a).toOuterMeasure S ≤ C) : (μ.bind f).toOuterMeasure S ≤ C := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc ∑' a, μ a * (f a).toOuterMeasure S ≤ ∑' a, μ a * C :=
        ENNReal.tsum_le_tsum fun a => by gcongr; exact h a
    _ = C := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [DecidableEq CGR.Exp] in
/-- **The tag-collision event.** For an adversary with at most `q_m` MAC queries, two MAC
answers have the same `t` with probability at most `Σ_{j < q_m} j / p`. -/
theorem tColl_le (D qm : ℕ) (A : AlgAdv G n)
    (hA : ∀ p pk, (A p pk).IsQueryBoundBy macCost qm) :
    (experiment D A).toOuterMeasure {ω | TColl ω} ≤
      ((∑ j ∈ Finset.range qm, j : ℕ) : ℝ≥0∞) * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by
  refine bind_toOuterMeasure_le _ _ _ _ fun χ => ?_
  refine bind_toOuterMeasure_le _ _ _ _ fun γ => ?_
  refine bind_toOuterMeasure_le _ _ _ _ fun ab => ?_
  rw [PMF.toOuterMeasure_map_apply]
  have h := run_simF_tColl_le (kDLChallenge G D χ) γ.1 (keyPolys ab.1 ab.2)
    (basisPolys0 expOne γ (keyPolys ab.1 ab.2))
    (A (parOf γ) (iparams (parOf γ) (keyAt (keyPolys ab.1 ab.2) χ))) qm [] (hA _ _)
    List.nodup_nil
  simpa [TColl, runF] using h

/-! ## The Schwartz–Zippel event -/

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- **Schwartz–Zippel at a uniform point.** A nonzero polynomial over a finite domain in
finitely many variables vanishes at a uniform point with probability at most its total degree
divided by the size of the domain. -/
theorem uniform_eval_eq_zero_le {R ι : Type} [CommRing R] [IsDomain R] [Fintype R]
    [Fintype ι] [DecidableEq ι] (p : MvPolynomial ι R) (hp : p ≠ 0) :
    (PMF.uniformFintype (ι → R)).toOuterMeasure {x | MvPolynomial.eval x p = 0} ≤
      (p.totalDegree : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ := by
  classical
  let e := Fintype.equivFin ι
  let q : MvPolynomial (Fin (Fintype.card ι)) R := MvPolynomial.rename e p
  have hq : q ≠ 0 := fun h =>
    hp ((MvPolynomial.rename_injective _ e.injective) (h.trans (map_zero _).symm))
  have hdeg : q.totalDegree ≤ p.totalDegree := MvPolynomial.totalDegree_rename_le e p
  have hev : ∀ x : ι → R, MvPolynomial.eval x p = MvPolynomial.eval (x ∘ e.symm) q := by
    intro x
    simp only [q, MvPolynomial.eval_rename]
    congr 2
    funext i
    simp
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hq (Finset.univ : Finset R)
  rw [Fintype.piFinset_univ, Finset.card_univ,
    div_le_div_iff₀ (by positivity) (by positivity)] at hsz
  have hcard : Fintype.card {x : ι → R | MvPolynomial.eval x p = 0} =
      (Finset.univ.filter fun f : Fin (Fintype.card ι) → R => MvPolynomial.eval f q = 0).card := by
    rw [Fintype.card_ofFinset]
    refine Finset.card_bij (fun x _ => x ∘ e.symm) (fun x hx => by simpa [← hev] using hx)
      (fun x _ y _ h => ?_) (fun f hf => ⟨f ∘ e, by simpa [hev, Function.comp_assoc] using hf,
        by simp [Function.comp_assoc]⟩)
    funext i
    simpa using congrFun h (e i)
  have hN : ((Finset.univ.filter fun f : Fin (Fintype.card ι) → R =>
      MvPolynomial.eval f q = 0).card) * Fintype.card R ≤
        p.totalDegree * Fintype.card R ^ Fintype.card ι := by
    have h : ((Finset.univ.filter fun f : Fin (Fintype.card ι) → R =>
        MvPolynomial.eval f q = 0).card) * Fintype.card R ≤
          q.totalDegree * Fintype.card R ^ Fintype.card ι := by exact_mod_cast hsz
    exact h.trans (Nat.mul_le_mul_right _ hdeg)
  have hR0 : (Fintype.card R : ℝ≥0∞) ≠ 0 := by simp
  have hRt : (Fintype.card R : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [PMF.toOuterMeasure_uniformFintype_apply, hcard, Fintype.card_fun]
  rw [ENNReal.div_le_iff (by simp) (by simp)]
  calc ((Finset.univ.filter fun f : Fin (Fintype.card ι) → R =>
        MvPolynomial.eval f q = 0).card : ℝ≥0∞)
      = ((Finset.univ.filter fun f : Fin (Fintype.card ι) → R =>
        MvPolynomial.eval f q = 0).card : ℝ≥0∞) * Fintype.card R *
          (Fintype.card R : ℝ≥0∞)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hR0 hRt, mul_one]
    _ ≤ (p.totalDegree * Fintype.card R ^ Fintype.card ι : ℕ) * (Fintype.card R : ℝ≥0∞)⁻¹ := by
        gcongr
        exact_mod_cast hN
    _ = _ := by push_cast; ring

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- Renaming the variables by an injective map keeps the total degree. -/
theorem totalDegree_rename_of_injective' {R σ τ : Type} [CommSemiring R]
    {f : σ → τ} (hf : Function.Injective f) (p : MvPolynomial σ R) :
    (MvPolynomial.rename f p).totalDegree = p.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree, MvPolynomial.support_rename_of_injective hf, Finset.sup_image,
    MvPolynomial.totalDegree]
  congr 1
  funext s
  simp only [Function.comp_apply]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The polynomial of a representation has at most the total degree of the basis. -/
theorem totalDegree_rep_le (d : ℕ) :
    ∀ (B : List (MvPolynomial (Formal.Var n) CGR.Exp)) (c : Rep G),
      (∀ b ∈ B, b.totalDegree ≤ d) → (Formal.rep B c).totalDegree ≤ d
  | [], c, _ => by cases c <;> simp [Formal.rep]
  | _ :: _, [], _ => by simp [Formal.rep]
  | b :: B, a :: c, h => by
    have ih := totalDegree_rep_le d B c fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
    simp only [Formal.rep, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ih)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact h b List.mem_cons_self

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- A variable has total degree at most `1`. -/
theorem totalDegree_X_le' {R σ : Type} [CommSemiring R] (v : σ) :
    (MvPolynomial.X v : MvPolynomial σ R).totalDegree ≤ 1 := by
  have h := MvPolynomial.totalDegree_monomial_le (Finsupp.single v 1) (1 : R)
  rw [Finsupp.sum_single_index rfl] at h
  exact h

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- `x0 + s x1` has total degree at most `1`. -/
theorem totalDegree_lin_le (s : CGR.Exp) : (Formal.lin (n := n) s).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (totalDegree_X_le' _) ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact totalDegree_X_le' _

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The polynomials received before the `k`-th MAC answer have total degree at most `k + 1`. -/
theorem totalDegree_basis_le (γ' : Formal.ParLog CGR.Exp n) (t : ℕ → CGR.Exp)
    (M : ℕ → SymMsg G n) : ∀ (k : ℕ), ∀ p ∈ Formal.basis γ' t M k, p.totalDegree ≤ k + 1 := by
  have hX : ∀ v : Formal.Var n,
      (MvPolynomial.X v : MvPolynomial (Formal.Var n) CGR.Exp).totalDegree ≤ 1 :=
    fun v => totalDegree_X_le' _
  have hCX : ∀ (a : CGR.Exp) (v : Formal.Var n),
      (MvPolynomial.C a * MvPolynomial.X v : MvPolynomial (Formal.Var n) CGR.Exp).totalDegree
        ≤ 1 := fun a v => by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hX v
  intro k
  induction k with
  | zero =>
    intro p hp
    simp only [Formal.basis, Formal.basis0, List.mem_append, List.mem_cons, List.mem_ofFn,
      List.not_mem_nil, or_false] at hp
    rcases hp with (((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | rfl | rfl
    all_goals try (simp only [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_C]; omega)
    · exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hCX _ _) (hCX _ _))
    · simp only [Formal.iPoly]
      refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ (hCX _ _))
        refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ (hCX _ _))
        simp
      · refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
        exact Finset.sup_le fun i _ => hCX _ _
  | succ k ih =>
    intro p hp
    rw [Formal.basis_succ] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | rfl | rfl
    · have := ih p hp
      omega
    · exact (hX _).trans (by omega)
    · simp only [Formal.vPoly, Formal.mPoly]
      refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ((hCX _ _).trans (by omega)) ?_)
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        have := totalDegree_lin_le (n := n) (t k)
        have := hX (Formal.Var.u k)
        omega
      · refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
        refine Finset.sup_le fun i _ => (MvPolynomial.totalDegree_mul _ _).trans ?_
        have := totalDegree_rep_le (k + 1) _ (M k i) ih
        have := hX (Formal.Var.y i)
        omega

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The formal forgery equation over a log of length `k` has total degree at most `k + 2`. -/
theorem totalDegree_forgeryForm_le (γ : ParExp G n) (F : List (FEntry G n)) (o : SymOut G n) :
    (forgeryForm γ F o).totalDegree ≤ F.length + 2 := by
  have hB := totalDegree_basis_le (parLog γ) (tOf F) (MOf F) F.length
  have hr : ∀ c, (Formal.rep (Formal.basis (parLog γ) (tOf F) (MOf F) F.length) c).totalDegree
      ≤ F.length + 1 := fun c => totalDegree_rep_le _ _ c hB
  have hX : ∀ v : Formal.Var n,
      (MvPolynomial.X v : MvPolynomial (Formal.Var n) CGR.Exp).totalDegree ≤ 1 :=
    fun v => totalDegree_X_le' _
  simp only [forgeryForm]
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ((hr _).trans (by omega)) ?_)
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      exact (hX _).trans (by omega)
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have := hr o.2.2.1
      have := totalDegree_lin_le (n := n) o.2.1
      omega
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    refine Finset.sup_le fun i _ => (MvPolynomial.totalDegree_mul _ _).trans ?_
    have := hr (o.1 i)
    have := hX (Formal.Var.y i)
    omega

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The formal forgery equation over a log of length `k` contains no `u_j` with `j ≥ k`. -/
theorem forgeryForm_mem_supported (γ : ParExp G n) (F : List (FEntry G n)) (o : SymOut G n) :
    forgeryForm γ F o ∈ MvPolynomial.supported CGR.Exp (Formal.early (n := n) F.length) := by
  have hr : ∀ c, Formal.rep (Formal.basis (parLog γ) (tOf F) (MOf F) F.length) c ∈
      MvPolynomial.supported CGR.Exp (Formal.early (n := n) F.length) := fun c =>
    Formal.spanAt_le F.length (Formal.rep_mem _ c)
  have hX : ∀ v : Formal.Var n, (∀ j, v ≠ .u j) →
      (MvPolynomial.X v : MvPolynomial (Formal.Var n) CGR.Exp) ∈
        MvPolynomial.supported CGR.Exp (Formal.early (n := n) F.length) := fun v hv =>
    Formal.X_mem_supported_of_mem fun j hj => absurd hj (hv j)
  have hlin : ∀ s, Formal.lin (n := n) s ∈
      MvPolynomial.supported CGR.Exp (Formal.early (n := n) F.length) := fun s =>
    Subalgebra.add_mem _ (hX _ (by simp))
      (Subalgebra.mul_mem _ (Formal.C_mem_supported _ _) (hX _ (by simp)))
  simp only [forgeryForm]
  refine Subalgebra.sub_mem _ (hr _) (Subalgebra.add_mem _ (Subalgebra.add_mem _
    (Subalgebra.mul_mem _ (Formal.C_mem_supported _ _) (hX _ (by simp)))
    (Subalgebra.mul_mem _ (hr _) (hlin _))) ?_)
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hX _ (by simp)) (hr _)

variable (n) in
/-- The index of the formal variables of the key and of `u_0, …, u_{k-1}`. -/
abbrev VarIdx (k : ℕ) := Option (Option (Option (Option (Fin n ⊕ Fin k))))

/-- The formal variable of an index. -/
def varOf {k : ℕ} : VarIdx n k → Formal.Var n
  | none => .w
  | some none => .w'
  | some (some none) => .x0
  | some (some (some none)) => .x1
  | some (some (some (some (.inl i)))) => .y i
  | some (some (some (some (.inr j)))) => .u j

/-- Distinct indices name distinct formal variables. -/
theorem varOf_injective (k : ℕ) : Function.Injective (varOf (n := n) (k := k)) := by
  intro a b h
  rcases a with _ | _ | _ | _ | _ | i | j <;> rcases b with _ | _ | _ | _ | _ | i' | j' <;>
    simp_all [varOf, Fin.ext_iff]

/-- The variables without `u_j`, `j ≥ k`, are indexed by `VarIdx n k`. -/
theorem early_subset_range (k : ℕ) :
    Formal.early (n := n) k ⊆ Set.range (varOf (n := n) (k := k)) := by
  intro v hv
  cases v with
  | w => exact ⟨none, rfl⟩
  | w' => exact ⟨some none, rfl⟩
  | x0 => exact ⟨some (some none), rfl⟩
  | x1 => exact ⟨some (some (some none)), rfl⟩
  | y i => exact ⟨some (some (some (some (.inl i)))), rfl⟩
  | u j => exact ⟨some (some (some (some (.inr ⟨j, hv j rfl⟩)))), rfl⟩

/-- The point of the index set given by a key and values of `u_0, …, u_{k-1}`. -/
def zOf {k : ℕ} (b : MacN.Key G n) (z : Fin k → CGR.Exp) : VarIdx n k → CGR.Exp
  | none => b.1
  | some none => b.2.1
  | some (some none) => b.2.2.1
  | some (some (some none)) => b.2.2.2.1
  | some (some (some (some (.inl i)))) => b.2.2.2.2 i
  | some (some (some (some (.inr j)))) => z j

/-- Keys with values of `u_0, …, u_{k-1}` are the points of the index set. -/
def zEquiv (k : ℕ) : MacN.Key G n × (Fin k → CGR.Exp) ≃ (VarIdx n k → CGR.Exp) where
  toFun x := zOf x.1 x.2
  invFun f := ((f none, f (some none), f (some (some none)), f (some (some (some none))),
    fun i => f (some (some (some (some (.inl i)))))),
    fun j => f (some (some (some (some (.inr j))))))
  left_inv x := by obtain ⟨⟨_, _, _, _, _⟩, _⟩ := x; rfl
  right_inv f := by
    funext i
    rcases i with _ | _ | _ | _ | _ | i | j <;> rfl

/-- The point of the formal variables given by a key and values of `u_0, …, u_{k-1}` (`0` for
the other `u_j`). -/
noncomputable def embAt (k : ℕ) (b : MacN.Key G n) (z : Fin k → CGR.Exp) : Formal.Var n → CGR.Exp
  | .w => b.1
  | .w' => b.2.1
  | .x0 => b.2.2.1
  | .x1 => b.2.2.2.1
  | .y i => b.2.2.2.2 i
  | .u j => if h : j < k then z ⟨j, h⟩ else 0

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- **Schwartz–Zippel at a shifted uniform point.** For a generator `g ≠ 1`, a nonzero
polynomial without `u_j`, `j ≥ k`, vanishes at `c + (b, z)` for a uniform key `b` and uniform
values `z` of `u_0, …, u_{k-1}` with probability at most its total degree over `p`. -/
theorem sz_shift_le (hgen : CGR.gen ≠ CGR.one) (k : ℕ)
    (φ : MvPolynomial (Formal.Var n) CGR.Exp)
    (hφ : φ ∈ MvPolynomial.supported CGR.Exp (Formal.early (n := n) k))
    (c : Formal.Var n → CGR.Exp) :
    (PMF.uniformFintype (MacN.Key G n × (Fin k → CGR.Exp))).toOuterMeasure
        {x | φ ≠ 0 ∧ MvPolynomial.eval (c + embAt k x.1 x.2) φ = 0} ≤
      (φ.totalDegree : ℝ≥0∞) * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by
  classical
  have := exp_nontrivial hgen
  have := expIsDomain (G := G)
  by_cases hφ0 : φ = 0
  · simp [hφ0]
  have hvars : (φ.vars : Set (Formal.Var n)) ⊆ Set.range (varOf (n := n) (k := k)) :=
    (MvPolynomial.mem_supported.mp hφ).trans (early_subset_range k)
  obtain ⟨φ', rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range φ _
    (varOf_injective k) hvars
  have hφ'0 : φ' ≠ 0 := fun h => hφ0 (by rw [h, map_zero])
  have hcomp : ∀ x : MacN.Key G n × (Fin k → CGR.Exp),
      (c + embAt k x.1 x.2) ∘ varOf = (c ∘ varOf) + zEquiv k x := by
    intro x
    funext i
    rcases i with _ | _ | _ | _ | _ | i | j <;>
      simp only [varOf, embAt, zEquiv, zOf, Pi.add_apply, Function.comp_apply,
        Equiv.coe_fn_mk] <;>
      rw [dite_eq_left_of_eq_true (eq_true ‹_›)]
  have hs : {x : MacN.Key G n × (Fin k → CGR.Exp) | MvPolynomial.rename varOf φ' ≠ 0 ∧
      MvPolynomial.eval (c + embAt k x.1 x.2) (MvPolynomial.rename varOf φ') = 0} ⊆
      (zEquiv k) ⁻¹' ((Equiv.addLeft (c ∘ varOf)) ⁻¹' {y | MvPolynomial.eval y φ' = 0}) := by
    intro x hx
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_rename, hcomp] at hx
    exact hx.2
  refine (MeasureTheory.measure_mono hs).trans ?_
  rw [← PMF.toOuterMeasure_map_apply, PMF.uniformFintype_map_equiv,
    ← PMF.toOuterMeasure_map_apply, PMF.uniformFintype_map_equiv,
    totalDegree_rename_of_injective' (varOf_injective k)]
  exact uniform_eval_eq_zero_le φ' hφ'0

/-! ### The view of the adversary -/

variable (G) in
/-- An entry of the MAC log seen by the adversary: the attribute representations, `t` and the
value `v_u = a_u + b_u χ` of `u`. -/
abbrev VEntry (n : ℕ) := SymMsg G n × CGR.Exp × CGR.Exp

/-- The formal log with the coefficients `b_u` and `a_u = v_u - b_u χ`. -/
noncomputable def attachL (χ : CGR.Exp) (FV : List (VEntry G n)) (bs : List CGR.Exp) :
    List (FEntry G n) :=
  List.zipWith (fun e b => (e.1, e.2.1, e.2.2 - χ * b, b)) FV bs

/-- The key `b χ`. -/
noncomputable def kshift (χ : CGR.Exp) (b : MacN.Key G n) : MacN.Key G n :=
  (χ * b.1, χ * b.2.1, χ * b.2.2.1, χ * b.2.2.2.1, fun i => χ * b.2.2.2.2 i)

/-- The values of the formal variables seen by the adversary: the key values and the `v_u`. -/
noncomputable def valsV (vkey : MacN.Key G n) (FV : List (VEntry G n)) :
    Formal.Var n → CGR.Exp
  | .w => vkey.1
  | .w' => vkey.2.1
  | .x0 => vkey.2.2.1
  | .x1 => vkey.2.2.2.1
  | .y i => vkey.2.2.2.2 i
  | .u j => (FV[j]?.map fun e => e.2.2).getD 0

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The formal log of a view has the length of the view. -/
theorem length_attachL (χ : CGR.Exp) (FV : List (VEntry G n)) (bs : List CGR.Exp)
    (h : bs.length = FV.length) : (attachL χ FV bs).length = FV.length := by
  simp [attachL, h]

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The entries of the formal log of a view. -/
theorem getElem?_attachL (χ : CGR.Exp) (FV : List (VEntry G n)) (bs : List CGR.Exp) (j : ℕ) :
    (attachL χ FV bs)[j]? = (FV[j]?).bind fun e => bs[j]?.map fun b =>
      (e.1, e.2.1, e.2.2 - χ * b, b) := by
  simp only [attachL, List.getElem?_zipWith]
  cases FV[j]? <;> cases bs[j]? <;> rfl

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The tag values of the formal log are those of the view. -/
theorem tOf_attachL (χ : CGR.Exp) (FV : List (VEntry G n)) (bs : List CGR.Exp)
    (h : bs.length = FV.length) :
    tOf (attachL χ FV bs) = fun k => (FV[k]?.map fun e => e.2.1).getD 0 := by
  funext k
  rw [tOf, getElem?_attachL χ FV bs]
  rcases Nat.lt_or_ge k FV.length with hk | hk
  · simp [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (h ▸ hk : k < bs.length)]
  · simp [List.getElem?_eq_none hk]

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The attribute representations of the formal log are those of the view. -/
theorem MOf_attachL (χ : CGR.Exp) (FV : List (VEntry G n)) (bs : List CGR.Exp)
    (h : bs.length = FV.length) :
    MOf (attachL χ FV bs) = fun k => (FV[k]?.map fun e => e.1).getD fun _ => [] := by
  funext k
  rw [MOf, getElem?_attachL χ FV bs]
  rcases Nat.lt_or_ge k FV.length with hk | hk
  · simp [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (h ▸ hk : k < bs.length)]
  · simp [List.getElem?_eq_none hk]

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The formal basis of the formal log is that of the view. -/
theorem basis_attachL (γ : ParExp G n) (χ : CGR.Exp) (FV : List (VEntry G n))
    (bs bs' : List CGR.Exp) (h : bs.length = FV.length) (h' : bs'.length = FV.length) :
    Formal.basis (parLog γ) (tOf (attachL χ FV bs)) (MOf (attachL χ FV bs))
        (attachL χ FV bs).length =
      Formal.basis (parLog γ) (tOf (attachL χ FV bs')) (MOf (attachL χ FV bs'))
        (attachL χ FV bs').length := by
  rw [tOf_attachL χ FV bs h, tOf_attachL χ FV bs' h', MOf_attachL χ FV bs h,
    MOf_attachL χ FV bs' h', length_attachL χ FV bs h, length_attachL χ FV bs' h']

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The formal forgery equation over the formal log is that over the view. -/
theorem forgeryForm_attachL (γ : ParExp G n) (χ : CGR.Exp) (FV : List (VEntry G n))
    (bs bs' : List CGR.Exp) (h : bs.length = FV.length) (h' : bs'.length = FV.length)
    (o : SymOut G n) :
    forgeryForm γ (attachL χ FV bs) o = forgeryForm γ (attachL χ FV bs') o := by
  simp only [forgeryForm, basis_attachL γ χ FV bs bs' h h']

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- At `χ`, the point of the formal log with `a = v - b χ` is the view. -/
theorem valsAt_attachL (χ : CGR.Exp) (vkey b : MacN.Key G n) (FV : List (VEntry G n))
    (bs : List CGR.Exp) (h : bs.length = FV.length) :
    valsAt χ (vkey - kshift χ b) b (attachL χ FV bs) = valsV vkey FV := by
  funext v
  cases v with
  | u j =>
    simp only [valsAt, valsV, getElem?_attachL χ FV bs]
    rcases Nat.lt_or_ge j FV.length with hk | hk
    · simp [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (h ▸ hk : j < bs.length)]
    · simp [List.getElem?_eq_none hk]
  | _ => simp [valsAt, valsV, kshift]

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- At `χ + 1`, the point of the formal log with `a = v - b χ` is the view shifted by the
coefficients `b`. -/
theorem valsAt_succ_attachL (χ : CGR.Exp) (vkey b : MacN.Key G n) (FV : List (VEntry G n))
    (z : Fin FV.length → CGR.Exp) :
    valsAt (χ + 1) (vkey - kshift χ b) b (attachL χ FV (List.ofFn z)) =
      valsV vkey FV + embAt FV.length b z := by
  funext v
  cases v with
  | u j =>
    simp only [valsAt, Pi.add_apply, valsV, embAt,
      getElem?_attachL χ FV (List.ofFn z)]
    rcases Nat.lt_or_ge j FV.length with hk | hk
    · simp [hk]
      ring
    · simp [Nat.not_lt.mpr hk]
  | _ => simp [valsAt, valsV, kshift, embAt]; ring

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The key `kp(χ)` of `a = v - b χ` is `v`. -/
theorem keyAt_kshift (χ : CGR.Exp) (vkey b : MacN.Key G n) :
    keyAt (keyPolys (vkey - kshift χ b) b) χ = vkey := by
  obtain ⟨v1, v2, v3, v4, v5⟩ := vkey
  simp only [keyAt, keyPolys, kshift, peval_cons, peval_nil, mul_zero, add_zero, Prod.mk_sub_mk,
    w, w', x0, x1, y, Pi.sub_apply, sub_add_cancel]

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The MAC polynomial at the key polynomials of `a = v - b χ` evaluates at `χ` with the key
`v`. -/
theorem peval_macPoly_kshift (χ γw : CGR.Exp) (vkey b : MacN.Key G n) (pA0 pA1 : Poly G)
    (pA : Fin n → Poly G) :
    peval (macPoly γw (keyPolys (vkey - kshift χ b) b) pA0 pA1 pA) χ =
      γw * vkey.1 + vkey.2.2.1 * peval pA0 χ + vkey.2.2.2.1 * peval pA1 χ +
        ∑ i, vkey.2.2.2.2 i * peval (pA i) χ := by
  rw [peval_macPoly]
  obtain ⟨v1, v2, v3, v4, v5⟩ := vkey
  simp only [kshift, Prod.mk_sub_mk, Pi.sub_apply, sub_add_cancel]

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The received polynomials over a log of length `k` have degree at most `k + 1`. -/
theorem length_polysOf (γ : ParExp G n) (a b : MacN.Key G n) :
    ∀ (F : List (FEntry G n)), ∀ p ∈ polysOf (basisPolys0 expOne γ (keyPolys a b)) γ.1
      (keyPolys a b) F, p.length ≤ F.length + 2 := by
  intro F
  induction F using List.reverseRecOn with
  | nil => exact fun p hp => basisPolys0_length expOne γ a b p hp
  | append_singleton F e ih =>
    intro p hp
    rw [polysOf, stateOf_append, stepS] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    change p ∈ polysOf _ _ _ F ∨ p = uPoly e ∨
      p = vPolyL γ.1 (keyPolys a b) (polysOf _ _ _ F) e at hp
    simp only [List.length_append, List.length_singleton]
    rcases hp with hp | rfl | rfl
    · have := ih p hp
      omega
    · simp [uPoly]
    · exact length_macPoly_le γ.1 _ (keyPolys_lin a b) _ _ _ (F.length + 1) (by simp [uPoly])
        (by simp [uPoly, length_pscale]) fun i => length_polyRep_le _ _ _ ih

/-- The formal basis of a view. -/
noncomputable def basisV (γ : ParExp G n) (FV : List (VEntry G n)) :
    List (MvPolynomial (Formal.Var n) CGR.Exp) :=
  Formal.basis (parLog γ) (fun k => (FV[k]?.map fun e => e.2.1).getD 0)
    (fun k => (FV[k]?.map fun e => e.1).getD fun _ => []) FV.length

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The formal basis of the formal log of a view is the basis of the view. -/
theorem basis_attachL_eq (γ : ParExp G n) (χ : CGR.Exp) (FV : List (VEntry G n))
    (bs : List CGR.Exp) (h : bs.length = FV.length) :
    Formal.basis (parLog γ) (tOf (attachL χ FV bs)) (MOf (attachL χ FV bs))
      (attachL χ FV bs).length = basisV γ FV := by
  rw [tOf_attachL χ FV bs h, MOf_attachL χ FV bs h, length_attachL χ FV bs h, basisV]

/-- The value at the view of a representation. -/
noncomputable def evV (γ : ParExp G n) (vkey : MacN.Key G n) (FV : List (VEntry G n))
    (c : Rep G) : CGR.Exp :=
  MvPolynomial.eval (valsV vkey FV) (Formal.rep (basisV γ FV) c)

/-- The answer of a verification or helper query computed from the view. -/
noncomputable def ansView (γ : ParExp G n) (vkey : MacN.Key G n) (FV : List (VEntry G n)) :
    (SymMsg G n × SymTag G) ⊕ (Rep G × Rep G × SymMsg G n × Rep G) → Ans G
  | .inl q => .inr (.inl (decide (evV γ vkey FV q.2.2.2 = γ.1 * vkey.1 +
      vkey.2.2.1 * evV γ vkey FV q.2.2.1 + vkey.2.2.2.1 * (q.2.1 * evV γ vkey FV q.2.2.1) +
        ∑ i, vkey.2.2.2.2 i * evV γ vkey FV (q.1 i))))
  | .inr q => .inr (.inr (decide (evV γ vkey FV q.2.2.2 = γ.1 * vkey.1 +
      vkey.2.2.1 * evV γ vkey FV q.1 + vkey.2.2.2.1 * evV γ vkey FV q.2.1 +
        ∑ i, vkey.2.2.2.2 i * evV γ vkey FV (q.2.2.1 i))))

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- The received polynomial of a representation evaluates at `χ` to its value at the view. -/
theorem peval_polyRep_attachL (χ : CGR.Exp) (γ : ParExp G n) (vkey b : MacN.Key G n)
    (FV : List (VEntry G n)) (bs : List CGR.Exp) (hbs : bs.length = FV.length) (c : Rep G) :
    peval (polyRep (polysOf (basisPolys0 expOne γ (keyPolys (vkey - kshift χ b) b)) γ.1
      (keyPolys (vkey - kshift χ b) b) (attachL χ FV bs)) c) χ = evV γ vkey FV c := by
  have h := peval_polyRep_polysOf χ γ (vkey - kshift χ b) b (attachL χ FV bs) [] c
  rw [List.append_nil, valsAt_attachL χ vkey b FV bs hbs, basis_attachL_eq γ χ FV bs hbs] at h
  exact h

/-- **A verification or helper query on the view.** For a log of at most `q_m` entries, the
answer of `simF` with `a = v - b χ` is the answer computed from the view: the formal
equation at the key values and the `v_u`. -/
theorem simF_inr_attachL (hgen : CGR.gen ≠ CGR.one) (qm : ℕ) (χ : CGR.Exp) (γ : ParExp G n)
    (vkey b : MacN.Key G n) (FV : List (VEntry G n)) (bs : List CGR.Exp)
    (hbs : bs.length = FV.length) (hk : FV.length ≤ qm)
    (q : (SymMsg G n × SymTag G) ⊕ (Rep G × Rep G × SymMsg G n × Rep G)) :
    simF (kDLChallenge G (qm + 2) χ) γ.1 (keyPolys (vkey - kshift χ b) b)
        (basisPolys0 expOne γ (keyPolys (vkey - kshift χ b) b)) (attachL χ FV bs) (.inr q) =
      PMF.pure (ansView γ vkey FV q, attachL χ FV bs) := by
  have hinj := (elemPow_gen_bijective (G := G) hgen).1
  have hP := length_polysOf γ (vkey - kshift χ b) b (attachL χ FV bs)
  rw [length_attachL χ FV bs hbs] at hP
  have hl : ∀ c, (polyRep (polysOf (basisPolys0 expOne γ (keyPolys (vkey - kshift χ b) b)) γ.1
      (keyPolys (vkey - kshift χ b) b) (attachL χ FV bs)) c).length ≤ FV.length + 2 :=
    fun c => length_polyRep_le _ c _ hP
  have hrep := peval_polyRep_attachL χ γ vkey b FV bs hbs
  have hkp := keyPolys_lin (vkey - kshift χ b) b
  rcases q with q | q
  · simp only [simF, simO, PMF.pure_map, ansView]
    set P := polysOf (basisPolys0 expOne γ (keyPolys (vkey - kshift χ b) b)) γ.1
      (keyPolys (vkey - kshift χ b) b) (attachL χ FV bs) with hPdef
    have hm := length_macPoly_le γ.1 _ hkp (polyRep P q.2.2.1) (pscale q.2.1 (polyRep P q.2.2.1))
      (fun i => polyRep P (q.1 i)) (FV.length + 1) (by have := hl q.2.2.1; omega)
      (by rw [length_pscale]; have := hl q.2.2.1; omega) fun i => by have := hl (q.1 i); omega
    rw [vanishes_padd_pneg hgen (qm + 2) χ _ _ (by have := hl q.2.2.2; omega) (by omega)]
    simp only [evP, hinj.eq_iff, peval_macPoly_kshift, peval_pscale, hrep]
  · simp only [simF, simO, PMF.pure_map, ansView]
    set P := polysOf (basisPolys0 expOne γ (keyPolys (vkey - kshift χ b) b)) γ.1
      (keyPolys (vkey - kshift χ b) b) (attachL χ FV bs) with hPdef
    have hm := length_macPoly_le γ.1 _ hkp (polyRep P q.1) (polyRep P q.2.1)
      (fun i => polyRep P (q.2.2.1 i)) (FV.length + 1) (by have := hl q.1; omega)
      (by have := hl q.2.1; omega) fun i => by have := hl (q.2.2.1 i); omega
    rw [vanishes_padd_pneg hgen (qm + 2) χ _ _ (by have := hl q.2.2.2; omega) (by omega)]
    simp only [evP, hinj.eq_iff, peval_macPoly_kshift, hrep]

/-- The answer of a MAC query computed from the view and the coins `(t, v_u)`. -/
noncomputable def macAnsView (γ : ParExp G n) (vkey : MacN.Key G n) (FV : List (VEntry G n))
    (M : SymMsg G n) (t v : CGR.Exp) : Ans G :=
  .inl (t, CyclicGroup.elemPow CGR.gen v, CyclicGroup.elemPow CGR.gen (γ.1 * vkey.1 +
    vkey.2.2.1 * v + vkey.2.2.2.1 * (t * v) + ∑ i, vkey.2.2.2.2 i * evV γ vkey FV (M i)))

omit [DecidableEq CGR.Exp] in
/-- **A MAC query on the view.** For a log of fewer than `q_m` entries, the MAC query of `simF`
with `a = v - b χ` samples `(t, v_u, b_u)` uniformly, answers from the view and `(t, v_u)`,
and logs `b_u`. -/
theorem simF_inl_attachL (qm : ℕ) (χ : CGR.Exp) (γ : ParExp G n)
    (vkey b : MacN.Key G n) (FV : List (VEntry G n)) (bs : List CGR.Exp)
    (hbs : bs.length = FV.length) (hk : FV.length + 1 ≤ qm) (M : SymMsg G n) :
    simF (kDLChallenge G (qm + 2) χ) γ.1 (keyPolys (vkey - kshift χ b) b)
        (basisPolys0 expOne γ (keyPolys (vkey - kshift χ b) b)) (attachL χ FV bs) (.inl M) =
      (PMF.uniformFintype (CGR.Exp × CGR.Exp × CGR.Exp)).map fun r =>
        (macAnsView γ vkey FV M r.1 r.2.1,
          attachL χ (FV ++ [(M, r.1, r.2.1)]) (bs ++ [r.2.2])) := by
  let E : CGR.Exp × CGR.Exp × CGR.Exp ≃ CGR.Exp × CGR.Exp × CGR.Exp :=
    { toFun := fun r => (r.1, r.2.1 - χ * r.2.2, r.2.2)
      invFun := fun r => (r.1, r.2.1 + χ * r.2.2, r.2.2)
      left_inv := fun r => by simp
      right_inv := fun r => by simp }
  have hP := length_polysOf γ (vkey - kshift χ b) b (attachL χ FV bs)
  rw [length_attachL χ FV bs hbs] at hP
  have hrep := peval_polyRep_attachL χ γ vkey b FV bs hbs
  rw [simF]
  conv_lhs => rw [← PMF.uniformFintype_map_equiv E, PMF.map_comp]
  congr 1
  funext r
  obtain ⟨t, v, b'⟩ := r
  simp only [Function.comp_apply, E, Equiv.coe_fn_mk]
  have hm := length_macPoly_le γ.1 _ (keyPolys_lin (vkey - kshift χ b) b)
    (uPoly (M, t, v - χ * b', b')) (pscale t (uPoly (M, t, v - χ * b', b')))
    (fun i => polyRep (polysOf (basisPolys0 expOne γ (keyPolys (vkey - kshift χ b) b)) γ.1
      (keyPolys (vkey - kshift χ b) b) (attachL χ FV bs)) (M i)) (FV.length + 1)
    (by simp [uPoly]) (by simp [uPoly, length_pscale])
    fun i => by have := length_polyRep_le _ (M i) _ hP; omega
  rw [elemOf_kDLChallenge (qm + 2) χ _ (by simp [uPoly]),
    elemOf_kDLChallenge (qm + 2) χ _ (by simp only [vPolyL]; omega)]
  have hatt : attachL χ FV bs ++ [(M, t, v - χ * b', b')] =
      attachL χ (FV ++ [(M, t, v)]) (bs ++ [b']) := by
    simp [attachL, List.zipWith_append, hbs]
  rw [hatt]
  simp only [macAnsView, evP, vPolyL, peval_macPoly_kshift, peval_pscale, peval_uPoly, hrep,
    sub_add_cancel]

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- A uniform triple is a uniform pair followed by an independent uniform third component. -/
theorem uniform_triple_bind {X β : Type} [Fintype X] [Nonempty X] (f : X × X × X → PMF β) :
    (PMF.uniformFintype (X × X × X)).bind f =
      (PMF.uniformFintype (X × X)).bind fun tv =>
        (PMF.uniformFintype X).bind fun c => f (tv.1, tv.2, c) := by
  rw [← PMF.uniformFintype_map_equiv (Equiv.prodAssoc X X X), PMF.bind_map,
    PMF.uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map]
  rfl

omit [DecidableEq G] [DecidableEq CGR.Exp] in
/-- A uniform vector of length `k + 1` is a uniform vector of length `k` followed by an
independent uniform last entry. -/
theorem uniform_snoc_bind {X β : Type} [Fintype X] [Nonempty X] (k : ℕ)
    (f : (Fin (k + 1) → X) → PMF β) :
    (PMF.uniformFintype (Fin (k + 1) → X)).bind f =
      (PMF.uniformFintype (Fin k → X)).bind fun z =>
        (PMF.uniformFintype X).bind fun c => f (Fin.snoc z c) := by
  rw [← PMF.uniformFintype_map_equiv (Fin.snocEquiv fun _ => X), PMF.bind_map,
    PMF.uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map]
  rw [PMF.bind_comm]
  rfl

/-- **The run averaged over the coefficients `b`.** For the view `FV` with `k` entries: uniform
key coefficients `b` and uniform coefficients `b_u` of the logged `u`, then the run of `A'`
against `simF` with `a = v - b χ` from the formal log of the view. -/
noncomputable def jDist (qm : ℕ) (χ : CGR.Exp) (γ : ParExp G n) (vkey : MacN.Key G n)
    (A' : OracleAdv (SymQ G n) (Ans G) (SymOut G n)) (FV : List (VEntry G n)) (k : ℕ) :
    PMF (MacN.Key G n × (SymOut G n × List (FEntry G n))) :=
  (PMF.uniformFintype (MacN.Key G n)).bind fun b =>
    (PMF.uniformFintype (Fin k → CGR.Exp)).bind fun z =>
      (OracleAdv.run (simF (kDLChallenge G (qm + 2) χ) γ.1 (keyPolys (vkey - kshift χ b) b)
        (basisPolys0 expOne γ (keyPolys (vkey - kshift χ b) b))) A'
          (attachL χ FV (List.ofFn z))).map fun y => (b, y)

/-- The Schwartz–Zippel event of an averaged run. -/
def szSet (χ : CGR.Exp) (γ : ParExp G n) (vkey : MacN.Key G n) :
    Set (MacN.Key G n × (SymOut G n × List (FEntry G n))) :=
  {x | SZEvent (χ, γ, (vkey - kshift χ x.1, x.1), x.2)}

omit [DecidableEq CGR.Exp] in
/-- **The Schwartz–Zippel bound of the averaged run.** For a generator `g ≠ 1`, an adversary
with at most `m` MAC queries and a view of `k` entries with `k + m ≤ q_m`, the averaged run
ends in the Schwartz–Zippel event with probability at most `(q_m + 2) / p`. -/
theorem jDist_sz_le (hgen : CGR.gen ≠ CGR.one) (qm : ℕ) (χ : CGR.Exp) (γ : ParExp G n)
    (vkey : MacN.Key G n) :
    ∀ (A' : OracleAdv (SymQ G n) (Ans G) (SymOut G n)) (m : ℕ) (FV : List (VEntry G n))
      (k : ℕ), FV.length = k → A'.IsQueryBoundBy macCost m → k + m ≤ qm →
      (jDist qm χ γ vkey A' FV k).toOuterMeasure (szSet χ γ vkey) ≤
        ((qm + 2 : ℕ) : ℝ≥0∞) * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by
  classical
  intro A'
  induction A' with
  | ret o =>
    intro m FV k hk _ hkm
    subst hk
    set φ0 := forgeryForm γ (attachL χ FV (List.replicate FV.length 0)) o with hφ0
    have hjd : jDist qm χ γ vkey (.ret o) FV FV.length =
        (PMF.uniformFintype (MacN.Key G n × (Fin FV.length → CGR.Exp))).map
          fun x => (x.1, (o, attachL χ FV (List.ofFn x.2))) := by
      rw [PMF.uniform_prod_eq_bind, PMF.map_bind]
      simp only [jDist, OracleAdv.run_ret, PMF.pure_map, PMF.map_comp]
      congr 1
    rw [hjd, PMF.toOuterMeasure_map_apply]
    have hsub : (fun x : MacN.Key G n × (Fin FV.length → CGR.Exp) =>
        (x.1, (o, attachL χ FV (List.ofFn x.2)))) ⁻¹' szSet χ γ vkey ⊆
        {x | φ0 ≠ 0 ∧ MvPolynomial.eval (valsV vkey FV + embAt FV.length x.1 x.2) φ0 = 0} := by
      intro x hx
      simp only [szSet, SZEvent, Set.mem_preimage, Set.mem_ofPred_eq] at hx
      rw [valsAt_succ_attachL, forgeryForm_attachL γ χ FV (List.ofFn x.2)
        (List.replicate FV.length 0) (by simp) (by simp) o] at hx
      exact hx
    refine (MeasureTheory.measure_mono hsub).trans ?_
    have hsupp := forgeryForm_mem_supported γ (attachL χ FV (List.replicate FV.length 0)) o
    rw [length_attachL χ FV _ (by simp)] at hsupp
    have hdeg := totalDegree_forgeryForm_le γ (attachL χ FV (List.replicate FV.length 0)) o
    rw [length_attachL χ FV _ (by simp), ← hφ0] at hdeg
    refine (sz_shift_le hgen FV.length φ0 hsupp (valsV vkey FV)).trans ?_
    gcongr
    exact_mod_cast (show φ0.totalDegree ≤ qm + 2 by omega)
  | rand p k' ih =>
    intro m FV k hk hA hkm
    have h : jDist qm χ γ vkey (.rand p k') FV k =
        p.bind fun x => jDist qm χ γ vkey (k' x) FV k := by
      simp only [jDist, OracleAdv.run_rand, PMF.map_bind]
      conv_lhs => arg 2; ext b; rw [PMF.bind_comm]
      rw [PMF.bind_comm]
    rw [h]
    exact bind_toOuterMeasure_le _ _ _ _ fun x => ih x m FV k hk (hA x) hkm
  | query d k' ih =>
    intro m FV k hk hA hkm
    obtain ⟨hc, hk'⟩ := hA
    rcases d with M | q
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp only [macCost] at hc; omega⟩
      have h : jDist qm χ γ vkey (.query (.inl M) k') FV k =
          (PMF.uniformFintype (CGR.Exp × CGR.Exp)).bind fun tv =>
            jDist qm χ γ vkey (k' (macAnsView γ vkey FV M tv.1 tv.2))
              (FV ++ [(M, tv.1, tv.2)]) (k + 1) := by
        subst hk
        have hS : ∀ (b : MacN.Key G n) (z : Fin FV.length → CGR.Exp),
            simF (kDLChallenge G (qm + 2) χ) γ.1 (keyPolys (vkey - kshift χ b) b)
              (basisPolys0 expOne γ (keyPolys (vkey - kshift χ b) b))
              (attachL χ FV (List.ofFn z)) (.inl M) =
            (PMF.uniformFintype (CGR.Exp × CGR.Exp × CGR.Exp)).map fun r =>
              (macAnsView γ vkey FV M r.1 r.2.1,
                attachL χ (FV ++ [(M, r.1, r.2.1)]) (List.ofFn z ++ [r.2.2])) :=
          fun b z => simF_inl_attachL qm χ γ vkey b FV (List.ofFn z) (by simp) (by omega) M
        simp only [jDist, OracleAdv.run_query, hS, PMF.bind_map, uniform_triple_bind,
          PMF.map_bind, uniform_snoc_bind]
        conv_lhs => arg 2; ext b; rw [PMF.bind_comm]
        conv_lhs => rw [PMF.bind_comm]
        refine congrArg _ (funext fun tv => congrArg _ (funext fun b => congrArg _
          (funext fun z => congrArg _ (funext fun c => ?_))))
        simp only [Function.comp_apply, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
          List.concat_eq_append]
      rw [h]
      refine bind_toOuterMeasure_le _ _ _ _ fun tv => ih _ m' _ (k + 1) (by simp [hk]) ?_ (by omega)
      simpa [macCost] using hk' _
    · have h : jDist qm χ γ vkey (.query (.inr q) k') FV k =
          jDist qm χ γ vkey (k' (ansView γ vkey FV q)) FV k := by
        subst hk
        simp only [jDist, OracleAdv.run_query]
        congr 1
        funext b
        congr 1
        funext z
        rw [simF_inr_attachL hgen qm χ γ vkey b FV (List.ofFn z) (by simp) (by omega) q,
          PMF.pure_bind]
      rw [h]
      exact ih _ m FV k hk (by simpa [macCost] using hk' _) hkm

omit [DecidableEq CGR.Exp] in
/-- **The Schwartz–Zippel step.** For a generator `g ≠ 1` and an adversary with at most `q_m`
MAC queries, the formal forgery equation is nonzero and vanishes at `v ↦ a_v + b_v (χ + 1)`
with probability at most `(q_m + 2) / p`: given the view of the adversary, the coefficients
`b` are uniform, so the point is uniform, and the equation has degree at most `q_m + 2`. -/
theorem forgeryPoly_ne_zero_prob (hgen : CGR.gen ≠ CGR.one) (qm : ℕ) (A : AlgAdv G n)
    (hA : ∀ p pk, (A p pk).IsQueryBoundBy macCost qm) :
    (experiment (qm + 2) A).toOuterMeasure {ω | SZEvent ω} ≤
      ((qm + 2 : ℕ) : ℝ≥0∞) * (Fintype.card CGR.Exp : ℝ≥0∞)⁻¹ := by
  refine bind_toOuterMeasure_le _ _ _ _ fun χ => ?_
  refine bind_toOuterMeasure_le _ _ _ _ fun γ => ?_
  let E2 : MacN.Key G n × MacN.Key G n ≃ MacN.Key G n × MacN.Key G n :=
    { toFun := fun x => (x.1 - kshift χ x.2, x.2)
      invFun := fun x => (x.1 + kshift χ x.2, x.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  rw [← PMF.uniformFintype_map_equiv E2, PMF.bind_map, PMF.uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map]
  refine bind_toOuterMeasure_le _ _ _ _ fun vkey => ?_
  have h : (PMF.uniformFintype (MacN.Key G n)).bind
      (((fun ab => (runF (qm + 2) A χ γ ab).map fun y => (χ, γ, ab, y)) ∘ E2) ∘ Prod.mk vkey) =
      (jDist qm χ γ vkey (A (parOf γ) (iparams (parOf γ) vkey)) [] 0).map
        fun x => (χ, γ, (vkey - kshift χ x.1, x.1), x.2) := by
    simp only [jDist, runF, PMF.map_bind, PMF.map_comp, E2, Equiv.coe_fn_mk]
    congr 1
    funext b
    have h0 : ∀ z : Fin 0 → CGR.Exp, attachL χ ([] : List (VEntry G n)) (List.ofFn z) = [] :=
      fun z => by simp [attachL]
    simp only [h0, PMF.bind_const, Function.comp_apply, keyAt_kshift]
    rfl
  rw [h, PMF.toOuterMeasure_map_apply]
  exact jDist_sz_le hgen qm χ γ vkey _ qm [] 0 rfl (hA _ _) (by omega)

/-! ## The target theorem -/

/-- **suf-cmva-Help of `MAC_n` in the algebraic group model.** For a generator `g ≠ 1`, an
algebraic adversary `A` with at most `q_m` MAC queries and a root finder `RF` of the exponent
ring, with `p` the order of the group:

`Adv ≤ Adv^dl(B_z (A.toAdv)) + Adv^{(q_m+2)-dl}(B_alg A) + (q_m + 5) / p + q_m (q_m - 1) / (2 p)`,

where `B_z = reductionZ` and `B_alg = reductionAlg expOne RF.roots`. -/
theorem macN_sufCmvaHelpAGM_le (hgen : CGR.gen ≠ CGR.one) (qm : ℕ) (A : AlgAdv G n)
    (hA : ∀ p pk, (A p pk).IsQueryBoundBy macCost qm) (RF : RootFinder G) :
    sufCmvaHelpAGM_Advantage A ≤
      DL_Advantage (reductionZ A.toAdv) +
        KDL_Advantage G (qm + 2) (reductionAlg expOne RF.roots A) +
          ((qm + 2 + 3 : ℕ) : ℝ≥0∞) / (Fintype.card CGR.Exp : ℝ≥0∞) +
            ((qm * (qm - 1) : ℕ) : ℝ≥0∞) / (2 * (Fintype.card CGR.Exp : ℝ≥0∞)) := by
  set p : ℝ≥0∞ := (Fintype.card CGR.Exp : ℝ≥0∞) with hp
  set μ := (experiment (qm + 2) A).toOuterMeasure with hμ
  let fw : MacN.Par G n → MacN.Key G n → ((macN G n).Msg × (macN G n).Tag) × (macN G n).Log →
      Bool := fun par k y => (macN G n).verify par k y.1.1 y.1.2 && (macN G n).strongFresh y.1 y.2
  let fz : MacN.Par G n → MacN.Key G n → ((macN G n).Msg × (macN G n).Tag) × (macN G n).Log →
      Bool := fun par k y => fw par k y &&
        decide (CyclicGroup.elemPow (gx0 par) (y.1.2 : CGR.Exp × G × G).1 = gx1 par)
  have hW := game_eq_experiment hgen qm A hA fw
  have hZ := game_eq_experiment hgen qm A hA fz
  have hAdv : sufCmvaHelpAGM_Advantage A = μ {ω | fw (parOf ω.2.1)
      (keyAt (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.1) (gameOut ω) = true} := by
    rw [← hW, sufCmvaHelpAGM_Advantage]
    unfold AlgMac.SUFCMVAHelp_Advantage AlgMac.sufCmvaHelpGame AlgMac.forgeGame
    rw [prTrue_liftPMF]
    rfl
  have hz : μ {ω | fz (parOf ω.2.1) (keyAt (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.1) (gameOut ω) = true}
      ≤ DL_Advantage (reductionZ A.toAdv) := by
    rw [← hZ]
    refine le_of_eq_of_le ?_ (reductionZ_bound hgen A.toAdv)
    rw [zEventGame, prTrue_liftPMF]
  have hsub : {ω : Outcome G n | fw (parOf ω.2.1) (keyAt (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.1)
      (gameOut ω) = true} ⊆
      {ω | fz (parOf ω.2.1) (keyAt (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.1) (gameOut ω) = true} ∪
        ((({ω | KDLEvent ω} ∪ {ω | BadPar ω}) ∪ {ω | TColl ω}) ∪ {ω | SZEvent ω}) := by
    intro ω hω
    by_cases hzω : CyclicGroup.elemPow (gx0 (parOf ω.2.1)) ω.2.2.2.1.2.1 = gx1 (parOf ω.2.1)
    · left
      simp only [Set.mem_ofPred_eq, fz, Bool.and_eq_true, decide_eq_true_eq] at hω ⊢
      exact ⟨hω, hzω⟩
    · right
      rcases win_cases hgen ω hω hzω with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  have hsum : ((∑ j ∈ Finset.range qm, j : ℕ) : ℝ≥0∞) * p⁻¹ =
      ((qm * (qm - 1) : ℕ) : ℝ≥0∞) / (2 * p) := by
    have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
    rw [← Finset.sum_range_id_mul_two, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    calc ((∑ j ∈ Finset.range qm, j : ℕ) : ℝ≥0∞) * p⁻¹ =
        ((∑ j ∈ Finset.range qm, j : ℕ) : ℝ≥0∞) * (2 * 2⁻¹) * p⁻¹ := by rw [h2, mul_one]
      _ = _ := by ring
  rw [hAdv]
  calc _ ≤ μ ({ω | fz (parOf ω.2.1) (keyAt (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.1) (gameOut ω) = true}
          ∪ ((({ω | KDLEvent ω} ∪ {ω | BadPar ω}) ∪ {ω | TColl ω}) ∪ {ω | SZEvent ω})) :=
        MeasureTheory.measure_mono hsub
    _ ≤ μ {ω | fz (parOf ω.2.1) (keyAt (keyPolys ω.2.2.1.1 ω.2.2.1.2) ω.1) (gameOut ω) = true}
          + (((μ {ω | KDLEvent ω} + μ {ω | BadPar ω}) + μ {ω | TColl ω}) + μ {ω | SZEvent ω}) := by
        refine (MeasureTheory.measure_union_le _ _).trans ?_
        gcongr
        refine (MeasureTheory.measure_union_le _ _).trans ?_
        gcongr
        refine (MeasureTheory.measure_union_le _ _).trans ?_
        gcongr
        exact MeasureTheory.measure_union_le _ _
    _ ≤ DL_Advantage (reductionZ A.toAdv) +
          (((KDL_Advantage G (qm + 2) (reductionAlg expOne RF.roots A) + 3 * p⁻¹) +
            ((∑ j ∈ Finset.range qm, j : ℕ) : ℝ≥0∞) * p⁻¹) + ((qm + 2 : ℕ) : ℝ≥0∞) * p⁻¹) := by
        gcongr
        · exact kdlEvent_le hgen qm A RF
        · exact badPar_le (qm + 2) A
        · exact tColl_le (qm + 2) qm A hA
        · exact forgeryPoly_ne_zero_prob hgen qm A hA
    _ = _ := by
        rw [hsum, div_eq_mul_inv ((qm + 2 + 3 : ℕ) : ℝ≥0∞)]
        push_cast
        ring

end CatCrypt.Crypto.KVAC.MacNHelpAGM
