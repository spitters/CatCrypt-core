/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.GenericGroup
public import CatCryptCore.Crypto.MLKEM.MLKEM512Params
public import CatCryptCore.Crypto.KeyAgreement.MontgomeryLadder
public import CatCryptCore.Crypto.KeyAgreement.MontgomeryXOnly
import CatCryptCore.Complexity.D.FreeThm

/-!
# Free theorems of D for code of the workspace

Applications of the command `free_theorem` to definitions of the workspace, in its three shapes.

* Non-interference. The message decoding and encoding of ML-KEM (`MLKEM512Instance.compress1`,
  `MLKEM512Instance.decompress1`) are reflected by `reflect_d`, and their free theorems are
  refused: `Compress₁` compares the natural number `x.val` of the secret coefficient, whose
  primitive `natLt` costs the length of its arguments, and `Decompress₁` branches on the secret
  bit. The refusals are checked here.
* Commutation with a homomorphism. The Montgomery ladder of the key agreement
  (`CatCrypt.Crypto.ECC.ladderFold`) over a generic group, as the term `ladderT` of D: it
  commutes with every homomorphism at equal cost, and its number of steps, two group operations
  per bit, does not depend on the bits.
* Representation independence. The x-only doubling `CatCrypt.Crypto.ECC.xdbl a24 (x, 1)` of
  Curve25519, as the term `xdblT` over the field operations: on two environments of operations
  related by the graph of an encoding, its results are related by the encoding, at equal cost.
* Timing non-interference with secret field elements (`noninterference_ops`). With the field
  secret, `xdblT` and, for public bits, `ladderT` take the same number of steps on any two
  inputs and on any two environments of operations of the same costs. With the bits secret the
  ladder is refused at its branch on the bit; the refusal is checked here.

## Main results

* `Prim.respB_secret_of_cost` — a primitive of constant cost with a secret result respects the
  relation of the secret types;
* `ladderSpec_addOps` — the ladder over the operations of an additive group is
  `CatCrypt.Crypto.ECC.ladderFold`;
* `ladderT_eval`, `ladderT_cost`, `ladderT_commute` — the ladder in D: its value, its number of
  steps and its commutation with homomorphisms;
* `xdblEnv_secret_rel`, `homEnv_secret_rel` — environments of operations of fixed cost over a
  secret field or group are related by the relation of the secret types;
* `xdblT_ni`, `xdblT_cost_secret`, `ladderT_ni`, `ladderT_cost_secret` — timing
  non-interference of x-only doubling and of the ladder with the field elements secret: equal
  cost on any two secret inputs and any two operations of the same costs;
* `xdblT_eval`, `xdblT_eval_ring`, `xdblT_rep` — x-only doubling in D: its value and number of
  steps, its value over a commutative ring, and its representation independence.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

/-! ## Primitives with a secret result -/

/-- A primitive whose result is of a secret type and whose cost is constant respects the
relation of the secret types. -/
theorem Prim.respB_secret_of_cost {Sec : FTy → Prop} {a : Ty} {f : FTy} (p : Prim a (.base f))
    (hf : Sec f) (hc : ∀ u v, p.cost u = p.cost v) : p.RespB (BRel.secret Sec) :=
  fun u v _ => ⟨Or.inl hf, hc u v⟩

/-- A comparison of residues with a secret result respects the relation of the secret types. -/
@[resp_b] theorem Prim.respB_finLt_secret {Sec : FTy → Prop} (n : ℕ) (hb : Sec .bool) :
    (Prim.finLt n).RespB (BRel.secret Sec) :=
  Prim.respB_secret_of_cost _ hb fun _ _ => rfl

/-- The conjunction of secret booleans respects the relation of the secret types. -/
@[resp_b] theorem Prim.respB_band_secret {Sec : FTy → Prop} (hb : Sec .bool) :
    Prim.band.RespB (BRel.secret Sec) :=
  Prim.respB_secret_of_cost _ hb fun _ _ => rfl

/-- The negation of a secret boolean respects the relation of the secret types. -/
@[resp_b] theorem Prim.respB_bnot_secret {Sec : FTy → Prop} (hb : Sec .bool) :
    Prim.bnot.RespB (BRel.secret Sec) :=
  Prim.respB_secret_of_cost _ hb fun _ _ => rfl

namespace FreeThmApps

open GenericGroup

/-! ## Timing non-interference of the ML-KEM message coding: refusals

With the coefficients and the bits secret, `Compress₁` is refused at the comparison `natLt` of
the natural number `x.val`, whose cost depends on its length. With the bits secret,
`Decompress₁` is refused at its branch on the bit. -/

/--
error: resp_b: no registered lemma closes the obligation
  Prim.RespB (BRel.secret Sec) Prim.natLt
-/
#guard_msgs in
free_theorem compress1_ni {Sec : FTy → Prop} (hs : Sec (.fin 3328)) (hb : Sec .bool)
  for reflect_d CatCrypt.Crypto.MLKEM.MLKEM512Instance.compress1 at noninterference hs

/--
error: resp_b: no registered lemma closes the obligation
  ∀ (b b' : FTy.bool.den), BRel.secret Sec FTy.bool b b' → b = b'
-/
#guard_msgs in
free_theorem decompress1_ni {Sec : FTy → Prop} (hb : Sec .bool) (hs : ¬ Sec (.fin 3328))
  for reflect_d CatCrypt.Crypto.MLKEM.MLKEM512Instance.decompress1 at noninterference hb

/-! ## The Montgomery ladder over a generic group -/

/-- The Montgomery ladder over the operations `M`: from `(1, x)`, each bit `b` sends `(R₀, R₁)`
to `(R₀ R₁, R₁²)` when `b` is set and to `(R₀², R₀ R₁)` otherwise. -/
def ladderSpec {X : Type} (M : GrpOps X) (x : X) (bits : List Bool) : X × X :=
  bits.foldl (fun acc b => bif b then (M.mul acc.1 acc.2, M.mul acc.2 acc.2)
    else (M.mul acc.1 acc.1, M.mul acc.1 acc.2)) (M.one, x)

/-- The operations of an additive group: addition, negation and zero. -/
def addOps (X : Type) [AddGroup X] : GrpOps X := ⟨(· + ·), (- ·), 0⟩

/-- Over the operations of an additive commutative group, the ladder is the Montgomery ladder
`CatCrypt.Crypto.ECC.ladderFold` of the key agreement, run on the reversed bits. -/
theorem ladderSpec_addOps {X : Type} [AddCommGroup X] (x : X) (bits : List Bool) :
    ladderSpec (addOps X) x bits = CatCrypt.Crypto.ECC.ladderFold x bits.reverse := by
  have h : ∀ l : List Bool, CatCrypt.Crypto.ECC.ladderFold x l =
      l.foldr (fun b acc => CatCrypt.Crypto.ECC.ladderStep acc b) (0, x) := by
    intro l
    induction l with
    | nil => rfl
    | cons b l ih => simp [CatCrypt.Crypto.ECC.ladderFold, ih]
  rw [h, List.foldr_reverse]
  simp only [ladderSpec, addOps]
  congr 1
  funext acc b
  obtain ⟨r₀, r₁⟩ := acc
  cases b <;> rfl

/-- The step of the ladder on the pair `((R₀, R₁), b)`, over the bits, the base and the group
operations. -/
def ladderStepT (g : FTy) :
    Tm (.prod (.prod (el g) (el g)) .bool :: .list .bool :: el g :: homCtx g)
      (.prod (el g) (el g)) :=
  .ite (.snd (.var .here))
    (.pair
      (.app (.var (.there (.there (.there .here))))
        (.pair (.fst (.fst (.var .here))) (.snd (.fst (.var .here)))))
      (.app (.var (.there (.there (.there .here))))
        (.pair (.snd (.fst (.var .here))) (.snd (.fst (.var .here))))))
    (.pair
      (.app (.var (.there (.there (.there .here))))
        (.pair (.fst (.fst (.var .here))) (.fst (.fst (.var .here)))))
      (.app (.var (.there (.there (.there .here))))
        (.pair (.fst (.fst (.var .here))) (.snd (.fst (.var .here))))))

/-- The Montgomery ladder as a term of D over the bits, the base and the group operations: the
first component of the fold of `ladderStepT` from `(1, x)`. -/
def ladderT (g : FTy) : Tm (.list .bool :: el g :: homCtx g) (el g) :=
  .fst (.foldl (.lam (ladderStepT g))
    (.pair (.var (.there (.there (.there (.there .here))))) (.var (.there .here))) (.var .here))

/-- One step of the ladder: the next pair after `2 m + 3` steps, for multiplication cost `m`,
whatever the bit. -/
theorem ladderStepT_eval {g : FTy} (M : GrpOps g.den) (c : OpCost) (x : g.den)
    (bits : List Bool) (r₀ r₁ : g.den) (b : Bool) :
    (ladderStepT g).eval (Env.cons (τ := .prod (.prod (el g) (el g)) .bool) ((r₀, r₁), b)
        (powEnv g M c x bits)) =
      stepN CTree.tick (2 * c.mul + 3) (CTree.ret (α := Val (.prod (el g) (el g)))
        (bif b then (M.mul r₀ r₁, M.mul r₁ r₁)
          else (M.mul r₀ r₀, M.mul r₀ r₁))) := by
  rw [show 2 * c.mul + 3 = 1 + (1 + (c.mul + (1 + (c.mul + 0)))) by omega]
  simp only [← Reflect.stepN_tick_add]
  cases b
  · change CTree.tick ((CTree.tick (stepN CTree.tick c.mul (.ret (M.mul r₀ r₀)))).bind
        fun u => (CTree.tick (stepN CTree.tick c.mul (.ret (M.mul r₀ r₁)))).bind
          fun v => .ret (u, v)) = _
    simp only [CTree.bind_tick, Reflect.stepN_ret_bind]
    rfl
  · change CTree.tick ((CTree.tick (stepN CTree.tick c.mul (.ret (M.mul r₀ r₁)))).bind
        fun u => (CTree.tick (stepN CTree.tick c.mul (.ret (M.mul r₁ r₁)))).bind
          fun v => .ret (u, v)) = _
    simp only [CTree.bind_tick, Reflect.stepN_ret_bind]
    rfl

/-- The fold of the ladder from a pair: `l.length · (2 m + 4)` steps. -/
theorem ladderT_foldT {g : FTy} (M : GrpOps g.den) (c : OpCost) (x : g.den)
    (bits : List Bool) :
    ∀ (l : List Bool) (acc : g.den × g.den),
      foldT CTree.tick (a := .bool) (c := .prod (el g) (el g))
          (fun v => (ladderStepT g).eval (Env.cons v (powEnv g M c x bits))) acc l =
        stepN CTree.tick (l.length * (2 * c.mul + 4)) (CTree.ret (α := Val (.prod (el g) (el g)))
          (l.foldl (fun acc b => bif b then (M.mul acc.1 acc.2, M.mul acc.2 acc.2)
            else (M.mul acc.1 acc.1, M.mul acc.1 acc.2)) acc)) := by
  intro l
  induction l with
  | nil =>
    intro acc
    rw [List.length_nil, Nat.zero_mul]
    rfl
  | cons b l ih =>
    intro acc
    obtain ⟨r₀, r₁⟩ := acc
    change (CTree.tick ((ladderStepT g).eval
      (Env.cons (τ := .prod (.prod (el g) (el g)) .bool) ((r₀, r₁), b)
        (powEnv g M c x bits)))).bind _ = _
    rw [ladderStepT_eval, CTree.bind_tick, Reflect.stepN_ret_bind]
    erw [ih]
    rw [Reflect.stepN_tick_add, show (b :: l).length * (2 * c.mul + 4) =
      (2 * c.mul + 3 + l.length * (2 * c.mul + 4)) + 1 by simp only [List.length_cons]; ring]
    rfl

/-- The ladder returns the first component of `ladderSpec` after `n · (2 m + 4)` steps for `n`
bits and multiplication cost `m`. -/
theorem ladderT_eval {g : FTy} (M : GrpOps g.den) (c : OpCost) (x : g.den)
    (bits : List Bool) :
    (ladderT g).eval (powEnv g M c x bits) =
      stepN CTree.tick (bits.length * (2 * c.mul + 4)) (.ret (ladderSpec M x bits).1) := by
  change (foldT CTree.tick (a := .bool) (c := .prod (el g) (el g))
      (fun v => (ladderStepT g).eval (Env.cons v (powEnv g M c x bits))) (M.one, x) bits).bind
    (fun v => .ret v.1) = _
  erw [ladderT_foldT, Reflect.stepN_ret_bind]
  rfl

/-- The number of steps of the ladder, `n · (2 m + 4)` for `n` bits: two group operations per
bit, whatever the bits. -/
theorem ladderT_cost {g : FTy} (M : GrpOps g.den) (c : OpCost) (x : g.den)
    (bits : List Bool) :
    ((ladderT g).eval (powEnv g M c x bits)).cost = bits.length * (2 * c.mul + 4) := by
  rw [ladderT_eval]
  exact (cost_stepN_tick (α := g.den) _ _).trans (Nat.add_zero _)

/-- The Montgomery ladder commutes with every homomorphism `φ` of a group other than `bool`, at
equal cost: on the base `φ x` over the operations `N` it returns the image under `φ` of its
result on `x` over `M`, in the same number of steps. -/
free_theorem ladderT_commute {g : FTy} {φ : g.den → g.den} {M N : GrpOps g.den}
  (hφ : M.IsHom N φ) (hg : FTy.bool ≠ g) for ladderT g at hom_commute hφ

/-! ## x-only doubling on two representations of the field -/

/-- The type of a binary operation of D on the field `g`. -/
abbrev binop (g : FTy) : Ty := .arr (.prod (el g) (el g)) (el g)

/-- The context of x-only doubling: multiplication, subtraction, addition, the curve constant
`a24` and the unit, innermost first. -/
abbrev xdblCtx (g : FTy) : List Ty := [binop g, binop g, binop g, el g, el g]

/-- x-only doubling of the affine point `(x : 1)` (`CatCrypt.Crypto.ECC.xdbl a24 (x, 1)`) as a
term of D over the field operations of `xdblCtx`: with `a = x + 1`, `b = x - 1`, the result is
`(a² b², (a² - b²) (b² + a24 (a² - b²)))`. -/
def xdblT (g : FTy) : Tm (el g :: xdblCtx g) (.prod (el g) (el g)) :=
  .letE (.app (.var (.there (.there (.there .here))))
      (.pair (.var .here) (.var (.there (.there (.there (.there (.there .here))))))))
  (.letE (.app (.var (.there (.there (.there .here))))
      (.pair (.var (.there .here))
        (.var (.there (.there (.there (.there (.there (.there .here)))))))))
  (.letE (.app (.var (.there (.there (.there .here))))
      (.pair (.var (.there .here)) (.var (.there .here))))
  (.letE (.app (.var (.there (.there (.there (.there .here)))))
      (.pair (.var (.there .here)) (.var (.there .here))))
  (.letE (.app (.var (.there (.there (.there (.there (.there (.there .here)))))))
      (.pair (.var (.there .here)) (.var .here)))
  (.pair
    (.app (.var (.there (.there (.there (.there (.there (.there .here)))))))
      (.pair (.var (.there (.there .here))) (.var (.there .here))))
    (.app (.var (.there (.there (.there (.there (.there (.there .here)))))))
      (.pair (.var .here)
        (.app (.var (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
          (.pair (.var (.there .here))
            (.app (.var (.there (.there (.there (.there (.there (.there .here)))))))
              (.pair (.var (.there (.there (.there (.there (.there (.there (.there (.there
                (.there .here))))))))))
                (.var .here))))))))))))

/-- An environment of `xdblCtx`: multiplication at `cm` steps, subtraction and addition at
`cs` steps, the constant `a24` and the unit. -/
def xdblEnv (g : FTy) (mul sub add : g.den → g.den → g.den) (a24 one : g.den) (cm cs : ℕ) :
    Env (xdblCtx g) :=
  Env.cons (τ := binop g) (fun p : g.den × g.den => opT cm (mul p.1 p.2))
    (Env.cons (τ := binop g) (fun p : g.den × g.den => opT cs (sub p.1 p.2))
      (Env.cons (τ := binop g) (fun p : g.den × g.den => opT cs (add p.1 p.2))
        (Env.cons (τ := el g) a24 (Env.cons (τ := el g) one Env.nil))))

/-- The unfolding of `stepN` at a successor, read from the outside. -/
private theorem tick_stepN {α : Type} (n : ℕ) (t : CTree α) :
    CTree.tick (stepN CTree.tick n t) = stepN CTree.tick (n + 1) t := rfl

/-- x-only doubling returns the doubled point after `5 cm + 4 cs + 14` steps: five
multiplications, four additions or subtractions and five bindings. -/
theorem xdblT_eval (g : FTy) (mul sub add : g.den → g.den → g.den) (a24 one : g.den)
    (cm cs : ℕ) (x : g.den) :
    (xdblT g).eval (Env.cons (τ := el g) x (xdblEnv g mul sub add a24 one cm cs)) =
      stepN CTree.tick (5 * cm + 4 * cs + 14) (CTree.ret (α := Val (.prod (el g) (el g)))
        (mul (mul (add x one) (add x one)) (mul (sub x one) (sub x one)),
          mul (sub (mul (add x one) (add x one)) (mul (sub x one) (sub x one)))
            (add (mul (sub x one) (sub x one))
              (mul a24 (sub (mul (add x one) (add x one)) (mul (sub x one) (sub x one))))))) := by
  change (CTree.tick (opT cs (add x one))).bind (fun a =>
    CTree.tick ((CTree.tick (opT cs (sub x one))).bind fun b =>
    CTree.tick ((CTree.tick (opT cm (mul a a))).bind fun aa =>
    CTree.tick ((CTree.tick (opT cm (mul b b))).bind fun bb =>
    CTree.tick ((CTree.tick (opT cs (sub aa bb))).bind fun c =>
    CTree.tick ((CTree.tick (opT cm (mul aa bb))).bind fun u =>
      ((((((CTree.tick (opT cm (mul a24 c))).bind fun v => CTree.ret (bb, v)).bind
        fun v => CTree.tick (opT cs (add v.1 v.2))).bind fun v => CTree.ret (c, v)).bind
        fun v => CTree.tick (opT cm (mul v.1 v.2))).bind fun v =>
          CTree.ret (α := Val (.prod (el g) (el g))) (u, v)))))))) = _
  simp only [opT, Reflect.stepN_ret_bind, tick_stepN, Reflect.stepN_tick_add]
  congr 1
  ring

/-- Over a commutative ring with unit operations, `xdblT_eval` returns
`CatCrypt.Crypto.ECC.xdbl a24 (x, 1)`. -/
theorem xdblT_eval_ring (g : FTy) [CommRing g.den] (a24 : g.den) (cm cs : ℕ) (x : g.den) :
    (xdblT g).eval (Env.cons (τ := el g) x
        (xdblEnv g (· * ·) (· - ·) (· + ·) a24 1 cm cs)) =
      stepN CTree.tick (5 * cm + 4 * cs + 14) (CTree.ret (α := Val (.prod (el g) (el g)))
        (CatCrypt.Crypto.ECC.xdbl (F := g.den) a24 (x, 1))) := by
  rw [xdblT_eval]
  rfl

/-- Representation independence of x-only doubling: on two environments of field operations
related by the graph of an encoding `φ`, the doubling of `x` and of `φ x` give results related
componentwise by `φ`, in the same number of steps. -/
free_theorem xdblT_rep {g : FTy} {φ : g.den → g.den} {ρ δ : Env (xdblCtx g)}
  (h : EnvRelB (homRel g φ) ρ δ) for xdblT g at rep_independence h

/-! ## Timing non-interference with secret field elements

With the field (or the group) secret, x-only doubling and the ladder are timing
non-interfering: their cost depends neither on the field inputs nor on the operations, as long
as the operations have fixed costs. With the bits of the ladder secret, the ladder is refused at
its branch on the bit. -/

/-- Two environments of the field operations of `xdblCtx` at equal costs are related by the
relation of the secret types when the field is secret, whatever the operations and constants. -/
theorem xdblEnv_secret_rel {Sec : FTy → Prop} {g : FTy} (hg : Sec g)
    (mul sub add mul' sub' add' : g.den → g.den → g.den) (a24 one a24' one' : g.den)
    (cm cs : ℕ) :
    EnvRelB (BRel.secret Sec) (xdblEnv g mul sub add a24 one cm cs)
      (xdblEnv g mul' sub' add' a24' one' cm cs) := by
  have he : ∀ a b : g.den, Ty.relB (BRel.secret Sec) (el g) a b := fun _ _ => Or.inl hg
  have hop : ∀ (k : ℕ) (f f' : g.den → g.den → g.den), Ty.relB (BRel.secret Sec) (binop g)
      (fun p : g.den × g.den => opT k (f p.1 p.2))
      (fun p : g.den × g.den => opT k (f' p.1 p.2)) :=
    fun _ _ _ _ _ _ => stepN_lift (.ret (he _ _)) _
  have hnil : EnvRelB (BRel.secret Sec) Env.nil Env.nil := fun _ x => by cases x
  exact ((((hnil.cons (he one one')).cons (he a24 a24')).cons (hop cs add add')).cons
    (hop cs sub sub')).cons (hop cm mul mul')

/-- Two environments of group operations at equal costs are related by the relation of the
secret types when the group is secret, whatever the operations. -/
theorem homEnv_secret_rel {Sec : FTy → Prop} {g : FTy} (hg : Sec g) (M N : GrpOps g.den)
    (c : OpCost) : EnvRelB (BRel.secret Sec) (homEnv g M c) (homEnv g N c) := by
  have he : ∀ a b : g.den, Ty.relB (BRel.secret Sec) (el g) a b := fun _ _ => Or.inl hg
  have hnil : EnvRelB (BRel.secret Sec) Env.nil Env.nil := fun _ x => by cases x
  have hinv : Ty.relB (BRel.secret Sec) (.arr (el g) (el g))
      (fun a : g.den => opT c.inv (M.inv a)) (fun a : g.den => opT c.inv (N.inv a)) :=
    fun _ _ _ => stepN_lift (.ret (he _ _)) _
  have hmul : Ty.relB (BRel.secret Sec) (.arr (.prod (el g) (el g)) (el g))
      (fun p : g.den × g.den => opT c.mul (M.mul p.1 p.2))
      (fun p : g.den × g.den => opT c.mul (N.mul p.1 p.2)) :=
    fun _ _ _ => stepN_lift (.ret (he _ _)) _
  exact ((hnil.cons (he M.one N.one)).cons hinv).cons hmul

/-- Timing non-interference of x-only doubling with the field secret: on two environments of
operations related by the relation of the secret types, any two inputs give runs of equal
cost, and equal trees when the result type is public. -/
free_theorem xdblT_ni {Sec : FTy → Prop} {g : FTy} (hg : Sec g) {ρ δ : Env (xdblCtx g)}
  (h : EnvRelB (BRel.secret Sec) ρ δ) for xdblT g at noninterference_ops h hg

/-- x-only doubling takes the same number of steps on any two field inputs and any two choices
of operations and constants at the same costs. -/
theorem xdblT_cost_secret {g : FTy} (mul sub add mul' sub' add' : g.den → g.den → g.den)
    (a24 one a24' one' : g.den) (cm cs : ℕ) (x x' : g.den) :
    ((xdblT g).eval (Env.cons (τ := el g) x (xdblEnv g mul sub add a24 one cm cs))).cost =
      ((xdblT g).eval
        (Env.cons (τ := el g) x' (xdblEnv g mul' sub' add' a24' one' cm cs))).cost :=
  (xdblT_ni (Sec := (· = g)) rfl
    (xdblEnv_secret_rel (Sec := (· = g)) rfl mul sub add mul' sub' add' a24 one a24' one' cm
      cs) x x').1

/-- Timing non-interference of the ladder with the base secret and the bits public: on two
environments of group operations related by the relation of the secret types, the same bits
and any two bases give runs of equal cost, and equal trees when the result type is public. -/
free_theorem ladderT_ni {Sec : FTy → Prop} {g : FTy} (hg : Sec g) (hb : ¬ Sec .bool)
  {ρ δ : Env (homCtx g)} (h : EnvRelB (BRel.secret Sec) ρ δ)
  for ladderT g at noninterference_ops h _ hg

/-- The ladder takes the same number of steps on any two bases and any two group operations
at the same costs, for the same bits. -/
theorem ladderT_cost_secret {g : FTy} (hg : FTy.bool ≠ g) (M N : GrpOps g.den) (c : OpCost)
    (bits : List Bool) (x x' : g.den) :
    ((ladderT g).eval (powEnv g M c x bits)).cost =
      ((ladderT g).eval (powEnv g N c x' bits)).cost :=
  (ladderT_ni (Sec := (· = g)) rfl hg (homEnv_secret_rel (Sec := (· = g)) rfl M N c) bits x x').1

/--
error: resp_b: no registered lemma closes the obligation
  ∀ (b b' : FTy.bool.den), BRel.secret Sec FTy.bool b b' → b = b'
-/
#guard_msgs in
free_theorem ladderT_ni_bits {Sec : FTy → Prop} {g : FTy} (hb : Sec .bool)
  {ρ δ : Env (.list .bool :: el g :: homCtx g)} (h : EnvRelB (BRel.secret Sec) ρ δ)
  for ladderT g at noninterference_ops h

end FreeThmApps

end CatCrypt.Complexity.D
