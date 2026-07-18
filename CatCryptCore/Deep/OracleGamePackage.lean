/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.Reflect
import CatCryptCore.Deep.Package
import CatCryptCore.Deep.Bridge
import CatCryptCore.Crypto.NomAdvantage

set_option autoImplicit false

/-!
# Oracle-Exporting Game Packages from Reflected Code

`DeepPackage.ofCode` (`Deep/GamePackage.lean`) packages a closed `RawCode Bool`
as the *main* export `(0, Unit, Bool)`. This file provides the missing dual: a
reusable constructor `DeepPackage.ofOracle` that turns a *shallow oracle
implementation* `impl₀ : dom → RawCode codom` into a package that **exports** a
single oracle `(op, dom, codom)` for other packages to call. Fed through
`rawCode%`, a shallow `SPComp` oracle becomes an oracle-exporting deep package
with no hand-written `RawCode`, no hand-written `impl` literal, and no
hand-written validity proof.

## Main definitions

* `DeepPackage.ofOracle` — the single-export oracle package for `impl₀`.
* `NomPackage.ofOracle` — its stateless (`∅`-location) nominal wrapper.

## Main results

* `evalOp_ofOracle` — evaluating the exported oracle recovers the shallow body
  `(impl₀ x).eval`.
* `runPkg_ofOracle_zero` — the main-export packaging `DeepPackage.ofCode` is the
  `op = 0`, `(dom, codom) = (Unit, Bool)` instance of `ofOracle`.
* `oracleGame_advantage_eq_shallow` — a worked reduction: the deep-package
  advantage of two reflected oracle games against a forwarding adversary equals
  the shallow `Advantage` of the two game bodies.
-/

namespace CatCrypt.Deep

open CatCrypt.Core CatCrypt.Crypto

/-! ## The oracle-package constructor -/

/-- The single-export `DeepPackage` that exports the oracle `(op, dom, codom)`
    and implements it by the shallow family `impl₀`.

    It has locations `L`, no imports, and exactly one export. The `impl` field
    matches an incoming request `(op', dom', codom')` against the singleton
    export list: membership forces `dom' = dom` and `codom' = codom`, and the
    bundle `ValidCodeBundle.auto (impl₀ x)` is cast across **both** type
    equalities (recall `(op, dom, codom)` parses as `(op, (dom, codom))`, so the
    two equalities are extracted from nested `Prod.mk.injEq`). Validity is
    discharged automatically from `[∀ x, IsValid L (impl₀ x)]`. -/
noncomputable def DeepPackage.ofOracle {L : LocSet} (op : ℕ) (dom codom : Type)
    (impl₀ : dom → RawCode codom) [∀ x, IsValid L (impl₀ x)] :
    DeepPackage where
  locs := L
  imports := ∅
  exports := ⟨[(op, dom, codom)]⟩
  impl := fun _ dom' codom' h x =>
    have hd : dom' = dom := by
      have hh := List.mem_singleton.mp h
      simp only [Prod.mk.injEq] at hh
      exact hh.2.1
    have hc : codom' = codom := by
      have hh := List.mem_singleton.mp h
      simp only [Prod.mk.injEq] at hh
      exact hh.2.2
    hc ▸ ValidCodeBundle.auto (impl₀ (hd ▸ x))

/-- Evaluating the exported oracle of `DeepPackage.ofOracle` recovers the shallow
    body `(impl₀ x).eval`: a game oracle's package evaluation is exactly the
    shallow game body's `eval`. -/
theorem evalOp_ofOracle {L : LocSet} (op : ℕ) (dom codom : Type)
    (impl₀ : dom → RawCode codom) [∀ x, IsValid L (impl₀ x)] (x : dom) :
    (DeepPackage.ofOracle (L := L) op dom codom impl₀).evalOp op dom codom
      (by simp [DeepPackage.ofOracle]) x = (impl₀ x).eval := by
  simp only [DeepPackage.evalOp, DeepPackage.ofOracle, ValidCodeBundle.auto]

/-- The stateless nominal wrapper of `DeepPackage.ofOracle`: no locations, so the
    location invariant reduces to `∅ = ∅.image _`. -/
noncomputable def NomPackage.ofOracle (op : ℕ) (dom codom : Type)
    (impl₀ : dom → RawCode codom) [∀ x, IsValid (∅ : LocSet) (impl₀ x)] :
    NomPackage where
  pkg := DeepPackage.ofOracle (L := ∅) op dom codom impl₀
  locs_eq := by simp [DeepPackage.ofOracle]

/-- `DeepPackage.ofCode c` is the `op = 0`, `(dom, codom) = (Unit, Bool)`
    instance of `DeepPackage.ofOracle`: running it recovers `c.eval`, so the
    main-export packaging is a special case of the oracle-export packaging. -/
theorem runPkg_ofOracle_zero {L : LocSet} (c : RawCode Bool) [IsValid L c] :
    CatCrypt.Crypto.runPkg
      (DeepPackage.ofOracle (L := L) 0 Unit Bool (fun _ => c)) = c.eval := by
  have hmem : (0, Unit, Bool) ∈
      (DeepPackage.ofOracle (L := L) 0 Unit Bool (fun _ => c)).exports.ops :=
    List.mem_singleton.mpr rfl
  simp only [CatCrypt.Crypto.runPkg, dif_pos hmem]
  rfl

/-! ## Feeding the constructor from shallow code by reflection

A shallow oracle `f : dom → SPComp codom` becomes an oracle package with no
hand-written `RawCode`: reflect the (inlined) body under the domain binder with
`rawCode%`, which handles the bound variable as a free variable. A bare
`fun x => rawCode% (f x)` referencing a top-level `def f` does *not* elaborate —
the reifier normalizes to weak-head-normal form under reducible transparency,
which leaves `f x` opaque; inlining `f`'s body exposes the `SPComp` head. -/

/-- A shallow one-bit oracle: XOR the query with a fresh uniform key. -/
noncomputable def sampleOracle : Bool → SPComp Bool :=
  fun m => SPComp.bind (SPComp.sample Bool) (fun k => SPComp.pure (xor k m))

/-- The oracle package for `sampleOracle`, produced by reflecting the inlined
    body under the domain binder — no hand-written `RawCode`, `impl` literal, or
    validity proof. -/
noncomputable def sampleOraclePkg : DeepPackage :=
  DeepPackage.ofOracle (L := ∅) 1 Bool Bool
    (fun m => rawCode% (SPComp.bind (SPComp.sample Bool) (fun k => SPComp.pure (xor k m))))

/-! ## Worked reduction: reflected oracle games vs a forwarding adversary

The two closed shallow game bodies are the one-time-pad ciphertext for a fixed
message (`realRaw`) and a fresh uniform bit (`idealRaw`) — the real/ideal pair of
one-time secrecy. Each is reflected into `RawCode` and packaged as an oracle
game exporting `(1, Unit, Bool)`; the adversary forwards the oracle unchanged.
The advantage of the whole deep-package/adversary construction collapses, by
reflection and linking correctness, to the shallow `Advantage` of the two bodies
— the quantity a bijection coupling bounds. -/

/-- Real body: one-time-pad encryption of the fixed message `true`. -/
noncomputable def realRaw : RawCode Bool :=
  rawCode% (SPComp.bind (SPComp.sample Bool) (fun k => SPComp.pure (xor k true)))

/-- Ideal body: a fresh uniform bit. -/
noncomputable def idealRaw : RawCode Bool :=
  rawCode% (SPComp.bind (SPComp.sample Bool) (fun k => SPComp.pure k))

instance instValidRealRaw : IsValid (∅ : LocSet) realRaw := by
  unfold realRaw; infer_instance

instance instValidIdealRaw : IsValid (∅ : LocSet) idealRaw := by
  unfold idealRaw; infer_instance

/-- Real oracle game, exporting `(1, Unit, Bool)`. -/
noncomputable def realGame : NomPackage :=
  NomPackage.ofOracle 1 Unit Bool (fun _ => realRaw)

/-- Ideal oracle game, exporting `(1, Unit, Bool)`. -/
noncomputable def idealGame : NomPackage :=
  NomPackage.ofOracle 1 Unit Bool (fun _ => idealRaw)

/-- Forwarding adversary: exports the main procedure `(0, Unit, Bool)` and
    implements it by a single oracle call `(1, Unit, Bool)`, returning the
    result unchanged. Built through the same `ofOracle` constructor. -/
noncomputable def forwardAdv : NomPackage :=
  NomPackage.ofOracle 0 Unit Bool (fun _ => RawCode.oracleCall 1 Unit Bool ())

/-- Running the forwarding adversary linked with an oracle game
    `NomPackage.ofOracle 1 Unit Bool (fun _ => body)` yields exactly the game
    body's evaluation `body.eval`. The oracle call in the adversary's main
    procedure is resolved, through linking, against the game's single export. -/
theorem runPkg_link_forward (body : RawCode Bool) [IsValid (∅ : LocSet) body] :
    CatCrypt.Crypto.runPkg
      (DeepPackage.link forwardAdv.pkg
        (NomPackage.ofOracle 1 Unit Bool (fun _ => body)).pkg) = body.eval := by
  rw [CatCrypt.Crypto.runPkg_link]
  simp only [forwardAdv, NomPackage.ofOracle, DeepPackage.ofOracle, ValidCodeBundle.auto,
    List.mem_singleton, RawCode.evalWith, dite_eq_ite, if_true]

/-- **Worked reduction.** The deep-package advantage of the two reflected oracle
    games against the forwarding adversary equals the shallow `Advantage` of the
    two game bodies — the one-time-secrecy advantage that a bijection coupling
    bounds. -/
theorem oracleGame_advantage_eq_shallow :
    DeepNomAdvantage realGame idealGame forwardAdv =
    Advantage realRaw.eval idealRaw.eval := by
  simp only [DeepNomAdvantage, realGame, idealGame,
    runPkg_link_forward realRaw, runPkg_link_forward idealRaw]

end CatCrypt.Deep
