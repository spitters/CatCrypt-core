/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# The `kron_nf` simp set

Declares the simp attribute `kron_nf`, the rewrite system of the Kronecker normal form: products,
adjoints, scalars, sums, traces and partial traces of Kronecker products are rewritten to sums of
scalar multiples of single Kronecker products. The lemmas are tagged, and the tactics `kron_nf`,
`kron_index` and `kron_ext` are defined, in `CatCryptCore.Quantum.KronNf`; an attribute declared
by `register_simp_attr` is usable only in modules that import its declaring module.
-/

@[expose] public section

set_option autoImplicit false

/-- `kron_nf` is the simp set of the Kronecker normal form: oriented rules that move products,
adjoints, scalars, sums and traces through Kronecker products. -/
register_simp_attr kron_nf
