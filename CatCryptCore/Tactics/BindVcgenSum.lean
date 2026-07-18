/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Tactics.BindVcgen
import CatCryptCore.Crypto.UC

/-!
# `bind_vcgen_sum` — a `mapSum`-extended run-to-completion driver

`spcomp_normalize_sum` / `bind_vcgen_sum` extend the base `spcomp_normalize` /
`bind_vcgen` drivers (run-to-completion for `SPComp`-equality goals) with the
`mapSum` `.inl`/`.inr` rewrites, so a bind-chain that dispatches on a `Sum`-typed
interface flattens. This is what the genuine-UC view equalities over `Sum`-typed
interfaces need (e.g. `pedersen_view_eq`, `sigma_view_eq`). The `mapSum` lemmas
live in `CatCryptCore.Crypto.UC`, above the base `BindVcgen` layer.
-/

namespace CatCrypt.Tactic

open Lean Elab Tactic

/-- `mapSum`-extended normalization: like `spcomp_normalize`, but the `simp only`
    set additionally fires `mapSum_inr` / `mapSum_inl`, so a `bind`-chain that
    dispatches on a `Sum`-typed interface flattens. Fails cleanly on no progress
    (safe inside `first` / `repeat`). -/
syntax "spcomp_normalize_sum" : tactic
macro_rules
  | `(tactic| spcomp_normalize_sum) => `(tactic|
      set_option linter.unusedSimpArgs false in
      simp only [CatCrypt.Core.SPComp.monad_bind_eq, CatCrypt.Core.SPComp.bind_assoc,
                 CatCrypt.Core.SPComp.pure_bind, CatCrypt.Core.SPComp.map,
                 CatCrypt.Crypto.mapSum_inr, CatCrypt.Crypto.mapSum_inl])

/-- `mapSum`-extended run-to-completion driver for `SPComp`-equality goals: the
    `bind_vcgen` loop with `spcomp_normalize_sum` in place of `spcomp_normalize`,
    so it also closes the `mapSum` reassociation steps of `Sum`-typed view
    equalities.

    `bind_vcgen_sum using e` applies the change of variables
    `SPComp.sample_bind_equiv e` to the `sample`-residual (right-hand side only),
    then peels again. -/
syntax "bind_vcgen_sum" (" using " term)? : tactic
macro_rules
  | `(tactic| bind_vcgen_sum) => `(tactic|
      repeat (first | rfl | spcomp_normalize_sum | bind_step))
  | `(tactic| bind_vcgen_sum using $e) => `(tactic|
      (try spcomp_normalize_sum);
      (try (refine Eq.trans ?_ (CatCrypt.Core.SPComp.sample_bind_equiv $e _)));
      (repeat (first | rfl | spcomp_normalize_sum | bind_step)))

end CatCrypt.Tactic
