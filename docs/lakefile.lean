import Lake
open Lake DSL

-- Documentation package — SEPARATE from the `catcryptCore` library package so the
-- verso toolchain is NOT a transitive dependency of consumers of the library
-- (a downstream `require catcryptCore` must not be made to resolve verso).
-- The manual transcribes library declarations as text, so it needs only verso —
-- not the library or mathlib. Build it with:
--   cd docs && lake update && lake build && lake exe core-manual --output _out
-- Open docs/_out/html-single/index.html (a single self-contained page).
require verso from git
  "https://github.com/leanprover/verso.git" @ "v4.30.0"

package catcryptCoreDocs where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib CoreManual where

lean_exe «core-manual» where
  root := `ManualMain
