import Lake
open Lake DSL

package catcryptCore where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib CatCrypt where
  globs := #[.submodules `CatCrypt]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

require smt from git
  "https://github.com/dhsorens/lean-smt.git" @ "dhsorens/4_28_0-update"

require auto from git
  "https://github.com/leanprover-community/lean-auto.git" @ "v4.28.0-hammer"

require Duper from git
  "https://github.com/leanprover-community/duper.git" @ "v4.28.0"

require VCVio from git
  "https://github.com/Verified-zkEVM/VCV-io" @ "master"
