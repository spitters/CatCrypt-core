#!/usr/bin/env bash
# Tests of scripts/deletion-gate.sh on temporary git repositories.
#
#   bash scripts/test_deletion_gate.sh [path/to/deletion-gate.sh]
#
# Each case builds a repository `dev` with a sibling `sib` (searched in its
# working tree) and a private notes directory `priv`, commits a base, stages a
# change, and checks the gate's exit code.
set -uo pipefail

GATE="$(cd "$(dirname "${1:-$0}")" && pwd)/deletion-gate.sh"
[ -n "${1:-}" ] && GATE="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
[ -f "$GATE" ] || { echo "no gate at $GATE" >&2; exit 2; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
pass=0; fail=0

g() { git -c core.hooksPath=/dev/null -c user.name=t -c user.email=t@t "$@"; }

setup() {
  rm -rf "$TMP/w"; mkdir -p "$TMP/w/dev/scripts" "$TMP/w/dev/Pkg" "$TMP/w/sib/Other" "$TMP/w/priv/docs"
  cd "$TMP/w/dev" || exit 2
  g init -q .
  printf 'name\tremoved_in\tsuccessor\tdecision\tnote\n' > scripts/deletion-ledger.tsv
  cat > Pkg/A.lean <<'EOF'
/-! Module A. -/
namespace Pkg.A

/-- First. -/
theorem foo_comm : True := trivial

@[simp] lemma bar_eq : 1 = 1 := rfl

private def helper : Nat := 0

/- A block comment:
theorem commented_out : True := trivial
-/
def baz : Nat := 1

end Pkg.A
EOF
  cat > Pkg/B.lean <<'EOF'
namespace Pkg.B
def keep : Nat := 2
end Pkg.B
EOF
  mkdir -p Pkg/Scratch
  printf 'namespace S\ntheorem scratch_thm : True := trivial\nend S\n' > Pkg/Scratch/S.lean
  g add -A && g commit -qm base
}

run_case() {  # name expected-rc
  local name="$1" want="$2" out rc
  out="$(cd "$TMP/w/dev" && DELETION_GATE_ROOTS="$TMP/w/sib" DELETION_DECISIONS_DIR="$TMP/w/priv" \
         bash "$GATE" staged 2>&1)"; rc=$?
  if [ "$rc" = "$want" ]; then
    pass=$((pass + 1)); echo "ok   $name (rc $rc)"
  else
    fail=$((fail + 1)); echo "FAIL $name (rc $rc, want $want)"; printf '%s\n' "$out" | sed 's/^/     /'
  fi
}

ledger_row() { printf '%s\t2026-11-09\t%s\t%s\ttest\n' "$1" "$2" "$3" >> "$TMP/w/dev/scripts/deletion-ledger.tsv"; }

# 1. A removal without a ledger row is refused.
setup; sed -i '/foo_comm/d' Pkg/A.lean; g add -A
run_case "removal without ledger refused" 1

# 2. A ledger row whose successor exists passes.
setup; sed -i '/foo_comm/d' Pkg/A.lean; ledger_row Pkg.A.foo_comm Pkg.B.keep -; g add -A
run_case "ledger successor that exists passes" 0

# 3. A ledger row whose successor is declared nowhere is refused.
setup; sed -i '/foo_comm/d' Pkg/A.lean; ledger_row Pkg.A.foo_comm Pkg.B.nowhere -; g add -A
run_case "ledger successor that does not exist refused" 1

# 4. A declaration moved to another file of the same commit passes.
setup; sed -i '/foo_comm/d' Pkg/A.lean
printf 'namespace Pkg.A\ntheorem foo_comm : True := trivial\nend Pkg.A\n' > Pkg/C.lean; g add -A
run_case "moved declaration passes" 0

# 5. A move into another namespace is a rename and is refused.
setup; sed -i '/foo_comm/d' Pkg/A.lean
printf 'namespace Pkg.C\ntheorem foo_comm : True := trivial\nend Pkg.C\n' > Pkg/C.lean; g add -A
run_case "move into another namespace refused" 1

# 6. A deleted file whose declarations exist elsewhere (a sibling) passes.
setup; cp Pkg/A.lean "$TMP/w/sib/Other/A2.lean"; g rm -q Pkg/A.lean
run_case "deleted file declared in sibling passes" 0

# 7. A sibling copy at the same relative path is a republished copy, not a move.
setup; mkdir -p "$TMP/w/sib/Pkg"; cp Pkg/A.lean "$TMP/w/sib/Pkg/A.lean"; g rm -q Pkg/A.lean
run_case "republished copy at the same path refused" 1

# 8. A decision path that exists passes; one that does not is refused.
setup; sed -i '/foo_comm/d' Pkg/A.lean; touch "$TMP/w/priv/docs/decision.md"
ledger_row Pkg.A.foo_comm - docs/decision.md; g add -A
run_case "decision path passes" 0
setup; sed -i '/foo_comm/d' Pkg/A.lean; ledger_row Pkg.A.foo_comm - docs/missing.md; g add -A
run_case "missing decision file refused" 1

# 9. An exempt scratch file passes.
setup; g rm -q Pkg/Scratch/S.lean
run_case "exempt scratch file passes" 0

# 10. Private declarations and commented-out text are not tracked.
setup; sed -i '/private def helper/d; /commented_out/d' Pkg/A.lean; g add -A
run_case "private and comment removal passes" 0

# 11. A ledger successor that this commit removes is refused.
setup; sed -i '/foo_comm/d' Pkg/A.lean; ledger_row Pkg.A.foo_comm Pkg.B.keep -
g add -A; g commit -qm step
touch "$TMP/w/priv/docs/d.md"
sed -i '/def keep/d' Pkg/B.lean; ledger_row Pkg.B.keep - docs/d.md; g add -A
run_case "ledger successor removed by the commit refused" 1

# 12. A changed statement (same name) passes.
setup; sed -i 's/theorem foo_comm : True := trivial/theorem foo_comm : 1 = 1 := rfl/' Pkg/A.lean; g add -A
run_case "changed statement passes" 0

# 13. A namespace rename removes every name of the file and is refused.
setup; sed -i 's/Pkg\.A/Pkg.Z/' Pkg/A.lean; g add -A
run_case "namespace rename refused" 1

# 14. A commit removing nothing passes, quickly.
setup; printf '\ntheorem added_thm : True := trivial\n' >> Pkg/B.lean; g add -A
t0=$(date +%s%N); run_case "no-removal commit passes" 0; t1=$(date +%s%N)
echo "     no-removal case: $(( (t1 - t0) / 1000000 )) ms"

echo "$pass passed, $fail failed"
[ "$fail" = 0 ]
