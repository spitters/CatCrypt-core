#!/usr/bin/env bash
# Tests of scripts/headline-witness-gate.sh on small trees of the two layouts
# (text only, no Lean).
set -uo pipefail

GATE="$(cd "$(dirname "$0")" && pwd)/headline-witness-gate.sh"
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
pass=0
failed=0

expect() {  # expect <name> <exit code> <fixed string of the output>
  local out rc
  out=$(bash "$GATE" --root "$ROOT" 2>&1); rc=$?
  if [ "$rc" = "$2" ] && grep -qF -- "$3" <<< "$out"; then
    pass=$((pass + 1))
  else
    failed=$((failed + 1))
    echo "FAILED: $1 (exit $rc, expected $2 and '$3')"
    printf '%s\n' "$out" | sed 's/^/    /'
  fi
}

row() { printf '%s\t%s\t%s\t%s\n' "$@"; }

missing() {  # missing <count> <name>...
  { echo "count=$1"; shift; [ "$#" = 0 ] || printf '%s\n' "$@"; } \
    > "$ROOT/scripts/headline-witness-missing.txt"
}

compiler_tree() {
  ROOT=$(mktemp -d "$WORK/compiler.XXXXXX")
  mkdir -p "$ROOT/CatCrypt" "$ROOT/HaxAscent" "$ROOT/scripts"
  cat > "$ROOT/HEADLINES.md" <<'DOC'
# Headlines

| Area | Theorem |
|---|---|
| Compiler | [`comp_correct`](#compiler) |

`Comp.comp_correct` (`CatCrypt/Comp.lean`). Hypothesis: the level check, which
implies the semantic one by `helper_of_check`.

- `Comp.comp_bound`: the advantage is at most `1/4`.
DOC
  cat > "$ROOT/CatCrypt/Comp.lean" <<'LEAN'
namespace CatCrypt.Comp
noncomputable section Results
theorem helper_of_check (h : P) : Q := proof
theorem comp_correct (c : Code) (h : Accepted c) : Correct c := proof
theorem comp_bound (n : Nat) (h : Good n) : Adv n ≤ eps n := proof
theorem correct_witness : Correct code0 := comp_correct code0 accepted0
theorem bound_witness : Adv 2 ≤ eps 2 ∧ eps 2 < 1 := ⟨comp_bound 2 good2, small2⟩
theorem bound_no_number : Adv 2 ≤ eps 2 := comp_bound 2 good2
theorem unrelated : True := trivial
theorem unproved : Correct code0 := by
  have := comp_correct
  sorry
end Results
end CatCrypt.Comp
LEAN
}

R=CatCrypt.Comp
registry() {  # registry <witness of comp_correct> <witness of comp_bound>
  {
    echo "# registry"
    row $R.comp_correct headline statement "$1"
    row $R.comp_bound headline bound "$2"
    row $R.helper_of_check cited statement -
  } > "$ROOT/scripts/headline-witness.tsv"
}

compiler_tree; registry $R.correct_witness $R.bound_witness; missing 0
expect "both headlines have witnesses" 0 "2 with a witness"

registry - $R.bound_witness; missing 1 $R.comp_correct
expect "a recorded missing witness" 0 "1 recorded as missing"

missing 0
expect "a headline without witness outside the list" 1 "has no witness and is not in"

missing 0 $R.comp_correct
expect "the list grew" 1 "grew (0 -> 1)"

registry $R.correct_witness $R.bound_witness; missing 1 $R.comp_correct
expect "a recorded headline that has a witness" 1 "remove it from"

missing 0; registry $R.unrelated $R.bound_witness
expect "a witness that does not name the headline" 1 "does not name comp_correct"

registry $R.nowhere $R.bound_witness
expect "a witness that does not exist" 1 "is no declaration of the tree"

registry $R.comp_correct $R.bound_witness
expect "the headline as its own witness" 1 "is registered as its own witness"

registry $R.unproved $R.bound_witness
expect "a witness with a hole" 1 "is not proved"

registry $R.correct_witness $R.bound_no_number
# the statement of the witness has no comparison with 1
expect "a bound without a value below 1" 1 'states no `< 1`'

registry $R.correct_witness $R.bound_witness
sed -i '/helper_of_check/d' "$ROOT/scripts/headline-witness.tsv"
expect "a named theorem without a row" 1 "helper_of_check is not registered"

registry $R.correct_witness $R.bound_witness
row $R.gone cited statement - >> "$ROOT/scripts/headline-witness.tsv"
expect "a row without a declaration" 1 "registered $R.gone is no declaration"

registry $R.correct_witness $R.bound_witness
sed -i '/comp_bound\theadline/s/headline/cited/' "$ROOT/scripts/headline-witness.tsv"
expect "a headline recorded as cited" 1 "is registered as cited"

registry $R.correct_witness $R.bound_witness
printf '\n- `Comp.unrelated`: a new headline.\n' >> "$ROOT/HEADLINES.md"
expect "a new headline that is not registered" 1 "$R.unrelated is not registered"

compiler_tree; registry $R.correct_witness $R.bound_witness; missing 0
printf '\n- `Comp.absent_theorem`: a headline that no module has.\n' >> "$ROOT/HEADLINES.md"
expect "a headline without a declaration" 1 "Comp.absent_theorem, which is no declaration"

missing 1 "undeclared Comp.absent_theorem"
expect "a recorded headline without a declaration" 0 "1 recorded as missing"

compiler_tree; registry $R.correct_witness $R.bound_witness
rm -f "$ROOT/scripts/headline-witness-missing.txt"
expect "no recorded list" 1 "headline-witness-missing.txt is missing"

core_tree() {
  ROOT=$(mktemp -d "$WORK/core.XXXXXX")
  mkdir -p "$ROOT/CatCryptCore/Examples" "$ROOT/scripts"
  cat > "$ROOT/JoyOfCrypto.md" <<'DOC'
| Ch. | Topic | Module | Main results | Statement |
|---|---|---|---|---|
| 1 | One-time pad | `OneTimePad` | `otp_perfect` | advantage 0 |
DOC
  echo 'The time theorem is `otp_time_bound`.' > "$ROOT/README.md"
  cat > "$ROOT/CatCryptCore/Examples/OneTimePad.lean" <<'LEAN'
namespace CatCrypt.OTP
theorem otp_perfect (A : Adv) : advantage A = 0 := proof
theorem otp_time_bound (A : Adv) : time A ≤ t := proof
end CatCrypt.OTP
LEAN
}

core_tree
row CatCrypt.OTP.otp_perfect headline statement - > "$ROOT/scripts/headline-witness.tsv"
missing 1 CatCrypt.OTP.otp_perfect
expect "core: a theorem of the README without a row" 1 "otp_time_bound is not registered"

row CatCrypt.OTP.otp_time_bound cited statement - >> "$ROOT/scripts/headline-witness.tsv"
expect "core: registered results" 0 "1 headlines"

sed -i '/otp_perfect/d' "$ROOT/scripts/headline-witness.tsv"
missing 0
expect "core: a main result without a row" 1 "otp_perfect is not registered"

echo "test_headline_witness_gate: $pass passed, $failed failed"
[ "$failed" = 0 ]
