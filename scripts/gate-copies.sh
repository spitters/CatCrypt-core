#!/usr/bin/env bash
#
# The copies of the shared gates agree.
#
# The gates against empty statements are carried as identical files by
# CatCrypt-core, catcrypt-compiler and the repository that develops on both.
# scripts/shared-gates.sha256 lists the files with their checksums and is itself
# one of the copies.
#
#   - Each listed file has its recorded checksum. This needs no other checkout
#     and refuses an edit of one copy on its own.
#   - A sibling checkout of core or the compiler that has the list has the same
#     list and the same files. A sibling without the list is reported and
#     skipped.
#
# After a change of a shared file: copy it to every repository, run `--write` in
# one of them, and copy the list to the others.
#
# Usage:
#   scripts/gate-copies.sh            # check
#   scripts/gate-copies.sh --write    # record the checksums of this copy
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
LIST="scripts/shared-gates.sha256"
FILES="scripts/gate-copies.sh
scripts/headline-witness-gate.sh
scripts/test_headline_witness_gate.sh
scripts/unbounded-hardness-fixtures.expected
scripts/unbounded-hardness-fixtures.txt
scripts/unbounded-hardness-ratchet.sh
scripts/unbounded-hardness-shapes.py"

if [ "${1:-}" = "--write" ]; then
  # shellcheck disable=SC2086
  sums=$(sha256sum $FILES) || exit 1
  printf '%s\n' "$sums" > "$LIST"
  echo "gate-copies: wrote $LIST"
  exit 0
fi

fail=0
if [ ! -f "$LIST" ]; then
  echo "FAIL: $LIST is missing."
  exit 1
fi
if [ "$(awk '{ print $2 }' "$LIST")" != "$FILES" ]; then
  echo "FAIL: $LIST does not list the shared files."
  fail=1
fi
if ! out=$(sha256sum -c --quiet "$LIST" 2>&1); then
  echo "FAIL: a shared gate differs from $LIST:"
  printf '%s\n' "$out" | sed 's/^/  /'
  fail=1
fi

for sibling in ../CatCrypt-core ../catcrypt-compiler; do
  [ -d "$sibling" ] || continue
  [ "$(cd "$sibling" && pwd -P)" != "$(pwd -P)" ] || continue
  if [ ! -f "$sibling/$LIST" ]; then
    echo "gate-copies: $sibling has no $LIST; not compared."
    continue
  fi
  for f in "$LIST" $FILES; do
    if ! cmp -s "$f" "$sibling/$f"; then
      echo "FAIL: $f differs from its copy in $sibling."
      fail=1
    fi
  done
done

if [ "$fail" = 1 ]; then
  echo "Copy the change to every repository and record it with scripts/gate-copies.sh --write."
  exit 1
fi
echo "gate-copies: the copies agree ($(wc -l < "$LIST") files)."
