#!/usr/bin/env bash
# Refuse a commit that adds a new definition of a lemma family the library
# already defines. scripts/duplicate-decl-watch.txt lists short-name regexes, one
# per line. A staged .lean file fails when its added lines define a matching name
# (def/theorem/lemma/abbrev, optionally private) that the file did not define
# before. Import the existing declaration instead.
# Usage: duplicate-decl-guard.sh <staged .lean files>   (from the pre-commit hook)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
WATCH="scripts/duplicate-decl-watch.txt"
[ -f "$WATCH" ] || exit 0
pat="$(grep -vE '^\s*(#|$)' "$WATCH" | paste -sd'|')"
[ -n "$pat" ] || exit 0
declre="^\+\s*(private\s+|protected\s+)?(noncomputable\s+)?(def|theorem|lemma|abbrev)\s+([A-Za-z_.']*\.)?($pat)\b"
fail=0
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
for f in "$@"; do
  case "$f" in *.lean) ;; *) continue ;; esac
  { git diff --cached -U0 -- "$f" | grep -E "$declre" || true; } | while IFS= read -r line; do
    name="$(sed -E "s/$declre.*/\5/" <<<"$line")"
    if git show "HEAD:$f" 2>/dev/null | grep -qE "(def|theorem|lemma|abbrev)\s+([A-Za-z_.']*\.)?$name\b"; then
      continue
    fi
    echo "duplicate-decl-guard: $f adds a new definition of '$name', which the workspace already defines." >&2
    echo "  import the existing declaration." >&2
    echo x
  done > "$tmp"
  [ -s "$tmp" ] && fail=1
done
exit $fail
