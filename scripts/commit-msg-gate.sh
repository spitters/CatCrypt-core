#!/usr/bin/env bash
# The commit-message gate: a commit message states what the code now does or proves.
#
# Refused, in the subject: a work-plan label (`ASC-7:`, `R1:`, `row B2`), a branch name
# (`work/x`, `origin/x`), a merge subject that names a branch, a commit hash, a report
# (`final report`, `night report`), and the words `landing build`.
# Refused, anywhere in the message: an acknowledgement tag such as `[no-golf]`. The commit
# hooks read those from the command, so a tag belongs in a comment on the command line:
#   git commit -F msg -- path  # [no-golf]
#
#   scripts/commit-msg-gate.sh [--warn] <message-file>
#   scripts/commit-msg-gate.sh --subject '<subject>'    # checks one line, exit 1 on a fault
#
# `--warn` prints the faults and exits 0.
set -uo pipefail

mode=enforce
case "${1:-}" in
  --warn) mode=warn; shift ;;
  --subject) mode=subject; shift ;;
esac
[ $# -eq 1 ] || { echo "usage: $0 [--warn] <message-file> | --subject <line>" >&2; exit 2; }

if [ "$mode" = subject ]; then
  msg="$1"
else
  msg="$(sed -e '/^#/d' "$1")"
fi
subject="$(printf '%s\n' "$msg" | sed -n '1p')"

# Names of primitives, groups and fields that have the shape of a plan label.
names='ML-KEM(-[0-9]+)?|ML-DSA(-[0-9]+)?|SLH-DSA(-[0-9A-Za-z]+)?|SHA-?[0-9]+|AES(-[A-Z0-9]+)*|HMAC(-[A-Z0-9]+)?|HKDF(-[A-Z0-9]+)?|BLS[0-9-]*|BN[0-9]+|P-?[0-9]+|X[0-9]+|M[0-9]+|G[0-9T]|F[0-9p]+|GF[0-9()]*|CT-[A-Za-z]+|UC-[A-Za-z]+|EC-[A-Za-z]+'
stripped="$(printf '%s' "$subject" | sed -E "s/(^|[^A-Za-z0-9-])($names)([^A-Za-z0-9-]|$)/\1\3/g")"

faults=()
printf '%s\n' "$msg" | grep -qE '\[(no-golf|golfed|docs-ok|no-docs|heartbeats-ok|native-decide-ok|pr-verified)\]' \
  && faults+=("an acknowledgement tag in the message: move it to a comment on the command line")
printf '%s\n' "$stripped" | grep -qE '^[A-Z]{1,4}(-[A-Z]{1,5})?-?[0-9]{1,2}[a-z]?([:,]| (and|final|report|\())' \
  && faults+=("a work-plan label at the start of the subject")
printf '%s\n' "$stripped" | grep -qE '(^|[^A-Za-z])[Rr]ows? [A-Z]{1,4}-?[0-9]{1,2}[a-z]?([^0-9A-Za-z]|$)' \
  && faults+=("a work-plan row named in the subject")
printf '%s\n' "$subject" | grep -qE '(^|[^A-Za-z0-9_/.-])(work|origin|master|main)/[A-Za-z0-9_.-]+' \
  && faults+=("a branch name in the subject")
printf '%s\n' "$subject" | grep -qE "^Merge (branch|remote-tracking|pull request|work/|'|[a-z0-9]+-?[a-z0-9]*\$)" \
  && faults+=("a merge subject that names a branch: land the work as a written commit")
printf '%s\n' "$subject" | grep -qE '(^|[^0-9a-f])[0-9]+[a-f]+[0-9a-f]{5,}([^0-9a-f]|$)|(^|[^0-9a-f])[a-f]+[0-9]+[0-9a-f]{5,}([^0-9a-f]|$)' \
  && faults+=("a commit hash in the subject")
printf '%s\n' "$subject" | grep -qiE '(final|night|status|morning) report|^report[: ]|landing build' \
  && faults+=("report or plan vocabulary in the subject")

[ ${#faults[@]} -eq 0 ] && exit 0

{
  echo "commit-msg gate: $subject"
  for f in "${faults[@]}"; do echo "  - $f"; done
} >&2
[ "$mode" = warn ] && exit 0
exit 1
