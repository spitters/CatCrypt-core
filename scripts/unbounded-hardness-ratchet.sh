#!/usr/bin/env bash
#
# Unbounded-adversary hardness ratchet.
#
# Adversaries in CatCrypt are arbitrary Lean functions. A hypothesis or
# definition of the shape `∀ A, <X>Advantage … A ≤ ε` on a computational game
# (DDH, DL, PRF, MLWE, EUF-CMA, …) is therefore unsatisfiable for ε below about
# 1: the adversary that inverts by `Classical.choose` wins. A theorem that
# assumes it is vacuous. Security theorems are stated as concrete reductions
# instead, as in EasyCrypt: for every adversary `A`,
# `Adv_protocol A ≤ Adv_prim (B A) + … + ε_stat` with `B` constructed.
#
# All categories scan Lean source with `/- … -/` blocks (docstrings and
# comments) and `--` line comments removed. The scanner runs with LC_ALL=C, so
# awk matches bytes: a bracket expression such as `[^≤]` excludes every byte
# of `≤`, and with it every character sharing its lead byte (subscripts, `→`,
# `∀`), under both mawk and gawk. An advantage term is an identifier containing
# `Advantage` or ending in `_Adv` or `GameAdv` (`PRF_Adv`, `OTSacrifice_Adv`,
# `ExtractabilityGameAdv`; not `GameAdvBoundC` or `DDH_Adversary`). The
# categories:
#
#   single     Lines of the scanned tree containing `∀ … ,` followed by an
#              `Advantage` term and `≤`, where the text after the first `≤` of
#              the line mentions no `Advantage`, and where the tokens of the
#              line pass the token test of `multiline` below: a `∀` of the line
#              binds the adversary of the advantage term, and the right-hand
#              side, up to the end of the line, does not mention it. A bound
#              that depends on the adversary (`∀ x D, AdvantageA … D ≤ bound x
#              D`, the `bound_le` field of `GameAdvBoundC`) and a step for an
#              adversary fixed outside the `∀` (`∀ x, AdvantageA (f x) (g x) A
#              ≤ ε`) are concrete statements and are not counted.
#              A right-hand side that runs
#              to the end of the line continues on the following non-blank
#              lines indented deeper than the line (at most 8), so a bound
#              `≤` at the end of a line whose next line names the adversary
#              (`≤` / `eufcmaAdvantage S A`) is not counted. Because of the
#              byte matching above, a line whose binder or advantage arguments
#              contain a subscript or an arrow is not matched
#              (`∀ m₀ m₁ A, INDCPA_Advantage E m₀ m₁ A ≤ ε`).
#   multiline  Numeric `∀`-bounds found on tokens inside one declaration
#              signature (theorem, lemma, def, abbrev, instance, structure,
#              class, example, axiom, opaque, variable, or a structure/class
#              field) up to its first `:=` or `where` at bracket depth 0, or in
#              the first 40 lines of the body of a `Prop`-valued def/abbrev,
#              and not counted by the line rule of `single`/`ascii`: the `≤`
#              lies on a later line than the innermost enclosing `∀`, or its
#              line fails the line rule. A token match is `∀ binders ,` then,
#              within the bracket group of that `∀` and after its last `,`,
#              `→`, `∧`, `↔` or `∨`, exactly one `Advantage` term followed by
#              `≤` whose right-hand side (up to the next such separator at the
#              same depth, where the comma ending the binder of a big operator
#              `∑ ∏ ⨆ ⨅ ⋃ ⋂` is not a separator) mentions no `Advantage`, no
#              variable bound by an `∃` of the chain, and not the adversary,
#              so `≤ ∑ i : Fin d, PRG_Adv G (red A i)` is not counted. The
#              `∀` chain must bind
#              the adversary: the last top-level argument of the advantage
#              term is a bound variable, or a bound variable whose binder type
#              mentions SPComp, Adversary, Distinguisher, Forger, Adv, Prover,
#              Attacker or Oracle occurs in the term, or an untyped bound
#              variable named A, B, D, F, Adv or adv occurs in it. A hybrid
#              step `∀ i, … AdvantageA (G i) (G (i+1)) A ≤ ε` with `A` free is
#              therefore not counted. Each site is reported at the first line
#              of its declaration.
#   ascii      Lines matching the `single` rule only after ASCII notation is
#              rewritten (`forall` to `∀`, `<=` to `≤`), and not matched by
#              `single` itself.
#   named_def  Definitions whose body is a `multiline` token match (on any
#              number of lines): a `Prop`-valued def/abbrev with the match in
#              its body, or a structure/class with the match in a field. A
#              match does not name its definition when it is the antecedent of
#              `→`, or when an identifier containing Advantage, Secure, Hard or
#              Assumption occurs between the start of the body (or field type)
#              and the bound; those are implications from an assumed bound.
#              The set is closed under reference: a structure/class with a
#              field whose type starts with a named definition, a
#              structure/class extending one, and a `Prop`-valued def/abbrev
#              whose body mentions one and contains no `→` are named as well
#              (reported `via` that name).
#   named_use  Binders `(h : N …)`, `{h : N …}`, `⦃h : N …⦄`, `[N …]` or
#              `[h : N …]` in a declaration signature (as delimited for
#              `multiline`), where `N`, stripped of its namespace, is a
#              `named_def` name. One site per binder. Instances providing `N`
#              are not uses.
#   exists     Assumed existential bounds: a bracket group before the
#              conclusion colon of a declaration signature, a bracket group in
#              the conclusion followed by `→`, the type of a structure/class
#              field, or the body of a `Prop`-valued def/abbrev, containing
#              `∃`, then an identifier containing `Advantage`, `advantage` or a
#              `_Adv` suffix, then `≤`. A conclusion `∃ B, …` of a theorem is
#              a constructed reduction and is not counted.
#   sdist_named  Assumed statistical-distance bounds on specific games in
#              protocol code: an sdist-family term (`sdist`, `sdistD`,
#              `sdistITreeN`, `sdistITreeGN`, `kdistITreeN`, `ucSdist`, …: a name
#              `sdist…`, `kdist…`, `…Sdist…` or `…Kdist…`) followed, after its
#              arguments, by `≤` or `= 0`, whose right-hand side (up to the next
#              `, → ∧ ↔ ∨ :=` or closing bracket) mentions no sdist-family or
#              advantage term. One site per hypothesis binder group before the
#              conclusion colon (every group of a `variable`), per antecedent of
#              `→` in a conclusion, per structure/class field, and per
#              `Prop`-valued def/abbrev body; binder and antecedent sites are
#              reported at the first line of their declaration. Counted only in
#              `Crypto/<P>/` outside UCMonad, Bridges, Choreography,
#              CompilerSecurity, SecureCompilation, SecurityDefs, Constructions
#              and Symbolic, in `Examples/`, and in `Bridges/IrisBridge/Ratchet*`
#              and `Choreography/ChannelCap*` (dev and core). The compared games,
#              the last two arguments of the term, must not both be built only
#              from bound names (binders of the declaration, of `∀ ∃ fun λ`,
#              `let`, `←`, and of earlier `variable` commands of the file; the
#              parameters of a structure for its fields) and the combinators
#              `SPComp.*`, `mapSum`, `ucMapSum`, `ITreeN.bind'`, `liftSDistr`; a
#              projection `Q.f` of a bound name and a sibling field of a
#              structure count as specific, the binder types of `∀ ∃ fun λ` do
#              not count. A counted field or `Prop` body names its definition
#              for `named_use` and the closure of `named_def`; a definition named
#              through that closure from an sdist definition is reported here
#              (`via`). An application `RefinesFamilyUpTo G F ε` is such a bound
#              on the games `G` and `F`, as the class is equivalent to one.
#   nested     Numeric `∀`-bounds that `multiline` does not see, for one of two
#              reasons. The adversary has a type outside the adversary types of
#              `multiline` and occurs inside another argument
#              (`∀ (A : NomPkg) i, Advantage_game G (nomComp (Ai A i) R) ≤ ε`):
#              a typed bound variable named A, B, D, Adv or adv, or of a package
#              type. Or the advantage has a name outside the pattern above
#              (`Adv`, `adv`, a name containing `advantage`, beginning with
#              `Adv_` or ending in `…Adv` or `_adv`). A bound that `multiline`
#              matches, excluded or not, is not a site.
#   nested_use Binders over a definition whose body is a `nested` match and
#              that is no `named_def`.
#
# The next five are found by scripts/unbounded-hardness-shapes.py; a site is a
# declaration.
#
#   point_mass A comparison (an advantage, statistical distance, `absDiff` or
#              emulation term) with two adjacent arguments of which one is a
#              point mass (`pure v`) and the other one uniform sample, written
#              in place or as the body of a definition of the same file:
#              `AdvantageA (pure (f x)) (sample W) A` is at least 1 - 1/|W| for
#              some `A`, so a bound on it states nothing about `f`.
#   point_mass_use  A statement over a `point_mass` definition, in its file or
#              in a file of the same repository that imports it.
#   same_body  A definition whose name contains `ideal` with the body of the
#              definition of the same file named with `real` in its place, or
#              whose body applies that definition; and an advantage defined by
#              comparing a game with itself.
#   free_witness  A statement in which the body or the frame map of `RunSafe`,
#              `AccessIn`, `StoreIn` or `LoadIn` is bound by `∃` and no equation
#              or membership determines it from other terms (`decode bs = some
#              body` determines `body`): some body is safe, not the compiled one.
#   returned_arg  A theorem with an existential conclusion whose proof is the
#              theorem's own argument and a proof by reflexivity
#              (`∃ c', f c' = f c` by `⟨c, rfl⟩`).
#
#   core_*     Every category over `../CatCrypt-core/CatCryptCore/`
#              (read with `git -C ../CatCrypt-core ls-files`); `named_def`
#              names are shared between the two trees, so a dev binder over a
#              core definition counts as `named_use`. Skipped when the sibling
#              is absent.
#   compiler_* Every category over `CatCrypt/` and `HaxAscent/` of
#              `../catcrypt-compiler`, scanned without the exclusion file, as
#              the compiler's own run does. Skipped when the sibling is absent.
#
# The script is carried as an identical copy by three repositories
# (scripts/gate-copies.sh) and scans the one it is in: in CatCrypt-core and in
# catcrypt-compiler its own tree with category names without prefix, in the
# development repository its tree and the two siblings.
#
# Not detected: a shape behind a definition of another file, an advantage with
# a name outside both patterns, a point mass or
# a uniform sample written by a bind or match, equal games with differently
# written bodies or with names without real/ideal, a witness fixed by an
# equation that itself says nothing, an argument returned through a tactic
# other than `exact`, `refine`, `use` and `exists`, and a theorem that forwards
# one of the sites by name.
#
# Information-theoretic games also match these patterns; a site whose game is
# information-theoretic is recorded in the exclusion file with its reason. An
# entry is a fixed string matched against `category:path:line:text` of a site
# (a `named_def` site also against `path:line:name`), so a `category:` prefix
# restricts an entry to one category and a path ending in `/` covers a
# directory; an entry containing spaces is written in double quotes. An
# excluded `named_def` or `sdist_named` definition site does not enter the name
# set. Every category may fall, never rise.
#
# Baseline file: the first line is the `single` count (the number CI has
# always read); each further category is a `name=count` line, and a category
# without one fails. A category may also have a `sites=name` line: its sites
# are then recorded as `site<TAB>category<TAB>path<TAB>text` lines (no line
# numbers), and a site that is not recorded fails even at an equal count.
#
# Usage:
#   scripts/unbounded-hardness-ratchet.sh            # check every category against the baseline
#   scripts/unbounded-hardness-ratchet.sh --list     # print category:path:line:text for every site
#   scripts/unbounded-hardness-ratchet.sh --accept   # write the current counts as the baseline
#   scripts/unbounded-hardness-ratchet.sh --self-test   # check the rules on the fixture file
#   scripts/unbounded-hardness-ratchet.sh --scan FILE...  # print the sites of these files, no exclusion
#
# Every run first scans `scripts/unbounded-hardness-fixtures.txt` and compares the
# sites found with `scripts/unbounded-hardness-fixtures.expected`; a difference
# fails the run, so a change of a rule shows up as a change of that file. In the
# fixture file, a line `#path <path>` sets the path that the directory test of
# `sdist_named` reads for the declarations after it.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
BASELINE="scripts/unbounded-hardness-baseline.txt"
EXCLUDE="scripts/unbounded-hardness-exclude.txt"
FIXTURES="scripts/unbounded-hardness-fixtures.txt"
FIXTURES_EXPECTED="scripts/unbounded-hardness-fixtures.expected"
SHAPES="scripts/unbounded-hardness-shapes.py"
CORE_DIR="../CatCrypt-core"
COMPILER_DIR="../catcrypt-compiler"
mode="${1:-check}"

# The categories recorded by count only, and those recorded by count and site.
COUNT_CATS="single multiline ascii named_def named_use exists sdist_named"
SHAPE_CATS="nested nested_use point_mass point_mass_use same_body free_witness returned_arg"
CATS="$COUNT_CATS $SHAPE_CATS"

# The repository this copy is in. Only the development repository scans siblings.
if [ -d CatCryptCore ]; then SELF=core
elif [ -f HEADLINES.md ] && [ -d HaxAscent ]; then SELF=compiler
else SELF=dev
fi
have_core=0
have_compiler=0
if [ "$SELF" = dev ]; then
  if git -C "$CORE_DIR" rev-parse --git-dir >/dev/null 2>&1; then have_core=1; fi
  if git -C "$COMPILER_DIR" rev-parse --git-dir >/dev/null 2>&1; then have_compiler=1; fi
fi

# `repo<TAB>path` lines of one tree; `dev` is the tree without category prefix.
tree_list() {
  case "$1" in
    own)
      case "$SELF" in
        core) git ls-files 'CatCryptCore/*.lean' ;;
        compiler) git ls-files 'CatCrypt/*.lean' 'HaxAscent/*.lean' ;;
        *) git ls-files 'CatCrypt/*.lean' ;;
      esac | awk '{ print "dev\t" $0 }' ;;
    core)
      git -C "$CORE_DIR" ls-files 'CatCryptCore/*.lean' \
        | awk -v d="$CORE_DIR" '{ print "core\t" d "/" $0 }' ;;
    compiler)
      git -C "$COMPILER_DIR" ls-files 'CatCrypt/*.lean' 'HaxAscent/*.lean' \
        | awk -v d="$COMPILER_DIR" '{ print "compiler\t" d "/" $0 }' ;;
  esac
}

# The scanner reads `repo<TAB>path` lines and prints `category:path:line:text`.
read -r -d '' AWKPROG <<'AWK'
function strip(line,   out, p1, p2) {
  out = ""
  while (line != "") {
    if (cdepth > 0) {
      p1 = index(line, "-/"); p2 = index(line, "/-")
      if (p1 == 0 && p2 == 0) return out
      if (p2 == 0 || (p1 > 0 && p1 < p2)) { cdepth--; line = substr(line, p1 + 2) }
      else { cdepth++; line = substr(line, p2 + 2) }
    } else {
      p1 = index(line, "/-"); p2 = index(line, "--")
      if (p1 == 0 && p2 == 0) return out line
      if (p2 == 0 || (p1 > 0 && p1 < p2)) { out = out substr(line, 1, p1 - 1); cdepth++; line = substr(line, p1 + 2) }
      else return out substr(line, 1, p2 - 1)
    }
  }
  return out
}
function wordrep(s, w, r,   out, m, k) {
  out = ""
  while (match(s, "(^|[^A-Za-z0-9_'.])" w "([^A-Za-z0-9_'!?]|$)")) {
    m = substr(s, RSTART, RLENGTH); k = index(m, w)
    out = out substr(s, 1, RSTART - 1) substr(m, 1, k - 1) r
    s = substr(s, RSTART + k - 1 + length(w))
  }
  return out s
}
function norm(s) {
  if (s !~ /forall|exists|<=|->|\/\\/) return s
  gsub(/<->/, "↔", s); gsub(/->/, "→", s); gsub(/<=/, "≤", s); gsub(/\/\\/, "∧", s)
  if (s ~ /forall/) s = wordrep(s, "forall", "∀")
  if (s ~ /exists/) s = wordrep(s, "exists", "∃")
  return s
}
function squash(t) {
  gsub(/[ \t\n]+/, " ", t); sub(/^ /, "", t); sub(/ $/, "", t)
  if (length(t) > 600) { t = substr(t, 1, 600); sub(/ [^ ]*$/, " …", t) }
  return t
}
function excluded(rec,   k) {
  for (k = 1; k <= nx; k++) if (index(rec, excl[k])) return 1
  return 0
}
function emit(cat, p, l, text,   rec) {
  rec = cat ":" p ":" l ":" text
  if (nx && excluded(rec)) return
  print rec
}
# An advantage token: a name containing Advantage, or ending in _Adv or GameAdv
# (`PRF_Adv`, `ExtractabilityGameAdv`; not `GameAdvBoundC` or `DDH_Adversary`).
function isadv(t) { return t ~ /Advantage/ || t ~ /(_Adv|GameAdv)[0-9']*$/ }
# The names that the second pass (WIDE, category `nested`) takes as advantages.
function iswide(t) { return isadv(t) || t ~ /advantage|(^|\.)(Adv|adv)$|(^|\.)Adv_|(^|\.)[a-z][A-Za-z0-9_]*Adv[0-9']*$|_adv$/ }
function isopen(t) { return t == "(" || t == "[" || t == "{" || t == "⟨" || t == "⦃" }
function isclose(t) { return t == ")" || t == "]" || t == "}" || t == "⟩" || t == "⦄" }
function issep(t) { return t == "→" || t == "∧" || t == "↔" || t == "∨" }
# A big operator: its binder ends at a comma (`∑ i ∈ s, f i`).
function isbig(t) { return t == "∑" || t == "∏" || t == "⨆" || t == "⨅" || t == "⋃" || t == "⋂" }
function tokenize(s,   used, t) {
  ntok = 0; used = 0; curl = 0
  while (match(s, /\n|:=|[][(){},:]|⟨|⟩|⦃|⦄|∀|∃|≤|→|∧|↔|∨|∑|∏|⨆|⨅|⋃|⋂|[A-Za-z_\300-\337][A-Za-z0-9_'.!?\200-\337]*/)) {
    t = substr(s, RSTART, RLENGTH)
    tstart = used + RSTART
    used += RSTART + RLENGTH - 1
    s = substr(s, RSTART + RLENGTH)
    if (t == "\n") { curl++; continue }
    ntok++; tok[ntok] = t; tokl[ntok] = curl; toks[ntok] = tstart; toke[ntok] = used
  }
}
# Token index of the `≤` of the first numeric bound in the body of the `∀` at
# token i, within the bracket group of that `∀`; 0 when there is none. Sets
# MF_LAST (innermost `∀` enclosing the `≤`) and MF_END (first token after the
# right-hand side).
function mforall(i,   j, k, d, dd, comma, t, t2, hasadv, rhasadv, bp) {
  d = 0; comma = 0
  for (j = i + 1; j <= ntok; j++) {
    t = tok[j]
    if (isopen(t)) d++
    else if (isclose(t)) { d--; if (d < 0) return 0 }
    else if (t == ":=" && d == 0) return 0
    else if (t == "," && d == 0) { comma = j; break }
  }
  if (!comma) return 0
  d = 0; lastsep[0] = comma; lastf[0] = i
  for (j = comma + 1; j <= ntok; j++) {
    t = tok[j]
    if (isopen(t)) { d++; lastsep[d] = j; lastf[d] = lastf[d - 1]; continue }
    if (isclose(t)) { d--; if (d < 0) return 0; continue }
    if (t == ":=" && d == 0) return 0
    if (t == "∀") { lastf[d] = j; continue }
    if (t == "," || issep(t)) { lastsep[d] = j; continue }
    if (t != "≤") continue
    hasadv = 0
    for (k = lastsep[d] + 1; k < j; k++) if (WIDE ? iswide(tok[k]) : isadv(tok[k])) hasadv++
    if (hasadv != 1) continue
    dd = 0; rhasadv = 0; bp = 0
    for (k = j + 1; k <= ntok; k++) {
      t2 = tok[k]
      if (isopen(t2)) dd++
      else if (isclose(t2)) { dd--; if (dd < 0) break }
      else if (dd == 0 && isbig(t2)) bp++
      else if (dd == 0 && t2 == ":=") break
      else if (dd == 0 && bp > 0) { if (t2 == ",") bp-- }
      else if (dd == 0 && (issep(t2) || t2 == "," || t2 == "≤")) break
      if (WIDE ? iswide(t2) : isadv(t2)) { rhasadv = 1; break }
    }
    if (rhasadv) continue
    MF_LAST = lastf[d]; MF_END = k; MF_SEG = lastsep[d]
    if (!bindsadv(i, lastsep[d], j)) continue
    for (k = j + 1; k < MF_END; k++) {
      t2 = tok[k]; sub(/\..*/, "", t2)
      if ((t2 in advset) || bv[t2] == "e") { rhasadv = 1; break }
    }
    if (rhasadv) continue
    return j
  }
  return 0
}
# Record the variables bound by the `∀` at token b in bv[name]: "a" when the
# binder type mentions an adversary-like type, "t" for another type, "u" when
# untyped.
function binders(b,   k, d, t, gn, gt, gm, tn, tt, tm) {
  d = 0; tn = ""; tt = ""; tm = 0
  for (k = b + 1; k <= ntok; k++) {
    t = tok[k]
    if (d == 0 && t == ",") break
    if (isopen(t)) { d++; if (d == 1) { gn = ""; gt = ""; gm = 0 }; continue }
    if (isclose(t)) { d--; if (d == 0) setkind(gn, gt, gm); if (d < 0) break; continue }
    if (d == 0) {
      if (t == ":") { tm = 1; continue }
      if (tm) tt = tt " " t; else if (t ~ /^[A-Za-z_\300-\337]/) tn = tn " " t
    } else if (d == 1 && !gm) {
      if (t == ":") { gm = 1; continue }
      if (t ~ /^[A-Za-z_\300-\337]/) gn = gn " " t
    } else if (gm) gt = gt " " t
  }
  setkind(tn, tt, tm)
}
function setkind(names, ty, typed,   nn, q, k) {
  nn = split(names, q, " ")
  if (WIDE) for (k = 1; k <= nn; k++) bvpkg[q[k]] = (typed && ty ~ /NomPkg|Package|Pkg/)
  for (k = 1; k <= nn; k++)
    bv[q[k]] = (tok[BINDB] == "∃") ? "e" : !typed ? "u" : (ty ~ /SPComp|Adversary|Distinguisher|Forger|Adv|Prover|Attacker|Oracle/ ? "a" : "t")
}
# Number of adversaries bound by a `∀` in [i, j) on which the advantage term
# between token s (exclusive) and the `≤` at j depends, recorded in advset: the
# term's last top-level argument when it is a bound variable, a bound variable
# of adversary-like type occurring in the term, or an untyped bound variable
# named A, B, D or F occurring in it.
function bindsadv(i, s, j,   k, a, dd, t, last, v, n) {
  split("", bv); split("", advset); n = 0
  for (k = i; k < j; k++) if (tok[k] == "∀" || tok[k] == "∃") { BINDB = k; binders(k) }
  a = 0
  for (k = s + 1; k < j; k++) if (WIDE ? iswide(tok[k]) : isadv(tok[k])) a = k
  if (!a) return 0
  # A bound variable named like an advantage (`adv`, `Adv`) is no advantage, and
  # neither is a name inside a distance (`staticAdv` in the games of an `sdist`).
  if (WIDE && !isadv(tok[a])) {
    if (tok[a] in bv) return 0
    for (k = s + 1; k < a; k++) if (issd(tok[k])) return 0
  }
  dd = 0; last = ""
  for (k = a + 1; k < j; k++) {
    t = tok[k]
    if (isopen(t)) { dd++; continue }
    if (isclose(t)) { dd--; if (dd <= 0) last = ""; if (dd < 0) dd = 0; continue }
    if (dd == 0) last = (t ~ /^[A-Za-z_\300-\337]/) ? t : ""
  }
  if (last != "" && (last in bv) && bv[last] != "e") { advset[last] = 1; n++ }
  for (k = a; k < j; k++) {
    t = tok[k]
    if (t !~ /^[A-Za-z_\300-\337]/) continue
    v = t; sub(/\..*/, "", v)
    if (!(v in bv) || (v in advset)) continue
    if (bv[v] == "a" || (bv[v] == "u" && v ~ /^(A|B|D|F|Adv|adv)[0-9_']*$/)) { advset[v] = 1; n++ }
    else if (WIDE && bv[v] == "t" && (bvpkg[v] || v ~ /^(A|B|D|Adv|adv)[0-9_']*$/)) { advset[v] = 1; n++ }
  }
  return n
}
function adddef(name, p, l, how,   rec) {
  rec = p ":" l ":" name
  if (nx && excluded(rec)) return
  if (!(name in named) || nroot[name] == "s") { named[name] = how; nroot[name] = "a" }
  if (index(defsites[name], SUBSEP pfx "named_def:" rec SUBSEP) == 0)
    defsites[name] = defsites[name] SUBSEP pfx "named_def:" rec SUBSEP
}
function addcand(name, p, l, idents,   rec) {
  cand[name] = cand[name] " " idents
  rec = pfx "named_def:" p ":" l ":" name
  if (index(candsites[name], SUBSEP rec SUBSEP) == 0)
    candsites[name] = candsites[name] SUBSEP rec SUBSEP
}
function identsof(a, b,   k, out, t) {
  out = ""
  for (k = a; k <= b; k++) {
    t = tok[k]
    if (t ~ /^[A-Za-z_]/) { sub(/.*\./, "", t); out = out " " t }
  }
  return out
}
function hasexists(a, b,   k, e, adv) {
  e = 0; adv = 0
  for (k = a; k <= b; k++) {
    if (tok[k] == "∃") e = 1
    else if (e && (tok[k] ~ /[Aa]dvantage|_Adv([^a-z]|$)/ || isadv(tok[k]))) adv = 1
    else if (adv && tok[k] == "≤") return 1
  }
  return 0
}
function startchunk(kind, name, l) {
  ckind = kind; cname = name; cline = l
  ctext = ""; cbody = ""; cstate = "sig"; sdepth = 0; cbl = 0; cfirst = 1
  split("", chunkline); cn = 0
}
# Position of the first `:=` or `where` at bracket depth 0 in t (0 if none);
# SE_TOK names it. Updates the running depth sdepth.
function sigend(t,   s, used, m, k) {
  s = t; used = 0
  while (match(s, /:=|[][(){}]|⟨|⟩|⦃|⦄|(^|[^A-Za-z0-9_'.])where([^A-Za-z0-9_'!?]|$)/)) {
    m = substr(s, RSTART, RLENGTH)
    if (m == ":=") { if (sdepth == 0) { SE_TOK = ":="; return used + RSTART } }
    else if (m ~ /where/) {
      if (sdepth == 0) { SE_TOK = "where"; return used + RSTART + index(m, "where") - 1 }
      k = index(m, "where") + 4; used += RSTART + k - 1; s = substr(s, RSTART + k); continue
    }
    else if (m == "(" || m == "[" || m == "{" || m == "⟨" || m == "⦃") sdepth++
    else { sdepth--; if (sdepth < 0) sdepth = 0 }
    used += RSTART + RLENGTH - 1; s = substr(s, RSTART + RLENGTH)
  }
  return 0
}
function feed(t,   p, rest, sep) {
  if (cstate == "sig" || (cstate == "body" && cbl < 40)) chunkline[cn++] = t
  if (cstate == "sig") {
    sep = cfirst ? "" : "\n"; cfirst = 0
    p = sigend(t)
    if (p == 0) { ctext = ctext sep t; return }
    ctext = ctext sep substr(t, 1, p - 1)
    if (SE_TOK == ":=") {
      rest = substr(t, p + 2)
      if ((ckind == "def" || ckind == "abbrev") && (ctext ~ /:[ \t\n]*Prop[ \t\n]*$/ || rest ~ /^[ \t]*\(?∀/)) {
        cstate = "body"; cbody = rest; cbl = 1
      } else cstate = "done"
    } else {
      cstate = "done"
      if (ckind == "structure" || ckind == "class") { inbody = 1; fieldIndent = -1; sname = cname; sline = cline }
    }
  } else if (cstate == "body") {
    if (cbl < 40) cbody = cbody "\n" t
    cbl++
  }
}
function uses(text,   s, m, t, nl, nl2, pre) {
  s = text; nl = 0
  while (match(s, /(\(|\{|⦃|\[)[^():\[\]{},=]*:[ \t\n]*[A-Za-z_][A-Za-z0-9_'.!?]*|\[[ \t\n]*[A-Za-z_][A-Za-z0-9_'.!?]*/)) {
    m = substr(s, RSTART, RLENGTH)
    pre = substr(s, 1, RSTART - 1); nl += gsub(/\n/, "", pre)
    s = substr(s, RSTART + RLENGTH)
    match(m, /[A-Za-z_][A-Za-z0-9_'.!?]*$/); t = substr(m, RSTART); sub(/.*\./, "", t)
    pre = m; nl2 = gsub(/\n/, "", pre)
    if (t ~ /[A-Z]/) {
      nuse++; utok[nuse] = t
      uloc[nuse] = pfx "named_use:" path ":" (cline + nl) ":" (cname != "" ? cname ": " : "") squash(m)
    }
    nl += nl2
  }
}
# A match names its definition unless it is the antecedent of `→`, or an
# identifier mentioning an advantage or a Secure/Hard predicate occurs between
# the start of the definition body (bs) and the bound (an assumed bound in an
# implication or binder).
# Token index at which the body of the current chunk, or the type of a field,
# starts (0 when there is none).
function bodystart(   i, d, t) {
  d = 0
  for (i = 1; i <= ntok; i++) {
    t = tok[i]
    if (isopen(t)) d++
    else if (isclose(t)) d--
    else if (ckind == "field" && t == ":" && d == 0) return i + 1
    else if (ckind != "field" && toks[i] > length(ctext)) return i
  }
  return 0
}
# The second pass over the tokens of a declaration, with the wider adversary
# types and advantage names: a bound that the first pass (multiline) matched at
# the same `≤` (seen) is left to it.
function wideflush(full, bs,   i, j, lastline, frag) {
  WIDE = 1
  i = 1
  while (i <= ntok) {
    if (tok[i] != "∀" || !(j = mforall(i))) { i++; continue }
    if (!(j in seen)) {
      lastline = (MF_END <= ntok) ? toks[MF_END] - 1 : length(full)
      frag = squash(substr(full, toks[i], lastline - toks[i] + 1))
      emit(pfx "nested", path, cline, (cname != "" ? cname ": " : "") frag)
      if (bs && toks[MF_SEG] >= toks[bs]) {
        if (ckind == "field") wnamed[sname] = 1
        else if ((ckind == "def" || ckind == "abbrev") && cstate == "body") wnamed[cname] = 1
      }
    }
    i = j + 1
  }
  WIDE = 0
}
# True when a `∀` on the first line of the text t binds the adversary of a
# numeric bound whose `≤` is on that line: the token test of `multiline`
# (mforall) applied to t alone. ADV_OPEN is set when the right-hand side of that
# bound runs to the end of t. Overwrites the token arrays, which `flush`
# rebuilds from the declaration text.
function advline(t,   i, j) {
  tokenize(t)
  for (i = 1; i <= ntok && tokl[i] == 0; i++)
    if (tok[i] == "∀" && (j = mforall(i)) && tokl[j] == 0) { ADV_OPEN = (MF_END > ntok); return 1 }
  return 0
}
# advline on source line ln (text t; continuation lines are rewritten to
# Unicode notation when asc is set), with the right-hand side read across
# continuation lines: while it runs to the end of the text, the next non-blank
# line indented deeper than line ln is appended (at most 8). A line indented no
# deeper than line ln ends the term.
function advcont(t, ln, asc,   k, ind, c) {
  match(L[ln], /^[ \t]*/); ind = RLENGTH
  k = ln; c = 0
  while (advline(t)) {
    if (!ADV_OPEN) return 1
    do { k++ } while (k <= NL && L[k] ~ /^[ \t]*$/)
    if (k > NL || c >= 8) return 1
    match(L[k], /^[ \t]*/)
    if (RLENGTH <= ind) return 1
    t = t "\n" (asc ? norm(L[k]) : L[k]); c++
  }
  return 0
}
function defmatch(bs,   k) {
  if (!bs || toks[MF_SEG] < toks[bs]) return 0
  for (k = MF_END; k <= ntok && isclose(tok[k]); k++) ;
  if (k <= ntok && tok[k] == "→") return 0
  for (k = bs; k <= MF_SEG; k++) if (isadv(tok[k]) || tok[k] ~ /Secure|Hard|Assumption/) return 0
  return 1
}
# True when source line k of the current chunk (0-based, ASCII notation
# rewritten) satisfies the line rule of `single`/`ascii`.
function linerule(k,   ls, r) {
  ls = (k in chunkline) ? chunkline[k] : ""
  if (ls !~ LRE) return 0
  r = substr(ls, index(ls, "≤") + LE)
  return r !~ ADVL
}
# --- sdist_named -------------------------------------------------------------
# True when the path lies where `sdist_named` counts: a protocol directory
# `Crypto/<P>/` outside the framework directories, an Examples directory, the
# ratchet bridges `Bridges/IrisBridge/Ratchet*` or `Choreography/ChannelCap*`
# (dev and core alike).
function sddir(p,   q, d) {
  q = p; sub(/^(\.\.\/CatCrypt-core\/)?CatCryptCore\//, "CatCrypt/", q); sub(/^\.\.\/catcrypt-compiler\//, "", q)
  if (q ~ /^CatCrypt\/Examples\//) return 1
  if (q ~ /^CatCrypt\/Crypto\/Bridges\/IrisBridge\/Ratchet/ || q ~ /^CatCrypt\/Crypto\/Choreography\/ChannelCap/) return 1
  if (!match(q, /^CatCrypt\/Crypto\/[^\/]+\//)) return 0
  d = substr(q, 17, RLENGTH - 17)
  return d !~ /^(UCMonad|Bridges|Choreography|CompilerSecurity|SecureCompilation|SecurityDefs|Constructions|Symbolic)$/
}
# An sdist-family token: `sdist`, `sdistD`, `sdistITreeN`, `kdistITreeN`,
# `UCMonadMetric.ucSdist`, `ucSdistV`, … (namespace stripped; not `SDistr`).
function issd(t) { sub(/.*\./, "", t); return t ~ /^([sk]dist|[A-Za-z]*[SK]dist)[A-Za-z0-9]*(_pt)?$/ }
function iskw(t) { return t ~ /^(fun|λ|let|in|do|if|then|else|match|with|return|have|show|from|by|at|Type|Prop|Sort|_)$/ }
function isname(t) { return t ~ /^[A-Za-z_\300-\337]/ && !iskw(t) }
function tokenize2(s,   used, t) {
  ntok = 0; used = 0; curl = 0
  while (match(s, TOK2)) {
    t = substr(s, RSTART, RLENGTH)
    tstart = used + RSTART
    used += RSTART + RLENGTH - 1
    s = substr(s, RSTART + RLENGTH)
    if (t == "\n") { curl++; continue }
    ntok++; tok[ntok] = t; tokl[ntok] = curl; toks[ntok] = tstart; toke[ntok] = used
  }
}
# Record in bn[] the names bound in tokens [a, b]: the names before `:` of a
# bracket group `(x y : T)`, the binders of `∀ ∃ fun λ` and the big operators up
# to their `,` or `=>`, `let x` and `x ←`. The binder types of `∀ ∃ fun λ`
# (`fun _ : Unit => G 0`) are marked in ty[] and are not game arguments.
function bindall(a, b,   k, j, m, d, t, u) {
  split("", ty)
  for (k = a; k <= b; k++) {
    t = tok[k]
    if (isopen(t)) {
      for (j = k + 1; j <= b && isname(tok[j]) && tok[j] !~ /\./; j++) ;
      if (j > k + 1 && j <= b && tok[j] == ":") for (m = k + 1; m < j; m++) bn[tok[m]] = 1
      continue
    }
    if (t == "∀" || t == "∃" || isbig(t) || t == "fun" || t == "λ") {
      d = 0; split("", tmd)
      for (j = k + 1; j <= b; j++) {
        u = tok[j]
        if (d == 0 && (u == "," || u == "=>")) break
        if (isopen(u)) { d++; tmd[d] = 0; continue }
        if (isclose(u)) { d--; if (d < 0) break; continue }
        if (u == ":" || u == "∈") { tmd[d] = 1; continue }
        if (tmd[d]) ty[j] = 1
        else if (isname(u)) bn[u] = 1
      }
    }
    if (t == "let" && k < b && isname(tok[k + 1])) bn[tok[k + 1]] = 1
    if (t == "←" && k > a && isname(tok[k - 1])) bn[tok[k - 1]] = 1
  }
}
# True when identifier t makes a game argument specific: a name neither bound
# (bn[]) nor whitelisted (`SPComp.*`, `mapSum`, `ucMapSum`, `ITreeN.bind'`,
# `liftSDistr`), or a projection `Q.f` of a bound name Q.
function sdspec(t,   b, r) {
  if (t !~ /^[A-Za-z_\300-\337]/ || iskw(t)) return 0
  if (t ~ /^SPComp\./ || t ~ /(^|\.)(mapSum|ucMapSum|liftSDistr)$/ || t ~ /(^|\.)ITreeN\.bind'$/) return 0
  b = t; sub(/\..*/, "", b); r = substr(t, length(b) + 2)
  if (b in bn) return r != "" && r !~ /^[0-9]/
  return 1
}
# For the sdist-family token at index i: the index of its bound (`≤`, or `=`
# followed by `0`) when the token's arguments reach it at depth 0 and the
# right-hand side, up to the next `, → ∧ ↔ ∨ :=` or closing bracket, mentions no
# sdist-family or advantage term; 0 otherwise. Sets SD_END (first token after
# the right-hand side) and SD_SPEC (the last two arguments, the compared games,
# are not both built from bound names and whitelisted combinators only).
function sdbound(i,   k, d, t, na, le, a, m) {
  d = 0; na = 0; le = 0
  for (k = i + 1; k <= ntok; k++) {
    t = tok[k]
    if (isopen(t)) { if (d == 0) { na++; argb[na] = k }; d++; continue }
    if (isclose(t)) { d--; if (d < 0) return 0; if (d == 0) arge[na] = k; continue }
    if (d > 0) continue
    if (t == "≤" || (t == "=" && k < ntok && tok[k + 1] == "0")) { le = k; break }
    if (t ~ /^[A-Za-z_0-9\300-\337]/ && !iskw(t)) { na++; argb[na] = k; arge[na] = k; continue }
    return 0
  }
  if (!le) return 0
  d = 0
  for (k = le + 1; k <= ntok; k++) {
    t = tok[k]
    if (isopen(t)) { d++; continue }
    if (isclose(t)) { d--; if (d < 0) break; continue }
    if (d == 0 && (t == "," || t == ":=" || issep(t))) break
    if (issd(t) || isadv(t)) return 0
  }
  SD_END = k; SD_SPEC = 0
  for (a = (na > 2 ? na - 1 : 1); a <= na && !SD_SPEC; a++)
    for (m = argb[a]; m <= arge[a]; m++) if (!(m in ty) && sdspec(tok[m])) { SD_SPEC = 1; break }
  return le
}
# Emit an sdist_named site unless excluded; 1 when emitted.
function sdemit(l, text,   rec) {
  rec = pfx "sdist_named:" path ":" l ":" text
  if (nx && excluded(rec)) return 0
  print rec; return 1
}
# A premise class equivalent to an sdist bound at its last argument, applied as
# `C G F ε` (core `Refinement/RRelWRPUC`): the compared games are the first two
# arguments. SD_END and SD_SPEC are set as by sdbound.
function isbcls(t) { sub(/.*\./, "", t); return t == "RefinesFamilyUpTo" }
function clsbound(i,   k, d, t, na, a, m) {
  d = 0; na = 0
  for (k = i + 1; k <= ntok; k++) {
    t = tok[k]
    if (isopen(t)) { if (d == 0) { na++; argb[na] = k }; d++; continue }
    if (isclose(t)) { d--; if (d < 0) break; if (d == 0) arge[na] = k; continue }
    if (d > 0) continue
    if (t ~ /^[A-Za-z_0-9\300-\337]/ && !iskw(t)) { na++; argb[na] = k; arge[na] = k; continue }
    break
  }
  if (na < 3) return 0
  SD_END = k; SD_SPEC = 0
  for (a = 1; a <= 2 && !SD_SPEC; a++)
    for (m = argb[a]; m <= arge[a]; m++) if (!(m in ty) && sdspec(tok[m])) { SD_SPEC = 1; break }
  return i
}
# True when token k starts a bound: an sdist bound or a bound class.
function bndat(k) { return (issd(tok[k]) && sdbound(k)) || (isbcls(tok[k]) && clsbound(k)) }
# The first counted sdist bound among tokens [a, b]: its token index, or 0.
function sdfirst(a, b,   k) {
  for (k = a; k <= b; k++) if (bndat(k) && SD_SPEC && SD_END <= b + 1) return k
  return 0
}
# sdist_named sites of the current chunk: one per hypothesis binder group
# before the conclusion colon (every group of a `variable`), one per antecedent
# of `→` in a conclusion, one per structure/class field, one per `Prop`-valued
# def/abbrev body. A counted field or `Prop` body names its definition for
# `named_use` (and the closure of `named_def`).
function sdflush(   full, lc, i, d, g, conc, k, lbl) {
  if (ckind == "") return
  if (ckind == "variable" || ckind == "structure" || ckind == "class") {
    tokenize2(ctext); split("", bn); bindall(1, ntok)
    if (ckind == "variable") { for (k in bn) fvars[k] = 1 }
    else { split("", sbn); for (k in bn) sbn[k] = 1 }
  }
  full = ctext; lc = length(ctext)
  if (cstate == "body") full = ctext " :=" cbody
  if (full ~ /[sk]dist|[SK]dist|RefinesFamilyUpTo/) {
    tokenize2(full); split("", bn); bindall(1, ntok)
    for (k in fvars) bn[k] = 1
    if (ckind == "field") for (k in sbn) bn[k] = 1
    lbl = (cname != "" ? cname ": " : "")
    if (ckind == "field") {
      if ((k = sdfirst(2, ntok)) && sdemit(cline, lbl squash(ctext))) addsd(sname, path, sline)
    } else {
      d = 0; g = 0; conc = 0
      for (i = 1; i <= ntok && toks[i] <= lc; i++) {
        if (isopen(tok[i])) { if (d == 0) g = i; d++ }
        else if (isclose(tok[i])) {
          d--; if (d < 0) d = 0
          if (d == 0 && g) { if (sdfirst(g + 1, i - 1)) sdemit(cline, lbl squash(substr(full, toks[g], toke[i] - toks[g] + 1))); g = 0 }
        }
        else if (tok[i] == ":" && d == 0 && ckind != "variable") { conc = i; break }
      }
      if (conc && ckind ~ /^(theorem|lemma|def|abbrev|instance|example)$/) {
        for (i = conc + 1; i <= ntok && toks[i] <= lc; i++) {
          if (!bndat(i) || !SD_SPEC) continue
          for (k = SD_END; k <= ntok && isclose(tok[k]); k++) ;
          if (k <= ntok && tok[k] == "→" && toks[k] <= lc)
            sdemit(cline, lbl squash(substr(full, toks[i], toke[SD_END - 1] - toks[i] + 1)))
          i = SD_END
        }
      }
      if (cstate == "body") {
        for (i = 1; i <= ntok && toks[i] <= lc; i++) ;
        if ((k = sdfirst(i, ntok)) && sdemit(cline, lbl squash(substr(full, toks[k], toke[SD_END - 1] - toks[k] + 1))))
          addsd(cname, path, cline)
      }
    }
  }
}
function addsd(name, p, l) {
  if (!(name in named)) { named[name] = "sdist: " p ":" l; nroot[name] = "s" }
}
function flush(   full, i, j, conc, d, g, t, lastline, colon, rec, frag, bs, narrow, wide) {
  if (ckind == "") return
  if (sdok) sdflush()
  full = ctext
  if (cstate == "body") full = ctext " :=" cbody
  narrow = 0; wide = 0
  if (full ~ /≤/ && full ~ /∀/) {
    narrow = (full ~ ADVL)
    wide = (full ~ /Advantage|advantage|Adv([^A-Za-z]|$)|adv([^A-Za-z]|$)/)
    if (narrow || wide) { tokenize(full); bs = bodystart(); split("", seen) }
  }
  if (narrow) {
    i = 1
    while (i <= ntok) {
      if (tok[i] != "∀") { i++; continue }
      j = mforall(i)
      if (!j) { i++; continue }
      lastline = (MF_END <= ntok) ? toks[MF_END] - 1 : length(full)
      frag = squash(substr(full, toks[i], lastline - toks[i] + 1))
      if (tokl[MF_LAST] != tokl[j] || !linerule(tokl[j]))
        emit(pfx "multiline", path, cline, (cname != "" ? cname ": " : "") frag)
      if (ckind == "field" && defmatch(bs)) adddef(sname, path, sline, "direct: " frag)
      else if ((ckind == "def" || ckind == "abbrev") && cstate == "body" && defmatch(bs)) adddef(cname, path, cline, "direct: " frag)
      seen[j] = 1
      i = j + 1
    }
  }
  if (wide) wideflush(full, bs)
  if (ckind == "field") {
    if (ctext ~ /∃/ || ctext ~ /[A-Za-z_]/) {
      tokenize(ctext)
      colon = 0
      for (i = 1; i <= ntok; i++) if (tok[i] == ":") { colon = i; break }
      if (colon) {
        if (ctext ~ /∃/ && hasexists(colon + 1, ntok))
          emit(pfx "exists", path, cline + tokl[colon], squash(ctext))
        for (i = colon + 1; i <= ntok; i++) if (tok[i] ~ /^[A-Za-z_]/) {
          t = tok[i]; sub(/.*\./, "", t); addcand(sname, path, sline, t); break
        }
      }
    }
  } else {
    if (ckind == "structure" || ckind == "class") {
      if (ctext ~ /extends/) {
        tokenize(ctext)
        for (i = 1; i <= ntok; i++) if (tok[i] == "extends") { addcand(cname, path, cline, identsof(i + 1, ntok)); break }
      }
    }
    if ((ckind == "def" || ckind == "abbrev") && cstate == "body") {
      tokenize(cbody)
      if (ntok && cbody !~ /→/) addcand(cname, path, cline, identsof(1, ntok))
      if (cbody ~ /∃/ && hasexists(1, ntok))
        emit(pfx "exists", path, cline, cname ": " squash(cbody))
    }
    uses(ctext)
    if (ctext ~ /∃/) {
      tokenize(ctext)
      conc = 0; d = 0; g = 0
      for (i = 1; i <= ntok; i++) {
        t = tok[i]
        if (isopen(t)) { if (d == 0) g = i; d++ }
        else if (isclose(t)) {
          d--
          if (d < 0) d = 0
          if (d == 0 && g && (!conc || (i < ntok && tok[i + 1] == "→")) && hasexists(g + 1, i - 1))
            emit(pfx "exists", path, cline + tokl[g], (cname != "" ? cname ": " : "") squash(substr(ctext, toks[g], toke[i] - toks[g] + 1)))
          if (d == 0) g = 0
        }
        else if (t == ":" && d == 0) conc = 1
      }
    }
  }
  ckind = ""
}
BEGIN {
  FS = "\t"; nx = 0; nuse = 0; ckind = ""; WIDE = 0
  if (EXCL != "") {
    while ((getline e < EXCL) > 0) {
      if (e ~ /^#/ || e ~ /^[ \t]*$/) continue
      if (e ~ /^"/ && (k = index(substr(e, 2), "\"")) > 1) { excl[++nx] = substr(e, 2, k - 1); continue }
      split(e, ea, /[ \t]+/); if (ea[1] != "") excl[++nx] = ea[1]
    }
    close(EXCL)
  }
  LE = length("≤")
  # An advantage name: one containing Advantage, or ending in _Adv or GameAdv.
  ADVL = "(Advantage|(_Adv|GameAdv)[0-9']*([^A-Za-z0-9_'.]|$))"
  TOK2 = "\n|:=|=>|[][(){},:=|]|⟨|⟩|⦃|⦄|∀|∃|≤|→|←|∧|↔|∨|∈|∑|∏|⨆|⨅|⋃|⋂|[0-9][0-9.]*|[A-Za-z_\300-\337]([A-Za-z0-9_'.!?\200-\337]|\342\202[\200-\234])*"
  LRE = "∀[^,]*,[^≤]*" ADVL "[^≤]*≤"
}
# The records that a MAP run prints, read in the order of the files they come from.
MERGE {
  nm = $2
  if ($1 == "@n") { if (!(nm in named) || (nroot[nm] == "s" && $3 == "a")) { named[nm] = $4; nroot[nm] = $3 } }
  else if ($1 == "@d") defsites[nm] = defsites[nm] $3
  else if ($1 == "@c") cand[nm] = cand[nm] " " $3
  else if ($1 == "@s") candsites[nm] = candsites[nm] $3
  else if ($1 == "@w") wnamed[nm] = 1
  else if ($1 == "@u") { nuse++; utok[nuse] = nm; uloc[nuse] = $3 }
  next
}
{
  repo = $1; path = $2
  pfx =(repo == "core" || repo == "compiler") ? repo "_" : ""
  cdepth = 0; ckind = ""; inbody = 0; fieldIndent = -1; NL = 0
  sdok = sddir(path); split("", fvars); split("", sbn)
  while ((getline raw < path) > 0) L[++NL] = strip(raw)
  close(path)
  for (ln = 1; ln <= NL; ln++) {
    s = L[ln]
    hit = 0
    if (FIXTURE && s ~ /^#path /) { flush(); inbody = 0; sdok = sddir(substr(s, 7)); split("", fvars); continue }
    if (s ~ LRE) {
      rhs = substr(s, index(s, "≤") + LE)
      if (rhs !~ ADVL && advcont(s, ln, 0)) { emit(pfx "single", path, ln, s); hit = 1 }
    }
    n = norm(s)
    if (!hit && n != s && n ~ LRE) {
      rhs = substr(n, index(n, "≤") + LE)
      if (rhs !~ ADVL && advcont(n, ln, 1)) emit(pfx "ascii", path, ln, s)
    }
    if (n ~ /^[ \t]*(@\[[^]]*\][ \t]*)*((private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)[ \t]+)*(theorem|lemma|def|abbrev|instance|structure|class|example|axiom|opaque|variable)([ \t]|$)/) {
      flush(); inbody = 0
      u = n; sub(/^[ \t]*(@\[[^]]*\][ \t]*)*/, "", u)
      while (match(u, /^(private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)[ \t]+/)) u = substr(u, RLENGTH + 1)
      match(u, /^[a-z]+/); kind = substr(u, 1, RLENGTH); u = substr(u, RLENGTH + 1); sub(/^[ \t]+/, "", u)
      name = ""
      if (kind != "variable" && kind != "example" && match(u, /^[^][ \t(){}:]+/)) name = substr(u, 1, RLENGTH)
      if (name ~ /^⦃/) name = ""
      startchunk(kind, name, ln); feed(n)
      continue
    }
    if (inbody && match(n, /^[ \t]+/)) {
      ind = RLENGTH
      if ((fieldIndent < 0 || ind <= fieldIndent) && n ~ /^[ \t]+[A-Za-z_][^ \t:(){}\[\]]*[ \t]*((\([^)]*\)|\{[^}]*\}|\[[^]]*\])[ \t]*)*:([^=:]|$)/) {
        if (fieldIndent < 0) fieldIndent = ind
        match(n, /^[ \t]+[^ \t:(){}\[\]]+/); u = substr(n, 1, RLENGTH); sub(/^[ \t]+/, "", u)
        flush(); startchunk("field", sname "." u, ln); feed(n)
        continue
      }
    }
    if (n ~ /^[^ \t]/) { flush(); inbody = 0; continue }
    if (ckind != "") feed(n)
  }
  flush()
}
END {
  if (MAP) {
    for (nm in named) print "@n\t" nm "\t" nroot[nm] "\t" named[nm]
    for (nm in defsites) print "@d\t" nm "\t" defsites[nm]
    for (nm in cand) print "@c\t" nm "\t" cand[nm]
    for (nm in candsites) print "@s\t" nm "\t" candsites[nm]
    for (nm in wnamed) print "@w\t" nm
    for (k = 1; k <= nuse; k++) print "@u\t" utok[k] "\t" uloc[k]
    exit
  }
  changed = 1
  while (changed) {
    changed = 0
    for (nm in cand) {
      if (nm in named) continue
      nt = split(cand[nm], ts, " ")
      for (k = 1; k <= nt; k++) if (ts[k] != nm && (ts[k] in named)) {
        named[nm] = "via " ts[k]; nroot[nm] = nroot[ts[k]]; defsites[nm] = candsites[nm]; changed = 1; break
      }
    }
  }
  for (nm in named) {
    ns = split(defsites[nm], ds, SUBSEP)
    for (k = 1; k <= ns; k++) if (ds[k] != "") {
      r = ds[k]; if (named[nm] ~ /^via / && nroot[nm] == "s") sub(/named_def:/, "sdist_named:", r)
      if (!(nx && excluded(r))) print r " (" named[nm] ")"
    }
  }
  for (k = 1; k <= nuse; k++) if ((utok[k] in named) && !(nx && excluded(uloc[k]))) print uloc[k]
  for (k = 1; k <= nuse; k++) if ((utok[k] in wnamed) && !(utok[k] in named)) {
    r = uloc[k]; sub(/named_use:/, "nested_use:", r)
    if (!(nx && excluded(r))) print r
  }
}
AWK

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

awk_scan() { LC_ALL=C awk -v EXCL="$1" "$AWKPROG" < "$2"; }

# awk_scan in $3 concurrent processes: each reads a part of the files, and the
# names, whose closure is over all files, are closed by a last process.
awk_scan_parts() {
  local dir part pid pids=()
  dir=$(mktemp -d "$tmp/parts.XXXXXX") || return 2
  split -n "l/$3" "$2" "$dir/in." || return 2
  for part in "$dir"/in.*; do
    LC_ALL=C awk -v EXCL="$1" -v MAP=1 "$AWKPROG" < "$part" > "$dir/map.${part##*.}" & pids+=($!)
  done
  for pid in "${pids[@]}"; do wait "$pid" || return 2; done
  cat "$dir"/map.* > "$dir/all"
  LC_ALL=C awk '!/^@[ndcswu]\t/' "$dir/all" || return 2
  LC_ALL=C awk '/^@[ndcswu]\t/' "$dir/all" > "$dir/records"
  LC_ALL=C awk -v EXCL="$1" -v MERGE=1 "$AWKPROG" < "$dir/records"
}

# The trees are scanned by concurrent processes; a process that fails fails the run.
scan() {
  local excl="" pid pids=()
  [ -f "$EXCLUDE" ] && excl="$EXCLUDE"
  tree_list own > "$tmp/own"
  cp "$tmp/own" "$tmp/first"
  if [ "$have_core" = 1 ]; then
    tree_list core > "$tmp/core"
    cat "$tmp/core" >> "$tmp/first"
    python3 "$SHAPES" < "$tmp/core" > "$tmp/out.core" & pids+=($!)
  fi
  if [ "$have_compiler" = 1 ]; then
    tree_list compiler > "$tmp/compiler"
    python3 "$SHAPES" < "$tmp/compiler" > "$tmp/out.compiler" & pids+=($!)
    awk_scan_parts "" "$tmp/compiler" 3 > "$tmp/out.compiler-rules" & pids+=($!)
  fi
  [ -s "$tmp/own" ] || { echo "no Lean file to scan" >&2; return 2; }
  python3 "$SHAPES" < "$tmp/own" > "$tmp/out.own" & pids+=($!)
  awk_scan_parts "$excl" "$tmp/first" 5 > "$tmp/out.rules" & pids+=($!)
  local rc=0
  for pid in "${pids[@]}"; do wait "$pid" || rc=2; done
  [ "$rc" = 0 ] || { echo "a scanner failed" >&2; return 2; }
  cat "$tmp"/out.* | LC_ALL=C sort -t: -k1,1 -k2,2 -k3,3n
}

# The sites of the fixture file as `category:line`, sorted.
fixture_sites() {
  {
    printf 'dev\t%s\n' "$FIXTURES" | LC_ALL=C awk -v EXCL="" -v FIXTURE=1 "$AWKPROG" \
      | awk -F: '{ print $1 ":" $3 }'
    printf 'dev\t%s\n' "$FIXTURES" | python3 "$SHAPES" --fixture
  } | LC_ALL=C sort -t: -k1,1 -k2,2n
}

if [ "$mode" = "--scan" ]; then
  shift
  [ "$#" -gt 0 ] || { echo "usage: $0 --scan FILE..." >&2; exit 2; }
  for f in "$@"; do
    [ -f "$f" ] || { echo "no such file: $f" >&2; exit 2; }
    printf 'dev\t%s\n' "$f"
  done > "$tmp/given"
  { awk_scan "" "$tmp/given" && python3 "$SHAPES" < "$tmp/given"; } \
    | LC_ALL=C sort -t: -k1,1 -k2,2 -k3,3n
  exit
fi

if [ ! -f "$FIXTURES" ] || [ ! -f "$FIXTURES_EXPECTED" ] || [ ! -f "$SHAPES" ]; then
  echo "FAIL: the scanner $SHAPES or the fixtures of this gate are missing."
  exit 1
fi
got=$(fixture_sites)
want=$(grep -v '^#' "$FIXTURES_EXPECTED" 2>/dev/null)
if [ "$got" != "$want" ]; then
  echo "FAIL: the rules disagree with $FIXTURES_EXPECTED on $FIXTURES:"
  diff <(printf '%s\n' "$want") <(printf '%s\n' "$got") | sed 's/^/  /'
  exit 1
fi
if [ "$mode" = "--self-test" ]; then echo "self-test: OK ($(printf '%s\n' "$got" | grep -c .) sites)"; exit 0; fi

sites=$(scan) || exit 2

if [ "$mode" = "--list" ]; then
  [ -n "$sites" ] && printf '%s\n' "$sites"
  exit 0
fi

# The categories in the order of the baseline file, and those recorded by site:
# the shapes everywhere, and every category of a tree that was never recorded by
# count only (the compiler, and core or the compiler scanning itself).
all_cats="$CATS"
site_cats="$SHAPE_CATS"
[ "$SELF" = dev ] || site_cats="$CATS"
if [ "$have_core" = 1 ]; then
  for c in $CATS; do all_cats="$all_cats core_$c"; done
  for c in $SHAPE_CATS; do site_cats="$site_cats core_$c"; done
fi
if [ "$have_compiler" = 1 ]; then
  for c in $CATS; do all_cats="$all_cats compiler_$c"; done
  for c in $CATS; do site_cats="$site_cats compiler_$c"; done
fi

count_of() {
  printf '%s\n' "$sites" | awk -F: -v c="$1" '$1 == c { n++ } END { print n + 0 }'
}

# The sites of category $1 as baseline lines, without line numbers.
site_lines() {
  printf '%s\n' "$sites" | LC_ALL=C awk -v c="$1" '
    index($0, c ":") == 1 {
      r = substr($0, length(c) + 2)
      p = index(r, ":"); path = substr(r, 1, p - 1); r = substr(r, p + 1)
      sub(/^[0-9]+:/, "", r); gsub(/[ \t]+/, " ", r); sub(/^ /, "", r); sub(/ $/, "", r)
      # A definition site is recorded by its name: how it was named (`direct: …`,
      # `via …`, `sdist: path:line`) depends on lines and on the order of the closure.
      if (c ~ /(named_def|sdist_named)$/) sub(/ \((direct: |via |sdist: ).*$/, "", r)
      printf "site\t%s\t%s\t%s\n", c, path, r
    }' | LC_ALL=C sort
}

if [ "$mode" = "--accept" ]; then
  # The records of a sibling that is absent are kept.
  kept=""
  if [ -f "$BASELINE" ]; then
    kept=$(awk -v ALL="$all_cats" '
      BEGIN { n = split(ALL, a, " "); for (i = 1; i <= n; i++) cur[a[i]] = 1 }
      /^site\t/ { split($0, f, "\t"); if (!(f[2] in cur)) print; next }
      /^sites=/ { if (!(substr($0, 7) in cur)) print; next }
      /^[a-z_]+=/ { c = $0; sub(/=.*/, "", c); if (!(c in cur)) print }' "$BASELINE")
  fi
  {
    count_of single
    for c in $all_cats; do
      [ "$c" = single ] && continue
      printf '%s=%s\n' "$c" "$(count_of "$c")"
    done
    for c in $site_cats; do printf 'sites=%s\n' "$c"; done
    for c in $site_cats; do site_lines "$c"; done
    [ -n "$kept" ] && printf '%s\n' "$kept"
    true
  } > "$tmp/baseline"
  cp "$tmp/baseline" "$BASELINE"
  echo "baseline written:"; grep -v -e '^site' "$BASELINE" | sed 's/^/  /'
  exit 0
fi

fail=0
for c in $all_cats; do
  cur=$(count_of "$c")
  if [ "$c" = single ]; then
    base=$(grep -m1 -oE '^[0-9]+' "$BASELINE" 2>/dev/null || true)
  else
    base=$(grep -m1 -E "^$c=" "$BASELINE" 2>/dev/null | cut -d= -f2 || true)
  fi
  if [ -z "$base" ]; then
    printf '%-28s current=%s baseline=none\n' "$c:" "$cur"
    echo "FAIL: $c has no baseline line in $BASELINE."; fail=1
    continue
  fi
  printf '%-28s current=%s baseline=%s\n' "$c:" "$cur" "$base"
  if grep -qxF "sites=$c" "$BASELINE"; then
    new=$(LC_ALL=C comm -23 <(site_lines "$c") \
      <(LC_ALL=C grep -F "site"$'\t'"$c"$'\t' "$BASELINE" | LC_ALL=C sort))
    if [ -n "$new" ]; then
      echo "FAIL: $c has a site that is not recorded:"
      printf '%s\n' "$new" | cut -f3- | sed 's/^/  /'
      fail=1
    fi
  else
    case " $site_cats " in
      *" $c "*) echo "FAIL: $c has no sites=$c line in $BASELINE."; fail=1 ;;
    esac
  fi
  if [ "$cur" -gt "$base" ]; then
    echo "FAIL: $c rose ($base -> $cur)."; fail=1
  elif [ "$cur" -lt "$base" ]; then
    echo "OK: $c fell ($base -> $cur). Run --accept to lower the baseline."
  fi
done
if [ "$SELF" = dev ]; then
  [ "$have_core" = 1 ] || echo "core_*: skipped ($CORE_DIR is not a git checkout)"
  [ "$have_compiler" = 1 ] || echo "compiler_*: skipped ($COMPILER_DIR is not a git checkout)"
fi
if [ "$fail" = 1 ]; then
  echo "State the new bound as an explicit reduction Adv(A) <= Adv_prim(B A) + ..., or"
  echo "record an information-theoretic game in $EXCLUDE with its reason."
  echo "A point mass, equal real and ideal games, a free body or frame and a returned"
  echo "argument are repaired in the statement: name the compiled body, the simulator or"
  echo "the reduction, or delete the statement."
  exit 1
fi
exit 0
