/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean

/-!
# `EnvSearch` — "loogle-lite" local declaration search over the elaborated env

This module provides two `#…Find` commands that query the **elaborated
environment** (every declaration reachable from the current imports), not the
source text. This is precisely the discovery problem `grep` cannot solve:
`grep` searches resolved *syntax*; these commands search resolved **names** and
pretty-printed **types**. So questions like

* "which defs *produce* a `Com jasminDialect`?" (the **result type** matters, not
  the spelling in any one file), or
* "which theorems mention `thirToJasmin`?"

are answered directly, even when the producing declaration lives in a different
file, is generated, or names its type via an abbreviation that `grep` would miss.

## Commands

* `#nameFind "substr" (cap)?` — list every declaration whose **name** contains
  `substr` (case-insensitive), printed as `name : <type>`. The name filter is
  cheap, so this scans the whole environment. Internal/auto-generated names
  (`_`-mangled, `.proof_…`, `._…`, `.match_…`, `.eq_…`, `.brecOn`, …) are
  skipped. Result count is capped (default 40); pass a trailing `Nat` to change
  the cap.

* `#typeFind "typeSubstr" (in <Namespace>)? (cap)?` — list every declaration
  whose **pretty-printed type** contains `typeSubstr`, printed as
  `name : <type>`. Pretty-printing every type in a Mathlib-scale environment is
  expensive, so a namespace prefilter is strongly recommended: with
  `in <Namespace>` only declarations whose name starts with that namespace are
  pretty-printed and matched (default namespace prefix: `CatCrypt`). Cap default
  is 40; pass a trailing `Nat` to change it.

* `#docFind "substr" (in <Namespace>)? (cap)?` — list every declaration whose
  **docstring** contains `substr` (case-insensitive), printed as
  `name : <docstring snippet around the match>`. This is the **concept** search:
  the human-readable capability descriptions in this project live in docstrings
  (e.g. "verified Pippenger bucket-accumulation MSM equals the naive sum"), which
  `#nameFind` (names only) and `#typeFind` (types only) both miss — so a
  cryptically-named theorem like `bucketMsm_eq_msm` is found by asking for
  "Pippenger" or "bucket". Docstring lookup is cheap (an env-extension hit, no
  pretty-printing), so the whole environment under the namespace prefilter
  (default `CatCrypt`) is scanned. Cap default 40. **Use this BEFORE writing a
  new `def`/theorem — it is the fastest way to catch that the capability already
  exists under an unguessable name.**

## How an agent uses this

Create (or reuse) a scratch file that `import`s `CatCrypt.Tactic.EnvSearch`
together with whatever module brings the declarations of interest into scope,
edit the `#…Find` query line, and read the resulting **info** diagnostic via
`mcp__lean-lsp__lean_diagnostic_messages`. Each command emits its hits as a
single multi-line `logInfo`, so one diagnostic carries the whole answer.

### Example queries

```lean
import CatCrypt.Tactic.EnvSearch
import CatCrypt.Crypto.SecureCompilation.ThirToComFront

-- defs/theorems whose *type* mentions `Com jasminDialect`, under `CatCrypt`:
#typeFind "Com jasminDialect" in CatCrypt

-- everything named like the front lowering:
#nameFind "thirToJasmin"

-- raise the cap and search a narrower namespace:
#typeFind "SPComp" in CatCrypt.Crypto.UOV 80
```
-/

open Lean Elab Command Meta

namespace CatCrypt.Tactic.EnvSearch

/-- Heuristic: is `n` an internal / auto-generated name we want to hide?
    Covers the compiler-mangled and proof-helper families that swamp a raw
    `name`-substring scan without being useful search hits. -/
def isInternalName (n : Name) : Bool :=
  -- Lean's own marker for inaccessible / internal names.
  n.isInternal ||
  -- Anonymous-constructor and macro-scope hygiene markers anywhere in the name.
  n.hasMacroScopes ||
  -- Known auto-generated suffixes/components.
  (n.components.any fun c =>
    match c with
    | .str _ s =>
        s.startsWith "_" ||
        s == "proof_1" || s.startsWith "proof_" ||
        s == "match_1" || s.startsWith "match_" ||
        s == "eq_1"    || s.startsWith "eq_" ||
        s == "eq_def"  ||
        s == "brecOn"  || s == "rec" || s == "recOn" ||
        s == "below"   || s == "ibelow" ||
        s == "casesOn" || s == "noConfusion" || s == "noConfusionType" ||
        s == "injEq"   || s == "sizeOf_spec" || s == "induct" ||
        s == "fwd" || s == "unfold"
    | _ => false)

/-- Lowercase substring containment test. -/
def containsCI (hay needle : String) : Bool :=
  let parts := (hay.toLower).splitOn (needle.toLower)
  parts.length > 1

/-- Characters that can legitimately appear *inside* a (possibly dotted)
    Lean identifier. Anything else is a separator when we collapse qualified
    names to their final component. -/
def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '\'' || c == '!' || c == '?'

/-- Collapse every dotted qualified identifier in `s` to its **final
    component** (`A.B.foo` ↦ `foo`), leaving all other text intact. This lets
    `#typeFind "Com jasminDialect"` match a type the pretty-printer rendered
    fully-qualified as `…VIR.Com …VIR.jasminDialect`, without the caller having
    to `open` the right namespaces or spell the full path. -/
def collapseQualified (s : String) : String := Id.run do
  let cs := s.toList
  let mut out : String := ""
  let mut tok : String := ""
  for c in cs do
    if isIdentChar c then
      tok := tok.push c
    else
      if tok ≠ "" then
        out := out ++ ((tok.splitOn ".").getLastD tok)
        tok := ""
      out := out.push c
  if tok ≠ "" then
    out := out ++ ((tok.splitOn ".").getLastD tok)
  return out

/-- Pretty-print a declaration's type to a single-line `String`, with binders
    and a generous width so the substring match sees a stable rendering. -/
def ppTypeString (ty : Expr) : MetaM String := do
  -- Drop universe-level clutter so the printed `name : type` stays readable.
  -- (Namespace abbreviation is handled at match time by `collapseQualified`,
  -- which works regardless of which namespaces the caller has `open`ed.)
  let fmt ← withOptions (fun o => o.setBool `pp.universes false) do
    ppExpr (← instantiateMVars ty)
  -- Render wide and collapse internal newlines so the printed `name : type`
  -- stays on one logical line per hit.
  let s := (fmt.pretty (width := 1000)).replace "\n" " "
  -- squeeze runs of spaces produced by the newline collapse
  return " ".intercalate (s.splitOn " " |>.filter (· ≠ ""))

/-- Format one hit as `name : type`. -/
def fmtHit (n : Name) (tyStr : String) : String :=
  s!"  {n} : {tyStr}"

/-- Flatten a docstring to one line (trim each line, drop blanks, single-space
    join), then return a ~180-char window around the first case-insensitive
    occurrence of `needle` (starting a little before it for context). Used to
    render a `#docFind` hit on one line. -/
def docSnippet (doc needle : String) : String :=
  let flat := " ".intercalate
    ((doc.replace "\n" " ").splitOn " " |>.filter (· ≠ ""))
  let chars := flat.toList
  let parts := (flat.toLower).splitOn needle.toLower
  match parts with
  | pre :: _ :: _ =>
    let start := pre.length - min pre.length 30
    let win := String.ofList ((chars.drop start).take 180)
    (if start > 0 then "…" else "") ++ win
  | _ => String.ofList (chars.take 180)

/-- Render the accumulated hit lines (or the empty-result message) for command
    `cmd` with the given `query`, noting truncation if the cap was reached. -/
def renderResult (cmd query : String) (hits : Array String)
    (scanned cap : Nat) (truncated : Bool) : MessageData :=
  if hits.isEmpty then
    m!"{cmd} {query}: no matches (scanned {scanned} decl(s))"
  else
    let header := s!"{cmd} {query}: {hits.size} hit(s)" ++
      (if truncated then s!" (capped at {cap}; more exist)" else "")
    let body := String.intercalate "\n" hits.toList
    m!"{header}\n{body}"

/-! ## `#nameFind` -/

/-- `#nameFind "substr" (cap)?` — declarations whose **name** contains `substr`
    (case-insensitive). Scans the whole environment (cheap, name-only); skips
    internal/auto-generated names; prints `name : <type>`. Cap default 40. -/
elab "#nameFind " s:str cap?:(num)? : command => do
  let needle := s.getString
  let cap := (cap?.map (·.getNat)).getD 40
  liftTermElabM do
    let env ← getEnv
    let mut hits : Array String := #[]
    let mut truncated := false
    let mut scanned := 0
    for (n, ci) in env.constants.toList do
      if isInternalName n then continue
      scanned := scanned + 1
      if containsCI n.toString needle then
        if hits.size ≥ cap then
          truncated := true
          break
        let tyStr ← (do ppTypeString ci.type) <|> pure "<type print failed>"
        hits := hits.push (fmtHit n tyStr)
    logInfo (renderResult "#nameFind" s!"\"{needle}\"" hits scanned cap truncated)

/-! ## `#typeFind` -/

/-- `#typeFind "typeSubstr" (in <Namespace>)? (cap)?` — declarations whose
    **pretty-printed type** contains `typeSubstr`. A namespace prefilter keeps
    the (expensive) pretty-printing bounded; default prefix `CatCrypt`. Prints
    `name : <type>`. Cap default 40. -/
elab "#typeFind " s:str ns?:(" in " ident)? cap?:(num)? : command => do
  let needle := s.getString
  let cap := (cap?.map (·.getNat)).getD 40
  let nsPrefix : Name :=
    match ns? with
    | some stx => stx.raw[1].getId
    | none => `CatCrypt
  liftTermElabM do
    let env ← getEnv
    let mut hits : Array String := #[]
    let mut truncated := false
    let mut scanned := 0
    for (n, ci) in env.constants.toList do
      if isInternalName n then continue
      -- Namespace prefilter BEFORE pretty-printing (the cost guard).
      unless nsPrefix.isPrefixOf n do continue
      scanned := scanned + 1
      let tyStr ← (do ppTypeString ci.type) <|> pure ""
      -- Match the needle against the rendered type AND a form in which every
      -- qualified name is collapsed to its final component, so a short query
      -- like "Com jasminDialect" hits a fully-qualified rendering.
      if containsCI tyStr needle || containsCI (collapseQualified tyStr) needle then
        if hits.size ≥ cap then
          truncated := true
          break
        hits := hits.push (fmtHit n tyStr)
    let q := s!"\"{needle}\" in {nsPrefix}"
    logInfo (renderResult "#typeFind" q hits scanned cap truncated)

/-! ## `#docFind` — search the human-readable capability descriptions -/

/-- `#docFind "substr" (in <Namespace>)? (cap)?` — declarations whose
    **docstring** contains `substr` (case-insensitive). The CONCEPT search:
    capability descriptions live in docstrings, which `#nameFind`/`#typeFind`
    miss. Namespace prefilter (default `CatCrypt`); prints `name : <snippet>`.
    Cap default 40. Run this BEFORE building a new declaration. -/
elab "#docFind " s:str ns?:(" in " ident)? cap?:(num)? : command => do
  let needle := s.getString
  let cap := (cap?.map (·.getNat)).getD 40
  let nsPrefix : Name :=
    match ns? with
    | some stx => stx.raw[1].getId
    | none => `CatCrypt
  liftTermElabM do
    let env ← getEnv
    let mut hits : Array String := #[]
    let mut truncated := false
    let mut scanned := 0
    for (n, _ci) in env.constants.toList do
      if isInternalName n then continue
      unless nsPrefix.isPrefixOf n do continue
      let some doc ← findDocString? env n | continue
      scanned := scanned + 1
      if containsCI doc needle then
        if hits.size ≥ cap then
          truncated := true
          break
        hits := hits.push (fmtHit n (docSnippet doc needle))
    let q := s!"\"{needle}\" in {nsPrefix}"
    logInfo (renderResult "#docFind" q hits scanned cap truncated)

end CatCrypt.Tactic.EnvSearch
