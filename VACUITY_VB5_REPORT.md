# Vacuity sweep, severity 3, interface items (VB5)

Branch `work/vacuity-vb5`, based on `origin/work/auto-corpus`. Items S3-6, S3-5, S3-7a and
S3-8 from the section "Severity 3" of `VACUITY_SWEEP_REPORT.md`
(branch `work/vacuity-sweep`). One commit per item, in the order below. No item was reverted.

The diff adds no `sorry`, no `native_decide` and no axiom (checked with
`git diff origin/work/auto-corpus HEAD | grep '^+' | grep 'sorry\|native_decide\|axiom\|admit'`,
which prints nothing).

## S3-6: `class ValidCode` (`CatCryptCore/Package/ValidPackage.lean`)

Commit `18fd8a5`.

### Before

```lean
class ValidCode (L : Locations) (I : Interface) (α : Type*) (c : SPComp α) : Prop where
  reads_in_L : ∀ l v h, l ∉ L →
    (c h).bind (fun (a, _) => SDistr.pure a) =
    (c (Heap.set h l v)).bind (fun (a, _) => SDistr.pure a)
  writes_in_L : ∀ l h, l ∉ L →
    (c h).bind (fun (a, h₁) => SDistr.pure (a, h₁.get l)) =
    (c h).bind (fun (a, _) => SDistr.pure (a, h.get l))
```

### After

```lean
class ValidCode (L : Locations) (α : Type*) (c : SPComp α) : Prop where
  frame : ∀ l v h, l ∉ L →
    c (Heap.set h l v) = (c h).bind (fun p => SDistr.pure (p.1, Heap.set p.2 l v))
  writes_in_L : ∀ l h, l ∉ L → ∀ p, (c h) (some p) ≠ 0 → p.2.get l = h.get l
```

`frame` constrains every read. Take a location `l ∉ L` and any value `v`. Running the
code after overwriting `l` with `v` gives the same distribution over results and final
heaps as running it first and then overwriting `l` in each final heap. So neither the
result nor the final value at any other location depends on the value at `l`. In
particular, copying `l ∉ L` into a location `k ∈ L` violates `frame`. `writes_in_L`
constrains every write: each final heap in the support keeps the initial value at each
location outside `L`.

`SPComp α = Heap → SDistr (α × Heap)` is a function and has no syntax, so the predicate
is semantic and is not defined by recursion on the code. The recursive, syntactic
predicate on code with oracle calls is `CatCrypt.Deep.ValidCode` (inductive on
`RawCode`). An `SPComp` makes no imported call, so `I` had no possible use and is
dropped.

### Proved

- `ValidCode.reads_in_L`: the old field `reads_in_L`, derived from `frame`.
- Instances `ValidCode.pure`, `ValidCode.fail`, `ValidCode.sample` and `ValidCode.bind`
  (the last from instances for `c` and for every `f a`).
- Theorems `ValidCode.get (l₀) (h₀ : l₀ ∈ L)` and `ValidCode.set (l₀) (w) (h₀ : l₀ ∈ L)`.
- `ValidPackage.validCode_weaken`, restated without `I₁ I₂`.

Before this change CatCrypt-core had no instance of the class. `par_valid` and
`empty_valid` go through unchanged.

### Users adapted

- `ValidPackage.valid_impl` now reads `ValidCode L e.fun_.tgt (e.fun_.impl x)`.
- `ValidPackage.validCode_weaken`.
- The docstring example of `ssprove_valid` (`CatCryptCore/Tactics/Basic.lean`).

`ValidPackage L I E P` keeps its parameter `I`, because `par_valid` and
`Invariant/EqUpToInv.lean` use it. After this change no field of `ValidPackage` mentions
`I`.

### Names to search for in other repositories

- `CatCrypt.Package.ValidCode`: one argument fewer (`I` removed). The fields
  `reads_in_L` and `writes_in_L` change. `reads_in_L` is now the theorem
  `ValidCode.reads_in_L`. `writes_in_L` now has a support form. `frame` is new.
- `CatCrypt.Package.ValidPackage.validCode_weaken`: the implicit arguments `I₁ I₂` are
  removed.

## S3-5: `ValidCode.embed` and `ValidCode.ofSPComp`

Commit `491e37c`.

Each user needs an arbitrary embedding:
- The reifier (`Deep/Reflect.lean`) turns every opaque `SPComp` subterm into an `embed`
  leaf and proves its validity with the instance `IsValid.embed`.
- `wrapMainNomPkg` (`Crypto/NomPkgBridge.lean`) embeds `heapReset h₀`, which overwrites
  the whole heap, and an arbitrary post-processing `D b`.

Neither use can supply a proof that the embedded computation stays within the declared
locations. So the embeddings are renamed, not restricted.

The S3-6 predicate is stated on `Package.Locations`; `Deep.ValidCode` uses
`LocSet = Finset ℕ`. No checked variant was added.

### Before

```lean
-- Deep/Package.lean
| embed : ∀ {α : Type u} (c : Core.SPComp α), ValidCode L α (RawCode.embed c)
instance IsValid.embed {L : LocSet} {α : Type u} (c : Core.SPComp α) :
    IsValid L (RawCode.embed c)
-- Crypto/EvalComplete.lean
theorem ValidCode.ofSPComp {α : Type} (c : SPComp α) (L : LocSet) :
    ValidCode L α (RawCode.ofSPComp c)
noncomputable def ValidCodeBundle.ofSPComp {α : Type} (c : SPComp α) (L : LocSet) :
    ValidCodeBundle L α
```

### After

```lean
/-- An embedded shallow computation is accepted without any check: its heap
    accesses are not inspected, so `ValidCode L` does not constrain the locations
    used by an `embed` leaf. -/
| embedUnchecked : ∀ {α : Type u} (c : Core.SPComp α), ValidCode L α (RawCode.embed c)
instance IsValid.embedUnchecked {L : LocSet} {α : Type u} (c : Core.SPComp α) :
    IsValid L (RawCode.embed c)
theorem ValidCode.ofSPCompUnchecked {α : Type} (c : SPComp α) (L : LocSet) :
    ValidCode L α (RawCode.ofSPComp c)
noncomputable def ValidCodeBundle.ofSPCompUnchecked {α : Type} (c : SPComp α) (L : LocSet) :
    ValidCodeBundle L α
```

Each docstring states that the heap accesses of the embedded computation are not checked
against `L`.

### Users adapted

- `ValidCode.mono` and `substOracle_valid`: induction cases renamed.
- `wrapMainNomPkg` (`Crypto/NomPkgBridge.lean`).
- Docstrings in `Deep/Package.lean`, `Deep/Reflect.lean`, `Deep/ReflectOracleDemo.lean`
  and `Crypto/EvalComplete.lean`.

### Names to search for in other repositories

- `ValidCode.embed`: the constructor, including `| embed c =>` cases in `induction` or
  `cases` on `CatCrypt.Deep.ValidCode`.
- `IsValid.embed`.
- `ValidCode.ofSPComp`.
- `ValidCodeBundle.ofSPComp`.

`RawCode.embed` and `RawCode.ofSPComp` are unchanged.

## S3-7a: `RawPackage.link`, `RawPackage.idPkg` (`CatCryptCore/Package/RawPackage.lean`)

Commit `f686c7b`.

### Before

```lean
noncomputable def link (P₁ _P₂ : RawPackage) : RawPackage :=
  P₁
noncomputable def idPkg (I : Interface) : RawPackage := empty
-- Nominal/NomPackage.lean
noncomputable def link (P₁ P₂ : NomPackage) : NomPackage :=
  ⟨RawPackage.link P₁.raw P₂.raw, P₁.support ∪ P₂.support⟩
```

### After

All three definitions are deleted.

A `RawPackage` stores its operations as `S → SPComp T`, which make no imported call. So
linking has nothing to resolve, and an identity package has nothing to forward. The
module docstring of `Package/RawPackage.lean` gains a section "Sequential composition
and identity". It names the replacements:
- `CatCrypt.Deep.DeepPackage.link`: oracle substitution through `RawCode.substOracle`.
  Its nominal form is `CatCrypt.Deep.NomPackage.link`. `runPkg_link` and
  `runPkg_link_assoc` (`Crypto/NomAdvantage.lean`) state its evaluation and
  associativity.
- `CatCrypt.Deep.DeepPackage.id`: forwards each operation as an oracle call.
  `DeepPackage.link_id_right_code` gives the code of `link p (id p.imports)`.

The module docstring of `Nominal/NomPackage.lean` names `CatCrypt.Deep.NomPackage.link`.

### Users adapted

- `CatCrypt.Nominal.NomPackage.link`: the only user of `RawPackage.link`, itself without
  users. Deleted.
- The docstring of `security_based_on_prf` (`Examples/PRFMAC.lean`), which referred to
  the WARNING.

`idPkg` had no users.

### Names to search for in other repositories

- `RawPackage.link`.
- `RawPackage.idPkg`.
- `CatCrypt.Nominal.NomPackage.link`. The deep `CatCrypt.Deep.NomPackage.link` is
  unchanged.

`NomPackage.support` and `rename` (the same row of the sweep report) are not part of
S3-7a and are unchanged.

## S3-8: `class RelQ0` (`CatCryptCore/Relational/RelationalQ0.lean`)

Commit `6c502e7`.

### Before

The fields were `pure'`, `bind'`, `liftR`, `liftR_pure`, `liftR_bind`, `liftR_mono_rel`
and `liftR_mono_eps`. No field related `liftR` to a semantics, so `liftR := True`
satisfied all of them.

### After

Four fields are added:

```lean
  denote : {α : Type} → T α → SDistr α
  denote_pure : ∀ {α : Type} (a : α), denote (pure' a) = SDistr.pure a
  denote_bind : ∀ {α β : Type} (m : T α) (k : α → T β),
    denote (bind' m k) = (denote m).bind (fun a => denote (k a))
  liftR_adequate : ∀ {α β : Type} {ε : ℝ≥0∞} {R : α → β → Prop} {m₁ : T α} {m₂ : T β},
    liftR ε R m₁ m₂ → liftRApprox ε R (denote m₁) (denote m₂)
```

`liftRApprox ε R d₁ d₂` is an `ε`-approximate sub-coupling of `d₁` and `d₂` supported
in `R`. At grade 0 it is an exact coupling (`liftRApprox_zero_iff`).

New theorem:

```lean
theorem RelQ0.not_liftR_zero_pure_empty {T : Type → Type} [RelQ0 T] {α β : Type}
    (a : α) (b : β) :
    ¬ RelQ0.liftR 0 (fun (_ : α) (_ : β) => False) (RelQ0.pure' (T := T) a)
      (RelQ0.pure' (T := T) b)
```

So no `RelQ0` has `liftR := True`.

### Instances proved

These are all the `RelQ0` instances in CatCrypt-core:

- `instRelQ0SDistr`: `denote m := m`. `denote_pure` and `denote_bind` hold by `rfl`;
  adequacy is the identity, since `liftR = liftRApprox`.
- `instRelQ0PMF` (`XDijkstra/Rel/XRelQ0.lean`): `denote μ := μ.map some`.
  - `denote_pure` is `PMF.pure_map`.
  - `denote_bind` follows from `PMF.map_bind` and `PMF.bind_map`.
  - Adequacy is the new theorem
    `liftRApprox_map_some_of_couples : Couples μ ν R → ∀ ε, liftRApprox ε R (μ.map some) (ν.map some)`.

No instance was left with a docstring note.

### Users adapted

The generic users (`XRelSpecMonad`, `XRelMvcgen`, `XLargeReduction`, `XRelMvcgenControl`,
`XCombinedAutomation`, `XCategoricalModelRel`, `AutoDispatchExtTest`) use only the old
fields and build unchanged.

### Names to search for in other repositories

- `RelQ0`: every instance, including those under `CatCrypt/Crypto/Bridges/XDijkstra` in
  the dev repository, must now provide `denote`, `denote_pure`, `denote_bind` and
  `liftR_adequate`.
- New: `RelQ0.not_liftR_zero_pure_empty` and `liftRApprox_map_some_of_couples`.

## Builds

`export PATH=$HOME/.elan/bin:$PATH`, from the repository root. Every build is a plain
`lake build`. No build printed `Built Mathlib.`.

For each item, the targets were the edited modules and every CatCrypt-core module that
imports one of them, directly or transitively. The list was computed from the `import`
lines.

| Item | Targets | Result | Jobs | Wall time |
|---|---|---|---|---|
| S3-6 | `Package.ValidPackage`, `Tactics.Basic` and 59 modules that import them (61 targets) | success | 3709 | 418 s (first build in the session; most CatCrypt-core modules were compiled here) |
| S3-5 | `Deep.Package`, `Crypto.EvalComplete`, `Crypto.NomPkgBridge`, `Deep.Reflect`, `Deep.ReflectOracleDemo` and their importers (87 targets) | success | 3709 | 70 s |
| S3-7a | `Package.RawPackage`, `Nominal.NomPackage`, `Examples.PRFMAC` and their importers (97 targets) | success | 3709 | 75 s |
| S3-8 | `Relational.RelationalQ0`, `XDijkstra.Rel.XRelQ0` and their importers (17 targets) | success | 3709 | 27 s |
| all | `lake build CatCryptCore` (whole library, after all items) | success, `Build completed successfully (3709 jobs).` | 3709 | 3 s (every module already up to date from the per-item builds) |

### Warnings in edited files

The final build reports these warnings in edited files. All are unused-variable warnings
on lines that occur unchanged in `origin/work/auto-corpus`:

- `Package/ValidPackage.lean`: `e` in `empty_valid`.
- `Deep/Package.lean`: `op` (three times) and `h_exp`.
- `Crypto/EvalComplete.lean`: `op` (twice).
- `Nominal/NomPackage.lean`: `hDisj₁₃` and `hIds₁₃`.

The unused-variable warning on `I` in `RawPackage.idPkg` is gone with the definition. No
new warning appears in an edited file.
