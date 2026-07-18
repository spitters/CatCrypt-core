# Contributing

Thanks for your interest in CatCrypt Core.

## Building

See the Build section of `README.md`. In short: install
[elan](https://github.com/leanprover/elan), then

```
lake exe cache get
lake build
```

## Ground rules

- **No `sorry`/`admit`.** CI rejects builds that produce
  `declaration uses 'sorry'`.
- **No new axioms.** The axiom allowlist (see `README.md` § Trust edges) is
  checked by CI. If you believe a new trust edge is justified, open an issue
  first and include a literature reference.
- **`set_option autoImplicit false`** is set package-wide; keep it.
- Every file carries the standard copyright header (MIT, "CatCrypt
  Contributors") and a `/-! ... -/` module docstring stating what is proved —
  and, where relevant, what is deliberately not.
- Security statements are reductions: hypotheses state primitive security,
  the conclusion states protocol security. Prefer standard assumptions
  (see `Crypto/Assumptions/Catalog.lean`).

## Pull requests

Keep PRs focused. A PR that adds a lemma should not also reformat
neighbouring proofs. CI must pass; please run `lake build` locally before
submitting.

## Reporting issues

Use the GitHub issue tracker. For suspected unsoundness (an axiom that
proves too much, a vacuous security statement), please mark the issue as
such — these take priority.
