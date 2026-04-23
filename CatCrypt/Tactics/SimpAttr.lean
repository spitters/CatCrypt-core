/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean

/-!
# CatCrypt Simp Attribute Declarations

This file declares the named simp sets used by CatCrypt tactics.

**Important**: `register_simp_attr` creates simp attributes that cannot be
used in the same file they are declared in. This file must be imported
by any file that wants to tag lemmas with these attributes.

## Simp sets

* `ssprove_simpl` - SPComp normalization (monad laws, dead code, contraction)
* `ssprove_eval` - Deep→shallow bridge evaluation lemmas
-/

/-- `ssprove_simpl` is the named simp set for normalizing SPComp terms.

Collects lemmas for:
- Monad laws (bind associativity, pure/bind identity)
- Dead code elimination (unused sample, get, pure)
- Contraction rules (duplicate get, put, put-get)
- Copy propagation (set-get same location)
-/
register_simp_attr ssprove_simpl

/-- `ssprove_eval` is the named simp set for deep→shallow bridge evaluation.

Collects lemmas for evaluating RawCode into SPComp.
-/
register_simp_attr ssprove_eval
