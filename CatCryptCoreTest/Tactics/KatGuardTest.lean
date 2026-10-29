/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.KatGuard

/-!
# Tests of `#kat` and `#kat_kernel`

Each passing check is a fixture: its evaluation is small and permanent. The failing
cases are wrapped in `#guard_msgs`, so that the error message is itself checked.
-/

/-- A small function whose values the checks pin. -/
def katSquare (n : Nat) : Nat := n * n

#kat katSquare 12 == 144

set_option kat.ms 50 in
set_option kat.heartbeats 2000 in
#kat katSquare 3 = 9

#kat_kernel katSquare 7 = 49

set_option kat.heartbeats 2000 in
#kat_kernel (List.range 10).sum = 45

/-- error: Expression
  katSquare 3 == 10
did not evaluate to `true` -/
#guard_msgs in
#kat katSquare 3 == 10

-- A kernel check over a two-thousand-element list exceeds a budget of one thousand heartbeats.
set_option kat.heartbeats 1 in
/-- maximum number of heartbeats (1) has been reached -/
#guard_msgs (substring := true) in
#kat_kernel (List.range 2000).sum = 1999000
