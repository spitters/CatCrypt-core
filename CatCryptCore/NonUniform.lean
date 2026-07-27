/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.Sample
import CatCryptCore.NonUniform.Conditional
import CatCryptCore.NonUniform.Product
import CatCryptCore.NonUniform.CouplingRules
import CatCryptCore.NonUniform.UnaryRules
import CatCryptCore.NonUniform.Bernoulli
import CatCryptCore.NonUniform.CenteredBinomial
import CatCryptCore.NonUniform.Limit
import CatCryptCore.NonUniform.WhileApprox
import CatCryptCore.NonUniform.WhileApproxMono
import CatCryptCore.NonUniform.WhileUnary
import CatCryptCore.NonUniform.WhileRelational
import CatCryptCore.NonUniform.While
import CatCryptCore.NonUniform.WhileRelationalLimit

/-!
# Non-uniform sampling

`SPComp.sample` samples uniformly from a finite nonempty type, which is the only
sampling combinator in `Core.Code`. This tree adds `sampleFrom d` for an arbitrary
`SDistr d`, together with the pRHL and pHL rules for reasoning about it.

## Layout

* `Sample` — the combinator, its monadic laws, its mass/losslessness
  characterisation, and `ofPMF` for total distributions
* `Conditional` — restriction, rescaling, conditioning and `excepted`, with the
  weight, support and point-mass results for each
* `Product` — the independent product of two sub-distributions and of a
  `Fin n`-indexed family, with `mass_bind_of_mass_one` and the marginals
* `CouplingRules` — pushforward couplings and the general pRHL sampling rule,
  with the uniform rules re-derived as instances
* `UnaryRules` — event and success probability of a program that starts with a
  general sample
* `Bernoulli` — biased coins, the negation coupling, and its pRHL step
* `CenteredBinomial` — the ML-KEM noise distribution over `ℤ`, its symmetry under
  negation, and the resulting sign-independence of a noise term
* `Limit` — the limit of a sequence of sub-distributions that is non-decreasing on
  values, and the two laws commuting that limit with `bind` on either side
* `WhileApprox` — `whileApprox guard body n`, which runs `body` at most `n` times
  while `guard` holds and fails when the budget runs out
* `WhileApproxMono` — the approximants are non-decreasing on values and
  non-increasing on failure as the budget grows, and their value mass stays
  summable to at most one
* `WhileUnary` — the pHL invariant rule at each budget, and the probability-one
  form under a losslessness hypothesis
* `WhileRelational` — the pRHL synchronous invariant rule at each budget, over two
  loops whose guards the invariant keeps equal
* `While` — `whileLoop guard body` as the limit of the approximants, and the pHL
  rule for it
* `WhileRelationalLimit` — the pRHL rule at the loop, over a non-decreasing family
  of couplings built by recursion on the budget

The pHL rule transports from the approximants to the limit because `pHoare`
constrains the support, and an outcome of the limit is an outcome of some
approximant. `rHoare` asserts that a coupling exists, so it does not transport
that way: couplings obtained for each budget separately need not be comparable,
and only a non-decreasing family has a limit that couples the two loops. The
family is therefore constructed rather than obtained, by recursion on the budget
from one chosen coupling of the two bodies.

`sampleFrom (SDistr.uniform α) = SPComp.sample α` holds by `rfl`, and the
derived-instance `example`s in `CouplingRules` and `UnaryRules` state the uniform
rules verbatim, so the uniform API is untouched.

The one-sided rules `rHoare_sampleFrom_l/r` carry a `SDistr.mass d = 1` hypothesis
that the uniform versions `rHoare_sample_l/r` do not need, because
`SDistr.mass (SDistr.uniform α) = 1` is automatic. The uniform rules are therefore
corollaries, not instances of a strictly weaker statement.
-/
