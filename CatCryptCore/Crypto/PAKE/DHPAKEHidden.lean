/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.DHPAKE
public import CatCryptCore.Crypto.SamplerCert

/-!
# Diffie–Hellman PAKE with a hidden share: the bound with a sampler certificate

A hidden share is a message drawn as a representative of the public value from a sampler
`rep` on strings `V` (the inverse map of an encoding such as Elligator 2) and sent under a
password-keyed bijection `E pw : V ≃ W`. A `SamplerCert` `c` of `rep` against the uniform
law on `V` gives the message certificate `MsgCert.hidden`: under every password the message
is within `c.δ` of the uniform law on `W`, which does not depend on the password.

With the client's share hidden and the server's share in clear (a message law `m` that does
not depend on the password), the generic bound `sampled_success_le` reads
(`hidden_success_le`)
`Pr[success] ≤ 1/2 + qS/|Pw| + qH · CDH_Advantage (cdhDef P) (cdhReduction P D) + c.δ`.

## Main definitions

* `MsgCert.hidden` — the message certificate of a hidden share

## Main results

* `hidden_success_le` — the bound with one hidden share and one share in clear
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.DH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

variable {S G W Pw K : Type} [Fintype S] [Nonempty S] [SampleableType G] [DecidableEq W]
  [Fintype Pw] [Nonempty Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] {qH qS : ℕ}

omit [Fintype S] [Nonempty S] [SampleableType G] [DecidableEq W] [Fintype Pw] [Nonempty Pw]
  [DecidableEq Pw] [Fintype K] [Nonempty K] in
/-- **A hidden share**: a message that is a representative drawn from `rep`, sent under a
    password-keyed bijection `E pw` of strings, has the certificate of `rep`: the reference
    law is uniform and the bound is that of a sampler certificate `c` of `rep` against the
    uniform law on representatives. -/
noncomputable def MsgCert.hidden {V : Type} [Fintype V] [Nonempty V] [Fintype W] [Nonempty W]
    (key : Pw → PMF (S × W)) (c : SamplerCert V) (rep : PMF V) (hμ : c.μ = rep.map some)
    (hν : c.ν = (PMF.uniformFintype V).map some) (E : Pw → V ≃ W)
    (h : ∀ pw, (key pw).map Prod.snd = rep.map (E pw)) : MsgCert key where
  ν := PMF.uniformFintype W
  δ := c.δ
  tv_le pw := by
    rw [h pw, ← PMF.uniformFintype_map_equiv (E pw)]
    refine (tvDist_map_map_some_le _ _ _).trans ?_
    rw [← hμ, ← hν]
    exact c.tv_le

/-- **The bound with a hidden client share.** The client's message is a representative drawn
    from `rep` and sent under the bijection `E pw`, with a sampler certificate `c` of `rep`
    against the uniform law; the server's message law `m` does not depend on the password.
    For every adversary `D` the success probability in the find-then-guess game is at most
    `1/2 + qS/|Pw| + qH · CDH_Advantage (cdhDef P) (cdhReduction P D) + c.δ`. -/
theorem hidden_success_le {V : Type} [Fintype V] [Nonempty V] [Fintype W] [Nonempty W]
    (P : SampledDHPAKE S G W Pw) (c : SamplerCert V) (rep : PMF V) (hμ : c.μ = rep.map some)
    (hν : c.ν = (PMF.uniformFintype V).map some) (E : Pw → V ≃ W)
    (hC : ∀ pw, (P.keyC pw).map Prod.snd = rep.map (E pw)) (m : PMF W)
    (hS : ∀ pw, (P.keyS pw).map Prod.snd = m) (D : DHPAKEAdversary Pw W K qH qS G) :
    dhpakeGame P D true ≤ 2⁻¹ + qS * (Fintype.card Pw : ℝ≥0∞)⁻¹ +
      qH * CDH_Advantage (cdhDef P) (cdhReduction P D) + c.δ := by
  have h := sampled_success_le P (MsgCert.hidden P.keyC c rep hμ hν E hC)
    (MsgCert.clear P.keyS m hS) D
  simpa [MsgCert.hidden, MsgCert.clear] using h

end CatCrypt.Crypto.PAKE.DH
