# Quantum systems, Selinger's order and quantum UC

The modules of this directory added on 2026-10-31 (Selinger's order, the quantum system category
and its tensor, private registers, the open theory, the classical lift and its functor, the
quantum one-time pad over an insecure channel) are
not yet pushed, so some links below resolve only after the next push.

The foundations (instruments, completely positive maps, trace and diamond norms, partial trace,
Stinespring dilation), the quantum distances and the QROM are listed in the
[top-level README](https://github.com/spitters/CatCrypt-core/blob/main/README.md). This page
describes the order-theoretic and categorical structure of quantum programs and reactive quantum
systems, and the quantum UC layer built on it. The circuit compiler, dynamic circuits and the ZX
category that use this structure are in the CatCrypt development repository, which is not public.

## Selinger's order on subinstruments

Subinstruments are ordered branchwise by complete positivity of the difference, after Selinger
(*Towards a quantum programming language*, MSCS 2004, §3.3). The order is a partial order
([`instPartialOrder`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/SubInstrumentOrder.lean))
in which every increasing sequence has a least upper bound, the pointwise limit of its branches
([`instOmegaCompletePartialOrder`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/SubInstrumentOrder.lean),
[`tendsto_branch_ωSup`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/SubInstrumentOrder.lean));
complete positivity is closed under pointwise limits
([`MatrixMap.isCP_of_tendsto`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/SubInstrumentOrder.lean)).
Sequencing is monotone
([`bind_mono_left`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/SubInstrumentOrder.lean),
[`bind_mono_right`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/SubInstrumentOrder.lean))
and commutes with suprema of chains in each argument
([`ωSup_bind`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/SubInstrumentOrder.lean),
[`bind_ωSup`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/SubInstrumentOrder.lean)),
and the same holds for `CPComp.qbind`
([`CPComp.qbind_mono_left`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/SubInstrumentOrder.lean),
[`CPComp.ωSup_qbind`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/SubInstrumentOrder.lean)).
On `Unit`-valued instruments the order implies the Löwner order of the programs
([`CPComp.posSemidef_sub_toQComp_branch_of_le`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/SubInstrumentOrder.lean)).

The quantum while loop is the supremum of its bounded unfoldings in this order, and a dynamic
circuit's loop is the least fixed point of its unfolding
(`CPComp.qwhile_eq_ωSup` and `DCircuit.denoteCP_whileBit_le_of_prefixed`, in the development
repository).
Properties of such suprema are proved by Scott induction for predicates closed under suprema of
chains
([`ωSup_iterateChain_induction`, `OrderHom.lfp_scott_induction`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/ForMathlib/Order/ScottInduction.lean)),
also for the unbounded activation of a loopback
([`QRSys.fbRunω_scott_induction`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/ScottInduction.lean)),
driven by the tactic `scott_induction`.

## The quantum system category: `⊕` traced by the ω-supremum

A quantum reactive system `QRSys R τ E O` has a classical state `τ` and acts on a register `R`
shared with the environment; an activation on an event is a subinstrument on `R` whose outcome
is the new state and the output. The development follows the classical traced category of
reactive systems (`UCLoopbackTrace`, `UCLoopbackTraced`) with sub-distributions replaced by
subinstruments and the order of `SDistr` by Selinger's order.

`QSysCat R` has port types as objects and systems modulo step equivalence as morphisms;
composition is the cascade `QRSys.seq`, the monoidal product `⊕` on ports is the parallel
composition `QRSys.par`, and the trace is the unbounded loopback `QRSys.loopbackω`, the supremum
of the fuel-bounded feedback runs (`QRSys.fbRunω`, with its unfolding equation
[`QRSys.fbRunω_eq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCat.lean)).
The trace axioms are proved for the loopback: naturality
([`loopbackω_seq_left`, `loopbackω_seq_right`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCat.lean)),
dinaturality ([`loopbackω_slide`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCat.lean)),
vanishing ([`loopbackω_empty`, `loopbackω_loopbackω`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCat.lean)),
superposing ([`loopbackω_par_left`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCat.lean))
and yanking ([`loopbackω_swap`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCat.lean)),
and step equivalence is a congruence for it
([`QRSys.StepEq.loopbackω`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCat.lean)).
Together they give the traced symmetric monoidal category
([`QSysCat.tracedCategory`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCat.lean)).
The quantum while loop is this trace applied to the system of its guard and body
(`CPComp.loopbackω_whileSys_step`, in the development repository).

## The tensor `⊗` by framing

The product of systems on different registers places `S` on `M` and `T` on `N` side by side on
`M × N`, each step framed by the identity on the other register
([`QRSys.parFramed`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCat.lean)).
It is assembled from the framing functors `QSysCat.frameR` and `QSysCat.frameL`, which preserve
`⊕` ([`QRSys.frameR_par`, `QRSys.frameL_par`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatTensor.lean))
and the trace
([`QRSys.frameR_loopbackω`, `QRSys.frameL_loopbackω`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatTensor.lean),
[`QSysCat.frameR_map_trace`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatTensor.lean)),
which is Selinger's condition that `A ⊗ (−)` is traced (MSCS 2004, §6.6). The tensor of
morphisms [`QSysCat.tensor`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatTensor.lean)
satisfies the interchange laws with composition and with `⊕` and distributes over `⊕`
([`QSysCat.tensor_comp`, `QSysCat.tensor_id`, `QSysCat.tensor_tensorHom`, `QSysCat.tensor_distrib`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatTensor.lean)).
A register equivalence relabels systems functorially
([`QSysCat.relabel`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatTensor.lean)).

## Private registers

In `QSysPriv` every morphism carries a finite nonempty private register `K` of its own (`PObj`),
modulo placement in a register `K'` along an equivalence `K × N ≃ K'` followed by a step map;
this covers relabelling and extension by a nonempty register
([`PObj.privEq_extend`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatPrivate.lean)).
The cascade runs on the product of the two registers, each system framed by the identity on the
other. The parallel composition `⊕` and the paired activation `⊗` (the first system on the first
event, then the second on the second) are symmetric monoidal structures
([`QSysPriv.sumMonoidal`, `QSysPriv.sumSymmetric`, `QSysPrivMul.monoidalCategory`, `QSysPrivMul.symmetricCategory`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatPrivate.lean)),
with a distributor `QSysPriv.distrib` natural in the two summands and an annihilator
`QSysPriv.annihilator`. Two systems with no events are equivalent
([`PObj.privEq_of_isEmpty`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatPrivate.lean)),
so the annihilator is natural.

## The Int construction as an open theory

The Int construction `IntConstruction (QSysCat R)` carries a PolyFun open theory
`QOpenTheory.qOpenTheory R`, whose open systems on a port boundary `Δ` are quantum reactive systems
receiving the packets of `Δ.In` and emitting those of `Δ.Out`; it satisfies `HasPlugWireFactor`
([`QOpenTheory.qOpenTheory_hasPlugWireFactor`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatOpenTheory.lean)),
and equality of closed systems is step equivalence
([`QOpenTheory.closed_mk_eq_iff`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatOpenTheory.lean)).
Quantum UC emulation `EmulatesΩ` compares open systems through tests on the bit boundary,
observed by the subinstrument of the first activation; every test is composition with a morphism
of the Int construction
([`QOpenTheory.runTest_eq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatOpenTheory.lean)),
so emulation is preserved by composition, parallel composition and wiring
([`QOpenTheory.EmulatesΩ.comp`, `QOpenTheory.EmulatesΩ.par_compose`, `QOpenTheory.EmulatesΩ.wire_compose`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCatOpenTheory.lean)).
`EmulatesΩ` is the instance at distance `0` of the quantitative emulation `EmulatesObs` over any
open theory with test factorization, which is reflexive, symmetric, satisfies the triangle
inequality and is closed under composition with the bounds added
([`EmulatesObs.trans`, `EmulatesObs.par_compose`, `EmulatesObs.wire_compose`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/OpenTheoryObs.lean)).

## The classical lift

A sub-distribution is the diagonal subinstrument
([`SubInstrument.ofSDistr`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftSys.lean));
the lift preserves `pure`, `bind` and failure, is monotone and preserves suprema of chains
([`ofSDistr_bind`, `ofSDistr_mono`, `ofSDistr_ωSup`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftSys.lean)).
A classical reactive system lifts to a quantum one with the same classical state
([`ClassicalLiftSys.liftSys`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftSys.lean));
the lift preserves parallel composition and, for heap-independent systems, the cascade and the
unbounded loopback
([`liftSys_par`, `liftSys_seq`, `liftSys_loopbackω`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftSys.lean)),
and classical step equivalence gives quantum step equivalence
([`stepEq_liftObj`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftSys.lean)).
On the category `PSysCat` of heap-independent systems this is a functor
`liftFunctor : PSysCat ⥤ QSysCat R` preserving `⊕` and the trace
([`liftFunctor_map_tensor`, `liftFunctor_map_trace`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftSys.lean)).
A classical party program lifts by `toQSys p = liftSys (toSys p)`, and its quantum interpreter is
that lift ([`qAct_eq_toQSys_step`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftSys.lean)).
A classical realization at distance `0` gives equal quantum views against environments of the
classical-lift form
([`qview_liftQSys_eq_of_realizes`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftSys.lean)).

The traced symmetric monoidal structure of `PSysCat` is induced along its faithful inclusion into
`SysCat`, and the lift `liftFunctor R` is a strong monoidal functor with identity structure
isomorphisms, braided, and preserves the trace in the form `F (Tr_U f) = Tr_{F U} (μ ≫ F f ≫ δ)`
([`liftCoreMonoidal`, `liftFunctor_map_traceC`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftFunctor.lean)).
A classical realization of heap-independent systems at distance `ε` bounds the diamond distance of
the quantum views of their lifts by the same `ε` against every environment of the classical-lift
form
([`quc_liftQSys_of_realizes_le`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftFunctor.lean)),
since the diamond distance of two classical embeddings is at most their statistical distance.

## Transport along observation-preserving maps

A map of systems and of environment tests between two observation settings that preserves the
cascade with a test and the observation carries every statement about observations to the image
systems
([`ObsPreserving.transport`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCTransport.lean)),
after Broadbent and Karvonen: classical realization with a simulator, quantum realization and
testing equivalence through the bit boundary
([`RealizesSim.transport`, `QRealizes.transport`, `EmulatesΩ.transport`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCTransport.lean)).
The instances are the compiled-step map of classical systems, the classical lift into quantum
systems ([`liftObsPreserving`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/TransportAlong.lean))
and the quantum compiled step
(`qcompiledObsPreserving`, in the development repository).
The tactic `transport_along P` reduces a goal about the images to the goal about the sources.

## Quantum UC

| Result | What is proved |
|---|---|
| Realization of quantum reactive systems | A system `QSys H τ E O d` acts on the environment's register `Fin d` and a private register `H`. [`QRealizes R I ε`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QRealizes.lean) bounds the diamond distance between the views of `R` and `I` for every environment, and `QRealizesSim R I S ε` does so behind a simulator `S`; both are reflexive at `0` and transitive with added errors ([`QRealizes.trans`, `QRealizesSim.trans`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QRealizes.lean)). The run of an open process placed on a factor of a register is the placed run ([`closedRun_frame`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QRealizes.lean)). |
| Simulators and environments with a private quantum register | Environments and simulators hold registers that persist across activations; [`QRealizesSimQ`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QRealizesMem.lean) is reflexive and transitive ([`QRealizesSimQ.refl`, `QRealizesSimQ.trans`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QRealizesMem.lean)), the view is invariant under an equivalence of memory registers ([`qviewQ_iso`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QRealizesMem.lean)), and realization behind a memoryless simulator is the special case ([`QRealizesSimQ.toQSim`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QRealizesMem.lean)). |
| The reactive quantum one-time pad | Ideal functionality: the secure quantum channel, which on `send` buffers the message and leaks its length, on `deliver` hands the buffer to the receiver and on `drop` aborts. Real world: Alice applies the Pauli operator of a uniformly sampled key, Bob its inverse, and the adversary may take the ciphertext off the channel. Simulator: it translates a theft to `drop` and answers with a uniformly random Pauli operator applied to the interface register. The real world realizes the ideal one at distance `0` behind the simulator ([`QOTPReactive.qotp_realizesSim`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QOTPReactive.lean)). |
| The quantum one-time pad over an insecure channel | Ideal functionality: the confidential quantum channel with Pauli tampering, which leaks the length on `send` and on `deliver j` applies the Pauli operator `P_j` chosen by the adversary. Real world: the ciphertext stays with the adversary, who delivers a register to Bob. Simulator: it holds `n` halves of EPR pairs in its private register, hands the other halves to the adversary in place of the ciphertext, and on `deliver` measures in the Bell basis to obtain `j`. The real world realizes the ideal one at distance `0` behind this simulator ([`QOTPInsecure.qotpInsecure_realizesSimQ`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QOTPInsecure.lean)), through the four-point identity of the Pauli operators ([`pauliFin_four_point`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QOTPInsecure.lean)). |

A quantum system on `Fin d × H` is a system of the quantum system category
([`QSys.toQRSys`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QSysCat.lean)).
The real world of the reactive one-time pad is the loop of a quantum party program
([`Party.QProg.qotpRealBody_stepEq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/QProg.lean);
[party language](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/README.md)).
A quantum party whose steps are QPL programs is realized at distance `0` by the party running
the compiled circuits, with simulators and bounds transported
(`QRealizesSim.ofCompile`, in the development repository).

## Composition law for quantum realization

Realization is preserved along environment pullbacks: a map of quantum systems with a map of
quantum environments in the opposite direction, such that the view of an environment against
the image of a system is the view of its reduced environment against the system. Each
composition theorem below is the pullback law at a context; the bounds are functions of the
environment.

| Result | What is proved |
|---|---|
| Environment-dependent realization and pullbacks | [`QRealizesB R I b`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullback.lean) bounds, for every environment `Z`, the diamond distance of the views of `Z` against `R` and against `I` by `b ζ Z`; it is reflexive at the zero bound and transitive with the sum of the bounds, and at a constant bound it is `QRealizes` ([`QRealizesB.refl`, `QRealizesB.trans`, `QRealizes_iff_const`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullback.lean)). A quantum environment pullback `F` maps a realization with bound `b` to a realization of the images with bound `b ∘ F.pull`; pullbacks compose, and a context with two holes is two pullbacks and transitivity ([`QEnvPullback.realizes_map`, `QEnvPullback.realizes_map_comp`, `QEnvPullback.realizes_twoHole`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullback.lean)). The same laws hold against environments with a quantum memory register ([`QRealizesQB`, `QEnvPullbackQ.realizes_map`, `QEnvPullbackQ.realizes_twoHole`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackCascade.lean)). Simulator absorption is a context with one hole: the view of `Z` against `Y` behind `S` is the view of the absorbed environment `S.absorb Z` against `Y`, and realization behind `S` is realization of `S.attach I` ([`QSim.qview_attach`, `QRealizesSimB_iff_attach`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullback.lean)). |
| Cascade with private registers | The cascade `QSys.cascade X Y` keeps the private registers of `X` and `Y` apart, on `H × H'`. Register transfer moves the register of a simulator from the system to the environment memory, so the view of `Z` against an attached system is the view of the absorbed environment ([`QSimQ.qviewQ_attachQ`, `QSimQ.qviewQ_attachQL`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackCascade.lean)). As a quantum reactive system on the joint register the cascade is the composition `QRSys.seq` of `QSysCat` of `X` on the left factor and `Y` on the right factor ([`QSys.cascade_toQRSys`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackCascade.lean)). If `X` realizes `X'` with bound `bX` and `Y` realizes `Y'` with bound `bY`, then `X.cascade Y` realizes `X'.cascade Y'` with `bX` at the environment that absorbs `Y` plus `bY` at the environment that absorbs `X'` ([`QRealizesQB.cascade`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackCascade.lean)). |
| Parallel composition | `QSys.par X Y` runs on the sum interface, activating `X` on the left factor of the register `H × H'` and `Y` on the right factor. When the component in the hole is idle at a given event, each one-hole context `- ∥ Y` and `X ∥ -` is a pullback over environments with memory, the register of the other component moving to the environment memory ([`QSys.par_stepMap_attachQ`, `QSys.parLeft`, `QSys.parRight`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackPar.lean)). The composition theorem adds the bound of each factor at the environment that absorbs the other ([`QRealizesQB.par`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackPar.lean)). |
| Feedback | The bounded loopback `QSys.loopback S n cut` feeds wire outputs of `S` back at most `n` times and ends an exhausted call with the cut-off output. For a system idle at a given event, the feedback context is a pullback whose reduced environment runs `Z.rounds * (n + 1)` rounds against `S` ([`QSys.qviewQ_loopback`, `QSys.loopbackCtx`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackFeedback.lean)), and the loopback of `R` realizes the loopback of `I` with the bound of `R` and `I` at the reduced environment ([`QRealizesQB.loopback`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackFeedback.lean)). |
| Adversary systems and the dummy adversary | A quantum adversary system `QAdvSys` sits between the environment and the adversary ports of a system, with classical state and a private register; attaching it is a pullback, and realization with an environment-dependent bound is preserved by attaching an adversary ([`QSys.qviewQ_attachAdv`, `QRealizesQB.attachAdv`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackAdversary.lean)). `QUCEmulatesSysB R F b` asks, for every adversary system `A`, for a simulator `S` with `R.attachAdv A` realizing `F.attachAdv S` with `b` at the environment that absorbs `A`. Dummy-adversary theorem: a realization of `F.attachAdv S` by `R` gives emulation against every adversary with simulator `S.comp A`; emulation gives a realization at the environment that absorbs the forwarding adversary; and when absorbing that adversary does not increase the bound the two are equivalent ([`qucEmulatesSysB_of_realizes`, `QUCEmulatesSysB.realizes_dummy`, `qucEmulatesSysB_iff_realizes_of_le`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackAdversary.lean)). |
| Classical lift as a pullback | The classical lift is a pullback of advantage theories from classical heap-independent systems tested by classical strategies, at the statistical distance of the views, to their quantum lifts tested by the lifted strategies, at the diamond distance ([`ClassicalLiftSys.liftPullback`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftPullback.lean)). Its advantage equation is the equality of the diamond distance of diagonal embeddings with their statistical distance ([`ClassicalLiftSys.cpDist_qview_liftQSys`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftPullback.lean)). Since the pull of tests has a section, the pullback reflects realizations ([`AdvPullback.realizes_of_rel`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftPullback.lean)), and classical realization is equivalent to quantum realization of the lifts ([`quc_liftQSys_iff_realizes`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftReflect.lean)). |

The classical composition law, of which these are the quantum analogues, is in
[`UCPullback`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCPullback.lean)
and [`UCPullbackSemantics`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCPullbackSemantics.lean).

## References

* P. Selinger. Towards a quantum programming language. *Mathematical Structures in Computer
  Science* 14(4), 2004.
