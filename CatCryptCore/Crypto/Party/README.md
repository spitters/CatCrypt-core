# The party language

The modules of this directory were added on 2026-10-31 and are not yet pushed, so the links
below resolve only after the next push.

A party of a protocol is written as a program; its meaning is a reactive system, and a protocol
is the composite of the systems of its parties. Classical parties are
[`Party.Prog E O α`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Prog.lean),
parties that call subroutines are programs on a sum interface
([`Call`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Call.lean)),
and quantum parties are
[`Party.QProg R E O α`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/QProg.lean),
with qubit ports.

Both are instances of one generic program tree
[`Party.ProgE Op E O α`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/ProgE.lean)
over an effect signature `Op`, interpreted through an effect handler `Handler Op M`: the classical
party language is `ProgE (SPComp ℕ)` with the handler `Prog.handler` in `SPComp`, and the quantum
party language is `ProgE (SubInstrument R R ℕ)` with the handler `QProg.handler` in
`SubInstrument R R`. The two phases of an activation (`ProgE.emitK`, `ProgE.awaitK`), the monad
laws, the parallel composition `ProgE.par` and its activations are stated once for every lawful
handler, and a map of effect signatures (`ProgE.mapOp`) carries programs from one language to the
other.

## Programs and their denotation

A program on input events `E` and outputs `O` returns, waits for the next activation (`recv`),
emits the output of the current activation (`send`), samples (`sampleN`, a sub-distribution on
codes in `ℕ`; `Prog.sample` samples any countable type) or fails. Programs form a monad, so a
party is written in `do` notation with `Prog.recvE`, `Prog.sendE` and `Prog.sampleE`.

The denotation is a reactive system
[`UCTransparent.Sys`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCTransparent.lean)
whose state is the residual program. An activation on `e` performs the samples up to the next
`recv`, feeds it `e`, performs the samples up to the next `send o` and stops with output `o`. The
two phases are continuation-passing interpreters that respect `bind`
([`Prog.emitK_bind`, `Prog.awaitK_bind`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Prog.lean)),
and a receive followed by a send is one step
([`Prog.act_recv_send`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Prog.lean)).
A finite program denotes `Prog.toSys p`; an unbounded session is the loop `Prog.loopSys body s₀`,
which, when every iteration is one activation, is step-equivalent to the system with the iteration
as its step
([`Prog.loopSys_stepEq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Prog.lean)).
The forwarding party denotes `Sys.ofFun`
([`Prog.forward_stepEq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Prog.lean)).

## Composition and the Int construction

The parallel composition `Prog.par p q` on `E ⊕ E'` and `O ⊕ O'` runs one activation of the party
addressed by the event. Its denotation is step-equivalent to `Sys.par` of the denotations
([`Prog.toSys_par`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Compose.lean)).
In the Int construction on systems (`IntConstruction SysCat`,
[`UCLoopbackInt`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCLoopbackInt.lean)),
`sysHom` sends parallel composition to the tensor product
([`SysCat.sysHom_par`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Compose.lean)),
so the class of `par p q` is the tensor of the classes
([`Prog.sysHom_toSys_par`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Compose.lean)).
The class of a system depends only on its step-equivalence class
([`SysCat.sysHom_eq_of_stepEq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Compose.lean)),
so the class of a loop of one-activation iterations is the class of the system it re-expresses
([`Prog.sysHom_loopSys`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Compose.lean)),
and wiring of program parties is wiring in the Int construction and in the open theory
[`loopOpenTheory`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCLoopbackOpenTheory.lean).
A system that samples and then updates deterministically is the loop of a program
([`Prog.sampleBody_stepEq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Compose.lean)),
and the ideal channel `FChan` is the loop of `chanBody`
([`Prog.chanBody_stepEq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Compose.lean)).

## The category of wiring diagrams

A wiring diagram of party programs is a term `WTerm Gen X Y` built from generators by identities,
sequence, tensor, the structure maps of a symmetric monoidal category and the trace. For a traced
symmetric monoidal category `C` and a denotation `g` of the generators, the category `Diag g` of
terms modulo equality of their denotations is traced symmetric monoidal, and the denotation is a
faithful strict traced symmetric monoidal functor `Diag.functor g : Diag g ⥤ C`
([`Diag.map_trace`, `Diag.map_braiding_hom`, `Diag.hom_ext`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Category.lean)).
In the classical instance `PartyCat` the generators are party programs and their loops, denoted in
`SysCat`; in the quantum instance `QPartyCat R` they are quantum party programs and their loops,
denoted in `QSysCat R`. The parallel composition of programs is the tensor product
([`PartyCat.ofProg_par`, `QPartyCat.ofProg_par`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Category.lean)),
port functions are forwarding parties
([`PartyCat.toSys_map_ofLoop_forward`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Category.lean)),
and two programs are equal in the category exactly when their denotations are step-equivalent
([`PartyCat.ofProg_eq_iff`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Category.lean)).
The trace is the term constructor `WTerm.trace`, sent to the unbounded loopback of `SysCat` and
`QSysCat R`.

## Subroutine calls

A party with outer events `E`, outer outputs `O`, calls `Q` and answers `A` is a program on
`E ⊕ A` and `Q ⊕ O`; `Prog.call q k` emits the call and continues with the answer. Its denotation
is a multi-call hybrid
([`MultiHybrid`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCTransparentMulti.lean)),
[`MultiHybrid.ofSys`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Call.lean),
and the loop of a body is `Prog.loopMulti`. An embedding of states between two multi-call hybrids
makes them step-equivalent with every subroutine
([`MultiHybrid.Embeds.stepEq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Call.lean)),
and the loop theorem derives the embedding from per-step hypotheses on the body
([`Prog.loopMulti_stepEq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Call.lean)).
The X3DH simulator written as a program is step-equivalent to the hand-written simulator with
every subroutine
([`X3DHProg.simProt_stepEq_simLoop`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Call.lean)).

## Derived structure: port typing, opacity, unwinding

The structural facts of a party are theorems over the syntax of programs
([`Derived`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Derived.lean)).
The activation unfolds along each constructor and along `bind` (`Prog.act_bind`). Port typing
`ProgE.Ports Pe Po p` (outputs in `Po`; events outside `Pe` fail) is kept by the states of the
denotation, which emits only outputs of `Po` and has no outcome on other events
(`Prog.toSys_ports`, `Prog.loopSys_ports`). Information flow for a public view `V` is the
relation `ProgE.ViewRel V RA` on programs; a program related to itself has this relation as an
unwinding relation of its denotation (`Sys.Unwinding`), so the denotation is opaque for `V`
(`Prog.toSys_opaque`, `Prog.loopSys_opaque`). A program whose continuations read each event only
through a projection `f` has equal activations on events with equal images and is
step-equivalent to a program on the projected events (`Prog.toSys_stepEq_of_readsVia`). The loop
of the X3DH simulator program is opaque from the view of `F_AKE` to the view of the real
interface (`X3DHProg.simLoopSys_opaque`).

An unwinding relation of a system on the sum interface of a multi-call simulator is an unwinding
relation of its multi-hybrid, and opacity transfers with it
([`MultiHybrid.unwinding_ofSys`, `MultiHybrid.opaque_ofSys`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/UnwindingTransfer.lean));
an embedding of multi-hybrids pulls unwinding back
([`MultiHybrid.Embeds.unwinding`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/UnwindingTransfer.lean)).
The transfer uses that a coupling preserves total mass, so two computations related by a
relational Hoare triple at equal heaps fail together
([`rHoare_noFail_iff`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Relational/CouplingMass.lean))
and their guarded forms take the same branch
([`rHoare_guardNF`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/GuardCoupling.lean)).
The unwinding condition and the opacity of the hand-written X3DH simulator follow from its program
form
([`X3DHProg.simProt_unwinding_of_prog`, `X3DHProg.simProt_opaque_of_prog`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/UnwindingTransfer.lean)).

## Relational program logic and refinement

The relational triple `Prog.RelTriple V RA p p'` relates two programs under a public view `V`:
equal shapes of receives and sends, outputs related by `V.out`, continuations at events related by
`V.ev`, samples coupled exactly, and returns related by `RA`. Its rules are the constructors, the
bind rule, the sampling rule on countable types and the loop rule from an invariant
([`RelTriple.bind`, `RelTriple.sampleC`, `Prog.loopSys_couplingBisim`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Relational.lean)).
The activations of related programs are coupled
([`RelTriple.stepWith_rHoare`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Relational.lean)),
and for the equality view the triple is a coupling bisimulation of the denotations, which gives
step equivalence through the Larsen–Skou quotient
([`UCCoupling.CouplingBisim.stepEq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Relational.lean)).
Related programs therefore emulate one another in every context of `loopOpenTheory`, and
emulation of related programs is closed under parallel composition and wiring
([`RelTriple.emulatesΩ`, `RelTriple.emulatesΩ_par`, `RelTriple.emulatesΩ_wire`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Relational.lean)).
The party that sends `m + k` for a fresh uniform key `k` emulates the ideal channel that sends a
fresh uniform ciphertext
([`OTPProg.otp_emulatesΩ`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Relational.lean)).

A map of return values gives a step map between the denotations, and a loop whose iterations read
their state only through an abstraction `g` refines the loop of the abstract body on the
`g`-images: step equivalence, equal views and realization at distance `0`
([`Prog.loopSys_stepMapOn_absBody`, `Prog.loopSys_stepEq_absBody`, `Prog.loopSys_view_eq_absBody`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Refinement.lean)).
Two loops that receive one event and dispatch on it are coupled when their branches at each event
are related
([`Prog.loopSys_couplingBisim_perEvent`, `Prog.loopSys_emulatesΩ_perEvent`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Refinement.lean)),
with per-branch rules for a receive, a send followed by a return, and a uniform sample along a
bijection
([`RelTriple.act_recv_rHoare`, `RelTriple.sendRet`, `RelTriple.sample_bij`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Refinement.lean)).

## Side conditions by `party_derive`

The tactic `party_derive` proves the side conditions of a concrete program by descent over its
term: the sampling structure `Prog.Samples p c` used by `Prog.loopMulti_stepEq`, the port typing
`ProgE.Ports Pe Po p`, the information-flow relation `ProgE.ViewRel V Eq p p` of a program without
receives and sends, and a time bound `ProgE.Bound w p t P`, at a given `t` or at a bound it reads
off the program
([`PartyDerive`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/PartyDerive.lean),
tests in [`PartyDeriveTest`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/PartyDeriveTest.lean)).
A subprogram with a lemma `c_bound` is bounded by that lemma; `party_derive!` unfolds instead.

## Protocols in the party language

| Protocol | What is proved |
|---|---|
| The authenticated key-exchange functionality | `F_AKE` (multi-session key exchange after Canetti and Krawczyk, with adversarial key delivery, corruption and an unlinked delivery) written as a loop of one activation per event is step-equivalent to the hand-written functionality ([`FAKEProg.sys_stepEq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Protocols/FAKE.lean)), and a realization behind a multi-call simulator against `F_AKE` holds against the program ([`FAKEProg.realizesSim_sys`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Protocols/FAKE.lean)). |
| X3DH | Ideal functionality: `F_AKE` with uniform keys. Real world: X3DH over a Diffie–Hellman group for every session, with static corruption and the key derivation a lazily sampled random function. Simulator: the program `X3DHProg.simBody`, which keeps a copy of the real state, draws the secrets itself and delivers keys through `F_AKE`; its opacity and its graded time bound are derived from the program ([`X3DH.simLoop_opaque`, `X3DH.simLoop_time`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Protocols/X3DH.lean)). X3DH realizes `F_AKE` behind this simulator with the advantage of the oracle-game reduction as bound, also against the program form of `F_AKE` ([`X3DH.x3dh_realizesSim_prog`, `X3DH.x3dh_realizesSim_progFAKE`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Protocols/X3DH.lean)). |
| PQXDH | Ideal functionality: `F_AKE` with uniform keys. Real world: PQXDH (X3DH with a post-quantum KEM prekey whose shared secret enters the key derivation) for every session. Simulator: the program `PQXDH.simBody`, which also draws every KEM key pair and encapsulates on `complete`; it is step-equivalent to the hand-written simulator with every subroutine ([`PQXDH.simProtK_stepEq_simLoop`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Protocols/PQXDH.lean)), opaque, and has a graded time bound ([`PQXDH.simLoop_opaque`, `PQXDH.simLoop_time`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Protocols/PQXDH.lean)). PQXDH realizes `F_AKE` behind this simulator with the advantage of the oracle-game reduction as bound ([`PQXDH.pqxdh_realizesSim_prog`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Protocols/PQXDH.lean)). |

## Quantum programs and qubit ports

A quantum party on the register `R` has the classical ports of `Party.Prog`, and its operation
`opN q k` applies a subinstrument on `R` and continues with the classical outcome; gates,
measurements, preparations and sampling (the diagonal subinstrument
`SubInstrument.ofSDistr` of the classical lift) are such operations, run by the quantum party
handler `QProg.handler`. Its denotation is a quantum reactive system of the quantum system category
([`QProg.toQRSys`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/QProg.lean);
[core quantum README](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/README.md)),
and the loop `QProg.loopQSys` of one-activation iterations is step-equivalent to the system with
the iteration as its step
([`QProg.loopQSys_stepEq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/QProg.lean)).
The parallel composition denotes the monoidal product `QRSys.par` of `QSysCat`
([`QProg.toQRSys_par`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/QProg.lean)).

A program on `M` framed to `M × N` acts by the identity on `N`, and framing commutes with the
denotation
([`QProg.toQRSys_frameR`, `QProg.toQRSys_frameL`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/QProg.lean)).
The qubit ports move ownership of a factor: `QProg.sendQ o k` emits `o` with the factor `N` and
continues as a program on `M`, and `QProg.recvQ p k` runs `p` on `M` and then continues on
`M × N`. Linearity is enforced by the register type, and every operation is completely positive,
so no step copies the state of a factor. Framing and the embedding of classical programs are
maps of effect signatures, monad morphisms of the generic tree
([`ProgE.mapOp_bind`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/ProgE.lean)).
The real world of the reactive quantum one-time pad is the loop of a program
([`QProg.qotpRealBody_stepEq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/QProg.lean)).

The weakest precondition `QProg.wp p e V` of an activation maps a state to the expected value of
the postcondition effects `V` after the activation of `p` on `e`. It is the expectation after the
denotation of the activation
([`QProg.wp_eq_expect_act`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/QProgWP.lean)),
it satisfies the bind rule and the frame rule for programs framed on one factor of the register
([`QProg.wpEmit_bind`, `QProg.wp_frameR`, `QProg.wp_frameL`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/QProgWP.lean)),
and the loop rule of partial correctness from an invariant holds for the unbounded loop
activation, by Scott induction
([`QProg.loopActω_pcorrect`, `QProg.loopQSys_pcorrect`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/QProgWP.lean)).
In the real world of the reactive quantum one-time pad, an activation at the phase `done` outputs
`ignored` with certainty, up to failure
([`QProg.qotpReal_done_ignored`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/QProgWP.lean)).

## The classical lift

A classical program `p` lifts to the quantum system `ClassicalLiftSys.toQSys p`, the lift of
`toSys p`, and its quantum interpreter, the generic activation at the effect handler
`ClassicalLiftSys.liftHandler` (the quantum party handler precomposed with the diagonal
subinstrument of a sample), is that lift
([`ClassicalLiftSys.qAct_eq_toQSys_step`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftSys.lean)).
The lift of systems is a functor into the quantum system category preserving `⊕` and the trace
([`ClassicalLiftSys.liftFunctor_map_trace`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftSys.lean)).

## Time certificates

The costed form of a program carries ticks `tick c`; its erasure removes them, and the costed
handler on a costed program is the handler on the erased program
([`ProgE.act_erase`, `Prog.loopSys_step_erase`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Timed.lean)).
`ProgE.Bound w p t P` bounds the cost of every path of `p` by `t` under the weights `w` of the
effect operations, and composes along `bind`
([`ProgE.Bound.bind`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Timed.lean)).
A loop body that at a state of invariant `i` costs at most `a + b * i` has the graded bound
`ProgE.LoopBoundGraded`, and `q` iterations cost at most `q * a + b * (q * (q - 1) / 2)`
([`ProgE.LoopBoundGraded.iterate_time_le`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Timed.lean)).
The X3DH simulator program, priced by the length of its key-derivation table, has the graded
bound `7`, `1`
([`X3DHProg.simBodyT_loopBoundGraded`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Timed.lean)),
and the forwarding party the constant bound `2`
([`Prog.forward_loopBoundGraded`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/Timed.lean)).

A simulator whose state grows with the activations (a lazily sampled table) has the graded time
bound
[`MultiHybrid.Timed.TimeBoundGraded`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCSimulatorCostGraded.lean):
step `i` costs at most `a + b * i`, and `q` activations cost at most
`q * a + b * (q * (q - 1) / 2)`
([`TimeBoundGraded.actRun_time_le`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCSimulatorCostGraded.lean)).

## Relation to Viaduct's projected processes

The Viaduct experiment of the CatCrypt repository (`CatCrypt/Experimental/Viaduct/`, after Acay,
Gancher, Recto and Myers, CSF 2024) projects a choreography to one process per party
(`PProc`, compiled to first-order code `HCode`), whose code machine runs from one blocking node
to the next: the activation semantics of `Party.Prog`. The party program of a host machine, a
projected process or first-order host code is a loop step-equivalent to the machine's system
([`Mach.loopSys_body_stepEq`, `CStmt.project_loopSys_body_stepEq`](https://github.com/spitters/CatCrypt/blob/master/CatCrypt/Experimental/Viaduct/PartyProg.lean)),
and the choreography run is a party loop
([`Systems`](https://github.com/spitters/CatCrypt/blob/master/CatCrypt/Experimental/Viaduct/Systems.lean)).
