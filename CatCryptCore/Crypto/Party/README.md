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

## The classical lift

A classical program `p` lifts to the quantum system `ClassicalLiftSys.toQSys p`, the lift of
`toSys p`, and its quantum interpreter, the generic activation at the effect handler
`ClassicalLiftSys.liftHandler` (the quantum party handler precomposed with the diagonal
subinstrument of a sample), is that lift
([`ClassicalLiftSys.qAct_eq_toQSys_step`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftSys.lean)).
The lift of systems is a functor into the quantum system category preserving `⊕` and the trace
([`ClassicalLiftSys.liftFunctor_map_trace`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftSys.lean)).

## Time certificates

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
to the next: the activation semantics of `Party.Prog`.
