# The C compiler

`ccomp`, Silmaril's C compiler, and the machinery its correctness is stated in: a C frontend
over the [Cerberus port](cerberus.md) (Cabs, typed Ail, Core), intermediate languages (Mir,
RTL, the target-independent Lir, the C-backend's behaviours and refinement), passes with their
validators, back ends for x86-64 and RV64, the stage registry with each stage's correctness
contract, verified Core fragments, a ladder of C semantics, and the native x86-64 compiler with
its correctness theorems for its supported fragments.

Most of it is `Raw`: valid but unrefined proofs behind thin `Defs`/`Thms` headers, as the
earlier promotions of the Cerberus port and the SSA calculi. It arrives in dependency-ordered
waves; each section below says which.

## Infrastructure: IRs, back ends, behaviours (first wave)

| Area | Modules | What |
| --- | --- | --- |
| Behaviours and refinement | `Silmaril.Machine.CBackend.{Behaviour,…}` | the target-independent vocabulary of compiler correctness: outcomes, small-step semantics, refinement, the compilation relation, simulation conventions |
| C-backend IRs | `Silmaril.Machine.CBackend.{RTL,Lir,Lift,…}`, `Silmaril.Machine.CompilerSemantics` | RTL and its SSA form, Lir, lifting Lir to RTL, RTL to Lir with its VC |
| Mir | `Silmaril.Compiler.Mir` | the mid-level IR of `ccomp`: syntax, semantics, CSE, copy propagation, liveness, linking with its correctness, memory agreement |
| Targets | `Silmaril.Compiler.Target` | register allocation, back ends from linked Lir to relocatable objects, object contracts |
| RV64 | `Silmaril.Machine.RiscV` | an RV64 integer fragment (from the Sail model, see Provenance), its encoding, an extended machine, the RV64 Lir back end |
| Stage contracts and driver | `Silmaril.Compiler.{Contract,Registry,Driver,Category,Semantics,Passes,Clang}` | the correctness contract a stage must prove to count as validated, the stage registry, the pure core of the driver, compiler categories, the Clang JSON frontend |
| x86 checks | `Silmaril.X86.{Verify,FetchTrace,Decompile.VC}` | assembly text against programs, fetched-trace decoding, decompilation VCs |
| Ports of older Silmaril code | `Silmaril.Semantics.CPort.*` | the definitions the above import from the earlier Silmaril tree |

## Verified Core fragments (second wave)

| Area | Modules | What |
| --- | --- | --- |
| The specification | `Silmaril.Raw.Compiler.Core.Spec` (in #69) | what a compiled program may do: for every machine on which the trusted loader placed the artifact, every behaviour of the x86-64 fetch/decode/execute model is a behaviour Cerberus Core allows (`SoundSpec`) |
| Verified fragments | `Silmaril.Compiler.Core.Verified.*` | compilers of Core fragments to x86-64 with their soundness proofs, fragment by fragment: integer state and arithmetic, control flow, calls and returns, `printf` of integers and strings, loops, argument vectors, exits; their typing, run and state lemmas |
| Around them | `Silmaril.Compiler.Core.{Source,ReturnControl,Semantics,Main,ExactRun,Checks,BehaviourAdapter,Arguments}`, `Silmaril.Compiler.Decompile.WordC` | the Core source reader, return control, the behaviour adapter to the C-backend vocabulary, the verified driver, decompiled word-level C |

Each fragment proves `SoundSpec` for the programs it accepts and rejects the rest; which C
programs that covers is stated in each module.

## The C semantics ladder (third wave)

`csem`: semantics of typed-Ail programs (one translation unit with `main`), observed as a
process is (its standard output and how it ended), in rungs ordered by refinement on fragments:
C0 integers, C1 flat memory, …, C7 the full Cerberus semantics.

| Area | Modules | What |
| --- | --- | --- |
| The rungs | `Silmaril.Compiler.C.Sem.{C0,…,C7}`, `…Mono`, `…CoreProofs` | each rung's semantics, its monotonicity in fuel, and the proofs relating it to Cerberus Core |
| Elaboration | `Silmaril.Compiler.C.Sem.ElabC0` … `ElabC5` | each rung's elaboration to Core, with its witnesses |
| Ladder checks | `LadderCheck*`, `LadderGap`, `Targets` | the refinement checks between rungs, the known gaps, and the statement registry of the semantics (`Targets`, frozen) |
| Back to the compiler | `Mir*`, `C1Lir*`, `LirFast`, `CoreComp*`, `CoreX86`, `RefinedC*` | adequacy of `ccomp`'s Mir and Lir against the rungs, owned-resource (RefinedC-style) specifications checked on Lir |
| Runtime | `Runtime` (`runtime/libc.ail`, from `tools/ccomp/runtime/libc.c`) | `ccomp`'s C library as embedded typed Ail, so the semantics link a program with it |

`Targets` states each claim of the semantics as a `Prop`; a claim is proved when a theorem of
exactly that type exists. Which are proved, and which stay open, is listed in `Targets`.

## Status

Proved where a theorem is stated (no `sorry`, no new `axiom`, no `native_decide`); open goals are
`def Task.… : Prop` with conditional theorems. The x86-64 and RV64 machine models are trusted
definitions.

Left out, and why:

* The correspondence of the RV64 semantics with the generated Sail model
  (`RiscV.Ext.Sail`, `RiscV.Sail.Arithmetic`): it needs the third-party `riscv-zkvm` package.
* **CompCert-derived code is not in this repository, by decision.** The source development
  adapts parts of CompCert v3.17 (`Machine.CSupport.CompCert`: Clight, Cminor, machine integers,
  the Clight-to-Cminor translation, a register IR, assertion lowering, validation, 12 modules
  with their headers) and builds 30 modules of the C semantics ladder on them (with their
  headers); all of these stay out. So the following are **absent**, and nothing here states or
  proves them:
  * the signed C0 results through Cminor and x86: `C0SignedCondition`, `C0SignedSafety`,
    `C0SignedToCminor`, `C0SignedX86Add` (and their `…Checks`);
  * the owned-resource (RefinedC-style) results that go through the CompCert register IR to
    Lir or RV64: `RefinedCMaxLir`, `RefinedCOwnedLir`, `RefinedCOwnedRV64`,
    `RefinedCOwnedScalar*` (scalar reads, writes, read-back, RV64), `RefinedCOwnedSwapLir*`,
    `RefinedCOwnedUint64Frontend*`, `RefinedCOwnedUint64WriterFrontend`,
    `RefinedCProgramsLir`, `RefinedCProgramsSignedLir*`.

  The rungs C0 to C7 themselves, their elaborations and ladder checks, and the owned-resource
  specifications on C1 memory and on Lir that do not use CompCert code (`RefinedCPrograms`,
  `RefinedCMax`, `RefinedCOwnedSwap`, `RefinedCOwnedLirFrontend`, `RefinedCOwnedByte`, …)
  are here. No module in this repository carries CompCert's licence marker.

## Build

```sh
lake build --wfail Silmaril.Compiler.Target.Backends.Defs Silmaril.Compiler.Mir.Interp.Defs \
  Silmaril.Machine.RiscV.Lir.Defs Silmaril.Compiler.Registry.Defs Silmaril.Compiler.Core.Main.Defs \
  Silmaril.Compiler.C.Sem.Main.Defs
```

## Provenance and licence

Silmaril's own development, under this repository's MIT licence, except: the RV64 fragment
adapts clauses of the Sail RISC-V model at `27224ccb` (BSD-2-Clause, `NOTICES/sail-riscv`); the
frontend uses the Cerberus port (`NOTICES/Cerberus`); `runtime/libc.ail` is the Cerberus
elaboration of `tools/ccomp/runtime/libc.c` (in-house) against the Cerberus runtime headers
(BSD-2-Clause, `NOTICES/Cerberus`).
