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

## Status

Proved where a theorem is stated (no `sorry`, no new `axiom`, no `native_decide`); open goals are
`def Task.… : Prop` with conditional theorems. The x86-64 and RV64 machine models are trusted
definitions.

Left out, and why:

* The correspondence of the RV64 semantics with the generated Sail model
  (`RiscV.Ext.Sail`, `RiscV.Sail.Arithmetic`): it needs the third-party `riscv-zkvm` package.
* The modules adapted from CompCert (`Machine.CSupport.CompCert`: Clight, Cminor, integers, the
  Clight-to-Cminor translation) and the C-semantics modules that use them: they are marked
  LGPL-2.1-or-later, and CompCert distributes only part of its sources under free licences;
  which parts these adapt is not checked yet.

## Build

```sh
lake build --wfail Silmaril.Compiler.Target.Backends.Defs Silmaril.Compiler.Mir.Interp.Defs \
  Silmaril.Machine.RiscV.Lir.Defs Silmaril.Compiler.Registry.Defs
```

## Provenance and licence

Silmaril's own development, under this repository's MIT licence, except: the RV64 fragment
adapts clauses of the Sail RISC-V model at `27224ccb` (BSD-2-Clause, `NOTICES/sail-riscv`); the
frontend uses the Cerberus port (`NOTICES/Cerberus`).
