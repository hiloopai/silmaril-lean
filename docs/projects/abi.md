# Calling conventions and ABI-level function contracts

Calling conventions as **institution comorphisms** from a C-level interface institution to a
machine-level one, the System V AMD64 and Microsoft x64 (`ms_abi`) conventions as instances,
cross-ABI thunks and their link-time checks, and the x86 function-level pieces that connect them
to `Silmaril.X86`: function contracts proved on the open machine become System V and
FFI certificates (`Realizes`), assembler-level functions are tied to the bytes of a pinned
executable, and demonic (relational) contracts transfer along machine refinement.

It builds on [the System V model](systemv-abi.md) of `Silmaril.Machine.SystemV` (the ABI, C type
classification and native contracts) and on `Silmaril.X86` (the open machines `Open`/`Open9`,
`FnContract`, `RelIsa`, the separation logic, block certificates, the ELF ladder).

## Module map

| Module | What |
| --- | --- |
| `Silmaril.Machine.Abi.{Defs,Thms}` | the interface-contract institution; a convention as a comorphism (`coHom_sat`); thunks (`Thunk.sound`); agreement of conventions |
| `Silmaril.Machine.Abi.SystemV` | System V AMD64 for the INTEGER/pointer fragment of `Silmaril.C.Api` prototypes: `sysv`, `sysv_sat`, cross-profile agreement |
| `Silmaril.Machine.Abi.Win64` | Microsoft x64 (`ms_abi`) as a second comorphism: `win64`, `win64_sat`, the result conventions |
| `Silmaril.Machine.Abi.CrossAbi`, `CrossAbi.Gcc` | thunks between the two conventions (`sysv_of_ms`, `ms_of_sysv`); GCC's `call_ms` transition code decoded and proved a System V → `ms_abi` thunk (`callMs_sound`) |
| `Silmaril.Machine.Abi.{Link,LinkTags,LinkSim}` | link compatibility: ABI tags on imports and exports, the linker's `checkAbi` guard, link soundness through simulations (`checkAbi_link_sound`, `callMs_link_sound`) |
| `Silmaril.Machine.Abi.Thunk` | `Thunk.Correct` versus forward simulation (`Thunk.Simulates.sound`) |
| `Silmaril.Machine.Abi.OpenMachine`, `OpenMachine.Rel` | the conventions' call model on the open machine (`callModel`): first returns, `FnContract Open.isa` and block certificates as convention-level contracts; the relational (`RelIsa`) version |
| `Silmaril.Machine.Abi.{CallFootprint,CtypeBridge,FsBase,Infer,LibMini,SpecNotions}` | argument-dependent footprints for `Realizes`; the bridge to the native compiler's C types; the thread pointer; ABI inference from register usage; libmini's C header; the three notions of a spec (author, compiled, export) and how they relate |
| `Silmaril.X86.FnContract.SystemV` | function contracts as integer `Realizes` and FFI `Ffi.Realizes` certificates (`toRealizes`, `toFfiRealizes`); decompilation certificates as contracts (`ofDecompiled`) |
| `Silmaril.X86.FnContract.Must` | demonic first-return contracts on relational machines (`Spec.MustIn`, `Spec.Must`), their bridges to strict contracts (`Strict.toMust`, `Must.toStrict`) and the loosened machine |
| `Silmaril.X86.FnContract.RightRot` | a worked contract: the decompiled `right_rot` |
| `Silmaril.X86.AbiFunction`, `AbiFunction.LeafArith` | assembler-level functions (an AT&T reader, placement, relocation of `rip`-relative operands) as `FnContract`s and `Realizes` certificates; rung 01's leaves checked against the pinned executable |
| `Silmaril.X86.Ladder.LeafArith` | rung 01 of the ELF ladder (`examples/elf-ladder/01-leaf-arith`): `sat_add_u32`, `bswap32_manual`, `clamp_i32`, `gcd_u32` as total System V contracts on the open machine, for every load address |
| `Silmaril.X86.Ladder.LibMini.SystemV` | the C signatures of libmini's `memcpy`, `memset`, `strlen` and their integer `Realizes` certificates |
| `Silmaril.X86.Ladder.Pinned.LeafArith{,.Thms}` | the embedded rung-01 executable and its binary tie |
| `Silmaril.Semantics.CPort.Formats.ELF.Extract` | extraction of a named function, its constants and relocations from a relocatable ELF file (the `right_rot` object bytes) |

The `Raw` modules `Silmaril.Raw.X86.{Assembly,Decompile.RightRot,Bench.Objects.RightRotClangO0}`
are an earlier import of the x86 development, kept as they are behind thin headers
(`Silmaril.X86.{Assembly,Decompile.RightRot,Bench.Objects.RightRotClangO0}.Defs`); they declare
in `Silmaril.X86.*` namespaces the public tree does not otherwise use. They are not an API.

## Status

| Claim | Status |
| --- | --- |
| Conventions as comorphisms, satisfaction transfer, thunk soundness, cross-ABI thunks, link soundness | proved |
| GCC's `call_ms` thunk (`callMs_sound`, decode and fetch) | proved, for the decoded code and an abstract callee relation |
| GCC's reverse transition `ms_calls_sysv` (`Task.msCallsSysvBridge`) | open: a `def Task.… : Prop`; the results that need it take it as a hypothesis |
| The open machine keeps the thread pointer (`Task.openStepKeepsFs`) | open: `def Task.… : Prop`, used as a hypothesis |
| Rung 01 leaves (`sat_add_u32`, `bswap32_manual`, `clamp_i32`, `gcd_u32`) | proved on the open machine, tied to the pinned executable |
| libmini `Realizes` certificates | proved |
| The x86 models themselves | trusted definitions (see [the x86 guide](../x86.md)) |

No `sorry`, no `axiom` beyond the standard three, no `native_decide`.

Not in this wave: the C-level separation-logic specs (`Silmaril.Machine.Abi.CSpecFfi`) and the
XMM, C-spec, plan and demo layers of the separation logic (`Sep.{Xmm,CSpec,Plan,Demo,BI}`) they
rest on. They are written against an earlier, step-function form of `Safe`/`Sep` and need
porting to the ISA-generic `Sep`/`Safe` of `Silmaril.X86`.

## Build

```sh
lake build --wfail Silmaril.Machine.Abi.Thms Silmaril.Machine.Abi.SpecNotions.Thms \
  Silmaril.X86.AbiFunction.LeafArith.Thms Silmaril.X86.FnContract.Must.Thms
bash examples/elf-ladder/pin.sh --check
```

## Provenance and licence

All of it is Silmaril's own development, under this repository's MIT licence. The rung-01
executable is built from `examples/elf-ladder/01-leaf-arith` and `common/` (MIT) by GCC
13.3.0 and GNU ld 2.42, freestanding and statically linked, with no third-party code; the
GCC `call_ms`/`ms_calls_sysv` byte sequences are short instruction sequences GCC emits, given as
byte lists. The `right_rot` object bytes (`Bench.Objects.RightRotClangO0`) come from clang `-O0`
builds of the same in-house SHA-256 cross-compilation corpus as `Silmaril.Crypto.X86.Sha256O2`. The calling conventions follow the System V AMD64 psABI (H. J. Lu et al., *System V
Application Binary Interface, AMD64 Architecture Processor Supplement*) and Microsoft's x64
calling convention documentation.
