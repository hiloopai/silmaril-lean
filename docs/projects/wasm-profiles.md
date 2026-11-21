# Wasm profile-indexed syntax

`Silmaril.Wasm.Profiles.Tags` provides the tags used by the syntax and typing
interfaces. Tags do not select an executor, UB policy, or host. The operational
semantics layer can take the same tag and separately choose its execution model.
For conversions between these native dialects, see the [version injection API](wasm-version-injections.md).
For exact Core syntax images and a checked way to lift the Core linker, see
[Wasm sublanguages](wasm-sublanguages.md).
For raw, checked, and intrinsic views with a common API, see
[indexed Wasm syntax](wasm-indexed-syntax.md).

| Tag | `Module W` and `Instruction W` | Judgment |
| --- | --- | --- |
| `Wasm1` | `V1.Module`, `V1.Instr` | `V1.Validation.ModuleValid` (no interface index); the function relation exposes the resolved signature already used by `FuncValid`. |
| `Wasm2` | `V2.Module`, `V2.Instr` | `V2.Validation.ModuleOk` at its import/export pair, and `V2.Validation.FuncOk`. |
| `Wasm3` | `Wasm.Module`, `Wasm.Instr` | Core `ModuleOk` and `FuncOk`; also the Core intrinsic witness families. |
| `Lime` | `Lime1.Module`, `Lime1.Instr` | The repository's Lime1 module and function validation, not an alias for a feature-filtered Core AST. |
| `FX` | The Core loadable module and the extended `InstrFX` code family | The current FX model loads Core modules and uses an external host-code-to-`FuncFX` table. `FX.WithBindings` keeps that table without interpreting it. No whole-FX typing or binary instance is supplied. |
| `FunctionalCore gc exceptions` | Exact restrictions of the Core AST in four modes | Each mode uses the same Core module/function judgments after erasure; the guard is not itself typing. |

The 1.0, 2.0 and 3.0 references are the [pinned SpecTec snapshots](../../specs/spectec/manifest.json).
`HasFeatures` reuses `Models.Features`' manifests. Capabilities are monotone in
the `v10 ≤ v20 ≤ v30 ≤ wasmFX` chain, but `CoreImage v10` and `CoreImage v20`
are not the native V1 and V2 structures or all their valid encodings. For
example, the checked Lime1 translation to Core differs from the raw Core
feature guard for legacy tables and elements (`Models.Lime1Core.Thms`); the
Lime1 binary agreement uses `toCoreBinary`, not generally `toCore`.
Lime1 here follows the [pinned Lime1 profile](https://github.com/WebAssembly/tool-conventions/blob/83e5d715d0c18aee51e2d5ae9434f22d67b6e905/Lime.md),
not a fourth edition of the Core standard.
For FX the existing `Models.FXVModel.fxEmb'` is the conservative Core-to-FX
result with identity on modules and no FX function bindings at the program point.
The `dir = .eq` result concerns behavior under those bindings, not an erasure of
arbitrary FX code. `InstrFX` adds continuation operations and nesting; `FuncFX`
has a module instance, arities, locals and code and is stored in an external
host-code table. That is the modeled interface, not a native validated FX
module format or a complete stack-switching validation judgment.

The native value and instruction bindings differ even when scalar operators
share Lean types:

| Profile | Value type and representative instruction differences |
| --- | --- |
| `Wasm1` | `NumType` (four scalar types). `V1.Instr` excludes sign extension and saturating truncation; block result is an optional scalar. |
| `Wasm2` | `V2.ValType` adds `v128` and the two enumerated reference types. `V2.Instr` includes indexed block signatures, SIMD and saturating truncation, but no GC `struct.set` or typed `call_ref`. |
| `Wasm3` | Core `ValType` has nullability and abstract or indexed heap types. Core `Instr` includes the GC, tail-call and exception families. |
| `Lime` | Scalar `V1.ValType`, but native `Lime1.Instr` supports sign extension, saturating conversion and indexed block types; no reference or vector value types. |

Only `Wasm3` has a full `HasIntrinsic` instance. The native Wasm1 and Lime
scalar slices have explicit sound intrinsic witnesses, but do not cover the
whole native judgment. To get a Core witness, transport validation via the existing
`V1.Validation.ModuleValid.toCore`, `V2.Validation.ModuleValid.toCore_ok`
(given a `toCore` image), or `Lime1.Validation.ModuleValid.toCore`, then use
Core `Intrinsic.Module.lift_erase` at the resulting Core interface. Such a witness
erases to the **translated Core module**. It is not a native intrinsic witness
or a proof that typing reflects back for every Core feature-filtered module.

The optional `HasEncoding` relation selects the existing binary grammars for
V1, Lime1 and Core 3.0, not an executable encoder contract. There is no new
native V2 or FX codec. `Strict.decode?_iff` restricts the exact result of
`Core.decode?` without a second parser, and `decode?_sound` links that result to
the Core binary relation. It does not establish decoder completeness or validate
the resulting term.

## Known type, retained type, and forgotten type

`TypedModule Wasm3 iface` and `TypedFunction Wasm3 ctx sig` are the intrinsic
families. `SomeTypedModule`/`SomeTypedFunction` are dependent sums that retain
the interface or signature. `CheckedModule W iface` and `CheckedFunction` are
raw syntax with a judgment at a known index. `Typing.declaredEquiv` exchanges
the checked dependent sum for a raw/index pair with a proof, retaining both
values exactly. `Typing.Declared.forget` instead gives a raw term with a
propositional existence proof: its fibers identify exactly the same raw term,
even when the indices differ. We do not assume index uniqueness.

At a fixed index, `wasm3ModuleEquiv` and `wasm3FunctionEquiv` are equivalences
only **after quotienting by exact erasure**, not equivalences of typing trees
or semantic congruences. The intrinsic family instance requires soundness and
exact-erasure lifting against the real judgment. `Strict.checkedEquiv` is
two-sided on the checked raw image, cancels the nested subtype, and does not
claim that the strict subtype has a new intrinsic syntax. `Strict.parts`
retains the assembled module exactly and uses the standard `ModuleParts` API.

The [native V1 scalar fragment](wasm-v1-intrinsic.md) has its own stack- and
context-indexed instructions, bodies, functions and single-export module. It
proves native validation and exact Core emission, but does not implement the
arbitrary source lifting required by a full `HasIntrinsic Wasm1` instance.

## Functional and strict boundaries

`FunctionalCore GCMode ExceptionMode` makes the two choices independent:

| Alias | GC fields and writes | Exception tags, types and instructions |
| --- | --- | --- |
| `Functional` | Mutable allowed | Internal allowed |
| `FunctionalNoExceptions` | Mutable allowed | Disabled |
| `StrictWithExceptions` | Immutable only | Internal allowed |
| `Strict` | Immutable only | Disabled |

`closedShape` checks that **all four** have no imports, linear memories, tables,
globals, element segments or data segments, and only export functions. In
particular an internal tag cannot be exported as a host entry; this does not
promise that every throw is caught. `features`
uses `functionalMutGC` or `functional`; disabling exceptions removes `.exn`.
The feature check already traverses recursion groups (including fields and
function signatures), locals, type immediates, and nested block/loop/if/try
bodies. Typing still resolves all references and validates exports/start and
handlers. Legacy exception opcodes and shared/atomic extensions are not enabled.
The selected manifests are not maximal: for example they do not enable SIMD,
saturating conversion, sign extension or bulk-memory instructions.

`FunctionalCore.allowMutation` and `allowExceptions` are injections preserving
the exact Core AST. `inclusion_square` proves they commute, `checkedToCore`
preserves the actual Core `ModuleOk` interface, and `checkedEquiv` is two-sided
onto the precisely guarded well-typed Core image. None claims a semantics or
UB policy. Modules cannot call imported host functions, but they may be called
through exports, can still use opaque external reference values, and may trap,
allocate, or diverge. Immutable allocation is not asserted observationally pure.

The [regressions](../../tests/wasm/profiles/Functional.lean) independently check
the validator and the guards. A block allocates and actually writes a mutable
struct via `struct.set`; it separates the two GC modes even with EH disabled.
An immutable-mode module throws to a local `try_table` handler, separating
the exception modes. The tests also check an immutable capture record holding
a scalar and a typed function reference, projecting them and applying with
`call_ref`. Function exports provide `ref.func` declaration scope. This is a
checked closure-shaped target example, not a closure-conversion algorithm or
execution equivalence theorem.

`Profiles.Functional`'s `FunctionalISA` namespace adds raw and stack-indexed
inductive code for numeric add/div and constants, initialized local reads,
`ref.i31`, `ref.func` and `call_ref`, struct allocation/reads and mutable-only
writes, and `i32` result blocks with in-scope `br_if 0`. `Code.toRaw` drops only
typing indices and proofs; `.sub` has no runtime syntax. `Code.sound` derives `InstrsOk` for the
same erased expression using the real Core frame, block, branch and GC rules.
`Code.liftCore` gives a Core intrinsic witness with that exact erasure, not a
canonical inverse on derivations. `Raw.features` traverses the raw tree and
`Raw.allowWrites_erase` proves exact erasure after widening mutability. This
instruction slice does not check the enclosing module declarations. It does not
cover local writes, arrays, general branch depths or EH syntax. The checked
closure fixture has intrinsic terms for allocation and application: `ref.func`
requires declaration scope, and `call_ref` requires a function signature at the
type index. Their exact erasures bracket the fixture's `local.set`, which still
needs a local-init effect to express the entire body in this slice. An immutable
closure can still carry a null callee and calling it can trap.

## A checked opcode slice

The `Profiles.ISA` slice covers ten immediate-free instructions: `i32`/`i64`
addition and signed/unsigned division, `i64.extend32_s`, the two
`i32.trunc_sat_f32` signednesses, and `ref.i31`. `Flat` is an ordinary enum;
`RawOp` factors integer width and operator. `Flat.factoredEquiv` preserves Core
erasure. `Op` is the factored syntax indexed by precise input and output stacks.
`Flat.At.equiv` is a two-sided typed equivalence at fixed stack effects, while
`Flat.equiv` and `RawOp.equiv` retain those effects in a dependent sum.
`Op.sound` derives the actual Core `InstrOk` rule, not just a classification.
Factoring does not introduce `i32.extend32_s` or identify the two divisions.

`Admitted Wasm1` embeds into `Admitted Wasm2` and then `Admitted Wasm3` without
changing the operation. Sign extension and saturating conversion separate the
first two; `ref.i31` separates the next two. `Flat.toV1_core` and
`Flat.toV2_core` check the manifest/native syntax/Core translation triangles
on **this slice**. `Admitted Strict` is the same enum restricted by the Strict
manifest; there are no control transfers or exception instructions in this slice.

`Opcode` distinguishes primary bytes from the `0xfb` GC, `0xfc` miscellaneous,
`0xfd` SIMD and `0xfe` atomic spaces. A prefixed index is a `u32`, serialized
with the existing unsigned LEB encoder. The [opcode chart](https://wasm-chart.pengowray.com/)
is a quick reference; the formal evidence is the [pinned Core 3.0 binary
grammar](../../specs/spectec/src/specification/wasm-3.0/5.3-binary.instructions.spectec)
and `Binary.Core`'s opcode propositions and reader. `Flat.lookup?_some` is exact
on the ten tags, `Flat.encodes` inhabits the Core binary relation, and
`Flat.readOne_bytes` runs the existing instruction decoder on canonical bytes
and proves exact consumption. The regression also exercises a non-minimal
permitted `0xfc` LEB and a truncated one.

No instruction with additional immediates is represented by just its opcode.
An uncovered opcode need not be reserved: for example `0xfc 10` is
`memory.copy`, with further immediates. SIMD/atomic spaces have no entries in
the slice; representing their indices does not enable them in the Core reader
or a strict module. Factoring structured control or exception handling next
requires the body and handler typing indices, not just more enum cases.
