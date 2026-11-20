# Choosing a Wasm entry point

Start with [`Silmaril.Wasm.Profiles.Syntax.Thms`](../../Silmaril/Wasm/Profiles/Syntax/Thms.lean)
for a function or module. Add
[`Silmaril.Wasm.Profiles.Syntax.Components.Thms`](../../Silmaril/Wasm/Profiles/Syntax/Components/Thms.lean)
for components. These use the same `Family` interface: `Untyped` is raw syntax,
`Checked index` attaches the actual typing judgment, and `Intrinsic.Typed index`
selects a representation whose erasure is sound. `SomeTyped` retains the index;
`Accepted` forgets it. Erasure quotients identify the same raw AST, not programs
that happen to behave alike. Lifting all checked ASTs is a separate theorem.

For Core execution, import
[`Silmaril.Wasm.Execution.Core.Entry.Program.Thms`](../../Silmaril/Wasm/Execution/Core/Entry/Program/Thms.lean).
Use `HasOpSem.May` and `HasOpSem.UBReachable` for program observations, and
`OpSem.Diverges` for infinite runs from a state. These are unfuelled. Use a
bounded runner only when executing or measuring a witness. Missing entry,
trap, reachable UB, and divergence are distinct; a checked module has not
necessarily been instantiated or linked. See the [operational guide](opsem-programs.md).

## Core and Lime coverage

| Dialect and unit | Raw, checked, and intrinsic syntax | Actual execution boundary |
| --- | --- | --- |
| **Core function** | `Wasm.Func`; `Core.functionSyntax context` uses `FuncOk`; `Core.functionWitness context` and `functionLifts` use the existing validation witnesses. | `Entry.ResolvedExport.equivalent` compares the intrinsic integer/local body machine with Core invocation of an already resolved named export (no host). A bare open function is not an entry. |
| **Core module** | `Wasm.Module` / `ModuleParts`; `Core.moduleSyntax` is indexed by `CModuleType`; `Core.moduleWitness` lifts checked modules. The section split is exact. | `Entry.rawModule`, `checkedModule`, and `typedModule` use actual Core initialization with an input store and resolved imports. `typedModule_equivalent_raw` compares finite observations and reachable UB under `HostOk`; it is not an independent typed interpreter or a readiness theorem. |
| **Core component** | `Component Wasm.Module`; `Core.componentSyntax feat` uses `ValidComponentCore3`; `Core.componentWitness feat` wraps flat `IntrinsicWiring.Closed` with reference-validated, named Core payloads, not intrinsically typed payload bodies. | Use the stock component observer. `Closed.terminal_iff` needs an exact `Simple` presentation and `Adequate`; `DirectLift.terminalReadback` preserves the final store of a terminal default-option direct lift in a ready one-owner frame. Neither gives whole-component `HasOpSem` equivalence. |
| **Lime function** | `Lime1.Func`; `Lime.functionSyntax context` uses native type resolution and body typing; `LimeScalar.functionWitness context` covers the stack-indexed scalar slice, including direct-call syntax and multi-result signatures. No general reifier. | Native `Lime1.Execution.Step` and `lime1_core_beh` concern allocated invocations. The latter includes source behavior in the induced Core host at `Profile.spec` with store/host premises; it supplies neither reflection nor a native scalar `HasOpSem` entry adapter. |
| **Lime module** | `Lime1.Module`; `Lime.moduleSyntax` uses native `ModuleValid` (index `Unit`, not a named interface); `LimeScalar.moduleWitness` covers one exported scalar definition. No full lifting or decidable native validator. | Native instantiation and its conditional Core simulation exist. The AST map `toCore` is not `toCoreBinary`. A composed program observation theorem still needs to match readiness, resolved export addresses and observer arguments for the translated initialization. |
| **Lime component** | `Component Lime1.Module`; `Lime.componentSyntax feat` uses full `ValidComponentLime1`. `Lime.componentWitness feat` combines flat wiring with native scalar payload witnesses. `checkLime1?` alone does **not** certify those bodies. | The native reference Lime engine (`lime1Semantics`) exists. The Core-restricted `lime1RT` game uses a different construction. There is no adapter here from these typed Lime declarations to matching native/Core ready configurations and component observations. |

## What commutes

`Lime.componentWitness_erase` gives an exact square for any closed program in
the supported wiring grammar: erase the wiring and map payload erasure over it,
or erase the payloads through the scope-indexed program and then erase the
wiring. Either route produces the same native Lime component AST; the witness
proves `ValidComponentLime1` at the original named interface. The body-validity
conjunct comes from the native module witnesses, not from a second run of
`checkLime1?`. The [wired adder regression](../../tests/wasm/profiles/ComponentSyntax.lean)
checks both paths, the `add` exposure and its Core syntax image, plus an
interface-resolving payload with an invalid body and rejection of nested wiring
by the scoped reifier. The flat grammar has Core declarations, instances,
aliases, function types, canonical adapters and unascribed exports. It does not
lift arbitrary checked components or compile arbitrary Lime bodies.

[The sublanguage API](wasm-sublanguages.md) embeds native syntax into Core and
checks which feature sets admit its image. It does not select a semantic policy.
For valid native Lime payloads with function-only ports,
[`resolveLimeFunctionPorts`](../../Silmaril/Wasm/Component/Reference/Validation/FunctionPorts/Thms.lean)
proves that `lime1ModuleType` and `core3ModuleType?` of `toCore` agree after
translating the function signatures. This preserves names and declaration order,
including reexports. Export names are unique by validation; import keys may
repeat. Exact signature equality is reflected, not ABI or subtype compatibility.

The next static obligation is to lift this module-level agreement through the
wiring and canonical-lift commands. Execution also needs a relation on ready
stores and resolved addresses, aligned ABI arguments/results, and related host
moves. [The independent Core ready-entry and terminal read-back proofs](https://github.com/hiloopai/silmaril-lean/pull/1410)
supply a scoped Core-side result, not that cross-dialect square.

The [room/corridor laws](../../Silmaril/Logic/Institution/Room.lean) and
[SpecTec reduct and satisfaction laws](../../Silmaril/Wasm/SpecTec/Institution/Thms.lean)
are separate. No institution morphism is inferred from an AST injection or
this erasure square: a model reduct and its satisfaction law for the selected
sentences would have to be supplied.

```sh
make check CHECK_TARGETS='+Silmaril.Wasm.Profiles.Syntax.Components.Thms +Silmaril.Wasm.Profiles.Syntax.LimeScalar.Thms +Silmaril.Wasm.Execution.Core.Entry.Program.Thms +Silmaril.Wasm.Execution.Core.Entry.Program.Versions.Thms +Silmaril.Semantics.Operational.Determinism.Fuel.Thms +Silmaril.Wasm.Component.IntrinsicWiring.Lift.Observation.Thms +Silmaril.Wasm.Component.Reference.DirectLift.Thms'
```
