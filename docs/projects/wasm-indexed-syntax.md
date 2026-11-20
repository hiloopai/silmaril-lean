# Indexed Wasm syntax

For component and execution entry points, see [Choosing a Wasm entry point](wasm-entry.md).

Import `Silmaril.Wasm.Profiles.Syntax.Thms`. `moduleFamily W` and
`functionFamily W context` are views of the existing `Profiles.HasSyntax`
and `HasTyping` instances, not a second class registry. A function's context
is fixed before choosing its signature. A module uses its actual validation
interface, or `Unit` when its native validator has no interface index.

| Want | Use |
| --- | --- |
| Raw syntax | `family.Untyped` (the existing `Module W` or `Function W`) |
| Raw, with proof at a known index | `family.Checked index` |
| Raw, retaining its checked index | `family.SomeChecked` or `family.Declared` (exactly equivalent) |
| Raw, forgetting its checked index | `family.Accepted` |
| Intrinsic syntax at a known index | `witness.Typed index` |
| Intrinsic syntax retaining its index | `witness.SomeTyped` |

`witness.checked` and `witness.someChecked` erase with a proof of the real
judgment. `Intrinsic.Lifts` is separate: it states existence of a witness at
the same index with exact erasure, not an executable reifier. With `Lifts`,
`Intrinsic.erasureEquiv` equates the **fixed-index exact-erasure quotient** to
checked raw terms; it does not identify witness trees or prove semantic
equivalence. `Family.forget` is always surjective and only identifies equal
raw syntax. `Family.acceptedEquiv` requires a separate proof of index
uniqueness (proved for the Core and Lime families, with a fixed context for
functions). Its inverse need not be executable.

## Choose a family

- **Core 3.0:** `Syntax.Core.moduleSyntax` and `Syntax.Core.functionSyntax
  context` are the actual `Wasm.Module` and `Wasm.Func`. `moduleWitness` and
  `functionWitness context` are the existing full intrinsic families.
  `Core.partsSyntax` uses `ModuleParts Func` with the same Core interface;
  `checkedPartsEquiv` splits and reassembles without losing sections or local
  definitions. `toPartsWitness.checked_natural` agrees with splitting after
  erasure. None of this validates the sections by themselves.
- **Wasm1 and Lime:** `moduleFamily Wasm1` or `Syntax.Lime.moduleSyntax` use
  native module validity. The analogous function views retain the resolved
  type. Import `Silmaril.Wasm.Profiles.Syntax.LimeScalar.Thms` for explicit
  stack-indexed Lime witnesses for integer operations, scalar `select`,
  locals and direct calls, with one exported definition in the closed module
  slice. Multi-result functions work natively. The function and module maps
  from the existing Wasm1 scalar slice commute exactly with native erasure and
  validation. Neither slice supplies lifting for all native modules/functions.
- **Wasm2:** Native checked forms and `Injections.checkedWasm2ToWasm3`
  are available. The raw conversion is partial, so it is not registered as
  a total `Family.Map`. There is no native intrinsic family here.
- **FX:** `Profiles.HasSyntax` selects the loadable Core module and extended
  FX body. No native whole-FX typing or intrinsic instance is assumed.

## Map syntax without choosing semantics

`Family.Map` supplies a raw map, an index map, and typing preservation;
`id`, `comp`, and the checked/forgotten-index laws keep those choices coherent.
Use `Intrinsic.Map` when there is an explicit witness map with an erasure
square. `onErasure` descends that map to the quotient, and
`erasureChecked_natural` proves it agrees with the checked map.
`wasm1ModuleToLime` and `wasm1FunctionToLime` reuse the native
injections, and `functionalOfLE` followed by `functionalToCore` agrees exactly
with embedding directly. The Lime-to-Core validation transfer gives existence
of a Core interface; it is not an index map from Lime's `Unit` to a fixed Core
interface. Use the existing accepted-raw adapter or the checked Core reifier
when it supports the body.

For component clients, `Core.moduleWitness` erases to the input of
[`Component.Validation.core3ModuleType?`](../../Silmaril/Wasm/Component/Reference/Validation/Defs.lean).
That resolver adds named, ordered ports; the unnamed `CModuleType` alone is
not a component interface. The existing
[`IntrinsicWiring.Program.map`](../../Silmaril/Wasm/Component/IntrinsicWiring/Defs.lean)
needs preservation of the resolver's result, which is automatic for exact
erasure-preserving changes of representation. The component judgment and
scope indices stay with the component track. No operational policy is chosen
by this API, and no satisfaction condition follows merely from these maps.
See the existing [room and corridor laws](../../Silmaril/Logic/Institution/Room.lean)
and [SpecTec institution chain](../../Silmaril/Wasm/SpecTec/Institution/Chain2030/Thms.lean)
for the additional model-side data and proofs.

The [regression](../../tests/wasm/profiles/IndexedSyntax.lean) crosses the
Wasm1–Lime–Core syntax path, checks a two-result Lime export, passes its Core
image through the real reifier and `ModuleParts`, and exercises a Core feature
inclusion and a counterexample to forgetting a nonunique index.

```sh
make check CHECK_TARGETS=+Silmaril.Wasm.Profiles.Syntax.LimeScalar.Thms
```
