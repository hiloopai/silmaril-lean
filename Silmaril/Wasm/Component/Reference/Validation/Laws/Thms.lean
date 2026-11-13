module

public import Silmaril.Wasm.Component.Reference.Validation.Check.Thms

/-!
# The soundness of the component reference validator, as a header for other topics

`check?_sound`, `checkDef?_sound`, `checkDefs?_sound` and the profile instances
(`checkCore3?_sound`, `checkLime1?_sound`, `checkV1?_sound`, ...) of the component reference
copy, for the component tools (`Silmaril.Wasm.Tools.Component.{Validate,GcAbi}.Thms`) and through
them the component generator (`Silmaril.Wasm.Tools.Gen.Comp.Thms`).

A narrower form of `Silmaril.Wasm.Component.Reference.Laws.Thms`: it re-exports only the
validator's `Thms` part, not the machine, canonical ABI or runtime laws. The soundness chain
(`checkCoreInstance?_sound`, `checkInstantiate?_sound`, `checkAlias?_sound`,
`checkExport?_sound`, `resolveDesc?_iff`, `openInstanceType?_sound` and the declaration
lemmas of `Validation/DefTypes`) is refined into the `Thms` parts, so no Raw module is in this
header's import closure.
-/
