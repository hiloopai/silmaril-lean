/-!
# The component path of the core commands, as a hook

`validate`, `print` and `parse` belong to the core groups (`WasmTools.ValidateCmd`,
`WasmTools.Core`). In the full build (`wasm-tools`, `WasmTools.lean`) they hand component inputs
to the compval track (`WasmTools.CompRoute.install`, which sets `hooks` before the dispatch); in
the core build (`wasm-tools-core`, `WasmToolsCore.lean`) `hooks` stays `none` and no component
module is linked: `validate` checks component binaries with `Silmaril.Wasm.Tools.CompValidate`, and
`print` and `parse` read core modules only.
-/

namespace WasmTools.CompHook

/-- The component path of `validate`, `print` and `parse`. -/
structure Hooks where
  /-- Does the input go to the component path (`CompVal.isComponentInput`)? -/
  isComponent : ByteArray → Bool
  /-- `parse` of a component input: `-t`, `-o`, the input (`CompVal.parseOn`). -/
  parseOn : Bool → Option String → ByteArray → IO (Except String Unit)
  /-- `print` of a component input: `-o`, the input (`CompVal.printOn`). -/
  printOn : Option String → ByteArray → IO (Except String Unit)
  /-- The whole of `validate` (arguments to exit status), components and core modules. -/
  validate : List String → IO UInt32

/-- The component path, if this build has one (set at the start of `main`). -/
initialize hooks : IO.Ref (Option Hooks) ← IO.mkRef none

end WasmTools.CompHook
