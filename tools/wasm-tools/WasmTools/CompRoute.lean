import WasmTools.CompHook
import WasmTools.CompVal
import WasmTools.ValidateComp
import WasmTools.SpecMain

/-!
# The component path of the full build

`install` sets `WasmTools.CompHook.hooks` to the compval track's bodies, so that the core
groups' `print` and `parse` hand component inputs (`CompVal.isComponentInput`) to
`CompVal.printOn` and `parseOn`, and `validate` (behind the core reader, as in `wasm-tools-vt`)
runs the component-aware `ValidateComp.run` behind the specification. The full build
(`wasm-tools`) and `wasm-tools-vt` call it at the start of `main`; the core build
(`wasm-tools-core`) does not import this module.
-/

namespace WasmTools.CompRoute

/-- `wasm-tools validate ARGS…` behind the specification (`ValidateComp.run` on its record). -/
def validate (args : List String) : IO UInt32 :=
  WasmTools.specMain (fun _ _ m =>
      if m.path == ["validate"] then ValidateComp.run (CompVal.ValidateArgs.ofMatches m)
      else notImplemented m.path)
    ("validate" :: args)

/-- Install the component path. -/
def install : IO Unit :=
  CompHook.hooks.set (some
    { isComponent := CompVal.isComponentInput
      parseOn := CompVal.parseOn
      printOn := CompVal.printOn
      validate := validate })

end WasmTools.CompRoute
