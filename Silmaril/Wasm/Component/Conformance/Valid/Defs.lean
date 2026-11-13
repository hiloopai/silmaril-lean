module

public import Silmaril.Wasm.Component.Conformance.ToRef.Defs

/-!
# The validator of the conformance runs

`features` (the feature gates the component-model conformance scripts run wasmtime with) and
`validate c` (the copied validator `Reference.check?` at `features`). They are the part of
`Conformance.Run` that does not run components, kept apart so that validation alone
(`Conformance.Extra.validateFull`, `wasm-tools validate` on components) does not import the
reference machine, the core engine or the hosts of `Conformance.Host`. `Conformance.Run`
re-exports this module.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Conformance

open Silmaril.Wasm.Component

/-- The feature gates of the runs: the set the component-model `test/README.md` (at `d095e2f`)
runs wasmtime with (`-W component-model-more-async-builtins, -threading, -async-stackful,
-implements, -fixed-length-lists, -map, -canonical-names`, plus wasmtime 50's defaults), i.e.
`Features.p3plus` (🔀 🗺️ 🏷️ 📝 🔧 🚝 🚟 🧵 ➡️ 🐘) with 🔗; 📡, 🪙 and 🪺 stay off. -/
def features : Features := { Features.p3plus with canonicalNames := true }

/-- Validate at `features`. -/
def validate (c : RefComponent) : Except String Reference.ComponentType :=
  match Reference.check? features c with
  | .ok t => .ok t
  | .error e => .error (reprStr e)

end Silmaril.Wasm.Component.Conformance
