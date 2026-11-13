module

public import Silmaril.Wasm.Component.Reference.Wasm.Execution.Runtime.Host.Defs

public import Silmaril.Wasm.Execution.Runtime

@[expose] public section

/-! # Store extension and host contracts

Store extension preserves allocated addresses and immutable contents; it is
separate from store validity. `HostContract` states the required nonempty
outcome set, result typing, and preservation of an explicit store invariant.
It does not supply a complete store-typing judgment or a type-safety theorem.

See the [Wasm 1.0 runtime properties](https://github.com/WebAssembly/spec/blob/977f97014c962f7bd1291fcc6d28b41a924882bf/document/core/appendix/properties.rst).
-/

namespace Silmaril.Wasm.Execution.Runtime

end Silmaril.Wasm.Execution.Runtime
