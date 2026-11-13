module

public import Silmaril.Wasm.Component.Reference.Example.Defs
import Silmaril.Proofs.Wasm.Component.Reference.Example

/-!
# Example: the Core 3.0 adder component, theorems

The adder is a valid Core 3.0 component (`adder3_valid`), and over `core3 neverFail` its
export `"add"` returns `[u32 7]` on `[u32 3, u32 4]` after instantiation from the empty store
(`adder3_returns`). Both are closed runs of the executable validator and drivers (`decide
+kernel`); nothing is claimed for other arguments or for `core3P`.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.Example`.
-/

public section

namespace Silmaril.Wasm.Component.Reference.Core3Adder

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine

/-- The Core 3.0 adder is a valid component of type `adder3Type`. -/
theorem adder3_valid : Valid Features.p2 adder3 adder3Type :=
  Silmaril.Proofs.Wasm.Component.Reference.Core3Adder.adder3_valid

/-- Over `core3 neverFail`, the adder's export `"add"` returns `[u32 7]` on `[u32 3, u32 4]`
after instantiation from the empty store. -/
theorem adder3_returns :
    Outcome.returns (some [Value.Val.u32 7]) ∈
      exportBehaviours first.prof (Host.ofEmbedder emb) () adder3 [] "add"
        [Value.Val.u32 3, Value.Val.u32 4] :=
  Silmaril.Proofs.Wasm.Component.Reference.Core3Adder.adder3_returns

end Silmaril.Wasm.Component.Reference.Core3Adder
