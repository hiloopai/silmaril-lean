module

public import Silmaril.Wasm.Wac.Nest.Defs

/-!
# WAC: nesting and inlining with first-occurrence import order

`nest_inline` (`Silmaril.Wasm.Wac.NestInline.Thms`) compares the nested and the inlined
composition over **sorted** imports (`Graph.toCompSorted`). `Graph.toComp` lists the
imports in first-occurrence order instead, and the two sides can list them in different
orders (`Silmaril.Wasm.Wac.NestOrder.Thms` has an instance). Imports are positional in the
component IR, so the two components then differ by a renumbering of their imports.

`importPerm I J` is that renumbering: for each import of `J`, in order, a forward to the
import of the same name in `I`. Composing the handler of `importPerm I J` below a
component over the imports `J` gives a component over the imports `I`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component

/-- **The renumbering of imports**: the `i`-th import of `J` is forwarded to the import
of the same name in `I`. -/
def importPerm (I J : Iface) : List Impl :=
  (names J).map fun x => .fwd ((names I).idxOf x)

end Silmaril.Wasm.Wac
