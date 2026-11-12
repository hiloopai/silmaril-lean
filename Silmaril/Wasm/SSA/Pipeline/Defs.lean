module

public import Silmaril.Wasm.SSA.Translate.Defs
public import Silmaril.Wasm.SSA.Passes.Defs
public import Silmaril.Wasm.SSA.OutOfSSA.Defs
public import Silmaril.Wasm.SSA.Bridge.Defs

/-!
# The SSA optimiser for Wasm functions

`optimizeSSA` runs the SSA passes (simplification, then dead bindings, twice);
`optimize` is `fragment → SSA → optimise → fragment`, falling back to the
input when out-of-SSA fails. `optimizeFunc?` works on silmaril `BFunc`s: it
returns `none` when the function is outside the fragment or the optimised
code cannot be brought back, so a driver keeps the original function.
`optimizeModule` applies it to every defined function of a `BModule`.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen

/-- The SSA pipeline. -/
def optimizeSSA (f : SFunc) : SFunc :=
  ((((f.simp {}).dce).simp {}).dce)

/-- Fragment to fragment through SSA, if out-of-SSA succeeds. -/
def optimize? (f : FragFunc) : Option FragFunc := decompileFunc (optimizeSSA (compileFunc f))

/-- Fragment to fragment through SSA, with fallback. -/
def optimize (f : FragFunc) : FragFunc := (optimize? f).getD f

/-- Optimise a Binaryen function of the given type, if it is in the fragment. -/
def optimizeFunc? (ft : FuncType) (bf : BFunc) : Option BFunc := do
  let f ← ofBFunc? ft bf
  toBFunc? bf.type (← optimize? f)

/-- Optimise a function of a module (looking its type up), if possible. -/
def optimizeFuncIn? (m : BModule) (bf : BFunc) : Option BFunc := do
  optimizeFunc? (← m.funcType? bf.type) bf

/-- Optimise every defined function of a module that is in the fragment. -/
def optimizeModule (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => (optimizeFuncIn? m f).getD f }

end Silmaril.Wasm.SSA
