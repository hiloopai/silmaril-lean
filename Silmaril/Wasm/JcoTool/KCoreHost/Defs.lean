module

public import Silmaril.Wasm.JcoTool.KCoreRun.Defs

/-!
# The canonical built-ins as a Core 3.0 host store

`KCoreRun` runs the generated stream modules (`KCoreEmit.toModule`) on Core 3.0 with the eight
imported canonical built-ins supplied as host functions. Its instantiation theorems assumed a
store that supplies them (`KCoreRun.ImpsOK hb s as`). Here is such a store, built once for every
host-call encoding `hb`:

* `hostDT b`: the defined type of built-in `b`'s import, the type of `KCoreEmit.types` that
  `KCoreEmit.imports` gives it, closed (`liftRec`, the closed form silmaril's validation uses);
* `hostStore hb`: a store whose functions `0..7` are the host functions `hb b` with those types,
  in `KCoreEmit.biFn` order; `hostAddrs = [0, …, 7]`.

`KCoreHost.Thms` proves `ImpsOK hb (hostStore hb) hostAddrs` (`impsOK_host`), so the
instantiation and lift theorems of `KCoreRun` hold on this store with no hypothesis on it.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KCoreHost

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.JcoTool.KCore (BI)

/-- The type index of built-in `b`'s import in `KCoreEmit.types` (as `KCoreEmit.imports`). -/
def impTy : BI → Nat
  | .taskReturn => 0 | .streamNew => 1 | .streamRead => 2 | .streamWrite => 2
  | .dropR => 0 | .dropW => 0 | .wsNew => 3 | .join => 4

/-- The closed defined type of built-in `b`'s import. -/
def hostDT (b : BI) : DefType :=
  .defn (liftRec (Silmaril.Wasm.JcoTool.KCoreEmit.types.getD (impTy b) ⟨[]⟩)) 0

/-- The built-ins in `KCoreEmit.biFn` order. -/
def bis : List BI := [.taskReturn, .streamNew, .streamRead, .streamWrite, .dropR, .dropW, .wsNew, .join]

variable {H : Type}

/-- **The host store**: functions `0..7` are the built-ins, as host functions `hb b`. -/
def hostStore (hb : BI → H) : Store H :=
  { funcs := bis.map fun b => ⟨hostDT b, {}, .host (hb b)⟩ }

/-- The addresses of the built-ins in `hostStore`. -/
def hostAddrs : List Nat := List.range 8

end Silmaril.Wasm.JcoTool.KCoreHost
