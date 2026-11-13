module

public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs

@[expose] public section

/-!
# The resolved WIT packages of the hand-written 0.2 and 0.3 slices

`p2P` (0.2.12 `cli`, `clocks`, `filesystem`) and `p3P` (0.3.2 `cli`, `clocks`, `filesystem`):
the resolved tables of `RTables`/`RTables3`, appended with their type environments. They used
to be defined in `WitImport.RCli2` and `WitImport.RP3`, which import the theorem modules of the
hand-written slices; they live here, below `P2.World` and `P3`, so that `P2.cliOk` and `P3.ok3`
can be defined from them (track `wf-p2-switch`). The names are unchanged.

Also here: two type abbreviations used by those definitions' comparisons (`lref`, `tStreamFut`,
previously in `WitImport.P3`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-- The resolved 0.2.12 `cli`, `clocks` and `filesystem` packages. -/
def p2P : RPkg := rappend cli2P (rappend clocks2P fs2P)

/-- The resolved 0.3.2 `cli`, `clocks` and `filesystem` packages. -/
def p3P : RPkg := rappend cli3P (rappend clocks3P fs3P)

/-- A local named type. -/
abbrev lref (n : String) : Binary.Ty := .ref ⟨.local, n⟩

/-- `tuple<stream<u8>, future<result<_, error-code>>>`. -/
abbrev tStreamFut : Binary.Ty :=
  .tuple [.stream (some (.prim .u8)), .future (some (.result none (some (lref "error-code"))))]

end Silmaril.Wasi.Versions.WitImport
