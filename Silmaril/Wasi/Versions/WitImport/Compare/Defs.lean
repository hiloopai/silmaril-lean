module

public import Silmaril.Wasi.Versions.WitImport.Pick.Defs
public import Silmaril.Wasi.Versions.Random.Defs
public import Silmaril.Wasi.Versions.P3.Defs

@[expose] public section

/-!
# Comparing the imported signatures with the hand-written WASI definitions

* `restrict T L`: the entries of a table for the functions `L`.
* `p3T`: the 0.3.2 `cli`, `clocks` and `filesystem` tables; `p3L`: the WASI functions of the
  hand-written 0.3 slice except `get-directories` (`P3.wasiFns3` minus `P3.getDirs3`).
* `lenM P`, `len2`, `len3`: the length part of the hand-written `wasi:random` theories (exact in
  0.2, short reads in 0.3), the part the WIT types do not express.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions.Random

/-- The entries of `T` for the functions `L`. -/
def restrict (T : Table) (L : List FnName) : Table := T.filter fun x => decide (x.1 ∈ L)

/-- The WASI functions of the 0.3 slice whose hand-written typing refines the WIT typing. -/
def p3L : List FnName :=
  [P3.stdoutWrite3, P3.stdinRead3, P3.now3, P3.waitFor3, P3.openAt3, P3.readVia3]

end Silmaril.Wasi.Versions.WitImport
