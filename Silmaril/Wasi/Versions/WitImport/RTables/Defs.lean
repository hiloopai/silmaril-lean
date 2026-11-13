module

public import Silmaril.Wasi.Versions.WitImport.RImport.Defs
public meta import Silmaril.Wasi.Versions.WitImport.RQuote.Defs

@[expose] public section

/-!
# Resolved WASI 0.2 tables with their type environments

Each package is `wit_rpkg% …` on the same vendored files as its table in
`Silmaril.Wasi.Versions.WitImport.Tables`: the resolved table (functions with their interface and
signature) and the named types of the package and its dependencies. `strip` of each resolved
table is the corresponding table (`io2R_strip`, …, in `Silmaril.Wasi.Versions.WitImport.RTyping`).

| package | table | files |
| --- | --- | --- |
| `io2P` | `io2T` | `io/{error,poll,streams}.wit` |
| `clocks2P` | `clocks2T` | `clocks/{monotonic-clock,wall-clock,timezone}.wit` with the io files |
| `cli2P` | `cli2T` | `cli/{environment,exit,run,stdio,terminal}.wit` with the io files |
| `fs2P` | `fs2T` | `filesystem/{types,preopens}.wit` with the clocks and io files |

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- `wasi:io@0.2.12`, resolved. -/
def io2P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"
/-- `wasi:clocks@0.2.12`, resolved. -/
def clocks2P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"
/-- `wasi:cli@0.2.12` (interfaces), resolved. -/
def cli2P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/0.2.12/cli/environment.wit"
    "../../../../../specs/wasi/0.2.12/cli/exit.wit"
    "../../../../../specs/wasi/0.2.12/cli/run.wit"
    "../../../../../specs/wasi/0.2.12/cli/stdio.wit"
    "../../../../../specs/wasi/0.2.12/cli/terminal.wit"
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"
/-- `wasi:filesystem@0.2.12`, resolved. -/
def fs2P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/0.2.12/filesystem/types.wit"
    "../../../../../specs/wasi/0.2.12/filesystem/preopens.wit"
    "../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport
