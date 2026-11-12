module

public import Silmaril.Wasi.Versions.WitImport.Defs
public meta import Silmaril.Wasi.Versions.WitImport.Quote.Defs

@[expose] public section

/-!
# WASI signature tables computed by the WIT importer

Each table is `wit_table% …` on vendored WIT files (`specs/wasi`, see `specs/wasi/README.md`
for upstream revisions and `SHA256SUMS`): the functions of the first file's package, in the
universe of all listed files, with their WIT signatures. Only interface files are listed (no
world files: a world such as `wasi:cli/imports` would pull in every package). 0.3 names carry
`@0.3.2`, 0.2 names no version, as in `Silmaril.Wasi.Versions`.

| table | package | files |
| --- | --- | --- |
| `rand3T` | `wasi:random@0.3.2` | `random/{insecure-seed,insecure,random}.wit` |
| `clocks3T` | `wasi:clocks@0.3.2` | `clocks/{monotonic-clock,system-clock,timezone,types}.wit` |
| `cli3T` | `wasi:cli@0.3.2` | `cli/{environment,exit,run,stdio,terminal}.wit` |
| `fs3T`, `fs3D` | `wasi:filesystem@0.3.2` | `filesystem/{types,preopens}.wit` with the clocks files |
| `rand2T` | `wasi:random@0.2.12` | `random/{insecure-seed,insecure,random}.wit` |
| `io2T`, `io2D` | `wasi:io@0.2.12` | `io/{error,poll,streams}.wit` |
| `clocks2T` | `wasi:clocks@0.2.12` | `clocks/{monotonic-clock,wall-clock,timezone}.wit` with the io files |
| `cli2T` | `wasi:cli@0.2.12` | `cli/{environment,exit,run,stdio,terminal}.wit` with the io files |
| `fs2T`, `fs2D` | `wasi:filesystem@0.2.12` | `filesystem/{types,preopens}.wit` with the clocks and io files |

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-! ## WASI 0.3.2 -/

/-- `wasi:random@0.3.2`. -/
def rand3T : Table := wit_table% versioned
    "../../../../../specs/wasi/0.3.2/random/insecure-seed.wit"
    "../../../../../specs/wasi/0.3.2/random/insecure.wit"
    "../../../../../specs/wasi/0.3.2/random/random.wit"
/-- `wasi:clocks@0.3.2`. -/
def clocks3T : Table := wit_table% versioned
    "../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
    "../../../../../specs/wasi/0.3.2/clocks/types.wit"
/-- `wasi:cli@0.3.2` (interfaces). -/
def cli3T : Table := wit_table% versioned
    "../../../../../specs/wasi/0.3.2/cli/environment.wit"
    "../../../../../specs/wasi/0.3.2/cli/exit.wit"
    "../../../../../specs/wasi/0.3.2/cli/run.wit"
    "../../../../../specs/wasi/0.3.2/cli/stdio.wit"
    "../../../../../specs/wasi/0.3.2/cli/terminal.wit"
/-- `wasi:filesystem@0.3.2`. -/
def fs3T : Table := wit_table% versioned
    "../../../../../specs/wasi/0.3.2/filesystem/types.wit"
    "../../../../../specs/wasi/0.3.2/filesystem/preopens.wit"
    "../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
    "../../../../../specs/wasi/0.3.2/clocks/types.wit"
/-- The resource drops of `wasi:filesystem@0.3.2`. -/
def fs3D : List FnName := wit_drops% versioned
    "../../../../../specs/wasi/0.3.2/filesystem/types.wit"
    "../../../../../specs/wasi/0.3.2/filesystem/preopens.wit"
    "../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
    "../../../../../specs/wasi/0.3.2/clocks/types.wit"
/-! ## WASI 0.2.12 -/

/-- `wasi:random@0.2.12`. -/
def rand2T : Table := wit_table% unversioned
    "../../../../../specs/wasi/0.2.12/random/insecure-seed.wit"
    "../../../../../specs/wasi/0.2.12/random/insecure.wit"
    "../../../../../specs/wasi/0.2.12/random/random.wit"
/-- `wasi:io@0.2.12`. -/
def io2T : Table := wit_table% unversioned
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"
/-- The resource drops of `wasi:io@0.2.12`. -/
def io2D : List FnName := wit_drops% unversioned
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"
/-- `wasi:clocks@0.2.12`. -/
def clocks2T : Table := wit_table% unversioned
    "../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"
/-- `wasi:cli@0.2.12` (interfaces). -/
def cli2T : Table := wit_table% unversioned
    "../../../../../specs/wasi/0.2.12/cli/environment.wit"
    "../../../../../specs/wasi/0.2.12/cli/exit.wit"
    "../../../../../specs/wasi/0.2.12/cli/run.wit"
    "../../../../../specs/wasi/0.2.12/cli/stdio.wit"
    "../../../../../specs/wasi/0.2.12/cli/terminal.wit"
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"
/-- `wasi:filesystem@0.2.12`. -/
def fs2T : Table := wit_table% unversioned
    "../../../../../specs/wasi/0.2.12/filesystem/types.wit"
    "../../../../../specs/wasi/0.2.12/filesystem/preopens.wit"
    "../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"
/-- The resource drops of `wasi:filesystem@0.2.12`. -/
def fs2D : List FnName := wit_drops% unversioned
    "../../../../../specs/wasi/0.2.12/filesystem/types.wit"
    "../../../../../specs/wasi/0.2.12/filesystem/preopens.wit"
    "../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"
end Silmaril.Wasi.Versions.WitImport
