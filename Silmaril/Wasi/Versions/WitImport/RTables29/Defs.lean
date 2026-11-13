module

public import Silmaril.Wasi.Versions.WitImport.RImport.Defs
public meta import Silmaril.Wasi.Versions.WitImport.RQuote.Defs

@[expose] public section

/-!
# Resolved WASI 0.2.9 tables with their type environments

The 0.2.9 counterparts of `Silmaril.Wasi.Versions.WitImport.RTables` and of `rand2P`: each package
is `wit_rpkg% unversioned all …` on the files of `specs/wasi/v0.2.9` (WebAssembly/WASI tag
`v0.2.9`, provenance in `provenance/wasi-0.2.9-wit.json`), in the same order as the 0.2.12
files. The hand-written 0.2 modules (`P2/Io`, `P2/World`) cite these files; until now only
the 0.2.12 files were imported. `Silmaril.Wasi.Versions.WitImport.R29.Thms` compares the tables
with the 0.2.12 ones.

| package | files (`specs/wasi/v0.2.9/…`) |
| --- | --- |
| `io29P` | `io/{error,poll,streams}.wit` |
| `clocks29P` | `clocks/{monotonic-clock,wall-clock,timezone}.wit` with the io files |
| `cli29P` | `cli/{environment,exit,run,stdio,terminal}.wit` with the io files |
| `fs29P` | `filesystem/{types,preopens}.wit` with the clocks and io files |
| `rand29P` | `random/{insecure-seed,insecure,random}.wit` |

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- `wasi:io@0.2.9`, resolved. -/
def io29P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/v0.2.9/io/error.wit"
    "../../../../../specs/wasi/v0.2.9/io/poll.wit"
    "../../../../../specs/wasi/v0.2.9/io/streams.wit"
/-- `wasi:clocks@0.2.9`, resolved. -/
def clocks29P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
    "../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
    "../../../../../specs/wasi/v0.2.9/io/error.wit"
    "../../../../../specs/wasi/v0.2.9/io/poll.wit"
    "../../../../../specs/wasi/v0.2.9/io/streams.wit"
/-- `wasi:cli@0.2.9` (interfaces), resolved. -/
def cli29P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/v0.2.9/cli/environment.wit"
    "../../../../../specs/wasi/v0.2.9/cli/exit.wit"
    "../../../../../specs/wasi/v0.2.9/cli/run.wit"
    "../../../../../specs/wasi/v0.2.9/cli/stdio.wit"
    "../../../../../specs/wasi/v0.2.9/cli/terminal.wit"
    "../../../../../specs/wasi/v0.2.9/io/error.wit"
    "../../../../../specs/wasi/v0.2.9/io/poll.wit"
    "../../../../../specs/wasi/v0.2.9/io/streams.wit"
/-- `wasi:filesystem@0.2.9`, resolved. -/
def fs29P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/v0.2.9/filesystem/types.wit"
    "../../../../../specs/wasi/v0.2.9/filesystem/preopens.wit"
    "../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
    "../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
    "../../../../../specs/wasi/v0.2.9/io/error.wit"
    "../../../../../specs/wasi/v0.2.9/io/poll.wit"
    "../../../../../specs/wasi/v0.2.9/io/streams.wit"
/-- `wasi:random@0.2.9`, resolved. -/
def rand29P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/v0.2.9/random/insecure-seed.wit"
    "../../../../../specs/wasi/v0.2.9/random/insecure.wit"
    "../../../../../specs/wasi/v0.2.9/random/random.wit"

end Silmaril.Wasi.Versions.WitImport
