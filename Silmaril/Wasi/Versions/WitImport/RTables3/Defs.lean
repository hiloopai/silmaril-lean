module

public import Silmaril.Wasi.Versions.WitImport.RImport.Defs
public meta import Silmaril.Wasi.Versions.WitImport.RQuote.Defs

@[expose] public section

/-!
# Resolved WASI 0.3 tables (and `wasi:random` 0.2) with their type environments

As `Silmaril.Wasi.Versions.WitImport.RTables` for 0.2: each package is `wit_rpkg% …` on the same
vendored files as its table in `Silmaril.Wasi.Versions.WitImport.Tables` (or
`Silmaril.Wasi.Versions.WitImport.Http3Table`). `strip` of each resolved table is the
corresponding table (`rand3P_strip`, `p3P_strip`, `http3P_strip`, in
`Silmaril.Wasi.Versions.WitImport.RP3`).

| package | table | files |
| --- | --- | --- |
| `rand3P` | `rand3T` | `random/{insecure-seed,insecure,random}.wit` |
| `clocks3P` | `clocks3T` | `clocks/{monotonic-clock,system-clock,timezone,types}.wit` |
| `cli3P` | `cli3T` | `cli/{environment,exit,run,stdio,terminal}.wit` |
| `fs3P` | `fs3T` | `filesystem/{types,preopens}.wit` with the clocks files |
| `http3P` | `http3T` | `http/{worlds,types}.wit` (worlds dropped) with the clocks files |
| `rand2P` | `rand2T` | 0.2.12 `random/{insecure-seed,insecure,random}.wit` |

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- `wasi:random@0.3.2`, resolved. -/
def rand3P : RPkg := wit_rpkg% versioned all
    "../../../../../specs/wasi/0.3.2/random/insecure-seed.wit"
    "../../../../../specs/wasi/0.3.2/random/insecure.wit"
    "../../../../../specs/wasi/0.3.2/random/random.wit"
/-- `wasi:clocks@0.3.2`, resolved. -/
def clocks3P : RPkg := wit_rpkg% versioned all
    "../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
    "../../../../../specs/wasi/0.3.2/clocks/types.wit"
/-- `wasi:cli@0.3.2` (interfaces), resolved. -/
def cli3P : RPkg := wit_rpkg% versioned all
    "../../../../../specs/wasi/0.3.2/cli/environment.wit"
    "../../../../../specs/wasi/0.3.2/cli/exit.wit"
    "../../../../../specs/wasi/0.3.2/cli/run.wit"
    "../../../../../specs/wasi/0.3.2/cli/stdio.wit"
    "../../../../../specs/wasi/0.3.2/cli/terminal.wit"
/-- `wasi:filesystem@0.3.2`, resolved. -/
def fs3P : RPkg := wit_rpkg% versioned all
    "../../../../../specs/wasi/0.3.2/filesystem/types.wit"
    "../../../../../specs/wasi/0.3.2/filesystem/preopens.wit"
    "../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
    "../../../../../specs/wasi/0.3.2/clocks/types.wit"
/-- `wasi:http@0.3.2` (interfaces `handler` and `client`), resolved. -/
def http3P : RPkg := wit_rpkg% versioned ifaces
    "../../../../../specs/wasi/0.3.2/http/worlds.wit"
    "../../../../../specs/wasi/0.3.2/http/types.wit"
    "../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
    "../../../../../specs/wasi/0.3.2/clocks/types.wit"

/-- `wasi:random@0.2.12`, resolved. -/
def rand2P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/0.2.12/random/insecure-seed.wit"
    "../../../../../specs/wasi/0.2.12/random/insecure.wit"
    "../../../../../specs/wasi/0.2.12/random/random.wit"

end Silmaril.Wasi.Versions.WitImport
