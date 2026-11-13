module

public import Silmaril.Wasi.Versions.WitImport.Defs
public meta import Silmaril.Wasi.Versions.WitImport.SelectQuote.Defs

@[expose] public section

/-!
# The `wasi:http@0.3.2` signature table, selected out of `worlds.wit`

`http3T` is `wit_iface_table%` on `specs/wasi/0.3.2/http/{worlds,types}.wit` with the 0.3.2
clocks files (`types` uses `wasi:clocks/types.{duration}`). The worlds `service` and
`middleware` of `worlds.wit` are dropped before elaboration
(`Silmaril.Wasi.Versions.WitImport.Select`); the interfaces `handler` and `client` (from
`worlds.wit`) and `types` are imported. Names carry `@0.3.2`, as in
`Silmaril.Wasi.Versions.Http3`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- `wasi:http@0.3.2` (interfaces `handler`, `client`, `types`). -/
def http3T : Table := wit_iface_table% versioned
    "../../../../../specs/wasi/0.3.2/http/worlds.wit"
    "../../../../../specs/wasi/0.3.2/http/types.wit"
    "../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
    "../../../../../specs/wasi/0.3.2/clocks/types.wit"

end Silmaril.Wasi.Versions.WitImport
