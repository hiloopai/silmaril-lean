module

public import Silmaril.Wasi.Versions.WitImport.RImport.Defs
public meta import Silmaril.Wasi.Versions.WitImport.RQuote.Defs

@[expose] public section

/-!
# Resolved WASI 0.2.9 `wasi:sockets` and `wasi:http` tables

The 0.2.9 counterparts of `sock2P` and `http2P` (`Silmaril.Wasi.Versions.WitImport.RNetTables`), on
the files of `specs/wasi/v0.2.9` in the same order. Compared with the 0.2.12 tables in
`Silmaril.Wasi.Versions.WitImport.R29.Thms`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- `wasi:sockets@0.2.9`, resolved. -/
def sock29P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/v0.2.9/sockets/network.wit"
    "../../../../../specs/wasi/v0.2.9/sockets/instance-network.wit"
    "../../../../../specs/wasi/v0.2.9/sockets/tcp.wit"
    "../../../../../specs/wasi/v0.2.9/sockets/tcp-create-socket.wit"
    "../../../../../specs/wasi/v0.2.9/sockets/udp.wit"
    "../../../../../specs/wasi/v0.2.9/sockets/udp-create-socket.wit"
    "../../../../../specs/wasi/v0.2.9/sockets/ip-name-lookup.wit"
    "../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
    "../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
    "../../../../../specs/wasi/v0.2.9/io/error.wit"
    "../../../../../specs/wasi/v0.2.9/io/poll.wit"
    "../../../../../specs/wasi/v0.2.9/io/streams.wit"
/-- `wasi:http@0.2.9`, resolved. -/
def http29P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/v0.2.9/http/types.wit"
    "../../../../../specs/wasi/v0.2.9/http/handler.wit"
    "../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
    "../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
    "../../../../../specs/wasi/v0.2.9/io/error.wit"
    "../../../../../specs/wasi/v0.2.9/io/poll.wit"
    "../../../../../specs/wasi/v0.2.9/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport
