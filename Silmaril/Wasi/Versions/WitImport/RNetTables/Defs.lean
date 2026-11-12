module

public import Silmaril.Wasi.Versions.WitImport.RImport.Defs
public meta import Silmaril.Wasi.Versions.WitImport.RQuote.Defs

@[expose] public section

/-!
# Resolved `wasi:sockets` and `wasi:http` 0.2 tables with their type environments

As `Silmaril.Wasi.Versions.WitImport.RTables`, on the files of
`Silmaril.Wasi.Versions.WitImport.NetTables`: `sock3P` (`sock3T`), `sock2P` (`sock2T`) and
`http2P` (`http2T`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- `wasi:sockets@0.3.2`, resolved. -/
def sock3P : RPkg := wit_rpkg% versioned all
    "../../../../../specs/wasi/0.3.2/sockets/types.wit"
    "../../../../../specs/wasi/0.3.2/sockets/ip-name-lookup.wit"
    "../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
    "../../../../../specs/wasi/0.3.2/clocks/types.wit"
/-- `wasi:sockets@0.2.12`, resolved. -/
def sock2P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/0.2.12/sockets/network.wit"
    "../../../../../specs/wasi/0.2.12/sockets/instance-network.wit"
    "../../../../../specs/wasi/0.2.12/sockets/tcp.wit"
    "../../../../../specs/wasi/0.2.12/sockets/tcp-create-socket.wit"
    "../../../../../specs/wasi/0.2.12/sockets/udp.wit"
    "../../../../../specs/wasi/0.2.12/sockets/udp-create-socket.wit"
    "../../../../../specs/wasi/0.2.12/sockets/ip-name-lookup.wit"
    "../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"
/-- `wasi:http@0.2.12`, resolved. -/
def http2P : RPkg := wit_rpkg% unversioned all
    "../../../../../specs/wasi/0.2.12/http/types.wit"
    "../../../../../specs/wasi/0.2.12/http/handler.wit"
    "../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"
end Silmaril.Wasi.Versions.WitImport
