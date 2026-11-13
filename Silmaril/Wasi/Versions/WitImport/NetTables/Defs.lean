module

public import Silmaril.Wasi.Versions.WitImport.Defs
public meta import Silmaril.Wasi.Versions.WitImport.Quote.Defs

@[expose] public section

/-!
# `wasi:sockets` and `wasi:http` signature tables computed by the WIT importer

As `Silmaril.Wasi.Versions.WitImport.Tables`, for the network packages:

| table | package | files |
| --- | --- | --- |
| `sock3T` | `wasi:sockets@0.3.2` | `sockets/{types,ip-name-lookup}.wit` with the 0.3.2 clocks files |
| `sock2T` | `wasi:sockets@0.2.12` | `sockets/{network,instance-network,tcp,tcp-create-socket,udp,udp-create-socket,ip-name-lookup}.wit` with the 0.2.12 clocks and io files |
| `http2T` | `wasi:http@0.2.12` | `http/{types,handler}.wit` with the 0.2.12 clocks and io files |

`wasi:http@0.3.2` is not imported: its `client` and `handler` interfaces are in `worlds.wit`
together with the worlds `service` and `middleware`, which include the whole of WASI 0.3.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- `wasi:sockets@0.3.2`. -/
def sock3T : Table := wit_table% versioned
    "../../../../../specs/wasi/0.3.2/sockets/types.wit"
    "../../../../../specs/wasi/0.3.2/sockets/ip-name-lookup.wit"
    "../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
    "../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
    "../../../../../specs/wasi/0.3.2/clocks/types.wit"
/-- `wasi:sockets@0.2.12`. -/
def sock2T : Table := wit_table% unversioned
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
/-- `wasi:http@0.2.12`. -/
def http2T : Table := wit_table% unversioned
    "../../../../../specs/wasi/0.2.12/http/types.wit"
    "../../../../../specs/wasi/0.2.12/http/handler.wit"
    "../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
    "../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
    "../../../../../specs/wasi/0.2.12/io/error.wit"
    "../../../../../specs/wasi/0.2.12/io/poll.wit"
    "../../../../../specs/wasi/0.2.12/io/streams.wit"
end Silmaril.Wasi.Versions.WitImport
