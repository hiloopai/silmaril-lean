module

public import Silmaril.Wasi.Versions.WitImport.Tables.Defs
public import Silmaril.Wasi.Versions.WitImport.NetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.Http3Table.Defs

@[expose] public section

/-!
# Selecting slices of the imported tables

The function sets of the hand-written WASI slices (`Silmaril.Wasi.Versions.P2`, `P3`, `Net`,
`Net3`, `Http3`) are defined from the imported tables with `pick T keys`: the imported functions
of `T` whose interface (version dropped) and function name are among `keys`. This module
imports only the tables (no hand-written WASI module), so the hand-written modules can import
it. The keys are the only hand-entered part: they name the slice, and every key that matches
no imported function would drop a member, which the `…_eq` theorems of the hand-written modules
exclude (they list the members).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi

/-- The interface id without its `@version`. -/
def unver (s : String) : String := String.ofList (s.toList.takeWhile (· ≠ '@'))

/-- The imported functions of `T` with an (unversioned interface, function) among `keys`. -/
def pick (T : List FnName) (keys : List (String × String)) : List FnName :=
  T.filter fun f => keys.contains (unver f.iface, f.fn)

/-- The keys of the `wasi:cli` 0.2 slice (stable imports: no `exit-with-code`, no `run`). -/
def cliKeys : List (String × String) :=
  [("wasi:cli/environment", "get-environment"), ("wasi:cli/environment", "get-arguments"),
   ("wasi:cli/environment", "initial-cwd"), ("wasi:cli/exit", "exit"),
   ("wasi:cli/stdin", "get-stdin"), ("wasi:cli/stdout", "get-stdout"),
   ("wasi:cli/stderr", "get-stderr"), ("wasi:cli/terminal-stdin", "get-terminal-stdin"),
   ("wasi:cli/terminal-stdout", "get-terminal-stdout"),
   ("wasi:cli/terminal-stderr", "get-terminal-stderr")]

/-- The keys of the `wasi:filesystem` 0.2 slice. -/
def fsKeys : List (String × String) :=
  [("wasi:filesystem/preopens", "get-directories"),
   ("wasi:filesystem/types", "[method]descriptor.open-at"),
   ("wasi:filesystem/types", "[method]descriptor.write"),
   ("wasi:filesystem/types", "[method]descriptor.read"),
   ("wasi:filesystem/types", "[resource-drop]descriptor"),
   ("wasi:filesystem/types", "[method]descriptor.read-via-stream"),
   ("wasi:filesystem/types", "[method]descriptor.write-via-stream"),
   ("wasi:filesystem/types", "[method]descriptor.append-via-stream"),
   ("wasi:filesystem/types", "[method]descriptor.get-type")]

/-- The keys of the WASI 0.3 slice. -/
def keys3 : List (String × String) :=
  [("wasi:cli/stdout", "write-via-stream"), ("wasi:cli/stdin", "read-via-stream"),
   ("wasi:clocks/monotonic-clock", "now"), ("wasi:clocks/monotonic-clock", "wait-for"),
   ("wasi:filesystem/preopens", "get-directories"),
   ("wasi:filesystem/types", "[method]descriptor.open-at"),
   ("wasi:filesystem/types", "[method]descriptor.read-via-stream")]

/-- The 0.3.2 tables of the hand-written 0.3 slice. -/
def p3T : Table := cli3T ++ clocks3T ++ fs3T

/-- The keys of the 0.3 TCP slice. -/
def tcp3Keys : List (String × String) :=
  [("wasi:sockets/types", "[static]tcp-socket.create"),
   ("wasi:sockets/types", "[method]tcp-socket.connect")]

/-- The keys of the 0.2 TCP slice. -/
def tcpKeys : List (String × String) :=
  [("wasi:sockets/instance-network", "instance-network"),
   ("wasi:sockets/tcp-create-socket", "create-tcp-socket"),
   ("wasi:sockets/tcp", "[method]tcp-socket.start-connect"),
   ("wasi:sockets/tcp", "[method]tcp-socket.finish-connect")]

/-- The keys of the 0.2 HTTP slice. -/
def httpKeys : List (String × String) :=
  [("wasi:http/outgoing-handler", "handle"),
   ("wasi:http/types", "[method]outgoing-request.set-authority"),
   ("wasi:http/types", "[method]outgoing-request.set-path-with-query"),
   ("wasi:http/types", "[method]future-incoming-response.get"),
   ("wasi:http/types", "[method]incoming-response.status")]

/-- The keys of the 0.3 HTTP slice. -/
def http3Keys : List (String × String) :=
  [("wasi:http/client", "send"), ("wasi:http/types", "[method]request.set-authority"),
   ("wasi:http/types", "[method]request.set-path-with-query"),
   ("wasi:http/types", "[method]response.get-status-code")]

/-- The functions of the imported 0.3 slice that the WIT marks `async`. -/
def async3L : List FnName := (pick (names p3T) keys3).filter fun g => (p3T.lookup g).any (·.async)

end Silmaril.Wasi.Versions.WitImport
