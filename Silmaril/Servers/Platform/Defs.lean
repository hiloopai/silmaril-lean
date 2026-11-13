module

public import Silmaril.Servers.Reuse.Defs
public import Silmaril.Servers.Cgi.Defs

@[expose] public section

/-!
# Platforms: comparing HTTP servers run as processes, containers, components and scripts

A **platform** (`Platform T`) says what an implementation is on some substrate, what is
observed of its runs there, and how such an observation is read as HTTP traces of type `T`:

* `Impl`, `Obs`, `runs i o`: the implementations, their native observations (socket events,
  component calls, process runs), and which observations a run of `i` can produce;
* `reads o t`: the observation `o` is read as the HTTP trace `t` (a relation: decoding may be
  partial, and the order of concurrent events may be fixed in several ways);
* `view P i`: the HTTP traces of `i`; `Sat P i φ`: every trace of `i` satisfies the trace
  specification `φ`; **`Refines P i Q j`**: every trace of `i` on `P` is a trace of `j` on `Q`
  (trace inclusion, across platforms), so `j`'s specifications hold of `i`.

Instances:

* `Platform.seq σ`, `Platform.fresh σ`, `Platform.host σ` (`Log` traces): a handler with instance
  state `σ` (an origin and its initial state) run on one reused instance, a fresh instance per
  request, or a host that pools instances (`Silmaril.Servers.Reuse`); the last is how the
  `wasi:http` worlds run a component;
* `Platform.cgi g` (`Log`): a CGI or WAGI script (`Silmaril.Servers.Cgi`) with its initial
  files, one run per request, in order;
* `Platform.linux fr` (`ConnLog`): a Linux process serving HTTP/1.1 over sockets: the
  observation is its socket events (`SockEv`: `accept`, `recv`, `send`, `close` per connection),
  and each connection's octets are framed into requests and responses by `fr : Framing`
  (responses in request order, RFC 9112 §9.3);
* `Platform.container fr` (`ConnLog`): a container is a process started from an image
  (`Image`: layers of file changes, `none` a whiteout as in the OCI image layer format) with an
  entry point and environment; it is the process platform at the launch invocation
  (`Container.launch`).

`ConnLog` (one `Log` per connection) and `Log` (one sequence of exchanges) are compared through
`Merge`: a `Log` that interleaves the per-connection logs. So a statement such as "the Wasm
component refines the Linux server" reads: every `Log` of the component under every host is a
merge of a `ConnLog` of the Linux server (`Refines` after `toLogs`).

Not modelled here: the socket semantics of a Linux process (which `SockEv` traces a binary
produces, to be read off `Silmaril.Process` system-call traces), the HTTP/1.1 framing instance
of `Framing` (from `Silmaril.Net.Http1.Framing` once its heads map to
`Silmaril.Net.Http.Request`), interleavings finer than whole exchanges, and the network
between client and server.

A Silmaril addition.
-/

namespace Silmaril.Servers

open Silmaril.Net.Http Silmaril.Cli Silmaril.Servers.Reuse

/-- **A platform**: implementations, their observations, and how observations are read as
HTTP traces `T`. -/
structure Platform (T : Type) where
  /-- The implementations. -/
  Impl : Type
  /-- What is observed of a run. -/
  Obs : Type
  /-- `runs i o`: some run of `i` is observed as `o`. -/
  runs : Impl → Obs → Prop
  /-- `reads o t`: the observation `o` is read as the trace `t`. -/
  reads : Obs → T → Prop

namespace Platform

variable {T U : Type}

/-- **The HTTP traces of an implementation.** -/
def view (P : Platform T) (i : P.Impl) (t : T) : Prop := ∃ o, P.runs i o ∧ P.reads o t

/-- **Satisfaction**: every trace of `i` satisfies `φ`. -/
def Sat (P : Platform T) (i : P.Impl) (φ : T → Prop) : Prop := ∀ t, P.view i t → φ t

/-- **Refinement across platforms**: every trace of `i` on `P` is a trace of `j` on `Q`. -/
def Refines (P Q : Platform T) (i : P.Impl) (j : Q.Impl) : Prop := ∀ t, P.view i t → Q.view j t

/-- The platform read through a relation between traces (a change of observation). -/
def map (f : T → U → Prop) (P : Platform T) : Platform U where
  Impl := P.Impl
  Obs := P.Obs
  runs := P.runs
  reads o u := ∃ t, P.reads o t ∧ f t u

/-! ## Handlers with instance state -/

/-- A handler with instance state `σ` on one reused instance. -/
def seq (σ : Type) : Platform Log where
  Impl := Origin σ × σ
  Obs := Log
  runs i l := Seq i.1 i.2 l
  reads := Eq

/-- A handler with instance state `σ`, a fresh instance per request. -/
def fresh (σ : Type) : Platform Log where
  Impl := Origin σ × σ
  Obs := Log
  runs i l := Fresh i.1 i.2 l
  reads := Eq

/-- A handler with instance state `σ` under a host that pools instances (`wasi:http`). -/
def host (σ : Type) : Platform Log where
  Impl := Origin σ × σ
  Obs := Log
  runs i l := HostRuns i.1 i.2 l
  reads := Eq

/-- A CGI or WAGI script with its initial files. -/
def cgi (g : Cgi.Gateway) : Platform Log where
  Impl := Spec × Fs
  Obs := Log
  runs i l := Seq (Cgi.origin g i.1) i.2 l
  reads := Eq

/-! ## Linux processes over sockets -/

/-- A connection, by the order in which it was accepted. -/
abbrev ConnId : Type := Nat

/-- **A socket event** of a server process. -/
inductive SockEv where
  /-- A connection was accepted. -/
  | accept (c : ConnId)
  /-- Octets were received on a connection. -/
  | recv (c : ConnId) (bs : List UInt8)
  /-- Octets were sent on a connection. -/
  | send (c : ConnId) (bs : List UInt8)
  /-- The server closed a connection. -/
  | close (c : ConnId)
  deriving DecidableEq, Repr

/-- The octets received on `c`, in order. -/
def received (c : ConnId) : List SockEv → List UInt8
  | [] => []
  | .recv c' bs :: t => (if c' = c then bs else []) ++ received c t
  | _ :: t => received c t

/-- The octets sent on `c`, in order. -/
def sent (c : ConnId) : List SockEv → List UInt8
  | [] => []
  | .send c' bs :: t => (if c' = c then bs else []) ++ sent c t
  | _ :: t => sent c t

/-- **HTTP/1.1 framing of a connection**: the complete requests in the octets received, and
the complete responses (to those requests, in order) in the octets sent. -/
structure Framing where
  requests : List UInt8 → List Request
  responses : List Request → List UInt8 → List Response

/-- The exchanges of each connection. -/
abbrev ConnLog : Type := ConnId → Log

/-- The exchanges of each connection of a socket trace: requests paired with the responses in
order; a request not yet answered is not an exchange. -/
def connLog (fr : Framing) (tr : List SockEv) : ConnLog := fun c =>
  let rs := fr.requests (received c tr)
  rs.zip (fr.responses rs (sent c tr))

/-- The connections a socket trace accepted. -/
def accepted : List SockEv → List ConnId
  | [] => []
  | .accept c :: t => c :: accepted t
  | _ :: t => accepted t

/-- The socket semantics of a server program: the socket traces of its runs when started with
an invocation. -/
abbrev SockSem : Type := Input → List SockEv → Prop

/-- **A Linux process serving HTTP/1.1**: a program and its invocation; observed through its
socket events. -/
def linux (fr : Framing) : Platform (List ConnId × ConnLog) where
  Impl := SockSem × Input
  Obs := List SockEv
  runs i tr := i.1 i.2 tr
  reads tr t := t = (accepted tr, connLog fr tr)

/-! ## Containers -/

/-- An image layer: files set (`some`) or removed (`none`, a whiteout). -/
abbrev Layer : Type := List (FPath × Option (List UInt8))

/-- An image: its layers, the lowest first. -/
abbrev Image : Type := List Layer

/-- The files of an image: each layer applied over the ones below. -/
def Image.fs (img : Image) : Fs :=
  img.foldl (fun fs layer => layer.foldl (fun fs e => fs.set e.1 e.2) fs) Fs.empty

/-- **A container**: an image, an entry point, an environment and the roots it is given. -/
structure Container where
  image : Image
  entry : String
  args : List String := []
  env : List (String × String) := []
  roots : List Root := []

/-- The invocation a container starts its entry point with. -/
def Container.launch (c : Container) : Input :=
  { prog := c.entry, args := c.args, env := c.env, roots := c.roots, fs := c.image.fs }

/-- **A container serving HTTP/1.1**: a program run as the container's entry point. -/
def container (fr : Framing) : Platform (List ConnId × ConnLog) where
  Impl := SockSem × Container
  Obs := List SockEv
  runs i tr := i.1 i.2.launch tr
  reads tr t := t = (accepted tr, connLog fr tr)

/-! ## Comparing per-connection and sequential traces -/

/-- **`Merge ls l`**: `l` interleaves the logs `ls`, each kept in order. -/
inductive Merge : List Log → Log → Prop where
  | nil : Merge [] []
  | cons {l : Log} {ls : List Log} {m out : Log} :
      Merge ls m → Interleave l m out → Merge (l :: ls) out

/-- The sequential logs of a per-connection trace: the merges of its connections' logs. -/
def toLogs (t : List ConnId × ConnLog) (l : Log) : Prop := Merge (t.1.map t.2) l

end Platform

end Silmaril.Servers
