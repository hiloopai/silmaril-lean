module

public import Silmaril.Servers.Platform.Defs

/-!
# Core traces read from the timing of socket events

`Platform.connModel` reads a socket trace through its per-connection logs: it fixes the order of
the exchanges on each connection and nothing else, so every interleaving across connections
that well-formedness allows is a trace of the model. The socket trace says more: each event
happens at a point of it. `timed fr tr` reads the core trace those points give:

* a request is **received** at the socket event that completes it: the first prefix of the
  trace whose octets on its connection frame it (`fr.requests`);
* a response is **sent** at the socket event that completes it, or, if the server sent it
  before its request was complete, at the event that completes the request (an exchange is a
  request paired with its response, `Platform.connLog`).

At each socket event the newly complete requests and exchanges of its connection are read
(`stepEvs`), receptions before sendings; the `k`-th request of connection `c` has the identity
`⟨c, k⟩`, as in `connModel`. The order across connections is the order of the socket events.

For this reading to be well defined the framing must not take back what it has read
(`Mono`): reading more octets extends the requests and exchanges read so far. The theorems
(`Thms`) show that, for such a framing, the receptions of each connection in `timed fr tr` are
its requests in order and its sendings are the responses of its exchanges in order: the timed
trace contains exactly the per-connection logs, now with a cross-connection order. That the
HTTP/1.1 framing `Wire1.framing` is monotone is the open `Task.wire1Mono`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Timed

open Silmaril.Servers.Platform

/-- The connection a socket event concerns. -/
def connOfEv : SockEv → ConnId
  | .accept c | .recv c _ | .send c _ | .close c => c

/-- **A monotone framing**: more octets never take back requests or exchanges already read. -/
def Mono (fr : Framing) : Prop :=
  fr.requests [] = [] ∧ (∀ a b, fr.requests a <+: fr.requests (a ++ b)) ∧
    ∀ a a' b b', (fr.requests a).zip (fr.responses (fr.requests a) b) <+:
      (fr.requests (a ++ a')).zip (fr.responses (fr.requests (a ++ a')) (b ++ b'))

/-- The requests of connection `c` complete in `cur` and not in `pre`. -/
def newRecvs (fr : Framing) (c : ConnId) (pre cur : List SockEv) : Trace Http.sig :=
  (((fr.requests (received c cur)).zipIdx).drop (fr.requests (received c pre)).length).map
    fun p => .recv ⟨c, p.2⟩ p.1

/-- The exchanges of connection `c` complete in `cur` and not in `pre`: their responses. -/
def newSends (fr : Framing) (c : ConnId) (pre cur : List SockEv) : Trace Http.sig :=
  (((connLog fr cur c).zipIdx).drop (connLog fr pre c).length).map
    fun p => .send ⟨c, p.2⟩ p.1.2

/-- What the socket event `e` after the prefix `pre` completes. -/
def stepEvs (fr : Framing) (pre : List SockEv) (e : SockEv) : Trace Http.sig :=
  newRecvs fr (connOfEv e) pre (pre ++ [e]) ++ newSends fr (connOfEv e) pre (pre ++ [e])

/-- The timed reading of the rest of a trace after the prefix `pre`. -/
def timedAux (fr : Framing) : List SockEv → List SockEv → Trace Http.sig
  | _, [] => []
  | pre, e :: rest => stepEvs fr pre e ++ timedAux fr (pre ++ [e]) rest

/-- **The core trace of a socket trace, by the timing of its events.** -/
def timed (fr : Framing) (tr : List SockEv) : Trace Http.sig := timedAux fr [] tr

/-- The receptions on connection `c` of a core trace, with their identities. -/
def recvsOn (c : ConnId) (t : Trace Http.sig) : List (ReqId × Net.Http.Request) :=
  t.filterMap fun
    | .recv i r => if i.conn = c then some (i, r) else none
    | .send _ _ => none

/-- The sendings on connection `c` of a core trace, with their identities. -/
def sendsOn (c : ConnId) (t : Trace Http.sig) : List (ReqId × Net.Http.Response) :=
  t.filterMap fun
    | .send i s => if i.conn = c then some (i, s) else none
    | .recv _ _ => none

/-- **The core model of a socket semantics read by timing.** -/
def timedModel (L : SockSem) (inp : Cli.Input) (fr : Framing) : Model Http.sig :=
  ⟨fun t => ∃ tr, L inp tr ∧ t = timed fr tr⟩

end Silmaril.Servers.Timed
