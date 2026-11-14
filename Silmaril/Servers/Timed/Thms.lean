module

public import Silmaril.Servers.Timed.Defs
public import Silmaril.Servers.Wire1.Defs
import Silmaril.Proofs.Servers.Timed.Basic

/-!
# Core traces read from the timing of socket events: theorems

PROVED (standard axioms), for a monotone framing (`Mono`):

* **`recvsOn_timed`**: the receptions of connection `c` in `timed fr tr` are its requests
  (`fr.requests (received c tr)`) in order, the `k`-th with identity `⟨c, k⟩`;
* **`sendsOn_timed`**: the sendings of connection `c` are the responses of its exchanges
  (`connLog fr tr c`) in order, the `k`-th with identity `⟨c, k⟩`.

So the timed trace holds exactly the per-connection logs `Platform.connModel` reads, each
exchange once, and adds what `connModel` leaves open: the order across connections, and of a
request against the responses before it, is the order of the socket events that complete
them.

OPEN (frozen): `Task.wire1Mono`, that `Wire1.framing` is monotone (more octets never take back
a request or a response read): a complete message reads the same followed by anything. The
head grammars are sound and complete (`Grammar.Lawful`), so the head half is a short argument;
the chunked body parser needs the same.
-/

@[expose] public section

namespace Silmaril.Servers.Timed

open Silmaril.Servers.Platform

/-- **The receptions of a connection in the timed trace are its requests, in order.** -/
theorem recvsOn_timed {fr : Framing} (hm : Mono fr) (c : ConnId) (tr : List SockEv) :
    recvsOn c (timed fr tr) =
      ((fr.requests (received c tr)).zipIdx).map fun p => ((⟨c, p.2⟩ : ReqId), p.1) := by
  have := Proofs.Servers.Timed.recvsOn_timedAux hm c tr []
  simpa [timed, received, hm.1] using this

/-- **The sendings of a connection in the timed trace are the responses of its exchanges, in
order.** -/
theorem sendsOn_timed {fr : Framing} (hm : Mono fr) (c : ConnId) (tr : List SockEv) :
    sendsOn c (timed fr tr) =
      ((connLog fr tr c).zipIdx).map fun p => ((⟨c, p.2⟩ : ReqId), p.1.2) := by
  have := Proofs.Servers.Timed.sendsOn_timedAux hm c tr []
  simpa [timed, connLog, received, sent, hm.1] using this

/-- Socket refinement gives refinement of the timed models. -/
theorem timedModel_mono {L L' : SockSem} {inp inp' : Cli.Input} (fr : Framing)
    (h : ∀ tr, L inp tr → L' inp' tr) : (timedModel L inp fr).Refines (timedModel L' inp' fr) :=
  fun _ ⟨tr, ht, e⟩ => ⟨tr, h tr ht, e⟩

end Silmaril.Servers.Timed

namespace Silmaril.Servers.Timed.Task

/-- **Open**: the HTTP/1.1 framing is monotone. -/
def wire1Mono : Prop := Mono Wire1.framing

end Silmaril.Servers.Timed.Task
