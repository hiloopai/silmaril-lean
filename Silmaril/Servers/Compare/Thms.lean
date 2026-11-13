module

public import Silmaril.Servers.Compare.Defs
public import Silmaril.Servers.Platform.Thms
import Silmaril.Proofs.Servers.Compare.Hello

/-!
# Comparing a `wasi:http` component with a Linux process: hello

PROVED (standard axioms):

* `toResponse_helloWire`, `helloWire_ok`: `helloWire` reads as `helloResp`, and reads back
  after any request whose method is neither `HEAD` nor `CONNECT`.
* `wasi_hello_iff`: the logs of the hello component are exactly the logs answering every
  request `helloResp`.
* **`wasi_refines_linux`**: on logs whose requests are on the wire, the hello component
  refines every Linux process that serves hello on one connection (`ServesHello`): each such
  log is the merged log of a run of the process, its octets framed by HTTP/1.1. End to end:
  the component's `wasi:http` calls (`Silmaril.Servers.WasiHttp`), the HTTP/1.1 round trips
  (`Silmaril.Servers.Wire1`) and the socket reading of the process (`Platform.linux`).
* **`linux_refines_wasi`**: every Linux process that only says hello (`OnlyHello`) refines
  the hello component, on all logs.
* `hello_equiv`: both, so on logs on the wire the two are equivalent.
* `wasi_refines_linux_model`: the first, as refinement in the server institution.
* `helloSock_serves`, `helloSock_only`, **`hello_equiv_helloSock`**: the reference hello
  server at the socket level satisfies both hypotheses, so it and the component are
  equivalent on logs on the wire.

ASSUMED: the Linux side is the hypothesis `ServesHello` / `OnlyHello` about the program's
socket semantics (`Platform.SockSem`); no Linux binary is proved to satisfy it here. A binary
would discharge it through `Silmaril.Servers.Sockets.sockSem` and the process model.
-/

@[expose] public section

namespace Silmaril.Servers.Compare

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Servers.Platform Silmaril.Servers.Wire1 Silmaril.Servers.Reuse
open Silmaril.Net.Http (Request Response)
open Silmaril.Cli (Input)

theorem toResponse_helloWire : toResponse helloWire = helloResp :=
  Proofs.Servers.Compare.toResponse_helloWire

theorem helloWire_ok {meth : List UInt8} (h1 : meth ≠ Net.Http1.methodHEAD)
    (h2 : meth ≠ Net.Http1.methodCONNECT) : RespOk meth helloWire :=
  Proofs.Servers.Compare.helloWire_ok h1 h2

/-- The logs of the hello component answer every request `helloResp`. -/
theorem wasi_hello_iff (l : Log) : wasi.view hello l ↔ ∀ p ∈ l, p.2 = helloResp :=
  Proofs.Servers.Compare.wasi_hello_iff l

/-- **The hello component refines a Linux hello server**, on logs on the wire. -/
theorem wasi_refines_linux {L : SockSem} {inp : Input} (hL : ServesHello L inp) :
    Refines (restrict wasi wireLog) linux1 hello (L, inp) :=
  Proofs.Servers.Compare.wasi_refines_linux hL

/-- **A Linux server that only says hello refines the hello component.** -/
theorem linux_refines_wasi {L : SockSem} {inp : Input} (hL : OnlyHello L inp) :
    Refines linux1 wasi (L, inp) hello :=
  Proofs.Servers.Compare.linux_refines_wasi hL

/-- Restricting both platforms to the same traces preserves refinement. -/
theorem refines_restrict {T : Type} {P Q : Platform T} {i : P.Impl} {j : Q.Impl}
    (D : T → Prop) (h : Refines P Q i j) : Refines (restrict P D) (restrict Q D) i j :=
  fun t ⟨o, ho, hr, hd⟩ => let ⟨o', ho', hr'⟩ := h t ⟨o, ho, hr⟩; ⟨o', ho', hr', hd⟩

/-- **On logs on the wire, the hello component and a Linux hello server are equivalent.** -/
theorem hello_equiv {L : SockSem} {inp : Input} (h₁ : ServesHello L inp)
    (h₂ : OnlyHello L inp) :
    Refines (restrict wasi wireLog) (restrict linux1 wireLog) hello (L, inp) ∧
      Refines (restrict linux1 wireLog) (restrict wasi wireLog) (L, inp) hello :=
  ⟨fun t ht =>
      let ⟨_, _, _, hd⟩ := ht
      let ⟨o', ho', hr'⟩ := wasi_refines_linux h₁ t ht
      ⟨o', ho', hr', hd⟩,
    refines_restrict wireLog (linux_refines_wasi h₂)⟩

/-- The hello comparison in the server institution: the core model of the component, on logs
on the wire, refines that of the Linux server. -/
theorem wasi_refines_linux_model {L : SockSem} {inp : Input} (hL : ServesHello L inp) :
    (model (restrict wasi wireLog) hello).Refines (model linux1 (L, inp)) :=
  (refines_iff_model (P := restrict wasi wireLog) (Q := linux1) hello (L, inp)).1
    (wasi_refines_linux hL)

/-- The reference Linux hello server serves hello on one connection. -/
theorem helloSock_serves (inp : Input) : ServesHello helloSock inp :=
  Proofs.Servers.Compare.helloSock_serves inp

/-- The reference Linux hello server only says hello. -/
theorem helloSock_only (inp : Input) : OnlyHello helloSock inp :=
  Proofs.Servers.Compare.helloSock_only inp

/-- **The hello component and the reference Linux hello server are equivalent** on logs on
the wire, for every invocation. -/
theorem hello_equiv_helloSock (inp : Input) :
    Refines (restrict wasi wireLog) (restrict linux1 wireLog) hello (helloSock, inp) ∧
      Refines (restrict linux1 wireLog) (restrict wasi wireLog) (helloSock, inp) hello :=
  hello_equiv (helloSock_serves inp) (helloSock_only inp)

end Silmaril.Servers.Compare
