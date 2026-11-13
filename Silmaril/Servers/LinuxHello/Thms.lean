module

public import Silmaril.Servers.LinuxHello.Defs
public import Silmaril.Servers.Compare.Thms
public import Silmaril.Process.LPS.Table
import Silmaril.Proofs.Servers.LinuxHello.Serves
import Silmaril.Proofs.Servers.LinuxHello.Table

/-!
# A Linux hello server loop over LPS's socket system calls: theorems

PROVED (standard axioms):

* `serverSpec_iff`, **`L_eq_full`**: the loop's four arms are those of LPS's generic table,
  and the loop traps only with their numbers, so its socket semantics under `serverSpec` is its
  socket semantics under LPS's whole table `syscallSpec`.
* **`serves`**: `Compare.ServesHello L inp` for every invocation. For every sequence of
  requests on the wire (`Compare.WireOk`), the network whose first client sends them back to
  back and then `FIN` gives a run that accepts that one connection (on channel `3`, from
  `accept4Spec`), reads all the octets (in `read`s of at most 4096, LPS's socket `read`), and
  sends `helloWire` once per request (in `sendto`s of at most 4096 with `MSG_NOSIGNAL`). The
  octets come off the run's raw history (`Sockets.ofRecordsC`).
* **`wasi_refines_loop`**: so, on logs whose requests are on the wire, the `wasi:http` hello
  component refines this process: every such log of the component is the merged connection
  log of a run of the loop under LPS's semantics.

OPEN: `Compare.OnlyHello L inp`, the converse direction (every exchange of every run answered
`helloResp`). It needs an invariant over all runs (every outcome LPS allows: failed accepts,
short reads and sends, resets) and the fact that no strict prefix of `helloWire`'s octets
frames as a response; neither is done.
-/

@[expose] public section

namespace Silmaril.Servers.LinuxHello

open Silmaril.Process Silmaril.Process.LPS Silmaril.Servers.Platform Silmaril.Servers.Compare

theorem serverSpec_iff (i : SyscallInput) (m : LPS.Model) (o : Outcome SyscallEffect)
    (h : i.sysno.toNat = 202 ∨ i.sysno.toNat = 63 ∨ i.sysno.toNat = 206 ∨ i.sysno.toNat = 57) :
    serverSpec i m o ↔ syscallSpec i m o :=
  Proofs.Servers.LinuxHello.serverSpec_iff i m o h

/-- **The loop's socket semantics is the same under LPS's whole table.** -/
theorem L_eq_full :
    L = Sockets.sockSemNet launch [] syscallSpec noFilter Sockets.genericAccept
      Sockets.genericClose := by
  funext inp tr
  simp only [L, Sockets.sockSemNet, Proofs.Servers.LinuxHello.hstar_iff]

/-- **The loop serves hello on one connection**, for every invocation. -/
theorem serves (inp : Cli.Input) : ServesHello L inp :=
  Proofs.Servers.LinuxHello.serves inp

/-- **The hello component refines the loop** on logs on the wire. -/
theorem wasi_refines_loop (inp : Cli.Input) :
    Refines (restrict wasi wireLog) linux1 WasiExamples.hello (L, inp) :=
  wasi_refines_linux (serves inp)

end Silmaril.Servers.LinuxHello
