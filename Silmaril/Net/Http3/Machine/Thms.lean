module

public import Silmaril.Net.Http3.Machine.Defs
public import Silmaril.Automata.Shapes.Thms
import Silmaril.Proofs.Net.Http3.Machine

@[expose] public section

/-!
# HTTP/3 stream machines: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Http3/Machine.lean`):

* `requestMachine_step`: the finite request machine is exactly the reader's phase transition:
  `reqStep` succeeds iff the machine has the edge, and lands in the machine's target phase;
* `controlStep_machine`: every frame the control-stream reader accepts is an edge of the
  finite control machine (the machine over-approximates the value checks on GOAWAY and
  MAX_PUSH_ID).

DECIDED by the verified procedures of `Silmaril.Automata.Decide` (kernel-checked `decide`), RFC 9114 §4.1 and §6.2.1:

* `request_done_reachable`, `request_done_final`: a request stream can reach the end of its
  trailer section, and after it only `done` is reachable;
* `request_needs_final_headers`: without a final HEADERS frame a request stream never leaves
  `awaitHeaders` — no DATA before the header section;
* `request_no_promise`, `push_no_promise`: PUSH_PROMISE is never an edge on requests read by
  servers or on push streams;
* `control_needs_settings`: without a SETTINGS frame a control stream never becomes ready;
  `control_ready_final`: once ready it never returns to `awaitSettings`.
-/

namespace Silmaril.Net.Http3

open Silmaril.Automata.Shapes

theorem requestMachine_step (k : StreamKind) (interim : List UInt8 → Bool) (s : ReqState)
    (f : Frame) :
    (reqStep k interim s f).toOption.map ReqState.phase =
      (requestMachine k).step s.phase (f.kind k interim) :=
  Silmaril.Proofs.Net.Http3.Machine.requestMachine_step k interim s f

theorem controlStep_machine {peer : Role} {s s' : ControlState} {f : Frame}
    (h : controlStep peer s f = .ok s') :
    (controlMachine peer).step s.phase f.controlKind = some s'.phase :=
  Silmaril.Proofs.Net.Http3.Machine.controlStep_machine h

theorem request_done_reachable :
    Reach (requestMachine .request) (fun _ => true) .awaitHeaders .done := by decide

theorem request_done_final :
    ∀ p, Reach (requestMachine .request) (fun _ => true) .done p → p = .done := by decide

theorem request_needs_final_headers :
    ¬ Reach (requestMachine .request) (· != .headersFinal) .awaitHeaders .body := by decide

theorem request_no_promise :
    ∀ p, (requestMachine .request).step p .pushPromise = none := by decide

theorem push_no_promise : ∀ p, (requestMachine .push).step p .pushPromise = none := by decide

theorem control_needs_settings (peer : Role) :
    ¬ Reach (controlMachine peer) (· != .settings) .awaitSettings .ready := by
  cases peer <;> decide

theorem control_ready_final (peer : Role) :
    ¬ Reach (controlMachine peer) (fun _ => true) .ready .awaitSettings := by
  cases peer <;> decide

end Silmaril.Net.Http3
