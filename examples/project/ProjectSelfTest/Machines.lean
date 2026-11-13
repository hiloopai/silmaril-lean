module

public import Silmaril.Automata.Registry.Defs
public import Silmaril.Automata.Shapes.Thms
public import Silmaril.Net.Http2.Stream.Thms

/-!
# The `sil project` self-test: machines

The machine documents of `silmaril/machines/` and their bindings:

* `silmaril.net.http2.stream`: the HTTP/2 stream machine (RFC 9113 §5.1), bound to
  `Silmaril.Net.Http2.machine` and its marks;
* `silmaril.selftest.door`: a small document bound to **two** typed machines over different
  inductive types (`Door` and `DoorAlt`, whose constructors are declared in other orders), so
  one document carries several attachments and `step_iff_of_canon_eq` relates them.

Each binding is the theorem `<binding>.bound` (and `<binding>.layers` for marks), checked by
the kernel when this module is built.
-/

namespace ProjectSelfTest.Machines

@[expose] public section

open Silmaril.Automata

namespace Door

inductive St where | closed | locked | «open» deriving DecidableEq, Repr
silmaril_finite St

inductive Lb where | «open» | close | lock | unlock deriving DecidableEq, Repr
silmaril_finite Lb

def machine : DMachine St Lb := ⟨fun s l => match s, l with
  | .closed, .open => some .open
  | .closed, .lock => some .locked
  | .open, .close => some .closed
  | .locked, .unlock => some .closed
  | _, _ => none⟩

def marks : Marks St where
  initial s := s == .closed
  accepting s := s == .closed || s == .locked

end Door

namespace DoorAlt

inductive Lb where | lock | unlock | «open» | close deriving DecidableEq, Repr
silmaril_finite Lb

inductive St where | «open» | closed | locked deriving DecidableEq, Repr
silmaril_finite St

def machine : DMachine St Lb := ⟨fun s l => match s, l with
  | .closed, .open => some .open
  | .closed, .lock => some .locked
  | .open, .close => some .closed
  | .locked, .unlock => some .closed
  | _, _ => none⟩

end DoorAlt

end

end ProjectSelfTest.Machines

silmaril load "silmaril/machines/door.toml"
silmaril load "silmaril/machines/http2-stream.toml"

namespace ProjectSelfTest.Machines

open Silmaril.Automata Silmaril.Automata.Shapes

/-- The two door machines agree step by step on corresponding names (from their bindings). -/
public theorem door_steps_agree {s : Door.St} {l : Door.Lb} {s' : Door.St} {t : DoorAlt.St}
    {k : DoorAlt.Lb} {t' : DoorAlt.St} (hs : FinNamed.name s = FinNamed.name t)
    (hl : FinNamed.name l = FinNamed.name k) (hs' : FinNamed.name s' = FinNamed.name t') :
    Door.machine.step s l = some s' ↔ DoorAlt.machine.step t k = some t' :=
  step_iff_of_canon_eq Door.machine DoorAlt.machine
    (silmaril.selftest.door.typed.bound.trans silmaril.selftest.door.typed_alt.bound.symm) hs hl hs'

/-- A JSON problem answered on the typed side: in the HTTP/2 stream document, `closed` is
reachable from `idle`. -/
public theorem http2_json_closed_reachable :
    JsonReach silmaril.net.http2.stream
      (((FinNamed.elems (α := Silmaril.Net.Http2.Event)).filter fun _ => true).map FinNamed.name)
      "idle" "closed" :=
  (jsonReach_iff_of_bound Silmaril.Net.Http2.machine _ silmaril.net.http2.stream.typed.bound
    (fun _ => true) .idle .closed).mp (by decide)

end ProjectSelfTest.Machines

namespace ProjectSelfTest.Machines

/-- Every event. -/
public def anyEvent : Silmaril.Net.Http2.Event → Bool := fun _ => true

end ProjectSelfTest.Machines

/-! Rows of the machine shapes, decided by the verified procedures. -/

silmaril instance silmaril.net.http2.stream.closes
    (title := "An HTTP/2 stream can go from idle to closed") :=
  silmaril.shapes.machine.reach (M := Silmaril.Net.Http2.machine)
    (P := ProjectSelfTest.Machines.anyEvent) (a := Silmaril.Net.Http2.StreamState.idle)
    (b := Silmaril.Net.Http2.StreamState.closed)
@[answers "silmaril.net.http2.stream.closes" thm] public theorem http2_closes :
    silmaril.net.http2.stream.closes := by
  unfold silmaril.net.http2.stream.closes; decide

silmaril instance silmaril.net.http2.stream.quiet_closes
    (title := "Without END_STREAM or RST_STREAM an HTTP/2 stream closes") :=
  silmaril.shapes.machine.reach (M := Silmaril.Net.Http2.machine)
    (P := Silmaril.Net.Http2.quiet) (a := Silmaril.Net.Http2.StreamState.idle)
    (b := Silmaril.Net.Http2.StreamState.closed)
@[answers "silmaril.net.http2.stream.quiet_closes" uns] public theorem http2_quiet :
    ¬ silmaril.net.http2.stream.quiet_closes := by
  unfold silmaril.net.http2.stream.quiet_closes; decide

silmaril instance silmaril.selftest.door.closed_locked_bisimilar
    (title := "A closed and a locked door are bisimilar") :=
  silmaril.shapes.machine.bisimilar (M := ProjectSelfTest.Machines.Door.machine)
    (N := ProjectSelfTest.Machines.Door.machine)
    (s := ProjectSelfTest.Machines.Door.St.closed) (t := ProjectSelfTest.Machines.Door.St.locked)
@[answers "silmaril.selftest.door.closed_locked_bisimilar" uns] public theorem door_nb :
    ¬ silmaril.selftest.door.closed_locked_bisimilar := by
  unfold silmaril.selftest.door.closed_locked_bisimilar; decide
