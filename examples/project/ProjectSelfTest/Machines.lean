module

public import Silmaril.Automata.Registry.Defs
public import Silmaril.Automata.Shapes.Thms
public import Silmaril.Net.Http2.Stream.Thms

/-!
# The `sil project` self-test: machines

The machine documents of `silmaril/machines/` and their bindings:

* `silmaril.net.http2.stream`: the HTTP/2 stream machine (RFC 9113 §5.1), bound to
  `Silmaril.Net.Http2.machine` and its marks;
* `silmaril.selftest.coin`: a nondeterministic document bound to a typed `NMachine`;
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

namespace Door

/-- The door with its marks. -/
def marked : Marked St Lb := ⟨machine, marks⟩

/-- Open, close, lock. -/
def word : List Lb := [.open, .close, .lock]

/-- The same word, by name. -/
def wordNames : List String := ["open", "close", "lock"]

end Door

namespace Coin

inductive Side where | heads | tails deriving DecidableEq, Repr
silmaril_finite Side

inductive Act where | toss deriving DecidableEq, Repr
silmaril_finite Act

/-- Tossing lands on either side: a nondeterministic machine. -/
def machine : NMachine Side Act := ⟨fun _ _ => {.heads, .tails}⟩

end Coin

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

/-- The name `heads`. -/
public def headsName : String := "heads"

/-- The name `tails`. -/
public def tailsName : String := "tails"

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

silmaril instance silmaril.selftest.door.closed_bisimilar
    (title := "A closed door is bisimilar to itself (the greatest bisimulation, decided)") :=
  silmaril.shapes.machine.bisimilar (M := ProjectSelfTest.Machines.Door.machine)
    (N := ProjectSelfTest.Machines.Door.machine)
    (s := ProjectSelfTest.Machines.Door.St.closed) (t := ProjectSelfTest.Machines.Door.St.closed)
@[answers "silmaril.selftest.door.closed_bisimilar" thm] public theorem door_bisim :
    silmaril.selftest.door.closed_bisimilar := by
  unfold silmaril.selftest.door.closed_bisimilar; decide

/-- Negative facts stay theorems, not failing rows: a quiet HTTP/2 stream never closes, and a
closed and a locked door are not bisimilar. -/
public theorem ProjectSelfTest.Machines.http2_quiet : ¬ Silmaril.Automata.Shapes.Reach Silmaril.Net.Http2.machine
    Silmaril.Net.Http2.quiet .idle .closed := by decide

public theorem ProjectSelfTest.Machines.door_not_bisim : ¬ Silmaril.Automata.Shapes.Bisimilar ProjectSelfTest.Machines.Door.machine
    ProjectSelfTest.Machines.Door.machine
    .closed .locked := by decide

silmaril instance silmaril.selftest.door.accepts_word
    (title := "The door accepts open, close, lock") :=
  silmaril.shapes.machine.accepts (M := ProjectSelfTest.Machines.Door.marked)
    (w := ProjectSelfTest.Machines.Door.word)
@[answers "silmaril.selftest.door.accepts_word" thm] public theorem door_accepts :
    silmaril.selftest.door.accepts_word := by
  unfold silmaril.selftest.door.accepts_word; decide

silmaril instance silmaril.selftest.door.nonempty
    (title := "The door accepts some word") :=
  silmaril.shapes.machine.nonempty (M := ProjectSelfTest.Machines.Door.marked)
@[answers "silmaril.selftest.door.nonempty" thm] public theorem door_nonempty :
    silmaril.selftest.door.nonempty := by
  unfold silmaril.selftest.door.nonempty; decide

silmaril instance silmaril.selftest.door.json_accepts
    (title := "The door document accepts open, close, lock (on names, without a typed machine)") :=
  silmaril.shapes.machine.json.accepts (d := silmaril.selftest.door)
    (w := ProjectSelfTest.Machines.Door.wordNames)
@[answers "silmaril.selftest.door.json_accepts" thm] public theorem door_json_accepts :
    silmaril.selftest.door.json_accepts := by
  unfold silmaril.selftest.door.json_accepts; decide +kernel

silmaril instance silmaril.selftest.coin.json_simulates
    (title := "In the coin document, tails simulates heads (on names)") :=
  silmaril.shapes.machine.json.simulates (d := silmaril.selftest.coin) (e := silmaril.selftest.coin)
    (a := ProjectSelfTest.Machines.headsName) (b := ProjectSelfTest.Machines.tailsName)
@[answers "silmaril.selftest.coin.json_simulates" thm] public theorem coin_sim :
    silmaril.selftest.coin.json_simulates := by
  unfold silmaril.selftest.coin.json_simulates; decide +kernel
