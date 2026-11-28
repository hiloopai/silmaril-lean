module

public import Silmaril.Logic.ACL2.X86Run.Status.Source
public import Silmaril.Logic.ACL2.X86Run.Standard.Thms

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status

open Standard

/-- The native logical encoding has a NIL bad tail on a nonempty accepted entry list. -/
theorem logicalStateP_of_entries (p : RecordPrimitives) {entries : Object}
    (h : p.entriesP entries = true) (hne : entries ≠ .nil) :
    logicalStateP p (.cons entries .nil) = true := by
  simp only [Object.nil] at hne
  simp [logicalStateP, toRecord, recordP, Object.nil, Object.cdr, h, hne]

/-- On a nonempty accepted entry list, read the good part of the native encoding. -/
theorem Accessor.read_of_entries (a : Accessor) (p : RecordPrimitives) {entries : Object}
    (h : p.entriesP entries = true) (hne : entries ≠ .nil) :
    a.read p (.cons entries .nil) = readEntries p a.key a.fallback entries := by
  simp only [Object.nil] at hne
  simp [Accessor.read, toRecord, recordP, Object.nil, Object.car, h, hne]

theorem Accessor.read_atom (a : Accessor) (p : RecordPrimitives) {state : Object}
    (h : state.consp = false) : a.read p state = a.fallback := by
  cases state <;> simp_all [Object.consp, Accessor.read, toRecord, recordP,
    Object.car, readEntries, Object.nil]

/-- Bind the two status readers in the generated standard-object X86-RUN model.
The record primitives and the logical step remain parameters. -/
def machineBindings (p : RecordPrimitives) (step : Object → Object) : MachineBindings :=
  ⟨fault.read p, ms.read p, step⟩

theorem fault_exit (p : RecordPrimitives) (step : Object → Object) (n state : Object)
    (h : fault.read p state ≠ .nil) : (machineBindings p step).run n state = state :=
  (machineBindings p step).fault_exit n state h

theorem ms_exit (p : RecordPrimitives) (step : Object → Object) (n state : Object)
    (hf : fault.read p state = .nil) (hm : ms.read p state ≠ .nil) :
    (machineBindings p step).run n state = state :=
  (machineBindings p step).ms_exit n state hf hm

theorem halted_holds (p : RecordPrimitives) (step : Object → Object) :
    halted.Holds (machineBindings p step).admittedModel :=
  (machineBindings p step).halted_holds

end Silmaril.Logic.ACL2.X86Run.Status
