module

public import Silmaril.Formats.Parquet.Date.Leaf.Defs
public import Silmaril.Formats.Parquet.Date.Events.ToIpc.Defs

/-! # Footer-ordered DATE events and native IPC from one selected leaf -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Events

open Silmaril.Relational

inductive Error where
  | openFailure (cause : Leaf.Error)
  | groupFailure (index : Nat) (cause : Leaf.Error)
  deriving DecidableEq, Repr

def schema (bound : Bound) : Scan.Schema String Date.Events.Kind :=
  ⟨1, fun _ => (bound.binding.leaf.name, .date32 bound.nullable)⟩

def rows (bound : Bound) (slots : Slots) : Reader.RowGroup (schema bound) Date.Events.Cell :=
  slots.map fun slot _ => slot

def rowsAtWith {ε δ : Type} (bound : Bound) (read : Nat → Except ε Slots)
    (tag : Nat → ε → δ) (index : Nat) :
    Except δ (Reader.RowGroup (schema bound) Date.Events.Cell) :=
  ((read index).map (rows bound)).mapError (tag index)

def rowsAt (limits : Date.Limits) (bound : Bound) (index : Nat) :
    Except Error (Reader.RowGroup (schema bound) Date.Events.Cell) :=
  rowsAtWith bound (readGroup limits bound) .groupFailure index

def source (limits : Date.Limits) (bound : Bound) :
    Reader.Source Nat (schema bound) Date.Events.Cell Error :=
  ⟨List.range bound.snapshot.groupCount, rowsAt limits bound, fun _ => .ok ()⟩

def openSource (limits : Date.Limits) (ordinal : Nat) (input : Bytes) :
    Reader.OpenResult Nat String Date.Events.Cell Error :=
  ((openLeaf limits.snapshot input ordinal).mapError .openFailure).map fun bound =>
    ⟨schema bound, source limits bound⟩

def readAll (limits : Date.Limits) (ordinal : Nat) (input : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  Reader.readAll (openSource limits ordinal input)

/-- Denote the original footer order with the supplied selected-leaf decoder. -/
def traceWith {ε δ : Type} (bound : Bound) (read : Nat → Except ε Slots)
    (tag : Nat → ε → δ) : Arrow.Events.Trace (schema bound) Date.Events.Cell δ :=
  let groups := Reader.denoteGroups (rowsAtWith bound read tag) (List.range bound.snapshot.groupCount)
  ⟨groups.1.map AlignedColumns.ofRows, groups.2⟩

def trace (limits : Date.Limits) (bound : Bound) :
    Arrow.Events.Trace (schema bound) Date.Events.Cell Error :=
  traceWith bound (readGroup limits bound) .groupFailure

inductive IpcError where
  | source (cause : Error)
  | closed
  | writer (cause : Arrow.DateStream.Writer.Error)
  deriving DecidableEq, Repr

/-- Read the selected leaf through EOF before emitting the original group cuts. -/
def emitWith {ε δ : Type} (output : Arrow.ObservationLimits) (bound : Bound)
    (sourceError : ε → δ) (closed : δ) (writerError : Arrow.DateStream.Writer.Error → δ)
    (events : Arrow.Events.Trace (schema bound) Date.Events.Cell ε) :
    Except δ KBytes :=
  match events.termination with
  | .readError cause | .closeError cause => .error (sourceError cause)
  | .closed => .error closed
  | .eos =>
    let batches := events.batches.map fun batch => batch.values ⟨0, Nat.zero_lt_succ 0⟩
    (Arrow.DateStream.Writer.emit output bound.binding.leaf.name bound.nullable batches).mapError
      writerError

def emit (output : Arrow.ObservationLimits) (bound : Bound)
    (events : Arrow.Events.Trace (schema bound) Date.Events.Cell Error) :
    Except IpcError KBytes :=
  emitWith output bound .source .closed .writer events

/-- Open and read the strict selected-leaf source, returning complete native IPC on success. -/
def toIpc (limits : Date.Limits) (output : Arrow.ObservationLimits) (ordinal : Nat)
    (input : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf limits.snapshot input ordinal).mapError (.source ∘ .openFailure)
  emit output bound (trace limits bound)

end Silmaril.Formats.Parquet.Date.Leaf.Events
