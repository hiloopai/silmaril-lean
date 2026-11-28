module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Defs

/-! Emit strict native IPC from a complete recursive Arrow event trace. -/

namespace Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc

@[expose] public section

abbrev Input (Failure : Type) := Arrow.Events.EventStream (Option String) Value Failure

inductive Error (Failure : Type) where
  | openError (cause : Failure)
  | readError (cause : Failure) (completed : List Batch.Rows.Observation)
  | closeError (cause : Failure) (completed : List Batch.Rows.Observation)
  | closed (completed : List Batch.Rows.Observation)
  | writer (cause : Stream.Writer.Error)
  deriving Repr

def schemaOf (source : Signature) : Schema := ⟨(declarations source).map Prod.snd⟩

/-- Writer admission follows the source terminal check. Refusals carry
logical batches or the original writer cause, without an IPC result. -/
def emit {Failure : Type} (limits : Batch.Limits) (input : Input Failure) :
    Except (Error Failure) KBytes :=
  match input with
  | .error cause => .error (.openError cause)
  | .ok ⟨source, trace⟩ =>
    let groups := trace.batches.map eraseBatch
    match trace.termination with
    | .readError cause => .error (.readError cause groups)
    | .closeError cause => .error (.closeError cause groups)
    | .closed => .error (.closed groups)
    | .eos => (Stream.Writer.emit limits (schemaOf source) groups).mapError .writer

end

end Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc
