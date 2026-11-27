module

public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Defs

/-! Exact Arrow TIMESTAMP seconds to the canonical Parquet millis writer. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds

open Silmaril.Numeric.Timestamp (ConversionError Kind Ticks)

inductive Error where
  | inputByteLimit
  | source (cause : Arrow.TimestampStream.Error)
  | expectedSeconds
  | metadata (cause : FromIpc.Error)
  | rescale (batch slot : Nat) (cause : ConversionError)
  | sink (cause : FromIpc.Error)
  deriving DecidableEq, Repr

/-- Preserve the exact original name, optionality and timezone option. -/
def millisecondBinding (binding : Arrow.TimestampBatch.Binding) : Arrow.TimestampBatch.Binding :=
  { binding with metadata := ⟨.millisecond, binding.metadata.timezone⟩ }

/-- Apply the canonical writer's timezone admission to the target field. -/
def admit (binding : Arrow.TimestampBatch.Binding) : Except Error Descriptor :=
  if binding.metadata.unit = .second then
    (FromIpc.descriptor (millisecondBinding binding)).mapError .metadata
  else .error .expectedSeconds

namespace Internal

def rescaleSlot {binding : Arrow.TimestampBatch.Binding} (batch slot : Nat)
    (value : Option (Arrow.TimestampBatch.Value binding)) :
    Except Error (Option (Arrow.TimestampBatch.Value (millisecondBinding binding))) :=
  (value.mapM fun ticks => (Ticks.toInt64 ticks .millisecond).map (millisecondBinding binding).metadata.decode)
    |>.mapError (.rescale batch slot)

def rescaleBatch {binding : Arrow.TimestampBatch.Binding} (batch : Nat)
    (slots : Arrow.TimestampBatch.Column binding) :
    Except Error (Arrow.TimestampBatch.Column (millisecondBinding binding)) :=
  slots.zipIdx.mapM fun (value, slot) => rescaleSlot batch slot value

end Internal

/-- Bind millis under the same epoch convention and retain every IPC batch. -/
def prepare (original : Arrow.TimestampStream.Stream) : Except Error FromIpc.Source := do
  let descriptor ← admit original.binding
  let batches ← original.batches.zipIdx.mapM fun (slots, batch) => Internal.rescaleBatch batch slots
  return ⟨⟨millisecondBinding original.binding, batches⟩, descriptor⟩

/-- The complete original stream, including exact EOS, is checked before
metadata admission, rescaling, and any sink work. -/
def convert (ipc : Arrow.Limits) (limits : FromIpc.Limits) (input : KBytes) : Except Error Bytes :=
  if limits.maxInputBytes < input.len then .error .inputByteLimit
  else do
    let original ← (Arrow.TimestampStream.read ipc input).mapError .source
    let prepared ← prepare original
    let wire ← (FromIpc.Internal.serialize limits prepared).mapError .sink
    (FromIpc.Internal.certify limits prepared wire).mapError .sink
    return wire

/-- Interpret readback counts under the retained epoch and recover whole
seconds, preserving the full nullable batch shape. -/
def recover (kind : Kind) (groups : List (List (Option Int))) : Option (List (List (Option Int))) :=
  groups.mapM fun group =>
    group.mapM (Option.mapM fun count =>
      ((⟨count⟩ : Ticks kind .millisecond).rescale .second).map Ticks.ticks)

end Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds
