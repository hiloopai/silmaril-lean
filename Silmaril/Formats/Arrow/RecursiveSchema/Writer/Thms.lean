module

public import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Writer.Size
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Writer.Readback

@[expose] public section

namespace Silmaril.Formats.Arrow.RecursiveSchema.Writer

theorem Wire.fieldHeader_extent (name : Option String) (nullable : Bool)
    (kind : RecursiveSchema.Wire.Kind) (children : Nat) :
    (Wire.fieldHeader name nullable kind children).len = 68 :=
  Proofs.Formats.Arrow.RecursiveSchema.Writer.header_extent name nullable kind children

theorem Wire.fieldPrefix_extent (name : Option String) (nullable : Bool)
    (kind : RecursiveSchema.Wire.Kind) (children : List KBytes) :
    (Wire.fieldPrefix name nullable kind children).len = Wire.fieldPrefixSize name children.length :=
  Proofs.Formats.Arrow.RecursiveSchema.Writer.prefix_extent name nullable kind children

theorem Wire.metadata_extent (schema : Schema) :
    (Wire.metadata schema).len = Wire.metadataSize schema :=
  Proofs.Formats.Arrow.RecursiveSchema.Writer.metadata_extent schema

/-- The offset at each slot refers to its positional fragment, whose
Field table is 12 bytes after the fragment start. -/
theorem Wire.offsets_target {slot start index : Nat} {objects : List KBytes}
    (bound : index < objects.length) :
    (MetadataWriter.Wire.fieldOffsets slot start objects)[index]? =
      some (start + ((objects.take index).map KBytes.len).sum + 12 - (slot + 4 * index)) :=
  Proofs.Formats.Arrow.RecursiveSchema.Writer.offsets_target bound

theorem Wire.offsets_forward {slot start : Nat} {objects : List KBytes}
    (gap : slot + 4 * objects.length ≤ start)
    (objectsFit : ∀ object ∈ objects, 16 ≤ object.len) :
    ∀ offset ∈ MetadataWriter.Wire.fieldOffsets slot start objects,
      4 ≤ offset ∧ offset < start + (objects.map KBytes.len).sum :=
  Proofs.Formats.Arrow.RecursiveSchema.Writer.offsets_forward gap objectsFit

/-- Preflight accounts for the actual padded metadata before allocation. -/
theorem plan_extent {limits : Limits} {schema : Schema} {budget : Budget}
    (accepted : plan limits schema = .ok budget) :
    budget.bytes = Wire.metadataSize schema ∧ budget.bytes < 2^31 ∧
      budget.bytes ≤ limits.ipc.metadataBytes ∧ budget.fields ≤ limits.ipc.fields :=
  Proofs.Formats.Arrow.RecursiveSchema.Writer.plan_extent accepted

theorem serialize_extent {limits : Limits} {schema : Schema} {bytes : KBytes}
    (accepted : serialize limits schema = .ok bytes) :
    ∃ budget, plan limits schema = .ok budget ∧
      budget.bytes = Wire.metadataSize schema ∧ budget.bytes = (Wire.metadata schema).len ∧
      budget.bytes < 2^31 ∧ budget.bytes ≤ limits.ipc.metadataBytes ∧
      bytes = StreamWriter.envelopeBytes budget.bytes ++ (Wire.metadata schema ++ StreamWriter.eos) :=
  Proofs.Formats.Arrow.RecursiveSchema.Writer.serialize_extent accepted

theorem equalSchema_exact {depth : Nat} {left right : Schema}
    (same : equalFields (equalField depth) left.fields right.fields = true) : left = right :=
  Proofs.Formats.Arrow.RecursiveSchema.Writer.equalSchema_exact same

theorem serializeFrame_extent {limits : Limits} {schema : Schema} {bytes : KBytes}
    (written : serializeFrame limits schema = .ok bytes) :
    ∃ budget, plan limits schema = .ok budget ∧
      budget.bytes = (Wire.metadata schema).len ∧ budget.bytes < 2^31 ∧
      budget.bytes ≤ limits.ipc.metadataBytes ∧
      bytes = StreamWriter.envelopeBytes budget.bytes ++ Wire.metadata schema :=
  Proofs.Formats.Arrow.RecursiveSchema.Writer.serializeFrame_extent written

/-- Successful emission certifies exact readback of the original schema,
zero RecordBatches and the native modern EOS at the end of the carrier. -/
theorem emit_wire {limits : Limits} {schema : Schema} {bytes : KBytes}
    (accepted : emit limits schema = .ok bytes) : EmissionWire limits schema bytes :=
  Proofs.Formats.Arrow.RecursiveSchema.Writer.emit_wire accepted

end Silmaril.Formats.Arrow.RecursiveSchema.Writer
