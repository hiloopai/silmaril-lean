module

public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.FromIpc.Readback

public section

namespace Silmaril.Formats.Parquet.Timestamp.FromIpc

/-- The accepted descriptor preserves the original unit and epoch interpretation. -/
theorem descriptor_exact {binding : Arrow.TimestampBatch.Binding} {annotation : Descriptor}
    (h : descriptor binding = .ok annotation) :
    annotation.unit.tickUnit = binding.metadata.unit ∧
      binding.metadata.timezone = (if annotation.isAdjustedToUTC then some "UTC" else none) ∧
      annotation.kind = binding.metadata.kind :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.descriptor_exact h

/-- Metadata refusal follows checked Schema admission and precedes record decoding. -/
theorem readSource_refusal {ipc : Arrow.Limits} {limits : Limits} {input : KBytes}
    {binding : Arrow.TimestampBatch.Binding} {start : Nat} {cause : Error}
    (bytes : input.len ≤ limits.maxInputBytes) (wellFormed : input.wf = true)
    (schema : Arrow.TimestampStream.readSchema ipc input = .ok (binding, start))
    (refused : descriptor binding = .error cause) :
    readSource ipc limits input = .error cause :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.readSource_refusal bytes wellFormed schema refused

/-- An admitted source agrees with the complete IPC reader through exact EOS. -/
theorem readSource_exact {ipc : Arrow.Limits} {limits : Limits} {input : KBytes} {source : Source}
    (read : readSource ipc limits input = .ok source) :
    Arrow.TimestampStream.read ipc input = .ok source.stream ∧
      descriptor source.stream.binding = .ok source.descriptor :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.readSource_exact read

/-- Certification exposes the same checked file binding and indexed readback
for every prepared source given to the canonical writer. -/
theorem certify_readback {limits : Limits} {source : Source} {wire : Bytes}
    (certified : Internal.certify limits source wire = .ok ()) :
    ∃ bound groups, Leaf.openLeaf limits.snapshot wire 1 = .ok bound ∧
      Internal.readGroups limits.leaf bound = .ok groups ∧ Internal.ReadbackMatches source bound groups :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.certify_sound certified

/-- The emitted file recovers the exact descriptor and one ordered nullable group
per explicit input batch through the stated certification limits. -/
theorem convert_readback {ipc : Arrow.Limits} {limits : Limits} {input : KBytes} {wire : Bytes}
    (written : convert ipc limits input = .ok wire) :
    ∃ source bound groups,
      Arrow.TimestampStream.read ipc input = .ok source.stream ∧
      descriptor source.stream.binding = .ok source.descriptor ∧
      Leaf.openLeaf limits.snapshot wire 1 = .ok bound ∧
      Internal.readGroups limits.leaf bound = .ok groups ∧
      Internal.ReadbackMatches source bound groups :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.convert_readback written

end Silmaril.Formats.Parquet.Timestamp.FromIpc
