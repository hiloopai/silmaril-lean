module

public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Defs
import Silmaril.Formats.Arrow.TimestampStream.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.FromIpc

open Silmaril.Formats Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.FromIpc
open Silmaril.Numeric.Timestamp (TickUnit)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

theorem descriptor_exact {binding : Arrow.TimestampBatch.Binding} {annotation : Descriptor}
    (h : descriptor binding = .ok annotation) :
    annotation.unit.tickUnit = binding.metadata.unit ∧
      binding.metadata.timezone = (if annotation.isAdjustedToUTC then some "UTC" else none) ∧
      annotation.kind = binding.metadata.kind := by
  obtain ⟨name, nullable, unit, zone⟩ := binding
  cases unit <;> cases zone <;> simp [descriptor, Bind.bind, Except.bind] at h
  all_goals
    first
    | cases h; exact ⟨rfl, rfl, rfl⟩
    | rename_i zone
      by_cases canonical : zone = "UTC"
      · subst zone
        simp [Pure.pure, Except.pure] at h
        cases h
        exact ⟨rfl, rfl, rfl⟩
      · simp [canonical] at h

theorem readSource_refusal {ipc : Arrow.Limits} {limits : Limits} {input : KBytes}
    {binding : Arrow.TimestampBatch.Binding} {start : Nat} {cause : FromIpc.Error}
    (bytes : input.len ≤ limits.maxInputBytes) (wellFormed : input.wf = true)
    (schema : Arrow.TimestampStream.readSchema ipc input = .ok (binding, start))
    (refused : descriptor binding = .error cause) :
    readSource ipc limits input = .error cause := by
  simp [readSource, Nat.not_lt.mpr bytes, wellFormed, schema, refused, Bind.bind, Except.bind, Except.mapError]

theorem readSource_exact {ipc : Arrow.Limits} {limits : Limits} {input : KBytes} {source : Source}
    (read : readSource ipc limits input = .ok source) :
    Arrow.TimestampStream.read ipc input = .ok source.stream ∧
      descriptor source.stream.binding = .ok source.descriptor := by
  unfold readSource at read
  split at read
  · contradiction
  · split at read
    · contradiction
    · rename_i wellFormed
      obtain ⟨⟨binding, start⟩, schema, read⟩ := bind_ok read
      obtain ⟨annotation, admitted, read⟩ := bind_ok read
      obtain ⟨batches, batchRead, read⟩ := bind_ok read
      cases read
      have wf : input.wf = true := by simpa using wellFormed
      exact ⟨by simp [Arrow.TimestampStream.read, wf, mapError_ok schema, mapError_ok batchRead,
        Bind.bind, Except.bind, Pure.pure, Except.pure], admitted⟩

theorem certifyWith_sound {admit : Leaf.Bound → Bool} {limits : Limits} {source : Source} {wire : Bytes}
    (certified : Internal.certifyWith admit limits source wire = .ok ()) :
    ∃ bound groups, Leaf.openLeaf limits.snapshot wire 1 = .ok bound ∧
      Internal.readGroups limits.leaf bound = .ok groups ∧
      admit bound = true ∧ Internal.ReadbackMatches source bound groups := by
  unfold Internal.certifyWith at certified
  obtain ⟨bound, openResult, certified⟩ := bind_ok certified
  obtain ⟨groups, groupResult, certified⟩ := bind_ok certified
  split at certified
  · exact ⟨bound, groups, mapError_ok openResult, groupResult, by assumption⟩
  · contradiction

theorem certify_sound {limits : Limits} {source : Source} {wire : Bytes}
    (certified : Internal.certify limits source wire = .ok ()) :
    ∃ bound groups, Leaf.openLeaf limits.snapshot wire 1 = .ok bound ∧
      Internal.readGroups limits.leaf bound = .ok groups ∧ Internal.ReadbackMatches source bound groups := by
  obtain ⟨bound, groups, opened, read, _, agrees⟩ := certifyWith_sound certified
  exact ⟨bound, groups, opened, read, agrees⟩

theorem convert_readback {ipc : Arrow.Limits} {limits : Limits} {input : KBytes} {wire : Bytes}
    (written : convert ipc limits input = .ok wire) :
    ∃ source bound groups,
      Arrow.TimestampStream.read ipc input = .ok source.stream ∧
      descriptor source.stream.binding = .ok source.descriptor ∧
      Leaf.openLeaf limits.snapshot wire 1 = .ok bound ∧
      Internal.readGroups limits.leaf bound = .ok groups ∧
      Internal.ReadbackMatches source bound groups := by
  unfold convert at written
  obtain ⟨source, read, written⟩ := bind_ok written
  obtain ⟨output, _, written⟩ := bind_ok written
  obtain ⟨_, certified, written⟩ := bind_ok written
  cases written
  obtain ⟨bound, groups, checked, decoded, exactRead⟩ := certify_sound certified
  exact ⟨source, bound, groups, (readSource_exact read).1, (readSource_exact read).2,
    checked, decoded, exactRead⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.FromIpc
