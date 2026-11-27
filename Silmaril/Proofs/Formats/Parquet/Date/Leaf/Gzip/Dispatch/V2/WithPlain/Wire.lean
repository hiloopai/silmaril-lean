module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Chunk Slots selectChunk)
open Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem route_selected {bound : Bound} {index : Nat} {selected : Chunk}
    (admitted : selectChunk bound index = .ok selected) :
    route bound index = .ok (if selected.column.metadata.dictionaryPageOffset.isSome then
      .dictionaryBacked else .plain) := by
  obtain ⟨group, column, _⟩ := Date.Leaf.selectChunk_exact admitted
  simp [route, group, column, Pure.pure, Except.pure]

theorem readGroup_routeError {limits : Limits} {bound : Bound} {index : Nat} {cause : Date.Leaf.Error}
    (failed : route bound index = .error cause) :
    readGroup limits bound index = .error (.selection cause) := by
  simp [readGroup, failed, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_plain_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (routed : route bound index = .ok .plain) :
    readGroup limits bound index =
      (Date.Leaf.Gzip.V2.readGroup (plainLimits limits) bound index).mapError .plain := by
  simp [readGroup, routed, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_dictionaryBacked_agrees {limits : Limits} {bound : Bound} {index : Nat}
    (routed : route bound index = .ok .dictionaryBacked) :
    readGroup limits bound index =
      (Date.Leaf.Gzip.Dispatch.V2.readGroup limits bound index).mapError .dictionaryBacked := by
  simp [readGroup, routed, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_dictionary_agrees {limits : Limits} {bound : Bound} {index : Nat} {frames : List Page.Frame}
    (routed : route bound index = .ok .dictionaryBacked)
    (original : Date.Leaf.Gzip.Dispatch.V2.FramedGroup limits bound index frames)
    (chosen : Date.Leaf.Gzip.Dispatch.V2.profile frames = .dictionary) :
    readGroup limits bound index =
      ((Date.Leaf.Dictionary.Gzip.V2.readGroup limits bound index).mapError
        Date.Leaf.Gzip.Dispatch.V2.dictionaryError).mapError .dictionaryBacked := by
  rw [readGroup_dictionaryBacked_agrees routed, Date.Leaf.Gzip.Dispatch.V2.readGroup_dictionary_agrees original chosen]

theorem readGroup_fallback_agrees {limits : Limits} {bound : Bound} {index : Nat} {frames : List Page.Frame}
    (routed : route bound index = .ok .dictionaryBacked)
    (original : Date.Leaf.Gzip.Dispatch.V2.FramedGroup limits bound index frames)
    (chosen : Date.Leaf.Gzip.Dispatch.V2.profile frames = .fallback) :
    readGroup limits bound index =
      (Date.Leaf.Fallback.Gzip.V2.readGroup limits bound index).mapError .dictionaryBacked := by
  rw [readGroup_dictionaryBacked_agrees routed, Date.Leaf.Gzip.Dispatch.V2.readGroup_fallback_agrees original chosen]

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    GroupWire limits bound index slots := by
  cases routed : route bound index with
  | error => rw [readGroup_routeError routed] at read; contradiction
  | ok choice =>
    cases choice with
    | plain =>
      have decoded := mapError_ok ((readGroup_plain_agrees routed).symm.trans read)
      obtain ⟨_, _, accepted, chunk, decoded, ordered, count⟩ := Date.Leaf.Gzip.V2.readGroup_wire decoded
      exact .plain routed accepted chunk decoded ordered count
    | dictionaryBacked =>
      have decoded := mapError_ok ((readGroup_dictionaryBacked_agrees routed).symm.trans read)
      obtain ⟨_, _, accepted, chunk, nonempty, phase, decoded, ordered, count⟩ :=
        Date.Leaf.Gzip.Dispatch.V2.readGroup_wire decoded
      exact .dictionaryBacked routed accepted chunk nonempty phase decoded ordered count

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain
