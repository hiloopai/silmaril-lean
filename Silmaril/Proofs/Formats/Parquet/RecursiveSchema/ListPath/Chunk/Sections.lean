module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs
import Silmaril.Formats.Parquet.Page.Checksum.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Chunk
open Parquet.RecursiveSchema.Repeated.Chunk (LevelBlock LevelWire)

private theorem section_slice {source body : Bytes} {start stop : Nat}
    (sliced : source.slice? start (some stop) = some body)
    {preceding part suffix : List UInt8}
    (split : body.toList = preceding ++ part ++ suffix) :
    source.slice? (start + preceding.length) (some (start + preceding.length + part.length)) =
      some (Bytes.ofList part) := by
  obtain ⟨lower, upper, exact⟩ := Bytes.slice?_eq_some_iff.mp sliced
  simp only [Option.getD_some] at lower upper exact
  have bytes := Bytes.length_of_slice? sliced
  simp only [Option.getD_some] at bytes
  have needed : preceding.length + part.length ≤ stop - start := by
    have count := congrArg List.length split
    simp only [List.length_append, Bytes.length_toList] at count
    omega
  apply Bytes.slice?_eq_some_iff.mpr
  refine ⟨by simp, by simp; omega, ?_⟩
  congr 1
  simp only [Option.getD_some, Nat.add_sub_cancel_left]
  have original : (source.toList.drop start).take (stop - start) = preceding ++ part ++ suffix := by
    rw [← split, exact, Bytes.toList_ofList]
  have selected := congrArg (fun xs : List UInt8 => (xs.drop preceding.length).take part.length) original
  simp only [List.drop_take, List.take_take,
    List.drop_drop] at selected
  rw [show min part.length (stop - start - preceding.length) = part.length from
    Nat.min_eq_left (by omega)] at selected
  simpa [Nat.add_comm] using selected.symm

public theorem sections_wire {limits : Hybrid.Limits} {plan : Plan} {count : Nat} {source : Bytes}
    {frame : Page.Frame} {reps defs : LevelBlock}
    (extent : Page.Checksum.PayloadWithin source frame)
    (repWire : LevelWire limits plan.shape.repetitions count (Page.Checksum.payloadBytes source frame) reps)
    (defWire : LevelWire limits plan.shape.definitions count reps.tail defs) :
    SectionsWire limits plan count source frame
      (sections frame (Page.Checksum.payloadBytes source frame) reps defs) reps.levels defs.levels defs.tail := by
  let body := Page.Checksum.payloadBytes source frame
  obtain ⟨sliced, size⟩ := Page.Checksum.payload_exact extent
  have total : frame.payload.stop = frame.payload.start + body.length := by
    change (Page.Checksum.payloadBytes source frame).length = _ at size
    rw [extent.2.2.1, ← size]
  have repeated : plan.shape.repetitions ≠ 0 := by simp [Plan.shape, Shape.repetitions]
  have defined : plan.shape.definitions ≠ 0 := by
    simp only [Plan.shape, Shape.definitions]
    omega
  cases repWire with
  | omitted absent _ _ => exact False.elim (repeated absent)
  | @encoded reps repTail repBytes repPrefix _ repLen repSize repBound repBody repHybrid =>
    cases defWire with
    | omitted absent _ _ => exact False.elim (defined absent)
    | @encoded defs suffix defBytes defPrefix _ defLen defSize defBound defBody defHybrid =>
      let repetition := repPrefix ++ repBytes.toList
      let definition := defPrefix ++ defBytes.toList
      change body.toList = _ at repBody
      have split : body.toList = repetition ++ definition ++ suffix.toList := by
        rw [repBody, defBody]
        simp [repetition, definition, List.append_assoc]
      have afterRep : body.length - repTail.length = repetition.length := by
        have count := congrArg List.length repBody
        simp only [List.length_append, Bytes.length_toList] at count
        simp only [repetition, List.length_append, Bytes.length_toList]
        omega
      have afterDef : body.length - suffix.length = repetition.length + definition.length := by
        have count := congrArg List.length split
        simp only [List.length_append, Bytes.length_toList] at count
        omega
      have suffixEnd :
          frame.payload.start + (repetition ++ definition).length + suffix.length = frame.payload.stop := by
        have count := congrArg List.length split
        simp only [List.length_append, Bytes.length_toList] at count ⊢
        omega
      have repSlice := section_slice sliced (preceding := []) (part := repetition)
        (suffix := definition ++ suffix.toList) (by simpa [List.append_assoc] using split)
      have defSlice := section_slice sliced (preceding := repetition) (part := definition)
        (suffix := suffix.toList) split
      have suffixSlice := section_slice sliced (preceding := repetition ++ definition) (part := suffix.toList)
        (suffix := []) (by simpa using split)
      refine ⟨repPrefix, defPrefix, repBytes.toList, defBytes.toList, repLen, defLen, ?_, ?_, ?_, ?_,
        repHybrid, defHybrid, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simpa using repSize
      · simpa using defSize
      · simpa using repBound
      · simpa using defBound
      · simpa [sections, ← show body = Page.Checksum.payloadBytes source frame from rfl, afterRep, repetition]
          using repSlice
      · simpa [sections, ← show body = Page.Checksum.payloadBytes source frame from rfl, afterRep, afterDef,
          Nat.add_assoc, definition] using defSlice
      · rw [Bytes.length_toList] at suffixSlice
        rw [suffixEnd] at suffixSlice
        simpa [sections, ← show body = Page.Checksum.payloadBytes source frame from rfl, afterDef,
          List.length_append] using suffixSlice

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk
