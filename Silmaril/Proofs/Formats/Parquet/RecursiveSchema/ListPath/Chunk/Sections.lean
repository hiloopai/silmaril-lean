module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs


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

public theorem sections_wire {limits : Hybrid.Limits} {plan : Plan} {count : Nat}
    {input : SectionSource} {body : Bytes} {reps defs : LevelBlock}
    (sliced : input.bytes.slice? input.span.start (some input.span.stop) = some body)
    (repWire : LevelWire limits plan.shape.repetitions count body reps)
    (defWire : LevelWire limits plan.shape.definitions count reps.tail defs) :
    SectionsWire limits plan count input (sections input body reps defs) reps.levels defs.levels defs.tail := by
  have total : input.span.stop = input.span.start + body.length := by
    have ordered := (Bytes.slice?_eq_some_iff.mp sliced).1
    have length := Bytes.length_of_slice? sliced
    simp only [Option.getD_some] at ordered length
    omega
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
          input.span.start + (repetition ++ definition).length + suffix.length = input.span.stop := by
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
        repHybrid, defHybrid, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simpa using repSize
      · simpa using defSize
      · simpa using repBound
      · simpa using defBound
      · simpa [sections, afterRep, repetition]
          using repSlice
      · simpa [sections, afterRep, afterDef,
          Nat.add_assoc, definition] using defSlice
      · rw [Bytes.length_toList] at suffixSlice
        rw [suffixEnd] at suffixSlice
        simpa [sections, afterDef,
          List.length_append] using suffixSlice

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk
