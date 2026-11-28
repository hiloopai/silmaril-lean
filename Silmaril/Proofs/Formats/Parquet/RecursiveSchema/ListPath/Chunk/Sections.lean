module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs


namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Chunk
open Parquet.RecursiveSchema.Repeated.Chunk (LevelBlock LevelWire)

variable {P : Type} [ScanShape P]

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

/-- Isolate exactly the bytes consumed by a V1 level reader. An omitted
level consumes nothing and leaves the payload cursor in place. -/
private theorem level_section {limits : Hybrid.Limits} {maximum count : Nat}
    {body : Bytes} {block : LevelBlock} (wire : LevelWire limits maximum count body block) :
    ∃ bytes, body.toList = bytes ++ block.tail.toList ∧
      LevelWire limits maximum count (Bytes.ofList bytes) ⟨block.levels, .empty⟩ := by
  cases wire with
  | omitted zero bounded budget => exact ⟨[], rfl, .omitted zero bounded budget⟩
  | @encoded levels tail encoded lengthBytes nonzero length size budget bodyBytes hybrid =>
    refine ⟨lengthBytes ++ encoded.toList, by simpa [List.append_assoc] using bodyBytes, ?_⟩
    exact .encoded nonzero length size budget (by simp) hybrid

public theorem sections_wire {limits : Hybrid.Limits} {plan : P} {count : Nat}
    {input : SectionSource} {body : Bytes} {reps defs : LevelBlock}
    (sliced : input.bytes.slice? input.span.start (some input.span.stop) = some body)
    (repWire : LevelWire limits (ScanShape.shape plan).repetitions count body reps)
    (defWire : LevelWire limits (ScanShape.shape plan).definitions count reps.tail defs) :
    SectionsWire limits plan count input (sections input body reps defs) reps.levels defs.levels defs.tail := by
  obtain ⟨repetition, repBody, repSection⟩ := level_section repWire
  obtain ⟨definition, defBody, defSection⟩ := level_section defWire
  have split : body.toList = repetition ++ definition ++ defs.tail.toList := by
    rw [repBody, defBody, List.append_assoc]
  have total : input.span.stop = input.span.start + body.length := by
    have ordered := (Bytes.slice?_eq_some_iff.mp sliced).1
    have length := Bytes.length_of_slice? sliced
    simp only [Option.getD_some] at ordered length
    omega
  have afterRep : body.length - reps.tail.length = repetition.length := by
    have count := congrArg List.length repBody
    simp only [List.length_append, Bytes.length_toList] at count
    omega
  have afterDef : body.length - defs.tail.length = repetition.length + definition.length := by
    have count := congrArg List.length split
    simp only [List.length_append, Bytes.length_toList] at count
    omega
  have suffixEnd :
      input.span.start + (repetition ++ definition).length + defs.tail.length = input.span.stop := by
    have count := congrArg List.length split
    simp only [List.length_append, Bytes.length_toList] at count ⊢
    omega
  have repSlice := section_slice sliced (preceding := []) (part := repetition)
    (suffix := definition ++ defs.tail.toList) (by simpa [List.append_assoc] using split)
  have defSlice := section_slice sliced (preceding := repetition) (part := definition)
    (suffix := defs.tail.toList) split
  have suffixSlice := section_slice sliced (preceding := repetition ++ definition) (part := defs.tail.toList)
    (suffix := []) (by simpa using split)
  refine ⟨repetition, definition, repSection, defSection, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [sections, afterRep] using repSlice
  · simpa [sections, afterRep, afterDef, Nat.add_assoc] using defSlice
  · rw [Bytes.length_toList, suffixEnd] at suffixSlice
    simpa [sections, afterDef, List.length_append] using suffixSlice

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk
