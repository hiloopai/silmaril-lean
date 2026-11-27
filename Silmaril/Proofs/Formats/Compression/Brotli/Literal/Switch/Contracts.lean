module

public import Silmaril.Formats.Compression.Brotli.Literal.Switch.Defs
import Silmaril.Formats.Compression.Brotli.Literal.Thms
import Silmaril.Formats.Compression.Brotli.BlockTypes.Switch.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Literal.Switch

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Literal (History lookup contextId readByte readByte_sound)
open Silmaril.Formats.Compression.Brotli.Literal.Switch

private theorem bind_mapped_ok {ε δ α β : Type} {action : Except ε α} {next : α → Except δ β}
    {map : ε → δ} {value : β} (parsed : (action.mapError map >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases parsed
  | ok result => exact ⟨result, rfl, parsed⟩

theorem Source.trans {before middle after : LSBReader} {input a rest b suffix : List Bool}
    (first : Source before middle input a rest) (second : Source middle after rest b suffix) :
    Source before after input (a ++ b) suffix :=
  ⟨by rw [first.split, second.split, List.append_assoc], second.rep, second.count,
    by rw [second.position, first.position, List.length_append, Nat.add_assoc]⟩

theorem tableFor_sound {header : CompressedHeader.Header} {history : History} {type : Nat}
    {table : Huffman.Description.Table} (read : tableFor header history type = .ok table) :
    TableWire header history type table := by
  unfold tableFor at read
  cases modeRead : header.initial.fields.modes[type]? with
  | none => simp [modeRead, throw] at read
  | some mode =>
    simp only [modeRead] at read
    cases mapped : lookup header.literalMap (64 * type + (contextId mode history).val) with
    | none => simp [mapped, throw] at read
    | some ordinal =>
      simp only [mapped] at read
      cases selected : header.literalTrees[ordinal]? with
      | none => simp [selected, throw] at read
      | some found =>
        simp only [selected] at read
        cases read
        exact ⟨mode, ordinal, modeRead, mapped, selected⟩

theorem readOne_sound {header : CompressedHeader.Header} {limit : Nat} {initial final : State}
    {before after : LSBReader} {input : List Bool} {byte : UInt8}
    (rep : before.Rep input) (count : before.count < 8)
    (read : Literal.Switch.readOne header limit initial before = .ok (byte, final, after)) :
    ∃ used suffix, StepWire header initial used byte final ∧
      Source before after input used suffix ∧ used.length ≤ limit := by
  unfold Literal.Switch.readOne at read
  obtain ⟨⟨runs, atCode⟩, switched, read⟩ := bind_mapped_ok read
  obtain ⟨table, tableRead, read⟩ := bind_mapped_ok read
  obtain ⟨⟨byte, after⟩, byteRead, done⟩ := bind_mapped_ok read
  cases done
  obtain ⟨_, other, switchBits, tail, selection, split, tailRep, tailCount, position, cap⟩ :=
    BlockTypes.Switch.select_sound rep count switched
  obtain ⟨alphabet, code, width, suffix, assigned, widthBound, codeCap, suffixBits, afterRep, afterCount, offset⟩ :=
    readByte_sound tailRep tailCount byteRead
  have first : Source before atCode input switchBits tail := ⟨split, tailRep, tailCount, position⟩
  have second : Source atCode after tail (msbBits code width) suffix :=
    ⟨suffixBits, afterRep, afterCount, by simpa only [msbBits_length] using offset⟩
  refine ⟨_, suffix, ⟨other .insertCopy (by decide), other .distance (by decide), rfl,
    switchBits, table, code, width, rfl, selection, tableFor_sound tableRead, alphabet, assigned, widthBound⟩,
    Source.trans first second, ?_⟩
  simp only [List.length_append, msbBits_length]
  omega

theorem Wire.carry {header : CompressedHeader.Header} {initial final : State}
    {bits : List Bool} {bytes : List UInt8} (wire : Wire header initial bits bytes final) :
    final.history = initial.history.advance bytes ∧ final.runs.insertCopy = initial.runs.insertCopy ∧
    final.runs.distance = initial.runs.distance := by
  induction wire with
  | done => exact ⟨rfl, rfl, rfl⟩
  | step one _ ih =>
    exact ⟨by simpa [History.advance, one.history] using ih.1,
      ih.2.1.trans one.insertCopy, ih.2.2.trans one.distance⟩

private theorem scan_sound {header : CompressedHeader.Header} {amount index limit : Nat}
    {initial final : State} {reversed output : List UInt8} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (read : Internal.scan header amount index limit initial reversed before = .ok (output, final, after)) :
    ∃ bytes used suffix, output = reversed.reverse ++ bytes ∧ bytes.length = amount ∧
      Wire header initial used bytes final ∧ Source before after input used suffix ∧ used.length ≤ limit := by
  induction amount generalizing index limit initial final reversed output before after input with
  | zero =>
    cases read
    exact ⟨[], [], input, by simp, rfl, .done _, ⟨rfl, rep, count, by simp⟩, by simp⟩
  | succ amount ih =>
    unfold Internal.scan at read
    obtain ⟨⟨byte, next, cursor⟩, readOne, read⟩ := bind_mapped_ok read
    obtain ⟨used, tail, step, first, cap⟩ := readOne_sound rep count readOne
    obtain ⟨bytes, bits, suffix, outputEq, size, wire, second, nextCap⟩ := ih first.rep first.count read
    refine ⟨byte :: bytes, used ++ bits, suffix, ?_, by simp [size], .step step wire, Source.trans first second, ?_⟩
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using outputEq
    · have position := first.position
      simp only [List.length_append]
      omega

theorem read_sound {header : CompressedHeader.Header} {amount limit : Nat} {initial final : State}
    {before after : LSBReader} {input : List Bool} {bytes : List UInt8}
    (rep : before.Rep input) (count : before.count < 8)
    (read : Literal.Switch.read header amount limit initial before = .ok (bytes, final, after)) :
    bytes.length = amount ∧ ∃ used suffix, Wire header initial used bytes final ∧
      Source before after input used suffix ∧ used.length ≤ limit := by
  obtain ⟨_, used, suffix, rfl, size, wire, source, cap⟩ := scan_sound rep count read
  simpa using And.intro size (show ∃ used suffix, Wire header initial used _ final ∧
      Source before after input used suffix ∧ used.length ≤ limit from ⟨used, suffix, wire, source, cap⟩)

theorem readOne_error {header : CompressedHeader.Header} {limit : Nat} {initial : State}
    {before : LSBReader} {input : List Bool} {error : StepError}
    (rep : before.Rep input) (count : before.count < 8)
    (read : Literal.Switch.readOne header limit initial before = .error error) :
    StepFailure header limit initial before input error := by
  unfold Literal.Switch.readOne at read
  cases select : BlockTypes.Switch.select header.initial.controls .literal limit initial.runs before with
  | error reason =>
    simp only [select, Except.mapError, bind, Except.bind] at read
    cases read
    exact .switch (BlockTypes.Switch.select_error rep count select)
  | ok pair =>
    obtain ⟨runs, atCode⟩ := pair
    simp only [select, Except.mapError, bind, Except.bind] at read
    obtain ⟨_, _, used, suffix, wire, split, afterRep, afterCount, position, cap⟩ :=
      BlockTypes.Switch.select_sound rep count select
    have source : Source before atCode input used suffix := ⟨split, afterRep, afterCount, position⟩
    cases chosen : tableFor header initial.history runs.literal.current with
    | error reason =>
      simp only [chosen] at read
      cases read
      exact .symbol select wire source cap (.table chosen)
    | ok table =>
      simp only [chosen] at read
      cases decoded : readByte table (limit - (atCode.totalRead - before.totalRead)) atCode with
      | error reason =>
        simp only [decoded] at read
        cases read
        exact .symbol select wire source cap (.code chosen decoded)
      | ok pair =>
        obtain ⟨_, _⟩ := pair
        simp only [decoded] at read
        cases read

private theorem scan_error {header : CompressedHeader.Header} {amount index limit : Nat}
    {initial : State} {reversed : List UInt8} {before : LSBReader} {input : List Bool} {error : Error}
    (rep : before.Rep input) (count : before.count < 8)
    (read : Internal.scan header amount index limit initial reversed before = .error error) :
    Failure header amount index limit initial before input error := by
  induction amount generalizing index limit initial reversed before input with
  | zero => cases read
  | succ amount ih =>
    unfold Internal.scan at read
    cases current : Literal.Switch.readOne header limit initial before with
    | error reason =>
      simp only [current, Except.mapError, bind, Except.bind] at read
      cases read
      exact .here (readOne_error rep count current)
    | ok result =>
      obtain ⟨byte, next, after⟩ := result
      simp only [current, Except.mapError, bind, Except.bind] at read
      obtain ⟨used, suffix, wire, source, cap⟩ := readOne_sound rep count current
      exact .next current wire source cap (ih source.rep source.count read)

theorem read_error {header : CompressedHeader.Header} {amount limit : Nat} {initial : State}
    {before : LSBReader} {input : List Bool} {error : Error} (rep : before.Rep input) (count : before.count < 8)
    (read : Literal.Switch.read header amount limit initial before = .error error) :
    Failure header amount 0 limit initial before input error :=
  scan_error rep count read

theorem Failure.index_bounds {header : CompressedHeader.Header} {amount index limit : Nat} {state : State}
    {before : LSBReader} {input : List Bool} {error : Error}
    (failure : Failure header amount index limit state before input error) :
    index ≤ error.index ∧ error.index < index + amount := by
  induction failure with
  | here => dsimp only; omega
  | next _ _ _ _ _ ih => omega

theorem Failure.offset {header : CompressedHeader.Header} {amount index limit : Nat} {state : State}
    {before : LSBReader} {input : List Bool} {error : Error}
    (failure : Failure header amount index limit state before input error) :
    ∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length := by
  induction failure with
  | here step =>
    cases step with
    | switch low => exact low.offset
    | symbol _ _ source _ _ => exact ⟨_, _, source.split, source.position⟩
  | next _ _ source _ _ ih =>
    obtain ⟨used, suffix, read, bit⟩ := ih
    exact ⟨_, suffix, by rw [source.split, read, List.append_assoc],
      by rw [bit, source.position, List.length_append, Nat.add_assoc]⟩

end Silmaril.Proofs.Formats.Compression.Brotli.Literal.Switch
