module

public import Silmaril.Formats.Compression.Brotli.Literal.Defs
import Silmaril.Formats.Compression.Bits.Thms
import Silmaril.Formats.Compression.Brotli.Huffman.Description.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Literal

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Literal
open Silmaril.Formats.Compression.Brotli.Literal.Internal

private structure Advance (before after : Cursor) (input used suffix : List Bool) : Prop where
  split : input = used ++ suffix
  rep : after.reader.Rep suffix
  count : after.reader.count < 8
  offset : after.reader.totalRead = before.reader.totalRead + used.length
  budget : before.remaining = after.remaining + used.length

private theorem Advance.trans {before middle after : Cursor} {input a rest b suffix : List Bool}
    (first : Advance before middle input a rest) (second : Advance middle after rest b suffix) :
    Advance before after input (a ++ b) suffix := by
  refine ⟨by rw [first.split, second.split, List.append_assoc], second.rep, second.count, ?_, ?_⟩
  · simp only [List.length_append, first.offset, second.offset]
    omega
  · simp only [List.length_append, first.budget, second.budget]
    omega

private theorem bind_ok {α β : Type} {action : Except Error α} {next : α → Except Error β}
    {value : β} (read : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases read
  | ok result => exact ⟨result, rfl, read⟩

private theorem mapError_ok {ε α : Type} {action : Except ε α} {f : ε → Error} {value : α}
    (read : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases read <;> rfl

theorem source_sound {header : CompressedHeader.Header} {tables : Source}
    (read : source header = .ok tables) : FromHeader header tables := by
  unfold source at read
  split at read <;> try contradiction
  rename_i control
  split at read <;> try contradiction
  rename_i mode modes
  split at read <;> try contradiction
  split at read <;> try contradiction
  cases read
  exact ⟨control, modes, rfl, rfl⟩

theorem Wire.history {source : Source} {start final : History} {bits : List Bool} {bytes : List UInt8}
    (wire : Wire source start bits bytes final) : final = start.advance bytes := by
  induction wire with
  | done => rfl
  | step _ _ _ _ _ _ ih => exact ih

theorem Wire.bit_bound {source : Source} {start final : History} {bits : List Bool} {bytes : List UInt8}
    (wire : Wire source start bits bytes final) : bits.length ≤ 15 * bytes.length := by
  induction wire with
  | done => decide
  | step _ _ _ _ widthBound _ ih =>
    simp only [List.length_append, List.length_cons, msbBits_length]
    omega

theorem readByte_sound {table : Huffman.Description.Table} {bitLimit : Nat} {before after : LSBReader}
    {byte : UInt8} {input : List Bool} (rep : before.Rep input) (count : before.count < 8)
    (read : readByte table bitLimit before = .ok (byte, after)) :
    table.alphabetSize = 256 ∧
    ∃ code width suffix, table.codeFor byte.toNat = some (code, width) ∧ width ≤ 15 ∧ width ≤ bitLimit ∧
      input = msbBits code width ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + width := by
  unfold readByte at read
  split at read <;> try contradiction
  rename_i alphabet
  obtain ⟨⟨symbol, cursor⟩, actual, done⟩ := bind_ok read
  simp only [] at done
  split at done <;> try contradiction
  cases done
  obtain ⟨code, width, suffix, assigned, widthBound, cap, split, nextRep, nextCount, offset⟩ :=
    Huffman.Description.Table.readBounded_sound rep count (mapError_ok actual)
  exact ⟨by omega, code, width, suffix, by simpa only [UInt8.toNat_ofNatLT] using assigned, widthBound, cap,
    split, nextRep, nextCount, offset⟩

private theorem readOne_sound {source : Source} {history : History} {before after : Cursor}
    {byte : UInt8} {input : List Bool}
    (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : readOne source history before = .ok (byte, after)) :
    ∃ tree table code width suffix, source.treeIndex? history = some tree ∧
      source.trees[tree]? = some table ∧ table.alphabetSize = 256 ∧
      table.codeFor byte.toNat = some (code, width) ∧ width ≤ 15 ∧
      Advance before after input (msbBits code width) suffix := by
  unfold readOne at read
  split at read <;> try contradiction
  rename_i tree treeRead
  split at read <;> try contradiction
  rename_i table tableRead
  obtain ⟨⟨byte, next⟩, parsed, done⟩ := bind_ok read
  cases done
  obtain ⟨alphabet, code, width, suffix, assigned, widthBound, cap, split, nextRep, nextCount, offset⟩ :=
    readByte_sound rep count parsed
  exact ⟨tree, table, code, width, suffix, treeRead, tableRead, alphabet, assigned, widthBound, split,
    nextRep, nextCount, by simpa only [Cursor.advance, msbBits_length] using offset,
    by simp only [Cursor.advance, msbBits_length, offset]; omega⟩

private theorem scan_sound {source : Source} {amount : Nat} {history finalHistory : History}
    {reversed output : List UInt8} {before after : Cursor} {input : List Bool}
    (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : scan source amount history reversed before = .ok (output, finalHistory, after)) :
    ∃ bytes used suffix, output = reversed.reverse ++ bytes ∧ bytes.length = amount ∧
      Wire source history used bytes finalHistory ∧ Advance before after input used suffix := by
  induction amount generalizing history finalHistory reversed output before after input with
  | zero =>
    cases read
    exact ⟨[], [], input, by simp, rfl, .done _, ⟨by simp, rep, count, by simp, by simp⟩⟩
  | succ amount ih =>
    unfold scan at read
    obtain ⟨⟨byte, cursor⟩, actual, next⟩ := bind_ok read
    obtain ⟨tree, table, code, width, rest, selected, bound, alphabet, assigned, widthCap, first⟩ :=
      readOne_sound rep count actual
    obtain ⟨tail, bits, suffix, outputEq, size, wire, second⟩ := ih first.rep first.count next
    refine ⟨byte :: tail, _, suffix, ?_, by simp [size],
      .step selected bound alphabet assigned widthCap wire, first.trans second⟩
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using outputEq

theorem read_sound {header : CompressedHeader.Header} {command : Command.Value} {metaLength : Nat}
    {limits : Limits} {state : State} {before after : LSBReader} {input : List Bool} {result : Result}
    (rep : before.Rep input) (count : before.count < 8)
    (read : Silmaril.Formats.Compression.Brotli.Literal.read header command metaLength limits state before =
      .ok (result, after)) :
    state.produced < metaLength ∧ result.bytes.length = command.insertLength ∧
    result.state.produced = state.produced + result.bytes.length ∧
    result.state.produced ≤ metaLength ∧ result.state.produced ≤ limits.output ∧
    result.state.history = state.history.advance result.bytes ∧
    (result.next = .endOfMetaBlock ↔ result.state.produced = metaLength) ∧
    (result.next = .copyPending ↔ result.state.produced < metaLength) ∧
    ∃ tables used suffix, FromHeader header tables ∧
      Wire tables state.history used result.bytes result.state.history ∧ input = used ++ suffix ∧
      after.Rep suffix ∧ after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧
      used.length ≤ limits.bits := by
  unfold Silmaril.Formats.Compression.Brotli.Literal.read at read
  obtain ⟨tables, fromHeader, next⟩ := bind_ok read
  simp only [] at next
  split at next <;> try contradiction
  rename_i metaCap
  split at next <;> try contradiction
  rename_i outCap
  obtain ⟨⟨bytes, history, cursor⟩, scanned, done⟩ := bind_ok next
  cases done
  obtain ⟨output, used, suffix, outputEq, size, wire, advance⟩ := scan_sound rep count scanned
  simp only [List.reverse_nil, List.nil_append] at outputEq
  subst bytes
  have cap := advance.budget
  dsimp at cap
  refine ⟨by omega, size, by rw [size],
    by change state.produced + command.insertLength ≤ metaLength; omega,
    by change state.produced + command.insertLength ≤ limits.output; omega, Wire.history wire, ?_, ?_,
    tables, used, suffix, source_sound fromHeader, wire, advance.split, advance.rep,
    advance.count, advance.offset, by omega⟩
  · split <;> simp_all
  · split <;> simp_all <;> omega

end Silmaril.Proofs.Formats.Compression.Brotli.Literal
