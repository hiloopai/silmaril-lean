module

public import Silmaril.Formats.Compression.Brotli.BlockTypes.Defs
import Silmaril.Formats.Compression.Brotli.Huffman.Description.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.BlockTypes

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.BlockTypes
open Silmaril.Formats.Compression.Brotli.BlockTypes.Internal
open Huffman.Description (Table)

private structure Advance (before after : Cursor) (input used suffix : List Bool) : Prop where
  split : input = used ++ suffix
  rep : after.reader.Rep suffix
  count : after.reader.count < 8
  offset : after.reader.totalRead = before.reader.totalRead + used.length
  budget : before.remaining = after.remaining + used.length

private theorem Advance.trans {before middle after : Cursor}
    {input a rest b suffix : List Bool}
    (first : Advance before middle input a rest) (second : Advance middle after rest b suffix) :
    Advance before after input (a ++ b) suffix := by
  refine ⟨by rw [first.split, second.split, List.append_assoc], second.rep, second.count, ?_, ?_⟩
  · simp only [List.length_append, second.offset, first.offset]
    omega
  · simp only [List.length_append, first.budget, second.budget]
    omega

private theorem bind_ok {α β : Type} {action : Except Error α} {next : α → Except Error β}
    {value : β} (read : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

private theorem description_ok {α : Type} {action : Except Huffman.Description.Error α} {out : α}
    (read : action.mapError Error.description = .ok out) : action = .ok out := by
  cases action <;> cases read <;> rfl

private theorem take_sound {width value : Nat} {before after : Cursor} {input : List Bool}
    (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : take before width = .ok (value, after)) :
    value < 2 ^ width ∧ ∃ suffix, Advance before after input (natBits value width) suffix := by
  unfold take at read
  split at read <;> try contradiction
  rename_i cap
  split at read <;> try contradiction
  rename_i n cursor actual
  cases read
  obtain ⟨suffix, split, rep', fits, offset, count'⟩ := LSBReader.readBits_sound rep count actual
  refine ⟨fits, suffix, split, rep', count' ▸ Nat.mod_lt _ (by decide), ?_, ?_⟩
  · simpa only [natBits_length] using offset
  · simp only [natBits_length]
    omega

private theorem count_sound {before after : Cursor} {types : Nat} {input : List Bool}
    (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : Internal.readCount before = .ok (types, after)) :
    ∃ used suffix, CountWire used types ∧ Advance before after input used suffix := by
  unfold Internal.readCount at read
  obtain ⟨⟨lead, cursor⟩, field, next⟩ := bind_ok read
  obtain ⟨range, middle, first⟩ := take_sound rep count field
  simp only [] at next
  split at next
  · rename_i zero
    subst lead
    cases next
    exact ⟨[false], middle, .one, first⟩
  · rename_i nonzero
    have : lead = 1 := by omega
    subst lead
    obtain ⟨⟨width, widthCursor⟩, header, data⟩ := bind_ok next
    obtain ⟨⟨extra, final⟩, payload, done⟩ := bind_ok data
    cases done
    obtain ⟨widthRange, tail, second⟩ := take_sound first.rep first.count header
    obtain ⟨extraRange, suffix, third⟩ := take_sound second.rep second.count payload
    exact ⟨_, suffix, .many widthRange extraRange, first.trans (second.trans third)⟩

theorem readCount_sound {bitLimit types : Nat} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (read : BlockTypes.readCount bitLimit before = .ok (types, after)) :
    ∃ used suffix, CountWire used types ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold BlockTypes.readCount at read
  obtain ⟨⟨value, cursor⟩, actual, done⟩ := bind_ok read
  cases done
  obtain ⟨used, suffix, wire, advance⟩ := count_sound rep count actual
  have budget := advance.budget
  dsimp at budget
  exact ⟨used, suffix, wire, advance.split, advance.rep, advance.count, advance.offset, by omega⟩

theorem CountWire.bounds {bits : List Bool} {types : Nat} (wire : CountWire bits types) :
    1 ≤ types ∧ types ≤ 256 ∧ 1 ≤ bits.length ∧ bits.length ≤ 11 := by
  cases wire with
  | one => decide
  | @many width extra widthRange extraRange =>
    have powBound : 2 ^ width ≤ 128 :=
      Nat.pow_le_pow_right (by decide) (show width ≤ 7 by omega)
    simp only [List.length_append, List.length_cons, List.length_nil, natBits_length]
    omega

private theorem table_sound {alphabet : Nat} {before after : Cursor} {table : Table}
    {input : List Bool} (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : readTable alphabet before = .ok (table, after)) :
    ∃ used suffix, Huffman.Description.Wire alphabet used table ∧ Advance before after input used suffix := by
  unfold readTable at read
  obtain ⟨⟨found, cursor⟩, decoded, done⟩ := bind_ok read
  cases done
  obtain ⟨_, _, _, _, used, suffix, wire, split, nextRep, nextCount, offset, cap, _⟩ :=
    Huffman.Description.read_sound rep count (description_ok decoded)
  exact ⟨used, suffix, wire, split, nextRep, nextCount, offset, by dsimp at cap; simp [Cursor.advance]; omega⟩

private theorem code_sound {before after : Cursor} {table : Table} {symbol : Nat}
    {input : List Bool} (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : readCode table before = .ok (symbol, after)) :
    ∃ code width suffix, table.codeFor symbol = some (code, width) ∧ width ≤ 15 ∧
      Advance before after input (msbBits code width) suffix := by
  unfold readCode at read
  obtain ⟨⟨found, cursor⟩, decoded, done⟩ := bind_ok read
  cases done
  have decoded : table.readBounded before.remaining before.reader = .ok (symbol, cursor) := by
    cases actual : table.readBounded before.remaining before.reader
    · simp [actual, Except.mapError] at decoded
    · simpa [actual, Except.mapError] using decoded
  obtain ⟨code, width, suffix, assigned, bounded, cap, split, nextRep, nextCount, offset⟩ :=
    Table.readBounded_sound rep count decoded
  exact ⟨code, width, suffix, assigned, bounded, split, nextRep, nextCount,
    by simpa [Cursor.advance, msbBits_length] using offset,
    by simp [Cursor.advance, offset, msbBits_length]; omega⟩

private theorem initial_sound {before after : Cursor} {table : Table} {value : Nat}
    {input : List Bool} (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : readInitial table before = .ok (value, after)) :
    ∃ symbol code size base width extra suffix, value = base + extra ∧
      table.codeFor symbol = some (code, size) ∧ size ≤ 15 ∧ countCode symbol = some (base, width) ∧
      extra < 2 ^ width ∧ Advance before after input (msbBits code size ++ natBits extra width) suffix := by
  unfold readInitial at read
  obtain ⟨⟨symbol, cursor⟩, codeRead, next⟩ := bind_ok read
  cases assigned : countCode symbol with
  | none => simp [assigned, throw] at next
  | some entry =>
    obtain ⟨base, width⟩ := entry
    simp only [assigned] at next
    obtain ⟨⟨extra, final⟩, field, done⟩ := bind_ok next
    cases done
    obtain ⟨code, size, middle, codeWire, bound, first⟩ := code_sound rep count codeRead
    obtain ⟨fits, suffix, second⟩ := take_sound first.rep first.count field
    exact ⟨symbol, code, size, base, width, extra, suffix, rfl, codeWire, bound, assigned, fits,
      first.trans second⟩

theorem readLength_sound {table : Table} {bitLimit length : Nat} {before after : LSBReader}
    {input : List Bool} (rep : before.Rep input) (count : before.count < 8)
    (read : readLength table bitLimit before = .ok (length, after)) :
    ∃ used suffix, LengthWire table used length ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold readLength at read
  obtain ⟨⟨length, stop⟩, decoded, done⟩ := bind_ok read
  cases done
  obtain ⟨_, _, _, _, _, _, suffix, rfl, assigned, width, entry, extra, advance⟩ :=
    initial_sound rep count decoded
  have budget := advance.budget
  dsimp at budget
  exact ⟨_, suffix, .fields assigned width entry extra, advance.split, advance.rep, advance.count, advance.offset,
    by omega⟩

private theorem length_bounds {base width extra : Nat} {symbol : Nat}
    (entry : countCode symbol = some (base, width)) (extraBound : extra < 2 ^ width) :
    1 ≤ base + extra ∧ base + extra ≤ 16793840 := by
  have all : countCodes.all (fun row => 1 ≤ row.1 ∧ row.1 + 2 ^ row.2 ≤ 16793841) = true := by decide
  have bound := List.all_eq_true.mp all (base, width) (List.mem_of_getElem? entry)
  have bounds : 1 ≤ base ∧ base + 2 ^ width ≤ 16793841 := of_decide_eq_true bound
  obtain ⟨lower, upper⟩ := bounds
  omega

theorem LengthWire.bounds {table : Table} {bits : List Bool} {length : Nat}
    (wire : LengthWire table bits length) : 1 ≤ length ∧ length ≤ 16793840 := by
  cases wire with | fields _ _ entry extra => exact length_bounds entry extra

theorem CountWire.bits_of_one {bits : List Bool} {types : Nat}
    (wire : CountWire bits types) (one : types = 1) : bits = [false] := by
  cases wire with
  | one => rfl
  | @many width extra hw he => have := Nat.two_pow_pos width; omega

private theorem control_sound {before after : Cursor} {control : Control} {input : List Bool}
    (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : readControl before = .ok (control, after)) :
    ∃ used suffix, ControlWire used control ∧ Advance before after input used suffix := by
  unfold readControl at read
  obtain ⟨⟨types, cursor⟩, readTypes, next⟩ := bind_ok read
  obtain ⟨countBits, middle, countWire, first⟩ := count_sound rep count readTypes
  simp only [] at next
  split at next
  · rename_i one
    cases next
    rw [CountWire.bits_of_one countWire one] at first
    exact ⟨_, middle, .single, first⟩
  · rename_i multiple
    obtain ⟨⟨typeTable, typeCursor⟩, readTypeTable, next⟩ := bind_ok next
    obtain ⟨⟨countTable, countCursor⟩, readCountTable, next⟩ := bind_ok next
    obtain ⟨⟨initial, final⟩, readLength, done⟩ := bind_ok next
    cases done
    obtain ⟨typeBits, tail, typeWire, second⟩ := table_sound first.rep first.count readTypeTable
    obtain ⟨countTableBits, tail', tableWire, third⟩ := table_sound second.rep second.count readCountTable
    obtain ⟨symbol, code, size, base, width, extra, suffix, rfl, assigned, sizeCap, entry, extraCap, fourth⟩ :=
      initial_sound third.rep third.count readLength
    have range := (CountWire.bounds countWire).1
    exact ⟨_, suffix, .multiple (by omega) countWire typeWire tableWire assigned sizeCap entry extraCap,
      by simpa only [List.append_assoc] using ((first.trans second).trans third).trans fourth⟩

theorem read_sound {bitLimit : Nat} {before after : LSBReader} {input : List Bool} {controls : Controls}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read bitLimit before = .ok (controls, after)) :
    ∃ used suffix, Wire used controls ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold Formats.Compression.Brotli.BlockTypes.read at read
  obtain ⟨⟨literal, first⟩, literalRead, next⟩ := bind_ok read
  obtain ⟨⟨insertCopy, second⟩, insertRead, next⟩ := bind_ok next
  obtain ⟨⟨distance, third⟩, distanceRead, done⟩ := bind_ok next
  cases done
  obtain ⟨a, rest, literalWire, one⟩ := control_sound rep count literalRead
  obtain ⟨b, tail, insertWire, two⟩ := control_sound one.rep one.count insertRead
  obtain ⟨c, suffix, distanceWire, three⟩ := control_sound two.rep two.count distanceRead
  have both := one.trans (two.trans three)
  refine ⟨_, suffix, ⟨a, b, c, rfl, literalWire, insertWire, distanceWire⟩,
    by simpa only [List.append_assoc] using both.split, both.rep, both.count,
    by simpa only [List.append_assoc] using both.offset, ?_⟩
  have bound := both.budget
  dsimp at bound
  simpa only [List.append_assoc] using (show (a ++ (b ++ c)).length ≤ bitLimit by omega)

theorem ControlWire.bounds {bits : List Bool} {control : Control} (wire : ControlWire bits control) :
    1 ≤ control.typeCount ∧ control.typeCount ≤ 256 ∧
      match control with
      | .single => True
      | .multiple _ _ _ initial => 1 ≤ initial ∧ initial ≤ 16793840 := by
  cases wire with
  | single => decide
  | @multiple types base width symbol code size extra typeTable countTable countBits typeBits tableBits
      multi countWire _ _ _ _ entry extraBound =>
    have ⟨lower, upper, _⟩ := CountWire.bounds countWire
    exact ⟨lower, upper, length_bounds entry extraBound⟩

end Silmaril.Proofs.Formats.Compression.Brotli.BlockTypes
