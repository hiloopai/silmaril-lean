module

public import Silmaril.Formats.Compression.Brotli.Defs
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Internal

private theorem bind_ok {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {out : β} (read : (action >>= next) = .ok out) :
    ∃ value, action = .ok value ∧ next value = .ok out := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

theorem take_sound {width value : Nat} {reader next : LSBReader} {bits : List Bool}
    (cursor : Cursor reader bits) (read : take reader width = .ok (value, next)) :
    ∃ tail, bits = natBits value width ++ tail ∧ Cursor next tail ∧
      value < 2 ^ width ∧ next.totalRead = reader.totalRead + width := by
  have fields : reader.readBits width = some (value, next) := by
    unfold take at read
    split at read
    · rename_i pair parsed
      cases read
      exact parsed
    · contradiction
  obtain ⟨tail, split, rep, bound, pos, count⟩ := LSBReader.readBits_sound cursor.1 cursor.2.1 fields
  have previous := cursor.2.2
  refine ⟨tail, split, ⟨rep, count ▸ Nat.mod_lt _ (by decide), ?_⟩, bound, pos⟩
  rw [pos, count]
  omega

theorem readWindow_sound {reader next : LSBReader} {bits : List Bool} {wbits : Nat}
    (cursor : Cursor reader bits) (read : readWindow reader = .ok (wbits, next)) :
    ∃ code tail, WindowWire wbits code ∧ bits = code ++ tail ∧ Cursor next tail ∧
      next.totalRead = reader.totalRead + code.length := by
  unfold readWindow at read
  obtain ⟨⟨first, afterFirst⟩, firstRead, read⟩ := bind_ok read
  dsimp only at read
  obtain ⟨tail₁, bits₁, cur₁, firstBound, pos₁⟩ := take_sound cursor firstRead
  split at read
  · rename_i zero
    cases read
    subst first
    exact ⟨[false], tail₁, .sixteen, bits₁, cur₁, pos₁⟩
  · rename_i nonzero
    have firstOne : first = 1 := by omega
    obtain ⟨⟨short, afterShort⟩, shortRead, read⟩ := bind_ok read
    dsimp only at read
    obtain ⟨tail₂, bits₂, cur₂, shortBound, pos₂⟩ := take_sound cur₁ shortRead
    split at read
    · rename_i present
      cases read
      refine ⟨[true] ++ natBits short 3, tail₂, .short (Nat.pos_of_ne_zero present) shortBound,
        ?_, cur₂, ?_⟩
      · rw [bits₁, firstOne, bits₂]
        rfl
      · simp only [List.length_append, natBits_length, List.length_cons, List.length_nil]
        omega
    · rename_i shortZero
      have shortZero : short = 0 := by omega
      obtain ⟨⟨long, afterLong⟩, longRead, read⟩ := bind_ok read
      dsimp only at read
      obtain ⟨tail₃, bits₃, cur₃, longBound, pos₃⟩ := take_sound cur₂ longRead
      have splitBits :
          bits = ([true] ++ natBits 0 3 ++ natBits long 3) ++ tail₃ := by
        rw [bits₁, firstOne, bits₂, shortZero, bits₃]
        simp only [List.append_assoc]
        rfl
      have advanced : afterLong.totalRead = reader.totalRead + ([true] ++ natBits 0 3 ++ natBits long 3).length := by
        simp only [List.length_append, natBits_length, List.length_cons, List.length_nil]
        omega
      split at read
      · rename_i zero
        cases read
        subst long
        exact ⟨_, tail₃, .seventeen, splitBits, cur₃, advanced⟩
      · rename_i nonzeroLong
        split at read
        · contradiction
        rename_i longNotOne
        cases read
        exact ⟨_, tail₃, .long (by omega) longBound, splitBits, cur₃, advanced⟩

private theorem readLength_sound {reader next : LSBReader} {bits : List Bool} {raw : RawLength}
    (cursor : Cursor reader bits) (read : readLength reader = .ok (raw, next)) :
    ∃ tail, raw.Valid ∧ bits = natBits raw.selector 2 ++ natBits raw.minusOne raw.width ++ tail ∧
      Cursor next tail ∧ next.totalRead = reader.totalRead + 2 + raw.width := by
  unfold readLength at read
  obtain ⟨⟨selector, afterSelector⟩, selectorRead, read⟩ := bind_ok read
  dsimp only at read
  obtain ⟨tail₁, bits₁, cur₁, selectorBound, pos₁⟩ := take_sound cursor selectorRead
  split at read
  · obtain ⟨⟨_, _⟩, _, read⟩ := bind_ok read
    dsimp only at read
    split at read <;> contradiction
  · rename_i regular
    obtain ⟨⟨value, afterValue⟩, valueRead, read⟩ := bind_ok read
    dsimp only at read
    obtain ⟨tail₂, bits₂, cur₂, valueBound, pos₂⟩ := take_sound cur₁ valueRead
    split at read
    · contradiction
    rename_i canonical
    cases read
    refine ⟨tail₂, ⟨by change selector < 3; omega, valueBound, ?_⟩, ?_, cur₂, ?_⟩
    · change selector = 0 ∨ 2 ^ (4 * (4 + selector) - 4) ≤ value
      change ¬ (selector ≠ 0 ∧ value < 2 ^ (4 * (4 + selector) - 4)) at canonical
      omega
    · rw [bits₁, bits₂, List.append_assoc]
      rfl
    · rw [pos₂, pos₁]
      rfl

private theorem readHeader_sound {reader next : LSBReader} {bits : List Bool} {header : MetaHeader}
    (cursor : Cursor reader bits) (read : readHeader reader = .ok (header, next)) :
    ∃ tail, header.Valid ∧ bits = header.bits ++ tail ∧ Cursor next tail ∧
      next.totalRead = reader.totalRead + header.bits.length := by
  unfold readHeader at read
  obtain ⟨⟨last, afterLast⟩, lastRead, read⟩ := bind_ok read
  dsimp only at read
  obtain ⟨tail₁, bits₁, cur₁, lastBound, pos₁⟩ := take_sound cursor lastRead
  split at read
  · rename_i notLast
    obtain ⟨⟨length, afterLength⟩, lengthRead, read⟩ := bind_ok read
    dsimp only at read
    obtain ⟨tail₂, valid, bits₂, cur₂, pos₂⟩ := readLength_sound cur₁ lengthRead
    obtain ⟨⟨raw, afterRaw⟩, rawRead, read⟩ := bind_ok read
    dsimp only at read
    obtain ⟨tail₃, bits₃, cur₃, _, pos₃⟩ := take_sound cur₂ rawRead
    split at read
    · rename_i rawBit
      cases read
      refine ⟨tail₃, valid, ?_, cur₃, ?_⟩
      · rw [bits₁, notLast, bits₂, bits₃, rawBit]
        simp only [MetaHeader.bits, List.append_assoc]
        rfl
      · simp only [MetaHeader.bits, List.length_append, natBits_length, List.length_cons, List.length_nil]
        omega
    · contradiction
  · rename_i nonzero
    have lastOne : last = 1 := by omega
    obtain ⟨⟨empty, afterEmpty⟩, emptyRead, read⟩ := bind_ok read
    dsimp only at read
    obtain ⟨tail₂, bits₂, cur₂, _, pos₂⟩ := take_sound cur₁ emptyRead
    split at read
    · rename_i emptyBit
      cases read
      refine ⟨tail₂, trivial, ?_, cur₂, ?_⟩
      · rw [bits₁, lastOne, bits₂, emptyBit]
        rfl
      · change _ = reader.totalRead + 2
        omega
    · obtain ⟨_, _, read⟩ := bind_ok read
      contradiction

theorem alignZero_sound {reader aligned : LSBReader} {bits : List Bool}
    (cursor : Cursor reader bits) (read : alignZero reader = .ok aligned) :
    ∃ tail, bits = padding reader.totalRead ++ tail ∧ Cursor aligned tail ∧ aligned.count = 0 ∧
      aligned.totalRead = reader.totalRead + (padding reader.totalRead).length := by
  unfold alignZero at read
  split at read
  · rename_i zero
    cases read
    obtain ⟨⟨_, shape⟩, count, boundary⟩ := cursor
    have width : (8 - reader.totalRead % 8) % 8 = reader.count := by omega
    refine ⟨bytesBits reader.input, ?_, ⟨?_, ?_, ?_⟩, rfl, ?_⟩
    · rw [← shape, zero, natBits_zero_fill]
      simp only [padding, width]
    · simp [LSBReader.Rep, LSBReader.alignToByte, natBits]
    · simp [LSBReader.alignToByte]
    · exact boundary
    · simp [LSBReader.alignToByte, padding, width]
  · contradiction

theorem takeBody_sound {size : Nat} {reader next : LSBReader} {bits : List Bool} {body : List UInt8}
    (cursor : Cursor reader bits) (aligned : reader.count = 0)
    (read : takeBody size reader = .ok (body, next)) :
    ∃ tail, body.length = size ∧ bits = bytesBits body ++ tail ∧ Cursor next tail ∧
      next.totalRead = reader.totalRead + 8 * body.length := by
  simp only [takeBody, List.splitAt_eq] at read
  split at read
  · rename_i extent
    obtain ⟨⟨bufferBound, shape⟩, _, boundary⟩ := cursor
    cases read
    refine ⟨bytesBits (reader.input.drop size), extent, ?_, ⟨?_, by simp [aligned], ?_⟩, ?_⟩
    · rw [aligned, natBits, List.nil_append] at shape
      have cut := congrArg bytesBits (List.take_append_drop size reader.input)
      exact shape.symm.trans (by
        simpa only [bytesBits, List.flatMap_append] using cut.symm)
    · have small : reader.buffer < 1 := by simpa [aligned] using bufferBound
      have bufferZero : reader.buffer = 0 := by omega
      simp [LSBReader.Rep, bufferZero, aligned, natBits]
    · simp only at boundary ⊢
      omega
    · simp [extent]
  · contradiction

theorem emptyCursor {reader : LSBReader} {bits : List Bool}
    (cursor : Cursor reader bits) (count : reader.count = 0) (input : reader.input = []) : bits = [] := by
  have shape := cursor.1.2
  rw [count, input] at shape
  simpa [natBits, bytesBits] using shape.symm

private theorem readBlocks_sound {fuel remaining : Nat} {reader : LSBReader} {bits : List Bool}
    {acc returned : List (List UInt8)} (cursor : Cursor reader bits)
    (read : readBlocks fuel remaining reader acc = .ok returned) :
    ∃ chunks steps, BlocksWire reader.totalRead bits chunks steps ∧
      chunks.flatten.length ≤ remaining ∧ steps ≤ fuel ∧ returned = acc.reverse ++ chunks := by
  induction fuel generalizing remaining reader bits acc returned with
  | zero => contradiction
  | succ fuel ih =>
    simp only [readBlocks] at read
    obtain ⟨⟨header, afterHeader⟩, headRead, read⟩ := bind_ok read
    dsimp only at read
    obtain ⟨headTail, valid, headBits, headCursor, headPosition⟩ := readHeader_sound cursor headRead
    obtain ⟨aligned, alignRead, read⟩ := bind_ok read
    obtain ⟨alignTail, fillBits, alignCursor, alignCount, alignPosition⟩ := alignZero_sound headCursor alignRead
    cases header with
    | terminal =>
      dsimp only at read
      split at read
      · rename_i finished
        cases read
        have inputEmpty : aligned.input = [] := by simpa using finished
        have noTail := emptyCursor alignCursor alignCount inputEmpty
        rw [headBits, fillBits, noTail, List.append_nil, headPosition]
        exact ⟨[], 1, .terminal, Nat.zero_le _, by omega, by simp⟩
      · contradiction
    | raw length =>
      dsimp only at read
      split at read
      · contradiction
      rename_i within
      obtain ⟨⟨body, next⟩, bodyRead, read⟩ := bind_ok read
      dsimp only at read
      obtain ⟨tail, size, bodyBits, nextCursor, nextPosition⟩ := takeBody_sound alignCursor alignCount bodyRead
      obtain ⟨chunks, steps, chain, budget, stepsFit, order⟩ := ih nextCursor read
      have position : next.totalRead = bodyStart reader.totalRead (.raw length) + 8 * body.length := by
        rw [nextPosition, alignPosition, headPosition]
        rfl
      rw [position] at chain
      rw [headBits, fillBits, bodyBits, headPosition]
      refine ⟨body :: chunks, steps + 1, ?_, ?_, by omega, ?_⟩
      · simpa only [List.append_assoc] using BlocksWire.raw valid size chain
      · simp only [List.flatten_cons, List.length_append]
        change ¬ remaining < length.size at within
        omega
      · simpa [List.reverse_cons, List.append_assoc] using order

theorem decode_sound {limits : Limits} {input output : List UInt8}
    (read : decode limits input = .ok output) :
    ∃ wbits steps, StreamWire input output wbits steps ∧ input.length ≤ limits.input ∧
      output.length ≤ limits.output ∧ windowSize wbits ≤ limits.window ∧ steps ≤ limits.steps := by
  unfold decode at read
  split at read
  · contradiction
  rename_i inputFits
  obtain ⟨⟨wbits, reader⟩, windowRead, read⟩ := bind_ok read
  dsimp only at read
  have cursor : Cursor (start input) (bytesBits input) := by
    simp [Cursor, start, LSBReader.Rep, natBits]
  obtain ⟨code, tail, window, split, nextCursor, position⟩ := readWindow_sound cursor windowRead
  split at read
  · contradiction
  rename_i windowFits
  obtain ⟨chunks, blocksRead, read⟩ := bind_ok read
  obtain ⟨wireChunks, steps, chain, outputFits, stepFits, order⟩ := readBlocks_sound nextCursor blocksRead
  have pos : reader.totalRead = code.length := by simpa [start] using position
  rw [pos] at chain
  cases read
  have shape : chunks = wireChunks := by simpa using order
  subst chunks
  exact ⟨wbits, steps, ⟨code, tail, wireChunks, window, split, chain, rfl⟩,
    Nat.le_of_not_gt inputFits, outputFits, Nat.le_of_not_gt windowFits, stepFits⟩

end Silmaril.Proofs.Formats.Compression.Brotli
