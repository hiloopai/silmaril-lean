module

public import Silmaril.Formats.Compression.Brotli.Stream.Defs
import Silmaril.Formats.Compression.Brotli.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Stream

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Internal (Cursor take take_sound alignZero_sound takeBody_sound emptyCursor)
open Silmaril.Formats.Compression.Brotli.Stream
open Silmaril.Formats.Compression.Brotli.Stream.Internal

theorem bind_ok {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {out : β} (read : (action >>= next) = .ok out) :
    ∃ value, action = .ok value ∧ next value = .ok out := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

theorem map_ok {ε δ α : Type} {action : Except ε α} {error : ε → δ}
    {out : α} (read : action.mapError error = .ok out) : action = .ok out := by
  cases action <;> cases read
  rfl

theorem bind_mapped_ok {ε δ α β : Type} {action : Except ε α} {next : α → Except δ β}
    {error : ε → δ} {out : β} (read : (action.mapError error >>= next) = .ok out) :
    ∃ value, action = .ok value ∧ next value = .ok out := by
  obtain ⟨value, response, rest⟩ := bind_ok read
  exact ⟨value, map_ok response, rest⟩

theorem withinBits_ok {limits : Stream.Limits} {after : LSBReader}
    (read : withinBits limits after = .ok ()) : after.totalRead ≤ limits.bits := by
  unfold withinBits at read
  split at read <;> simp_all

theorem bytes_length (bytes : List UInt8) : (bytesBits bytes).length = 8 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    simp only [bytesBits, List.flatMap_cons, List.length_append, natBits_length, List.length_cons] at *
    omega

theorem cursor_advance {before after : LSBReader} {input used suffix : List Bool}
    (cursor : Cursor before input) (split : input = used ++ suffix)
    (rep : after.Rep suffix) (count : after.count < 8)
    (position : after.totalRead = before.totalRead + used.length) : Cursor after suffix := by
  refine ⟨rep, count, ?_⟩
  have beforeShape := congrArg List.length cursor.1.2
  have afterShape := congrArg List.length rep.2
  simp only [List.length_append, natBits_length, bytes_length] at beforeShape afterShape
  rw [split, List.length_append] at beforeShape
  have boundary := cursor.2.2
  omega

private theorem readFlags_sound {before after : LSBReader} {input : List Bool} {flags : Option Bool}
    (cursor : Cursor before input) (read : readFlags before = .ok (flags, after)) :
    let code := flags.elim [true, true] lastBits
    ∃ suffix, input = code ++ suffix ∧ Cursor after suffix ∧
      after.totalRead = before.totalRead + code.length := by
  unfold readFlags at read
  obtain ⟨⟨last, reader⟩, parsed, read⟩ := bind_ok read
  dsimp only at read
  obtain ⟨tail, bits, next, lastBound, position⟩ := take_sound cursor parsed
  split at read
  · rename_i notLast
    cases read
    rw [bits, notLast]
    exact ⟨tail, rfl, next, position⟩
  · have lastOne : last = 1 := by omega
    obtain ⟨⟨empty, stop⟩, parsed, read⟩ := bind_ok read
    obtain ⟨suffix, emptyBits, stopCursor, emptyBound, stopPos⟩ := take_sound next parsed
    dsimp only at read
    split at read
    · rename_i notEmpty
      cases read
      rw [bits, emptyBits, lastOne, notEmpty]
      exact ⟨suffix, rfl, stopCursor, by change _ = before.totalRead + 2; omega⟩
    · have emptyOne : empty = 1 := by omega
      cases read
      rw [bits, emptyBits, lastOne, emptyOne]
      exact ⟨suffix, rfl, stopCursor, by change _ = before.totalRead + 2; omega⟩

private theorem readLength_sound {selector : Nat} {before after : LSBReader} {input : List Bool} {length : RawLength}
    (cursor : Cursor before input) (bound : selector < 3) (read : readLength selector before = .ok (length, after)) :
    ∃ tail, length.selector = selector ∧ length.Valid ∧ input = natBits length.minusOne length.width ++ tail ∧
      Cursor after tail ∧ after.totalRead = before.totalRead + length.width := by
  unfold readLength at read
  obtain ⟨⟨value, reader⟩, parsed, read⟩ := bind_ok read
  dsimp only at read
  obtain ⟨tail, bits, next, fits, position⟩ := take_sound cursor parsed
  split at read
  · contradiction
  · rename_i canonical
    cases read
    refine ⟨tail, rfl, ⟨bound, fits, ?_⟩, bits, next, position⟩
    change ¬ (selector ≠ 0 ∧ value < 2 ^ (4 * (4 + selector) - 4)) at canonical
    change selector = 0 ∨ 2 ^ (4 * (4 + selector) - 4) ≤ value
    omega

private theorem readMetadata_sound {before after : LSBReader} {input : List Bool} {length : MetadataLength}
    (cursor : Cursor before input) (read : readMetadata before = .ok (length, after)) :
    ∃ tail, length.Valid ∧
      input = [false] ++ natBits length.selector 2 ++ natBits length.minusOne length.width ++ tail ∧
      Cursor after tail ∧ after.totalRead = before.totalRead + 1 + 2 + length.width := by
  unfold readMetadata at read
  obtain ⟨⟨reserved, reader⟩, parsed, read⟩ := bind_ok read
  dsimp only at read
  obtain ⟨tail, bits, next, _, pos⟩ := take_sound cursor parsed
  split at read
  · contradiction
  · have reservedZero : reserved = 0 := by omega
    obtain ⟨⟨selector, afterSelector⟩, parsed, read⟩ := bind_ok read
    obtain ⟨tail₂, bits₂, next₂, bound, pos₂⟩ := take_sound next parsed
    obtain ⟨⟨value, stop⟩, parsed, read⟩ := bind_ok read
    dsimp only at read
    obtain ⟨tail₃, bits₃, next₃, valueBound, pos₃⟩ := take_sound next₂ parsed
    split at read
    · contradiction
    · rename_i canonical
      cases read
      refine ⟨tail₃, ⟨bound, valueBound, ?_⟩, ?_, next₃, ?_⟩
      · change ¬ (1 < selector ∧ value < 2 ^ (8 * selector - 8)) at canonical
        change selector ≤ 1 ∨ 2 ^ (8 * selector - 8) ≤ value
        omega
      · rw [bits, bits₂, bits₃, reservedZero]
        simp only [MetadataLength.width, List.append_assoc]
        rfl
      · simp only [MetadataLength.width]
        omega

theorem readHeader_sound {before after : LSBReader} {bits : List Bool} {header : Header}
    (cursor : Cursor before bits) (read : readHeader before = .ok (header, after)) :
    ∃ tail, header.Valid ∧ bits = header.bits ++ tail ∧ Cursor after tail ∧
      after.totalRead = before.totalRead + header.bits.length := by
  unfold readHeader at read
  obtain ⟨⟨flags, reader⟩, parsed, read⟩ := bind_ok read
  obtain ⟨tail, flagBits, next, flagPos⟩ := readFlags_sound cursor parsed
  cases flags with
  | none =>
    cases read
    exact ⟨tail, trivial, flagBits, next, flagPos⟩
  | some last =>
    dsimp only [Option.elim] at flagBits flagPos
    dsimp only at read
    obtain ⟨⟨selector, afterSelector⟩, parsed, read⟩ := bind_ok read
    obtain ⟨tail₂, selectorBits, next₂, bound, selectorPos⟩ := take_sound next parsed
    dsimp only at read
    split at read
    · rename_i metadata
      obtain ⟨⟨length, stop⟩, parsed, read⟩ := bind_ok read
      obtain ⟨suffix, valid, bodyBits, stopCursor, stopPos⟩ := readMetadata_sound next₂ parsed
      cases read
      refine ⟨suffix, valid, ?_, stopCursor, ?_⟩
      · rw [flagBits, selectorBits, metadata, bodyBits]
        simp only [Header.bits, List.append_assoc]
        rfl
      · simp only [Header.bits, List.length_append, natBits_length, List.length_cons, List.length_nil]
        omega
    · obtain ⟨⟨length, afterLength⟩, parsed, read⟩ := bind_ok read
      obtain ⟨tail₃, selection, valid, bodyBits, next₃, lengthPos⟩ :=
        readLength_sound next₂ (by omega) parsed
      dsimp only at read
      cases last with
      | true =>
        cases read
        refine ⟨tail₃, valid, ?_, next₃, ?_⟩
        · rw [flagBits, selectorBits, bodyBits, ← selection]
          simp [Header.bits, List.append_assoc]
        · simp only [Header.bits, lastBits, ite_true, List.length_append, natBits_length,
            List.length_cons, List.length_nil]
          simp [lastBits] at flagPos
          omega
      | false =>
        obtain ⟨⟨raw, stop⟩, parsed, read⟩ := bind_ok read
        obtain ⟨suffix, rawBits, stopCursor, rawBound, stopPos⟩ := take_sound next₃ parsed
        dsimp only at read
        cases read
        by_cases zero : raw = 0
        · simp only [zero, ite_true]
          refine ⟨suffix, valid, ?_, stopCursor, ?_⟩
          · rw [flagBits, selectorBits, bodyBits, rawBits, ← selection, zero]
            simp only [Header.bits, Bool.false_eq_true, ite_false, List.append_assoc, lastBits]
            rfl
          · simp [Header.bits, lastBits, natBits_length] at flagPos ⊢
            omega
        · have one : raw = 1 := by omega
          simp only [zero, ite_false]
          refine ⟨suffix, valid, ?_, stopCursor, ?_⟩
          · rw [flagBits, selectorBits, bodyBits, rawBits, ← selection, one]
            simp only [Header.bits, MetaHeader.bits, List.append_assoc, lastBits, Bool.false_eq_true, ite_false]
            rfl
          · simp [Header.bits, MetaHeader.bits, lastBits, natBits_length] at flagPos ⊢
            omega

theorem alignedBody_sound {limits : Stream.Limits} {size : Nat} {before after : LSBReader}
    {input : List Bool} {body : List UInt8} (cursor : Cursor before input)
    (read : alignedBody limits size before = .ok (body, after)) :
    ∃ suffix, body.length = size ∧ input = (padding before.totalRead ++ bytesBits body) ++ suffix ∧
      Cursor after suffix ∧ after.totalRead = before.totalRead + (padding before.totalRead ++ bytesBits body).length ∧
      after.totalRead ≤ limits.bits := by
  unfold alignedBody at read
  obtain ⟨aligned, alignedRead, read⟩ := bind_mapped_ok read
  obtain ⟨tail, fill, alignedCursor, count, position⟩ := alignZero_sound cursor alignedRead
  split at read
  · contradiction
  rename_i fits
  obtain ⟨suffix, length, bodyBits, next, stop⟩ := takeBody_sound alignedCursor count (map_ok read)
  refine ⟨suffix, length, ?_, next, ?_, ?_⟩
  · simp [fill, bodyBits, List.append_assoc]
  · simp [List.length_append, bytes_length, stop, position, Nat.add_assoc]
  · omega

theorem finish_sound {limits : Stream.Limits} {before after : LSBReader} {input : List Bool}
    (cursor : Cursor before input) (read : finish limits before = .ok after) :
    input = padding before.totalRead ∧
      after.totalRead = before.totalRead + input.length ∧ after.totalRead ≤ limits.bits := by
  unfold finish at read
  obtain ⟨aligned, alignedRead, read⟩ := bind_mapped_ok read
  obtain ⟨tail, fill, alignedCursor, count, position⟩ := alignZero_sound cursor alignedRead
  obtain ⟨⟨⟩, within, read⟩ := bind_ok read
  split at read
  · rename_i finished
    cases read
    have nil := emptyCursor alignedCursor count (by simpa using finished)
    rw [nil, List.append_nil] at fill
    exact ⟨fill, by rwa [fill], withinBits_ok within⟩
  · contradiction

end Silmaril.Proofs.Formats.Compression.Brotli.Stream
