module

public import Silmaril.Formats.Compression.Brotli.Distance.Defs
import Silmaril.Formats.Compression.Bits.Thms
import Silmaril.Formats.Compression.Brotli.Huffman.Description.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Distance

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Distance
open Silmaril.Formats.Compression.Brotli.Distance.Internal

private theorem bind_ok {α β : Type} {action : Except Distance.Error α} {next : α → Except Distance.Error β}
    {value : β} (read : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases read
  | ok result => exact ⟨result, rfl, read⟩

private theorem mapError_ok {ε α : Type} {action : Except ε α} {f : ε → Distance.Error} {value : α}
    (read : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases read <;> rfl

theorem extraWidth_bound {fields : ContextHeader.Fields} {code : Nat}
    (inAlphabet : code < fields.distanceAlphabet) : extraWidth fields code ≤ 24 := by
  unfold extraWidth
  split
  · decide
  · have positive := Nat.two_pow_pos fields.postfixBits.val
    change 0 < scale fields at positive
    change code < 16 + fields.direct + 48 * scale fields at inAlphabet
    have interval : code - 16 - fields.direct < 24 * (2 * scale fields) := by omega
    have ratio := (Nat.div_lt_iff_lt_mul (show 0 < 2 * scale fields by omega)).2 interval
    omega

private theorem route_sound {bounds : Bounds} {ring : Ring} {copyLength code extra distance : Nat}
    {result : Result} (read : route bounds ring copyLength code extra distance = .ok result) :
    result.code = code ∧ result.extra = extra ∧
      Resolved bounds ring copyLength code distance result.target result.ring := by
  unfold route at read
  split at read <;> try contradiction
  rename_i positive
  split at read
  · rename_i bounded
    cases read
    exact ⟨rfl, rfl, .back (by omega) bounded⟩
  · rename_i tooFar
    split at read <;> try contradiction
    rename_i lengthBound
    simp only [] at read
    split at read <;> try contradiction
    rename_i wordBound
    cases read
    exact ⟨rfl, rfl, .dictionary (by omega) (by omega) (by omega) (by omega)⟩

theorem Resolved.valid {bounds : Bounds} {ring after : Ring} {copyLength code distance : Nat}
    {target : Target} (resolved : Resolved bounds ring copyLength code distance target after) :
    target.distance = distance ∧ 0 < distance ∧
    match target with
    | .backReference _ =>
      distance ≤ bounds.maxBackward ∧ after = (if code = 0 then ring else ring.push distance)
    | .staticDictionary _ length wordId =>
      bounds.maxBackward < distance ∧ length = copyLength ∧ 4 ≤ length ∧ length ≤ 24 ∧
        wordId = distance - (bounds.maxBackward + 1) ∧ wordId < 121 * dictionaryWordCount length ∧ after = ring := by
  cases resolved
  · rename_i positive upper
    exact ⟨rfl, positive, upper, rfl⟩
  · rename_i strict lo hi word
    exact ⟨rfl, by omega, strict, rfl, lo, hi, rfl, word, rfl⟩

theorem Resolved.ring_positive {bounds : Bounds} {ring after : Ring} {copyLength code distance : Nat}
    {target : Target} (resolved : Resolved bounds ring copyLength code distance target after)
    (positive : ring.Positive) : after.Positive := by
  cases resolved
  · unfold nextRing
    split
    · exact positive
    · exact ⟨‹0 < distance›, positive.1, positive.2.1, positive.2.2.1⟩
  · exact positive

theorem Wire.bit_bound {header : CompressedHeader.Header} {command : Command.Value} {bounds : Bounds}
    {ring : Ring} {bits : List Bool} {result : Result} (wire : Wire header command bounds ring bits result) :
    bits.length ≤ 39 := by
  cases wire with
  | implicit => decide
  | explicit _ _ _ _ _ prefixCap range _ _ =>
    have extraCap := extraWidth_bound range
    simp only [List.length_append, msbBits_length, natBits_length]
    omega

theorem Wire.resolved {header : CompressedHeader.Header} {command : Command.Value} {bounds : Bounds}
    {ring : Ring} {bits : List Bool} {result : Result} (wire : Wire header command bounds ring bits result) :
    Resolved bounds ring command.copyLength result.code result.target.distance result.target result.ring := by
  cases wire with
  | implicit _ resolved =>
    exact (Resolved.valid resolved).1 ▸ resolved
  | explicit _ _ _ _ _ _ _ _ resolved =>
    exact (Resolved.valid resolved).1 ▸ resolved

private theorem take_sound {limit width extra : Nat} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (read : take limit width before = .ok (extra, after)) :
    width ≤ limit ∧ extra < 2 ^ width ∧ ∃ suffix, input = natBits extra width ++ suffix ∧
      after.Rep suffix ∧ after.count < 8 ∧ after.totalRead = before.totalRead + width := by
  unfold take at read
  split at read <;> try contradiction
  rename_i cap
  split at read <;> try contradiction
  rename_i value cursor actual
  cases read
  obtain ⟨suffix, split, rep', fits, offset, count'⟩ := LSBReader.readBits_sound rep count actual
  exact ⟨by omega, fits, suffix, split, rep', count' ▸ Nat.mod_lt _ (by decide), offset⟩

private theorem readExplicitAt_sound {blockType : Nat} {header : CompressedHeader.Header} {command : Command.Value} {bounds : Bounds}
    {ring : Ring} {bitLimit : Nat} {before after : LSBReader} {input : List Bool} {result : Result}
    (mode : command.distance = .explicit) (rep : before.Rep input) (count : before.count < 8)
    (read : readExplicitAt header blockType command.copyLength bounds ring bitLimit before = .ok (result, after)) :
    ∃ used suffix, WireAt header command bounds ring blockType used result ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold readExplicitAt at read
  split at read <;> try contradiction
  rename_i tree treeRead
  split at read <;> try contradiction
  rename_i table tableRead
  simp only [] at read
  split at read <;> try contradiction
  rename_i alphabet
  obtain ⟨⟨code, cursor⟩, codeRead, next⟩ := bind_ok read
  simp only [] at next
  split at next <;> try contradiction
  rename_i codeBound
  obtain ⟨⟨extra, final⟩, extraRead, next⟩ := bind_ok next
  obtain ⟨found, routed, done⟩ := bind_ok next
  cases done
  obtain ⟨prefixCode, prefixWidth, rest, assignment, widthCap, cap, split, rep', count', first⟩ :=
    Huffman.Description.Table.readBounded_sound rep count (mapError_ok codeRead)
  obtain ⟨extraCap, extraFits, suffix, split', outRep, outCount, second⟩ := take_sound rep' count' extraRead
  obtain ⟨codeEq, extraEq, resolved⟩ := route_sound routed
  rcases result with ⟨actualCode, actualExtra, target, finalRing⟩
  dsimp at codeEq extraEq
  subst actualCode
  subst actualExtra
  refine ⟨_, suffix, .explicit mode treeRead tableRead (by omega) assignment widthCap (by omega)
    extraFits resolved, ?_, outRep, outCount, ?_, ?_⟩
  · rw [split, split', List.append_assoc]
  · simp only [List.length_append, msbBits_length, natBits_length, first, second]
    omega
  · simp only [List.length_append, msbBits_length, natBits_length]
    omega

theorem readAt_sound {blockType : Nat} {header : CompressedHeader.Header} {command : Command.Value} {bounds : Bounds}
    {ring : Ring} {bitLimit : Nat} {before after : LSBReader} {input : List Bool} {result : Result}
    (rep : before.Rep input) (count : before.count < 8)
    (read : readAt header blockType command bounds ring bitLimit before =
      .ok (result, after)) :
    bounds.Valid ∧ 2 ≤ command.copyLength ∧
    (command.distance = .implicitZero → after = before) ∧
    ∃ used suffix, WireAt header command bounds ring blockType used result ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold readAt at read
  split at read <;> try contradiction
  rename_i window
  split at read <;> try contradiction
  rename_i length
  refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
  split at read
  · rename_i mode
    obtain ⟨found, routed, done⟩ := bind_ok read
    cases done
    obtain ⟨codeEq, extraEq, resolved⟩ := route_sound routed
    rcases result with ⟨actualCode, actualExtra, target, finalRing⟩
    dsimp at codeEq extraEq
    subst actualCode
    subst actualExtra
    exact ⟨fun _ => rfl, [], input, .implicit mode resolved, by simp, rep, count, by simp, by simp⟩
  · rename_i mode
    exact ⟨by simp [mode], readExplicitAt_sound mode rep count read⟩

theorem read_sound {header : CompressedHeader.Header} {command : Command.Value} {bounds : Bounds}
    {ring : Ring} {bitLimit : Nat} {before after : LSBReader} {input : List Bool} {result : Result}
    (rep : before.Rep input) (count : before.count < 8)
    (read : Silmaril.Formats.Compression.Brotli.Distance.read header command bounds ring bitLimit before =
      .ok (result, after)) :
    header.initial.controls.distance = .single ∧ bounds.Valid ∧ 2 ≤ command.copyLength ∧
    (command.distance = .implicitZero → after = before) ∧
    ∃ used suffix, Wire header command bounds ring used result ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold Silmaril.Formats.Compression.Brotli.Distance.read at read
  split at read <;> try contradiction
  rename_i single
  obtain ⟨valid, length, implicitCursor, used, suffix, wire, source⟩ := readAt_sound rep count read
  refine ⟨single, valid, length, implicitCursor, used, suffix, ?_, source⟩
  cases wire with
  | implicit mode resolved => exact .implicit mode resolved
  | explicit mode index table alphabet code width range extra resolved =>
    exact .explicit mode index table alphabet code width range extra resolved

theorem WireAt.resolved {header : CompressedHeader.Header} {command : Command.Value} {bounds : Bounds}
    {ring : Ring} {blockType : Nat} {bits : List Bool} {result : Result}
    (wire : WireAt header command bounds ring blockType bits result) :
    Resolved bounds ring command.copyLength result.code result.target.distance result.target result.ring := by
  cases wire with
  | implicit _ resolved => exact (Resolved.valid resolved).1 ▸ resolved
  | explicit _ _ _ _ _ _ _ _ resolved => exact (Resolved.valid resolved).1 ▸ resolved

end Silmaril.Proofs.Formats.Compression.Brotli.Distance
