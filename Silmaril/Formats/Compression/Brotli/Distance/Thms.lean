module

public import Silmaril.Formats.Compression.Brotli.Distance.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Distance.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Distance

theorem Ring.start_positive : Ring.start.Positive := by
  unfold Ring.start Ring.Positive
  decide

theorem extraWidth_bound {fields : ContextHeader.Fields} {code : Nat}
    (inAlphabet : code < fields.distanceAlphabet) : extraWidth fields code ≤ 24 :=
  Proofs.Formats.Compression.Brotli.Distance.extraWidth_bound inAlphabet

/-- A back reference fits both the produced stream and the window.
    A dictionary address instead fits the word and transform range. -/
theorem Resolved.valid {bounds : Bounds} {ring after : Ring} {copyLength code distance : Nat}
    {target : Target} (resolved : Resolved bounds ring copyLength code distance target after) :
    target.distance = distance ∧ 0 < distance ∧
    match target with
    | .backReference _ =>
      distance ≤ bounds.maxBackward ∧ after = (if code = 0 then ring else ring.push distance)
    | .staticDictionary _ length wordId =>
      bounds.maxBackward < distance ∧ length = copyLength ∧ 4 ≤ length ∧ length ≤ 24 ∧
        wordId = distance - (bounds.maxBackward + 1) ∧ wordId < 121 * dictionaryWordCount length ∧ after = ring :=
  Proofs.Formats.Compression.Brotli.Distance.Resolved.valid resolved

theorem Resolved.back_bounds {bounds : Bounds} {ring after : Ring} {copyLength code distance : Nat}
    (resolved : Resolved bounds ring copyLength code distance (.backReference distance) after) :
    0 < distance ∧ distance ≤ windowSize bounds.windowBits ∧ distance ≤ bounds.produced := by
  cases resolved with
  | back pos bound => exact ⟨pos, (Nat.le_min.mp bound).1, (Nat.le_min.mp bound).2⟩

theorem Resolved.ring_positive {bounds : Bounds} {ring after : Ring} {copyLength code distance : Nat}
    {target : Target} (resolved : Resolved bounds ring copyLength code distance target after)
    (positive : ring.Positive) : after.Positive :=
  Proofs.Formats.Compression.Brotli.Distance.Resolved.ring_positive resolved positive

theorem Wire.bit_bound {header : CompressedHeader.Header} {command : Command.Value} {bounds : Bounds}
    {ring : Ring} {bits : List Bool} {result : Result} (wire : Wire header command bounds ring bits result) :
    bits.length ≤ 39 :=
  Proofs.Formats.Compression.Brotli.Distance.Wire.bit_bound wire

theorem Wire.resolved {header : CompressedHeader.Header} {command : Command.Value} {bounds : Bounds}
    {ring : Ring} {bits : List Bool} {result : Result} (wire : Wire header command bounds ring bits result) :
    Resolved bounds ring command.copyLength result.code result.target.distance result.target result.ring :=
  Proofs.Formats.Compression.Brotli.Distance.Wire.resolved wire

/-- The original explicit tree code and exact extra bits leave the
    given suffix. An implicit distance leaves the entire cursor intact. -/
theorem read_sound {header : CompressedHeader.Header} {command : Command.Value} {bounds : Bounds}
    {ring : Ring} {bitLimit : Nat} {before after : LSBReader} {input : List Bool} {result : Result}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read header command bounds ring bitLimit before = .ok (result, after)) :
    header.initial.controls.distance = .single ∧ bounds.Valid ∧ 2 ≤ command.copyLength ∧
    (command.distance = .implicitZero → after = before) ∧
    ∃ used suffix, Wire header command bounds ring used result ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit :=
  Proofs.Formats.Compression.Brotli.Distance.read_sound rep count read

end Silmaril.Formats.Compression.Brotli.Distance
