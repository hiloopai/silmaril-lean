module

import Silmaril.Formats.Compression.Brotli.Execute.Thms
meta import Silmaril.Formats.Compression.Brotli.Execute.Defs

namespace Silmaril.Formats.Compression.Brotli.Execute

open Silmaril.Formats.Compression

private def cursor (bits : List Bool) : LSBReader :=
  let width := bits.length % 8
  let lead := LSBWriter.empty.writeBits (bits.take width)
  let bytes := LSBWriter.empty.writeBits (bits.drop width)
  ⟨lead.buffer, lead.count, bytes.bytes.data.toList, 11⟩

private def header (command : Nat) (fits : command < 704 := by decide) : CompressedHeader.Header :=
  ⟨⟨⟨.single, .single, .single⟩, ⟨0, 0, [.lsb6]⟩⟩, .implicit 64, .implicit 4,
    [.singleton 256 65 (by decide)], [.singleton 704 command fits], [.singleton 64 16 (by decide)]⟩

private def one : State := ⟨#[9], Distance.Ring.start⟩
private def two : State := ⟨#[1, 2], Distance.Ring.start⟩

private def observed (result : Except Error (Result × LSBReader)) :
    Option (List UInt8 × Distance.Ring × Option Nat × Nat × Option Bool) := do
  let (step, after) ← result.toOption
  pure (step.state.output.toList, step.state.ring, step.distance,
    after.totalRead, after.readBit |>.map Prod.fst)

private def errorOf (result : Except Error (Result × LSBReader)) : Option Error :=
  match result with
  | .error reason => some reason
  | .ok _ => none

#guard observed (read (header 131) ⟨18, 1, 5⟩ ⟨6, 1⟩ one (cursor [false, true])) =
  some ([9, 9, 9, 9, 9, 9], ⟨1, 4, 11, 15⟩, some 1, 12, some true)

#guard observed (read (header 131) ⟨18, 2, 5⟩ ⟨7, 1⟩ two (cursor [true, false])) =
  some ([1, 2, 1, 2, 1, 2, 1], ⟨2, 4, 11, 15⟩, some 2, 12, some false)

#guard observed (read (header 152) ⟨18, 0, 3⟩ ⟨3, 0⟩ State.start (cursor [true])) =
  some ([65, 65, 65], Distance.Ring.start, none, 11, some true)

#guard observed (read (header 152) ⟨18, 0, 5⟩ ⟨5, 1⟩ State.start (cursor [false])) =
  some ([65, 65, 65, 65, 65], ⟨1, 4, 11, 15⟩, some 1, 12, none)

#guard errorOf (read (header 131) ⟨18, 1, 4⟩ ⟨9, 1⟩ one (cursor [false])) = some .metaBlockExtent
#guard errorOf (read (header 131) ⟨18, 1, 5⟩ ⟨5, 1⟩ one (cursor [false])) = some .outputLimit
#guard errorOf (read (header 131) ⟨18, 1, 5⟩ ⟨6, 0⟩ one (cursor [false])) =
  some (.distance .extraBitLimit)
#guard errorOf (read (header 131) ⟨18, 1, 5⟩ ⟨6, 1⟩ one (cursor [])) =
  some (.distance .truncatedExtra)
#guard errorOf (read (header 131) ⟨18, 0, 1⟩ ⟨1, 1⟩ State.start (cursor [false])) =
  some (.unsupportedDictionary 1 5 0)
#guard errorOf (read (header 152) ⟨18, 0, 2⟩ ⟨9, 0⟩ State.start (cursor [])) =
  some (.literal .metaBlockExtent)
#guard errorOf (read (header 131) ⟨18, 2, 5⟩ ⟨9, 1⟩ one (cursor [false])) = some .metaBlockExtent
#guard errorOf (read (header 131) ⟨25, 1, 5⟩ ⟨9, 1⟩ one (cursor [false])) = some .window
#guard (⟨#[1, 5, 9], Distance.Ring.start⟩ : State).literalHistory = ⟨9, 5⟩
#guard one.literalHistory = ⟨9, 0⟩

#guard errorOf (read (header 131) ⟨18, 0, 1⟩ ⟨6, 1⟩ one (cursor [])) = some .metaBlockExtent
#guard (
  let parsed := header 131
  let initial := parsed.initial
  let block : BlockTypes.Control := .multiple 2 (.singleton 4 0 (by decide)) (.singleton 26 0 (by decide)) 1
  let controls := { initial.controls with distance := block }
  let multi := { parsed with initial := { initial with controls := controls } }
  errorOf (read multi ⟨18, 1, 5⟩ ⟨6, 1⟩ one (cursor [false]))) = some .blockTypes

end Silmaril.Formats.Compression.Brotli.Execute
