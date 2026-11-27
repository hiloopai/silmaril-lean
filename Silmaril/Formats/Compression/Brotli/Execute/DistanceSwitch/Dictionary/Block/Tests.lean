module

import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.Thms
import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Defs
import Batteries.Data.Except
import Init.Data.Option.Basic
meta import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Defs
meta import Batteries.Data.Except
meta import Init.Data.Option.Basic

namespace Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary

open Silmaril.Formats.Compression

-- Assembled RFC control, independently accepted by the pinned native decoder.
-- Base word "time" first uses omit-first-9 and then omit-last-1 + "ing ".
private def wire : List UInt8 := [0xc2, 0, 0x80, 0x28, 0x0a, 0, 0, 0x11, 0x14, 0x82, 0xc4, 0x4a, 0x80, 0x85, 0x80, 0]

private abbrev Observation := List UInt8 × Nat × Distance.Ring × List Nat × Option Nat

private def expect (actual : Option (Except BlockError Observation)) (expected : Except BlockError Observation) : Bool :=
  match actual, expected with
  | some (.ok found), .ok value => decide (found = value)
  | some (.error found), .error reason => decide (found = reason)
  | _, _ => false

private def check (commands : Nat) (output := 7) (bits := 31) (input := wire)
    (initial := Execute.State.start) (size : Option Nat := none) :=
  let decoded := do
    let (window, next) ← (Brotli.Internal.readWindow (Brotli.Internal.start input)).toOption
    let (.compressed true length, tables) ← (Stream.Internal.readHeader next).toOption | none
    let (header, payload) ← (CompressedHeader.read ⟨17408, 768, 128⟩ tables).toOption
    some (readBlock header window (size.getD length.size) commands ⟨output, bits⟩ initial payload)
  decoded.map (Except.map fun (state, after) =>
      let nextByte := (after.readBits ((8 - after.totalRead % 8) % 8) >>= fun (_, aligned) =>
        aligned.readBits 8).map Prod.fst
      (state.execution.output.toList, after.totalRead, state.execution.ring,
        [state.runs.literal.remaining, state.runs.insertCopy.remaining, state.runs.distance.remaining], nextByte))

#guard expect (check 2 (input := wire ++ [0xa5]))
  (.ok ([116, 105, 109, 105, 110, 103, 32], 123, Distance.Ring.start,
    [16777216, 16777214, 0], some 0xa5))
#guard expect (check 1) (.error (.fuel 1 106))
#guard expect (check 0) (.error (.fuel 0 92))
#guard expect (check 1 (bits := 14)) (.error (.fuel 1 106))
#guard expect (check 2 (bits := 30)) (.error (.command 1 (.distance 109 .extraBitLimit)))
#guard expect (check 2 (output := 6)) (.error (.command 1 (.copy 123 .outputLimit)))
#guard expect (check 2 (output := 6) (size := some 6)) (.error (.command 1 (.copy 123 .metaBlockExtent)))
#guard expect (check 2 (input := wire.dropLast)) (.error (.command 1 (.distance 109 .truncatedExtra)))
#guard expect (check 0 (output := 0) (initial := ⟨#[0x78], Distance.Ring.start⟩)) (.error (.initialOutput 92))
#guard expect (check 0 (output := 0) (bits := 0) (size := some 0))
  (.ok ([], 92, Distance.Ring.start, [16777216, 16777216, 1], some 128))
-- Increase each encoded distance by one for the inherited history byte.
private def withHistory : List UInt8 := wire.set 11 0x5a |>.set 13 0xa5

#guard expect (check 2 (output := 8) (input := withHistory) (initial := ⟨#[120], ⟨9, 8, 7, 6⟩⟩))
  (.ok ([120, 116, 105, 109, 105, 110, 103, 32], 123, ⟨9, 8, 7, 6⟩,
    [16777216, 16777214, 0], none))
#guard Stream.DistanceSwitch.decode ⟨16, 7, windowSize 16, 128, 1, 17408, 768⟩ wire =
  .error (.block 0 (.command 0 (.copy 106 (.unsupportedDictionary 55297 4 55296))))

end Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary
