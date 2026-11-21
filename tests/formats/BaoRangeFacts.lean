module

import Silmaril.Formats.Blake3Cas.RangeFacts.Grouped.Thms
import Silmaril.Formats.Blake3Cas.RangeFacts.SingleChunk.Thms
meta import Silmaril.Formats.Blake3Cas.RangeFacts.Thms
meta import Silmaril.Formats.Blake3Cas.RangeFacts.Grouped.Defs
meta import Silmaril.Formats.Blake3Cas.RangeFacts.SingleChunk.Defs
meta import Silmaril.Formats.Iroh.Vectors

open Silmaril.Crypto.Blake3
open Silmaril.Formats
open Silmaril.Formats.Blake3Cas
open Silmaril.Formats.Blake3Cas.RangeFacts

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

set_option maxRecDepth 8192

#eval do
  let (root, combined, outboard, interior, tail) := Iroh.Vectors.baoFixtures
  let cap := 4096
  let some middle := decodeSlice? cap root (.bounded 1024 1) interior |
    throw (IO.userError "interior slice")
  require "interior frame complete without object EOF" (middle.done.bytes == [0] && middle.eof.isNone)
  let some right := decodeSlice? cap root (.toEnd 2048) tail | throw (IO.userError "tail slice")
  let some suffix := right.suffix? | throw (IO.userError "authenticated suffix")
  require "open request yields true suffix" (suffix.stop == 2049 && suffix.bytes == [0])
  let some spanAtEnd := middle.doneAt? suffix.stop | throw (IO.userError "matching separate extent")
  require "interior range sealed using a separate response" ((spanAtEnd.seal suffix.extent).bytes == [0])
  let bogus := Bao.putLE64 2050 ++ interior.drop 8
  let some staged := decodeSlice? cap root (.bounded 1024 1) bogus | throw (IO.userError "false header staged")
  require "even complete false-header frame cannot seal against real extent"
    (staged.done.bytes == [0] && staged.eof.isNone && (staged.doneAt? suffix.stop).isNone)
  require "open request cannot be satisfied by an interior-only slice"
    (decodeSlice? cap root (.toEnd 1024) interior).isNone
  require "false header on the actual edge is rejected"
    (decodeSlice? cap root (.toEnd 2048) (Bao.putLE64 2050 ++ tail.drop 8 ++ [0])).isNone
  require "empty suffix at EOF"
    (((decodeSlice? cap root (.toEnd 2049) tail).bind Response.suffix?).map Suffix.bytes == some [])
  require "empty bounded slice does not assert EOF"
    ((decodeSlice? cap root (.bounded 1024 0) interior).map
      (fun (response : Response root (.bounded 1024 0)) => (response.done.bytes, response.eof.isSome)) == some ([], false))
  require "past EOF is not empty suffix" (decodeSlice? cap root (.toEnd 2050) tail).isNone
  let some all := (decodeCombined? cap root (.toEnd 0) combined).bind Response.suffix? |
    throw (IO.userError "whole object")
  let some first := all.bounded.slice? 1023 1025 | throw (IO.userError "across two chunks")
  let some last := (decodeSlice? cap root (.toEnd 2048) tail).bind Response.suffix? |
    throw (IO.userError "missing tail")
  let left : Bounded root 1023 2048 := first
  require "compose adjacent facts at the same digest" ((left.prependSuffix last).bytes == List.replicate 1026 0)
  require "outboard exact range across boundary"
    ((decodeOutboard? cap root (.bounded 1023 2) outboard (List.replicate 2049 0)).map
      (fun (response : Response root (.bounded 1023 2)) => response.done.bytes) == some [0, 0])
  let some state := begin? 2049 cap root (Bao.slicePlan 2049 ⟨2048, 1⟩) |
    throw (IO.userError "tail stream begin")
  let request := Request.toEnd 2048
  let window := request.window 2049
  match parentRead : readRangeStep? window window.start state (tail.drop 8) with
  | none => throw (IO.userError "tail parent")
  | some parent =>
    match edgeRead : readRangeStep? window parent.next parent.raw.next parent.raw.rest with
    | none => throw (IO.userError "tail data")
    | some edge =>
      let trace := Prefix.cons parentRead (.cons edgeRead (.nil edge.next edge.raw.next edge.raw.rest))
      require "EOF before enclosing frame boundary"
        (edge.raw.next.eof.isSome && (finishPrefix? (request := request) trace false).isNone &&
          (finishPrefix? (request := request) trace true).map Done.bytes == some [0])

#eval do
  let payloads : List Bytes := [[], [1, 2, 3], (List.range 1024).map UInt8.ofNat]
  for payload in payloads do
    let size := List.length payload
    let some root := hash? (some ∘ compress32) payload | throw (IO.userError "single chunk hash")
    for profile in [SingleChunk.Profile.combined, .outboard, .slice] do
      let request := Request.toEnd (size / 2)
      let some wire := SingleChunk.encode? profile request payload | throw (IO.userError "single chunk encode")
      let some response := SingleChunk.decode? profile size root request wire payload |
        throw (IO.userError "single chunk decode")
      require "single-chunk profile with empty and exact boundary included"
        (response.suffix?.map Suffix.bytes == some (payload.drop (size / 2)))
      require "strict framing rejects trailing byte"
        (SingleChunk.decode? profile size root request (wire ++ [0]) payload).isNone

#eval do
  let (root, full, subdivided, _) := Iroh.Vectors.rawGetFixtures
  let cap := 40000
  let fullReq : Bytes := 0 :: root ++ [2, 0, 1, 0, 1, 0]
  let partialReq : Bytes := 0 :: root ++ [2, 0, 2, 1, 1, 1, 0]
  let some grouped := decodeIroh? cap root (.toEnd 16383) fullReq full | throw (IO.userError "Iroh grouped")
  require "Iroh grouped suffix across a group and short tail"
    (grouped.suffix?.map (fun (suffix : Suffix root 16383) => suffix.bytes.length) == some 16386)
  let some part := decodeIroh? cap root (.bounded 1024 1024) partialReq subdivided |
    throw (IO.userError "Iroh subdivided")
  require "Iroh projected interior frame supplies no EOF" (part.eof.isNone && part.done.bytes.length == 1024)
  let size := 17409
  let payload := (List.range size).map (fun index => UInt8.ofNat (index % 251))
  let some digest := hash? (some ∘ compress32) payload | throw (IO.userError "short group root")
  let shape := geometry 0 size
  for layers in [0, 1, 2, 4, 5] do
    let cut := Grouped.Cut.forLayers layers (fun index => index ≥ 16) true shape
    let some evidence := cut.emit? payload | throw (IO.userError "short group cut")
    require "grouped and expanded cuts retain ROOT, absolute counters, and EOF"
      (cut.revealed == [16, 17] && (evidence.check? true).map digestBytes == some digest &&
        (eval? (some ∘ compress32) true shape evidence.expand).map digestBytes == some digest &&
        evidence.expand.exposesEOF)
  let shortRoot := geometry 0 1025
  let shortBytes := payload.take 1025
  let rootGroup : Grouped.Evidence shortRoot := .raw shortBytes
  require "a collapsed root uses ROOT, not a child CV"
    ((rootGroup.check? true).map digestBytes == hash? (some ∘ compress32) shortBytes &&
      (rootGroup.check? true).map digestBytes != (rootGroup.check? false).map digestBytes)
  let truncated : Grouped.Evidence shortRoot := .raw (shortBytes.take 1024)
  require "a raw group cannot stand in for missing bytes" (truncated.check? true).isNone

#print axioms suffix_split
#print axioms Bounded.prependSuffix
#print axioms Suffix.against
#print axioms finishPrefix?
#print axioms Grouped.Evidence.check_expand
#print axioms Grouped.raw_width
#print axioms Grouped.Cut.forLayers_reveals
#print axioms Grouped.Cut.emit_named
#print axioms SingleChunk.complete
