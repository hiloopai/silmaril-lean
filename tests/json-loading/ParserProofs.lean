module

import Silmaril.Formats.Json.Fast.Parser.Thms
import Silmaril.Formats.Json.Fast.Parser.Wire.Thms
import Silmaril.Formats.Json.Fast.Elab

open Silmaril.Formats
open Silmaril.Formats.Json.Fast.Parser

example :
    let pos : Pos := ⟨0, (r#""\ud83d\ude00\u0000\n""# ++ ",null").toList⟩
    let stop : Pos := ⟨22, ",null".toList⟩
    JsonWire.Internal.tokensOf pos.rest = (JsonWire.Internal.tokensOf stop.rest).map
      (.string (JsonWire.stringUnits (String.ofList ['😀', Char.ofNat 0, '\n'])) :: ·) :=
  quoted_tokens (size := 27) rfl

private def sample := "\t" ++ r#"{"z":[-0e-7,{},false],"😀":"\ud83d\ude00","\u007a":null}"# ++ "\r\n"

private def expected : Json.Fast.Value := Json.Fast.Value.ofObject #[
  ("z", Json.Fast.Value.ofArray #[.number ⟨true, 0, -7⟩, Json.Fast.Value.ofObject #[], .bool false]),
  ("😀", .string "😀"), ("z", .null)]

private theorem sampleParsed : Json.Fast.parseBytes sample.toUTF8 Json.Fast.defaultLimits = .ok expected := by
  exact (show Json.Fast.SourceMatches sample.toUTF8 (.ok expected) by json_source)

example : (Bytes.mk sample.toUTF8).IsJson .rfc8259 := Json.Fast.parseBytes_isJson sampleParsed

example : JsonWire.parse? ⟨sample.toUTF8⟩ = expected.toWire? Json.Fast.defaultLimits.depth := by
  obtain ⟨_, fast, wire⟩ := Json.Fast.parseBytes_sound sampleParsed
  exact wire.trans fast.symm

#print axioms quoted_tokens
#print axioms numberLoop_sound
#print axioms more_sound
#print axioms series_sound
#print axioms Json.Fast.Value.toWire?_ofObject
#print axioms Json.Fast.Value.member?_ofObject_sound
#print axioms Json.Fast.parseBytes_sound
#print axioms Json.Fast.parseBytes_isJson
