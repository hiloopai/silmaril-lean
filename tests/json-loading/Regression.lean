module

import Silmaril.Formats.Json.Fast.Elab
import Silmaril.Formats.Json.Fast.Thms
meta import Silmaril.Formats.Json.Fast.Wire.Defs
meta import Silmaril.Formats.JsonWire.Defs

open Silmaril.Formats Json.Fast

set_option maxRecDepth 4096

def field {α : Type} (doc : Except Error Value) (path : JsonPath) (access : Value → Option α) : Option α :=
  doc.toOption.bind (fun value => (value.at? path).bind access)

json_file manifest from "example.json"

example : SourceMatches manifest.source.toUTF8 manifest := by json_source
example : field manifest [.key "registry", .key "active"] Value.bool? = some true := by json_decide

/-- error: precomputed JSON requires `set_option silmaril.json.allowPrecomputed true` -/
#guard_msgs in
example : Except Error Value := json_precomputed% "true"

set_option silmaril.json.allowPrecomputed true in
json_file_precomputed prepared from "example.json"

theorem preparedMatches : SourceMatches prepared.source.toUTF8 prepared := by json_source
example : field prepared [.key "entries", .index 1] Value.string? = some "𝄞" := by json_decide
example : field prepared [.key "exact"] Value.number? = some ⟨true, 0, 7⟩ := by json_decide
example : ¬ SourceMatches "false".toUTF8 (json% "true") := by
  intro agreement
  simp only [SourceMatches, parseBytes_toUTF8] at agreement
  have select := congrArg (fun result : Except Error Value => result.toOption.bind Value.bool?) agreement
  have left : (parseText "false").toOption.bind Value.bool? = some false := by json_decide
  have right : (parseText "true").toOption.bind Value.bool? = some true := by json_decide
  simp only [left, right] at select
  contradiction

example : field (json% "[\"😀\",\"\\uD83D\\uDE00\",\"é\",\"e\\u0301\"]")
    [.index 1] Value.string? = some "😀" := by json_decide
example : field (json% "{\"😀\":true,\"\\uD83D\\uDE00\":false}") [.key "😀"] Value.bool? = some true := by
  json_decide
example : field (json% "{\"é\":true,\"e\\u0301\":false}") [.key "e\u0301"] Value.bool? = some false := by
  json_decide

example : field (json% "[9007199254740993,1.2500e-24,1e99999]") [.index 0] Value.number? =
    some ⟨false, 9007199254740993, 0⟩ := by json_decide
example : field (json% "[9007199254740993,1.2500e-24,1e99999]") [.index 1] Value.number? =
    some ⟨false, 12500, -28⟩ := by json_decide
example : field (json% "[9007199254740993,1.2500e-24,1e99999]") [.index 2] Value.number? =
    some ⟨false, 1, 99999⟩ := by json_decide

def errorOf (result : Except Error Value) : Option Error :=
  match result with | .error error => some error | .ok _ => none

example : errorOf (parseBytes ⟨#[0xC0, 0x80]⟩) = some ⟨0, .invalidUtf8⟩ := by json_decide
example : errorOf (json% "\"\\uDEAD\"") = some ⟨3, .unpairedSurrogate⟩ := by json_decide
example : errorOf (json% "\"\\uD800\\u0000\"") = some ⟨3, .unpairedSurrogate⟩ := by json_decide
example : errorOf (json% "\"λ\" false") = some ⟨5, .trailingInput⟩ := by json_decide
example : errorOf (parseText "{\"k\":[]}" { depth := 1 }) = some ⟨5, .depthLimit⟩ := by json_decide
example : (parseText "{\"k\":[]}" { depth := 2 }).isOk = true := by json_decide
example : (parseText "-9e99" { numberBytes := 5 }).isOk = true := by json_decide
example : errorOf (parseText "-9e99" { numberBytes := 4 }) = some ⟨4, .numberLimit⟩ := by json_decide

def invalid : List String :=
  ["", " ", "[0,]", "{\"a\":0,}", "\"\\x20\"", "\"\n\"", "\"\\u012\"", "\"\\uD800", "{a:0}",
    "00", "-01", "1e", "1E+", "1.", "-.1", "+1", "NaN", "Infinity", "truefalse", "[", "{",
    "{} []", "/*x*/0", String.singleton (Char.ofNat 0xFEFF) ++ "{}"]

example : invalid.all (fun text => (parseText text).isOk == false) = true := by json_decide

def collisionFirst := "2d3c3bdde54f96f7"
def collisionSecond := "d2d837d4c0d63d36"

example : keyHash collisionFirst = keyHash collisionSecond := by json_decide

set_option silmaril.json.allowPrecomputed true in
def wide : Except Error Value := json_precomputed% r#"{"2d3c3bdde54f96f7":true,"d2d837d4c0d63d36":false,"a":null,"b":null,"c":null,"d":null,"e":null,"f":null,"g":null,"h":null,"i":null,"j":null,"k":null,"l":null,"m":null,"n":null,"o":null,"p":null,"q":null,"r":null,"s":null,"t":null,"u":null,"v":null,"w":null,"x":null,"y":null,"z":null,"0":null,"1":null,"2":null,"3":null,"4":null,"2d3c3bdde54f96f7":false,"last":true}"#

example : (wide.toOption.bind fun value => (value.member? collisionFirst).bind Value.bool?) = some true := by
  json_decide
example : (wide.toOption.bind fun value => (value.member? collisionSecond).bind Value.bool?) = some false := by
  json_decide
example : (wide.toOption.bind fun value => (value.member? "missing").bind Value.bool?) = none := by
  json_decide
example : ((wide.toOption.bind Value.entries?).map fun entries => entries.toList.map Prod.fst).map
    (·.drop 32) = some ["4", collisionFirst, "last"] := by json_decide

def semanticFixture := r#"[null,true,false,-0,0e-999,123.4500,"\u0000\/\\\"\b\f\n\r\t",{"😀":1,"\ud83d\ude00":2,"é":3,"e\u0301":4}]"#

def sameWire (text : String) : Bool :=
  match (parseText text).toOption.bind (Value.toWire? 128), JsonWire.parse? ⟨text.toUTF8⟩ with
  | some fast, some wire => (JsonWire.encode fast).data == (JsonWire.encode wire).data
  | _, _ => false

#eval show IO Unit from do
  let loaded ← load "tests/json-loading/example.json"
  unless field loaded [.key "registry", .key "active"] Value.bool? == some true do
    throw (IO.userError "runtime file load did not find the expected field")
  unless sameWire semanticFixture do
    throw (IO.userError "wire mismatch on semantic fixture")
  unless sameWire (include_str "../../examples/containers/noop-oci/layout/manifest.json") do
    throw (IO.userError "wire mismatch on OCI manifest")

example : (prepared.toOption.bind (Value.toWire? 128)) = JsonWire.parse? ⟨prepared.source.toUTF8⟩ := by rfl
