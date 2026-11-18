module

import Silmaril.Formats.JsonWithBytes.Utf8Map.Thms

open Silmaril.Formats
open Silmaril.Formats.JsonWithBytes
open Silmaril.Formats.JsonWithBytes.Utf8Map

private def entries : List (String × UnorderedI64) := [
  ("", .scalar (.bytes [0, 255])), ("é", .scalar (.bool true)), ("e\u0301", .scalar .null),
  ("😀", .scalar (.number (-4)))]

example : (Map.ofEntries entries).toOption.bind (·.find? "") = some (.scalar (.bytes [0, 255])) := rfl

example : (Map.ofEntries entries).toOption.bind (·.find? "é") = some (.scalar (.bool true)) := rfl

example : (Map.ofEntries entries).toOption.bind (·.find? "e\u0301") = some (.scalar .null) := rfl

example : (Map.ofEntries entries).toOption.bind (·.find? "😀") = some (.scalar (.number (-4))) := rfl

example : Map.ofEntries (entries ++ [("😀", .scalar .null)]) = .error "😀" := rfl

example {map : Map UnorderedI64} (accepted : Map.ofEntries entries = .ok map) :
    (equiv map).val = Json.ofEntries entries (ofEntries_sound accepted).1 := equiv_ofEntries accepted

#print axioms ofEntries_accepts
#print axioms equiv_ofEntries
#print axioms equiv
