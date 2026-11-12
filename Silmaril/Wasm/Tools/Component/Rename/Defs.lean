module

public import Silmaril.Wasm.Component.Codec.Defs
public import Silmaril.Wasm.Component.BinaryP3.Encode.Defs

/-!
# `wasm-tools component new --import-name OLD=NEW`

wit-component's `ComponentEncoder::import_name_map` names the component's import of the world
import `OLD` (an interface's world key: `ns:pkg/iface[@v]` or a plain name) `NEW` instead
(`encode_imports`). The component is otherwise unchanged. Here the rename is applied to the
encoded component: every import of the top-level component named `OLD` is renamed `NEW`
(`renameAst`), through the verified component grammar (`Codec.decodeLax`/`BinaryP3.encode`); the name
form is kept. With no pairs the bytes are returned unchanged (`renameBytes_nil`).

`--import-name` takes `OLD=NEW` (clap's `parse_import_name`: split at the first `=`, else
upstream's message `expected `--import-name` option to be of the form `OLD=NEW``).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Rename

open Silmaril.Wasm.Component.Binary (Import)
open Silmaril.Wasm.Component.BinaryP3 (Section Ast)

/-- The new name of an import (the first pair for its name; `HashMap` keeps the last of
duplicate keys, so the pairs are looked up from the end). -/
def newName (m : List (String × String)) (n : String) : String :=
  (m.reverse.lookup n).getD n

def renameImport (m : List (String × String)) (i : Import) : Import :=
  { i with name := { i.name with name := newName m i.name.name } }

def renameSection (m : List (String × String)) : Section → Section
  | .imports is => .imports (is.map (renameImport m))
  | s => s

/-- Rename the imports of the top-level component. -/
def renameAst (m : List (String × String)) (c : Ast) : Ast :=
  .mk (c.sections.map (renameSection m))

/-- `OLD=NEW` as `(OLD, NEW)` (split at the first `=`). -/
def parsePair (s : String) : Option (String × String) :=
  match s.splitOn "=" with
  | a :: b :: rest => some (a, "=".intercalate (b :: rest))
  | _ => none

/-- **`--import-name`** on the encoded component. -/
def renameBytes (m : List (String × String)) (b : ByteArray) : Except String ByteArray :=
  if m.isEmpty then .ok b
  else match Silmaril.Wasm.Component.Codec.decodeLax b with
    | .error _ => .error "--import-name: the component is outside the verified component grammar"
    | .ok c => match Silmaril.Wasm.Component.BinaryP3.encode (renameAst m c) with
      | some b' => .ok b'
      | none => .error "a number or size exceeds 2^32"

end Silmaril.Wasm.Tools.Component.Rename
