module

public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Component.Binary.Lower.Defs
public import Silmaril.Wasm.Component.Pipeline.Defs
public meta import Silmaril.Wasm.Component.Binary.Encode.Defs
public meta import Silmaril.Wasm.Component.Binary.Lower.Defs
public meta import Silmaril.Wasm.Component.Pipeline.Defs

/-!
# Hand-built component binaries

Test inputs written with the encoder (`encode`), parsed back (`parse`),
lowered (`lower`) and optimised (`optimizeComponent`). No real component
binaries were available on the development machine (no `wasm-tools` or
`cargo component`; no `.wasm` file under `~` has the component layer), so all
inputs here are hand-built; the expected IR is the one of the
`Silmaril.Wasm.Component.Example` toy components, now with real core modules.
The checks are executed by `#guard`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary.Example

open Silmaril.Wasm.Component

/-- A core module exporting `get : [] → [i32]` (answers `42`). -/
def producer : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f,
  0x03, 0x02, 0x01, 0x00,
  0x07, 0x07, 0x01, 0x03, 0x67, 0x65, 0x74, 0x00, 0x00,
  0x0a, 0x06, 0x01, 0x04, 0x00, 0x41, 0x2a, 0x0b]⟩

/-- A core module importing `env.get` and exporting `run` (`get() + 1`). -/
def consumer : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f,
  0x02, 0x0b, 0x01, 0x03, 0x65, 0x6e, 0x76, 0x03, 0x67, 0x65, 0x74, 0x00, 0x00,
  0x03, 0x02, 0x01, 0x00,
  0x07, 0x07, 0x01, 0x03, 0x72, 0x75, 0x6e, 0x00, 0x01,
  0x0a, 0x09, 0x01, 0x07, 0x00, 0x10, 0x00, 0x41, 0x01, 0x6a, 0x0b]⟩

/-- `func() -> u32` as a binary type. -/
def getTy : DefType := .func ⟨[], some (.prim .u32), false⟩

/-- Like the toy component `B`: import `get`, lower it into `consumer`,
lift and export `run`. -/
def compB : Ast := .mk [
  .types [getTy],
  .imports [⟨↑"get", .func 0⟩],
  .coreModule consumer,
  .canons [.lower 0 []],
  .coreInstances [.exports [("get", ⟨.func, 0⟩)], .instantiate 0 [("env", 0)]],
  .aliases [⟨.core .func, .coreExport 1 "run"⟩],
  .canons [.lift 1 [] 0],
  .exports [⟨↑"run", ⟨.func, 1⟩, none⟩]]

/-- Producer and consumer in one component: `get` is lifted, lowered again
into the consumer, and `run` is exported. Fusion removes the round trip. -/
def linked : Ast := .mk [
  .coreModule producer,
  .coreModule consumer,
  .types [getTy],
  .coreInstances [.instantiate 0 []],
  .aliases [⟨.core .func, .coreExport 0 "get"⟩],
  .canons [.lift 0 [.utf8] 0, .lower 0 []],
  .coreInstances [.exports [("get", ⟨.func, 1⟩)], .instantiate 1 [("env", 1)]],
  .aliases [⟨.core .func, .coreExport 2 "run"⟩],
  .canons [.lift 2 [] 0],
  .exports [⟨↑"run", ⟨.func, 1⟩, none⟩],
  .custom "producers" ⟨#[0x00]⟩]

/-- An instance import with a record type and an instance export. -/
def withInstance : Ast := .mk [
  .types [.val (.record [("x", .prim .u32), ("ok", .prim .bool)]),
    .instance [.alias ⟨.type, .outer 1 0⟩, .type (.func ⟨[("p", .idx 0)], none, false⟩),
      .export ↑"f" (.func 1)]],
  .imports [⟨↑"host", .instance 1⟩],
  .aliases [⟨.func, .export 0 "f"⟩],
  .instances [.exports [(↑"g", ⟨.func, 1⟩)]],
  .exports [⟨↑"api", ⟨.instance, 1⟩, none⟩]]

/-! ## Byte sequences assembled by hand from `Binary.md`

The component-model `design/mvp/Binary.md` at commit `8505ba73` (2026-10-27).
Each test parses the bytes and re-encodes the result. -/

/-- The bytes, parsed and re-encoded (`none` if parsing fails). -/
def reparse (l : List UInt8) : Option (List UInt8) :=
  (parse ⟨l.toArray⟩).toOption.bind fun c => (encode c).map (·.data.toList)

def preamble : List UInt8 := [0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00]

/-- `(type (func (param "x" u32) (result u32)))`: `0x40`, a paramlist, `0x00 valtype`. -/
def funcTypeSec : List UInt8 := [0x07, 0x08, 0x01, 0x40, 0x01, 0x01, 0x78, 0x79, 0x00, 0x79]

/-- `(type (func async))` with no result: `0x43 vec() 0x01 0x00`. -/
def asyncFuncSec : List UInt8 := [0x07, 0x05, 0x01, 0x43, 0x00, 0x01, 0x00]

/-- `(type (map string u32))`, `0x63`, and `(type (list 64))` with the index as
a non-negative SLEB128 (`c0 00`). -/
def mapListSec : List UInt8 := [0x07, 0x07, 0x02, 0x63, 0x73, 0x79, 0x70, 0xc0, 0x00]

/-- `(import "wasi:cli/run" (version-suffix "0.2.0") (instance (type 0)))`:
`nameattributes ::= 0x02 name vec(attribute)`, `attribute ::= 0x01 name`. -/
def versionedImport : List UInt8 :=
  [0x0a, 0x19, 0x01, 0x02, 0x0c] ++ "wasi:cli/run".toUTF8.data.toList ++
    [0x01, 0x01, 0x05] ++ "0.2.0".toUTF8.data.toList ++ [0x05, 0x00]

/-- `(core type (module (alias outer 1 0 (type)) (import "m" "t" (tag (type 0)))))`:
`core:alias ::= 0x10 0x01 ct idx` and the core `tag` extern type. -/
def moduleTypeSec : List UInt8 :=
  [0x03, 0x10, 0x01, 0x50, 0x02, 0x02, 0x10, 0x01, 0x01, 0x00,
    0x00, 0x01, 0x6d, 0x01, 0x74, 0x04, 0x00, 0x00]

/-- `(alias core export 0 "t" (core tag))`: core sort `0x04` is `tag`. -/
def tagAlias : List UInt8 := [0x06, 0x07, 0x01, 0x00, 0x04, 0x01, 0x00, 0x01, 0x74]

/-- `(type (resource (rep i32) (dtor 0)))`: `0x3f core:valtype funcidx?`. -/
def resourceSec : List UInt8 := [0x07, 0x05, 0x01, 0x3f, 0x7f, 0x01, 0x00]

#guard reparse preamble == some preamble
#guard reparse (preamble ++ funcTypeSec) == some (preamble ++ funcTypeSec)
#guard reparse (preamble ++ asyncFuncSec) == some (preamble ++ asyncFuncSec)
#guard reparse (preamble ++ mapListSec) == some (preamble ++ mapListSec)
#guard reparse (preamble ++ versionedImport) == some (preamble ++ versionedImport)
#guard reparse (preamble ++ moduleTypeSec) == some (preamble ++ moduleTypeSec)
#guard reparse (preamble ++ tagAlias) == some (preamble ++ tagAlias)
#guard reparse (preamble ++ resourceSec) == some (preamble ++ resourceSec)
-- `(list 64)` with the index as a `u32` (`0x40`) is a negative SLEB128: rejected.
#guard reparse (preamble ++ [0x07, 0x03, 0x01, 0x70, 0x40]) == none
-- Removed named results (`0x01 vec(labelvaltype)` with entries) are rejected.
#guard reparse (preamble ++ [0x07, 0x07, 0x01, 0x40, 0x00, 0x01, 0x01, 0x01, 0x78, 0x79]) == none
-- The GC `0x00 0x50` core sub type and async canon built-ins are not supported.
#guard reparse (preamble ++ [0x03, 0x05, 0x01, 0x00, 0x50, 0x00, 0x60]) == none
#guard reparse (preamble ++ [0x08, 0x02, 0x01, 0x05]) == none
-- The section size must match: one byte short is rejected.
#guard reparse (preamble ++ [0x07, 0x07, 0x01, 0x40, 0x01, 0x01, 0x78, 0x79, 0x00, 0x79]) == none

/-- Encode, then parse back. -/
def roundTrip (c : Ast) : Option Ast := (encode c).bind fun b => (parse b).toOption

/-- Encode, parse, lower. -/
def lowered (c : Ast) : Except String (Comp CoreMod) :=
  match encode c with
  | some b => parseComponent b
  | none => .error "encoder failed"

def bytesOf (c : Ast) : List UInt8 := ((encode c).map (·.data.toList)).getD []

def ftU32 : FuncTy := ⟨[], [.u32]⟩

-- The encoder output parses back to an AST with the same encoding.
#guard (roundTrip compB).map bytesOf == some (bytesOf compB)
#guard (roundTrip linked).map bytesOf == some (bytesOf linked)
#guard (roundTrip withInstance).map bytesOf == some (bytesOf withInstance)

-- The preamble: magic, version 0x0d, layer 1.
#guard (bytesOf compB).take 8 == [0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00]

-- A core module (layer 0) is not a component.
#guard (parse producer).toOption.isNone
-- Truncation and trailing bytes are rejected.
#guard (parse ⟨((bytesOf compB).dropLast).toArray⟩).toOption.isNone
#guard (parse ⟨(bytesOf compB ++ [0x00]).toArray⟩).toOption.isNone

/-- The lowered imports, nodes (as import wirings) and exports. -/
def shape (c : Comp CoreMod) : Iface × List (List Impl) × List (String × Impl) :=
  (c.imports, c.nodes.map (fun | .core _ args => args | .inst _ args => args),
    c.exports.map fun x => (x.name, x.impl))

-- `compB` lowers to the IR of the toy component `B`.
#guard (lowered compB).toOption.map shape ==
  some ([("get", ftU32)], [[⟨[.lower ftU32], .call 0⟩]], [("run", ⟨[.lift ftU32], .call 1⟩)])

-- The core interfaces come from silmaril's core decoder.
#guard ((lowered compB).toOption.map fun c => c.nodes.map fun
    | .core m _ => (m.importNames, m.exports.map (·.1)) | .inst _ _ => ([], [])) ==
  some [([("env", "get")], ["run"])]

-- `linked`: the consumer imports `lower ∘ lift` of the producer's `get`.
#guard (lowered linked).toOption.map shape ==
  some ([], [[], [⟨[.lower ftU32, .lift ftU32], .call 0⟩]], [("run", ⟨[.lift ftU32], .call 1⟩)])

-- The optimiser fuses the adapters into a flat check (`u32` is a plain `i32`).
#guard ((lowered linked).toOption.map fun c => shape (optimizeComponent c)) ==
  some ([], [[], [⟨[.flatCheck [] [.int .i32]], .call 0⟩]], [("run", ⟨[.lift ftU32], .call 1⟩)])

-- An imported instance contributes `host#f`; the exported instance `api#g`.
#guard (lowered withInstance).toOption.map shape ==
  some ([("host#f", ⟨[.record [.u32, .bool]], []⟩)], [],
    [("api#g", ⟨[], .call 0⟩)])

-- Unsupported constructs are reported.
#guard (lowered (.mk [.types [.val (.prim .string)], .types [.func ⟨[("s", .idx 0)], none, false⟩],
    .imports [⟨↑"f", .func 1⟩]])).toOption.isNone
#guard match lowered (.mk [.component (.mk [])]) with
  | .error e => e == "nested components are not supported"
  | .ok _ => false

end Silmaril.Wasm.Component.Binary.Example
