module

public import Silmaril.Parse.ByteParse.Defs

/-!
# Section framing of Wasm core modules and components

A re-implementation, on the cursor-parser idioms, of the *framing* layer of
silmaril's core decoder (`Silmaril.Wasm.Binary.Core.Decode.readModule.go`):
a fixed preamble, then `id:byte size:u32 body:byte^size` sections up to the
end of the input. Bodies are returned as copied `ByteArray`s; section order,
custom-section names and body contents are left to the next layer.

The same parser frames core modules (`coreFraming`, preamble
`magic ++ version`) and components (`componentFraming`, preamble
`magic 0d 00 01 00`). The grammar of one section, `RawSection`, is silmaril's
`Section id G` with `G c [c]` (`rawSection_iff_section`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary.Framing

open Silmaril.Parse.ByteParse (Grammar GrammarE Bytes Error runAll)
open Silmaril.Parse.ByteParse.Grammar

/-- A framed section: its id and its body. -/
structure RawSection where
  id : UInt8
  body : ByteArray

/-- `id:byte size:u32 body`. -/
def rawSectionG : Grammar RawSection :=
  byte.bind fun id => (u32.bind fun n => bytes n).map fun body => ⟨id, body⟩

/-- A preamble, then sections up to the end. -/
def framingG (preamble : List UInt8) : GrammarE (List RawSection) :=
  GrammarE.after (lit preamble) fun _ =>
    GrammarE.items rawSectionG (bind_nonEmpty byte_nonEmpty)

/-- The core-module preamble `\0asm` version 1 (silmaril's `magic ++ version`). -/
def corePreamble : List UInt8 := Silmaril.Wasm.Binary.magic ++ Silmaril.Wasm.Binary.version

/-- The component preamble: version `0x0d`, layer 1. -/
def componentPreamble : List UInt8 := [0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00]

/-- Frame a core module. -/
def coreFraming (b : ByteArray) : Except Error (List RawSection) :=
  runAll (framingG corePreamble).parse b

/-- Frame a component. -/
def componentFraming (b : ByteArray) : Except Error (List RawSection) :=
  runAll (framingG componentPreamble).parse b

/-- The grammar of one section, stated directly. -/
def RawSection.G (l : Bytes) (s : RawSection) : Prop :=
  ∃ lb, l = [s.id] ++ lb ++ s.body.data.toList ∧ Silmaril.Wasm.Binary.U32 lb s.body.size

end Silmaril.Wasm.Component.Binary.Framing
