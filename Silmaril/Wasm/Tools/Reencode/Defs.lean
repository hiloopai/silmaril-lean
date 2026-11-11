module

public import Silmaril.Wasm.Tools.Layout.Defs
public import Silmaril.Wasm.Tools.Framing.Defs

/-!
# A re-encoder that keeps the original encoding choices (`RoundtripReencoder`)

`wasm-tools wast` checks every text module by re-encoding its binary with wasm-encoder's
`RoundtripReencoder` (`crates/wasm-encoder/src/reencode.rs`, wasm-tools 1.262.0) and comparing
the result with the original bytes. That re-encoder decodes with wasmparser and writes every
item again with wasm-encoder, so it keeps the choices wasmparser reports and drops the rest:

* kept: the order of the sections and the custom sections between them (custom sections are
  copied; the `name` section is re-encoded subsection by subsection, which for a well-formed
  `name` section is a copy), the data count section when there was one, the element segment
  forms (function indices versus expressions, an explicit table index: `ElementKind::Active`'s
  `table_index: Option<u32>`), table initializer expressions (`TableInit::Expr`), the `rec`
  prefix of a recursion group with one type, explicit empty `else` arms (wasmparser reports
  the `else` operator), local declaration groups;
* dropped: LEB128 widths (wasm-encoder writes every LEB128 minimally) and the other
  non-canonical encodings wasmparser does not report.

`reencode b` does the same on top of the certified decoder: it decodes `b`, reads the kept
choices from the raw bytes (`hintsOf`, with the readers of `Silmaril.Wasm.Tools.Print.Raw`),
writes the module with them (`Layout.candidate`), and copies the custom sections of `b`
between the non-custom sections (`splice`). Nothing of this is trusted: the result is kept
only when the certified decoder reads it back as the module of `b` (`Layout.accepts`);
otherwise the canonical encoding with the custom sections copied, and otherwise the
canonical encoding alone. So whatever `reencode` returns encodes the module `b` encodes
(`Silmaril.Wasm.Tools.Reencode.Thms.reencode_sound`).

Local declaration groups are written run-length (silmaril-lean's decoded module keeps the
types of the locals, not their grouping), which is how the `wast` crate and wasm-encoder's
`Function::new_with_locals_types` write them.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Reencode

open Silmaril Silmaril.Wasm
open Silmaril.Wasm.Tools.Print

/-- The payload offset of the first section with id `id`. -/
def payloadOf (secs : List Raw.Section) (id : Nat) : Option Nat :=
  (secs.find? (·.id == id)).map (·.payload)

/-- The encoding choices of a module binary that `RoundtripReencoder` keeps, read from the raw
bytes: per recursion group the `rec` prefix, per defined table an initializer expression, per
element segment its form, per defined function its explicit `else`s. -/
def hintsOf (b : ByteArray) : Layout.Hints :=
  match Raw.sections b with
  | none => {}
  | some secs =>
    let at_ := payloadOf secs
    { recs := (((at_ 1).bind (Raw.recForms b)).getD []).toArray,
      tables := (((at_ 4).bind (Raw.tableInits b)).getD []).toArray,
      elems := (((at_ 9).bind (Raw.elemForms b)).getD []).toArray.map
        fun f => ⟨f.explicitTable, !f.exprs⟩,
      elses := (((at_ 10).bind (Raw.codeEvents b)).getD []).toArray.map
        fun (_, evs) => Raw.explicitElses evs }

/-- Does the binary have a data count section? -/
def hasDataCount (b : ByteArray) : Bool :=
  match Raw.sections b with
  | some secs => secs.any (·.id == 12)
  | none => false

/-- The sections of `orig` with each non-custom section replaced, in order, by the next
non-custom section of `cand`. -/
def merge : List Framing.RawSec → List Framing.RawSec → List Framing.RawSec
  | [], _ => []
  | s :: os, cs =>
    if s.id == 0 then s :: merge os cs
    else match cs with
      | c :: cs => c :: merge os cs
      | [] => s :: merge os []

/-- `cand`'s non-custom sections with the custom sections of `orig` around them, as
`RoundtripReencoder` places them; `none` when the two have different non-custom section ids
or a framing error. -/
def splice (orig cand : List UInt8) : Option (List UInt8) :=
  match Framing.splitSecs (orig.drop 8), Framing.splitSecs (cand.drop 8) with
  | some os, some cs =>
    let cs' := cs.filter (·.id != 0)
    if (os.filter (·.id != 0)).map (·.id) == cs'.map (·.id) then
      some (cand.take 8 ++ Framing.join (merge os cs'))
    else none
  | _, _ => none

/-- The first of the candidates that the certified check accepts as an encoding of the module
whose canonical encoding is `canon`; `canon` when none is. -/
def firstAccepted (dc : Bool) (canon : List UInt8) : List (Option (List UInt8)) → List UInt8
  | [] => canon
  | some c :: cs => if Layout.accepts dc canon c then c else firstAccepted dc canon cs
  | none :: cs => firstAccepted dc canon cs

/-- The re-encoding of the module `m` decoded from `b`: the module written with `b`'s kept
choices and custom sections, else the canonical encoding with the custom sections, else the
canonical encoding. -/
def reencodeModule (b : ByteArray) (m : Module) : Except String (List UInt8) := do
  let dc := hasDataCount b
  let canon ← Binaryen.Exe.encodeModuleWith? dc m
  let o := b.data.toList
  let kept := match Layout.candidate (hintsOf b) [] [] dc m with
    | .ok c => splice o c
    | .error _ => none
  pure (firstAccepted dc canon [kept, splice o canon])

/-- `RoundtripReencoder` on a core module binary. -/
def reencode (b : ByteArray) : Except String ByteArray := do
  let m ← Binary.Core.Decode.decodeModule b
  pure ⟨(← reencodeModule b m).toArray⟩

end Silmaril.Wasm.Tools.Reencode
