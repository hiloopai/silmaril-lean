module

public import Silmaril.Project.WasmComponents.Kernel.Framing.Defs

/-!
# Kernel decoders for registered releases: kernel-friendly forms of Silmaril's decoders

The kernel evaluates Silmaril's decoders on a registered file by unfolding them on the file's
`include_bytes` term. That is cheap for byte *lists*, but three things the decoders do are not:

* reading `bs[i]` of a `ByteArray` walks its list to position `i`, so a cursor parser over a
  15 KB file takes minutes (the an earlier step measurement: about 4 minutes for the `wasi:io` fixture);
* `List.toArray`, `Array.push`, `Array.extract` and `ByteArray.extract` rebuild their array one
  push at a time, quadratic in the kernel (the encoder's final `toArray` on 15 KB did not finish
  in 280 s);
* `String.fromUTF8Lossy`, which `readDocsSection` applies to a 12 KB `package-docs` section, is
  not exposed by Lean core, so the kernel cannot unfold it at all.

This module gives forms of the decoders that avoid all three, each **equal** to the original
(`Silmaril.Project.WasmComponents.Kernel.Thms`), so a kernel computation on the fast form proves
the statement about the original:

* `readDocsFast`: `readDocsSection` on a section whose bytes are ASCII is `JVal.parse` of the
  bytes as characters (`readDocsFast_eq`, from Lean's `fromUTF8Lossy_utf8Encode`); other
  sections fall back to `readDocsSection`;
* `decodeSectionsWith rd`: `decodeSections` with the docs reader a parameter
  (`decodeSections_eq_fast`);
* `sliceOf b i j`: `b.extract i j` as a list slice wrapped in constructors, with no pushes
  (`extract_eq_sliceOf`), and `customSectionsFast`, `extractPayloadFast`: the custom sections of
  a core module on the list framing of `Kernel.Framing`, with their contents sliced (`customSections_eq_fast`, `extractPayload_eq_fast`).

Component parses themselves are not evaluated: a component AST is checked by running Silmaril's
list-based encoder (`Binary.Encode.ast`) and comparing with the file's byte list, and
`Binary.parse_encode` turns that into the parse (`Kernel.is_of_ast`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Wit.Binary
open Silmaril.Parse.ByteParse (Parser Res)

/-- The character of a byte below `128`. -/
def asciiChar (b : UInt8) : Char := Char.ofNat b.toNat

/-- `readDocsSection`, without `fromUTF8Lossy` when the section is ASCII. -/
def readDocsFast (data : ByteArray) : Option JVal :=
  match data.data.toList with
  | v :: rest =>
    if v = 0 ∨ v = 1 then
      if rest.all (fun b => decide (b.toNat < 128)) then JVal.parse (rest.map asciiChar)
      else JVal.parse (String.fromUTF8Lossy ⟨rest.toArray⟩).toList
    else none
  | [] => none

/-- `decodeSections` with the reader of the `package-docs` section a parameter. -/
def decodeSectionsWith (rd : ByteArray → Option JVal) (ss : List Section) :
    Except String Package := do
  let (items, cs) := splitCustom ss
  let p ← decodeItems items
  match cs.find? (·.1 = "package-docs") with
  | none => pure p
  | some (_, d) =>
    match rd d with
    | some m => pure (p.inject m)
    | none => throw "malformed package-docs section"

/-- The `wit.binary` reading of a component AST, with the fast docs reader. -/
def witDecodeFast (c : Ast) : Option Package :=
  match decodeSectionsWith readDocsFast c.sections with
  | .ok p => some p
  | .error _ => none

/-- `customSections` on the list framing (`coreSectionsFast`, `nameFast`), with each section's
contents sliced (`sliceOf`). -/
def customSectionsFast (b : ByteArray) : Except String (List (String × ByteArray)) := do
  let ss ← coreSectionsFast b
  ss.filterMapM fun (id, s, e) =>
    if id = 0 then
      match nameFast b e s with
      | Res.ok n j => pure (some (n, sliceOf b j e))
      | Res.err _ => throw s!"malformed custom section name at offset {s}"
    else pure none

/-- `extractPayload` on `customSectionsFast`, with the name test on character lists. -/
def extractPayloadFast (m : ByteArray) : Except String ByteArray := do
  let cs ← customSectionsFast m
  match cs.filter (fun c => decide (componentTypeSection.toList <+: c.1.toList)) with
  | [(_, d)] => pure d
  | [] => throw "no component-type custom section"
  | _ => throw "several component-type custom sections (merging is not supported)"

/-- `extractPayloadFast m` is the slice `j` to `e` of `m` (a check the kernel can run). -/
def payloadAt (m : ByteArray) (j e : Nat) : Bool :=
  match extractPayloadFast m with
  | .ok d => decide (d.data.toList = (sliceOf m j e).data.toList)
  | .error _ => false

/-- The `wasm.module.world` reading of an embedded component AST. -/
def worldDecodeFast (c : Ast) : Option (PackageName × String × World × StringEncoding) :=
  match decodeWorldTypeSections c.sections with
  | .ok w => some w
  | .error _ => none

end Silmaril.Project.WasmComponents.Kernel

end
