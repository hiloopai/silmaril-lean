module

public import Silmaril.Project.WasmComponents.Kernel.Defs
public import Silmaril.Project.WasmComponents.Kernel.Framing.Thms
public import Silmaril.Project.Formats.Component.Thms
public import Silmaril.Project.Formats.Wit.Defs
public import Silmaril.Wasm.Component.Binary.Thms
import Init.Data.String.Lemmas.Lossy

/-!
# Kernel decoders for registered releases: the fast forms are the decoders

**PROVED**:

* `fromUTF8Lossy_ascii`: on ASCII bytes, `String.fromUTF8Lossy` is the bytes as characters;
  hence `readDocsFast_eq` and `decodeSections_eq_fast`;
* `extract_eq_sliceOf`, `customSections_eq_fast`, `extractPayload_eq_fast`;
* the certificates: `is_of_ast` (a component value is the AST whose list encoding is its
  bytes), `witBinary_parse_of_ast` (a WIT package value decodes through `decodeSectionsWith
  readDocsFast` on that AST), `parse_of_list` (the parse of any byte array whose list is an
  AST's encoding).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Wit.Binary
open Silmaril.Project (Value)

/-! ## `package-docs` on ASCII -/

theorem utf8EncodeChar_ascii : ∀ {x : UInt8}, x.toNat < 128 →
    String.utf8EncodeChar (asciiChar x) = [x] := by
  decide

/-- ASCII bytes are the UTF-8 encoding of their characters. -/
theorem utf8Encode_ascii {l : List UInt8} (h : ∀ x ∈ l, x.toNat < 128) :
    (l.map asciiChar).utf8Encode = ⟨l.toArray⟩ := by
  have e : (l.map asciiChar).flatMap String.utf8EncodeChar = l := by
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [utf8EncodeChar_ascii (h x (List.mem_cons_self ..)),
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      rfl
  apply ByteArray.ext
  rw [List.utf8Encode_eq_toByteArray]
  show ((l.map asciiChar).flatMap String.utf8EncodeChar).toByteArray.data = l.toArray
  rw [e, List.data_toByteArray]

/-- **`fromUTF8Lossy` on ASCII bytes** is the bytes as characters. -/
theorem fromUTF8Lossy_ascii {l : List UInt8} (h : ∀ x ∈ l, x.toNat < 128) :
    (String.fromUTF8Lossy ⟨l.toArray⟩).toList = l.map asciiChar := by
  rw [← utf8Encode_ascii h, String.fromUTF8Lossy_utf8Encode, String.toList_ofList]

theorem readDocsFast_eq (d : ByteArray) : readDocsFast d = readDocsSection d := by
  unfold readDocsFast readDocsSection
  rcases hd : d.data.toList with _ | ⟨v, rest⟩
  · rfl
  · simp only
    by_cases hv : v = 0 ∨ v = 1
    · simp only [hv, ite_true]
      by_cases ha : rest.all (fun b => decide (b.toNat < 128)) = true
      · rw [ite_eq_left ha, fromUTF8Lossy_ascii (fun x hx => by simpa using List.all_eq_true.mp ha x hx)]
      · rw [ite_eq_right ha]
    · simp only [hv, ite_false]

theorem decodeSections_eq_with (ss : List Section) :
    decodeSections ss = decodeSectionsWith readDocsSection ss := rfl

/-- **`decodeSections` is its fast form.** -/
theorem decodeSections_eq_fast (ss : List Section) :
    decodeSections ss = decodeSectionsWith readDocsFast ss := by
  rw [decodeSections_eq_with, show readDocsFast = readDocsSection from funext readDocsFast_eq]

/-! ## Slices -/

theorem customSections_eq_fast (b : ByteArray) : customSections b = customSectionsFast b := by
  unfold customSections customSectionsFast
  simp only [extract_eq_sliceOf, coreSections_eq_fast, name_eq_fast]
  rfl

theorem extractPayload_eq_fast (m : ByteArray) : extractPayload m = extractPayloadFast m := by
  unfold extractPayload extractPayloadFast
  rw [customSections_eq_fast]
  congr 1
  funext cs
  have : cs.filter (·.1.startsWith componentTypeSection) =
      cs.filter (fun c => decide (componentTypeSection.toList <+: c.1.toList)) := by
    congr 1
    funext c
    exact Bool.eq_iff_iff.mpr (by simp [String.startsWith_string_iff])
  rw [this]
  rfl

/-! ## Certificates -/

/-- The parse of a byte array whose list is the encoding of `c`. -/
theorem parse_of_list {c : Ast} {b : ByteArray} (h : Encode.ast c = some b.data.toList) :
    parse b = .ok c := by
  apply parse_encode
  unfold encode
  rw [h]
  simp

/-- **A component certificate from the list encoder**: if `Binary.Encode.ast c` is the file's
byte list, the file parses to `c`. -/
theorem is_of_ast {X : Value Ast} (hf : X.format = Silmaril.Project.Formats.wasmComponent) {c : Ast}
    (h : Encode.ast c = some X.bytes.data.data.toList) : X.Is c := by
  show X.format.parse X.bytes = some c
  rw [hf]
  exact Silmaril.Project.Formats.wasmComponent_parse_eq.mpr (parse_of_list h)

/-- **A WIT package value through a component AST**: its decoding is the fast decoding of the
AST's sections. -/
theorem witBinary_parse_of_ast {X : Value Package} (hf : X.format = Silmaril.Project.Formats.witBinary)
    {c : Ast} (h : Encode.ast c = some X.bytes.data.data.toList) :
    X.parse = witDecodeFast c := by
  show X.format.parse X.bytes = _
  rw [hf]
  show (match decodePackage X.bytes.data with | .ok p => some p | .error _ => none) = _
  unfold decodePackage
  rw [parse_of_list h]
  cases c with
  | mk ss =>
    simp only [witDecodeFast, Ast.sections, ← decodeSections_eq_fast]
    rfl

theorem extractPayloadFast_of {m : ByteArray} {j e : Nat} (h : payloadAt m j e = true) :
    extractPayloadFast m = .ok (sliceOf m j e) := by
  unfold payloadAt at h
  split at h
  · rename_i d hd
    rw [hd, ByteArray.ext (Array.ext' (of_decide_eq_true h))]
  · cases h

/-- **A core module's embedded world through its payload's AST**: if the `component-type`
section's contents are the slice `j` to `e` and the list encoder writes that slice from `c`,
the `wasm.module.world` reading is the world decoding of `c`'s sections. -/
theorem wasmModuleWorld_parse_of_ast {X : Value (PackageName × String × World × StringEncoding)}
    (hf : X.format = Silmaril.Project.Formats.wasmModuleWorld) {j e : Nat} {c : Ast}
    (hp : payloadAt X.bytes.data j e = true)
    (hc : Encode.ast c = some (sliceOf X.bytes.data j e).data.toList) :
    X.parse = worldDecodeFast c := by
  show X.format.parse X.bytes = _
  rw [hf]
  show (match extractWorldType X.bytes.data with | .ok w => some w | .error _ => none) = _
  unfold extractWorldType
  rw [extractPayload_eq_fast, extractPayloadFast_of hp]
  show (match decodeWorldType (sliceOf X.bytes.data j e) with
    | .ok w => some w | .error _ => none) = _
  unfold decodeWorldType
  rw [parse_of_list hc]
  cases c with
  | mk ss => rfl

end Silmaril.Project.WasmComponents.Kernel

end
