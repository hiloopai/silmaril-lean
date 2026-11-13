module

public import Silmaril.Wasm.Component.Chunked.Thms
public import Silmaril.Wasm.Component.BinaryP3.Thms

/-!
# Chunked certificates for whole components with async built-ins

**PROVED**: per-section certificates of a component compose to its parse under the
grammar with async built-ins (`Silmaril.Wasm.Component.BinaryP3`, component-model `d095e2f`):

* `sections_of`: sections whose encodings are consecutive pieces encode to the pieces'
  concatenation;
* `ast_of`: with the preamble in front and the pieces between sorted cut points covering
  the file, the component encodes to the whole file;
* `parse_of_ast`: then `BinaryP3.parse` reads the file back as that component
  (`BinaryP3.parse_encode`);
* the three kinds of pieces: `ofV0_eq` (a section of the old grammar, certified with the
  old encoder: the new encoder writes the same bytes, `RoundTrip.section_ofV0`),
  `coreModule_eq` (a core module kept as the bytes of its slice: only its id and its
  size are read) and, for `canon` sections with async built-ins, a kernel evaluation of
  `BinaryP3.Encode.section_` on the section's window.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Chunked

open Silmaril.Parse.ByteParse (Bytes)
open Silmaril.Wasm.Component.BinaryP3 (Section Ast)

theorem sections_of :
    ∀ {ss : List Section} {fs : List Bytes},
      List.Forall₂ (fun s f => BinaryP3.Encode.section_ s = some f) ss fs →
        BinaryP3.Encode.sections ss = some fs.flatten
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [BinaryP3.Encode.sections, h, sections_of hs, Option.bind_eq_bind,
      Option.bind_some, List.flatten_cons]
    rfl

/-- **A whole component from per-section certificates.** -/
theorem ast_of (l : List UInt8) {cuts : List Nat} {ss : List Section}
    (hpre : slice l 0 8 = Silmaril.Wasm.Component.Binary.preambleBytes)
    (hs : sorted 8 cuts = true) (hend : lastCut 8 cuts = l.length)
    (h : List.Forall₂ (fun s f => BinaryP3.Encode.section_ s = some f) ss (pieces l 8 cuts)) :
    BinaryP3.Encode.ast (.mk ss) = some l := by
  have e : l = slice l 0 8 ++ slice l 8 (lastCut 8 cuts) := by
    rw [slice_append l (by omega) (by have := sorted_le_last hs; omega), hend]
    simp [slice]
  simp only [BinaryP3.Encode.ast, sections_of h, ← slice_eq_flatten l 8 cuts hs, ← hpre,
    Option.bind_eq_bind, Option.bind_some, ← e]
  rfl

/-- **The parse of a whole file** from the encoding of a component. -/
theorem parse_of_ast {c : Ast} {l : List UInt8} (h : BinaryP3.Encode.ast c = some l) :
    BinaryP3.parse (arr l) = .ok c := by
  refine BinaryP3.parse_encode ?_
  simp only [BinaryP3.encode, h, Option.map_some, arr]

/-- A section of the old grammar, certified with the old encoder. -/
theorem ofV0_eq {s : Silmaril.Wasm.Component.Binary.Section} {b : Bytes}
    (h : Silmaril.Wasm.Component.Binary.Encode.section_ s = some b) :
    BinaryP3.Encode.section_ (Section.ofV0 s) = some b := by
  rw [BinaryP3.RoundTrip.section_ofV0]
  exact h

/-- **A core module section from its frame**: its id byte, its minimal LEB128 size and its
length; the module's bytes are its slice, not read. -/
theorem coreModule_eq (l : List UInt8) {s x e : Nat}
    (hid : slice l s (s + 1) = [1])
    (hsz : Silmaril.Parse.ByteParse.Enc.u32 (e - x) = some (slice l (s + 1) x))
    (h₁ : s + 1 ≤ x) (h₂ : x ≤ e) (h₃ : e ≤ l.length) :
    BinaryP3.Encode.section_ (.coreModule (arr (slice l x e))) = some (slice l s e) := by
  have h := frameEnc_of l hid hsz h₁ h₂ h₃
  simp only [frameEnc] at h
  simp only [BinaryP3.Encode.section_, arr, Option.bind_eq_bind]
  cases hs : Silmaril.Parse.ByteParse.Enc.sized (slice l x e) <;> simp_all

end Silmaril.Wasm.Component.Chunked

end
