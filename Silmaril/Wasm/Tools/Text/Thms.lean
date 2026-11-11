module

public import Silmaril.Wasm.Tools.Text.Defs
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleSound
public import Silmaril.Encoding.TextExtras
public import Silmaril.Wasm.Tools.Names.Thms
public import Silmaril.Wasm.Tools.Layout.Thms
public import Silmaril.Wasm.Tools.Print.Thms

/-!
# Specification theorems of `wasm-tools parse` / `print` (core modules)

* `textToBinary_sound`: the output bytes and the input text encode one module, in the formal
  binary and text grammars.
* `watToBinary_sound`: for `parse`, the output bytes encode the module that the input
  (binary, or UTF-8 text) encodes.
* `binaryToWat_sound`: for `print`, the input bytes and the output text encode one module.
* `print_parse_roundtrip`: parsing printed text yields bytes encoding the same module as the
  original bytes (round trip modulo the binary normal form of the encoder: minimal LEB128, the
  encoder's section layout, custom sections other than the `name` section dropped).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Text

open Silmaril Silmaril.Wasm

open Silmaril.Wasm.Tools.Annot (stripTrivia)

theorem textTree?_sound {s : String} {x : Text.SExp} {m : Wasm.Module}
    (h : textTree? s = .ok (x, m)) : Text.Core.Encodes (stripTrivia s) m := by
  unfold textTree? at h
  split at h
  · cases h
  · rename_i tree htree
    split at h
    · cases h
    · rename_i m' hm
      cases h
      exact ⟨_, Formats.SExpEncoding.Wat.sexpWat_of_fullExec htree,
        Binaryen.Toolkit.Wat.parseSupported?_sound hm⟩

theorem textModule?_sound {s : String} {m : Wasm.Module} (h : textModule? s = .ok m) :
    Text.Core.Encodes (stripTrivia s) m := by
  unfold textModule? at h
  cases ht : textTree? s with
  | error e => simp [ht, Except.map] at h
  | ok p =>
    simp [ht, Except.map] at h
    subst h
    exact textTree?_sound (x := p.1) (by simpa using ht)

theorem namesFor_customs {cs : List Annot.Custom} {ns : List UInt8} (h : Binary.Customs ns) :
    Binary.Customs (namesFor cs ns) := by
  unfold namesFor
  split
  · exact .nil
  · exact h

theorem textToBinary_sound {s : String} {b : ByteArray} (h : textToBinary s = .ok b) :
    ∃ m, Text.Core.Encodes (stripTrivia s) m ∧ Binary.Core.Encodes b.data.toList m := by
  unfold textToBinary at h
  cases hm : textTree? s with
  | error e => simp [hm, bind, Except.bind] at h
  | ok p =>
    obtain ⟨x, m⟩ := p
    cases he : Binaryen.Exe.encodeModuleWith? (Binaryen.Exe.usesDataIdx m) m with
    | error e => simp [hm, he, bind, Except.bind] at h
    | ok bs =>
      cases hn : ((Names.ofTree x m (s.length + 1)).rename (Annot.nameAnnots s)).section with
      | error e => simp [hm, he, hn, bind, Except.bind] at h
      | ok ns =>
        simp [hm, he, hn, bind, Except.bind, pure, Except.pure] at h
        subst h
        exact ⟨m, textTree?_sound hm, by
          simpa using Layout.relayout_sound (Binaryen.Exe.encodeModuleWith?_sound he)
            (namesFor_customs (Names.section_sound hn))⟩

/-- `parse`: a binary input is returned unchanged and encodes a module; a text input is
UTF-8 text encoding (annotations removed) the module the output encodes. -/
theorem watToBinary_sound {i b : ByteArray} (h : watToBinary i = .ok b) :
    ∃ m, Binary.Core.Encodes b.data.toList m ∧
      ((isBinary i = true ∧ b = i) ∨
        (isBinary i = false ∧ ∃ s, String.fromUTF8? i = some s ∧
          Text.Core.Encodes (stripTrivia s) m)) := by
  unfold watToBinary at h
  split at h
  · rename_i hb
    split at h
    · rename_i m hd
      cases h
      exact ⟨m, Binary.Core.Decode.decodeModule_sound hd, .inl ⟨hb, rfl⟩⟩
    · cases h
  · rename_i hb
    split at h
    · cases h
    · rename_i s hs
      obtain ⟨m, ht, hbin⟩ := textToBinary_sound h
      exact ⟨m, hbin, .inr ⟨by simpa using hb, s, hs, ht⟩⟩

/-- `print`: the input bytes and the printed text (annotations removed) encode the same
module. -/
theorem binaryToWatWith_sound {cfg : Print.Config} {i : ByteArray} {t : String}
    (h : binaryToWatWith cfg i = .ok t) :
    ∃ m, Binary.Core.Encodes i.data.toList m ∧ Text.Core.Encodes (stripTrivia t) m := by
  unfold binaryToWatWith at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · rename_i hc
      cases h
      exact ⟨r.module, Print.printModule_sound hr hc⟩
    · split at h
      · cases h
      · split at h
        · rename_i a _ hc
          cases h
          exact ⟨r.module, Print.printModule_module hr, Print.check_sound hc⟩
        · cases h

theorem binaryToWat_sound {i : ByteArray} {t : String} (h : binaryToWat i = .ok t) :
    ∃ m, Binary.Core.Encodes i.data.toList m ∧ Text.Core.Encodes (stripTrivia t) m :=
  binaryToWatWith_sound h

/-- Round trip: printing, then parsing the printed text, gives bytes that encode the module
the original bytes encode. Byte equality is not claimed here (it is tested). -/
theorem print_parse_roundtrip {i b : ByteArray} {t : String}
    (hp : binaryToWat i = .ok t) (hq : textToBinary t = .ok b) :
    ∃ m, Binary.Core.Encodes i.data.toList m ∧ Binary.Core.Encodes b.data.toList m := by
  obtain ⟨m, hi, ht⟩ := binaryToWat_sound hp
  obtain ⟨m', ht', hb⟩ := textToBinary_sound hq
  have : m' = m := Text.Core.encodes_functional ht' ht
  subst this
  exact ⟨m', hi, hb⟩

/-- `parse -t` agrees with `print` after `parse`: the output text encodes the module of the
parsed bytes. -/
theorem watToWat_sound {i : ByteArray} {t : String} (h : watToWat i = .ok t) :
    ∃ b m, watToBinary i = .ok b ∧ Binary.Core.Encodes b.data.toList m ∧
      Text.Core.Encodes (stripTrivia t) m := by
  unfold watToWat at h
  cases hb : watToBinary i with
  | error e => simp [hb, bind, Except.bind] at h
  | ok b =>
    simp [hb, bind, Except.bind] at h
    obtain ⟨m, h1, h2⟩ := binaryToWat_sound h
    exact ⟨b, m, rfl, h1, h2⟩

end Silmaril.Wasm.Tools.Text
