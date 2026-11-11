module

public import Silmaril.Wasm.Tools.Print.Defs
public import Silmaril.Wasm.Tools.Parse.Thms
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound

/-!
# Specification theorems of `wasm-tools print` (core modules)

* `check_sound`: a passed check means the text, annotations removed, encodes the module in
  the Core 3.0 text grammar (`Text.Core.Encodes`).
* `printText_sound`: the module the printer prints is the one the input bytes encode in the
  binary grammar (`Binary.Core.Encodes`).
* `printModule_sound`: a certified `print` result: the input bytes and the output text
  (annotations removed) encode the same module.
* `print_parse_roundtrip`: parsing a certified printed text gives bytes encoding the module
  of the original bytes (round trip modulo the binary normal form: custom sections, LEB128
  widths and section layout are not part of the module).
* `printModule_unique`: that module is the only one the text denotes.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Print

open Silmaril Silmaril.Wasm
open Silmaril.Wasm.Tools.Annot (stripTrivia)

theorem readBack_sound {s : String} {m : Wasm.Module} (h : readBack s = some m) :
    Text.Core.Encodes s m := by
  unfold readBack at h
  split at h
  · cases h
  · rename_i x hx
    refine ⟨x, Formats.SExpEncoding.Wat.sexpWat_of_fullExec hx, ?_⟩
    split at h
    · rename_i c _
      cases h
      exact c.2
    · exact Binaryen.Toolkit.Wat.parseCanonical?_sound h

theorem check_sound {m : Wasm.Module} {t : String} (h : check m t = true) :
    Text.Core.Encodes (stripTrivia t) m := by
  unfold check at h
  split at h
  · rename_i m' hm'
    split at h
    · rename_i a a' ha ha'
      have hEq : a = a' := by simpa using h
      subst hEq
      have hmm : m = m' :=
        Binary.Core.functional (Binaryen.Exe.encodeModule?_sound ha)
          (Binaryen.Exe.encodeModule?_sound ha')
      subst hmm
      exact readBack_sound hm'
    · cases h
  · cases h

theorem printText_sound {cfg : Config} {b : ByteArray} {m : Wasm.Module} {t : String}
    (h : printText cfg b = .ok (m, t)) : Binary.Core.Encodes b.data.toList m := by
  unfold printText at h
  cases hd : Binary.Core.Decode.decodeModule b with
  | error e => simp [hd, Except.mapError, bind, Except.bind] at h
  | ok m' =>
    simp only [hd, Except.mapError, bind, Except.bind] at h
    split at h
    · cases h; exact Binary.Core.Decode.decodeModule_sound hd
    · cases h

/-- The module of any `print` result (certified or not) is the module of the input bytes. -/
theorem printModule_module {cfg : Config} {b : ByteArray} {r : Printed}
    (h : printModule cfg b = .ok r) : Binary.Core.Encodes b.data.toList r.module := by
  unfold printModule at h
  cases hp : printText cfg b with
  | error e => simp [hp, bind, Except.bind] at h
  | ok p =>
    simp only [hp, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact printText_sound hp

theorem printModule_sound {cfg : Config} {b : ByteArray} {r : Printed}
    (h : printModule cfg b = .ok r) (hc : r.certified = true) :
    Binary.Core.Encodes b.data.toList r.module ∧
      Text.Core.Encodes (stripTrivia r.text) r.module := by
  unfold printModule at h
  cases hp : printText cfg b with
  | error e => simp [hp, bind, Except.bind] at h
  | ok p =>
    obtain ⟨m, t⟩ := p
    simp only [hp, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨printText_sound hp, ?_⟩
    simp only at hc
    split at hc
    · cases hc
    · exact check_sound hc

/-- The module of a certified printed text is unique: any module the text denotes is the
module of the input bytes. -/
theorem printModule_unique {cfg : Config} {b : ByteArray} {r : Printed} {m : Wasm.Module}
    (h : printModule cfg b = .ok r) (hc : r.certified = true)
    (hm : Text.Core.Encodes (stripTrivia r.text) m) : m = r.module :=
  Text.Core.encodes_functional hm (printModule_sound h hc).2

/-- Round trip: `parse` of a certified `print` output encodes the module of the input. -/
theorem print_parse_roundtrip {cfg : Config} {b b' : ByteArray} {r : Printed}
    (h : printModule cfg b = .ok r) (hc : r.certified = true)
    (hp : Parse.parseModule (stripTrivia r.text) = .ok b') :
    Binary.Core.Encodes b'.data.toList r.module ∧ Binary.Core.Encodes b.data.toList r.module :=
  ⟨Parse.parseModule_module_unique hp (printModule_sound h hc).2, (printModule_sound h hc).1⟩

end Silmaril.Wasm.Tools.Print
