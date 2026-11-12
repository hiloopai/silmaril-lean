module

public import Silmaril.Wasm.Tools.Names.Defs
public import Silmaril.Wasm.Binaryen.Exe.EncodeBaseSound
public import Silmaril.Wasm.Binary.Core.Modules

/-!
# Custom sections do not change the module a binary encodes

`encodes_append_custom`: appending custom sections to a binary keeps the module it encodes
(custom sections are not part of the abstract syntax). `customSection_sound`: the bytes of
`customSection` are a custom section. Together: `section_sound`, adding the `name` section
that `wasm-tools parse` writes is harmless for the encoded module.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Names

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary

theorem customs_append {c s : Bytes} (hc : Customs c) (hs : Customs s) : Customs (c ++ s) := by
  induction hc with
  | nil => simpa using hs
  | cons hb _ ih => simpa [List.append_assoc] using Customs.cons hb ih

theorem encodes_append_custom {b s : Bytes} {m : Wasm.Module} (h : Core.Encodes b m)
    (hs : Customs s) : Core.Encodes (b ++ s) m := by
  cases h with
  | mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ htg h₆ hgl h₇ hex h₈ hst h₉ hel h₁₀ hdc
      h₁₁ hco h₁₂ hda h₁₃ hcount hdataidx hfuncs =>
    have := Core.ModuleWithImports.mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ htg h₆ hgl h₇ hex
      h₈ hst h₉ hel h₁₀ hdc h₁₁ hco h₁₂ hda (customs_append h₁₃ hs) hcount hdataidx hfuncs
    simpa [List.append_assoc] using this

theorem customSection_sound {nm : String} {p bs : List UInt8}
    (h : customSection nm p = .ok bs) : Customs bs := by
  unfold customSection at h
  obtain ⟨bn, hbn, h⟩ := Binaryen.Exe.bind_ok h
  obtain ⟨lb, hlb, h⟩ := Binaryen.Exe.bind_ok h
  cases h
  have hsec : CustomSec ([0] ++ lb ++ (bn ++ p)) :=
    ⟨[()], Section.mk (Binaryen.Exe.encU32_sound hlb) rfl
      (Custom.mk p (Binaryen.Exe.encName_sound hbn))⟩
  simpa using Customs.cons hsec Customs.nil

theorem section_sound {n : NameTable} {bs : List UInt8} (h : n.section = .ok bs) : Customs bs := by
  unfold NameTable.section at h
  split at h
  · cases h; exact Customs.nil
  · exact customSection_sound h

/-- Adding the `name` section to an encoding keeps the module. -/
theorem encodes_with_names {b bs : Bytes} {m : Wasm.Module} {n : NameTable}
    (h : Core.Encodes b m) (hn : n.section = .ok bs) : Core.Encodes (b ++ bs) m :=
  encodes_append_custom h (section_sound hn)

end Silmaril.Wasm.Tools.Names
