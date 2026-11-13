module

public import Silmaril.Project.Formats.Wit.Defs
public import Silmaril.Project.Formats.Component.Thms
public import Silmaril.Wasm.Wit.Text.Thms
public import Silmaril.Wasm.Wit.Elab.Thms
public import Silmaril.Wasm.Wit.Binary.Thms

/-!
# Formats `wit.*` and `wasm.module.world`: laws

* `witPackage_sound` (law `sound` for `WitPackageRel`), from `Wit.Elab.elaborate_sound`: the
  text is a valid WIT universe, and the elaborated package is valid in the environment it comes
  with, has distinct names and is named after the main package.
* `witBinary_sound` (law `sound` for `WitBinaryRel`): the bytes are a component of the
  component grammar and its sections decode to the package.
* `wasmModuleWorld_sound` (law `sound` for `ModuleWorldRel`).
* `witText_print_parse`: a printable document prints to bytes that parse back to its normal form
  (`Wit.Text.parse_print`); not the `roundtrip` law, which would need every document printable.
* `witBinary_encode`: the bytes `encodePackage` writes for a valid package with distinct names
  read back under `wit.binary` as its canonical form (`decodePackage_encodePackage_canon`).
* `witPackage_witBinary`: the two WIT formats agree. If WIT text reads under `wit.package` as
  `(P, env)` and `encodePackage env P` writes `b`, then `b` reads under `wit.binary` as
  `P.canon` (`elaborate_decode`).

There are no kernel examples: on the small fixtures of `examples/project-formats`
(`hello.wit`, `hello-wit.wasm`, `module-getter.wasm`) the kernel takes 16 s for `wit.text` and
over 200 s for the other two. `gen-components.lean` checks them by compiled evaluation.
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Wasm

theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, s.isValidUTF8]

theorem witPackage_sound : witPackage.SoundFor WitPackageRel := by
  intro b r h
  simp only [witPackage, Silmaril.Project.Format.andThen, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨d, hd, hr⟩ := h
  simp only [elabDocument] at hr
  split at hr
  · rename_i r' he
    cases hr
    have hs := Wit.Elab.elaborate_sound he
    exact ⟨d, hd, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
  · cases hr

theorem witBinary_parse_eq {b : Silmaril.Formats.Bytes} {p : Wit.Binary.Package} :
    witBinary.parse b = some p ↔ Wit.Binary.decodePackage b.data = .ok p := by
  simp only [witBinary]
  split <;> simp_all

theorem witBinary_sound : witBinary.SoundFor WitBinaryRel := by
  intro b p h
  have h' := witBinary_parse_eq.mp h
  unfold Wit.Binary.decodePackage at h'
  split at h'
  · rename_i ss hc
    exact ⟨.mk ss, wasmComponent_sound _ _ (wasmComponent_parse_eq.mpr hc), h'⟩
  · cases h'

theorem wasmModuleWorld_sound : wasmModuleWorld.SoundFor ModuleWorldRel := by
  intro b w h
  simp only [wasmModuleWorld] at h
  split at h
  · rename_i w' he
    cases h
    simp only [Wit.Binary.extractWorldType, bind, Except.bind] at he
    split at he
    · cases he
    · rename_i payload hp
      unfold Wit.Binary.decodeWorldType at he
      split at he
      · rename_i ss hc
        exact ⟨payload, .mk ss, hp, wasmComponent_sound _ _ (wasmComponent_parse_eq.mpr hc), he⟩
      · cases he
  · cases h

theorem witText_print_parse {p} (hp : witText.print = some p) {d : Wit.Document}
    (hd : Wit.Text.printable d = true) {b : Silmaril.Formats.Bytes} (h : p d = some b) :
    witText.parse b = some (Wit.Text.Document.norm d) := by
  cases hp
  cases h
  simp only [witText, fromUTF8?_toUTF8, Option.bind_some]
  exact Wit.Text.parse_print d hd

theorem witBinary_encode {deps : Wit.Binary.Env} {p : Wit.Binary.Package} (hv : p.Valid deps)
    (hu : p.NamesUnique) {b : ByteArray} (h : Wit.Binary.encodePackage deps p = .ok b) :
    witBinary.parse ⟨b⟩ = some p.canon :=
  witBinary_parse_eq.mpr (Wit.Binary.decodePackage_encodePackage_canon hv hu h)

theorem witPackage_witBinary {t : Silmaril.Formats.Bytes} {P : Wit.Binary.Package}
    {env : Wit.Binary.Env} (h : witPackage.parse t = some (P, env)) {b : ByteArray}
    (hb : Wit.Binary.encodePackage env P = .ok b) : witBinary.parse ⟨b⟩ = some P.canon := by
  obtain ⟨_, _, _, hv, hu, _⟩ := witPackage_sound _ _ h
  exact witBinary_encode hv hu hb

end Silmaril.Project.Formats

silmaril format_law wit.package sound := Silmaril.Project.Formats.witPackage_sound
  (rel := Silmaril.Project.Formats.WitPackageRel)
silmaril format_law wit.binary sound := Silmaril.Project.Formats.witBinary_sound
  (rel := Silmaril.Project.Formats.WitBinaryRel)
silmaril format_law wasm.module.world sound := Silmaril.Project.Formats.wasmModuleWorld_sound
  (rel := Silmaril.Project.Formats.ModuleWorldRel)
