module
public import Silmaril.Compiler.Clang.Lowering.Defs
public import Silmaril.Compiler.Clang.Thms
public section
namespace Silmaril.Compiler.Clang.Lowering

theorem lowers_functional : Lowers.Functional := by
  intro node a b ha hb
  exact Except.ok.inj (ha.symm.trans hb)

theorem decodeAil?_iff {json : Silmaril.Formats.Json.Ast} {program : TypedProgram} :
    decodeAil? json = some program ↔ DecodesAil json program := by
  cases h : decode? json with
  | none => simp [decodeAil?, DecodesAil, Silmaril.EncRel.comp, ← decode?_iff, h]
  | some node =>
    cases hl : lower node <;> simp [decodeAil?, DecodesAil, Lowers,
      Silmaril.EncRel.comp, ← decode?_iff, h, hl, Except.toOption]

theorem parseAil?_iff {bytes : Silmaril.Formats.Bytes} {program : TypedProgram} :
    parseAil? bytes = some program ↔ ParsesAil bytes program := by
  rw [parseAil?, Silmaril.Formats.Json.Decode.parse?_iff]
  constructor
  · rintro ⟨json, hjson, hast⟩
    exact ⟨json, hjson, decodeAil?_iff.mp hast⟩
  · rintro ⟨json, hjson, hast⟩
    exact ⟨json, hjson, decodeAil?_iff.mpr hast⟩

theorem decodesAil_functional : DecodesAil.Functional := by
  rintro json a b ⟨node, hn, ha⟩ ⟨node', hn', hb⟩
  have heq : node = node' := decodes_functional hn hn'
  subst node'
  exact lowers_functional ha hb

theorem parsesAil_functional : ParsesAil.Functional :=
  Silmaril.Formats.Json.Decode.text_functional decodesAil_functional

end Silmaril.Compiler.Clang.Lowering
