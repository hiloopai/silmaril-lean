module
public import Silmaril.Compiler.Clang.Defs
public import Silmaril.Formats.Json.Decode.Thms
public section
namespace Silmaril.Compiler.Clang

theorem decode?_iff {json : Silmaril.Formats.Json.Ast} {node : Node} :
    decode? json = some node ↔ Decodes json node :=
  Silmaril.Formats.Json.Decode.leanDecode?_iff

theorem parse?_iff {bytes : Silmaril.Formats.Bytes} {node : Node} :
    parse? bytes = some node ↔ Parses bytes node :=
  Silmaril.Formats.Json.Decode.parseLean?_iff

theorem decodes_functional : Decodes.Functional :=
  Silmaril.Formats.Json.Decode.fromLeanDecoder_functional _

theorem parses_functional : Parses.Functional :=
  Silmaril.Formats.Json.Decode.text_functional decodes_functional

theorem parseTranslationUnit?_iff {bytes : Silmaril.Formats.Bytes} {node : Node} :
    parseTranslationUnit? bytes = some node ↔ ParsesTranslationUnit bytes node := by
  constructor
  · intro h
    cases hn : parse? bytes with
    | none => simp [parseTranslationUnit?, hn] at h
    | some result =>
      by_cases ht : IsTranslationUnit result
      · simp [parseTranslationUnit?, hn, ht] at h
        subst node
        exact ⟨parse?_iff.mp hn, ht⟩
      · simp [parseTranslationUnit?, hn, ht] at h
  · rintro ⟨hparse, htu⟩
    simp [parseTranslationUnit?, parse?_iff.mpr hparse, htu]

theorem parsesTranslationUnit_functional : ParsesTranslationUnit.Functional := by
  intro bytes a b ha hb
  exact parses_functional ha.1 hb.1

end Silmaril.Compiler.Clang
