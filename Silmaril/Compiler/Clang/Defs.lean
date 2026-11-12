module
public import Silmaril.Compiler.Clang.AST.Defs
public import Silmaril.Compiler.Clang.Json.Defs
public import Silmaril.Formats.Json.Decode.Defs
/-! Clang's AST schema is a format inside standard JSON. JSON syntax parsing,
the Unicode/unique-key bridge, AST decoding, and the translation-unit root
condition are separate interfaces. The schema below specifies the imported
decoder's successful graph; it is not an independent Clang specification.
-/
@[expose] public section
namespace Silmaril.Compiler.Clang

abbrev Node := Silmaril.Clang.Node

/-- Decode one Clang AST node from a standard JSON value. Opaque documentation
nodes follow the imported decoder's policy; unknown semantic node kinds fail. -/
def Decodes : Silmaril.Formats.Json.Decode.Schema Node :=
  Silmaril.Formats.Json.Decode.fromLeanDecoder Silmaril.Clang.Json.decodeNode

/-- Complete UTF-8 RFC JSON input followed by Clang's AST schema decoder. -/
def Parses : Silmaril.EncRel Silmaril.Formats.Bytes Node :=
  Silmaril.Formats.Json.Decode.text Decodes

def decode? : Silmaril.Formats.Json.Ast → Option Node :=
  Silmaril.Formats.Json.Decode.leanDecode? Silmaril.Clang.Json.decodeNode

def parse? : Silmaril.Formats.Bytes → Option Node :=
  Silmaril.Formats.Json.Decode.parseLean? Silmaril.Clang.Json.decodeNode

/-- Child nodes are valid ASTs but are not complete translation units. -/
def IsTranslationUnit (node : Node) : Prop :=
  node.kind? = some .translationUnitDecl

instance (node : Node) : Decidable (IsTranslationUnit node) :=
  inferInstanceAs (Decidable (node.kind? = some .translationUnitDecl))

def ParsesTranslationUnit : Silmaril.EncRel Silmaril.Formats.Bytes Node :=
  Parses.restrict IsTranslationUnit

def parseTranslationUnit? (bytes : Silmaril.Formats.Bytes) : Option Node := do
  let node ← parse? bytes
  if IsTranslationUnit node then some node else none

end Silmaril.Compiler.Clang
