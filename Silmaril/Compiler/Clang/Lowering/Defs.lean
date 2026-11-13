module
public import Silmaril.Compiler.Clang.Defs
public import Silmaril.Compiler.Clang.ToAil.Defs
/-! The pure Clang AST to typed-Ail pass is separate from JSON import. Its
successful graph gives a modular pass relation; semantic preservation remains
a separate obligation. This interface uses strict translation and never the
imported optional recovery mode that omits unsupported function bodies.
-/
@[expose] public section
namespace Silmaril.Compiler.Clang.Lowering

abbrev TypedProgram := Silmaril.Cerberus.Ail.TypedProgram

def lower (node : Node) : Except String TypedProgram :=
  Silmaril.Clang.ToAil.translate node

def Lowers : Silmaril.EncRel Node TypedProgram := fun node program => lower node = .ok program

/-- An AST value is first decoded, then passed to the pure Ail lowering. -/
def DecodesAil : Silmaril.Formats.Json.Decode.Schema TypedProgram :=
  Silmaril.EncRel.comp Decodes Lowers

/-- The byte-level pipeline still exposes a JSON-stage derivation. -/
def ParsesAil : Silmaril.EncRel Silmaril.Formats.Bytes TypedProgram :=
  Silmaril.Formats.Json.Decode.text DecodesAil

def decodeAil? (json : Silmaril.Formats.Json.Ast) : Option TypedProgram := do
  let node ← decode? json
  (lower node).toOption

def parseAil? : Silmaril.Formats.Bytes → Option TypedProgram :=
  Silmaril.Formats.Json.Decode.parse? decodeAil?

end Silmaril.Compiler.Clang.Lowering
