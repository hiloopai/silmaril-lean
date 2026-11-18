module

public import Silmaril.Formats.Json.Fast.Parser.Defs

@[expose] public section
namespace Silmaril.Formats.Json.Fast.Parser

abbrev White (chars : List Char) : Prop := ∀ char ∈ chars, JsonWire.Internal.white .rfc8259 char = true

/-- The consumed character span of a nonempty container tail, starting after its
opening delimiter. The item relation records both the lexeme and its decoded value. -/
inductive Tail {Item : Type} (close : Char) (Accept : List Char → Item → Prop) :
    List Char → List Item → Prop where
  | last {left lexeme right : List Char} {item : Item} :
    White left → Accept lexeme item → White right →
    Tail close Accept (left ++ lexeme ++ right ++ [close]) [item]
  | next {left lexeme right span : List Char} {item : Item} {items : List Item} :
    White left → Accept lexeme item → White right → Tail close Accept span items →
    Tail close Accept (left ++ lexeme ++ right ++ (',' :: span)) (item :: items)

end Silmaril.Formats.Json.Fast.Parser
