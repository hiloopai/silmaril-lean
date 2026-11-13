module

public import Silmaril.Cerberus.Schema.Generated.Defs
public import Silmaril.Cerberus.Names.Defs
meta import Silmaril.Cerberus.Schema.Reflect.Defs

@[expose] public section

/-! # Agreement of the Core syntax with the pinned Lem schema

`schema_agreement` resolves all 81 `Names` targets as Lean types after their
parameters. For the 60 variants and four records, the agreement theorems check
constructor order and arities or record field order, renamed through `Names`.
Every rename names a distinct Lem constructor or field. `covers_generated` proves
coverage of all 81 generated Lem entries, one to one and in order. Abstract and
abbreviated representations and payload types are not compared.
-/

namespace Silmaril.Cerberus.Schema

/-- The Lem constructor or field names of a shape. -/
def Shape.names : Shape → List String
  | .record fields => fields
  | .variant constructors => constructors.map Prod.fst
  | .abstract | .abbrev => []

/-- A Lem shape with its constructor or field names renamed through `type`. -/
def Shape.rename (type : Names.TypeName) : Shape → Shape
  | .record fields => .record (fields.map type.rename)
  | .variant constructors =>
      .variant (constructors.map fun (tag, arity) => (type.rename tag, arity))
  | shape => shape

/-- Check renamed constructor or record shapes and distinct valid rename keys.
Abstract and abbreviated shapes impose no representation check. -/
def agrees (type : Names.TypeName) (lem : Shape) (constructors : List (String × Nat))
    (fields : List String) : Bool :=
  type.renames.all (lem.names.contains ·.1) && decide (type.renames.map Prod.fst).Nodup &&
    match lem.rename type with
    | .variant renamed => renamed == constructors
    | .record renamed => renamed == fields
    | .abstract | .abbrev => true

/-- `agrees` for the `Names` entry and generated schema of the Lem type `name`. -/
def agreesAt (name : String) (constructors : List (String × Nat)) (fields : List String) :
    Bool :=
  match Names.types.find? (·.cerberus == name), typeSchemas.find? (·.name == name) with
  | some type, some schema => agrees type schema.body.shape constructors fields
  | _, _ => false

schema_agreement

end Silmaril.Cerberus.Schema
