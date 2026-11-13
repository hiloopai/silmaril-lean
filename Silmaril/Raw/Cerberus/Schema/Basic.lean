module

@[expose] public section

/-! # Structural schema of Cerberus's Lem types

`sil cerberus` records each Lem type declaration reachable from `Core.file` at
the pinned Cerberus revision: its type parameters, and either its constructors
in order with their ordered payload types, its record fields, the type it
abbreviates, or that it is abstract (OCaml-backed). Type names are resolved to
the declaring Lem module (`Core.generic_pexpr`, `Symbol.sym`); Lem library
types (`list`, `maybe`, `map`, `nat`, …) keep their bare names.

`C of a * b` has the two fields `a` and `b`; `C of (a * b)` has the single field
`.tuple [a, b]`. A schema records shapes only; it says nothing about which
values the OCaml code produces.
-/

namespace Silmaril.Cerberus.Schema

/-- A Lem type expression. `var` is a type parameter, without its quote. -/
inductive LemType where
  | var (name : String)
  | app (name : String) (arguments : List LemType)
  | tuple (components : List LemType)
  deriving Repr

/-- A variant constructor: its verbatim Lem name and its ordered payload. -/
structure Constructor where
  tag : String
  fields : List LemType
  deriving Repr

/-- The right-hand side of a Lem type declaration. -/
inductive Body where
  | abstract
  | abbrev (target : LemType)
  | record (fields : List (String × LemType))
  | variant (constructors : List Constructor)
  deriving Repr

structure TypeSchema where
  /-- `Module.name`, with the Lem type name verbatim. -/
  name : String
  parameters : List String
  body : Body
  /-- SHA-256 of the comment-free declaration, tokens joined by single spaces. -/
  digest : String
  deriving Repr

/-- What the wire format depends on: constructor tags, their order and arities,
or record field names in order. -/
inductive Shape where
  | abstract
  | abbrev
  | record (fields : List String)
  | variant (constructors : List (String × Nat))
  deriving DecidableEq, Repr

def Body.shape : Body → Shape
  | .abstract => .abstract
  | .abbrev _ => .abbrev
  | .record fields => .record (fields.map Prod.fst)
  | .variant constructors => .variant (constructors.map fun c => (c.tag, c.fields.length))

end Silmaril.Cerberus.Schema
