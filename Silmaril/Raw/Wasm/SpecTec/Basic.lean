module

public import Silmaril.Formats.SExp.Tagged

@[expose] public section

/-! # Structural data exchanged with SpecTec

Constructor tags and ordered payloads are separate from SpecTec's typing and
execution judgments. A schema records payload families and dependencies on
earlier fields; its digest also covers the upstream binders and side conditions.
-/

namespace Silmaril.Wasm.SpecTecEnc

abbrev Value := Silmaril.Formats.TExpr String Int

def node (tag : String) (args : List Value) : Value :=
  Silmaril.Formats.TExpr.ofList tag args

def nat (n : Nat) : Value := .atom (Int.ofNat n)

def list (xs : List Value) : Value := node "$list" xs

def option {α : Type} (f : α → Value) : Option α → Value
  | none => node "$none" []
  | some a => node "$some" [f a]

/-- References in a dependent family point to earlier tuple fields. -/
inductive FieldType where
  | named (name : String) (parameters : List Nat)
  | optional (element : FieldType)
  | sequence (element : FieldType)
  | namedList (element : FieldType)
  deriving DecidableEq, Repr

structure ConstructorSchema where
  tag : String
  fields : List FieldType
  /-- SHA-256 of the complete decoded case, including binders and premises. -/
  digest : String
  deriving DecidableEq, Repr

structure Argument where
  type : FieldType
  value : Value

structure Constructor where
  tag : String
  arguments : List Argument

def Constructor.toValue (c : Constructor) : Value := node c.tag (c.arguments.map Argument.value)

/-- Structural agreement only: semantic predicates on payloads are separate. -/
def Constructor.hasShape (c : Constructor) (s : ConstructorSchema) : Prop :=
  c.tag = s.tag ∧ c.arguments.map Argument.type = s.fields

theorem Constructor.hasShape_arity {c : Constructor} {s : ConstructorSchema}
    (h : c.hasShape s) : c.arguments.length = s.fields.length := by
  simpa using congrArg List.length h.2

end Silmaril.Wasm.SpecTecEnc
