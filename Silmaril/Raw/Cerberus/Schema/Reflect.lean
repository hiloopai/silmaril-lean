module

public meta import Lean
public import Silmaril.Cerberus.Schema.Basic.Defs
public meta import Silmaril.Cerberus.Schema.Basic.Defs
public import Silmaril.Cerberus.Names.Defs
public meta import Silmaril.Cerberus.Names.Defs

/-! # Reflected shapes of the Silmaril declarations

`schema_agreement` resolves every target in `Names.types` and checks that it is a
type after its parameters, including abstract memory-model projections. It proves
structural agreement for 60 Lem variants and four records renamed through `Names`,
and coverage of all 81 generated Lem entries in order. Abstract and abbreviated
representations and payload types are not compared.

The Silmaril shape is reflected from the elaborated environment: the last name
component and field count of each constructor in declaration order, and the field
names of a structure. Type parameters are not fields. The reflected shape is a
closed term, so each equation can be decided by the kernel. The statements refer to
`agreesAt` and `typeSchemas`, which the using module defines.
-/

public meta section

namespace Silmaril.Cerberus.Schema

open Lean Elab Command Meta

instance : ReduceEval (String × String) where
  reduceEval e := do
    let_expr Prod.mk _ _ a b := (← whnf e) | throwError "not a pair: {e}"
    return (← reduceEval a, ← reduceEval b)

instance : ReduceEval Names.TypeName where
  reduceEval e := do
    let_expr Names.TypeName.mk cerberus silmaril renames := (← whnf e)
      | throwError "not a TypeName: {e}"
    return ⟨← reduceEval cerberus, ← reduceEval silmaril, ← reduceEval renames⟩

/-- Resolve a type declaration and reflect its constructors and structure fields.
Non-inductive types, including memory-model projections, have empty shapes. -/
def reflect (n : Lean.Name) : MetaM (List (String × Nat) × List String) := do
  let env ← getEnv
  let some declaration := env.find? n | throwError "schema target {n} does not exist"
  forallTelescopeReducing declaration.type fun _ result => do
    unless result.isSort do
      throwError "schema target {n} is not a type after its parameters"
  let .inductInfo info := declaration | return ([], [])
  let constructors ← info.ctors.mapM fun c => do
    let some (.ctorInfo ctor) := env.find? c | throwError "{c} is not a constructor"
    let .str _ tag := c | throwError "{c} has no string name"
    return (tag, ctor.numFields)
  let fields := if isStructure env n then (getStructureFields env n).toList.map (·.toString)
    else []
  return (constructors, fields)

elab "schema_agreement" : command => do
  let types : List Names.TypeName ← liftTermElabM <| reduceEval (mkConst ``Names.types)
  let agreesAt := mkIdent `Silmaril.Cerberus.Schema.agreesAt
  let typeSchemas := mkIdent `Silmaril.Cerberus.Schema.typeSchemas
  let names := mkIdent ``Names.types
  for type in types do
    let (constructors, fields) ← liftTermElabM <| reflect type.silmaril
    let theoremName := mkIdent <| .mkSimple <| "agrees_" ++ type.cerberus.replace "." "_"
    elabCommand (← `(command|
      theorem $theoremName :
          $agreesAt $(quote type.cerberus) $(quote constructors) $(quote fields) = true := by
        decide +kernel))
  elabCommand (← `(command|
    theorem $(mkIdent `covers_generated) :
        List.map Names.TypeName.cerberus $names = List.map TypeSchema.name $typeSchemas := by
      decide +kernel))

/--
error: schema target Silmaril.Cerberus.DoesNotExist does not exist
-/
#guard_msgs in
run_meta do
  let mutated : Names.TypeName := ⟨"Symbol.digest", `Silmaril.Cerberus.DoesNotExist, []⟩
  discard <| reflect mutated.silmaril

/--
error: schema target Silmaril.Cerberus.Identifier.key is not a type after its parameters
-/
#guard_msgs in
run_meta do
  let mutated : Names.TypeName := ⟨"Symbol.digest", ``Silmaril.Cerberus.Identifier.key, []⟩
  discard <| reflect mutated.silmaril

end Silmaril.Cerberus.Schema
