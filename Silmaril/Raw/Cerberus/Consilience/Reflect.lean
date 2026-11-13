module

public meta import Lean
public import Silmaril.Cerberus.Names.Defs
public meta import Silmaril.Cerberus.Schema.Reflect.Defs

/-! # Constructor names for consilience

`names_constructor%` resolves a verbatim Lem tag through `Names`. The resulting
constructor application and every equation about it are checked by the kernel.
`consilience_constructors%` reflects declaration order and arities as a closed
list, as the schema check does for the hand port.
-/

public meta section

namespace Silmaril.Cerberus.Consilience

open Lean Elab Term Meta

elab "names_constructor%" lem:str tag:str : term => do
  let types : List Names.TypeName ← reduceEval (mkConst ``Names.types)
  let some entry := types.find? (·.cerberus == lem.getString)
    | throwError "no Names entry for {lem}"
  let constructor := entry.silmaril ++ .mkSimple (entry.rename tag.getString)
  let some (.ctorInfo _) := (← getEnv).find? constructor
    | throwError "Names target {constructor} is not a constructor"
  return mkConst constructor

elab "consilience_constructors%" type:ident : term => do
  let typeName ← realizeGlobalConstNoOverloadWithInfo type
  let (constructors, _) ← Schema.reflect typeName
  return toExpr constructors

end Silmaril.Cerberus.Consilience
