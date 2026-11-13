module

public import Silmaril.Cerberus.Elaboration.State.Defs
public import Silmaril.Cerberus.Elaboration.Runtime.Defs

/-! The actual empty-argument call branch from pinned
`translation.lem:2635–2671`. The recursive expression dispatcher owns the
function-designator child, source annotations and full-expression boundary.
The returned Core retains metadata checks and the real `ccall` constructor;
there are no argument objects on this source branch. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Calls
open Silmaril.Cerberus
open Construction

def liftError {α : Type} : Except String α → State.ElabM α
  | .ok value => pure value
  | .error why => throw (.message why)

def zeroArguments (runtime : List Runtime.Binding) (location : Loc)
    (annotations : List Annot) (designatorType : Ctype)
    (designator : State.ElabM Effect) : State.ElabM Effect := do
  let returnType ← match designatorType with
    | .mk _ (.pointer _ (.mk _ (.functionNoParams (_, result)))) => pure result
    | .mk _ (.pointer _ (.mk _ (.function (_, result) parameters variadic))) =>
        if parameters.isEmpty && !variadic then pure result
        else throw (.message "invalid: empty call expects no fixed or variadic parameters")
    | _ => throw (.message "invalid: call designator is not a function pointer")
  let function ← State.wrappedFreshSymbol (.loaded .pointer)
  let result ← State.wrappedFreshSymbol .ctype
  let parameters ← State.wrappedFreshSymbol (.list .ctype)
  let core ← designator
  let signature ← liftError <| tuplePattern
    [result.pattern, parameters.pattern, wildcard .boolean, wildcard .boolean]
  let count ← liftError <| Runtime.standardCall runtime "params_length" [parameters.expression]
  return strongSequence function.pattern core
    (letEffect signature (cfunction function.expression)
      (ifEffect (operation .eq count (integer 0))
        (ifEffect (compatible (ailCtype returnType) result.expression)
          (ccallWith annotations (ailCtype designatorType) function.expression [])
          (pureEffect (standardUndefined location "§6.5.2.2#9" .UB041_function_not_compatible)))
        (pureEffect (standardUndefined location "§6.5.2.2#6, sentence 3" .UB038_number_of_args))))

end Silmaril.Cerberus.Elaboration.Calls
