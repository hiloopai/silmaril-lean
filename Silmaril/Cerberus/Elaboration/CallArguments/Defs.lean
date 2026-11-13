module

public import Silmaril.Cerberus.Elaboration.Calls.Defs
public import Silmaril.Cerberus.Target.Defs
public import Silmaril.Cerberus.Elaboration.MemoryActions.Defs
public import Silmaril.Cerberus.Elaboration.Lifetimes.Defs

/-! Selected normal-convention, fixed nonvariadic integer-argument calls from
Cerberus `b3e11ea334e95359907d4abf9194f0e7fedc6c6a`,
`translation.lem:835–1155`. The function and argument children are actual
recursive translations. The extracted OCaml `mapi` allocates argument object names tail first, before
any argument child. Monadic child translation then visits source order; generated
Core evaluates the designator and arguments with `unseq`, then creates real
parameter objects, calls, kills those objects and returns the bound result.
CHERI, inner-argument convention, variadic, pointer, floating and atomic
parameter branches remain outside this selected successful domain. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.CallArguments
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

structure Argument where
  location : Loc
  type : Ctype
  elaboration : State.ElabM Effect

def directInteger : Ctype → Bool
  | .mk _ (.basic (.integer _)) => true
  | _ => false

/-- Unlike argument object symbols, these wrappers use the ordinary description.
The loaded wrapper is allocated before the actual recursive child. -/
def elaborateArgument (argument : Argument) : State.ElabM (State.WrappedSymbol × Effect) := do
  let loaded ← State.wrappedFreshSymbol (.loaded .integer)
  let core ← argument.elaboration
  return (loaded, core)

/-- The static expected CType determines allocation, conversion and memory
order. The dynamic parameter CType is inspected only for compatibility. -/
def createParameter (runtime : List Runtime.Binding) (location : Loc)
    (parameters : Pure) (index : Nat) (expected : Ctype)
    (loaded : Pure) : State.ElabM Effect := do
  let parameterType ← State.wrappedFreshSymbol .ctype
  let pointer ← State.wrappedFreshSymbol (.object .pointer)
  let actualType ← Calls.liftError <|
    Runtime.standardCall runtime "params_nth" [parameters, integer index]
  let converted ← Calls.liftError <|
    Runtime.standardCall runtime "conv_loaded_int" [ailCtype expected, loaded]
  let digest := (← get).freshness.digest
  return letEffect parameterType.pattern actualType
    (ifEffect (notPure (compatible (ailCtype expected) parameterType.expression))
      (pureEffect (standardUndefined location "§6.5.2.2#9" .UB041_function_not_compatible))
      (addStandard "§6.5.2.2#7, sentence 1"
        (weakSequence pointer.pattern
          (MemoryActions.create location (alignof (ailCtype expected)) (ailCtype expected)
            (.funArg location digest index))
          (weakSequence (wildcard .unit)
            (MemoryActions.store location false (ailCtype expected) pointer.expression converted .na)
            (pureEffect pointer.expression)))))

/-- Source cleanup uses a scalar unit pattern for zero/one object and a tuple
of units otherwise. `unseq` here is the source smart constructor. -/
def cleanup (location : Loc) (parameters : List Ctype) (pointers : List Sym)
    (continuation : Effect) : Effect :=
  let resultType := if pointers.length < 2 then .unit
    else .tuple (List.replicate pointers.length .unit)
  strongSequence (wildcard resultType)
    (unseq ((pointers.zip parameters).map fun (pointer, type) =>
      MemoryActions.staticKill location type (symbolPure pointer))) continuation

def translate (config : Target.Config) (runtime : List Runtime.Binding) (location : Loc)
    (annotations : List Annot) (designatorType : Ctype)
    (designator : State.ElabM Effect) (arguments : List Argument) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI argument-bearing call")
  let (returnType, parameterTypes) ← match designatorType with
    | .mk _ (.pointer _ (.mk _ (.function (_, result) parameters false))) =>
        pure (result, parameters.map fun parameter => parameter.2.1)
    | _ => throw (.message "unsupported: nonempty call requires a fixed nonvariadic prototype")
  if arguments.isEmpty || arguments.length != parameterTypes.length then
    throw (.message "unsupported: nonempty call requires exactly its fixed arguments")
  if !directInteger returnType || !parameterTypes.all directInteger ||
      !arguments.all (fun argument => directInteger argument.type) then
    throw (.message "unsupported: nonempty call requires direct integer arguments, parameters and return")
  let .normal ← State.getCallingConvention
    | throw (.message "unsupported: nonempty call requires the normal calling convention")
  let function ← State.wrappedFreshSymbol (.loaded .pointer)
  let called ← State.wrappedFreshSymbol (.loaded .pointer)
  let result ← State.wrappedFreshSymbol .ctype
  let parameters ← State.wrappedFreshSymbol (.list .ctype)
  let variadic ← State.wrappedFreshSymbol .boolean
  let prototype ← State.wrappedFreshSymbol .boolean
  let functionCore ← designator
  -- Lem list.lem:1024–1028 extracts a recursive cons whose OCaml tail is
  -- evaluated first. Restore source order after those reversed fresh effects.
  let reversePointers ← arguments.zipIdx.reverse.mapM fun (argument, index) =>
    State.freshDescription (.funArg argument.location index)
  let pointers := reversePointers.reverse
  let elaborated ← arguments.mapM elaborateArgument
  let creates ← (parameterTypes.zip elaborated).zipIdx.mapM fun ((type, (loaded, _)), index) =>
    createParameter runtime location parameters.expression index type loaded.expression
  let returned ← State.wrappedFreshSymbol (.loaded .integer)
  let signature ← Calls.liftError <| tuplePattern
    [result.pattern, parameters.pattern, variadic.pattern, prototype.pattern]
  let functionPattern ← Calls.liftError <| tuplePattern [called.pattern, signature]
  let evaluationPattern ← Calls.liftError <|
    tuplePattern (functionPattern :: elaborated.map (fun argument => argument.1.pattern))
  let functionValue ← Calls.liftError <| tuplePure
    [function.expression, cfunction function.expression]
  let count ← Calls.liftError <| Runtime.standardCall runtime "params_length" [parameters.expression]
  let call := strongSequence returned.pattern
    (ccallWith annotations (ailCtype designatorType) called.expression (pointers.map symbolPure))
    (cleanup location parameterTypes pointers (pureEffect returned.expression))
  let prepared := Lifetimes.sequenceBindings
    ((pointers.map fun pointer => symbolPattern pointer (.object .pointer)).zip creates) call
  return addStandard "§6.5.2.2#10, sentence 1"
    (strongSequence evaluationPattern
      (addStandard "§6.5.2.2#4, sentence 2"
        (unseqEffect (strongSequence function.pattern functionCore (pureEffect functionValue) ::
          elaborated.map Prod.snd)))
      (ifEffect (notPure (operation .eq count (integer arguments.length)))
        (pureEffect (standardUndefined location "§6.5.2.2#6, sentence 3" .UB038_number_of_args))
        (ifEffect (operation .or variadic.expression
            (notPure (compatible (ailCtype returnType) result.expression)))
          (pureEffect (standardUndefined location "§6.5.2.2#9" .UB041_function_not_compatible))
          prepared)))

end Silmaril.Cerberus.Elaboration.CallArguments
