module

public import Silmaril.Cerberus.Frontend.Desugar.Expressions.Defs
public import Silmaril.Cerberus.Frontend.Desugar.ConstEval.Defs
public import Silmaril.Cerberus.Frontend.Desugar.Init.Defs

/-! # Initializers

`wip_desugar_initializer_` (`cabs_to_ail.lem:3346-3506`) at `b3e11ea3`: a scalar takes a
single expression, optionally braced, which must be a constant for a static or thread-local
object (STD §6.7.9#4, #11); an array of characters may take a string literal, one character
constant per element (STD §6.7.9#14); a structure may take an expression of its type. The
other aggregate and union initializers are interpreted by `Desugaring_init` (`Desugar.Init`).
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- The string literal of an initializer that is one, braced or not (`is_string_literal_init`,
`cabs_to_ail.lem:3348-3355`). -/
def stringLiteralOfInit : Cabs.Initializer → Option Cabs.StringLiteral
  | .expr (.mk _ (.string lit)) => some lit
  | .list _ [(none, .expr (.mk _ (.string lit)))] => some lit
  | _ => none

/-- The string-literal case of `wip_desugar_initializer_` (`cabs_to_ail.lem:3391-3451`): the
characters, cut to the size of the array or padded with zeros (STD §6.7.9#14), each
converted to the element type; an array of unknown size gets one more element than there
are characters. -/
def desugarStringLiteralInitialiser (loc : Loc) (currentTy : Ctype) (lit : Cabs.StringLiteral) :
    DesugM (Ctype × Expression Unit) := do
  let (_, charStrs) := translateCabsStringLiteral lit
  let charStrs := (charStrs.map (·.2)).flatten
  let (annots, elemTy, currentSizeOpt) ← match currentTy with
    | .mk annots (.array elemTy sz) => pure (annots, elemTy, sz)
    | _ => internalError "TODO(msg): assert false, array_of_character init, no size opt"
  let doWrap (xs : List Cabs.RawString) : List (Option (Expression Unit)) :=
    xs.map fun z => some (mkExpression loc (.const (.character (none, z))))
  let charsN := charStrs.length
  let (newTy, charsArray) := match currentSizeOpt with
    | some currentN' =>
      let currentN := currentN'.toNat
      (currentTy,
        if currentN == charsN + 1 then doWrap charStrs ++ [some zeroAil]
        else if currentN < charsN + 1 then doWrap (charStrs.take currentN)
        else doWrap charStrs ++ List.replicate (currentN - charsN) (some zeroAil))
    | none => (Ctype.mk annots (.array elemTy (some (charsN + 1))), doWrap charStrs ++ [some zeroAil])
  let convedCharsArray := charsArray.map fun
    | none => none
    | some z => some (mkExpression loc (.cast noQualifiers elemTy z))
  return (newTy, mkExpression loc (.array true elemTy convedCharsArray))

/-- `wip_desugar_initializer_` (`cabs_to_ail.lem:3346-3506`): the type of the entity after
initialisation (an array of unknown size gets one) and the initializer's value. -/
def wipDesugarInitialiser (r : Rec) (loc : Loc) (dur : StorageDuration) (currentTy : Ctype)
    (init : Cabs.Initializer) : DesugM (Ctype × Expression Unit) := do
  if isScalar currentTy then
    let e ← match init with
      | .expr e => pure e
      -- a scalar can be initialised with optional enclosing braces
      | .list _ [(none, .expr e)] => pure e
      -- STD §6.7.9#11, sentence 1 ("shall" outside a constraint: undefined behaviour)
      | _ => throw (scalarInitialiserNotSingleExpression loc)
    let dE ← r.expression e
    -- STD §6.7.9#4
    if dur == .static || dur == .thread then
      if ← isInitializerConstantExpressionOrStringLiteral dE then return (currentTy, dE)
      else constraintViolation dE.loc .illegalStorageClassStaticOrThreadInitializer
    else return (currentTy, dE)
  else if isArrayOfCharacter currentTy && (stringLiteralOfInit init).isSome then
    match stringLiteralOfInit init with
    | some lit => desugarStringLiteralInitialiser loc currentTy lit
    | none => internalError s!"wip_desugar_{initialiserWord}_: string literal"
  else
    match unatomic_ currentTy, init with
    | .struct _, .expr e => do
      let dE ← r.expression e
      return (currentTy, dE)
    | _, _ =>
      let funcs : DesugaringInitFuncs :=
        { desugarExpression := r.expression
          isIntegerConstantExpression := isIntegerConstantExpression
          isInitializerConstantExpressionOrStringLiteral := isInitializerConstantExpressionOrStringLiteral
          evaluateIntegerConstantExpression := evaluateIntegerConstantExpression }
      desugarAggregateInitialiser funcs loc dur currentTy init

end Silmaril.Cerberus.Frontend.Desugar
