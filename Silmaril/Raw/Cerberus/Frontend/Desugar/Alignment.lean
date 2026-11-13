module

public import Silmaril.Cerberus.Frontend.Desugar.ConstEval.Defs

/-! # Alignment specifiers

`cabs_to_ail.lem:2767-2891` at `b3e11ea3`. Type-based alignment uses the existing
LP64 layout port; expression-based alignment uses the integer constant evaluator of
`ConstEval.lean`.
-/

@[expose] public section
namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus

/-- `AilTypesAux.is_character` (`ailTypesAux.lem:95-104`), STD §6.2.5#15. -/
def isCharacter : Ctype → Bool
  | .mk _ (.basic (.integer .char))
  | .mk _ (.basic (.integer (.signed .ichar)))
  | .mk _ (.basic (.integer (.unsigned .ichar))) => true
  | _ => false

/-- `AilTypesAux.is_corresponding_unsigned` (`ailTypesAux.lem:562-569`). -/
def isCorrespondingUnsigned : IntegerType → IntegerType → Bool
  | .signed a, .unsigned b => a == b
  | _, _ => false

/-- `AilTypesAux.agnostic_alignment_requirement_ord` (`ailTypesAux.lem:1287-1323`):
compare requirements where the standard fixes their order, before consulting LP64 layout.
The recursion follows array element types. -/
def agnosticAlignmentRequirementOrd (typeofEnum : Sym → Option IntegerType)
    (ty₁ ty₂ : Ctype) : Option Ordering :=
  if ctypeEqual ty₁ ty₂ then some .eq
  else if isCharacter ty₁ then some (if isCharacter ty₂ then .eq else .lt)
  else if isCharacter ty₂ then some (if isCharacter ty₁ then .eq else .gt)
  else match ty₁, ty₂ with
    | .mk _ (.basic (.integer a)), .mk _ (.basic (.integer b)) =>
      if isCorrespondingUnsigned a b || isCorrespondingUnsigned b a then some .eq else none
    | .mk _ (.pointer _ a), .mk _ (.pointer _ b) =>
      if (isVoid a && isCharacter b) || (isCharacter a && isVoid b) ||
          areCompatibleCtype typeofEnum a b then some .eq
      else match a, b with
        | .mk _ (.struct _), .mk _ (.struct _)
        | .mk _ (.union _), .mk _ (.union _) => some .eq
        | _, _ => none
    | .mk _ (.array a _), b => agnosticAlignmentRequirementOrd typeofEnum a b
    | a, .mk _ (.array b _) => agnosticAlignmentRequirementOrd typeofEnum a b
    | _, _ => none
termination_by sizeOf ty₁ + sizeOf ty₂
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- `is_power_of_two`. -/
def isPowerOfTwo (n : Int) : Bool := n > 0 && (n.toNat &&& (n.toNat - 1)) == 0

/-- `desugar_alignment_specifier` (`cabs_to_ail.lem:2767-2791`): `_Alignas(type)`, or
`_Alignas(e)` with `e` an integer constant expression, 0 meaning no alignment
(STD §6.7.5#6), otherwise a power of two. -/
def desugarAlignmentSpecifier (r : Rec) (_loc : Loc) : Cabs.AlignmentSpecifier →
    DesugM (Option Alignment)
  | .type_ tyname => do
    let (_, ty) ← r.typeName tyname
    return some (.ctype ty)
  | .expr e => do
    let loc := locOfExpression e
    let dE ← r.expression e
    -- STD §6.7.2.2#2
    if !(← isIntegerConstantExpression dE) then constraintViolation loc .alignasNotIntegerConstant
    else
      let n ← evaluateIntegerConstantExpression loc none dE
      -- STD §6.7.5#6, second sentence
      if n == 0 then return none
      else if n < 0 || !isPowerOfTwo n then constraintViolation loc .alignasInvalidIntegerConstant
      else return some (.integer n)

/-- `desugar_alignment_specifiers` (`cabs_to_ail.lem:2794-2891`), STD §6.7.5#4 and #6:
fold left, retaining the first of equally strict specifiers, then compare with the
required declaration alignment. Equal type requirements remove the redundant specifier. -/
def desugarAlignmentSpecifiers (r : Rec) (loc : Loc) (declTy : Ctype)
    (xs : List Cabs.AlignmentSpecifier) : DesugM (Option Alignment) := do
  let alignofTy ← getAlignof
  let typeofEnum ← getTypeofEnum
  let align (ty : Ctype) : DesugM Int := do
    match ← alignofTy ty with
    | some n => pure n
    | none => notPorted loc "alignment of this type"
  let value : Alignment → DesugM Int
    | .ctype ty => align ty
    | .integer n => pure n
  let accOpt ← xs.foldlM (init := (none : Option Alignment)) fun accOpt aspec => do
    match ← desugarAlignmentSpecifier r loc aspec with
    | none => return accOpt
    | some al =>
      match accOpt with
      | none => return some al
      | some prev =>
        let common : DesugM (Option Alignment) := do
          if (← value prev) >= (← value al) then return accOpt else return some al
        match prev, al with
        | .ctype prevTy, .ctype newTy =>
          match agnosticAlignmentRequirementOrd typeofEnum prevTy newTy with
          | some .eq | some .gt => return accOpt
          | some .lt => return some al
          | none => common
        | _, _ => common
  match accOpt with
  | none => return none
  | some (.integer n) =>
    if isCharacter declTy then return accOpt
    else if (← align declTy) > n then constraintViolation loc (.alignasLessThanRequired declTy)
    else return accOpt
  | some (.ctype ty) =>
    match agnosticAlignmentRequirementOrd typeofEnum declTy ty with
    | some .eq => return none
    | some .gt => constraintViolation loc (.alignasLessThanRequired declTy)
    | some .lt => return accOpt
    | none =>
      if (← align declTy) > (← align ty) then constraintViolation loc (.alignasLessThanRequired declTy)
      else return accOpt

end Silmaril.Cerberus.Frontend.Desugar
