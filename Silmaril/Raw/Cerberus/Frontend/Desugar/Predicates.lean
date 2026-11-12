module

public import Silmaril.Cerberus.Frontend.Desugar.Rec.Defs

/-! # Predicates on Ail expressions

The syntactic checks of constant expressions that the desugaring makes on untyped Ail
(`cabs_to_ail.lem:583-978`, STD §6.6), with `AilSyntaxAux.is_null_pointer_constant`
(`ail/ailSyntaxAux.lem:18`). Lem's `error` on a form that only exists after typing is
`internalError`.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- `Located cabs_expression`'s `locOf` (`cabs.lem`): the region of the expression. -/
def locOfExpression : Cabs.Expression → Loc
  | .mk loc _ => loc

/-- `AilSyntaxAux.is_null_pointer_constant` (`ail/ailSyntaxAux.lem:18-33`), STD §6.3.2.3#3,
sentence 1, under `strip_expression` (`ail/ailSyntaxAux.lem:7`), which drops annotations and
`__cerb_printtype`. -/
def isNullPointerConstant {α : Type} : Expression α → Bool
  | .mk _ _ _ (.annot _ e) | .mk _ _ _ (.printType e) => isNullPointerConstant e
  | .mk _ _ _ (.const .null) => true
  | .mk _ _ _ (.const (.integer (.iconstant n _ _))) => n == 0
  | .mk _ _ _ (.cast castQs (.mk _ (.pointer referencedQs (.mk _ .void))) e) =>
    isNullPointerConstant e && isUnqualified castQs && isUnqualified referencedQs
  | .mk _ _ _ (.atomic e) => isNullPointerConstant e
  | _ => false

/-- `is_integer_constant_expression` (`cabs_to_ail.lem:583-762`), STD §6.6#6: casts are not
supported, and conditionals are checked in both branches. -/
def isIntegerConstantExpression : Expression Unit → DesugM Bool
  | .mk _ _ loc expr_ =>
    match expr_ with
    | .unary .plus e | .unary .minus e | .unary .bnot e => isIntegerConstantExpression e
    | .unary _ _ => return false
    | .cast .. => fail loc (.notYetSupported "cast operator in `integer constant expressions'")
    | .assert _ => return false
    -- STD §7.19#3
    | .offsetof .. => return true
    | .str _ => return false
    | .annot _ e => isIntegerConstantExpression e
    | .vaStart .. | .vaCopy .. | .vaArg .. | .vaEnd _ => return false
    | .printType e => isIntegerConstantExpression e
    | .bmcAssume _ => return false
    | .rvalue _ => internalError "cabs_to_ail.is_integer_constant_expression (AilErvalue _)"
    | .arrayDecay _ => internalError "cabs_to_ail.is_integer_constant_expression (AilEarray_decay _)"
    | .functionDecay _ => internalError "cabs_to_ail.is_integer_constant_expression (AilEfunction_decay _)"
    | .atomic _ => internalError "cabs_to_ail.is_integer_constant_expression (AilEatomic _)"
    -- this includes enumeration constants
    | .const (.integer _) => return true
    | .const (.floating _) => return false
    | .const (.character _) => return true
    | .const (.predefined _) => return true
    -- STD §6.5.3.4#2, sentence 4
    | .sizeof _ ty => return !isVla ty
    | .sizeofExpr _ => return true
    | .alignof .. => return true
    -- STD §6.6#3
    | .assign .. | .compoundAssign .. | .call .. | .binary _ .comma _ => return false
    | .binary e₁ _ e₂ => do
      if ← isIntegerConstantExpression e₁ then isIntegerConstantExpression e₂ else return false
    | .cond e₁ none e₃ => do
      if ← isIntegerConstantExpression e₁ then isIntegerConstantExpression e₃ else return false
    | .cond e₁ (some e₂) e₃ => do
      if ← isIntegerConstantExpression e₁ then
        let b₂ ← isIntegerConstantExpression e₂
        let b₃ ← isIntegerConstantExpression e₃
        return b₂ && b₃
      else return false
    | .memberof .. | .memberofptr .. => return false
    | .ident _ => return false
    | .gccStatement .. =>
      fail loc (.notYetSupported "GNU statement as expression in constant expression")
    | _ => internalError "TODO: Cabs_to_ail.is_integer_constant_expression, wildcard"

/-- `is_arithmetic_constant_expression` (`cabs_to_ail.lem:785-831`), STD §6.6#8. -/
def isArithmeticConstantExpression (isLvalue : Bool) : Expression Unit → DesugM Bool
  | .mk _ _ _ expr =>
    match expr with
    | .const (.integer _) | .const (.floating _) | .const (.character _) | .const (.predefined _) =>
      return true
    | .ident _ => return isLvalue
    | .annot _ e => isArithmeticConstantExpression true e
    | .unary .address e => isArithmeticConstantExpression true e
    | .unary _ e => isArithmeticConstantExpression isLvalue e
    | .binary e₁ _ e₂ => do
      let b₁ ← isArithmeticConstantExpression isLvalue e₁
      let b₂ ← isArithmeticConstantExpression isLvalue e₂
      return b₁ && b₂
    | .sizeof _ ty => return !isVla ty
    | .alignof .. => return true
    | .cast _ ty e =>
      if !isArithmetic ty then return false else isArithmeticConstantExpression isLvalue e
    -- STD §7.19#3
    | .offsetof .. => return true
    | _ => return false

/-- `is_lvalue_to_static_object` (`cabs_to_ail.lem:833-871`). An addition is an array
subscript. -/
def isLvalueToStaticObject : Expression Unit → DesugM Bool
  | .mk _ _ _ expr =>
    match expr with
    | .ident sym => isStaticObjectIdentifier sym
    | .binary e₁ (.arithmetic .add) e₂ => do
      let b₁₁ ← isLvalueToStaticObject e₁
      let b₁₂ ← isArithmeticConstantExpression false e₁
      let b₂₁ ← isLvalueToStaticObject e₂
      let b₂₂ ← isArithmeticConstantExpression false e₂
      return b₁₁ && b₂₂ || b₁₂ && b₂₁
    | .memberof e _ | .memberofptr e _ => isLvalueToStaticObject e
    | .cast _ ty e => if !isPointer ty then return false else isLvalueToStaticObject e
    -- a string literal is an array of static storage duration
    | .str _ => return true
    | _ => return false

/-- `is_address_constant` (`cabs_to_ail.lem:874-907`), STD §6.6#9. -/
def isAddressConstant (aExpr : Expression Unit) : DesugM Bool :=
  if isNullPointerConstant aExpr then return true
  else match aExpr with
    | .mk _ _ _ (.ident sym) => do
      if ← isFunctionDesignator sym then return true
      else
        let (_, _, dur, _, _, _, ty) ← fetchObjectDeclaration sym
        match dur with
        | .static => return isArray ty
        | _ => return false
    | .mk _ _ _ (.unary .address expr) => isLvalueToStaticObject expr
    | .mk _ _ _ (.cast _ _ expr) => do
      if ← isLvalueToStaticObject expr then return true else isIntegerConstantExpression expr
    | _ => return false

/-- `is_initializer_constant_expression_or_string_literal` (`cabs_to_ail.lem:913-943`): the
constant expressions of an initializer, STD §6.6#7. -/
def isInitializerConstantExpressionOrStringLiteral (aExpr : Expression Unit) : DesugM Bool := do
  let b₁ ← isArithmeticConstantExpression false aExpr
  let b₂ ← isAddressConstant aExpr
  -- STD §6.6#7, bullets 1 - 3
  if b₁ || isNullPointerConstant aExpr || b₂ then return true
  -- STD §6.6#7, bullet 4
  else match aExpr with
    | .mk _ _ _ (.binary e₁ (.arithmetic .add) e₂) | .mk _ _ _ (.binary e₁ (.arithmetic .sub) e₂) => do
      let b₁₁ ← isAddressConstant e₁
      let b₁₂ ← isIntegerConstantExpression e₂
      let b₂₁ ← isAddressConstant e₂
      let b₂₂ ← isIntegerConstantExpression e₁
      return b₁₁ && b₁₂ || b₂₁ && b₂₂
    | .mk _ _ _ (.str _) => return true
    | _ => return false

/-- `check_initialised_type_constraint` (`cabs_to_ail.lem:97-109`), STD §6.7.9#3. -/
def checkInitialisedTypeConstraint (loc : Loc) (ty : Ctype) : DesugM Unit := do
  let isCompleteObject ← isCompleteObjectM ty
  if !(isArrayUnknownSize ty || (isCompleteObject && !isVla ty)) then
    if isVla ty then constraintViolation loc .illegalInitialisationVla
    else notPorted loc "the message of IllegalInitialisation InitialisedIncomplete (prints a ctype)"

end Silmaril.Cerberus.Frontend.Desugar
