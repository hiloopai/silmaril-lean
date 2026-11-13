module

public import Silmaril.Cerberus.Frontend.Desugar.Builtins.Defs
public import Silmaril.Cerberus.Frontend.Desugar.Constants.Defs
public import Silmaril.Cerberus.Frontend.Desugar.Predicates.Defs

/-! # Expressions

`desugar_expression` (`cabs_to_ail.lem:2248-2538`) at `b3e11ea3`: every Cabs expression
becomes an Ail expression at the same location; `e1[e2]` is `*(e1 + e2)`, `!e` is `0 == e`,
`++e` and `--e` are compound assignments (STD §6.5.2.1#2, §6.5.3.1#2-3, §6.5.3.3#5).
Subexpressions are desugared left to right, as Lem's applicative `<*>` does.

Not ported yet: `sizeof e` (which types its operand), `_Generic`, GNU statement expressions
and `__builtin_choose_expr` (which evaluates a constant).
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- `AnnotatedExpression () [] loc`. -/
def mkExpression (loc : Loc) (node : ExpressionNode Unit) : Expression Unit := .mk () [] loc node

/-- The `CabsEident` case of `desugar_expression` (`cabs_to_ail.lem:2250-2290`), STD §6.5.1#2:
an enumeration constant is its value; a typedef name, an identifier out of sight or a tag
is undeclared; a name without declaration may be a builtin `__cerbvar_*` variable. -/
def desugarIdentifier (ident : Identifier) : DesugM (ExpressionNode Unit) := do
  let undeclared {α : Type} : DesugM α :=
    fail ident.loc (.miscViolation (.undeclaredIdentifier ident.name))
  match ← resolveOrdinaryIdentifier ident.loc ident with
  | some (_, .enumConstant sym) => resolveEnumConstant sym
  | some (_, .typedef _) => undeclared
  | some (scope, .other sym kind _) =>
    let isVisible ← scopeIsVisible scope
    if !isVisible || !(isObjectKind kind || kind == .function) then undeclared
    else
      addUsedIdentifier sym
      match kind with
      | .object _ =>
        let _ ← fetchObjectDeclaration sym
        return .ident sym
      | _ => return .ident sym
  | none =>
    match translateBuiltinVarnames ident with
    | some dE => return dE
    | none => undeclared

/-- `desugar_expression` (`cabs_to_ail.lem:2248-2538`). -/
def desugarExpression (r : Rec) : Cabs.Expression → DesugM (Expression Unit)
  | .mk loc expr =>
    let ret (node : ExpressionNode Unit) : DesugM (Expression Unit) := return mkExpression loc node
    match expr with
    | .ident ident => do ret (← desugarIdentifier ident)
    | .const cst => ret (.const (desugarCabsConstant cst))
    | .string lit => ret (.str (translateCabsStringLiteral lit))
    | .generic .. => notPorted loc "generic selections (_Generic)"
    -- STD §6.5.2.1#2, sentence 2
    | .subscript e₁ e₂ => do
      let dE₁ ← r.expression e₁
      let dE₂ ← r.expression e₂
      ret (.unary .indirection (mkExpression loc (.binary dE₁ (.arithmetic .add) dE₂)))
    | .call e es none => do
      let dE ← r.expression e
      let dEs ← es.mapM r.expression
      ret (.call dE dEs)
    | .call e es (some attrs) => do
      let id ← recordMarker
      let dE ← r.expression e
      let dEs ← es.mapM r.expression
      return .mk () [.marker id, .attrs attrs] loc (.call dE dEs)
    -- the member is resolved by the typing, which knows the type of `e`
    | .memberof e ident => do ret (.memberof (← r.expression e) ident)
    | .memberofptr e ident => do ret (.memberofptr (← r.expression e) ident)
    | .postincr e => do ret (.unary .postfixIncr (← r.expression e))
    | .postdecr e => do ret (.unary .postfixDecr (← r.expression e))
    | .compound tyname inits => do
      let (qs, ty) ← r.typeName tyname
      let insideFunc ← isInsideFunction
      -- STD §6.7.9#3 is checked by the Ail typing
      let (ty', dE) ← r.wipInitializer loc (if insideFunc then .automatic else .static) ty (.list loc inits)
      ret (.compound qs ty' dE)
    -- STD §6.5.3.1#2, sentence 3
    | .preincr e => do ret (.compoundAssign (← r.expression e) .add oneAil)
    -- STD §6.5.3.1#3
    | .predecr e => do ret (.compoundAssign (← r.expression e) .sub oneAil)
    -- STD §6.5.3.3#5
    | .unary .not e => do ret (.binary zeroAil .eq (← r.expression e))
    | .unary uop e => do
      let dE ← r.expression e
      ret (.unary (← translateUnaryOperator uop) dE)
    | .sizeofExpr _ => notPorted loc "sizeof of an expression (types its operand)"
    | .sizeofType tyname => do
      let (qs, ty) ← r.typeName tyname
      ret (.sizeof qs ty)
    | .alignof tyname => do
      let (qs, ty) ← r.typeName tyname
      ret (.alignof qs ty)
    | .cast tyname e => do
      let (qs, ty) ← r.typeName tyname
      let dE ← r.expression e
      ret (.cast qs ty dE)
    | .binary bop e₁ e₂ => do
      let dE₁ ← r.expression e₁
      let dE₂ ← r.expression e₂
      ret (.binary dE₁ (translateBinaryOperator bop) dE₂)
    | .cond e₁ e₂ e₃ => do
      let dE₁ ← r.expression e₁
      let dE₂ ← r.expression e₂
      let dE₃ ← r.expression e₃
      ret (.cond dE₁ (some dE₂) dE₃)
    | .assign aop e₁ e₂ => do
      let dE₁ ← r.expression e₁
      let dE₂ ← r.expression e₂
      match translateAssignmentOperator aop with
      | none => ret (.assign dE₁ dE₂)
      | some aop => ret (.compoundAssign dE₁ aop dE₂)
    | .comma e₁ e₂ => do
      let dE₁ ← r.expression e₁
      let dE₂ ← r.expression e₂
      ret (.binary dE₁ .comma dE₂)
    | .assert e => do ret (.assert (← r.expression e))
    | .offsetof tyname ident => do
      let (_, ty) ← r.typeName tyname
      ret (.offsetof ty ident)
    | .vaStart e ident => do
      let dE ← r.expression e
      match ← r.expression (.mk ident.loc (.ident ident)) with
      | .mk _ _ _ (.ident sym) => ret (.vaStart dE sym)
      | _ => internalError "the second operand of va_start() was not paramN"
    | .vaCopy e₁ e₂ => do
      let dE₁ ← r.expression e₁
      let dE₂ ← r.expression e₂
      ret (.vaCopy dE₁ dE₂)
    | .vaArg e tyname => do
      let dE ← r.expression e
      let (_, ty) ← r.typeName tyname
      ret (.vaArg dE ty)
    | .vaEnd e => do ret (.vaEnd (← r.expression e))
    | .printType e => do ret (.printType (← r.expression e))
    | .bmcAssume e => do ret (.bmcAssume (← r.expression e))
    | .labelAddressGnu ident => do
      guardExtension loc "GNU address-of-label"
      ret (.labelAddressGnu (← resolveLabel ident))
    | .gccStatement _ => notPorted loc "GNU statement expressions"
    | .condGnu e₁ e₃ => do
      let dE₁ ← r.expression e₁
      let dE₃ ← r.expression e₃
      ret (.cond dE₁ none dE₃)
    | .builtinGnu (.typesCompatibleP tyname₁ tyname₂) => do
      let (_, ty₁) ← r.typeName tyname₁
      let (_, ty₂) ← r.typeName tyname₂
      if areCompatible (← getTypeofEnum) (noQualifiers, ty₁) (noQualifiers, ty₂) then
        ret (.const (.integer (.iconstant 1 .decimal none)))
      else ret (.const (.integer (.iconstant 0 .octal none)))
    | .builtinGnu (.chooseExpr ..) => notPorted loc "__builtin_choose_expr (evaluates a constant)"

end Silmaril.Cerberus.Frontend.Desugar
