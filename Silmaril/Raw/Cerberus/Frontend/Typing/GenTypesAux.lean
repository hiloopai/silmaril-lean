module

public import Silmaril.Cerberus.Frontend.Typing.Constants.Defs

@[expose] public section
namespace Silmaril.Cerberus.Frontend.Typing
open Silmaril.Cerberus Ail

/-- `genTypesAux.lem:35`. -/
def isInteger : GenType → Bool | .basic (.integer _) => true | _ => false
/-- `genTypesAux.lem:43`. -/
def isFloating : GenType → Bool | .basic (.floating _) => true | _ => false
/-- `genTypesAux.lem:51`. -/
def isPointer : GenType → Bool | .pointer .. => true | _ => false
/-- `genTypesAux.lem:108`, ISO C11 §6.2.5#18. -/
def isArithmetic (t : GenType) : Bool := isInteger t || isFloating t
/-- `genTypesAux.lem:113`, ISO C11 §6.2.5#21 (including Cerberus byte). -/
def isScalar (t : GenType) : Bool := isArithmetic t || isPointer t || match t with
  | .byte => true | _ => false
/-- `genTypesAux.lem:214`, ISO C11 §6.3.1.1; keep promotion symbolic. -/
def integerPromotion (t : GenIntegerType) : GenIntegerType := .promote t
/-- `genTypesAux.lem:220`. Only called on integer types. -/
def integerPromote : GenType → GenType
  | .basic (.integer i) => .basic (.integer (integerPromotion i))
  | t => t
/-- `genTypesAux.lem:253`, ISO C11 §6.3.1.8; keep usual conversions symbolic. -/
def usualArithmetic (a b : GenType) : GenType :=
  match a, b with
  | .basic (.integer i), .basic (.integer j) =>
      .basic (.integer (.usual (integerPromotion i) (integerPromotion j)))
  | .basic (.floating (.realFloating .longDouble)), _
  | _, .basic (.floating (.realFloating .longDouble)) => .basic (.floating (.realFloating .longDouble))
  | .basic (.floating (.realFloating .double)), _
  | _, .basic (.floating (.realFloating .double)) => .basic (.floating (.realFloating .double))
  | _, _ => .basic (.floating (.realFloating .float))

/-- `genTypesAux.lem:153`: pointer to complete object (§6.5.6#2). -/
def isPointerToCompleteObject (s : Sigma Unit) : GenType → Bool
  | .pointer _ t => !isFunction t && isComplete s t
  | _ => false
/-- `genTypesAux.lem:181`: compatible pointers ignoring outer referenced qualifiers. -/
def arePointersToQualifiedOrUnqualifiedCompatibleTypes (a b : GenType) : Bool :=
  match a, b with
  | .pointer _ x, .pointer _ y => areCompatible (fun _ => none) (noQualifiers, x) (noQualifiers, y)
  | _, _ => false

/-- `ailSyntaxAux.lem`: syntactic null pointer constants, §6.3.2.3#3. -/
def isNullPointerConstant : TypedExpression → Bool
  | .mk _ _ _ (.const (.integer (.iconstant 0 _ _))) => true
  | .mk _ _ _ (.cast _ (.mk _ (.pointer _ (.mk _ .void))) e) => isNullPointerConstant e
  | _ => false

/-- `genTypes.lem:274`: type category accessor as an rvalue type. -/
def rvalueType (e : TypedExpression) : GenType := match e.annotation with
  | .rvalue t => t | .lvalue _ t _ => injectType t

/-- Member lookup shared by the branches of `genTyping.lem:1161-1352`.
Flexible arrays retain the empty type-annotation list used by Lem. -/
def lookupMember (s : Sigma Unit) (l : Loc) (t : Ctype) (x : Identifier) : TypingM (Qualifiers × Ctype) := do
  let tag ← match projCtype_ (unatomic t) with
    | .struct tag | .union tag => pure tag
    | _ => unsupported l "member base type (§6.5.2.3#1-2)"
  if !isComplete s (unatomic t) then unsupported l "incomplete member base (§6.5.2.3#1-2)"
  match lookupTagDefinition s tag with
  | some (.struct ms flex) =>
      match ms.find? (fun p => p.1.key == x.key) with
      | some (_, (_, _, q, ty)) => pure (q, ty)
      | none => match flex with
        | some (.mk _ y q ty) =>
            if x.key == y.key then pure (q, .mk [] (.array ty none))
            else unsupported l "missing member (§6.5.2.3#1)"
        | none => unsupported l "missing member (§6.5.2.3#1)"
  | some (.union ms) =>
      match ms.find? (fun p => p.1.key == x.key) with
      | some (_, (_, _, q, ty)) => pure (q, ty)
      | none => unsupported l "missing member (§6.5.2.3#2)"
  | none => unsupported l "missing tag definition"

/-- `genTyping.lem:168`: assignment constraints (§6.5.16.1#1).
Unported diagnostic formatting rejects conservatively. -/
def wellTypedAssignment (s : Sigma Unit) (isInit : Bool) (l : Loc)
    (t : Ctype) (g : GenType) (e : TypedExpression) : TypingM Unit := do
  let u := unatomic t
  if isArithmetic (injectType u) then
    if isArithmetic g then add "§6.5.16.1#1, bullet 1"
    else if (match projCtype_ u with | .basic (.integer .bool) => true | _ => false) && isPointer g then
      add "§6.5.16.1#1, bullet 6"
    else unsupported l "assignment arithmetic (§6.5.16.1#1)"
  else if (match projCtype_ u, g with | .byte, .byte => true | _, _ => false) then pure ()
  else match projCtype_ u, g with
  | .struct x, .struct y | .union x, .union y =>
      add "§6.5.16.1#1, bullet 2"
      if x.key != y.key then unsupported l "assignment tag (§6.5.16.1#1)"
  | .pointer q x, .pointer r y =>
      if (r.const && !q.const) || (r.volatile && !q.volatile) || (r.restrict && !q.restrict) then
        unsupported l "assignment discards qualifiers (§6.5.16.1#1)"
      if areCompatible (fun _ => none) (noQualifiers, x) (noQualifiers, y) then
        add "§6.5.16.1#1, bullet 3"
      else if (match projCtype_ x with | .void => !isFunction y | _ => false) ||
          (match projCtype_ y with | .void => !isFunction x | _ => false) then
        add "§6.5.16.1#1, bullet 4"
      else unsupported l "assignment pointer compatibility (§6.5.16.1#1)"
  | .pointer .., _ =>
      if isNullPointerConstant e then add "§6.5.16.1#1, bullet 5"
      else unsupported l "assignment pointer (§6.5.16.1#1)"
  | .array x n, .array y m =>
      if !isInit || !areCompatible (fun _ => none) (noQualifiers, x) (noQualifiers, y) ||
          (n.isSome && m.isSome && n != m) then unsupported l "array assignment (§6.5.16.1#1)"
  | _, _ => unsupported l "assignment (§6.5.16.1#1)"
  let _ := s

/-- `genTyping.lem:1912`: assignment checks after annotation; add atomic wrapper. -/
def annotateAssignee (annotate : Expression Unit → TypingM TypedExpression)
    (s : Sigma Unit) (isInit : Bool) (l : Loc) (t : Ctype) (e : Expression Unit) : TypingM TypedExpression := do
  let e ← annotate e
  let g := rvalueType e
  wellTypedAssignment s isInit l t g e
  match projCtype_ t, g with
  | .atomic _, .atomic _ => pure e
  | .atomic _, _ => pure (.mk (.rvalue (.atomic g)) [] l (.atomic e))
  | _, _ => pure e

/-- `genTyping.lem:327`: arithmetic operand constraints, §6.5.5-6.5.12. -/
def wellTypedBinaryArithmetic (l : Loc) (a : GenType) (op : ArithmeticOperator) (b : GenType) : TypingM Unit := do
  let ok := match op with
    | .mul | .div | .add | .sub => isArithmetic a && isArithmetic b
    | _ => isInteger a && isInteger b
  if !ok then unsupported l "binary operands (§6.5.5-6.5.12)"

/-- `genTyping.lem:1803`: explicit lvalue, array and function conversions (§6.3.2.1#2-4). -/
inductive AnnotationContext where
  | sizeof | addr | incr | decr | memberof | assign | arrayInit | other
  deriving DecidableEq

/-- `genTyping.lem:1803`: preserve nodes and duplicate annotations on conversion wrappers. -/
def performDecays (s : Sigma Unit) (ctx : AnnotationContext) (e : TypedExpression) : TypingM TypedExpression := do
  let .mk cat ann l n := e
  let literal := match n with | .array true .. | .const (.array ..) | .str _ => true | _ => false
  match cat with
  | .lvalue _ t reg =>
      if !isArray t && !([AnnotationContext.sizeof, .addr, .incr, .decr, .memberof, .assign].contains ctx) then
        if !isComplete s t then unsupported (typeLoc t) "incomplete lvalue conversion (§6.3.2.1#2)"
        return .mk (.rvalue (injectType (.mk [] (projCtype_ (unatomic t))))) ann l (.rvalue e)
      else if isArray t && !([AnnotationContext.sizeof, .addr].contains ctx) && !(ctx == .arrayInit && literal) then
        if reg then unsupported .unknown "register array decay (§6.3.2.1#3)"
        return .mk (.rvalue (injectType (arrayCoercion t))) ann l (.arrayDecay e)
      else pure e
  | .rvalue g =>
      if [.sizeof, .addr].contains ctx then return e
      match g with
      | .function r ps v =>
          return .mk (.rvalue (.pointer noQualifiers (.mk [] (.function r ps v)))) ann l (.functionDecay e)
      | .array t _ =>
          match n with
          | .const (.indeterminate _) | .array false .. | .invalid .. => pure e
          | _ =>
              if ctx == .arrayInit && literal then pure e
              else pure (.mk (.rvalue (.pointer noQualifiers t)) ann l (.arrayDecay e))
      | _ => pure e

/-- `genTyping.lem:2080`: scalar and array initialisations; preserves effect order. -/
def annotateDefinitionAux (annotate : AnnotationContext → Expression Unit → TypingM TypedExpression)
    (s : Sigma Unit) (g : Bindings) (t : Ctype) (e : Expression Unit) : TypingM TypedExpression := do
  let _ := g
  let u := unatomic t
  if isScalar (injectType u) then
    add "§6.7.9#11, sentence 3"
    annotateAssignee (annotate .other) s true .unknown t e
  else if (match projCtype_ u with | .struct _ | .union _ => true | _ => false) then
    add "§6.7.9#13"
    annotateAssignee (annotate .other) s true .unknown t e
  else if isArray t then
    let e ← annotate .arrayInit e
    match projCtype_ t, e.annotation with
    | .array x n, .rvalue (.array y m) =>
        if !areCompatible (fun _ => none) (noQualifiers, x) (noQualifiers, y) || (n.isSome && n != m) then
          unsupported e.loc "array initialisation types (§6.7.9#16)"
        return e
    | .array x (some n), .lvalue _ (.mk _ (.array y (some m))) _ =>
        if !areCompatible (fun _ => none) (noQualifiers, x) (noQualifiers, y) || n < m then
          unsupported e.loc "string initialisation types (§6.7.9#14)"
        return e
    | _, _ => unsupported e.loc "array initialisation (§6.7.9#14-16)"
  else unsupported e.loc "initialisation (§6.7.9#3)"

end Silmaril.Cerberus.Frontend.Typing
