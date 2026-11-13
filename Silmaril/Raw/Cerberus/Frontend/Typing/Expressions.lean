module

public import Silmaril.Cerberus.Frontend.Typing.GenTypesAux.Defs

@[expose] public section
namespace Silmaril.Cerberus.Frontend.Typing
open Silmaril.Cerberus Ail

/-- The block callback of `genTyping.lem:600` (closed over the function return type). -/
abbrev AnnotateBlock := Loc → Sigma Unit → Bindings → Bindings → List (Statement Unit) → TypingM (List TypedStatement)

/-- `genTyping.lem:154`: type of a GNU statement expression's final statement. -/
def typeofStatementAsExpression : TypedStatement → GenTypeCategory
  | .mk _ _ _ (.expr e) => e.annotation
  | .mk _ _ _ (.label _ s _) | .mk _ _ _ (.marker _ s) => typeofStatementAsExpression s
  | _ => .rvalue .void

/-- `genTyping.lem:1921`: prototype arguments, left to right, without implicit casts
(except for the atomic builtins, whose branch is still unported). -/
def annotateArgumentsAux (annotate : Expression Unit → TypingM TypedExpression)
    (s : Sigma Unit) (nArgs nParams : Nat) (l : Loc) (variadic : Bool)
    (args : List (Expression Unit)) (ps : List (Qualifiers × Ctype × Bool)) : TypingM (List TypedExpression) := do
  match args, ps with
  | [], [] | [], [(_, .mk _ .void, _)] => return []
  | e :: es, (_, t, _) :: ts =>
      let e ← annotateAssignee annotate s false .unknown (rvalueCoercion t) e
      let es ← annotateArgumentsAux annotate s nArgs nParams l variadic es ts
      return e :: es
  | _, [] =>
      if variadic then args.mapM annotate
      else constraintViolation l s!"too many arguments to function call, expected {nParams}, have {nArgs}"
  | _, _ => constraintViolation l s!"too few arguments to function call, expected {nParams}, have {nArgs}"
termination_by args.length + ps.length

/-- `genTyping.lem:600-1743`: expression annotation with Cerberus effect order.
Unported cases return an explicit reject, never an assumed annotation. -/
partial def annotateExpression (annotateBlock : AnnotateBlock) (s : Sigma Unit) (g : Bindings)
    (ctx : AnnotationContext) (e : Expression Unit) : TypingM TypedExpression := do
  let .mk _ stdAnnots l n := e
  let annotate := annotateExpression annotateBlock s g
  let rv := annotate .other
  let (n, cat) ← (show TypingM (ExpressionNode GenTypeCategory × GenTypeCategory) from do
    match n with
    | .const c =>
        add "§6.5.1#3"
        let t ← typecheckConstant l c
        return (.const c, .rvalue t)
    | .str lit => add "§6.5.1#4"; return annotateStringLiteral lit
    | .ident x =>
        match (g.find? fun p => symbolEqual p.1 x), (s.declarations.find? fun p => symbolEqual p.1 x) with
        | some (_, ((_, _, reg), _, q, t)), none => return (.ident x, .lvalue q t reg)
        | none, some (_, (_, _, .object (_, reg) _ q t)) => return (.ident x, .lvalue q t reg)
        | none, some (_, (_, _, .function _ r ps v _ _)) => return (.ident x, .rvalue (.function r ps v))
        | _, _ => unsupported l "unresolved identifier"
    | .unary op a =>
        match op with
        | .plus | .minus | .bnot =>
            if op == .bnot then
              add "STD §6.5#4, sentence 1"; add "STD §6.5.3.3#1, sentence 2"
            else add "§6.5.3.3#1, sentence 1"
            let a ← rv a
            let t := rvalueType a
            if !(if op == .bnot then isInteger t else isArithmetic t) then
              unsupported l "unary operand (§6.5.3.3#1)"
            return (.unary op a, .rvalue (if isInteger t then integerPromote t else t))
        | .address =>
            add "§6.5.3.2#1"
            let a ← annotate .addr a
            match a.annotation with
            | .rvalue (.function r ps v) =>
                return (.unary op a, .rvalue (.pointer noQualifiers (.mk [] (.function r ps v))))
            | .lvalue q t reg =>
                if reg then constraintViolation a.loc "address of lvalue declared with register storage-class specifier"
                add "§6.5.3.2#3, 2nd sentence"
                return (.unary op a, .rvalue (.pointer q t))
            | _ => unsupported l "address of rvalue (§6.5.3.2#1)"
        | .indirection =>
            let a ← rv a
            match rvalueType a with
            | .pointer q t =>
                add "§6.5.3.2#4, sentence 2"; add "§6.5.3.2#4, sentence 3"
                return (.unary op a, if isFunction t then .rvalue (injectType t) else .lvalue q t false)
            | _ => constraintViolation a.loc "the * operator expects a pointer operand"
        | .postfixIncr | .postfixDecr =>
            let a ← annotate (if op == .postfixIncr then .incr else .decr) a
            match a.annotation with
            | .lvalue q t _ =>
                let u := rvalueCoercion t
                if !modifiable s q t || !(isArithmetic (injectType (unatomic u)) || isPointerToCompleteObject s (injectType (unatomic u))) then
                  unsupported l "increment/decrement operand (§6.5.2.4#1)"
                return (.unary op a, .rvalue (injectType u))
            | _ => constraintViolation l "expression is not assignable"
    | .binary a op b =>
        if op == .comma then add "§6.5.17#3, sentence 3"
        let a ← rv a
        let b ← rv b
        let ta := rvalueType a
        let tb := rvalueType b
        let t ← (show TypingM GenType from do
          match op with
          | .comma => pure tb
          | .arithmetic aop =>
              if aop == .add && isPointerToCompleteObject s ta && isInteger tb then return ta
              if aop == .add && isPointerToCompleteObject s tb && isInteger ta then return tb
              if aop == .sub && isPointerToCompleteObject s ta then
                if isInteger tb then return ta
                if isPointerToCompleteObject s tb && arePointersToQualifiedOrUnqualifiedCompatibleTypes ta tb then
                  return .basic (.integer .ptrdiffT)
              wellTypedBinaryArithmetic l ta aop tb
              return if aop == .shl || aop == .shr then integerPromote ta else usualArithmetic ta tb
          | .and | .or =>
              if !isScalar ta || !isScalar tb then unsupported l "logical operands (§6.5.13-14#2)"
              pure signedIntGty
          | .eq | .ne =>
              let voidPtr := fun t => match t with | GenType.pointer _ (.mk _ .void) => true | _ => false
              let objectPtr := fun t => match t with | GenType.pointer _ t => !isFunction t | _ => false
              if !(isArithmetic ta && isArithmetic tb || arePointersToQualifiedOrUnqualifiedCompatibleTypes ta tb ||
                  isPointer ta && isNullPointerConstant b || isPointer tb && isNullPointerConstant a ||
                  voidPtr ta && objectPtr tb || voidPtr tb && objectPtr ta) then
                unsupported l "equality operands (§6.5.9#2)"
              pure signedIntGty
          | _ =>
              if !(isArithmetic ta && isArithmetic tb || arePointersToQualifiedOrUnqualifiedCompatibleTypes ta tb) then
                unsupported l "relational operands (§6.5.8#2)"
              pure signedIntGty)
        return (.binary a op b, .rvalue t)
    | .cond a b c =>
        let a ← rv a
        let b ← b.mapM rv
        let c ← rv c
        let ta := rvalueType a
        let tb := b.map rvalueType |>.getD (rvalueType c)
        let tc := rvalueType c
        if !isScalar ta || (match ta with | .byte => true | _ => false) then
          unsupported l "conditional control (§6.5.15#2)"
        add "§6.5.15#2"
        let t ← (show TypingM GenType from do
          if isArithmetic tb && isArithmetic tc then
            add "§6.5.15#3, bullet 1"; add "§6.5.15#5, sentence 1"
            return usualArithmetic tb tc
          match tb, tc with
          | .struct x, .struct y | .union x, .union y =>
              if x.key != y.key then unsupported l "conditional tags (§6.5.15#3)"
              add "§6.5.15#3, bullet 2"; add "§6.5.15#5, sentence 2"
              return tb
          | .void, .void =>
              add "§6.5.15#3, bullet 3"; add "§6.5.15#5, sentence 3"
              return .void
          | _, _ => unsupported l "conditional pointer operands (§6.5.15#3)")
        return (.cond a b c, .rvalue t)
    | .assign a b =>
        let a ← annotate .assign a
        match a.annotation with
        | .lvalue q t _ =>
            if !modifiable s q t then constraintViolation l "expression is not assignable"
            let t := rvalueCoercion t
            add "§6.5.16#3, sentence 3"
            let b ← annotateAssignee rv s false l t b
            return (.assign a b, .rvalue (injectType t))
        | _ => constraintViolation l "expression is not assignable"
    | .compoundAssign a op b =>
        let a ← annotate .assign a
        let b ← rv b
        match a.annotation with
        | .lvalue q t _ =>
            if !modifiable s q t then constraintViolation l "expression is not assignable"
            let ta := injectType (rvalueCoercion t)
            let tb := rvalueType b
            if (op == .add || op == .sub) && isPointerToCompleteObject s (injectType t) && isInteger tb then pure ()
            else wellTypedBinaryArithmetic l ta op tb
            return (.compoundAssign a op b, .rvalue ta)
        | _ => constraintViolation l "expression is not assignable"
    | .cast q t a =>
        wfLvalue s q t
        let a ← rv a
        let ta := rvalueType a
        let tt := injectType t
        if (match tt with | .void => false | _ => true) then
          if !isScalar ta || !isScalar (injectType (unatomic t)) then unsupported l "cast scalar (§6.5.4#2)"
          if isPointer ta && isFloating tt then constraintViolation a.loc "pointer cannot be cast to type 'float'"
          if isFloating ta && isPointer tt then constraintViolation a.loc "operand of type 'float' cannot be cast to a pointer type"
          if (match ta, tt with | .byte, .byte => false | .byte, _ => !isInteger tt | _, .byte => !isInteger ta | _, _ => false) then
            unsupported l "byte cast"
        return (.cast q t a, .rvalue tt)
    | .call f args =>
        add "§6.5.2.2#1"
        let f ← rv f
        match rvalueType f with
        | .pointer q (.mk _ (.function (_, t) ps v)) =>
            if q != noQualifiers then unsupported l "qualified function decay"
            if isArray t || (!(match projCtype_ t with | .void => true | _ => false) && !isComplete s t) then
              unsupported l "function return type (§6.5.2.2#1)"
            let args ← annotateArgumentsAux rv s args.length ps.length f.loc v args ps
            return (.call f args, .rvalue (injectType t))
        | _ => constraintViolation l "called object type is not a function or function pointer"
    | .array fromString t elems =>
        let elems ← elems.mapM fun e => e.mapM fun a => do
          if isArray t then rv a
          else
            add "§6.7.9#11"
            annotateAssignee rv s true l t a
        return (.array fromString t elems, .rvalue (.array t (some elems.length)))
    | .struct tag ms =>
        match lookupTagDefinition s tag with
        | some (.struct defs _) =>
            if ms.length != defs.length then unsupported l "struct member count"
            let ms ← ms.mapM fun (x, e) => do
              match defs.find? (fun p => p.1.key == x.key) with
              | some (_, (_, _, _, t)) =>
                  let e ← e.mapM (annotateAssignee rv s true l t)
                  return (x, e)
              | none => unsupported l "struct initialisation member (§6.7.9)"
            return (.struct tag ms, .rvalue (.struct tag))
        | _ => unsupported l "struct initialisation tag"
    | .union tag x none => return (.union tag x none, .rvalue (.union tag))
    | .union tag x (some e) =>
        match lookupTagDefinition s tag with
        | some (.union defs) =>
            match defs.find? (fun p => p.1.key == x.key) with
            | some (_, (_, _, _, t)) =>
                let e ← annotateAssignee rv s true l t e
                return (.union tag x (some e), .rvalue (.union tag))
            | none => unsupported l "union initialisation member (§6.7.9)"
        | _ => unsupported l "union initialisation tag"
    | .memberof a x =>
        let a ← annotate .memberof a
        match a.annotation with
        | .lvalue q t _ =>
            let (mq, mt) ← lookupMember s a.loc t x
            return (.memberof a x, .lvalue (combineQualifiers q mq) mt false)
        | .rvalue t =>
            let t ← match t with
              | .struct tag | .atomic (.struct tag) => pure (Ctype.mk [] (.struct tag))
              | .union tag | .atomic (.union tag) => pure (Ctype.mk [] (.union tag))
              | _ => unsupported a.loc "member base rvalue (§6.5.2.3#1)"
            let (_, mt) ← lookupMember s a.loc t x
            return (.memberof a x, .rvalue (injectType mt))
    | .memberofptr a x =>
        let a ← rv a
        match rvalueType a with
        | .pointer q t =>
            let (mq, mt) ← lookupMember s a.loc t x
            return (.memberofptr a x, .lvalue (combineQualifiers q mq) mt false)
        | _ => unsupported a.loc "member pointer operand (§6.5.2.3#2)"
    | .compound q t a =>
        add "§6.5.2.5#1"
        if !isComplete s t && !(isArray t) then unsupported l "compound literal (§6.5.2.5#1)"
        let a ← annotateDefinitionAux annotate s g t a
        add "§6.5.2.5#4"
        return (.compound q t a, .lvalue q t false)
    | .sizeof q t | .alignof q t =>
        wfLvalue s q t
        add "§6.5.3.4#1, sentence 1"
        if isFunction t || !isComplete s t then unsupported l "sizeof/alignof (§6.5.3.4#1)"
        add "§6.5.3.4#5"
        let node := match n with | .sizeof .. => ExpressionNode.sizeof q t | _ => .alignof q t
        return (node, .rvalue (.basic (.integer .sizeT)))
    | .sizeofExpr a =>
        let a ← annotate .sizeof a
        let t := rvalueType a
        let incomplete := match t with
          | .void | .function .. | .functionNoParams .. => true
          | .array t n => n.isNone || !isComplete s t
          | .struct x | .union x => (lookupTagDefinition s x).isNone
          | _ => false
        add "§6.5.3.4#1, sentence 1"
        if incomplete then unsupported l "sizeof expression (§6.5.3.4#1)"
        add "§6.5.3.4#5"
        return (.sizeofExpr a, .rvalue (.basic (.integer .sizeT)))
    | .assert a =>
        let a ← rv a
        if !isScalar (rvalueType a) then
          unsupported l "assert operand (§7.2.1.1#2)"
        add "§7.2.1.1#2"
        return (.assert a, .rvalue .void)
    | .offsetof t x => return (.offsetof t x, .rvalue (.basic (.integer .sizeT)))
    | .annot t a =>
        let .mk cat _ _ a ← annotate ctx a
        return (a, match cat with | .lvalue q _ r => .lvalue q t r | .rvalue _ => .rvalue (injectType t))
    | .vaStart a x => let a ← rv a; return (.vaStart a x, .rvalue signedIntGty)
    | .vaArg a t => let a ← rv a; return (.vaArg a t, .rvalue (injectType t))
    | .vaCopy a b => let a ← rv a; let b ← rv b; return (.vaCopy a b, .rvalue signedIntGty)
    | .vaEnd a => let a ← rv a; return (.vaEnd a, .rvalue .void)
    | .printType a => let a ← annotate ctx a; return (.printType a, a.annotation)
    | .bmcAssume a => let a ← rv a; return (.bmcAssume a, .rvalue .void)
    | .regLoad r => return (.regLoad r, .rvalue signedIntGty)
    | .labelAddressGnu x => return (.labelAddressGnu x, .rvalue (.pointer noQualifiers (.mk [] .void)))
    | .invalid t reason => return (.invalid t reason, .rvalue (injectType t))
    | .gccStatement bs ss =>
        bs.forM fun (_, (_, _, q, t)) => wfLvalue s q t
        let ss ← annotateBlock l s g bs ss
        return (.gccStatement bs ss, ss.getLast?.map typeofStatementAsExpression |>.getD (.rvalue .void))
    | .generic .. => unsupported l "generic selection (§6.5.1.1)"
    | .builtin .. => unsupported l "builtin function"
    | .rvalue _ | .arrayDecay _ | .functionDecay _ | .atomic _ =>
        unsupported l "conversion node in untyped input")
  let ann ← unpack
  performDecays s ctx (.mk cat (stdAnnots ++ ann.map Annot.std) l n)

/-- `genTyping.lem:1902`: annotate in the ordinary conversion context. -/
def annotateRvalue (block : AnnotateBlock) (s : Sigma Unit) (g : Bindings) (e : Expression Unit) :
    TypingM (TypedExpression × GenType) := do
  let e ← annotateExpression block s g .other e
  return (e, rvalueType e)

end Silmaril.Cerberus.Frontend.Typing
