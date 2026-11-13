module

public import Silmaril.Cerberus.Frontend.Typing.TypesAux.Defs
public import Silmaril.Cerberus.Ail.Reject.Defs

/-! The typing effects of `ail/errorMonad.lem` and well-formedness checks of
`ail/ailWf.lem`, shared by the expression and program typing ports. -/

@[expose] public section
namespace Silmaril.Cerberus.Frontend.Typing
open Silmaril.Cerberus Ail

/-- `ail/errorMonad.lem:8`: annotation stack and typing errors. -/
abbrev TypingM := StateT (List (List String)) (Except Ail.Reject)

/-- `ail/errorMonad.lem:19`: prepend to the current annotation frame. -/
def add (s : String) : TypingM Unit := modify fun
  | [] => [[s]]
  | x :: xs => (s :: x) :: xs

/-- `ail/errorMonad.lem:29`: pop the annotations consumed by an expression. -/
def unpack : TypingM (List String) := do
  match ← get with
  | [] => pure []
  | x :: xs => set xs; pure x

/-- `ail/errorMonad.lem:15`: typing failure with the oracle's short message. -/
def fail {α : Type} (loc : Loc) (message : String) : TypingM α :=
  throw ⟨"typing", .loc loc, message⟩

/-- `errorMonad.lem:15`: an error inhabits the typing monad at every result type. -/
instance {α : Type} : Nonempty (TypingM α) := ⟨fail .unknown "typing stopped"⟩

/-- `errorMonad.lem:61`, `pp_errors.ml:417`: constraint short-message prefix. -/
def constraintViolation {α : Type} (l : Loc) (msg : String) : TypingM α :=
  fail l ("constraint violation: " ++ msg)

/-- Explicit boundary for unported branches of `ail/genTyping.lem:600`. -/
def unsupported {α : Type} (loc : Loc) (what : String) : TypingM α :=
  fail loc ("Silmaril: typing not yet ported: " ++ what)

/-- `loc.lem`: the first location annotation of a type. -/
def typeLoc : Ctype → Loc
  | .mk a _ => ((a.findSome? fun | .loc l => some l | _ => none).getD .unknown)

/-- `genTypes.lem:229`: inject a C type without interpreting integer promotions. -/
def injectType : Ctype → GenType
  | .mk _ .void => .void
  | .mk _ (.basic (.integer i)) => .basic (.integer (.concrete i))
  | .mk _ (.basic (.floating f)) => .basic (.floating f)
  | .mk _ (.array t n) => .array t n
  | .mk _ (.function r ps v) => .function r ps v
  | .mk _ (.functionNoParams r) => .functionNoParams r
  | .mk _ (.pointer q t) => .pointer q t
  | .mk _ (.struct t) => .struct t
  | .mk _ (.union t) => .union t
  | .mk _ (.atomic t) => .atomic (injectType t)
  | .mk _ .byte => .byte

/-- `genTypes.lem:31`: signed int generic type. -/
def signedIntGty : GenType := .basic (.integer (.concrete (.signed .int)))

/-- `ailWf.lem:23`: reject unported restrict diagnostics conservatively. -/
def wfLvalueAux (q : Qualifiers) (t : Ctype) : TypingM Unit := do
  if q.restrict then
    match projCtype_ t with
    | .pointer _ r => if isFunction r then unsupported (typeLoc r) "restrict function pointer (§6.7.3#2)"
    | _ => constraintViolation (typeLoc t) "restrict requires a pointer"
  if isFunction t && q != noQualifiers then
    unsupported (typeLoc t) "qualified function (§6.7.3#9)"

/-- `ailWf.lem:71`: well-formed types; invalid shapes fail closed. -/
def wfType (s : Sigma Unit) : Ctype → TypingM Unit
  | .mk _ (.array t _) => do
      if isFunction t then constraintViolation (typeLoc t) "element of the array has function type"
      if !isComplete s t then constraintViolation (typeLoc t) "array has incomplete type"
      if hasFlexibleArrayMember s t then
        constraintViolation (typeLoc t) "struct member with a flexible array member found as element of an array"
      wfType s t
  | .mk _ (.pointer q t) => do wfType s t; wfLvalueAux q t
  | .mk _ (.atomic t) => do
      if isArray t || isFunction t || (match projCtype_ t with | .atomic _ => true | _ => false) then
        constraintViolation (typeLoc t) "invalid use of _Atomic"
      wfType s t
  | .mk _ (.function (q, r) ps _) => do
      if isArray r || isFunction r then constraintViolation (typeLoc r) "function cannot return a function type or an array type"
      wfType s r
      wfLvalueAux q r
      let voidParam := match ps with | [(_, .mk _ .void, _)] => true | _ => false
      if voidParam then
        if ps.any (fun p => p.1 != noQualifiers) then unsupported .unknown "qualified void parameter (§6.7.6.3#10)"
      else ps.attach.forM fun p => do
        let q := p.val.1
        let t := p.val.2.1
        if isArray t || isFunction t then fail (typeLoc t) "internal: the parameter type was not adjusted"
        if !isComplete s t then constraintViolation (typeLoc t) "incomplete type"
        wfType s t
        wfLvalueAux q t
  | .mk _ (.functionNoParams (q, r)) => do
      if isArray r || isFunction r then constraintViolation (typeLoc r) "function cannot return a function type or an array type"
      wfType s r; wfLvalueAux q r
  | _ => pure ()
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have h := List.sizeOf_lt_of_mem p.property
     rcases p with ⟨⟨q, t, reg⟩, hp⟩
     simp_all
     omega)

/-- `ailWf.lem:135`. -/
def wfLvalue (s : Sigma Unit) (q : Qualifiers) (t : Ctype) : TypingM Unit := do
  wfType s t; wfLvalueAux q t

end Silmaril.Cerberus.Frontend.Typing
