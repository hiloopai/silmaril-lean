module

public import Silmaril.Cerberus.Core.TypePrint.Defs
public import Silmaril.Cerberus.Core.Compatibility.Defs

/-! The printf fragment reached by the census. References are to formatted.lem
and driver.lem at b3e11ea3. Flags and width remain Unsupported; real
fixed-point precision is enabled. -/

@[expose] public section
namespace Silmaril.Cerberus.Core.Dynamics
open Mem.Concrete

abbrev PrintArgs := List (Ctype × Pointer)

/-- formatted.lem:349-385, decode.ml:223-225. Read a zero-terminated character
array, encoding each integer modulo 256. The finite
bound gives an explicit Unsupported result rather than inventing a terminator. -/
def loadString (tags : Tags) : Nat → State → Ctype → Pointer → Except Failure (String × State)
  | 0, _, _, _ => .error (.unsupported "printf string bound")
  | fuel+1, s, ty, p => do
      let (v, s) ← loadTyped tags s ty p
      match v with
      | .integer _ n =>
          if n == 0 then pure ("", s)
          else
            let next ← match p with
              | .allocated id addr => pure (.allocated id (addr+1))
              | .unprovenanced addr => pure (.unprovenanced (addr+1))
              | _ => throw (.unsupported "printf character pointer")
            let (text, s) ← loadString tags fuel s ty next
            pure (String.singleton (Char.ofNat (n % 256).toNat) ++ text, s)
      | _ => throw (.unsupported "printf unspecified character exception")

/-- formatted.lem:493-541. Default conversions check exact integer types;
l and ll accept either sign of their respective base, as the pin does. -/
def printIntegerType (lm : String) (signed : Bool) (ty : Ctype) (tags : Tags := ∅) : Bool :=
  match ty with
  | .mk _ (.basic (.integer ity)) =>
      match lm, Core.normalizeInteger ity tags.enums with
      | "", some t => t == (if signed then .signed .int else .unsigned .int)
      | "l", some (.signed .long) | "l", some (.unsigned .long) => true
      | "ll", some (.signed .longLong) | "ll", some (.unsigned .longLong) => true
      | _, _ => false
  | _ => false

/-- formatted.lem:548-578 uses naturalFromInteger and base 8/16 digits. -/
def radix (base : Nat) (upper : Bool) (n : Nat) : String :=
  let digits := (if upper then "0123456789ABCDEF" else "0123456789abcdef").toList
  String.ofList (go (n+1) n digits)
where
  go : Nat → Nat → List Char → List Char
    | 0, _, _ => []
    | fuel+1, n, digits =>
        let c := digits[n % base]?.getD '0'
        if n < base then [c] else go fuel (n / base) digits ++ [c]

/-- formatted.lem:417-489,534-610,620-705. Integer radix, character and fixed floating conversions use the pinned
rendering, unsigned-char conversion and binary64 profile. Unsupported syntax is checked first. -/
def printConversion (tags : Tags) (s : State) (lm : String) (c : Char)
    (args : PrintArgs) (precision : Option Nat := none) : Except Failure (String × PrintArgs × State) := do
  if !(c == 'd' || c == 'i' || c == 'u' || c == 'o' || c == 'x' || c == 'X' || c == 'c' || c == 's' || c == 'p' || c == 'f') then
    throw (.unsupported s!"printf conversion %{lm}{c}")
  -- formatted.lem:611-621: wide characters raise a host exception; other
  -- character length modifiers emit the pinned DUMMY diagnostic.
  if c == 'c' && lm == "l" then throw (.unsupported "Cerberus printf %lc exception")
  if c == 'c' && lm != "" then throw (.ub (.DUMMY "TODO_find_quote_printf_CS_c"))
  if c == 'f' && lm == "ll" then throw (.ub .UB158_invalid_length_modifier)
  if c != 'f' && precision.isSome then throw (.unsupported "printf non-floating precision")
  if precision.getD 6 > 1024 then throw (.unsupported "printf precision bound")
  let (ty, p) :: rest := args | throw (.ub .UB153a_insufficient_arguments_for_format)
  let valid := if c == 's' then match ty with
      | .mk _ (.pointer _ (.mk _ (.basic (.integer .char)))) => lm == ""
      | .mk _ (.pointer _ (.mk _ (.basic (.integer (.signed .ichar))))) => lm == ""
      | .mk _ (.pointer _ (.mk _ (.basic (.integer (.unsigned .ichar))))) => lm == ""
      | _ => false
    else if c == 'p' then match ty with
      | .mk _ (.pointer _ (.mk _ .void)) => lm == ""
      | _ => false
    else if c == 'f' then
      match ty with
      | .mk [] (.basic (.floating (.realFloating .double))) => lm == "" || lm == "l"
      | _ => false
    else printIntegerType lm (c == 'd' || c == 'i' || c == 'c') ty tags
  if !valid then throw (.ub .UB153b_illtyped_argument_for_format)
  let (v, s) ← loadTyped tags s ty p
  match c, v with
  | 'f', .floating _ x => pure (Floating.fixed (precision.getD 6) x, rest, s)
  | 's', .pointer refTy ptr =>
      let (text, s) ← loadString tags 65536 s refTy ptr
      pure (text, rest, s)
  | 'p', .pointer _ ptr =>
      let some text := pointerText 256 ptr | throw (.unsupported "printf pointer type printer")
      pure (text, rest, s)
  | 's', .unspecified _ | 'p', .unspecified _ => throw (.ub .UB_unspecified_lvalue)
  | 'c', .integer _ n => pure (String.singleton (Char.ofNat (n % 256).toNat), rest, s)
  | 'o', .integer _ n => pure (radix 8 false n.natAbs, rest, s)
  | 'x', .integer _ n => pure (radix 16 false n.natAbs, rest, s)
  | 'X', .integer _ n => pure (radix 16 true n.natAbs, rest, s)
  | 'u', .integer _ n => pure (toString n.natAbs, rest, s)
  | _, .integer _ n => pure (toString n, rest, s)
  | _, .unspecified _ => pure ("UNSPEC", rest, s)
  | _, _ => throw (.unsupported "printf conversion value")

/-- formatted.lem:709-757,815-825. Extra arguments are ignored. Percent escapes
consume none. More elaborate format syntax stops explicitly. -/
def printFormat (tags : Tags) : Nat → List Char → PrintArgs → State → Except Failure (String × State)
  | 0, _, _, _ => .error (.unsupported "printf format depth")
  | _+1, [], _, s => .ok ("", s)
  | fuel+1, '%' :: '%' :: cs, args, s => do
      let (text, s) ← printFormat tags fuel cs args s
      pure ("%" ++ text, s)
  | fuel+1, '%' :: cs, args, s => do
      let (precision, cs) ← match cs with
        | '.' :: tail =>
            let digits := tail.takeWhile Char.isDigit
            let n := (String.ofList digits).toNat?.getD 0
            pure (some n, tail.drop digits.length)
        | _ => pure (none, cs)
      let (lm, tail) := match cs with
        | 'l' :: 'l' :: tail => ("ll", tail)
        | 'l' :: tail => ("l", tail)
        | _ => ("", cs)
      let c :: tail := tail | throw (.unsupported "printf incomplete format")
      let (text, args, s) ← printConversion tags s lm c args precision
      let (more, s) ← printFormat tags fuel tail args s
      pure (text ++ more, s)
  | fuel+1, c :: cs, args, s => do
      let (text, s) ← printFormat tags fuel cs args s
      pure (String.singleton c ++ text, s)

end Silmaril.Cerberus.Core.Dynamics
