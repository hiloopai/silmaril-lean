module

public import Silmaril.Cerberus.Frontend.Typing.Effect.Defs

@[expose] public section
namespace Silmaril.Cerberus.Frontend.Typing
open Silmaril.Cerberus Ail

/-- `genTyping.lem:21`: LP64 ranges for the constant candidate types (§6.4.4.1#5). -/
def inRange (n : Int) (i : IntegerType) : Bool :=
  let (bits, signed) := match i with
    | .signed .int => (32, true)
    | .unsigned .int => (32, false)
    | .signed _ => (64, true)
    | _ => (64, false)
  if signed then -(2 ^ (bits - 1) : Int) ≤ n && n < (2 ^ (bits - 1) : Int)
  else 0 ≤ n && n < (2 ^ bits : Int)

/-- `genTyping.lem:35`: try integer types in the standard's order. -/
def tryRanges (l : Loc) (n : Int) : List IntegerType → TypingM IntegerType
  | [] => fail l "integer constant cannot be represented by any type"
  | t :: ts => if inRange n t then pure t else tryRanges l n ts

/-- `genTyping.lem:50`: non-agnostic constant typing, ISO C11 §6.4.4.1#5. -/
def genTypingTypeOfConstant (l : Loc) : IntegerConstant → TypingM GenIntegerType
  | .max i | .min i => pure (.concrete i)
  | .iconstant n b suff => do
      let si := IntegerType.signed .int
      let ui := IntegerType.unsigned .int
      let sl := IntegerType.signed .long
      let ul := IntegerType.unsigned .long
      let sll := IntegerType.signed .longLong
      let ull := IntegerType.unsigned .longLong
      let ts := match b, suff with
        | .decimal, none => [si, sl, sll]
        | _, none => [si, ui, sl, ul, sll, ull]
        | _, some .u => [ui, ul, ull]
        | .decimal, some .l => [sl, sll]
        | _, some .l => [sl, ul, sll, ull]
        | _, some .ul => [ul, ull]
        | .decimal, some .ll => [sll]
        | _, some .ll => [sll, ull]
        | _, some .ull => [ull]
      return .concrete (← tryRanges l n ts)

/-- `genTyping.lem:448`: type constants, preserving annotation effects. -/
def typecheckConstant (l : Loc) : Constant → TypingM GenType
  | .integer i => return .basic (.integer (← genTypingTypeOfConstant l i))
  | .floating (_, s) => do
      add "§6.4.4.2#4"
      return .basic (.floating (.realFloating (match s with
        | none => .double | some .f => .float | some .l => .longDouble)))
  | .character (p, _) => do
      add (if p.isNone then "§6.4.4.4#10" else "§6.4.4.4#11")
      return .basic (.integer (.concrete (match p with
        | none => .signed .int | some .wide => .wchar
        | some .utf16 => .unsigned (.intLeastN 16) | some .utf32 => .unsigned (.intLeastN 32))))
  | .indeterminate t => pure (injectType t)
  | .null => pure (.pointer noQualifiers (.mk [] .void))
  | .array t cs => do
      if cs.isEmpty then unsupported l "empty constant array"
      let _ ← cs.mapM (typecheckConstant l)
      return .array t (some cs.length)
  | .struct x ms => do
      let _ ← ms.mapM fun p => typecheckConstant l p.2
      return .struct x
  | .union x _ c => do let _ ← typecheckConstant l c; return .union x
  | .predefined _ => pure (.basic (.integer (.concrete .bool)))
termination_by c => sizeOf c
decreasing_by
  all_goals first | decreasing_trivial |
    (have h := List.sizeOf_lt_of_mem ‹p ∈ ms›
     rcases p with ⟨i, c⟩
     simp_all
     omega)

/-- `genTyping.lem:432`: string types, ISO C11 §6.4.5#6. -/
def annotateStringLiteral (s : StringLiteral) : ExpressionNode GenTypeCategory × GenTypeCategory :=
  let i := match s.1 with
    | none | some .utf8 => IntegerType.char
    | some .utf16 => .unsigned (.intLeastN 16)
    | some .utf32 => .unsigned (.intLeastN 32)
    | some .wide => .wchar
  let t := Ctype.mk [] (.basic (.integer i))
  let n : Nat := s.2.foldl (fun n x => n + x.2.length) 1
  (.str s, .lvalue noQualifiers (.mk [] (.array t (some n))) false)

end Silmaril.Cerberus.Frontend.Typing
