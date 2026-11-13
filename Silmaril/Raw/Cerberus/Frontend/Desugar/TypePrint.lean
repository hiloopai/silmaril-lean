module

public import Silmaril.Cerberus.Ctype.Defs

/-! # C type text in desugaring diagnostics

The colour-free, non-executable-spec path of `pp_ail.ml:142-324` at `b3e11ea3`.
This is the C declarator printer selected by `Pp_errors.string_of_ctype`, including
its precedence and spacing, with human names for struct and union tags.
-/

@[expose] public section
namespace Silmaril.Cerberus.Frontend.Desugar.TypePrint

open Silmaril.Cerberus

/-- `Cerb_location.location_to_string` (`util/cerb_location.ml:188-228`), without a cursor. -/
def locationText : Loc → String
  | .unknown => "unknown location"
  | .other s => "other_location(" ++ s ++ ")"
  | .point file line column => s!"{file}:{line}:{column}:"
  | .region file line column endFile endLine endColumn =>
    s!"{file}:{line}:{column}-" ++ (if file == endFile then "" else endFile) ++
      (if line == endLine then "" else s!"{endLine}:") ++ toString endColumn

/-- `Pp_symbol.to_string_pretty` (`pp_symbol.ml:12-40`), default verbosity. -/
def symbolText (s : Sym) : String :=
  match s.description with
  | .id x | .objectAddress x | .funArgValue x | .cnId x => x
  | .unnamedTag _ => s!"__cerbty_unnamed_tag_{s.number}"
  | _ => s!"a_{s.number}"

/-- `Pp_symbol.to_string_pretty` (`pp_symbol.ml:12-40`), human tag spelling. -/
def humanSymbolText (s : Sym) : String :=
  match s.description with
  | .unnamedTag loc => "(unnamed tag at " ++ locationText loc ++ ")"
  | _ => symbolText s

/-- `Pp_ail.string_of_integerBaseType` (`pp_ail.ml:142-153`). -/
def stringOfIntegerBaseType : IntegerBaseType → String
  | .ichar => "char"
  | .short => "short"
  | .int => "int"
  | .long => "long"
  | .longLong => "long long"
  | .intN n => s!"int{n}_t"
  | .intLeastN n => s!"int_least{n}_t"
  | .intFastN n => s!"int_fast{n}_t"
  | .intmax => "intmax_t"
  | .intptr => "intptr_t"

/-- `Pp_ail.pp_integerType` (`pp_ail.ml:167-194`), with colours disabled. -/
def ppIntegerType : IntegerType → String
  | .char => "char"
  | .bool => "_Bool"
  | .signed b => match b with
    | .intN _ | .intLeastN _ | .intFastN _ | .intmax | .intptr => stringOfIntegerBaseType b
    | _ => "signed " ++ stringOfIntegerBaseType b
  | .unsigned b => match b with
    | .intN _ | .intLeastN _ | .intFastN _ | .intmax | .intptr => "u" ++ stringOfIntegerBaseType b
    | _ => "unsigned " ++ stringOfIntegerBaseType b
  | .enum s => "enum " ++ symbolText s
  | .size => "size_t"
  | .wchar => "wchar_t"
  | .wint => "wint_t"
  | .ptrdiff => "ptrdiff_t"
  | .ptraddr => "ptraddr_t"

/-- `Pp_ail.pp_qualifiers` (`pp_ail.ml:118-123`): each qualifier includes its trailing space. -/
def ppQualifiers (qs : Qualifiers) : String :=
  (if qs.const then "const " else "") ++
  (if qs.restrict then "restrict " else "") ++
  (if qs.volatile then "volatile " else "")

/-- `Pp_ail.pp_basicType` (`pp_ail.ml:232-236`). -/
def ppBasicType : BasicType → String
  | .integer t => ppIntegerType t
  | .floating (.realFloating t) => match t with
    | .float => "float" | .double => "double" | .longDouble => "long double"

/-- `precOf` inside `pp_ctype_aux` (`pp_ail.ml:239-255`). -/
def precOf : CtypeNode → Nat
  | .void | .basic _ | .atomic _ | .struct _ | .union _ => 0
  | .array .. => 1
  | .function .. | .functionNoParams _ => 2
  | .pointer .. => 3
  | .byte => 4

/-- `aux` inside `pp_ctype_aux` (`pp_ail.ml:257-312`): its continuation is the
part of the declarator already printed. Fuel bounds diagnostic nesting. -/
def ppCtypeAux : Nat → Nat → Qualifiers → Ctype → String → String
  | 0, _, _, _, _ => "<type nesting too deep>"
  | fuel + 1, p, qs, .mk _ ty, k =>
    let p' := precOf ty
    let wrap (s : String) := if p' > 0 && p' >= p then s else "(" ++ s ++ ")"
    let paramsText (params : List (Qualifiers × Ctype × Bool)) (variadic : Bool) :=
      (if params.isEmpty then "void" else
        String.intercalate ", " (params.map fun (q, t, _) => ppCtypeAux fuel p' q t "")) ++
        (if variadic then ", ..." else "")
    match ty with
    | .void => ppQualifiers qs ++ "void" ++ k
    | .basic b => ppQualifiers qs ++ ppBasicType b ++ k
    | .array elem n => ppCtypeAux fuel p' qs elem (k ++ "[" ++ (n.map toString).getD "" ++ "]")
    | .function (rq, rt) params variadic =>
      ppCtypeAux fuel p' rq rt "" ++ " (" ++ k ++ ")(" ++ paramsText params variadic ++ ")"
    | .functionNoParams (rq, rt) => ppCtypeAux fuel p' rq rt "" ++ " (" ++ k ++ ")()"
    | .pointer refQs refTy => match refTy with
      | .mk _ (.function (rq, rt) params variadic) =>
        ppCtypeAux fuel p' rq rt "" ++ " (*" ++ k ++ ") (" ++ paramsText params variadic ++ ")"
      | _ => ppCtypeAux fuel p' refQs refTy (wrap ("*" ++ ppQualifiers qs ++ k))
    | .atomic t => ppQualifiers qs ++ "_Atomic(" ++ ppCtypeAux fuel p' ⟨false, false, false⟩ t "" ++ ")" ++ k
    | .struct s => ppQualifiers qs ++ "struct " ++ humanSymbolText s ++ k
    | .union s => ppQualifiers qs ++ "union " ++ humanSymbolText s ++ k
    | .byte => ppQualifiers qs ++ "byte" ++ k

/-- `String_ail.string_of_ctype ~is_human:true` (`string_ail.ml:9-10`), the oracle's
colour-free error spelling, with the same nesting bound as the parser. -/
def stringOfCtype (qs : Qualifiers) (ty : Ctype) : String :=
  ppCtypeAux 1000000 1 qs ty ""

end Silmaril.Cerberus.Frontend.Desugar.TypePrint
