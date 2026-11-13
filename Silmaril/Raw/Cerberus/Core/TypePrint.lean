module

public import Silmaril.Cerberus.Mem.Operations.Defs

/-! Compact type and pointer printing from pp_core_ctype.ml:22-107,
pp_symbol.ml:14-40 and impl_mem.ml:375-399 at b3e11ea3. -/

@[expose] public section
namespace Silmaril.Cerberus.Core.Dynamics

/-- util/cerb_location.ml:188-228. Wire locations omit optional cursors. -/
def locationText : Loc → String
  | .unknown => "unknown location"
  | .other s => "other_location(" ++ s ++ ")"
  | .point file line column => s!"{file}:{line}:{column}:"
  | .region file line column endFile endLine endColumn =>
      s!"{file}:{line}:{column}-" ++ (if file == endFile then "" else endFile) ++
        (if line == endLine then "" else s!"{endLine}:") ++ toString endColumn

/-- annot.lem:101-134. The first source annotation supplies the diagnostic. -/
def annotationLocation (annots : List Annot) : Loc :=
  (annots.findSome? fun a => match a with | .loc l => some l | _ => none).getD .unknown

/-- util/cerb_location.ml:512-525. Library arenas preserve the caller location. -/
def libraryLocation (loc : Loc) : Bool :=
  let file := match loc with
    | .point f _ _ | .region f _ _ _ _ _ => f
    | _ => ""
  let directory := String.intercalate "/" ((file.splitOn "/").dropLast)
  ["/root/.opam/default/lib/cerberus-lib/runtime/libc/include",
   "/root/.opam/default/lib/cerberus-lib/runtime/libcore",
   "/root/.opam/default/lib/cerberus-lib/runtime/libcore/impls"].contains directory

def symbolText : Sym → String
  | .mk _ n sd => match sd with
    | .id s | .cnId s | .objectAddress s | .funArgValue s => s
    | .unnamedTag _ => s!"__cerbty_unnamed_tag_{n}"
    | _ => s!"a_{n}"

def baseText : IntegerBaseType → String
  | .ichar => "ichar" | .short => "short" | .int => "int"
  | .long => "long" | .longLong => "long_long"
  | .intN n => s!"int{n}_t" | .intLeastN n => s!"int_least{n}_t"
  | .intFastN n => s!"int_fast{n}_t" | .intmax => "intmax_t" | .intptr => "intptr_t"

def integerText : IntegerType → String
  | .char => "char" | .bool => "_Bool"
  | .signed b => match b with
    | .intN _ | .intLeastN _ | .intFastN _ | .intmax | .intptr => baseText b
    | _ => "signed " ++ baseText b
  | .unsigned b => match b with
    | .intN _ | .intLeastN _ | .intFastN _ | .intmax | .intptr => "u" ++ baseText b
    | _ => "unsigned " ++ baseText b
  | .enum s => "enum " ++ symbolText s
  | .size => "size_t" | .wchar => "wchar_t" | .wint => "wint_t"
  | .ptrdiff => "ptrdiff_t" | .ptraddr => "ptraddr_t"

def typeText : Nat → Ctype → Option String
  | 0, _ => none
  | fuel+1, .mk _ ty => do
      match ty with
      | .void => some "void"
      | .basic (.integer t) => some (integerText t)
      | .basic (.floating (.realFloating t)) => some (match t with
          | .float => "float" | .double => "double" | .longDouble => "long_double")
      | .array t n => pure ((← typeText fuel t) ++ "[" ++ (n.map toString).getD "" ++ "]")
      | .pointer _ t => pure ((← typeText fuel t) ++ "*")
      | .atomic t => pure ("_Atomic (" ++ (← typeText fuel t) ++ ")")
      | .struct s => pure ("struct " ++ symbolText s)
      | .union s => pure ("union " ++ symbolText s)
      | .byte => pure "byte"
      | .function (_, t) ps variadic => do
          let ts ← ps.mapM fun (_, t, _) => typeText fuel t
          pure ((← typeText fuel t) ++ " (" ++ String.intercalate ", " ts ++
            (if variadic then ", ..." else "") ++ ")")
      | .functionNoParams (_, t) => pure ((← typeText fuel t) ++ " ()")

/-- concrete/impl_mem.ml:375-399, at the default diagnostic verbosity. -/
def pointerText (fuel : Nat) : Mem.Concrete.Pointer → Option String
  | .null t => do pure ("NULL(" ++ (← typeText fuel t) ++ ")")
  | .function s => some ("Cfunction(" ++ symbolText s ++ ")")
  | .allocated id addr => some ("(@" ++ toString id ++ ", 0x" ++ hex addr ++ ")")
  | .unprovenanced addr => some ("(@empty, 0x" ++ hex addr ++ ")")
where
  hex (n : Int) : String := (if n < 0 then "-" else "") ++ String.ofList (Nat.toDigits 16 n.natAbs)

/-- driver_ocaml.ml:89-93 uses OCaml String.escaped before JSON encoding.
This is producer output transport, not a census comparison normalization. -/
def batchEscape (s : String) : String :=
  String.join (s.toList.map fun c => match c with
    | '\\' => "\\\\" | '"' => "\\\"" | '\n' => "\\n" | '\r' => "\\r"
    | '\t' => "\\t" | '\x08' => "\\b"
    | c => if c.toNat < 32 || c.toNat > 126 then
        "\\" ++ String.ofList [Char.ofNat (48 + c.toNat / 100),
          Char.ofNat (48 + c.toNat / 10 % 10), Char.ofNat (48 + c.toNat % 10)]
      else String.singleton c)

end Silmaril.Cerberus.Core.Dynamics
