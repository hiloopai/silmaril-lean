module

public import Silmaril.Data.Layout.Defs

/-!
# Declarations as C source

`CTy.declare t d` is the C declaration of declarator `d` with type `t` (`struct malloc_chunk *fd`,
`mchunkptr bins[254]`, `char (*p)[4]`); `Decl.cSource` renders a tag definition as C source and
`Decl.ptype` as `gdb`'s `ptype` prints it from DWARF. Comparing `ptype` with a recorded `gdb`
dump relates a declaration to the compiled C struct (`Glibc.Malloc.Thms`).
-/

@[expose] public section

namespace Silmaril.Data.Layout

/-- A decimal digit. -/
def digitStr : Nat → String
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"

/-- Decimal numeral with `fuel` digits at most (`Nat.repr`, kernel-reducible in modules). -/
def natStrAux : Nat → Nat → String
  | 0, _ => ""
  | fuel + 1, n => if n < 10 then digitStr n else natStrAux fuel (n / 10) ++ digitStr (n % 10)

/-- Decimal numeral. -/
def natStr (n : Nat) : String := natStrAux (n + 1) n

/-- C spelling of an integer type. -/
def intName : IntKind → Sign → String
  | .char, .plain => "char" | .char, .signed => "signed char" | .char, .unsigned => "unsigned char"
  | .short, .unsigned => "unsigned short" | .short, _ => "short"
  | .int, .unsigned => "unsigned int" | .int, _ => "int"
  | .long, .unsigned => "unsigned long" | .long, _ => "long"
  | .longLong, .unsigned => "unsigned long long" | .longLong, _ => "long long"
  | .int128, .unsigned => "unsigned __int128" | .int128, _ => "__int128"
  | .size, .signed => "ssize_t" | .size, _ => "size_t"
  | .ptrdiff, _ => "ptrdiff_t"
  | .intptr, .unsigned => "uintptr_t" | .intptr, _ => "intptr_t"
  | .wchar, _ => "wchar_t"
  | .exact n, .unsigned => "uint" ++ natStr (8 * n) ++ "_t" | .exact n, _ => "int" ++ natStr (8 * n) ++ "_t"

def floatName : FloatKind → String
  | .float => "float" | .double => "double" | .longDouble => "long double"
  | .float128 => "_Float128"

def withDeclarator (base d : String) : String :=
  if d.isEmpty then base else base ++ " " ++ d

/-- The declaration of `d` with type `t`. -/
def CTy.declare : CTy → String → String
  | .void, d => withDeclarator "void" d
  | .bool, d => withDeclarator "_Bool" d
  | .int k s, d => withDeclarator (intName k s) d
  | .float k, d => withDeclarator (floatName k) d
  | .ptr t, d => match t with
    | .array .. => t.declare ("(*" ++ d ++ ")")
    | _ => t.declare ("*" ++ d)
  | .enum tag _, d => withDeclarator ("enum " ++ tag) d
  | .array e n, d => e.declare (d ++ "[" ++ natStr n ++ "]")
  | .struct tag, d => withDeclarator ("struct " ++ tag) d
  | .union tag, d => withDeclarator ("union " ++ tag) d
  | .typedef name _, d => withDeclarator name d

def Kind.keyword : Kind → String
  | .struct => "struct" | .union => "union"

/-- One member line. -/
def Field.declare (f : Field) : String :=
  let alignas := match f.alignas with
    | some a => "_Alignas(" ++ natStr a ++ ") "
    | none => ""
  let bits := match f.bits with
    | some b => " : " ++ natStr b
    | none => ""
  alignas ++ f.ty.declare f.name ++ bits ++ ";"

/-- `String.join`, by structural recursion (kernel-reducible in modules). -/
def concatAll : List String → String
  | [] => ""
  | s :: ss => s ++ concatAll ss

/-- The definition, with members indented by `indent`. -/
def Decl.render (d : Decl) (indent : String) : String :=
  d.kind.keyword ++ " " ++ d.tag ++ " {\n" ++
    concatAll (d.fields.map fun f => indent ++ f.declare ++ "\n") ++ "}"

/-- As C source. -/
def Decl.cSource (d : Decl) : String := d.render "  " ++ ";\n"

/-- As `gdb`'s `ptype struct tag` prints it. -/
def Decl.ptype (d : Decl) : String := "type = " ++ d.render "    "

end Silmaril.Data.Layout
