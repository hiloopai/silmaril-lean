module

public import Silmaril.Compiler.Clang.Vector.Defs
public import Silmaril.Compiler.Clang.Builtin.Defs

/-! # Complex values as pairs of real components

The frontend represents `_Complex float` and `_Complex double` by ordinary structs
with `re` and `im` members. Helpers take values as parameters so componentwise
operations evaluate each source operand once. Long double and integer complex
types, byte reinterpretations, multiplication and division remain rejected.
-/

@[expose] public section

namespace Silmaril.Clang.Complex

open Silmaril.Cerberus Ail

def component (imag : Bool) : Identifier := .mk .unknown (if imag then "im" else "re")

def members (t : Ctype) : List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)) :=
  [ (component false, (.mk [], none, Vector.noQ, t)),
    (component true, (.mk [], none, Vector.noQ, t)) ]

def initValue (s : Sym) (re im : TypedExpression) : TypedExpression :=
  Vector.rv (Vector.structTy s) (.struct s [(component false, some re), (component true, some im)])

/-- Aggregate constructors are initializers in Ail, not runtime expressions. Materialize
one as a compound literal before loading its pair value. -/
def value (s : Sym) (re im : TypedExpression) : TypedExpression :=
  let t := Vector.structTy s
  Vector.load t (Vector.lv t (.compound Vector.noQ t (initValue s re im)))

def zero (t : Ctype) : TypedExpression := Builtin.cast t (Builtin.int 0)

def part (s : Sym) (t : Ctype) (a : Sym) (imag : Bool) : TypedExpression :=
  Vector.load t (Vector.lv t (.memberof (Vector.lv (Vector.structTy s) (.ident a)) (component imag)))

def truth (s : Sym) (t : Ctype) (a : Sym) : TypedStatement :=
  Builtin.ret (Builtin.test .or (Builtin.test .ne (part s t a false) (zero t))
    (Builtin.test .ne (part s t a true) (zero t)))

def convert (s : Sym) (t : Ctype) (dst : Sym) (dt : Ctype) (a : Sym) : TypedStatement :=
  Builtin.ret (value dst (Builtin.cast dt (part s t a false)) (Builtin.cast dt (part s t a true)))

def unary (s : Sym) (t : Ctype) (conj : Bool) (a : Sym) : TypedStatement :=
  let neg := fun e => Vector.rv t (.unary .minus e)
  Builtin.ret (value s (if conj then part s t a false else neg (part s t a false))
    (neg (part s t a true)))

def binary (s : Sym) (t : Ctype) (op : ArithmeticOperator) (a b : Sym) : TypedStatement :=
  Builtin.ret (value s (Builtin.arith t op (part s t a false) (part s t b false))
    (Builtin.arith t op (part s t a true) (part s t b true)))

def compare (s : Sym) (t : Ctype) (equal : Bool) (a b : Sym) : TypedStatement :=
  let op : BinaryOperator := if equal then .eq else .ne
  Builtin.ret (Builtin.test (if equal then .and else .or)
    (Builtin.test op (part s t a false) (part s t b false))
    (Builtin.test op (part s t a true) (part s t b true)))

end Silmaril.Clang.Complex
