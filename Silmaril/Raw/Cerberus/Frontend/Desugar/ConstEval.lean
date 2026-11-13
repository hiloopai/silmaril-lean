module

public import Silmaril.Cerberus.Frontend.Desugar.Predicates.Defs

/-! # Integer constant expressions

`evaluate_integer_constant_expression` (`cabs_to_ail.lem:1128`) runs
`Mini_pipeline.evalIntegerConstantExpression` (`mini_pipeline.lem:65-205`): it types the
expression (GenTyping), elaborates it to Core and runs it, checking that the value is
representable in the expression's type (STD §6.6#4). Here the typed expression is evaluated
natively, for the forms whose typing and value do not need the implementation's layouts:
integer constants (STD §6.4.4.1, LP64: `int` has 32 bits, `long` and `long long` 64),
plain character constants, and the unary, binary and conditional operators on them, under the
integer promotions and usual arithmetic conversions (STD §6.3.1.1, §6.3.1.8).

Not ported yet (they reject with `notPorted`): `sizeof`, `_Alignof`, `offsetof`, escape
sequences and prefixes in character constants, and every evaluation
with undefined behaviour (overflow, division by zero, out-of-range shifts), whose Cerberus
error is the memory model's.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- The integer types of an evaluation: `int`, `long` and `long long` (rank 1-3), signed or
not, under LP64. -/
structure ConstIntType where
  rank : Nat
  signed : Bool
  deriving DecidableEq

namespace ConstIntType

/-- The width in bits. -/
def width (t : ConstIntType) : Nat := if t.rank == 1 then 32 else 64

/-- The smallest and largest values. -/
def bounds (t : ConstIntType) : Int × Int :=
  if t.signed then (-(2 ^ (t.width - 1) : Nat), (2 ^ (t.width - 1) - 1 : Nat)) else (0, (2 ^ t.width - 1 : Nat))

/-- Whether `n` is a value of the type. -/
def represents (t : ConstIntType) (n : Int) : Bool := t.bounds.1 ≤ n && n ≤ t.bounds.2

/-- `int`. -/
def int : ConstIntType := ⟨1, true⟩

end ConstIntType

/-- The types an integer constant may have, in order (STD §6.4.4.1#5). -/
def integerConstantCandidates (basis : Basis) : Option IntegerSuffix → List ConstIntType
  | none =>
    if basis == .decimal then [⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩]
    else [⟨1, true⟩, ⟨1, false⟩, ⟨2, true⟩, ⟨2, false⟩, ⟨3, true⟩, ⟨3, false⟩]
  | some .u => [⟨1, false⟩, ⟨2, false⟩, ⟨3, false⟩]
  | some .l =>
    if basis == .decimal then [⟨2, true⟩, ⟨3, true⟩] else [⟨2, true⟩, ⟨2, false⟩, ⟨3, true⟩, ⟨3, false⟩]
  | some .ul => [⟨2, false⟩, ⟨3, false⟩]
  | some .ll => if basis == .decimal then [⟨3, true⟩] else [⟨3, true⟩, ⟨3, false⟩]
  | some .ull => [⟨3, false⟩]

/-- The usual arithmetic conversions on promoted integer types (STD §6.3.1.8#1). -/
def usualArithmeticConversion (t₁ t₂ : ConstIntType) : ConstIntType :=
  if t₁.signed == t₂.signed then if t₁.rank ≥ t₂.rank then t₁ else t₂
  else
    let (s, u) := if t₁.signed then (t₁, t₂) else (t₂, t₁)
    if u.rank ≥ s.rank then u
    else if s.width > u.width then s
    else ⟨s.rank, false⟩

/-- The value of `n` converted to the unsigned type `t` (STD §6.3.1.3#2). -/
def wrapUnsigned (t : ConstIntType) (n : Int) : Int := n % (2 ^ t.width : Nat)

/-- A value converted to `t`: for a signed type it must be representable. -/
def convertConst (loc : Loc) (t : ConstIntType) (n : Int) : DesugM Int :=
  if t.signed then
    if t.represents n then return n
    else notPorted loc "an integer constant expression with an out-of-range conversion"
  else return wrapUnsigned t n

/-- The result of an arithmetic operation in `t`: unsigned arithmetic wraps, signed overflow is
undefined (STD §6.5#5). -/
def arithmeticResult (loc : Loc) (t : ConstIntType) (n : Int) : DesugM (Int × ConstIntType) :=
  if t.signed then
    if t.represents n then return (n, t)
    else notPorted loc "an integer constant expression that overflows"
  else return (wrapUnsigned t n, t)

/-- The bitwise operations on the two's complement representations in `t`. -/
def bitwiseConst (t : ConstIntType) (op : ArithmeticOperator) (a b : Int) : Int :=
  let w := t.width
  let m : Nat := 2 ^ w
  let ua := (a % m).toNat
  let ub := (b % m).toNat
  let r : Nat := match op with
    | .band => ua &&& ub
    | .bor => ua ||| ub
    | _ => ua ^^^ ub
  if t.signed && r ≥ 2 ^ (w - 1) then (r : Int) - m else r

/-- The value and type of a plain character constant: one character other than a backslash
or a quote, of type `int` (STD §6.4.4.4#10). -/
def plainCharacterValue : CharacterConstant → Option Int
  | (none, .utf8 s) =>
    match s.toList with
    | [c] => if c.toNat < 128 && c != '\\' && c != '\'' then some c.toNat else none
    | _ => none
  | _ => none

/-- The native evaluation of an untyped Ail integer constant expression: its value and type. -/
def evalConstExpr : Expression Unit → DesugM (Int × ConstIntType)
  | .mk _ _ loc expr =>
    match expr with
    | .const (.integer (.iconstant n basis suffOpt)) =>
      match (integerConstantCandidates basis suffOpt).find? (·.represents n) with
      | some t => return (n, t)
      | none => notPorted loc "an integer constant that fits no integer type"
    | .const (.character c) =>
      match plainCharacterValue c with
      | some n => return (n, .int)
      | none => notPorted loc "the value of a character constant"
    -- an enumeration constant, of type int (STD §6.7.2.2#3)
    | .annot (.mk _ (.basic (.integer (.signed .int)))) e => do return ((← evalConstExpr e).1, .int)
    | .annot _ e | .printType e => evalConstExpr e
    | .unary .plus e => evalConstExpr e
    | .unary .minus e => do
      let (n, t) ← evalConstExpr e
      arithmeticResult loc t (-n)
    | .unary .bnot e => do
      let (n, t) ← evalConstExpr e
      return (bitwiseConst t .bxor n (-1), t)
    | .binary e₁ (.arithmetic op) e₂ => do
      let (n₁, t₁) ← evalConstExpr e₁
      let (n₂, t₂) ← evalConstExpr e₂
      match op with
      | .shl | .shr =>
        if n₂ < 0 || n₂ ≥ t₁.width then notPorted loc "an integer constant expression with an out-of-range shift"
        else if op == .shr then
          -- an arithmetic shift for a negative value (implementation-defined, STD §6.5.7#5)
          return (n₁.fdiv (2 ^ n₂.toNat : Nat), t₁)
        else if t₁.signed && n₁ < 0 then notPorted loc "an integer constant expression shifting a negative value"
        else arithmeticResult loc t₁ (n₁ * (2 ^ n₂.toNat : Nat))
      | _ =>
        let t := usualArithmeticConversion t₁ t₂
        let a ← convertConst loc t n₁
        let b ← convertConst loc t n₂
        match op with
        | .add => arithmeticResult loc t (a + b)
        | .sub => arithmeticResult loc t (a - b)
        | .mul => arithmeticResult loc t (a * b)
        | .div | .mod =>
          if b == 0 then notPorted loc "an integer constant expression dividing by zero"
          else arithmeticResult loc t (if op == .div then a.tdiv b else a.tmod b)
        | .band | .bor | .bxor => return (bitwiseConst t op a b, t)
        | .shl | .shr => notPorted loc "shift"
    | .binary e₁ op e₂ => do
      let (n₁, t₁) ← evalConstExpr e₁
      let (n₂, t₂) ← evalConstExpr e₂
      let t := usualArithmeticConversion t₁ t₂
      let a ← convertConst loc t n₁
      let b ← convertConst loc t n₂
      let truth (p : Bool) : DesugM (Int × ConstIntType) := return (if p then 1 else 0, .int)
      match op with
      | .lt => truth (a < b)
      | .gt => truth (a > b)
      | .le => truth (a ≤ b)
      | .ge => truth (a ≥ b)
      | .eq => truth (a == b)
      | .ne => truth (a != b)
      | .and => truth (n₁ != 0 && n₂ != 0)
      | .or => truth (n₁ != 0 || n₂ != 0)
      | _ => notPorted loc "the comma operator in an integer constant expression"
    | .cond e₁ (some e₂) e₃ => do
      let (n₁, _) ← evalConstExpr e₁
      let (n₂, t₂) ← evalConstExpr e₂
      let (n₃, t₃) ← evalConstExpr e₃
      let t := usualArithmeticConversion t₂ t₃
      return (← convertConst loc t (if n₁ != 0 then n₂ else n₃), t)
    | _ => notPorted loc "this integer constant expression (sizeof, _Alignof, offsetof, enumeration constants)"

/-- `evaluate_integer_constant_expression` (`cabs_to_ail.lem:1128`), natively; with a type,
the value must be representable in it (STD §6.6#4). -/
def evaluateIntegerConstantExpression (loc : Loc) (tyOpt : Option Ctype) (e : Expression Unit) : DesugM Int := do
  let (n, _) ← evalConstExpr e
  match tyOpt with
  | none => return n
  | some (.mk _ (.basic (.integer (.signed .int)))) =>
    if ConstIntType.int.represents n then return n
    -- the elaborated check of STD §6.6#4 fails
    else constraintViolation loc .integerConstantOutRange
  | some _ => notPorted loc "integer constant expressions of a given type"

end Silmaril.Cerberus.Frontend.Desugar
