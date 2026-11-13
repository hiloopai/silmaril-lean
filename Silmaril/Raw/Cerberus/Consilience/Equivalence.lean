module

public import Silmaril.Cerberus.Consilience.Generated.Defs
public import Silmaril.Cerberus.Names.Defs
meta import Silmaril.Cerberus.Consilience.Reflect.Defs

/-! # Equivalence with pinned Lem→Lean syntax

Translations select the hand-port constructors through `Names`. The constructor
equations fix their intended meaning, and both inverse laws cover every value,
including all natural-number payloads. Constructor-order checks compare the
compiled declarations with the pinned Lem/backend inventory.
-/

@[expose] public section

namespace Silmaril.Cerberus.Consilience

open Generated.LemLean

/-- The hand-port shape obtained by resolving the Lem tags through `Names`. -/
def renamedConstructors (lem : String) (constructors : List (String × String × Nat)) :
    List (String × Nat) :=
  match Names.types.find? (·.cerberus == lem) with
  | some entry => constructors.map fun c => (entry.rename c.1, c.2.2)
  | none => []

/-- Translate the backend's `integerType.IntegerBaseType` through `Names`. -/
def integerBaseTypeToHand : integerType.IntegerBaseType → IntegerBaseType
  | .ichar => (names_constructor% "IntegerType.integerBaseType" "Ichar")
  | .short => (names_constructor% "IntegerType.integerBaseType" "Short")
  | .int_ => (names_constructor% "IntegerType.integerBaseType" "Int_")
  | .long => (names_constructor% "IntegerType.integerBaseType" "Long")
  | .longLong => (names_constructor% "IntegerType.integerBaseType" "LongLong")
  | .intN_t n => (names_constructor% "IntegerType.integerBaseType" "IntN_t") n
  | .int_leastN_t n => (names_constructor% "IntegerType.integerBaseType" "Int_leastN_t") n
  | .int_fastN_t n => (names_constructor% "IntegerType.integerBaseType" "Int_fastN_t") n
  | .intmax_t => (names_constructor% "IntegerType.integerBaseType" "Intmax_t")
  | .intptr_t => (names_constructor% "IntegerType.integerBaseType" "Intptr_t")

/-- Translate the hand port back to the backend's constructor names. -/
def integerBaseTypeFromHand : IntegerBaseType → integerType.IntegerBaseType
  | .ichar => .ichar
  | .short => .short
  | .int => .int_
  | .long => .long
  | .longLong => .longLong
  | .intN n => .intN_t n
  | .intLeastN n => .int_leastN_t n
  | .intFastN n => .int_fastN_t n
  | .intmax => .intmax_t
  | .intptr => .intptr_t

@[simp] theorem integerBaseType_Ichar :
    integerBaseTypeToHand (.ichar) = .ichar := rfl

@[simp] theorem integerBaseType_Short :
    integerBaseTypeToHand (.short) = .short := rfl

@[simp] theorem integerBaseType_Int_ :
    integerBaseTypeToHand (.int_) = .int := rfl

@[simp] theorem integerBaseType_Long :
    integerBaseTypeToHand (.long) = .long := rfl

@[simp] theorem integerBaseType_LongLong :
    integerBaseTypeToHand (.longLong) = .longLong := rfl

@[simp] theorem integerBaseType_IntN_t (n : Nat) :
    integerBaseTypeToHand (.intN_t n) = .intN n := rfl

@[simp] theorem integerBaseType_Int_leastN_t (n : Nat) :
    integerBaseTypeToHand (.int_leastN_t n) = .intLeastN n := rfl

@[simp] theorem integerBaseType_Int_fastN_t (n : Nat) :
    integerBaseTypeToHand (.int_fastN_t n) = .intFastN n := rfl

@[simp] theorem integerBaseType_Intmax_t :
    integerBaseTypeToHand (.intmax_t) = .intmax := rfl

@[simp] theorem integerBaseType_Intptr_t :
    integerBaseTypeToHand (.intptr_t) = .intptr := rfl

@[simp] theorem integerBaseType_left_inv (x : integerType.IntegerBaseType) :
    integerBaseTypeFromHand (integerBaseTypeToHand x) = x := by
  cases x <;> rfl

@[simp] theorem integerBaseType_right_inv (x : IntegerBaseType) :
    integerBaseTypeToHand (integerBaseTypeFromHand x) = x := by
  cases x <;> rfl

/-- Full equivalence of the pinned backend syntax with the hand port. -/
def integerBaseTypeEquiv : integerType.IntegerBaseType ≃ IntegerBaseType where
  toFun := integerBaseTypeToHand
  invFun := integerBaseTypeFromHand
  left_inv := integerBaseType_left_inv
  right_inv := integerBaseType_right_inv

/-- The pinned backend constructor inventory agrees with the compiled declaration. -/
theorem integerBaseType_generated_constructors :
    (consilience_constructors% integerType.IntegerBaseType) =
      integerType_IntegerBaseType_constructors.map (fun c => (c.2.1, c.2.2)) := by
  decide +kernel

/-- Lem tags renamed through `Names` agree with the hand-port declaration in order. -/
theorem integerBaseType_names_constructors :
    renamedConstructors "IntegerType.integerBaseType" integerType_IntegerBaseType_constructors =
      (consilience_constructors% IntegerBaseType) := by
  decide +kernel

/-- Translate the backend's `ctype.RealFloatingType` through `Names`. -/
def realFloatingTypeToHand : ctype.RealFloatingType → RealFloatingType
  | .float => (names_constructor% "Ctype.realFloatingType" "Float")
  | .double => (names_constructor% "Ctype.realFloatingType" "Double")
  | .longDouble => (names_constructor% "Ctype.realFloatingType" "LongDouble")

/-- Translate the hand port back to the backend's constructor names. -/
def realFloatingTypeFromHand : RealFloatingType → ctype.RealFloatingType
  | .float => .float
  | .double => .double
  | .longDouble => .longDouble

@[simp] theorem realFloatingType_Float :
    realFloatingTypeToHand (.float) = .float := rfl

@[simp] theorem realFloatingType_Double :
    realFloatingTypeToHand (.double) = .double := rfl

@[simp] theorem realFloatingType_LongDouble :
    realFloatingTypeToHand (.longDouble) = .longDouble := rfl

@[simp] theorem realFloatingType_left_inv (x : ctype.RealFloatingType) :
    realFloatingTypeFromHand (realFloatingTypeToHand x) = x := by
  cases x <;> rfl

@[simp] theorem realFloatingType_right_inv (x : RealFloatingType) :
    realFloatingTypeToHand (realFloatingTypeFromHand x) = x := by
  cases x <;> rfl

/-- Full equivalence of the pinned backend syntax with the hand port. -/
def realFloatingTypeEquiv : ctype.RealFloatingType ≃ RealFloatingType where
  toFun := realFloatingTypeToHand
  invFun := realFloatingTypeFromHand
  left_inv := realFloatingType_left_inv
  right_inv := realFloatingType_right_inv

/-- The pinned backend constructor inventory agrees with the compiled declaration. -/
theorem realFloatingType_generated_constructors :
    (consilience_constructors% ctype.RealFloatingType) =
      ctype_RealFloatingType_constructors.map (fun c => (c.2.1, c.2.2)) := by
  decide +kernel

/-- Lem tags renamed through `Names` agree with the hand-port declaration in order. -/
theorem realFloatingType_names_constructors :
    renamedConstructors "Ctype.realFloatingType" ctype_RealFloatingType_constructors =
      (consilience_constructors% RealFloatingType) := by
  decide +kernel

/-- Translate the backend's `core.Binop` through `Names`. -/
def binOpToHand : core.Binop → Core.BinOp
  | .opAdd => (names_constructor% "Core.binop" "OpAdd")
  | .opSub => (names_constructor% "Core.binop" "OpSub")
  | .opMul => (names_constructor% "Core.binop" "OpMul")
  | .opDiv => (names_constructor% "Core.binop" "OpDiv")
  | .opRem_t => (names_constructor% "Core.binop" "OpRem_t")
  | .opRem_f => (names_constructor% "Core.binop" "OpRem_f")
  | .opExp => (names_constructor% "Core.binop" "OpExp")
  | .opEq => (names_constructor% "Core.binop" "OpEq")
  | .opGt => (names_constructor% "Core.binop" "OpGt")
  | .opLt => (names_constructor% "Core.binop" "OpLt")
  | .opGe => (names_constructor% "Core.binop" "OpGe")
  | .opLe => (names_constructor% "Core.binop" "OpLe")
  | .opAnd => (names_constructor% "Core.binop" "OpAnd")
  | .opOr => (names_constructor% "Core.binop" "OpOr")

/-- Translate the hand port back to the backend's constructor names. -/
def binOpFromHand : Core.BinOp → core.Binop
  | .add => .opAdd
  | .sub => .opSub
  | .mul => .opMul
  | .div => .opDiv
  | .remT => .opRem_t
  | .remF => .opRem_f
  | .exp => .opExp
  | .eq => .opEq
  | .gt => .opGt
  | .lt => .opLt
  | .ge => .opGe
  | .le => .opLe
  | .and => .opAnd
  | .or => .opOr

@[simp] theorem binOp_OpAdd :
    binOpToHand (.opAdd) = .add := rfl

@[simp] theorem binOp_OpSub :
    binOpToHand (.opSub) = .sub := rfl

@[simp] theorem binOp_OpMul :
    binOpToHand (.opMul) = .mul := rfl

@[simp] theorem binOp_OpDiv :
    binOpToHand (.opDiv) = .div := rfl

@[simp] theorem binOp_OpRem_t :
    binOpToHand (.opRem_t) = .remT := rfl

@[simp] theorem binOp_OpRem_f :
    binOpToHand (.opRem_f) = .remF := rfl

@[simp] theorem binOp_OpExp :
    binOpToHand (.opExp) = .exp := rfl

@[simp] theorem binOp_OpEq :
    binOpToHand (.opEq) = .eq := rfl

@[simp] theorem binOp_OpGt :
    binOpToHand (.opGt) = .gt := rfl

@[simp] theorem binOp_OpLt :
    binOpToHand (.opLt) = .lt := rfl

@[simp] theorem binOp_OpGe :
    binOpToHand (.opGe) = .ge := rfl

@[simp] theorem binOp_OpLe :
    binOpToHand (.opLe) = .le := rfl

@[simp] theorem binOp_OpAnd :
    binOpToHand (.opAnd) = .and := rfl

@[simp] theorem binOp_OpOr :
    binOpToHand (.opOr) = .or := rfl

@[simp] theorem binOp_left_inv (x : core.Binop) :
    binOpFromHand (binOpToHand x) = x := by
  cases x <;> rfl

@[simp] theorem binOp_right_inv (x : Core.BinOp) :
    binOpToHand (binOpFromHand x) = x := by
  cases x <;> rfl

/-- Full equivalence of the pinned backend syntax with the hand port. -/
def binOpEquiv : core.Binop ≃ Core.BinOp where
  toFun := binOpToHand
  invFun := binOpFromHand
  left_inv := binOp_left_inv
  right_inv := binOp_right_inv

/-- The pinned backend constructor inventory agrees with the compiled declaration. -/
theorem binOp_generated_constructors :
    (consilience_constructors% core.Binop) =
      core_Binop_constructors.map (fun c => (c.2.1, c.2.2)) := by
  decide +kernel

/-- Lem tags renamed through `Names` agree with the hand-port declaration in order. -/
theorem binOp_names_constructors :
    renamedConstructors "Core.binop" core_Binop_constructors =
      (consilience_constructors% Core.BinOp) := by
  decide +kernel

end Silmaril.Cerberus.Consilience
