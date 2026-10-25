module

public import Silmaril.Wasm.Ops

/-!
# WebAssembly 1.0 source types and scalar operators

The source language follows the fixed W3C Recommendation of 5 December 2019.
Only the four scalar value types occur. Result arities and limit bounds are
validation conditions; the raw function type therefore retains a result list.
Mutable globals are part of this version, including imported and exported ones.

See https://www.w3.org/TR/2019/REC-wasm-core-1-20191205/.
-/

@[expose] public section

namespace Silmaril.Wasm.V1

abbrev ValType := NumType
abbrev ResultType := List ValType
abbrev BlockType := Option ValType

namespace ValType

def i32 : ValType := .int .i32
def i64 : ValType := .int .i64
def f32 : ValType := .float .f32
def f64 : ValType := .float .f64

end ValType

/-- Both bounds in the original grammar are unsigned 32-bit integers. -/
structure Limits where
  min : Fin (2 ^ 32)
  max : Option (Fin (2 ^ 32))
  deriving DecidableEq, Repr

structure FuncType where
  params : ResultType
  results : ResultType
  deriving DecidableEq, Repr

/-- A 1.0 table contains nullable function addresses; there is no choice of element type. -/
structure TableType where
  limits : Limits
  deriving DecidableEq, Repr

/-- A 1.0 memory uses 32-bit addresses and 64 KiB pages. -/
structure MemoryType where
  limits : Limits
  deriving DecidableEq, Repr

structure GlobalType where
  mutability : Mutability
  value : ValType
  deriving DecidableEq, Repr

/-- Resolved external types, as used by validation and instantiation. -/
inductive ExternType where
  | func (type : FuncType)
  | table (type : TableType)
  | memory (type : MemoryType)
  | global (type : GlobalType)
  deriving DecidableEq, Repr

/-- The original unary integer operators exclude later sign-extension instructions. -/
inductive IntUnOp where
  | clz | ctz | popcnt
  deriving DecidableEq, Repr

/-- Original scalar conversions; saturating float-to-integer conversions are absent. -/
inductive ConvertOp where
  | wrap
  | extend (sign : Signedness)
  | trunc (source : FloatType) (target : IntType) (sign : Signedness)
  | convert (source : IntType) (target : FloatType) (sign : Signedness)
  | demote | promote
  | reinterpretInt (source : FloatType)
  | reinterpretFloat (source : IntType)
  deriving DecidableEq, Repr

/-- Packed scalar memory accesses never have a 64-bit packed width. -/
inductive PackSize where
  | i8 | i16 | i32
  deriving DecidableEq, Repr

def PackSize.width : PackSize → Nat
  | .i8 => 8
  | .i16 => 16
  | .i32 => 32

/-- The alignment is an exponent; the offset is an unsigned 32-bit immediate. -/
structure MemArg where
  align : Fin (2 ^ 32)
  offset : Fin (2 ^ 32)
  deriving DecidableEq, Repr

end Silmaril.Wasm.V1
