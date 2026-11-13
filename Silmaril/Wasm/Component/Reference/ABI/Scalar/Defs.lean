module

public import Silmaril.Wasm.Component.Reference.ABI.Calling.Defs
public import Silmaril.Wasm.Execution.Runtime

/-!
# Canonical boolean and integer values

These direct adapters cover booleans and all eight WIT integer types. Narrow
unsigned values are zero-extended and signed values are sign-extended on
lowering; lifting keeps the low bits. Floating-point NaN choices, Unicode,
handles, and memory-backed values are separate extensions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

/-- Integer and boolean canonical values. Signed values use their two's-complement
bit representation; `BitVec.toInt` gives their mathematical signed value. -/
inductive Scalar where
  | bool | u8 | u16 | u32 | u64 | s8 | s16 | s32 | s64
  deriving Repr, DecidableEq

def Scalar.width : Scalar → Nat
  | .bool => 1
  | .u8 | .s8 => 8
  | .u16 | .s16 => 16
  | .u32 | .s32 => 32
  | .u64 | .s64 => 64

def Scalar.signed : Scalar → Bool
  | .s8 | .s16 | .s32 | .s64 => true
  | _ => false

def Scalar.primitive : Scalar → WIT.Primitive
  | .bool => .bool | .u8 => .u8 | .u16 => .u16 | .u32 => .u32 | .u64 => .u64
  | .s8 => .s8 | .s16 => .s16 | .s32 => .s32 | .s64 => .s64

def Scalar.coreType : Scalar → IntType
  | .u64 | .s64 => .i64
  | _ => .i32

structure ScalarValue where
  type : Scalar
  bits : BitVec type.width
  deriving Repr

def ScalarValue.toInt (v : ScalarValue) : Int :=
  if v.type.signed then v.bits.toInt else v.bits.toNat

def ScalarValue.lower (v : ScalarValue) : Execution.Runtime.Value :=
  .int v.type.coreType
    (if v.type.signed then v.bits.signExtend v.type.coreType.width
     else v.bits.setWidth v.type.coreType.width)

/-- Booleans accept every nonzero core integer. Narrow integers keep their low
bits, including when the incoming core value was not canonically extended. -/
def Scalar.liftBits (t : Scalar) {w : Nat} (x : BitVec w) : BitVec t.width :=
  if t = .bool then BitVec.ofNat t.width (if x = 0 then 0 else 1)
  else x.setWidth t.width

def Scalar.lift (t : Scalar) (v : Execution.Runtime.Value) : Option ScalarValue :=
  match t.coreType, v with
  | .i32, ⟨.int .i32, x⟩ => some ⟨t, t.liftBits x⟩
  | .i64, ⟨.int .i64, x⟩ => some ⟨t, t.liftBits x⟩
  | _, _ => none

@[simp] theorem ScalarValue.lower_type (v : ScalarValue) :
    v.lower.type = .int v.type.coreType := rfl

def lowerValues (vs : List ScalarValue) : List Execution.Runtime.Value := vs.map ScalarValue.lower

/-- Lifting checks both arity and core scalar tags. -/
def liftValues : List Scalar → List Execution.Runtime.Value → Option (List ScalarValue)
  | [], [] => some []
  | t :: ts, v :: vs => do
      let w ← t.lift v
      let ws ← liftValues ts vs
      return w :: ws
  | _, _ => none

def Scalar.wit (t : Scalar) : WIT.ClosedType Empty := .prim t.primitive

@[simp] theorem Scalar.flatten_wit (p : AddrType) (t : Scalar) :
    flatten p t.wit = [.int t.coreType] := by
  cases t <;> simp only [Scalar.wit, flatten, Scalar.primitive, flattenPrimitive, Scalar.coreType]

/-- The direct subset has at most sixteen scalar inputs and one scalar result. -/
structure DirectSignature where
  params : List Scalar
  result : Option Scalar
  paramsBound : params.length ≤ 16
  deriving Repr

def DirectSignature.abi (f : DirectSignature) : FuncType Empty :=
  ⟨f.params.map Scalar.wit, f.result.toList.map Scalar.wit⟩

def DirectSignature.core (f : DirectSignature) : V1.FuncType :=
  ⟨f.params.map (fun t => .int t.coreType), f.result.toList.map (fun t => .int t.coreType)⟩

end Silmaril.Wasm.Component.ABI
