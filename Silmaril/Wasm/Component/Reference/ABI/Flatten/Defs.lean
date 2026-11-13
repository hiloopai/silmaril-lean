module

public import Silmaril.Wasm.Component.Reference.WIT.Defs
public import Mathlib.Data.List.Basic

/-! # Canonical ABI scalar flattening -/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

universe u

/-- Canonical flattened values use exactly the four scalar core types. -/
abbrev CoreType := NumType

def pointerType : AddrType → CoreType
  | .i32 => .int .i32 | .i64 => .int .i64

def flattenPrimitive (p : AddrType) : WIT.Primitive → List CoreType
  | .bool | .u8 | .s8 | .u16 | .s16 | .u32 | .s32 | .char => [.int .i32]
  | .u64 | .s64 => [.int .i64]
  | .f32 => [.float .f32]
  | .f64 => [.float .f64]
  | .string => [pointerType p, pointerType p]

/-- Bit-preserving common carrier for alternative variant payloads. This is a
representation join, not an arithmetic numeric conversion. -/
def joinType : CoreType → CoreType → CoreType
  | .int .i32, .int .i32 | .int .i32, .float .f32 | .float .f32, .int .i32 => .int .i32
  | .float .f32, .float .f32 => .float .f32
  | .float .f64, .float .f64 => .float .f64
  | _, _ => .int .i64

@[simp] theorem joinType_self (a : CoreType) : joinType a a = a := by
  rcases a with (a | a) <;> cases a <;> rfl

def joinFlat : List CoreType → List CoreType → List CoreType
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => joinType x y :: joinFlat xs ys

@[simp] theorem joinFlat_nil_left (xs : List CoreType) : joinFlat [] xs = xs := rfl
@[simp] theorem joinFlat_nil_right (xs : List CoreType) : joinFlat xs [] = xs := by cases xs <;> rfl

@[simp] theorem joinFlat_self (xs : List CoreType) : joinFlat xs xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [joinFlat, joinType_self, ih]

def variantPayload : List (List CoreType) → List CoreType
  | [] => []
  | payload :: cases => joinFlat payload (variantPayload cases)

variable {Resource : Type u}

mutual
  def flatten (p : AddrType) : WIT.ClosedType Resource → List CoreType
    | .prim t => flattenPrimitive p t
    | .ref name => nomatch name
    | .list _ | .map _ _ => [pointerType p, pointerType p]
    | .fixedList t n => (List.replicate n (flatten p t)).flatten
    | .record fields => flattenFields p fields
    | .tuple fields => flattenTypes p fields
    | .variant cases => .int .i32 :: variantPayload (flattenCases p cases)
    | .enum _ | .flags _ => [.int .i32]
    | .option t => .int .i32 :: flatten p t
    | .result ok error => .int .i32 :: joinFlat (flattenOption p ok) (flattenOption p error)
    | .own _ | .borrow _ | .future _ | .stream _ | .errorContext => [.int .i32]
  termination_by t => sizeOf t

  def flattenFields (p : AddrType) : List (String × WIT.ClosedType Resource) → List CoreType
    | [] => []
    | (_, t) :: fields => flatten p t ++ flattenFields p fields
  termination_by fields => sizeOf fields

  def flattenTypes (p : AddrType) : List (WIT.ClosedType Resource) → List CoreType
    | [] => []
    | t :: fields => flatten p t ++ flattenTypes p fields
  termination_by fields => sizeOf fields

  def flattenCases (p : AddrType) : List (String × Option (WIT.ClosedType Resource)) → List (List CoreType)
    | [] => []
    | (_, t) :: cases => flattenOption p t :: flattenCases p cases
  termination_by cases => sizeOf cases

  def flattenOption (p : AddrType) : Option (WIT.ClosedType Resource) → List CoreType
    | none => []
    | some t => flatten p t
  termination_by t => sizeOf t
end

end Silmaril.Wasm.Component.ABI
