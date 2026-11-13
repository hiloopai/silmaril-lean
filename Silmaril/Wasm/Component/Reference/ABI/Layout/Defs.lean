module

public import Silmaril.Wasm.Component.Reference.WIT.Defs
public import Mathlib.Data.Nat.Basic

/-!
# Canonical ABI memory layout

Alignment and element size for resolved value types, with explicit memory32 or
memory64 pointers. Layouts describe one value's representation: the payloads of
dynamic lists and strings live elsewhere. Invalid raw shapes have total layout
operations, but no conformance claim; use WIT well-formedness separately.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

universe u

inductive Alignment where
  | one | two | four | eight
  deriving Repr, DecidableEq

def Alignment.bytes : Alignment → Nat
  | .one => 1 | .two => 2 | .four => 4 | .eight => 8

def Alignment.join : Alignment → Alignment → Alignment
  | .eight, _ | _, .eight => .eight
  | .four, _ | _, .four => .four
  | .two, _ | _, .two => .two
  | .one, .one => .one

@[simp] theorem Alignment.bytes_pos (a : Alignment) : 0 < a.bytes := by cases a <;> decide

@[simp] theorem Alignment.join_bytes (a b : Alignment) : (a.join b).bytes = max a.bytes b.bytes := by
  cases a <;> cases b <;> rfl

/-- Integer rounding avoids the floating-point division in the executable
Python design reference, including for addresses beyond exact IEEE integers. -/
def alignTo (n : Nat) (a : Alignment) : Nat := (n + a.bytes - 1) / a.bytes * a.bytes

/-- A layout records aligned units, making its element size a multiple of its
alignment by construction. It may have size zero on invalid raw input. -/
structure Layout where
  alignment : Alignment
  units : Nat
  deriving Repr, DecidableEq

def Layout.size (l : Layout) : Nat := l.units * l.alignment.bytes

def Layout.rounded (a : Alignment) (size : Nat) : Layout :=
  ⟨a, (size + a.bytes - 1) / a.bytes⟩

@[simp] theorem Layout.size_rounded (a : Alignment) (n : Nat) : (Layout.rounded a n).size = alignTo n a := rfl

def pointerAlignment : AddrType → Alignment
  | .i32 => .four | .i64 => .eight

def pointerLayout (p : AddrType) : Layout := ⟨pointerAlignment p, 2⟩

def primitiveLayout (p : AddrType) : WIT.Primitive → Layout
  | .bool | .s8 | .u8 => ⟨.one, 1⟩
  | .s16 | .u16 => ⟨.two, 1⟩
  | .s32 | .u32 | .f32 | .char => ⟨.four, 1⟩
  | .s64 | .u64 | .f64 => ⟨.eight, 1⟩
  | .string => pointerLayout p

/-- The smallest discriminant for a nonempty, fewer-than-2^32 case sequence. -/
def discriminantAlignment (cases : Nat) : Alignment :=
  if cases ≤ 256 then .one else if cases ≤ 65536 then .two else .four

def flagsAlignment (count : Nat) : Alignment :=
  if count ≤ 8 then .one else if count ≤ 16 then .two else .four

/-- Offset and next cursor for one field. The end cursor excludes tail padding. -/
def placeField (cursor : Nat) (field : Layout) : Nat × Nat :=
  let offset := alignTo cursor field.alignment
  (offset, offset + field.size)

def recordAlignment : List Layout → Alignment
  | [] => .one
  | field :: fields => field.alignment.join (recordAlignment fields)

def recordEnd (cursor : Nat) : List Layout → Nat
  | [] => cursor
  | field :: fields => recordEnd (placeField cursor field).2 fields

def fieldOffsets (cursor : Nat) : List Layout → List Nat
  | [] => []
  | field :: fields => (placeField cursor field).1 :: fieldOffsets (placeField cursor field).2 fields

def recordLayout (fields : List Layout) : Layout :=
  Layout.rounded (recordAlignment fields) (recordEnd 0 fields)

@[simp] theorem fieldOffsets_length (cursor : Nat) (fields : List Layout) :
    (fieldOffsets cursor fields).length = fields.length := by
  induction fields generalizing cursor with
  | nil => rfl
  | cons f fs ih => simp only [fieldOffsets, List.length_cons, ih]

def maxCaseAlignment : List (Option Layout) → Alignment
  | [] => .one
  | none :: cases => maxCaseAlignment cases
  | some l :: cases => l.alignment.join (maxCaseAlignment cases)

def maxCaseSize : List (Option Layout) → Nat
  | [] => 0
  | none :: cases => maxCaseSize cases
  | some l :: cases => max l.size (maxCaseSize cases)

def variantLayout (cases : List (Option Layout)) : Layout :=
  let tag := discriminantAlignment cases.length
  let payload := maxCaseAlignment cases
  Layout.rounded (tag.join payload) (alignTo tag.bytes payload + maxCaseSize cases)

variable {Resource : Type u}

mutual
  def layout (p : AddrType) : WIT.ClosedType Resource → Layout
    | .prim t => primitiveLayout p t
    | .ref name => nomatch name
    | .list _ | .map _ _ => pointerLayout p
    | .fixedList t n => let l := layout p t; ⟨l.alignment, n * l.units⟩
    | .record fields => recordLayout (layoutFields p fields)
    | .tuple fields => recordLayout (layoutTypes p fields)
    | .variant cases => variantLayout (layoutCases p cases)
    | .enum cases => ⟨discriminantAlignment cases.length, 1⟩
    | .flags labels => ⟨flagsAlignment labels.length, 1⟩
    | .option t => variantLayout [none, some (layout p t)]
    | .result ok error => variantLayout [layoutOption p ok, layoutOption p error]
    | .own _ | .borrow _ | .future _ | .stream _ | .errorContext => ⟨.four, 1⟩
  termination_by t => sizeOf t

  def layoutFields (p : AddrType) : List (String × WIT.ClosedType Resource) → List Layout
    | [] => []
    | (_, t) :: fields => layout p t :: layoutFields p fields
  termination_by fields => sizeOf fields

  def layoutTypes (p : AddrType) : List (WIT.ClosedType Resource) → List Layout
    | [] => []
    | t :: fields => layout p t :: layoutTypes p fields
  termination_by fields => sizeOf fields

  def layoutCases (p : AddrType) : List (String × Option (WIT.ClosedType Resource)) → List (Option Layout)
    | [] => []
    | (_, t) :: cases => layoutOption p t :: layoutCases p cases
  termination_by cases => sizeOf cases

  def layoutOption (p : AddrType) : Option (WIT.ClosedType Resource) → Option Layout
    | none => none
    | some t => some (layout p t)
  termination_by t => sizeOf t
end

end Silmaril.Wasm.Component.ABI
