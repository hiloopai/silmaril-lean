module

public import Silmaril.Wasm.Instructions
public import Mathlib.Logic.Equiv.List

/-!
# Injective numeric codes of Core 3.0 immediates

`Code α`: an injective map `α → Nat`. The universal syntax stores operator fields and
immediates of silmaril's Core 3.0 instructions as such codes (`Silmaril.Wasm.Unified.Core30`).
Injectivity is what makes the encoding of instructions decodable.

Instances: `Nat`, `Bool`, `Fin n`, the index spaces `Idx k`, `Option`, `List`, products, and
the types of silmaril's instruction fields (number, vector, heap, reference, value and block
types, memory arguments, signedness, pack sizes, and every operator type). A constructor with
fields is coded as `tag k [codes of the fields]` (`Nat.pair` of the constructor number and the
`Encodable` code of the list).

(Mathlib's `deriving Encodable` handler does not run inside the module system here: its
auxiliary declarations are private. These instances are written by hand.)
-/

@[expose] public section

namespace Silmaril.Wasm.Unified

/-- An injective numeric code. -/
class Code (α : Type) where
  /-- The code. -/
  code : α → Nat
  /-- Codes are injective. -/
  inj : Function.Injective code

export Code (code)

@[simp] theorem Code.code_eq_iff {α : Type} [Code α] {a b : α} : code a = code b ↔ a = b :=
  Code.inj.eq_iff

/-- A constructor number with the codes of its fields. -/
def tag (k : Nat) (xs : List Nat) : Nat := Nat.pair k (Encodable.encode xs)

@[simp] theorem tag_inj {k k' : Nat} {xs xs' : List Nat} :
    tag k xs = tag k' xs' ↔ k = k' ∧ xs = xs' := by
  unfold tag
  rw [Nat.pair_eq_pair, Encodable.encode_inj]

/-- Injectivity of a hand-written code: case on both sides and compare tags. -/
macro "code_inj" : tactic =>
  `(tactic| (intro a b h; cases a <;> cases b <;> simp_all [tag_inj]))

instance : Code Nat := ⟨id, fun _ _ h => h⟩

instance : Code Bool := ⟨fun b => if b then 1 else 0, by code_inj⟩

instance (n : Nat) : Code (Fin n) := ⟨Fin.val, Fin.val_injective⟩

instance {α : Type} [Code α] : Code (Option α) :=
  ⟨fun | none => tag 0 [] | some a => tag 1 [code a], by code_inj⟩

instance {α : Type} [Code α] : Code (List α) :=
  ⟨fun l => Encodable.encode (l.map code), fun a b h => by
    simpa using List.map_injective_iff.2 Code.inj (Encodable.encode_injective h)⟩

instance {α β : Type} [Code α] [Code β] : Code (α × β) :=
  ⟨fun x => tag 0 [code x.1, code x.2], by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp_all [tag_inj]⟩

open Silmaril.Wasm

instance (k : IndexKind) : Code (Idx k) :=
  ⟨fun i => i.value.val, fun a b h => by
    cases a; cases b; simp_all [Fin.val_inj]⟩

instance : Code IntType := ⟨fun | .i32 => 0 | .i64 => 1, by code_inj⟩
instance : Code FloatType := ⟨fun | .f32 => 0 | .f64 => 1, by code_inj⟩
instance : Code NumType := ⟨fun | .int t => tag 0 [code t] | .float t => tag 1 [code t], by code_inj⟩
instance : Code VecType := ⟨fun | .v128 => 0, by code_inj⟩

instance : Code AbsHeapType :=
  ⟨fun | .any => 0 | .eq => 1 | .i31 => 2 | .struct => 3 | .array => 4 | .none => 5
       | .func => 6 | .nofunc => 7 | .exn => 8 | .noexn => 9 | .extern => 10 | .noextern => 11,
   by code_inj⟩

instance : Code HeapType :=
  ⟨fun | .abstract t => tag 0 [code t] | .typeIdx i => tag 1 [code i], by code_inj⟩

instance : Code RefType :=
  ⟨fun r => tag 0 [code r.nullable, code r.heap], by
    rintro ⟨n, h⟩ ⟨n', h'⟩ e
    simp_all [tag_inj]⟩

instance : Code ValType :=
  ⟨fun | .num t => tag 0 [code t] | .vec t => tag 1 [code t] | .ref t => tag 2 [code t],
   by code_inj⟩

instance : Code BlockType :=
  ⟨fun | .empty => tag 0 [] | .value t => tag 1 [code t] | .typeIdx i => tag 2 [code i],
   by code_inj⟩

instance : Code MemArg :=
  ⟨fun m => tag 0 [code m.align, code m.offset], by
    rintro ⟨a, o⟩ ⟨a', o'⟩ e
    simp_all [tag_inj]⟩

instance : Code Signedness := ⟨fun | .signed => 0 | .unsigned => 1, by code_inj⟩
instance : Code PackSize := ⟨fun | .i8 => 0 | .i16 => 1 | .i32 => 2 | .i64 => 3, by code_inj⟩
instance : Code Half := ⟨fun | .low => 0 | .high => 1, by code_inj⟩

instance : Code IntUnOp :=
  ⟨fun | .clz => tag 0 [] | .ctz => tag 1 [] | .popcnt => tag 2 [] | .extend k => tag 3 [code k],
   by code_inj⟩

instance : Code IntBinOp :=
  ⟨fun | .add => tag 0 [] | .sub => tag 1 [] | .mul => tag 2 [] | .div s => tag 3 [code s]
       | .rem s => tag 4 [code s] | .and => tag 5 [] | .or => tag 6 [] | .xor => tag 7 []
       | .shl => tag 8 [] | .shr s => tag 9 [code s] | .rotl => tag 10 [] | .rotr => tag 11 [],
   by code_inj⟩

instance : Code IntTestOp := ⟨fun | .eqz => 0, by code_inj⟩

instance : Code IntRelOp :=
  ⟨fun | .eq => tag 0 [] | .ne => tag 1 [] | .lt s => tag 2 [code s] | .gt s => tag 3 [code s]
       | .le s => tag 4 [code s] | .ge s => tag 5 [code s],
   by code_inj⟩

instance : Code FloatUnOp :=
  ⟨fun | .abs => 0 | .neg => 1 | .sqrt => 2 | .ceil => 3 | .floor => 4 | .trunc => 5
       | .nearest => 6,
   by code_inj⟩

instance : Code FloatBinOp :=
  ⟨fun | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .min => 4 | .max => 5
       | .copysign => 6,
   by code_inj⟩

instance : Code FloatRelOp :=
  ⟨fun | .eq => 0 | .ne => 1 | .lt => 2 | .gt => 3 | .le => 4 | .ge => 5, by code_inj⟩

instance : Code ConvertOp :=
  ⟨fun | .wrap => tag 0 [] | .extend s => tag 1 [code s]
       | .trunc a b s => tag 2 [code a, code b, code s]
       | .truncSat a b s => tag 3 [code a, code b, code s]
       | .convert a b s => tag 4 [code a, code b, code s]
       | .demote => tag 5 [] | .promote => tag 6 []
       | .reinterpretInt a => tag 7 [code a] | .reinterpretFloat a => tag 8 [code a],
   by code_inj⟩

instance : Code IntShape := ⟨fun | .i8x16 => 0 | .i16x8 => 1 | .i32x4 => 2 | .i64x2 => 3, by code_inj⟩
instance : Code FloatShape := ⟨fun | .f32x4 => 0 | .f64x2 => 1, by code_inj⟩
instance : Code Shape := ⟨fun | .int s => tag 0 [code s] | .float s => tag 1 [code s], by code_inj⟩

instance : Code VecUnOp := ⟨fun | .not => 0, by code_inj⟩
instance : Code VecBinOp := ⟨fun | .and => 0 | .andnot => 1 | .or => 2 | .xor => 3, by code_inj⟩
instance : Code VecTernOp := ⟨fun | .bitselect => 0, by code_inj⟩
instance : Code VecTestOp := ⟨fun | .anyTrue => 0, by code_inj⟩
instance : Code VecIntUnOp := ⟨fun | .abs => 0 | .neg => 1 | .popcnt => 2, by code_inj⟩

instance : Code VecIntBinOp :=
  ⟨fun | .add => tag 0 [] | .sub => tag 1 [] | .mul => tag 2 [] | .addSat s => tag 3 [code s]
       | .subSat s => tag 4 [code s] | .avgrU => tag 5 [] | .q15mulrSatS => tag 6 []
       | .relaxedQ15mulrS => tag 7 [] | .min s => tag 8 [code s] | .max s => tag 9 [code s],
   by code_inj⟩

instance : Code VecFloatBinOp :=
  ⟨fun | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .min => 4 | .max => 5 | .pmin => 6
       | .pmax => 7 | .relaxedMin => 8 | .relaxedMax => 9,
   by code_inj⟩

instance : Code VecIntTernOp := ⟨fun | .relaxedLaneSelect => 0, by code_inj⟩
instance : Code VecFloatTernOp := ⟨fun | .relaxedMadd => 0 | .relaxedNmadd => 1, by code_inj⟩

instance : Code VecShiftOp := ⟨fun | .shl => tag 0 [] | .shr s => tag 1 [code s], by code_inj⟩
instance : Code VecSwizzleOp := ⟨fun | .swizzle => 0 | .relaxedSwizzle => 1, by code_inj⟩
instance : Code VecExtUnOp := ⟨fun | .extaddPairwise s => tag 0 [code s], by code_inj⟩

instance : Code VecExtBinOp :=
  ⟨fun | .extmul h s => tag 0 [code h, code s] | .dotS => tag 1 [] | .relaxedDotS => tag 2 [],
   by code_inj⟩

instance : Code VecExtTernOp := ⟨fun | .relaxedDotAddS => 0, by code_inj⟩

instance : Code VecConvertOp :=
  ⟨fun | .extend h s => tag 0 [code h, code s] | .convert h s => tag 1 [code h, code s]
       | .truncSat s z => tag 2 [code s, code z] | .relaxedTrunc s z => tag 3 [code s, code z]
       | .demoteZero => tag 4 [] | .promoteLow => tag 5 [],
   by code_inj⟩

instance : Code VecLoadOp :=
  ⟨fun | .full => tag 0 [] | .extend8x8 s => tag 1 [code s] | .extend16x4 s => tag 2 [code s]
       | .extend32x2 s => tag 3 [code s] | .splat k => tag 4 [code k] | .zero32 => tag 5 []
       | .zero64 => tag 6 [],
   by code_inj⟩

end Silmaril.Wasm.Unified
