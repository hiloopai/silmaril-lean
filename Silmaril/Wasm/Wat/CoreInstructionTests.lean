module

public import Silmaril.Wasm.Instructions
public meta import Silmaril.Wasm.Wat.CoreInstructions

/-! Exact instruction AST regressions, independent of stack validation. -/

open Silmaril.Wasm
local syntax "core_expr% " str : term
local syntax "core_types% " str : term
meta section
macro_rules
  | `(core_expr% $s:str) => Silmaril.Wasm.Wat.Core.expressionTerm s.getString
macro_rules
  | `(core_types% $s:str) => do
    let nodes ← match Silmaril.Wasm.Wat.parse s.getString with
      | .ok ns => pure ns | .error e => Lean.Macro.throwError e
    let ((body, _), tables) ← (Silmaril.Wasm.Wat.Core.instructions {} nodes).run {}
    let groups ← Silmaril.Wasm.Wat.listTerm (← tables.groups.mapM Silmaril.Wasm.Wat.Core.recTerm)
    let body ← Silmaril.Wasm.Wat.listTerm body
    `(Prod.mk ($groups : List Silmaril.Wasm.RecType) ($body : Silmaril.Wasm.Expr))
end

example : core_expr% "(i32.add (i32.const 1) (i32.const 2))" =
    [.intConst .i32 1, .intConst .i32 2, .intBinOp .i32 .add] := rfl

example : core_expr% "i64.load32_u 3 offset=4294967296 align=8" =
    [.intLoad .i64 (some (.i32, .unsigned)) ⟨3⟩ ⟨3, 4294967296⟩] := rfl

example : core_expr% "f32.store offset=18446744073709551615 align=9223372036854775808" =
    [.floatStore .f32 ⟨0⟩ ⟨63, 18446744073709551615⟩] := rfl

example : core_expr% "v128.load8_lane 7" =
    [.vecLoadLane .i8 ⟨0⟩ ⟨0, 0⟩ 7] := rfl

example : core_expr% "v128.store64_lane 2 offset=8 align=8 1" =
    [.vecStoreLane .i64 ⟨2⟩ ⟨3, 8⟩ 1] := rfl

example : core_expr% "v128.load16x4_u 2 v128.load64_splat v128.load32_zero" =
    [.vecLoad (.extend16x4 .unsigned) ⟨2⟩ ⟨3, 0⟩,
     .vecLoad (.splat .i64) ⟨0⟩ ⟨3, 0⟩, .vecLoad .zero32 ⟨0⟩ ⟨2, 0⟩] := rfl

example : core_expr% "memory.copy 2 3 memory.init 4 5 table.init 6 table.copy" =
    [.memoryCopy ⟨2⟩ ⟨3⟩, .memoryInit ⟨4⟩ ⟨5⟩, .tableInit ⟨0⟩ ⟨6⟩,
     .tableCopy ⟨0⟩ ⟨0⟩] := rfl

example : core_expr% "select (result i32 (ref null func)) ref.test (ref 1) ref.cast funcref" =
    [.select (some [.i32, .ref ⟨true, .abstract .func⟩]),
     .refTest ⟨false, .typeIdx ⟨1⟩⟩, .refCast ⟨true, .abstract .func⟩] := rfl

example : core_expr% "br_on_cast_fail 3 (ref null any) (ref 7)" =
    [.brOnCastFail ⟨3⟩ ⟨true, .abstract .any⟩ ⟨false, .typeIdx ⟨7⟩⟩] := rfl

example : core_expr% "struct.get_u 2 3 array.new_fixed 4 5 array.copy 6 7 array.init_elem 8 9" =
    [.structGet (some .unsigned) ⟨2⟩ ⟨3⟩, .arrayNewFixed ⟨4⟩ 5,
     .arrayCopy ⟨6⟩ ⟨7⟩, .arrayInitElem ⟨8⟩ ⟨9⟩] := rfl

example : (core_types% "call_ref 2 return_call 3 return_call_ref 4 return_call_indirect 5 (result i64)").2 =
    [.callRef ⟨2⟩, .returnCall ⟨3⟩, .returnCallRef ⟨4⟩, .returnCallIndirect ⟨5⟩ ⟨0⟩] := rfl

/-- Catch labels see the surrounding scope, while the body sees the try label. -/
example : core_expr% "block $out try_table $inner (catch 2 $out) (catch_ref 3 $out) (catch_all $out) (catch_all_ref $out) br $inner end end" =
    [.block .empty [.tryTable .empty
      [.catch_ ⟨2⟩ ⟨0⟩, .catchRef ⟨3⟩ ⟨0⟩, .catchAll ⟨0⟩, .catchAllRef ⟨0⟩]
      [.br ⟨0⟩]]] := rfl

example : core_expr% "(block $outer (try_table $inner (catch_all $outer) (br $inner)))" =
    [.block .empty [.tryTable .empty [.catchAll ⟨0⟩] [.br ⟨0⟩]]] := rfl

example : core_expr% "block $\"outer label\" block $inner br $\"outer label\" end end" =
    [.block .empty [.block .empty [.br ⟨1⟩]]] := rfl

example : core_expr% "v128.const i32x4 1 -1 0 0x80000000" =
    [.vecConst (BitVec.ofNat 128 (1 + 4294967295 * 2^32 + 2147483648 * 2^96))] := rfl

example : core_expr% "v128.const f32x4 -0 1 nan:0x1 -inf" =
    [.vecConst (BitVec.ofNat 128
      (2147483648 + 1065353216 * 2^32 + 2139095041 * 2^64 + 4286578688 * 2^96))] := rfl

example : core_expr% "i8x16.narrow_i16x8_s i64x2.extmul_high_i32x4_u i16x8.extadd_pairwise_i8x16_s" =
    [.vecNarrow .i16x8 .i8x16 .signed,
     .vecExtBinOp .i32x4 .i64x2 (.extmul .high .unsigned),
     .vecExtUnOp .i8x16 .i16x8 (.extaddPairwise .signed)] := rfl

example : core_expr% "f64x2.convert_low_i32x4_s i32x4.trunc_sat_f64x2_u_zero f32x4.demote_f64x2_zero" =
    [.vecConvert (.int .i32x4) (.float .f64x2) (.convert (some .low) .signed),
     .vecConvert (.float .f64x2) (.int .i32x4) (.truncSat .unsigned true),
     .vecConvert (.float .f64x2) (.float .f32x4) .demoteZero] := rfl

example : core_expr% "i32x4.relaxed_dot_i8x16_i7x16_add_s i16x8.relaxed_dot_i8x16_i7x16_s i64x2.relaxed_laneselect f32x4.relaxed_nmadd" =
    [.vecExtTernOp .i8x16 .i32x4 .relaxedDotAddS,
     .vecExtBinOp .i8x16 .i16x8 .relaxedDotS,
     .vecIntTernOp .i64x2 .relaxedLaneSelect, .vecFloatTernOp .f32x4 .relaxedNmadd] := rfl

example : core_expr% "i8x16.shuffle 0 1 2 3 4 5 6 7 24 25 26 27 28 29 30 31" =
    [.vecShuffle [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31]] := rfl

example : core_types% "(return_call_indirect 3 (result i64) (call_indirect 4 (result i32)))" =
    ([⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], [.i64]⟩⟩]⟩],
     [.callIndirect ⟨4⟩ ⟨0⟩, .returnCallIndirect ⟨3⟩ ⟨1⟩]) := rfl

/-- error: WAT at character 0: unsupported Core3 instruction 'i64x2.lt_u' -/
#guard_msgs in
example : Expr := core_expr% "i64x2.lt_u"

/-- error: WAT at character 19: SIMD lane index exceeds unsigned byte range -/
#guard_msgs in
example : Expr := core_expr% "i8x16.replace_lane 256"

/-- error: WAT at character 9: memory offset exceeds unsigned 64-bit range -/
#guard_msgs in
example : Expr := core_expr% "i32.load offset=18446744073709551616"

/-- error: WAT at character 9: alignment must be a nonzero power of two in unsigned 64-bit range -/
#guard_msgs in
example : Expr := core_expr% "i32.load align=3"

/-- error: WAT at character 28: unknown label identifier $inner -/
#guard_msgs in
example : Expr := core_expr% "try_table $inner (catch_all $inner) end"

/-- error: WAT at character 0: indirect call parameters must be anonymous -/
#guard_msgs in
example : Expr := core_expr% "return_call_indirect (param $x i32)"

/-- error: WAT expression requires implicit function types; use wat3! with a module context -/
#guard_msgs in
example : Expr := core_expr% "call_indirect (result i32)"
