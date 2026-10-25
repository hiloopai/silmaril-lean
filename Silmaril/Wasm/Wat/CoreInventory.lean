module

public meta import Silmaril.Wasm.Wat.CoreInstructions
public import Silmaril.Wasm.Instructions

/-! Exhaustive mnemonic fixtures from the pinned Core3 text instruction grammar.
These are syntax coverage checks, not stack-valid programs. Exact AST regression
checks live in CoreInstructionTests.lean. -/

open Silmaril.Wasm
local syntax "core_fixture% " str : term
meta section
macro_rules
  | `(core_fixture% $s:str) => do
    let nodes ← match Silmaril.Wasm.Wat.parse s.getString with
      | .ok ns => pure ns | .error e => Lean.Macro.throwError e
    let ((body, _), tables) ← (Silmaril.Wasm.Wat.Core.instructions {} nodes).run {}
    let groups ← Silmaril.Wasm.Wat.listTerm (← tables.groups.mapM Silmaril.Wasm.Wat.Core.recTerm)
    let body ← Silmaril.Wasm.Wat.listTerm body
    `(Prod.mk ($groups : List Silmaril.Wasm.RecType) ($body : Silmaril.Wasm.Expr))
end

example : (core_fixture% "unreachable").2.length = 1 := rfl
example : (core_fixture% "nop").2.length = 1 := rfl
example : (core_fixture% "drop").2.length = 1 := rfl
example : (core_fixture% "select").2.length = 1 := rfl
example : (core_fixture% "br 0").2.length = 1 := rfl
example : (core_fixture% "br_if 0").2.length = 1 := rfl
example : (core_fixture% "br_table  0 0").2.length = 1 := rfl
example : (core_fixture% "br_on_null 0").2.length = 1 := rfl
example : (core_fixture% "br_on_non_null 0").2.length = 1 := rfl
example : (core_fixture% "br_on_cast 0 (ref null func) (ref null func)").2.length = 1 := rfl
example : (core_fixture% "br_on_cast_fail 0 (ref null func) (ref null func)").2.length = 1 := rfl
example : (core_fixture% "call 0").2.length = 1 := rfl
example : (core_fixture% "call_ref 0").2.length = 1 := rfl
example : (core_fixture% "call_indirect 0 (param)").2.length = 1 := rfl
example : (core_fixture% "return").2.length = 1 := rfl
example : (core_fixture% "return_call 0").2.length = 1 := rfl
example : (core_fixture% "return_call_ref 0").2.length = 1 := rfl
example : (core_fixture% "return_call_indirect 0 (param)").2.length = 1 := rfl
example : (core_fixture% "throw 0").2.length = 1 := rfl
example : (core_fixture% "throw_ref").2.length = 1 := rfl
example : (core_fixture% "local.get 0").2.length = 1 := rfl
example : (core_fixture% "local.set 0").2.length = 1 := rfl
example : (core_fixture% "local.tee 0").2.length = 1 := rfl
example : (core_fixture% "global.get 0").2.length = 1 := rfl
example : (core_fixture% "global.set 0").2.length = 1 := rfl
example : (core_fixture% "table.get 0").2.length = 1 := rfl
example : (core_fixture% "table.set 0").2.length = 1 := rfl
example : (core_fixture% "table.size 0").2.length = 1 := rfl
example : (core_fixture% "table.grow 0").2.length = 1 := rfl
example : (core_fixture% "table.fill 0").2.length = 1 := rfl
example : (core_fixture% "table.copy 0 0").2.length = 1 := rfl
example : (core_fixture% "table.init 0 0").2.length = 1 := rfl
example : (core_fixture% "elem.drop 0").2.length = 1 := rfl
example : (core_fixture% "i32.load 0").2.length = 1 := rfl
example : (core_fixture% "i64.load 0").2.length = 1 := rfl
example : (core_fixture% "f32.load 0").2.length = 1 := rfl
example : (core_fixture% "f64.load 0").2.length = 1 := rfl
example : (core_fixture% "i32.load8_s 0").2.length = 1 := rfl
example : (core_fixture% "i32.load8_u 0").2.length = 1 := rfl
example : (core_fixture% "i32.load16_s 0").2.length = 1 := rfl
example : (core_fixture% "i32.load16_u 0").2.length = 1 := rfl
example : (core_fixture% "i64.load8_s 0").2.length = 1 := rfl
example : (core_fixture% "i64.load8_u 0").2.length = 1 := rfl
example : (core_fixture% "i64.load16_s 0").2.length = 1 := rfl
example : (core_fixture% "i64.load16_u 0").2.length = 1 := rfl
example : (core_fixture% "i64.load32_s 0").2.length = 1 := rfl
example : (core_fixture% "i64.load32_u 0").2.length = 1 := rfl
example : (core_fixture% "v128.load 0").2.length = 1 := rfl
example : (core_fixture% "v128.load8x8_s 0").2.length = 1 := rfl
example : (core_fixture% "v128.load8x8_u 0").2.length = 1 := rfl
example : (core_fixture% "v128.load16x4_s 0").2.length = 1 := rfl
example : (core_fixture% "v128.load16x4_u 0").2.length = 1 := rfl
example : (core_fixture% "v128.load32x2_s 0").2.length = 1 := rfl
example : (core_fixture% "v128.load32x2_u 0").2.length = 1 := rfl
example : (core_fixture% "v128.load8_splat 0").2.length = 1 := rfl
example : (core_fixture% "v128.load16_splat 0").2.length = 1 := rfl
example : (core_fixture% "v128.load32_splat 0").2.length = 1 := rfl
example : (core_fixture% "v128.load64_splat 0").2.length = 1 := rfl
example : (core_fixture% "v128.load32_zero 0").2.length = 1 := rfl
example : (core_fixture% "v128.load64_zero 0").2.length = 1 := rfl
example : (core_fixture% "v128.load8_lane 0  0").2.length = 1 := rfl
example : (core_fixture% "v128.load16_lane 0  0").2.length = 1 := rfl
example : (core_fixture% "v128.load32_lane 0  0").2.length = 1 := rfl
example : (core_fixture% "v128.load64_lane 0  0").2.length = 1 := rfl
example : (core_fixture% "i32.store 0").2.length = 1 := rfl
example : (core_fixture% "i64.store 0").2.length = 1 := rfl
example : (core_fixture% "f32.store 0").2.length = 1 := rfl
example : (core_fixture% "f64.store 0").2.length = 1 := rfl
example : (core_fixture% "i32.store8 0").2.length = 1 := rfl
example : (core_fixture% "i32.store16 0").2.length = 1 := rfl
example : (core_fixture% "i64.store8 0").2.length = 1 := rfl
example : (core_fixture% "i64.store16 0").2.length = 1 := rfl
example : (core_fixture% "i64.store32 0").2.length = 1 := rfl
example : (core_fixture% "v128.store 0").2.length = 1 := rfl
example : (core_fixture% "v128.store8_lane 0  0").2.length = 1 := rfl
example : (core_fixture% "v128.store16_lane 0  0").2.length = 1 := rfl
example : (core_fixture% "v128.store32_lane 0  0").2.length = 1 := rfl
example : (core_fixture% "v128.store64_lane 0  0").2.length = 1 := rfl
example : (core_fixture% "memory.size 0").2.length = 1 := rfl
example : (core_fixture% "memory.grow 0").2.length = 1 := rfl
example : (core_fixture% "memory.fill 0").2.length = 1 := rfl
example : (core_fixture% "memory.copy 0 0").2.length = 1 := rfl
example : (core_fixture% "memory.init 0 0").2.length = 1 := rfl
example : (core_fixture% "data.drop 0").2.length = 1 := rfl
example : (core_fixture% "ref.null func").2.length = 1 := rfl
example : (core_fixture% "ref.func 0").2.length = 1 := rfl
example : (core_fixture% "ref.is_null").2.length = 1 := rfl
example : (core_fixture% "ref.as_non_null").2.length = 1 := rfl
example : (core_fixture% "ref.eq").2.length = 1 := rfl
example : (core_fixture% "ref.test (ref null func)").2.length = 1 := rfl
example : (core_fixture% "ref.cast (ref null func)").2.length = 1 := rfl
example : (core_fixture% "ref.i31").2.length = 1 := rfl
example : (core_fixture% "i31.get_s").2.length = 1 := rfl
example : (core_fixture% "i31.get_u").2.length = 1 := rfl
example : (core_fixture% "struct.new 0").2.length = 1 := rfl
example : (core_fixture% "struct.new_default 0").2.length = 1 := rfl
example : (core_fixture% "struct.get 0 0").2.length = 1 := rfl
example : (core_fixture% "struct.get_s 0 0").2.length = 1 := rfl
example : (core_fixture% "struct.get_u 0 0").2.length = 1 := rfl
example : (core_fixture% "struct.set 0 0").2.length = 1 := rfl
example : (core_fixture% "array.new 0").2.length = 1 := rfl
example : (core_fixture% "array.new_default 0").2.length = 1 := rfl
example : (core_fixture% "array.new_fixed 0 0").2.length = 1 := rfl
example : (core_fixture% "array.new_data 0 0").2.length = 1 := rfl
example : (core_fixture% "array.new_elem 0 0").2.length = 1 := rfl
example : (core_fixture% "array.get 0").2.length = 1 := rfl
example : (core_fixture% "array.get_s 0").2.length = 1 := rfl
example : (core_fixture% "array.get_u 0").2.length = 1 := rfl
example : (core_fixture% "array.set 0").2.length = 1 := rfl
example : (core_fixture% "array.len").2.length = 1 := rfl
example : (core_fixture% "array.fill 0").2.length = 1 := rfl
example : (core_fixture% "array.copy 0 0").2.length = 1 := rfl
example : (core_fixture% "array.init_data 0 0").2.length = 1 := rfl
example : (core_fixture% "array.init_elem 0 0").2.length = 1 := rfl
example : (core_fixture% "any.convert_extern").2.length = 1 := rfl
example : (core_fixture% "extern.convert_any").2.length = 1 := rfl
example : (core_fixture% "i32.const 0").2.length = 1 := rfl
example : (core_fixture% "i64.const 0").2.length = 1 := rfl
example : (core_fixture% "f32.const 0").2.length = 1 := rfl
example : (core_fixture% "f64.const 0").2.length = 1 := rfl
example : (core_fixture% "i32.eqz").2.length = 1 := rfl
example : (core_fixture% "i64.eqz").2.length = 1 := rfl
example : (core_fixture% "i32.eq").2.length = 1 := rfl
example : (core_fixture% "i32.ne").2.length = 1 := rfl
example : (core_fixture% "i32.lt_s").2.length = 1 := rfl
example : (core_fixture% "i32.lt_u").2.length = 1 := rfl
example : (core_fixture% "i32.gt_s").2.length = 1 := rfl
example : (core_fixture% "i32.gt_u").2.length = 1 := rfl
example : (core_fixture% "i32.le_s").2.length = 1 := rfl
example : (core_fixture% "i32.le_u").2.length = 1 := rfl
example : (core_fixture% "i32.ge_s").2.length = 1 := rfl
example : (core_fixture% "i32.ge_u").2.length = 1 := rfl
example : (core_fixture% "i64.eq").2.length = 1 := rfl
example : (core_fixture% "i64.ne").2.length = 1 := rfl
example : (core_fixture% "i64.lt_s").2.length = 1 := rfl
example : (core_fixture% "i64.lt_u").2.length = 1 := rfl
example : (core_fixture% "i64.gt_s").2.length = 1 := rfl
example : (core_fixture% "i64.gt_u").2.length = 1 := rfl
example : (core_fixture% "i64.le_s").2.length = 1 := rfl
example : (core_fixture% "i64.le_u").2.length = 1 := rfl
example : (core_fixture% "i64.ge_s").2.length = 1 := rfl
example : (core_fixture% "i64.ge_u").2.length = 1 := rfl
example : (core_fixture% "f32.eq").2.length = 1 := rfl
example : (core_fixture% "f32.ne").2.length = 1 := rfl
example : (core_fixture% "f32.lt").2.length = 1 := rfl
example : (core_fixture% "f32.gt").2.length = 1 := rfl
example : (core_fixture% "f32.le").2.length = 1 := rfl
example : (core_fixture% "f32.ge").2.length = 1 := rfl
example : (core_fixture% "f64.eq").2.length = 1 := rfl
example : (core_fixture% "f64.ne").2.length = 1 := rfl
example : (core_fixture% "f64.lt").2.length = 1 := rfl
example : (core_fixture% "f64.gt").2.length = 1 := rfl
example : (core_fixture% "f64.le").2.length = 1 := rfl
example : (core_fixture% "f64.ge").2.length = 1 := rfl
example : (core_fixture% "i32.clz").2.length = 1 := rfl
example : (core_fixture% "i32.ctz").2.length = 1 := rfl
example : (core_fixture% "i32.popcnt").2.length = 1 := rfl
example : (core_fixture% "i32.extend8_s").2.length = 1 := rfl
example : (core_fixture% "i32.extend16_s").2.length = 1 := rfl
example : (core_fixture% "i64.clz").2.length = 1 := rfl
example : (core_fixture% "i64.ctz").2.length = 1 := rfl
example : (core_fixture% "i64.popcnt").2.length = 1 := rfl
example : (core_fixture% "i64.extend8_s").2.length = 1 := rfl
example : (core_fixture% "i64.extend16_s").2.length = 1 := rfl
example : (core_fixture% "i64.extend32_s").2.length = 1 := rfl
example : (core_fixture% "f32.abs").2.length = 1 := rfl
example : (core_fixture% "f32.neg").2.length = 1 := rfl
example : (core_fixture% "f32.sqrt").2.length = 1 := rfl
example : (core_fixture% "f32.ceil").2.length = 1 := rfl
example : (core_fixture% "f32.floor").2.length = 1 := rfl
example : (core_fixture% "f32.trunc").2.length = 1 := rfl
example : (core_fixture% "f32.nearest").2.length = 1 := rfl
example : (core_fixture% "f64.abs").2.length = 1 := rfl
example : (core_fixture% "f64.neg").2.length = 1 := rfl
example : (core_fixture% "f64.sqrt").2.length = 1 := rfl
example : (core_fixture% "f64.ceil").2.length = 1 := rfl
example : (core_fixture% "f64.floor").2.length = 1 := rfl
example : (core_fixture% "f64.trunc").2.length = 1 := rfl
example : (core_fixture% "f64.nearest").2.length = 1 := rfl
example : (core_fixture% "i32.add").2.length = 1 := rfl
example : (core_fixture% "i32.sub").2.length = 1 := rfl
example : (core_fixture% "i32.mul").2.length = 1 := rfl
example : (core_fixture% "i32.div_s").2.length = 1 := rfl
example : (core_fixture% "i32.div_u").2.length = 1 := rfl
example : (core_fixture% "i32.rem_s").2.length = 1 := rfl
example : (core_fixture% "i32.rem_u").2.length = 1 := rfl
example : (core_fixture% "i32.and").2.length = 1 := rfl
example : (core_fixture% "i32.or").2.length = 1 := rfl
example : (core_fixture% "i32.xor").2.length = 1 := rfl
example : (core_fixture% "i32.shl").2.length = 1 := rfl
example : (core_fixture% "i32.shr_s").2.length = 1 := rfl
example : (core_fixture% "i32.shr_u").2.length = 1 := rfl
example : (core_fixture% "i32.rotl").2.length = 1 := rfl
example : (core_fixture% "i32.rotr").2.length = 1 := rfl
example : (core_fixture% "i64.add").2.length = 1 := rfl
example : (core_fixture% "i64.sub").2.length = 1 := rfl
example : (core_fixture% "i64.mul").2.length = 1 := rfl
example : (core_fixture% "i64.div_s").2.length = 1 := rfl
example : (core_fixture% "i64.div_u").2.length = 1 := rfl
example : (core_fixture% "i64.rem_s").2.length = 1 := rfl
example : (core_fixture% "i64.rem_u").2.length = 1 := rfl
example : (core_fixture% "i64.and").2.length = 1 := rfl
example : (core_fixture% "i64.or").2.length = 1 := rfl
example : (core_fixture% "i64.xor").2.length = 1 := rfl
example : (core_fixture% "i64.shl").2.length = 1 := rfl
example : (core_fixture% "i64.shr_s").2.length = 1 := rfl
example : (core_fixture% "i64.shr_u").2.length = 1 := rfl
example : (core_fixture% "i64.rotl").2.length = 1 := rfl
example : (core_fixture% "i64.rotr").2.length = 1 := rfl
example : (core_fixture% "f32.add").2.length = 1 := rfl
example : (core_fixture% "f32.sub").2.length = 1 := rfl
example : (core_fixture% "f32.mul").2.length = 1 := rfl
example : (core_fixture% "f32.div").2.length = 1 := rfl
example : (core_fixture% "f32.min").2.length = 1 := rfl
example : (core_fixture% "f32.max").2.length = 1 := rfl
example : (core_fixture% "f32.copysign").2.length = 1 := rfl
example : (core_fixture% "f64.add").2.length = 1 := rfl
example : (core_fixture% "f64.sub").2.length = 1 := rfl
example : (core_fixture% "f64.mul").2.length = 1 := rfl
example : (core_fixture% "f64.div").2.length = 1 := rfl
example : (core_fixture% "f64.min").2.length = 1 := rfl
example : (core_fixture% "f64.max").2.length = 1 := rfl
example : (core_fixture% "f64.copysign").2.length = 1 := rfl
example : (core_fixture% "i32.wrap_i64").2.length = 1 := rfl
example : (core_fixture% "i32.trunc_f32_s").2.length = 1 := rfl
example : (core_fixture% "i32.trunc_f32_u").2.length = 1 := rfl
example : (core_fixture% "i32.trunc_f64_s").2.length = 1 := rfl
example : (core_fixture% "i32.trunc_f64_u").2.length = 1 := rfl
example : (core_fixture% "i32.trunc_sat_f32_s").2.length = 1 := rfl
example : (core_fixture% "i32.trunc_sat_f32_u").2.length = 1 := rfl
example : (core_fixture% "i32.trunc_sat_f64_s").2.length = 1 := rfl
example : (core_fixture% "i32.trunc_sat_f64_u").2.length = 1 := rfl
example : (core_fixture% "i64.extend_i32_s").2.length = 1 := rfl
example : (core_fixture% "i64.extend_i32_u").2.length = 1 := rfl
example : (core_fixture% "i64.trunc_f32_s").2.length = 1 := rfl
example : (core_fixture% "i64.trunc_f32_u").2.length = 1 := rfl
example : (core_fixture% "i64.trunc_f64_s").2.length = 1 := rfl
example : (core_fixture% "i64.trunc_f64_u").2.length = 1 := rfl
example : (core_fixture% "i64.trunc_sat_f32_s").2.length = 1 := rfl
example : (core_fixture% "i64.trunc_sat_f32_u").2.length = 1 := rfl
example : (core_fixture% "i64.trunc_sat_f64_s").2.length = 1 := rfl
example : (core_fixture% "i64.trunc_sat_f64_u").2.length = 1 := rfl
example : (core_fixture% "f32.demote_f64").2.length = 1 := rfl
example : (core_fixture% "f32.convert_i32_s").2.length = 1 := rfl
example : (core_fixture% "f32.convert_i32_u").2.length = 1 := rfl
example : (core_fixture% "f32.convert_i64_s").2.length = 1 := rfl
example : (core_fixture% "f32.convert_i64_u").2.length = 1 := rfl
example : (core_fixture% "f64.promote_f32").2.length = 1 := rfl
example : (core_fixture% "f64.convert_i32_s").2.length = 1 := rfl
example : (core_fixture% "f64.convert_i32_u").2.length = 1 := rfl
example : (core_fixture% "f64.convert_i64_s").2.length = 1 := rfl
example : (core_fixture% "f64.convert_i64_u").2.length = 1 := rfl
example : (core_fixture% "i32.reinterpret_f32").2.length = 1 := rfl
example : (core_fixture% "i64.reinterpret_f64").2.length = 1 := rfl
example : (core_fixture% "f32.reinterpret_i32").2.length = 1 := rfl
example : (core_fixture% "f64.reinterpret_i64").2.length = 1 := rfl
example : (core_fixture% "v128.const i8x16 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0").2.length = 1 := rfl
example : (core_fixture% "v128.const i16x8 0 0 0 0 0 0 0 0").2.length = 1 := rfl
example : (core_fixture% "v128.const i32x4 0 0 0 0").2.length = 1 := rfl
example : (core_fixture% "v128.const i64x2 0 0").2.length = 1 := rfl
example : (core_fixture% "v128.const f32x4 0 0 0 0").2.length = 1 := rfl
example : (core_fixture% "v128.const f64x2 0 0").2.length = 1 := rfl
example : (core_fixture% "i8x16.shuffle 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0").2.length = 1 := rfl
example : (core_fixture% "i8x16.swizzle").2.length = 1 := rfl
example : (core_fixture% "i8x16.relaxed_swizzle").2.length = 1 := rfl
example : (core_fixture% "i8x16.splat").2.length = 1 := rfl
example : (core_fixture% "i16x8.splat").2.length = 1 := rfl
example : (core_fixture% "i32x4.splat").2.length = 1 := rfl
example : (core_fixture% "i64x2.splat").2.length = 1 := rfl
example : (core_fixture% "f32x4.splat").2.length = 1 := rfl
example : (core_fixture% "f64x2.splat").2.length = 1 := rfl
example : (core_fixture% "i8x16.extract_lane_s 0").2.length = 1 := rfl
example : (core_fixture% "i8x16.extract_lane_u 0").2.length = 1 := rfl
example : (core_fixture% "i16x8.extract_lane_s 0").2.length = 1 := rfl
example : (core_fixture% "i16x8.extract_lane_u 0").2.length = 1 := rfl
example : (core_fixture% "i32x4.extract_lane 0").2.length = 1 := rfl
example : (core_fixture% "i64x2.extract_lane 0").2.length = 1 := rfl
example : (core_fixture% "f32x4.extract_lane 0").2.length = 1 := rfl
example : (core_fixture% "f64x2.extract_lane 0").2.length = 1 := rfl
example : (core_fixture% "i8x16.replace_lane 0").2.length = 1 := rfl
example : (core_fixture% "i16x8.replace_lane 0").2.length = 1 := rfl
example : (core_fixture% "i32x4.replace_lane 0").2.length = 1 := rfl
example : (core_fixture% "i64x2.replace_lane 0").2.length = 1 := rfl
example : (core_fixture% "f32x4.replace_lane 0").2.length = 1 := rfl
example : (core_fixture% "f64x2.replace_lane 0").2.length = 1 := rfl
example : (core_fixture% "v128.any_true").2.length = 1 := rfl
example : (core_fixture% "i8x16.all_true").2.length = 1 := rfl
example : (core_fixture% "i16x8.all_true").2.length = 1 := rfl
example : (core_fixture% "i32x4.all_true").2.length = 1 := rfl
example : (core_fixture% "i64x2.all_true").2.length = 1 := rfl
example : (core_fixture% "i8x16.eq").2.length = 1 := rfl
example : (core_fixture% "i8x16.ne").2.length = 1 := rfl
example : (core_fixture% "i8x16.lt_s").2.length = 1 := rfl
example : (core_fixture% "i8x16.lt_u").2.length = 1 := rfl
example : (core_fixture% "i8x16.gt_s").2.length = 1 := rfl
example : (core_fixture% "i8x16.gt_u").2.length = 1 := rfl
example : (core_fixture% "i8x16.le_s").2.length = 1 := rfl
example : (core_fixture% "i8x16.le_u").2.length = 1 := rfl
example : (core_fixture% "i8x16.ge_s").2.length = 1 := rfl
example : (core_fixture% "i8x16.ge_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.eq").2.length = 1 := rfl
example : (core_fixture% "i16x8.ne").2.length = 1 := rfl
example : (core_fixture% "i16x8.lt_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.lt_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.gt_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.gt_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.le_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.le_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.ge_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.ge_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.eq").2.length = 1 := rfl
example : (core_fixture% "i32x4.ne").2.length = 1 := rfl
example : (core_fixture% "i32x4.lt_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.lt_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.gt_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.gt_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.le_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.le_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.ge_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.ge_u").2.length = 1 := rfl
example : (core_fixture% "i64x2.eq").2.length = 1 := rfl
example : (core_fixture% "i64x2.ne").2.length = 1 := rfl
example : (core_fixture% "i64x2.lt_s").2.length = 1 := rfl
example : (core_fixture% "i64x2.gt_s").2.length = 1 := rfl
example : (core_fixture% "i64x2.le_s").2.length = 1 := rfl
example : (core_fixture% "i64x2.ge_s").2.length = 1 := rfl
example : (core_fixture% "f32x4.eq").2.length = 1 := rfl
example : (core_fixture% "f32x4.ne").2.length = 1 := rfl
example : (core_fixture% "f32x4.lt").2.length = 1 := rfl
example : (core_fixture% "f32x4.gt").2.length = 1 := rfl
example : (core_fixture% "f32x4.le").2.length = 1 := rfl
example : (core_fixture% "f32x4.ge").2.length = 1 := rfl
example : (core_fixture% "f64x2.eq").2.length = 1 := rfl
example : (core_fixture% "f64x2.ne").2.length = 1 := rfl
example : (core_fixture% "f64x2.lt").2.length = 1 := rfl
example : (core_fixture% "f64x2.gt").2.length = 1 := rfl
example : (core_fixture% "f64x2.le").2.length = 1 := rfl
example : (core_fixture% "f64x2.ge").2.length = 1 := rfl
example : (core_fixture% "v128.not").2.length = 1 := rfl
example : (core_fixture% "i8x16.abs").2.length = 1 := rfl
example : (core_fixture% "i8x16.neg").2.length = 1 := rfl
example : (core_fixture% "i8x16.popcnt").2.length = 1 := rfl
example : (core_fixture% "i16x8.abs").2.length = 1 := rfl
example : (core_fixture% "i16x8.neg").2.length = 1 := rfl
example : (core_fixture% "i32x4.abs").2.length = 1 := rfl
example : (core_fixture% "i32x4.neg").2.length = 1 := rfl
example : (core_fixture% "i64x2.abs").2.length = 1 := rfl
example : (core_fixture% "i64x2.neg").2.length = 1 := rfl
example : (core_fixture% "f32x4.abs").2.length = 1 := rfl
example : (core_fixture% "f32x4.neg").2.length = 1 := rfl
example : (core_fixture% "f32x4.sqrt").2.length = 1 := rfl
example : (core_fixture% "f32x4.ceil").2.length = 1 := rfl
example : (core_fixture% "f32x4.floor").2.length = 1 := rfl
example : (core_fixture% "f32x4.trunc").2.length = 1 := rfl
example : (core_fixture% "f32x4.nearest").2.length = 1 := rfl
example : (core_fixture% "f64x2.abs").2.length = 1 := rfl
example : (core_fixture% "f64x2.neg").2.length = 1 := rfl
example : (core_fixture% "f64x2.sqrt").2.length = 1 := rfl
example : (core_fixture% "f64x2.ceil").2.length = 1 := rfl
example : (core_fixture% "f64x2.floor").2.length = 1 := rfl
example : (core_fixture% "f64x2.trunc").2.length = 1 := rfl
example : (core_fixture% "f64x2.nearest").2.length = 1 := rfl
example : (core_fixture% "v128.and").2.length = 1 := rfl
example : (core_fixture% "v128.andnot").2.length = 1 := rfl
example : (core_fixture% "v128.or").2.length = 1 := rfl
example : (core_fixture% "v128.xor").2.length = 1 := rfl
example : (core_fixture% "i8x16.add").2.length = 1 := rfl
example : (core_fixture% "i8x16.add_sat_s").2.length = 1 := rfl
example : (core_fixture% "i8x16.add_sat_u").2.length = 1 := rfl
example : (core_fixture% "i8x16.sub").2.length = 1 := rfl
example : (core_fixture% "i8x16.sub_sat_s").2.length = 1 := rfl
example : (core_fixture% "i8x16.sub_sat_u").2.length = 1 := rfl
example : (core_fixture% "i8x16.min_s").2.length = 1 := rfl
example : (core_fixture% "i8x16.min_u").2.length = 1 := rfl
example : (core_fixture% "i8x16.max_s").2.length = 1 := rfl
example : (core_fixture% "i8x16.max_u").2.length = 1 := rfl
example : (core_fixture% "i8x16.avgr_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.add").2.length = 1 := rfl
example : (core_fixture% "i16x8.add_sat_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.add_sat_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.sub").2.length = 1 := rfl
example : (core_fixture% "i16x8.sub_sat_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.sub_sat_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.mul").2.length = 1 := rfl
example : (core_fixture% "i16x8.min_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.min_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.max_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.max_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.avgr_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.q15mulr_sat_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.relaxed_q15mulr_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.add").2.length = 1 := rfl
example : (core_fixture% "i32x4.sub").2.length = 1 := rfl
example : (core_fixture% "i32x4.mul").2.length = 1 := rfl
example : (core_fixture% "i32x4.min_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.min_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.max_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.max_u").2.length = 1 := rfl
example : (core_fixture% "i64x2.add").2.length = 1 := rfl
example : (core_fixture% "i64x2.sub").2.length = 1 := rfl
example : (core_fixture% "i64x2.mul").2.length = 1 := rfl
example : (core_fixture% "f32x4.add").2.length = 1 := rfl
example : (core_fixture% "f32x4.sub").2.length = 1 := rfl
example : (core_fixture% "f32x4.mul").2.length = 1 := rfl
example : (core_fixture% "f32x4.div").2.length = 1 := rfl
example : (core_fixture% "f32x4.min").2.length = 1 := rfl
example : (core_fixture% "f32x4.max").2.length = 1 := rfl
example : (core_fixture% "f32x4.pmin").2.length = 1 := rfl
example : (core_fixture% "f32x4.pmax").2.length = 1 := rfl
example : (core_fixture% "f32x4.relaxed_min").2.length = 1 := rfl
example : (core_fixture% "f32x4.relaxed_max").2.length = 1 := rfl
example : (core_fixture% "f64x2.add").2.length = 1 := rfl
example : (core_fixture% "f64x2.sub").2.length = 1 := rfl
example : (core_fixture% "f64x2.mul").2.length = 1 := rfl
example : (core_fixture% "f64x2.div").2.length = 1 := rfl
example : (core_fixture% "f64x2.min").2.length = 1 := rfl
example : (core_fixture% "f64x2.max").2.length = 1 := rfl
example : (core_fixture% "f64x2.pmin").2.length = 1 := rfl
example : (core_fixture% "f64x2.pmax").2.length = 1 := rfl
example : (core_fixture% "f64x2.relaxed_min").2.length = 1 := rfl
example : (core_fixture% "f64x2.relaxed_max").2.length = 1 := rfl
example : (core_fixture% "v128.bitselect").2.length = 1 := rfl
example : (core_fixture% "i8x16.relaxed_laneselect").2.length = 1 := rfl
example : (core_fixture% "i16x8.relaxed_laneselect").2.length = 1 := rfl
example : (core_fixture% "i32x4.relaxed_laneselect").2.length = 1 := rfl
example : (core_fixture% "i64x2.relaxed_laneselect").2.length = 1 := rfl
example : (core_fixture% "f32x4.relaxed_madd").2.length = 1 := rfl
example : (core_fixture% "f32x4.relaxed_nmadd").2.length = 1 := rfl
example : (core_fixture% "f64x2.relaxed_madd").2.length = 1 := rfl
example : (core_fixture% "f64x2.relaxed_nmadd").2.length = 1 := rfl
example : (core_fixture% "i8x16.shl").2.length = 1 := rfl
example : (core_fixture% "i8x16.shr_s").2.length = 1 := rfl
example : (core_fixture% "i8x16.shr_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.shl").2.length = 1 := rfl
example : (core_fixture% "i16x8.shr_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.shr_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.shl").2.length = 1 := rfl
example : (core_fixture% "i32x4.shr_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.shr_u").2.length = 1 := rfl
example : (core_fixture% "i64x2.shl").2.length = 1 := rfl
example : (core_fixture% "i64x2.shr_s").2.length = 1 := rfl
example : (core_fixture% "i64x2.shr_u").2.length = 1 := rfl
example : (core_fixture% "i8x16.bitmask").2.length = 1 := rfl
example : (core_fixture% "i16x8.bitmask").2.length = 1 := rfl
example : (core_fixture% "i32x4.bitmask").2.length = 1 := rfl
example : (core_fixture% "i64x2.bitmask").2.length = 1 := rfl
example : (core_fixture% "i8x16.narrow_i16x8_s").2.length = 1 := rfl
example : (core_fixture% "i8x16.narrow_i16x8_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.narrow_i32x4_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.narrow_i32x4_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.extend_low_i8x16_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.extend_low_i8x16_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.extend_high_i8x16_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.extend_high_i8x16_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.extend_low_i16x8_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.extend_low_i16x8_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.extend_high_i16x8_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.extend_high_i16x8_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.trunc_sat_f32x4_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.trunc_sat_f32x4_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.trunc_sat_f64x2_s_zero").2.length = 1 := rfl
example : (core_fixture% "i32x4.trunc_sat_f64x2_u_zero").2.length = 1 := rfl
example : (core_fixture% "i32x4.relaxed_trunc_f32x4_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.relaxed_trunc_f32x4_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.relaxed_trunc_f64x2_s_zero").2.length = 1 := rfl
example : (core_fixture% "i32x4.relaxed_trunc_f64x2_u_zero").2.length = 1 := rfl
example : (core_fixture% "i64x2.extend_low_i32x4_s").2.length = 1 := rfl
example : (core_fixture% "i64x2.extend_low_i32x4_u").2.length = 1 := rfl
example : (core_fixture% "i64x2.extend_high_i32x4_s").2.length = 1 := rfl
example : (core_fixture% "i64x2.extend_high_i32x4_u").2.length = 1 := rfl
example : (core_fixture% "f32x4.demote_f64x2_zero").2.length = 1 := rfl
example : (core_fixture% "f32x4.convert_i32x4_s").2.length = 1 := rfl
example : (core_fixture% "f32x4.convert_i32x4_u").2.length = 1 := rfl
example : (core_fixture% "f64x2.promote_low_f32x4").2.length = 1 := rfl
example : (core_fixture% "f64x2.convert_low_i32x4_s").2.length = 1 := rfl
example : (core_fixture% "f64x2.convert_low_i32x4_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.extadd_pairwise_i8x16_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.extadd_pairwise_i8x16_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.extadd_pairwise_i16x8_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.extadd_pairwise_i16x8_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.extmul_low_i8x16_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.extmul_low_i8x16_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.extmul_high_i8x16_s").2.length = 1 := rfl
example : (core_fixture% "i16x8.extmul_high_i8x16_u").2.length = 1 := rfl
example : (core_fixture% "i16x8.relaxed_dot_i8x16_i7x16_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.extmul_low_i16x8_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.extmul_low_i16x8_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.extmul_high_i16x8_s").2.length = 1 := rfl
example : (core_fixture% "i32x4.extmul_high_i16x8_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.dot_i16x8_s").2.length = 1 := rfl
example : (core_fixture% "i64x2.extmul_low_i32x4_s").2.length = 1 := rfl
example : (core_fixture% "i64x2.extmul_low_i32x4_u").2.length = 1 := rfl
example : (core_fixture% "i64x2.extmul_high_i32x4_s").2.length = 1 := rfl
example : (core_fixture% "i64x2.extmul_high_i32x4_u").2.length = 1 := rfl
example : (core_fixture% "i32x4.relaxed_dot_i8x16_i7x16_add_s").2.length = 1 := rfl
example : (core_fixture% "block end").2.length = 1 := rfl
example : (core_fixture% "loop end").2.length = 1 := rfl
example : (core_fixture% "if else end").2.length = 1 := rfl
example : (core_fixture% "try_table end").2.length = 1 := rfl
