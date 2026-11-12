module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.V1.Binary.Types
public import Silmaril.Wasm.V1.Instructions

/-! # WebAssembly 1.0 binary format: instructions

Transcribed from REC 5.4 (5 December 2019). `call_indirect`, `memory.size` and
`memory.grow` carry a literal reserved byte `0x00`; there are no multi-value
block types, no `0xFC` prefix, and no sign-extension opcodes. Constants are
`iN ::= n:sN` (signed LEB128) and `fN` little-endian IEEE bytes (REC 5.2).
The opcode tables were generated from the opcode list and cross-checked against
REC 5.4.1–5.4.5 (the 1.0 opcodes coincide with Core 3.0's for these instructions).
-/

@[expose] public section

namespace Silmaril.Wasm.V1.Binary

open Silmaril.Wasm.Binary

/-- Single-byte instructions without immediates. -/
inductive PlainOp : UInt8 → V1.Instr → Prop where
  /-- `0x00` ⇒ `unreachable` (REC 5.4.1) -/
  | rx00 : PlainOp 0x00 .unreachable
  /-- `0x01` ⇒ `nop` (REC 5.4.1) -/
  | rx01 : PlainOp 0x01 .nop
  /-- `0x1A` ⇒ `drop` (REC 5.4.2) -/
  | rx1A : PlainOp 0x1A .drop
  /-- `0x1B` ⇒ `select` (REC 5.4.2) -/
  | rx1B : PlainOp 0x1B .select
  /-- `0x0F` ⇒ `return` (REC 5.4.1) -/
  | rx0F : PlainOp 0x0F .return_
  /-- `0x45` ⇒ `i32.eqz` (REC 5.4.5) -/
  | rx45 : PlainOp 0x45 (.intTestOp .i32 .eqz)
  /-- `0x46` ⇒ `i32.eq` (REC 5.4.5) -/
  | rx46 : PlainOp 0x46 (.intRelOp .i32 .eq)
  /-- `0x47` ⇒ `i32.ne` (REC 5.4.5) -/
  | rx47 : PlainOp 0x47 (.intRelOp .i32 .ne)
  /-- `0x48` ⇒ `i32.lt_s` (REC 5.4.5) -/
  | rx48 : PlainOp 0x48 (.intRelOp .i32 (.lt .signed))
  /-- `0x49` ⇒ `i32.lt_u` (REC 5.4.5) -/
  | rx49 : PlainOp 0x49 (.intRelOp .i32 (.lt .unsigned))
  /-- `0x4A` ⇒ `i32.gt_s` (REC 5.4.5) -/
  | rx4A : PlainOp 0x4A (.intRelOp .i32 (.gt .signed))
  /-- `0x4B` ⇒ `i32.gt_u` (REC 5.4.5) -/
  | rx4B : PlainOp 0x4B (.intRelOp .i32 (.gt .unsigned))
  /-- `0x4C` ⇒ `i32.le_s` (REC 5.4.5) -/
  | rx4C : PlainOp 0x4C (.intRelOp .i32 (.le .signed))
  /-- `0x4D` ⇒ `i32.le_u` (REC 5.4.5) -/
  | rx4D : PlainOp 0x4D (.intRelOp .i32 (.le .unsigned))
  /-- `0x4E` ⇒ `i32.ge_s` (REC 5.4.5) -/
  | rx4E : PlainOp 0x4E (.intRelOp .i32 (.ge .signed))
  /-- `0x4F` ⇒ `i32.ge_u` (REC 5.4.5) -/
  | rx4F : PlainOp 0x4F (.intRelOp .i32 (.ge .unsigned))
  /-- `0x50` ⇒ `i64.eqz` (REC 5.4.5) -/
  | rx50 : PlainOp 0x50 (.intTestOp .i64 .eqz)
  /-- `0x51` ⇒ `i64.eq` (REC 5.4.5) -/
  | rx51 : PlainOp 0x51 (.intRelOp .i64 .eq)
  /-- `0x52` ⇒ `i64.ne` (REC 5.4.5) -/
  | rx52 : PlainOp 0x52 (.intRelOp .i64 .ne)
  /-- `0x53` ⇒ `i64.lt_s` (REC 5.4.5) -/
  | rx53 : PlainOp 0x53 (.intRelOp .i64 (.lt .signed))
  /-- `0x54` ⇒ `i64.lt_u` (REC 5.4.5) -/
  | rx54 : PlainOp 0x54 (.intRelOp .i64 (.lt .unsigned))
  /-- `0x55` ⇒ `i64.gt_s` (REC 5.4.5) -/
  | rx55 : PlainOp 0x55 (.intRelOp .i64 (.gt .signed))
  /-- `0x56` ⇒ `i64.gt_u` (REC 5.4.5) -/
  | rx56 : PlainOp 0x56 (.intRelOp .i64 (.gt .unsigned))
  /-- `0x57` ⇒ `i64.le_s` (REC 5.4.5) -/
  | rx57 : PlainOp 0x57 (.intRelOp .i64 (.le .signed))
  /-- `0x58` ⇒ `i64.le_u` (REC 5.4.5) -/
  | rx58 : PlainOp 0x58 (.intRelOp .i64 (.le .unsigned))
  /-- `0x59` ⇒ `i64.ge_s` (REC 5.4.5) -/
  | rx59 : PlainOp 0x59 (.intRelOp .i64 (.ge .signed))
  /-- `0x5A` ⇒ `i64.ge_u` (REC 5.4.5) -/
  | rx5A : PlainOp 0x5A (.intRelOp .i64 (.ge .unsigned))
  /-- `0x5B` ⇒ `f32.eq` (REC 5.4.5) -/
  | rx5B : PlainOp 0x5B (.floatRelOp .f32 .eq)
  /-- `0x5C` ⇒ `f32.ne` (REC 5.4.5) -/
  | rx5C : PlainOp 0x5C (.floatRelOp .f32 .ne)
  /-- `0x5D` ⇒ `f32.lt` (REC 5.4.5) -/
  | rx5D : PlainOp 0x5D (.floatRelOp .f32 .lt)
  /-- `0x5E` ⇒ `f32.gt` (REC 5.4.5) -/
  | rx5E : PlainOp 0x5E (.floatRelOp .f32 .gt)
  /-- `0x5F` ⇒ `f32.le` (REC 5.4.5) -/
  | rx5F : PlainOp 0x5F (.floatRelOp .f32 .le)
  /-- `0x60` ⇒ `f32.ge` (REC 5.4.5) -/
  | rx60 : PlainOp 0x60 (.floatRelOp .f32 .ge)
  /-- `0x61` ⇒ `f64.eq` (REC 5.4.5) -/
  | rx61 : PlainOp 0x61 (.floatRelOp .f64 .eq)
  /-- `0x62` ⇒ `f64.ne` (REC 5.4.5) -/
  | rx62 : PlainOp 0x62 (.floatRelOp .f64 .ne)
  /-- `0x63` ⇒ `f64.lt` (REC 5.4.5) -/
  | rx63 : PlainOp 0x63 (.floatRelOp .f64 .lt)
  /-- `0x64` ⇒ `f64.gt` (REC 5.4.5) -/
  | rx64 : PlainOp 0x64 (.floatRelOp .f64 .gt)
  /-- `0x65` ⇒ `f64.le` (REC 5.4.5) -/
  | rx65 : PlainOp 0x65 (.floatRelOp .f64 .le)
  /-- `0x66` ⇒ `f64.ge` (REC 5.4.5) -/
  | rx66 : PlainOp 0x66 (.floatRelOp .f64 .ge)
  /-- `0x67` ⇒ `i32.clz` (REC 5.4.5) -/
  | rx67 : PlainOp 0x67 (.intUnOp .i32 .clz)
  /-- `0x68` ⇒ `i32.ctz` (REC 5.4.5) -/
  | rx68 : PlainOp 0x68 (.intUnOp .i32 .ctz)
  /-- `0x69` ⇒ `i32.popcnt` (REC 5.4.5) -/
  | rx69 : PlainOp 0x69 (.intUnOp .i32 .popcnt)
  /-- `0x6A` ⇒ `i32.add` (REC 5.4.5) -/
  | rx6A : PlainOp 0x6A (.intBinOp .i32 .add)
  /-- `0x6B` ⇒ `i32.sub` (REC 5.4.5) -/
  | rx6B : PlainOp 0x6B (.intBinOp .i32 .sub)
  /-- `0x6C` ⇒ `i32.mul` (REC 5.4.5) -/
  | rx6C : PlainOp 0x6C (.intBinOp .i32 .mul)
  /-- `0x6D` ⇒ `i32.div_s` (REC 5.4.5) -/
  | rx6D : PlainOp 0x6D (.intBinOp .i32 (.div .signed))
  /-- `0x6E` ⇒ `i32.div_u` (REC 5.4.5) -/
  | rx6E : PlainOp 0x6E (.intBinOp .i32 (.div .unsigned))
  /-- `0x6F` ⇒ `i32.rem_s` (REC 5.4.5) -/
  | rx6F : PlainOp 0x6F (.intBinOp .i32 (.rem .signed))
  /-- `0x70` ⇒ `i32.rem_u` (REC 5.4.5) -/
  | rx70 : PlainOp 0x70 (.intBinOp .i32 (.rem .unsigned))
  /-- `0x71` ⇒ `i32.and` (REC 5.4.5) -/
  | rx71 : PlainOp 0x71 (.intBinOp .i32 .and)
  /-- `0x72` ⇒ `i32.or` (REC 5.4.5) -/
  | rx72 : PlainOp 0x72 (.intBinOp .i32 .or)
  /-- `0x73` ⇒ `i32.xor` (REC 5.4.5) -/
  | rx73 : PlainOp 0x73 (.intBinOp .i32 .xor)
  /-- `0x74` ⇒ `i32.shl` (REC 5.4.5) -/
  | rx74 : PlainOp 0x74 (.intBinOp .i32 .shl)
  /-- `0x75` ⇒ `i32.shr_s` (REC 5.4.5) -/
  | rx75 : PlainOp 0x75 (.intBinOp .i32 (.shr .signed))
  /-- `0x76` ⇒ `i32.shr_u` (REC 5.4.5) -/
  | rx76 : PlainOp 0x76 (.intBinOp .i32 (.shr .unsigned))
  /-- `0x77` ⇒ `i32.rotl` (REC 5.4.5) -/
  | rx77 : PlainOp 0x77 (.intBinOp .i32 .rotl)
  /-- `0x78` ⇒ `i32.rotr` (REC 5.4.5) -/
  | rx78 : PlainOp 0x78 (.intBinOp .i32 .rotr)
  /-- `0x79` ⇒ `i64.clz` (REC 5.4.5) -/
  | rx79 : PlainOp 0x79 (.intUnOp .i64 .clz)
  /-- `0x7A` ⇒ `i64.ctz` (REC 5.4.5) -/
  | rx7A : PlainOp 0x7A (.intUnOp .i64 .ctz)
  /-- `0x7B` ⇒ `i64.popcnt` (REC 5.4.5) -/
  | rx7B : PlainOp 0x7B (.intUnOp .i64 .popcnt)
  /-- `0x7C` ⇒ `i64.add` (REC 5.4.5) -/
  | rx7C : PlainOp 0x7C (.intBinOp .i64 .add)
  /-- `0x7D` ⇒ `i64.sub` (REC 5.4.5) -/
  | rx7D : PlainOp 0x7D (.intBinOp .i64 .sub)
  /-- `0x7E` ⇒ `i64.mul` (REC 5.4.5) -/
  | rx7E : PlainOp 0x7E (.intBinOp .i64 .mul)
  /-- `0x7F` ⇒ `i64.div_s` (REC 5.4.5) -/
  | rx7F : PlainOp 0x7F (.intBinOp .i64 (.div .signed))
  /-- `0x80` ⇒ `i64.div_u` (REC 5.4.5) -/
  | rx80 : PlainOp 0x80 (.intBinOp .i64 (.div .unsigned))
  /-- `0x81` ⇒ `i64.rem_s` (REC 5.4.5) -/
  | rx81 : PlainOp 0x81 (.intBinOp .i64 (.rem .signed))
  /-- `0x82` ⇒ `i64.rem_u` (REC 5.4.5) -/
  | rx82 : PlainOp 0x82 (.intBinOp .i64 (.rem .unsigned))
  /-- `0x83` ⇒ `i64.and` (REC 5.4.5) -/
  | rx83 : PlainOp 0x83 (.intBinOp .i64 .and)
  /-- `0x84` ⇒ `i64.or` (REC 5.4.5) -/
  | rx84 : PlainOp 0x84 (.intBinOp .i64 .or)
  /-- `0x85` ⇒ `i64.xor` (REC 5.4.5) -/
  | rx85 : PlainOp 0x85 (.intBinOp .i64 .xor)
  /-- `0x86` ⇒ `i64.shl` (REC 5.4.5) -/
  | rx86 : PlainOp 0x86 (.intBinOp .i64 .shl)
  /-- `0x87` ⇒ `i64.shr_s` (REC 5.4.5) -/
  | rx87 : PlainOp 0x87 (.intBinOp .i64 (.shr .signed))
  /-- `0x88` ⇒ `i64.shr_u` (REC 5.4.5) -/
  | rx88 : PlainOp 0x88 (.intBinOp .i64 (.shr .unsigned))
  /-- `0x89` ⇒ `i64.rotl` (REC 5.4.5) -/
  | rx89 : PlainOp 0x89 (.intBinOp .i64 .rotl)
  /-- `0x8A` ⇒ `i64.rotr` (REC 5.4.5) -/
  | rx8A : PlainOp 0x8A (.intBinOp .i64 .rotr)
  /-- `0x8B` ⇒ `f32.abs` (REC 5.4.5) -/
  | rx8B : PlainOp 0x8B (.floatUnOp .f32 .abs)
  /-- `0x8C` ⇒ `f32.neg` (REC 5.4.5) -/
  | rx8C : PlainOp 0x8C (.floatUnOp .f32 .neg)
  /-- `0x8D` ⇒ `f32.ceil` (REC 5.4.5) -/
  | rx8D : PlainOp 0x8D (.floatUnOp .f32 .ceil)
  /-- `0x8E` ⇒ `f32.floor` (REC 5.4.5) -/
  | rx8E : PlainOp 0x8E (.floatUnOp .f32 .floor)
  /-- `0x8F` ⇒ `f32.trunc` (REC 5.4.5) -/
  | rx8F : PlainOp 0x8F (.floatUnOp .f32 .trunc)
  /-- `0x90` ⇒ `f32.nearest` (REC 5.4.5) -/
  | rx90 : PlainOp 0x90 (.floatUnOp .f32 .nearest)
  /-- `0x91` ⇒ `f32.sqrt` (REC 5.4.5) -/
  | rx91 : PlainOp 0x91 (.floatUnOp .f32 .sqrt)
  /-- `0x92` ⇒ `f32.add` (REC 5.4.5) -/
  | rx92 : PlainOp 0x92 (.floatBinOp .f32 .add)
  /-- `0x93` ⇒ `f32.sub` (REC 5.4.5) -/
  | rx93 : PlainOp 0x93 (.floatBinOp .f32 .sub)
  /-- `0x94` ⇒ `f32.mul` (REC 5.4.5) -/
  | rx94 : PlainOp 0x94 (.floatBinOp .f32 .mul)
  /-- `0x95` ⇒ `f32.div` (REC 5.4.5) -/
  | rx95 : PlainOp 0x95 (.floatBinOp .f32 .div)
  /-- `0x96` ⇒ `f32.min` (REC 5.4.5) -/
  | rx96 : PlainOp 0x96 (.floatBinOp .f32 .min)
  /-- `0x97` ⇒ `f32.max` (REC 5.4.5) -/
  | rx97 : PlainOp 0x97 (.floatBinOp .f32 .max)
  /-- `0x98` ⇒ `f32.copysign` (REC 5.4.5) -/
  | rx98 : PlainOp 0x98 (.floatBinOp .f32 .copysign)
  /-- `0x99` ⇒ `f64.abs` (REC 5.4.5) -/
  | rx99 : PlainOp 0x99 (.floatUnOp .f64 .abs)
  /-- `0x9A` ⇒ `f64.neg` (REC 5.4.5) -/
  | rx9A : PlainOp 0x9A (.floatUnOp .f64 .neg)
  /-- `0x9B` ⇒ `f64.ceil` (REC 5.4.5) -/
  | rx9B : PlainOp 0x9B (.floatUnOp .f64 .ceil)
  /-- `0x9C` ⇒ `f64.floor` (REC 5.4.5) -/
  | rx9C : PlainOp 0x9C (.floatUnOp .f64 .floor)
  /-- `0x9D` ⇒ `f64.trunc` (REC 5.4.5) -/
  | rx9D : PlainOp 0x9D (.floatUnOp .f64 .trunc)
  /-- `0x9E` ⇒ `f64.nearest` (REC 5.4.5) -/
  | rx9E : PlainOp 0x9E (.floatUnOp .f64 .nearest)
  /-- `0x9F` ⇒ `f64.sqrt` (REC 5.4.5) -/
  | rx9F : PlainOp 0x9F (.floatUnOp .f64 .sqrt)
  /-- `0xA0` ⇒ `f64.add` (REC 5.4.5) -/
  | rxA0 : PlainOp 0xA0 (.floatBinOp .f64 .add)
  /-- `0xA1` ⇒ `f64.sub` (REC 5.4.5) -/
  | rxA1 : PlainOp 0xA1 (.floatBinOp .f64 .sub)
  /-- `0xA2` ⇒ `f64.mul` (REC 5.4.5) -/
  | rxA2 : PlainOp 0xA2 (.floatBinOp .f64 .mul)
  /-- `0xA3` ⇒ `f64.div` (REC 5.4.5) -/
  | rxA3 : PlainOp 0xA3 (.floatBinOp .f64 .div)
  /-- `0xA4` ⇒ `f64.min` (REC 5.4.5) -/
  | rxA4 : PlainOp 0xA4 (.floatBinOp .f64 .min)
  /-- `0xA5` ⇒ `f64.max` (REC 5.4.5) -/
  | rxA5 : PlainOp 0xA5 (.floatBinOp .f64 .max)
  /-- `0xA6` ⇒ `f64.copysign` (REC 5.4.5) -/
  | rxA6 : PlainOp 0xA6 (.floatBinOp .f64 .copysign)
  /-- `0xA7` ⇒ `i32.wrap_i64` (REC 5.4.5) -/
  | rxA7 : PlainOp 0xA7 (.convert .wrap)
  /-- `0xA8` ⇒ `i32.trunc_f32_s` (REC 5.4.5) -/
  | rxA8 : PlainOp 0xA8 (.convert (.trunc .f32 .i32 .signed))
  /-- `0xA9` ⇒ `i32.trunc_f32_u` (REC 5.4.5) -/
  | rxA9 : PlainOp 0xA9 (.convert (.trunc .f32 .i32 .unsigned))
  /-- `0xAA` ⇒ `i32.trunc_f64_s` (REC 5.4.5) -/
  | rxAA : PlainOp 0xAA (.convert (.trunc .f64 .i32 .signed))
  /-- `0xAB` ⇒ `i32.trunc_f64_u` (REC 5.4.5) -/
  | rxAB : PlainOp 0xAB (.convert (.trunc .f64 .i32 .unsigned))
  /-- `0xAC` ⇒ `i64.extend_i32_s` (REC 5.4.5) -/
  | rxAC : PlainOp 0xAC (.convert (.extend .signed))
  /-- `0xAD` ⇒ `i64.extend_i32_u` (REC 5.4.5) -/
  | rxAD : PlainOp 0xAD (.convert (.extend .unsigned))
  /-- `0xAE` ⇒ `i64.trunc_f32_s` (REC 5.4.5) -/
  | rxAE : PlainOp 0xAE (.convert (.trunc .f32 .i64 .signed))
  /-- `0xAF` ⇒ `i64.trunc_f32_u` (REC 5.4.5) -/
  | rxAF : PlainOp 0xAF (.convert (.trunc .f32 .i64 .unsigned))
  /-- `0xB0` ⇒ `i64.trunc_f64_s` (REC 5.4.5) -/
  | rxB0 : PlainOp 0xB0 (.convert (.trunc .f64 .i64 .signed))
  /-- `0xB1` ⇒ `i64.trunc_f64_u` (REC 5.4.5) -/
  | rxB1 : PlainOp 0xB1 (.convert (.trunc .f64 .i64 .unsigned))
  /-- `0xB2` ⇒ `f32.convert_i32_s` (REC 5.4.5) -/
  | rxB2 : PlainOp 0xB2 (.convert (.convert .i32 .f32 .signed))
  /-- `0xB3` ⇒ `f32.convert_i32_u` (REC 5.4.5) -/
  | rxB3 : PlainOp 0xB3 (.convert (.convert .i32 .f32 .unsigned))
  /-- `0xB4` ⇒ `f32.convert_i64_s` (REC 5.4.5) -/
  | rxB4 : PlainOp 0xB4 (.convert (.convert .i64 .f32 .signed))
  /-- `0xB5` ⇒ `f32.convert_i64_u` (REC 5.4.5) -/
  | rxB5 : PlainOp 0xB5 (.convert (.convert .i64 .f32 .unsigned))
  /-- `0xB6` ⇒ `f32.demote_f64` (REC 5.4.5) -/
  | rxB6 : PlainOp 0xB6 (.convert .demote)
  /-- `0xB7` ⇒ `f64.convert_i32_s` (REC 5.4.5) -/
  | rxB7 : PlainOp 0xB7 (.convert (.convert .i32 .f64 .signed))
  /-- `0xB8` ⇒ `f64.convert_i32_u` (REC 5.4.5) -/
  | rxB8 : PlainOp 0xB8 (.convert (.convert .i32 .f64 .unsigned))
  /-- `0xB9` ⇒ `f64.convert_i64_s` (REC 5.4.5) -/
  | rxB9 : PlainOp 0xB9 (.convert (.convert .i64 .f64 .signed))
  /-- `0xBA` ⇒ `f64.convert_i64_u` (REC 5.4.5) -/
  | rxBA : PlainOp 0xBA (.convert (.convert .i64 .f64 .unsigned))
  /-- `0xBB` ⇒ `f64.promote_f32` (REC 5.4.5) -/
  | rxBB : PlainOp 0xBB (.convert .promote)
  /-- `0xBC` ⇒ `i32.reinterpret_f32` (REC 5.4.5) -/
  | rxBC : PlainOp 0xBC (.convert (.reinterpretInt .f32))
  /-- `0xBD` ⇒ `i64.reinterpret_f64` (REC 5.4.5) -/
  | rxBD : PlainOp 0xBD (.convert (.reinterpretInt .f64))
  /-- `0xBE` ⇒ `f32.reinterpret_i32` (REC 5.4.5) -/
  | rxBE : PlainOp 0xBE (.convert (.reinterpretFloat .i32))
  /-- `0xBF` ⇒ `f64.reinterpret_i64` (REC 5.4.5) -/
  | rxBF : PlainOp 0xBF (.convert (.reinterpretFloat .i64))

/-- Loads and stores (`0xNN m:memarg`, REC 5.4.4). -/
inductive MemOp : UInt8 → (MemArg → V1.Instr) → Prop where
  /-- `0x28 m:memarg` -/
  | rx28 : MemOp 0x28 (fun ao => .intLoad .i32 none ao)
  /-- `0x29 m:memarg` -/
  | rx29 : MemOp 0x29 (fun ao => .intLoad .i64 none ao)
  /-- `0x2A m:memarg` -/
  | rx2A : MemOp 0x2A (fun ao => .floatLoad .f32 ao)
  /-- `0x2B m:memarg` -/
  | rx2B : MemOp 0x2B (fun ao => .floatLoad .f64 ao)
  /-- `0x2C m:memarg` -/
  | rx2C : MemOp 0x2C (fun ao => .intLoad .i32 (some (.i8, .signed)) ao)
  /-- `0x2D m:memarg` -/
  | rx2D : MemOp 0x2D (fun ao => .intLoad .i32 (some (.i8, .unsigned)) ao)
  /-- `0x2E m:memarg` -/
  | rx2E : MemOp 0x2E (fun ao => .intLoad .i32 (some (.i16, .signed)) ao)
  /-- `0x2F m:memarg` -/
  | rx2F : MemOp 0x2F (fun ao => .intLoad .i32 (some (.i16, .unsigned)) ao)
  /-- `0x30 m:memarg` -/
  | rx30 : MemOp 0x30 (fun ao => .intLoad .i64 (some (.i8, .signed)) ao)
  /-- `0x31 m:memarg` -/
  | rx31 : MemOp 0x31 (fun ao => .intLoad .i64 (some (.i8, .unsigned)) ao)
  /-- `0x32 m:memarg` -/
  | rx32 : MemOp 0x32 (fun ao => .intLoad .i64 (some (.i16, .signed)) ao)
  /-- `0x33 m:memarg` -/
  | rx33 : MemOp 0x33 (fun ao => .intLoad .i64 (some (.i16, .unsigned)) ao)
  /-- `0x34 m:memarg` -/
  | rx34 : MemOp 0x34 (fun ao => .intLoad .i64 (some (.i32, .signed)) ao)
  /-- `0x35 m:memarg` -/
  | rx35 : MemOp 0x35 (fun ao => .intLoad .i64 (some (.i32, .unsigned)) ao)
  /-- `0x36 m:memarg` -/
  | rx36 : MemOp 0x36 (fun ao => .intStore .i32 none ao)
  /-- `0x37 m:memarg` -/
  | rx37 : MemOp 0x37 (fun ao => .intStore .i64 none ao)
  /-- `0x38 m:memarg` -/
  | rx38 : MemOp 0x38 (fun ao => .floatStore .f32 ao)
  /-- `0x39 m:memarg` -/
  | rx39 : MemOp 0x39 (fun ao => .floatStore .f64 ao)
  /-- `0x3A m:memarg` -/
  | rx3A : MemOp 0x3A (fun ao => .intStore .i32 (some .i8) ao)
  /-- `0x3B m:memarg` -/
  | rx3B : MemOp 0x3B (fun ao => .intStore .i32 (some .i16) ao)
  /-- `0x3C m:memarg` -/
  | rx3C : MemOp 0x3C (fun ao => .intStore .i64 (some .i8) ao)
  /-- `0x3D m:memarg` -/
  | rx3D : MemOp 0x3D (fun ao => .intStore .i64 (some .i16) ao)
  /-- `0x3E m:memarg` -/
  | rx3E : MemOp 0x3E (fun ao => .intStore .i64 (some .i32) ao)

/-- `memarg ::= a:u32 o:u32 ⇒ {align a, offset o}` (REC 5.4.4). -/
inductive Memarg : Bytes → V1.MemArg → Prop where
  | mk {ba bo : Bytes} {a o : Fin (2 ^ 32)} (ha : U32 ba a.val) (ho : U32 bo o.val) :
      Memarg (ba ++ bo) ⟨a, o⟩

mutual

/-- `instr` (REC 5.4.1–5.4.5). -/
inductive Instr : Bytes → V1.Instr → Prop where
  /-- Every opcode without immediates (`PlainOp`): REC 5.4.1 (`unreachable`, `nop`,
  `return`), 5.4.2 (`drop`, `select`), 5.4.5 (numeric). -/
  | plain {op : UInt8} {i : V1.Instr} (h : PlainOp op i) : Instr [op] i
  /-- `0x02 rt:blocktype (in:instr)* 0x0B ⇒ block rt in* end` (REC 5.4.1). -/
  | block {bt b : Bytes} {t : V1.BlockType} {body : List V1.Instr} (ht : BlockType bt t)
      (hb : Instrs b body) : Instr ([0x02] ++ bt ++ b ++ [0x0B]) (.block t body)
  /-- `0x03 rt:blocktype (in:instr)* 0x0B ⇒ loop rt in* end` (REC 5.4.1). -/
  | loop {bt b : Bytes} {t : V1.BlockType} {body : List V1.Instr} (ht : BlockType bt t)
      (hb : Instrs b body) : Instr ([0x03] ++ bt ++ b ++ [0x0B]) (.loop t body)
  /-- `0x04 rt:blocktype (in:instr)* 0x0B ⇒ if rt in* else ε end` (REC 5.4.1). -/
  | if_ {bt b : Bytes} {t : V1.BlockType} {body : List V1.Instr} (ht : BlockType bt t)
      (hb : Instrs b body) : Instr ([0x04] ++ bt ++ b ++ [0x0B]) (.if_ t body [])
  /-- `0x04 rt:blocktype (in₁:instr)* 0x05 (in₂:instr)* 0x0B ⇒ if rt in₁* else in₂* end`. -/
  | ifElse {bt b₁ b₂ : Bytes} {t : V1.BlockType} {body₁ body₂ : List V1.Instr}
      (ht : BlockType bt t) (h₁ : Instrs b₁ body₁) (h₂ : Instrs b₂ body₂) :
      Instr ([0x04] ++ bt ++ b₁ ++ [0x05] ++ b₂ ++ [0x0B]) (.if_ t body₁ body₂)
  /-- `0x0C l:labelidx ⇒ br l` (REC 5.4.1). -/
  | br {b : Bytes} {l : LabelIdx} (h : Index b l) : Instr ([0x0C] ++ b) (.br l)
  /-- `0x0D l:labelidx ⇒ br_if l` (REC 5.4.1). -/
  | brIf {b : Bytes} {l : LabelIdx} (h : Index b l) : Instr ([0x0D] ++ b) (.brIf l)
  /-- `0x0E l*:vec(labelidx) l_N:labelidx ⇒ br_table l* l_N` (REC 5.4.1). -/
  | brTable {b b' : Bytes} {ls : List LabelIdx} {l : LabelIdx} (h : Vec Index b ls)
      (h' : Index b' l) : Instr ([0x0E] ++ b ++ b') (.brTable ls l)
  /-- `0x10 x:funcidx ⇒ call x` (REC 5.4.1). -/
  | call {b : Bytes} {x : FuncIdx} (h : Index b x) : Instr ([0x10] ++ b) (.call x)
  /-- `0x11 x:typeidx 0x00 ⇒ call_indirect x` (REC 5.4.1): a literal zero byte. -/
  | callIndirect {b : Bytes} {x : TypeIdx} (h : Index b x) :
      Instr ([0x11] ++ b ++ [0x00]) (.callIndirect x)
  /-- `0x20 x:localidx ⇒ local.get x` (REC 5.4.3). -/
  | localGet {b : Bytes} {x : LocalIdx} (h : Index b x) : Instr ([0x20] ++ b) (.localGet x)
  /-- `0x21 x:localidx ⇒ local.set x` (REC 5.4.3). -/
  | localSet {b : Bytes} {x : LocalIdx} (h : Index b x) : Instr ([0x21] ++ b) (.localSet x)
  /-- `0x22 x:localidx ⇒ local.tee x` (REC 5.4.3). -/
  | localTee {b : Bytes} {x : LocalIdx} (h : Index b x) : Instr ([0x22] ++ b) (.localTee x)
  /-- `0x23 x:globalidx ⇒ global.get x` (REC 5.4.3). -/
  | globalGet {b : Bytes} {x : GlobalIdx} (h : Index b x) : Instr ([0x23] ++ b) (.globalGet x)
  /-- `0x24 x:globalidx ⇒ global.set x` (REC 5.4.3). -/
  | globalSet {b : Bytes} {x : GlobalIdx} (h : Index b x) : Instr ([0x24] ++ b) (.globalSet x)
  /-- Loads and stores `0xNN m:memarg` (REC 5.4.4, `MemOp`). -/
  | mem {op : UInt8} {b : Bytes} {mk : V1.MemArg → V1.Instr} {a : V1.MemArg} (h : MemOp op mk)
      (hm : Memarg b a) : Instr ([op] ++ b) (mk a)
  /-- `0x3F 0x00 ⇒ memory.size` (REC 5.4.4). -/
  | memorySize : Instr [0x3F, 0x00] .memorySize
  /-- `0x40 0x00 ⇒ memory.grow` (REC 5.4.4). -/
  | memoryGrow : Instr [0x40, 0x00] .memoryGrow
  /-- `0x41 n:i32 ⇒ i32.const n` (REC 5.4.5). -/
  | i32Const {b : Bytes} {v : BitVec 32} (h : IN 32 b v) : Instr ([0x41] ++ b) (.intConst .i32 v)
  /-- `0x42 n:i64 ⇒ i64.const n` (REC 5.4.5). -/
  | i64Const {b : Bytes} {v : BitVec 64} (h : IN 64 b v) : Instr ([0x42] ++ b) (.intConst .i64 v)
  /-- `0x43 z:f32 ⇒ f32.const z` (REC 5.4.5). -/
  | f32Const {b : Bytes} {p : BitVec 32} (h : FN 32 b p) : Instr ([0x43] ++ b) (.floatConst .f32 p)
  /-- `0x44 z:f64 ⇒ f64.const z` (REC 5.4.5). -/
  | f64Const {b : Bytes} {p : BitVec 64} (h : FN 64 b p) : Instr ([0x44] ++ b) (.floatConst .f64 p)

/-- `(in:instr)*`. -/
inductive Instrs : Bytes → List V1.Instr → Prop where
  | nil : Instrs [] []
  | cons {b bs : Bytes} {i : V1.Instr} {is : List V1.Instr} (h : Instr b i) (hs : Instrs bs is) :
      Instrs (b ++ bs) (i :: is)

end

/-- `expr ::= (in:instr)* 0x0B ⇒ in* end` (REC 5.4.6). -/
inductive Expr : Bytes → V1.Expr → Prop where
  | mk {b : Bytes} {is : List V1.Instr} (h : Instrs b is) : Expr (b ++ [0x0B]) is

/-! ## Unambiguity

Opcodes are dispatched through computable tables (`plainOp?`, `memOp?`), so the
opcode-level case analysis is linear: each table entry is checked once by `rfl`. -/

/-- The `PlainOp` table as a lookup. -/
def plainOp? (op : UInt8) : Option V1.Instr :=
  match op with
  | 0x00 => some .unreachable
  | 0x01 => some .nop
  | 0x1A => some .drop
  | 0x1B => some .select
  | 0x0F => some .return_
  | 0x45 => some (.intTestOp .i32 .eqz)
  | 0x46 => some (.intRelOp .i32 .eq)
  | 0x47 => some (.intRelOp .i32 .ne)
  | 0x48 => some (.intRelOp .i32 (.lt .signed))
  | 0x49 => some (.intRelOp .i32 (.lt .unsigned))
  | 0x4A => some (.intRelOp .i32 (.gt .signed))
  | 0x4B => some (.intRelOp .i32 (.gt .unsigned))
  | 0x4C => some (.intRelOp .i32 (.le .signed))
  | 0x4D => some (.intRelOp .i32 (.le .unsigned))
  | 0x4E => some (.intRelOp .i32 (.ge .signed))
  | 0x4F => some (.intRelOp .i32 (.ge .unsigned))
  | 0x50 => some (.intTestOp .i64 .eqz)
  | 0x51 => some (.intRelOp .i64 .eq)
  | 0x52 => some (.intRelOp .i64 .ne)
  | 0x53 => some (.intRelOp .i64 (.lt .signed))
  | 0x54 => some (.intRelOp .i64 (.lt .unsigned))
  | 0x55 => some (.intRelOp .i64 (.gt .signed))
  | 0x56 => some (.intRelOp .i64 (.gt .unsigned))
  | 0x57 => some (.intRelOp .i64 (.le .signed))
  | 0x58 => some (.intRelOp .i64 (.le .unsigned))
  | 0x59 => some (.intRelOp .i64 (.ge .signed))
  | 0x5A => some (.intRelOp .i64 (.ge .unsigned))
  | 0x5B => some (.floatRelOp .f32 .eq)
  | 0x5C => some (.floatRelOp .f32 .ne)
  | 0x5D => some (.floatRelOp .f32 .lt)
  | 0x5E => some (.floatRelOp .f32 .gt)
  | 0x5F => some (.floatRelOp .f32 .le)
  | 0x60 => some (.floatRelOp .f32 .ge)
  | 0x61 => some (.floatRelOp .f64 .eq)
  | 0x62 => some (.floatRelOp .f64 .ne)
  | 0x63 => some (.floatRelOp .f64 .lt)
  | 0x64 => some (.floatRelOp .f64 .gt)
  | 0x65 => some (.floatRelOp .f64 .le)
  | 0x66 => some (.floatRelOp .f64 .ge)
  | 0x67 => some (.intUnOp .i32 .clz)
  | 0x68 => some (.intUnOp .i32 .ctz)
  | 0x69 => some (.intUnOp .i32 .popcnt)
  | 0x6A => some (.intBinOp .i32 .add)
  | 0x6B => some (.intBinOp .i32 .sub)
  | 0x6C => some (.intBinOp .i32 .mul)
  | 0x6D => some (.intBinOp .i32 (.div .signed))
  | 0x6E => some (.intBinOp .i32 (.div .unsigned))
  | 0x6F => some (.intBinOp .i32 (.rem .signed))
  | 0x70 => some (.intBinOp .i32 (.rem .unsigned))
  | 0x71 => some (.intBinOp .i32 .and)
  | 0x72 => some (.intBinOp .i32 .or)
  | 0x73 => some (.intBinOp .i32 .xor)
  | 0x74 => some (.intBinOp .i32 .shl)
  | 0x75 => some (.intBinOp .i32 (.shr .signed))
  | 0x76 => some (.intBinOp .i32 (.shr .unsigned))
  | 0x77 => some (.intBinOp .i32 .rotl)
  | 0x78 => some (.intBinOp .i32 .rotr)
  | 0x79 => some (.intUnOp .i64 .clz)
  | 0x7A => some (.intUnOp .i64 .ctz)
  | 0x7B => some (.intUnOp .i64 .popcnt)
  | 0x7C => some (.intBinOp .i64 .add)
  | 0x7D => some (.intBinOp .i64 .sub)
  | 0x7E => some (.intBinOp .i64 .mul)
  | 0x7F => some (.intBinOp .i64 (.div .signed))
  | 0x80 => some (.intBinOp .i64 (.div .unsigned))
  | 0x81 => some (.intBinOp .i64 (.rem .signed))
  | 0x82 => some (.intBinOp .i64 (.rem .unsigned))
  | 0x83 => some (.intBinOp .i64 .and)
  | 0x84 => some (.intBinOp .i64 .or)
  | 0x85 => some (.intBinOp .i64 .xor)
  | 0x86 => some (.intBinOp .i64 .shl)
  | 0x87 => some (.intBinOp .i64 (.shr .signed))
  | 0x88 => some (.intBinOp .i64 (.shr .unsigned))
  | 0x89 => some (.intBinOp .i64 .rotl)
  | 0x8A => some (.intBinOp .i64 .rotr)
  | 0x8B => some (.floatUnOp .f32 .abs)
  | 0x8C => some (.floatUnOp .f32 .neg)
  | 0x8D => some (.floatUnOp .f32 .ceil)
  | 0x8E => some (.floatUnOp .f32 .floor)
  | 0x8F => some (.floatUnOp .f32 .trunc)
  | 0x90 => some (.floatUnOp .f32 .nearest)
  | 0x91 => some (.floatUnOp .f32 .sqrt)
  | 0x92 => some (.floatBinOp .f32 .add)
  | 0x93 => some (.floatBinOp .f32 .sub)
  | 0x94 => some (.floatBinOp .f32 .mul)
  | 0x95 => some (.floatBinOp .f32 .div)
  | 0x96 => some (.floatBinOp .f32 .min)
  | 0x97 => some (.floatBinOp .f32 .max)
  | 0x98 => some (.floatBinOp .f32 .copysign)
  | 0x99 => some (.floatUnOp .f64 .abs)
  | 0x9A => some (.floatUnOp .f64 .neg)
  | 0x9B => some (.floatUnOp .f64 .ceil)
  | 0x9C => some (.floatUnOp .f64 .floor)
  | 0x9D => some (.floatUnOp .f64 .trunc)
  | 0x9E => some (.floatUnOp .f64 .nearest)
  | 0x9F => some (.floatUnOp .f64 .sqrt)
  | 0xA0 => some (.floatBinOp .f64 .add)
  | 0xA1 => some (.floatBinOp .f64 .sub)
  | 0xA2 => some (.floatBinOp .f64 .mul)
  | 0xA3 => some (.floatBinOp .f64 .div)
  | 0xA4 => some (.floatBinOp .f64 .min)
  | 0xA5 => some (.floatBinOp .f64 .max)
  | 0xA6 => some (.floatBinOp .f64 .copysign)
  | 0xA7 => some (.convert .wrap)
  | 0xA8 => some (.convert (.trunc .f32 .i32 .signed))
  | 0xA9 => some (.convert (.trunc .f32 .i32 .unsigned))
  | 0xAA => some (.convert (.trunc .f64 .i32 .signed))
  | 0xAB => some (.convert (.trunc .f64 .i32 .unsigned))
  | 0xAC => some (.convert (.extend .signed))
  | 0xAD => some (.convert (.extend .unsigned))
  | 0xAE => some (.convert (.trunc .f32 .i64 .signed))
  | 0xAF => some (.convert (.trunc .f32 .i64 .unsigned))
  | 0xB0 => some (.convert (.trunc .f64 .i64 .signed))
  | 0xB1 => some (.convert (.trunc .f64 .i64 .unsigned))
  | 0xB2 => some (.convert (.convert .i32 .f32 .signed))
  | 0xB3 => some (.convert (.convert .i32 .f32 .unsigned))
  | 0xB4 => some (.convert (.convert .i64 .f32 .signed))
  | 0xB5 => some (.convert (.convert .i64 .f32 .unsigned))
  | 0xB6 => some (.convert .demote)
  | 0xB7 => some (.convert (.convert .i32 .f64 .signed))
  | 0xB8 => some (.convert (.convert .i32 .f64 .unsigned))
  | 0xB9 => some (.convert (.convert .i64 .f64 .signed))
  | 0xBA => some (.convert (.convert .i64 .f64 .unsigned))
  | 0xBB => some (.convert .promote)
  | 0xBC => some (.convert (.reinterpretInt .f32))
  | 0xBD => some (.convert (.reinterpretInt .f64))
  | 0xBE => some (.convert (.reinterpretFloat .i32))
  | 0xBF => some (.convert (.reinterpretFloat .i64))
  | _ => none

/-- The `MemOp` table as a lookup. -/
def memOp? (op : UInt8) : Option (MemArg → V1.Instr) :=
  match op with
  | 0x28 => some (fun ao => .intLoad .i32 none ao)
  | 0x29 => some (fun ao => .intLoad .i64 none ao)
  | 0x2A => some (fun ao => .floatLoad .f32 ao)
  | 0x2B => some (fun ao => .floatLoad .f64 ao)
  | 0x2C => some (fun ao => .intLoad .i32 (some (.i8, .signed)) ao)
  | 0x2D => some (fun ao => .intLoad .i32 (some (.i8, .unsigned)) ao)
  | 0x2E => some (fun ao => .intLoad .i32 (some (.i16, .signed)) ao)
  | 0x2F => some (fun ao => .intLoad .i32 (some (.i16, .unsigned)) ao)
  | 0x30 => some (fun ao => .intLoad .i64 (some (.i8, .signed)) ao)
  | 0x31 => some (fun ao => .intLoad .i64 (some (.i8, .unsigned)) ao)
  | 0x32 => some (fun ao => .intLoad .i64 (some (.i16, .signed)) ao)
  | 0x33 => some (fun ao => .intLoad .i64 (some (.i16, .unsigned)) ao)
  | 0x34 => some (fun ao => .intLoad .i64 (some (.i32, .signed)) ao)
  | 0x35 => some (fun ao => .intLoad .i64 (some (.i32, .unsigned)) ao)
  | 0x36 => some (fun ao => .intStore .i32 none ao)
  | 0x37 => some (fun ao => .intStore .i64 none ao)
  | 0x38 => some (fun ao => .floatStore .f32 ao)
  | 0x39 => some (fun ao => .floatStore .f64 ao)
  | 0x3A => some (fun ao => .intStore .i32 (some .i8) ao)
  | 0x3B => some (fun ao => .intStore .i32 (some .i16) ao)
  | 0x3C => some (fun ao => .intStore .i64 (some .i8) ao)
  | 0x3D => some (fun ao => .intStore .i64 (some .i16) ao)
  | 0x3E => some (fun ao => .intStore .i64 (some .i32) ao)
  | _ => none

theorem PlainOp.get {op : UInt8} {i : V1.Instr} (h : PlainOp op i) : plainOp? op = some i := by
  cases h <;> rfl

theorem MemOp.get {op : UInt8} {mk : MemArg → V1.Instr} (h : MemOp op mk) :
    memOp? op = some mk := by
  cases h <;> rfl

/-- The class of a leading byte: a plain opcode, a load/store opcode, a body
terminator (`0x05`, `0x0B`), or anything else. -/
inductive OpKind where
  | plain | mem | term | other
  deriving DecidableEq

/-- The class of a leading byte. -/
def opKind (op : UInt8) : OpKind :=
  if (plainOp? op).isSome then .plain
  else if (memOp? op).isSome then .mem
  else if op = 0x05 ∨ op = 0x0B then .term
  else .other

theorem PlainOp.kind {op : UInt8} {i : V1.Instr} (h : PlainOp op i) : opKind op = .plain := by
  simp [opKind, h.get]

theorem MemOp.kind {op : UInt8} {mk : MemArg → V1.Instr} (h : MemOp op mk) :
    opKind op = .mem := by
  cases h <;> rfl

theorem Memarg.prefixFree : PrefixFree Memarg := by
  intro _ _ r r' _ _ h h' e
  cases h with
  | mk ha ho => cases h' with
    | mk ha' ho' =>
      obtain ⟨rfl, hv, rfl, hv'⟩ :=
        PrefixFree.append (UN.prefixFree 32) (UN.prefixFree 32) ha ho ha' ho'
        (by simpa only [List.append_assoc] using e)
      exact ⟨rfl, by rw [Fin.ext hv, Fin.ext hv']⟩

/-- Every instruction encoding begins with a byte that is not a body terminator. -/
theorem Instr.exists_cons {b : Bytes} {i : V1.Instr} (h : Instr b i) :
    ∃ op rest, b = op :: rest ∧ opKind op ≠ .term := by
  cases h with
  | plain hp => exact ⟨_, _, rfl, by rw [hp.kind]; decide⟩
  | mem hm => exact ⟨_, _, rfl, by rw [hm.kind]; decide⟩
  | _ => exact ⟨_, _, rfl, by decide⟩

/-- Instruction sequences followed by a terminator byte are prefix-free, given
prefix-freeness of single instructions up to a length bound. -/
theorem Instrs.term_aux {n : Nat}
    (IH : ∀ ⦃c c' r r' : Bytes⦄ ⦃i i' : V1.Instr⦄, c.length ≤ n → Instr c i → Instr c' i' →
      c ++ r = c' ++ r' → c = c' ∧ i = i')
    {is : List V1.Instr} :
    ∀ {b b' r r' : Bytes} {is' : List V1.Instr} {e e' : UInt8}, Instrs b is → b.length ≤ n →
      Instrs b' is' → opKind e = .term → opKind e' = .term → b ++ e :: r = b' ++ e' :: r' →
      b = b' ∧ is = is' ∧ e = e' ∧ r = r' := by
  induction is with
  | nil =>
    intro b b' r r' is' e e' h _ h' he _ heq
    cases h
    cases h' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      exact ⟨rfl, rfl, heq.1, heq.2⟩
    | cons hc _ =>
      obtain ⟨op, rest, rfl, hk⟩ := hc.exists_cons
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      exact absurd (heq.1 ▸ he) hk
  | cons i is ih =>
    intro b b' r r' is' e e' h hn h' he he' heq
    cases h with
    | cons hc hcs =>
      cases h' with
      | nil =>
        obtain ⟨op, rest, rfl, hk⟩ := hc.exists_cons
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
        exact absurd (heq.1 ▸ he') hk
      | cons hc' hcs' =>
        simp only [List.length_append] at hn
        simp only [List.append_assoc] at heq
        obtain ⟨rfl, rfl⟩ := IH (by omega) hc hc' heq
        obtain ⟨rfl, rfl, rfl, rfl⟩ :=
          ih hcs (by omega) hcs' he he' (List.append_cancel_left heq)
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- Clash between distinct leading bytes, at least one being a table opcode. -/
macro "op_clash" : tactic => `(tactic|
  first
    | exact absurd (‹_ ∧ _›).1 (by decide)
    | obtain ⟨h₀, -⟩ := ‹_ ∧ _›
      subst h₀
      first
        | exact absurd (PlainOp.kind ‹_›) (by decide)
        | exact absurd (MemOp.kind ‹_›) (by decide)
        | exact absurd ((PlainOp.kind ‹_›).symm.trans (MemOp.kind ‹_›)) (by decide)
        | exact absurd ((MemOp.kind ‹_›).symm.trans (PlainOp.kind ‹_›)) (by decide))

theorem Instr.prefixFree_aux (n : Nat) : ∀ ⦃c c' r r' : Bytes⦄ ⦃i i' : V1.Instr⦄,
    c.length ≤ n → Instr c i → Instr c' i' → c ++ r = c' ++ r' → c = c' ∧ i = i' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c c' r r' i i' hn h h' heq
  cases h <;> cases h' <;>
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq,
      true_and] at heq <;>
    try op_clash
  case plain.plain _ hp _ hp' =>
    obtain ⟨rfl, -⟩ := heq
    exact ⟨rfl, Option.some.inj (hp.get.symm.trans hp'.get)⟩
  case block.block _ _ _ _ ht hb _ _ _ _ ht' hb' =>
    obtain ⟨rfl, rfl⟩ := BlockType.prefixFree ht ht' heq
    obtain ⟨rfl, rfl, -, -⟩ := Instrs.term_aux (ih _ (by simp at hn; omega)) hb le_rfl hb'
      (by decide) (by decide) (List.append_cancel_left heq)
    exact ⟨rfl, rfl⟩
  case loop.loop _ _ _ _ ht hb _ _ _ _ ht' hb' =>
    obtain ⟨rfl, rfl⟩ := BlockType.prefixFree ht ht' heq
    obtain ⟨rfl, rfl, -, -⟩ := Instrs.term_aux (ih _ (by simp at hn; omega)) hb le_rfl hb'
      (by decide) (by decide) (List.append_cancel_left heq)
    exact ⟨rfl, rfl⟩
  case if_.if_ _ _ _ _ ht hb _ _ _ _ ht' hb' =>
    obtain ⟨rfl, rfl⟩ := BlockType.prefixFree ht ht' heq
    obtain ⟨rfl, rfl, -, -⟩ := Instrs.term_aux (ih _ (by simp at hn; omega)) hb le_rfl hb'
      (by decide) (by decide) (List.append_cancel_left heq)
    exact ⟨rfl, rfl⟩
  case if_.ifElse _ _ _ _ ht hb _ _ _ _ _ _ ht' hb' _ =>
    obtain ⟨rfl, rfl⟩ := BlockType.prefixFree ht ht' heq
    obtain ⟨-, -, he, -⟩ := Instrs.term_aux (ih _ (by simp at hn; omega)) hb le_rfl hb'
      (by decide) (by decide) (List.append_cancel_left heq)
    exact absurd he (by decide)
  case ifElse.if_ _ _ _ _ _ _ ht hb _ _ _ _ _ ht' hb' =>
    obtain ⟨rfl, rfl⟩ := BlockType.prefixFree ht ht' heq
    obtain ⟨-, -, he, -⟩ := Instrs.term_aux (ih _ (by simp at hn; omega)) hb le_rfl hb'
      (by decide) (by decide) (List.append_cancel_left heq)
    exact absurd he (by decide)
  case ifElse.ifElse _ _ _ _ _ _ ht hb₁ hb₂ _ _ _ _ _ _ ht' hb₁' hb₂' =>
    obtain ⟨rfl, rfl⟩ := BlockType.prefixFree ht ht' heq
    obtain ⟨rfl, rfl, -, heq⟩ := Instrs.term_aux (ih _ (by simp at hn; omega)) hb₁ le_rfl hb₁'
      (by decide) (by decide) (List.append_cancel_left heq)
    obtain ⟨rfl, rfl, -, -⟩ := Instrs.term_aux (ih _ (by simp at hn; omega)) hb₂ le_rfl hb₂'
      (by decide) (by decide) heq
    exact ⟨rfl, rfl⟩
  case br.br _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
    exact ⟨rfl, rfl⟩
  case brIf.brIf _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
    exact ⟨rfl, rfl⟩
  case brTable.brTable _ _ _ _ h₁ h₂ _ _ _ _ h₁' h₂' =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      PrefixFree.append (Vec.prefixFree Index.prefixFree) Index.prefixFree h₁ h₂ h₁' h₂' heq
    exact ⟨rfl, rfl⟩
  case call.call _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
    exact ⟨rfl, rfl⟩
  case callIndirect.callIndirect _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
    exact ⟨rfl, rfl⟩
  case localGet.localGet _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
    exact ⟨rfl, rfl⟩
  case localSet.localSet _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
    exact ⟨rfl, rfl⟩
  case localTee.localTee _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
    exact ⟨rfl, rfl⟩
  case globalGet.globalGet _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
    exact ⟨rfl, rfl⟩
  case globalSet.globalSet _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
    exact ⟨rfl, rfl⟩
  case mem.mem _ _ _ _ hm ha _ _ _ _ hm' ha' =>
    obtain ⟨rfl, heq⟩ := heq
    obtain rfl := Option.some.inj (hm.get.symm.trans hm'.get)
    obtain ⟨rfl, rfl⟩ := Memarg.prefixFree ha ha' heq
    exact ⟨rfl, rfl⟩
  case memorySize.memorySize => exact ⟨rfl, rfl⟩
  case memoryGrow.memoryGrow => exact ⟨rfl, rfl⟩
  case i32Const.i32Const _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := IN.prefixFree 32 h h' heq
    exact ⟨rfl, rfl⟩
  case i64Const.i64Const _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := IN.prefixFree 64 h h' heq
    exact ⟨rfl, rfl⟩
  case f32Const.f32Const _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := FN.prefixFree 32 h h' heq
    exact ⟨rfl, rfl⟩
  case f64Const.f64Const _ _ h _ _ h' =>
    obtain ⟨rfl, rfl⟩ := FN.prefixFree 64 h h' heq
    exact ⟨rfl, rfl⟩

theorem Instr.prefixFree : PrefixFree Instr :=
  fun c _ _ _ _ _ h h' heq => Instr.prefixFree_aux c.length le_rfl h h' heq

theorem Instrs.functional_aux {is : List V1.Instr} : ∀ {b b' : Bytes} {is' : List V1.Instr},
    Instrs b is → Instrs b' is' → b = b' → is = is' := by
  induction is with
  | nil =>
    intro b b' is' h h' hb
    cases h
    cases h' with
    | nil => rfl
    | cons hc _ =>
      obtain ⟨op, rest, rfl, -⟩ := hc.exists_cons
      simp at hb
  | cons i is ih =>
    intro b b' is' h h' hb
    cases h with
    | cons hc hcs =>
      cases h' with
      | nil =>
        obtain ⟨op, rest, rfl, -⟩ := hc.exists_cons
        simp at hb
      | cons hc' hcs' =>
        obtain ⟨rfl, rfl⟩ := Instr.prefixFree hc hc' hb
        rw [ih hcs hcs' (List.append_cancel_left hb)]

/-- Instruction sequences decode uniquely. -/
theorem Instrs.functional : Functional Instrs :=
  fun _ _ _ h h' => Instrs.functional_aux h h' rfl

theorem Expr.prefixFree : PrefixFree Expr := by
  intro _ _ r r' _ _ h h' e
  cases h with
  | mk h => cases h' with
    | mk h' =>
      simp only [List.append_assoc, List.singleton_append] at e
      obtain ⟨rfl, rfl, -, -⟩ := Instrs.term_aux (n := _)
        (fun _ _ _ _ _ _ _ hc hc' hcc => Instr.prefixFree hc hc' hcc) h le_rfl h' (by decide) (by decide) e
      exact ⟨rfl, rfl⟩

end Silmaril.Wasm.V1.Binary
