module

public import Silmaril.Wasm.Binary.Core.Types
public import Silmaril.Wasm.Instructions

/-! # Core 3.0 binary format: opcode tables

The instructions of `5.3-binary.instructions.spectec` (cited `5.3:n`) whose immediates
are fixed by their opcode, grouped by opcode prefix into tables (`PlainOp`, `PrefixFBOp`,
`PrefixFCOp`, `PrefixFDOp`) and the memory and lane families (`MemOp`, `VecMemOp`,
`VecMemLaneOp`, `VecLaneOp`). Each constructor is one spec rule, with its line. The
tables are generated mechanically from the pinned SpecTec source and used by `Instr`
(`Core/Instructions.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.Binary.Core

/-! ## Opcode tables (generated from 5.3) -/

/-- Single-byte instructions without immediates (`Binstr` rules of the form `| 0xNN => instr`). -/
inductive PlainOp : UInt8 → Wasm.Instr → Prop where
  /-- `0x00 ⇒ UNREACHABLE` (5.3:8) -/
  | rx00 : PlainOp 0x00 .unreachable
  /-- `0x01 ⇒ NOP` (5.3:9) -/
  | rx01 : PlainOp 0x01 .nop
  /-- `0x1A ⇒ DROP` (5.3:10) -/
  | rx1A : PlainOp 0x1A .drop
  /-- `0x1B ⇒ SELECT` (5.3:11) -/
  | rx1B : PlainOp 0x1B (.select none)
  /-- `0x0A ⇒ THROW_REF` (5.3:41) -/
  | rx0A : PlainOp 0x0A .throwRef
  /-- `0x0F ⇒ RETURN` (5.3:45) -/
  | rx0F : PlainOp 0x0F .return_
  /-- `0xD1 ⇒ REF.IS_NULL` (5.3:141) -/
  | rxD1 : PlainOp 0xD1 .refIsNull
  /-- `0xD3 ⇒ REF.EQ` (5.3:143) -/
  | rxD3 : PlainOp 0xD3 .refEq
  /-- `0xD4 ⇒ REF.AS_NON_NULL` (5.3:144) -/
  | rxD4 : PlainOp 0xD4 .refAsNonNull
  /-- `0x45 ⇒ TESTOP I32 EQZ` (5.3:199) -/
  | rx45 : PlainOp 0x45 (.intTestOp .i32 .eqz)
  /-- `0x46 ⇒ RELOP I32 EQ` (5.3:203) -/
  | rx46 : PlainOp 0x46 (.intRelOp .i32 .eq)
  /-- `0x47 ⇒ RELOP I32 NE` (5.3:204) -/
  | rx47 : PlainOp 0x47 (.intRelOp .i32 .ne)
  /-- `0x48 ⇒ RELOP I32 LT S` (5.3:205) -/
  | rx48 : PlainOp 0x48 (.intRelOp .i32 (.lt .signed))
  /-- `0x49 ⇒ RELOP I32 LT U` (5.3:206) -/
  | rx49 : PlainOp 0x49 (.intRelOp .i32 (.lt .unsigned))
  /-- `0x4A ⇒ RELOP I32 GT S` (5.3:207) -/
  | rx4A : PlainOp 0x4A (.intRelOp .i32 (.gt .signed))
  /-- `0x4B ⇒ RELOP I32 GT U` (5.3:208) -/
  | rx4B : PlainOp 0x4B (.intRelOp .i32 (.gt .unsigned))
  /-- `0x4C ⇒ RELOP I32 LE S` (5.3:209) -/
  | rx4C : PlainOp 0x4C (.intRelOp .i32 (.le .signed))
  /-- `0x4D ⇒ RELOP I32 LE U` (5.3:210) -/
  | rx4D : PlainOp 0x4D (.intRelOp .i32 (.le .unsigned))
  /-- `0x4E ⇒ RELOP I32 GE S` (5.3:211) -/
  | rx4E : PlainOp 0x4E (.intRelOp .i32 (.ge .signed))
  /-- `0x4F ⇒ RELOP I32 GE U` (5.3:212) -/
  | rx4F : PlainOp 0x4F (.intRelOp .i32 (.ge .unsigned))
  /-- `0x50 ⇒ TESTOP I64 EQZ` (5.3:216) -/
  | rx50 : PlainOp 0x50 (.intTestOp .i64 .eqz)
  /-- `0x51 ⇒ RELOP I64 EQ` (5.3:220) -/
  | rx51 : PlainOp 0x51 (.intRelOp .i64 .eq)
  /-- `0x52 ⇒ RELOP I64 NE` (5.3:221) -/
  | rx52 : PlainOp 0x52 (.intRelOp .i64 .ne)
  /-- `0x53 ⇒ RELOP I64 LT S` (5.3:222) -/
  | rx53 : PlainOp 0x53 (.intRelOp .i64 (.lt .signed))
  /-- `0x54 ⇒ RELOP I64 LT U` (5.3:223) -/
  | rx54 : PlainOp 0x54 (.intRelOp .i64 (.lt .unsigned))
  /-- `0x55 ⇒ RELOP I64 GT S` (5.3:224) -/
  | rx55 : PlainOp 0x55 (.intRelOp .i64 (.gt .signed))
  /-- `0x56 ⇒ RELOP I64 GT U` (5.3:225) -/
  | rx56 : PlainOp 0x56 (.intRelOp .i64 (.gt .unsigned))
  /-- `0x57 ⇒ RELOP I64 LE S` (5.3:226) -/
  | rx57 : PlainOp 0x57 (.intRelOp .i64 (.le .signed))
  /-- `0x58 ⇒ RELOP I64 LE U` (5.3:227) -/
  | rx58 : PlainOp 0x58 (.intRelOp .i64 (.le .unsigned))
  /-- `0x59 ⇒ RELOP I64 GE S` (5.3:228) -/
  | rx59 : PlainOp 0x59 (.intRelOp .i64 (.ge .signed))
  /-- `0x5A ⇒ RELOP I64 GE U` (5.3:229) -/
  | rx5A : PlainOp 0x5A (.intRelOp .i64 (.ge .unsigned))
  /-- `0x5B ⇒ RELOP F32 EQ` (5.3:233) -/
  | rx5B : PlainOp 0x5B (.floatRelOp .f32 .eq)
  /-- `0x5C ⇒ RELOP F32 NE` (5.3:234) -/
  | rx5C : PlainOp 0x5C (.floatRelOp .f32 .ne)
  /-- `0x5D ⇒ RELOP F32 LT` (5.3:235) -/
  | rx5D : PlainOp 0x5D (.floatRelOp .f32 .lt)
  /-- `0x5E ⇒ RELOP F32 GT` (5.3:236) -/
  | rx5E : PlainOp 0x5E (.floatRelOp .f32 .gt)
  /-- `0x5F ⇒ RELOP F32 LE` (5.3:237) -/
  | rx5F : PlainOp 0x5F (.floatRelOp .f32 .le)
  /-- `0x60 ⇒ RELOP F32 GE` (5.3:238) -/
  | rx60 : PlainOp 0x60 (.floatRelOp .f32 .ge)
  /-- `0x61 ⇒ RELOP F64 EQ` (5.3:242) -/
  | rx61 : PlainOp 0x61 (.floatRelOp .f64 .eq)
  /-- `0x62 ⇒ RELOP F64 NE` (5.3:243) -/
  | rx62 : PlainOp 0x62 (.floatRelOp .f64 .ne)
  /-- `0x63 ⇒ RELOP F64 LT` (5.3:244) -/
  | rx63 : PlainOp 0x63 (.floatRelOp .f64 .lt)
  /-- `0x64 ⇒ RELOP F64 GT` (5.3:245) -/
  | rx64 : PlainOp 0x64 (.floatRelOp .f64 .gt)
  /-- `0x65 ⇒ RELOP F64 LE` (5.3:246) -/
  | rx65 : PlainOp 0x65 (.floatRelOp .f64 .le)
  /-- `0x66 ⇒ RELOP F64 GE` (5.3:247) -/
  | rx66 : PlainOp 0x66 (.floatRelOp .f64 .ge)
  /-- `0x67 ⇒ UNOP I32 CLZ` (5.3:251) -/
  | rx67 : PlainOp 0x67 (.intUnOp .i32 .clz)
  /-- `0x68 ⇒ UNOP I32 CTZ` (5.3:252) -/
  | rx68 : PlainOp 0x68 (.intUnOp .i32 .ctz)
  /-- `0x69 ⇒ UNOP I32 POPCNT` (5.3:253) -/
  | rx69 : PlainOp 0x69 (.intUnOp .i32 .popcnt)
  /-- `0x6A ⇒ BINOP I32 ADD` (5.3:257) -/
  | rx6A : PlainOp 0x6A (.intBinOp .i32 .add)
  /-- `0x6B ⇒ BINOP I32 SUB` (5.3:258) -/
  | rx6B : PlainOp 0x6B (.intBinOp .i32 .sub)
  /-- `0x6C ⇒ BINOP I32 MUL` (5.3:259) -/
  | rx6C : PlainOp 0x6C (.intBinOp .i32 .mul)
  /-- `0x6D ⇒ BINOP I32 DIV S` (5.3:260) -/
  | rx6D : PlainOp 0x6D (.intBinOp .i32 (.div .signed))
  /-- `0x6E ⇒ BINOP I32 DIV U` (5.3:261) -/
  | rx6E : PlainOp 0x6E (.intBinOp .i32 (.div .unsigned))
  /-- `0x6F ⇒ BINOP I32 REM S` (5.3:262) -/
  | rx6F : PlainOp 0x6F (.intBinOp .i32 (.rem .signed))
  /-- `0x70 ⇒ BINOP I32 REM U` (5.3:263) -/
  | rx70 : PlainOp 0x70 (.intBinOp .i32 (.rem .unsigned))
  /-- `0x71 ⇒ BINOP I32 AND` (5.3:264) -/
  | rx71 : PlainOp 0x71 (.intBinOp .i32 .and)
  /-- `0x72 ⇒ BINOP I32 OR` (5.3:265) -/
  | rx72 : PlainOp 0x72 (.intBinOp .i32 .or)
  /-- `0x73 ⇒ BINOP I32 XOR` (5.3:266) -/
  | rx73 : PlainOp 0x73 (.intBinOp .i32 .xor)
  /-- `0x74 ⇒ BINOP I32 SHL` (5.3:267) -/
  | rx74 : PlainOp 0x74 (.intBinOp .i32 .shl)
  /-- `0x75 ⇒ BINOP I32 SHR S` (5.3:268) -/
  | rx75 : PlainOp 0x75 (.intBinOp .i32 (.shr .signed))
  /-- `0x76 ⇒ BINOP I32 SHR U` (5.3:269) -/
  | rx76 : PlainOp 0x76 (.intBinOp .i32 (.shr .unsigned))
  /-- `0x77 ⇒ BINOP I32 ROTL` (5.3:270) -/
  | rx77 : PlainOp 0x77 (.intBinOp .i32 .rotl)
  /-- `0x78 ⇒ BINOP I32 ROTR` (5.3:271) -/
  | rx78 : PlainOp 0x78 (.intBinOp .i32 .rotr)
  /-- `0x79 ⇒ UNOP I64 CLZ` (5.3:275) -/
  | rx79 : PlainOp 0x79 (.intUnOp .i64 .clz)
  /-- `0x7A ⇒ UNOP I64 CTZ` (5.3:276) -/
  | rx7A : PlainOp 0x7A (.intUnOp .i64 .ctz)
  /-- `0x7B ⇒ UNOP I64 POPCNT` (5.3:277) -/
  | rx7B : PlainOp 0x7B (.intUnOp .i64 .popcnt)
  /-- `0xC0 ⇒ UNOP I32 EXTEND '8` (5.3:281) -/
  | rxC0 : PlainOp 0xC0 (.intUnOp .i32 (.extend .i8))
  /-- `0xC1 ⇒ UNOP I32 EXTEND '16` (5.3:282) -/
  | rxC1 : PlainOp 0xC1 (.intUnOp .i32 (.extend .i16))
  /-- `0xC2 ⇒ UNOP I64 EXTEND '8` (5.3:286) -/
  | rxC2 : PlainOp 0xC2 (.intUnOp .i64 (.extend .i8))
  /-- `0xC3 ⇒ UNOP I64 EXTEND '16` (5.3:287) -/
  | rxC3 : PlainOp 0xC3 (.intUnOp .i64 (.extend .i16))
  /-- `0xC4 ⇒ UNOP I64 EXTEND '32` (5.3:288) -/
  | rxC4 : PlainOp 0xC4 (.intUnOp .i64 (.extend .i32))
  /-- `0x7C ⇒ BINOP I64 ADD` (5.3:292) -/
  | rx7C : PlainOp 0x7C (.intBinOp .i64 .add)
  /-- `0x7D ⇒ BINOP I64 SUB` (5.3:293) -/
  | rx7D : PlainOp 0x7D (.intBinOp .i64 .sub)
  /-- `0x7E ⇒ BINOP I64 MUL` (5.3:294) -/
  | rx7E : PlainOp 0x7E (.intBinOp .i64 .mul)
  /-- `0x7F ⇒ BINOP I64 DIV S` (5.3:295) -/
  | rx7F : PlainOp 0x7F (.intBinOp .i64 (.div .signed))
  /-- `0x80 ⇒ BINOP I64 DIV U` (5.3:296) -/
  | rx80 : PlainOp 0x80 (.intBinOp .i64 (.div .unsigned))
  /-- `0x81 ⇒ BINOP I64 REM S` (5.3:297) -/
  | rx81 : PlainOp 0x81 (.intBinOp .i64 (.rem .signed))
  /-- `0x82 ⇒ BINOP I64 REM U` (5.3:298) -/
  | rx82 : PlainOp 0x82 (.intBinOp .i64 (.rem .unsigned))
  /-- `0x83 ⇒ BINOP I64 AND` (5.3:299) -/
  | rx83 : PlainOp 0x83 (.intBinOp .i64 .and)
  /-- `0x84 ⇒ BINOP I64 OR` (5.3:300) -/
  | rx84 : PlainOp 0x84 (.intBinOp .i64 .or)
  /-- `0x85 ⇒ BINOP I64 XOR` (5.3:301) -/
  | rx85 : PlainOp 0x85 (.intBinOp .i64 .xor)
  /-- `0x86 ⇒ BINOP I64 SHL` (5.3:302) -/
  | rx86 : PlainOp 0x86 (.intBinOp .i64 .shl)
  /-- `0x87 ⇒ BINOP I64 SHR S` (5.3:303) -/
  | rx87 : PlainOp 0x87 (.intBinOp .i64 (.shr .signed))
  /-- `0x88 ⇒ BINOP I64 SHR U` (5.3:304) -/
  | rx88 : PlainOp 0x88 (.intBinOp .i64 (.shr .unsigned))
  /-- `0x89 ⇒ BINOP I64 ROTL` (5.3:305) -/
  | rx89 : PlainOp 0x89 (.intBinOp .i64 .rotl)
  /-- `0x8A ⇒ BINOP I64 ROTR` (5.3:306) -/
  | rx8A : PlainOp 0x8A (.intBinOp .i64 .rotr)
  /-- `0x8B ⇒ UNOP F32 ABS` (5.3:310) -/
  | rx8B : PlainOp 0x8B (.floatUnOp .f32 .abs)
  /-- `0x8C ⇒ UNOP F32 NEG` (5.3:311) -/
  | rx8C : PlainOp 0x8C (.floatUnOp .f32 .neg)
  /-- `0x8D ⇒ UNOP F32 CEIL` (5.3:312) -/
  | rx8D : PlainOp 0x8D (.floatUnOp .f32 .ceil)
  /-- `0x8E ⇒ UNOP F32 FLOOR` (5.3:313) -/
  | rx8E : PlainOp 0x8E (.floatUnOp .f32 .floor)
  /-- `0x8F ⇒ UNOP F32 TRUNC` (5.3:314) -/
  | rx8F : PlainOp 0x8F (.floatUnOp .f32 .trunc)
  /-- `0x90 ⇒ UNOP F32 NEAREST` (5.3:315) -/
  | rx90 : PlainOp 0x90 (.floatUnOp .f32 .nearest)
  /-- `0x91 ⇒ UNOP F32 SQRT` (5.3:316) -/
  | rx91 : PlainOp 0x91 (.floatUnOp .f32 .sqrt)
  /-- `0x92 ⇒ BINOP F32 ADD` (5.3:320) -/
  | rx92 : PlainOp 0x92 (.floatBinOp .f32 .add)
  /-- `0x93 ⇒ BINOP F32 SUB` (5.3:321) -/
  | rx93 : PlainOp 0x93 (.floatBinOp .f32 .sub)
  /-- `0x94 ⇒ BINOP F32 MUL` (5.3:322) -/
  | rx94 : PlainOp 0x94 (.floatBinOp .f32 .mul)
  /-- `0x95 ⇒ BINOP F32 DIV` (5.3:323) -/
  | rx95 : PlainOp 0x95 (.floatBinOp .f32 .div)
  /-- `0x96 ⇒ BINOP F32 MIN` (5.3:324) -/
  | rx96 : PlainOp 0x96 (.floatBinOp .f32 .min)
  /-- `0x97 ⇒ BINOP F32 MAX` (5.3:325) -/
  | rx97 : PlainOp 0x97 (.floatBinOp .f32 .max)
  /-- `0x98 ⇒ BINOP F32 COPYSIGN` (5.3:326) -/
  | rx98 : PlainOp 0x98 (.floatBinOp .f32 .copysign)
  /-- `0x99 ⇒ UNOP F64 ABS` (5.3:330) -/
  | rx99 : PlainOp 0x99 (.floatUnOp .f64 .abs)
  /-- `0x9A ⇒ UNOP F64 NEG` (5.3:331) -/
  | rx9A : PlainOp 0x9A (.floatUnOp .f64 .neg)
  /-- `0x9B ⇒ UNOP F64 CEIL` (5.3:332) -/
  | rx9B : PlainOp 0x9B (.floatUnOp .f64 .ceil)
  /-- `0x9C ⇒ UNOP F64 FLOOR` (5.3:333) -/
  | rx9C : PlainOp 0x9C (.floatUnOp .f64 .floor)
  /-- `0x9D ⇒ UNOP F64 TRUNC` (5.3:334) -/
  | rx9D : PlainOp 0x9D (.floatUnOp .f64 .trunc)
  /-- `0x9E ⇒ UNOP F64 NEAREST` (5.3:335) -/
  | rx9E : PlainOp 0x9E (.floatUnOp .f64 .nearest)
  /-- `0x9F ⇒ UNOP F64 SQRT` (5.3:336) -/
  | rx9F : PlainOp 0x9F (.floatUnOp .f64 .sqrt)
  /-- `0xA0 ⇒ BINOP F64 ADD` (5.3:340) -/
  | rxA0 : PlainOp 0xA0 (.floatBinOp .f64 .add)
  /-- `0xA1 ⇒ BINOP F64 SUB` (5.3:341) -/
  | rxA1 : PlainOp 0xA1 (.floatBinOp .f64 .sub)
  /-- `0xA2 ⇒ BINOP F64 MUL` (5.3:342) -/
  | rxA2 : PlainOp 0xA2 (.floatBinOp .f64 .mul)
  /-- `0xA3 ⇒ BINOP F64 DIV` (5.3:343) -/
  | rxA3 : PlainOp 0xA3 (.floatBinOp .f64 .div)
  /-- `0xA4 ⇒ BINOP F64 MIN` (5.3:344) -/
  | rxA4 : PlainOp 0xA4 (.floatBinOp .f64 .min)
  /-- `0xA5 ⇒ BINOP F64 MAX` (5.3:345) -/
  | rxA5 : PlainOp 0xA5 (.floatBinOp .f64 .max)
  /-- `0xA6 ⇒ BINOP F64 COPYSIGN` (5.3:346) -/
  | rxA6 : PlainOp 0xA6 (.floatBinOp .f64 .copysign)
  /-- `0xA7 ⇒ CVTOP I32 I64 WRAP` (5.3:351) -/
  | rxA7 : PlainOp 0xA7 (.convert .wrap)
  /-- `0xA8 ⇒ CVTOP I32 F32 TRUNC S` (5.3:352) -/
  | rxA8 : PlainOp 0xA8 (.convert (.trunc .f32 .i32 .signed))
  /-- `0xA9 ⇒ CVTOP I32 F32 TRUNC U` (5.3:353) -/
  | rxA9 : PlainOp 0xA9 (.convert (.trunc .f32 .i32 .unsigned))
  /-- `0xAA ⇒ CVTOP I32 F64 TRUNC S` (5.3:354) -/
  | rxAA : PlainOp 0xAA (.convert (.trunc .f64 .i32 .signed))
  /-- `0xAB ⇒ CVTOP I32 F64 TRUNC U` (5.3:355) -/
  | rxAB : PlainOp 0xAB (.convert (.trunc .f64 .i32 .unsigned))
  /-- `0xAC ⇒ CVTOP I64 I32 EXTEND S` (5.3:356) -/
  | rxAC : PlainOp 0xAC (.convert (.extend .signed))
  /-- `0xAD ⇒ CVTOP I64 I32 EXTEND U` (5.3:357) -/
  | rxAD : PlainOp 0xAD (.convert (.extend .unsigned))
  /-- `0xAE ⇒ CVTOP I64 F32 TRUNC S` (5.3:358) -/
  | rxAE : PlainOp 0xAE (.convert (.trunc .f32 .i64 .signed))
  /-- `0xAF ⇒ CVTOP I64 F32 TRUNC U` (5.3:359) -/
  | rxAF : PlainOp 0xAF (.convert (.trunc .f32 .i64 .unsigned))
  /-- `0xB0 ⇒ CVTOP I64 F64 TRUNC S` (5.3:360) -/
  | rxB0 : PlainOp 0xB0 (.convert (.trunc .f64 .i64 .signed))
  /-- `0xB1 ⇒ CVTOP I64 F64 TRUNC U` (5.3:361) -/
  | rxB1 : PlainOp 0xB1 (.convert (.trunc .f64 .i64 .unsigned))
  /-- `0xB2 ⇒ CVTOP F32 I32 CONVERT S` (5.3:362) -/
  | rxB2 : PlainOp 0xB2 (.convert (.convert .i32 .f32 .signed))
  /-- `0xB3 ⇒ CVTOP F32 I32 CONVERT U` (5.3:363) -/
  | rxB3 : PlainOp 0xB3 (.convert (.convert .i32 .f32 .unsigned))
  /-- `0xB4 ⇒ CVTOP F32 I64 CONVERT S` (5.3:364) -/
  | rxB4 : PlainOp 0xB4 (.convert (.convert .i64 .f32 .signed))
  /-- `0xB5 ⇒ CVTOP F32 I64 CONVERT U` (5.3:365) -/
  | rxB5 : PlainOp 0xB5 (.convert (.convert .i64 .f32 .unsigned))
  /-- `0xB6 ⇒ CVTOP F32 F64 DEMOTE` (5.3:366) -/
  | rxB6 : PlainOp 0xB6 (.convert .demote)
  /-- `0xB7 ⇒ CVTOP F64 I32 CONVERT S` (5.3:367) -/
  | rxB7 : PlainOp 0xB7 (.convert (.convert .i32 .f64 .signed))
  /-- `0xB8 ⇒ CVTOP F64 I32 CONVERT U` (5.3:368) -/
  | rxB8 : PlainOp 0xB8 (.convert (.convert .i32 .f64 .unsigned))
  /-- `0xB9 ⇒ CVTOP F64 I64 CONVERT S` (5.3:369) -/
  | rxB9 : PlainOp 0xB9 (.convert (.convert .i64 .f64 .signed))
  /-- `0xBA ⇒ CVTOP F64 I64 CONVERT U` (5.3:370) -/
  | rxBA : PlainOp 0xBA (.convert (.convert .i64 .f64 .unsigned))
  /-- `0xBB ⇒ CVTOP F64 F32 PROMOTE` (5.3:371) -/
  | rxBB : PlainOp 0xBB (.convert .promote)
  /-- `0xBC ⇒ CVTOP I32 F32 REINTERPRET` (5.3:372) -/
  | rxBC : PlainOp 0xBC (.convert (.reinterpretInt .f32))
  /-- `0xBD ⇒ CVTOP I64 F64 REINTERPRET` (5.3:373) -/
  | rxBD : PlainOp 0xBD (.convert (.reinterpretInt .f64))
  /-- `0xBE ⇒ CVTOP F32 I32 REINTERPRET` (5.3:374) -/
  | rxBE : PlainOp 0xBE (.convert (.reinterpretFloat .i32))
  /-- `0xBF ⇒ CVTOP F64 I64 REINTERPRET` (5.3:375) -/
  | rxBF : PlainOp 0xBF (.convert (.reinterpretFloat .i64))

/-- `0xFB n:Bu32` instructions without further immediates. -/
inductive PrefixFBOp : Nat → Wasm.Instr → Prop where
  /-- `0xFB 15:Bu32 ⇒ ARRAY.LEN` (5.3:170) -/
  | r15 : PrefixFBOp 15 .arrayLen
  /-- `0xFB 26:Bu32 ⇒ ANY.CONVERT_EXTERN` (5.3:178) -/
  | r26 : PrefixFBOp 26 .anyConvertExtern
  /-- `0xFB 27:Bu32 ⇒ EXTERN.CONVERT_ANY` (5.3:179) -/
  | r27 : PrefixFBOp 27 .externConvertAny
  /-- `0xFB 28:Bu32 ⇒ REF.I31` (5.3:183) -/
  | r28 : PrefixFBOp 28 .refI31
  /-- `0xFB 29:Bu32 ⇒ I31.GET S` (5.3:184) -/
  | r29 : PrefixFBOp 29 (.i31Get .signed)
  /-- `0xFB 30:Bu32 ⇒ I31.GET U` (5.3:185) -/
  | r30 : PrefixFBOp 30 (.i31Get .unsigned)

/-- `0xFC n:Bu32` instructions without further immediates (saturating truncation). -/
inductive PrefixFCOp : Nat → Wasm.Instr → Prop where
  /-- `0xFC 0:Bu32 ⇒ CVTOP I32 F32 TRUNC_SAT S` (5.3:379) -/
  | r0 : PrefixFCOp 0 (.convert (.truncSat .f32 .i32 .signed))
  /-- `0xFC 1:Bu32 ⇒ CVTOP I32 F32 TRUNC_SAT U` (5.3:380) -/
  | r1 : PrefixFCOp 1 (.convert (.truncSat .f32 .i32 .unsigned))
  /-- `0xFC 2:Bu32 ⇒ CVTOP I32 F64 TRUNC_SAT S` (5.3:381) -/
  | r2 : PrefixFCOp 2 (.convert (.truncSat .f64 .i32 .signed))
  /-- `0xFC 3:Bu32 ⇒ CVTOP I32 F64 TRUNC_SAT U` (5.3:382) -/
  | r3 : PrefixFCOp 3 (.convert (.truncSat .f64 .i32 .unsigned))
  /-- `0xFC 4:Bu32 ⇒ CVTOP I64 F32 TRUNC_SAT S` (5.3:383) -/
  | r4 : PrefixFCOp 4 (.convert (.truncSat .f32 .i64 .signed))
  /-- `0xFC 5:Bu32 ⇒ CVTOP I64 F32 TRUNC_SAT U` (5.3:384) -/
  | r5 : PrefixFCOp 5 (.convert (.truncSat .f32 .i64 .unsigned))
  /-- `0xFC 6:Bu32 ⇒ CVTOP I64 F64 TRUNC_SAT S` (5.3:385) -/
  | r6 : PrefixFCOp 6 (.convert (.truncSat .f64 .i64 .signed))
  /-- `0xFC 7:Bu32 ⇒ CVTOP I64 F64 TRUNC_SAT U` (5.3:386) -/
  | r7 : PrefixFCOp 7 (.convert (.truncSat .f64 .i64 .unsigned))

/-- `0xFD n:Bu32` vector instructions without further immediates. -/
inductive PrefixFDOp : Nat → Wasm.Instr → Prop where
  /-- `0xFD 14:Bu32 ⇒ VSWIZZLOP (I8 X '16) SWIZZLE` (5.3:426) -/
  | r14 : PrefixFDOp 14 (.vecSwizzle .swizzle)
  /-- `0xFD 256:Bu32 ⇒ VSWIZZLOP (I8 X '16) RELAXED_SWIZZLE` (5.3:427) -/
  | r256 : PrefixFDOp 256 (.vecSwizzle .relaxedSwizzle)
  /-- `0xFD 15:Bu32 ⇒ VSPLAT (I8 X '16)` (5.3:431) -/
  | r15 : PrefixFDOp 15 (.vecSplat (.int .i8x16))
  /-- `0xFD 16:Bu32 ⇒ VSPLAT (I16 X '8)` (5.3:432) -/
  | r16 : PrefixFDOp 16 (.vecSplat (.int .i16x8))
  /-- `0xFD 17:Bu32 ⇒ VSPLAT (I32 X '4)` (5.3:433) -/
  | r17 : PrefixFDOp 17 (.vecSplat (.int .i32x4))
  /-- `0xFD 18:Bu32 ⇒ VSPLAT (I64 X '2)` (5.3:434) -/
  | r18 : PrefixFDOp 18 (.vecSplat (.int .i64x2))
  /-- `0xFD 19:Bu32 ⇒ VSPLAT (F32 X '4)` (5.3:435) -/
  | r19 : PrefixFDOp 19 (.vecSplat (.float .f32x4))
  /-- `0xFD 20:Bu32 ⇒ VSPLAT (F64 X '2)` (5.3:436) -/
  | r20 : PrefixFDOp 20 (.vecSplat (.float .f64x2))
  /-- `0xFD 35:Bu32 ⇒ VRELOP (I8 X '16) EQ` (5.3:457) -/
  | r35 : PrefixFDOp 35 (.vecIntRelOp .i8x16 .eq)
  /-- `0xFD 36:Bu32 ⇒ VRELOP (I8 X '16) NE` (5.3:458) -/
  | r36 : PrefixFDOp 36 (.vecIntRelOp .i8x16 .ne)
  /-- `0xFD 37:Bu32 ⇒ VRELOP (I8 X '16) LT S` (5.3:459) -/
  | r37 : PrefixFDOp 37 (.vecIntRelOp .i8x16 (.lt .signed))
  /-- `0xFD 38:Bu32 ⇒ VRELOP (I8 X '16) LT U` (5.3:460) -/
  | r38 : PrefixFDOp 38 (.vecIntRelOp .i8x16 (.lt .unsigned))
  /-- `0xFD 39:Bu32 ⇒ VRELOP (I8 X '16) GT S` (5.3:461) -/
  | r39 : PrefixFDOp 39 (.vecIntRelOp .i8x16 (.gt .signed))
  /-- `0xFD 40:Bu32 ⇒ VRELOP (I8 X '16) GT U` (5.3:462) -/
  | r40 : PrefixFDOp 40 (.vecIntRelOp .i8x16 (.gt .unsigned))
  /-- `0xFD 41:Bu32 ⇒ VRELOP (I8 X '16) LE S` (5.3:463) -/
  | r41 : PrefixFDOp 41 (.vecIntRelOp .i8x16 (.le .signed))
  /-- `0xFD 42:Bu32 ⇒ VRELOP (I8 X '16) LE U` (5.3:464) -/
  | r42 : PrefixFDOp 42 (.vecIntRelOp .i8x16 (.le .unsigned))
  /-- `0xFD 43:Bu32 ⇒ VRELOP (I8 X '16) GE S` (5.3:465) -/
  | r43 : PrefixFDOp 43 (.vecIntRelOp .i8x16 (.ge .signed))
  /-- `0xFD 44:Bu32 ⇒ VRELOP (I8 X '16) GE U` (5.3:466) -/
  | r44 : PrefixFDOp 44 (.vecIntRelOp .i8x16 (.ge .unsigned))
  /-- `0xFD 45:Bu32 ⇒ VRELOP (I16 X '8) EQ` (5.3:470) -/
  | r45 : PrefixFDOp 45 (.vecIntRelOp .i16x8 .eq)
  /-- `0xFD 46:Bu32 ⇒ VRELOP (I16 X '8) NE` (5.3:471) -/
  | r46 : PrefixFDOp 46 (.vecIntRelOp .i16x8 .ne)
  /-- `0xFD 47:Bu32 ⇒ VRELOP (I16 X '8) LT S` (5.3:472) -/
  | r47 : PrefixFDOp 47 (.vecIntRelOp .i16x8 (.lt .signed))
  /-- `0xFD 48:Bu32 ⇒ VRELOP (I16 X '8) LT U` (5.3:473) -/
  | r48 : PrefixFDOp 48 (.vecIntRelOp .i16x8 (.lt .unsigned))
  /-- `0xFD 49:Bu32 ⇒ VRELOP (I16 X '8) GT S` (5.3:474) -/
  | r49 : PrefixFDOp 49 (.vecIntRelOp .i16x8 (.gt .signed))
  /-- `0xFD 50:Bu32 ⇒ VRELOP (I16 X '8) GT U` (5.3:475) -/
  | r50 : PrefixFDOp 50 (.vecIntRelOp .i16x8 (.gt .unsigned))
  /-- `0xFD 51:Bu32 ⇒ VRELOP (I16 X '8) LE S` (5.3:476) -/
  | r51 : PrefixFDOp 51 (.vecIntRelOp .i16x8 (.le .signed))
  /-- `0xFD 52:Bu32 ⇒ VRELOP (I16 X '8) LE U` (5.3:477) -/
  | r52 : PrefixFDOp 52 (.vecIntRelOp .i16x8 (.le .unsigned))
  /-- `0xFD 53:Bu32 ⇒ VRELOP (I16 X '8) GE S` (5.3:478) -/
  | r53 : PrefixFDOp 53 (.vecIntRelOp .i16x8 (.ge .signed))
  /-- `0xFD 54:Bu32 ⇒ VRELOP (I16 X '8) GE U` (5.3:479) -/
  | r54 : PrefixFDOp 54 (.vecIntRelOp .i16x8 (.ge .unsigned))
  /-- `0xFD 55:Bu32 ⇒ VRELOP (I32 X '4) EQ` (5.3:483) -/
  | r55 : PrefixFDOp 55 (.vecIntRelOp .i32x4 .eq)
  /-- `0xFD 56:Bu32 ⇒ VRELOP (I32 X '4) NE` (5.3:484) -/
  | r56 : PrefixFDOp 56 (.vecIntRelOp .i32x4 .ne)
  /-- `0xFD 57:Bu32 ⇒ VRELOP (I32 X '4) LT S` (5.3:485) -/
  | r57 : PrefixFDOp 57 (.vecIntRelOp .i32x4 (.lt .signed))
  /-- `0xFD 58:Bu32 ⇒ VRELOP (I32 X '4) LT U` (5.3:486) -/
  | r58 : PrefixFDOp 58 (.vecIntRelOp .i32x4 (.lt .unsigned))
  /-- `0xFD 59:Bu32 ⇒ VRELOP (I32 X '4) GT S` (5.3:487) -/
  | r59 : PrefixFDOp 59 (.vecIntRelOp .i32x4 (.gt .signed))
  /-- `0xFD 60:Bu32 ⇒ VRELOP (I32 X '4) GT U` (5.3:488) -/
  | r60 : PrefixFDOp 60 (.vecIntRelOp .i32x4 (.gt .unsigned))
  /-- `0xFD 61:Bu32 ⇒ VRELOP (I32 X '4) LE S` (5.3:489) -/
  | r61 : PrefixFDOp 61 (.vecIntRelOp .i32x4 (.le .signed))
  /-- `0xFD 62:Bu32 ⇒ VRELOP (I32 X '4) LE U` (5.3:490) -/
  | r62 : PrefixFDOp 62 (.vecIntRelOp .i32x4 (.le .unsigned))
  /-- `0xFD 63:Bu32 ⇒ VRELOP (I32 X '4) GE S` (5.3:491) -/
  | r63 : PrefixFDOp 63 (.vecIntRelOp .i32x4 (.ge .signed))
  /-- `0xFD 64:Bu32 ⇒ VRELOP (I32 X '4) GE U` (5.3:492) -/
  | r64 : PrefixFDOp 64 (.vecIntRelOp .i32x4 (.ge .unsigned))
  /-- `0xFD 65:Bu32 ⇒ VRELOP (F32 X '4) EQ` (5.3:496) -/
  | r65 : PrefixFDOp 65 (.vecFloatRelOp .f32x4 .eq)
  /-- `0xFD 66:Bu32 ⇒ VRELOP (F32 X '4) NE` (5.3:497) -/
  | r66 : PrefixFDOp 66 (.vecFloatRelOp .f32x4 .ne)
  /-- `0xFD 67:Bu32 ⇒ VRELOP (F32 X '4) LT` (5.3:498) -/
  | r67 : PrefixFDOp 67 (.vecFloatRelOp .f32x4 .lt)
  /-- `0xFD 68:Bu32 ⇒ VRELOP (F32 X '4) GT` (5.3:499) -/
  | r68 : PrefixFDOp 68 (.vecFloatRelOp .f32x4 .gt)
  /-- `0xFD 69:Bu32 ⇒ VRELOP (F32 X '4) LE` (5.3:500) -/
  | r69 : PrefixFDOp 69 (.vecFloatRelOp .f32x4 .le)
  /-- `0xFD 70:Bu32 ⇒ VRELOP (F32 X '4) GE` (5.3:501) -/
  | r70 : PrefixFDOp 70 (.vecFloatRelOp .f32x4 .ge)
  /-- `0xFD 71:Bu32 ⇒ VRELOP (F64 X '2) EQ` (5.3:505) -/
  | r71 : PrefixFDOp 71 (.vecFloatRelOp .f64x2 .eq)
  /-- `0xFD 72:Bu32 ⇒ VRELOP (F64 X '2) NE` (5.3:506) -/
  | r72 : PrefixFDOp 72 (.vecFloatRelOp .f64x2 .ne)
  /-- `0xFD 73:Bu32 ⇒ VRELOP (F64 X '2) LT` (5.3:507) -/
  | r73 : PrefixFDOp 73 (.vecFloatRelOp .f64x2 .lt)
  /-- `0xFD 74:Bu32 ⇒ VRELOP (F64 X '2) GT` (5.3:508) -/
  | r74 : PrefixFDOp 74 (.vecFloatRelOp .f64x2 .gt)
  /-- `0xFD 75:Bu32 ⇒ VRELOP (F64 X '2) LE` (5.3:509) -/
  | r75 : PrefixFDOp 75 (.vecFloatRelOp .f64x2 .le)
  /-- `0xFD 76:Bu32 ⇒ VRELOP (F64 X '2) GE` (5.3:510) -/
  | r76 : PrefixFDOp 76 (.vecFloatRelOp .f64x2 .ge)
  /-- `0xFD 77:Bu32 ⇒ VVUNOP V128 NOT` (5.3:514) -/
  | r77 : PrefixFDOp 77 (.vecUnOp .not)
  /-- `0xFD 78:Bu32 ⇒ VVBINOP V128 AND` (5.3:518) -/
  | r78 : PrefixFDOp 78 (.vecBinOp .and)
  /-- `0xFD 79:Bu32 ⇒ VVBINOP V128 ANDNOT` (5.3:519) -/
  | r79 : PrefixFDOp 79 (.vecBinOp .andnot)
  /-- `0xFD 80:Bu32 ⇒ VVBINOP V128 OR` (5.3:520) -/
  | r80 : PrefixFDOp 80 (.vecBinOp .or)
  /-- `0xFD 81:Bu32 ⇒ VVBINOP V128 XOR` (5.3:521) -/
  | r81 : PrefixFDOp 81 (.vecBinOp .xor)
  /-- `0xFD 82:Bu32 ⇒ VVTERNOP V128 BITSELECT` (5.3:525) -/
  | r82 : PrefixFDOp 82 (.vecTernOp .bitselect)
  /-- `0xFD 83:Bu32 ⇒ VVTESTOP V128 ANY_TRUE` (5.3:529) -/
  | r83 : PrefixFDOp 83 (.vecTestOp .anyTrue)
  /-- `0xFD 96:Bu32 ⇒ VUNOP (I8 X '16) ABS` (5.3:533) -/
  | r96 : PrefixFDOp 96 (.vecIntUnOp .i8x16 .abs)
  /-- `0xFD 97:Bu32 ⇒ VUNOP (I8 X '16) NEG` (5.3:534) -/
  | r97 : PrefixFDOp 97 (.vecIntUnOp .i8x16 .neg)
  /-- `0xFD 98:Bu32 ⇒ VUNOP (I8 X '16) POPCNT` (5.3:535) -/
  | r98 : PrefixFDOp 98 (.vecIntUnOp .i8x16 .popcnt)
  /-- `0xFD 99:Bu32 ⇒ VTESTOP (I8 X '16) ALL_TRUE` (5.3:539) -/
  | r99 : PrefixFDOp 99 (.vecAllTrue .i8x16)
  /-- `0xFD 100:Bu32 ⇒ VBITMASK (I8 X '16)` (5.3:543) -/
  | r100 : PrefixFDOp 100 (.vecBitmask .i8x16)
  /-- `0xFD 101:Bu32 ⇒ VNARROW (I8 X '16) (I16 X '8) S` (5.3:547) -/
  | r101 : PrefixFDOp 101 (.vecNarrow .i16x8 .i8x16 .signed)
  /-- `0xFD 102:Bu32 ⇒ VNARROW (I8 X '16) (I16 X '8) U` (5.3:548) -/
  | r102 : PrefixFDOp 102 (.vecNarrow .i16x8 .i8x16 .unsigned)
  /-- `0xFD 107:Bu32 ⇒ VSHIFTOP (I8 X '16) SHL` (5.3:552) -/
  | r107 : PrefixFDOp 107 (.vecShiftOp .i8x16 .shl)
  /-- `0xFD 108:Bu32 ⇒ VSHIFTOP (I8 X '16) SHR S` (5.3:553) -/
  | r108 : PrefixFDOp 108 (.vecShiftOp .i8x16 (.shr .signed))
  /-- `0xFD 109:Bu32 ⇒ VSHIFTOP (I8 X '16) SHR U` (5.3:554) -/
  | r109 : PrefixFDOp 109 (.vecShiftOp .i8x16 (.shr .unsigned))
  /-- `0xFD 110:Bu32 ⇒ VBINOP (I8 X '16) ADD` (5.3:558) -/
  | r110 : PrefixFDOp 110 (.vecIntBinOp .i8x16 .add)
  /-- `0xFD 111:Bu32 ⇒ VBINOP (I8 X '16) ADD_SAT S` (5.3:559) -/
  | r111 : PrefixFDOp 111 (.vecIntBinOp .i8x16 (.addSat .signed))
  /-- `0xFD 112:Bu32 ⇒ VBINOP (I8 X '16) ADD_SAT U` (5.3:560) -/
  | r112 : PrefixFDOp 112 (.vecIntBinOp .i8x16 (.addSat .unsigned))
  /-- `0xFD 113:Bu32 ⇒ VBINOP (I8 X '16) SUB` (5.3:561) -/
  | r113 : PrefixFDOp 113 (.vecIntBinOp .i8x16 .sub)
  /-- `0xFD 114:Bu32 ⇒ VBINOP (I8 X '16) SUB_SAT S` (5.3:562) -/
  | r114 : PrefixFDOp 114 (.vecIntBinOp .i8x16 (.subSat .signed))
  /-- `0xFD 115:Bu32 ⇒ VBINOP (I8 X '16) SUB_SAT U` (5.3:563) -/
  | r115 : PrefixFDOp 115 (.vecIntBinOp .i8x16 (.subSat .unsigned))
  /-- `0xFD 118:Bu32 ⇒ VBINOP (I8 X '16) MIN S` (5.3:564) -/
  | r118 : PrefixFDOp 118 (.vecIntBinOp .i8x16 (.min .signed))
  /-- `0xFD 119:Bu32 ⇒ VBINOP (I8 X '16) MIN U` (5.3:565) -/
  | r119 : PrefixFDOp 119 (.vecIntBinOp .i8x16 (.min .unsigned))
  /-- `0xFD 120:Bu32 ⇒ VBINOP (I8 X '16) MAX S` (5.3:566) -/
  | r120 : PrefixFDOp 120 (.vecIntBinOp .i8x16 (.max .signed))
  /-- `0xFD 121:Bu32 ⇒ VBINOP (I8 X '16) MAX U` (5.3:567) -/
  | r121 : PrefixFDOp 121 (.vecIntBinOp .i8x16 (.max .unsigned))
  /-- `0xFD 123:Bu32 ⇒ VBINOP (I8 X '16) AVGR U` (5.3:568) -/
  | r123 : PrefixFDOp 123 (.vecIntBinOp .i8x16 .avgrU)
  /-- `0xFD 124:Bu32 ⇒ VEXTUNOP (I16 X '8) (I8 X '16) EXTADD_PAIRWISE S` (5.3:572) -/
  | r124 : PrefixFDOp 124 (.vecExtUnOp .i8x16 .i16x8 (.extaddPairwise .signed))
  /-- `0xFD 125:Bu32 ⇒ VEXTUNOP (I16 X '8) (I8 X '16) EXTADD_PAIRWISE U` (5.3:573) -/
  | r125 : PrefixFDOp 125 (.vecExtUnOp .i8x16 .i16x8 (.extaddPairwise .unsigned))
  /-- `0xFD 128:Bu32 ⇒ VUNOP (I16 X '8) ABS` (5.3:577) -/
  | r128 : PrefixFDOp 128 (.vecIntUnOp .i16x8 .abs)
  /-- `0xFD 129:Bu32 ⇒ VUNOP (I16 X '8) NEG` (5.3:578) -/
  | r129 : PrefixFDOp 129 (.vecIntUnOp .i16x8 .neg)
  /-- `0xFD 130:Bu32 ⇒ VBINOP (I16 X '8) Q15MULR_SAT S` (5.3:582) -/
  | r130 : PrefixFDOp 130 (.vecIntBinOp .i16x8 .q15mulrSatS)
  /-- `0xFD 142:Bu32 ⇒ VBINOP (I16 X '8) ADD` (5.3:583) -/
  | r142 : PrefixFDOp 142 (.vecIntBinOp .i16x8 .add)
  /-- `0xFD 143:Bu32 ⇒ VBINOP (I16 X '8) ADD_SAT S` (5.3:584) -/
  | r143 : PrefixFDOp 143 (.vecIntBinOp .i16x8 (.addSat .signed))
  /-- `0xFD 144:Bu32 ⇒ VBINOP (I16 X '8) ADD_SAT U` (5.3:585) -/
  | r144 : PrefixFDOp 144 (.vecIntBinOp .i16x8 (.addSat .unsigned))
  /-- `0xFD 145:Bu32 ⇒ VBINOP (I16 X '8) SUB` (5.3:586) -/
  | r145 : PrefixFDOp 145 (.vecIntBinOp .i16x8 .sub)
  /-- `0xFD 146:Bu32 ⇒ VBINOP (I16 X '8) SUB_SAT S` (5.3:587) -/
  | r146 : PrefixFDOp 146 (.vecIntBinOp .i16x8 (.subSat .signed))
  /-- `0xFD 147:Bu32 ⇒ VBINOP (I16 X '8) SUB_SAT U` (5.3:588) -/
  | r147 : PrefixFDOp 147 (.vecIntBinOp .i16x8 (.subSat .unsigned))
  /-- `0xFD 149:Bu32 ⇒ VBINOP (I16 X '8) MUL` (5.3:589) -/
  | r149 : PrefixFDOp 149 (.vecIntBinOp .i16x8 .mul)
  /-- `0xFD 150:Bu32 ⇒ VBINOP (I16 X '8) MIN S` (5.3:590) -/
  | r150 : PrefixFDOp 150 (.vecIntBinOp .i16x8 (.min .signed))
  /-- `0xFD 151:Bu32 ⇒ VBINOP (I16 X '8) MIN U` (5.3:591) -/
  | r151 : PrefixFDOp 151 (.vecIntBinOp .i16x8 (.min .unsigned))
  /-- `0xFD 152:Bu32 ⇒ VBINOP (I16 X '8) MAX S` (5.3:592) -/
  | r152 : PrefixFDOp 152 (.vecIntBinOp .i16x8 (.max .signed))
  /-- `0xFD 153:Bu32 ⇒ VBINOP (I16 X '8) MAX U` (5.3:593) -/
  | r153 : PrefixFDOp 153 (.vecIntBinOp .i16x8 (.max .unsigned))
  /-- `0xFD 155:Bu32 ⇒ VBINOP (I16 X '8) AVGR U` (5.3:594) -/
  | r155 : PrefixFDOp 155 (.vecIntBinOp .i16x8 .avgrU)
  /-- `0xFD 273:Bu32 ⇒ VBINOP (I16 X '8) RELAXED_Q15MULR S` (5.3:595) -/
  | r273 : PrefixFDOp 273 (.vecIntBinOp .i16x8 .relaxedQ15mulrS)
  /-- `0xFD 131:Bu32 ⇒ VTESTOP (I16 X '8) ALL_TRUE` (5.3:599) -/
  | r131 : PrefixFDOp 131 (.vecAllTrue .i16x8)
  /-- `0xFD 132:Bu32 ⇒ VBITMASK (I16 X '8)` (5.3:603) -/
  | r132 : PrefixFDOp 132 (.vecBitmask .i16x8)
  /-- `0xFD 133:Bu32 ⇒ VNARROW (I16 X '8) (I32 X '4) S` (5.3:607) -/
  | r133 : PrefixFDOp 133 (.vecNarrow .i32x4 .i16x8 .signed)
  /-- `0xFD 134:Bu32 ⇒ VNARROW (I16 X '8) (I32 X '4) U` (5.3:608) -/
  | r134 : PrefixFDOp 134 (.vecNarrow .i32x4 .i16x8 .unsigned)
  /-- `0xFD 135:Bu32 ⇒ VCVTOP (I16 X '8) (I8 X '16) EXTEND LOW S` (5.3:612) -/
  | r135 : PrefixFDOp 135 (.vecConvert (.int .i8x16) (.int .i16x8) (.extend .low .signed))
  /-- `0xFD 136:Bu32 ⇒ VCVTOP (I16 X '8) (I8 X '16) EXTEND HIGH S` (5.3:613) -/
  | r136 : PrefixFDOp 136 (.vecConvert (.int .i8x16) (.int .i16x8) (.extend .high .signed))
  /-- `0xFD 137:Bu32 ⇒ VCVTOP (I16 X '8) (I8 X '16) EXTEND LOW U` (5.3:614) -/
  | r137 : PrefixFDOp 137 (.vecConvert (.int .i8x16) (.int .i16x8) (.extend .low .unsigned))
  /-- `0xFD 138:Bu32 ⇒ VCVTOP (I16 X '8) (I8 X '16) EXTEND HIGH U` (5.3:615) -/
  | r138 : PrefixFDOp 138 (.vecConvert (.int .i8x16) (.int .i16x8) (.extend .high .unsigned))
  /-- `0xFD 139:Bu32 ⇒ VSHIFTOP (I16 X '8) SHL` (5.3:619) -/
  | r139 : PrefixFDOp 139 (.vecShiftOp .i16x8 .shl)
  /-- `0xFD 140:Bu32 ⇒ VSHIFTOP (I16 X '8) SHR S` (5.3:620) -/
  | r140 : PrefixFDOp 140 (.vecShiftOp .i16x8 (.shr .signed))
  /-- `0xFD 141:Bu32 ⇒ VSHIFTOP (I16 X '8) SHR U` (5.3:621) -/
  | r141 : PrefixFDOp 141 (.vecShiftOp .i16x8 (.shr .unsigned))
  /-- `0xFD 156:Bu32 ⇒ VEXTBINOP (I16 X '8) (I8 X '16) EXTMUL LOW S` (5.3:625) -/
  | r156 : PrefixFDOp 156 (.vecExtBinOp .i8x16 .i16x8 (.extmul .low .signed))
  /-- `0xFD 157:Bu32 ⇒ VEXTBINOP (I16 X '8) (I8 X '16) EXTMUL HIGH S` (5.3:626) -/
  | r157 : PrefixFDOp 157 (.vecExtBinOp .i8x16 .i16x8 (.extmul .high .signed))
  /-- `0xFD 158:Bu32 ⇒ VEXTBINOP (I16 X '8) (I8 X '16) EXTMUL LOW U` (5.3:627) -/
  | r158 : PrefixFDOp 158 (.vecExtBinOp .i8x16 .i16x8 (.extmul .low .unsigned))
  /-- `0xFD 159:Bu32 ⇒ VEXTBINOP (I16 X '8) (I8 X '16) EXTMUL HIGH U` (5.3:628) -/
  | r159 : PrefixFDOp 159 (.vecExtBinOp .i8x16 .i16x8 (.extmul .high .unsigned))
  /-- `0xFD 274:Bu32 ⇒ VEXTBINOP (I16 X '8) (I8 X '16) RELAXED_DOT S` (5.3:629) -/
  | r274 : PrefixFDOp 274 (.vecExtBinOp .i8x16 .i16x8 .relaxedDotS)
  /-- `0xFD 126:Bu32 ⇒ VEXTUNOP (I32 X '4) (I16 X '8) EXTADD_PAIRWISE S` (5.3:633) -/
  | r126 : PrefixFDOp 126 (.vecExtUnOp .i16x8 .i32x4 (.extaddPairwise .signed))
  /-- `0xFD 127:Bu32 ⇒ VEXTUNOP (I32 X '4) (I16 X '8) EXTADD_PAIRWISE U` (5.3:634) -/
  | r127 : PrefixFDOp 127 (.vecExtUnOp .i16x8 .i32x4 (.extaddPairwise .unsigned))
  /-- `0xFD 160:Bu32 ⇒ VUNOP (I32 X '4) ABS` (5.3:638) -/
  | r160 : PrefixFDOp 160 (.vecIntUnOp .i32x4 .abs)
  /-- `0xFD 161:Bu32 ⇒ VUNOP (I32 X '4) NEG` (5.3:639) -/
  | r161 : PrefixFDOp 161 (.vecIntUnOp .i32x4 .neg)
  /-- `0xFD 163:Bu32 ⇒ VTESTOP (I32 X '4) ALL_TRUE` (5.3:643) -/
  | r163 : PrefixFDOp 163 (.vecAllTrue .i32x4)
  /-- `0xFD 164:Bu32 ⇒ VBITMASK (I32 X '4)` (5.3:647) -/
  | r164 : PrefixFDOp 164 (.vecBitmask .i32x4)
  /-- `0xFD 167:Bu32 ⇒ VCVTOP (I32 X '4) (I16 X '8) EXTEND LOW S` (5.3:651) -/
  | r167 : PrefixFDOp 167 (.vecConvert (.int .i16x8) (.int .i32x4) (.extend .low .signed))
  /-- `0xFD 168:Bu32 ⇒ VCVTOP (I32 X '4) (I16 X '8) EXTEND HIGH S` (5.3:652) -/
  | r168 : PrefixFDOp 168 (.vecConvert (.int .i16x8) (.int .i32x4) (.extend .high .signed))
  /-- `0xFD 169:Bu32 ⇒ VCVTOP (I32 X '4) (I16 X '8) EXTEND LOW U` (5.3:653) -/
  | r169 : PrefixFDOp 169 (.vecConvert (.int .i16x8) (.int .i32x4) (.extend .low .unsigned))
  /-- `0xFD 170:Bu32 ⇒ VCVTOP (I32 X '4) (I16 X '8) EXTEND HIGH U` (5.3:654) -/
  | r170 : PrefixFDOp 170 (.vecConvert (.int .i16x8) (.int .i32x4) (.extend .high .unsigned))
  /-- `0xFD 171:Bu32 ⇒ VSHIFTOP (I32 X '4) SHL` (5.3:658) -/
  | r171 : PrefixFDOp 171 (.vecShiftOp .i32x4 .shl)
  /-- `0xFD 172:Bu32 ⇒ VSHIFTOP (I32 X '4) (SHR S)` (5.3:659) -/
  | r172 : PrefixFDOp 172 (.vecShiftOp .i32x4 (.shr .signed))
  /-- `0xFD 173:Bu32 ⇒ VSHIFTOP (I32 X '4) (SHR U)` (5.3:660) -/
  | r173 : PrefixFDOp 173 (.vecShiftOp .i32x4 (.shr .unsigned))
  /-- `0xFD 174:Bu32 ⇒ VBINOP (I32 X '4) ADD` (5.3:664) -/
  | r174 : PrefixFDOp 174 (.vecIntBinOp .i32x4 .add)
  /-- `0xFD 177:Bu32 ⇒ VBINOP (I32 X '4) SUB` (5.3:665) -/
  | r177 : PrefixFDOp 177 (.vecIntBinOp .i32x4 .sub)
  /-- `0xFD 181:Bu32 ⇒ VBINOP (I32 X '4) MUL` (5.3:666) -/
  | r181 : PrefixFDOp 181 (.vecIntBinOp .i32x4 .mul)
  /-- `0xFD 182:Bu32 ⇒ VBINOP (I32 X '4) MIN S` (5.3:667) -/
  | r182 : PrefixFDOp 182 (.vecIntBinOp .i32x4 (.min .signed))
  /-- `0xFD 183:Bu32 ⇒ VBINOP (I32 X '4) MIN U` (5.3:668) -/
  | r183 : PrefixFDOp 183 (.vecIntBinOp .i32x4 (.min .unsigned))
  /-- `0xFD 184:Bu32 ⇒ VBINOP (I32 X '4) MAX S` (5.3:669) -/
  | r184 : PrefixFDOp 184 (.vecIntBinOp .i32x4 (.max .signed))
  /-- `0xFD 185:Bu32 ⇒ VBINOP (I32 X '4) MAX U` (5.3:670) -/
  | r185 : PrefixFDOp 185 (.vecIntBinOp .i32x4 (.max .unsigned))
  /-- `0xFD 186:Bu32 ⇒ VEXTBINOP (I32 X '4) (I16 X '8) DOT S` (5.3:674) -/
  | r186 : PrefixFDOp 186 (.vecExtBinOp .i16x8 .i32x4 .dotS)
  /-- `0xFD 188:Bu32 ⇒ VEXTBINOP (I32 X '4) (I16 X '8) EXTMUL LOW S` (5.3:675) -/
  | r188 : PrefixFDOp 188 (.vecExtBinOp .i16x8 .i32x4 (.extmul .low .signed))
  /-- `0xFD 189:Bu32 ⇒ VEXTBINOP (I32 X '4) (I16 X '8) EXTMUL HIGH S` (5.3:676) -/
  | r189 : PrefixFDOp 189 (.vecExtBinOp .i16x8 .i32x4 (.extmul .high .signed))
  /-- `0xFD 190:Bu32 ⇒ VEXTBINOP (I32 X '4) (I16 X '8) EXTMUL LOW U` (5.3:677) -/
  | r190 : PrefixFDOp 190 (.vecExtBinOp .i16x8 .i32x4 (.extmul .low .unsigned))
  /-- `0xFD 191:Bu32 ⇒ VEXTBINOP (I32 X '4) (I16 X '8) EXTMUL HIGH U` (5.3:678) -/
  | r191 : PrefixFDOp 191 (.vecExtBinOp .i16x8 .i32x4 (.extmul .high .unsigned))
  /-- `0xFD 275:Bu32 ⇒ VEXTTERNOP (I32 X '4) (I8 X '16) RELAXED_DOT_ADD S` (5.3:682) -/
  | r275 : PrefixFDOp 275 (.vecExtTernOp .i8x16 .i32x4 .relaxedDotAddS)
  /-- `0xFD 192:Bu32 ⇒ VUNOP (I64 X '2) ABS` (5.3:686) -/
  | r192 : PrefixFDOp 192 (.vecIntUnOp .i64x2 .abs)
  /-- `0xFD 193:Bu32 ⇒ VUNOP (I64 X '2) NEG` (5.3:687) -/
  | r193 : PrefixFDOp 193 (.vecIntUnOp .i64x2 .neg)
  /-- `0xFD 195:Bu32 ⇒ VTESTOP (I64 X '2) ALL_TRUE` (5.3:691) -/
  | r195 : PrefixFDOp 195 (.vecAllTrue .i64x2)
  /-- `0xFD 196:Bu32 ⇒ VBITMASK (I64 X '2)` (5.3:695) -/
  | r196 : PrefixFDOp 196 (.vecBitmask .i64x2)
  /-- `0xFD 199:Bu32 ⇒ VCVTOP (I64 X '2) (I32 X '4) EXTEND LOW S` (5.3:699) -/
  | r199 : PrefixFDOp 199 (.vecConvert (.int .i32x4) (.int .i64x2) (.extend .low .signed))
  /-- `0xFD 200:Bu32 ⇒ VCVTOP (I64 X '2) (I32 X '4) EXTEND HIGH S` (5.3:700) -/
  | r200 : PrefixFDOp 200 (.vecConvert (.int .i32x4) (.int .i64x2) (.extend .high .signed))
  /-- `0xFD 201:Bu32 ⇒ VCVTOP (I64 X '2) (I32 X '4) EXTEND LOW U` (5.3:701) -/
  | r201 : PrefixFDOp 201 (.vecConvert (.int .i32x4) (.int .i64x2) (.extend .low .unsigned))
  /-- `0xFD 202:Bu32 ⇒ VCVTOP (I64 X '2) (I32 X '4) EXTEND HIGH U` (5.3:702) -/
  | r202 : PrefixFDOp 202 (.vecConvert (.int .i32x4) (.int .i64x2) (.extend .high .unsigned))
  /-- `0xFD 203:Bu32 ⇒ VSHIFTOP (I64 X '2) SHL` (5.3:706) -/
  | r203 : PrefixFDOp 203 (.vecShiftOp .i64x2 .shl)
  /-- `0xFD 204:Bu32 ⇒ VSHIFTOP (I64 X '2) (SHR S)` (5.3:707) -/
  | r204 : PrefixFDOp 204 (.vecShiftOp .i64x2 (.shr .signed))
  /-- `0xFD 205:Bu32 ⇒ VSHIFTOP (I64 X '2) (SHR U)` (5.3:708) -/
  | r205 : PrefixFDOp 205 (.vecShiftOp .i64x2 (.shr .unsigned))
  /-- `0xFD 206:Bu32 ⇒ VBINOP (I64 X '2) ADD` (5.3:712) -/
  | r206 : PrefixFDOp 206 (.vecIntBinOp .i64x2 .add)
  /-- `0xFD 209:Bu32 ⇒ VBINOP (I64 X '2) SUB` (5.3:713) -/
  | r209 : PrefixFDOp 209 (.vecIntBinOp .i64x2 .sub)
  /-- `0xFD 213:Bu32 ⇒ VBINOP (I64 X '2) MUL` (5.3:714) -/
  | r213 : PrefixFDOp 213 (.vecIntBinOp .i64x2 .mul)
  /-- `0xFD 214:Bu32 ⇒ VRELOP (I64 X '2) EQ` (5.3:718) -/
  | r214 : PrefixFDOp 214 (.vecIntRelOp .i64x2 .eq)
  /-- `0xFD 215:Bu32 ⇒ VRELOP (I64 X '2) NE` (5.3:719) -/
  | r215 : PrefixFDOp 215 (.vecIntRelOp .i64x2 .ne)
  /-- `0xFD 216:Bu32 ⇒ VRELOP (I64 X '2) (LT S)` (5.3:720) -/
  | r216 : PrefixFDOp 216 (.vecIntRelOp .i64x2 (.lt .signed))
  /-- `0xFD 217:Bu32 ⇒ VRELOP (I64 X '2) (GT S)` (5.3:721) -/
  | r217 : PrefixFDOp 217 (.vecIntRelOp .i64x2 (.gt .signed))
  /-- `0xFD 218:Bu32 ⇒ VRELOP (I64 X '2) (LE S)` (5.3:722) -/
  | r218 : PrefixFDOp 218 (.vecIntRelOp .i64x2 (.le .signed))
  /-- `0xFD 219:Bu32 ⇒ VRELOP (I64 X '2) (GE S)` (5.3:723) -/
  | r219 : PrefixFDOp 219 (.vecIntRelOp .i64x2 (.ge .signed))
  /-- `0xFD 220:Bu32 ⇒ VEXTBINOP (I64 X '2) (I32 X '4) EXTMUL LOW S` (5.3:727) -/
  | r220 : PrefixFDOp 220 (.vecExtBinOp .i32x4 .i64x2 (.extmul .low .signed))
  /-- `0xFD 221:Bu32 ⇒ VEXTBINOP (I64 X '2) (I32 X '4) EXTMUL HIGH S` (5.3:728) -/
  | r221 : PrefixFDOp 221 (.vecExtBinOp .i32x4 .i64x2 (.extmul .high .signed))
  /-- `0xFD 222:Bu32 ⇒ VEXTBINOP (I64 X '2) (I32 X '4) EXTMUL LOW U` (5.3:729) -/
  | r222 : PrefixFDOp 222 (.vecExtBinOp .i32x4 .i64x2 (.extmul .low .unsigned))
  /-- `0xFD 223:Bu32 ⇒ VEXTBINOP (I64 X '2) (I32 X '4) EXTMUL HIGH U` (5.3:730) -/
  | r223 : PrefixFDOp 223 (.vecExtBinOp .i32x4 .i64x2 (.extmul .high .unsigned))
  /-- `0xFD 103:Bu32 ⇒ VUNOP (F32 X '4) CEIL` (5.3:734) -/
  | r103 : PrefixFDOp 103 (.vecFloatUnOp .f32x4 .ceil)
  /-- `0xFD 104:Bu32 ⇒ VUNOP (F32 X '4) FLOOR` (5.3:735) -/
  | r104 : PrefixFDOp 104 (.vecFloatUnOp .f32x4 .floor)
  /-- `0xFD 105:Bu32 ⇒ VUNOP (F32 X '4) TRUNC` (5.3:736) -/
  | r105 : PrefixFDOp 105 (.vecFloatUnOp .f32x4 .trunc)
  /-- `0xFD 106:Bu32 ⇒ VUNOP (F32 X '4) NEAREST` (5.3:737) -/
  | r106 : PrefixFDOp 106 (.vecFloatUnOp .f32x4 .nearest)
  /-- `0xFD 224:Bu32 ⇒ VUNOP (F32 X '4) ABS` (5.3:738) -/
  | r224 : PrefixFDOp 224 (.vecFloatUnOp .f32x4 .abs)
  /-- `0xFD 225:Bu32 ⇒ VUNOP (F32 X '4) NEG` (5.3:739) -/
  | r225 : PrefixFDOp 225 (.vecFloatUnOp .f32x4 .neg)
  /-- `0xFD 227:Bu32 ⇒ VUNOP (F32 X '4) SQRT` (5.3:740) -/
  | r227 : PrefixFDOp 227 (.vecFloatUnOp .f32x4 .sqrt)
  /-- `0xFD 228:Bu32 ⇒ VBINOP (F32 X '4) ADD` (5.3:744) -/
  | r228 : PrefixFDOp 228 (.vecFloatBinOp .f32x4 .add)
  /-- `0xFD 229:Bu32 ⇒ VBINOP (F32 X '4) SUB` (5.3:745) -/
  | r229 : PrefixFDOp 229 (.vecFloatBinOp .f32x4 .sub)
  /-- `0xFD 230:Bu32 ⇒ VBINOP (F32 X '4) MUL` (5.3:746) -/
  | r230 : PrefixFDOp 230 (.vecFloatBinOp .f32x4 .mul)
  /-- `0xFD 231:Bu32 ⇒ VBINOP (F32 X '4) DIV` (5.3:747) -/
  | r231 : PrefixFDOp 231 (.vecFloatBinOp .f32x4 .div)
  /-- `0xFD 232:Bu32 ⇒ VBINOP (F32 X '4) MIN` (5.3:748) -/
  | r232 : PrefixFDOp 232 (.vecFloatBinOp .f32x4 .min)
  /-- `0xFD 233:Bu32 ⇒ VBINOP (F32 X '4) MAX` (5.3:749) -/
  | r233 : PrefixFDOp 233 (.vecFloatBinOp .f32x4 .max)
  /-- `0xFD 234:Bu32 ⇒ VBINOP (F32 X '4) PMIN` (5.3:750) -/
  | r234 : PrefixFDOp 234 (.vecFloatBinOp .f32x4 .pmin)
  /-- `0xFD 235:Bu32 ⇒ VBINOP (F32 X '4) PMAX` (5.3:751) -/
  | r235 : PrefixFDOp 235 (.vecFloatBinOp .f32x4 .pmax)
  /-- `0xFD 269:Bu32 ⇒ VBINOP (F32 X '4) RELAXED_MIN` (5.3:752) -/
  | r269 : PrefixFDOp 269 (.vecFloatBinOp .f32x4 .relaxedMin)
  /-- `0xFD 270:Bu32 ⇒ VBINOP (F32 X '4) RELAXED_MAX` (5.3:753) -/
  | r270 : PrefixFDOp 270 (.vecFloatBinOp .f32x4 .relaxedMax)
  /-- `0xFD 261:Bu32 ⇒ VTERNOP (F32 X '4) RELAXED_MADD` (5.3:757) -/
  | r261 : PrefixFDOp 261 (.vecFloatTernOp .f32x4 .relaxedMadd)
  /-- `0xFD 262:Bu32 ⇒ VTERNOP (F32 X '4) RELAXED_NMADD` (5.3:758) -/
  | r262 : PrefixFDOp 262 (.vecFloatTernOp .f32x4 .relaxedNmadd)
  /-- `0xFD 116:Bu32 ⇒ VUNOP (F64 X '2) CEIL` (5.3:762) -/
  | r116 : PrefixFDOp 116 (.vecFloatUnOp .f64x2 .ceil)
  /-- `0xFD 117:Bu32 ⇒ VUNOP (F64 X '2) FLOOR` (5.3:763) -/
  | r117 : PrefixFDOp 117 (.vecFloatUnOp .f64x2 .floor)
  /-- `0xFD 122:Bu32 ⇒ VUNOP (F64 X '2) TRUNC` (5.3:764) -/
  | r122 : PrefixFDOp 122 (.vecFloatUnOp .f64x2 .trunc)
  /-- `0xFD 148:Bu32 ⇒ VUNOP (F64 X '2) NEAREST` (5.3:765) -/
  | r148 : PrefixFDOp 148 (.vecFloatUnOp .f64x2 .nearest)
  /-- `0xFD 236:Bu32 ⇒ VUNOP (F64 X '2) ABS` (5.3:766) -/
  | r236 : PrefixFDOp 236 (.vecFloatUnOp .f64x2 .abs)
  /-- `0xFD 237:Bu32 ⇒ VUNOP (F64 X '2) NEG` (5.3:767) -/
  | r237 : PrefixFDOp 237 (.vecFloatUnOp .f64x2 .neg)
  /-- `0xFD 239:Bu32 ⇒ VUNOP (F64 X '2) SQRT` (5.3:768) -/
  | r239 : PrefixFDOp 239 (.vecFloatUnOp .f64x2 .sqrt)
  /-- `0xFD 240:Bu32 ⇒ VBINOP (F64 X '2) ADD` (5.3:772) -/
  | r240 : PrefixFDOp 240 (.vecFloatBinOp .f64x2 .add)
  /-- `0xFD 241:Bu32 ⇒ VBINOP (F64 X '2) SUB` (5.3:773) -/
  | r241 : PrefixFDOp 241 (.vecFloatBinOp .f64x2 .sub)
  /-- `0xFD 242:Bu32 ⇒ VBINOP (F64 X '2) MUL` (5.3:774) -/
  | r242 : PrefixFDOp 242 (.vecFloatBinOp .f64x2 .mul)
  /-- `0xFD 243:Bu32 ⇒ VBINOP (F64 X '2) DIV` (5.3:775) -/
  | r243 : PrefixFDOp 243 (.vecFloatBinOp .f64x2 .div)
  /-- `0xFD 244:Bu32 ⇒ VBINOP (F64 X '2) MIN` (5.3:776) -/
  | r244 : PrefixFDOp 244 (.vecFloatBinOp .f64x2 .min)
  /-- `0xFD 245:Bu32 ⇒ VBINOP (F64 X '2) MAX` (5.3:777) -/
  | r245 : PrefixFDOp 245 (.vecFloatBinOp .f64x2 .max)
  /-- `0xFD 246:Bu32 ⇒ VBINOP (F64 X '2) PMIN` (5.3:778) -/
  | r246 : PrefixFDOp 246 (.vecFloatBinOp .f64x2 .pmin)
  /-- `0xFD 247:Bu32 ⇒ VBINOP (F64 X '2) PMAX` (5.3:779) -/
  | r247 : PrefixFDOp 247 (.vecFloatBinOp .f64x2 .pmax)
  /-- `0xFD 271:Bu32 ⇒ VBINOP (F64 X '2) RELAXED_MIN` (5.3:780) -/
  | r271 : PrefixFDOp 271 (.vecFloatBinOp .f64x2 .relaxedMin)
  /-- `0xFD 272:Bu32 ⇒ VBINOP (F64 X '2) RELAXED_MAX` (5.3:781) -/
  | r272 : PrefixFDOp 272 (.vecFloatBinOp .f64x2 .relaxedMax)
  /-- `0xFD 263:Bu32 ⇒ VTERNOP (F64 X '2) RELAXED_MADD` (5.3:785) -/
  | r263 : PrefixFDOp 263 (.vecFloatTernOp .f64x2 .relaxedMadd)
  /-- `0xFD 264:Bu32 ⇒ VTERNOP (F64 X '2) RELAXED_NMADD` (5.3:786) -/
  | r264 : PrefixFDOp 264 (.vecFloatTernOp .f64x2 .relaxedNmadd)
  /-- `0xFD 265:Bu32 ⇒ VTERNOP (I8 X '16) RELAXED_LANESELECT` (5.3:787) -/
  | r265 : PrefixFDOp 265 (.vecIntTernOp .i8x16 .relaxedLaneSelect)
  /-- `0xFD 266:Bu32 ⇒ VTERNOP (I16 X '8) RELAXED_LANESELECT` (5.3:788) -/
  | r266 : PrefixFDOp 266 (.vecIntTernOp .i16x8 .relaxedLaneSelect)
  /-- `0xFD 267:Bu32 ⇒ VTERNOP (I32 X '4) RELAXED_LANESELECT` (5.3:789) -/
  | r267 : PrefixFDOp 267 (.vecIntTernOp .i32x4 .relaxedLaneSelect)
  /-- `0xFD 268:Bu32 ⇒ VTERNOP (I64 X '2) RELAXED_LANESELECT` (5.3:790) -/
  | r268 : PrefixFDOp 268 (.vecIntTernOp .i64x2 .relaxedLaneSelect)
  /-- `0xFD 94:Bu32 ⇒ VCVTOP (F32 X '4) (F64 X '2) DEMOTE ZERO` (5.3:794) -/
  | r94 : PrefixFDOp 94 (.vecConvert (.float .f64x2) (.float .f32x4) .demoteZero)
  /-- `0xFD 95:Bu32 ⇒ VCVTOP (F64 X '2) (F32 X '4) PROMOTE LOW` (5.3:795) -/
  | r95 : PrefixFDOp 95 (.vecConvert (.float .f32x4) (.float .f64x2) .promoteLow)
  /-- `0xFD 248:Bu32 ⇒ VCVTOP (I32 X '4) (F32 X '4) TRUNC_SAT S` (5.3:796) -/
  | r248 : PrefixFDOp 248 (.vecConvert (.float .f32x4) (.int .i32x4) (.truncSat .signed false))
  /-- `0xFD 249:Bu32 ⇒ VCVTOP (I32 X '4) (F32 X '4) TRUNC_SAT U` (5.3:797) -/
  | r249 : PrefixFDOp 249 (.vecConvert (.float .f32x4) (.int .i32x4) (.truncSat .unsigned false))
  /-- `0xFD 250:Bu32 ⇒ VCVTOP (F32 X '4) (I32 X '4) CONVERT S` (5.3:798) -/
  | r250 : PrefixFDOp 250 (.vecConvert (.int .i32x4) (.float .f32x4) (.convert none .signed))
  /-- `0xFD 251:Bu32 ⇒ VCVTOP (F32 X '4) (I32 X '4) CONVERT U` (5.3:799) -/
  | r251 : PrefixFDOp 251 (.vecConvert (.int .i32x4) (.float .f32x4) (.convert none .unsigned))
  /-- `0xFD 252:Bu32 ⇒ VCVTOP (I32 X '4) (F64 X '2) TRUNC_SAT S ZERO` (5.3:800) -/
  | r252 : PrefixFDOp 252 (.vecConvert (.float .f64x2) (.int .i32x4) (.truncSat .signed true))
  /-- `0xFD 253:Bu32 ⇒ VCVTOP (I32 X '4) (F64 X '2) TRUNC_SAT U ZERO` (5.3:801) -/
  | r253 : PrefixFDOp 253 (.vecConvert (.float .f64x2) (.int .i32x4) (.truncSat .unsigned true))
  /-- `0xFD 254:Bu32 ⇒ VCVTOP (F64 X '2) (I32 X '4) CONVERT LOW S` (5.3:802) -/
  | r254 : PrefixFDOp 254 (.vecConvert (.int .i32x4) (.float .f64x2) (.convert (some .low) .signed))
  /-- `0xFD 255:Bu32 ⇒ VCVTOP (F64 X '2) (I32 X '4) CONVERT LOW U` (5.3:803) -/
  | r255 : PrefixFDOp 255 (.vecConvert (.int .i32x4) (.float .f64x2) (.convert
      (some .low) .unsigned))
  /-- `0xFD 257:Bu32 ⇒ VCVTOP (I32 X '4) (F32 X '4) RELAXED_TRUNC S` (5.3:804) -/
  | r257 : PrefixFDOp 257 (.vecConvert (.float .f32x4) (.int .i32x4) (.relaxedTrunc .signed false))
  /-- `0xFD 258:Bu32 ⇒ VCVTOP (I32 X '4) (F32 X '4) RELAXED_TRUNC U` (5.3:805) -/
  | r258 : PrefixFDOp 258 (.vecConvert (.float .f32x4) (.int .i32x4)
      (.relaxedTrunc .unsigned false))
  /-- `0xFD 259:Bu32 ⇒ VCVTOP (I32 X '4) (F64 X '2) RELAXED_TRUNC S ZERO` (5.3:806) -/
  | r259 : PrefixFDOp 259 (.vecConvert (.float .f64x2) (.int .i32x4) (.relaxedTrunc .signed true))
  /-- `0xFD 260:Bu32 ⇒ VCVTOP (I32 X '4) (F64 X '2) RELAXED_TRUNC U ZERO` (5.3:807) -/
  | r260 : PrefixFDOp 260 (.vecConvert (.float .f64x2) (.int .i32x4) (.relaxedTrunc .unsigned true))

/-- Scalar loads and stores: `| 0xNN (x,ao):Bmemarg => ...`. -/
inductive MemOp : UInt8 → (MemIdx → MemArg → Wasm.Instr) → Prop where
  /-- `0x28 ⇒ LOAD I32 x ao` (5.3:105) -/
  | rx28 : MemOp 0x28 (fun x ao => .intLoad .i32 none x ao)
  /-- `0x29 ⇒ LOAD I64 x ao` (5.3:106) -/
  | rx29 : MemOp 0x29 (fun x ao => .intLoad .i64 none x ao)
  /-- `0x2A ⇒ LOAD F32 x ao` (5.3:107) -/
  | rx2A : MemOp 0x2A (fun x ao => .floatLoad .f32 x ao)
  /-- `0x2B ⇒ LOAD F64 x ao` (5.3:108) -/
  | rx2B : MemOp 0x2B (fun x ao => .floatLoad .f64 x ao)
  /-- `0x2C ⇒ LOAD I32 ('8 _ S) x ao` (5.3:109) -/
  | rx2C : MemOp 0x2C (fun x ao => .intLoad .i32 (some (.i8, .signed)) x ao)
  /-- `0x2D ⇒ LOAD I32 ('8 _ U) x ao` (5.3:110) -/
  | rx2D : MemOp 0x2D (fun x ao => .intLoad .i32 (some (.i8, .unsigned)) x ao)
  /-- `0x2E ⇒ LOAD I32 ('16 _ S) x ao` (5.3:111) -/
  | rx2E : MemOp 0x2E (fun x ao => .intLoad .i32 (some (.i16, .signed)) x ao)
  /-- `0x2F ⇒ LOAD I32 ('16 _ U) x ao` (5.3:112) -/
  | rx2F : MemOp 0x2F (fun x ao => .intLoad .i32 (some (.i16, .unsigned)) x ao)
  /-- `0x30 ⇒ LOAD I64 ('8 _ S) x ao` (5.3:113) -/
  | rx30 : MemOp 0x30 (fun x ao => .intLoad .i64 (some (.i8, .signed)) x ao)
  /-- `0x31 ⇒ LOAD I64 ('8 _ U) x ao` (5.3:114) -/
  | rx31 : MemOp 0x31 (fun x ao => .intLoad .i64 (some (.i8, .unsigned)) x ao)
  /-- `0x32 ⇒ LOAD I64 ('16 _ S) x ao` (5.3:115) -/
  | rx32 : MemOp 0x32 (fun x ao => .intLoad .i64 (some (.i16, .signed)) x ao)
  /-- `0x33 ⇒ LOAD I64 ('16 _ U) x ao` (5.3:116) -/
  | rx33 : MemOp 0x33 (fun x ao => .intLoad .i64 (some (.i16, .unsigned)) x ao)
  /-- `0x34 ⇒ LOAD I64 ('32 _ S) x ao` (5.3:117) -/
  | rx34 : MemOp 0x34 (fun x ao => .intLoad .i64 (some (.i32, .signed)) x ao)
  /-- `0x35 ⇒ LOAD I64 ('32 _ U) x ao` (5.3:118) -/
  | rx35 : MemOp 0x35 (fun x ao => .intLoad .i64 (some (.i32, .unsigned)) x ao)
  /-- `0x36 ⇒ STORE I32 x ao` (5.3:119) -/
  | rx36 : MemOp 0x36 (fun x ao => .intStore .i32 none x ao)
  /-- `0x37 ⇒ STORE I64 x ao` (5.3:120) -/
  | rx37 : MemOp 0x37 (fun x ao => .intStore .i64 none x ao)
  /-- `0x38 ⇒ STORE F32 x ao` (5.3:121) -/
  | rx38 : MemOp 0x38 (fun x ao => .floatStore .f32 x ao)
  /-- `0x39 ⇒ STORE F64 x ao` (5.3:122) -/
  | rx39 : MemOp 0x39 (fun x ao => .floatStore .f64 x ao)
  /-- `0x3A ⇒ STORE I32 '8 x ao` (5.3:123) -/
  | rx3A : MemOp 0x3A (fun x ao => .intStore .i32 (some .i8) x ao)
  /-- `0x3B ⇒ STORE I32 '16 x ao` (5.3:124) -/
  | rx3B : MemOp 0x3B (fun x ao => .intStore .i32 (some .i16) x ao)
  /-- `0x3C ⇒ STORE I64 '8 x ao` (5.3:125) -/
  | rx3C : MemOp 0x3C (fun x ao => .intStore .i64 (some .i8) x ao)
  /-- `0x3D ⇒ STORE I64 '16 x ao` (5.3:126) -/
  | rx3D : MemOp 0x3D (fun x ao => .intStore .i64 (some .i16) x ao)
  /-- `0x3E ⇒ STORE I64 '32 x ao` (5.3:127) -/
  | rx3E : MemOp 0x3E (fun x ao => .intStore .i64 (some .i32) x ao)

/-- Vector loads and stores: `| 0xFD n:Bu32 (x,ao):Bmemarg => ...`. -/
inductive VecMemOp : Nat → (MemIdx → MemArg → Wasm.Instr) → Prop where
  /-- `0xFD 0:Bu32 ⇒ VLOAD V128 x ao` (5.3:396) -/
  | r0 : VecMemOp 0 (fun x ao => .vecLoad .full x ao)
  /-- `0xFD 1:Bu32 ⇒ VLOAD V128 (SHAPE '8 X '8 _ S) x ao` (5.3:397) -/
  | r1 : VecMemOp 1 (fun x ao => .vecLoad (.extend8x8 .signed) x ao)
  /-- `0xFD 2:Bu32 ⇒ VLOAD V128 (SHAPE '8 X '8 _ U) x ao` (5.3:398) -/
  | r2 : VecMemOp 2 (fun x ao => .vecLoad (.extend8x8 .unsigned) x ao)
  /-- `0xFD 3:Bu32 ⇒ VLOAD V128 (SHAPE '16 X '4 _ S) x ao` (5.3:399) -/
  | r3 : VecMemOp 3 (fun x ao => .vecLoad (.extend16x4 .signed) x ao)
  /-- `0xFD 4:Bu32 ⇒ VLOAD V128 (SHAPE '16 X '4 _ U) x ao` (5.3:400) -/
  | r4 : VecMemOp 4 (fun x ao => .vecLoad (.extend16x4 .unsigned) x ao)
  /-- `0xFD 5:Bu32 ⇒ VLOAD V128 (SHAPE '32 X '2 _ S) x ao` (5.3:401) -/
  | r5 : VecMemOp 5 (fun x ao => .vecLoad (.extend32x2 .signed) x ao)
  /-- `0xFD 6:Bu32 ⇒ VLOAD V128 (SHAPE '32 X '2 _ U) x ao` (5.3:402) -/
  | r6 : VecMemOp 6 (fun x ao => .vecLoad (.extend32x2 .unsigned) x ao)
  /-- `0xFD 7:Bu32 ⇒ VLOAD V128 (SPLAT '8) x ao` (5.3:403) -/
  | r7 : VecMemOp 7 (fun x ao => .vecLoad (.splat .i8) x ao)
  /-- `0xFD 8:Bu32 ⇒ VLOAD V128 (SPLAT '16) x ao` (5.3:404) -/
  | r8 : VecMemOp 8 (fun x ao => .vecLoad (.splat .i16) x ao)
  /-- `0xFD 9:Bu32 ⇒ VLOAD V128 (SPLAT '32) x ao` (5.3:405) -/
  | r9 : VecMemOp 9 (fun x ao => .vecLoad (.splat .i32) x ao)
  /-- `0xFD 10:Bu32 ⇒ VLOAD V128 (SPLAT '64) x ao` (5.3:406) -/
  | r10 : VecMemOp 10 (fun x ao => .vecLoad (.splat .i64) x ao)
  /-- `0xFD 11:Bu32 ⇒ VSTORE V128 x ao` (5.3:407) -/
  | r11 : VecMemOp 11 (fun x ao => .vecStore x ao)
  /-- `0xFD 92:Bu32 ⇒ VLOAD V128 (ZERO '32) x ao` (5.3:416) -/
  | r92 : VecMemOp 92 (fun x ao => .vecLoad .zero32 x ao)
  /-- `0xFD 93:Bu32 ⇒ VLOAD V128 (ZERO '64) x ao` (5.3:417) -/
  | r93 : VecMemOp 93 (fun x ao => .vecLoad .zero64 x ao)

/-- Vector lane loads and stores: `| 0xFD n:Bu32 (x,ao):Bmemarg i:Blaneidx => ...`. -/
inductive VecMemLaneOp : Nat → (MemIdx → MemArg → LaneIdx → Wasm.Instr) → Prop where
  /-- `0xFD 84:Bu32 ⇒ VLOAD_LANE V128 '8 x ao i` (5.3:408) -/
  | r84 : VecMemLaneOp 84 (fun x ao i => .vecLoadLane .i8 x ao i)
  /-- `0xFD 85:Bu32 ⇒ VLOAD_LANE V128 '16 x ao i` (5.3:409) -/
  | r85 : VecMemLaneOp 85 (fun x ao i => .vecLoadLane .i16 x ao i)
  /-- `0xFD 86:Bu32 ⇒ VLOAD_LANE V128 '32 x ao i` (5.3:410) -/
  | r86 : VecMemLaneOp 86 (fun x ao i => .vecLoadLane .i32 x ao i)
  /-- `0xFD 87:Bu32 ⇒ VLOAD_LANE V128 '64 x ao i` (5.3:411) -/
  | r87 : VecMemLaneOp 87 (fun x ao i => .vecLoadLane .i64 x ao i)
  /-- `0xFD 88:Bu32 ⇒ VSTORE_LANE V128 '8 x ao i` (5.3:412) -/
  | r88 : VecMemLaneOp 88 (fun x ao i => .vecStoreLane .i8 x ao i)
  /-- `0xFD 89:Bu32 ⇒ VSTORE_LANE V128 '16 x ao i` (5.3:413) -/
  | r89 : VecMemLaneOp 89 (fun x ao i => .vecStoreLane .i16 x ao i)
  /-- `0xFD 90:Bu32 ⇒ VSTORE_LANE V128 '32 x ao i` (5.3:414) -/
  | r90 : VecMemLaneOp 90 (fun x ao i => .vecStoreLane .i32 x ao i)
  /-- `0xFD 91:Bu32 ⇒ VSTORE_LANE V128 '64 x ao i` (5.3:415) -/
  | r91 : VecMemLaneOp 91 (fun x ao i => .vecStoreLane .i64 x ao i)

/-- Vector lane extraction and replacement: `| 0xFD n:Bu32 l:Blaneidx => ...`. -/
inductive VecLaneOp : Nat → (LaneIdx → Wasm.Instr) → Prop where
  /-- `0xFD 21:Bu32 ⇒ VEXTRACT_LANE (I8 X '16) S l` (5.3:440) -/
  | r21 : VecLaneOp 21 (fun l => .vecExtractLane (.int .i8x16) (some .signed) l)
  /-- `0xFD 22:Bu32 ⇒ VEXTRACT_LANE (I8 X '16) U l` (5.3:441) -/
  | r22 : VecLaneOp 22 (fun l => .vecExtractLane (.int .i8x16) (some .unsigned) l)
  /-- `0xFD 23:Bu32 ⇒ VREPLACE_LANE (I8 X '16) l` (5.3:442) -/
  | r23 : VecLaneOp 23 (fun l => .vecReplaceLane (.int .i8x16) l)
  /-- `0xFD 24:Bu32 ⇒ VEXTRACT_LANE (I16 X '8) S l` (5.3:443) -/
  | r24 : VecLaneOp 24 (fun l => .vecExtractLane (.int .i16x8) (some .signed) l)
  /-- `0xFD 25:Bu32 ⇒ VEXTRACT_LANE (I16 X '8) U l` (5.3:444) -/
  | r25 : VecLaneOp 25 (fun l => .vecExtractLane (.int .i16x8) (some .unsigned) l)
  /-- `0xFD 26:Bu32 ⇒ VREPLACE_LANE (I16 X '8) l` (5.3:445) -/
  | r26 : VecLaneOp 26 (fun l => .vecReplaceLane (.int .i16x8) l)
  /-- `0xFD 27:Bu32 ⇒ VEXTRACT_LANE (I32 X '4) l` (5.3:446) -/
  | r27 : VecLaneOp 27 (fun l => .vecExtractLane (.int .i32x4) none l)
  /-- `0xFD 28:Bu32 ⇒ VREPLACE_LANE (I32 X '4) l` (5.3:447) -/
  | r28 : VecLaneOp 28 (fun l => .vecReplaceLane (.int .i32x4) l)
  /-- `0xFD 29:Bu32 ⇒ VEXTRACT_LANE (I64 X '2) l` (5.3:448) -/
  | r29 : VecLaneOp 29 (fun l => .vecExtractLane (.int .i64x2) none l)
  /-- `0xFD 30:Bu32 ⇒ VREPLACE_LANE (I64 X '2) l` (5.3:449) -/
  | r30 : VecLaneOp 30 (fun l => .vecReplaceLane (.int .i64x2) l)
  /-- `0xFD 31:Bu32 ⇒ VEXTRACT_LANE (F32 X '4) l` (5.3:450) -/
  | r31 : VecLaneOp 31 (fun l => .vecExtractLane (.float .f32x4) none l)
  /-- `0xFD 32:Bu32 ⇒ VREPLACE_LANE (F32 X '4) l` (5.3:451) -/
  | r32 : VecLaneOp 32 (fun l => .vecReplaceLane (.float .f32x4) l)
  /-- `0xFD 33:Bu32 ⇒ VEXTRACT_LANE (F64 X '2) l` (5.3:452) -/
  | r33 : VecLaneOp 33 (fun l => .vecExtractLane (.float .f64x2) none l)
  /-- `0xFD 34:Bu32 ⇒ VREPLACE_LANE (F64 X '2) l` (5.3:453) -/
  | r34 : VecLaneOp 34 (fun l => .vecReplaceLane (.float .f64x2) l)

end Silmaril.Wasm.Binary.Core
