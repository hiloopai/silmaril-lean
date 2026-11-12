module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.Lime1.Binary.TableZero
public import Silmaril.Raw.Wasm.SpecTec.Wasm.V1.Binary.Instructions
public import Silmaril.Wasm.Lime1.Instructions

/-! # Lime1 binary format: instructions

Lime1 is Wasm 1.0 plus seven features; their encodings are those of the
corresponding proposals as included in Core 3.0 (`5.3-binary.instructions.spectec`):

* multivalue: block types `i:Bs33 => _IDX i` (if `i ≥ 0`), 5.3:29;
* sign-extension: `0xC0`–`0xC4`, 5.3:281–288;
* nontrapping float-to-int: `0xFC n:Bu32` for `n = 0..7`, 5.3:379–386;
* bulk-memory-opt: `memory.copy` `0xFC 10:Bu32 0x00 0x00` and `memory.fill`
  `0xFC 11:Bu32 0x00`, with the bulk-memory proposal's *reserved* zero bytes (the
  memory indices of 5.3:132–133 are multi-memory, which Lime1 lacks);
* call-indirect-overlong: `call_indirect`'s reserved byte becomes a `u32` encoding of
  zero, possibly overlong (`TableZero`, reused from `TableZero.lean`), enabled by the
  `overlong` parameter (the profile has `overlong = true`; `false` gives exactly the
  1.0 encoding, used to state the converse agreement);
* mutable-globals and extended-const change no encoding (1.0 already encodes the
  mutability flag on imports/exports, and constant expressions are expressions).

Everything else is the 1.0 grammar (REC 5.4). The data count section is *not*
part of Lime1 (it belongs to bulk-memory proper; see docs/projects/wasm.md).

## Interpretation: memory-index immediates

In Core 3.0, `memory.size`, `memory.grow`, `memory.copy` and `memory.fill` take
`Bmemidx = Bu32` immediates (5.3:128–133), so a literal reading of "the encodings of
the corresponding proposals as included in the 3.0 spec" would admit overlong
memory indices (`3F 80 00`, `FC 0A 80 00 00`). This grammar instead keeps the
reserved byte `0x00`, as in Wasm 1.0 and the bulk-memory proposal. Reason: Lime1
lists call-indirect-overlong as a *separate* feature, which generalizes exactly one
reserved byte to a `u32`; the `Bu32` memory indices come from multi-memory, which
Lime1 does not include. This is a deliberate interpretation, pinned by
`Examples.memorySize_not_lime1` and `Examples.memoryCopy_not_lime1`; it makes
these byte strings Lime1 → Core disagreements (Core-only `memIdxImm` forms).
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Binary

open Silmaril.Wasm.Binary

/-- Lime1 block types: REC 5.3.2 plus the multivalue type-index form (5.3:26–29). -/
inductive BlockType : Bytes → Lime1.BlockType → Prop where
  | empty : BlockType [0x40] .empty
  | value {b : Bytes} {t : Lime1.ValType} (h : V1.Binary.ValType b t) : BlockType b (.value t)
  | idx {b : Bytes} (i : TypeIdx) (h : S33 b i.toNat) : BlockType b (.typeIdx i)

/-- `call_indirect`'s table operand: the literal 1.0 byte `0x00`, or, with
call-indirect-overlong, any `TableZero` encoding. -/
inductive TableIdxZero (overlong : Bool) : Bytes → Prop where
  | literal : TableIdxZero overlong [0x00]
  | padded {b : Bytes} (g : overlong = true) (h : TableZero ⟨b.toArray⟩) : TableIdxZero overlong b

/-- Single-byte instructions without immediates. -/
inductive PlainOp : UInt8 → Lime1.Instr → Prop where
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
  /-- `0xC0` ⇒ `i32.extend8_s` (sign-extension-ops, as SpecTec 5.3:281) -/
  | rxC0 : PlainOp 0xC0 (.intUnOp .i32 (.extend .i8))
  /-- `0xC1` ⇒ `i32.extend16_s` (sign-extension-ops, as SpecTec 5.3:282) -/
  | rxC1 : PlainOp 0xC1 (.intUnOp .i32 (.extend .i16))
  /-- `0xC2` ⇒ `i64.extend8_s` (sign-extension-ops, as SpecTec 5.3:286) -/
  | rxC2 : PlainOp 0xC2 (.intUnOp .i64 (.extend .i8))
  /-- `0xC3` ⇒ `i64.extend16_s` (sign-extension-ops, as SpecTec 5.3:287) -/
  | rxC3 : PlainOp 0xC3 (.intUnOp .i64 (.extend .i16))
  /-- `0xC4` ⇒ `i64.extend32_s` (sign-extension-ops, as SpecTec 5.3:288) -/
  | rxC4 : PlainOp 0xC4 (.intUnOp .i64 (.extend .i32))
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
inductive MemOp : UInt8 → (MemArg → Lime1.Instr) → Prop where
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

/-- `0xFC n:u32` saturating truncations (nontrapping-float-to-int, as SpecTec 5.3). -/
inductive PrefixFCOp : Nat → Lime1.Instr → Prop where
  /-- `0xFC 0:u32` ⇒ `i32.trunc_sat_f32_s` (5.3:379) -/
  | r0 : PrefixFCOp 0 (.convert (.truncSat .f32 .i32 .signed))
  /-- `0xFC 1:u32` ⇒ `i32.trunc_sat_f32_u` (5.3:380) -/
  | r1 : PrefixFCOp 1 (.convert (.truncSat .f32 .i32 .unsigned))
  /-- `0xFC 2:u32` ⇒ `i32.trunc_sat_f64_s` (5.3:381) -/
  | r2 : PrefixFCOp 2 (.convert (.truncSat .f64 .i32 .signed))
  /-- `0xFC 3:u32` ⇒ `i32.trunc_sat_f64_u` (5.3:382) -/
  | r3 : PrefixFCOp 3 (.convert (.truncSat .f64 .i32 .unsigned))
  /-- `0xFC 4:u32` ⇒ `i64.trunc_sat_f32_s` (5.3:383) -/
  | r4 : PrefixFCOp 4 (.convert (.truncSat .f32 .i64 .signed))
  /-- `0xFC 5:u32` ⇒ `i64.trunc_sat_f32_u` (5.3:384) -/
  | r5 : PrefixFCOp 5 (.convert (.truncSat .f32 .i64 .unsigned))
  /-- `0xFC 6:u32` ⇒ `i64.trunc_sat_f64_s` (5.3:385) -/
  | r6 : PrefixFCOp 6 (.convert (.truncSat .f64 .i64 .signed))
  /-- `0xFC 7:u32` ⇒ `i64.trunc_sat_f64_u` (5.3:386) -/
  | r7 : PrefixFCOp 7 (.convert (.truncSat .f64 .i64 .unsigned))

open V1.Binary (Memarg)

mutual

/-- Lime1 `instr`: REC 5.4 with the feature encodings above. -/
inductive Instr (overlong : Bool) : Bytes → Lime1.Instr → Prop where
  /-- Opcodes without immediates (`PlainOp`), including sign extension. -/
  | plain {op : UInt8} {i : Lime1.Instr} (h : PlainOp op i) : Instr overlong [op] i
  /-- `0xFC n:Bu32` saturating truncations (`PrefixFCOp`). -/
  | prefixFC {b : Bytes} {n : Nat} {i : Lime1.Instr} (h : PrefixFCOp n i) (hn : U32 b n) :
      Instr overlong ([0xFC] ++ b) i
  /-- `0x02 bt (in)* 0x0B` (REC 5.4.1, multivalue block type). -/
  | block {bt b : Bytes} {t : Lime1.BlockType} {body : List Lime1.Instr} (ht : BlockType bt t)
      (hb : Instrs overlong b body) : Instr overlong ([0x02] ++ bt ++ b ++ [0x0B]) (.block t body)
  /-- `0x03 bt (in)* 0x0B` (REC 5.4.1). -/
  | loop {bt b : Bytes} {t : Lime1.BlockType} {body : List Lime1.Instr} (ht : BlockType bt t)
      (hb : Instrs overlong b body) : Instr overlong ([0x03] ++ bt ++ b ++ [0x0B]) (.loop t body)
  /-- `0x04 bt (in)* 0x0B` (REC 5.4.1). -/
  | if_ {bt b : Bytes} {t : Lime1.BlockType} {body : List Lime1.Instr} (ht : BlockType bt t)
      (hb : Instrs overlong b body) :
      Instr overlong ([0x04] ++ bt ++ b ++ [0x0B]) (.if_ t body [])
  /-- `0x04 bt (in₁)* 0x05 (in₂)* 0x0B` (REC 5.4.1). -/
  | ifElse {bt b₁ b₂ : Bytes} {t : Lime1.BlockType} {body₁ body₂ : List Lime1.Instr}
      (ht : BlockType bt t) (h₁ : Instrs overlong b₁ body₁) (h₂ : Instrs overlong b₂ body₂) :
      Instr overlong ([0x04] ++ bt ++ b₁ ++ [0x05] ++ b₂ ++ [0x0B]) (.if_ t body₁ body₂)
  /-- `0x0C l:labelidx` (REC 5.4.1). -/
  | br {b : Bytes} {l : LabelIdx} (h : Index b l) : Instr overlong ([0x0C] ++ b) (.br l)
  /-- `0x0D l:labelidx` (REC 5.4.1). -/
  | brIf {b : Bytes} {l : LabelIdx} (h : Index b l) : Instr overlong ([0x0D] ++ b) (.brIf l)
  /-- `0x0E l*:vec(labelidx) l_N:labelidx` (REC 5.4.1). -/
  | brTable {b b' : Bytes} {ls : List LabelIdx} {l : LabelIdx} (h : Vec Index b ls)
      (h' : Index b' l) : Instr overlong ([0x0E] ++ b ++ b') (.brTable ls l)
  /-- `0x10 x:funcidx` (REC 5.4.1). -/
  | call {b : Bytes} {x : FuncIdx} (h : Index b x) : Instr overlong ([0x10] ++ b) (.call x)
  /-- `0x11 x:typeidx z` with `z` the table-zero operand (REC 5.4.1; call-indirect-overlong). -/
  | callIndirect {b bz : Bytes} {x : TypeIdx} (h : Index b x) (hz : TableIdxZero overlong bz) :
      Instr overlong ([0x11] ++ b ++ bz) (.callIndirect x)
  /-- `0x20 x:localidx` (REC 5.4.3). -/
  | localGet {b : Bytes} {x : LocalIdx} (h : Index b x) :
      Instr overlong ([0x20] ++ b) (.localGet x)
  /-- `0x21 x:localidx` (REC 5.4.3). -/
  | localSet {b : Bytes} {x : LocalIdx} (h : Index b x) :
      Instr overlong ([0x21] ++ b) (.localSet x)
  /-- `0x22 x:localidx` (REC 5.4.3). -/
  | localTee {b : Bytes} {x : LocalIdx} (h : Index b x) :
      Instr overlong ([0x22] ++ b) (.localTee x)
  /-- `0x23 x:globalidx` (REC 5.4.3). -/
  | globalGet {b : Bytes} {x : GlobalIdx} (h : Index b x) :
      Instr overlong ([0x23] ++ b) (.globalGet x)
  /-- `0x24 x:globalidx` (REC 5.4.3). -/
  | globalSet {b : Bytes} {x : GlobalIdx} (h : Index b x) :
      Instr overlong ([0x24] ++ b) (.globalSet x)
  /-- Loads and stores `0xNN m:memarg` (REC 5.4.4, `MemOp`). -/
  | mem {op : UInt8} {b : Bytes} {mk : Lime1.MemArg → Lime1.Instr} {a : Lime1.MemArg}
      (h : MemOp op mk) (hm : Memarg b a) : Instr overlong ([op] ++ b) (mk a)
  /-- `0x3F 0x00 ⇒ memory.size` (REC 5.4.4). -/
  | memorySize : Instr overlong [0x3F, 0x00] .memorySize
  /-- `0x40 0x00 ⇒ memory.grow` (REC 5.4.4). -/
  | memoryGrow : Instr overlong [0x40, 0x00] .memoryGrow
  /-- `0xFC 10:u32 0x00 0x00 ⇒ memory.copy` (bulk-memory-opt, reserved bytes). -/
  | memoryCopy {b : Bytes} (hn : U32 b 10) : Instr overlong ([0xFC] ++ b ++
      [0x00, 0x00]) .memoryCopy
  /-- `0xFC 11:u32 0x00 ⇒ memory.fill` (bulk-memory-opt, reserved byte). -/
  | memoryFill {b : Bytes} (hn : U32 b 11) : Instr overlong ([0xFC] ++ b ++ [0x00]) .memoryFill
  /-- `0x41 n:i32` (REC 5.4.5). -/
  | i32Const {b : Bytes} {v : BitVec 32} (h : IN 32 b v) :
      Instr overlong ([0x41] ++ b) (.intConst .i32 v)
  /-- `0x42 n:i64` (REC 5.4.5). -/
  | i64Const {b : Bytes} {v : BitVec 64} (h : IN 64 b v) :
      Instr overlong ([0x42] ++ b) (.intConst .i64 v)
  /-- `0x43 z:f32` (REC 5.4.5). -/
  | f32Const {b : Bytes} {p : BitVec 32} (h : FN 32 b p) :
      Instr overlong ([0x43] ++ b) (.floatConst .f32 p)
  /-- `0x44 z:f64` (REC 5.4.5). -/
  | f64Const {b : Bytes} {p : BitVec 64} (h : FN 64 b p) :
      Instr overlong ([0x44] ++ b) (.floatConst .f64 p)

/-- `(in:instr)*`. -/
inductive Instrs (overlong : Bool) : Bytes → List Lime1.Instr → Prop where
  | nil : Instrs overlong [] []
  | cons {b bs : Bytes} {i : Lime1.Instr} {is : List Lime1.Instr} (h : Instr overlong b i)
      (hs : Instrs overlong bs is) : Instrs overlong (b ++ bs) (i :: is)

end

/-- `expr ::= (in:instr)* 0x0B` (REC 5.4.6). -/
inductive Expr (overlong : Bool) : Bytes → Lime1.Expr → Prop where
  | mk {b : Bytes} {is : List Lime1.Instr} (h : Instrs overlong b is) : Expr overlong (b ++
      [0x0B]) is

/-- The single-byte opcode table, as a lookup list (`PlainOp` as a function). -/
def plainTable : List (Nat × Lime1.Instr) := [
  (0x00, .unreachable),
  (0x01, .nop),
  (0x1A, .drop),
  (0x1B, .select),
  (0x0F, .return_),
  (0x45, (.intTestOp .i32 .eqz)),
  (0x46, (.intRelOp .i32 .eq)),
  (0x47, (.intRelOp .i32 .ne)),
  (0x48, (.intRelOp .i32 (.lt .signed))),
  (0x49, (.intRelOp .i32 (.lt .unsigned))),
  (0x4A, (.intRelOp .i32 (.gt .signed))),
  (0x4B, (.intRelOp .i32 (.gt .unsigned))),
  (0x4C, (.intRelOp .i32 (.le .signed))),
  (0x4D, (.intRelOp .i32 (.le .unsigned))),
  (0x4E, (.intRelOp .i32 (.ge .signed))),
  (0x4F, (.intRelOp .i32 (.ge .unsigned))),
  (0x50, (.intTestOp .i64 .eqz)),
  (0x51, (.intRelOp .i64 .eq)),
  (0x52, (.intRelOp .i64 .ne)),
  (0x53, (.intRelOp .i64 (.lt .signed))),
  (0x54, (.intRelOp .i64 (.lt .unsigned))),
  (0x55, (.intRelOp .i64 (.gt .signed))),
  (0x56, (.intRelOp .i64 (.gt .unsigned))),
  (0x57, (.intRelOp .i64 (.le .signed))),
  (0x58, (.intRelOp .i64 (.le .unsigned))),
  (0x59, (.intRelOp .i64 (.ge .signed))),
  (0x5A, (.intRelOp .i64 (.ge .unsigned))),
  (0x5B, (.floatRelOp .f32 .eq)),
  (0x5C, (.floatRelOp .f32 .ne)),
  (0x5D, (.floatRelOp .f32 .lt)),
  (0x5E, (.floatRelOp .f32 .gt)),
  (0x5F, (.floatRelOp .f32 .le)),
  (0x60, (.floatRelOp .f32 .ge)),
  (0x61, (.floatRelOp .f64 .eq)),
  (0x62, (.floatRelOp .f64 .ne)),
  (0x63, (.floatRelOp .f64 .lt)),
  (0x64, (.floatRelOp .f64 .gt)),
  (0x65, (.floatRelOp .f64 .le)),
  (0x66, (.floatRelOp .f64 .ge)),
  (0x67, (.intUnOp .i32 .clz)),
  (0x68, (.intUnOp .i32 .ctz)),
  (0x69, (.intUnOp .i32 .popcnt)),
  (0x6A, (.intBinOp .i32 .add)),
  (0x6B, (.intBinOp .i32 .sub)),
  (0x6C, (.intBinOp .i32 .mul)),
  (0x6D, (.intBinOp .i32 (.div .signed))),
  (0x6E, (.intBinOp .i32 (.div .unsigned))),
  (0x6F, (.intBinOp .i32 (.rem .signed))),
  (0x70, (.intBinOp .i32 (.rem .unsigned))),
  (0x71, (.intBinOp .i32 .and)),
  (0x72, (.intBinOp .i32 .or)),
  (0x73, (.intBinOp .i32 .xor)),
  (0x74, (.intBinOp .i32 .shl)),
  (0x75, (.intBinOp .i32 (.shr .signed))),
  (0x76, (.intBinOp .i32 (.shr .unsigned))),
  (0x77, (.intBinOp .i32 .rotl)),
  (0x78, (.intBinOp .i32 .rotr)),
  (0x79, (.intUnOp .i64 .clz)),
  (0x7A, (.intUnOp .i64 .ctz)),
  (0x7B, (.intUnOp .i64 .popcnt)),
  (0xC0, (.intUnOp .i32 (.extend .i8))),
  (0xC1, (.intUnOp .i32 (.extend .i16))),
  (0xC2, (.intUnOp .i64 (.extend .i8))),
  (0xC3, (.intUnOp .i64 (.extend .i16))),
  (0xC4, (.intUnOp .i64 (.extend .i32))),
  (0x7C, (.intBinOp .i64 .add)),
  (0x7D, (.intBinOp .i64 .sub)),
  (0x7E, (.intBinOp .i64 .mul)),
  (0x7F, (.intBinOp .i64 (.div .signed))),
  (0x80, (.intBinOp .i64 (.div .unsigned))),
  (0x81, (.intBinOp .i64 (.rem .signed))),
  (0x82, (.intBinOp .i64 (.rem .unsigned))),
  (0x83, (.intBinOp .i64 .and)),
  (0x84, (.intBinOp .i64 .or)),
  (0x85, (.intBinOp .i64 .xor)),
  (0x86, (.intBinOp .i64 .shl)),
  (0x87, (.intBinOp .i64 (.shr .signed))),
  (0x88, (.intBinOp .i64 (.shr .unsigned))),
  (0x89, (.intBinOp .i64 .rotl)),
  (0x8A, (.intBinOp .i64 .rotr)),
  (0x8B, (.floatUnOp .f32 .abs)),
  (0x8C, (.floatUnOp .f32 .neg)),
  (0x8D, (.floatUnOp .f32 .ceil)),
  (0x8E, (.floatUnOp .f32 .floor)),
  (0x8F, (.floatUnOp .f32 .trunc)),
  (0x90, (.floatUnOp .f32 .nearest)),
  (0x91, (.floatUnOp .f32 .sqrt)),
  (0x92, (.floatBinOp .f32 .add)),
  (0x93, (.floatBinOp .f32 .sub)),
  (0x94, (.floatBinOp .f32 .mul)),
  (0x95, (.floatBinOp .f32 .div)),
  (0x96, (.floatBinOp .f32 .min)),
  (0x97, (.floatBinOp .f32 .max)),
  (0x98, (.floatBinOp .f32 .copysign)),
  (0x99, (.floatUnOp .f64 .abs)),
  (0x9A, (.floatUnOp .f64 .neg)),
  (0x9B, (.floatUnOp .f64 .ceil)),
  (0x9C, (.floatUnOp .f64 .floor)),
  (0x9D, (.floatUnOp .f64 .trunc)),
  (0x9E, (.floatUnOp .f64 .nearest)),
  (0x9F, (.floatUnOp .f64 .sqrt)),
  (0xA0, (.floatBinOp .f64 .add)),
  (0xA1, (.floatBinOp .f64 .sub)),
  (0xA2, (.floatBinOp .f64 .mul)),
  (0xA3, (.floatBinOp .f64 .div)),
  (0xA4, (.floatBinOp .f64 .min)),
  (0xA5, (.floatBinOp .f64 .max)),
  (0xA6, (.floatBinOp .f64 .copysign)),
  (0xA7, (.convert .wrap)),
  (0xA8, (.convert (.trunc .f32 .i32 .signed))),
  (0xA9, (.convert (.trunc .f32 .i32 .unsigned))),
  (0xAA, (.convert (.trunc .f64 .i32 .signed))),
  (0xAB, (.convert (.trunc .f64 .i32 .unsigned))),
  (0xAC, (.convert (.extend .signed))),
  (0xAD, (.convert (.extend .unsigned))),
  (0xAE, (.convert (.trunc .f32 .i64 .signed))),
  (0xAF, (.convert (.trunc .f32 .i64 .unsigned))),
  (0xB0, (.convert (.trunc .f64 .i64 .signed))),
  (0xB1, (.convert (.trunc .f64 .i64 .unsigned))),
  (0xB2, (.convert (.convert .i32 .f32 .signed))),
  (0xB3, (.convert (.convert .i32 .f32 .unsigned))),
  (0xB4, (.convert (.convert .i64 .f32 .signed))),
  (0xB5, (.convert (.convert .i64 .f32 .unsigned))),
  (0xB6, (.convert .demote)),
  (0xB7, (.convert (.convert .i32 .f64 .signed))),
  (0xB8, (.convert (.convert .i32 .f64 .unsigned))),
  (0xB9, (.convert (.convert .i64 .f64 .signed))),
  (0xBA, (.convert (.convert .i64 .f64 .unsigned))),
  (0xBB, (.convert .promote)),
  (0xBC, (.convert (.reinterpretInt .f32))),
  (0xBD, (.convert (.reinterpretInt .f64))),
  (0xBE, (.convert (.reinterpretFloat .i32))),
  (0xBF, (.convert (.reinterpretFloat .i64)))
]

/-- The load/store opcode table (`MemOp` as a function). -/
def memTable : List (Nat × (MemArg → Lime1.Instr)) := [
  (0x28, fun ao => .intLoad .i32 none ao),
  (0x29, fun ao => .intLoad .i64 none ao),
  (0x2A, fun ao => .floatLoad .f32 ao),
  (0x2B, fun ao => .floatLoad .f64 ao),
  (0x2C, fun ao => .intLoad .i32 (some (.i8, .signed)) ao),
  (0x2D, fun ao => .intLoad .i32 (some (.i8, .unsigned)) ao),
  (0x2E, fun ao => .intLoad .i32 (some (.i16, .signed)) ao),
  (0x2F, fun ao => .intLoad .i32 (some (.i16, .unsigned)) ao),
  (0x30, fun ao => .intLoad .i64 (some (.i8, .signed)) ao),
  (0x31, fun ao => .intLoad .i64 (some (.i8, .unsigned)) ao),
  (0x32, fun ao => .intLoad .i64 (some (.i16, .signed)) ao),
  (0x33, fun ao => .intLoad .i64 (some (.i16, .unsigned)) ao),
  (0x34, fun ao => .intLoad .i64 (some (.i32, .signed)) ao),
  (0x35, fun ao => .intLoad .i64 (some (.i32, .unsigned)) ao),
  (0x36, fun ao => .intStore .i32 none ao),
  (0x37, fun ao => .intStore .i64 none ao),
  (0x38, fun ao => .floatStore .f32 ao),
  (0x39, fun ao => .floatStore .f64 ao),
  (0x3A, fun ao => .intStore .i32 (some .i8) ao),
  (0x3B, fun ao => .intStore .i32 (some .i16) ao),
  (0x3C, fun ao => .intStore .i64 (some .i8) ao),
  (0x3D, fun ao => .intStore .i64 (some .i16) ao),
  (0x3E, fun ao => .intStore .i64 (some .i32) ao)
]

/-! ## Opcode tables -/

/-- `PlainOp` as a partial function. -/
def plainOp? (op : UInt8) : Option Lime1.Instr :=
  (plainTable.find? (·.1 == op.toNat)).map (·.2)

/-- `MemOp` as a partial function. -/
def memOp? (op : UInt8) : Option (MemArg → Lime1.Instr) :=
  (memTable.find? (·.1 == op.toNat)).map (·.2)

theorem PlainOp.eq_plainOp? {op : UInt8} {i : Lime1.Instr} (h : PlainOp op i) :
    plainOp? op = some i := by
  cases h <;> rfl

theorem MemOp.eq_memOp? {op : UInt8} {mk : MemArg → Lime1.Instr} (h : MemOp op mk) :
    memOp? op = some mk := by
  cases h <;> rfl

theorem PlainOp.functional {op : UInt8} {i i' : Lime1.Instr} (h : PlainOp op i)
    (h' : PlainOp op i') : i = i' :=
  Option.some.inj (h.eq_plainOp?.symm.trans h'.eq_plainOp?)

theorem MemOp.functional {op : UInt8} {mk mk' : MemArg → Lime1.Instr} (h : MemOp op mk)
    (h' : MemOp op mk') : mk = mk' :=
  Option.some.inj (h.eq_memOp?.symm.trans h'.eq_memOp?)

/-- The single-byte opcodes: `0x00`, `0x01`, `0x0F`, `0x1A`, `0x1B` and `0x45`–`0xC4`. -/
theorem PlainOp.range {op : UInt8} {i : Lime1.Instr} (h : PlainOp op i) :
    op.toNat = 0x00 ∨ op.toNat = 0x01 ∨ op.toNat = 0x0F ∨ op.toNat = 0x1A ∨
      op.toNat = 0x1B ∨ (0x45 ≤ op.toNat ∧ op.toNat ≤ 0xC4) := by
  cases h <;> decide

/-- The load/store opcodes are `0x28`–`0x3E`. -/
theorem MemOp.range {op : UInt8} {mk : MemArg → Lime1.Instr} (h : MemOp op mk) :
    0x28 ≤ op.toNat ∧ op.toNat ≤ 0x3E := by
  cases h <;> decide

theorem PrefixFCOp.le {n : Nat} {i : Lime1.Instr} (h : PrefixFCOp n i) : n ≤ 7 := by
  cases h <;> decide

theorem PrefixFCOp.functional {n : Nat} {i i' : Lime1.Instr} (h : PrefixFCOp n i)
    (h' : PrefixFCOp n i') : i = i' := by
  cases h <;> cases h' <;> rfl

/-! ## Immediates -/

theorem memarg_prefixFree : PrefixFree Memarg := by
  intro b b' r r' a a' h h' heq
  cases h with
  | mk ha ho =>
    cases h' with
    | mk ha' ho' =>
      simp only [List.append_assoc] at heq
      obtain ⟨rfl, e₁⟩ := UN.prefixFree 32 ha ha' heq
      obtain ⟨rfl, e₂⟩ := UN.prefixFree 32 ho ho' (List.append_cancel_left heq)
      obtain rfl := Fin.ext e₁
      obtain rfl := Fin.ext e₂
      exact ⟨rfl, rfl⟩

/-- A nonnegative signed LEB128 value does not begin with a one-byte negative form. -/
theorem SN.head_of_nonneg {N : Nat} {x : UInt8} {rest : Bytes} {v : Int}
    (h : SN N (x :: rest) v) (hv : 0 ≤ v) : x.toNat < 0x40 ∨ 0x80 ≤ x.toNat := by
  cases h with
  | pos _ h₁ _ => left; omega
  | neg _ h₁ h₂ _ => omega
  | cont _ h₁ _ _ => right; omega

theorem ValType.head {b : Bytes} {t : Lime1.ValType} (h : V1.Binary.ValType b t) :
    ∃ x, b = [x] ∧ 0x7C ≤ x.toNat ∧ x.toNat < 0x80 := by
  cases h <;> exact ⟨_, rfl, by decide, by decide⟩

theorem Idx.toNat_injective {k : IndexKind} {i j : Idx k} (h : i.toNat = j.toNat) : i = j := by
  cases i
  cases j
  simp only [Idx.toNat] at h
  rw [Fin.ext h]

theorem BlockType.prefixFree : PrefixFree BlockType := by
  intro b b' r r' t t' h h' heq
  cases h with
  | empty =>
    cases h' with
    | empty => exact ⟨rfl, rfl⟩
    | value hv =>
      obtain ⟨x, rfl, h₁, h₂⟩ := ValType.head hv
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      have := congrArg UInt8.toNat heq.1
      simp only [UInt8.reduceToNat] at this
      omega
    | idx i hi =>
      cases b' with
      | nil => cases hi
      | cons x rest =>
        have hx := SN.head_of_nonneg hi (by omega)
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
        have := congrArg UInt8.toNat heq.1
        simp only [UInt8.reduceToNat] at this
        omega
  | value hv =>
    obtain ⟨x, rfl, h₁, h₂⟩ := ValType.head hv
    cases h' with
    | empty =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      have := congrArg UInt8.toNat heq.1
      simp only [UInt8.reduceToNat] at this
      omega
    | value hv' =>
      obtain ⟨rfl, rfl⟩ := V1.Binary.ValType.prefixFree hv hv' heq
      exact ⟨rfl, rfl⟩
    | idx i hi =>
      cases b' with
      | nil => cases hi
      | cons x' rest =>
        have hx := SN.head_of_nonneg hi (by omega)
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
        have := congrArg UInt8.toNat heq.1
        omega
  | idx i hi =>
    cases b with
    | nil => cases hi
    | cons x rest =>
      have hx := SN.head_of_nonneg hi (by omega)
      cases h' with
      | empty =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
        have := congrArg UInt8.toNat heq.1
        simp only [UInt8.reduceToNat] at this
        omega
      | value hv' =>
        obtain ⟨x', rfl, h₁, h₂⟩ := ValType.head hv'
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
        have := congrArg UInt8.toNat heq.1
        omega
      | idx i' hi' =>
        obtain ⟨rfl, e⟩ := SN.prefixFree 33 hi hi' heq
        obtain rfl := Idx.toNat_injective (by exact_mod_cast e)
        exact ⟨rfl, rfl⟩

/-- With call-indirect-overlong, the table operand is exactly a `u32` encoding of zero. -/
theorem TableIdxZero.true_iff (b : Bytes) : TableIdxZero true b ↔ U32 b 0 := by
  have key : TableZero ⟨b.toArray⟩ ↔ ∃ k, k ≤ 4 ∧ b = List.replicate k 0x80 ++ [0x00] := by
    simp only [TableZero, ZeroPayload.iff_padding, ByteArray.size,
      List.size_toArray]
    constructor
    · rintro ⟨⟨n, rfl⟩, h⟩
      simp only [List.length_append, List.length_replicate, List.length_singleton] at h
      exact ⟨n, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      simp only [List.length_append, List.length_replicate, List.length_singleton]
      exact ⟨⟨k, rfl⟩, by omega⟩
  rw [UN.u32_zero_iff]
  constructor
  · rintro (_ | ⟨_, h⟩)
    · exact ⟨0, by omega, rfl⟩
    · exact key.mp h
  · intro h
    exact .padded rfl (key.mpr h)

theorem TableIdxZero.mono {b : Bytes} (h : TableIdxZero false b) : TableIdxZero true b := by
  cases h with
  | literal => exact .literal
  | padded g _ => cases g

theorem TableIdxZero.prefixFree {overlong : Bool} {b b' r r' : Bytes}
    (h : TableIdxZero overlong b) (h' : TableIdxZero overlong b') (heq : b ++ r = b' ++ r') :
    b = b' := by
  cases overlong with
  | false =>
    cases h with
    | padded g _ => cases g
    | literal =>
      cases h' with
      | padded g _ => cases g
      | literal => rfl
  | true =>
    exact (UN.prefixFree 32 ((TableIdxZero.true_iff _).mp h)
      ((TableIdxZero.true_iff _).mp h') heq).1

/-! ## Monotonicity in `overlong` -/

mutual

theorem Instr.mono {b : Bytes} {i : Lime1.Instr} (h : Instr false b i) : Instr true b i := by
  cases h with
  | plain h => exact .plain h
  | prefixFC h hn => exact .prefixFC h hn
  | block ht hb => exact .block ht (Instrs.mono hb)
  | loop ht hb => exact .loop ht (Instrs.mono hb)
  | if_ ht hb => exact .if_ ht (Instrs.mono hb)
  | ifElse ht h₁ h₂ => exact .ifElse ht (Instrs.mono h₁) (Instrs.mono h₂)
  | br h => exact .br h
  | brIf h => exact .brIf h
  | brTable h h' => exact .brTable h h'
  | call h => exact .call h
  | callIndirect h hz => exact .callIndirect h hz.mono
  | localGet h => exact .localGet h
  | localSet h => exact .localSet h
  | localTee h => exact .localTee h
  | globalGet h => exact .globalGet h
  | globalSet h => exact .globalSet h
  | mem h hm => exact .mem h hm
  | memorySize => exact .memorySize
  | memoryGrow => exact .memoryGrow
  | memoryCopy hn => exact .memoryCopy hn
  | memoryFill hn => exact .memoryFill hn
  | i32Const h => exact .i32Const h
  | i64Const h => exact .i64Const h
  | f32Const h => exact .f32Const h
  | f64Const h => exact .f64Const h

theorem Instrs.mono {b : Bytes} {is : List Lime1.Instr} (h : Instrs false b is) :
    Instrs true b is :=
  match h with
  | .nil => .nil
  | .cons h hs => .cons (Instr.mono h) (Instrs.mono hs)

end

theorem Expr.mono {b : Bytes} {e : Lime1.Expr} (h : Expr false b e) : Expr true b e := by
  cases h with
  | mk h => exact .mk h.mono

/-! ## Unambiguity -/

/-- Every instruction begins with an opcode other than `0x05` (`else`) and `0x0B` (`end`). -/
theorem Instr.head {overlong : Bool} {b : Bytes} {i : Lime1.Instr} (h : Instr overlong b i) :
    ∃ op rest, b = op :: rest ∧ op.toNat ≠ 0x05 ∧ op.toNat ≠ 0x0B := by
  cases h with
  | plain hp =>
    have := hp.range
    exact ⟨_, [], rfl, by omega, by omega⟩
  | mem hm =>
    have := hm.range
    exact ⟨_, _, rfl, by omega, by omega⟩
  | memorySize => exact ⟨_, _, rfl, by decide, by decide⟩
  | memoryGrow => exact ⟨_, _, rfl, by decide, by decide⟩
  | _ => exact ⟨_, _, rfl, by decide, by decide⟩

/-- The bytes that end an instruction sequence: `0x05` (`else`) and `0x0B` (`end`). -/
abbrev IsTerm (t : UInt8) : Prop := t.toNat = 0x05 ∨ t.toNat = 0x0B

/-- Prefix-freeness of instructions shorter than `n`. -/
def PFLt (overlong : Bool) (n : Nat) : Prop :=
  ∀ ⦃b b' r r' : Bytes⦄ ⦃i i' : Lime1.Instr⦄, b.length < n → Instr overlong b i →
    Instr overlong b' i' → b ++ r = b' ++ r' → b = b' ∧ i = i'

/-- Instruction sequences, each followed by a terminator, are determined by their bytes. -/
theorem Instrs.prefixFree_aux {overlong : Bool} {n : Nat} (H : PFLt overlong n) :
    ∀ (is : List Lime1.Instr) {b b' : Bytes} {is' : List Lime1.Instr} {t t' : UInt8}
      {r r' : Bytes}, b.length < n → Instrs overlong b is → Instrs overlong b' is' → IsTerm t →
      IsTerm t' → b ++ t :: r = b' ++ t' :: r' → b = b' ∧ is = is'
  | [], _, _, _, _, _, _, _, _, h, h', ht, _, heq => by
    cases h
    cases h' with
    | nil => exact ⟨rfl, rfl⟩
    | cons h₁ _ =>
      obtain ⟨op, rest, rfl, h₅, h₁₁⟩ := h₁.head
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      rw [heq.1] at ht
      unfold IsTerm at ht
      omega
  | _ :: xs, _, _, _, _, _, _, _, hl, h, h', ht, ht', heq => by
    cases h with
    | cons h₁ hs =>
      cases h' with
      | nil =>
        obtain ⟨op, rest, rfl, h₅, h₁₁⟩ := h₁.head
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
        rw [← heq.1] at ht'
        unfold IsTerm at ht'
        omega
      | cons h₁' hs' =>
        simp only [List.append_assoc] at heq
        simp only [List.length_append] at hl
        obtain ⟨rfl, rfl⟩ := H (by omega) h₁ h₁' heq
        obtain ⟨rfl, rfl⟩ :=
          Instrs.prefixFree_aux H xs (by omega) hs hs' ht ht' (List.append_cancel_left heq)
        exact ⟨rfl, rfl⟩

set_option hygiene false in
/-- Close a goal whose two instructions begin with different opcodes. -/
local macro "opcode_mismatch" : tactic => `(tactic| (
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
    List.cons.injEq] at heq
  have hh := congrArg UInt8.toNat heq.1
  try simp only [UInt8.reduceToNat] at hh
  try have := PlainOp.range ‹PlainOp _ _›
  try have := MemOp.range ‹MemOp _ _›
  omega))

set_option hygiene false in
/-- Strip the common opcode from `heq`. -/
local macro "strip_opcode" : tactic => `(tactic| (
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
    List.cons.injEq, true_and] at heq))

theorem Instr.pfLt_succ {overlong : Bool} {n : Nat} (H : PFLt overlong n) :
    PFLt overlong (n + 1) := by
  intro b b' r r' i i' hl h₁ h₂ heq
  cases h₁ with
  | plain hp =>
    cases h₂ with
    | plain hp' =>
      strip_opcode
      obtain ⟨rfl, -⟩ := heq
      exact ⟨rfl, hp.functional hp'⟩
    | _ => opcode_mismatch
  | prefixFC hp hn =>
    cases h₂ with
    | prefixFC hp' hn' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := UN.prefixFree 32 hn hn' heq
      exact ⟨rfl, hp.functional hp'⟩
    | memoryCopy hn' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := UN.prefixFree 32 hn hn' heq
      have := hp.le
      omega
    | memoryFill hn' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := UN.prefixFree 32 hn hn' heq
      have := hp.le
      omega
    | _ => opcode_mismatch
  | block ht hb =>
    cases h₂ with
    | block ht' hb' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := BlockType.prefixFree ht ht' heq
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      obtain ⟨rfl, rfl⟩ := Instrs.prefixFree_aux H _ (by omega) hb hb' (by decide) (by decide)
        (List.append_cancel_left heq)
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | loop ht hb =>
    cases h₂ with
    | loop ht' hb' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := BlockType.prefixFree ht ht' heq
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      obtain ⟨rfl, rfl⟩ := Instrs.prefixFree_aux H _ (by omega) hb hb' (by decide) (by decide)
        (List.append_cancel_left heq)
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | if_ ht hb =>
    cases h₂ with
    | if_ ht' hb' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := BlockType.prefixFree ht ht' heq
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      obtain ⟨rfl, rfl⟩ := Instrs.prefixFree_aux H _ (by omega) hb hb' (by decide) (by decide)
        (List.append_cancel_left heq)
      exact ⟨rfl, rfl⟩
    | ifElse ht' hb₁ hb₂ =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := BlockType.prefixFree ht ht' heq
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      have heq := List.append_cancel_left heq
      obtain ⟨rfl, rfl⟩ := Instrs.prefixFree_aux H _ (by omega) hb hb₁ (by decide) (by decide)
        heq
      have := (List.cons.inj (List.append_cancel_left heq)).1
      exact absurd this (by decide)
    | _ => opcode_mismatch
  | ifElse ht hb₁ hb₂ =>
    cases h₂ with
    | if_ ht' hb' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := BlockType.prefixFree ht ht' heq
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      have heq := List.append_cancel_left heq
      obtain ⟨rfl, rfl⟩ := Instrs.prefixFree_aux H _ (by omega) hb₁ hb' (by decide) (by decide)
        heq
      have := (List.cons.inj (List.append_cancel_left heq)).1
      exact absurd this (by decide)
    | ifElse ht' hb₁' hb₂' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := BlockType.prefixFree ht ht' heq
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      have heq := List.append_cancel_left heq
      obtain ⟨rfl, rfl⟩ := Instrs.prefixFree_aux H _ (by omega) hb₁ hb₁' (by decide) (by decide)
        heq
      have heq := (List.cons.inj (List.append_cancel_left heq)).2
      obtain ⟨rfl, rfl⟩ := Instrs.prefixFree_aux H _ (by omega) hb₂ hb₂' (by decide) (by decide)
        heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | br h =>
    cases h₂ with
    | br h' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | brIf h =>
    cases h₂ with
    | brIf h' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | brTable h hl' =>
    cases h₂ with
    | brTable h' hl'' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := Vec.prefixFree Index.prefixFree h h' heq
      obtain ⟨rfl, rfl⟩ := Index.prefixFree hl' hl'' (List.append_cancel_left heq)
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | call h =>
    cases h₂ with
    | call h' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | callIndirect h hz =>
    cases h₂ with
    | callIndirect h' hz' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
      obtain rfl := TableIdxZero.prefixFree hz hz' (List.append_cancel_left heq)
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | localGet h =>
    cases h₂ with
    | localGet h' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | localSet h =>
    cases h₂ with
    | localSet h' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | localTee h =>
    cases h₂ with
    | localTee h' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | globalGet h =>
    cases h₂ with
    | globalGet h' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | globalSet h =>
    cases h₂ with
    | globalSet h' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | mem hm ha =>
    cases h₂ with
    | mem hm' ha' =>
      strip_opcode
      obtain ⟨rfl, heq⟩ := heq
      obtain rfl := hm.functional hm'
      obtain ⟨rfl, rfl⟩ := memarg_prefixFree ha ha' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | memorySize =>
    cases h₂ with
    | memorySize => exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | memoryGrow =>
    cases h₂ with
    | memoryGrow => exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | memoryCopy hn =>
    cases h₂ with
    | prefixFC hp' hn' =>
      strip_opcode
      obtain ⟨rfl, h⟩ := UN.prefixFree 32 hn hn' heq
      have := hp'.le
      omega
    | memoryCopy hn' => exact ⟨by rw [(UN.prefixFree 32 hn hn' (by strip_opcode; exact heq)).1], rfl⟩
    | memoryFill hn' =>
      strip_opcode
      obtain ⟨rfl, h⟩ := UN.prefixFree 32 hn hn' heq
      omega
    | _ => opcode_mismatch
  | memoryFill hn =>
    cases h₂ with
    | prefixFC hp' hn' =>
      strip_opcode
      obtain ⟨rfl, h⟩ := UN.prefixFree 32 hn hn' heq
      have := hp'.le
      omega
    | memoryCopy hn' =>
      strip_opcode
      obtain ⟨rfl, h⟩ := UN.prefixFree 32 hn hn' heq
      omega
    | memoryFill hn' => exact ⟨by rw [(UN.prefixFree 32 hn hn' (by strip_opcode; exact heq)).1], rfl⟩
    | _ => opcode_mismatch
  | i32Const h =>
    cases h₂ with
    | i32Const h' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := IN.prefixFree 32 h h' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | i64Const h =>
    cases h₂ with
    | i64Const h' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := IN.prefixFree 64 h h' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | f32Const h =>
    cases h₂ with
    | f32Const h' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := FN.prefixFree 32 h h' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch
  | f64Const h =>
    cases h₂ with
    | f64Const h' =>
      strip_opcode
      obtain ⟨rfl, rfl⟩ := FN.prefixFree 64 h h' heq
      exact ⟨rfl, rfl⟩
    | _ => opcode_mismatch

theorem Instr.pfLt (overlong : Bool) : ∀ n, PFLt overlong n
  | 0 => fun _ _ _ _ _ _ hl => absurd hl (Nat.not_lt_zero _)
  | n + 1 => Instr.pfLt_succ (Instr.pfLt overlong n)

private theorem Instrs.functional_aux {overlong : Bool} :
    ∀ (is : List Lime1.Instr) {b b' : Bytes} {is' : List Lime1.Instr},
      Instrs overlong b is → Instrs overlong b' is' → b = b' → is = is'
  | [], _, _, _, h, h', heq => by
    cases h
    cases h' with
    | nil => rfl
    | cons h₁ _ =>
      obtain ⟨op, rest, rfl, -, -⟩ := h₁.head
      simp at heq
  | _ :: xs, _, _, _, h, h', heq => by
    cases h with
    | cons h₁ hs =>
      cases h' with
      | nil =>
        obtain ⟨op, rest, rfl, -, -⟩ := h₁.head
        simp at heq
      | cons h₁' hs' =>
        obtain ⟨rfl, rfl⟩ := Instr.pfLt overlong _ (Nat.lt_succ_self _) h₁ h₁' heq
        rw [Instrs.functional_aux xs hs hs' (List.append_cancel_left heq)]

/-- Instruction sequences decode uniquely. -/
theorem Instrs.functional (overlong : Bool) : Functional (Instrs overlong) :=
  fun _ _ _ h h' => Instrs.functional_aux _ h h' rfl

theorem Instr.prefixFree (overlong : Bool) : PrefixFree (Instr overlong) :=
  fun b _ _ _ _ _ h h' heq => Instr.pfLt overlong (b.length + 1) (Nat.lt_succ_self _) h h' heq

theorem Expr.prefixFree (overlong : Bool) : PrefixFree (Expr overlong) := by
  intro b b' r r' e e' h h' heq
  cases h with
  | mk hs =>
    cases h' with
    | mk hs' =>
      simp only [List.append_assoc, List.singleton_append] at heq
      obtain ⟨rfl, rfl⟩ := Instrs.prefixFree_aux (Instr.pfLt overlong _) _
        (Nat.lt_succ_self _) hs hs' (by decide) (by decide) heq
      exact ⟨rfl, rfl⟩

end Silmaril.Wasm.Lime1.Binary
