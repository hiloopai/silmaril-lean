module

public import Silmaril.Wasm.Binary.Core.Opcodes

/-! # Core 3.0 binary format: opcode table lemmas

Each opcode table of `Core/Opcodes.lean` as a computable lookup, with the
soundness of the table against it (`lookup`, by cases and evaluation) and hence
determinism (`det`): an opcode names at most one instruction. Disjointness of tables
sharing an opcode space (`PlainOp`/`MemOp`, and the `0xFD` tables) is stated as
the lookups of the other tables failing.
-/

@[expose] public section

namespace Silmaril.Wasm.Binary.Core

/-- The `PlainOp` table as a lookup. -/
def plainOp? (op : UInt8) : Option (Wasm.Instr) :=
  match op.toNat with
  | 0x00 => some .unreachable
  | 0x01 => some .nop
  | 0x1A => some .drop
  | 0x1B => some (.select none)
  | 0x0A => some .throwRef
  | 0x0F => some .return_
  | 0xD1 => some .refIsNull
  | 0xD3 => some .refEq
  | 0xD4 => some .refAsNonNull
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
  | 0xC0 => some (.intUnOp .i32 (.extend .i8))
  | 0xC1 => some (.intUnOp .i32 (.extend .i16))
  | 0xC2 => some (.intUnOp .i64 (.extend .i8))
  | 0xC3 => some (.intUnOp .i64 (.extend .i16))
  | 0xC4 => some (.intUnOp .i64 (.extend .i32))
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

theorem PlainOp.lookup {op : UInt8} {i : Wasm.Instr} (h : PlainOp op i) :
    plainOp? op = some i := by
  cases h <;> rfl

theorem PlainOp.det {op : UInt8} {i i' : Wasm.Instr} (h : PlainOp op i)
    (h' : PlainOp op i') : i = i' :=
  Option.some.inj (h.lookup.symm.trans h'.lookup)

/-- The `PrefixFBOp` table as a lookup. -/
def prefixFBOp? (n : Nat) : Option (Wasm.Instr) :=
  match n with
  | 15 => some .arrayLen
  | 26 => some .anyConvertExtern
  | 27 => some .externConvertAny
  | 28 => some .refI31
  | 29 => some (.i31Get .signed)
  | 30 => some (.i31Get .unsigned)
  | _ => none

theorem PrefixFBOp.lookup {n : Nat} {i : Wasm.Instr} (h : PrefixFBOp n i) :
    prefixFBOp? n = some i := by
  cases h <;> rfl

theorem PrefixFBOp.det {n : Nat} {i i' : Wasm.Instr} (h : PrefixFBOp n i)
    (h' : PrefixFBOp n i') : i = i' :=
  Option.some.inj (h.lookup.symm.trans h'.lookup)

/-- The `PrefixFCOp` table as a lookup. -/
def prefixFCOp? (n : Nat) : Option (Wasm.Instr) :=
  match n with
  | 0 => some (.convert (.truncSat .f32 .i32 .signed))
  | 1 => some (.convert (.truncSat .f32 .i32 .unsigned))
  | 2 => some (.convert (.truncSat .f64 .i32 .signed))
  | 3 => some (.convert (.truncSat .f64 .i32 .unsigned))
  | 4 => some (.convert (.truncSat .f32 .i64 .signed))
  | 5 => some (.convert (.truncSat .f32 .i64 .unsigned))
  | 6 => some (.convert (.truncSat .f64 .i64 .signed))
  | 7 => some (.convert (.truncSat .f64 .i64 .unsigned))
  | _ => none

theorem PrefixFCOp.lookup {n : Nat} {i : Wasm.Instr} (h : PrefixFCOp n i) :
    prefixFCOp? n = some i := by
  cases h <;> rfl

theorem PrefixFCOp.det {n : Nat} {i i' : Wasm.Instr} (h : PrefixFCOp n i)
    (h' : PrefixFCOp n i') : i = i' :=
  Option.some.inj (h.lookup.symm.trans h'.lookup)

/-- The `PrefixFDOp` table as a lookup. -/
def prefixFDOp? (n : Nat) : Option (Wasm.Instr) :=
  match n with
  | 14 => some (.vecSwizzle .swizzle)
  | 256 => some (.vecSwizzle .relaxedSwizzle)
  | 15 => some (.vecSplat (.int .i8x16))
  | 16 => some (.vecSplat (.int .i16x8))
  | 17 => some (.vecSplat (.int .i32x4))
  | 18 => some (.vecSplat (.int .i64x2))
  | 19 => some (.vecSplat (.float .f32x4))
  | 20 => some (.vecSplat (.float .f64x2))
  | 35 => some (.vecIntRelOp .i8x16 .eq)
  | 36 => some (.vecIntRelOp .i8x16 .ne)
  | 37 => some (.vecIntRelOp .i8x16 (.lt .signed))
  | 38 => some (.vecIntRelOp .i8x16 (.lt .unsigned))
  | 39 => some (.vecIntRelOp .i8x16 (.gt .signed))
  | 40 => some (.vecIntRelOp .i8x16 (.gt .unsigned))
  | 41 => some (.vecIntRelOp .i8x16 (.le .signed))
  | 42 => some (.vecIntRelOp .i8x16 (.le .unsigned))
  | 43 => some (.vecIntRelOp .i8x16 (.ge .signed))
  | 44 => some (.vecIntRelOp .i8x16 (.ge .unsigned))
  | 45 => some (.vecIntRelOp .i16x8 .eq)
  | 46 => some (.vecIntRelOp .i16x8 .ne)
  | 47 => some (.vecIntRelOp .i16x8 (.lt .signed))
  | 48 => some (.vecIntRelOp .i16x8 (.lt .unsigned))
  | 49 => some (.vecIntRelOp .i16x8 (.gt .signed))
  | 50 => some (.vecIntRelOp .i16x8 (.gt .unsigned))
  | 51 => some (.vecIntRelOp .i16x8 (.le .signed))
  | 52 => some (.vecIntRelOp .i16x8 (.le .unsigned))
  | 53 => some (.vecIntRelOp .i16x8 (.ge .signed))
  | 54 => some (.vecIntRelOp .i16x8 (.ge .unsigned))
  | 55 => some (.vecIntRelOp .i32x4 .eq)
  | 56 => some (.vecIntRelOp .i32x4 .ne)
  | 57 => some (.vecIntRelOp .i32x4 (.lt .signed))
  | 58 => some (.vecIntRelOp .i32x4 (.lt .unsigned))
  | 59 => some (.vecIntRelOp .i32x4 (.gt .signed))
  | 60 => some (.vecIntRelOp .i32x4 (.gt .unsigned))
  | 61 => some (.vecIntRelOp .i32x4 (.le .signed))
  | 62 => some (.vecIntRelOp .i32x4 (.le .unsigned))
  | 63 => some (.vecIntRelOp .i32x4 (.ge .signed))
  | 64 => some (.vecIntRelOp .i32x4 (.ge .unsigned))
  | 65 => some (.vecFloatRelOp .f32x4 .eq)
  | 66 => some (.vecFloatRelOp .f32x4 .ne)
  | 67 => some (.vecFloatRelOp .f32x4 .lt)
  | 68 => some (.vecFloatRelOp .f32x4 .gt)
  | 69 => some (.vecFloatRelOp .f32x4 .le)
  | 70 => some (.vecFloatRelOp .f32x4 .ge)
  | 71 => some (.vecFloatRelOp .f64x2 .eq)
  | 72 => some (.vecFloatRelOp .f64x2 .ne)
  | 73 => some (.vecFloatRelOp .f64x2 .lt)
  | 74 => some (.vecFloatRelOp .f64x2 .gt)
  | 75 => some (.vecFloatRelOp .f64x2 .le)
  | 76 => some (.vecFloatRelOp .f64x2 .ge)
  | 77 => some (.vecUnOp .not)
  | 78 => some (.vecBinOp .and)
  | 79 => some (.vecBinOp .andnot)
  | 80 => some (.vecBinOp .or)
  | 81 => some (.vecBinOp .xor)
  | 82 => some (.vecTernOp .bitselect)
  | 83 => some (.vecTestOp .anyTrue)
  | 96 => some (.vecIntUnOp .i8x16 .abs)
  | 97 => some (.vecIntUnOp .i8x16 .neg)
  | 98 => some (.vecIntUnOp .i8x16 .popcnt)
  | 99 => some (.vecAllTrue .i8x16)
  | 100 => some (.vecBitmask .i8x16)
  | 101 => some (.vecNarrow .i16x8 .i8x16 .signed)
  | 102 => some (.vecNarrow .i16x8 .i8x16 .unsigned)
  | 107 => some (.vecShiftOp .i8x16 .shl)
  | 108 => some (.vecShiftOp .i8x16 (.shr .signed))
  | 109 => some (.vecShiftOp .i8x16 (.shr .unsigned))
  | 110 => some (.vecIntBinOp .i8x16 .add)
  | 111 => some (.vecIntBinOp .i8x16 (.addSat .signed))
  | 112 => some (.vecIntBinOp .i8x16 (.addSat .unsigned))
  | 113 => some (.vecIntBinOp .i8x16 .sub)
  | 114 => some (.vecIntBinOp .i8x16 (.subSat .signed))
  | 115 => some (.vecIntBinOp .i8x16 (.subSat .unsigned))
  | 118 => some (.vecIntBinOp .i8x16 (.min .signed))
  | 119 => some (.vecIntBinOp .i8x16 (.min .unsigned))
  | 120 => some (.vecIntBinOp .i8x16 (.max .signed))
  | 121 => some (.vecIntBinOp .i8x16 (.max .unsigned))
  | 123 => some (.vecIntBinOp .i8x16 .avgrU)
  | 124 => some (.vecExtUnOp .i8x16 .i16x8 (.extaddPairwise .signed))
  | 125 => some (.vecExtUnOp .i8x16 .i16x8 (.extaddPairwise .unsigned))
  | 128 => some (.vecIntUnOp .i16x8 .abs)
  | 129 => some (.vecIntUnOp .i16x8 .neg)
  | 130 => some (.vecIntBinOp .i16x8 .q15mulrSatS)
  | 142 => some (.vecIntBinOp .i16x8 .add)
  | 143 => some (.vecIntBinOp .i16x8 (.addSat .signed))
  | 144 => some (.vecIntBinOp .i16x8 (.addSat .unsigned))
  | 145 => some (.vecIntBinOp .i16x8 .sub)
  | 146 => some (.vecIntBinOp .i16x8 (.subSat .signed))
  | 147 => some (.vecIntBinOp .i16x8 (.subSat .unsigned))
  | 149 => some (.vecIntBinOp .i16x8 .mul)
  | 150 => some (.vecIntBinOp .i16x8 (.min .signed))
  | 151 => some (.vecIntBinOp .i16x8 (.min .unsigned))
  | 152 => some (.vecIntBinOp .i16x8 (.max .signed))
  | 153 => some (.vecIntBinOp .i16x8 (.max .unsigned))
  | 155 => some (.vecIntBinOp .i16x8 .avgrU)
  | 273 => some (.vecIntBinOp .i16x8 .relaxedQ15mulrS)
  | 131 => some (.vecAllTrue .i16x8)
  | 132 => some (.vecBitmask .i16x8)
  | 133 => some (.vecNarrow .i32x4 .i16x8 .signed)
  | 134 => some (.vecNarrow .i32x4 .i16x8 .unsigned)
  | 135 => some (.vecConvert (.int .i8x16) (.int .i16x8) (.extend .low .signed))
  | 136 => some (.vecConvert (.int .i8x16) (.int .i16x8) (.extend .high .signed))
  | 137 => some (.vecConvert (.int .i8x16) (.int .i16x8) (.extend .low .unsigned))
  | 138 => some (.vecConvert (.int .i8x16) (.int .i16x8) (.extend .high .unsigned))
  | 139 => some (.vecShiftOp .i16x8 .shl)
  | 140 => some (.vecShiftOp .i16x8 (.shr .signed))
  | 141 => some (.vecShiftOp .i16x8 (.shr .unsigned))
  | 156 => some (.vecExtBinOp .i8x16 .i16x8 (.extmul .low .signed))
  | 157 => some (.vecExtBinOp .i8x16 .i16x8 (.extmul .high .signed))
  | 158 => some (.vecExtBinOp .i8x16 .i16x8 (.extmul .low .unsigned))
  | 159 => some (.vecExtBinOp .i8x16 .i16x8 (.extmul .high .unsigned))
  | 274 => some (.vecExtBinOp .i8x16 .i16x8 .relaxedDotS)
  | 126 => some (.vecExtUnOp .i16x8 .i32x4 (.extaddPairwise .signed))
  | 127 => some (.vecExtUnOp .i16x8 .i32x4 (.extaddPairwise .unsigned))
  | 160 => some (.vecIntUnOp .i32x4 .abs)
  | 161 => some (.vecIntUnOp .i32x4 .neg)
  | 163 => some (.vecAllTrue .i32x4)
  | 164 => some (.vecBitmask .i32x4)
  | 167 => some (.vecConvert (.int .i16x8) (.int .i32x4) (.extend .low .signed))
  | 168 => some (.vecConvert (.int .i16x8) (.int .i32x4) (.extend .high .signed))
  | 169 => some (.vecConvert (.int .i16x8) (.int .i32x4) (.extend .low .unsigned))
  | 170 => some (.vecConvert (.int .i16x8) (.int .i32x4) (.extend .high .unsigned))
  | 171 => some (.vecShiftOp .i32x4 .shl)
  | 172 => some (.vecShiftOp .i32x4 (.shr .signed))
  | 173 => some (.vecShiftOp .i32x4 (.shr .unsigned))
  | 174 => some (.vecIntBinOp .i32x4 .add)
  | 177 => some (.vecIntBinOp .i32x4 .sub)
  | 181 => some (.vecIntBinOp .i32x4 .mul)
  | 182 => some (.vecIntBinOp .i32x4 (.min .signed))
  | 183 => some (.vecIntBinOp .i32x4 (.min .unsigned))
  | 184 => some (.vecIntBinOp .i32x4 (.max .signed))
  | 185 => some (.vecIntBinOp .i32x4 (.max .unsigned))
  | 186 => some (.vecExtBinOp .i16x8 .i32x4 .dotS)
  | 188 => some (.vecExtBinOp .i16x8 .i32x4 (.extmul .low .signed))
  | 189 => some (.vecExtBinOp .i16x8 .i32x4 (.extmul .high .signed))
  | 190 => some (.vecExtBinOp .i16x8 .i32x4 (.extmul .low .unsigned))
  | 191 => some (.vecExtBinOp .i16x8 .i32x4 (.extmul .high .unsigned))
  | 275 => some (.vecExtTernOp .i8x16 .i32x4 .relaxedDotAddS)
  | 192 => some (.vecIntUnOp .i64x2 .abs)
  | 193 => some (.vecIntUnOp .i64x2 .neg)
  | 195 => some (.vecAllTrue .i64x2)
  | 196 => some (.vecBitmask .i64x2)
  | 199 => some (.vecConvert (.int .i32x4) (.int .i64x2) (.extend .low .signed))
  | 200 => some (.vecConvert (.int .i32x4) (.int .i64x2) (.extend .high .signed))
  | 201 => some (.vecConvert (.int .i32x4) (.int .i64x2) (.extend .low .unsigned))
  | 202 => some (.vecConvert (.int .i32x4) (.int .i64x2) (.extend .high .unsigned))
  | 203 => some (.vecShiftOp .i64x2 .shl)
  | 204 => some (.vecShiftOp .i64x2 (.shr .signed))
  | 205 => some (.vecShiftOp .i64x2 (.shr .unsigned))
  | 206 => some (.vecIntBinOp .i64x2 .add)
  | 209 => some (.vecIntBinOp .i64x2 .sub)
  | 213 => some (.vecIntBinOp .i64x2 .mul)
  | 214 => some (.vecIntRelOp .i64x2 .eq)
  | 215 => some (.vecIntRelOp .i64x2 .ne)
  | 216 => some (.vecIntRelOp .i64x2 (.lt .signed))
  | 217 => some (.vecIntRelOp .i64x2 (.gt .signed))
  | 218 => some (.vecIntRelOp .i64x2 (.le .signed))
  | 219 => some (.vecIntRelOp .i64x2 (.ge .signed))
  | 220 => some (.vecExtBinOp .i32x4 .i64x2 (.extmul .low .signed))
  | 221 => some (.vecExtBinOp .i32x4 .i64x2 (.extmul .high .signed))
  | 222 => some (.vecExtBinOp .i32x4 .i64x2 (.extmul .low .unsigned))
  | 223 => some (.vecExtBinOp .i32x4 .i64x2 (.extmul .high .unsigned))
  | 103 => some (.vecFloatUnOp .f32x4 .ceil)
  | 104 => some (.vecFloatUnOp .f32x4 .floor)
  | 105 => some (.vecFloatUnOp .f32x4 .trunc)
  | 106 => some (.vecFloatUnOp .f32x4 .nearest)
  | 224 => some (.vecFloatUnOp .f32x4 .abs)
  | 225 => some (.vecFloatUnOp .f32x4 .neg)
  | 227 => some (.vecFloatUnOp .f32x4 .sqrt)
  | 228 => some (.vecFloatBinOp .f32x4 .add)
  | 229 => some (.vecFloatBinOp .f32x4 .sub)
  | 230 => some (.vecFloatBinOp .f32x4 .mul)
  | 231 => some (.vecFloatBinOp .f32x4 .div)
  | 232 => some (.vecFloatBinOp .f32x4 .min)
  | 233 => some (.vecFloatBinOp .f32x4 .max)
  | 234 => some (.vecFloatBinOp .f32x4 .pmin)
  | 235 => some (.vecFloatBinOp .f32x4 .pmax)
  | 269 => some (.vecFloatBinOp .f32x4 .relaxedMin)
  | 270 => some (.vecFloatBinOp .f32x4 .relaxedMax)
  | 261 => some (.vecFloatTernOp .f32x4 .relaxedMadd)
  | 262 => some (.vecFloatTernOp .f32x4 .relaxedNmadd)
  | 116 => some (.vecFloatUnOp .f64x2 .ceil)
  | 117 => some (.vecFloatUnOp .f64x2 .floor)
  | 122 => some (.vecFloatUnOp .f64x2 .trunc)
  | 148 => some (.vecFloatUnOp .f64x2 .nearest)
  | 236 => some (.vecFloatUnOp .f64x2 .abs)
  | 237 => some (.vecFloatUnOp .f64x2 .neg)
  | 239 => some (.vecFloatUnOp .f64x2 .sqrt)
  | 240 => some (.vecFloatBinOp .f64x2 .add)
  | 241 => some (.vecFloatBinOp .f64x2 .sub)
  | 242 => some (.vecFloatBinOp .f64x2 .mul)
  | 243 => some (.vecFloatBinOp .f64x2 .div)
  | 244 => some (.vecFloatBinOp .f64x2 .min)
  | 245 => some (.vecFloatBinOp .f64x2 .max)
  | 246 => some (.vecFloatBinOp .f64x2 .pmin)
  | 247 => some (.vecFloatBinOp .f64x2 .pmax)
  | 271 => some (.vecFloatBinOp .f64x2 .relaxedMin)
  | 272 => some (.vecFloatBinOp .f64x2 .relaxedMax)
  | 263 => some (.vecFloatTernOp .f64x2 .relaxedMadd)
  | 264 => some (.vecFloatTernOp .f64x2 .relaxedNmadd)
  | 265 => some (.vecIntTernOp .i8x16 .relaxedLaneSelect)
  | 266 => some (.vecIntTernOp .i16x8 .relaxedLaneSelect)
  | 267 => some (.vecIntTernOp .i32x4 .relaxedLaneSelect)
  | 268 => some (.vecIntTernOp .i64x2 .relaxedLaneSelect)
  | 94 => some (.vecConvert (.float .f64x2) (.float .f32x4) .demoteZero)
  | 95 => some (.vecConvert (.float .f32x4) (.float .f64x2) .promoteLow)
  | 248 => some (.vecConvert (.float .f32x4) (.int .i32x4) (.truncSat .signed false))
  | 249 => some (.vecConvert (.float .f32x4) (.int .i32x4) (.truncSat .unsigned false))
  | 250 => some (.vecConvert (.int .i32x4) (.float .f32x4) (.convert none .signed))
  | 251 => some (.vecConvert (.int .i32x4) (.float .f32x4) (.convert none .unsigned))
  | 252 => some (.vecConvert (.float .f64x2) (.int .i32x4) (.truncSat .signed true))
  | 253 => some (.vecConvert (.float .f64x2) (.int .i32x4) (.truncSat .unsigned true))
  | 254 => some (.vecConvert (.int .i32x4) (.float .f64x2) (.convert (some .low) .signed))
  | 255 => some (.vecConvert (.int .i32x4) (.float .f64x2) (.convert (some .low) .unsigned))
  | 257 => some (.vecConvert (.float .f32x4) (.int .i32x4) (.relaxedTrunc .signed false))
  | 258 => some (.vecConvert (.float .f32x4) (.int .i32x4) (.relaxedTrunc .unsigned false))
  | 259 => some (.vecConvert (.float .f64x2) (.int .i32x4) (.relaxedTrunc .signed true))
  | 260 => some (.vecConvert (.float .f64x2) (.int .i32x4) (.relaxedTrunc .unsigned true))
  | _ => none

theorem PrefixFDOp.lookup {n : Nat} {i : Wasm.Instr} (h : PrefixFDOp n i) :
    prefixFDOp? n = some i := by
  cases h <;> rfl

theorem PrefixFDOp.det {n : Nat} {i i' : Wasm.Instr} (h : PrefixFDOp n i)
    (h' : PrefixFDOp n i') : i = i' :=
  Option.some.inj (h.lookup.symm.trans h'.lookup)

/-- The `MemOp` table as a lookup. -/
def memOp? (op : UInt8) : Option (MemIdx → MemArg → Wasm.Instr) :=
  match op.toNat with
  | 0x28 => some (fun x ao => .intLoad .i32 none x ao)
  | 0x29 => some (fun x ao => .intLoad .i64 none x ao)
  | 0x2A => some (fun x ao => .floatLoad .f32 x ao)
  | 0x2B => some (fun x ao => .floatLoad .f64 x ao)
  | 0x2C => some (fun x ao => .intLoad .i32 (some (.i8, .signed)) x ao)
  | 0x2D => some (fun x ao => .intLoad .i32 (some (.i8, .unsigned)) x ao)
  | 0x2E => some (fun x ao => .intLoad .i32 (some (.i16, .signed)) x ao)
  | 0x2F => some (fun x ao => .intLoad .i32 (some (.i16, .unsigned)) x ao)
  | 0x30 => some (fun x ao => .intLoad .i64 (some (.i8, .signed)) x ao)
  | 0x31 => some (fun x ao => .intLoad .i64 (some (.i8, .unsigned)) x ao)
  | 0x32 => some (fun x ao => .intLoad .i64 (some (.i16, .signed)) x ao)
  | 0x33 => some (fun x ao => .intLoad .i64 (some (.i16, .unsigned)) x ao)
  | 0x34 => some (fun x ao => .intLoad .i64 (some (.i32, .signed)) x ao)
  | 0x35 => some (fun x ao => .intLoad .i64 (some (.i32, .unsigned)) x ao)
  | 0x36 => some (fun x ao => .intStore .i32 none x ao)
  | 0x37 => some (fun x ao => .intStore .i64 none x ao)
  | 0x38 => some (fun x ao => .floatStore .f32 x ao)
  | 0x39 => some (fun x ao => .floatStore .f64 x ao)
  | 0x3A => some (fun x ao => .intStore .i32 (some .i8) x ao)
  | 0x3B => some (fun x ao => .intStore .i32 (some .i16) x ao)
  | 0x3C => some (fun x ao => .intStore .i64 (some .i8) x ao)
  | 0x3D => some (fun x ao => .intStore .i64 (some .i16) x ao)
  | 0x3E => some (fun x ao => .intStore .i64 (some .i32) x ao)
  | _ => none

theorem MemOp.lookup {op : UInt8} {i : MemIdx → MemArg → Wasm.Instr} (h : MemOp op i) :
    memOp? op = some i := by
  cases h <;> rfl

theorem MemOp.det {op : UInt8} {i i' : MemIdx → MemArg → Wasm.Instr} (h : MemOp op i)
    (h' : MemOp op i') : i = i' :=
  Option.some.inj (h.lookup.symm.trans h'.lookup)

/-- The `VecMemOp` table as a lookup. -/
def vecMemOp? (n : Nat) : Option (MemIdx → MemArg → Wasm.Instr) :=
  match n with
  | 0 => some (fun x ao => .vecLoad .full x ao)
  | 1 => some (fun x ao => .vecLoad (.extend8x8 .signed) x ao)
  | 2 => some (fun x ao => .vecLoad (.extend8x8 .unsigned) x ao)
  | 3 => some (fun x ao => .vecLoad (.extend16x4 .signed) x ao)
  | 4 => some (fun x ao => .vecLoad (.extend16x4 .unsigned) x ao)
  | 5 => some (fun x ao => .vecLoad (.extend32x2 .signed) x ao)
  | 6 => some (fun x ao => .vecLoad (.extend32x2 .unsigned) x ao)
  | 7 => some (fun x ao => .vecLoad (.splat .i8) x ao)
  | 8 => some (fun x ao => .vecLoad (.splat .i16) x ao)
  | 9 => some (fun x ao => .vecLoad (.splat .i32) x ao)
  | 10 => some (fun x ao => .vecLoad (.splat .i64) x ao)
  | 11 => some (fun x ao => .vecStore x ao)
  | 92 => some (fun x ao => .vecLoad .zero32 x ao)
  | 93 => some (fun x ao => .vecLoad .zero64 x ao)
  | _ => none

theorem VecMemOp.lookup {n : Nat} {i : MemIdx → MemArg → Wasm.Instr} (h : VecMemOp n i) :
    vecMemOp? n = some i := by
  cases h <;> rfl

theorem VecMemOp.det {n : Nat} {i i' : MemIdx → MemArg → Wasm.Instr} (h : VecMemOp n i)
    (h' : VecMemOp n i') : i = i' :=
  Option.some.inj (h.lookup.symm.trans h'.lookup)

/-- The `VecMemLaneOp` table as a lookup. -/
def vecMemLaneOp? (n : Nat) : Option (MemIdx → MemArg → LaneIdx → Wasm.Instr) :=
  match n with
  | 84 => some (fun x ao i => .vecLoadLane .i8 x ao i)
  | 85 => some (fun x ao i => .vecLoadLane .i16 x ao i)
  | 86 => some (fun x ao i => .vecLoadLane .i32 x ao i)
  | 87 => some (fun x ao i => .vecLoadLane .i64 x ao i)
  | 88 => some (fun x ao i => .vecStoreLane .i8 x ao i)
  | 89 => some (fun x ao i => .vecStoreLane .i16 x ao i)
  | 90 => some (fun x ao i => .vecStoreLane .i32 x ao i)
  | 91 => some (fun x ao i => .vecStoreLane .i64 x ao i)
  | _ => none

theorem VecMemLaneOp.lookup {n : Nat} {i : MemIdx → MemArg → LaneIdx → Wasm.Instr}
    (h : VecMemLaneOp n i) :
    vecMemLaneOp? n = some i := by
  cases h <;> rfl

theorem VecMemLaneOp.det {n : Nat} {i i' : MemIdx → MemArg → LaneIdx → Wasm.Instr}
    (h : VecMemLaneOp n i)
    (h' : VecMemLaneOp n i') : i = i' :=
  Option.some.inj (h.lookup.symm.trans h'.lookup)

/-- The `VecLaneOp` table as a lookup. -/
def vecLaneOp? (n : Nat) : Option (LaneIdx → Wasm.Instr) :=
  match n with
  | 21 => some (fun l => .vecExtractLane (.int .i8x16) (some .signed) l)
  | 22 => some (fun l => .vecExtractLane (.int .i8x16) (some .unsigned) l)
  | 23 => some (fun l => .vecReplaceLane (.int .i8x16) l)
  | 24 => some (fun l => .vecExtractLane (.int .i16x8) (some .signed) l)
  | 25 => some (fun l => .vecExtractLane (.int .i16x8) (some .unsigned) l)
  | 26 => some (fun l => .vecReplaceLane (.int .i16x8) l)
  | 27 => some (fun l => .vecExtractLane (.int .i32x4) none l)
  | 28 => some (fun l => .vecReplaceLane (.int .i32x4) l)
  | 29 => some (fun l => .vecExtractLane (.int .i64x2) none l)
  | 30 => some (fun l => .vecReplaceLane (.int .i64x2) l)
  | 31 => some (fun l => .vecExtractLane (.float .f32x4) none l)
  | 32 => some (fun l => .vecReplaceLane (.float .f32x4) l)
  | 33 => some (fun l => .vecExtractLane (.float .f64x2) none l)
  | 34 => some (fun l => .vecReplaceLane (.float .f64x2) l)
  | _ => none

theorem VecLaneOp.lookup {n : Nat} {i : LaneIdx → Wasm.Instr} (h : VecLaneOp n i) :
    vecLaneOp? n = some i := by
  cases h <;> rfl

theorem VecLaneOp.det {n : Nat} {i i' : LaneIdx → Wasm.Instr} (h : VecLaneOp n i)
    (h' : VecLaneOp n i') : i = i' :=
  Option.some.inj (h.lookup.symm.trans h'.lookup)

/-! ## Disjointness -/

theorem MemOp.plainOp?_eq_none {op : UInt8} {mk : MemIdx → MemArg → Wasm.Instr}
    (h : MemOp op mk) : plainOp? op = none := by
  cases h <;> rfl

theorem VecMemOp.prefixFDOp?_eq_none {n : Nat} {mk : MemIdx → MemArg → Wasm.Instr}
    (h : VecMemOp n mk) : prefixFDOp? n = none := by
  cases h <;> rfl

theorem VecMemLaneOp.lookups_eq_none {n : Nat} {mk : MemIdx → MemArg → LaneIdx → Wasm.Instr}
    (h : VecMemLaneOp n mk) : prefixFDOp? n = none ∧ vecMemOp? n = none := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem VecLaneOp.lookups_eq_none {n : Nat} {mk : LaneIdx → Wasm.Instr} (h : VecLaneOp n mk) :
    prefixFDOp? n = none ∧ vecMemOp? n = none ∧ vecMemLaneOp? n = none := by
  cases h <;> exact ⟨rfl, rfl, rfl⟩

/-- No single-byte instruction is `else` (`0x05`) or `end` (`0x0B`). -/
theorem PlainOp.ne_end {op : UInt8} {i : Wasm.Instr} (h : PlainOp op i) :
    op ≠ 0x0B ∧ op ≠ 0x05 := by
  cases h <;> decide

theorem MemOp.ne_end {op : UInt8} {mk : MemIdx → MemArg → Wasm.Instr} (h : MemOp op mk) :
    op ≠ 0x0B ∧ op ≠ 0x05 := by
  cases h <;> decide

end Silmaril.Wasm.Binary.Core
