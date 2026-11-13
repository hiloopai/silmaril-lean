module

public import Silmaril.Wasm.Unified.Sig.Defs
public import Silmaril.Wasm.Models.Features.Defs

/-!
# Version feature signatures

The feature signatures of the Wasm versions and dialects of `Silmaril.Wasm.Models.Features`
(1.0, 2.0, 3.0, Lime1, WasmFX, wasmi 2.0.0, functional Wasm, ...), as signatures of the unified
institution (`Silmaril.Wasm.Unified.FSig`). A feature set `S` gives the signature `vsig S` whose
opcodes are the binary opcodes whose capabilities are all in `S`; every version signature has
the same syntactic typing `tyU`, so inclusions of feature sets give inclusions of signatures
(`Thms`).

* `OpKind`, `kindPlain`, `kindGC`, `kindMisc`, `kindVec`, `kind`, `need`: **the opcode table**
  at capability granularity (an opcode's class and the capabilities of the class), read off the binary format of Wasm 3.0 (`5.3-binary.instructions`) and the
  stack-switching proposal: the capabilities (`Silmaril.Wasm.Models.Cap`) an opcode needs, `none`
  for a code no standard capability covers (the threads prefix `0xFE`, unassigned codes, open
  names);
* `tyU`: the syntactic typing (immediates, nested blocks, handler table) of the structured
  and indexed opcodes; opcodes not listed get no immediates. It is one typing for every version
  signature, which is all an inclusion needs; refining it changes no result here;
* `inB S o`: the opcode is typed within `S` (Boolean); `vsig S`: **the signature of `S`**;
* named signatures `bsig10`, `bsig20`, `bsig30`, `bsigLime1`, `bsigFX`, `bsigWasmi`;
* named opcodes for examples (`opTableGrow`, `opSelect`, `opResume`, ...).

Choices worth recording:

* Opcodes are classified by the capabilities of the *instruction*, not of its immediates:
  `select t` (`0x1C`) needs `refTypes` whatever `t` is, block types with a type index
  (multi-value) and memory indices other than 0 (multi-memory) are not separate opcodes;
  validation (a model's `ok`) is where such immediates are checked.
* Features without an opcode of their own (`extConst`, `multiValue`, `memory64`,
  `callIndirectOverlong`, `customPageSizes`) contribute no opcodes. Hence `vsig lime1 ≤ vsig v20`
  at the opcode level although `lime1 ≰ v20` as feature sets (`Thms`): the difference between
  Lime1 and 2.0 that is not an opcode is in validation.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm.Models

/-- The opcode classes of the table: each class needs a fixed list of capabilities
(`OpKind.caps`). -/
inductive OpKind where
  | control | exn | directCall | callIndirect | tailCall | tailCallIndirect | callRef
  | returnCallRef | selectT | globalGet | globalSet | tableAccess | memFloat | memInt | memSize
  | intNum | floatNum | conv | signExt | refBasic | refEq | refTyped | stackSwitching
  | gcImm | gcMut | satConv | bulkMem | bulkMemOpt | bulkTable | tableRef | wideArith
  | simd | relaxedSimd
  deriving DecidableEq, Repr

/-- The capabilities of an opcode class. -/
def OpKind.caps : OpKind → List Cap
  | .control => [.control]
  | .exn => [.exn]
  | .directCall => [.directCall]
  | .callIndirect => [.callIndirect]
  | .tailCall => [.tailCall]
  | .tailCallIndirect => [.tailCall, .callIndirect]
  | .callRef => [.typedFuncRef]
  | .returnCallRef => [.typedFuncRef, .tailCall]
  | .selectT => [.refTypes]
  | .globalGet => [.globals]
  | .globalSet => [.mutGlobal]
  | .tableAccess => [.refTypes, .table]
  | .memFloat => [.memory, .intNum, .floatNum]
  | .memInt => [.memory, .intNum]
  | .memSize => [.memory]
  | .intNum => [.intNum]
  | .floatNum => [.floatNum]
  | .conv => [.intNum, .floatNum]
  | .signExt => [.signExt]
  | .refBasic => [.refTypes]
  | .refEq => [.gcImm]
  | .refTyped => [.typedFuncRef]
  | .stackSwitching => [.stackSwitching]
  | .gcImm => [.gcImm]
  | .gcMut => [.gcMut]
  | .satConv => [.satConv]
  | .bulkMem => [.bulkMemory, .memory]
  | .bulkMemOpt => [.bulkMemoryOpt, .memory]
  | .bulkTable => [.bulkMemory, .table]
  | .tableRef => [.refTypes, .table]
  | .wideArith => [.wideArith]
  | .simd => [.simd]
  | .relaxedSimd => [.relaxedSimd]

/-- The class of an unprefixed opcode. -/
def kindPlain (n : Nat) : Option OpKind :=
  if n ≤ 0x04 || (0x0B ≤ n && n ≤ 0x0F) || n = 0x1A || n = 0x1B || (0x20 ≤ n && n ≤ 0x22) then
    some .control
  else if n = 0x08 || n = 0x0A || n = 0x1F then some .exn
  else if n = 0x10 then some .directCall
  else if n = 0x11 then some .callIndirect
  else if n = 0x12 then some .tailCall
  else if n = 0x13 then some .tailCallIndirect
  else if n = 0x14 then some .callRef
  else if n = 0x15 then some .returnCallRef
  else if n = 0x1C then some .selectT
  else if n = 0x23 then some .globalGet
  else if n = 0x24 then some .globalSet
  else if n = 0x25 || n = 0x26 then some .tableAccess
  else if n = 0x2A || n = 0x2B || n = 0x38 || n = 0x39 then some .memFloat
  else if 0x28 ≤ n && n ≤ 0x3E then some .memInt
  else if n = 0x3F || n = 0x40 then some .memSize
  else if n = 0x41 || n = 0x42 || (0x45 ≤ n && n ≤ 0x5A) || (0x67 ≤ n && n ≤ 0x8A) ||
      n = 0xA7 || n = 0xAC || n = 0xAD then some .intNum
  else if n = 0x43 || n = 0x44 || (0x5B ≤ n && n ≤ 0x66) || (0x8B ≤ n && n ≤ 0xA6) ||
      n = 0xB6 || n = 0xBB then some .floatNum
  else if 0xA8 ≤ n && n ≤ 0xBF then some .conv
  else if 0xC0 ≤ n && n ≤ 0xC4 then some .signExt
  else if n = 0xD0 || n = 0xD1 || n = 0xD2 then some .refBasic
  else if n = 0xD3 then some .refEq
  else if 0xD4 ≤ n && n ≤ 0xD6 then some .refTyped
  else if 0xE0 ≤ n && n ≤ 0xE5 then some .stackSwitching
  else none

/-- The class of a `0xFB` (GC) opcode. -/
def kindGC (n : Nat) : Option OpKind :=
  if n = 0x05 || n = 0x0E || (0x10 ≤ n && n ≤ 0x13) then some .gcMut
  else if n ≤ 0x1E then some .gcImm
  else none

/-- The class of a `0xFC` (saturating, bulk, table, wide-arithmetic) opcode. -/
def kindMisc (n : Nat) : Option OpKind :=
  if n ≤ 0x07 then some .satConv
  else if n = 0x08 || n = 0x09 then some .bulkMem
  else if n = 0x0A || n = 0x0B then some .bulkMemOpt
  else if 0x0C ≤ n && n ≤ 0x0E then some .bulkTable
  else if 0x0F ≤ n && n ≤ 0x11 then some .tableRef
  else if 0x13 ≤ n && n ≤ 0x16 then some .wideArith
  else none

/-- The class of a `0xFD` (vector) opcode. -/
def kindVec (n : Nat) : Option OpKind :=
  if 0x100 ≤ n && n ≤ 0x113 then some .relaxedSimd
  else if n ≤ 0xFF then some .simd
  else none

/-- The class of an opcode (`none`: no standard capability covers it). -/
def kind : Opcode → Option OpKind
  | .bin none n => kindPlain n
  | .bin (some 0xFB) n => kindGC n
  | .bin (some 0xFC) n => kindMisc n
  | .bin (some 0xFD) n => kindVec n
  | _ => none

/-- **The opcode table**: the capabilities an opcode needs. -/
def need (o : Opcode) : Option (List Cap) := (kind o).map OpKind.caps

/-- The opcode is typed within the feature set `S`. -/
def inB (S : FeatureSet) (o : Opcode) : Bool :=
  match need o with
  | some l => l.all fun c => S.has c
  | none => false

/-- The number of immediates of an unprefixed opcode. -/
def immsPlain (n : Nat) : Nat :=
  if n = 0x02 || n = 0x03 || n = 0x04 || n = 0x1F || n = 0x08 || n = 0x0C || n = 0x0D ||
      n = 0x10 || n = 0x12 || n = 0x14 || n = 0x15 || n = 0x1C || (0x20 ≤ n && n ≤ 0x26) ||
      (0x3F ≤ n && n ≤ 0x44) || n = 0xD0 || n = 0xD2 || n = 0xD5 || n = 0xD6 || n = 0xE0 ||
      n = 0xE2 || n = 0xE3 then 1
  else if n = 0x0E || n = 0x11 || n = 0x13 || (0x28 ≤ n && n ≤ 0x3E) || n = 0xE1 ||
      n = 0xE4 || n = 0xE5 then 2
  else 0

/-- The number of immediates of a `0xFC` opcode. -/
def immsMisc (n : Nat) : Nat :=
  if n = 0x08 || n = 0x0A || n = 0x0C || n = 0x0E then 2
  else if n = 0x09 || n = 0x0B || n = 0x0D || (0x0F ≤ n && n ≤ 0x11) then 1
  else 0

/-- **The syntactic typing** shared by every version signature: immediates, nested blocks
(`block`, `loop`: one; `if`: two; `try_table`: one) and handler tables (`try_table`,
`resume`, `resume_throw`). -/
def tyU : Opcode → OpTy
  | .bin none n =>
    ⟨immsPlain n, if n = 0x04 then 2 else if n = 0x02 || n = 0x03 || n = 0x1F then 1 else 0,
      n = 0x1F || n = 0xE3 || n = 0xE4⟩
  | .bin (some 0xFC) n => ⟨immsMisc n, 0, false⟩
  | _ => ⟨0, 0, false⟩

/-- **The signature of a feature set**: the opcodes typed within it, with the shared typing. -/
def vsig (S : FeatureSet) : FSig := ⟨{o | inB S o = true}, tyU⟩

/-- Wasm 1.0. -/
abbrev bsig10 : FSig := vsig v10
/-- Wasm 2.0. -/
abbrev bsig20 : FSig := vsig v20
/-- Wasm 3.0. -/
abbrev bsig30 : FSig := vsig v30
/-- Lime1. -/
abbrev bsigLime1 : FSig := vsig lime1
/-- WasmFX (3.0 with stack switching). -/
abbrev bsigFX : FSig := vsig wasmFX
/-- wasmi 2.0.0. -/
abbrev bsigWasmi : FSig := vsig wasmi200

/-- `table.grow`. -/
def opTableGrow : Opcode := .bin (some 0xFC) 0x0F
/-- `select` (untyped). -/
def opSelect : Opcode := .bin none 0x1B
/-- `i32.add`. -/
def opI32Add : Opcode := .bin none 0x6A
/-- `f32.add`. -/
def opF32Add : Opcode := .bin none 0x92
/-- `memory.copy`. -/
def opMemoryCopy : Opcode := .bin (some 0xFC) 0x0A
/-- `return_call`. -/
def opReturnCall : Opcode := .bin none 0x12
/-- `resume` (stack switching). -/
def opResume : Opcode := .bin none 0xE3
/-- `try_table`. -/
def opTryTable : Opcode := .bin none 0x1F
/-- `i64.add128` (wide arithmetic). -/
def opI64Add128 : Opcode := .bin (some 0xFC) 0x13

end Silmaril.Wasm.Unified.Versions
