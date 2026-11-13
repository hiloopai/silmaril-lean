module

public import Silmaril.Wasm.Unified.Versions.Defs
public import Silmaril.Wasm.Binary.Core.OpcodesProps

/-!
# Binary opcodes renamed to the named 3.0 opcodes

The binary presentation of the version signatures as signatures of the unified institution
whose opcodes **decode** to Core 3.0 instructions, and the renaming morphism to the named
presentation inside `sig30` (`Silmaril.Wasm.Unified.Versions.Named`).

* `binInstr? o`: **the decoding of a binary opcode** to a representative Core 3.0 instruction
  (immediates set to `0`, empty bodies, empty block type). Immediate-free opcodes use silmaril's
  opcode lookups (`Silmaril.Wasm.Binary.Core.plainOp?`, `prefixFBOp?`, `prefixFCOp?`,
  `prefixFDOp?`, and the memory and lane families `memOp?`, `vecMemOp?`, `vecMemLaneOp?`,
  `vecLaneOp?`); the opcodes with other immediates (control, indices, constants, tables, bulk
  memory, GC) are transcribed from the rules of `Silmaril.Wasm.Binary.Core.Instr`
  (`5.3-binary.instructions`). Unassigned codes and the stack-switching codes `0xE0`–`0xE5`
  (not Core 3.0) decode to `none`.
* `tyBin o`: the typing of a binary opcode, the typing `arity30` of the named opcode it decodes
  to;
* `bsigB S`: **the binary signature of `S`**: the decodable opcodes whose representative is in
  `S` at its head (`Silmaril.Wasm.Models.Instr.headB`);
* `renB S : bsigB S ⟶ nsig S`: **the renaming morphism**, a binary opcode to the named opcode
  `head` of its decoding; `ren30 : bsigB v30 ⟶ sig30` its composite with `nsig v30 ⊆ sig30`;
* `binAt S P f okc x`: **Core 3.0 on binary opcodes**, the reduct along `renB S` of
  `coreSAt S` (the model of `core|S`).

Choices worth recording:

* The binary signature here is not the capability-level `vsig S` of `Versions.Sig`. `vsig`
  gives every opcode the coarse typing `tyU` (no immediates for vector memory opcodes, GC
  opcodes, ...) and contains codes no instruction has; a renaming must preserve typing, so the
  decoding renaming cannot start at `vsig S` (`Thms`: `vsig_no_decode`). `bsigB S` keeps the
  binary opcode names and takes the typing from the decoding.
* The renaming is not injective: `select` (`0x1B`) and `select t` (`0x1C`) are one named
  opcode, `if` with and without `else` are one binary opcode (`0x04`), as in the binary format.

New definitions; the opcode transcription is copied from silmaril's binary grammar.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open CategoryTheory Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Numerics (Profile)

/-- Index `0`. -/
abbrev i0 {k : IndexKind} : Idx k := ⟨0⟩

/-- The memory argument with alignment and offset `0`. -/
abbrev ma0 : MemArg := ⟨0, 0⟩

/-- Unprefixed opcodes with immediates other than a memory argument. -/
def plainImm? : Nat → Option Instr
  | 0x02 => some (.block .empty [])
  | 0x03 => some (.loop .empty [])
  | 0x04 => some (.if_ .empty [] [])
  | 0x08 => some (.throw i0)
  | 0x0C => some (.br i0)
  | 0x0D => some (.brIf i0)
  | 0x0E => some (.brTable [] i0)
  | 0x10 => some (.call i0)
  | 0x11 => some (.callIndirect i0 i0)
  | 0x12 => some (.returnCall i0)
  | 0x13 => some (.returnCallIndirect i0 i0)
  | 0x14 => some (.callRef i0)
  | 0x15 => some (.returnCallRef i0)
  | 0x1C => some (.select (some []))
  | 0x1F => some (.tryTable .empty [] [])
  | 0x20 => some (.localGet i0)
  | 0x21 => some (.localSet i0)
  | 0x22 => some (.localTee i0)
  | 0x23 => some (.globalGet i0)
  | 0x24 => some (.globalSet i0)
  | 0x25 => some (.tableGet i0)
  | 0x26 => some (.tableSet i0)
  | 0x3F => some (.memorySize i0)
  | 0x40 => some (.memoryGrow i0)
  | 0x41 => some (.intConst .i32 0)
  | 0x42 => some (.intConst .i64 0)
  | 0x43 => some (.floatConst .f32 0)
  | 0x44 => some (.floatConst .f64 0)
  | 0xD0 => some (.refNull (.abstract .func))
  | 0xD2 => some (.refFunc i0)
  | 0xD5 => some (.brOnNull i0)
  | 0xD6 => some (.brOnNonNull i0)
  | _ => none

/-- `0xFB` opcodes with immediates. -/
def fbImm? : Nat → Option Instr
  | 0 => some (.structNew i0)
  | 1 => some (.structNewDefault i0)
  | 2 => some (.structGet none i0 i0)
  | 3 => some (.structGet (some .signed) i0 i0)
  | 4 => some (.structGet (some .unsigned) i0 i0)
  | 5 => some (.structSet i0 i0)
  | 6 => some (.arrayNew i0)
  | 7 => some (.arrayNewDefault i0)
  | 8 => some (.arrayNewFixed i0 0)
  | 9 => some (.arrayNewData i0 i0)
  | 10 => some (.arrayNewElem i0 i0)
  | 11 => some (.arrayGet none i0)
  | 12 => some (.arrayGet (some .signed) i0)
  | 13 => some (.arrayGet (some .unsigned) i0)
  | 14 => some (.arraySet i0)
  | 16 => some (.arrayFill i0)
  | 17 => some (.arrayCopy i0 i0)
  | 18 => some (.arrayInitData i0 i0)
  | 19 => some (.arrayInitElem i0 i0)
  | 20 => some (.refTest ⟨false, .abstract .any⟩)
  | 21 => some (.refTest ⟨true, .abstract .any⟩)
  | 22 => some (.refCast ⟨false, .abstract .any⟩)
  | 23 => some (.refCast ⟨true, .abstract .any⟩)
  | 24 => some (.brOnCast i0 ⟨true, .abstract .any⟩ ⟨true, .abstract .any⟩)
  | 25 => some (.brOnCastFail i0 ⟨true, .abstract .any⟩ ⟨true, .abstract .any⟩)
  | _ => none

/-- `0xFC` opcodes with immediates. -/
def fcImm? : Nat → Option Instr
  | 8 => some (.memoryInit i0 i0)
  | 9 => some (.dataDrop i0)
  | 10 => some (.memoryCopy i0 i0)
  | 11 => some (.memoryFill i0)
  | 12 => some (.tableInit i0 i0)
  | 13 => some (.elemDrop i0)
  | 14 => some (.tableCopy i0 i0)
  | 15 => some (.tableGrow i0)
  | 16 => some (.tableSize i0)
  | 17 => some (.tableFill i0)
  | _ => none

/-- `0xFD` opcodes with immediates other than lanes and memory arguments. -/
def fdImm? : Nat → Option Instr
  | 12 => some (.vecConst 0)
  | 13 => some (.vecShuffle [])
  | _ => none

/-- An unprefixed opcode. -/
def plainB? (n : Nat) : Option Instr :=
  if n < 256 then
    (Binary.Core.plainOp? n.toUInt8).or
      (((Binary.Core.memOp? n.toUInt8).map fun mk => mk i0 ma0).or (plainImm? n))
  else none

/-- A `0xFD` opcode. -/
def vecB? (n : Nat) : Option Instr :=
  (Binary.Core.prefixFDOp? n).or <|
    ((Binary.Core.vecMemOp? n).map fun mk => mk i0 ma0).or <|
      ((Binary.Core.vecMemLaneOp? n).map fun mk => mk i0 ma0 0).or <|
        ((Binary.Core.vecLaneOp? n).map fun mk => mk 0).or (fdImm? n)

/-- **The decoding of a binary opcode** to a representative Core 3.0 instruction. -/
def binInstr? : Opcode → Option Instr
  | .bin none n => plainB? n
  | .bin (some 0xFB) n => (Binary.Core.prefixFBOp? n).or (fbImm? n)
  | .bin (some 0xFC) n => (Binary.Core.prefixFCOp? n).or (fcImm? n)
  | .bin (some 0xFD) n => vecB? n
  | _ => none

/-- The typing of a binary opcode: the typing of the named opcode it decodes to. -/
def tyBin (o : Opcode) : OpTy :=
  match binInstr? o with
  | some i => arity30 (head i)
  | none => ⟨0, 0, false⟩

/-- **The binary signature of a feature set**: decodable opcodes whose representative is in `S`
at its head. -/
def bsigB (S : FeatureSet) : FSig :=
  ⟨{o | ∃ i, binInstr? o = some i ∧ Instr.headB S i = true}, tyBin⟩

/-- The decoding of an opcode of a binary signature. -/
def instOf {S : FeatureSet} (o : (bsigB S).Op) : Instr :=
  (binInstr? o.1).get (by obtain ⟨i, h, -⟩ := o.2; simp [h])

theorem binInstr?_instOf {S : FeatureSet} (o : (bsigB S).Op) :
    binInstr? o.1 = some (instOf o) := by
  simp [instOf]

theorem headB_instOf {S : FeatureSet} (o : (bsigB S).Op) : Instr.headB S (instOf o) = true := by
  obtain ⟨i, h, hs⟩ := o.2
  have : instOf o = i := Option.some.inj ((binInstr?_instOf o).symm.trans h)
  rw [this]
  exact hs

theorem tyBin_instOf {S : FeatureSet} (o : (bsigB S).Op) :
    tyBin o.1 = arity30 (head (instOf o)) := by
  unfold tyBin
  rw [binInstr?_instOf]

/-- **The renaming morphism** from binary to named opcodes. -/
def renB (S : FeatureSet) : bsigB S ⟶ nsig S :=
  ⟨fun o => ⟨head (instOf o), instOf o, rfl, headB_instOf o⟩, fun o => (tyBin_instOf o).symm⟩

/-- The renaming into the 3.0 signature. -/
def ren30 : bsigB v30 ⟶ sig30 := renB v30 ≫ FSig.incl (nsig_sub30 v30)

/-- **Core 3.0 on binary opcodes**: the reduct of `core|S` along the renaming. -/
def binAt {H : Type} (S : FeatureSet) (P : Profile) (f : Execution.Core.Frame)
    (okc : List Instr → Prop) (x : Silmaril.Wasm.Atlas.Core.Pt H) : Model UIn UObs (bsigB S) :=
  (coreSAt S P f okc x).reduct (renB S)

end Silmaril.Wasm.Unified.Versions
