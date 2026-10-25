module

public import Silmaril.Wasm.Binaryen.Exe.MemoryEncode
public import Silmaril.Wasm.Binary.Core.OpcodesProps

@[expose] public section

/-! # Encoding the `0xFD` opcode space from the Core opcode tables

Every SIMD and relaxed-SIMD instruction is written as `0xFD n` followed by one of
five immediate shapes: none, a memory argument, a memory argument and a lane, a lane,
or sixteen lane bytes (`i8x16.shuffle`; `v128.const` is written by `encInstr`). The
opcode tables list every rule of the Core grammar's `0xFD` relations (`PrefixFDOp`,
`VecMemOp`, `VecMemLaneOp`, `VecLaneOp` in `Binary/Core/Opcodes.lean`), each entry
carrying its rule, and the encoder searches them for the entry that rebuilds the
instruction, compared with `vecInstrEqb`. So one soundness argument covers every
opcode (`SIMDEncodeSound.lean`); the decoder reads the same rules through the
grammar's lookups (`prefixFDOp?` and the others, `Exe/Decode.lean`).
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binary.Core

/-- Structural equality of the vector instructions (every field has decidable
equality); `false` on every other instruction. -/
def vecInstrEqb : Instr → Instr → Bool
  | .vecLoad o x a, .vecLoad o' x' a' => decide (o = o' ∧ x = x' ∧ a = a')
  | .vecLoadLane s x a l, .vecLoadLane s' x' a' l' => decide (s = s' ∧ x = x' ∧ a = a' ∧ l = l')
  | .vecStore x a, .vecStore x' a' => decide (x = x' ∧ a = a')
  | .vecStoreLane s x a l, .vecStoreLane s' x' a' l' =>
      decide (s = s' ∧ x = x' ∧ a = a' ∧ l = l')
  | .vecUnOp o, .vecUnOp o' => decide (o = o')
  | .vecBinOp o, .vecBinOp o' => decide (o = o')
  | .vecTernOp o, .vecTernOp o' => decide (o = o')
  | .vecTestOp o, .vecTestOp o' => decide (o = o')
  | .vecIntUnOp s o, .vecIntUnOp s' o' => decide (s = s' ∧ o = o')
  | .vecFloatUnOp s o, .vecFloatUnOp s' o' => decide (s = s' ∧ o = o')
  | .vecIntBinOp s o, .vecIntBinOp s' o' => decide (s = s' ∧ o = o')
  | .vecFloatBinOp s o, .vecFloatBinOp s' o' => decide (s = s' ∧ o = o')
  | .vecIntTernOp s o, .vecIntTernOp s' o' => decide (s = s' ∧ o = o')
  | .vecFloatTernOp s o, .vecFloatTernOp s' o' => decide (s = s' ∧ o = o')
  | .vecAllTrue s, .vecAllTrue s' => decide (s = s')
  | .vecIntRelOp s o, .vecIntRelOp s' o' => decide (s = s' ∧ o = o')
  | .vecFloatRelOp s o, .vecFloatRelOp s' o' => decide (s = s' ∧ o = o')
  | .vecShiftOp s o, .vecShiftOp s' o' => decide (s = s' ∧ o = o')
  | .vecBitmask s, .vecBitmask s' => decide (s = s')
  | .vecSwizzle o, .vecSwizzle o' => decide (o = o')
  | .vecExtUnOp s t o, .vecExtUnOp s' t' o' => decide (s = s' ∧ t = t' ∧ o = o')
  | .vecExtBinOp s t o, .vecExtBinOp s' t' o' => decide (s = s' ∧ t = t' ∧ o = o')
  | .vecExtTernOp s t o, .vecExtTernOp s' t' o' => decide (s = s' ∧ t = t' ∧ o = o')
  | .vecNarrow s t g, .vecNarrow s' t' g' => decide (s = s' ∧ t = t' ∧ g = g')
  | .vecConvert s t o, .vecConvert s' t' o' => decide (s = s' ∧ t = t' ∧ o = o')
  | .vecSplat s, .vecSplat s' => decide (s = s')
  | .vecExtractLane s g l, .vecExtractLane s' g' l' => decide (s = s' ∧ g = g' ∧ l = l')
  | .vecReplaceLane s l, .vecReplaceLane s' l' => decide (s = s' ∧ l = l')
  | _, _ => false

/-- An immediate-free `0xFD` opcode with its instruction, proved in the Core grammar. -/
structure FDPlain where
  n : Nat
  i : Instr
  h : PrefixFDOp n i

/-- A vector memory opcode with its instruction family. -/
structure FDMem where
  n : Nat
  ins : MemIdx → MemArg → Instr
  h : VecMemOp n ins

/-- A vector lane memory opcode with its instruction family. -/
structure FDMemLane where
  n : Nat
  ins : MemIdx → MemArg → LaneIdx → Instr
  h : VecMemLaneOp n ins

/-- A lane opcode with its instruction family. -/
structure FDLane where
  n : Nat
  ins : LaneIdx → Instr
  h : VecLaneOp n ins

/-- Every rule of `PrefixFDOp` (SIMD and relaxed SIMD without immediates). -/
def fdPlainTable : List FDPlain := [
   ⟨_, _, .r14⟩, ⟨_, _, .r256⟩, ⟨_, _, .r15⟩, ⟨_, _, .r16⟩, ⟨_, _, .r17⟩, ⟨_, _, .r18⟩, ⟨_, _, .r19⟩, ⟨_, _, .r20⟩,
   ⟨_, _, .r35⟩, ⟨_, _, .r36⟩, ⟨_, _, .r37⟩, ⟨_, _, .r38⟩, ⟨_, _, .r39⟩, ⟨_, _, .r40⟩, ⟨_, _, .r41⟩, ⟨_, _, .r42⟩,
   ⟨_, _, .r43⟩, ⟨_, _, .r44⟩, ⟨_, _, .r45⟩, ⟨_, _, .r46⟩, ⟨_, _, .r47⟩, ⟨_, _, .r48⟩, ⟨_, _, .r49⟩, ⟨_, _, .r50⟩,
   ⟨_, _, .r51⟩, ⟨_, _, .r52⟩, ⟨_, _, .r53⟩, ⟨_, _, .r54⟩, ⟨_, _, .r55⟩, ⟨_, _, .r56⟩, ⟨_, _, .r57⟩, ⟨_, _, .r58⟩,
   ⟨_, _, .r59⟩, ⟨_, _, .r60⟩, ⟨_, _, .r61⟩, ⟨_, _, .r62⟩, ⟨_, _, .r63⟩, ⟨_, _, .r64⟩, ⟨_, _, .r65⟩, ⟨_, _, .r66⟩,
   ⟨_, _, .r67⟩, ⟨_, _, .r68⟩, ⟨_, _, .r69⟩, ⟨_, _, .r70⟩, ⟨_, _, .r71⟩, ⟨_, _, .r72⟩, ⟨_, _, .r73⟩, ⟨_, _, .r74⟩,
   ⟨_, _, .r75⟩, ⟨_, _, .r76⟩, ⟨_, _, .r77⟩, ⟨_, _, .r78⟩, ⟨_, _, .r79⟩, ⟨_, _, .r80⟩, ⟨_, _, .r81⟩, ⟨_, _, .r82⟩,
   ⟨_, _, .r83⟩, ⟨_, _, .r96⟩, ⟨_, _, .r97⟩, ⟨_, _, .r98⟩, ⟨_, _, .r99⟩, ⟨_, _, .r100⟩, ⟨_, _, .r101⟩, ⟨_, _, .r102⟩,
   ⟨_, _, .r107⟩, ⟨_, _, .r108⟩, ⟨_, _, .r109⟩, ⟨_, _, .r110⟩, ⟨_, _, .r111⟩, ⟨_, _, .r112⟩, ⟨_, _, .r113⟩, ⟨_, _, .r114⟩,
   ⟨_, _, .r115⟩, ⟨_, _, .r118⟩, ⟨_, _, .r119⟩, ⟨_, _, .r120⟩, ⟨_, _, .r121⟩, ⟨_, _, .r123⟩, ⟨_, _, .r124⟩, ⟨_, _, .r125⟩,
   ⟨_, _, .r128⟩, ⟨_, _, .r129⟩, ⟨_, _, .r130⟩, ⟨_, _, .r142⟩, ⟨_, _, .r143⟩, ⟨_, _, .r144⟩, ⟨_, _, .r145⟩, ⟨_, _, .r146⟩,
   ⟨_, _, .r147⟩, ⟨_, _, .r149⟩, ⟨_, _, .r150⟩, ⟨_, _, .r151⟩, ⟨_, _, .r152⟩, ⟨_, _, .r153⟩, ⟨_, _, .r155⟩, ⟨_, _, .r273⟩,
   ⟨_, _, .r131⟩, ⟨_, _, .r132⟩, ⟨_, _, .r133⟩, ⟨_, _, .r134⟩, ⟨_, _, .r135⟩, ⟨_, _, .r136⟩, ⟨_, _, .r137⟩, ⟨_, _, .r138⟩,
   ⟨_, _, .r139⟩, ⟨_, _, .r140⟩, ⟨_, _, .r141⟩, ⟨_, _, .r156⟩, ⟨_, _, .r157⟩, ⟨_, _, .r158⟩, ⟨_, _, .r159⟩, ⟨_, _, .r274⟩,
   ⟨_, _, .r126⟩, ⟨_, _, .r127⟩, ⟨_, _, .r160⟩, ⟨_, _, .r161⟩, ⟨_, _, .r163⟩, ⟨_, _, .r164⟩, ⟨_, _, .r167⟩, ⟨_, _, .r168⟩,
   ⟨_, _, .r169⟩, ⟨_, _, .r170⟩, ⟨_, _, .r171⟩, ⟨_, _, .r172⟩, ⟨_, _, .r173⟩, ⟨_, _, .r174⟩, ⟨_, _, .r177⟩, ⟨_, _, .r181⟩,
   ⟨_, _, .r182⟩, ⟨_, _, .r183⟩, ⟨_, _, .r184⟩, ⟨_, _, .r185⟩, ⟨_, _, .r186⟩, ⟨_, _, .r188⟩, ⟨_, _, .r189⟩, ⟨_, _, .r190⟩,
   ⟨_, _, .r191⟩, ⟨_, _, .r275⟩, ⟨_, _, .r192⟩, ⟨_, _, .r193⟩, ⟨_, _, .r195⟩, ⟨_, _, .r196⟩, ⟨_, _, .r199⟩, ⟨_, _, .r200⟩,
   ⟨_, _, .r201⟩, ⟨_, _, .r202⟩, ⟨_, _, .r203⟩, ⟨_, _, .r204⟩, ⟨_, _, .r205⟩, ⟨_, _, .r206⟩, ⟨_, _, .r209⟩, ⟨_, _, .r213⟩,
   ⟨_, _, .r214⟩, ⟨_, _, .r215⟩, ⟨_, _, .r216⟩, ⟨_, _, .r217⟩, ⟨_, _, .r218⟩, ⟨_, _, .r219⟩, ⟨_, _, .r220⟩, ⟨_, _, .r221⟩,
   ⟨_, _, .r222⟩, ⟨_, _, .r223⟩, ⟨_, _, .r103⟩, ⟨_, _, .r104⟩, ⟨_, _, .r105⟩, ⟨_, _, .r106⟩, ⟨_, _, .r224⟩, ⟨_, _, .r225⟩,
   ⟨_, _, .r227⟩, ⟨_, _, .r228⟩, ⟨_, _, .r229⟩, ⟨_, _, .r230⟩, ⟨_, _, .r231⟩, ⟨_, _, .r232⟩, ⟨_, _, .r233⟩, ⟨_, _, .r234⟩,
   ⟨_, _, .r235⟩, ⟨_, _, .r269⟩, ⟨_, _, .r270⟩, ⟨_, _, .r261⟩, ⟨_, _, .r262⟩, ⟨_, _, .r116⟩, ⟨_, _, .r117⟩, ⟨_, _, .r122⟩,
   ⟨_, _, .r148⟩, ⟨_, _, .r236⟩, ⟨_, _, .r237⟩, ⟨_, _, .r239⟩, ⟨_, _, .r240⟩, ⟨_, _, .r241⟩, ⟨_, _, .r242⟩, ⟨_, _, .r243⟩,
   ⟨_, _, .r244⟩, ⟨_, _, .r245⟩, ⟨_, _, .r246⟩, ⟨_, _, .r247⟩, ⟨_, _, .r271⟩, ⟨_, _, .r272⟩, ⟨_, _, .r263⟩, ⟨_, _, .r264⟩,
   ⟨_, _, .r265⟩, ⟨_, _, .r266⟩, ⟨_, _, .r267⟩, ⟨_, _, .r268⟩, ⟨_, _, .r94⟩, ⟨_, _, .r95⟩, ⟨_, _, .r248⟩, ⟨_, _, .r249⟩,
   ⟨_, _, .r250⟩, ⟨_, _, .r251⟩, ⟨_, _, .r252⟩, ⟨_, _, .r253⟩, ⟨_, _, .r254⟩, ⟨_, _, .r255⟩, ⟨_, _, .r257⟩, ⟨_, _, .r258⟩,
   ⟨_, _, .r259⟩, ⟨_, _, .r260⟩]

/-- Every rule of `VecMemOp`. -/
def fdMemTable : List FDMem := [
   ⟨_, _, .r0⟩, ⟨_, _, .r1⟩, ⟨_, _, .r2⟩, ⟨_, _, .r3⟩, ⟨_, _, .r4⟩, ⟨_, _, .r5⟩, ⟨_, _, .r6⟩, ⟨_, _, .r7⟩,
   ⟨_, _, .r8⟩, ⟨_, _, .r9⟩, ⟨_, _, .r10⟩, ⟨_, _, .r11⟩, ⟨_, _, .r92⟩, ⟨_, _, .r93⟩]

/-- Every rule of `VecMemLaneOp`. -/
def fdMemLaneTable : List FDMemLane := [
   ⟨_, _, .r84⟩, ⟨_, _, .r85⟩, ⟨_, _, .r86⟩, ⟨_, _, .r87⟩, ⟨_, _, .r88⟩, ⟨_, _, .r89⟩, ⟨_, _, .r90⟩, ⟨_, _, .r91⟩]

/-- Every rule of `VecLaneOp`. -/
def fdLaneTable : List FDLane := [
   ⟨_, _, .r21⟩, ⟨_, _, .r22⟩, ⟨_, _, .r23⟩, ⟨_, _, .r24⟩, ⟨_, _, .r25⟩, ⟨_, _, .r26⟩, ⟨_, _, .r27⟩, ⟨_, _, .r28⟩,
   ⟨_, _, .r29⟩, ⟨_, _, .r30⟩, ⟨_, _, .r31⟩, ⟨_, _, .r32⟩, ⟨_, _, .r33⟩, ⟨_, _, .r34⟩]

/-- A lane index as its immediate byte (`laneOf` reads it back). -/
def laneByte (l : LaneIdx) : UInt8 := ⟨⟨l⟩⟩

/-- Encode a vector instruction other than `v128.const`: the opcode is the table entry
that rebuilds it from its own immediates. Unsupported instructions and memory
arguments fail explicitly. -/
def encSIMDInstr (i : Instr) : Except String (List UInt8) :=
  match i with
  | .vecLoad _ x a | .vecStore x a =>
    match fdMemTable.find? (fun e => vecInstrEqb (e.ins x a) i) with
    | some e => do pure ([0xFD] ++ encU e.n ++ (← encMemArg x a))
    | none => throw "encoder: vector memory instruction outside the 0xfd tables"
  | .vecLoadLane _ x a l | .vecStoreLane _ x a l =>
    match fdMemLaneTable.find? (fun e => vecInstrEqb (e.ins x a l) i) with
    | some e => do pure ([0xFD] ++ encU e.n ++ (← encMemArg x a) ++ [laneByte l])
    | none => throw "encoder: vector lane memory instruction outside the 0xfd tables"
  | .vecExtractLane _ _ l | .vecReplaceLane _ l =>
    match fdLaneTable.find? (fun e => vecInstrEqb (e.ins l) i) with
    | some e => pure ([0xFD] ++ encU e.n ++ [laneByte l])
    | none => throw "encoder: vector lane instruction outside the 0xfd tables"
  | .vecShuffle ls =>
    if ls.length = 16 then pure ([0xFD, 13] ++ ls.map laneByte)
    else throw "encoder: i8x16.shuffle needs sixteen lanes"
  | i =>
    match fdPlainTable.find? (fun e => vecInstrEqb e.i i) with
    | some e => pure ([0xFD] ++ encU e.n)
    | none => throw "encoder: instruction outside the profile"

end Silmaril.Wasm.Binaryen.Exe
