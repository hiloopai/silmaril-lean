module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.FwdRef2.Forms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms

/-!
# Round 5, pass 3, track fwdref: a decoder for `instrToV`

`recon` reads an instruction back from its image. It dispatches on the image's head (the IL
constructor) and then inverts the one or two Core constructors with that head
(`Typing.instrHead`). Each inversion is the classical inverse `inv f` of the constructor's
image `f`, so `recon` needs no injectivity to be defined. Proving that it inverts `instrToV`
(`Round5.FwdRef2.recon_instrToV`) needs only that each constructor's image is injective in the
constructor's own arguments. Without a decoder, injectivity would need a case split on pairs of
constructors.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)

/-- The classical inverse of `f` at `v`, if `v` is in its image. -/
noncomputable def inv {α : Type} (f : α → Value) (v : Value) : Option α :=
  open Classical in if h : ∃ a, f a = v then some h.choose else none

/-- Invert `f`, then rebuild with `g`. -/
noncomputable def dec {α : Type} (f : α → Value) (g : α → Instr) (v : Value) : Option Instr :=
  (inv f v).map g

theorem inv_eq {α : Type} (f : α → Value) {a : α} (hinj : ∀ a', f a' = f a → a' = a) :
    inv f (f a) = some a := by
  unfold inv
  split
  · next h => exact congrArg some (hinj _ h.choose_spec)
  · next h => exact absurd ⟨a, rfl⟩ h

theorem inv_none {α : Type} (f : α → Value) {v : Value} (h : ∀ a, f a ≠ v) : inv f v = none := by
  unfold inv
  split
  · next h' => exact absurd h'.choose_spec (h _)
  · rfl

theorem dec_eq {α : Type} (f : α → Value) (g : α → Instr) {a : α}
    (hinj : ∀ a', f a' = f a → a' = a) : dec f g (f a) = some (g a) := by
  unfold dec
  rw [inv_eq f hinj]
  rfl

theorem dec_none {α : Type} (f : α → Value) (g : α → Instr) {v : Value} (h : ∀ a, f a ≠ v) :
    dec f g v = none := by
  unfold dec
  rw [inv_none f h]
  rfl

/-- A numeral as a constant instruction. -/
def constInstr : Silmaril.Wasm.Execution.Core.NumVal → Instr
  | ⟨.int t, b⟩ => .intConst t b
  | ⟨.float t, b⟩ => .floatConst t b

/-- The decoder of each head: the classical inverse of the image of each constructor with that
head. Its branches follow `instrToV`'s clauses. -/
noncomputable def decodeHead (op : MixopS) (v : Value) : Option Instr :=
  if op = "NOP" then some .nop else
  if op = "UNREACHABLE" then some .unreachable else
  if op = "DROP" then some .drop else
  if op = "RETURN" then some .return_ else
  if op = "THROW_REF" then some .throwRef else
  if op = "REF.IS_NULL" then some .refIsNull else
  if op = "REF.AS_NON_NULL" then some .refAsNonNull else
  if op = "REF.EQ" then some .refEq else
  if op = "REF.I31" then some .refI31 else
  if op = "ARRAY.LEN" then some .arrayLen else
  if op = "EXTERN.CONVERT_ANY" then some .externConvertAny else
  if op = "ANY.CONVERT_EXTERN" then some .anyConvertExtern else
  if op = "SELECT" then dec (fun o => instrToV (.select o)) .select v else
  if op = "BLOCK" then dec (fun p : BlockType × List Instr =>
      .case "BLOCK" (.tuple [Encode.toValue p.1, .list (instrsToV p.2)]))
    (fun p => .block p.1 p.2) v else
  if op = "LOOP" then dec (fun p : BlockType × List Instr =>
      .case "LOOP" (.tuple [Encode.toValue p.1, .list (instrsToV p.2)]))
    (fun p => .loop p.1 p.2) v else
  if op = "IF%%ELSE%" then dec (fun p : BlockType × List Instr × List Instr =>
      .case "IF%%ELSE%" (.tuple [Encode.toValue p.1, .list (instrsToV p.2.1),
        .list (instrsToV p.2.2)]))
    (fun p => .if_ p.1 p.2.1 p.2.2) v else
  if op = "TRY_TABLE" then dec (fun p : BlockType × List Catch × List Instr =>
      .case "TRY_TABLE" (.tuple [Encode.toValue p.1,
        .case "%" (.tuple [.list (p.2.1.map Encode.toValue)]), .list (instrsToV p.2.2)]))
    (fun p => .tryTable p.1 p.2.1 p.2.2) v else
  if op = "BR" then dec (fun x : LabelIdx => .case "BR" (Encode.toValue x)) .br v else
  if op = "BR_IF" then dec (fun x : LabelIdx => .case "BR_IF" (Encode.toValue x)) .brIf v else
  if op = "BR_TABLE" then dec (fun p : List LabelIdx × LabelIdx =>
      .case "BR_TABLE" (.tuple [.list (p.1.map Encode.toValue), Encode.toValue p.2]))
    (fun p => .brTable p.1 p.2) v else
  if op = "BR_ON_NULL" then
    dec (fun x : LabelIdx => .case "BR_ON_NULL" (Encode.toValue x)) .brOnNull v else
  if op = "BR_ON_NON_NULL" then
    dec (fun x : LabelIdx => .case "BR_ON_NON_NULL" (Encode.toValue x)) .brOnNonNull v else
  if op = "BR_ON_CAST" then dec (fun p : LabelIdx × RefType × RefType =>
      .case "BR_ON_CAST" (.tuple [Encode.toValue p.1, Encode.toValue p.2.1,
        Encode.toValue p.2.2]))
    (fun p => .brOnCast p.1 p.2.1 p.2.2) v else
  if op = "BR_ON_CAST_FAIL" then dec (fun p : LabelIdx × RefType × RefType =>
      .case "BR_ON_CAST_FAIL" (.tuple [Encode.toValue p.1, Encode.toValue p.2.1,
        Encode.toValue p.2.2]))
    (fun p => .brOnCastFail p.1 p.2.1 p.2.2) v else
  if op = "CALL" then dec (fun x : FuncIdx => .case "CALL" (Encode.toValue x)) .call v else
  if op = "CALL_REF" then
    dec (fun x : TypeIdx => .case "CALL_REF" (.case "_IDX" (Encode.toValue x))) .callRef v else
  if op = "CALL_INDIRECT" then dec (fun p : TableIdx × TypeIdx =>
      .case "CALL_INDIRECT" (.tuple [Encode.toValue p.1, .case "_IDX" (Encode.toValue p.2)]))
    (fun p => .callIndirect p.1 p.2) v else
  if op = "RETURN_CALL" then
    dec (fun x : FuncIdx => .case "RETURN_CALL" (Encode.toValue x)) .returnCall v else
  if op = "RETURN_CALL_REF" then
    dec (fun x : TypeIdx => .case "RETURN_CALL_REF" (.case "_IDX" (Encode.toValue x)))
      .returnCallRef v else
  if op = "RETURN_CALL_INDIRECT" then dec (fun p : TableIdx × TypeIdx =>
      .case "RETURN_CALL_INDIRECT" (.tuple [Encode.toValue p.1,
        .case "_IDX" (Encode.toValue p.2)]))
    (fun p => .returnCallIndirect p.1 p.2) v else
  if op = "THROW" then dec (fun x : TagIdx => .case "THROW" (Encode.toValue x)) .throw v else
  if op = "LOCAL.GET" then
    dec (fun x : LocalIdx => .case "LOCAL.GET" (Encode.toValue x)) .localGet v else
  if op = "LOCAL.SET" then
    dec (fun x : LocalIdx => .case "LOCAL.SET" (Encode.toValue x)) .localSet v else
  if op = "LOCAL.TEE" then
    dec (fun x : LocalIdx => .case "LOCAL.TEE" (Encode.toValue x)) .localTee v else
  if op = "GLOBAL.GET" then
    dec (fun x : GlobalIdx => .case "GLOBAL.GET" (Encode.toValue x)) .globalGet v else
  if op = "GLOBAL.SET" then
    dec (fun x : GlobalIdx => .case "GLOBAL.SET" (Encode.toValue x)) .globalSet v else
  if op = "TABLE.GET" then
    dec (fun x : TableIdx => .case "TABLE.GET" (Encode.toValue x)) .tableGet v else
  if op = "TABLE.SET" then
    dec (fun x : TableIdx => .case "TABLE.SET" (Encode.toValue x)) .tableSet v else
  if op = "TABLE.SIZE" then
    dec (fun x : TableIdx => .case "TABLE.SIZE" (Encode.toValue x)) .tableSize v else
  if op = "TABLE.GROW" then
    dec (fun x : TableIdx => .case "TABLE.GROW" (Encode.toValue x)) .tableGrow v else
  if op = "TABLE.FILL" then
    dec (fun x : TableIdx => .case "TABLE.FILL" (Encode.toValue x)) .tableFill v else
  if op = "TABLE.COPY" then dec (fun p : TableIdx × TableIdx =>
      .case "TABLE.COPY" (.tuple [Encode.toValue p.1, Encode.toValue p.2]))
    (fun p => .tableCopy p.1 p.2) v else
  if op = "TABLE.INIT" then dec (fun p : TableIdx × ElemIdx =>
      .case "TABLE.INIT" (.tuple [Encode.toValue p.1, Encode.toValue p.2]))
    (fun p => .tableInit p.1 p.2) v else
  if op = "ELEM.DROP" then
    dec (fun x : ElemIdx => .case "ELEM.DROP" (Encode.toValue x)) .elemDrop v else
  if op = "LOAD" then
    (dec (fun p : IntType × Option (PackSize × Signedness) × MemIdx × MemArg =>
      .case "LOAD" (.tuple [Encode.toValue (NumType.int p.1),
        .opt (p.2.1.map fun q => .case "%_%" (.tuple [szV q.1, sxV q.2])),
        Encode.toValue p.2.2.1, memargV p.2.2.2]))
      (fun p => .intLoad p.1 p.2.1 p.2.2.1 p.2.2.2) v).or
    (dec (fun p : FloatType × MemIdx × MemArg =>
      .case "LOAD" (.tuple [Encode.toValue (NumType.float p.1), .opt none,
        Encode.toValue p.2.1, memargV p.2.2]))
      (fun p => .floatLoad p.1 p.2.1 p.2.2) v) else
  if op = "STORE" then
    (dec (fun p : IntType × Option PackSize × MemIdx × MemArg =>
      .case "STORE" (.tuple [Encode.toValue (NumType.int p.1),
        .opt (p.2.1.map fun q => .case "%" (.tuple [szV q])),
        Encode.toValue p.2.2.1, memargV p.2.2.2]))
      (fun p => .intStore p.1 p.2.1 p.2.2.1 p.2.2.2) v).or
    (dec (fun p : FloatType × MemIdx × MemArg =>
      .case "STORE" (.tuple [Encode.toValue (NumType.float p.1), .opt none,
        Encode.toValue p.2.1, memargV p.2.2]))
      (fun p => .floatStore p.1 p.2.1 p.2.2) v) else
  if op = "VLOAD" then dec (fun p : VecLoadOp × MemIdx × MemArg =>
      instrToV (.vecLoad p.1 p.2.1 p.2.2)) (fun p => .vecLoad p.1 p.2.1 p.2.2) v else
  if op = "VLOAD_LANE" then dec (fun p : PackSize × MemIdx × MemArg × LaneIdx =>
      instrToV (.vecLoadLane p.1 p.2.1 p.2.2.1 p.2.2.2))
    (fun p => .vecLoadLane p.1 p.2.1 p.2.2.1 p.2.2.2) v else
  if op = "VSTORE" then dec (fun p : MemIdx × MemArg =>
      instrToV (.vecStore p.1 p.2)) (fun p => .vecStore p.1 p.2) v else
  if op = "VSTORE_LANE" then dec (fun p : PackSize × MemIdx × MemArg × LaneIdx =>
      instrToV (.vecStoreLane p.1 p.2.1 p.2.2.1 p.2.2.2))
    (fun p => .vecStoreLane p.1 p.2.1 p.2.2.1 p.2.2.2) v else
  if op = "MEMORY.SIZE" then
    dec (fun x : MemIdx => .case "MEMORY.SIZE" (Encode.toValue x)) .memorySize v else
  if op = "MEMORY.GROW" then
    dec (fun x : MemIdx => .case "MEMORY.GROW" (Encode.toValue x)) .memoryGrow v else
  if op = "MEMORY.FILL" then
    dec (fun x : MemIdx => .case "MEMORY.FILL" (Encode.toValue x)) .memoryFill v else
  if op = "MEMORY.COPY" then dec (fun p : MemIdx × MemIdx =>
      .case "MEMORY.COPY" (.tuple [Encode.toValue p.1, Encode.toValue p.2]))
    (fun p => .memoryCopy p.1 p.2) v else
  if op = "MEMORY.INIT" then dec (fun p : MemIdx × DataIdx =>
      .case "MEMORY.INIT" (.tuple [Encode.toValue p.1, Encode.toValue p.2]))
    (fun p => .memoryInit p.1 p.2) v else
  if op = "DATA.DROP" then
    dec (fun x : DataIdx => .case "DATA.DROP" (Encode.toValue x)) .dataDrop v else
  if op = "REF.NULL" then
    dec (fun x : HeapType => .case "REF.NULL" (Encode.toValue x)) .refNull v else
  if op = "REF.TEST" then
    dec (fun x : RefType => .case "REF.TEST" (Encode.toValue x)) .refTest v else
  if op = "REF.CAST" then
    dec (fun x : RefType => .case "REF.CAST" (Encode.toValue x)) .refCast v else
  if op = "REF.FUNC" then
    dec (fun x : FuncIdx => .case "REF.FUNC" (Encode.toValue x)) .refFunc v else
  if op = "I31.GET" then dec (fun s => .case "I31.GET" (sxV s)) .i31Get v else
  if op = "STRUCT.NEW" then
    dec (fun x : TypeIdx => .case "STRUCT.NEW" (Encode.toValue x)) .structNew v else
  if op = "STRUCT.NEW_DEFAULT" then
    dec (fun x : TypeIdx => .case "STRUCT.NEW_DEFAULT" (Encode.toValue x))
      .structNewDefault v else
  if op = "STRUCT.GET" then dec (fun p : Option Signedness × TypeIdx × FieldIdx =>
      .case "STRUCT.GET" (.tuple [.opt (p.1.map sxV), Encode.toValue p.2.1,
        Encode.toValue p.2.2]))
    (fun p => .structGet p.1 p.2.1 p.2.2) v else
  if op = "STRUCT.SET" then dec (fun p : TypeIdx × FieldIdx =>
      .case "STRUCT.SET" (.tuple [Encode.toValue p.1, Encode.toValue p.2]))
    (fun p => .structSet p.1 p.2) v else
  if op = "ARRAY.NEW" then
    dec (fun x : TypeIdx => .case "ARRAY.NEW" (Encode.toValue x)) .arrayNew v else
  if op = "ARRAY.NEW_DEFAULT" then
    dec (fun x : TypeIdx => .case "ARRAY.NEW_DEFAULT" (Encode.toValue x))
      .arrayNewDefault v else
  if op = "ARRAY.NEW_FIXED" then dec (fun p : TypeIdx × Fin (2 ^ 32) =>
      .case "ARRAY.NEW_FIXED" (.tuple [Encode.toValue p.1, pctV p.2.val]))
    (fun p => .arrayNewFixed p.1 p.2) v else
  if op = "ARRAY.NEW_DATA" then dec (fun p : TypeIdx × DataIdx =>
      .case "ARRAY.NEW_DATA" (.tuple [Encode.toValue p.1, Encode.toValue p.2]))
    (fun p => .arrayNewData p.1 p.2) v else
  if op = "ARRAY.NEW_ELEM" then dec (fun p : TypeIdx × ElemIdx =>
      .case "ARRAY.NEW_ELEM" (.tuple [Encode.toValue p.1, Encode.toValue p.2]))
    (fun p => .arrayNewElem p.1 p.2) v else
  if op = "ARRAY.GET" then dec (fun p : Option Signedness × TypeIdx =>
      .case "ARRAY.GET" (.tuple [.opt (p.1.map sxV), Encode.toValue p.2]))
    (fun p => .arrayGet p.1 p.2) v else
  if op = "ARRAY.SET" then
    dec (fun x : TypeIdx => .case "ARRAY.SET" (Encode.toValue x)) .arraySet v else
  if op = "ARRAY.FILL" then
    dec (fun x : TypeIdx => .case "ARRAY.FILL" (Encode.toValue x)) .arrayFill v else
  if op = "ARRAY.COPY" then dec (fun p : TypeIdx × TypeIdx =>
      .case "ARRAY.COPY" (.tuple [Encode.toValue p.1, Encode.toValue p.2]))
    (fun p => .arrayCopy p.1 p.2) v else
  if op = "ARRAY.INIT_DATA" then dec (fun p : TypeIdx × DataIdx =>
      .case "ARRAY.INIT_DATA" (.tuple [Encode.toValue p.1, Encode.toValue p.2]))
    (fun p => .arrayInitData p.1 p.2) v else
  if op = "ARRAY.INIT_ELEM" then dec (fun p : TypeIdx × ElemIdx =>
      .case "ARRAY.INIT_ELEM" (.tuple [Encode.toValue p.1, Encode.toValue p.2]))
    (fun p => .arrayInitElem p.1 p.2) v else
  if op = "CONST" then dec (fun n => valV (.num n)) constInstr v else
  if op = "UNOP" then
    (dec (fun p : IntType × IntUnOp => instrToV (.intUnOp p.1 p.2))
      (fun p => .intUnOp p.1 p.2) v).or
    (dec (fun p : FloatType × FloatUnOp => instrToV (.floatUnOp p.1 p.2))
      (fun p => .floatUnOp p.1 p.2) v) else
  if op = "BINOP" then
    (dec (fun p : IntType × IntBinOp => instrToV (.intBinOp p.1 p.2))
      (fun p => .intBinOp p.1 p.2) v).or
    (dec (fun p : FloatType × FloatBinOp => instrToV (.floatBinOp p.1 p.2))
      (fun p => .floatBinOp p.1 p.2) v) else
  if op = "TESTOP" then dec (fun p : IntType × IntTestOp => instrToV (.intTestOp p.1 p.2))
    (fun p => .intTestOp p.1 p.2) v else
  if op = "RELOP" then
    (dec (fun p : IntType × IntRelOp => instrToV (.intRelOp p.1 p.2))
      (fun p => .intRelOp p.1 p.2) v).or
    (dec (fun p : FloatType × FloatRelOp => instrToV (.floatRelOp p.1 p.2))
      (fun p => .floatRelOp p.1 p.2) v) else
  if op = "CVTOP" then dec Vec.convertInstrV .convert v else
  if op = "VCONST" then dec (fun b => valV (.vec b)) .vecConst v else
  if op = "VVUNOP" then dec (fun o => .case "VVUNOP" (.tuple [Vec.vecTypeV, Vec.vvunopV o]))
    .vecUnOp v else
  if op = "VVBINOP" then dec (fun o => .case "VVBINOP" (.tuple [Vec.vecTypeV, Vec.vvbinopV o]))
    .vecBinOp v else
  if op = "VVTERNOP" then
    dec (fun o => .case "VVTERNOP" (.tuple [Vec.vecTypeV, Vec.vvternopV o])) .vecTernOp v else
  if op = "VVTESTOP" then
    dec (fun o => .case "VVTESTOP" (.tuple [Vec.vecTypeV, Vec.vvtestopV o])) .vecTestOp v else
  if op = "VUNOP" then
    (dec (fun p : IntShape × VecIntUnOp =>
      .case "VUNOP" (.tuple [Vec.ishV p.1, Vec.vIntUnOpV p.2]))
      (fun p => .vecIntUnOp p.1 p.2) v).or
    (dec (fun p : FloatShape × FloatUnOp =>
      .case "VUNOP" (.tuple [Vec.fshV p.1, Vec.vFloatUnOpV p.2]))
      (fun p => .vecFloatUnOp p.1 p.2) v) else
  if op = "VBINOP" then
    (dec (fun p : IntShape × VecIntBinOp =>
      .case "VBINOP" (.tuple [Vec.ishV p.1, Vec.vIntBinOpV p.2]))
      (fun p => .vecIntBinOp p.1 p.2) v).or
    (dec (fun p : FloatShape × VecFloatBinOp =>
      .case "VBINOP" (.tuple [Vec.fshV p.1, Vec.vFloatBinOpV p.2]))
      (fun p => .vecFloatBinOp p.1 p.2) v) else
  if op = "VTERNOP" then
    (dec (fun p : IntShape × VecIntTernOp =>
      .case "VTERNOP" (.tuple [Vec.ishV p.1, Vec.vIntTernOpV p.2]))
      (fun p => .vecIntTernOp p.1 p.2) v).or
    (dec (fun p : FloatShape × VecFloatTernOp =>
      .case "VTERNOP" (.tuple [Vec.fshV p.1, Vec.vFloatTernOpV p.2]))
      (fun p => .vecFloatTernOp p.1 p.2) v) else
  if op = "VTESTOP" then
    dec (fun s => .case "VTESTOP" (.tuple [Vec.ishV s, caseNilV "ALL_TRUE"])) .vecAllTrue v else
  if op = "VRELOP" then
    (dec (fun p : IntShape × IntRelOp =>
      .case "VRELOP" (.tuple [Vec.ishV p.1, Vec.vIntRelOpV p.2]))
      (fun p => .vecIntRelOp p.1 p.2) v).or
    (dec (fun p : FloatShape × FloatRelOp =>
      .case "VRELOP" (.tuple [Vec.fshV p.1, Vec.vFloatRelOpV p.2]))
      (fun p => .vecFloatRelOp p.1 p.2) v) else
  if op = "VSHIFTOP" then dec (fun p : IntShape × VecShiftOp =>
      .case "VSHIFTOP" (.tuple [Vec.ishapeV p.1, Vec.vShiftOpV p.2]))
    (fun p => .vecShiftOp p.1 p.2) v else
  if op = "VBITMASK" then dec (fun s => .case "VBITMASK" (Vec.ishapeV s)) .vecBitmask v else
  if op = "VSWIZZLOP" then
    dec (fun o => .case "VSWIZZLOP" (.tuple [Vec.bshapeV, Vec.vSwizzleOpV o])) .vecSwizzle v else
  if op = "VSHUFFLE" then dec (fun ls : List LaneIdx =>
      .case "VSHUFFLE" (.tuple [Vec.bshapeV, .list (ls.map Vec.laneIdxV)])) .vecShuffle v else
  if op = "VEXTUNOP" then dec (fun p : IntShape × IntShape × VecExtUnOp =>
      .case "VEXTUNOP" (.tuple [Vec.ishapeV p.2.1, Vec.ishapeV p.1, Vec.vExtUnOpV p.2.2]))
    (fun p => .vecExtUnOp p.1 p.2.1 p.2.2) v else
  if op = "VEXTBINOP" then dec (fun p : IntShape × IntShape × VecExtBinOp =>
      .case "VEXTBINOP" (.tuple [Vec.ishapeV p.2.1, Vec.ishapeV p.1, Vec.vExtBinOpV p.2.2]))
    (fun p => .vecExtBinOp p.1 p.2.1 p.2.2) v else
  if op = "VEXTTERNOP" then dec (fun p : IntShape × IntShape × VecExtTernOp =>
      .case "VEXTTERNOP" (.tuple [Vec.ishapeV p.2.1, Vec.ishapeV p.1, Vec.vExtTernOpV p.2.2]))
    (fun p => .vecExtTernOp p.1 p.2.1 p.2.2) v else
  if op = "VNARROW" then dec (fun p : IntShape × IntShape × Signedness =>
      .case "VNARROW" (.tuple [Vec.ishapeV p.2.1, Vec.ishapeV p.1, Vec.sxV p.2.2]))
    (fun p => .vecNarrow p.1 p.2.1 p.2.2) v else
  if op = "VCVTOP" then dec (fun p : Shape × Shape × VecConvertOp =>
      .case "VCVTOP" (.tuple [Vec.shapeV p.2.1, Vec.shapeV p.1, Vec.vConvertOpV p.2.2]))
    (fun p => .vecConvert p.1 p.2.1 p.2.2) v else
  if op = "VSPLAT" then dec (fun s => .case "VSPLAT" (Vec.shapeV s)) .vecSplat v else
  if op = "VEXTRACT_LANE" then dec (fun p : Shape × Option Signedness × LaneIdx =>
      .case "VEXTRACT_LANE" (.tuple [Vec.shapeV p.1, .opt (p.2.1.map Vec.sxV),
        Vec.laneIdxV p.2.2]))
    (fun p => .vecExtractLane p.1 p.2.1 p.2.2) v else
  if op = "VREPLACE_LANE" then dec (fun p : Shape × LaneIdx =>
      .case "VREPLACE_LANE" (.tuple [Vec.shapeV p.1, Vec.laneIdxV p.2]))
    (fun p => .vecReplaceLane p.1 p.2) v else
  none

/-- **The decoder**: dispatch on the head, then invert. -/
noncomputable def recon (v : Value) : Option Instr :=
  match Typing.headOf v with
  | some op => decodeHead op v
  | none => none

theorem recon_of_head {v : Value} {op : MixopS} (h : Typing.headOf v = some op) :
    recon v = decodeHead op v := by
  unfold recon
  rw [h]

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2
