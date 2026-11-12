module

public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# Decoders: the head constructor of an encoded instruction

`instrHead i` is the IL constructor (`MixopS`) of `instrToV i`, written out per Core constructor.
`instrToV_head`: the image of every instruction is a `case` with that head, or the junk value
`.tuple []` (only an invalid `extendN_s`, which `Equiv.instrV` does not encode). The proof is one
kernel-checked `rfl` per leaf, never unfolding `instrToV`'s equation lemmas, so it stays fast.

`adminHead`/`adminToV_head` and `refHead`/`refToValue_head` lift this to administrative
instructions and references. Tag inversions (`Typing.Tags`) are then case splits on the head,
which compare string literals only.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Typing

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)

/-- The IL constructor of an instruction's image. -/
def instrHead : Instr → MixopS
  | .nop => "NOP"
  | .unreachable => "UNREACHABLE"
  | .drop => "DROP"
  | .select _ => "SELECT"
  | .block _ _ => "BLOCK"
  | .loop _ _ => "LOOP"
  | .if_ _ _ _ => "IF%%ELSE%"
  | .br _ => "BR"
  | .brIf _ => "BR_IF"
  | .brTable _ _ => "BR_TABLE"
  | .brOnNull _ => "BR_ON_NULL"
  | .brOnNonNull _ => "BR_ON_NON_NULL"
  | .brOnCast _ _ _ => "BR_ON_CAST"
  | .brOnCastFail _ _ _ => "BR_ON_CAST_FAIL"
  | .call _ => "CALL"
  | .callRef _ => "CALL_REF"
  | .callIndirect _ _ => "CALL_INDIRECT"
  | .return_ => "RETURN"
  | .returnCall _ => "RETURN_CALL"
  | .returnCallRef _ => "RETURN_CALL_REF"
  | .returnCallIndirect _ _ => "RETURN_CALL_INDIRECT"
  | .throw _ => "THROW"
  | .throwRef => "THROW_REF"
  | .tryTable _ _ _ => "TRY_TABLE"
  | .localGet _ => "LOCAL.GET"
  | .localSet _ => "LOCAL.SET"
  | .localTee _ => "LOCAL.TEE"
  | .globalGet _ => "GLOBAL.GET"
  | .globalSet _ => "GLOBAL.SET"
  | .tableGet _ => "TABLE.GET"
  | .tableSet _ => "TABLE.SET"
  | .tableSize _ => "TABLE.SIZE"
  | .tableGrow _ => "TABLE.GROW"
  | .tableFill _ => "TABLE.FILL"
  | .tableCopy _ _ => "TABLE.COPY"
  | .tableInit _ _ => "TABLE.INIT"
  | .elemDrop _ => "ELEM.DROP"
  | .intLoad _ _ _ _ => "LOAD"
  | .floatLoad _ _ _ => "LOAD"
  | .intStore _ _ _ _ => "STORE"
  | .floatStore _ _ _ => "STORE"
  | .vecLoad _ _ _ => "VLOAD"
  | .vecLoadLane _ _ _ _ => "VLOAD_LANE"
  | .vecStore _ _ => "VSTORE"
  | .vecStoreLane _ _ _ _ => "VSTORE_LANE"
  | .memorySize _ => "MEMORY.SIZE"
  | .memoryGrow _ => "MEMORY.GROW"
  | .memoryFill _ => "MEMORY.FILL"
  | .memoryCopy _ _ => "MEMORY.COPY"
  | .memoryInit _ _ => "MEMORY.INIT"
  | .dataDrop _ => "DATA.DROP"
  | .refNull _ => "REF.NULL"
  | .refIsNull => "REF.IS_NULL"
  | .refAsNonNull => "REF.AS_NON_NULL"
  | .refEq => "REF.EQ"
  | .refTest _ => "REF.TEST"
  | .refCast _ => "REF.CAST"
  | .refFunc _ => "REF.FUNC"
  | .refI31 => "REF.I31"
  | .i31Get _ => "I31.GET"
  | .structNew _ => "STRUCT.NEW"
  | .structNewDefault _ => "STRUCT.NEW_DEFAULT"
  | .structGet _ _ _ => "STRUCT.GET"
  | .structSet _ _ => "STRUCT.SET"
  | .arrayNew _ => "ARRAY.NEW"
  | .arrayNewDefault _ => "ARRAY.NEW_DEFAULT"
  | .arrayNewFixed _ _ => "ARRAY.NEW_FIXED"
  | .arrayNewData _ _ => "ARRAY.NEW_DATA"
  | .arrayNewElem _ _ => "ARRAY.NEW_ELEM"
  | .arrayGet _ _ => "ARRAY.GET"
  | .arraySet _ => "ARRAY.SET"
  | .arrayLen => "ARRAY.LEN"
  | .arrayFill _ => "ARRAY.FILL"
  | .arrayCopy _ _ => "ARRAY.COPY"
  | .arrayInitData _ _ => "ARRAY.INIT_DATA"
  | .arrayInitElem _ _ => "ARRAY.INIT_ELEM"
  | .externConvertAny => "EXTERN.CONVERT_ANY"
  | .anyConvertExtern => "ANY.CONVERT_EXTERN"
  | .intConst _ _ => "CONST"
  | .floatConst _ _ => "CONST"
  | .intUnOp _ _ => "UNOP"
  | .intBinOp _ _ => "BINOP"
  | .intTestOp _ _ => "TESTOP"
  | .intRelOp _ _ => "RELOP"
  | .floatUnOp _ _ => "UNOP"
  | .floatBinOp _ _ => "BINOP"
  | .floatRelOp _ _ => "RELOP"
  | .convert _ => "CVTOP"
  | .vecConst _ => "VCONST"
  | .vecUnOp _ => "VVUNOP"
  | .vecBinOp _ => "VVBINOP"
  | .vecTernOp _ => "VVTERNOP"
  | .vecTestOp _ => "VVTESTOP"
  | .vecIntUnOp _ _ => "VUNOP"
  | .vecFloatUnOp _ _ => "VUNOP"
  | .vecIntBinOp _ _ => "VBINOP"
  | .vecFloatBinOp _ _ => "VBINOP"
  | .vecIntTernOp _ _ => "VTERNOP"
  | .vecFloatTernOp _ _ => "VTERNOP"
  | .vecAllTrue _ => "VTESTOP"
  | .vecIntRelOp _ _ => "VRELOP"
  | .vecFloatRelOp _ _ => "VRELOP"
  | .vecShiftOp _ _ => "VSHIFTOP"
  | .vecBitmask _ => "VBITMASK"
  | .vecSwizzle _ => "VSWIZZLOP"
  | .vecShuffle _ => "VSHUFFLE"
  | .vecExtUnOp _ _ _ => "VEXTUNOP"
  | .vecExtBinOp _ _ _ => "VEXTBINOP"
  | .vecExtTernOp _ _ _ => "VEXTTERNOP"
  | .vecNarrow _ _ _ => "VNARROW"
  | .vecConvert _ _ _ => "VCVTOP"
  | .vecSplat _ => "VSPLAT"
  | .vecExtractLane _ _ _ => "VEXTRACT_LANE"
  | .vecReplaceLane _ _ => "VREPLACE_LANE"

/-- The head of a value, if it is a `case`. -/
def headOf : Value → Option MixopS
  | .case op _ => some op
  | _ => none

/-- `instrToV i` has head `instrHead i`, unless it is the junk value of an invalid `extendN_s`. -/
def HeadOk (i : Instr) : Prop := headOf (instrToV i) = some (instrHead i) ∨ instrToV i = .tuple []

/-- A schema constructor's image has the constructor's tag. -/
theorem headOf_schemaInstrV (c : Silmaril.Wasm.SpecTecEnc.Constructor) :
    headOf (schemaInstrV c) = some c.tag := by
  unfold schemaInstrV
  split <;> rfl

set_option maxRecDepth 10000 in
/-- **Every encoded instruction has its head** (or is junk). -/
theorem instrToV_head : ∀ i : Instr, HeadOk i := by
  intro i
  cases i
  all_goals try first
    | exact Or.inl rfl
  case select ts => cases ts <;> exact Or.inl rfl
  case intUnOp t op =>
    rcases op with _ | _ | _ | ⟨_ | _ | _ | _⟩ <;> cases t <;>
      first | exact Or.inl rfl | exact Or.inr rfl
  case intBinOp t op =>
    rcases op with _ | _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ | _ | _ | _ | _ | ⟨_ | _⟩ | _ | _ <;> cases t <;>
      exact Or.inl rfl
  case intTestOp t op => cases t <;> cases op <;> exact Or.inl rfl
  case intRelOp t op =>
    rcases op with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> cases t <;> exact Or.inl rfl
  case floatUnOp t op => cases t <;> cases op <;> exact Or.inl rfl
  case floatBinOp t op => cases t <;> cases op <;> exact Or.inl rfl
  case floatRelOp t op => cases t <;> cases op <;> exact Or.inl rfl
  all_goals
    refine Or.inl ?_
    first
      | (show headOf (schemaInstrV (Silmaril.Wasm.SpecTecEnc.encodeInstruction _)) = _
         rw [headOf_schemaInstrV]
         simp only [Silmaril.Wasm.SpecTecEnc.encodeInstruction]
         rfl)

/-- A `case` image has the instruction's head. -/
theorem instrToV_case {i : Instr} {op : MixopS} {w : Value} (h : instrToV i = .case op w) :
    op = instrHead i := by
  rcases instrToV_head i with h' | h'
  · rw [h] at h'
    exact Option.some.inj h'
  · rw [h] at h'
    cases h'

/-- The IL constructor of a reference's image. -/
def refHead : Ref → MixopS
  | .i31 _ => "REF.I31_NUM"
  | .null => "REF.NULL_ADDR"
  | .struct _ => "REF.STRUCT_ADDR"
  | .array _ => "REF.ARRAY_ADDR"
  | .func _ => "REF.FUNC_ADDR"
  | .exn _ => "REF.EXN_ADDR"
  | .host _ => "REF.HOST_ADDR"
  | .extern _ => "REF.EXTERN"

theorem refToValue_head (r : Ref) : headOf (refToValue r) = some (refHead r) := by
  cases r <;> rfl

/-- The IL constructor of an administrative instruction's image. -/
def adminHead : Admin → MixopS
  | .plain i => instrHead i
  | .ref r => refHead r
  | .callRefType _ => "CALL_REF"
  | .returnCallRefType _ => "RETURN_CALL_REF"
  | .label .. => "LABEL_%{%}%"
  | .handler .. => "HANDLER_%{%}%"
  | .frame .. => "FRAME_%{%}%"
  | .trap => "TRAP"

/-- A `case` image of an administrative instruction has its head. -/
theorem adminToV_case {a : Admin} {op : MixopS} {w : Value} (h : adminToV a = .case op w) :
    op = adminHead a := by
  cases a with
  | plain i => exact instrToV_case (by simpa only [adminToV] using h)
  | ref r =>
      have h' := refToValue_head r
      rw [show refToValue r = .case op w from by simpa only [adminToV] using h] at h'
      exact Option.some.inj h'
  | callRefType d => simp only [adminToV, Value.case.injEq] at h; exact h.1.symm
  | returnCallRefType d => simp only [adminToV, Value.case.injEq] at h; exact h.1.symm
  | label n c b => simp only [adminToV, Value.case.injEq] at h; exact h.1.symm
  | handler n c b => simp only [adminToV, Value.case.injEq] at h; exact h.1.symm
  | frame n f b => simp only [adminToV, Value.case.injEq] at h; exact h.1.symm
  | trap =>
      simp only [adminToV, Silmaril.SpecTec.Equiv.Execution.caseNilV, Value.case.injEq] at h
      exact h.1.symm

end Silmaril.Wasm.SpecTec.Sim.Typing
