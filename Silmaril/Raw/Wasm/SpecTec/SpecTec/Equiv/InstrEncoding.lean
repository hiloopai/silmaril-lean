module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.BinaryTypes
public import Silmaril.Wasm.Instructions

/-!
# Instruction values shared by the binary and runtime bridges

The binary grammar proves properties of this encoding. The runtime bridge uses
its values when it encodes function bodies.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv

open Silmaril.SpecTec.IL Silmaril.SpecTec.Sem

/-- The SpecTec `instr` value of each instruction the binary-format bridge reaches, as the
elaborated stream spells it: the 137 that `Core.PlainOp` names, and the ones
whose only immediate is an index.  It is a *total* function only so that it can
be applied in a statement: elsewhere it is `.tuple []`, which is not a `case`
and therefore not in the denotation of the SpecTec type `instr` at all
(`instrV_case`). -/
def instrV : Wasm.Instr → Value
  | .unreachable => caseV "UNREACHABLE" []
  | .nop => caseV "NOP" []
  | .drop => caseV "DROP" []
  | (.select none) => .case "SELECT" (.opt none)
  | .throwRef => caseV "THROW_REF" []
  | .return_ => caseV "RETURN" []
  | .refIsNull => caseV "REF.IS_NULL" []
  | .refEq => caseV "REF.EQ" []
  | .refAsNonNull => caseV "REF.AS_NON_NULL" []
  | (.intTestOp .i32 .eqz) => caseV "TESTOP" [caseV "I32" [], caseV "EQZ" []]
  | (.intRelOp .i32 .eq) => caseV "RELOP" [caseV "I32" [], caseV "EQ" []]
  | (.intRelOp .i32 .ne) => caseV "RELOP" [caseV "I32" [], caseV "NE" []]
  | (.intRelOp .i32 (.lt .signed)) => caseV "RELOP" [caseV "I32" [], .case "LT" (caseV "S" [])]
  | (.intRelOp .i32 (.lt .unsigned)) => caseV "RELOP" [caseV "I32" [], .case "LT" (caseV "U" [])]
  | (.intRelOp .i32 (.gt .signed)) => caseV "RELOP" [caseV "I32" [], .case "GT" (caseV "S" [])]
  | (.intRelOp .i32 (.gt .unsigned)) => caseV "RELOP" [caseV "I32" [], .case "GT" (caseV "U" [])]
  | (.intRelOp .i32 (.le .signed)) => caseV "RELOP" [caseV "I32" [], .case "LE" (caseV "S" [])]
  | (.intRelOp .i32 (.le .unsigned)) => caseV "RELOP" [caseV "I32" [], .case "LE" (caseV "U" [])]
  | (.intRelOp .i32 (.ge .signed)) => caseV "RELOP" [caseV "I32" [], .case "GE" (caseV "S" [])]
  | (.intRelOp .i32 (.ge .unsigned)) => caseV "RELOP" [caseV "I32" [], .case "GE" (caseV "U" [])]
  | (.intTestOp .i64 .eqz) => caseV "TESTOP" [caseV "I64" [], caseV "EQZ" []]
  | (.intRelOp .i64 .eq) => caseV "RELOP" [caseV "I64" [], caseV "EQ" []]
  | (.intRelOp .i64 .ne) => caseV "RELOP" [caseV "I64" [], caseV "NE" []]
  | (.intRelOp .i64 (.lt .signed)) => caseV "RELOP" [caseV "I64" [], .case "LT" (caseV "S" [])]
  | (.intRelOp .i64 (.lt .unsigned)) => caseV "RELOP" [caseV "I64" [], .case "LT" (caseV "U" [])]
  | (.intRelOp .i64 (.gt .signed)) => caseV "RELOP" [caseV "I64" [], .case "GT" (caseV "S" [])]
  | (.intRelOp .i64 (.gt .unsigned)) => caseV "RELOP" [caseV "I64" [], .case "GT" (caseV "U" [])]
  | (.intRelOp .i64 (.le .signed)) => caseV "RELOP" [caseV "I64" [], .case "LE" (caseV "S" [])]
  | (.intRelOp .i64 (.le .unsigned)) => caseV "RELOP" [caseV "I64" [], .case "LE" (caseV "U" [])]
  | (.intRelOp .i64 (.ge .signed)) => caseV "RELOP" [caseV "I64" [], .case "GE" (caseV "S" [])]
  | (.intRelOp .i64 (.ge .unsigned)) => caseV "RELOP" [caseV "I64" [], .case "GE" (caseV "U" [])]
  | (.floatRelOp .f32 .eq) => caseV "RELOP" [caseV "F32" [], caseV "EQ" []]
  | (.floatRelOp .f32 .ne) => caseV "RELOP" [caseV "F32" [], caseV "NE" []]
  | (.floatRelOp .f32 .lt) => caseV "RELOP" [caseV "F32" [], caseV "LT" []]
  | (.floatRelOp .f32 .gt) => caseV "RELOP" [caseV "F32" [], caseV "GT" []]
  | (.floatRelOp .f32 .le) => caseV "RELOP" [caseV "F32" [], caseV "LE" []]
  | (.floatRelOp .f32 .ge) => caseV "RELOP" [caseV "F32" [], caseV "GE" []]
  | (.floatRelOp .f64 .eq) => caseV "RELOP" [caseV "F64" [], caseV "EQ" []]
  | (.floatRelOp .f64 .ne) => caseV "RELOP" [caseV "F64" [], caseV "NE" []]
  | (.floatRelOp .f64 .lt) => caseV "RELOP" [caseV "F64" [], caseV "LT" []]
  | (.floatRelOp .f64 .gt) => caseV "RELOP" [caseV "F64" [], caseV "GT" []]
  | (.floatRelOp .f64 .le) => caseV "RELOP" [caseV "F64" [], caseV "LE" []]
  | (.floatRelOp .f64 .ge) => caseV "RELOP" [caseV "F64" [], caseV "GE" []]
  | (.intUnOp .i32 .clz) => caseV "UNOP" [caseV "I32" [], caseV "CLZ" []]
  | (.intUnOp .i32 .ctz) => caseV "UNOP" [caseV "I32" [], caseV "CTZ" []]
  | (.intUnOp .i32 .popcnt) => caseV "UNOP" [caseV "I32" [], caseV "POPCNT" []]
  | (.intBinOp .i32 .add) => caseV "BINOP" [caseV "I32" [], caseV "ADD" []]
  | (.intBinOp .i32 .sub) => caseV "BINOP" [caseV "I32" [], caseV "SUB" []]
  | (.intBinOp .i32 .mul) => caseV "BINOP" [caseV "I32" [], caseV "MUL" []]
  | (.intBinOp .i32 (.div .signed)) => caseV "BINOP" [caseV "I32" [], .case "DIV" (caseV "S" [])]
  | (.intBinOp .i32 (.div .unsigned)) => caseV "BINOP" [caseV "I32" [], .case "DIV" (caseV "U" [])]
  | (.intBinOp .i32 (.rem .signed)) => caseV "BINOP" [caseV "I32" [], .case "REM" (caseV "S" [])]
  | (.intBinOp .i32 (.rem .unsigned)) => caseV "BINOP" [caseV "I32" [], .case "REM" (caseV "U" [])]
  | (.intBinOp .i32 .and) => caseV "BINOP" [caseV "I32" [], caseV "AND" []]
  | (.intBinOp .i32 .or) => caseV "BINOP" [caseV "I32" [], caseV "OR" []]
  | (.intBinOp .i32 .xor) => caseV "BINOP" [caseV "I32" [], caseV "XOR" []]
  | (.intBinOp .i32 .shl) => caseV "BINOP" [caseV "I32" [], caseV "SHL" []]
  | (.intBinOp .i32 (.shr .signed)) => caseV "BINOP" [caseV "I32" [], .case "SHR" (caseV "S" [])]
  | (.intBinOp .i32 (.shr .unsigned)) => caseV "BINOP" [caseV "I32" [], .case "SHR" (caseV "U" [])]
  | (.intBinOp .i32 .rotl) => caseV "BINOP" [caseV "I32" [], caseV "ROTL" []]
  | (.intBinOp .i32 .rotr) => caseV "BINOP" [caseV "I32" [], caseV "ROTR" []]
  | (.intUnOp .i64 .clz) => caseV "UNOP" [caseV "I64" [], caseV "CLZ" []]
  | (.intUnOp .i64 .ctz) => caseV "UNOP" [caseV "I64" [], caseV "CTZ" []]
  | (.intUnOp .i64 .popcnt) => caseV "UNOP" [caseV "I64" [], caseV "POPCNT" []]
  | (.intUnOp .i32 (.extend .i8)) =>
      caseV "UNOP" [caseV "I32" [], caseV "EXTEND" [caseV "%" [.num (.natN 8)]]]
  | (.intUnOp .i32 (.extend .i16)) =>
      caseV "UNOP" [caseV "I32" [], caseV "EXTEND" [caseV "%" [.num (.natN 16)]]]
  | (.intUnOp .i64 (.extend .i8)) =>
      caseV "UNOP" [caseV "I64" [], caseV "EXTEND" [caseV "%" [.num (.natN 8)]]]
  | (.intUnOp .i64 (.extend .i16)) =>
      caseV "UNOP" [caseV "I64" [], caseV "EXTEND" [caseV "%" [.num (.natN 16)]]]
  | (.intUnOp .i64 (.extend .i32)) =>
      caseV "UNOP" [caseV "I64" [], caseV "EXTEND" [caseV "%" [.num (.natN 32)]]]
  | (.intBinOp .i64 .add) => caseV "BINOP" [caseV "I64" [], caseV "ADD" []]
  | (.intBinOp .i64 .sub) => caseV "BINOP" [caseV "I64" [], caseV "SUB" []]
  | (.intBinOp .i64 .mul) => caseV "BINOP" [caseV "I64" [], caseV "MUL" []]
  | (.intBinOp .i64 (.div .signed)) => caseV "BINOP" [caseV "I64" [], .case "DIV" (caseV "S" [])]
  | (.intBinOp .i64 (.div .unsigned)) => caseV "BINOP" [caseV "I64" [], .case "DIV" (caseV "U" [])]
  | (.intBinOp .i64 (.rem .signed)) => caseV "BINOP" [caseV "I64" [], .case "REM" (caseV "S" [])]
  | (.intBinOp .i64 (.rem .unsigned)) => caseV "BINOP" [caseV "I64" [], .case "REM" (caseV "U" [])]
  | (.intBinOp .i64 .and) => caseV "BINOP" [caseV "I64" [], caseV "AND" []]
  | (.intBinOp .i64 .or) => caseV "BINOP" [caseV "I64" [], caseV "OR" []]
  | (.intBinOp .i64 .xor) => caseV "BINOP" [caseV "I64" [], caseV "XOR" []]
  | (.intBinOp .i64 .shl) => caseV "BINOP" [caseV "I64" [], caseV "SHL" []]
  | (.intBinOp .i64 (.shr .signed)) => caseV "BINOP" [caseV "I64" [], .case "SHR" (caseV "S" [])]
  | (.intBinOp .i64 (.shr .unsigned)) => caseV "BINOP" [caseV "I64" [], .case "SHR" (caseV "U" [])]
  | (.intBinOp .i64 .rotl) => caseV "BINOP" [caseV "I64" [], caseV "ROTL" []]
  | (.intBinOp .i64 .rotr) => caseV "BINOP" [caseV "I64" [], caseV "ROTR" []]
  | (.floatUnOp .f32 .abs) => caseV "UNOP" [caseV "F32" [], caseV "ABS" []]
  | (.floatUnOp .f32 .neg) => caseV "UNOP" [caseV "F32" [], caseV "NEG" []]
  | (.floatUnOp .f32 .ceil) => caseV "UNOP" [caseV "F32" [], caseV "CEIL" []]
  | (.floatUnOp .f32 .floor) => caseV "UNOP" [caseV "F32" [], caseV "FLOOR" []]
  | (.floatUnOp .f32 .trunc) => caseV "UNOP" [caseV "F32" [], caseV "TRUNC" []]
  | (.floatUnOp .f32 .nearest) => caseV "UNOP" [caseV "F32" [], caseV "NEAREST" []]
  | (.floatUnOp .f32 .sqrt) => caseV "UNOP" [caseV "F32" [], caseV "SQRT" []]
  | (.floatBinOp .f32 .add) => caseV "BINOP" [caseV "F32" [], caseV "ADD" []]
  | (.floatBinOp .f32 .sub) => caseV "BINOP" [caseV "F32" [], caseV "SUB" []]
  | (.floatBinOp .f32 .mul) => caseV "BINOP" [caseV "F32" [], caseV "MUL" []]
  | (.floatBinOp .f32 .div) => caseV "BINOP" [caseV "F32" [], caseV "DIV" []]
  | (.floatBinOp .f32 .min) => caseV "BINOP" [caseV "F32" [], caseV "MIN" []]
  | (.floatBinOp .f32 .max) => caseV "BINOP" [caseV "F32" [], caseV "MAX" []]
  | (.floatBinOp .f32 .copysign) => caseV "BINOP" [caseV "F32" [], caseV "COPYSIGN" []]
  | (.floatUnOp .f64 .abs) => caseV "UNOP" [caseV "F64" [], caseV "ABS" []]
  | (.floatUnOp .f64 .neg) => caseV "UNOP" [caseV "F64" [], caseV "NEG" []]
  | (.floatUnOp .f64 .ceil) => caseV "UNOP" [caseV "F64" [], caseV "CEIL" []]
  | (.floatUnOp .f64 .floor) => caseV "UNOP" [caseV "F64" [], caseV "FLOOR" []]
  | (.floatUnOp .f64 .trunc) => caseV "UNOP" [caseV "F64" [], caseV "TRUNC" []]
  | (.floatUnOp .f64 .nearest) => caseV "UNOP" [caseV "F64" [], caseV "NEAREST" []]
  | (.floatUnOp .f64 .sqrt) => caseV "UNOP" [caseV "F64" [], caseV "SQRT" []]
  | (.floatBinOp .f64 .add) => caseV "BINOP" [caseV "F64" [], caseV "ADD" []]
  | (.floatBinOp .f64 .sub) => caseV "BINOP" [caseV "F64" [], caseV "SUB" []]
  | (.floatBinOp .f64 .mul) => caseV "BINOP" [caseV "F64" [], caseV "MUL" []]
  | (.floatBinOp .f64 .div) => caseV "BINOP" [caseV "F64" [], caseV "DIV" []]
  | (.floatBinOp .f64 .min) => caseV "BINOP" [caseV "F64" [], caseV "MIN" []]
  | (.floatBinOp .f64 .max) => caseV "BINOP" [caseV "F64" [], caseV "MAX" []]
  | (.floatBinOp .f64 .copysign) => caseV "BINOP" [caseV "F64" [], caseV "COPYSIGN" []]
  | (.convert .wrap) => caseV "CVTOP" [caseV "I32" [], caseV "I64" [], caseV "WRAP" []]
  | (.convert (.trunc .f32 .i32 .signed)) =>
      caseV "CVTOP" [caseV "I32" [], caseV "F32" [], .case "TRUNC" (caseV "S" [])]
  | (.convert (.trunc .f32 .i32 .unsigned)) =>
      caseV "CVTOP" [caseV "I32" [], caseV "F32" [], .case "TRUNC" (caseV "U" [])]
  | (.convert (.trunc .f64 .i32 .signed)) =>
      caseV "CVTOP" [caseV "I32" [], caseV "F64" [], .case "TRUNC" (caseV "S" [])]
  | (.convert (.trunc .f64 .i32 .unsigned)) =>
      caseV "CVTOP" [caseV "I32" [], caseV "F64" [], .case "TRUNC" (caseV "U" [])]
  | (.convert (.extend .signed)) =>
      caseV "CVTOP" [caseV "I64" [], caseV "I32" [], .case "EXTEND" (caseV "S" [])]
  | (.convert (.extend .unsigned)) =>
      caseV "CVTOP" [caseV "I64" [], caseV "I32" [], .case "EXTEND" (caseV "U" [])]
  | (.convert (.trunc .f32 .i64 .signed)) =>
      caseV "CVTOP" [caseV "I64" [], caseV "F32" [], .case "TRUNC" (caseV "S" [])]
  | (.convert (.trunc .f32 .i64 .unsigned)) =>
      caseV "CVTOP" [caseV "I64" [], caseV "F32" [], .case "TRUNC" (caseV "U" [])]
  | (.convert (.trunc .f64 .i64 .signed)) =>
      caseV "CVTOP" [caseV "I64" [], caseV "F64" [], .case "TRUNC" (caseV "S" [])]
  | (.convert (.trunc .f64 .i64 .unsigned)) =>
      caseV "CVTOP" [caseV "I64" [], caseV "F64" [], .case "TRUNC" (caseV "U" [])]
  | (.convert (.convert .i32 .f32 .signed)) =>
      caseV "CVTOP" [caseV "F32" [], caseV "I32" [], .case "CONVERT" (caseV "S" [])]
  | (.convert (.convert .i32 .f32 .unsigned)) =>
      caseV "CVTOP" [caseV "F32" [], caseV "I32" [], .case "CONVERT" (caseV "U" [])]
  | (.convert (.convert .i64 .f32 .signed)) =>
      caseV "CVTOP" [caseV "F32" [], caseV "I64" [], .case "CONVERT" (caseV "S" [])]
  | (.convert (.convert .i64 .f32 .unsigned)) =>
      caseV "CVTOP" [caseV "F32" [], caseV "I64" [], .case "CONVERT" (caseV "U" [])]
  | (.convert .demote) => caseV "CVTOP" [caseV "F32" [], caseV "F64" [], caseV "DEMOTE" []]
  | (.convert (.convert .i32 .f64 .signed)) =>
      caseV "CVTOP" [caseV "F64" [], caseV "I32" [], .case "CONVERT" (caseV "S" [])]
  | (.convert (.convert .i32 .f64 .unsigned)) =>
      caseV "CVTOP" [caseV "F64" [], caseV "I32" [], .case "CONVERT" (caseV "U" [])]
  | (.convert (.convert .i64 .f64 .signed)) =>
      caseV "CVTOP" [caseV "F64" [], caseV "I64" [], .case "CONVERT" (caseV "S" [])]
  | (.convert (.convert .i64 .f64 .unsigned)) =>
      caseV "CVTOP" [caseV "F64" [], caseV "I64" [], .case "CONVERT" (caseV "U" [])]
  | (.convert .promote) => caseV "CVTOP" [caseV "F64" [], caseV "F32" [], caseV "PROMOTE" []]
  | (.convert (.reinterpretInt .f32)) =>
      caseV "CVTOP" [caseV "I32" [], caseV "F32" [], caseV "REINTERPRET" []]
  | (.convert (.reinterpretInt .f64)) =>
      caseV "CVTOP" [caseV "I64" [], caseV "F64" [], caseV "REINTERPRET" []]
  | (.convert (.reinterpretFloat .i32)) =>
      caseV "CVTOP" [caseV "F32" [], caseV "I32" [], caseV "REINTERPRET" []]
  | (.convert (.reinterpretFloat .i64)) =>
      caseV "CVTOP" [caseV "F64" [], caseV "I64" [], caseV "REINTERPRET" []]
  | .throw x => .case "THROW" (Encode.toValue x)
  | .br l => .case "BR" (Encode.toValue l)
  | .brIf l => .case "BR_IF" (Encode.toValue l)
  | .call x => .case "CALL" (Encode.toValue x)
  | .returnCall x => .case "RETURN_CALL" (Encode.toValue x)
  | .callRef x => .case "CALL_REF" (.case "_IDX" (Encode.toValue x))
  | .returnCallRef x => .case "RETURN_CALL_REF" (.case "_IDX" (Encode.toValue x))
  | .localGet x => .case "LOCAL.GET" (Encode.toValue x)
  | .localSet x => .case "LOCAL.SET" (Encode.toValue x)
  | .localTee x => .case "LOCAL.TEE" (Encode.toValue x)
  | .globalGet x => .case "GLOBAL.GET" (Encode.toValue x)
  | .globalSet x => .case "GLOBAL.SET" (Encode.toValue x)
  | .tableGet x => .case "TABLE.GET" (Encode.toValue x)
  | .tableSet x => .case "TABLE.SET" (Encode.toValue x)
  | .refFunc x => .case "REF.FUNC" (Encode.toValue x)
  | .brOnNull l => .case "BR_ON_NULL" (Encode.toValue l)
  | .brOnNonNull l => .case "BR_ON_NON_NULL" (Encode.toValue l)
  | .memorySize x => .case "MEMORY.SIZE" (Encode.toValue x)
  | .memoryGrow x => .case "MEMORY.GROW" (Encode.toValue x)
  | .refNull ht => .case "REF.NULL" (Encode.toValue ht)
  | _ => .tuple []

/-- `blocktype = _RESULT valtype? | _IDX typeidx`
(`specs/spectec/wasm-3.0.ast`, `(typ "blocktype" …)`). -/
def blockTypeView : Wasm.BlockType → MixopS × Value
  | .empty => ("_RESULT", .opt none)
  | .value t => ("_RESULT", .opt (some (Encode.toValue t)))
  | .typeIdx x => ("_IDX", Encode.toValue x)

/-- The partial inverse of `blockTypeView`. -/
def blockTypeUnview : MixopS → Value → Option Wasm.BlockType
  | "_RESULT", .opt none => some .empty
  | "_RESULT", .opt (some w) => (Encode.ofValue (α := Wasm.ValType) w).map .value
  | "_IDX", w => (Encode.ofValue (α := Wasm.TypeIdx) w).map .typeIdx
  | _, _ => none

/-- `blocktype` (`specs/spectec/wasm-3.0.ast`, `(typ "blocktype" …)`). -/
instance instEncodeBlockType : Encode Wasm.BlockType :=
  Encode.ofCase blockTypeView blockTypeUnview
    (by
      intro a
      match a with
      | .empty => rfl
      | .value t => simp [blockTypeView, blockTypeUnview, Encode.ofValue_toValue]
      | .typeIdx x => simp [blockTypeView, blockTypeUnview, Encode.ofValue_toValue])
    (by
      intro op v a h
      unfold blockTypeUnview at h
      split at h <;>
        first
          | (cases h; rfl)
          | (simp only [Option.map_eq_some_iff] at h
             obtain ⟨x, hx, rfl⟩ := h
             rw [blockTypeView, Encode.toValue_eq_of_ofValue hx])
          | exact absurd h (by simp))

/-- `catch = CATCH tagidx labelidx | CATCH_REF tagidx labelidx | CATCH_ALL labelidx
| CATCH_ALL_REF labelidx` (`specs/spectec/wasm-3.0.ast`, `(typ "catch" …)`). -/
def catchView : Wasm.Catch → MixopS × Value
  | .catch_ x l => ("CATCH", .tuple [Encode.toValue x, Encode.toValue l])
  | .catchRef x l => ("CATCH_REF", .tuple [Encode.toValue x, Encode.toValue l])
  | .catchAll l => ("CATCH_ALL", Encode.toValue l)
  | .catchAllRef l => ("CATCH_ALL_REF", Encode.toValue l)

/-- The partial inverse of `catchView`. -/
def catchUnview : MixopS → Value → Option Wasm.Catch
  | "CATCH", .tuple [a, b] =>
      (Encode.ofValue (α := Wasm.TagIdx) a).bind fun x =>
        (Encode.ofValue (α := Wasm.LabelIdx) b).map (.catch_ x)
  | "CATCH_REF", .tuple [a, b] =>
      (Encode.ofValue (α := Wasm.TagIdx) a).bind fun x =>
        (Encode.ofValue (α := Wasm.LabelIdx) b).map (.catchRef x)
  | "CATCH_ALL", a => (Encode.ofValue (α := Wasm.LabelIdx) a).map .catchAll
  | "CATCH_ALL_REF", a => (Encode.ofValue (α := Wasm.LabelIdx) a).map .catchAllRef
  | _, _ => none

/-- `catch` (`1.3-syntax.instructions.spectec`). -/
instance instEncodeCatch : Encode Wasm.Catch :=
  Encode.ofCase catchView catchUnview
    (by
      intro a
      match a with
      | .catch_ x l => simp [catchView, catchUnview, Encode.ofValue_toValue]
      | .catchRef x l => simp [catchView, catchUnview, Encode.ofValue_toValue]
      | .catchAll l => simp [catchView, catchUnview, Encode.ofValue_toValue]
      | .catchAllRef l => simp [catchView, catchUnview, Encode.ofValue_toValue])
    (by
      intro op v a h
      unfold catchUnview at h
      split at h <;>
        first
          | (simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
             obtain ⟨x, hx, y, hy, rfl⟩ := h
             rw [catchView, Encode.toValue_eq_of_ofValue hx, Encode.toValue_eq_of_ofValue hy])
          | (simp only [Option.map_eq_some_iff] at h
             obtain ⟨x, hx, rfl⟩ := h
             rw [catchView, Encode.toValue_eq_of_ofValue hx])
          | exact absurd h (by simp))

end Silmaril.SpecTec.Equiv
