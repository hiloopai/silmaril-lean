module

public import Silmaril.Raw.Wasm.SpecTecLean.Wasm30
public import Silmaril.Wasm.Execution.Core.Step

/-!
# The official SpecTec Lean model of Wasm 3.0, and a first bridge to it

`Silmaril.Raw.Wasm.SpecTecLean.Wasm30` is the Lean file that SpecTec's own (work-in-progress) Lean 4
backend generates for the wasm-3.0 specification at our pin
`WebAssembly/spec@608711107b7f1edb13efd57b7d79b49477462d36` (namespace `SpecTecLean`; generator,
patches and commands in `NOTICES/spectec/README.md`, assessment in
`docs/projects/wasm-extras.md`). Its relations are inductive predicates over generated
datatypes: `SpecTecLean.Step_pure`, `Step_read`, `Step`, with well-formedness relations `wf_*`
as premises.

This header fixes the first slice of a correspondence with our side:

* **a translation** of a fragment of silmaril-lean Core 3.0 administrative instructions into
  their `instr` (`slAdmin?`): `unreachable`, `nop`, `drop`, `select` without annotation, the
  integer constants and `i32.add`/`i64.add`, and `trap`. Everything else (floats, vectors,
  references, annotated `select`, the other operators, administrative frames) is `none`;
* **their rules, transcribed** (`SLUnreachable`, `SLNop`, `SLDrop`, `SLSelectTrue`,
  `SLSelectFalse`, `SLBinopVal`): each is the premises and conclusion of one constructor of
  `SpecTecLean.Step_pure`, exactly as the generated file states them. `Thms` proves that each
  transcription is sound for its constructor (`slNop_sound`, …), so the transcription cannot
  be stronger than their rule;
* **the Core shapes** of the same rules (`CoreUnreachable`, …), which are the conclusions of the
  constructors of `ParametricStep` and `NumericStep.intBinOp`.

The theorems (`Silmaril.Wasm.SpecTecLean.Thms`) relate, rule by rule, their rule at the image of a
Core sequence to the Core rule, and the Core rule to our declarative reading of the pinned IL
(`Silmaril.Wasm.SpecTec.Sim.Fires`/`SPure`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTecLean

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-! ## The translation of the fragment -/

/-- An integer type as their `addrtype` (their `Inn`). -/
def addrT : IntType → SpecTecLean.addrtype
  | .i32 => .I32
  | .i64 => .I64

/-- An integer type as their `numtype`. -/
def numT : IntType → SpecTecLean.numtype
  | .i32 => .I32
  | .i64 => .I64

/-- An integer bit pattern as their `num_`: `mk_num__0 Inn (mk_uN n)`. -/
def numSL (t : IntType) (b : BitVec t.width) : SpecTecLean.num_ :=
  .mk_num__0 (addrT t) (.mk_uN b.toNat)

/-- A source instruction of the fragment as their `instr`. -/
def slInstr? : Instr → Option SpecTecLean.instr
  | .unreachable => some .UNREACHABLE
  | .nop => some .NOP
  | .drop => some .DROP
  | .select none => some (.SELECT none)
  | .intConst t b => some (.CONST (numT t) (numSL t b))
  | .intBinOp t .add => some (.BINOP (numT t) (.mk_binop__0 (addrT t) .ADD))
  | _ => none

/-- An administrative instruction of the fragment as their `instr`. -/
def slAdmin? : Admin → Option SpecTecLean.instr
  | .plain i => slInstr? i
  | .trap => some .TRAP
  | _ => none

/-- A sequence of the fragment as their `instr*` (`List.mapM slAdmin?`). -/
def slAdmins? : List Admin → Option (List SpecTecLean.instr)
  | [] => some []
  | a :: as => match slAdmin? a, slAdmins? as with
    | some x, some X => some (x :: X)
    | _, _ => none

/-- An integer value as their `val`. -/
def slVal (t : IntType) (b : BitVec t.width) : SpecTecLean.val := .CONST (numT t) (numSL t b)

/-! ## Their rules, transcribed from the constructors of `SpecTecLean.Step_pure` -/

/-- `Step_pure/unreachable`. -/
def SLUnreachable (I J : List SpecTecLean.instr) : Prop :=
  I = [.UNREACHABLE] ∧ J = [.TRAP] ∧ SpecTecLean.wf_instr .UNREACHABLE ∧
    SpecTecLean.wf_instr .TRAP

/-- `Step_pure/nop`. -/
def SLNop (I J : List SpecTecLean.instr) : Prop :=
  I = [.NOP] ∧ J = [] ∧ SpecTecLean.wf_instr .NOP

/-- `Step_pure/drop`. -/
def SLDrop (I J : List SpecTecLean.instr) : Prop :=
  ∃ v : SpecTecLean.val, I = [SpecTecLean.instr_val v, .DROP] ∧ J = [] ∧
    SpecTecLean.wf_val v ∧ SpecTecLean.wf_instr .DROP

/-- `Step_pure/select-true`. -/
def SLSelectTrue (I J : List SpecTecLean.instr) : Prop :=
  ∃ (v₁ v₂ : SpecTecLean.val) (c : SpecTecLean.num_) (t : Option (List SpecTecLean.valtype)),
    I = [SpecTecLean.instr_val v₁, SpecTecLean.instr_val v₂, .CONST .I32 c, .SELECT t] ∧
    J = [SpecTecLean.instr_val v₁] ∧
    (SpecTecLean.proj_num__0 c != none) = true ∧
    (SpecTecLean.proj_uN_0 (Option.get! (SpecTecLean.proj_num__0 c)) != 0) = true ∧
    SpecTecLean.wf_val v₁ ∧ SpecTecLean.wf_val v₂ ∧ SpecTecLean.wf_instr (.CONST .I32 c) ∧
    SpecTecLean.wf_instr (.SELECT t)

/-- `Step_pure/select-false`. -/
def SLSelectFalse (I J : List SpecTecLean.instr) : Prop :=
  ∃ (v₁ v₂ : SpecTecLean.val) (c : SpecTecLean.num_) (t : Option (List SpecTecLean.valtype)),
    I = [SpecTecLean.instr_val v₁, SpecTecLean.instr_val v₂, .CONST .I32 c, .SELECT t] ∧
    J = [SpecTecLean.instr_val v₂] ∧
    (SpecTecLean.proj_num__0 c != none) = true ∧
    (SpecTecLean.proj_uN_0 (Option.get! (SpecTecLean.proj_num__0 c)) == 0) = true ∧
    SpecTecLean.wf_val v₁ ∧ SpecTecLean.wf_val v₂ ∧ SpecTecLean.wf_instr (.CONST .I32 c) ∧
    SpecTecLean.wf_instr (.SELECT t)

/-- `Step_pure/binop-val`. -/
def SLBinopVal (I J : List SpecTecLean.instr) : Prop :=
  ∃ (nt : SpecTecLean.numtype) (c₁ c₂ : SpecTecLean.num_) (op : SpecTecLean.binop_)
    (c : SpecTecLean.num_) (r : Option (List SpecTecLean.num_)),
    I = [.CONST nt c₁, .CONST nt c₂, .BINOP nt op] ∧ J = [.CONST nt c] ∧
    SpecTecLean.fun_binop_ nt op c₁ c₂ r ∧ List.length (Option.get! r) > 0 ∧
    (r != none) = true ∧ List.contains (Option.get! r) c = true ∧
    SpecTecLean.Forall (fun x => SpecTecLean.wf_num_ nt x) (Option.get! r) ∧
    SpecTecLean.wf_instr (.CONST nt c₁) ∧ SpecTecLean.wf_instr (.CONST nt c₂) ∧
    SpecTecLean.wf_instr (.BINOP nt op) ∧ SpecTecLean.wf_instr (.CONST nt c)

/-! ## The same rules in Core 3.0 -/

/-- `ParametricStep.unreachable`. -/
def CoreUnreachable (is js : List Admin) : Prop := is = [.plain .unreachable] ∧ js = [.trap]

/-- `ParametricStep.nop`. -/
def CoreNop (is js : List Admin) : Prop := is = [.plain .nop] ∧ js = []

/-- `ParametricStep.drop`. -/
def CoreDrop (is js : List Admin) : Prop := ∃ v : Val, is = [v.toAdmin, .plain .drop] ∧ js = []

/-- `ParametricStep.selectTrue`. -/
def CoreSelectTrue (is js : List Admin) : Prop :=
  ∃ (v₁ v₂ : Val) (c : BitVec 32) (ts : Option (List ValType)), c ≠ 0 ∧
    is = [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)] ∧ js = [v₁.toAdmin]

/-- `ParametricStep.selectFalse`. -/
def CoreSelectFalse (is js : List Admin) : Prop :=
  ∃ (v₁ v₂ : Val) (ts : Option (List ValType)),
    is = [v₁.toAdmin, v₂.toAdmin, constI32 0, .plain (.select ts)] ∧ js = [v₂.toAdmin]

/-- `NumericStep.intBinOp` at `add`. -/
def CoreAdd (is js : List Admin) : Prop :=
  ∃ (t : IntType) (x y : BitVec t.width),
    is = [.plain (.intConst t x), .plain (.intConst t y), .plain (.intBinOp t .add)] ∧
    js = [.plain (.intConst t (x + y))]

end Silmaril.Wasm.SpecTecLean
