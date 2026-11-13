module

public import Silmaril.Compiler.Native.Correctness.AdditionLower.Defs
public import Silmaril.Compiler.Native.Correctness.LiteralEmission.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Cleanup.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Defs
/-! Universal reduction follows the LiteralEmission bounded symbolic evaluation
pattern. The original proof remains unchanged. Open prologue evaluation and the
standalone raw-Mir obstruction are separate actual execution statements. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionLower
open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native Silmaril.Compiler.Native.Optimize
open Silmaril.Compile.Contract
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 2000000

private def Bounded := { number : Int // LiteralEmission.IsInt32 number }
private def signedValue (number : Bounded) : Int := number.val
attribute [local cbv_opaque] signedValue
private def word (number : Bounded) : Lir.Word := BitVec.ofInt 64 (signedValue number)
attribute [local cbv_opaque] word
private theorem word_bits (number : Bounded) : BitVec.ofInt 64 (signedValue number) = word number := rfl
attribute [local cbv_eval] word_bits
private theorem value (number : Bounded) :
    Types.integerConstantValue (.iconstant (signedValue number) .decimal none) = .ok (signedValue number) := by
  change Types.integerConstantValue (.iconstant number.val .decimal none) = .ok number.val
  have lower : -(2147483648 : Int) ≤ number.val := number.property.1
  have upper : number.val < (2147483648 : Int) := number.property.2
  simp [Types.integerConstantValue, Types.constantIntegerLayout,
    Silmaril.Compile.C.constantType, lower, upper]
  rfl
attribute [local cbv_opaque] Types.integerConstantValue
attribute [local cbv_eval] value

private theorem compileUnit_bounded (left right : Bounded) (tag : String) :
    Lower.compileUnit tag (AdditionSource.program (signedValue left) (signedValue right)) =
      .ok (unit (word left) (word right)) := by
  cbv

private theorem compile_bounded (left right : Bounded) (tag : String) :
    Lower.compile tag (AdditionSource.program (signedValue left) (signedValue right)) =
      .ok (artifact (word left) (word right)) := by
  cbv

/-- Exact actual unit lowering, under independent mathematical source bounds. -/
theorem compileUnit (left right : Int) (bounds : AdditionSource.Bounds left right) (tag : String) :
    Lower.compileUnit tag (AdditionSource.program left right) =
      .ok (unit (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) :=
  compileUnit_bounded ⟨left, bounds.1⟩ ⟨right, bounds.2.1⟩ tag

/-- Exact actual Artifact lowering, including ABI/frame metadata. -/
theorem compile (left right : Int) (bounds : AdditionSource.Bounds left right) (tag : String) :
    Lower.compile tag (AdditionSource.program left right) =
      .ok (artifact (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) :=
  compile_bounded ⟨left, bounds.1⟩ ⟨right, bounds.2.1⟩ tag


theorem actual_freshBase (left right : Lir.Word) : freshBase (function left right) = 11 := by cbv

theorem actual_prologue (cfg : Config) : roundTripBlock cfg 11 prologue = versionedPrologue := by
  have checked : Validation.check 11 prologue versionedPrologue = true := by
    simp [Validation.check, prologue, versionedPrologue, Validation.defs,
      Validation.evalBlock, Validation.evalInstr, Validation.evalOp, Validation.evalTerm,
      Validation.readReg, Validation.readSlot, Validation.writeReg, Validation.intern,
      Validation.normalize]
    cbv
  have lowered : leave (enter 11 prologue) = versionedPrologue := by cbv
  have ssa : (enter 11 prologue).isSSA = true := by decide +kernel
  have selected : LambdaSSA.optimize? 11 prologue = none := by cbv
  simp [roundTripBlock, lowered, ssa, checked, selected]


theorem body_admitted (left right : Lir.Word) : Validation.Slots.Admitted (body left right).instrs.toList := by
  simp [body, Validation.Slots.Admitted, Validation.Slots.AdmittedInstr, Validation.Slots.AdmittedOp,
    Validation.Roots.Admitted, Mir.DeadCode.faults]


theorem body_raw (calls : OpenCalls) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    (left right : Lir.Word) :
    BlockExec calls (body left right) frame memory (.returned [bodyValue left right])
      (bodyFrame frame left right) memory := by
  refine ⟨.cons (.op rfl) (.cons (.op rfl) (.cons (.op rfl) (.cons (.op rfl)
    (.cons (.op rfl) (.cons (.op rfl) (.cons (.op rfl) (.cons (.op rfl)
      (.cons (.op rfl) .nil)))))))), .ret ?_⟩
  rfl

theorem body_value (left right : Int) (bounded : AdditionSource.Bounds left right) :
    bodyValue (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) = BitVec.ofInt 64 (left + right) := by
  unfold bodyValue normalize
  rw [LiteralEmission.word_normalized left bounded.1, LiteralEmission.word_normalized left bounded.1,
    LiteralEmission.word_normalized right bounded.2.1, LiteralEmission.word_normalized right bounded.2.1,
    ← BitVec.ofInt_add, LiteralEmission.word_normalized (left + right) bounded.2.2,
    LiteralEmission.word_normalized (left + right) bounded.2.2]

/-- Actual source-only body execution computes the independently bounded sum. -/
theorem body_executed (calls : OpenCalls) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    (left right : Int) (bounded : AdditionSource.Bounds left right) :
    BlockExec calls (body (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) frame memory
      (.returned [BitVec.ofInt 64 (left + right)])
      (bodyFrame frame (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) memory := by
  have actual := body_raw calls frame memory (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)
  rw [body_value left right bounded] at actual
  exact actual

theorem unresolved_frame (left right : Lir.Word) (placement : MirSem.Placement) :
    MirSem.symValue #[unit left right] placement "__ccomp_frame" = none := by
  cbv

theorem raw_start (left right : Lir.Word) (placement : MirSem.Placement) (size : Nat) :
    MirSem.start #[unit left right] placement size = some
      ⟨function left right, 0, 0, Lir.Frame.empty, [], MirSem.initMem #[unit left right] placement size⟩ := rfl

/-- The standalone actual Mir has no frame definition, so its first step is stuck.
Native emission interprets this reserved placeholder separately. -/
theorem raw_stuck (left right : Lir.Word) (placement : MirSem.Placement) (size : Nat) :
    Validation.Cleanup.ProgramBehaves #[unit left right] placement size .stuck := by
  refine ⟨_, raw_start left right placement size, _, .refl, ?_⟩
  simp [MirSem.step, function, prologue, unresolved_frame]

theorem prologue_executed (calls : OpenCalls) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    (address : Lir.Word) (resolved : calls.address "__ccomp_frame" 0 = some address) :
    BlockExec calls prologue frame memory (.jump 1) (frame.set 0 address) memory :=
  ⟨.cons (.addr resolved) .nil, .jump⟩

/-- Local real candidate evaluation assumes only the explicit open address
meaning; deriving it from a real machine stack/ABI is a separate obligation. -/
theorem versioned_prologue_executed (calls : OpenCalls) (cfg : Config)
    (frame : Lir.Frame Nat) (memory : Lir.Memory) (address : Lir.Word)
    (resolved : calls.address "__ccomp_frame" 0 = some address) :
    BlockExec calls (roundTripBlock cfg 11 prologue) frame memory (.jump 1)
      ((frame.set 11 address).set 0 address) memory := by
  rw [actual_prologue]
  exact ⟨.cons (.addr resolved) (.cons (.op rfl) .nil), .jump⟩

theorem prologue_agrees (source candidate : Lir.Frame Nat) (address : Lir.Word)
    (agrees : Validation.PureSoundness.FrameAgrees 11 source candidate) :
    Validation.PureSoundness.FrameAgrees 11 (source.set 0 address)
      ((candidate.set 11 address).set 0 address) := by
  refine ⟨agrees.slots, ?_⟩
  intro reg below
  by_cases zero : reg = 0
  · subst reg
    simp [Lir.Frame.get_set]
  · have notScratch : reg ≠ 11 := by omega
    simpa [Lir.Frame.get_set, zero, Ne.symm zero, notScratch, Ne.symm notScratch] using agrees.registers reg below

theorem raw_no_return (left right : Lir.Word) (placement : MirSem.Placement) (size : Nat)
    (words : List Lir.Word) (memory : Lir.Memory) :
    ¬ Validation.Cleanup.ProgramBehaves #[unit left right] placement size (.returned words memory) := by
  intro actual
  have impossible := Validation.Cleanup.programBehaves_unique (raw_stuck left right placement size) actual
  cases impossible


end Silmaril.Compiler.Native.Correctness.AdditionLower
