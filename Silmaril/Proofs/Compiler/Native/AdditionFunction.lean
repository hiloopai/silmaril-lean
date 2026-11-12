module

public import Silmaril.Compiler.Native.Emit.AdditionFunction.Defs
public import Silmaril.Compiler.Native.Emit.AdditionBody.Thms
public import Silmaril.Compiler.Native.Emit.Epilogue.Thms
public import Silmaril.X86.Ext.Lemmas
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.AdditionFunction
open Silmaril Silmaril.X86
open Correctness
set_option maxRecDepth 8192
set_option maxHeartbeats 200000

theorem instruction_count (left right : Word) : (instructions left right).length = 36 := rfl

theorem code_length (left right : Word) : (code left right).length = 136 := by
  simp only [code, instructions, List.flatMap_append, List.length_append]
  have prefixBytes : (plan.activate 0 |>.flatMap Ext.encode).length = 19 := by decide +kernel
  have jump : ([Ext.Instr.jmp8 0].flatMap Ext.encode).length = 2 := rfl
  change _ + _ + (AdditionBody.code left right).length + Epilogue.code.length = _
  rw [prefixBytes, jump, AdditionBody.code_length, Epilogue.code_length]

private theorem permitted_slice (memory : Process.Memory) (access : Process.Access)
    (address length offset count : Nat) (permitted : memory.Permitted access address length)
    (within : offset + count ≤ length) (positive : 0 < count) : memory.Permitted access (address + offset) count := by
  obtain ⟨bound, limit, bytes⟩ := (Process.Memory.checkSpan_iff _ _ _ _).mp permitted
  apply (Process.Memory.checkSpan_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · intro index hi
    have indexBound : offset + index < length := by omega
    simpa only [Nat.add_assoc] using bytes (offset + index) indexBound

/-- The only control instruction between the activated frame and scalar body
is the real canonical short jump to the immediately following block. -/
theorem jump_next (before : X86.MState) :
    Prologue.Executes [.jmp8 0] before ⟨{before.core with rip := before.core.rip + BitVec.ofNat 64 2}, before.memory⟩ := by
  refine .cons _ _ _ _ _ ?_ (.nil _)
  have length : (Ext.Instr.jmp8 0).length = 2 := rfl
  have displacement : (0 : BitVec 8).signExtend 64 = 0 := rfl
  simpa only [length, displacement, add_zero] using
    (Ext.exec_jmp8 (s := before.core) (memory := before.memory) 0)

/-- Actual prologue stores preserve frame permissions and independently
create both saved-BP/reserved words, while deriving the scalar body's base. -/
theorem body_entry (caller prepared : X86.MState) (exit : Word)
    (entry : Entry caller exit) (ready : Prologue.Ready plan caller prepared) :
    AdditionBody.Entry (caller.core.read .rsp)
      ⟨{prepared.core with rip := prepared.core.rip + BitVec.ofNat 64 2}, prepared.memory⟩ := by
  refine ⟨by have := entry.lower; omega, ready.base, ?_, ?_⟩
  · exact (ready.frame.permitted_iff .read _ _).mpr
      (by simpa only [Nat.add_zero] using permitted_slice _ _ _ _ 0 72 entry.readable (by decide) (by decide))
  · exact (ready.frame.permitted_iff .write _ _).mpr
      (by simpa only [Nat.add_zero] using permitted_slice _ _ _ _ 0 72 entry.writable (by decide) (by decide))

/-- The complete real decoded function path is derived from the independent
call entry and permissions. Neither a body trace nor a physical result slot
is supplied, and the unused frame gap is preserved. -/
theorem execute (caller : X86.MState) (left right exit : Word) (entry : Entry caller exit) :
    ∃ final, Prologue.Executes (instructions left right) caller final ∧ Ready caller final left right exit := by
  have stackLower : 176 ≤ (caller.core.read .rsp).toNat := entry.lower
  have slice : (caller.core.read .rsp).toNat - 96 + 80 = (caller.core.read .rsp).toNat - 16 := by omega
  have activated : Prologue.Entry plan caller := by
    refine ⟨Prologue.addition_valid, entry.lower, ?_, ?_⟩
    · rw [← slice]
      exact permitted_slice _ _ _ _ 80 16 entry.readable (by decide) (by decide)
    · rw [← slice]
      exact permitted_slice _ _ _ _ 80 16 entry.writable (by decide) (by decide)
  obtain ⟨prepared, activatedTrace, preparedReady⟩ := Prologue.execute plan caller activated
  let bodyInput : X86.MState := ⟨{prepared.core with rip := prepared.core.rip + BitVec.ofNat 64 2}, prepared.memory⟩
  have bodyEntry : AdditionBody.Entry (caller.core.read .rsp) bodyInput := body_entry caller prepared exit entry preparedReady
  obtain ⟨bodyOutput, bodyTrace, bodyReady⟩ := AdditionBody.execute (caller.core.read .rsp) bodyInput left right bodyEntry
  have savedAddress : (caller.core.read .rsp - 8).toNat = (caller.core.read .rsp).toNat - 8 :=
    Ext.toNat_sub_ofNat (k := 8) (by omega) (by decide)
  have saved : bodyInput.memory.readBytes (caller.core.read .rsp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [caller.core.read .rbp]) := by
    rw [savedAddress]
    exact preparedReady.saved
  have returned : bodyInput.memory.readBytes (caller.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit]) := by
    have preserved := preparedReady.frame.readBytes (address := (caller.core.read .rsp).toNat) (length := 8)
      (by intro offset bound inside; unfold Prologue.footprint at inside; omega)
    exact preserved.trans entry.abi.returnAddress
  have epilogueEntry := AdditionBody.epilogue_entry caller bodyInput bodyOutput left right exit bodyEntry bodyReady saved returned
  obtain ⟨final, epilogueTrace, finalReady⟩ := Epilogue.execute caller bodyOutput _ exit epilogueEntry
  have frame : caller.memory.WritesWithin bodyOutput.memory (footprint (caller.core.read .rsp)) :=
    (preparedReady.frame.mono (fun _ h => Or.inl h)).trans (bodyReady.memory.mono (fun _ h => Or.inr h))
  have otherSaved : ∀ register ∈ sysv64.calleeSaved, register ≠ .rbp →
      bodyOutput.core.read register = caller.core.read register := by
    intro register member notBp
    have notSp : register ≠ .rsp := by cases register <;> simp_all [sysv64]
    have notAx : register ≠ .rax := by cases register <;> simp_all [sysv64]
    exact (AdditionBody.callee_saved bodyReady register member).trans (preparedReady.registers register notSp notBp notAx)
  refine ⟨final, ?_, finalReady.sysv_return caller.core.rip otherSaved, finalReady.result, ?_, ?_, ?_, ?_⟩
  · exact ((activatedTrace.append (jump_next prepared)).append bodyTrace).append epilogueTrace
  · rw [finalReady.memory]
    exact frame
  · exact finalReady.fsBase.trans (bodyReady.fsBase.trans preparedReady.fsBase)
  · rw [finalReady.memory]
    exact epilogueEntry.saved
  · rw [finalReady.memory]
    exact (AdditionBody.preserves_read bodyReady _ 8 (by omega)).trans preparedReady.reserved

/-- The completed function path supplies the bounded signed32 C result at
the existing limited INTEGER-state SysV boundary. -/
theorem Ready.int32 {caller final : X86.MState} {left right exit : Word}
    (ready : Ready caller final left right exit) :
    C.Api.SysV.ResultAt final (some .int32) ((AdditionLower.bodyValue left right).setWidth 32) := by
  change (final.core.read .rax).setWidth 32 = _
  rw [ready.result]

theorem Ready.addition_int32 {caller final : X86.MState} {exit : Word}
    (left right : Int) (bounded : AdditionSource.Bounds left right)
    (ready : Ready caller final (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) exit) :
    C.Api.SysV.ResultAt final (some .int32) ((BitVec.ofInt 64 (left + right)).setWidth 32) := by
  simpa only [AdditionLower.body_value left right bounded] using ready.int32

/-- Any byte slice disjoint from the exact two-piece store footprint is
preserved, including failed reads and the unused eight-byte frame gap. -/
theorem Ready.preserves_read {caller final : X86.MState} {left right exit : Word}
    (ready : Ready caller final left right exit) (address count : Nat)
    (disjoint : ∀ offset < count, ¬ footprint (caller.core.read .rsp) (address + offset)) :
    final.memory.readBytes address count = caller.memory.readBytes address count :=
  ready.frame.readBytes disjoint

theorem Ready.gap_preserved {caller final : X86.MState} {left right exit : Word}
    (ready : Ready caller final left right exit) (lower : 24 ≤ (caller.core.read .rsp).toNat) :
    final.memory.readBytes ((caller.core.read .rsp).toNat - 24) 8 =
      caller.memory.readBytes ((caller.core.read .rsp).toNat - 24) 8 := by
  apply ready.preserves_read
  intro offset bound inside
  unfold footprint Prologue.footprint Scalar.footprint at inside
  omega

/-- Actual source lowering, exact unoptimized Artifact and independent
function-entry execution compose without an assumed compiler success. -/
theorem compile_execute (left right : Int) (bounded : AdditionSource.Bounds left right)
    (tag : String) (caller : X86.MState) (exit : Word) (entry : Entry caller exit) :
    Lower.compile tag (AdditionSource.program left right) =
      .ok (AdditionLower.artifact (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) ∧
    ∃ final, Prologue.Executes (instructions (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) caller final ∧
      Ready caller final (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) exit ∧
      C.Api.SysV.ResultAt final (some .int32) ((BitVec.ofInt 64 (left + right)).setWidth 32) := by
  obtain ⟨final, executed, ready⟩ := execute caller (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) exit entry
  exact ⟨AdditionLower.compile left right bounded tag, final, executed, ready, ready.addition_int32 left right bounded⟩

private def additionInfo : Silmaril.Compiler.Native.FunctionInfo :=
  { name := "main", signature := ⟨.int 4 true, [], false, true⟩,
    tags := ∅, frameBytes := 0, frameAlign := 16 }

private def additionAbi : Silmaril.Machine.SystemV.Abi.CallPlan :=
  { arguments := [], result := .direct [⟨0, 4, .gp .rax⟩],
    stackSize := 0, stackAlign := 16, gpUsed := 0, vectorUsed := 0, variadicAL := none }

private theorem bind_ok {α β : Type} (value : α) (next : α → Except String β) :
    (Except.ok value >>= next) = next value := rfl

/-- The actual function emitter selects every rendered block from the actual
unoptimized Artifact, including the fallback retained after the return. -/
theorem rendered (left right : Word) (unit index : Nat) :
    Emit.function unit index (AdditionLower.artifact left right) (AdditionLower.function left right) =
      .ok (render unit index left right) := by
  have metadata : (AdditionLower.artifact left right).functions.find?
      (·.name == (AdditionLower.function left right).name) = some additionInfo := rfl
  have selected : Emit.functionPlan additionInfo = .ok additionAbi := rfl
  have framed : Emit.frame (AdditionLower.function left right) additionInfo additionAbi = ⟨96, 64, [], 0⟩ := by
    simp [Emit.frame, additionInfo, additionAbi, AdditionLower.function,
      Optimize.freshBase, Optimize.uses, Optimize.defs, AdditionLower.prologue, AdditionLower.body,
      AdditionLower.fallback, Silmaril.Compile.Mir.DeadCode.termUses, Silmaril.Compile.Mir.DeadCode.opUses,
      Silmaril.Compile.Mir.DeadCode.opDef, Emit.aggregate, Silmaril.Machine.SystemV.Abi.alignUp]
  simp only [Emit.function, metadata, selected]
  simp only [bind_ok, framed]
  have aligned : (AdditionLower.artifact left right).calls.foldlM
      (fun alignment call => do return max alignment (← Emit.callPlan call).stackAlign) 64 = Except.ok 64 := rfl
  have noParameters : Emit.entry (AdditionLower.function left right) additionInfo additionAbi ⟨96, 64, [], 0⟩ = .ok "" := rfl
  rw [aligned, bind_ok, noParameters, bind_ok]
  simp only [AdditionLower.function, AdditionLower.prologue, AdditionLower.body, AdditionLower.fallback,
    BitVec.ofNat_eq_ofNat, List.zipIdx_cons, zero_add, Nat.reduceAdd, List.zipIdx_nil, ↓reduceIte,
    String.append_assoc, Bool.false_eq_true, String.append_empty, Asm.operation, Nat.toString_eq_repr,
    bind_pure_comp, map_pure, Array.forIn_eq_foldlM, Emit.terminator, Emit.aggregate, additionInfo,
    String.empty_append, bind_map_left, List.forIn_cons, List.size_toArray, List.length_cons,
    List.length_nil, List.foldlM_toArray', List.foldlM_cons, List.foldlM_nil, bind_pure,
    ForInStep.value_yield, pure_bind, List.head?_cons, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod,
    List.forIn_nil, render, AdditionBody.render, Scalar.Operation.render, Scalar.Register.index,
    AdditionBody.operations, Fin.isValue, List.foldl_cons, Fin.coe_ofNat_eq_mod, Nat.one_mod,
    Nat.reduceMod, Nat.mod_succ, List.foldl_nil]
  simp only [Epilogue.render, ToString.toString, String.append_assoc]
  rfl

end Silmaril.Compiler.Native.Emit.AdditionFunction
