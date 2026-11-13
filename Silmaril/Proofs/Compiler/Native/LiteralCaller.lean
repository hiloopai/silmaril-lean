module

public import Silmaril.Compiler.Native.Correctness.LiteralCaller.Defs
import Silmaril.Compiler.Native.Correctness.Execution.Thms
import Silmaril.Compiler.Native.Correctness.LiteralInteger.Thms
/-! The historical42 caller interface specializes the universal actual encoded
integer template. Public statements and the original Entry/Result stay intact. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralCaller
open Silmaril Silmaril.X86
open Silmaril.Compiler.Native.Correctness

/-- Completion of the actual83-byte emitted integer function for arbitrary
caller state and arbitrary memory satisfying byte/permission/separation inputs.
No successful run, returned state, or result is assumed. -/
theorem execute {base exit : Word} (initial : NativeState)
    (entry : Entry base exit initial.toBase) :
    ∃ before final, Relation.ReflTransGen (Retires exit) initial before ∧
      Silmaril.Compiler.Native.Correctness.step exit before = .returned final ∧
      Result exit initial final := by
  have templateEntry : LiteralInteger.Entry 42 base exit initial.toBase := {
    pc := entry.pc
    image := by simpa only [LiteralInteger.code42] using entry.image
    stackLower := entry.stackLower
    stackUpper := entry.stackUpper
    alignment := entry.alignment
    stackRead := entry.stackRead
    stackWrite := entry.stackWrite
    returnAddress := entry.returnAddress
    separate := by simpa only [LiteralInteger.code42] using entry.separate }
  have bounded : LiteralEmission.IsInt32 42 := by
    unfold LiteralEmission.IsInt32
    decide
  obtain ⟨before, final, reaches, returned, result⟩ :=
    LiteralInteger.execute 42 bounded initial templateEntry
  exact ⟨before, final, reaches, returned,
    result.pc, result.stack, result.value, result.registers, result.fsBase,
    result.vectors, result.masks, result.mxcsr, result.x87, result.flags, result.frame⟩

/-- The actual integer-state System V return discipline. DF and x87-mode
architecture are absent from this machine, so this is not a full Ffi.Return. -/
theorem Result.sysv_return {base exit : Word} {initial final : NativeState}
    (result : Result exit initial final) :
    Silmaril.C.Api.SysV.Return ⟨base, exit, initial.toBase⟩ final.toBase := by
  refine ⟨result.pc, result.stack, ?_⟩
  intro r member
  exact result.registers r
    (by cases r <;> simp_all [Silmaril.X86.sysv64])
    (by cases r <;> simp_all [Silmaril.X86.sysv64])

theorem Result.sysv_int32 {exit : Word} {initial final : NativeState}
    (result : Result exit initial final) :
    Silmaril.C.Api.SysV.ResultAt final.toBase (some .int32) (42 : BitVec 32) := by
  change (final.state.core.read .rax).setWidth 32 = 42
  rw [result.value]
  rfl

theorem Result.readBytes {exit : Word} {initial final : NativeState}
    (result : Result exit initial final) {address count : Nat}
    (disjoint : ∀ offset < count, ¬ writeFootprint (initial.state.core.read .rsp) (address + offset)) :
    final.memory.readBytes address count = initial.memory.readBytes address count :=
  result.frame.readBytes disjoint

/-- Finite actual completion also excludes every stopped and infinite execution,
and determines a unique complete native state for the admitted caller. -/
theorem total {base exit : Word} (initial : NativeState)
    (entry : Entry base exit initial.toBase) :
    ∃ final, Result exit initial final ∧
      ∀ observation, Realises exit initial observation ↔ observation = .returned final := by
  obtain ⟨before, final, reaches, returned, result⟩ := execute initial entry
  exact ⟨final, result, Execution.realises_completed_iff reaches returned⟩

theorem observes42 {base exit : Word} (initial : NativeState)
    (entry : Entry base exit initial.toBase) (observation : Observation)
    (realised : Realises exit initial observation) :
    observe observation = .exit 42 [] := by
  obtain ⟨final, result, all⟩ := total initial entry
  rw [(all observation).mp realised]
  simp only [observe, result.value]
  rfl

end Silmaril.Compiler.Native.Correctness.LiteralCaller
