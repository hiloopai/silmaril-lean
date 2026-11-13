module

public import Silmaril.Machine.SystemV.Abi.Int32Identity.Defs
public import Silmaril.Machine.X86.Decompile.Features.Thms
public import Silmaril.Machine.X86.Decompile.Returns.Thms

/-! Actual checked MOV body plus actual fetched RET for a caller-parametric
integer SysV leaf. Classifier/call-plan equations stay distinct from the
integer-state call/return proof; no full FFI control-state contract is claimed. -/
@[expose] public section
namespace Silmaril.Machine.SystemV.Abi.Int32Identity
open Silmaril Silmaril.X86
open Silmaril.X86.Decompile.SemLift
open Silmaril.Machine.X86.Decompile.Features (lift)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem checked : check code 1 summary = true := by cbv

theorem decode_mov : Ext.decode ((code.drop 0).take 2) =
    some (.mov .d (.reg .rax) .rdi, 2) := by cbv

theorem decode_ret : Ext.decode ((code.drop 2).take 1) = some (.ret, 1) := by cbv

theorem classified (tags : Silmaril.Cerberus.Mem.Concrete.Tags) :
    objectOfCtype tags intType = .ok intObject := by cbv

theorem native_classified :
    Object.scalar (.integer .int .signed) = .ok intObject := by cbv

theorem planned : plan {} [intObject] (some intObject) 1 false = .ok callPlan := by cbv

/-- The same C type is classified for the sole argument and the result before
planning their actual RDI/RAX register locations. -/
theorem classified_plan (tags : Silmaril.Cerberus.Mem.Concrete.Tags) :
    (objectOfCtype tags intType >>= fun argument =>
      objectOfCtype tags intType >>= fun result =>
        plan {} [argument] (some result) 1 false) = .ok callPlan := by cbv

theorem Entry.argument {value : BitVec 32} {base exit : Word}
    {initial : Silmaril.X86.Features.MState} (entry : Entry value base exit initial) :
    (initial.state.core.read .rdi).setWidth 32 = value := by
  have argumentAt := entry.caller.arguments
  change (∃ word, Silmaril.C.Api.SysV.ArgumentWord initial.toBase 0 word ∧
    Silmaril.C.Api.SysV.Encodes .int32 value word) ∧ True at argumentAt
  obtain ⟨⟨word, wordAt, encoded⟩, _⟩ := argumentAt
  change initial.state.core.read .rdi = word at wordAt
  change word.setWidth 32 = value at encoded
  rw [wordAt]
  exact encoded

/-- The independent byte checker gives the ordinary body results for every
actual initial state and arbitrary base-first Features configuration. -/
theorem body {base exit : Word} (initial : Silmaril.X86.Features.MState)
    (featureSet : Silmaril.X86.Features.FeatureSet)
    (extensions : List Silmaril.X86.Features.Extension)
    (loaded : Ext.Loaded initial.memory base code) (pc : initial.state.core.rip = base) :
    ∃ final : X86.MState,
      Silmaril.X86.Features.run featureSet extensions exit 1 initial = some (lift initial.state final) ∧
      final.core.rip = base + 2 ∧
      final.core.read .rax = ((initial.state.core.read .rdi).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .rax → final.core.read r = initial.state.core.read r) ∧
      final.memory = initial.memory := by
  obtain ⟨final, actualRun, finalPc, outputs, stored, flags⟩ :=
    Silmaril.Machine.X86.Decompile.Features.check_sound checked featureSet extensions initial loaded pc
      (by simp [summary]) (by simp [summary]) (by simp [summary]) (by simp [summary, AssumeHolds])
  have rax := outputs (.rax, .ext .d (.reg .rdi)) (by simp [summary, registers])
  have preserved : ∀ r, r ≠ .rax → final.core.read r = initial.state.core.read r := by
    intro r notRax
    have encoded := outputs (r, .reg r) (by cases r <;> simp_all [summary, registers])
    exact encoded
  have sameMemory : final.memory = initial.memory := by
    change some initial.memory = some final.memory at stored
    exact (Option.some.inj stored).symm
  refine ⟨final, actualRun, finalPc, ?_, preserved, sameMemory⟩
  simpa only [Ex.eval, extW, Ext.Sz.bits] using rax

/-- The checked body composes with a real caller return word. The complete conclusion preserves actual FS,
flags and Features fields and writes no memory. -/
theorem execute {value : BitVec 32} {base exit : Word}
    (initial : Silmaril.X86.Features.MState)
    (featureSet : Silmaril.X86.Features.FeatureSet)
    (extensions : List Silmaril.X86.Features.Extension)
    (entry : Entry value base exit initial) :
    ∃ before final,
      Silmaril.X86.Features.run featureSet extensions exit 1 initial = some before ∧
      Silmaril.X86.Features.step featureSet extensions exit before = .returned final ∧
      Result value base exit initial final := by
  have pc : initial.state.core.rip = base := entry.caller.pc
  obtain ⟨checkedBase, checkedRun, checkedPc, checkedValue, checkedRegisters, checkedMemory⟩ :=
    body (exit := exit) initial featureSet extensions entry.loaded pc
  let moved : X86.MState :=
    ⟨{ initial.state.core.write .rax (((initial.state.core.read .rdi).setWidth 32).setWidth 64)
      with rip := base + 2 }, initial.memory⟩
  have integerStep : Ext.stepOpt exit initial.toBase = some moved :=
    Ext.stepOpt_mov_reg_mk entry.loaded (by simpa [Silmaril.X86.Features.MState.toBase] using pc) (by decide +kernel) decode_mov rfl
  have retired := Silmaril.Machine.X86.Decompile.Features.retire_of_loaded initial.state featureSet extensions
    entry.loaded (by simpa [Silmaril.X86.Features.MState.toBase] using pc) (by decide +kernel) decode_mov (by rfl) integerStep
  have liftInitial : lift initial.state initial.toBase = initial := by
    cases initial with
    | mk state memory => cases state; rfl
  rw [liftInitial] at retired
  have actualRun : Silmaril.X86.Features.run featureSet extensions exit 1 initial =
      some (lift initial.state moved) := by
    rw [Silmaril.X86.Features.run_succ, Silmaril.X86.Features.stepOpt_eq_some_iff.mpr retired]
    rfl
  have same : checkedBase = moved := by
    have lifted := Option.some.inj (checkedRun.symm.trans actualRun)
    exact congrArg Silmaril.X86.Features.MState.toBase lifted
  subst checkedBase
  let finished : X86.MState :=
    ⟨{ moved.core.write .rsp (moved.core.read .rsp + 8) with rip := exit }, moved.memory⟩
  have held : Ext.HoldsLE moved.memory (moved.core.read .rsp).toNat 8 exit := by
    simpa [moved, call, Ext.HoldsLE, Ext.leBytes_eight, Silmaril.X86.Features.MState.toBase]
      using entry.caller.returnAddress
  have returned := Silmaril.Machine.X86.Decompile.Returns.from_stack (machine := moved)
    initial.state featureSet extensions entry.loaded (by rfl) (by decide +kernel) decode_ret held
  have registersRestored : ∀ r, r ≠ .rax → r ≠ .rsp →
      finished.core.read r = initial.state.core.read r := by
    intro r notRax notRsp
    simpa [finished, State.read_write_other, notRsp] using checkedRegisters r notRax
  have valueAt : finished.core.read .rax = value.setWidth 64 := by
    simpa [finished, entry.argument] using checkedValue
  refine ⟨lift initial.state moved, lift initial.state finished, actualRun, returned, ?_⟩
  refine ⟨?_, ?_, valueAt, registersRestored, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · refine ⟨rfl, ?_, ?_⟩
    · simp [finished, moved, call, Silmaril.X86.Features.MState.toBase,
        Silmaril.X86.Features.State.setCore]
    · intro r member
      exact registersRestored r
        (by cases r <;> simp_all [sysv64]) (by cases r <;> simp_all [sysv64])
  · change (finished.core.read .rax).setWidth 32 = value
    rw [valueAt]
    simp
  · exact .refl _ _

/-- Any observed actual execution of this loaded leaf preserves the real
machine FS base. This is independent of the summary's unknown flag claim. -/
theorem executed_fsBase {value : BitVec 32} {base exit : Word}
    (initial : Silmaril.X86.Features.MState)
    (featureSet : Silmaril.X86.Features.FeatureSet)
    (extensions : List Silmaril.X86.Features.Extension)
    (entry : Entry value base exit initial)
    {before final : Silmaril.X86.Features.MState}
    (ran : Silmaril.X86.Features.run featureSet extensions exit 1 initial = some before)
    (returned : Silmaril.X86.Features.step featureSet extensions exit before = .returned final) :
    final.state.core.fsBase = initial.state.core.fsBase := by
  obtain ⟨provedBefore, provedFinal, provedRun, provedReturn, result⟩ :=
    execute initial featureSet extensions entry
  have sameBefore : provedBefore = before := Option.some.inj (provedRun.symm.trans ran)
  subst provedBefore
  have sameFinal : provedFinal = final := by
    exact Silmaril.X86.Features.Outcome.returned.inj (provedReturn.symm.trans returned)
  subst provedFinal
  exact result.fsBase

end Silmaril.Machine.SystemV.Abi.Int32Identity
