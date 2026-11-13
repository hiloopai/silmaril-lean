module

public import Silmaril.Machine.SystemV.Abi.Int32Add.Defs
public import Silmaril.Machine.X86.Decompile.Lea32.Thms
public import Silmaril.Machine.X86.Decompile.Returns.Thms

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi.Int32Add
open Silmaril Silmaril.X86
open Silmaril.X86.Decompile.SemLift
open Silmaril.Machine.X86.Decompile.Features (lift)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem checked : Silmaril.Machine.X86.Decompile.Lea32.check
    ((code.drop 0).take 3) .rax address 3 = true := by cbv

/-- Keep the general checker's actual LEA32 boundary visible. -/
theorem general_checker_rejects : check code 1 summary = false := by cbv

theorem decode_ret : Ext.decode ((code.drop 3).take 1) = some (.ret, 1) := by cbv

theorem classified_plan (tags : Silmaril.Cerberus.Mem.Concrete.Tags) :
    (objectOfCtype tags intType >>= fun first =>
      objectOfCtype tags intType >>= fun second =>
        objectOfCtype tags intType >>= fun result =>
          plan {} [first, second] (some result) 2 false) = .ok callPlan := by cbv

theorem Entry.arguments {a b : BitVec 32} {base exit : Word}
    {initial : Silmaril.X86.Features.MState} (entry : Entry a b base exit initial) :
    (initial.state.core.read .rdi).setWidth 32 = a ∧
      (initial.state.core.read .rsi).setWidth 32 = b := by
  have actualArguments := entry.caller.arguments
  change (∃ word, Silmaril.C.Api.SysV.ArgumentWord initial.toBase 0 word ∧
    Silmaril.C.Api.SysV.Encodes .int32 a word) ∧
    (∃ word, Silmaril.C.Api.SysV.ArgumentWord initial.toBase 1 word ∧
      Silmaril.C.Api.SysV.Encodes .int32 b word) ∧ True at actualArguments
  obtain ⟨⟨first, firstAt, firstEncoded⟩, ⟨second, secondAt, secondEncoded⟩, _⟩ := actualArguments
  change initial.state.core.read .rdi = first at firstAt
  change initial.state.core.read .rsi = second at secondAt
  change first.setWidth 32 = a at firstEncoded
  change second.setWidth 32 = b at secondEncoded
  exact ⟨firstAt ▸ firstEncoded, secondAt ▸ secondEncoded⟩

theorem expression_value (core : X86.State) (memory : Process.Memory) :
    expression.eval core memory = ((core.read .rdi + core.read .rsi).setWidth 32).setWidth 64 := by
  change ((core.read .rdi).setWidth 32 + (core.read .rsi).setWidth 32).setWidth 64 = _
  rw [BitVec.setWidth_add (i := 32) (core.read .rdi) (core.read .rsi) (by decide)]

/-- The checked LEA32 update realizes the same existing Ex register expression;
the general SemLift checker has not accepted this proposal. -/
theorem body_summary (machine : X86.MState) :
    ∀ output ∈ summary.outs,
      (Silmaril.Machine.X86.Decompile.Lea32.next machine .rax address 3).core.read output.1 =
        output.2.eval machine.core machine.memory := by
  intro output member
  obtain ⟨r, member, equal⟩ := List.mem_map.mp member
  subst output
  by_cases isRax : r = .rax
  · subst r
    simp [Silmaril.Machine.X86.Decompile.Lea32.next, address,
      Ext.Mem.addr, Ext.Mem.ofReg, Ext.Index.value, expression_value]
  · simp [isRax, Silmaril.Machine.X86.Decompile.Lea32.next, Ex.eval]

/-- Actual modulo32 byte semantics, independent of signed-C definedness. -/
theorem execute {a b : BitVec 32} {base exit : Word}
    (initial : Silmaril.X86.Features.MState)
    (featureSet : Silmaril.X86.Features.FeatureSet)
    (extensions : List Silmaril.X86.Features.Extension)
    (entry : Entry a b base exit initial) :
    ∃ before final,
      Silmaril.X86.Features.run featureSet extensions exit 1 initial = some before ∧
      Silmaril.X86.Features.step featureSet extensions exit before = .returned final ∧
      Result a b base exit initial final := by
  have pc : initial.state.core.rip = base := entry.caller.pc
  let moved := Silmaril.Machine.X86.Decompile.Lea32.next initial.toBase .rax address 3
  have liftInitial : lift initial.state initial.toBase = initial := by
    cases initial with
    | mk state memory => cases state; rfl
  have actualRun : Silmaril.X86.Features.run featureSet extensions exit 1 initial =
      some (lift initial.state moved) := by
    rw [← liftInitial]
    exact Silmaril.Machine.X86.Decompile.Lea32.run_sound initial.state featureSet extensions
      entry.loaded (by simpa [Silmaril.X86.Features.MState.toBase] using pc) (by decide +kernel) checked
  let finished : X86.MState :=
    ⟨{ moved.core.write .rsp (moved.core.read .rsp + 8) with rip := exit }, moved.memory⟩
  have held : Ext.HoldsLE moved.memory (moved.core.read .rsp).toNat 8 exit := by
    simpa [moved, Silmaril.Machine.X86.Decompile.Lea32.next, call, Ext.HoldsLE,
      Ext.leBytes_eight, Silmaril.X86.Features.MState.toBase] using entry.caller.returnAddress
  have returned : Silmaril.X86.Features.step featureSet extensions exit (lift initial.state moved) =
      .returned (lift initial.state finished) :=
    Silmaril.Machine.X86.Decompile.Returns.from_stack (machine := moved)
      initial.state featureSet extensions entry.loaded
      (by simp [moved, Silmaril.Machine.X86.Decompile.Lea32.next, Silmaril.X86.Features.MState.toBase, pc])
      (by decide +kernel) decode_ret held
  have registersRestored : ∀ r, r ≠ .rax → r ≠ .rsp →
      finished.core.read r = initial.state.core.read r := by
    intro r notRax notRsp
    simp [finished, moved, Silmaril.Machine.X86.Decompile.Lea32.next,
      Silmaril.X86.Features.MState.toBase, State.read_write_other, notRax, notRsp]
  have valueAt : finished.core.read .rax = (a + b).setWidth 64 := by
    have lowArguments := entry.arguments
    have lowSum : (initial.state.core.read .rdi + initial.state.core.read .rsi).setWidth 32 = a + b := by
      rw [BitVec.setWidth_add _ _ (by decide : 32 ≤ 64), lowArguments.1, lowArguments.2]
    simp [finished, moved, Silmaril.Machine.X86.Decompile.Lea32.next,
      address, Ext.Mem.ofReg, Ext.Mem.addr, Ext.Index.value, Silmaril.X86.Features.MState.toBase, lowSum]
  refine ⟨lift initial.state moved, lift initial.state finished, actualRun, returned, ?_⟩
  refine ⟨?_, ?_, valueAt, registersRestored, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · refine ⟨rfl, ?_, ?_⟩
    · simp [finished, moved, Silmaril.Machine.X86.Decompile.Lea32.next, call,
        Silmaril.X86.Features.MState.toBase, Silmaril.X86.Features.State.setCore]
    · intro r member
      exact registersRestored r
        (by cases r <;> simp_all [sysv64]) (by cases r <;> simp_all [sysv64])
  · change (finished.core.read .rax).setWidth 32 = a + b
    rw [valueAt]
    simp
  · exact .refl _ _

/-- Signed interpretation agrees with mathematical addition only when the
independent signed32 sum bounds hold. -/
theorem signed_sum {a b : BitVec 32} (defined : DefinedSum a b) :
    (a + b).toInt = a.toInt + b.toInt := by
  have encoded : BitVec.ofInt 32 (a.toInt + b.toInt) = a + b := by
    rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  rw [← encoded]
  exact BitVec.toInt_ofInt_eq_self (by decide) (by have := defined.1; omega) (by have := defined.2; omega)

/-- The imported Core signed-int primitive, not a mathematical surrogate,
corresponds to the returned bits under the independent defined-sum premise. -/
theorem core_result {a b : BitVec 32} {base exit : Word}
    {initial final : Silmaril.X86.Features.MState}
    (defined : DefinedSum a b) (result : Result a b base exit initial final) :
    CoreResult a b final := by
  unfold CoreResult
  rw [result.normalized]
  simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  rw [signed_sum defined]
  have lower : -2147483648 ≤ a.toInt + b.toInt := defined.1
  have upper : a.toInt + b.toInt ≤ 2147483647 := defined.2
  simp [Silmaril.Cerberus.Core.Dynamics.primitive, Silmaril.Cerberus.Core.Dynamics.integer,
    Silmaril.Cerberus.Core.Dynamics.integerOp,
    Silmaril.Cerberus.Mem.Concrete.registeredIntegerBounds,
    Silmaril.Cerberus.Mem.Concrete.registeredInteger,
    Silmaril.Cerberus.Mem.Concrete.integerBounds, Silmaril.Cerberus.Mem.Concrete.integerLayout,
    Silmaril.Cerberus.Mem.Concrete.baseWidth, lower, upper, Pure.pure, Except.pure]

/-- This combines actual completed execution with the bounded Core-primitive
correspondence; no signed-C claim is made without the independent sum bounds. -/
theorem execute_defined {a b : BitVec 32} {base exit : Word}
    (initial : Silmaril.X86.Features.MState)
    (featureSet : Silmaril.X86.Features.FeatureSet)
    (extensions : List Silmaril.X86.Features.Extension)
    (entry : Entry a b base exit initial) (defined : DefinedSum a b) :
    ∃ before final,
      Silmaril.X86.Features.run featureSet extensions exit 1 initial = some before ∧
      Silmaril.X86.Features.step featureSet extensions exit before = .returned final ∧
      Result a b base exit initial final ∧ CoreResult a b final := by
  obtain ⟨before, final, ran, returned, result⟩ := execute initial featureSet extensions entry
  exact ⟨before, final, ran, returned, result, core_result defined result⟩

end Silmaril.Machine.SystemV.Abi.Int32Add
