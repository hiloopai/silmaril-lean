module

public import Silmaril.Elf.Corpus.SqliteMutex.Defs
public import Silmaril.Machine.SqliteMutex.Thms

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteMutex

open Silmaril.Elf.Corpus.SqliteMutex
open Silmaril.X86 (State MState Word popWord wordOfBytes?_encodeWords)
open Silmaril.X86.Ext (Cond logicFlagsN)
open Silmaril.X86.Ext.Wire
open Silmaril.X86.Ext.Wire (Platform Outcome Decoded step)
open Silmaril.Machine SqliteMutex Behaviour Observable

set_option maxRecDepth 4096

private def testOp : Decoded := ⟨.canonical (.test .q (.reg .rdi) .rdi), [0x48, 0x85, 0xff]⟩
private def branchOp : Decoded := ⟨.canonical (.jcc8 .e 0x0b), [0x74, 0x0b]⟩
private def jumpMem : X86.Ext.Mem := ⟨.rip, none, 0x0ff6d5, fun _ => rfl⟩
private def jumpOp : Decoded :=
  ⟨.jmpRM (.mem jumpMem), [0xff, 0x25, 0xd5, 0xf6, 0x0f, 0x00]⟩
private def returnOp : Decoded := ⟨.canonical .ret, [0xc3]⟩

private theorem stepAt {platform : Platform} {caller : Word} {initial : MState}
    (loaded : region.LoadedIn initial.memory) (offset : Nat) (op : Decoded)
    (addr : initial.core.rip.toNat = region.base + offset)
    (within : offset + op.length ≤ region.bytes.length)
    (bytes : (region.bytes.drop offset).take op.length = op.bytes)
    (decoded : X86.Ext.Wire.decode op.bytes = some op) :
    step platform caller initial =
      match X86.Ext.Wire.exec platform op initial.core initial.memory with
      | .ok core memory =>
        if op.instr = .canonical .ret ∧ core.rip = caller then .returned ⟨core, memory⟩
        else .retired ⟨core, memory⟩
      | .dataFault => .dataFault op.instr
      | .divideError => .divideFault
      | .undefinedCondition cond => .undefinedCondition cond
      | .trap => .trapped :=
  X86.Ext.Wire.step_of_fetch (by rw [addr, loaded offset op.length within, bytes]) decoded

private def tested (initial : MState) : MState :=
  ⟨{ initial.core with flags := logicFlagsN (initial.core.read .rdi), rip := 0xff73 }, initial.memory⟩

private def atBranchTarget (initial : MState) (dest : Word) : MState :=
  ⟨{ (tested initial).core with rip := dest }, initial.memory⟩

private theorem step_test {platform : Platform} {initial : MState} {caller target : Word}
    (entry : Entry initial caller target) : step platform caller initial = .retired (tested initial) := by
  rw [stepAt entry.code 0 testOp (by rw [entry.rip]; rfl) (by decide) rfl (by decide +kernel)]
  simp [testOp, exec, execWithLength, X86.Ext.execWithLength, X86.Ext.exec, Decoded.length,
    tested, entry.rip, X86.Ext.Sz.read, X86.Ext.retire, X86.Ext.readRM]
  exact congrArg (fun word : Word => logicFlagsN word) BitVec.and_self

private theorem step_branch {platform : Platform} {initial : MState} {caller target : Word}
    (entry : Entry initial caller target) :
    step platform caller (tested initial) = .retired
      (atBranchTarget initial (if initial.core.read .rdi = 0#64 then 0xff80 else 0xff75)) := by
  rw [stepAt (initial := tested initial) entry.code 3 branchOp rfl (by decide) rfl (by decide +kernel)]
  have cond : Cond.e.eval (tested initial).core.flags = some (initial.core.read .rdi == 0#64) := rfl
  by_cases isNull : initial.core.read .rdi = 0#64
  · have flag : (initial.core.read .rdi == 0#64) = true := beq_iff_eq.mpr isNull
    simp only [ite_eq_left isNull, branchOp, exec, execWithLength, X86.Ext.execWithLength,
      X86.Ext.exec, cond, flag]
    rfl
  · have flag : (initial.core.read .rdi == 0#64) = false := beq_eq_false_iff_ne.mpr isNull
    simp only [ite_eq_right isNull, branchOp, exec, execWithLength, X86.Ext.execWithLength,
      X86.Ext.exec, cond, flag]
    rfl

private theorem step_jump {platform : Platform} {initial : MState} {caller target : Word}
    (entry : Entry initial caller target) (nonNull : initial.core.read .rdi ≠ 0#64) :
    step platform caller (atBranchTarget initial 0xff75) = .retired (atBranchTarget initial target) := by
  rw [stepAt (initial := atBranchTarget initial 0xff75) entry.code 5 jumpOp rfl
    (by decide) rfl (by decide +kernel)]
  have load := (entry.callback nonNull).2
  let state := (atBranchTarget initial 0xff75).core
  have address : jumpMem.addr state (state.rip + BitVec.ofNat 64 jumpOp.length) = slot := by
    change 0xff75#64 + 6#64 + 0#64 + (0x0ff6d5#32).signExtend 64 = slot
    decide +kernel
  have read : X86.Ext.readRM .q (.mem jumpMem) state initial.memory
      (state.rip + BitVec.ofNat 64 jumpOp.length) = some target := by
    simp only [X86.Ext.readRM, address, show X86.Ext.Sz.q.bytes = 8 from rfl, load, Option.map_some]
    exact congrArg some (BitVec.setWidth_eq target)
  have executed : exec platform jumpOp state initial.memory =
      .ok (atBranchTarget initial target).core initial.memory := by
    simp only [exec, execWithLength, jumpOp] at read ⊢
    rw [read]
    rfl
  rw [show (atBranchTarget initial 0xff75).memory = initial.memory from rfl, executed]
  rfl

private theorem step_ret {platform : Platform} {initial : MState} {caller target : Word}
    (entry : Entry initial caller target) : ∃ final,
    step platform caller (atBranchTarget initial 0xff80) = .returned final ∧
      final.core.rip = caller ∧ final.core.read .rsp = initial.core.read .rsp + 8 ∧
      final.memory = initial.memory := by
  rw [stepAt (initial := atBranchTarget initial 0xff80) entry.code 16 returnOp rfl
    (by decide) rfl (by decide +kernel)]
  let state := (atBranchTarget initial 0xff80).core
  have pop : popWord state initial.memory = some (caller, state.write .rsp (state.read .rsp + 8)) := by
    simp [popWord, show state.read .rsp = initial.core.read .rsp from rfl, entry.stack]
  refine ⟨⟨{ state.write .rsp (state.read .rsp + 8) with rip := caller }, initial.memory⟩, ?_, rfl, ?_, rfl⟩
  · have executed : exec platform returnOp state initial.memory =
        .ok { state.write .rsp (state.read .rsp + 8) with rip := caller } initial.memory := by
      change (match popWord state initial.memory with
        | none => X86.Ext.Result.dataFault
        | some (dest, final) => X86.Ext.Result.ok { final with rip := dest } initial.memory) = _
      rw [pop]
    rw [show (atBranchTarget initial 0xff80).memory = initial.memory from rfl, executed]
    simp [returnOp]
  · simp [State.read, State.write, state, atBranchTarget, tested]

theorem run_dispatch {platform : Platform} {initial : MState} {caller target : Word}
    (entry : Entry initial caller target) (nonNull : initial.core.read .rdi ≠ 0#64) :
    ∃ next, run platform caller 3 initial = .handlerEntry next ∧
      next.core.rip = target ∧ next.core.regs = initial.core.regs ∧ next.memory = initial.memory := by
  refine ⟨atBranchTarget initial target, ?_, rfl, rfl, rfl⟩
  simp only [run, step_test entry, entry.rip, step_branch entry, ite_eq_right nonNull,
    show (tested initial).core.rip = 0xff73 from rfl, step_jump entry nonNull]
  rfl

theorem run_return {platform : Platform} {initial : MState} {caller target : Word}
    (entry : Entry initial caller target) (isNull : initial.core.read .rdi = 0#64) :
    ∃ final, run platform caller 3 initial = .callerReturn final ∧
      final.core.rip = caller ∧ final.core.read .rsp = initial.core.read .rsp + 8 ∧
      final.memory = initial.memory := by
  obtain ⟨final, ret, rip, stack, memory⟩ := step_ret (platform := platform) entry
  refine ⟨final, ?_, rip, stack, memory⟩
  simp only [run, step_test entry, entry.rip, step_branch entry, ite_eq_left isNull,
    show (tested initial).core.rip = 0xff73 from rfl, ret]
  rfl

theorem sound {platform : Platform} {initial : MState} {caller target : Word} {env : Context}
    (entry : Entry initial caller target) (safe : Safe ((contract env).spec (initial.core.read .rdi))) :
    observe (run platform caller 3 initial) ∈ (contract env).spec (initial.core.read .rdi) := by
  rw [Observable.Contract.spec_of_pre ((SqliteMutex.safe_iff_admitted _ _).mp safe)]
  change observe (run platform caller 3 initial) = candidate (initial.core.read .rdi)
  by_cases isNull : initial.core.read .rdi = 0#64
  · obtain ⟨final, executed, _⟩ := run_return (platform := platform) entry isNull
    rw [executed]; simp [observe, candidate, isNull]
  · obtain ⟨next, executed, _, regs, _⟩ := run_dispatch (platform := platform) entry isNull
    have argument : next.core.read .rdi = initial.core.read .rdi := congrArg (· .rdi) regs
    rw [executed]; simp [observe, candidate, isNull, argument]

end Silmaril.Proofs.Elf.Corpus.SqliteMutex
