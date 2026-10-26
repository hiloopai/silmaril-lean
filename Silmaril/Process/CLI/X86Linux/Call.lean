module

public import Silmaril.Process.CLI.X86Linux.Silent
public import Silmaril.X86.Ext.Store

/-! # Direct calls as silent process segments

The hypotheses below concern actual executable bytes and an actual stack
write. A direct `CALL rel32` consumes five bytes and pushes `RIP + 5`;
neither its callee's final `RET` nor its continuation is a process exit.
The completed-result adapter introduces no termination requirement and retains
the continuation's complete observable trace.
-/

@[expose] public section

namespace Silmaril.Process.CLI.X86Linux

open Silmaril.X86 (MState State Word Byte Reg)
open Silmaril.Machine.LittleEndian (encodeWords)

/-- The core after the real direct call, including its stack-pointer update. -/
def directCallCore (core : Core) (rel : BitVec 32) : Core :=
  { core.write .rsp (core.read .rsp - 8#64) with
    rip := core.rip + 5#64 + rel.signExtend 64 }

/-- The callee entry state; `memory` is the result of the return-address push. -/
def directCallState (initial : MState) (rel : BitVec 32) (memory : Memory) : MState :=
  ⟨directCallCore initial.core rel, memory⟩

theorem directCallCore_rip (core : Core) (rel : BitVec 32) :
    (directCallCore core rel).rip = core.rip + 5#64 + rel.signExtend 64 := rfl

theorem directCallCore_rsp (core : Core) (rel : BitVec 32) :
    (directCallCore core rel).read .rsp = core.read .rsp - 8#64 := by
  simp [directCallCore, State.read, State.write]

/-- CALL itself preserves every register other than RSP, including scratch
registers; no callee-saved claim about the subsequent callee is made here. -/
theorem directCallCore_read (core : Core) (rel : BitVec 32) (reg : Reg)
    (other : reg ≠ .rsp) :
    (directCallCore core rel).read reg = core.read reg := by
  simp [directCallCore, State.read, State.write, other]

theorem directCallCore_flags (core : Core) (rel : BitVec 32) :
    (directCallCore core rel).flags = core.flags := rfl

theorem directCallCore_fsBase (core : Core) (rel : BitVec 32) :
    (directCallCore core rel).fsBase = core.fsBase := rfl

/-- The canonical direct-call instruction has exactly five bytes. -/
theorem direct_call_length (rel : BitVec 32) :
    (X86.Ext.encode (.call rel)).length = 5 := by
  change (X86.Insn.encode (.call rel)).length = 5
  rfl

/-- Executing checked direct-call bytes performs the supplied successful push.
The designated Ext return address does not affect CALL's retirement. -/
theorem direct_call_step {initial : MState} {rel : BitVec 32} {memory : Memory}
    (exit : Word)
    (code : initial.memory.fetchBytes initial.core.rip.toNat 5 =
      some (X86.Ext.encode (.call rel)))
    (pushed : X86.pushWord initial.core initial.memory (initial.core.rip + 5#64) =
      some (initial.core.write .rsp (initial.core.read .rsp - 8#64), memory)) :
    X86.Ext.step exit initial = .retired (directCallState initial rel memory) := by
  have decoded : X86.Ext.decode (X86.Ext.encode (.call rel)) = some (.call rel, 5) := by
    simpa only [direct_call_length] using X86.Ext.decode_encode (.call rel)
  rw [X86.Ext.step_of_fetch code decoded]
  have executed : X86.Ext.exec (.call rel) initial.core initial.memory =
      .ok (directCallCore initial.core rel) memory := by
    simp only [X86.Ext.exec, X86.Ext.Instr.length, direct_call_length]
    change (match X86.pushWord initial.core initial.memory (initial.core.rip + 5#64) with
      | none => X86.Ext.Result.dataFault
      | some (core, memory) =>
        X86.Ext.Result.ok { core with rip := initial.core.rip + 5#64 + rel.signExtend 64 }
          memory) = _
    rw [pushed]
    rfl
  simp only [executed, reduceCtorEq, false_and, ite_false]
  rfl

/-- Ordinary write permission suffices for the actual call's stack write.
The resulting memory remains opaque, characterised by `Stored`. -/
theorem direct_call_entry {initial : MState} {rel : BitVec 32}
    (code : initial.memory.fetchBytes initial.core.rip.toNat 5 =
      some (X86.Ext.encode (.call rel)))
    (writable : initial.memory.Permitted .write (initial.core.read .rsp - 8#64).toNat 8) :
    ∃ memory,
      X86.pushWord initial.core initial.memory (initial.core.rip + 5#64) =
        some (initial.core.write .rsp (initial.core.read .rsp - 8#64), memory) ∧
      (∀ exit, X86.Ext.step exit initial = .retired (directCallState initial rel memory)) ∧
      X86.Ext.Stored initial.memory memory (initial.core.read .rsp - 8#64).toNat
        (encodeWords [initial.core.rip + 5#64]) := by
  obtain ⟨memory, pushed, stored⟩ := X86.Ext.pushWord_isSome
    (s := initial.core) (v := initial.core.rip + 5#64) writable
  exact ⟨memory, pushed, fun exit => direct_call_step exit code pushed, stored⟩

/-- The pushed return address can be read by the callee's RET. -/
theorem direct_call_return_slot {initial : MState} {memory : Memory}
    (pushed : X86.pushWord initial.core initial.memory (initial.core.rip + 5#64) =
      some (initial.core.write .rsp (initial.core.read .rsp - 8#64), memory))
    (readable : initial.memory.Permitted .read (initial.core.read .rsp - 8#64).toNat 8) :
    memory.readBytes (initial.core.read .rsp - 8#64).toNat 8 =
      some (encodeWords [initial.core.rip + 5#64]) :=
  X86.pushWord_readBytes pushed readable

/-- Every checked read disjoint from the pushed slot is preserved, including
executable code and disjoint driver buffers. -/
theorem direct_call_preserves_read {initial : MState} {memory : Memory}
    (pushed : X86.pushWord initial.core initial.memory (initial.core.rip + 5#64) =
      some (initial.core.write .rsp (initial.core.read .rsp - 8#64), memory))
    (access : Access) (start count : Nat)
    (apart : start + count ≤ (initial.core.read .rsp - 8#64).toNat ∨
      (initial.core.read .rsp - 8#64).toNat + 8 ≤ start) :
    memory.readWith access start count = initial.memory.readWith access start count :=
  X86.Memory.readWith_writesOnly (X86.pushWord_writesOnly pushed) access start count apart

/-- The caller-visible frame includes the callee's writes and CALL's actual
return-slot store. In particular the return slot cannot be omitted merely
because the callee itself leaves that slot untouched. -/
theorem direct_call_frame {initial final : MState} {memory : Memory} {inside : Nat → Prop}
    (pushed : X86.pushWord initial.core initial.memory (initial.core.rip + 5#64) =
      some (initial.core.write .rsp (initial.core.read .rsp - 8#64), memory))
    (calleeFrame : Memory.WritesWithin memory final.memory inside) :
    Memory.WritesWithin initial.memory final.memory (fun address => inside address ∨
      ((initial.core.read .rsp - 8#64).toNat ≤ address ∧
        address < (initial.core.read .rsp - 8#64).toNat + 8)) := by
  have callFrame := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp
    (X86.pushWord_writesOnly pushed)
  exact (callFrame.mono (fun _ h => Or.inr h)).trans
    (calleeFrame.mono (fun _ h => Or.inl h))

/-- An actual Ext return has reached its designated return address. This is
an endpoint fact about successful execution, without a termination claim. -/
theorem ext_returned_target {exit : Word} {initial final : MState}
    (returned : X86.Ext.step exit initial = .returned final) :
    final.core.rip = exit := by
  cases fetched : X86.Ext.fetch initial.memory initial.core.rip.toNat with
  | undecodable => simp [X86.Ext.step, fetched] at returned
  | truncated => simp [X86.Ext.step, fetched] at returned
  | decoded instr length =>
    cases executed : X86.Ext.exec instr initial.core initial.memory with
    | ok core memory =>
      simp only [X86.Ext.step, fetched, executed] at returned
      split at returned
      · rename_i target
        cases returned
        exact target.2
      · cases returned
    | dataFault => simp [X86.Ext.step, fetched, executed] at returned
    | divideError => simp [X86.Ext.step, fetched, executed] at returned
    | undefinedCondition c => simp [X86.Ext.step, fetched, executed] at returned
    | trap => simp [X86.Ext.step, fetched, executed] at returned

/-- The final RET of a completed Ext execution reaches the designated
continuation; the preceding retirements do not change this endpoint fact. -/
theorem ext_returns_target {exit : Word} {initial final : MState}
    (returned : X86.Ext.Returns exit initial final) : final.core.rip = exit := by
  obtain ⟨_, _, _, returned⟩ := returned
  exact ext_returned_target returned

/-- The actual CALL can also be prefixed inside Ext's completed-return
contract, for clients that have not yet selected a process environment. -/
theorem ext_returns_of_direct_call_returns
    {initial final : MState} {rel : BitVec 32} {memory : Memory}
    (code : initial.memory.fetchBytes initial.core.rip.toNat 5 =
      some (X86.Ext.encode (.call rel)))
    (pushed : X86.pushWord initial.core initial.memory (initial.core.rip + 5#64) =
      some (initial.core.write .rsp (initial.core.read .rsp - 8#64), memory))
    (returned : X86.Ext.Returns (initial.core.rip + 5#64)
      (directCallState initial rel memory) final) :
    X86.Ext.Returns (initial.core.rip + 5#64) initial final := by
  obtain ⟨n, mid, run, returned⟩ := returned
  refine ⟨n + 1, mid, ?_, returned⟩
  rw [Machine.Execution.run_succ, X86.Ext.stepOpt_eq_some_iff.mpr
    (direct_call_step (initial.core.rip + 5#64) code pushed)]
  exact run

/-- CALL followed by an actual completed callee is one silent process segment.
Only the callee's completed execution is required; unrelated runs may fail,
block, or diverge. The final RET is included in this segment. -/
theorem runs_of_direct_call_returns {E : Env} (lens : E.MemoryLens)
    {initial final : MState} {rel : BitVec 32} {memory : Memory} {s : E.State}
    (running : E.exited s = none) (initialMemory : E.memory s = initial.memory)
    (code : initial.memory.fetchBytes initial.core.rip.toNat 5 =
      some (X86.Ext.encode (.call rel)))
    (pushed : X86.pushWord initial.core initial.memory (initial.core.rip + 5#64) =
      some (initial.core.write .rsp (initial.core.read .rsp - 8#64), memory))
    (returned : X86.Ext.Returns (initial.core.rip + 5#64)
      (directCallState initial rel memory) final) :
    Proc.Runs isa E ⟨initial.core, s⟩ [] ⟨final.core, E.withMemory s final.memory⟩ := by
  have call : Proc.Step isa E ⟨initial.core, s⟩ []
      ⟨(directCallCore initial.core rel), E.withMemory s memory⟩ := by
    apply Proc.Step.retire running
    rw [initialMemory]
    exact (step_of_ext_retired (direct_call_step (initial.core.rip + 5#64) code pushed)).symm
  have callee := runs_of_ext_returns lens
    ((lens.exited_withMemory s memory).trans running)
    (lens.memory_withMemory s memory) returned
  rw [lens.withMemory_withMemory] at callee
  exact .cons call callee

/-- A real CALL and its completed callee leave precisely the continuation's
observable trace. In particular successful completion claims compose without
asserting that a later failing run has no earlier output. -/
theorem continue_of_direct_call_returns {E : Env} (lens : E.MemoryLens)
    {initial final : MState} {rel : BitVec 32} {memory : Memory} {s : E.State}
    {target : PState isa E} {events : List Syscall.Event}
    (running : E.exited s = none) (initialMemory : E.memory s = initial.memory)
    (code : initial.memory.fetchBytes initial.core.rip.toNat 5 =
      some (X86.Ext.encode (.call rel)))
    (pushed : X86.pushWord initial.core initial.memory (initial.core.rip + 5#64) =
      some (initial.core.write .rsp (initial.core.read .rsp - 8#64), memory))
    (returned : X86.Ext.Returns (initial.core.rip + 5#64)
      (directCallState initial rel memory) final)
    (continuation : Proc.Runs isa E ⟨final.core, E.withMemory s final.memory⟩ events target) :
    Proc.Runs isa E ⟨initial.core, s⟩ events target :=
  (runs_of_direct_call_returns lens running initialMemory code pushed returned).append continuation

end Silmaril.Process.CLI.X86Linux
