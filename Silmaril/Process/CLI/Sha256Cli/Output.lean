module

public import Silmaril.Process.CLI.Sha256Cli.Spec

/-! # The actual filter's full-write and successful-exit path

This is a machine-code suffix theorem. Its entry premises are deliberately
local: checked code is intact, the canonical answer is readable at `out`, and
stdout is open/writable. Reaching this cut point from the loader remains a
separate driver obligation. The theorem constructs an admitted Linux full write
and the real branch/exit instructions; it does not assert that Linux must
choose a full transfer or that other executions terminate.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.Output

set_option maxRecDepth 10000

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

abbrev PS := PState X86Linux.isa Env.linux

/-- A local fetch premise, recovered after disjoint writes using the existing
memory-frame helper. It asserts actual bytes/permissions, not just CFG edges. -/
def Intact (memory : Memory) : Prop :=
  ∀ entry ∈ Binary.transcript,
    memory.fetchBytes entry.address entry.bytes.length = some entry.bytes

theorem intact_of_frame {input : ProcInput} {core : Core} {initial memory : Memory}
    (loaded : Loaded image input core initial) {inside : Nat → Prop}
    (frame : Memory.WritesWithin initial memory inside)
    (outside : ∀ entry ∈ Binary.transcript, ∀ offset < entry.bytes.length,
      ¬ inside (entry.address + offset)) : Intact memory := by
  intro entry member
  rw [frame.fetchBytes (outside entry member)]
  exact Transcript.fetch image_faithful image_wf loaded member

theorem retire {entry : Entry} (member : entry ∈ Binary.transcript) {c next : Core}
    {s : Syscall.State} (intact : Intact s.memory) (running : s.exited = none)
    (pc : c.rip.toNat = entry.address)
    (effect : entry.denote c s.memory = .retired next s.memory) :
    Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : PS) [] ⟨next, s⟩ := by
  have actual := (step_of_entry (image_faithful entry member).1 pc
    (intact entry member)).trans effect
  simpa only [Env.linux] using
    (Proc.Step.retire (I := X86Linux.isa) (E := Env.linux) running actual.symm)

/-- Register values at the real write syscall, after the hex loop. -/
def writeCore (c : Core) : Core :=
  { (((((c.write .rax 1).write .rdi 1).write .rsi 0x4015c0).write .rdx 65).write .r8 0)
      with rip := 0x4002a9 }

def returnedCore (c : Core) : Core :=
  ((({ writeCore c with rip := 0x4002ab }).write .rax 65).write .rcx 0x4002ab).write .r11 0

def tested (c : Core) : Core :=
  { returnedCore c with rip := 0x4002ae, flags := X86.Ext.logicFlagsN (65 : Word) }

def jumped (c : Core) : Core := { tested c with rip := 0x400290 }

def advanced (c : Core) : Core :=
  { (jumped c).write .r8 65 with rip := 0x400293, flags := X86.Ext.addFlagsN (0 : Word) 65 }

def compared (c : Core) : Core :=
  { advanced c with rip := 0x400297, flags := X86.Ext.subFlagsN (65 : Word) 64 }

def done (c : Core) : Core := { compared c with rip := 0x4002ca }

def exiting (c : Core) : Core :=
  { (done c).write .rax 60 with rip := 0x4002cf }

def exitCore (c : Core) : Core :=
  { (exiting c).write .rdi 0 with rip := 0x4002d1, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }

set_option maxRecDepth 10000 in
theorem suffix (c : Core) (s : Syscall.State) (intact : Intact s.memory)
    (running : s.exited = none) :
    ∃ target : PS,
      Proc.Runs X86Linux.isa Env.linux ⟨returnedCore c, s⟩ [.exit 0] target ∧
        Proc.Stop X86Linux.isa Env.linux target (.exited 0) := by
  have a : Proc.Step X86Linux.isa Env.linux (⟨returnedCore c, s⟩ : PS) [] ⟨tested c, s⟩ := by
    apply retire (entry := Binary.i_4002ab) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_4002ab, X86.Ext.exec, X86.Ext.readRM,
        X86.Ext.Sz.read, X86.Ext.retire, returnedCore, writeCore, tested,
        X86.State.read, X86.State.write, Machine.RegisterFile.write]
  have b : Proc.Step X86Linux.isa Env.linux (⟨tested c, s⟩ : PS) [] ⟨jumped c, s⟩ := by
    apply retire (entry := Binary.i_4002ae) (by simp [Binary.transcript]) intact running
    · rfl
    · have taken : X86.Ext.Cond.eval (X86.Ext.logicFlagsN (65 : Word)) .g = some true := by decide
      simp [Entry.denote, X86Linux.execResult, Binary.i_4002ae, X86.Ext.exec,
        tested, jumped]
      erw [taken]
  have d : Proc.Step X86Linux.isa Env.linux (⟨jumped c, s⟩ : PS) [] ⟨advanced c, s⟩ := by
    apply retire (entry := Binary.i_400290) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_400290, X86.Ext.exec, X86.Ext.aluStep,
        X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write,
        X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN,
        returnedCore, writeCore, tested, jumped, advanced,
        X86.State.read, X86.State.write, Machine.RegisterFile.write]
  have e : Proc.Step X86Linux.isa Env.linux (⟨advanced c, s⟩ : PS) [] ⟨compared c, s⟩ := by
    apply retire (entry := Binary.i_400293) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_400293, X86.Ext.exec, X86.Ext.aluStep,
        X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, X86.Ext.AluOp.flagsN,
        advanced, compared, X86.State.read, X86.State.write, Machine.RegisterFile.write]
  have f : Proc.Step X86Linux.isa Env.linux (⟨compared c, s⟩ : PS) [] ⟨done c, s⟩ := by
    apply retire (entry := Binary.i_400297) (by simp [Binary.transcript]) intact running
    · rfl
    · have taken : X86.Ext.Cond.eval (X86.Ext.subFlagsN (65 : Word) 64) .a = some true := by decide
      simp [Entry.denote, X86Linux.execResult, Binary.i_400297, X86.Ext.exec,
        compared, done]
      erw [taken]
  have g : Proc.Step X86Linux.isa Env.linux (⟨done c, s⟩ : PS) [] ⟨exiting c, s⟩ := by
    apply retire (entry := Binary.i_4002ca) (by simp [Binary.transcript]) intact running
    · rfl
    · rfl
  have h : Proc.Step X86Linux.isa Env.linux (⟨exiting c, s⟩ : PS) [] ⟨exitCore c, s⟩ := by
    apply retire (entry := Binary.i_4002cf) (by simp [Binary.transcript]) intact running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_4002cf, X86.Ext.exec, X86.Ext.aluStep,
        X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write,
        X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN,
        exitCore, exiting, X86.State.read, X86.State.write, Machine.RegisterFile.write]
      dsimp +instances only [X86.Ext.Sz.bits]
      simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  let final : PS := ⟨{ exitCore c with rip := 0x4002d3 }, { s with exited := some 0 }⟩
  have last : Proc.Step X86Linux.isa Env.linux (⟨exitCore c, s⟩ : PS) [.exit 0] final := by
    apply Proc.Step.exit (q := .exit 0) running
    · exact (step_of_entry Binary.ok_4002d1.1 rfl (intact _ (by simp [Binary.transcript]))).symm
    · simp [X86Linux.isa, X86Linux.request, X86Linux.readNumber, X86Linux.writeNumber,
        X86Linux.exitNumber, exitCore, exiting, X86.State.read, X86.State.write,
        Machine.RegisterFile.write]
    · exact Syscall.Step.exit 0 running
  exact ⟨final, .cons a (.cons b (.cons d (.cons e (.cons f (.cons g (.cons h (.single last))))))),
    .exited rfl⟩

/-- The actual write syscall may accept the complete canonical answer, after
which the checked instructions above exit 0. This is an existence theorem for
one admitted transfer, not a promise that every environment chooses it. -/
theorem full_write (c : Core) (s : Syscall.State) (message : List Byte)
    (intact : Intact s.memory) (running : s.exited = none) {descriptor : Descriptor}
    (stdoutOpen : s.descriptors 1 = some descriptor) (writable : descriptor.writable = true)
    (answer : s.memory.readBytes 0x4015c0 65 = some (Sha256.expected message)) :
    ∃ target : PS,
      Proc.Runs X86Linux.isa Env.linux ⟨writeCore c, s⟩
        [.write 1 (Sha256.expected message), .exit 0] target ∧
      Proc.Stop X86Linux.isa Env.linux target (.exited 0) := by
  let after := s.setDescriptor 1 { descriptor with output := descriptor.output ++ Sha256.expected message }
  have take : (Sha256.expected message).take 65 = Sha256.expected message :=
    List.take_of_length_le (by simp)
  have effect : Syscall.Step s (.write 1 0x4015c0 65)
      (.write 1 (Sha256.expected message)) (.returned (.ok 65)) after := by
    simpa only [take] using (Syscall.Step.writeSome (written := 65) running stdoutOpen
      writable answer (by decide) (by decide))
  have call : Proc.Step X86Linux.isa Env.linux (⟨writeCore c, s⟩ : PS)
      [.write 1 (Sha256.expected message)] ⟨returnedCore c, after⟩ := by
    apply Proc.Step.call (q := .write 1 0x4015c0 65) (r := .ok 65) running
    · exact (step_of_entry Binary.ok_4002a9.1 rfl
        (intact _ (by simp [Binary.transcript]))).symm
    · simp [X86Linux.isa, X86Linux.request, X86Linux.readNumber, X86Linux.writeNumber,
        writeCore, X86.State.read, X86.State.write, Machine.RegisterFile.write]
    · exact effect
    · exact ⟨0, rfl⟩
  obtain ⟨target, rest, stop⟩ := suffix c after intact running
  exact ⟨target, .cons call rest, stop⟩

/-- Local completion refinement: the already-accounted input/EOF trace plus
the real write/exit suffix meets the canonical successful-answer contract. -/
theorem answer_from_cutpoint (c : Core) (s : Syscall.State) {input : ProcInput}
    {message : List Byte} {events : List Event} (accounted : Driver.OutputInv message events 0)
    (finite : input.stdin = .ofList message) (intact : Intact s.memory)
    (running : s.exited = none) {descriptor : Descriptor}
    (stdoutOpen : s.descriptors 1 = some descriptor) (writable : descriptor.writable = true)
    (answer : s.memory.readBytes 0x4015c0 65 = some (Sha256.expected message)) :
    ∃ target : PS,
      Proc.Runs X86Linux.isa Env.linux ⟨writeCore c, s⟩
        [.write 1 (Sha256.expected message), .exit 0] target ∧
      Proc.Stop X86Linux.isa Env.linux target (.exited 0) ∧
      Sha256.Success input (events ++ [.write 1 (Sha256.expected message), .exit 0]) := by
  obtain ⟨target, run, stop⟩ := full_write c s message intact running stdoutOpen writable answer
  refine ⟨target, run, stop, message, finite, ?_, ?_, ?_⟩
  · simpa [stdinRead, readOn_append, readOn] using accounted.input
  · exact List.mem_append_left _ accounted.eof
  · have silent : stdout events = [] := by simpa using accounted.output
    simp [stdout, writtenOn_append, writtenOn, show writtenOn 1 events = [] from silent]

/-- Empty-input instance at the real output cut point. Reaching this state
from `core₀` still requires the separate startup/padding/compression/hex proof. -/
theorem empty_answer_from_cutpoint (c : Core) (s : Syscall.State)
    (intact : Intact s.memory) (running : s.exited = none) {descriptor : Descriptor}
    (stdoutOpen : s.descriptors 1 = some descriptor) (writable : descriptor.writable = true)
    (answer : s.memory.readBytes 0x4015c0 65 = some (Sha256.expected [])) :
    ∃ target : PS,
      Proc.Runs X86Linux.isa Env.linux ⟨writeCore c, s⟩
        [.write 1 (Sha256.expected []), .exit 0] target ∧
      Proc.Stop X86Linux.isa Env.linux target (.exited 0) ∧
      Sha256.Success (inputOf []) [.read 0 [], .write 1 (Sha256.expected []), .exit 0] := by
  apply answer_from_cutpoint c s (events := [.read 0 []]) (accounted := ?_) (finite := rfl)
    (intact := intact) (running := running) stdoutOpen writable answer
  exact ⟨rfl, by simp [SawEof], by intro fd bytes member; simp at member, rfl, by decide⟩

end Silmaril.Process.CLI.Sha256Cli.Output
