module

public import Silmaril.Process.CLI.Sha256Cli.EmptySupport
public import Silmaril.Process.CLI.Sha256Cli.OutputFrame
public import Silmaril.X86.Ext.Store

/-! # The compiled driver's four initial-state stores

This local execution follows the seven checked instructions at `0x40011a` to
`0x400154`. Its entry premises are the real cut point, the first loaded SHA
constant, intact code and a readable/writable 32-byte state buffer. It proves
the exact initial bytes and memory footprint without evaluating the hash map
or assuming that a whole driver execution already exists.

Reaching this cut point, padding, compression, hexadecimal conversion and the
stdout transfer remain separate execution obligations. This theorem concerns
the repository's decoded-byte x86/Linux model, not unmodeled hardware effects.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.InitStores

open Silmaril.Process (Memory)
open Silmaril.Process.CLI
open Silmaril.Process.CLI.X86Linux
open Silmaril.Process.Syscall
open Silmaril.X86 (Word)
open Silmaril.X86.Ext (Stored)

/-- H is a writable static buffer in the retained minimal filter. -/
def stateAddress : Nat := 0x401660

/-- Every register except RAX, and every flag, survives these instructions. -/
def finished (c : Core) : Core :=
  { c.write .rax 0x5be0cd191f83d9ab with rip := 0x400154 }

/-- The real read syscall entry: RAX selects read and RDI selects stdin;
the caller's RDX/RSI/RSP and all other registers are retained. -/
def readCore (c : Core) : Core :=
  { (c.write .rax 0).write .rdi 0 with
    rip := 0x400159, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }

@[simp] theorem readCore_preserves (c : Core) (register : X86.Reg)
    (notRax : register ≠ .rax) (notRdi : register ≠ .rdi) :
    (readCore c).read register = c.read register := by
  simp [readCore, X86.State.read, X86.State.write, Machine.RegisterFile.write,
    notRax, notRdi]

/-- Both permissions needed by the local theorem hold in the explicit launch
memory. This derives only mapping facts, without evaluating its byte map. -/
theorem initial_permissions :
    memory₀.Permitted .write stateAddress 32 ∧
      memory₀.Permitted .read stateAddress 32 := by
  constructor <;>
    apply X86.EntryState.permitted placements_wf
      (placement := ⟨Binary.seg1.region, some (List.replicate 0xc0 0)⟩)
      (by simp [placements]) rfl
  all_goals decide

/-- The local cut-point assumptions are simultaneously satisfiable on the
image's actual mapped memory. Reachability from entry is a separate claim. -/
theorem premises_inhabited :
    ∃ (c : Core) (s : Syscall.State), s.memory = memory₀ ∧
      s.exited = none ∧ Output.Intact s.memory ∧
      c.rip = 0x40011a ∧ c.read .rax = 0xbb67ae856a09e667 ∧
      s.memory.Permitted .write stateAddress 32 ∧
      s.memory.Permitted .read stateAddress 32 := by
  refine ⟨{ core₀.write .rax 0xbb67ae856a09e667 with rip := 0x40011a },
    ⟨memory₀, fun _ => none, none⟩, rfl, rfl, ?_, rfl, ?_,
    initial_permissions.1, initial_permissions.2⟩
  · intro entry member
    exact Transcript.fetch image_faithful image_wf (loaded []) member
  · simp [X86.State.read, X86.State.write]

private theorem store_rax {entry : Entry} {displacement : BitVec 32}
    (decoded : entry.Decodes)
    (instruction : entry.instr = .ext (.mov .q (.mem (X86.Ext.Mem.ofRip displacement)) .rax))
    {c : Core} {s : Syscall.State} {next address value : Word}
    (running : s.exited = none) (pc : c.rip.toNat = entry.address)
    (fetch : s.memory.fetchBytes entry.address entry.bytes.length = some entry.bytes)
    (nextEq : c.rip + BitVec.ofNat 64 entry.bytes.length = next)
    (addressEq : (X86.Ext.Mem.ofRip displacement).addr c next = address)
    (valueEq : c.read .rax = value)
    (writable : s.memory.Permitted .write address.toNat 8) :
    ∃ after : Memory,
      Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) []
        ⟨{ c with rip := next }, { s with memory := after }⟩ ∧
      Stored s.memory after address.toNat (X86.Ext.leBytes value 8) := by
  obtain ⟨after, written, frame⟩ := X86.Ext.storeN_isSome (v := value) writable
  have effect : entry.denote c s.memory =
      .retired { c with rip := next } after := by
    simp only [Entry.denote, instruction, X86.Ext.exec, nextEq,
      X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.bytes, X86.Ext.Sz.bits,
      BitVec.setWidth_eq, addressEq, valueEq, written, Option.map_some,
      X86.Ext.retire, X86Linux.execResult]
  exact ⟨after, .retire running ((step_of_entry decoded pc fetch).trans effect).symm, frame⟩

private theorem movabs_rax {entry : Entry} {value : Word}
    (member : entry ∈ Binary.transcript)
    (instruction : entry.instr = .ext (.movabs .rax value))
    {c : Core} {s : Syscall.State} {next : Word}
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip.toNat = entry.address)
    (nextEq : c.rip + BitVec.ofNat 64 entry.bytes.length = next) :
    Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) []
      ⟨{ c.write .rax value with rip := next }, s⟩ := by
  apply Output.retire member intact running pc
  simp only [Entry.denote, instruction, X86.Ext.exec, nextEq,
    X86.Ext.retire, X86Linux.execResult]

set_option maxRecDepth 10000 in
/-- A real silent execution initializes all eight SHA words. The 32-byte read
is assembled structurally from the four actual stores, and all other memory
is framed. Successful completion or driver totality is not a premise. -/
theorem initialize_state (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40011a) (rax : c.read .rax = 0xbb67ae856a09e667)
    (writable : s.memory.Permitted .write stateAddress 32)
    (readable : s.memory.Permitted .read stateAddress 32) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨finished c, { s with memory := after }⟩ ∧
      after.readBytes stateAddress 32 = some EmptySupport.initialStateBytes ∧
      Memory.WritesWithin s.memory after
        (fun a => stateAddress ≤ a ∧ a < stateAddress + 32) ∧
      Output.Intact after := by
  have w0 : s.memory.Permitted .write 0x401660 8 :=
    X86.Ext.Memory.Permitted.sub writable (by decide) (by decide) (by decide)
  obtain ⟨m1, a, stored1⟩ := store_rax Binary.ok_40011a.1 rfl running
    (by simp [pc, Binary.i_40011a]) (intact _ (by simp [Binary.transcript]))
    (next := 0x400121) (address := 0x401660) (value := 0xbb67ae856a09e667)
    (by rw [pc]; rfl)
    (by simp [X86.Ext.Mem.addr, X86.Ext.Mem.ofRip, X86.Ext.Base.value]) rax w0
  let c1 : Core := { c with rip := 0x400121 }
  have intact1 : Output.Intact m1 := Output.intact_of_store intact stored1 (by decide)
  let c2 : Core := { c1.write .rax 0xa54ff53a3c6ef372 with rip := 0x40012b }
  have b : Proc.Step X86Linux.isa Env.linux
      (⟨c1, { s with memory := m1 }⟩ : Output.PS) [] ⟨c2, { s with memory := m1 }⟩ :=
    movabs_rax (entry := Binary.i_400121) (by simp [Binary.transcript]) rfl
      running intact1 rfl rfl
  have w1 : m1.Permitted .write 0x401668 8 := stored1.permitted
    (X86.Ext.Memory.Permitted.sub writable (by decide) (by decide) (by decide))
  obtain ⟨m2, d, stored2⟩ := store_rax Binary.ok_40012b.1 rfl running rfl
    (intact1 _ (by simp [Binary.transcript]))
    (c := c2) (s := { s with memory := m1 })
    (next := 0x400132) (address := 0x401668) (value := 0xa54ff53a3c6ef372)
    rfl (by simp [X86.Ext.Mem.addr, X86.Ext.Mem.ofRip, X86.Ext.Base.value])
    (by simp [c2, X86.State.read, X86.State.write]) w1
  let c3 : Core := { c2 with rip := 0x400132 }
  have intact2 : Output.Intact m2 := Output.intact_of_store intact1 stored2 (by decide)
  let c4 : Core := { c3.write .rax 0x9b05688c510e527f with rip := 0x40013c }
  have e : Proc.Step X86Linux.isa Env.linux
      (⟨c3, { s with memory := m2 }⟩ : Output.PS) [] ⟨c4, { s with memory := m2 }⟩ :=
    movabs_rax (entry := Binary.i_400132) (by simp [Binary.transcript]) rfl
      running intact2 rfl rfl
  have w2 : m2.Permitted .write 0x401670 8 := stored2.permitted (stored1.permitted
    (X86.Ext.Memory.Permitted.sub writable (by decide) (by decide) (by decide)))
  obtain ⟨m3, f, stored3⟩ := store_rax Binary.ok_40013c.1 rfl running rfl
    (intact2 _ (by simp [Binary.transcript]))
    (c := c4) (s := { s with memory := m2 })
    (next := 0x400143) (address := 0x401670) (value := 0x9b05688c510e527f)
    rfl (by simp [X86.Ext.Mem.addr, X86.Ext.Mem.ofRip, X86.Ext.Base.value])
    (by simp [c4, X86.State.read, X86.State.write]) w2
  let c5 : Core := { c4 with rip := 0x400143 }
  have intact3 : Output.Intact m3 := Output.intact_of_store intact2 stored3 (by decide)
  let c6 : Core := { c5.write .rax 0x5be0cd191f83d9ab with rip := 0x40014d }
  have g : Proc.Step X86Linux.isa Env.linux
      (⟨c5, { s with memory := m3 }⟩ : Output.PS) [] ⟨c6, { s with memory := m3 }⟩ :=
    movabs_rax (entry := Binary.i_400143) (by simp [Binary.transcript]) rfl
      running intact3 rfl rfl
  have w3 : m3.Permitted .write 0x401678 8 := stored3.permitted
    (stored2.permitted (stored1.permitted
      (X86.Ext.Memory.Permitted.sub writable (by decide) (by decide) (by decide))))
  obtain ⟨after, h, stored4⟩ := store_rax Binary.ok_40014d.1 rfl running rfl
    (intact3 _ (by simp [Binary.transcript]))
    (c := c6) (s := { s with memory := m3 })
    (next := 0x400154) (address := 0x401678) (value := 0x5be0cd191f83d9ab)
    rfl (by simp [X86.Ext.Mem.addr, X86.Ext.Mem.ofRip, X86.Ext.Base.value])
    (by simp [c6, X86.State.read, X86.State.write]) w3
  have r0 : m1.readBytes 0x401660 8 =
      some (X86.Ext.leBytes (0xbb67ae856a09e667 : Word) 8) :=
    stored1.readWith_self (X86.Ext.Memory.Permitted.sub readable
      (by decide) (by decide) (by decide))
  have r1 : m2.readBytes 0x401668 8 =
      some (X86.Ext.leBytes (0xa54ff53a3c6ef372 : Word) 8) :=
    stored2.readWith_self (stored1.permitted (X86.Ext.Memory.Permitted.sub readable
      (by decide) (by decide) (by decide)))
  have r01 := Memory.readBytes_append
    ((stored2.readWith_disjoint .read 0x401660 8 (Or.inl (by decide))).trans r0) r1
  have r2 : m3.readBytes 0x401670 8 =
      some (X86.Ext.leBytes (0x9b05688c510e527f : Word) 8) :=
    stored3.readWith_self (stored2.permitted (stored1.permitted
      (X86.Ext.Memory.Permitted.sub readable (by decide) (by decide) (by decide))))
  have r012 := Memory.readBytes_append
    ((stored3.readWith_disjoint .read 0x401660 16 (Or.inl (by decide))).trans r01) r2
  have r3 : after.readBytes 0x401678 8 =
      some (X86.Ext.leBytes (0x5be0cd191f83d9ab : Word) 8) :=
    stored4.readWith_self (stored3.permitted (stored2.permitted (stored1.permitted
      (X86.Ext.Memory.Permitted.sub readable (by decide) (by decide) (by decide)))))
  have r0123 := Memory.readBytes_append
    ((stored4.readWith_disjoint .read 0x401660 24 (Or.inl (by decide))).trans r012) r3
  refine ⟨after, ?_, ?_, ?_, Output.intact_of_store intact3 stored4 (by decide)⟩
  · have execution := Silmaril.Machine.Trace.Runs.cons a
      (.cons b (.cons d (.cons e (.cons f (.cons g (.single h))))))
    simpa only [c1, c2, c3, c4, c5, c6, finished, X86.State.write,
      Machine.RegisterFile.write_shadow, List.nil_append] using execution
  · exact r0123
  · exact (stored1.writesWithin (by intro i hi; rw [X86.Ext.length_leBytes] at hi; dsimp [stateAddress]; omega)).trans
      ((stored2.writesWithin (by intro i hi; rw [X86.Ext.length_leBytes] at hi; dsimp [stateAddress]; omega)).trans
      ((stored3.writesWithin (by intro i hi; rw [X86.Ext.length_leBytes] at hi; dsimp [stateAddress]; omega)).trans
      (stored4.writesWithin (by intro i hi; rw [X86.Ext.length_leBytes] at hi; dsimp [stateAddress]; omega))))

set_option maxRecDepth 10000 in
/-- Two real register-only instructions reach the first read syscall without
touching memory or emitting an event. -/
theorem prepare_read (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400154) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨readCore c, s⟩ := by
  let cleared : Core := { c.write .rax 0 with
    rip := 0x400156, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }
  have first : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨cleared, s⟩ := by
    apply Output.retire (entry := Binary.i_400154) (by simp [Binary.transcript])
      intact running (by simp [pc, Binary.i_400154])
    simp [Entry.denote, X86Linux.execResult, Binary.i_400154, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN,
      cleared, pc, X86.State.write]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  have second : Proc.Step X86Linux.isa Env.linux
      (⟨cleared, s⟩ : Output.PS) [] ⟨readCore c, s⟩ := by
    apply Output.retire (entry := Binary.i_400156) (by simp [Binary.transcript])
      intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_400156, X86.Ext.exec,
      X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
      cleared, readCore, X86.State.read, X86.State.write]
  exact .cons first (.single second)

/-- The complete nine-instruction initialization slice reaches read with the
exact H bytes and a 32-byte footprint. The environment has not consumed input. -/
theorem initialize_read (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40011a) (rax : c.read .rax = 0xbb67ae856a09e667)
    (writable : s.memory.Permitted .write stateAddress 32)
    (readable : s.memory.Permitted .read stateAddress 32) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨readCore c, { s with memory := after }⟩ ∧
      after.readBytes stateAddress 32 = some EmptySupport.initialStateBytes ∧
      Memory.WritesWithin s.memory after
        (fun a => stateAddress ≤ a ∧ a < stateAddress + 32) ∧
      Output.Intact after := by
  obtain ⟨after, initialized, bytes, frame, code⟩ :=
    initialize_state c s running intact pc rax writable readable
  have ready := prepare_read (finished c) { s with memory := after } running code rfl
  refine ⟨after, ?_, bytes, frame, code⟩
  have combined := initialized.append ready
  simpa only [List.nil_append, readCore, finished, X86.State.write,
    Machine.RegisterFile.write_shadow] using combined

end Silmaril.Process.CLI.Sha256Cli.InitStores
