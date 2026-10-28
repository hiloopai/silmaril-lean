module

public import Silmaril.Process.CLI.Sha256Cli.InitStores
public import Silmaril.Process.CLI.X86Linux.LoadedExtension

/-! # Symbolic startup with arbitrary registers, mappings and stack address

The checked actual CALL/prologue is parameterized by its incoming core and
natural stack top. No incoming register except RIP/RSP is constrained; the
read arguments are overwritten. Existing symbolic H stores are reused.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.LoadedStartup

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

set_option maxRecDepth 10000

def mainCore (initial : Core) (top : Nat) : Core :=
  { initial.write .rsp (BitVec.ofNat 64 (top - 8)) with rip := 0x400100 }
def pushedRbp (initial : Core) (top : Nat) : Core :=
  { (mainCore initial top).write .rsp (BitVec.ofNat 64 (top - 16)) with rip := 0x400101 }
def countCore (initial : Core) (top : Nat) : Core :=
  { (pushedRbp initial top).write .rdx 64 with rip := 0x400106 }
def bufferCore (initial : Core) (top : Nat) : Core :=
  { (countCore initial top).write .rsi 0x401620 with rip := 0x40010b }
def valueCore (initial : Core) (top : Nat) : Core :=
  { (bufferCore initial top).write .rax 0xbb67ae856a09e667 with rip := 0x400115 }
def pushedRbx (initial : Core) (top : Nat) : Core :=
  { (valueCore initial top).write .rsp (BitVec.ofNat 64 (top - 24)) with rip := 0x400116 }
def initCore (initial : Core) (top : Nat) : Core :=
  { (pushedRbx initial top).write .rsp (BitVec.ofNat 64 (top - 32)) with rip := 0x40011a, flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (top - 24)) (8 : Word) }

def readCore (initial : Core) (top : Nat) : Core := InitStores.readCore (initCore initial top)

set_option maxRecDepth 10000 in
theorem prologue (initial : Core) (top : Nat) (s : Syscall.State)
    (room : 32 ≤ top) (limit : top < 2 ^ 64) (apart : 0x4005c0 ≤ top - 24) (intact : Output.Intact s.memory)
    (running : s.exited = none) (stack : s.memory.Permitted .write (top - 24) 24) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨(mainCore initial top), s⟩ []
        ⟨(initCore initial top), { s with memory := after }⟩ ∧
      Memory.WritesWithin s.memory after (fun a => top - 24 ≤ a ∧ a < top) ∧
      Output.Intact after := by
  have rsp1 : (mainCore initial top).read .rsp - (8 : Word) = BitVec.ofNat 64 (top - 16)  := by
    change BitVec.ofNat 64 (top - 8) - (8 : Word) = BitVec.ofNat 64 (top - 16)
    erw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (top - 8) 8 (by decide) (by omega)]
    congr 1
  have write1 : s.memory.Permitted .write ((mainCore initial top).read .rsp - (8 : Word)).toNat 8 := by
    rw [rsp1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : top - 16 < 2 ^ 64)]
    exact X86.Ext.Memory.Permitted.sub stack (by omega) (by omega) (by omega)
  obtain ⟨m1, push1, stored1⟩ := X86.Ext.pushWord_isSome
    (s := (mainCore initial top)) (v := (mainCore initial top).read .rbp) write1
  have address1 : ((mainCore initial top).read .rsp - (8 : Word)).toNat = top - 16 := by rw [rsp1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : top - 16 < 2 ^ 64)]
  erw [address1] at stored1
  have effect1 : Binary.i_400100.denote (mainCore initial top) s.memory = .retired (pushedRbp initial top) m1 := by
    change X86Linux.execResult (X86.Ext.retire ((mainCore initial top).rip + 1)
      (X86.pushWord (mainCore initial top) s.memory ((mainCore initial top).read .rbp))) = _
    rw [push1]
    erw [rsp1]
    rfl
  have a : Proc.Step X86Linux.isa Env.linux (⟨(mainCore initial top), s⟩ : Output.PS) []
      ⟨(pushedRbp initial top), { s with memory := m1 }⟩ :=
    .retire running ((step_of_entry Binary.ok_400100.1 rfl (intact _ (by simp [Binary.transcript]))).trans effect1).symm
  have intact1 : Output.Intact m1 := Output.intact_of_store intact stored1 (by omega)
  have b : Proc.Step X86Linux.isa Env.linux
      (⟨(pushedRbp initial top), { s with memory := m1 }⟩ : Output.PS) []
        ⟨(countCore initial top), { s with memory := m1 }⟩ := by
    apply Output.retire (s := { s with memory := m1 })
      (entry := Binary.i_400101) (by simp [Binary.transcript]) intact1 running
    · rfl
    · rfl
  have c : Proc.Step X86Linux.isa Env.linux
      (⟨(countCore initial top), { s with memory := m1 }⟩ : Output.PS) []
        ⟨(bufferCore initial top), { s with memory := m1 }⟩ := by
    apply Output.retire (s := { s with memory := m1 })
      (entry := Binary.i_400106) (by simp [Binary.transcript]) intact1 running
    · rfl
    · rfl
  have d : Proc.Step X86Linux.isa Env.linux
      (⟨(bufferCore initial top), { s with memory := m1 }⟩ : Output.PS) []
        ⟨(valueCore initial top), { s with memory := m1 }⟩ := by
    apply Output.retire (s := { s with memory := m1 })
      (entry := Binary.i_40010b) (by simp [Binary.transcript]) intact1 running
    · rfl
    · rfl
  have rsp2 : (valueCore initial top).read .rsp - (8 : Word) = BitVec.ofNat 64 (top - 24)  := by
    change BitVec.ofNat 64 (top - 16) - (8 : Word) = BitVec.ofNat 64 (top - 24)
    erw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (top - 16) 8 (by decide) (by omega)]
    congr 1
  have write2 : m1.Permitted .write ((valueCore initial top).read .rsp - (8 : Word)).toNat 8 := by
    rw [rsp2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : top - 24 < 2 ^ 64)]
    exact stored1.permitted (X86.Ext.Memory.Permitted.sub stack (by omega) (by omega) (by omega))
  obtain ⟨m2, push2, stored2⟩ := X86.Ext.pushWord_isSome
    (s := (valueCore initial top)) (v := (valueCore initial top).read .rbx) write2
  have address2 : ((valueCore initial top).read .rsp - (8 : Word)).toNat = top - 24 := by rw [rsp2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : top - 24 < 2 ^ 64)]
  erw [address2] at stored2
  have effect2 : Binary.i_400115.denote (valueCore initial top) m1 = .retired (pushedRbx initial top) m2 := by
    change X86Linux.execResult (X86.Ext.retire ((valueCore initial top).rip + 1)
      (X86.pushWord (valueCore initial top) m1 ((valueCore initial top).read .rbx))) = _
    rw [push2]
    erw [rsp2]
    rfl
  have e : Proc.Step X86Linux.isa Env.linux
      (⟨(valueCore initial top), { s with memory := m1 }⟩ : Output.PS) []
        ⟨(pushedRbx initial top), { s with memory := m2 }⟩ := by
    apply Proc.Step.retire running
    exact ((step_of_entry Binary.ok_400115.1 rfl
      (intact1 _ (by simp [Binary.transcript]))).trans effect2).symm
  have intact2 : Output.Intact m2 := Output.intact_of_store intact1 stored2 (by omega)
  have f : Proc.Step X86Linux.isa Env.linux
      (⟨(pushedRbx initial top), { s with memory := m2 }⟩ : Output.PS) []
        ⟨(initCore initial top), { s with memory := m2 }⟩ := by
    apply Output.retire (s := { s with memory := m2 })
      (entry := Binary.i_400116) (by simp [Binary.transcript]) intact2 running
    · rfl
    · simp [Entry.denote, X86Linux.execResult, Binary.i_400116, X86.Ext.exec, X86.Ext.aluStep,
        X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read, X86.Ext.Sz.write, X86.Ext.retire,
        X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN, pushedRbx, initCore, valueCore, bufferCore, countCore, pushedRbp, mainCore,
        X86.State.read, X86.State.write, Machine.RegisterFile.write]
      erw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (top - 24) 8 (by decide) (by omega)]
      congr 1
  have frame1 := stored1.writesWithin (inside := fun a => top - 24 ≤ a ∧ a < top) (by
    intro offset bound
    change offset < 8 at bound
    omega)
  have frame2 := stored2.writesWithin (inside := fun a => top - 24 ≤ a ∧ a < top) (by
    intro offset bound
    change offset < 8 at bound
    omega)
  exact ⟨m2, .cons a (.cons b (.cons c (.cons d (.cons e (.single f))))),
    frame1.trans frame2, intact2⟩



/-- The real entry CALL saves its return address without assuming zeroed
registers or a concrete stack address. -/
theorem call_main (initial : Core) (top : Nat) (s : Syscall.State)
    (room : 8 ≤ top) (limit : top < 2 ^ 64)
    (pc : initial.rip = 0x4000f0)
    (rsp : initial.read .rsp = BitVec.ofNat 64 top)
    (intact : Output.Intact s.memory) (running : s.exited = none)
    (stack : s.memory.Permitted .write (top - 8) 8) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨initial, s⟩ []
        ⟨mainCore initial top, { s with memory := after }⟩ ∧
      X86.Ext.Stored s.memory after (top - 8)
        (Machine.LittleEndian.encodeWords [(0x4000f5 : Word)]) := by
  have rspSub : initial.read .rsp - (8 : Word) = BitVec.ofNat 64 (top - 8) := by
    rw [rsp]
    erw [BitVec.ofNat_sub_ofNat_of_le (w := 64) top 8 (by decide) room]
  have address : (initial.read .rsp - (8 : Word)).toNat = top - 8 := by
    rw [rspSub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : top - 8 < 2 ^ 64)]
  have permission : s.memory.Permitted .write (initial.read .rsp - (8 : Word)).toNat 8 := by
    rw [address]
    exact stack
  obtain ⟨after, pushed, stored⟩ := X86.Ext.pushWord_isSome
    (s := initial) (v := (0x4000f5 : Word)) permission
  have effect : Binary.i_4000f0.denote initial s.memory =
      .retired (mainCore initial top) after := by
    change X86Linux.execResult
      (match X86.pushWord initial s.memory (initial.rip + 5) with
       | none => .dataFault
       | some (t, m) => .ok { t with rip := initial.rip + 5 + (0xb : BitVec 32).signExtend 64 } m) = _
    rw [pc]
    change X86Linux.execResult
      (match X86.pushWord initial s.memory (0x4000f5 : Word) with
       | none => .dataFault
       | some (t, m) => .ok { t with rip := 0x400100 } m) = _
    rw [pushed]
    simp only [X86Linux.execResult, mainCore]
    erw [rspSub]
  have transition : Proc.Step X86Linux.isa Env.linux (⟨initial, s⟩ : Output.PS) []
      ⟨mainCore initial top, { s with memory := after }⟩ := by
    apply Proc.Step.retire running
    exact ((step_of_entry Binary.ok_4000f0.1 (by rw [pc]; rfl)
      (intact _ (by simp [Binary.transcript]))).trans effect).symm
  refine ⟨after, .single transition, ?_⟩
  erw [address] at stored
  exact stored

/-- This exact footprint records only bytes written by startup; the bottom
8-byte allocation changes RSP but is not itself a memory write. -/
def Footprint (top address : Nat) : Prop :=
  (top - 24 ≤ address ∧ address < top) ∨
    (InitStores.stateAddress ≤ address ∧ address < InitStores.stateAddress + 32)

/-- A parameterized startup bridge using only local permissions and geometry.
It proves actual silent execution and initialized H, not completed behavior. -/
theorem launch_read (initial : Core) (top : Nat) (s : Syscall.State)
    (room : 32 ≤ top) (limit : top < 2 ^ 64)
    (pc : initial.rip = 0x4000f0)
    (rsp : initial.read .rsp = BitVec.ofNat 64 top)
    (apart : 0x4005c0 ≤ top - 24)
    (intact : Output.Intact s.memory) (running : s.exited = none)
    (stack : s.memory.Permitted .write (top - 24) 24)
    (writeH : s.memory.Permitted .write InitStores.stateAddress 32)
    (readH : s.memory.Permitted .read InitStores.stateAddress 32) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨initial, s⟩ []
        ⟨readCore initial top, { s with memory := after }⟩ ∧
      after.readBytes InitStores.stateAddress 32 = some EmptySupport.initialStateBytes ∧
      Memory.WritesWithin s.memory after (Footprint top) ∧ Output.Intact after := by
  obtain ⟨first, callRun, stored⟩ := call_main initial top s (by omega) limit pc rsp
    intact running (X86.Ext.Memory.Permitted.sub stack (by omega) (by omega) (by omega))
  have intactFirst : Output.Intact first := Output.intact_of_store intact stored (by omega)
  have frameFirst := stored.writesWithin
    (inside := fun a => top - 24 ≤ a ∧ a < top) (by
      intro offset bound
      change offset < 8 at bound
      omega)
  obtain ⟨middle, prefixRun, prefixFrame, prefixCode⟩ := prologue initial top
    { s with memory := first } room limit apart intactFirst running (stored.permitted stack)
  have frame := frameFirst.trans prefixFrame
  obtain ⟨after, initRun, initialized, initFrame, code⟩ :=
    InitStores.initialize_read (initCore initial top) { s with memory := middle }
      running prefixCode rfl (by
        simp [initCore, pushedRbx, valueCore, bufferCore, countCore, pushedRbp, mainCore,
          X86.State.read, X86.State.write, Machine.RegisterFile.write])
      ((frame.permitted_iff .write InitStores.stateAddress 32).mpr writeH)
      ((frame.permitted_iff .read InitStores.stateAddress 32).mpr readH)
  refine ⟨after, ?_, initialized, ?_, code⟩
  · simpa only [List.nil_append, readCore] using (callRun.append prefixRun).append initRun
  · exact (frame.mono (fun _ h => Or.inl h)).trans
      (initFrame.mono (fun _ h => Or.inr h))

/-- Mapped static H supplies both startup permissions; no initial H bytes
or zeroed backing are needed because the four real stores initialize it. -/
theorem loaded_state_permissions {input : ProcInput} {initial : Core} {memory : Memory}
    (loaded : Loaded image input initial memory) :
    memory.Permitted .write InitStores.stateAddress 32 ∧
      memory.Permitted .read InitStores.stateAddress 32 := by
  have member : Binary.seg1 ∈ image.segments := by simp [image, Binary.image]
  have region := (loaded.1 Binary.seg1 member).1
  constructor <;>
    apply Memory.permitted_of_region memory _ InitStores.stateAddress 32 Binary.seg1.region region
  all_goals decide

/-- Arbitrary Loaded startup needs only an explicit code/stack separation
clause beyond the current loader; the stack's readable backing is not yet used.
This does not claim the later fixed-frame compressor theorem is parameterized. -/
theorem of_loaded (input : ProcInput) (initial : Core) (s : Syscall.State)
    (loaded : Loaded image input initial s.memory)
    (apart : 0x4005c0 ≤ (initial.read .rsp).toNat - 24)
    (running : s.exited = none) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨initial, s⟩ []
        ⟨readCore initial (initial.read .rsp).toNat, { s with memory := after }⟩ ∧
      after.readBytes InitStores.stateAddress 32 = some EmptySupport.initialStateBytes ∧
      Memory.WritesWithin s.memory after (Footprint (initial.read .rsp).toNat) ∧
      Output.Intact after := by
  have room := loaded.2.2.2.1
  have stack := loaded.2.2.2.2.1
  have permissions := loaded_state_permissions loaded
  apply launch_read initial (initial.read .rsp).toNat s
    (by dsimp [stackRoom] at room; omega) (BitVec.isLt _)
    (BitVec.eq_of_toNat_eq (by simpa [image, Binary.image] using loaded.2.1))
    (by simp) apart (fun entry member =>
      Transcript.fetch image_faithful image_wf loaded member) running
    (X86.Ext.Memory.Permitted.sub stack (by dsimp [stackRoom] at room ⊢; omega)
      (by dsimp [stackRoom] at room ⊢; omega) (by dsimp [stackRoom] at room ⊢; omega))
    permissions.1 permissions.2


/-- The endpoint has a genuine positive-capacity stdin request regardless of
incoming registers, flags or stack address. -/
theorem read_arguments (initial : Core) (top : Nat) :
    (readCore initial top).read .rax = 0 ∧
    (readCore initial top).read .rdi = 0 ∧
    (readCore initial top).read .rsi = 0x401620 ∧
    (readCore initial top).read .rdx = 64 ∧
    (readCore initial top).read .rsp = BitVec.ofNat 64 (top - 32) := by
  simp [readCore, InitStores.readCore, initCore, pushedRbx, valueCore, bufferCore,
    countCore, pushedRbp, mainCore, X86.State.read, X86.State.write, Machine.RegisterFile.write]

theorem read_request (initial : Core) (top : Nat) :
    X86Linux.request (readCore initial top) = some (.read 0 0x401620 64) := by
  obtain ⟨rax, rdi, rsi, rdx, _⟩ := read_arguments initial top
  simp [X86Linux.request, rax, rdi, rsi, rdx, readNumber]

end Silmaril.Process.CLI.Sha256Cli.LoadedStartup


