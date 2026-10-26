module

public import Silmaril.Process.LPS.Machines.X86Wire

/-! # Fetched instruction/data-access and lazy-backing controls

The fixtures fetch actual executable bytes and run the direct LPS machine
adapters. Data accesses are distinguished from merely computed addresses.
Lazy-page checks are explicit computations of the direct port's materializer;
they are not an ELF-loading or whole-program Linux execution theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096

namespace Silmaril.Process.LPS.Machines.X86WireControls

open Silmaril.X86
open Silmaril.Process (Memory)

inductive Sample where
  | load | lea | cmovFalse | pushRsp
  deriving DecidableEq

def operand : Ext.Mem := Ext.Mem.ofReg .rdi none 0

def Sample.instruction : Sample → Ext.Instr
  | .load => .load .q .rax operand
  | .lea => .lea .q .rax operand
  | .cmovFalse => .cmov .q .e .rax (.mem operand)
  | .pushRsp => .push .rsp

def Sample.bytes (sample : Sample) : List Byte := Ext.encode sample.instruction

theorem sample_bytes :
    Sample.bytes .load = [0x48, 0x8b, 0x07] ∧
    Sample.bytes .lea = [0x48, 0x8d, 0x07] ∧
    Sample.bytes .cmovFalse = [0x48, 0x0f, 0x44, 0x07] ∧
    Sample.bytes .pushRsp = [0x54] := by decide +kernel

def core (address : Word := 0x4000) : Silmaril.X86.State where
  regs register := match register with
    | .rdi => address
    | .rsp => 0x4008
    | .rbp => 0x4000
    | .rax => 0x77
    | _ => 0
  rip := 0x1000
  flags := ⟨some false, some false, some false, some false, some false, some false⟩

def data : List Byte := List.replicate 8 0

def memory (sample : Sample) : Memory :=
  ⟨[⟨0x1000, sample.bytes.length, ⟨true, false, true⟩⟩,
     ⟨0x4000, 8, ⟨true, true, false⟩⟩],
    Memory.install (Memory.install {} 0x4000 data) 0x1000 sample.bytes⟩

def state (sample : Sample) (address : Word := 0x4000) : X86State :=
  ⟨⟨core address, memory sample⟩, none⟩

theorem fetched (sample : Sample) :
    (memory sample).fetchBytes 0x1000 sample.bytes.length = some sample.bytes := by
  apply Memory.readWith_eq (memory sample) .execute 0x1000 sample.bytes
    (by cases sample <;> decide +kernel)
  intro index bound
  exact Memory.install_get _ _ _ index bound

theorem data_read (sample : Sample) : (memory sample).readBytes 0x4000 8 = some data := by
  apply Memory.readWith_eq (memory sample) .read 0x4000 data
    (by cases sample <;> decide +kernel)
  intro index bound
  change (Memory.install (Memory.install {} 0x4000 data) 0x1000 sample.bytes).get? (0x4000 + index) = _
  have size : sample.bytes.length ≤ 4 := by cases sample <;> decide +kernel
  rw [Memory.install_outside _ _ _ _ (Or.inr (by omega))]
  exact Memory.install_get _ _ _ index bound

theorem not_syscall (sample : Sample) (address : Word) :
    (state sample address).m.memory.fetchBytes (state sample address).m.core.rip.toNat 2 ≠
      some [0x0f, 0x05] := by
  change (memory sample).fetchBytes 0x1000 2 ≠ some [0x0f, 0x05]
  intro syscall
  have syscallFirst := Memory.readWith_slice syscall 0 1 (by decide) (by decide)
  have positive : 1 ≤ sample.bytes.length := by cases sample <;> decide +kernel
  have ourFirst := Memory.readWith_slice (fetched sample) 0 1 (by decide) positive
  rw [ourFirst] at syscallFirst
  cases sample <;> contradiction

theorem native_step (sample : Sample) (address : Word) :
    x86NativeStep (state sample address) =
      x86ExecResult ((0x1000, sample.bytes.length) :: X86Accesses.canonical (core address) sample.bytes.length sample.instruction)
        (Ext.exec sample.instruction (core address) (memory sample) sample.bytes.length) := by
  exact x86NativeStep_of_fetch (state sample address) (not_syscall sample address)
    (fetched sample) (Ext.decode_encode sample.instruction)

theorem common (sample : Sample) (address : Word) : X86Wire.CommonAt (state sample address) := by
  exact X86Wire.canonical_common _ (Ext.fetch_eq_decoded_iff.mpr
    ⟨sample.bytes, fetched sample, Ext.decode_encode sample.instruction⟩)

theorem wire_step (platform : Ext.Wire.Platform) (sample : Sample) (address : Word) :
    x86WireStep platform (state sample address) = x86NativeStep (state sample address) :=
  X86Wire.common_result platform _ (common sample address)

theorem loaded_zero (sample : Sample) : Ext.loadN (memory sample) 0x4000 8 = some 0 := by
  unfold Ext.loadN
  change ((memory sample).readBytes 0x4000 8).map
    (fun bytes => BitVec.ofNat 64 (Ext.leValue bytes)) = some 0
  rw [data_read]
  rfl

theorem read_operand (sample : Sample) (next : Word) :
    Ext.readRM .q (.mem operand) core (memory sample) next = some 0 := by
  change (Ext.loadN (memory sample) 0x4000 8).map (fun value => value.setWidth 64) = some 0
  rw [loaded_zero]
  rfl

theorem load_positive :
    x86NativeStep (state .load) =
      .ok ⟨⟨⟨{ (core).write .rax 0 with rip := 0x1003 }, memory .load⟩, none⟩, [(0x1000, 3), (0x4000, 8)]⟩ := by
  rw [native_step]
  change x86ExecResult [(0x1000, 3), (0x4000, 8)]
    (Ext.retire 0x1003 ((Ext.readRM .q (.mem operand) core (memory .load) 0x1003).map
      (fun value => (core.write .rax value, memory .load)))) = _
  rw [read_operand]
  rfl

theorem lea_does_not_touch_data :
    x86NativeStep (state .lea 0) =
      .ok ⟨⟨⟨{ (core 0).write .rax 0 with rip := 0x1003 }, memory .lea⟩, none⟩, [(0x1000, 3)]⟩ := by
  rw [native_step]
  rfl

theorem cmov_false_reads_data :
    x86NativeStep (state .cmovFalse) =
      .ok ⟨⟨⟨{ core with rip := 0x1004 }, memory .cmovFalse⟩, none⟩, [(0x1000, 4), (0x4000, 8)]⟩ := by
  rw [native_step]
  have executed : Ext.exec (Sample.instruction .cmovFalse) core (memory .cmovFalse) 4 =
      .ok { core.write .rax 0x77 with rip := 0x1004 } (memory .cmovFalse) := by
    simp only [Sample.instruction, Ext.exec, read_operand]
    rfl
  change x86ExecResult [(0x1000, 4), (0x4000, 8)]
    (Ext.exec (Sample.instruction .cmovFalse) core (memory .cmovFalse) 4) = _
  rw [executed]
  have unchanged : core.write .rax 0x77 = core := by
    change { core with regs := Machine.RegisterFile.write core.regs .rax (core.regs .rax) } = core
    rw [Machine.RegisterFile.write_current]
  rw [unchanged]
  rfl

theorem cmov_false_invalid_source_faults : x86NativeStep (state .cmovFalse 0) = .fault := by
  rw [native_step]
  rfl

theorem load_invalid_source_faults : x86NativeStep (state .load 0) = .fault := by
  rw [native_step]
  rfl

theorem lazy_first_touch_charged :
    materializeAccesses [(0x4000, 4096)] [] 0 4096 [(0x4000, 8)] = some [0x4000] := by
  decide +kernel

theorem lazy_first_touch_budget_refused :
    materializeAccesses [(0x4000, 4096)] [] 0 4095 [(0x4000, 8)] = none := by
  decide +kernel

theorem lazy_second_touch_not_charged_again :
    materializeAccesses [(0x4000, 4096)] [0x4000] 4096 4096 [(0x4000, 8)] = some [0x4000] := by
  decide +kernel

theorem lea_cannot_charge_unaccessed_lazy_data :
    materializeAccesses [(0x4000, 4096)] [] 0 0
      (X86Accesses.canonical (core) (Sample.bytes .lea).length (Sample.instruction .lea)) = some [] := by
  decide +kernel

/-- LEA has no data access, but executing it still consumes instruction bytes. -/
theorem lea_instruction_fetch_charged :
    materializeAccesses [(0x1000, 4096)] [] 0 4096 [(0x1000, 3)] = some [0x1000] := by
  decide +kernel

theorem lea_instruction_fetch_budget_refused :
    materializeAccesses [(0x1000, 4096)] [] 0 0 [(0x1000, 3)] = none := by
  decide +kernel

/-- The positive load's full report needs backing for code and data. -/
theorem load_code_and_data_budget_refused :
    materializeAccesses [(0x1000, 4096), (0x4000, 4096)] [] 0 4096
      [(0x1000, 3), (0x4000, 8)] = none := by
  decide +kernel

theorem load_code_and_data_charged :
    materializeAccesses [(0x1000, 4096), (0x4000, 4096)] [] 0 8192
      [(0x1000, 3), (0x4000, 8)] = some [0x4000, 0x1000] := by
  decide +kernel

def syscallMemory : Memory :=
  ⟨[⟨0x1000, 2, ⟨true, false, true⟩⟩], Memory.install {} 0x1000 [0x0f, 0x05]⟩

def syscallState : X86State := ⟨⟨core.write .rax 39, syscallMemory⟩, none⟩

theorem syscall_fetched : syscallMemory.fetchBytes 0x1000 2 = some [0x0f, 0x05] := by
  apply Memory.readWith_eq syscallMemory .execute 0x1000 [0x0f, 0x05] (by decide +kernel)
  intro index bound
  exact Memory.install_get _ _ _ index bound

/-- Native GETPID keeps Linux x86's number 39, and reports the actual fetch. -/
theorem native_syscall_keeps_number_and_fetch :
    x86NativeStep syscallState =
      .ok ⟨{ syscallState with pending := some 39 }, [(0x1000, 2)]⟩ := by
  exact x86NativeStep_syscall syscallState syscall_fetched (by decide +kernel)

theorem wire_syscall_keeps_number_and_fetch (platform : Ext.Wire.Platform) :
    x86WireStep platform syscallState =
      .ok ⟨{ syscallState with pending := some 39 }, [(0x1000, 2)]⟩ := by
  rw [X86Wire.common_result platform syscallState (Or.inl syscall_fetched)]
  exact native_syscall_keeps_number_and_fetch

/-- The legacy option deliberately retains its original generic-number ABI. -/
theorem legacy_syscall_unchanged :
    x86Step syscallState = .ok ⟨{ syscallState with pending := some 172 }, []⟩ := by
  have fetched : syscallState.m.memory.fetchBytes syscallState.m.core.rip.toNat 2 =
      some [0x0f, 0x05] := syscall_fetched
  rw [x86Step, ite_eq_left fetched]
  rfl

theorem syscall_instruction_fetch_budget_refused :
    materializeAccesses [(0x1000, 4096)] [] 0 0 [(0x1000, 2)] = none := by
  decide +kernel

end Silmaril.Process.LPS.Machines.X86WireControls
