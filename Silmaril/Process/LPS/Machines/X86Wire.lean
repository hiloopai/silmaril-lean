module

public import Silmaril.Process.LPS.Machines.X86

/-! # Byte-faithful x86 execution under the direct LPS port

The native adapter shares the canonical machine's state, six syscall argument
registers, raw native pending number, syscall return/FS-base effects, loader
and address-space profile. It changes only instruction fetch/execution and the
corresponding successful instruction/data-span report. Actual consumed length is used for
RIP-relative operands, fallthrough and return addresses.

`common_result` preserves the complete result on the common fragment,
including every architectural fault, undefined-condition/model gap, syscall
and its data-access list. Newly supported spellings are outside that fragment.
No claim identifies old undecodable failures with newly successful execution.
Neither local handwritten x86 model is claimed to refine hardware here.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines

open Silmaril.X86

def x86WireStep (platform : Ext.Wire.Platform) (s : X86State) :
    MachineResult (AccessReport X86State) :=
  if s.m.memory.fetchBytes s.m.core.rip.toNat 2 = some [0x0f, 0x05] then
    match rflagsImage s.m.core.flags with
    | none => .unmodeled
    | some _ => .ok ⟨{ s with pending := some (s.m.core.read .rax) }, [(s.m.core.rip, 2)]⟩
  else
    match Ext.Wire.fetch s.m.memory s.m.core.rip.toNat with
    | .undecodable => .unmodeled
    | .truncated => .fault
    | .decoded decoded =>
      x86ExecResult ((s.m.core.rip, decoded.length) :: X86Accesses.wire s.m.core decoded)
        (Ext.Wire.exec platform decoded s.m.core s.m.memory)

def x86Wire (platform : Ext.Wire.Platform) : UserIsa :=
  { x86ExtNative with
    step := fun _ => x86WireStep platform
    entryFetchable := fun segments pc =>
      match Ext.Wire.fetch (initialMemory segments 0 []) pc with
      | .decoded _ => true
      | _ => (initialMemory segments 0 []).fetchBytes pc 2 = some [0x0f, 0x05] }

namespace X86Wire

/-- Canonical fetched instructions, including all execution failures, plus
fetch failures that both decoders classify identically. -/
inductive CommonFetch (memory : Process.Memory) (address : Nat) : Prop where
  | decoded {instruction : Ext.Instr} {length : Nat}
      (fetched : Ext.fetch memory address = .decoded instruction length)
  | truncated (canonical : Ext.fetch memory address = .truncated)
      (wire : Ext.Wire.fetch memory address = .truncated)
  | undecodable (canonical : Ext.fetch memory address = .undecodable)
      (wire : Ext.Wire.fetch memory address = .undecodable)

def CommonAt (state : X86State) : Prop :=
  state.m.memory.fetchBytes state.m.core.rip.toNat 2 = some [0x0f, 0x05] ∨
    CommonFetch state.m.memory state.m.core.rip.toNat

/-- Equality is over the entire LPS machine result: successful successor,
pending syscall and exact data spans, or the same fault/unmodeled outcome. -/
theorem common_result (platform : Ext.Wire.Platform) (state : X86State)
    (common : CommonAt state) : x86WireStep platform state = x86NativeStep state := by
  unfold x86WireStep x86NativeStep
  split
  · rfl
  · rename_i notSyscall
    have shared : CommonFetch state.m.memory state.m.core.rip.toNat := common.resolve_left notSyscall
    cases shared with
    | decoded fetched =>
      rw [Ext.Wire.fetch_of_ext fetched, fetched, Ext.fetch_length fetched]
      simp only [X86Accesses.wire_canonical, Ext.Wire.exec_canonical]
      rfl
    | truncated canonical wire => rw [canonical, wire]
    | undecodable canonical wire => rw [canonical, wire]

theorem common_isa_result (platform : Ext.Wire.Platform) (segments : List Segment)
    (state : X86State) (common : CommonAt state) :
    (x86Wire platform).step segments state = x86ExtNative.step segments state :=
  common_result platform state common

/-- A useful common-fragment witness does not exclude instruction faults. -/
theorem canonical_common (state : X86State) {instruction : Ext.Instr} {length : Nat}
    (fetched : Ext.fetch state.m.memory state.m.core.rip.toNat = .decoded instruction length) :
    CommonAt state := Or.inr (.decoded fetched)

end X86Wire

end Silmaril.Process.LPS.Machines
