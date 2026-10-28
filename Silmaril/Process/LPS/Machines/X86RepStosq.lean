module

public import Silmaril.Process.LPS.Machines.X86Wire

/-!
# Optional DF-clear REP STOSQ microsteps

This narrow option handles exactly `f3 48 ab`: 64-bit RCX, RDI and RAX, with
the direction flag scoped to zero. CLD/STD and address-size/operand-size variants
remain outside this profile. It is not a hardware correspondence theorem.

Each successful nonempty microstep stores one complete eight-byte element,
decrements RCX, advances RDI modulo 2^64 and reports precisely that data span.
RIP stays at the instruction until the last element. A failed iteration returns
`fault` without committing that iteration; prior successful microsteps persist.
Zero count advances RIP without inspecting or reporting destination memory.

The option is an actual `UserIsa`, sharing the native syscall ABI, loader and
memory effects. It leaves the original Wire adapter unchanged. This deterministic
option retains Wire's fully-defined-flags syscall requirement; the separate
`X86WireFlagOracle` leaf supplies an optional oracle wrapper.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines.X86RepStosq

open Silmaril.X86
open Silmaril.Process (Memory)

def bytes : List Byte := [0xf3, 0x48, 0xab]

/-- One DF=0 element, or the zero-count no-access case. -/
def iterate (state : X86State) : MachineResult (AccessReport X86State) :=
  let core := state.m.core
  let count := core.read .rcx
  if count = 0 then
    .ok ⟨⟨⟨{ core with rip := core.rip + 3 }, state.m.memory⟩, none⟩,
      [(core.rip, 3)]⟩
  else
    match Ext.storeN state.m.memory (core.read .rdi) 8 (core.read .rax) with
    | none => .fault
    | some memory =>
      let after := (core.write .rcx (count - 1)).write .rdi (core.read .rdi + 8)
      .ok ⟨⟨⟨{ after with rip := if count = 1 then core.rip + 3 else core.rip },
        memory⟩, none⟩, [(core.rip, 3), (core.read .rdi, 8)]⟩

def step (platform : Ext.Wire.Platform) (state : X86State) :
    MachineResult (AccessReport X86State) :=
  if state.m.memory.fetchBytes state.m.core.rip.toNat 3 = some bytes then
    iterate state
  else x86WireStep platform state

theorem step_rep (platform : Ext.Wire.Platform) (state : X86State)
    (fetched : state.m.memory.fetchBytes state.m.core.rip.toNat 3 = some bytes) :
    step platform state = iterate state := by
  rw [step, ite_eq_left fetched]

/-- Full machine-result equality away from the one new fetched spelling. -/
theorem step_eq_wire (platform : Ext.Wire.Platform) (state : X86State)
    (other : state.m.memory.fetchBytes state.m.core.rip.toNat 3 ≠ some bytes) :
    step platform state = x86WireStep platform state := by
  rw [step, ite_eq_right other]

/-- The old decoder cannot consume even a shorter prefix of the new spelling. -/
theorem wire_decode_rep_append (rest : List Byte) :
    Ext.Wire.decode (bytes ++ rest) = none := by rfl

theorem wire_parse_rep_append (rest : List Byte) :
    Ext.Wire.parseRaw (bytes ++ rest) = .bad := by rfl

/-- The extended spelling was a model gap, never an old success or fault. -/
theorem wire_rep_unmodeled (platform : Ext.Wire.Platform) (state : X86State)
    (fetched : state.m.memory.fetchBytes state.m.core.rip.toNat 3 = some bytes) :
    x86WireStep platform state = .unmodeled := by
  obtain ⟨rest, image⟩ := X86.fetchBytes_prefix_fetchWindow
    (limit := maxInstrLength) fetched (by decide)
  have firstTwo := Memory.readWith_slice fetched 0 2 (by decide) (by decide)
  have notSyscall : state.m.memory.fetchBytes state.m.core.rip.toNat 2 ≠ some [0x0f, 0x05] := by
    intro syscall
    change state.m.memory.fetchBytes state.m.core.rip.toNat 2 = some [0xf3, 0x48] at firstTwo
    rw [firstTwo] at syscall
    contradiction
  rw [x86WireStep, ite_eq_right notSyscall]
  unfold Ext.Wire.fetch
  simp only [← image, wire_decode_rep_append, wire_parse_rep_append]

/-- Every old modeled result, including faults, remains exactly the same.
This is a partial-model extension law, not a hardware refinement or a theorem
about specifications that count an old `unmodeled` result as success. -/
theorem preserves_modeled_result (platform : Ext.Wire.Platform) (state : X86State)
    (modeled : x86WireStep platform state ≠ .unmodeled) :
    step platform state = x86WireStep platform state := by
  by_cases fetched : state.m.memory.fetchBytes state.m.core.rip.toNat 3 = some bytes
  · exact False.elim (modeled (wire_rep_unmodeled platform state fetched))
  · exact step_eq_wire platform state fetched

/-- Reuse the existing common-fragment result, including faults and syscalls. -/
theorem step_eq_native (platform : Ext.Wire.Platform) (state : X86State)
    (other : state.m.memory.fetchBytes state.m.core.rip.toNat 3 ≠ some bytes)
    (common : X86Wire.CommonAt state) : step platform state = x86NativeStep state :=
  (step_eq_wire platform state other).trans (X86Wire.common_result platform state common)

theorem iterate_zero (state : X86State) (count : state.m.core.read .rcx = 0) :
    iterate state =
      .ok ⟨⟨⟨{ state.m.core with rip := state.m.core.rip + 3 }, state.m.memory⟩, none⟩,
        [(state.m.core.rip, 3)]⟩ := by
  simp only [iterate, count, ↓reduceIte]

theorem iterate_fault (state : X86State) (count : state.m.core.read .rcx ≠ 0)
    (failed : Ext.storeN state.m.memory (state.m.core.read .rdi) 8
      (state.m.core.read .rax) = none) : iterate state = .fault := by
  simp only [iterate, count, ↓reduceIte, failed]

theorem iterate_store (state : X86State) (memory : Memory)
    (count : state.m.core.read .rcx ≠ 0)
    (stored : Ext.storeN state.m.memory (state.m.core.read .rdi) 8
      (state.m.core.read .rax) = some memory) :
    iterate state =
      .ok ⟨⟨⟨{ ((state.m.core.write .rcx (state.m.core.read .rcx - 1)).write .rdi
        (state.m.core.read .rdi + 8)) with
        rip := if state.m.core.read .rcx = 1 then state.m.core.rip + 3 else state.m.core.rip },
        memory⟩, none⟩, [(state.m.core.rip, 3), (state.m.core.read .rdi, 8)]⟩ := by
  simp only [iterate, count, ↓reduceIte, stored]

/-- The existing memory frame theorem supplies a reusable per-element footprint. -/
theorem store_frame (state : X86State) (memory : Memory)
    (stored : Ext.storeN state.m.memory (state.m.core.read .rdi) 8
      (state.m.core.read .rax) = some memory) :
    Memory.WritesOnly state.m.memory memory (state.m.core.read .rdi).toNat 8 :=
  Ext.storeN_writesOnly stored

/-- This profile does not silently interpret an address-size override as RCX/RDI. -/
theorem address_override_rejected :
    Ext.Wire.decode [0x67, 0xf3, 0x48, 0xab] = none := by decide

theorem direction_changes_rejected :
    Ext.Wire.decode [0xfc] = none ∧ Ext.Wire.decode [0xfd] = none := by decide

end X86RepStosq

/-- An additive native-ABI Wire option for the explicitly DF=0 string subset. -/
def x86WireDf0RepStosq (platform : Silmaril.X86.Ext.Wire.Platform) : UserIsa :=
  { x86Wire platform with
    step := fun _ => X86RepStosq.step platform
    entryFetchable := fun segments pc =>
      (initialMemory segments 0 []).fetchBytes pc 3 = some X86RepStosq.bytes ||
        (x86Wire platform).entryFetchable segments pc }

end Silmaril.Process.LPS.Machines
