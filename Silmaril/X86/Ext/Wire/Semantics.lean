module

public import Silmaril.X86.Ext.Wire.Encoding
public import Silmaril.X86.Ext.Semantics

/-!
# Execution of byte-faithful local x86 instructions

Every next address uses the consumed length. Indirect CALL reads its target
before pushing its return address, including an RSP-based source. CMOV reads
its source even on a false condition and a 32-bit CMOV clears the upper half
on both outcomes. MUL defines CF/OF and leaves the other arithmetic flags
undefined. Faults carry no partially updated state.

CPUID is parameterized by an explicit platform response function. It writes
zero-extended EAX/EBX/ECX/EDX and preserves flags/memory. Fetch observes
`Process.Memory` directly: this model has no instruction cache, so CPUID does
not establish an external cache-publication theorem. A hardware or HOL4
cache refinement remains a separate obligation.

Reference: Intel SDM Vol. 2A, CALL, CMOVcc, CMP and CPUID; Vol. 2B, MUL and
XCHG. This is the handwritten local model, not an ISA correspondence proof.
-/

@[expose] public section

namespace Silmaril.X86.Ext.Wire

open Silmaril.X86 (State Word Reg Flags)
open Silmaril.Process (Memory)

/-- The four 32-bit CPUID outputs for an input leaf and subleaf. -/
structure CpuidReply where
  eax : BitVec 32
  ebx : BitVec 32
  ecx : BitVec 32
  edx : BitVec 32
  deriving DecidableEq, Repr

/-- Explicit platform contract: no invented default processor identity.
Availability of CPUID and any features used by canonical instructions are
preconditions of using this local user-mode machine on a platform. -/
structure Platform where
  cpuid : BitVec 32 → BitVec 32 → CpuidReply

/-- CPUID's register effects, with inputs sampled before any write. -/
def cpuidState (platform : Platform) (s : State) : State :=
  let reply := platform.cpuid (Sz.d.read s .rax) (Sz.d.read s .rcx)
  Sz.d.write (Sz.d.write (Sz.d.write (Sz.d.write s .rax reply.eax)
    .rbx reply.ebx) .rcx reply.ecx) .rdx reply.edx

@[simp] theorem cpuidState_flags (platform : Platform) (s : State) :
    (cpuidState platform s).flags = s.flags := rfl

/-- Unsigned full-width multiply flags: CF/OF indicate a nonzero upper half. -/
def mulFlags (highNonzero : Bool) : Flags :=
  Ext.mulFlags highNonzero

/-- Execute at the actual consumed length. -/
def execWithLength (platform : Platform) (i : Instr) (length : Nat)
    (s : State) (memory : Memory) : Result :=
  let next := s.rip + BitVec.ofNat 64 length
  match i with
  | .canonical i => Ext.execWithLength i length s memory
  | .callRM src =>
    match readRM .q src s memory next with
    | none => .dataFault
    | some target =>
      match X86.pushWord s memory next with
      | none => .dataFault
      | some (t, m) => .ok { t with rip := target } m
  | .jmpRM src =>
    match readRM .q src s memory next with
    | none => .dataFault
    | some target => .ok { s with rip := target } memory
  | .cmov sz c dst src => Ext.execWithLength (.cmov sz c dst src) length s memory
  | .xchg sz dst src =>
    retire next (some (sz.write (sz.write s dst (sz.read s src)) src (sz.read s dst), memory))
  | .mul sz src => Ext.execWithLength (.mul sz src) length s memory
  | .cmp8 dst src =>
    retire next ((readNarrow .b src s memory next).map fun y =>
      ({ s with flags := subFlagsN ((s.read dst).setWidth 8) y }, memory))
  | .testI sz dst imm =>
    retire next ((readRM sz dst s memory next).map fun x =>
      ({ s with flags := logicFlagsN (x &&& imm.signExtend sz.bits) }, memory))
  | .cpuid => retire next (some (cpuidState platform s, memory))

/-- Execute a byte-faithful decoded instruction. -/
def exec (platform : Platform) (d : Decoded) (s : State) (memory : Memory) : Result :=
  execWithLength platform d.instr d.length s memory

/-- Canonical semantics embed for every platform, with identical results. -/
@[simp] theorem exec_canonical (platform : Platform) (i : Ext.Instr)
    (s : State) (memory : Memory) :
    exec platform ⟨.canonical i, Ext.encode i⟩ s memory = Ext.exec i s memory := rfl

/-- A failed CMOV source read faults even when its condition is false. -/
theorem cmov_dataFault (platform : Platform) (sz : Sz) (c : Cond) (dst : Reg)
    (src : RM) (length : Nat) (s : State) (memory : Memory)
    (h : readRM sz src s memory (s.rip + BitVec.ofNat 64 length) = none) :
    execWithLength platform (.cmov sz c dst src) length s memory = .dataFault := by
  exact Ext.cmov_dataFault sz c dst src length s memory h

/-- A defined false 32-bit CMOV still clears bits 63:32. -/
theorem cmov_d_false (platform : Platform) (c : Cond) (dst src : Reg)
    (length : Nat) (s : State) (memory : Memory) (h : c.eval s.flags = some false) :
    execWithLength platform (.cmov .d c dst (.reg src)) length s memory =
      .ok { Sz.d.write s dst (Sz.d.read s dst) with
        rip := s.rip + BitVec.ofNat 64 length } memory := by
  exact Ext.cmov_d_false c dst src length s memory h

/-- The original Wire constructor uses the canonical CMOV operation at the
actual consumed length, including nonminimal spellings. -/
@[simp] theorem execWithLength_cmov (platform : Platform) (sz : Sz) (c : Cond)
    (dst : Reg) (src : RM) (length : Nat) (s : State) (memory : Memory) :
    execWithLength platform (.cmov sz c dst src) length s memory =
      Ext.execWithLength (.cmov sz c dst src) length s memory := rfl

/-- The original Wire MUL operation uses canonical semantics at the actual
consumed length. Its full product and undefined-flag convention are shared. -/
@[simp] theorem execWithLength_mul (platform : Platform) (sz : Sz) (src : RM)
    (length : Nat) (s : State) (memory : Memory) :
    execWithLength platform (.mul sz src) length s memory =
      Ext.execWithLength (.mul sz src) length s memory := rfl

/-- An indirect CALL uses the old register value, including old RSP. -/
theorem callRM_reg (platform : Platform) (target : Reg) (length : Nat)
    (s : State) (memory : Memory) :
    execWithLength platform (.callRM (.reg target)) length s memory =
      match X86.pushWord s memory (s.rip + BitVec.ofNat 64 length) with
      | none => .dataFault
      | some (t, after) => .ok { t with rip := s.read target } after := rfl

end Silmaril.X86.Ext.Wire
