module

public import Silmaril.Process.LPS.Machines.ProcessMemory
public import Silmaril.X86.Ext.Machine
public import Silmaril.Process.LPS.Machines.X86Accesses

/-!
# Silmaril's x86-64 machine under the LPS process layer

`x86Ext : UserIsa` runs Silmaril's handwritten x86-64 machine `X86.Ext.MState` as an LPS
process. This is a new instance: LPS models riscv64 only.

* `syscall` (`0F 05`): `X86.Ext` does not decode it, so the adapter recognises the two
  executable bytes at RIP and sets the pending syscall from RAX. Arguments are RDI, RSI, RDX,
  R10, R8, R9; the result goes to RAX; RIP advances by 2, RCX receives the return address and
  R11 the RFLAGS image (`syscall`, Intel SDM Vol. 2B). The model's status flags may be
  architecturally undefined; a `syscall` executed with an undefined flag is `unmodeled`,
  since the value R11 receives would then be unknown. RFLAGS bits the model does not hold are
  taken as their user-mode values (bit 1 and IF set, the others clear).
* Numbering: x86-64 numbers its calls differently (`arch/x86/entry/syscalls/syscall_64.tbl`).
  The adapter renumbers the calls whose LPS specification is translated and does not depend
  on an architecture-specific structure layout; every other number maps outside the table and
  is `unmodeled` (fail closed).
* Outcomes: UD2, divide errors, data faults and fetch faults are deaths (`fault`); bytes
  outside the model and conditions on undefined flags are `unmodeled`; RET is an ordinary
  instruction.
* `X86.Ext` does not report the ranges an instruction accesses, so `reportsAccesses` is
  false and the run fails closed while lazy (`MAP_NORESERVE`) reservations exist.

Known precision gap: LPS's address-space constants are riscv64 Sv48 ones. x86-64 with
four-level paging has `TASK_SIZE = 0x7ffffffff000`, one page lower, so the model admits a
mapping in the last page below `2^47` that x86-64 Linux refuses.
-/

@[expose] public section

namespace Silmaril.Process.LPS.Machines

open Silmaril.X86 (Reg MState Flags)

/-- The x86-64 machine state with LPS's pending-syscall slot. -/
structure X86State where
  m : MState
  pending : Option Word

/-- x86-64 syscall numbers of the translated, layout-independent LPS arms, with their
asm-generic numbers. -/
def x86SyscallMap : List (Nat × Nat) :=
  [ (0, 63), (1, 64), (3, 57), (9, 222), (11, 215), (12, 214), (39, 172), (60, 93), (61, 260),
    (102, 174), (104, 176), (107, 175), (108, 177), (186, 178), (218, 96), (231, 94),
    (318, 278) ]

/-- Renumber an x86-64 syscall; unknown numbers map outside the table. -/
def x86Renumber (n : Word) : Word :=
  match x86SyscallMap.find? (·.1 = n.toNat) with
  | some (_, g) => BitVec.ofNat 64 g
  | none => BitVec.ofNat 64 (2 ^ 63 + n.toNat % 2 ^ 32)

/-- The RFLAGS image `syscall` stores in R11, when every status flag is defined. -/
def rflagsImage (f : Flags) : Option Word := do
  let cf ← f.carry
  let pf ← f.parity
  let af ← f.adjust
  let zf ← f.zero
  let sf ← f.sign
  let of ← f.overflow
  let bit (b : Bool) (k : Nat) : Word := if b then BitVec.ofNat 64 (2 ^ k) else 0
  pure (bit cf 0 ||| bit true 1 ||| bit pf 2 ||| bit af 4 ||| bit zf 6 ||| bit sf 7 |||
    bit true 9 ||| bit of 11)

/-- One instruction, with LPS's outcome split. -/
def x86Step (s : X86State) : MachineResult (AccessReport X86State) :=
  if s.m.memory.fetchBytes s.m.core.rip.toNat 2 = some [0x0f, 0x05] then
    match rflagsImage s.m.core.flags with
    | none => .unmodeled
    | some _ => .ok ⟨{ s with pending := some (x86Renumber (s.m.core.read .rax)) }, []⟩
  else
    match Silmaril.X86.Ext.step 0 s.m with
    | .retired next => .ok ⟨⟨next, none⟩, []⟩
    | .returned final => .ok ⟨⟨final, none⟩, []⟩
    | .trapped => .fault
    | .undefinedCondition _ => .unmodeled
    | .divideFault => .fault
    | .dataFault _ => .fault
    | .fetchFault => .fault
    | .undecodable => .unmodeled

/-- Step past `syscall`: RIP advances by 2, RCX gets the return address, R11 the RFLAGS
image. -/
def x86AdvancePastSvc (s : X86State) : X86State :=
  let next := s.m.core.rip + 2
  let core := ((s.m.core.write .rcx next).write .r11
    ((rflagsImage s.m.core.flags).getD 0))
  ⟨{ s.m with core := { core with rip := next } }, none⟩

/-- Silmaril's x86-64 `Ext` machine as an LPS user machine. -/
def x86Ext : UserIsa where
  State := X86State
  step _ := x86Step
  svcPending s := s.pending
  syscallArgs s := [.rdi, .rsi, .rdx, .r10, .r8, .r9].map s.m.core.read
  readByte _ s := viewByte s.m.memory .read
  writableByte _ s := viewByte s.m.memory .write
  applyEffect s eff :=
    ⟨⟨s.m.core.write .rax eff.ret, applyMemoryEffect s.m.memory eff⟩, s.pending⟩
  advancePastSvc := x86AdvancePastSvc
  init segs pc sp stack :=
    ⟨⟨({ regs := fun _ => 0, rip := BitVec.ofNat 64 pc
         flags := ⟨some false, some false, some false, some false, some false, some false⟩ } :
        Silmaril.X86.State).write .rsp sp,
      initialMemory segs sp stack⟩, none⟩
  reportsAccesses := false
  entryFetchable segs pc :=
    match Silmaril.X86.Ext.fetch (initialMemory segs 0 []) pc with
    | .decoded _ _ => true
    | _ => (initialMemory segs 0 []).fetchBytes pc 2 = some [0x0f, 0x05]

/-- The original renumbered, non-reporting adapter is retained exactly.
Native adapters below use their own syscall table and address-space profile. -/
abbrev x86ExtLegacy : UserIsa := x86Ext

abbrev x86StepLegacy := x86Step

/-- Map the complete local executor result, retaining a successful data-span
report. No failed instruction reports a partially updated state. -/
def x86ExecResult (accesses : List (Word × Nat)) :
    Silmaril.X86.Ext.Result → MachineResult (AccessReport X86State)
  | .ok core memory => .ok ⟨⟨⟨core, memory⟩, none⟩, accesses⟩
  | .dataFault | .divideError | .trap => .fault
  | .undefinedCondition _ => .unmodeled

/-- Native x86 numbers are retained in the pending slot. The native syscall
table, rather than an ISA-side renumbering hack, interprets that slot. -/
def x86NativeStep (s : X86State) : MachineResult (AccessReport X86State) :=
  if s.m.memory.fetchBytes s.m.core.rip.toNat 2 = some [0x0f, 0x05] then
    match rflagsImage s.m.core.flags with
    | none => .unmodeled
    | some _ => .ok ⟨{ s with pending := some (s.m.core.read .rax) }, [(s.m.core.rip, 2)]⟩
  else
    match Silmaril.X86.Ext.fetch s.m.memory s.m.core.rip.toNat with
    | .undecodable => .unmodeled
    | .truncated => .fault
    | .decoded instruction length =>
      x86ExecResult ((s.m.core.rip, length) :: X86Accesses.canonical s.m.core length instruction)
        (Silmaril.X86.Ext.exec instruction s.m.core s.m.memory length)

theorem x86NativeStep_of_fetch (s : X86State) {bytes : List Byte}
    {instruction : Silmaril.X86.Ext.Instr} {length : Nat}
    (notSyscall : s.m.memory.fetchBytes s.m.core.rip.toNat 2 ≠ some [0x0f, 0x05])
    (fetched : s.m.memory.fetchBytes s.m.core.rip.toNat length = some bytes)
    (decoded : Silmaril.X86.Ext.decode bytes = some (instruction, length)) :
    x86NativeStep s = x86ExecResult ((s.m.core.rip, length) :: X86Accesses.canonical s.m.core length instruction)
      (Silmaril.X86.Ext.exec instruction s.m.core s.m.memory length) := by
  rw [x86NativeStep, ite_eq_right notSyscall,
    Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr ⟨bytes, fetched, decoded⟩]

/-- Architectural side effect of a successful native ARCH_SET_FS. The syscall
specification separately checks the operation, address and return value.
Arguments are sampled before writing RAX or applying memory effects. Other
calls (including a refused ARCH_SET_FS) cannot change FS base here. -/
def x86ApplyEffectNative (s : X86State) (effect : SyscallEffect) : X86State :=
  let core := s.m.core.write .rax effect.ret
  let core := if s.pending = some 158 ∧ s.m.core.read .rdi = 0x1002 ∧ effect.ret = 0 then
      { core with fsBase := s.m.core.read .rsi }
    else core
  ⟨⟨core, applyMemoryEffect s.m.memory effect⟩, s.pending⟩

/-- Canonical local x86 with consumed instruction-fetch and successful data
span reports, raw native
syscall numbers and the four-level Linux x86 address-space bound. REP/string
operations are not in this decoder and remain explicitly unmodeled. This does
not establish correspondence to hardware or to an external x86 semantics. -/
def x86ExtNative : UserIsa :=
  { x86Ext with
    step := fun _ => x86NativeStep
    applyEffect := x86ApplyEffectNative
    reportsAccesses := true
    addressSpace := fun _ => x86AddressSpace }

theorem x86NativeStep_syscall (s : X86State)
    (fetched : s.m.memory.fetchBytes s.m.core.rip.toNat 2 = some [0x0f, 0x05])
    (defined : (rflagsImage s.m.core.flags).isSome = true) :
    x86NativeStep s = .ok ⟨{ s with pending := some (s.m.core.read .rax) }, [(s.m.core.rip, 2)]⟩ := by
  rw [x86NativeStep, ite_eq_left fetched]
  cases flags : rflagsImage s.m.core.flags with
  | none => simp [flags] at defined
  | some word => rfl

theorem x86ApplyEffectNative_setFs (s : X86State) (effect : SyscallEffect)
    (pending : s.pending = some 158) (operation : s.m.core.read .rdi = 0x1002)
    (success : effect.ret = 0) :
    (x86ApplyEffectNative s effect).m.core.fsBase = s.m.core.read .rsi := by
  simp [x86ApplyEffectNative, pending, operation, success]

theorem x86ApplyEffectNative_preservesFs (s : X86State) (effect : SyscallEffect)
    (other : ¬ (s.pending = some 158 ∧ s.m.core.read .rdi = 0x1002 ∧ effect.ret = 0)) :
    (x86ApplyEffectNative s effect).m.core.fsBase = s.m.core.fsBase := by
  simp only [x86ApplyEffectNative, ite_eq_right other, Silmaril.X86.State.write_fsBase]

end Silmaril.Process.LPS.Machines
