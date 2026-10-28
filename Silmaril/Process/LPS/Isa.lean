module

public import Silmaril.Process.LPS.State
public import Silmaril.Process.LPS.MemImage

/-!
# LPS in Lean: the instruction-set interface of the process layer

LPS runs one ISA, its hand-written RV64GC, through `RiscvSemantics.v`. The process layer
touches the machine in only a few places: one instruction step reporting the memory it
accessed, the pending system call and its six argument registers, the readable and writable
views of user memory, the application of a syscall effect (return register and declared
memory effects), stepping past the trap, and the initial state. `UserIsa` collects exactly
these, so the run semantics, the statements and the shapes are parametric in the ISA.

Instances:

* `Silmaril.Process.LPS.Machines.RiscV`: Silmaril's RV64 `RiscV.Ext` machine;
* `Silmaril.Process.LPS.Machines.X86`: Silmaril's x86-64 `X86.Ext` machine, with the
  `syscall` instruction and the x86-64 syscall numbering mapped to the asm-generic table;
* the LPS RISC-V port (branch `riscv/lps-port`) is meant to instantiate it with
  `Overlay.applyEffect`, the literal translation of LPS `Run.apply_effect`.

The step result is LPS's three-way split (`RiscvSemantics.v:203`): `ok` (an instruction
retired, or a trap set a pending syscall), `fault` (the program died: SIGSEGV, SIGILL, SIGBUS
analogues) and `unmodeled` (the model declines).
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- LPS `RiscvSemantics.v:203` `machine_result`. -/
inductive MachineResult (α : Type) where
  | ok (x : α)
  | fault
  | unmodeled

/-- LPS `RiscvSemantics.v:825` `access_report`: a result and the user ranges accessed. -/
structure AccessReport (α : Type) where
  value : α
  accessed : List (Word × Nat)

/-- A machine the LPS process layer can run. `svcPending` uses the numbering of
the selected syscall table. Literal LPS and legacy adapters use asm-generic;
native adapters retain their architecture's numbers and select a native table. -/
structure UserIsa where
  /-- The user-mode machine state, memory included. -/
  State : Type
  /-- LPS `RiscvSemantics.v:1042` `step_accesses`: one instruction, given the loaded image.
  A trap instruction yields `ok` with a pending syscall. -/
  step : List Segment → State → MachineResult (AccessReport State)
  /-- LPS `ms_svc_pending`: the pending syscall's number. -/
  svcPending : State → Option Word
  /-- LPS `Run.v:92` `syscall_args`: the six argument registers. -/
  syscallArgs : State → List Word
  /-- LPS `RiscvSemantics.v:217` `ms_read_byte`: the readable view. -/
  readByte : List Segment → State → Word → Option Byte
  /-- LPS `RiscvSemantics.v:542` `ms_writable_byte`: the writable view. -/
  writableByte : List Segment → State → Word → Option Byte
  /-- LPS `Run.v:175` `apply_effect`: the return register and the declared memory effects. -/
  applyEffect : State → SyscallEffect → State
  /-- LPS `Run.v:191` `advance_past_svc`. -/
  advancePastSvc : State → State
  /-- LPS `Run.v:1058` `init_machine_state`: registers zero except the stack pointer, the pc
  at the entry point, and user memory given by the image, the entry block `stack` placed at
  `sp`, and zeros in the 8 MiB below `sp` (`stackOverlay`). -/
  init : List Segment → (pc : Nat) → (sp : Word) → (stack : List Byte) → State
  /-- Whether `step` reports every user range an instruction accesses. A machine that does not
  cannot charge lazy (`MAP_NORESERVE`) pages on first touch; the run semantics then fails
  closed (`unmodeled`) on its instructions while any lazy reservation exists. -/
  reportsAccesses : Bool
  /-- LPS `Equivalence.v:436` `image_entry_fetchable`: an instruction can be fetched at the
  entry point. -/
  entryFetchable : List Segment → Nat → Bool
  /-- The native kernel address boundary, selected from the input width where
  appropriate. The default preserves the literal LPS Sv48 gate at every width;
  native adapters opt into architecture-specific limits explicitly. -/
  addressSpace : VaSize → AddressSpaceProfile := fun _ => legacySv48AddressSpace

/-- Initialize the kernel model using the selected ISA's address boundary.
Launchers opt into this hook; the literal `initModel` API remains unchanged. -/
def UserIsa.initModel (isa : UserIsa) (reserved : List (Word × Word))
    (brk0 mbase sp : Word) (lim : Int) (inp : ProcInput) : Model :=
  initModelFor (isa.addressSpace inp.vaSize) reserved brk0 mbase sp lim inp

@[simp] theorem UserIsa.initModel_addressSpace (isa : UserIsa)
    (reserved : List (Word × Word)) (brk0 mbase sp : Word) (lim : Int) (inp : ProcInput) :
    (isa.initModel reserved brk0 mbase sp lim inp).addressSpace =
      isa.addressSpace inp.vaSize := rfl

/-- A legacy-profile ISA has the original initializer at every input width. -/
theorem UserIsa.initModel_eq_legacy (isa : UserIsa)
    (h : ∀ v, isa.addressSpace v = legacySv48AddressSpace)
    (reserved : List (Word × Word)) (brk0 mbase sp : Word) (lim : Int) (inp : ProcInput) :
    isa.initModel reserved brk0 mbase sp lim inp =
      Silmaril.Process.LPS.initModel reserved brk0 mbase sp lim inp := by
  simp only [UserIsa.initModel, h, initModelFor_legacy]

/-! ## Overlay memory: the literal LPS memory effects

LPS's user memory is an overlay `word → option byte` over the read-only image. The
following are the literal translations of the effect application of LPS `Run.v`. -/

/-- LPS user memory: a partial byte map. -/
abbrev Overlay := Word → Option Byte

namespace Overlay

/-- LPS `RiscvSemantics.v:139` `write_to_mem`. -/
def writeToMem (mem : Overlay) (addr : Word) : List Byte → Overlay
  | [] => mem
  | b :: rest => writeToMem (fun a => if a = addr then some b else mem a) (addr + 1) rest

/-- LPS `Run.v:95` `apply_writes`. -/
def applyWrites (mem : Overlay) : List (Word × List Byte) → Overlay
  | [] => mem
  | (a, bs) :: r => applyWrites (writeToMem mem a bs) r

/-- LPS `Run.v:104` `zeros_cover`. -/
def zerosCover (zs : List (Word × Word)) (a : Word) : Bool :=
  zs.any fun z => decide (uns z.1 ≤ uns a) && decide (uns a < uns z.1 + uns z.2)

/-- LPS `Run.v:113` `apply_zeros`. -/
def applyZeros (mem : Overlay) (zs : List (Word × Word)) : Overlay := fun a =>
  if zerosCover zs a then some 0 else mem a

/-- LPS `Run.v:128` `apply_unmaps`. -/
def applyUnmaps (mem : Overlay) (us : List (Word × Word)) : Overlay := fun a =>
  if zerosCover us a then none else mem a

/-- LPS `Run.v:139` `apply_copy`: copy from the pre-effect snapshot `before`. -/
def applyCopy (before mem : Overlay) (c : MemCopy) : Overlay := fun a =>
  if uns c.dst ≤ uns a ∧ uns a < uns c.dst + uns c.len then
    before (zw (uns c.src + (uns a - uns c.dst)))
  else mem a

/-- LPS `Run.v:150` `apply_copies`. -/
def applyCopies (before mem : Overlay) : List MemCopy → Overlay
  | [] => mem
  | c :: r => applyCopies before (applyCopy before mem c) r

/-- LPS `Run.v:1074` (`ms_mem` of `init_machine_state`): the entry block at `sp`, over zeros
in the 8 MiB below `sp`. -/
def stackOverlay (sp : Word) (bytes : List Byte) : Overlay := fun addr =>
  if uns sp ≤ uns addr ∧ uns addr - uns sp < bytes.length then bytes[(uns addr - uns sp).toNat]?
  else if uns sp - stackMaxSize ≤ uns addr ∧ uns addr < uns sp then some 0
  else none

/-- LPS `Run.v:175` `apply_effect` (memory part): unmaps, then zeros, then copies from the
snapshot, then writes. -/
def applyEffect (mem : Overlay) (eff : SyscallEffect) : Overlay :=
  applyWrites (applyCopies mem (applyZeros (applyUnmaps mem eff.unmaps) eff.zeros) eff.copies)
    eff.writes

end Overlay

end Silmaril.Process.LPS
