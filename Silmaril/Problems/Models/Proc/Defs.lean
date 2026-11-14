module

public import Silmaril.Process.CLI.X86Linux
public import Silmaril.Process.CLI.X86Linux.Static
public import Silmaril.Process.CLI.Observation
public import Silmaril.X86.Str9.Defs

/-!
# A process model for statically linked musl executables (`musl-str9`)

A problem about what a pinned executable prints is a process statement over the CLI
semantics (`Silmaril.Process.CLI.Agrees`), not a function statement. The model point
`X86Linux.linux` cannot run a statically linked musl executable: `X86.Ext` has no indirect
`call`/`jmp` (musl's `libc_start_main_stage2` calls `main` through a register), no
`rep movsq`/`rep stosq`/`movsb` (musl's `memcpy`/`memset`), and its syscall profile has no
`arch_prctl`/`set_tid_address` (musl's `__init_tp`). Every run would stop before `main`, so
every `Agrees` statement over it would hold vacuously.

`model` fixes those three gaps and nothing else:

* **Instructions**: `Silmaril.X86.Str9.step` (the open `Ext9` machine, which has the
  indirect forms, plus the three string forms), with `syscall` (`0F 05`) recognised first,
  as `X86Linux.step` does. A `none` from `Str9.step` is an `unmodeled` fault.
* **Startup system calls**: a trap with `rax = 158` and `rdi = 0x1002` (`arch_prctl
  (ARCH_SET_FS, rsi)`) retires silently, setting `fsBase := rsi` and `rax := 0`; a trap
  with `rax = 218` (`set_tid_address`) retires silently with any `rax` (the thread id).
  Both clobber `rcx` (the return address) and `r11` (any value), as the kernel does. They
  emit no event. Any other `arch_prctl` code has no outcome (the process blocks).
* **Everything else is `X86Linux`'s**: the request decoding and resume (`X86Linux.request`,
  `X86Linux.Resume`: `read`, `write`, `exit`, `exit_group`), the environment `Env.linux`
  (with its refusals and short transfers) and `linuxInit`.
* **The loader** (`Load`) is `X86Linux.Loaded` plus two conditions: the stack room below
  `rsp` does not alias the image, and the launch is static (`X86Linux.Static`): the
  auxiliary vector names the image's own program-header table (`AT_PHDR`, `AT_PHENT`,
  `AT_PHNUM`, each once), `AT_PAGESZ` is `4096`, there is no vDSO (`AT_SYSINFO_EHDR`),
  the table and any `PT_TLS` initializer come from the file's bytes, and the only
  executable mappings are the image's segments. Without the static condition a launch
  could point musl's `static_init_tls` at a forged table and run code of its choice
  before `main` (erebor-lean #70).

**The loader before #70** is kept as `LoadLoose` and `modelLoose`. `model ≼ modelLoose`
(`Thms.le_loose`), so every `Agrees`, `Covered`, `Halts` or `Bounded` statement proved over
`modelLoose` holds over `model`. Existential statements (`ExitsOn`, nonvacuity companions)
go the other way (`Thms.exitsOn_loose`): a witness over `modelLoose` must be re-proved with
a static launch.

**Trust.** A model, not a theorem: the handwritten `Ext`/`Ext8`/`Ext9`/`Str9` semantics
and the two startup arms above. `Agrees` ignores faults, so a gap on some path can make a
statement easier, never harder; that is why each problem carries a nonvacuity companion
(some run exits with status 0). Whether every instruction on the measured witness paths
is decoded is **not checked** here.
-/

@[expose] public section

namespace Silmaril.Problems.Models.Proc

open Silmaril.Process.CLI
open Silmaril.X86 (State MState Word)
open Silmaril.Process (Memory)

/-- `arch_prctl`, `ARCH_SET_FS` and `set_tid_address` (x86-64 Linux numbers). -/
def archPrctlNumber : Nat := 158
def archSetFs : Nat := 0x1002
def setTidAddressNumber : Nat := 218

/-- One user-mode step: `syscall` traps; otherwise one `Str9` step (`none`: unmodeled). -/
def userStep (core : State) (memory : Memory) : Step State :=
  if memory.fetchBytes core.rip.toNat 2 = some X86Linux.syscallBytes then
    .syscall { core with rip := core.rip + 2 }
  else
    match Silmaril.X86.Str9.step ⟨core, memory⟩ with
    | some next => .retired next.core next.memory
    | none => .fault .unmodeled

/-- The trap is one of the two startup calls answered silently. -/
def isStartup (trapped : State) : Bool :=
  (trapped.read .rax).toNat == archPrctlNumber || (trapped.read .rax).toNat == setTidAddressNumber

/-- The core after a silently answered startup call. -/
def Startup (trapped core' : State) : Prop :=
  ((trapped.read .rax).toNat = archPrctlNumber ∧ (trapped.read .rdi).toNat = archSetFs ∧
    ∃ flags : Word, core' =
      ((({ trapped with fsBase := trapped.read .rsi } : State).write .rax 0).write .rcx
        trapped.rip).write .r11 flags) ∨
  ((trapped.read .rax).toNat = setTidAddressNumber ∧
    ∃ tid flags : Word, core' = ((trapped.write .rax tid).write .rcx trapped.rip).write .r11 flags)

/-- **The instruction-set model**: `userStep`, with the startup calls retired silently. -/
def isa : Isa where
  Core := State
  step core memory o :=
    match userStep core memory with
    | .syscall trapped =>
      if isStartup trapped then ∃ core', Startup trapped core' ∧ o = .retired core' memory
      else o = .syscall trapped
    | r => o = r
  request := X86Linux.request
  resume := X86Linux.Resume

/-- **The loader before erebor-lean #70**: `X86Linux.Loaded`, and the writable stack room
below the initial `rsp` (`X86Linux.stackRoom` bytes) is disjoint from every image segment.
`X86Linux.Loaded` alone lets the stack alias the image's `.bss`, and a run whose frames
overwrite the program's state could then violate a spec on a correct build. -/
def LoadLoose (image : Image) (input : ProcInput) (core : State) (memory : Memory) : Prop :=
  X86Linux.Loaded image input core memory ∧
  ∀ seg ∈ image.segments, Silmaril.Process.Region.Disjoint seg.region
    ⟨(core.read .rsp).toNat - X86Linux.stackRoom, X86Linux.stackRoom, ⟨true, true, false⟩⟩

/-- **The loader**: `LoadLoose`, and the launch is static (`X86Linux.Static`): musl's startup
reads the image's own program headers, and the only executable mappings are the image's
segments. -/
def Load (image : Image) (input : ProcInput) (core : State) (memory : Memory) : Prop :=
  LoadLoose image input core memory ∧ X86Linux.Static image input core memory

/-- **`musl-str9`**: `isa` in the Linux environment `Env.linux`, loaded by `Load`. -/
def model : Model where
  isa := isa
  env := Env.linux
  envInit := linuxInit
  load := Load

/-- `musl-str9` with the loader before erebor-lean #70 (`LoadLoose`). Kept so that results
proved over it transfer (`Thms.le_loose`); new statements use `model`. -/
def modelLoose : Model := { model with load := LoadLoose }

/-- **Process nonvacuity**: some valid launch of `image` whose stdin is `stdin` has a run
that exits with status `0`. -/
def ExitsOn (M : Model) (image : Image) (stdin : List Silmaril.Process.Byte) : Prop :=
  ∃ input x events y, input.Valid ∧ input.stdin = .ofList stdin ∧ M.Init image input x ∧
    Proc.Runs M.isa M.env x events y ∧ Proc.Stop M.isa M.env y (.exited 0)

end Silmaril.Problems.Models.Proc
