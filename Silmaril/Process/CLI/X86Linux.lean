module

public import Silmaril.Process.CLI.Spec
public import Silmaril.X86.Ext.Machine
public import Silmaril.Machine.LittleEndian

/-! # x86-64 Linux as a model point

`isa` wraps the handwritten `X86.Ext` fetch/decode/execute machine as an
`Isa`, adding the one instruction a process needs and `X86.Ext` lacks:
`syscall` (`0F 05`). It is recognised before decoding, from two executable
bytes at RIP. Its ABI is the x86-64 Linux one (`arch/x86/entry/entry_64.S`,
`entry_SYSCALL_64`; `arch/x86/entry/syscalls/syscall_64.tbl`):

* number in `rax`, arguments in `rdi rsi rdx r10 r8 r9`;
* read = 0, write = 1, exit = 60, exit_group = 231 (one thread, so the two
  exits coincide); the descriptor is an `unsigned int` and is truncated to 32
  bits; the exit status keeps its low byte (`Syscall.Step.exit`);
* on return `rax` holds the result (−4095…−1 is −errno), `rcx` the address
  after `syscall`, and `r11` the flags; every other register and the flags are
  preserved. `r11` is left unspecified here (sound, less precise).

Faults are classified without naming a signal (`CLI.Observation`): a data or
fetch fault is `memory`, `#DE` is `divide`, `UD2` is `illegal`, and
undecodable bytes or a condition on an undefined flag are `unmodeled`.

`Loaded` is the loader relation: the image's segments are mapped, the initial
stack has the System V layout (psABI §3.4.1, Figure 3.9; Linux
`fs/binfmt_elf.c`, `create_elf_tables`) and RIP is the entry. It is an
existential over everything the program cannot choose (stack address, string
placement, auxiliary vector contents beyond `AT_NULL`, other mappings, the
other registers and the flags), so a proof covers every Linux launch.
`LoadedZeroed` adds Linux's zeroed registers (`ELF_PLAT_INIT`); it is a lower
model point.

Not modeled, and therefore excluded by `Covered`: every other system call
(in particular `arch_prctl`, `brk`, `mmap`, so a statically linked glibc or
musl `_start` is outside this profile and a program must be freestanding);
signals; the vDSO; stack growth below the mapped room.
-/

@[expose] public section

namespace Silmaril.Process.CLI.X86Linux

open Silmaril.Process.Syscall
open Silmaril.X86 (Reg Word)

abbrev Core := Silmaril.X86.State

/-! ## The instruction-set model -/

/-- `syscall` is `0F 05`. -/
def syscallBytes : List Byte := [0x0F, 0x05]

def execResult : X86.Ext.Result → Step Core
  | .ok core memory => .retired core memory
  | .dataFault => .fault .memory
  | .divideError => .fault .divide
  | .undefinedCondition _ => .fault .unmodeled
  | .trap => .fault .illegal

/-- One step of `X86.Ext` with `syscall` recognised first. -/
def step (core : Core) (memory : Memory) : Step Core :=
  if memory.fetchBytes core.rip.toNat 2 = some syscallBytes then
    .syscall { core with rip := core.rip + 2 }
  else
    match X86.Ext.fetch memory core.rip.toNat with
    | .undecodable => .fault .unmodeled
    | .truncated => .fault .memory
    | .decoded instr length => execResult (X86.Ext.exec instr core memory length)

def readNumber : Nat := 0
def writeNumber : Nat := 1
def exitNumber : Nat := 60
def exitGroupNumber : Nat := 231

/-- The request a trapped core makes; `none` outside the profile. -/
def request (core : Core) : Option Request :=
  let number := (core.read .rax).toNat
  let fd := ((core.read .rdi).setWidth 32).toNat
  let address := (core.read .rsi).toNat
  let count := (core.read .rdx).toNat
  if number = readNumber then some (.read fd address count)
  else if number = writeNumber then some (.write fd address count)
  else if number = exitNumber ∨ number = exitGroupNumber then some (.exit (core.read .rdi).toNat)
  else none

/-- The raw `rax` of a result. -/
def resultWord : Result → Word
  | .ok count => BitVec.ofNat 64 count
  | .error errno => BitVec.ofInt 64 (-(errno.value : Int))

/-- The kernel's return: `rax`, `rcx`, and an unspecified `r11`. -/
def Resume (core : Core) (result : Result) (core' : Core) : Prop :=
  ∃ flagsWord : Word,
    core' = ((core.write .rax (resultWord result)).write .rcx core.rip).write .r11 flagsWord

def isa : Isa where
  Core := Core
  step core memory o := o = step core memory
  request := request
  resume := Resume

theorem isa_total : isa.Total := fun core memory => ⟨step core memory, rfl⟩

/-! ## The initial stack -/

/-- `bytes` are mapped readable and backed at `address`. -/
def BytesAt (memory : Memory) (address : Nat) (bytes : List Byte) : Prop :=
  memory.readBytes address bytes.length = some bytes

/-- The auxiliary vector tags this profile names. -/
def atNull : Word := 0
def atPagesz : Word := 6
def atRandom : Word := 25

/-- The words from `rsp` upward: `argc`, `argv[]`, NULL, `envp[]`, NULL, then the
auxiliary vector pairs, the last of which is `(AT_NULL, 0)`. -/
def vectorWords (argv envp : List Word) (auxv : List (Word × Word)) : List Word :=
  [BitVec.ofNat 64 argv.length] ++ argv ++ [0] ++ envp ++ [0] ++
    auxv.flatMap (fun entry => [entry.1, entry.2]) ++ [atNull, 0]

/-- The stack a Linux `execve` builds, for one launch. -/
structure StackLayout (input : ProcInput) (memory : Memory) (sp : Nat) : Prop where
  aligned : sp % 16 = 0
  vectors : ∃ (argv envp : List Word) (auxv : List (Word × Word)),
    argv.length = input.argv.length ∧ envp.length = input.envp.length ∧
    BytesAt memory sp (Machine.LittleEndian.encodeWords (vectorWords argv envp auxv)) ∧
    (∀ i (hi : i < argv.length) (hs : i < input.argv.length),
      BytesAt memory argv[i].toNat (input.argv[i] ++ [0])) ∧
    (∀ i (hi : i < envp.length) (hs : i < input.envp.length),
      BytesAt memory envp[i].toNat (input.envp[i] ++ [0])) ∧
    (atNull, 0) ∉ auxv ∧
    (∀ value, (atRandom, value) ∈ auxv → ∃ bytes, bytes.length = 16 ∧ BytesAt memory value.toNat bytes)

/-- Writable room below the initial stack pointer, at least `stackRoom` bytes.
Linux pre-expands the stack mapping by 128 KiB (`setup_arg_pages`); unbacked
bytes are mapped but read as a fault until written (conservative). -/
def stackRoom : Nat := 0x10000

def Loaded (image : Image) (input : ProcInput) (core : Core) (memory : Memory) : Prop :=
  image.Mapped memory ∧
  core.rip.toNat = image.entry ∧
  StackLayout input memory (core.read .rsp).toNat ∧
  stackRoom ≤ (core.read .rsp).toNat ∧
  memory.Permitted .write ((core.read .rsp).toNat - stackRoom) stackRoom ∧
  core.read .rdx = 0

/-- Linux also zeroes every other general register (`ELF_PLAT_INIT`). -/
def LoadedZeroed (image : Image) (input : ProcInput) (core : Core) (memory : Memory) : Prop :=
  Loaded image input core memory ∧ ∀ r : Reg, r ≠ .rsp → core.read r = 0

/-! ## Model points -/

/-- x86-64 `X86.Ext` with `syscall`, in environment `env`. -/
def model (env : Env) (envInit : ProcInput → Memory → env.State → Prop) : Model where
  isa := isa
  env := env
  envInit := envInit
  load := Loaded

def linux : Model := model Env.linux linuxInit
def eintrClean : Model := model Env.eintrClean linuxInit
def reliable : Model := model Env.reliable linuxInit
def ideal : Model := model Env.ideal linuxInit

/-- Restricting the environment of a model point to a smaller one (same state
type and initial states) moves it down. -/
theorem model_le {E F : Env} (sim : Env.Sim E F)
    (envInit : ProcInput → Memory → E.State → Prop) (envInit' : ProcInput → Memory → F.State → Prop)
    (init : ∀ {input m s}, envInit input m s → ∃ t, envInit' input m t ∧ sim.rel s t) :
    (model E envInit).Le (model F envInit') :=
  ⟨{ isa := Isa.Sim.id isa
     env := sim
     envInit := init
     load := fun {_ _ c _} load => ⟨c, load, rfl⟩ }⟩

/-- The x86-64 ladder: `ideal ≼ reliable ≼ eintrClean ≼ linux`. -/
theorem ideal_le_reliable : ideal.Le reliable :=
  model_le (Env.restrictMonoSim Env.linux fun _ _ _ _ _ _ h => h.1) linuxInit linuxInit
    fun {_ _ s} init => ⟨s, init, rfl⟩

theorem reliable_le_eintrClean : reliable.Le eintrClean :=
  model_le (Env.restrictMonoSim Env.linux fun _ _ _ _ _ _ h => h.1) linuxInit linuxInit
    fun {_ _ s} init => ⟨s, init, rfl⟩

theorem eintrClean_le_linux : eintrClean.Le linux :=
  model_le (Env.restrictSim Env.linux _) linuxInit linuxInit fun {_ _ s} init => ⟨s, init, rfl⟩

/-- Zeroed registers are a lower point on the loader axis. -/
theorem zeroed_le (env : Env) (envInit : ProcInput → Memory → env.State → Prop) :
    ({ model env envInit with load := LoadedZeroed } : Model).Le (model env envInit) :=
  ⟨{ isa := Isa.Sim.id isa
     env := Env.Sim.id env
     envInit := fun {_ _ s} init => ⟨s, init, rfl⟩
     load := fun {_ _ c _} load => ⟨c, load.1, rfl⟩ }⟩

end Silmaril.Process.CLI.X86Linux
