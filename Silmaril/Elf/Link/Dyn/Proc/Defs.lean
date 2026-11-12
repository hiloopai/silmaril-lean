module

public import Silmaril.Elf.Link.Dyn.Loader.Defs
public import Silmaril.X86.RelIsa.Defs
public import Silmaril.X86.Open9.Defs

/-! # A dynamically linked process, modulo a loose libc

The process of an executable linked against a C library, as a relational machine
`proc W : RelIsa PState`. Inside the executable's image the machine is `Open9.step` (the
trusted instruction semantics). At the addresses the loader bound the executable's imports
to, the machine is the **import's loose contract**, one step from call to return (or to the
next callback): the library's code is not modelled, only what it is assumed to do.

**State.** `PState` is an `MState` and the library's abstract state `Ghost`: the bytes the
program has handed to `stdout` (`out`), the callbacks the library still has to make (`jobs`:
initialisers, `main`, `atexit` handlers, finalisers), the registered `atexit` handlers, and,
once the process has ended, its exit status and the bytes that reached file descriptor 1
(`done`).

**Callbacks.** The library calls back into the executable (`__libc_start_main` runs
`DT_INIT`, `DT_INIT_ARRAY` and `main`; `exit` runs `atexit` handlers, `DT_FINI_ARRAY` and
`DT_FINI`). A callback is entered with a return address `gate`, a library-internal address;
when the executable returns there, the library takes its next job (`gateStep`). Its stack,
registers and memory outside the executable's image are chosen demonically.

**The contracts** (`Fn`), from glibc 2.39's documented behaviour; each holds only under its
precondition (outside it, any outcome is allowed, including `stop`):

* `puts s`: System V call (`AbiEntry`), `rdi` a C string `s`. Returns (`AbiReturn`), the
  executable's image and the stack at and above the entry `rsp` unchanged, and either appends
  `s ++ "\n"` to `out` with a non-negative `eax`, or, unless the I/O environment is
  `reliable`, appends a prefix of it and returns `EOF` (`eax = -1`);
* `__libc_start_main (main, argc, argv, …)`: jobs := each initialiser with
  `(argc, argv, envp)`, then `main` with the same; `envp = argv + 8 (argc + 1)`;
* `__cxa_finalize d`: when no `atexit` handler is registered (the executables here register
  none), returns with nothing changed but scratch registers;
* `exit status`: jobs := the `atexit` handlers (last first), the finalisers, then end with
  `status`; the handler list is emptied (glibc takes each handler off the list before calling
  it, so a later `__cxa_finalize` finds none);
* the lazy-binding resolver (`_dl_runtime_resolve`, `ld.so`): from the PLT's two pushes
  (`GOT[1]`, the relocation index `j`), writes the `JUMP_SLOT`'s eager value into the slot and
  jumps to it with the argument and callee-saved registers and the caller's stack intact.

At the end (`.halt status`), the process records `status mod 256` and the bytes written to
fd 1: a prefix of `out`, all of it when `reliable` (`_IO_cleanup` flushes; flush errors do
not change the status).

When `main` returns, the bytes `stdout` still buffers (`World.pending`) are flushed into `out`
(glibc's `exit` flushes every stream; under reliable writes when it does so does not change
the bytes written).

**Trusted** (the assumptions a theorem over `proc` rests on): the `Open9` semantics, the loader
relation (`Dyn.Loader`), and these contracts: that glibc's functions, bound where the loader
model says, behave as stated, as one atomic step each.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Proc

open Silmaril.X86 (Word Byte MState State Reg sysv64)
open Silmaril.Process (Memory Access)
open Silmaril.X86.RelIsa (Res)
open Silmaril.X86.FnContract (AbiEntry AbiReturn retOf)

/-- A job the library still has to do when control reaches `gate`. -/
inductive Job where
  /-- Call `f` with `rdi, rsi, rdx = a1, a2, a3`. -/
  | call (f a1 a2 a3 : Word)
  /-- Call `f` with arguments the contract does not fix (finalisers, `atexit` handlers). -/
  | call0 (f : Word)
  /-- Call `main`; its `eax` is the exit status. -/
  | main (f argc argv envp : Word)
  /-- `main` has returned: exit with `eax`. -/
  | exitRax
  /-- Start `exit (status)`. -/
  | exit (status : Word)
  /-- End the process with `status`. -/
  | halt (status : Word)
  deriving DecidableEq, Repr

/-- The library's abstract state. -/
structure Ghost where
  jobs : List Job
  out : List Byte
  atexit : List Word
  done : Option (Nat × List Byte)
  /-- Bytes still to be read from stdin (unused by the contracts here). -/
  inp : List Byte := []
  /-- Bytes written to file descriptor 2 (`stderr` is unbuffered, so this is exact). -/
  err : List Byte := []
  /-- `malloc` requests the library has served (its allocation count, for the resource bound
  `Streams.AllocRoom`). -/
  allocs : Nat := 0
  /-- Bytes `malloc` has handed out. -/
  heap : Nat := 0
  /-- Streams `fopen` has opened (for the resource bound `Streams.OpenRoom`). -/
  files : Nat := 0
  /-- **The live heap blocks** (start, size), most recent first: `malloc` adds the block it
  returns, `free (p)` removes the block starting at `p` (`Streams.freeStep`). -/
  blocks : List (Nat × Nat) := []

structure PState where
  m : MState
  g : Ghost

/-- The imports with a contract. -/
inductive Fn where
  | puts | libcStartMain | cxaFinalize | exit
  /-- Another import, whose contract the world gives by name (`World.named`). -/
  | named (n : Name)
  deriving DecidableEq, Repr

/-- **The world**: the executable's image, what the loader bound, and the library's
parameters. -/
structure World where
  /-- Base and extent of the executable's image (end of its last `PT_LOAD`). -/
  base : Word
  size : Nat
  /-- `DT_INIT` then `DT_INIT_ARRAY`, as absolute addresses. -/
  inits : List Word
  /-- `DT_FINI_ARRAY` (last first) then `DT_FINI`, in the order `_dl_fini` calls them. -/
  finis : List Word
  /-- Where callbacks return to (inside the library). -/
  gate : Word
  /-- Lazy binding: the resolver's address, and for each `DT_JMPREL` index its slot (vaddr)
  and eager value; `none` under eager binding. -/
  lazy : Option (Word × List (Nat × Word))
  /-- The resolved entry points of the imports with a contract. -/
  fns : List (Word × Fn)
  /-- Writes to fd 1 do not fail. -/
  reliable : Bool
  /-- The contracts of the other imports (`Fn.named`), by name. Default: none (a call stops,
  so nothing is claimed about runs that make it). -/
  named : Name → PState → Res PState → Prop := fun _ _ r => r = .stop
  /-- The process's argument area (argv/envp strings and vectors, auxv), which the library
  never writes: kept by every library step, and not used for callback stacks. Default:
  empty. -/
  args : Nat → Prop := fun _ => False
  /-- The thread control block's words the program reads (the stack protector's guard at
  `%fs:0x28`), which the library never writes: kept by every library step, and not used for
  callback stacks. Default: empty. -/
  tls : Nat → Prop := fun _ => False
  /-- What the library guarantees of its own state when it enters `main` (stdio initialised:
  the streams `stdin`/`stdout`/`stderr` and the variables holding them). A per-program
  assumption on the library, like the contracts. Default: nothing. -/
  atMain : PState → Prop := fun _ => True
  /-- Output the library holds for file descriptor 1 but has not written yet (`stdout`'s
  buffer, as the library represents it), which `exit` flushes. Default: none. -/
  pending : PState → List Byte → Prop := fun _ p => p = []
  /-- What the library guarantees when it enters an exit handler or a finaliser (`Job.call0`):
  for example that the callback's stack lies above the library's streams. Default: nothing. -/
  atCall : PState → Prop := fun _ => True
  /-- What the library guarantees across a return to `gate` that runs an exit job, an exit
  handler or a finaliser (`Job.exitRax`, `Job.exit`, `Job.call0`), as a relation between the state
  at `gate` and the next one: for example that `stdout` and `stderr` keep their states until
  `close_stdout` runs. Default: nothing. -/
  atGate : PState → PState → Prop := fun _ _ => True

/-- `a` lies in the executable's image. -/
def World.InImage (W : World) (a : Nat) : Prop := W.base.toNat ≤ a ∧ a < W.base.toNat + W.size

instance (W : World) (a : Nat) : Decidable (W.InImage a) := inferInstanceAs (Decidable (_ ∧ _))

/-- What every library step keeps: the image, the argument area and the TCB words. -/
def World.Kept (W : World) (a : Nat) : Prop := W.InImage a ∨ W.args a ∨ W.tls a

/-- Bytes and permissions in `P` are unchanged (the mapping list elsewhere may change: the
library may `mmap`). -/
def Keeps (P : Nat → Prop) (m m' : Memory) : Prop :=
  ∀ a, P a → m'.bytes.get? a = m.bytes.get? a ∧ ∀ acc, m'.permits acc a = m.permits acc a

/-- `s` (no NUL) is a C string at `a`. -/
def CStr (mem : Memory) (a : Word) (s : List Byte) : Prop :=
  (∀ x ∈ s, x ≠ 0) ∧ mem.readBytes a.toNat (s.length + 1) = some (s ++ [0])

/-- A usable stack at `sp`: a page below it and the word at it readable and writable, outside
the executable's image, without wrapping. -/
def StackRoom (W : World) (mem : Memory) (sp : Word) : Prop :=
  4096 ≤ sp.toNat ∧ sp.toNat + 8 < 2 ^ 64 ∧
  ∀ a, sp.toNat - 4096 ≤ a → a < sp.toNat + 8 →
    mem.permits .read a = true ∧ mem.permits .write a = true ∧ ¬ W.Kept a

/-- The low 32 bits of a register. -/
def low32 (w : Word) : BitVec 32 := w.setWidth 32

/-- A return from a call entered at `s`: System V return, the image and the stack at and
above the entry `rsp` unchanged. -/
def Returns (W : World) (s t : PState) : Prop :=
  AbiReturn s.m.core s.m.memory t.m.core ∧
  Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) s.m.memory t.m.memory

/-- Entering a callback `f`: `rip = f`, a fresh aligned stack whose top word is `gate`, the
image and `fsBase` unchanged. -/
def Enters (W : World) (s t : PState) (f : Word) : Prop :=
  t.m.core.rip = f ∧ (t.m.core.read .rsp).toNat % 16 = 8 ∧
  t.m.memory.readBytes (t.m.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [W.gate]) ∧
  StackRoom W t.m.memory (t.m.core.read .rsp) ∧ Keeps W.Kept s.m.memory t.m.memory ∧
  t.m.core.fsBase = s.m.core.fsBase

/-- The library resumes at `gate` with the image and `fsBase` unchanged. -/
def AtGate (W : World) (s t : PState) : Prop :=
  t.m.core.rip = W.gate ∧ Keeps W.Kept s.m.memory t.m.memory ∧ t.m.core.fsBase = s.m.core.fsBase

/-- A contract step: under `pre`, every outcome is `ok` of a state satisfying `post`. -/
def Contract (pre : Prop) (post : PState → Prop) (r : Res PState) : Prop :=
  pre → ∃ t, r = .ok t ∧ post t

/-- **`puts`.** -/
def putsStep (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ ∃ str, CStr s.m.memory (s.m.core.read .rdi) str)
    fun t => Returns W s t ∧ ∃ str, CStr s.m.memory (s.m.core.read .rdi) str ∧
      t.g.jobs = s.g.jobs ∧ t.g.atexit = s.g.atexit ∧ t.g.done = none ∧ (t.g.inp = s.g.inp ∧ t.g.err = s.g.err) ∧
      ((t.g.out = s.g.out ++ str ++ [10] ∧ (low32 (t.m.core.read .rax)).msb = false) ∨
       (W.reliable = false ∧ ∃ p, p <+: str ++ [10] ∧ t.g.out = s.g.out ++ p ∧
         low32 (t.m.core.read .rax) = 0xffffffff#32))

/-- **`__libc_start_main (main, argc, argv, init, fini, rtld_fini, stack_end)`**. -/
def startMainStep (W : World) (s : PState) : Res PState → Prop :=
  let main := s.m.core.read .rdi
  let argc := (s.m.core.read .rsi).setWidth 32 |>.setWidth 64
  let argv := s.m.core.read .rdx
  let envp := argv + 8#64 * (argc + 1#64)
  Contract (AbiEntry s.m.core s.m.memory)
    fun t => AtGate W s t ∧
      t.g = { s.g with jobs := W.inits.map (fun f => .call f argc argv envp) ++
        [.main main argc argv envp] }

/-- **`__cxa_finalize (d)`**, when nothing is registered: it runs nothing and changes no memory. -/
def cxaFinalizeStep (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ s.g.atexit = [])
    fun t => Returns W s t ∧ t.g = s.g ∧ t.m.memory = s.m.memory

/-- **`exit (status)`**. -/
def exitStep (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory)
    fun t => AtGate W s t ∧ t.g = { s.g with jobs := [.exit (s.m.core.read .rdi)] }

/-- The jobs of `exit (status)`. -/
def exitJobs (W : World) (g : Ghost) (status : Word) : List Job :=
  g.atexit.reverse.map .call0 ++ W.finis.map .call0 ++ [.halt status]

/-- **The library at `gate`**: its next job. -/
def gateStep (W : World) (s : PState) (r : Res PState) : Prop :=
  match s.g.jobs with
  | [] => True
  | .call f a1 a2 a3 :: js => Contract True (fun t => Enters W s t f ∧
      t.m.core.read .rdi = a1 ∧ t.m.core.read .rsi = a2 ∧ t.m.core.read .rdx = a3 ∧
      t.g = { s.g with jobs := js }) r
  | .call0 f :: js => Contract True (fun t => Enters W s t f ∧ t.g = { s.g with jobs := js } ∧ W.atCall t ∧
      W.atGate s t) r
  | .main f argc argv envp :: js => Contract True (fun t => Enters W s t f ∧
      t.m.core.read .rdi = argc ∧ t.m.core.read .rsi = argv ∧ t.m.core.read .rdx = envp ∧
      t.g = { s.g with jobs := .exitRax :: js } ∧ W.atMain t) r
  | .exitRax :: _ => Contract True (fun t => ∃ p, W.pending s p ∧ AtGate W s t ∧
      t.g = { s.g with jobs := [.exit ((low32 (s.m.core.read .rax)).setWidth 64)], out := s.g.out ++ p } ∧
      W.atGate s t) r
  | .exit status :: _ => Contract True (fun t => AtGate W s t ∧
      t.g = { s.g with jobs := exitJobs W s.g status, atexit := [] } ∧ W.atGate s t) r
  | .halt status :: _ => Contract True (fun t => ∃ w, w <+: s.g.out ∧
      (W.reliable = true → w = s.g.out) ∧
      t.g = { s.g with jobs := [], done := some (status.toNat % 256, w) }) r

/-- What the lazy-binding resolver leaves for slot `e = (vaddr, value)`, from entry `s`. -/
def ResPost (W : World) (e : Nat × Word) (s t : PState) : Prop :=
  let sp := s.m.core.read .rsp
  t.m.core.rip = e.2 ∧ t.m.core.read .rsp = sp + 16#64 ∧
  (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rax, .rbx, .rbp, .r12, .r13, .r14, .r15],
    t.m.core.read r = s.m.core.read r) ∧
  Silmaril.X86.Ext.loadN t.m.memory (W.base + BitVec.ofNat 64 e.1) 8 = some e.2 ∧
  Keeps (fun a => ¬ ((W.base + BitVec.ofNat 64 e.1).toNat ≤ a ∧
      a < (W.base + BitVec.ofNat 64 e.1).toNat + 8) ∧ (W.Kept a ∨ (sp + 16#64).toNat ≤ a))
    s.m.memory t.m.memory ∧
  (∀ a acc, (W.base + BitVec.ofNat 64 e.1).toNat ≤ a →
    a < (W.base + BitVec.ofNat 64 e.1).toNat + 8 → t.m.memory.permits acc a = s.m.memory.permits acc a) ∧
  t.g = s.g ∧
  -- the stack page below the entry `rsp` and the two words it pops stay mapped as they were
  -- (the resolver writes there, it never unmaps or re-protects them)
  (∀ a acc, sp.toNat - 4096 ≤ a → a < sp.toNat + 16 →
    t.m.memory.permits acc a = s.m.memory.permits acc a)

/-- The resolver's precondition: the slot `e` is readable and writable (it is in the
executable's writable `.got.plt`). -/
def SlotRW (W : World) (e : Nat × Word) (s : PState) : Prop :=
  s.m.memory.Permitted .read (W.base + BitVec.ofNat 64 e.1).toNat 8 ∧
  s.m.memory.Permitted .write (W.base + BitVec.ofNat 64 e.1).toNat 8

/-- **The lazy-binding resolver**: `[rsp] = GOT[1]`, `[rsp + 8] = j`; it stores slot `j`'s
eager value and jumps to it with `rsp + 16` (`ResPost`). -/
def resolveStep (W : World) (slots : List (Nat × Word)) (s : PState) (r : Res PState) : Prop :=
  ∀ j, Silmaril.X86.Ext.loadN s.m.memory (s.m.core.read .rsp + 8#64) 8 = some (BitVec.ofNat 64 j) →
    ∀ e, slots[j]? = some e → Contract (SlotRW W e s) (ResPost W e s) r

def fnStep (W : World) : Fn → PState → Res PState → Prop
  | .puts => putsStep W
  | .libcStartMain => startMainStep W
  | .cxaFinalize => cxaFinalizeStep W
  | .exit => exitStep W
  | .named n => W.named n

/-- One step outside the executable's image. An address the model does not know stops. -/
def extStep (W : World) (s : PState) (r : Res PState) : Prop :=
  if s.m.core.rip = W.gate then gateStep W s r
  else match W.lazy with
    | some (res, slots) => if s.m.core.rip = res then resolveStep W slots s r else
        match W.fns.find? (·.1 == s.m.core.rip) with
        | some (_, f) => fnStep W f s r
        | none => r = .stop
    | none => match W.fns.find? (·.1 == s.m.core.rip) with
        | some (_, f) => fnStep W f s r
        | none => r = .stop

/-- **One step of the process.** An ended process stops; in the image, `Open9`; elsewhere,
the library. -/
def step (W : World) (s : PState) (r : Res PState) : Prop :=
  match s.g.done with
  | some _ => r = .stop
  | none =>
    if W.InImage s.m.core.rip.toNat then
      match Silmaril.X86.Open9.step s.m with
      | some m' => r = .ok ⟨m', s.g⟩
      | none => r = .stop
    else extStep W s r

/-- **The process machine.** -/
def proc (W : World) : Silmaril.X86.RelIsa PState where
  core s := s.m.core
  mem s := s.m.memory
  upd s c m := { s with m := ⟨c, m⟩ }
  core_upd _ _ _ := rfl
  mem_upd _ _ _ := rfl
  upd_self _ := rfl
  live _ := True
  step := step W
  live_step _ _ := trivial

/-- The process has ended with `status`, having written `w` to fd 1. -/
def Ended (status : Nat) (P : List Byte → Prop) (s : PState) : Prop :=
  ∃ w, s.g.done = some (status, w) ∧ P w

/-- Every entry of an instruction listing (offset, instruction, length) decodes as listed. -/
def listingOk (code : List Byte) (L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)) : Bool :=
  L.all fun e => decide (Silmaril.X86.Open9.decode ((code.drop e.1).take e.2.2) = some (e.2.1, e.2.2)) &&
    decide (e.1 + e.2.2 ≤ code.length)

/-- The memory after pushing `v` with stack pointer `sp` (as `pushWord` writes it). -/
def pushMem (m : Memory) (sp v : Word) : Memory :=
  ⟨m.regions, Memory.install m.bytes (sp - 8#64).toNat (Silmaril.Machine.LittleEndian.encodeWords [v])⟩

end Silmaril.Elf.Link.Dyn.Proc
