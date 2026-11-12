module

public import Silmaril.Libc.AllocElf.Defs
public import Silmaril.Elf.Link.Dyn.Loader.Defs
public import Silmaril.X86.Str9.Thms

/-!
# A concrete loading model for the allocator rows

`AllocElf.LoadModel` is the trusted base of an allocator row. This module gives one instance,
`model E`, for an environment `E` (the rest of the process), and the row statement
`Row s F S`: **for every environment whose bound imports satisfy their named contracts, `F` is
POSIX-safe at `s` in `model E`**.

## The process (`LState`)

An x86-64 machine state (`MState`: core and memory) with a ghost set `fr` of **foreign** bytes
(the memory of the rest of the process). The machine never changes `fr`; the client may extend it
with memory it maps itself.

## The machine (`mach E`)

One step from a state whose `rip` is an address `w` with `E.call w = some f` (a function of the
rest of the process: an import's definition) is one atomic step of `f`, from its System V entry
to its return. Every other step is `Silmaril.X86.Str9.step` (the open x86-64 machine with the
string forms), an undecoded instruction being an explicit stop.

## The started states (`Started E F b x`)

The loader has placed `F` at `b`, with **eager binding** (`LD_BIND_NOW`), as ld.so does it:

* `b` is page-aligned (`Dyn.PageBase`), `F` is placed (`ElfBind.Placement`) and its read-only
  segments are in memory (`ElfBind.RoLoaded`);
* **the image** (`Dyn.ImageOk`) of every `PT_LOAD` segment: mapped at `b + p_vaddr` with its
  `PF_R`/`PF_W`/`PF_X` (`PT_GNU_RELRO` pages read-only), each byte the file's byte, `0` in
  `.bss`, or the relocated value of a slot of `slots E F`:
  - `R_X86_64_RELATIVE` and each `DT_RELR` position: `b` plus the addend (the file's word);
  - `GLOB_DAT`, `JUMP_SLOT`, `R_X86_64_64`: the reference's definition **in `F` itself** if
    `F`'s `.dynsym` defines it (ld.so's lookup, `lookupDef`: `F` comes first in the search scope
    for the names it defines), else **the address `E.addr r` the environment bound it to**,
    else `0` for a weak reference (a strong reference without a binding has no value: no state
    starts);
  - `IRELATIVE` and IFUNC definitions: the environment's choice `E.ifn`;
  - `TPOFF64`: the offset `E.tpoff` of `F`'s TLS block from the thread pointer, plus the
    symbol's value and the addend;
  - any other kind: unconstrained;
* **the thread**: `fsBase` is the thread pointer, its first word points to itself (the TCB), and
  `F`'s TLS block at `fsBase + E.tpoff` is mapped readable and writable and holds the `PT_TLS`
  image (its file bytes, then zeros);
* **errno**: the calling thread's `errno` (`E.errno`, 4 bytes) is readable and writable, outside
  `F`'s image;
* the environment's functions are not in `F`'s image;
* **foreign memory**: exactly the mapped bytes outside `F`'s image and the `errno` word.

## Imports (`contracts`, `Env.Ok`)

`contracts E.errno n` is the **named contract** of the imported function `n`, when there is
one: entry conditions (beyond System V's) and a postcondition (a System V return, `fsBase`
kept, and what it does to memory: in every case only its own scratch stack below `rsp`
besides what is listed). The environment hypothesis `E.Ok` says that every import bound to an
address `w` and having a named contract is, at `w`, a function satisfying it (`Impl.Sat`). An
import without a named contract (`abort`, `pthread_create`, `dlsym`, `syscall`, glibc's `_dl_*`,
…) is unconstrained: any behaviour, a stop included, so a row whose valid calls reach it is not
provable. The contracts describe a **single-threaded** process (mutex operations succeed) with
**no environment variables** (`getenv`, `secure_getenv` return `NULL`).

## What is not modelled (no claim is made where it matters)

Constructors (`DT_INIT`, `DT_INIT_ARRAY`) need not have run: the started state is the image.
Threads and signals; TLS relocations other than `TPOFF64`; `COPY`; symbol interposition in the
names `F` defines; which implementation an IFUNC selects (`E.ifn` is arbitrary); x86
instructions outside `Str9` (they stop).
-/

@[expose] public section

namespace Silmaril.Libc.AllocLoad

open Silmaril.X86 (Word Byte State MState)
open Silmaril.X86.Link (Blob)
open Silmaril.Process (Memory)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.X86.RelIsa (Res)
open Silmaril.Elf.Link.DynElf (Rd)
open Silmaril.Elf.Link.DynElf.Elf (DynInfo Ref Rela Phdr)
open Silmaril.Elf.Link.ElfBind (Placement RoLoaded InImage leBytes)
open Silmaril.Elf.Link.Dyn (Obj Val finfo frun defVal ImageOk PageBase fileWord)
open Silmaril.Libc.AllocElf (LoadModel Scratch budget)

/-! ## Imported functions and their contracts -/

/-- **A bound function**, as one atomic step from its System V entry to its outcome. -/
abbrev Impl := MState → Res MState → Prop

/-- **A named contract** of an imported function: an entry condition (beyond System V's) and a
postcondition between the entry and the return state. -/
structure ImpSpec where
  pre : MState → Prop
  post : MState → MState → Prop

/-- **`f` satisfies `C`**: from every System V entry meeting `C.pre` it does not stop, and every
outcome is a System V return, with `fsBase` kept, satisfying `C.post`. -/
def Impl.Sat (f : Impl) (C : ImpSpec) : Prop :=
  ∀ x, AbiEntry x.core x.memory → C.pre x →
    ¬ f x .stop ∧ ∀ y, f x (.ok y) →
      AbiReturn x.core x.memory y.core ∧ y.core.fsBase = x.core.fsBase ∧ C.post x y

/-- An argument or result register, as a number. -/
def reg (x : MState) (r : Silmaril.X86.Reg) : Nat := (x.core.read r).toNat

/-- `[p, p + n)`. -/
def In (p n a : Nat) : Prop := p ≤ a ∧ a < p + n

/-- The bytes `[p, p + n)` are readable (`acc := .read`) or writable. -/
def Allowed (m : Memory) (acc : Silmaril.Process.Access) (p n : Nat) : Prop :=
  ∀ a, In p n a → m.permits acc a = true

/-- **The memory effect of a call**: the permissions are unchanged, and the bytes change only in
the callee's scratch stack and where `W` says. -/
def WritesOnly (x y : MState) (W : Nat → Prop) : Prop :=
  (∀ a acc, y.memory.permits acc a = x.memory.permits acc a) ∧
    ∀ a, ¬ Scratch (reg x .rsp) a → ¬ W a → y.memory.bytes.get? a = x.memory.bytes.get? a

/-- The 32-bit result (`int`). -/
def ret32 (y : MState) : Nat := reg y .rax % 2 ^ 32

/-- **A pure call**: any result, no memory effect but its scratch stack. -/
def pureC : ImpSpec := ⟨fun _ => True, fun x y => WritesOnly x y fun _ => False⟩

/-- **A call that returns `0`** (an `int` or a pointer) without a memory effect. -/
def zeroC : ImpSpec := ⟨fun _ => True, fun x y => reg y .rax = 0 ∧ WritesOnly x y fun _ => False⟩

/-- **A call that writes `n` bytes at the argument `r`** (a writable object there). -/
def writesC (r : Silmaril.X86.Reg) (n : Nat) (ok0 : Bool) : ImpSpec :=
  ⟨fun x => Allowed x.memory .write (reg x r) n,
   fun x y => (ok0 = true → ret32 y = 0) ∧ WritesOnly x y (In (reg x r) n)⟩

/-- `memset (d, c, n)`: `d`'s `n` bytes are `c`, `d` is returned. -/
def memsetC : ImpSpec :=
  ⟨fun x => Allowed x.memory .write (reg x .rdi) (reg x .rdx),
   fun x y => reg y .rax = reg x .rdi ∧ WritesOnly x y (In (reg x .rdi) (reg x .rdx)) ∧
     ∀ i < reg x .rdx, y.memory.bytes.get? (reg x .rdi + i) = some (BitVec.ofNat 8 (reg x .rsi))⟩

/-- `memcpy (d, s, n)` (`disjoint`) and `memmove`: `d` gets `s`'s `n` bytes, `d` is returned. -/
def copyC (disjoint : Bool) : ImpSpec :=
  ⟨fun x => Allowed x.memory .write (reg x .rdi) (reg x .rdx) ∧
     Allowed x.memory .read (reg x .rsi) (reg x .rdx) ∧
     (disjoint = true → reg x .rdi + reg x .rdx ≤ reg x .rsi ∨ reg x .rsi + reg x .rdx ≤ reg x .rdi),
   fun x y => reg y .rax = reg x .rdi ∧ WritesOnly x y (In (reg x .rdi) (reg x .rdx)) ∧
     ∀ i < reg x .rdx, y.memory.bytes.get? (reg x .rdi + i) = x.memory.bytes.get? (reg x .rsi + i)⟩

/-- `MAP_FAILED`, `-1` as a word. -/
def mapFailed : Nat := 2 ^ 64 - 1

/-- `prot`'s bit for an access (`PROT_READ = 1`, `PROT_WRITE = 2`, `PROT_EXEC = 4`). -/
def protAllows (prot : Nat) : Silmaril.Process.Access → Bool
  | .read => prot % 2 == 1
  | .write => prot / 2 % 2 == 1
  | .execute => prot / 4 % 2 == 1

/-- Outside `R`, permissions are kept, and bytes too except in the scratch stack. -/
def KeepsOutside (x y : MState) (R : Nat → Prop) : Prop :=
  ∀ a, ¬ R a → (∀ acc, y.memory.permits acc a = x.memory.permits acc a) ∧
    (¬ Scratch (reg x .rsp) a → y.memory.bytes.get? a = x.memory.bytes.get? a)

/-- The page-rounded length. -/
def pages (n : Nat) : Nat := (n + 4095) / 4096 * 4096

/-- **`mmap (hint, len, prot, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)`** (no `MAP_FIXED`): either
`MAP_FAILED` and nothing changes, or a page-aligned `p ≠ 0` whose `len` bytes (rounded up to pages)
were unmapped and are now zero with the permissions of `prot`. -/
def mmapC : ImpSpec :=
  ⟨fun x => 0 < reg x .rsi ∧ (reg x .rcx / 0x20) % 2 = 1 ∧ (reg x .rcx / 2) % 2 = 1 ∧
     (reg x .rcx / 0x10) % 2 = 0,
   fun x y =>
     (reg y .rax = mapFailed ∧ KeepsOutside x y fun _ => False) ∨
     (let p := reg y .rax; let n := pages (reg x .rsi)
      p ≠ 0 ∧ p % 4096 = 0 ∧ p + n < 2 ^ 64 ∧
        (∀ a, In p n a → ∀ acc, x.memory.permits acc a = false) ∧
        (∀ a, In p n a → (∀ acc, y.memory.permits acc a = protAllows (reg x .rdx) acc) ∧
          y.memory.bytes.get? a = some 0#8) ∧
        KeepsOutside x y (In p n))⟩

/-- **`munmap (p, len)`**: `0` and the range unmapped, or `-1` and nothing changes. -/
def munmapC : ImpSpec :=
  ⟨fun x => reg x .rdi % 4096 = 0,
   fun x y => (ret32 y = 0 ∧ (∀ a, In (reg x .rdi) (pages (reg x .rsi)) a → ∀ acc,
       y.memory.permits acc a = false) ∧ KeepsOutside x y (In (reg x .rdi) (pages (reg x .rsi)))) ∨
     (ret32 y = 2 ^ 32 - 1 ∧ KeepsOutside x y fun _ => False)⟩

/-- **`mprotect (p, len, prot)`** of mapped pages: `0` and the range has `prot`'s permissions,
the bytes kept; or `-1` and nothing changes. -/
def mprotectC : ImpSpec :=
  ⟨fun x => reg x .rdi % 4096 = 0,
   fun x y => (ret32 y = 0 ∧ (∀ a, In (reg x .rdi) (pages (reg x .rsi)) a →
       (∀ acc, y.memory.permits acc a = protAllows (reg x .rdx) acc) ∧
         y.memory.bytes.get? a = x.memory.bytes.get? a) ∧
       KeepsOutside x y (In (reg x .rdi) (pages (reg x .rsi)))) ∨
     (ret32 y = 2 ^ 32 - 1 ∧ KeepsOutside x y fun _ => False)⟩

/-- **`madvise (p, len, advice)`**: `0` or `-1`; the bytes of the range may change (for
`MADV_DONTNEED`, `MADV_FREE`), the permissions are kept. -/
def madviseC : ImpSpec :=
  ⟨fun x => reg x .rdi % 4096 = 0,
   fun x y => (ret32 y = 0 ∨ ret32 y = 2 ^ 32 - 1) ∧
     WritesOnly x y (In (reg x .rdi) (pages (reg x .rsi)))⟩

/-- **`__errno_location ()`**: the calling thread's `errno`. -/
def errnoC (errno : Nat) : ImpSpec :=
  ⟨fun _ => True, fun x y => reg y .rax = errno ∧ WritesOnly x y fun _ => False⟩

/-- **The named contracts** of imported functions (by name; versions are not distinguished).
`none`: no contract (any behaviour). -/
def contractList (errno : Nat) : List (String × ImpSpec) :=
  [("memset", memsetC), ("__memset_chk", memsetC),
   ("memcpy", copyC true), ("__memcpy_chk", copyC true), ("memmove", copyC false),
   ("mmap", mmapC), ("munmap", munmapC), ("mprotect", mprotectC), ("madvise", madviseC),
   ("__errno_location", errnoC errno),
   ("getenv", zeroC), ("secure_getenv", zeroC),
   ("pthread_mutex_init", writesC .rdi 40 true), ("pthread_mutex_destroy", writesC .rdi 40 true),
   ("pthread_mutex_lock", writesC .rdi 40 true), ("pthread_mutex_trylock", writesC .rdi 40 true),
   ("pthread_mutex_unlock", writesC .rdi 40 true),
   ("pthread_mutexattr_init", writesC .rdi 4 true), ("pthread_mutexattr_destroy", writesC .rdi 4 true),
   ("pthread_mutexattr_settype", writesC .rdi 4 true),
   ("pthread_key_create", writesC .rdi 4 true),
   ("pthread_setspecific", pureC), ("pthread_key_delete", pureC), ("pthread_self", pureC),
   ("clock_gettime", writesC .rsi 16 true), ("gettimeofday", writesC .rdi 16 true),
   ("getrusage", writesC .rsi 144 true), ("sigfillset", writesC .rdi 128 true),
   ("getpid", pureC), ("sysconf", pureC), ("sched_getcpu", pureC), ("sched_yield", pureC),
   ("__sched_cpucount", pureC), ("prctl", pureC), ("__cxa_atexit", pureC),
   ("__register_atfork", pureC),
   ("strlen", pureC), ("strcmp", pureC), ("strncmp", pureC), ("strchr", pureC),
   ("memchr", pureC), ("strstr", pureC)]

/-- The named contract of a reference, by its name. -/
def contracts (errno : Nat) (r : Ref) : Option ImpSpec :=
  ((contractList errno).find? fun e => Silmaril.Elf.Link.DynElf.nm e.1 == r.name).map (·.2)

/-! ## The environment -/

/-- **The rest of the process**, as the allocator sees it. -/
structure Env where
  /-- Where ld.so bound each reference `F` does not define (`none`: unbound). -/
  addr : Ref → Option Word
  /-- What an IFUNC resolver at an address returns. -/
  ifn : Word → Option Word
  /-- The functions of the rest of the process, by entry address. -/
  call : Word → Option Impl
  /-- The offset of `F`'s TLS block from the thread pointer (`TPOFF64`). -/
  tpoff : Word
  /-- The calling thread's `errno`. -/
  errno : Nat

/-- **The import hypothesis**: every bound reference with a named contract is bound to a function
satisfying it. -/
def Env.Ok (E : Env) : Prop :=
  ∀ r w C, E.addr r = some w → contracts E.errno r = some C → ∃ f, E.call w = some f ∧ f.Sat C

/-! ## The process and the machine -/

/-- **A process state**: the machine state and the foreign bytes. -/
structure LState where
  m : MState
  fr : Nat → Prop

/-- The views: core and memory of the machine state; `upd` keeps the foreign bytes. -/
def views : Silmaril.X86.RelIsa.Views LState where
  core s := s.m.core
  mem s := s.m.memory
  upd s c m := ⟨⟨c, m⟩, s.fr⟩
  core_upd _ _ _ := rfl
  mem_upd _ _ _ := rfl
  upd_self _ := rfl
  live _ := True

/-- A step's outcome on the machine state, the foreign bytes kept. -/
def lift (fr : Nat → Prop) : Res MState → Res LState
  | .ok y => .ok ⟨y, fr⟩
  | .stop => .stop

/-- **The machine** (module doc): the environment's functions as atomic steps, `Str9` elsewhere. -/
def mach (E : Env) : Silmaril.X86.RelIsa LState where
  toViews := views
  step s r := match E.call s.m.core.rip with
    | some f => ∃ o, f s.m o ∧ r = lift s.fr o
    | none => r = lift s.fr (match Silmaril.X86.Str9.step s.m with
        | some y => .ok y
        | none => .stop)
  live_step _ _ := trivial

/-! ## The loaded image -/

/-- `DT_RELRSZ`. -/
def DT_RELRSZ : Nat := 35

/-- The positions a `DT_RELR` table relocates, from its entries (an even entry is an address,
an odd one a bitmap of the 63 words after the last position). -/
def relrDecode : List Nat → Nat → List Nat
  | [], _ => []
  | w :: ws, at_ =>
    if w % 2 = 0 then w :: relrDecode ws (w + 8)
    else ((List.range 63).filter fun j => w / 2 ^ (j + 1) % 2 = 1).map (fun j => at_ + 8 * j) ++
      relrDecode ws (at_ + 63 * 8)

/-- The `DT_RELR` positions of `F`. -/
def relrs (F : Blob) (i : DynInfo) : Option (List Nat) :=
  match i.tagOff Silmaril.Elf.Link.DynElf.Elf.DT_RELR, i.tag DT_RELRSZ with
  | some o, some sz => (frun F ((List.range (sz / 8)).mapM fun k =>
      Silmaril.Elf.Link.DynElf.Elf.u64 (o + 8 * k))).map (relrDecode · 0)
  | _, _ => some []

/-- The value of a reference: `F`'s own definition, else the environment's binding, else `0` for
a weak reference. -/
def bindE (E : Env) (F : Blob) (i : DynInfo) (r : Ref) (plt : Bool) : Option Val := do
  match ← frun F (Silmaril.Elf.Link.DynElf.Elf.lookupDef i r plt) with
  | some d => pure (defVal (0, d))
  | none => match E.addr r with
    | some w => pure (.abs w.toNat)
    | none => if r.weak then some (.abs 0) else none

/-- A value plus an addend. -/
def plusV (v : Val) (a : Int) : Val :=
  match v with
  | .addr k off => .addr k (off + a)
  | .abs n => .abs (((n : Int) + a).toNat % 2 ^ 64)
  | v => if a = 0 then v else .any

/-- The symbol value of a dynamic symbol (`0` for index `0`). -/
def symValue (F : Blob) (i : DynInfo) (k : Nat) : Option Nat :=
  if k = 0 then some 0 else (frun F (Silmaril.Elf.Link.DynElf.Elf.sym i k)).map (·.value)

/-- **The eager value of a relocation** (module doc). -/
def relocE (E : Env) (F : Blob) (i : DynInfo) (r : Rela) : Option Val :=
  if r.kind = 8 then some (.addr 0 r.addend)
  else if r.kind = 37 then some (.ifunc 0 r.addend)
  else if r.kind = 6 ∨ r.kind = 7 ∨ r.kind = 1 then do
    let ref ← frun F (Silmaril.Elf.Link.DynElf.Elf.refOf i r.sym)
    let v ← bindE E F i ref (r.kind = 7)
    pure (plusV v (if r.kind = 1 then r.addend else 0))
  else if r.kind = 18 then do
    let v ← symValue F i r.sym
    pure (.abs ((((E.tpoff.toNat + v : Nat) : Int) + r.addend).toNat % 2 ^ 64))
  else some .any

/-- **The slot table** with eager binding: `DT_RELA`, `DT_JMPREL` and the `DT_RELR` positions. -/
def slots (E : Env) (F : Blob) (i : DynInfo) : Option (List (Nat × Val)) := do
  let a ← frun F (Silmaril.Elf.Link.DynElf.Elf.relaTable i Silmaril.Elf.Link.DynElf.Elf.DT_RELA
    ((i.tag Silmaril.Elf.Link.DynElf.Elf.DT_RELASZ).getD 0 / 24))
  let j ← frun F (Silmaril.Elf.Link.DynElf.Elf.relaTable i Silmaril.Elf.Link.DynElf.Elf.DT_JMPREL
    ((i.tag Silmaril.Elf.Link.DynElf.Elf.DT_PLTRELSZ).getD 0 / 24))
  let ra ← (a ++ j).mapM fun r => (relocE E F i r).map fun v => (r.off, v)
  let rr ← relrs F i
  let rw ← rr.mapM fun p => (fileWord F i p).map fun w => (p, Val.addr 0 w)
  pure (rw ++ ra)

/-- **The TLS block and the TCB** (module doc). -/
def TlsOk (F : Blob) (i : DynInfo) (tp tpoff : Word) (mem : Memory) : Prop :=
  mem.readBytes tp.toNat 8 = some (leBytes tp.toNat 8) ∧
  ∀ ph ∈ i.phs, ph.kind = 7 → ∀ k < ph.memsz,
    let a := (tp + tpoff + BitVec.ofNat 64 k).toNat
    mem.permits .read a = true ∧ mem.permits .write a = true ∧
      mem.bytes.get? a = (if k < ph.filesz then
        (frun F (Silmaril.Elf.Link.DynElf.Elf.u8 (ph.off + k))).map (BitVec.ofNat 8) else some 0#8)

/-- A byte is mapped (some permission). -/
def Mapped (mem : Memory) (a : Nat) : Prop :=
  mem.permits .read a = true ∨ mem.permits .write a = true ∨ mem.permits .execute a = true

/-- **The started states** (module doc). -/
def Started (E : Env) (F : Blob) (b : Word) (s : LState) : Prop :=
  PageBase [b] ∧ Placement F b ∧ RoLoaded F b s.m.memory ∧
  (∃ i D T, finfo F = some i ∧ slots E F i = some D ∧
    D.mapM (fun e => (e.2.word [b] E.ifn 0).map fun w => (e.1, w)) = some T ∧
    ImageOk ⟨F, b⟩ i T s.m.memory ∧ TlsOk F i s.m.core.fsBase E.tpoff s.m.memory) ∧
  Allowed s.m.memory .read E.errno 4 ∧ Allowed s.m.memory .write E.errno 4 ∧
  (∀ a, In E.errno 4 a → ¬ InImage F b a) ∧
  (∀ w, E.call w ≠ none → ¬ InImage F b w.toNat) ∧
  (∀ a, s.fr a ↔ Mapped s.m.memory a ∧ ¬ InImage F b a ∧ ¬ In E.errno 4 a)

/-- **The client's steps between calls** (`AllocElf.LoadModel.Client`): the owned bytes keep their
values, permissions and ownership; `fsBase` is kept; bytes change only where they were writable;
permissions change only on foreign bytes; and newly foreign bytes were unmapped (memory the client
mapped itself). -/
def Client (own : Nat → Prop) (s t : LState) : Prop :=
  t.m.core.fsBase = s.m.core.fsBase ∧
  (∀ a, own a → t.m.memory.bytes.get? a = s.m.memory.bytes.get? a ∧
    (∀ acc, t.m.memory.permits acc a = s.m.memory.permits acc a) ∧ (t.fr a ↔ s.fr a)) ∧
  (∀ a, s.m.memory.permits .write a = false → t.m.memory.bytes.get? a = s.m.memory.bytes.get? a) ∧
  (∀ a acc, t.m.memory.permits acc a ≠ s.m.memory.permits acc a → t.fr a) ∧
  (∀ a, s.fr a → t.fr a) ∧
  (∀ a, t.fr a → ¬ s.fr a → ¬ Mapped s.m.memory a)

/-- **The loading model at environment `E`**. -/
def model (E : Env) : LoadModel where
  σ := LState
  mach := mach E
  Started := Started E
  foreign s a := s.fr a
  Client := Client
  started_elf _ _ _ h := ⟨h.2.1, h.2.2.1⟩

/-! ## The rows -/

/-- **An allocator row at the concrete loading model**: for every environment whose bound imports
satisfy their named contracts, `F` is POSIX-safe at `s`. -/
def Row (s : Silmaril.Libc.AllocSig.Sig) (F : Blob) (S : Silmaril.Libc.AllocElf.Syms) : Prop :=
  ∀ E : Env, E.Ok → Silmaril.Libc.AllocElf.PosixSafe (model E) s F S

end Silmaril.Libc.AllocLoad
