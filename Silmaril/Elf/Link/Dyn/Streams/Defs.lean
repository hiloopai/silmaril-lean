module

public import Silmaril.Elf.Link.Dyn.Imports.Defs

/-! # stdio streams: an abstract representation and the contracts over it

glibc's `FILE` is the library's private object, except for the fields a C program reads or
writes **inline** (macros of `<stdio.h>`, as gnulib and coreutils compile them):

* `_flags` (offset `0x0`, a 32-bit `int`): bit 4 `_IO_EOF_SEEN`, bit 5 `_IO_ERR_SEEN` (`feof`,
  `ferror`, `feof_unlocked`, `ferror_unlocked`);
* `_IO_write_ptr` (`0x28`) and `_IO_write_end` (`0x30`): `putc_unlocked (c, f)` stores `c` at
  `_IO_write_ptr` and increments it when it is below `_IO_write_end`, and calls
  `__overflow (f, c)` otherwise.

`StreamRep` is a **loose** model in the style of `ShaRep`: the library chooses a predicate
`file mem f st` ("the `FILE` at `f` is the stream `st`") and a footprint `foot mem f` of the
bytes it owns for that stream (the `FILE` object and its buffer). The client relies only on the
laws listed as fields: locality, the layout of the two inline fields, and the effect of an
inline `putc`. The stream state `St` records the descriptor, the unread input with whether
reading past it fails (an I/O error) or reaches end of file, the `EOF`/`ERR` indicators, and
the output accepted but not yet written (`buf`).

**Output.** For `stdout`, the bytes handed to the stream are `g.out ++ st.buf`: `Ghost.out` is
what has reached file descriptor 1, the rest is buffered. Output functions append to that
concatenation (the split, i.e. when the library writes, is left open), and `fclose` writes the
buffer out (a prefix of it if writes may fail). This agrees with `puts` of `Proc` when the
buffer is empty.

**Input.** A stream opened by `fopen` reads the file system of the world (`fs`, the oracle of
`Silmaril.Apps.Sha256sum.World`): `.ok data` gives `data` then end of file; `.readErr e pre`
gives `pre` then an error.

**Frames.** Every contract returns with `LibRet E W fp`: the System V return keeping the
image, argument area and caller stack except `fp`, the stack guard, every *mapped, non-private*
byte outside `fp`, the permissions of the stack below it (`StackPerm`), and private memory (`StreamRep.priv`, which contains every stream's
footprint) grows only into unmapped memory. Stream calls name no `fp` (only `fread`'s
destination): a `FILE` and its buffer are never in the client's image, arguments or stack. Calls also keep the streams they do not name
(`OthersKept`). `malloc` returns memory that was private or unmapped (`Fresh`), so a client's
data never aliases it, and records it in `Ghost.blocks`; `free` writes only the block it releases
(`FreeRet`).
The contracts of `Imports` get the same frame through `framed`.

The contracts: `fopenStep`, `freadStep` (`fread_unlocked`; `freadChkStep`:
`__fread_unlocked_chk`), `fcloseStep`, `fflushStep`, `fwriteStep` (`fwrite_unlocked`),
`overflowStep` (`__overflow`), `fpendingStep` (`__fpending`), `filenoStep`, `freadingStep`
(`__freading`), `lseekStep`, `printfHexStep` (`__printf_chk (flag, "%02x", b)`), `errorStep`
(`error`; its message goes to `stderr`, which this model does not observe), `fadviseStep`,
`getoptNoneStep` (`getopt_long` on an argument vector without options), `setvbufStep`,
`strrchrStep`, `strncmpStep`, `mallocStep`, `freeStep`. `shaContracts` is the table by name.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Streams

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.RelIsa (Res)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.X86.Ext (loadN)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Imports

/-- A stream's state. -/
structure St where
  fd : Nat
  /-- Opened for reading (`__freading`). -/
  reading : Bool
  /-- Bytes not yet read. -/
  rd : List Byte
  /-- Reading past `rd` fails with an I/O error (instead of reaching end of file). -/
  fail : Bool
  eof : Bool
  err : Bool
  /-- Output accepted but not yet written to `fd`. -/
  buf : List Byte

/-- **The library's representation of streams**, with the laws a client may use. -/
structure StreamRep where
  file : Memory → Word → St → Prop
  /-- The bytes the stream at `f` owns (its `FILE` object and buffer). -/
  foot : Memory → Word → Nat → Prop
  /-- The library's private memory (its streams, heap metadata, …): see `LibRet`. -/
  priv : Memory → Nat → Prop
  foot_priv : ∀ m f st a, file m f st → foot m f a → priv m a
  /-- Streams live below `lo` (the stack is above it). -/
  lo : Nat
  foot_lo : ∀ m f st a, file m f st → foot m f a → a < lo
  /-- Private memory lies below `lo` (the stack is the client's). -/
  priv_lo : ∀ m a, priv m a → a < lo
  /-- Private memory is a matter of the memory below `lo`. -/
  priv_local : ∀ m m' : Memory, (∀ a, a < lo → m'.bytes.get? a = m.bytes.get? a ∧
    ∀ acc, m'.permits acc a = m.permits acc a) → priv m' = priv m
  /-- Which memory is private is determined by the private memory itself (a program store to
  non-private memory leaves it as it was). -/
  priv_keep : ∀ m m' : Memory, Keeps (priv m) m m' → priv m' = priv m
  /-- Only the footprint matters (and it is determined by it). -/
  local_ : ∀ m m' f st, Keeps (foot m f) m m' → file m f st → file m' f st ∧ foot m' f = foot m f
  /-- `_flags` holds the indicators. -/
  flags : ∀ m f st, file m f st → ∃ fl : Word, loadN m f 4 = some fl ∧
    fl.getLsbD 4 = st.eof ∧ fl.getLsbD 5 = st.err ∧ fl.getLsbD 8 = false
  /-- The low byte of `_flags` (what `test byte [f], mask` reads) carries the same two bits. -/
  flags1 : ∀ m f st, file m f st → ∃ fl : Word, loadN m f 1 = some fl ∧
    fl.getLsbD 4 = st.eof ∧ fl.getLsbD 5 = st.err ∧ fl.toNat < 256
  /-- The two write pointers are readable, and `[f, f+0x38)` is owned. -/
  ptrs : ∀ m f st, file m f st → (∃ p, loadN m (f + 0x28#64) 8 = some p) ∧
    (∃ e, loadN m (f + 0x30#64) 8 = some e) ∧ ∀ a, f.toNat ≤ a → a < f.toNat + 0x38 → foot m f a
  /-- **Inline `putc`**: below `_IO_write_end`, the byte at `_IO_write_ptr` is owned and
  writable, and storing `c` there and advancing the pointer appends `c` to the buffer. -/
  putc : ∀ m f st p e (c : Byte), file m f st → loadN m (f + 0x28#64) 8 = some p →
    loadN m (f + 0x30#64) 8 = some e → p.toNat < e.toNat →
    foot m f p.toNat ∧ m.Permitted .write p.toNat 1 ∧ m.Permitted .write (f + 0x28#64).toNat 8 ∧
    ∀ m' : Memory, Keeps (fun a => foot m f a ∧ a ≠ p.toNat ∧
        ¬ ((f + 0x28#64).toNat ≤ a ∧ a < (f + 0x28#64).toNat + 8)) m m' →
      m'.regions = m.regions →
      loadN m' p 1 = some (c.setWidth 64) → loadN m' (f + 0x28#64) 8 = some (p + 1#64) →
      file m' f { st with buf := st.buf ++ [c] }

/-- The `ERR` and `EOF` bits a program tests (`ferror`/`feof`). -/
def St.hasErr (st : St) : Bool := st.err

/-! ## The process-level parameters -/

/-- What a run of `sha256sum` assumes of the library's state beyond the contracts: the
streams, the address of `stdout`'s `FILE`, the file system, and `optind`'s address. -/
structure Env where
  S : StreamRep
  stdoutF : Word
  stderrF : Word
  fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult
  optindA : Word
  /-- The library does not run out of resources (an assumption on the run, like
  `World.reliable`: with `false`, `malloc` and `fopen` may fail with `NULL`). -/
  allocOk : Bool := true
  /-- Where the main thread's `errno` lives (the library's thread-local storage). -/
  errnoA : Word := 0
  /-- **Resource bounds** (world parameters, no defaults): while `main` runs, the library serves
  `maxAllocs` `malloc` requests of `maxHeap` bytes in total, and opens `maxOpen` streams of files
  of at most `maxFile` bytes. Beyond them `malloc`/`fopen` may return `NULL`. -/
  maxAllocs : Nat
  maxHeap : Nat
  maxOpen : Nat
  maxFile : Nat

/-- `stdout` is the stream `st` and has handed `g.out ++ st.buf` in total. -/
def StdoutIs (E : Env) (m : Memory) (st : St) : Prop := E.S.file m E.stdoutF st ∧ st.fd = 1

/-- Machine bytes to specification bytes and back. -/
def toSpec (l : List Byte) : Silmaril.Apps.Sha256sum.Bytes := l.map UInt8.ofBitVec
def ofSpec (l : Silmaril.Apps.Sha256sum.Bytes) : List Byte := l.map UInt8.toBitVec

/-- What reading a path opens. -/
def openedSt (r : Silmaril.Apps.Sha256sum.ReadResult) (fd : Nat) : Option St :=
  match r with
  | .ok data => some ⟨fd, true, ofSpec data, false, false, false, []⟩
  | .readErr _ pre => some ⟨fd, true, ofSpec pre, true, false, false, []⟩
  | .openErr _ => none

/-- The library leaves the permissions of the stack within a megabyte of the stack pointer as
they were (it does not unmap the stack the client will push to). -/
def StackPerm (s t : PState) : Prop :=
  ∀ a, (s.m.core.read .rsp).toNat - 0x100000 ≤ a → a < (s.m.core.read .rsp).toNat + 0x100000 →
    ∀ acc, t.m.memory.permits acc a = s.m.memory.permits acc a

/-- The library maps memory (outside `fp`) only as its own: an address unmapped before that is
not private after keeps its permissions. -/
def NoMap (E : Env) (fp : Nat → Prop) (s t : PState) : Prop :=
  ∀ a, ¬ fp a → s.m.memory.permits .read a = false → ¬ E.S.priv t.m.memory a →
    ∀ acc, t.m.memory.permits acc a = s.m.memory.permits acc a

/-- The library opens no stream on its own: every stream after the call was open before, or
lies in `fp` (the stream `fopen` returns). -/
def NoNewStream (E : Env) (fp : Nat → Prop) (s t : PState) : Prop :=
  ∀ f st, E.S.file t.m.memory f st → (∃ st0, E.S.file s.m.memory f st0) ∨ ∀ a, E.S.foot t.m.memory f a → fp a

/-- `main` is running (its return job is next): the library's resource promises
(`AllocRoom`, `OpenRoom`) are made while `main` runs only. -/
def InMain (g : Ghost) : Prop := ∃ js, g.jobs = .exitRax :: js

/-- **Room for `malloc (rdi)`**: `main` runs on a stack above the library's memory, fewer than
`maxAllocs` requests have been served, and the request fits in what is left of `maxHeap`. -/
def AllocRoom (E : Env) (s : PState) : Prop :=
  InMain s.g ∧ E.S.lo ≤ (s.m.core.read .rsp).toNat ∧ s.g.allocs < E.maxAllocs ∧
    s.g.heap + (s.m.core.read .rdi).toNat ≤ E.maxHeap

/-- **Room for `fopen`** of a file whose stream is `st`. -/
def OpenRoom (E : Env) (s : PState) (st : St) : Prop :=
  InMain s.g ∧ E.S.lo ≤ (s.m.core.read .rsp).toNat ∧ s.g.files < E.maxOpen ∧ st.rd.length ≤ E.maxFile

/-- **The frame of a library call.** A System V return that may write `fp` (besides the
library's private memory), keeps the stack guard, keeps every mapped byte that is neither
private nor in `fp`, and grows the private memory only into memory that was unmapped. A
client's own data (its image, stack, argument area, and heap blocks it received from `malloc`)
is mapped and not private, so it is kept unless named in `fp`. -/
def LibRet (E : Env) (W : World) (fp : Nat → Prop) (s t : PState) : Prop :=
  ReturnsExcept W fp s t ∧ t.m.core.fsBase = s.m.core.fsBase ∧ StackPerm s t ∧
  Keeps (fun a => ¬ E.S.priv s.m.memory a ∧ ¬ fp a ∧ s.m.memory.permits .read a = true)
    s.m.memory t.m.memory ∧
  (∀ a, E.S.priv t.m.memory a → E.S.priv s.m.memory a ∨ s.m.memory.permits .read a = false) ∧
  -- the permissions of the client's mapped memory, `fp` included, stay as they were
  (∀ a, ¬ E.S.priv s.m.memory a → s.m.memory.permits .read a = true →
    ∀ acc, t.m.memory.permits acc a = s.m.memory.permits acc a) ∧
  NoMap E fp s t ∧ NoNewStream E fp s t

/-- Not the client's: private to the library, or unmapped. -/
def Fresh (E : Env) (m : Memory) (a : Nat) : Prop := E.S.priv m a ∨ m.permits .read a = false

/-- **The library's private memory is never the program's kept memory** (its image, its
arguments, the guard words of its thread block): an assumption relating a library `E` to a world
`W`, as the contracts are. It holds of glibc (its private memory is its own data and heap), and
of any stream representation whose private memory lies outside `W.Kept`. With it, the bytes of
`argv` strings are not private in any state, which is what printing a name needs. -/
def PrivApart (E : Env) (W : World) : Prop := ∀ m a, W.Kept a → ¬ E.S.priv m a

/-- The streams of `E` other than the ones a call names keep their states. -/
def OthersKept (E : Env) (s t : PState) (fs : List Word) : Prop :=
  ∀ f st, f ∉ fs → E.S.file s.m.memory f st → E.S.file t.m.memory f st


/-- The Linux x86-64 numbers of the `errno` values `Silmaril.Apps.Sha256sum.Errno` names. -/
def errnoCode : Silmaril.Apps.Sha256sum.Errno → Nat
  | .ENOENT => 2 | .EACCES => 13 | .EISDIR => 21 | .ENOTDIR => 20 | .ELOOP => 40
  | .ENAMETOOLONG => 36 | .EIO => 5 | .ENOSPC => 28 | .EBADF => 9

/-- `errno` holds `e`: the 32-bit `int` at `E.errnoA` is readable and equals `errnoCode e`. The
cell is the library's: a call may change it unless its contract says otherwise. -/
def ErrnoIs (E : Env) (m : Memory) (e : Silmaril.Apps.Sha256sum.Errno) : Prop :=
  loadN m E.errnoA 4 = some (BitVec.ofNat 64 (errnoCode e)) ∧ m.Permitted .read E.errnoA.toNat 4

/-- **`errno` lies with the library's memory, below the stack** (trusted: glibc and `ld.so`).
`errno` is a thread-local variable of `libc.so.6`; the initial thread's static TLS block that
holds it is allocated by `ld.so` (with the thread control block `%fs` points to) in memory `ld.so`
maps for itself before `main` runs, apart from the stack, like the library's streams. So the
`int` at `errnoA` lies below `E.S.lo`, and the program's pushes and stores into its stack frame
(above `E.S.lo`) never change it. The loader relation does not place the TLS block (the thread
pointer is a parameter of the run), so this is a fact about the library, not derived; the
`main`-level statements take it from `World.atMain` (`Program.AtMain.errno`) and the
`sha256sum` file tiers as `errnoLo`. -/
def Env.ErrnoLo (E : Env) : Prop := E.errnoA.toNat + 4 ≤ E.S.lo

/-- **`fopen (path, "r")`**: a fresh stream reading the file, or `NULL`: with `errno` set to the
open's error when the file system refuses the open; also when the library is out of resources
(`allocOk = false`) or the request is beyond its bounds (`OpenRoom`). -/
def fopenStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ (∃ p, CStr s.m.memory (s.m.core.read .rdi) p) ∧
      CStr s.m.memory (s.m.core.read .rsi) [0x72#8])
    fun t => LibRet E W (fun a => t.m.core.read .rax ≠ 0#64 ∧ E.S.foot t.m.memory (t.m.core.read .rax) a) s t ∧
      t.g = { s.g with files := t.g.files } ∧ OthersKept E s t [] ∧
      ∀ p, CStr s.m.memory (s.m.core.read .rdi) p →
        match openedSt (E.fs (toSpec p)) 3 with
        | none => t.m.core.read .rax = 0#64 ∧ t.g.files = s.g.files ∧
            ∀ e, E.fs (toSpec p) = .openErr e → ErrnoIs E t.m.memory e
        | some st => (t.m.core.read .rax = 0#64 ∧ (E.allocOk = false ∨ ¬ OpenRoom E s st) ∧
              t.g.files = s.g.files) ∨
            ∃ fd, E.S.file t.m.memory (t.m.core.read .rax) { st with fd := fd } ∧
            t.m.core.read .rax ≠ 0#64 ∧ 3 ≤ fd ∧ fd < 2 ^ 31 ∧ t.g.files = s.g.files + 1 ∧
            (∀ a, E.S.foot t.m.memory (t.m.core.read .rax) a → ¬ W.Kept a ∧
              a + 0x100000 < (s.m.core.read .rsp).toNat ∧ Fresh E s.m.memory a) ∧
            -- a new stream: not one that was open before
            ∀ st0, ¬ E.S.file s.m.memory (t.m.core.read .rax) st0

/-- What `fread` of `k` bytes does to a stream: up to `k` bytes, then the indicator. -/
def readSt (st : St) (k : Nat) : List Byte × St :=
  let d := st.rd.take k
  if d.length = k then (d, { st with rd := st.rd.drop k })
  else (d, { st with rd := [], eof := st.eof || !st.fail, err := st.err || st.fail })

/-- **`fread_unlocked (ptr, size, n, f)`** (`size * n` bytes, result in elements). -/
def freadGen (E : Env) (W : World) (ptr size n f : Word) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ (∃ st, E.S.file s.m.memory f st) ∧
      s.m.memory.Permitted .write ptr.toNat (size.toNat * n.toNat) ∧ 0 < size.toNat ∧
      s.m.memory.Permitted .read ptr.toNat (size.toNat * n.toNat) ∧
      (∀ a, ptr.toNat ≤ a → a < ptr.toNat + size.toNat * n.toNat → ¬ E.S.priv s.m.memory a) ∧
      E.S.lo ≤ (s.m.core.read .rsp).toNat)
    fun t => ∀ st, E.S.file s.m.memory f st →
      let (d, st') := readSt st (size.toNat * n.toNat)
      LibRet E W (fun a => ptr.toNat ≤ a ∧ a < ptr.toNat + d.length) s t ∧
      t.g = s.g ∧ OthersKept E s t [f] ∧ E.S.file t.m.memory f st' ∧
      t.m.memory.readBytes ptr.toNat d.length = some d ∧
      t.m.core.read .rax = BitVec.ofNat 64 (d.length / size.toNat)

def freadStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  freadGen E W (s.m.core.read .rdi) (s.m.core.read .rsi) (s.m.core.read .rdx) (s.m.core.read .rcx) s

/-- `__fread_unlocked_chk (ptr, ptrlen, size, n, f)`: `fread_unlocked` when the buffer is large
enough (otherwise it aborts: no claim). -/
def freadChkStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  fun r => (s.m.core.read .rdx).toNat * (s.m.core.read .rcx).toNat ≤ (s.m.core.read .rsi).toNat →
    freadGen E W (s.m.core.read .rdi) (s.m.core.read .rdx) (s.m.core.read .rcx) (s.m.core.read .r8) s r

/-- Output appended to `stdout` (`new`): the handed total grows by `new` (a prefix of it if
writes may fail). -/
def Appended (E : Env) (W : World) (s t : PState) (new : List Byte) : Prop :=
  ∀ st, StdoutIs E s.m.memory st → ∃ st', StdoutIs E t.m.memory st' ∧ st'.eof = st.eof ∧
    st'.rd = st.rd ∧ st'.reading = st.reading ∧
    ((t.g.out ++ st'.buf = s.g.out ++ st.buf ++ new ∧ st'.err = st.err) ∨
     (W.reliable = false ∧ ∃ p, p <+: new ∧ t.g.out ++ st'.buf = s.g.out ++ st.buf ++ p ∧ st'.err = true))

/-- The rest of the library state is unchanged by an output call. -/
def GhostOut (s t : PState) : Prop :=
  t.g.jobs = s.g.jobs ∧ t.g.atexit = s.g.atexit ∧ t.g.done = none ∧ t.g.inp = s.g.inp ∧
    t.g.err = s.g.err ∧ t.g.allocs = s.g.allocs ∧ t.g.heap = s.g.heap ∧ t.g.files = s.g.files

/-- **`fwrite_unlocked (ptr, size, n, stdout)`**. -/
def fwriteStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  let ptr := s.m.core.read .rdi
  let k := (s.m.core.read .rsi).toNat * (s.m.core.read .rdx).toNat
  Contract (AbiEntry s.m.core s.m.memory ∧ s.m.core.read .rcx = E.stdoutF ∧
      (∃ st, StdoutIs E s.m.memory st) ∧ ∃ d, s.m.memory.readBytes ptr.toNat k = some d)
    fun t => LibRet E W (fun _ => False) s t ∧ GhostOut s t ∧ OthersKept E s t [E.stdoutF] ∧
      ∀ d, s.m.memory.readBytes ptr.toNat k = some d → Appended E W s t d ∧
        (W.reliable = true → t.m.core.read .rax = s.m.core.read .rdx)

/-- **`__overflow (stdout, c)`** (the slow path of an inline `putc`). -/
def overflowStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ s.m.core.read .rdi = E.stdoutF ∧
      ∃ st, StdoutIs E s.m.memory st)
    fun t => LibRet E W (fun _ => False) s t ∧ GhostOut s t ∧ OthersKept E s t [E.stdoutF] ∧
      Appended E W s t [(s.m.core.read .rsi).setWidth 8]

/-- **`__fpending (f)`**: the number of buffered bytes. -/
def fpendingStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ ∃ st, E.S.file s.m.memory (s.m.core.read .rdi) st)
    fun t => LibRet E W (fun _ => False) s t ∧ t.g = s.g ∧ OthersKept E s t [] ∧
      ∀ st, E.S.file s.m.memory (s.m.core.read .rdi) st →
        E.S.file t.m.memory (s.m.core.read .rdi) st ∧ t.m.core.read .rax = BitVec.ofNat 64 st.buf.length

/-- **`fclose (f)`**: a read stream is released; `stdout`'s buffer is written out. Returns 0,
or `EOF` if the stream had an error or the write failed. -/
def fcloseStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  let f := s.m.core.read .rdi
  Contract (AbiEntry s.m.core s.m.memory ∧ ∃ st, E.S.file s.m.memory f st)
    fun t => LibRet E W (fun _ => False) s t ∧ t.g.jobs = s.g.jobs ∧
      t.g.atexit = s.g.atexit ∧ t.g.done = none ∧ t.g.inp = s.g.inp ∧ t.g.err = s.g.err ∧
      t.g.allocs = s.g.allocs ∧ t.g.heap = s.g.heap ∧ t.g.files = s.g.files ∧ OthersKept E s t [f] ∧
      ∀ st, E.S.file s.m.memory f st →
        (st.fd = 1 →
          ((t.g.out = s.g.out ++ st.buf ∧ (st.err = false → low32 (t.m.core.read .rax) = 0#32)) ∨
           (W.reliable = false ∧ ∃ p, p <+: st.buf ∧ t.g.out = s.g.out ++ p ∧
             low32 (t.m.core.read .rax) = 0xffffffff#32))) ∧
        (st.fd ≠ 1 → t.g.out = s.g.out ∧ (st.err = false → low32 (t.m.core.read .rax) = 0#32))

/-- Two lower-case hexadecimal digits of a byte (`%02x`). -/
def hex2 (b : Byte) : List Byte :=
  let d (n : Nat) : Byte := BitVec.ofNat 8 (if n < 10 then 48 + n else 87 + n)
  [d (b.toNat / 16), d (b.toNat % 16)]

/-- `"%02x"` -/
def fmtHex : List Byte := [0x25#8, 0x30#8, 0x32#8, 0x78#8]

/-- **`__printf_chk (flag, "%02x", b)`**. -/
def printfHexStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ CStr s.m.memory (s.m.core.read .rsi) fmtHex ∧
      ∃ st, StdoutIs E s.m.memory st)
    fun t => LibRet E W (fun _ => False) s t ∧ GhostOut s t ∧ OthersKept E s t [E.stdoutF] ∧
      Appended E W s t (hex2 ((s.m.core.read .rdx).setWidth 8))

/-- **`error (status, errnum, fmt, …)`**: a message to `stderr` (not observed), then
`exit (status)` if `status ≠ 0`. -/
def errorStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory)
    fun t => if low32 (s.m.core.read .rdi) = 0#32 then
        LibRet E W (fun _ => False) s t ∧ t.g = s.g ∧ OthersKept E s t []
      else AtGate W s t ∧ t.g = { s.g with jobs := [.exit (s.m.core.read .rdi)] }

/-- A call with no effect the client observes but its result `rax ∈ P`. -/
def quietLib (E : Env) (W : World) (P : Word → Prop) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory)
    fun t => LibRet E W (fun _ => False) s t ∧ P (t.m.core.read .rax) ∧ t.g = s.g ∧ OthersKept E s t []

/-- **`posix_fadvise`**: advice only. -/
def fadviseStep (E : Env) (W : World) : PState → Res PState → Prop := quietLib E W fun _ => True

/-- **`lseek (fd, 0, SEEK_CUR)`** (`rpl_fclose` asks whether the stream is seekable): any result. -/
def lseekStep (E : Env) (W : World) : PState → Res PState → Prop := quietLib E W fun _ => True

/-- **`fileno (f)`**. -/
def filenoStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ ∃ st, E.S.file s.m.memory (s.m.core.read .rdi) st)
    fun t => LibRet E W (fun _ => False) s t ∧ t.g = s.g ∧ OthersKept E s t [] ∧
      ∀ st, E.S.file s.m.memory (s.m.core.read .rdi) st → low32 (t.m.core.read .rax) = BitVec.ofNat 32 st.fd

/-- **`clearerr_unlocked (f)`**: clears the end-of-file and error indicators (called on a stack above
the library's memory). -/
def clearerrStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ (∃ st, E.S.file s.m.memory (s.m.core.read .rdi) st) ∧
      E.S.lo ≤ (s.m.core.read .rsp).toNat)
    fun t => LibRet E W (fun _ => False) s t ∧ t.g = s.g ∧ OthersKept E s t [s.m.core.read .rdi] ∧
      ∀ st, E.S.file s.m.memory (s.m.core.read .rdi) st →
        E.S.file t.m.memory (s.m.core.read .rdi) { st with eof := false, err := false }

/-- **`__freading (f)`**: non-zero iff the stream is open for reading. -/
def freadingStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ ∃ st, E.S.file s.m.memory (s.m.core.read .rdi) st)
    fun t => LibRet E W (fun _ => False) s t ∧ t.g = s.g ∧ OthersKept E s t [] ∧
      ∀ st, E.S.file s.m.memory (s.m.core.read .rdi) st →
        (low32 (t.m.core.read .rax) = 0#32 ↔ st.reading = false)

/-- **`fflush (f)`**: `stdout`'s buffer is written out (a prefix, with `EOF` and the error
indicator, if writes may fail); other streams keep their state (an input stream's unread
bytes are still unread). -/
def fflushStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  let f := s.m.core.read .rdi
  Contract (AbiEntry s.m.core s.m.memory ∧ ∃ st, E.S.file s.m.memory f st)
    fun t => LibRet E W (fun _ => False) s t ∧ GhostOut s t ∧ OthersKept E s t [f] ∧
      ∀ st, E.S.file s.m.memory f st →
        (st.fd = 1 →
          ((t.g.out = s.g.out ++ st.buf ∧ E.S.file t.m.memory f { st with buf := [] } ∧
              (st.err = false → low32 (t.m.core.read .rax) = 0#32)) ∨
           (W.reliable = false ∧ ∃ p, p <+: st.buf ∧ t.g.out = s.g.out ++ p ∧
             low32 (t.m.core.read .rax) = 0xffffffff#32 ∧
             ∃ b, E.S.file t.m.memory f { st with buf := b, err := true }))) ∧
        (st.fd ≠ 1 → t.g.out = s.g.out ∧ E.S.file t.m.memory f { st with buf := [] } ∧
          (st.err = false → low32 (t.m.core.read .rax) = 0#32))

/-- **`malloc (n)`**: `n` readable and writable bytes that were not the client's (private or
unmapped), are no longer private, and lie below the stack and outside the image; or `NULL`, only
when the library is out of resources (`allocOk = false`) or the request is
beyond its bounds (`AllocRoom`). It writes only the new block and private memory (`LibRet`), and
records the block in `Ghost.blocks`. -/
def mallocStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory)
    fun t => LibRet E W (fun a => t.m.core.read .rax ≠ 0#64 ∧ (t.m.core.read .rax).toNat ≤ a ∧
        a < (t.m.core.read .rax).toNat + (s.m.core.read .rdi).toNat) s t ∧
      t.g = { s.g with allocs := t.g.allocs, heap := t.g.heap, blocks := t.g.blocks } ∧ OthersKept E s t [] ∧
      ((t.m.core.read .rax = 0#64 ∧ (E.allocOk = false ∨ ¬ AllocRoom E s) ∧ t.g.allocs = s.g.allocs ∧
          t.g.heap = s.g.heap ∧ t.g.blocks = s.g.blocks) ∨
        (t.m.core.read .rax ≠ 0#64 ∧ t.g.allocs = s.g.allocs + 1 ∧
         t.g.heap = s.g.heap + (s.m.core.read .rdi).toNat ∧
         t.g.blocks = ((t.m.core.read .rax).toNat, (s.m.core.read .rdi).toNat) :: s.g.blocks ∧
         t.m.memory.Permitted .read (t.m.core.read .rax).toNat (s.m.core.read .rdi).toNat ∧
         t.m.memory.Permitted .write (t.m.core.read .rax).toNat (s.m.core.read .rdi).toNat ∧
         ∀ a, (t.m.core.read .rax).toNat ≤ a → a < (t.m.core.read .rax).toNat + (s.m.core.read .rdi).toNat →
           ¬ E.S.priv t.m.memory a ∧ ¬ W.Kept a ∧ a + 0x100000 < (s.m.core.read .rsp).toNat ∧ a < E.S.lo ∧
           Fresh E s.m.memory a))

/-- The size of the live block starting at `p` (the most recent one), if any. -/
def blockAt (g : Ghost) (p : Nat) : Option Nat := (g.blocks.find? (·.1 == p)).map (·.2)

/-- `free`'s argument: `NULL`, or the start of a live block. -/
def FreeArg (s : PState) : Prop :=
  s.m.core.read .rdi = 0#64 ∨ (blockAt s.g (s.m.core.read .rdi).toNat).isSome

/-- The bytes of the block `free (rdi)` releases (outside the program's kept memory and below the
stack, as every block `malloc` returns). Empty for `free (NULL)`. -/
def FreedBlk (W : World) (s : PState) (a : Nat) : Prop :=
  (∃ n, blockAt s.g (s.m.core.read .rdi).toNat = some n ∧ (s.m.core.read .rdi).toNat ≤ a ∧
    a < (s.m.core.read .rdi).toNat + n) ∧ ¬ W.Kept a ∧ a < (s.m.core.read .rsp).toNat

/-- **The frame of `free`**: `LibRet` with the freed block `fp` given back to the library: it may
become private again or be unmapped (glibc reuses a chunk or returns an `mmap`ped one). Every
mapped, non-private byte outside `fp` keeps its contents and permissions. -/
def FreeRet (E : Env) (W : World) (fp : Nat → Prop) (s t : PState) : Prop :=
  ReturnsExcept W fp s t ∧ t.m.core.fsBase = s.m.core.fsBase ∧ StackPerm s t ∧
  Keeps (fun a => ¬ E.S.priv s.m.memory a ∧ ¬ fp a ∧ s.m.memory.permits .read a = true)
    s.m.memory t.m.memory ∧
  (∀ a, E.S.priv t.m.memory a → E.S.priv s.m.memory a ∨ s.m.memory.permits .read a = false ∨ fp a) ∧
  (∀ a, ¬ E.S.priv s.m.memory a → s.m.memory.permits .read a = true → ¬ fp a →
    ∀ acc, t.m.memory.permits acc a = s.m.memory.permits acc a) ∧
  NoMap E (fun _ => False) s t ∧ NoNewStream E (fun _ => False) s t

/-- **`free (p)`** (`p` is `NULL` or a live block, `FreeArg`): writes only the block it releases
and the library's private memory (`FreeRet`), and removes the block from `Ghost.blocks`. -/
def freeStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ FreeArg s)
    fun t => FreeRet E W (FreedBlk W s) s t ∧
      t.g = { s.g with blocks := s.g.blocks.eraseP (·.1 == (s.m.core.read .rdi).toNat) } ∧
      OthersKept E s t []

/-- **`setvbuf (f, NULL, mode, 0)`**: the buffering mode is not observable here. -/
def setvbufStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory)
    fun t => LibRet E W (fun _ => False) s t ∧ t.g = s.g ∧ OthersKept E s t []

/-- The C strings of `argc` arguments at `argv`. -/
def Argv (m : Memory) (argv : Word) (args : List (List Byte)) : Prop :=
  ∀ i (hi : i < args.length), ∃ p, loadN m (argv + BitVec.ofNat 64 (8 * i)) 8 = some p ∧
    CStr m p (args[i]'hi)

/-- **`getopt_long (argc, argv, …)`** on arguments none of which is an option (no argument
after `argv[0]` starts with `-`): returns `-1` with `optind = 1`. -/
def getoptNoneStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ s.m.memory.Permitted .read E.optindA.toNat 4 ∧
      s.m.memory.Permitted .write E.optindA.toNat 4 ∧ ∃ args : List (List Byte),
      args.length = (low32 (s.m.core.read .rdi)).toNat ∧ Argv s.m.memory (s.m.core.read .rsi) args ∧
      ∀ a ∈ args.drop 1, a.head? ≠ some 0x2d#8)
    fun t => LibRet E W (fun a => E.optindA.toNat ≤ a ∧ a < E.optindA.toNat + 4) s t ∧ t.g = s.g ∧
      OthersKept E s t [] ∧
      low32 (t.m.core.read .rax) = 0xffffffff#32 ∧ loadN t.m.memory E.optindA 4 = some 1#64

/-- **`strrchr (s, c)`**: the last occurrence of `c` in the string, or `NULL`. -/
def strrchrStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ ∃ str, CStr s.m.memory (s.m.core.read .rdi) str)
    fun t => LibRet E W (fun _ => False) s t ∧ t.g = s.g ∧ OthersKept E s t [] ∧ ∀ str, CStr s.m.memory (s.m.core.read .rdi) str →
      let c := (s.m.core.read .rsi).setWidth 8
      match (List.range (str.length + 1)).reverse.find? (fun i => (str ++ [0])[i]? = some c) with
      | some i => t.m.core.read .rax = s.m.core.read .rdi + BitVec.ofNat 64 i
      | none => t.m.core.read .rax = 0#64

/-- **`strncmp (a, b, n)`**: zero iff the first `n` characters agree (as C strings). -/
def strncmpStep (E : Env) (W : World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ (∃ a, CStr s.m.memory (s.m.core.read .rdi) a) ∧
      ∃ b, CStr s.m.memory (s.m.core.read .rsi) b)
    fun t => LibRet E W (fun _ => False) s t ∧ t.g = s.g ∧ OthersKept E s t [] ∧ ∀ a b, CStr s.m.memory (s.m.core.read .rdi) a →
      CStr s.m.memory (s.m.core.read .rsi) b →
      (low32 (t.m.core.read .rax) = 0#32 ↔
        ((a ++ [0]).take (s.m.core.read .rdx).toNat = (b ++ [0]).take (s.m.core.read .rdx).toNat ∨
         ((a ++ [0]).takeWhile (· ≠ 0)).take (s.m.core.read .rdx).toNat =
           ((b ++ [0]).takeWhile (· ≠ 0)).take (s.m.core.read .rdx).toNat))

/-- A contract of `Imports` (`SHA256_*`, `setlocale`, …) with the library frame added: when the
objects `fp` it writes are not the library's private memory, it writes only `fp` and private
memory, and keeps every stream. -/
def framed (E : Env) (W : World) (fp : PState → Nat → Prop) (c : PState → Res PState → Prop)
    (s : PState) (r : Res PState) : Prop :=
  c s r ∧ ((∀ a, fp s a → ¬ E.S.priv s.m.memory a) →
    ∀ t, r = .ok t → LibRet E W (fp s) s t ∧ OthersKept E s t []) ∧
  ∀ t, r = .ok t → NoMap E (fun _ => False) s t ∧ NoNewStream E (fun _ => False) s t

/-- **The import table of `sha256sum`'s happy path**, by name. -/
def shaContracts (E : Env) (R : ShaRep) (W : World) : List (Name × (PState → Res PState → Prop)) :=
  let none_ : PState → Nat → Prop := fun _ _ => False
  [(nm "setlocale", framed E W none_ (quietStep W fun _ => True)),
   (nm "bindtextdomain", framed E W none_ (quietStep W fun _ => True)),
   (nm "textdomain", framed E W none_ (quietStep W fun _ => True)),
   (nm "__cxa_atexit", framed E W none_ (cxaAtexitStep W)),
   (nm "SHA256_Init", framed E W (fun s => ctxRange (s.m.core.read .rdi)) (sha256InitStep R W)),
   (nm "SHA256_Update", framed E W (fun s => ctxRange (s.m.core.read .rdi)) (sha256UpdateStep R W)),
   (nm "SHA256_Final", framed E W (fun s a => ctxRange (s.m.core.read .rsi) a ∨
      ((s.m.core.read .rdi).toNat ≤ a ∧ a < (s.m.core.read .rdi).toNat + 32)) (sha256FinalStep R W)),
   (nm "fopen", fopenStep E W), (nm "fread_unlocked", freadStep E W),
   (nm "__fread_unlocked_chk", freadChkStep E W), (nm "fclose", fcloseStep E W),
   (nm "fwrite_unlocked", fwriteStep E W), (nm "__overflow", overflowStep E W),
   (nm "__fpending", fpendingStep E W), (nm "__printf_chk", printfHexStep E W),
   (nm "error", errorStep E W), (nm "posix_fadvise", fadviseStep E W),
   (nm "getopt_long", getoptNoneStep E W), (nm "setvbuf", setvbufStep E W),
   (nm "strrchr", strrchrStep E W), (nm "strncmp", strncmpStep E W),
   (nm "fileno", filenoStep E W), (nm "__freading", freadingStep E W), (nm "lseek", lseekStep E W),
   (nm "fflush", fflushStep E W), (nm "malloc", mallocStep E W), (nm "free", freeStep E W)]

/-- The table as `World.named`. -/
def namedOf (L : List (Name × (PState → Res PState → Prop))) (n : Name) : PState → Res PState → Prop :=
  match L.lookup n with
  | some c => c
  | none => fun _ r => r = .stop

end Silmaril.Elf.Link.Dyn.Streams
