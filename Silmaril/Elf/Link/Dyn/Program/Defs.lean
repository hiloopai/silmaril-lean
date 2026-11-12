module

public import Silmaril.Elf.Link.Dyn.Streams.Errors
public import Silmaril.Elf.Link.Dyn.Glibc.Thms
public import Silmaril.Elf.Link.Dyn.Hello.Cert
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Extra
public import Silmaril.Apps.Sha256sum.Basic
public import Silmaril.Elf.Link.Dyn.Cert.Defs

/-! # Verifying a dynamically linked C program on glibc: the API

A **program** is a pinned executable (`Bin`, generated) linked against a pinned glibc
(`LibPin`s for `libc.so.6` and `ld.so`). Its **specification** is a function from the
C-level world to the observable outcome, in the style of `Silmaril.Apps.Sha256sum`:

* `World` (argv, a read oracle for the file system, stdin, whether stdout is a full device),
* `Outcome` (the bytes on stdout and stderr, the exit status),
* `Spec := World → Outcome`, claimed on a `Tier` of worlds.

`Verified B spec tier` is the end-to-end statement: for every world of the tier, every glibc
agreeing with the pins, every load the loader relation allows (any bases, any ifunc choice)
and every documented initial state of the process for that world, **every run of the
process ends, with exactly the outcome `spec w`**.

## The world/outcome bridge

The C-level world reaches the process through four documented interfaces, each a field of
the process world `world B S w …` or of the initial state `AtStart`:

| C level | process level | who guarantees it |
|---|---|---|
| `w.argv` | `argc`/`argv` and the strings on the initial stack, in `World.args` (never written by the library) | the kernel (`AtStart`) |
| `w.stdin` | the stream `stdin` at `main`'s entry reads `w.stdin` (`AtMain.stdin`) | glibc (`World.atMain`) |
| `w.fs` | `fopen`/`fread` read `S.E.fs = w.fs` (`Streams.openedSt`) | glibc + kernel (`fopenStep`) |
| `w.stdoutFull` | `World.reliable = !w.stdoutFull` | the environment |
| `o.stdout` | the bytes that reached fd 1 when the process ended (`Ghost.done`), including what `exit` flushed (`World.pending`) | glibc (`Proc.gateStep`) |
| `o.stderr` | `Ghost.err` (fd 2, unbuffered) | glibc (the contracts that write it) |
| `o.status` | `Ghost.done`'s status (`main`'s `eax` or `exit`'s argument, mod 256) | glibc (`Proc.gateStep`) |

## What a user writes per binary

1. the pinned file and its generated facts (a `Bin`, a generator);
2. the spec (`Spec`) and the tier;
3. one check `B.ok libc ld = true` (`decide +kernel`): headers, references, the binding
   certificate against the cached glibc lookups, the C runtime's placement, the image facts,
   `main`'s listing and its call sites;
4. `main`'s proof against the C library contracts (`Program.Lib`), at the level of calls:
   each call site of an import is one step whose effect is the import's contract
   (`Program.Thms`: `call_site`, the frame and loop rules, the `verify_main` tactic).

`Program.Thms.verified` does the rest: the loader, the C runtime (`Crt.crt_run`), the
bridge, non-vacuity.

**Trusted** (beyond `Proc`): the bridge rows above (the initial state for a world, glibc's
stdio state at `main`, the flush at `exit`), and the contracts of `Program.Lib`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.RelIsa (Res)
open Silmaril.X86.Ext (loadN)
open Silmaril.X86.FnContract (AbiEntry)
open Silmaril.Elf.Link.Dyn.Proc (Ghost PState Keeps CStr Contract low32 MustQ Fn Job)
open Silmaril.Elf.Link.Dyn.Streams (St Env StdoutIs ofSpec toSpec ErrnoIs errnoCode errorMsg fmtS)
open Silmaril.Elf.Link.DynElf (Chunk ChunksOf sparseRead blobRead)

/-! ## 1. The C-level specification -/

/-- The C-level world (tool-agnostic despite the namespace: argv, file system, stdin, a full
stdout). -/
abbrev World := Silmaril.Apps.Sha256sum.World

/-- What a run shows: stdout, stderr, exit status. -/
abbrev Outcome := Silmaril.Apps.Sha256sum.Outcome

/-- A program's specification. -/
abbrev Spec := World → Outcome

/-- The worlds a claim is about. -/
abbrev Tier := World → Prop

/-- The bytes of an ASCII string. -/
abbrev lit := Silmaril.Apps.Sha256sum.lit

namespace Tier

/-- Writes to stdout succeed. -/
def reliable : Tier := fun w => w.stdoutFull = false

/-- No operands and no options: `argv = [argv0]`, stdin is a byte stream. -/
def stdinOnly : Tier := fun w => reliable w ∧ w.argv.length = 1 ∧ ∃ d, w.stdin = .bytes d

/-- Exactly `n` operands, none of them an option (`-…`). -/
def operands (n : Nat) : Tier := fun w =>
  reliable w ∧ w.argv.length = n + 1 ∧ ∀ a ∈ w.argv.drop 1, a.head? ≠ some 45

/-- Any number of operands, none of them an option. -/
def noOptions : Tier := fun w => reliable w ∧ 1 ≤ w.argv.length ∧ ∀ a ∈ w.argv.drop 1, a.head? ≠ some 45

end Tier

/-! ## 2. Pins -/

/-- A pinned shared library: the sparse view of its file that symbol lookup reads, its
headers, and the cached lookup results (`Known`). -/
structure LibPin where
  chunks : List Chunk
  info : Elf.DynInfo
  facts : List (Elf.Ref × Bool × Option Elf.Def)

/-- The pin is self-consistent (one `decide +kernel` per library version). -/
def LibPin.ok (P : LibPin) : Bool :=
  (Elf.dynInfo.run (sparseRead P.chunks) == some P.info) &&
    Glibc.factsHold P.chunks P.info P.facts

/-- An import the program calls through a `.plt.sec` stub: its name, the stub's offset, the
GOT slot's offset, and where `libc.so.6` defines it (offset from its base). -/
structure Import where
  name : Name
  stub : Nat
  slot : Nat
  off : Nat
  deriving DecidableEq, Repr

/-- A libc variable the program reads (`stdin`, `stdout`, …): through a `GLOB_DAT` slot of the
image holding its address in `libc.so.6` (`off`), or, for a `COPY` relocation (`copy`), as the
image's own copy at `slot`. -/
structure Var where
  name : Name
  slot : Nat
  off : Nat
  copy : Bool := false
  deriving DecidableEq, Repr

/-- Where the variable's value lives. -/
def Var.addr (v : Var) (b lb : Word) : Word :=
  if v.copy then b + BitVec.ofNat 64 v.slot else lb + BitVec.ofNat 64 v.off

/-- **A pinned executable** with the C runtime of gcc/clang `-O2` PIE (all generated). -/
structure Bin where
  file : Blob
  info : Elf.DynInfo
  refs : List (Nat × Elf.Ref)
  /-- The loader's slot table (eager binding). -/
  slots : List (Nat × Dyn.Val)
  layout : Crt.Layout
  tx : Elf.Phdr
  ro : Elf.Phdr
  rw : Elf.Phdr
  /-- `__libc_start_main` and `__cxa_finalize` in `libc.so.6`. -/
  lsmOff : Nat
  cxaOff : Nat
  imports : List Import
  vars : List Var
  /-- `main`'s listing (offsets from `main`). -/
  mainL : List (Nat × Silmaril.X86.Ext9.Instr × Nat)
  /-- `.plt.sec`'s bytes (offset, bytes) and its listing. -/
  pltAt : Nat
  plt : List Byte
  pltL : List (Nat × Silmaril.X86.Ext9.Instr × Nat)
  /-- The C strings `main` uses (offset in the image, bytes without the NUL). -/
  strs : List (Nat × List Byte) := []
  /-- Block certificates of `main` (offsets from `main`), straight-line stretches between calls
  and jump targets. -/
  blks : List Cert.Blk := []

/-- The code slices and slots `main` needs beyond the runtime: `.plt.sec` and the import and
variable slots. -/
def Bin.extraCode (B : Bin) : List (Nat × List Byte) := [(B.pltAt, B.plt)]
def Bin.extraSlots (B : Bin) : List (Nat × Nat) :=
  B.imports.map (fun i => (i.slot, i.off)) ++ (B.vars.filter (!·.copy)).map (fun v => (v.slot, v.off))

/-- The C string at offset `n` of the image, if it lies in `.rodata`. -/
def Bin.cstrAt (B : Bin) (n : Nat) : Option (List Byte) :=
  if B.layout.ro ≤ n then
    let l := B.layout.cRo.drop (n - B.layout.ro)
    let s := l.takeWhile (· ≠ 0)
    if s.length < l.length then some s else none
  else none

/-- `imp`'s stub in `.plt.sec`: `endbr64; jmp *slot(%rip)` (gcc, `-fcf-protection`). -/
def Bin.stubIbt (B : Bin) (imp : Import) : Bool :=
  decide (B.pltAt ≤ imp.stub) && decide (imp.stub + 10 ≤ B.pltAt + B.plt.length) &&
  (B.pltL.lookup (imp.stub - B.pltAt) == some (.ext8 (.base .endbr64), 4)) &&
  (B.pltL.lookup (imp.stub - B.pltAt + 4) ==
    some (.new (.jmpInd (.mem (.ofRip (BitVec.ofInt 32 ((imp.slot : Int) - (imp.stub + 10)))))), 6)) &&
  decide (imp.slot + 8 ≤ B.layout.size) && decide (imp.slot < 2 ^ 31) && decide (imp.stub < 2 ^ 31) &&
  (BitVec.ofNat 64 (imp.stub + 10) + (BitVec.ofInt 32 ((imp.slot : Int) - (imp.stub + 10))).signExtend 64 ==
    BitVec.ofNat 64 imp.slot)

/-- `imp`'s stub in `.plt`: `jmp *slot(%rip)` (clang; under eager binding the slot holds the
import, so the `push`/`jmp PLT0` after it are not reached). -/
def Bin.stubPlain (B : Bin) (imp : Import) : Bool :=
  decide (B.pltAt ≤ imp.stub) && decide (imp.stub + 6 ≤ B.pltAt + B.plt.length) &&
  (B.pltL.lookup (imp.stub - B.pltAt) ==
    some (.new (.jmpInd (.mem (.ofRip (BitVec.ofInt 32 ((imp.slot : Int) - (imp.stub + 6)))))), 6)) &&
  decide (imp.slot + 8 ≤ B.layout.size) && decide (imp.slot < 2 ^ 31) && decide (imp.stub < 2 ^ 31) &&
  (BitVec.ofNat 64 (imp.stub + 6) + (BitVec.ofInt 32 ((imp.slot : Int) - (imp.stub + 6))).signExtend 64 ==
    BitVec.ofNat 64 imp.slot)

/-- `imp`'s stub: either shape. -/
def Bin.stubOk (B : Bin) (imp : Import) : Bool := B.stubIbt imp || B.stubPlain imp

/-- **The one per-binary check**: headers, references, the binding certificate (against the
cached lookups of the pins), the runtime layout, the image facts, the extra facts, and the
listings of `main` and `.plt.sec`. -/
def Bin.ok (B : Bin) (libc ld : LibPin) : Bool :=
  (Elf.dynInfo.run (blobRead B.file) == some B.info) &&
  Hello.refsHold B.file B.info B.refs &&
  (Dyn.slotsWith (Dyn.resolveK [Hello.exeFacts B.refs, libc.facts, ld.facts]) false B.file B.info ==
    some B.slots) &&
  B.layout.ok &&
  B.layout.imageOk B.file B.info B.tx B.ro B.rw B.slots B.lsmOff B.cxaOff &&
  Crt.extraOk B.file B.info B.tx B.rw B.slots B.extraCode B.extraSlots &&
  Proc.listingOk B.layout.cMain B.mainL &&
  Proc.listingOk B.plt B.pltL &&
  B.extraCode.all (fun c => decide (c.1 + c.2.length ≤ B.layout.size)) &&
  B.extraSlots.all (fun s => decide (s.1 + 8 ≤ B.layout.size)) &&
  decide (([B.lsmOff, B.cxaOff] ++ B.imports.map (·.off)).Nodup) &&
  ([B.lsmOff, B.cxaOff] ++ B.imports.map (·.off)).all (fun o => decide (o < 2 ^ 32)) &&
  B.imports.all B.stubOk && decide (B.pltAt + B.plt.length ≤ B.layout.size) &&
  B.strs.all (fun e => B.cstrAt e.1 == some e.2) &&
  B.blks.all (fun k => k.ok B.layout.cMain) &&
  B.info.phs.contains B.tx && (B.tx.kind == 1) && (B.tx.flags == 5) &&
  decide (B.tx.vaddr ≤ B.layout.main) &&
  decide (B.layout.main + B.layout.cMain.length ≤ B.tx.vaddr + B.tx.memsz)

/-! ## 3. The library: its environment and its contracts -/

/-- **The library's stdio environment**: the stream representation, the `FILE` pointers and
where `errno` lives (`Streams.Env`), `stdin`'s `FILE`. -/
structure Std where
  E : Env
  stdinF : Word

/-- The library's allocations succeed (`fopen` does not fail for want of memory) within its
resource bounds: at least one stream may be open (`maxOpen`), and every file the world holds
fits the library's file bound (`maxFile`; `Streams.OpenRoom`). The environment assumption of
the tiers that open files. -/
def Std.allocates (S : Std) : Prop :=
  S.E.allocOk = true ∧ 1 ≤ S.E.maxOpen ∧
    ∀ p fd st, Streams.openedSt (S.E.fs p) fd = some st → st.rd.length ≤ S.E.maxFile

/-- `stdin` as a stream reading the world's standard input. -/
def stdinSt (w : World) : St :=
  match w.stdin with
  | .bytes d => ⟨0, true, ofSpec d, false, false, false, []⟩
  | .dir => ⟨0, true, [], true, false, false, []⟩

/-- `stdout` and `stderr` at the start: nothing buffered, no indicator. -/
def outSt (fd : Nat) : St := ⟨fd, false, [], false, false, false, []⟩

/-- **What glibc guarantees at `main`'s entry** (`World.atMain`): the three standard streams,
the libc variables holding them (at `lb + v.off`), and that the streams lie below the stack. -/
structure AtMain (B : Bin) (S : Std) (b lb : Word) (w : World) (t : PState) : Prop where
  stdin : S.E.S.file t.m.memory S.stdinF (stdinSt w)
  stdout : StdoutIs S.E t.m.memory (outSt 1)
  stderr : S.E.S.file t.m.memory S.E.stderrF (outSt 2)
  vars : ∀ v ∈ B.vars, loadN t.m.memory (v.addr b lb) 8 =
    some (if v.name = nm "stdin" then S.stdinF else if v.name = nm "stdout" then S.E.stdoutF
      else S.E.stderrF)
  lo : S.E.S.lo + 0x100000 ≤ (t.m.core.read .rsp).toNat
  /-- `errno` is the library's, below the stack (trusted, `Streams.Env.ErrnoLo`). -/
  errno : S.E.ErrnoLo

/-- The bytes `stdout` still buffers (flushed by `exit`). -/
def Pending (S : Std) (s : PState) (p : List Byte) : Prop :=
  ∀ st, StdoutIs S.E s.m.memory st → p = st.buf

/-! ### Contracts beyond `Streams` -/

/-- A contract that also leaves `stderr` alone. -/
def errKept (c : PState → Res PState → Prop) (s : PState) (r : Res PState) : Prop :=
  c s r ∧ ∀ t, r = .ok t → t.g.err = s.g.err

/-- **`fopen (path, "r")` with `errno`**: `Streams.fopenStep`, and when the open fails with
`e`, `errno = e`. -/
def fopenErrStep (S : Std) (W : Proc.World) (s : PState) (r : Res PState) : Prop :=
  Streams.fopenStep S.E W s r ∧ ∀ t, r = .ok t → t.g.err = s.g.err ∧
    ∀ p, CStr s.m.memory (s.m.core.read .rdi) p → ∀ e, S.E.fs (toSpec p) = .openErr e →
      ErrnoIs S.E t.m.memory e

/-- **`error (status, errnum, "%s", arg)`** with `errnum` an `errno` value: flushes `stdout`,
writes the message to `stderr`; returns when `status = 0`, otherwise `exit (status)`. The
program name is `argv[0]` (`prog`, glibc's `program_invocation_name`). -/
def errorStep (S : Std) (prog : List Byte) (W : Proc.World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ CStr s.m.memory (s.m.core.read .rdx) fmtS ∧
      (∃ a, CStr s.m.memory (s.m.core.read .rcx) a) ∧
      ∃ e, (low32 (s.m.core.read .rsi)).toNat = errnoCode e)
    fun t => ∀ a e, CStr s.m.memory (s.m.core.read .rcx) a →
      (low32 (s.m.core.read .rsi)).toNat = errnoCode e →
      if low32 (s.m.core.read .rdi) = 0#32 then
        Streams.LibRet S.E W (fun _ => False) s t ∧ Streams.OthersKept S.E s t [] ∧
          t.g = { s.g with err := s.g.err ++ errorMsg prog a e }
      else ∃ p, Pending S s p ∧ Proc.AtGate W s t ∧
        t.g = { s.g with jobs := [.exit (s.m.core.read .rdi)], out := s.g.out ++ p, err := s.g.err ++ errorMsg prog a e }

/-- Only the bytes handed to `stdout` may change in the library's state. -/
def OutOnly (s t : PState) : Prop := t.g = { s.g with out := t.g.out }

/-- **`puts (str)`** on the stream `stdout`: appends `str` and a newline (a prefix of them if
writes may fail). -/
def putsStep (S : Std) (W : Proc.World) (s : PState) : Res PState → Prop :=
  Contract (AbiEntry s.m.core s.m.memory ∧ (∃ str, CStr s.m.memory (s.m.core.read .rdi) str) ∧
      ∃ st, StdoutIs S.E s.m.memory st)
    fun t => Streams.LibRet S.E W (fun _ => False) s t ∧ OutOnly s t ∧
      Streams.OthersKept S.E s t [S.E.stdoutF] ∧
      ∀ str, CStr s.m.memory (s.m.core.read .rdi) str → Streams.Appended S.E W s t (str ++ [10])

/-- **`__stack_chk_fail ()`**: no claim (a program proved correct never calls it). -/
def stackChkFailStep (_ : PState) (r : Res PState) : Prop := r = .stop

/-- The bytes of stdin as a byte stream (a directory reads nothing here: no claim is made for it
at this level, see `Tier.stdinOnly`). -/
def stdinBytes (w : World) : List Byte :=
  match w.stdin with
  | .bytes d => ofSpec d
  | .dir => []

/-- **`read (0, buf, n)`** (`ssize_t`): the kernel delivers a non-empty prefix of the unread
standard input of at most `n` bytes (any split: short reads are allowed), or 0 at end of input.
The unread input is the library's `Ghost.inp`. The program's frame and every stream are kept
but for the buffer. -/
def readStep (S : Std) (W : Proc.World) (s : PState) : Res PState → Prop :=
  let buf := s.m.core.read .rsi
  let n := (s.m.core.read .rdx).toNat
  Contract (AbiEntry s.m.core s.m.memory ∧ s.m.core.read .rdi = 0#64 ∧ 0 < n ∧ n < 2 ^ 31 ∧
      s.m.memory.Permitted .write buf.toNat n ∧ s.m.memory.Permitted .read buf.toNat n ∧
      (∀ a, buf.toNat ≤ a → a < buf.toNat + n → ¬ S.E.S.priv s.m.memory a ∧ ¬ W.Kept a))
    fun t => ∃ k, k ≤ n ∧ k ≤ s.g.inp.length ∧ (k = 0 ↔ s.g.inp = []) ∧
      Streams.LibRet S.E W (fun a => buf.toNat ≤ a ∧ a < buf.toNat + k) s t ∧ Streams.OthersKept S.E s t [] ∧
      t.m.memory.readBytes buf.toNat k = some (s.g.inp.take k) ∧
      t.g = { s.g with inp := s.g.inp.drop k } ∧ t.m.core.read .rax = BitVec.ofNat 64 k

/-- **`write (1, buf, n)`**: the `n` bytes reach fd 1 (writes to stdout succeed, `W.reliable`);
otherwise a prefix of them and a result that is not `n`. -/
def writeStep (S : Std) (W : Proc.World) (s : PState) : Res PState → Prop :=
  let buf := s.m.core.read .rsi
  let n := (s.m.core.read .rdx).toNat
  Contract (AbiEntry s.m.core s.m.memory ∧ s.m.core.read .rdi = 1#64 ∧
      ∃ d, s.m.memory.readBytes buf.toNat n = some d)
    fun t => Streams.LibRet S.E W (fun _ => False) s t ∧ Streams.OthersKept S.E s t [] ∧
      ∀ d, s.m.memory.readBytes buf.toNat n = some d →
        (W.reliable = true → t.g = { s.g with out := s.g.out ++ d } ∧ t.m.core.read .rax = s.m.core.read .rdx) ∧
        (∃ p, p <+: d ∧ t.g = { s.g with out := s.g.out ++ p })

/-- **The library's contracts, by name.** -/
def lib (S : Std) (prog : List Byte) (W : Proc.World) : List (Name × (PState → Res PState → Prop)) :=
  [(nm "puts", putsStep S W),
   (nm "fread", errKept (Streams.freadStep S.E W)),
   (nm "fwrite", errKept (Streams.fwriteStep S.E W)),
   (nm "fopen", fopenErrStep S W),
   (nm "fclose", errKept (Streams.fcloseStep S.E W)),
   (nm "__errno_location", Streams.errnoLocStep S.E W),
   (nm "error", errorStep S prog W),
   (nm "__stack_chk_fail", stackChkFailStep),
   (nm "read", readStep S W),
   (nm "write", writeStep S W)]

/-- A table of library contracts, by name (`lib` is the standard one). The trusted base of a
`Verified` claim: the claim holds for every library meeting the table's contracts. -/
abbrev LibTable := Std → List Byte → Proc.World → List (Name × (PState → Res PState → Prop))

/-! ## 4. The process of a program, for a world -/

/-- The process world before the import contracts are attached (they refer to it). -/
def world0 (B : Bin) (b lb gate : Word) (rel : Bool) (args tls : Nat → Prop) : Proc.World where
  base := b
  size := B.layout.size
  inits := [b + BitVec.ofNat 64 B.layout.init, b + BitVec.ofNat 64 B.layout.fdummy]
  finis := [b + BitVec.ofNat 64 B.layout.dtors, b + BitVec.ofNat 64 B.layout.fini]
  gate := gate
  lazy := none
  fns := [(lb + BitVec.ofNat 64 B.lsmOff, .libcStartMain), (lb + BitVec.ofNat 64 B.cxaOff, .cxaFinalize)] ++
    B.imports.map fun i => (lb + BitVec.ofNat 64 i.off, Fn.named i.name)
  reliable := rel
  args := args
  tls := tls

/-- The words the library never writes and the program reads: the libc variables `B.vars`
and the stack protector's guard at `%fs:0x28`. -/
def libWords (B : Bin) (lb fs : Word) (a : Nat) : Prop :=
  (∃ v ∈ B.vars, (v.addr 0 lb).toNat ≤ a ∧ a < (v.addr 0 lb).toNat + 8 ∧ v.copy = false) ∨
  ((fs + 0x28#64).toNat ≤ a ∧ a < (fs + 0x28#64).toNat + 8)

/-- **The process of `B` in world `w`**: loaded at `b` (`libc.so.6` at `lb`), the callback
gate, whether writes succeed, the argument area, and the thread pointer `fs`. -/
def world (B : Bin) (S : Std) (w : World) (b lb gate : Word) (rel : Bool) (args : Nat → Prop)
    (fs : Word) (L : LibTable := lib) : Proc.World :=
  let W0 := world0 B b lb gate rel args (libWords B lb fs)
  { W0 with
    named := Streams.namedOf (L S (ofSpec w.argv0) W0)
    atMain := AtMain B S b lb w
    pending := Pending S }

/-- **The arguments** at `argv`: the vector of pointers and the C strings of `w.argv`, all in
the argument area (which the library never writes). -/
def ArgvAt (W : Proc.World) (w : World) (argv : Word) (m : Memory) : Prop :=
  ∀ i (hi : i < w.argv.length), ∃ p, loadN m (argv + BitVec.ofNat 64 (8 * i)) 8 = some p ∧
    CStr m p (ofSpec (w.argv[i]'hi)) ∧
    (∀ k < 8, W.args ((argv + BitVec.ofNat 64 (8 * i)).toNat + k)) ∧
    (∀ j ≤ (w.argv[i]'hi).length, W.args (p.toNat + j))

/-- **The initial state** of the process for world `w` (what `execve` and `ld.so` hand to
`_start`): `rip` at `_start`, the stack 16-byte aligned with `argc`, the `argv` vector and the
argument strings (in the argument area), a usable stack page, and the library's ghost state
fresh. -/
structure AtStart (B : Bin) (W : Proc.World) (w : World) (b : Word) (s : PState) : Prop where
  g : s.g = { jobs := [], out := [], atexit := [], done := none, inp := stdinBytes w }
  rip : s.m.core.rip = b + BitVec.ofNat 64 B.layout.start
  al : (s.m.core.read .rsp).toNat % 16 = 0
  room : Proc.StackRoom W s.m.memory (s.m.core.read .rsp)
  argc : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [BitVec.ofNat 64 w.argv.length])
  argv : ArgvAt W w (s.m.core.read .rsp + 8#64) s.m.memory
  /-- The thread pointer: the stack protector's guard word is readable. -/
  fs : ∃ g, loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g

/-- **Where the loader put things**: the image does not wrap; every import the world binds
and the gate lie outside it; the gate is none of them. -/
structure Placed (B : Bin) (b lb gate : Word) : Prop where
  hb : b.toNat + B.layout.size < 2 ^ 64
  gate_out : ¬ Crt.Img B.layout b gate.toNat
  out : ∀ o ∈ [B.lsmOff, B.cxaOff] ++ B.imports.map (·.off), ¬ Crt.Img B.layout b (lb + BitVec.ofNat 64 o).toNat
  gate_ne : ∀ o ∈ [B.lsmOff, B.cxaOff] ++ B.imports.map (·.off), lb + BitVec.ofNat 64 o ≠ gate
  cxa_ne : lb + BitVec.ofNat 64 B.cxaOff ≠ 0#64

/-- **How the run ended**: the outcome `o`: the status, the bytes that reached fd 1 and fd 2. -/
def Observed (o : Outcome) (u : PState) : Prop :=
  u.g.done = some (o.status, ofSpec o.stdout) ∧ u.g.err = ofSpec o.stderr

/-- **The end-to-end statement.** For every world of the tier, every `libc.so.6`/`ld.so`
agreeing with the pins, every stdio environment reading the world's file system, every
eager load (any bases, any ifunc choice, any placement), every argument area and every
initial state for the world: every run of the process ends, with outcome `spec w`. -/
def Verified (B : Bin) (libc ld : LibPin) (spec : Spec) (tier : Tier) (L : LibTable := lib)
    (env : Std → Prop := fun _ => True) : Prop :=
  ∀ w, tier w → ∀ (Fc Fl : Blob), ChunksOf Fc libc.chunks → ChunksOf Fl ld.chunks →
  ∀ (S : Std), S.E.fs = w.fs → env S →
  ∀ (b lb ldb res gate : Word) (ifn : Word → Option Word) (args : Nat → Prop) (s : PState),
    Dyn.ExeLoaded [B.file, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory →
    Placed B b lb gate →
    AtStart B (world B S w b lb gate (!w.stdoutFull) args s.m.core.fsBase L) w b s →
    MustQ (world B S w b lb gate (!w.stdoutFull) args s.m.core.fsBase L) (Observed (spec w)) s

end Silmaril.Elf.Link.Dyn.Program
