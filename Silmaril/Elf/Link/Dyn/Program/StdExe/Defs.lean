module

public import Silmaril.Elf.Link.Dyn.Program.Cli.Defs
public import Silmaril.Elf.Link.Dyn.Program.Glibc
public import Silmaril.Elf.Link.Dyn.Stdio.Defs

/-! # A standard executable: one binary, the standard linker, glibc

The Program API (`Silmaril.Elf.Link.Dyn.Program`) is general: any pinned executable, any pinned
`libc.so.6`/`ld.so`, any table of library contracts, any environment assumption, any tier of
worlds. **A standard executable** is the common case, a C program compiled by gcc or clang
`-O2`, linked by the system linker (`ld.bfd`, default PIE, dynamic) against the pinned glibc,
as `hello`, `cat` or an adder. `StdExe` names exactly what such a claim is about:

| field | what | default |
|---|---|---|
| `bin` | the ELF: its bytes (`bin.file`) and generated facts (a generator, checked by `Bin.ok`) | |
| `sha256` | the pinned file's hash (`examples/dyn/pins.txt`; documentation, not checked here) | |
| `glibc` | the glibc pin: `libc.so.6` and `ld.so` lookup pins | glibc 2.39 (`glibc239`) |
| `cc` | the compiler whose start-up shape surrounds `main` (`Cc.gcc`, `Cc.clang`) | `gcc` |
| `spec` | the specification, `World → Outcome` (read at a CLI level by `StdExe.cli`) | |
| `tier` | the worlds the claim is about | `Tier.reliable` |
| `env` | the library's environment assumption | none |
| `L` | the table of library contracts | `Program.lib` |

`StdExe.Verified E` is **by definition** `Program.Verified E.bin libc ld E.spec E.tier E.L E.env`
(by default the standard contract table `lib`): nothing new is trusted, and every theorem about
`Program.Verified` applies (`StdExe.verified_iff`, `Thms`). The CLI reading is
`E.cli = toCli .cwd E.spec E.tier` in the model `E.model = x86Model …`
(`Silmaril.Elf.Link.Dyn.Program.Cli`), so `E.Verified → E.model.Sat E.cli`;.

**`main`'s entry, fully initialised.** `Entry` records what the loader, `_start` and
`__libc_start_main` hand `main` (proved once, `Program.verified` through `Crt.crt_run'`): `argc`
and `argv`, the three standard streams, the library's ghost state, the thread pointer and the
stack guard, the stack page and its alignment. The tactic `at_main` (`StdExe.Tactic`) puts it in
context.

**The glibc-opaque view.** `GlibcView S m` is what `main` may know of the library's state: the
three standard streams, opaquely (`Streams.StreamRep`: any representation), and that the
library's private memory (stdio buffers, the `malloc` arena, the locale, TLS and `errno`) lies
below the stack. A proof of `main` is a proof for every `Std`, so it cannot depend on glibc's
internals; `Thms` gives the frame lemmas of the view and the outlining lemmas of the code
compilers inline (`putc`'s fast path, the stack protector, `printf` of a literal as `puts`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Ext (loadN)
open Silmaril.Process (Memory)
open Silmaril.Elf.Link.Dyn.Proc (PState StackRoom)
open Silmaril.Elf.Link.Dyn.Streams (StdoutIs)
open Silmaril.Cli.Institution (Level Model Sen)

/-- **The compiler** whose code surrounds `main` (the C runtime's objects are glibc's `crt1.o`,
`crti.o`/`crtn.o` and GCC 13's `crtbegin`/`crtend` for both). -/
inductive Cc where
  /-- Ubuntu gcc 13 `-O2`: `-fcf-protection` (`endbr64`, `.plt.sec` stubs), `-z now`. -/
  | gcc
  /-- Ubuntu clang 18 `-O2`: no `endbr64` in the image's own code, lazy `.plt` stubs. -/
  | clang
  deriving DecidableEq, Repr

/-- Whether the compiler's start-up code begins with `endbr64` (the runtime layout's `ibt`). -/
def Cc.ibt : Cc → Bool
  | .gcc => true
  | .clang => false

/-- **A glibc pin**: the lookup pins of `libc.so.6` and `ld.so`, checked, and the distribution
version they were taken from (documentation). -/
structure GlibcPin where
  libc : LibPin
  ld : LibPin
  version : String
  ok : libc.ok = true ∧ ld.ok = true

/-- glibc 2.39 (Ubuntu `libc6` 2.39-0ubuntu8.9), the pins of `Program.Glibc`. -/
def glibc239 : GlibcPin := ⟨libc, ld, "2.39-0ubuntu8.9", libc_ok, ld_ok⟩

/-- **A standard executable** and its claim. -/
structure StdExe where
  /-- The ELF: its bytes and generated facts. -/
  bin : Bin
  /-- The sha256 of the pinned file (documentation: `examples/dyn/pins.txt`). -/
  sha256 : String
  /-- The glibc it is run against. -/
  glibc : GlibcPin := glibc239
  /-- The compiler. -/
  cc : Cc := .gcc
  /-- The specification. -/
  spec : Spec
  /-- The worlds the claim is about. -/
  tier : Tier := Tier.reliable
  /-- The library's environment assumption. -/
  env : Std → Prop := fun _ => True
  /-- The table of library contracts (the trusted base). -/
  L : LibTable := lib

namespace StdExe

/-- **The one per-binary check**: `Bin.ok` against the pin, and the runtime's shape is the
compiler's. -/
def ok (E : StdExe) : Bool := E.bin.ok E.glibc.libc E.glibc.ld && (E.bin.layout.ibt == E.cc.ibt)

/-- **The claim**: `Program.Verified`, by definition. -/
def Verified (E : StdExe) : Prop :=
  Program.Verified E.bin E.glibc.libc E.glibc.ld E.spec E.tier E.L E.env

/-- The CLI model of the executable (`L3`): the Program API's process model. -/
def model (E : StdExe) (conv : PathConv := .cwd) : Model Level.full.sig :=
  x86Model E.bin E.glibc.libc E.glibc.ld E.L E.env conv

/-- **The specification as a CLI specification** (`L3`). -/
def cli (E : StdExe) (conv : PathConv := .cwd) : Silmaril.Cli.Spec := toCli conv E.spec E.tier

/-- The executable's process world for a run (`Program.world`). -/
abbrev W (E : StdExe) (S : Std) (w : World) (b lb gate fs : Word) (args : Nat → Prop) : Proc.World :=
  world E.bin S w b lb gate (!w.stdoutFull) args fs E.L

end StdExe

/-! ## `main`'s entry, fully initialised -/

/-- **What `main` finds at its entry `t`** in world `w`, process world `W`, with the library `S`:
`argc` and `argv` (the C strings of `w.argv`, in memory the library never writes), the three
standard streams (`stdin` reads `w.stdin`, nothing buffered on `stdout`/`stderr`) and the libc
variables holding them, the library's ghost state (the unread input is `w.stdin`, nothing
written, no allocation, no open stream, `main`'s return the one job left), the thread pointer
and the stack protector's guard word, the stack page (usable, outside the image, above the
library's memory) and the System V alignment. -/
structure Entry (B : Bin) (S : Std) (w : World) (W : Proc.World) (b lb fs argv : Word) (t : PState) :
    Prop where
  argc : t.m.core.read .rdi = ((BitVec.ofNat 64 w.argv.length).setWidth 32).setWidth 64
  argvReg : t.m.core.read .rsi = argv
  argv : ArgvAt W w argv t.m.memory
  stdin : S.E.S.file t.m.memory S.stdinF (stdinSt w)
  stdout : StdoutIs S.E t.m.memory (outSt 1)
  stderr : S.E.S.file t.m.memory S.E.stderrF (outSt 2)
  vars : ∀ v ∈ B.vars, loadN t.m.memory (v.addr b lb) 8 =
    some (if v.name = nm "stdin" then S.stdinF else if v.name = nm "stdout" then S.E.stdoutF
      else S.E.stderrF)
  inp : t.g.inp = stdinBytes w
  out : t.g.out = []
  err : t.g.err = []
  jobs : t.g.jobs = [.exitRax]
  fresh : t.g.allocs = 0 ∧ t.g.heap = 0 ∧ t.g.files = 0
  tls : t.m.core.fsBase = fs
  guard : ∃ g, loadN t.m.memory (fs + 0x28#64) 8 = some g
  stack : StackRoom W t.m.memory (t.m.core.read .rsp)
  align : (t.m.core.read .rsp).toNat % 16 = 8
  lo : S.E.S.lo + 0x100000 ≤ (t.m.core.read .rsp).toNat
  errno : S.E.ErrnoLo

/-- The library word `main` reads at its entry: the stack protector's guard `g` at `%fs:0x28`
(the library words of the frame bundle `at_main` starts with). -/
abbrev guardKL (fs g : Word) : List (Nat × List Byte) :=
  [((fs + 40#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [g])]

/-! ## The glibc-opaque view -/

/-- **What `main` knows of glibc's state** in memory `m`: the standard streams `stdin`
(`stdinF`), `stdout` and `stderr` are streams in some states, and the library's private memory
and streams lie below `lo`, under the stack pointer `sp`. Nothing else: stdio buffers, the
`malloc` arena, the locale, TLS and `errno` are behind the representation `S.E.S` (any
representation meeting `Streams.StreamRep`'s laws). -/
def GlibcView (S : Std) (sp : Word) (m : Memory) : Prop :=
  (∃ st, S.E.S.file m S.stdinF st) ∧ (∃ st, StdoutIs S.E m st) ∧ (∃ st, S.E.S.file m S.E.stderrF st) ∧
    S.E.S.lo + 0x100000 ≤ sp.toNat ∧ S.E.ErrnoLo

/-! ## Formatted I/O: a larger contract table

`libStdio` extends the standard table `lib` with `scanf ("%d %d", …)` (`__isoc99_scanf`) on the
stream `stdin` and `printf ("%d\n", …)` (`printf`, and `__printf_chk` as `_FORTIFY_SOURCE`
compiles it) on `stdout`, in the Program API's stream model (`Streams.StreamRep`, `LibRet`,
`Appended`). It is a new table, not a change of `lib`: a program that calls none of the three
names runs the same under both (the contracts are looked up by name). The formats and their
bytes are `Silmaril.Elf.Link.Dyn.Stdio`'s (`scanDD`, `decStr`), as in the `Small` adder proofs.
Trusted: that glibc 2.39's `__isoc99_scanf`, `printf` and `__printf_chk` behave so for these two
formats. -/

/-- **`scanf ("%d %d", rsi, rdx)`** (`__isoc99_scanf`) on the stream `stdin`, by `Stdio.scanDD` of
its unread bytes: both converted, it stores them in the two disjoint `int` objects, returns 2 and
consumes them; a matching failure returns something else; an `int` overflow is undefined (no
claim). `stdout` and the other streams are kept, the library's ghost state is unchanged. -/
def scanfDDStep (S : Std) (W : Proc.World) (s : PState) : Silmaril.X86.RelIsa.Res PState → Prop :=
  let p := s.m.core.read .rsi
  let q := s.m.core.read .rdx
  Proc.Contract (Silmaril.X86.FnContract.AbiEntry s.m.core s.m.memory ∧
      Proc.CStr s.m.memory (s.m.core.read .rdi) Stdio.fmtDD ∧ (∃ st, S.E.S.file s.m.memory S.stdinF st) ∧
      s.m.memory.Permitted .write p.toNat 4 ∧ s.m.memory.Permitted .write q.toNat 4 ∧
      s.m.memory.Permitted .read p.toNat 4 ∧ s.m.memory.Permitted .read q.toNat 4 ∧
      (p.toNat + 4 ≤ q.toNat ∨ q.toNat + 4 ≤ p.toNat) ∧
      (∀ a, (p.toNat ≤ a ∧ a < p.toNat + 4) ∨ (q.toNat ≤ a ∧ a < q.toNat + 4) →
        ¬ S.E.S.priv s.m.memory a ∧ ¬ W.Kept a))
    fun t => Streams.LibRet S.E W (fun a => (p.toNat ≤ a ∧ a < p.toNat + 4) ∨ (q.toNat ≤ a ∧ a < q.toNat + 4))
      s t ∧ t.g = s.g ∧
      Streams.OthersKept S.E s t [S.stdinF] ∧
      (∀ st, StdoutIs S.E s.m.memory st → StdoutIs S.E t.m.memory st) ∧
      ∀ st, S.E.S.file s.m.memory S.stdinF st →
        match Stdio.scanDD st.rd with
        | .ub => True
        | .ok a b rest => S.E.S.file t.m.memory S.stdinF { st with rd := rest } ∧
            Proc.low32 (t.m.core.read .rax) = 2#32 ∧
            t.m.memory.readBytes p.toNat 4 = some (Stdio.le32 a) ∧
            t.m.memory.readBytes q.toNat 4 = some (Stdio.le32 b)
        | .fail => Proc.low32 (t.m.core.read .rax) ≠ 2#32

/-- **`printf ("%d\n", x)`** with the format in `fr` and `x` in the low half of `vr`: appends the
decimal digits of `x` and a newline to `stdout`. -/
def printfDNStep (fr vr : Silmaril.X86.Reg) (S : Std) (W : Proc.World) (s : PState) :
    Silmaril.X86.RelIsa.Res PState → Prop :=
  Proc.Contract (Silmaril.X86.FnContract.AbiEntry s.m.core s.m.memory ∧
      Proc.CStr s.m.memory (s.m.core.read fr) Stdio.fmtDN ∧ ∃ st, StdoutIs S.E s.m.memory st)
    fun t => Streams.LibRet S.E W (fun _ => False) s t ∧ OutOnly s t ∧
      Streams.OthersKept S.E s t [S.E.stdoutF] ∧
      Streams.Appended S.E W s t (Stdio.decStr (Proc.low32 (s.m.core.read vr)).toInt ++ [10])

/-- **The standard table with formatted I/O.** -/
def libStdio : LibTable := fun S prog W =>
  lib S prog W ++ [(nm "__isoc99_scanf", scanfDDStep S W), (nm "__printf_chk", printfDNStep .rsi .rdx S W),
    (nm "printf", printfDNStep .rdi .rsi S W)]

/-! ## Open tasks -/

/-- **Open (`Task`): `libStdio` is conservative over `lib`.** A program that imports none of
`__isoc99_scanf`, `__printf_chk`, `printf` runs the same under both tables (the contracts are
looked up only for the imports, `world0`'s `fns`), so a claim against `lib` holds against
`libStdio`. Not a case of `Verified.mono` (`LibTable.Le lib libStdio` is false: under `lib` the
three names stop). Neither proved nor refuted. -/
def Task.libStdioConservative : Prop :=
  ∀ (B : Bin) (libc ld : LibPin) (spec : Spec) (tier : Tier) (env : Std → Prop),
    (∀ i ∈ B.imports, i.name ≠ nm "__isoc99_scanf" ∧ i.name ≠ nm "__printf_chk" ∧ i.name ≠ nm "printf") →
    Program.Verified B libc ld spec tier lib env → Program.Verified B libc ld spec tier libStdio env

end Silmaril.Elf.Link.Dyn.Program
