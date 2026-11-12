module

public import Silmaril.Elf.Link.Dyn.Program.Defs
public import Silmaril.Cli.Institution.Defs

/-!
# A dynamically linked x86 program as a model of the CLI institution

The bridge from the Program API (`Silmaril.Elf.Link.Dyn.Program`: a pinned executable on a
pinned glibc, its `World → Outcome` specification, `Verified`) to the CLI institution
(`Silmaril.Cli.Institution`) at the full level `L3`.

**Invocations as worlds.** `worldOf conv i` is the C-level world of the invocation `i`:
`argv` is the program name and the arguments in UTF-8, `POSIXLY_CORRECT` is read from the
environment, standard input is `i.stdin` (a byte stream), stdout is not a full device, and the
read oracle looks a path up through the path convention `conv : PathConv` (a path that names
no file of `i.fs`, or that `conv` cannot place, fails to open with `ENOENT`). The invocation's
file system has no directories, permissions or read errors, so the worlds of invocations are
those whose reads succeed or fail with `ENOENT`.

**Specifications.** `toCli conv spec tier` is the program's `World → Outcome` specification as
a `Silmaril.Cli.Spec`: on an invocation whose world is in the tier, stdout, stderr and the exit
code (the status modulo 256) are those of `spec`, and no file changed. Consumption, reads and
the file log are not constrained (the Program API does not observe them).

**The model.** `x86Model B libc ld L env conv` is the CLI semantics of the process model behind
`Verified`: a run on `i` is a load of `B` with libraries agreeing with the pins (any bases, any
ifunc choice, any placement), a stdio environment reading the world's files and meeting `env`,
an initial state for the world, and a finite run of the process machine
(`Proc.proc (world …)`, the executable's instructions and the library contracts `L`) to an
ended state. Its observation: the bytes on fd 1 and fd 2, the status as an exit code, the stdin
bytes consumed (`Ghost.inp`), the files unchanged (the contracts open files read-only), no
refusal, no file events.

`x86Model_sat` (`Thms`): **a `Verified` program is a model of `toCli spec tier`**.

**Trusted** (as for `Verified`): the loader relation, the process machine, the library
contracts `L` and the world/outcome bridge rows of `Program`; here also the reading of an
invocation as a world (`worldOf`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program

open Silmaril.Cli (Input Obs FPath)
open Silmaril.Cli.Institution (Level Model)
open Silmaril.X86 (Word Byte)
open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.Dyn.Proc (PState)
open Silmaril.Elf.Link.Dyn.Streams (toSpec ofSpec)
open Silmaril.Apps.Sha256sum (ReadResult Errno Stdin)

/-! ## Invocations as worlds -/

/-- **A path convention**: the file of the invocation a byte path names, if any. -/
abbrev PathConv : Type := List UInt8 → Option FPath

/-- The bytes of a path split at `/`, without empty components and `.`; each component read
byte by byte as characters (exact for ASCII names). -/
def pathComps (p : List UInt8) : List String :=
  ((Silmaril.Apps.Sha256sum.splitOn 47 p).filter fun c => !c.isEmpty && c != [46]).map
    fun c => String.ofList (c.map fun b => Char.ofNat b.toNat)

/-- **The working-directory convention**: a relative path names a file under the root `"."`
(its components below it); an absolute path under the root `"/"`. -/
def PathConv.cwd : PathConv := fun p =>
  if p.head? = some 47 then some ⟨"/", pathComps p⟩ else some ⟨".", pathComps p⟩

/-- **The read oracle of an invocation's files.** -/
def readOf (conv : PathConv) (i : Input) (p : List UInt8) : ReadResult :=
  match conv p >>= i.fs with
  | some d => .ok d
  | none => .openErr .ENOENT

/-- **The C-level world of an invocation.** -/
def worldOf (conv : PathConv) (i : Input) : World where
  argv := (i.prog :: i.args).map Silmaril.Cli.utf8
  posix := (i.getEnv "POSIXLY_CORRECT").isSome
  fs := readOf conv i
  stdin := .bytes i.stdin
  stdoutFull := false

/-! ## Specifications -/

/-- **A Program specification as a CLI specification** (level `L3`): on an invocation whose world
is in the tier, the outcome of `spec`, and no file changed. -/
def toCli (conv : PathConv) (spec : Spec) (tier : Tier) : Silmaril.Cli.Spec := fun i o =>
  tier (worldOf conv i) →
    o.stdout = (spec (worldOf conv i)).stdout ∧ o.stderr = (spec (worldOf conv i)).stderr ∧
      o.exit = UInt8.ofNat (spec (worldOf conv i)).status ∧ o.fs = i.fs

/-! ## The model -/

/-- One successful step of the process machine. -/
def OkStep (W : Proc.World) (s t : PState) : Prop := (Proc.proc W).step s (.ok t)

/-- **A run of `B` on the invocation `i`, observed as `o`**: some load, environment and initial
state allowed by `Verified`'s hypotheses, and a finite run of the process to an ended state. -/
def Run (B : Bin) (libc ld : LibPin) (L : LibTable) (env : Std → Prop) (conv : PathConv)
    (i : Input) (o : Obs) : Prop :=
  ∃ (Fc Fl : Blob) (S : Std) (b lb ldb res gate : Word) (ifn : Word → Option Word)
    (args : Nat → Prop) (s u : PState) (st : Nat) (out : List Byte),
    ChunksOf Fc libc.chunks ∧ ChunksOf Fl ld.chunks ∧ S.E.fs = (worldOf conv i).fs ∧ env S ∧
    Dyn.ExeLoaded [B.file, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory ∧
    Placed B b lb gate ∧
    AtStart B (world B S (worldOf conv i) b lb gate (!(worldOf conv i).stdoutFull) args
      s.m.core.fsBase L) (worldOf conv i) b s ∧
    Relation.ReflTransGen (OkStep (world B S (worldOf conv i) b lb gate
      (!(worldOf conv i).stdoutFull) args s.m.core.fsBase L)) s u ∧
    u.g.done = some (st, out) ∧
    o = { stdout := toSpec out, stderr := toSpec u.g.err, exit := UInt8.ofNat st,
          consumed := i.stdin.length - u.g.inp.length, fs := i.fs }

/-- **The CLI model of a pinned executable on a pinned glibc** (level `L3`). -/
def x86Model (B : Bin) (libc ld : LibPin) (L : LibTable := lib) (env : Std → Prop := fun _ => True)
    (conv : PathConv := .cwd) : Model Level.full.sig :=
  ⟨Run B libc ld L env conv⟩

end Silmaril.Elf.Link.Dyn.Program
