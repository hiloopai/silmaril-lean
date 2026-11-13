module

public import Silmaril.Wasi.Examples.Defs
public import Silmaril.Machine.Process.IoSpec.Defs
public import Silmaril.Machine.X86.Safe.Defs

@[expose] public section

/-!
# WASI hosts over the OS model of `Silmaril.Machine.Process.IoSpec`

Part D of `docs/projects/wasm-wasi.md`. A WASI host serves the imports of a component; on a real system it does so
by syscalls, answered by the kernel. `Silmaril.Machine.Process.IoSpec` models the kernel side as a
syscall environment `SysEnv` (LPS's process model, through the sound arms of `lpsEnv`) and the
process side as step-indexed safety `IoSafeN` of an x86 machine, with LPS event traces. This
module relates the two levels for the `wasi:cli/stdout` and `wasi:filesystem` slices.

## The OS image of WASI events (the abstraction)

* `osEv ch`: a successful `blocking-write-and-flush(h, bs)` answer of the host is the LPS trace
  `bs.map (writeEv ch)` on the stdout channel `ch`; every other WASI event emits nothing.
  `osTrace ch` is the OS image of an event list. LPS traces are byte-granular, so the image does
  not depend on how the host splits a write into syscalls.
* `hiOut ch`: the OS trace of `hello`'s write.
* `writesOnly bs`: every write request answered by the host carries the bytes `bs`
  (a pointwise guarantee, proved for `hello` with `bs = hi`).
* The filesystem slice. LPS's file system is a flat map from paths to contents (`Fs.FileSystem`),
  and LPS observes it only at exit (`exitEv code fs`), not through events. The OS image of a
  filesystem trace is therefore a *state*: `fsOs fs t` replays the host's answers on `fs`. A
  successful `open-at(d, path)` binds the new descriptor to `path`, creating an empty file.
  A successful `write(f, buf, off)` stores `buf` at `off` in the file bound to `f`
  (`writeAt`). Directories are not modelled: the path is taken as it is.

## The x86 side (the refinement)

* `WriteStub c segs ch e`: the code obligations of an x86 **host stub** writing bytes to stdout
  by `write(1, buf, n)` syscalls, over the machine `c` and segments `segs`, with LPS model `e`
  (stdout bound to the channel `ch`). `st bs` is the stub with the bytes `bs` still to write. It
  is at a `syscall` whose request `lpsEnv`'s `writeArm` handles, with source exactly `bs`. After
  a partial write of `ds` the stub runs, without syscalls, to `st (bs.drop |ds|)`, or to `fin`
  once everything is written. This is musl's `write` in a loop, as a host runtime does for a
  `blocking-write-and-flush`.
* `HelloRt c segs ch e`: an x86 **runtime of `hello`** over that stub: from `start` it runs
  without syscalls to `st hi` (the component's `get-stdout` and the host's handle are internal),
  after the write it runs without syscalls to an `exit(0)` trap (the stream drop and the
  return of `run` are internal; the command then exits with status `0`).

The theorems (`Silmaril.Wasi.Os.Thms`) prove `IoSafeN` with `lpsEnv` for these, with the trace
predicate "a prefix of `hi`, then `exit 0`", and identify that trace as the OS image of
`hello`'s WASI run against the concrete host `stdoutImpl`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Os

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Machine.X86.Safe (SafeN)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Examples (hiBytes)

/-! ## The OS image of the stdout slice -/

/-- **The OS events of a WASI event** on the stdout channel `ch`: a successful write of `bs`
writes `bs` to `ch`. -/
def osEv (ch : Word) : Silmaril.Wasi.WEv → List Event
  | .imp f (_ :: buf :: _) (some [.variant 0 none]) =>
    if f = streamWrite then (bytesOf buf).map (.writeEv ch) else []
  | _ => []

/-- **The OS image of a WASI event list.** -/
def osTrace (ch : Word) (t : List Silmaril.Wasi.WEv) : List Event := t.flatMap (osEv ch)

/-- The OS trace of writing `hi` to `ch`. -/
def hiOut (ch : Word) : List Event := hiBytes.map (.writeEv ch)

/-- Every write request answered by the host carries the bytes `bs`. -/
def writesOnly (bs : List Byte) : Silmaril.Wasi.WEv → Bool
  | .imp f (_ :: buf :: _) _ => !(decide (f = streamWrite)) || decide (bytesOf buf = bs)
  | _ => true

/-! ## The OS image of the filesystem slice -/

/-- The path of a WIT `string`: its characters, truncated to bytes. -/
def pathOf : Val → Fs.Path
  | .record vs => vs.filterMap fun | .char c => some (BitVec.ofNat 8 c.toNat) | _ => none
  | _ => []

/-- `data` with `bs` stored at offset `off` (zero-padded). -/
def writeAt (data : List Byte) (off : Nat) (bs : List Byte) : List Byte :=
  data.take off ++ List.replicate (off - data.length) 0 ++ bs ++ data.drop (off + bs.length)

/-- The OS-side state of the filesystem slice: descriptors bound to paths, and the files. -/
structure FsAbs where
  /-- The descriptors opened so far and their paths. -/
  binds : List (BitVec 32 × Fs.Path)
  /-- The flat file system of LPS. -/
  fs : Fs.FileSystem

/-- The path of a descriptor. -/
def FsAbs.pathOfFd (a : FsAbs) (f : BitVec 32) : Option Fs.Path := (a.binds.find? (·.1 = f)).map (·.2)

/-- One host answer on the OS-side state. -/
def fsStep (a : FsAbs) : Silmaril.Wasi.WEv → FsAbs
  | .imp f (_ :: p :: _) (some [.variant 0 (some (.u32 fd))]) =>
    if f = openAt then
      ⟨(fd, pathOf p) :: a.binds,
        if (Fs.lookup a.fs (pathOf p)).isSome then a.fs else Fs.set a.fs (pathOf p) []⟩
    else a
  | .imp f (.u32 fd :: buf :: .u64 off :: _) (some [.variant 0 _]) =>
    if f = fdWrite then
      match a.pathOfFd fd with
      | some p => ⟨a.binds, Fs.set a.fs p (writeAt ((Fs.lookup a.fs p).getD []) off.toNat (bytesOf buf))⟩
      | none => a
    else a
  | _ => a

/-- **The OS image of a filesystem trace**: the host's answers replayed on `fs`. -/
def fsOs (fs : Fs.FileSystem) (t : List Silmaril.Wasi.WEv) : Fs.FileSystem :=
  (t.foldl fsStep ⟨[], fs⟩).fs

/-- The LPS path of `out.txt`. -/
def outPath : Fs.Path := pathOf (strV "out.txt")

/-! ## The x86 side -/

/-- The trapped native state at the open state `m`, for the flag choice `k`. -/
abbrev trapAt (m : MState) (k : X86FlagChoices.Choice) : X86State := trapped ⟨m, none⟩ k

/-- The syscall request at the open state `m`. -/
abbrev reqAt (segs : List Segment) (m : MState) (k : X86FlagChoices.Choice) : SyscallInput :=
  reqOf segs (trapAt m k)

/-- The effect of a successful partial write of `ds` at `m` (the answer of `writeArm`). -/
def writeEff (segs : List Segment) (m : MState) (k : X86FlagChoices.Choice) (ds : List Byte) :
    SyscallEffect :=
  (mkEffect (lenWord ds) [] []).withCopyins ([((reqAt segs m k).arg 1, ds.length)] ++ [])

/-- **The code obligations of an x86 stdout host stub.** -/
structure WriteStub (c : MState → Option MState) (segs : List Segment) (ch : Word)
    (e : Silmaril.Process.LPS.Model) where
  /-- The stub with the bytes `bs` still to write. -/
  st : List Byte → MState
  /-- The stub after the last byte. -/
  fin : MState
  /-- With bytes left, the stub is at a `syscall`. -/
  trap : ∀ bs, bs ≠ [] → AtSyscall (st bs)
  /-- `writeArm` handles it. -/
  handles : ∀ bs, bs ≠ [] → ∀ k, (writeArm segs).Handles (trapAt (st bs) k) e
  /-- The descriptor is stdout's channel `ch`. -/
  chan : ∀ bs, bs ≠ [] → ∀ k,
    fdLookup e.fds (fd32 ((reqAt segs (st bs) k).arg 0)) = some (.channel ch)
  /-- The source is exactly the bytes left. -/
  source : ∀ bs, bs ≠ [] → ∀ k,
    writeSource (reqAt segs (st bs) k).mem ((reqAt segs (st bs) k).arg 1)
      ((reqAt segs (st bs) k).arg 2) = bs
  /-- After a partial write of `ds`, the stub runs without syscalls to the rest. -/
  next : ∀ bs, bs ≠ [] → ∀ k (ds : List Byte), 1 ≤ ds.length → ds <+: bs →
    ∀ n, SafeN c (fun m => m = if bs.drop ds.length = [] then fin else st (bs.drop ds.length)) n
      (resume (trapAt (st bs) k) (writeEff segs (st bs) k ds))

/-- **An x86 runtime of `hello`** over a stdout host stub. -/
structure HelloRt (c : MState → Option MState) (segs : List Segment) (ch : Word)
    (e : Silmaril.Process.LPS.Model) extends WriteStub c segs ch e where
  /-- The launch state of the runtime. -/
  start : MState
  /-- It runs without syscalls to the write of `hi`. -/
  toWrite : ∀ n, SafeN c (fun m => m = st hiBytes) n start
  /-- The `exit` trap. -/
  exitSt : MState
  /-- After the write it runs without syscalls to the `exit` trap. -/
  toExit : ∀ n, SafeN c (fun m => m = exitSt) n fin
  /-- At a `syscall`. -/
  exitTrap : AtSyscall exitSt
  /-- Number `60` (`exit`). -/
  exitNo : (exitSt.core.read .rax).toNat = 60
  /-- Status `0`. -/
  exitCode : exitSt.core.read .rdi &&& 255 = 0

/-- **Frozen target, refuted** (`Silmaril.Wasi.Runtime.not_helloRt_exists`): an x86 runtime of
`hello` exists on a machine extending the `Ext8` open machine. It is false because `WriteStub`
is empty: `source` asks for every non-empty list as a write source, and LPS reads at most
`MAX_RW_COUNT` bytes per `write`. The corrected target `Silmaril.Wasi.Runtime.Task.helloLoop_exists`
(obligations up to an invariant) is proved with a concrete program. -/
def Task.helloRt_exists : Prop :=
  ∃ (c : MState → Option MState) (segs : List Segment) (ch : Word) (e : Silmaril.Process.LPS.Model),
    Silmaril.Machine.X86.Safe.Refines Silmaril.Machine.X86.Open.step c ∧ Nonempty (HelloRt c segs ch e)

/-- The traces of `hello`'s runtime: a prefix of the write of `hi`, then `exit 0`. -/
def helloAllowed (ch : Word) (fs : Fs.FileSystem) (tr : List Event) : Prop :=
  tr <+: hiOut ch ++ [.exitEv 0 fs]

/-! ## The canonical runs -/

open Silmaril.Wasi.Examples in
/-- The export call `run` of the stdout world. -/
def runQ : (Silmaril.Wasi.nsig stdoutWorld.exports).Op := (⟨cliRun, rfl⟩, [])

open Silmaril.Games Silmaril.Wasi.Examples in
/-- **One run of `hello`** against the concrete host `stdoutImpl`: `run` is called, `get-stdout`
answers handle `0`, the write and the drop succeed, `run` returns `ok`. -/
def helloRun : List (Move (Silmaril.Wasi.nsig stdoutWorld.imports) (Silmaril.Wasi.nsig stdoutWorld.exports)) :=
  [.inr (.ask runQ), .inl (.ask getOp), .inl (.ans getOp (some [.u32 0])),
   .inl (.ask (writeOp 0)), .inl (.ans (writeOp 0) (some [okV none])),
   .inl (.ask (dropOp 0)), .inl (.ans (dropOp 0) (some [])), .inr (.ans runQ (some [okV none]))]

end Silmaril.Wasi.Os
