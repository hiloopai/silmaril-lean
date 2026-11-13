module

public import Silmaril.Cli.Behaviour.Defs
public import Silmaril.Machine.Process.IoSpec.Defs

/-!
# CLI specifications over the OS model of `Silmaril.Machine.Process.IoSpec`

The behaviour part of `docs/projects/wasm-binaryen-tooling.md`. A process of Silmaril's LPS model (an x86 program
whose syscalls LPS answers) emits byte-granular events: `readEv ch b`, `writeEv ch b`, and a
final `exitEv code fs` (the file system is observed only at exit). `IoSafeN` and the bridge's
`PSafeF` state safety of a process for a trace predicate `Allowed : List Event → Prop` over
every finite run. This module gives the trace predicate of a CLI spec, so that "this process
meets the CLI spec `S` on the invocation `i`" is an `IoSpec`/`PSafeF` statement.

* `Wiring`: how the invocation appears to LPS: the channels of stdin, stdout and stderr, and
  where each rooted path lives in LPS's flat file system (`mount`). Stdout and stderr are
  meant to be different channels (`2>&1` is not a wiring).
* `written ch tr`, `readFrom ch tr`: the bytes written to, and read from, the channel `ch`.
* `Consistent w i o tr`: the (possibly unfinished) trace `tr` is consistent with the
  observation `o`: it emits only expected events (reads from stdin, writes to stdout or
  stderr, an exit; never a kill), what it wrote and read so far are prefixes of `o`'s stdout,
  stderr and consumed stdin, and if it has exited, the exit is its last event, the streams are
  exactly `o`'s, the status is `o`'s exit code and the files under the declared roots are
  `o`'s files.
* **`Allowed S w i tr`**: `tr` is consistent with some observation that `S` allows on `i`.
  Prefix-consistency makes it a *safety* property: a process never writes a byte that no
  allowed observation has, and a finished run is an allowed observation.
* **`Sat segs refused S w i cfg`**: the LPS configuration `cfg` is process-safe (`PSafeF`)
  for `Allowed S w i`.

What LPS does not observe stays loose: files read (LPS has no read events for files), and
the files outside the declared roots.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Os

open Silmaril.Process.LPS (Event Word Byte)
open Silmaril.Machine.Process.LpsBridge

/-- An LPS byte. -/
def byte (b : UInt8) : Byte := b.toBitVec

/-- Bytes as LPS bytes. -/
def lpsBytes (bs : Bytes) : List Byte := bs.map byte

/-- An exit code as LPS's exit status word. -/
def exitWord (c : ExitCode) : Word := BitVec.ofNat 64 c.toNat

/-- **How an invocation appears to LPS.** -/
structure Wiring where
  /-- The channel stdin is read from. -/
  inCh : Word := 0
  /-- The channel stdout is written to. -/
  outCh : Word := 1
  /-- The channel stderr is written to. -/
  errCh : Word := 2
  /-- The LPS path of a rooted path. -/
  mount : FPath → Silmaril.Process.LPS.Fs.Path

/-- The events a CLI process may emit under the wiring `w`. -/
def Wiring.Expected (w : Wiring) : Event → Prop
  | .readEv c _ => c = w.inCh
  | .writeEv c _ => c = w.outCh ∨ c = w.errCh
  | .exitEv _ _ => True
  | .killEv _ _ => False

/-- The bytes written to the channel `ch`. -/
def written (ch : Word) : List Event → List Byte
  | [] => []
  | .writeEv c b :: t => if c = ch then b :: written ch t else written ch t
  | _ :: t => written ch t

/-- The bytes read from the channel `ch`. -/
def readFrom (ch : Word) : List Event → List Byte
  | [] => []
  | .readEv c b :: t => if c = ch then b :: readFrom ch t else readFrom ch t
  | _ :: t => readFrom ch t

/-- An exit event. -/
def IsExit : Event → Prop
  | .exitEv _ _ => True
  | _ => False

/-- The LPS file system `lfs` holds the files `fs` at every path under a declared root of
`i`. -/
def FsAgrees (w : Wiring) (i : Input) (fs : Fs) (lfs : Silmaril.Process.LPS.Fs.FileSystem) :
    Prop :=
  ∀ p, i.Under p → Silmaril.Process.LPS.Fs.lookup lfs (w.mount p) = (fs p).map lpsBytes

/-- **The trace `tr` is consistent with the observation `o` of the invocation `i`.** -/
def Consistent (w : Wiring) (i : Input) (o : Obs) (tr : List Event) : Prop :=
  (∀ ev ∈ tr, w.Expected ev) ∧
  written w.outCh tr <+: lpsBytes o.stdout ∧
  written w.errCh tr <+: lpsBytes o.stderr ∧
  readFrom w.inCh tr <+: lpsBytes (i.stdin.take o.consumed) ∧
  ∀ pre code lfs post, tr = pre ++ .exitEv code lfs :: post →
    post = [] ∧ written w.outCh pre = lpsBytes o.stdout ∧
    written w.errCh pre = lpsBytes o.stderr ∧
    readFrom w.inCh pre = lpsBytes (i.stdin.take o.consumed) ∧
    code = exitWord o.exit ∧ FsAgrees w i o.fs lfs

/-- **The LPS traces a CLI spec allows** on the invocation `i`. -/
def Allowed (S : Spec) (w : Wiring) (i : Input) (tr : List Event) : Prop :=
  ∃ o, S i o ∧ Consistent w i o tr

/-- **An LPS configuration meets the CLI spec `S`** on the invocation `i`: it is process-safe
for the traces `S` allows. -/
def Sat {oracle : Oracle} {nstep : NStep}
    (segs : List Silmaril.Process.LPS.Segment) (refused : Silmaril.Process.LPS.RefusalFilter)
    (S : Spec) (w : Wiring) (i : Input)
    (cfg : Silmaril.Process.LPS.Config (flagMachine oracle nstep)) : Prop :=
  PSafeF segs refused (Allowed S w i) cfg

end Silmaril.Cli.Os
