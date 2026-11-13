module

public import Silmaril.Wasi.Cli.Defs
public import Silmaril.Cli.Args.Defs

/-!
# The WASI 0.3 CLI view: stdout, stderr, stdin, files and exit codes

`p3View` (`Silmaril.Wasi.Cli.Defs`) reads stdout only (the OS image `osTrace3`), takes stdin as a
parameter and reads the exit code of `run` or `exit`. `p3CliView` reads everything a CLI run
shows in WASI 0.3, from the canonical ABI events of the world `p3CliWorld`:

* **streams and sinks**: `stream.new` answers a readable and a writable end; handing the
  readable end to `wasi:cli/stdout.write-via-stream`, `wasi:cli/stderr.write-via-stream` or
  `wasi:filesystem/types.[method]descriptor.write-via-stream(fd, r, offset)` makes its writable
  end a **sink** (`Sink`: stdout, stderr, or the file of `fd` at `offset`);
* **writes**: the bytes a `stream.write` on a sink's writable end delivered (`COMPLETED k` or
  `DROPPED k`: the first `k` bytes; `DROPPED` is also a refusal), or, after `BLOCKED`, the
  bytes the `STREAM_WRITE` event of `waitable-set.wait` (code `3`) reports; a file sink's
  offset advances by the bytes written;
* **stdin**: the readable ends `wasi:cli/stdin.read-via-stream` answered; the bytes of a
  `stream.read` on one (`COMPLETED k`/`DROPPED k`), or of a `STREAM_READ` event (code `2`) in
  the data-carrying 4-element form of `Silmaril.Project.WasmP3Rust.DenX` (`[code, index, payload,
  data]`);
* **files**: descriptors from `get-directories` and `open-at` (as `p2View` follows them,
  `fdStep`); a `[method]descriptor.read-via-stream(fd, offset)` answered with a stream is a
  read of the file of `fd`;
* **exit**: the first of `run`'s return (`ok` 0, `error` 1, a trap `trapExit`),
  `wasi:cli/exit.exit(result)` and `wasi:cli/exit.exit-with-code(code)` (the code itself).

On a trace with only `wasi:cli/stdout` streams the stdout read is `p3View`'s (`osTrace3`
follows the same pairs, sinks and pending writes); that equality is not proved here.

Not read: `append-via-stream`, truncation by `open-at` flags, the futures of
`write-via-stream` (a host's late failure after accepting bytes), directory operations.

A Silmaril addition; `docs/projects/wasm-binaryen-tooling.md`.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli

open Silmaril.Cli
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult)
open Silmaril.Wasi.Versions.P3 (natOf copyOf cStreamNew cStreamWrite cStreamRead cWait stdoutWrite3
  stdinRead3 getDirs3 openAt3 readVia3 run3 p3World)

/-! ## Names -/

namespace W3

/-- `wasi:cli/environment@0.3.2.get-arguments` (as `Versions.Cli3More.getArgs3`). -/
def getArgs : FnName := ⟨"wasi:cli/environment@0.3.2", "get-arguments"⟩
/-- `wasi:cli/environment@0.3.2.get-environment`. -/
def getEnv : FnName := ⟨"wasi:cli/environment@0.3.2", "get-environment"⟩
/-- `wasi:cli/exit@0.3.2.exit-with-code` (`vendor/wasi/0.3.2/cli/exit.wit`). -/
def exitCode : FnName := ⟨"wasi:cli/exit@0.3.2", "exit-with-code"⟩
/-- `wasi:cli/stderr@0.3.2.write-via-stream`. -/
def stderrWrite : FnName := ⟨"wasi:cli/stderr@0.3.2", "write-via-stream"⟩
/-- `wasi:filesystem/types@0.3.2.[method]descriptor.write-via-stream(data, offset)`. -/
def writeVia : FnName := ⟨"wasi:filesystem/types@0.3.2", "[method]descriptor.write-via-stream"⟩

end W3

/-- **The WASI 0.3 CLI world**: the 0.3 slice `p3World`, `get-arguments`, `get-environment`,
`exit`, `exit-with-code`, stderr and `descriptor.write-via-stream`; the export `run`. -/
def p3CliWorld : World :=
  ⟨p3World.imports ∪ {W3.getArgs, W3.getEnv, exit3, W3.exitCode, W3.stderrWrite, W3.writeVia},
    {run3}⟩

/-! ## The scan -/

/-- Where a writable end's bytes go. -/
inductive Sink where
  | stdout
  | stderr
  | file (p : FPath) (off : Nat)
  deriving DecidableEq

/-- What an event shows. -/
inductive Out3 where
  /-- Bytes delivered to a sink. -/
  | out (k : Sink) (b : List (BitVec 8))
  /-- Stdin bytes delivered. -/
  | inp (b : List (BitVec 8))
  /-- A file read. -/
  | read (p : FPath)
  /-- A refusal (a write answered `DROPPED`). -/
  | refused

/-- The state of the scan. -/
structure Sc3 where
  /-- Descriptors, as `p2View` follows them. -/
  fds : Fds := []
  /-- The ends of the streams created (readable, writable). -/
  pairs : List (Nat × Nat) := []
  /-- The sinks of writable ends (the latest first). -/
  sinks : List (Nat × Sink) := []
  /-- The buffer of the latest blocked write of a writable end. -/
  pend : List (Nat × List (BitVec 8)) := []
  /-- The readable ends of stdin. -/
  ins : List Nat := []

/-- The readable end a sink-making call hands over, and the sink. -/
def sinkCall (fds : Fds) (f : FnName) : List Val → Option (Nat × Sink)
  | [rv] =>
    if f = stdoutWrite3 then (natOf rv).map (·, .stdout)
    else if f = W3.stderrWrite then (natOf rv).map (·, .stderr)
    else none
  | [.u32 fd, rv, .u64 off] =>
    if f = W3.writeVia then
      match natOf rv, fds.lookup fd with
      | some r, some p => some (r, .file p off.toNat)
      | _, _ => none
    else none
  | _ => none

/-- Deliver bytes on the writable end `w`. -/
def Sc3.deliver (q : Sc3) (w : Nat) (b : List (BitVec 8)) : Sc3 × List Out3 :=
  match q.sinks.lookup w with
  | some (.file p off) =>
    ({ q with sinks := (w, .file p (off + b.length)) :: q.sinks }, [.out (.file p off) b])
  | some k => (q, [.out k b])
  | none => (q, [])

/-- The 0.2 names of the descriptor functions, to follow descriptors with `fdStep`. -/
def as2 : WEv → WEv
  | .imp f a r =>
    if f = getDirs3 then .imp getDirs a r else if f = openAt3 then .imp openAt a r else .imp f a r
  | e => e

/-- A `stream.write` answer: the copy result. -/
def copyAns : Option (List Val) → Option (Option (CopyResult × Nat))
  | some [pv] => natOf pv >>= copyOf
  | _ => none

/-- A `stream.write` on `w` of `bs`, answered `c`. -/
def Sc3.wrote (q : Sc3) (w : Nat) (bs : List (BitVec 8)) :
    Option (Option (CopyResult × Nat)) → Sc3 × List Out3
  | some (some (.completed, k)) => q.deliver w (bs.take k)
  | some (some (.dropped, k)) => let r := q.deliver w (bs.take k); (r.1, r.2 ++ [.refused])
  | some none => ({ q with pend := (w, bs) :: q.pend }, [])
  | _ => (q, [])

/-- A `waitable-set.wait` answer. -/
def Sc3.waited (q : Sc3) : Option (List Val) → Sc3 × List Out3
  | some [cv, iv, pv] =>
    match natOf cv, natOf iv, natOf pv >>= copyOf with
    | some 3, some w, some (some (_, k)) =>
      match q.pend.lookup w with
      | some bs => q.deliver w (bs.take k)
      | none => (q, [])
    | _, _, _ => (q, [])
  | some [cv, iv, pv, data] =>
    match natOf cv, natOf iv, natOf pv >>= copyOf with
    | some 2, some r, some (some (_, k)) =>
      if r ∈ q.ins then (q, [.inp ((bytesOf data).take k)]) else (q, [])
    | _, _, _ => (q, [])
  | _ => (q, [])

/-- The functions the scan reads. -/
inductive K3 where
  | new | write | wait | read | stdin | fd | readVia | other
  deriving DecidableEq

/-- The kind of a function. -/
def k3 (f : FnName) : K3 :=
  if f = cStreamNew then .new else if f = cStreamWrite then .write else if f = cWait then .wait
  else if f = cStreamRead then .read else if f = stdinRead3 then .stdin
  else if f = getDirs3 ∨ f = openAt3 then .fd else if f = readVia3 then .readVia else .other

/-- **One event of the scan.** -/
def Sc3.step (q : Sc3) : WEv → Sc3 × List Out3
  | .imp f a r =>
    match k3 f with
    | .new =>
      match r with
      | some [rv, wv] =>
        match natOf rv, natOf wv with
        | some r', some w' => ({ q with pairs := (r', w') :: q.pairs }, [])
        | _, _ => (q, [])
      | _ => (q, [])
    | .write =>
      match a with
      | [wv, buf] =>
        match natOf wv with
        | some w => q.wrote w (bytesOf buf) (copyAns r)
        | none => (q, [])
      | _ => (q, [])
    | .wait => q.waited r
    | .read =>
      match a, r with
      | [rv, _], some [pv, items] =>
        match natOf rv, natOf pv >>= copyOf with
        | some r', some (some (_, k)) =>
          if r' ∈ q.ins then (q, [.inp ((bytesOf items).take k)]) else (q, [])
        | _, _ => (q, [])
      | _, _ => (q, [])
    | .stdin =>
      match r with
      | some [.record [rv, _]] =>
        match natOf rv with
        | some r' => ({ q with ins := r' :: q.ins }, [])
        | none => (q, [])
      | _ => (q, [])
    | .fd => ({ q with fds := fdStep q.fds (as2 (.imp f a r)) }, [])
    | .readVia =>
      match a, r with
      | .u32 fd :: _, some [.record [_, _]] => (q, (q.fds.lookup fd).toList.map .read)
      | _, _ => (q, [])
    | .other =>
      match sinkCall q.fds f a with
      | some (r', k) =>
        match q.pairs.lookup r' with
        | some w => ({ q with sinks := (w, k) :: q.sinks }, [])
        | none => (q, [])
      | none => (q, [])
  | _ => (q, [])

/-- **The scan of a trace.** -/
def scan3 : Sc3 → List WEv → List Out3
  | _, [] => []
  | q, e :: t => (q.step e).2 ++ scan3 (q.step e).1 t

/-- The state after a trace. -/
def Sc3.after : Sc3 → List WEv → Sc3
  | q, [] => q
  | q, e :: t => Sc3.after (q.step e).1 t

/-- The sink of a channel. -/
def Sink.ofChannel : Channel → Sink
  | .stdout => .stdout
  | .stderr => .stderr

/-! ## Exit codes -/

/-- The exit code of an event when it ends a WASI 0.3 run. -/
def endCode3 : WEv → Option ExitCode
  | .ret f _ r => if f = run3 then some (retCode r) else none
  | .req f [v] =>
    if f = exit3 then some (codeOf v)
    else if f = W3.exitCode then
      match v with
      | .u8 c => some (UInt8.ofBitVec c)
      | _ => none
    else none
  | _ => none

/-! ## The view -/

/-- The bytes delivered to a sink. -/
def sinkBytes (k : Sink) (os : List Out3) : List (BitVec 8) :=
  os.flatMap fun | .out k' b => if k' = k then b else [] | _ => []

/-- **The WASI 0.3 CLI view.** -/
def p3CliView : View where
  run := run3
  stdout t := toBytes (sinkBytes .stdout (scan3 {} t))
  stderr t := toBytes (sinkBytes .stderr (scan3 {} t))
  stdin t := toBytes ((scan3 {} t).flatMap fun | .inp b => b | _ => [])
  reads t := (scan3 {} t).filterMap fun | .read p => some p | _ => none
  writes t := (scan3 {} t).filterMap fun
    | .out (.file p off) b => some (p, off, toBytes b)
    | _ => none
  refused t := (scan3 {} t).any fun | .refused => true | _ => false
  code t := t.findSome? endCode3

/-! ## The environment's side -/

/-- **The WASI 0.3 CLI theory of an invocation**: `get-arguments`, `get-environment` and
`get-directories` answer the invocation's. -/
def cliTh3 (i : Input) : Silmaril.Wasm.Resource.Protocol Unit WEv :=
  pointwise fun e => argsOk W3.getArgs i e && envOk W3.getEnv i e && preopensOk getDirs3 i e

end Silmaril.Wasi.Cli

end
