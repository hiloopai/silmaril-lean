import Silmaril.Project.WasmP3Rust.CoreLayer.Defs
import Silmaril.Wasm.Component.BinaryP3.Defs

/-!
# `wasip3-trace`: the canonical ABI calls of a WASI 0.3 command, on silmaril's interpreter

Instantiates the core layer of a component (`CoreLayer.layer`: the core modules of the file,
decoded with silmaril's `decode?`, instantiated by the Core 3.0 engine with the `canon`
built-ins as host functions), calls the async callback lift of `wasi:cli/run@0.3.0#run` and
drives it as `Den.den` does (`Den.internal`, `Den.forward`, the callback driver), answering the
world's calls with a scripted host. It prints one line per call of a `canon`-defined core
function (index, built-in, flat arguments), one per answer, and the end of the run.

```text
wasip3-trace FILE.wasm [--write done|blocked|half] [--fread done|blocked] [--fuel N]
```

* `--write done`: every `stream.write` completes at once with all its bytes; `blocked`: it
  returns `BLOCKED`, and the next `waitable-set.wait` delivers `STREAM_WRITE` with all of them;
  `half`: it completes at once with half of them (rounded up).
* `--fread done`: `future.read` completes at once with `ok`; `blocked`: it returns `BLOCKED`
  and a later `waitable-set.wait` delivers `FUTURE_READ` `COMPLETED`.

Handles: `stream.new` answers `(1, 2)`, `write-via-stream` answers `3`, `read-via-stream`
`(5, 6)` (stdin stream and its future), `waitable-set.new` `4`; `stream.read` answers
`DROPPED` with no bytes (empty stdin).

This is a test of the model, compiled: it shows which calls the real code makes under these
hosts; it proves nothing (see `tools/wasm-tools/README.md`).
-/

open Silmaril.Project.WasmP3Rust.Den Silmaril.Project.WasmP3Rust.CoreLayer
open Silmaril.Wasi Silmaril.Wasi.Versions.P3
open Silmaril.Wasm.Component (Val)

def builtinName : Builtin → String
  | .streamNew => "stream.new" | .streamWrite => "stream.write" | .streamRead => "stream.read"
  | .streamDropR => "stream.drop-readable" | .streamDropW => "stream.drop-writable"
  | .futureRead => "future.read" | .futureDropR => "future.drop-readable"
  | .wsNew => "waitable-set.new" | .wsWait => "waitable-set.wait" | .join => "waitable.join"
  | .taskReturn => "task.return" | .ctxGet i => s!"context.get {i}" | .ctxSet i => s!"context.set {i}"
  | .wsDrop => "waitable-set.drop" | .wasi f => s!"lower {f.1.iface}#{f.1.fn}"
  | .unsupported => "UNSUPPORTED"

structure HostSt where
  write : String := "done"
  fread : String := "done"
  /-- Events to deliver at the next waits. -/
  pending : List (List Nat) := []

def showVal : Val → String
  | .u32 x => toString x.toNat
  | v => (s!"{repr v}".take 60).toString

/-- The scripted host's answer to a world call. -/
def hostAnswer (h : HostSt) (op : P3Op) : HostSt × Option (List Val) :=
  let f := op.1.1
  let args := op.2
  if f.fn = "stream.new" then (h, some [natV 1, natV 2])
  else if f.fn = "write-via-stream" then (h, some [natV 3])
  else if f.fn = "read-via-stream" then (h, some [.record [natV 5, natV 6]])
  else if f.fn = "stream.read" then (h, some [natV 1, .record []])
  else if f.fn = "waitable-set.new" then (h, some [natV 4])
  else if f.fn = "waitable.join" then (h, some [])
  else if f.fn = "stream.drop-writable" || f.fn = "stream.drop-readable"
      || f.fn = "future.drop-readable" then (h, some [])
  else if f.fn = "stream.write" then
    let n := match args with
      | [_, .record bs] => bs.length
      | _ => 0
    let w := match args with
      | [w, _] => (natOf w).getD 0
      | _ => 0
    if h.write = "blocked" then
      ({ h with pending := h.pending ++ [[3, w, n * 16]] }, some [natV Silmaril.Wasm.Component.Async.blocked])
    else if h.write = "half" then (h, some [natV (((n + 1) / 2) * 16)])
    else (h, some [natV (n * 16)])
  else if f.fn = "future.read" then
    let fh := match args with
      | [x] => (natOf x).getD 0
      | _ => 0
    if h.fread = "blocked" then
      ({ h with pending := h.pending ++ [[4, fh, 0]] }, some [natV Silmaril.Wasm.Component.Async.blocked])
    else (h, some [natV 0, .variant 0 none])
  else if f.fn = "waitable-set.wait" then
    match h.pending with
    | e :: es => ({ h with pending := es }, some (e.map natV))
    | [] => (h, none)
  else (h, none)

def showOp (op : P3Op) : String :=
  s!"{op.1.1.iface}#{op.1.1.fn}({", ".intercalate (op.2.map showVal)})"

def showAns : Option (List Val) → String
  | some vs => s!"[{", ".intercalate (vs.map showVal)}]"
  | none => "none"

/-- Run the core thread to its next status (silent steps), within `fuel` steps. -/
partial def settle (c : Conf) (fuel : Nat) (n : Nat := 0) : Conf × Nat × Option (Silmaril.Wasm.Component.Engine.Status Nat) :=
  match status c with
  | some .running =>
    if n ≥ fuel then (c, n, some .running)
    else match c.thread with
      | some t =>
        match Silmaril.Wasm.SingleThreaded.internalC
            (Silmaril.Wasm.SingleThreaded.Exec.stepI oracle) (c.store, t) with
        | some (s', t') => settle ⟨s', some t'⟩ fuel (n + 1)
        | none => (c, n, some .stuck)
      | none => (c, n, none)
  | st => (c, n, st)

def parseArgs : List String → HostSt × Nat → HostSt × Nat
  | "--write" :: v :: rest, (h, f) => parseArgs rest ({ h with write := v }, f)
  | "--fread" :: v :: rest, (h, f) => parseArgs rest ({ h with fread := v }, f)
  | "--fuel" :: v :: rest, (h, _) => parseArgs rest (h, v.toNat!)
  | _ :: rest, x => parseArgs rest x
  | [], x => x

partial def drive (L : Layer) (S : Spaces) (cb : Nat) (d : DConf (exec L)) (h : HostSt)
    (fuel steps : Nat) (calls : Nat) : IO Unit := do
  if calls > 200 then IO.println "STOP after 200 calls"; return
  match d.mode with
  | .exit => IO.println s!"EXIT task.return={d.result} after {steps} steps"
  | .trap => IO.println s!"TRAP after {steps} steps"
  | .wait s =>
    let (h', ans) := hostAnswer h (opWait s)
    IO.println s!"  driver: waitable-set.wait({s}) -> {showAns ans}"
    if ans.isNone then IO.println "DEADLOCK (no pending event)"; return
    drive L S cb (afterWait cb d ans) h' fuel steps (calls + 1)
  | .run =>
    let (c, n, st) := settle d.core fuel
    let d := { d with core := c }
    let steps := steps + n
    match st with
    | some (.callout k fs) =>
      let args := fs.map ofVal
      let B := builtin S k
      IO.println s!"call {k} {builtinName B} {args}  (step {steps})"
      match internal B args d with
      | some (some d') => drive L S cb d' h fuel steps (calls + 1)
      | some none => IO.println "  internal trap"; drive L S cb d.trapped h fuel steps (calls + 1)
      | none =>
        match forward (exec L) B args d.core with
        | some (op, kont) =>
          let (h', ans) := hostAnswer h op
          IO.println s!"  world: {showOp op} -> {showAns ans}"
          drive L S cb (contWith d kont ans) h' fuel steps (calls + 1)
        | none => IO.println "  outside den's fragment: trap"
    | some (.returned (.values [p])) =>
      let p := ofVal p
      match Silmaril.Wasm.Component.Async.Cabi.unpackCallback p with
      | .ok (.exit, _) => IO.println s!"return EXIT ({p})"; drive L S cb { d with mode := .exit } h fuel steps calls
      | .ok (.wait, s) => IO.println s!"return WAIT {s} ({p})"; drive L S cb { d with mode := .wait s } h fuel steps calls
      | .ok (.yield, _) => IO.println s!"return YIELD ({p})"; drive L S cb (reenter cb d [0, 0, 0]) h fuel steps calls
      | _ => IO.println s!"return bad code {p}"
    | some (.returned r) => IO.println s!"returned {repr r} after {steps} steps"
    | some .running => IO.println s!"OUT OF FUEL after {steps} steps"
    | some .stuck => IO.println s!"STUCK after {steps} steps"
    | none => IO.println "no thread"

def main (argv : List String) : IO UInt32 := do
  match argv with
  | [] => IO.eprintln "usage: wasip3-trace FILE.wasm [--write done|blocked|half] [--fread done|blocked] [--fuel N]"; return 2
  | file :: rest =>
    let (h, fuel) := parseArgs rest ({}, 10000000)
    let b ← IO.FS.readBinFile file
    match Silmaril.Wasm.Component.BinaryP3.parse b with
    | .error _ => IO.eprintln "parse error"; return 1
    | .ok c =>
      match layer c with
      | none => IO.eprintln "core layer: instantiation failed"; return 1
      | some L =>
        IO.println s!"core layer: {L.modules.length} modules, {L.insts.length} core instances, {L.funcs.length} core functions, {L.hosts.length} host functions"
        let S := spaces c
        IO.println s!"run lift: {runLift S}"
        let d : DConf (exec L) := start (exec L) S
        drive L S (cbOf S) d h fuel 0 0
        return 0
