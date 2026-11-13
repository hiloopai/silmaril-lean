import Silmaril.Project.WasmP3Rust.CoreLayerX.Defs
import Silmaril.Wasm.Component.BinaryP3.Defs

/-!
# `cli-core-trace`: a WASI 0.3 command on the faithful core semantics, with arguments and stdin

Runs the `run` export of a component exactly as `DenX.den` does (`DenX.start`, `DenX.internal`,
`DenX.forward`, the callback driver), with the core layer `CoreLayerX.execXFuel L ra fuel`:
silmaril's Core 3.0 interpreter on the component's core layer, and `get-arguments` lowered
with the **re-entrant `realloc`** (a second interpreter thread on the same store). The host is
scripted: `get-arguments` answers the program name and the arguments, `read-via-stream` a
stdin stream whose `stream.read`s deliver the given stdin bytes (`--stdin-chunk` at a time) and
then report `DROPPED`, `write-via-stream` a stdout future, `stream.write` completes in full
and the bytes are stdout's, `future.read` reports `ok`.

```text
cli-core-trace FILE.wasm [--stdin TEXT] [--stdin-chunk N] [--fuel N] [--trace] -- ARG...
```

It prints `stdout-hex: <hex>` (the bytes stdout accepted), `end: <exit|trap|...>` and,
with `--trace`, one line per world call. A test of `Task.echoLinesCore` and
`Task.catCopiesCore` on concrete inputs (`tests/run.sh`); it proves nothing.
-/

open Silmaril.Project.WasmP3Rust.Den (Spaces spaces cbOf Mode)
open Silmaril.Project.WasmP3Rust.DenX
open Silmaril.Project.WasmP3Rust.CoreLayer
open Silmaril.Project.WasmP3Rust.CoreLayerX
open Silmaril.Wasi Silmaril.Wasi.Versions.P3
open Silmaril.Wasm.Component (Val)

structure HostSt where
  args : List String := []
  stdin : List UInt8 := []
  chunk : Nat := 4096
  next : Nat := 10
  outR : List Nat := []
  pairs : List (Nat × Nat) := []
  outW : List Nat := []
  inR : List Nat := []
  stdout : Array UInt8 := #[]
  pending : List (List Nat) := []

def strV' (s : String) : Val := .record (s.toList.map .char)

def bytesV' (b : List UInt8) : Val := .record (b.map fun x => .u8 x.toBitVec)

def hostAnswer (h : HostSt) (op : XOp) : HostSt × Option (List Val) :=
  let f := op.1.1
  let args := op.2
  if f = getArgs3 then (h, some [.record (h.args.map strV')])
  else if f = cStreamNew then
    let r := h.next; let w := h.next + 1
    ({ h with next := h.next + 2, pairs := (r, w) :: h.pairs }, some [natV r, natV w])
  else if f = stdoutWrite3 then
    let r := match args with | [rv] => (natOf rv).getD 0 | _ => 0
    let w := (h.pairs.lookup r).getD 0
    ({ h with next := h.next + 1, outW := w :: h.outW }, some [natV h.next])
  else if f = stdinRead3 then
    ({ h with next := h.next + 2, inR := h.next :: h.inR },
      some [.record [natV h.next, natV (h.next + 1)]])
  else if f = cStreamRead then
    let n := match args with | [_, nv] => (natOf nv).getD 0 | _ => 0
    if h.stdin.isEmpty then (h, some [natV 1, .record []])
    else
      let k := min (min n h.chunk) h.stdin.length
      ({ h with stdin := h.stdin.drop k }, some [natV (16 * k), bytesV' (h.stdin.take k)])
  else if f = cStreamWrite then
    match args with
    | [wv, buf] =>
      let w := (natOf wv).getD 0
      let bs := (bytesOf buf).map UInt8.ofBitVec
      let h' := if w ∈ h.outW then { h with stdout := h.stdout ++ bs.toArray } else h
      (h', some [natV (16 * bs.length)])
    | _ => (h, none)
  else if f = cStreamDropW ∨ f = cStreamDropR ∨ f = cFutureDropR ∨ f = cJoin then (h, some [])
  else if f = cFutureRead then (h, some [natV 0, .variant 0 none])
  else if f = cWsNew then ({ h with next := h.next + 1 }, some [natV h.next])
  else if f = cWait then
    match h.pending with
    | e :: es => ({ h with pending := es }, some (e.map natV))
    | [] => (h, none)
  else (h, none)

partial def settle (c : Conf) (fuel : Nat) (n : Nat := 0) :
    Conf × Nat × Option (Silmaril.Wasm.Component.Engine.Status Nat) :=
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

def hex (b : Array UInt8) : String :=
  b.foldl (fun s x => s ++ (if x.toNat < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 x.toNat)) ""

partial def drive (L : Layer) (ra : Nat) (S : Spaces) (cb : Nat) (fuel : Nat) (tr : Bool)
    (d : DConf (execXFuel L ra fuel)) (h : HostSt) (calls : Nat) : IO HostSt := do
  if calls > 100000 then IO.println "end: too many calls"; return h
  match d.mode with
  | .exit => IO.println s!"end: exit {repr d.result}"; return h
  | .trap => IO.println "end: trap"; return h
  | .wait s =>
    let (h', ans) := hostAnswer h (up (Silmaril.Project.WasmP3Rust.Den.opWait s))
    if tr then IO.println s!"wait {s} -> {repr ans}"
    if ans.isNone then IO.println "end: deadlock"; return h
    drive L ra S cb fuel tr (afterWait cb d ans) h' (calls + 1)
  | .run =>
    let (c, _, st) := settle d.core fuel
    let d := { d with core := c }
    match st with
    | some (.callout k fs) =>
      let args := fs.map ofVal
      let B := builtinX S k
      match internal B args d with
      | some (some d') => drive L ra S cb fuel tr d' h (calls + 1)
      | some none => IO.println "end: internal trap"; return h
      | none =>
        match forward B args d with
        | some (op, kont) =>
          let (h', ans) := hostAnswer h op
          if tr then IO.println s!"call {op.1.1.iface}#{op.1.1.fn} -> {(repr ans).pretty.take 80}"
          drive L ra S cb fuel tr (contWith d kont ans) h' (calls + 1)
        | none => IO.println s!"end: outside the fragment ({k})"; return h
    | some (.returned (.values [p])) =>
      let p := ofVal p
      match Silmaril.Wasm.Component.Async.Cabi.unpackCallback p with
      | .ok (.exit, _) => drive L ra S cb fuel tr { d with mode := .exit } h calls
      | .ok (.wait, s) => drive L ra S cb fuel tr { d with mode := .wait s } h calls
      | .ok (.yield, _) => drive L ra S cb fuel tr (reenter cb d [0, 0, 0]) h calls
      | _ => IO.println s!"end: bad callback code {p}"; return h
    | some (.returned _) => IO.println "end: trap (returned)"; return h
    | some .running => IO.println "end: out of fuel"; return h
    | some .stuck => IO.println "end: stuck"; return h
    | none => IO.println "end: no thread"; return h

structure Opts where
  stdin : String := ""
  chunk : Nat := 4096
  fuel : Nat := 100000000
  trace : Bool := false
  args : List String := []

def parseOpts : List String → Opts → Opts
  | "--stdin" :: v :: rest, o => parseOpts rest { o with stdin := v }
  | "--stdin-chunk" :: v :: rest, o => parseOpts rest { o with chunk := v.toNat! }
  | "--fuel" :: v :: rest, o => parseOpts rest { o with fuel := v.toNat! }
  | "--trace" :: rest, o => parseOpts rest { o with trace := true }
  | "--" :: rest, o => { o with args := rest }
  | _ :: rest, o => parseOpts rest o
  | [], o => o

def main (argv : List String) : IO UInt32 := do
  match argv with
  | [] => IO.eprintln "usage: cli-core-trace FILE.wasm [--stdin TEXT] [--stdin-chunk N] [--fuel N] [--trace] -- ARG..."; return 2
  | file :: rest =>
    let o := parseOpts rest {}
    let b ← IO.FS.readBinFile file
    match Silmaril.Wasm.Component.BinaryP3.parse b with
    | .error _ => IO.eprintln "parse error"; return 1
    | .ok c =>
      match layer c with
      | none => IO.eprintln "core layer: instantiation failed"; return 1
      | some L =>
        let ra := (reallocOf c).getD 0
        IO.println s!"realloc: {repr (reallocOf c)}"
        let S := spaces c
        let d : DConf (execXFuel L ra o.fuel) := start (execXFuel L ra o.fuel) S
        let h : HostSt := { args := file :: o.args, stdin := o.stdin.toUTF8.toList, chunk := o.chunk }
        let h ← drive L ra S (cbOf S) o.fuel o.trace d h 0
        IO.println s!"stdout-hex: {hex h.stdout}"
        return 0
