module

public import Silmaril.Cli.Files.Defs
public import Silmaril.Wasi.Host.Defs
public import Silmaril.Wasi.Versions.P3.Defs
public import Silmaril.Wasi.Versions.P2.World.Defs
public import Silmaril.Wasi.Versions.P2.Io.Defs

/-!
# WASI `cli` components and CLI behaviour specifications

The bridge from Wasm components to the CLI behaviour model of `Silmaril.Cli.Behaviour`
(`docs/projects/wasm-binaryen-tooling.md`).

**Views.** A component of a `wasi:cli/command` world is a strategy of the WASI game
(`Silmaril.Wasi`), and its plays are event lists (`WEv`): import calls with the host's answers,
export calls and returns. A `View` reads an event list, on an invocation `i`, as what has been
seen of a CLI run so far: a partial observation `Silmaril.Cli.Seen` of the behaviour model, the
same layer LPS trace prefixes and test harnesses produce. It records stdout and stderr (the bytes the host accepted), the stdin bytes the host
delivered (`Obs.consumed`), the files read and written under the preopened directories (rooted
paths `FPath`, the preopen's name as root), whether the host refused an operation, and the exit
code once `run` returned (or `exit` was called). `View.seen` assembles them; the files are `i.fs`
with the writes applied (`applyWrites`). `View.obs` is the same reading as a complete
observation (`Obs`), and `View.seen` is a partial view of it (`View.seen_le_obs`).

* `p2View` (WASI 0.2): writes on output streams `get-stderr` returned go to stderr, other
  successful writes (`write`, `blocking-write-and-flush`) to stdout, any other answer is a
  refusal (`failedWrite2`);
  reads (`read`, `blocking-read`) on input streams `get-stdin` returned are consumed stdin;
  descriptors are followed from `get-directories` (a preopen `(fd, name)` is the root `name`)
  through `open-at(dir, path)` (the path below `dir`'s); `descriptor.read` records the file as
  read, `descriptor.write(fd, buffer, offset)` writes the accepted bytes at `offset`, a failed
  one is a refusal; the exit code comes from `exit(result)` or from `run`'s result.
* `p3View` (WASI 0.3): stdout is the OS image `osTrace3` (the bytes the host accepted on
  `stdout.write-via-stream`'s streams); stdin is a parameter (`Silmaril.Project.WasmP3Rust.CliSpec`
  passes the data-carrying reading of `DenX`); the exit code comes from `run`'s `result`
  (`ok` 0, `error` 1, a trap `trapExit`), or `exit` when the world has it.

**The environment's side.** What the host gives (arguments, environment, stdin, preopens) is
the theory's business: `CliSat σ T V S` takes a theory `T i` per invocation. `argsOk`,
`envOk`, `preopensOk` and `stdinTh2` constrain the answers of `get-arguments` (the program name
and the arguments), `get-environment`, `get-directories` (the declared roots) and the WASI 0.2
stdin reads (a prefix of `i.stdin`, in order) to `i`; `cliTh2 i` is their product.

**Satisfaction.** `CliSat σ T V S`: for every invocation `i`, every play of `σ` whose host
answers satisfy `T i`, with at most one call of `run`, is seen through `V` as a partial view of
a run `S` allows on `i` (`Spec.Partial`: the outputs so far are prefixes of an allowed
observation's, stdin consumed and files read no more, a refusal seen is the observation's; once
the run has ended, stdout, stderr, exit code and files are exactly the observation's). By
`CliSat.every_host` this holds of every interaction with every host satisfying `T i`, whatever
the host's lower interface. Since the theory is a parameter, the same statement covers WASI 0.2
and 0.3 hosts (and their adapters, through the relations of `docs/projects/wasm-wasi.md`).

Not read off the trace: file truncation by `open-at` flags (writes apply to the file's previous
contents, or to an empty file), `read-via-stream`/`write-via-stream` on descriptors, directory
operations, and `wasi:cli/stderr` and file I/O in WASI 0.3 (`p3CliView` of
`Silmaril.Wasi.Cli.View3` reads those).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli

open Silmaril.Cli
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- The exit code read for a trapping `run`: `134` (`128 + SIGABRT`). Observed: wasmtime 50.0.0
`run` on a core module whose `_start` executes `unreachable` exits with 134 (Linux). A modelling
choice; any nonzero code would do for the specs here. -/
def trapExit : ExitCode := 134

/-- `b` written at `off` into `c` (zero-filled up to `off`). -/
def writeAt (c : Bytes) (off : Nat) (b : Bytes) : Bytes :=
  c.take off ++ List.replicate (off - c.length) 0 ++ b ++ c.drop (off + b.length)

/-- Apply writes `(path, offset, bytes)` in order. -/
def applyWrites (fs : Fs) : List (FPath × Nat × Bytes) → Fs
  | [] => fs
  | (p, off, b) :: ws => applyWrites (fs.set p (some (writeAt ((fs p).getD []) off b))) ws

/-! ## Views -/

/-- **A CLI view of the traces of a world**: its `run` export and readers of a trace. -/
structure View where
  /-- The `run` export. -/
  run : FnName
  /-- The bytes stdout accepted. -/
  stdout : List WEv → Bytes
  /-- The bytes stderr accepted. -/
  stderr : List WEv → Bytes := fun _ => []
  /-- The bytes stdin delivered. -/
  stdin : List WEv → Bytes := fun _ => []
  /-- The files read. -/
  reads : List WEv → List FPath := fun _ => []
  /-- The writes to files, in order: path, offset, bytes. -/
  writes : List WEv → List (FPath × Nat × Bytes) := fun _ => []
  /-- The host refused an operation. -/
  refused : List WEv → Bool := fun _ => false
  /-- The exit code, once the run has ended. -/
  code : List WEv → Option ExitCode

/-- **The observation `V` reads off the trace `t`** on the invocation `i`, as if the run had
ended there: the exit code `0` when it has not (`View.seen` keeps that apart), the files `i.fs`
with the writes applied, an empty file log. -/
def View.obs (V : View) (i : Input) (t : List WEv) : Obs where
  stdout := V.stdout t
  stderr := V.stderr t
  exit := (V.code t).getD 0
  consumed := (V.stdin t).length
  reads := V.reads t
  fs := applyWrites i.fs (V.writes t)
  refused := V.refused t

/-- **What `V` sees of the trace `t`** on the invocation `i`: a partial observation of the
behaviour model (`Silmaril.Cli.Seen`), whose exit code is known once the run has ended. The files
are those written so far; `Seen.Le` reads them only once the run has ended. -/
def View.seen (V : View) (i : Input) (t : List WEv) : Seen where
  stdout := V.stdout t
  stderr := V.stderr t
  exit := V.code t
  consumed := (V.stdin t).length
  reads := V.reads t
  fs := some (applyWrites i.fs (V.writes t))
  refused := V.refused t

/-- The calls of the export `f` along `t`. -/
def calls (f : FnName) (t : List WEv) : Nat :=
  t.countP fun
    | .call g _ => decide (g = f)
    | _ => false

/-- **The CLI guarantee** on one trace: with at most one run, what has been seen is a partial
view of a run `S` allows (`Spec.Partial`). -/
def View.Guar (V : View) (S : Spec) (i : Input) (t : List WEv) : Prop :=
  calls V.run t ≤ 1 → S.Partial i (V.seen i t)

/-- **The component `σ` satisfies the CLI specification `S`** through the view `V`, for every
host whose answers satisfy the theory `T i` on the invocation `i`. -/
def CliSat {W : World} {St : Type} (σ : W.Model) (T : Input → Protocol St WEv) (V : View)
    (S : Spec) : Prop :=
  ∀ i, (ag (I := W.imports) (X := W.exports) (fun t => (T i).Accepts (hostView t))
    (V.Guar S i)).holds σ

/-! ## Values -/

/-- WASI's bytes as the model's. -/
def toBytes (b : List (BitVec 8)) : Bytes := b.map UInt8.ofBitVec

/-- The characters of a `string` value (a record of `char`s). -/
def charsOf : Val → Option (List Char)
  | .record cs => cs.mapM fun (v : Val) => match v with | .char c => some c | _ => none
  | _ => none

/-- A `string` value. -/
def strOf (v : Val) : Option String := (charsOf v).map String.ofList

/-- Split characters at `/` (structural, so that the kernel evaluates it). -/
def splitSlash : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '/' then [] :: splitSlash cs
    else match splitSlash cs with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

/-- The components of a path, without empty and `.` components (as `pathComps`, on
characters). -/
def compsOf (cs : List Char) : List String :=
  ((splitSlash cs).filter fun c => c ≠ [] ∧ c ≠ ['.']).map String.ofList

/-- The exit code of a `result` value. -/
def codeOf (v : Val) : ExitCode := if Versions.P3.resultOk v then 0 else 1

/-- The exit code of the return `r` of `run` (`none`: a trap). -/
def retCode : Option (List Val) → ExitCode
  | some [v] => codeOf v
  | some _ => 1
  | none => trapExit

/-- The exit code of an event, when it ends the run: a return of `run`, or a call of `exit`
when the world has one. -/
def endCode (run : FnName) (exit : Option FnName) : WEv → Option ExitCode
  | .ret f _ r => if f = run then some (retCode r) else none
  | .req f [v] => if some f = exit then some (codeOf v) else none
  | _ => none

/-- **The exit code along `t`**: that of the first event that ends the run. -/
def exitOf (run : FnName) (exit : Option FnName) (t : List WEv) : Option ExitCode :=
  t.findSome? (endCode run exit)

/-! ## WASI 0.3 -/

/-- `wasi:cli/exit@0.3.2.exit`. -/
def exit3 : FnName := ⟨"wasi:cli/exit@0.3.2", "exit"⟩

/-- The bytes stdout accepted along a WASI 0.3 trace: the write events of `osTrace3`. -/
def p3Stdout (t : List WEv) : List (BitVec 8) :=
  (Versions.P3.osTrace3 0 t).filterMap fun
    | .writeEv _ b => some b
    | _ => none

/-- **The WASI 0.3 view** of a world with `wasi:cli/exit` (`exit = some exit3`) or without
(`none`, as the worlds of the 0.3 examples), reading stdin with `stdin`. -/
def p3View (exit : Option FnName := none) (stdin : List WEv → Bytes := fun _ => []) : View where
  run := Versions.P3.run3
  stdout t := toBytes (p3Stdout t)
  stdin := stdin
  code := exitOf Versions.P3.run3 exit

/-! ## WASI 0.2 -/

/-- The `u32` handles the function `f` answered along `t`. -/
def handles (f : FnName) (t : List WEv) : List (BitVec 32) :=
  t.filterMap fun
    | .imp g _ (some [.u32 h]) => if g = f then some h else none
    | _ => none

/-- A successful write's stream and bytes. -/
def write2 : WEv → Option (BitVec 32 × List (BitVec 8))
  | .imp f (.u32 h :: c :: _) (some [.variant 0 none]) =>
    if f = Versions.P2.osWrite ∨ f = streamWrite then some (h, bytesOf c) else none
  | _ => none

/-- The bytes written along `t` on the streams `get-stderr` returned (`err = true`) or on the
others. A handle is classified by the whole of `t`: WASI 0.2 hosts do not reuse a live handle. -/
def written2 (err : Bool) (t : List WEv) : List (BitVec 8) :=
  (t.filterMap write2).flatMap fun (h, b) =>
    if decide (h ∈ handles Versions.P2.getStderr t) = err then b else []

/-- A successful read's stream and bytes. -/
def read2 : WEv → Option (BitVec 32 × List (BitVec 8))
  | .imp f (.u32 h :: _) (some [.variant 0 (some c)]) =>
    if f = Versions.P2.isRead ∨ f = Versions.P2.isBread then some (h, bytesOf c) else none
  | _ => none

/-- **The bytes stdin delivered** along `t`: reads on the streams `get-stdin` returned. -/
def stdin2 (t : List WEv) : List (BitVec 8) :=
  (t.filterMap read2).flatMap fun (h, b) =>
    if h ∈ handles Versions.P2.getStdin t then b else []

/-- The descriptors along a prefix: preopens and the files and directories opened below them. -/
abbrev Fds : Type := List (BitVec 32 × FPath)

/-- The descriptors after an event. -/
def fdStep (ds : Fds) : WEv → Fds
  | .imp f args (some [r]) =>
    if f = getDirs then
      match r with
      | .record ps => ps.filterMap (fun
          | .record [.u32 fd, n] => (strOf n).map fun s => (fd, ⟨s, []⟩)
          | _ => none) ++ ds
      | _ => ds
    else if f = openAt then
      match args, r with
      | .u32 dir :: path :: _, .variant 0 (some (.u32 fd)) =>
        match ds.lookup dir, charsOf path with
        | some p, some cs => (fd, ⟨p.root, p.rel ++ compsOf cs⟩) :: ds
        | _, _ => ds
      | _, _ => ds
    else ds
  | _ => ds

/-- A file effect of an event with the descriptors `ds`: a read of a path, a write. -/
inductive FileEff where
  | read (p : FPath)
  | write (p : FPath) (off : Nat) (b : Bytes)
  | refused

/-- The file effect of an event. -/
def fileEff (ds : Fds) : WEv → Option FileEff
  | .imp f (.u32 fd :: rest) (some [r]) =>
    if f = fdRead then
      match r, ds.lookup fd with
      | .variant 0 _, some p => some (.read p)
      | _, _ => none
    else if f = fdWrite then
      match r, rest, ds.lookup fd with
      | .variant 0 (some (.u64 n)), buf :: .u64 off :: _, some p =>
        some (.write p off.toNat (toBytes ((bytesOf buf).take n.toNat)))
      | .variant 1 _, _, _ => some .refused
      | _, _, _ => none
    else none
  | _ => none

/-- The file effects along `t`, from the descriptors `ds`. -/
def fileEffs : Fds → List WEv → List FileEff
  | _, [] => []
  | ds, e :: t => (fileEff ds e).toList ++ fileEffs (fdStep ds e) t

/-- **A refused WASI 0.2 write**: an answer of `write` or `blocking-write-and-flush` other than
success (an error, or a malformed answer). -/
def failedWrite2 : WEv → Bool
  | .imp f _ r =>
    if f = Versions.P2.osWrite ∨ f = streamWrite then
      (match r with
       | some [.variant 0 none] => false
       | _ => true)
    else false
  | _ => false

/-- **The WASI 0.2 view.** -/
def p2View : View where
  run := cliRun
  stdout t := toBytes (written2 false t)
  stderr t := toBytes (written2 true t)
  stdin t := toBytes (stdin2 t)
  reads t := (fileEffs [] t).filterMap fun | .read p => some p | _ => none
  writes t := (fileEffs [] t).filterMap fun | .write p off b => some (p, off, b) | _ => none
  refused t := t.any failedWrite2 || (fileEffs [] t).any fun | .refused => true | _ => false
  code := exitOf cliRun (some Versions.P2.cliExit)

/-! ## The environment's side -/

/-- The strings of a `list<string>` answer. -/
def strsOf : Option (List Val) → Option (List String)
  | some [.record vs] => vs.mapM strOf
  | _ => none

/-- **`get-arguments` (the function `f`) answers the program name and the arguments.** -/
def argsOk (f : FnName) (i : Input) : WEv → Bool
  | .imp g _ r => !decide (g = f) || decide (strsOf r = some (i.prog :: i.args))
  | _ => true

/-- The bindings of a `list<tuple<string, string>>` answer. -/
def envOf : Option (List Val) → Option (List (String × String))
  | some [.record vs] => vs.mapM fun
    | .record [k, v] => do pure (← strOf k, ← strOf v)
    | _ => none
  | _ => none

/-- **`get-environment` (the function `f`) answers the environment.** -/
def envOk (f : FnName) (i : Input) : WEv → Bool
  | .imp g _ r => !decide (g = f) || decide (envOf r = some i.env)
  | _ => true

/-- **`get-directories` (the function `f`) answers the declared roots**, by name, in order. -/
def preopensOk (f : FnName) (i : Input) : WEv → Bool
  | .imp g _ (some [.record ps]) =>
    !decide (g = f) || decide ((ps.map fun | .record [_, n] => strOf n | _ => none) =
      i.roots.map fun r => some r.name)
  | .imp g _ _ => !decide (g = f)
  | _ => true

/-- One step of the WASI 0.2 stdin theory: the stdin handles and the bytes delivered so far. -/
def stdinStep2 (i : Input) (q : List (BitVec 32) × Nat) : WEv → Option (List (BitVec 32) × Nat)
  | .imp f a r =>
    if f = Versions.P2.getStdin then
      match r with
      | some [.u32 h] => some (h :: q.1, q.2)
      | _ => some q
    else
      match read2 (.imp f a r) with
      | some (h, b) =>
        if h ∈ q.1 then
          if toBytes b <+: i.stdin.drop q.2 then some (q.1, q.2 + b.length) else none
        else some q
      | none => some q
  | _ => some q

/-- **WASI 0.2 stdin delivers `i.stdin`**, in order (reads give the next bytes). -/
def stdinTh2 (i : Input) : Protocol (List (BitVec 32) × Nat) WEv := ⟨([], 0), stdinStep2 i⟩

/-- **The WASI 0.2 CLI theory of an invocation**: arguments, environment, preopens and stdin. -/
def cliTh2 (i : Input) : Protocol (Unit × (List (BitVec 32) × Nat)) WEv :=
  (pointwise fun e => argsOk Versions.P2.getArgs i e &&
    envOk Versions.P2.getEnv i e && preopensOk getDirs i e).prod (stdinTh2 i)

end Silmaril.Wasi.Cli

end
