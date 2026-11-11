module

public import Silmaril.Cli.Files.Defs

/-!
# CLI programs in Lean: a small IO interface read into the behaviour model

The bridge from Lean programs to the CLI behaviour model of `Silmaril.Cli.Behaviour`
(`docs/projects/wasm-binaryen-tooling.md`, track bridge). Observations, specifications and refinement are the
behaviour model's: an invocation `Input` (program name, arguments, environment, stdin, the
declared roots and the files under them), an observation `Obs` (stdout, stderr, exit code, stdin
consumed, files read, the files after the run, whether the environment refused something), and
`Spec := Input → Obs → Prop` ordered by refinement `≤`.

**Programs** (`Prog`): a free monad over the CLI effects: the arguments (without the program
name, as `Input.args` and Lean's `main` take them), an environment variable, stdin to its end, a
write on stdout or stderr, reading a whole file, writing a whole file (answered: `false` when the
environment refuses), exit. File names are strings resolved as the behaviour model resolves
argument paths (`Input.resolve`: relative to the root `"."`, or under an absolute root).

**The reading** `Prog.obs p i` evaluates `p` on the invocation `i` (`Prog.exec`):

* a read of `s` resolves `s`; a file present there is answered and recorded in `Obs.reads`;
  otherwise the answer is `none` and nothing is recorded;
* a write of `s` changes the file when `s` resolves under a writable root, and is refused
  (`Obs.refused`, answer `false`) otherwise;
* reading stdin consumes the rest of it (`Obs.consumed`).

`Prog.Sat p S` says every run of `p` is allowed by `S`; it is `Spec.det p.obs ≤ S`
(`Prog.sat_iff_det_le`), so implementations and specifications live in one order.
`Prog.toIO` (`Silmaril.Cli.Io.Run`) runs the same program with Lean's `IO`.

**Pure cores** (`Prog.ofCore`, `Prog.ofTool`): the shape of a CLI tool whose logic is a pure
function to a `Result` (stdout, stderr, files to write, exit code). `emit` prints the result,
writes its files and exits with its code, or with `1` as soon as a write is refused.
`Silmaril.Cli.Io.Thms` computes their observations (`Result.obs`), so a tool built with them
satisfies a spec iff its core does (`Prog.sat_ofCore_iff`, `Prog.sat_ofTool_iff`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Io

open Silmaril.Cli

/-! ## Programs -/

/-- The two output streams. -/
inductive Stream where
  | stdout
  | stderr
deriving DecidableEq, Repr

/-- **CLI programs**: a free monad over the CLI effects. -/
inductive Prog (α : Type) : Type where
  /-- Return `a`. -/
  | pure (a : α)
  /-- Get the arguments (without the program name). -/
  | args (k : List String → Prog α)
  /-- Get an environment variable. -/
  | env (name : String) (k : Option String → Prog α)
  /-- Read standard input to its end. -/
  | stdin (k : Bytes → Prog α)
  /-- Write bytes on a stream. -/
  | out (s : Stream) (b : Bytes) (k : Prog α)
  /-- Read a whole file (`none`: absent, or not under a declared root). -/
  | read (path : String) (k : Option Bytes → Prog α)
  /-- Write a whole file (`false`: refused). -/
  | write (path : String) (b : Bytes) (k : Bool → Prog α)
  /-- Exit with a code. -/
  | exit (code : ExitCode)

namespace Prog

variable {α β : Type}

/-- Sequencing. -/
def bind : Prog α → (α → Prog β) → Prog β
  | .pure a, f => f a
  | .args k, f => .args fun x => bind (k x) f
  | .env n k, f => .env n fun x => bind (k x) f
  | .stdin k, f => .stdin fun x => bind (k x) f
  | .out s b k, f => .out s b (bind k f)
  | .read p k, f => .read p fun x => bind (k x) f
  | .write p b k, f => .write p b fun x => bind (k x) f
  | .exit c, _ => .exit c

instance : Monad Prog where
  pure := .pure
  bind := bind

end Prog

/-! ## The operations -/

/-- The arguments, without the program name. -/
def getArgs : Prog (List String) := .args .pure

/-- An environment variable. -/
def getEnv (n : String) : Prog (Option String) := .env n .pure

/-- Several environment variables, with their names. -/
def getEnvs : List String → Prog (List (String × Option String))
  | [] => .pure []
  | n :: ns => .env n fun v => (getEnvs ns).bind fun vs => .pure ((n, v) :: vs)

/-- The rest of standard input. -/
def readStdin : Prog Bytes := .stdin .pure

/-- Write bytes on stdout. -/
def print (b : Bytes) : Prog Unit := .out .stdout b (.pure ())

/-- Write bytes on stderr. -/
def eprint (b : Bytes) : Prog Unit := .out .stderr b (.pure ())

/-- Read a whole file. -/
def readFile (p : String) : Prog (Option Bytes) := .read p .pure

/-- Write a whole file; `false` when refused. -/
def writeFile (p : String) (b : Bytes) : Prog Bool := .write p b .pure

/-- Exit with a code. -/
def exit {α : Type} (c : ExitCode) : Prog α := .exit c

/-! ## The reading of a program in the model -/

/-- The state of a run: the observation so far and the rest of stdin. -/
structure St where
  /-- What has been observed (its `fs` is the current files). -/
  obs : Obs
  /-- What stdin has not delivered yet. -/
  rest : Bytes

/-- The state at the start of a run on `i`. -/
def St.init (i : Input) : St := { obs := { fs := i.fs }, rest := i.stdin }

/-- Append bytes to a stream. -/
def _root_.Silmaril.Cli.Obs.emit (o : Obs) : Stream → Bytes → Obs
  | .stdout, b => { o with stdout := o.stdout ++ b }
  | .stderr, b => { o with stderr := o.stderr ++ b }

/-- Read stdin to its end. -/
def St.takeStdin (st : St) : St :=
  { obs := { st.obs with consumed := st.obs.consumed + st.rest.length }, rest := [] }

/-- Read the file `s` names in the observation `o` so far: answered and recorded when present. -/
def readObs (i : Input) (o : Obs) (s : String) : Obs × Option Bytes :=
  match i.resolve s with
  | some q =>
    match o.fs q with
    | some b => ({ o with reads := o.reads ++ [q], log := o.log ++ [.read q (some b)] }, some b)
    | none => (o, none)
  | none => (o, none)

/-- Write the file `s` names: done under a writable root, refused otherwise. -/
def writeObs (i : Input) (o : Obs) (s : String) (b : Bytes) : Obs × Bool :=
  match i.resolve s with
  | some q =>
    if i.Writable q then
      ({ o with fs := o.fs.set q (some b), log := o.log ++ [.write q (some b)] }, true)
    else ({ o with refused := true }, false)
  | none => ({ o with refused := true }, false)

/-- Write files in order, stopping at the first refused write. -/
def writeAllObs (i : Input) : Obs → List (String × Bytes) → Obs × Bool
  | o, [] => (o, true)
  | o, (p, b) :: fs =>
    match writeObs i o p b with
    | (o', true) => writeAllObs i o' fs
    | (o', false) => (o', false)

namespace Prog

variable {α : Type}

/-- **Evaluation** on the invocation `i`: the final state, and the value unless the program
exited. -/
def exec (i : Input) : Prog α → St → St × Option α
  | .pure a, st => (st, some a)
  | .args k, st => exec i (k i.args) st
  | .env n k, st => exec i (k (i.getEnv n)) st
  | .stdin k, st => exec i (k st.rest) st.takeStdin
  | .out s b k, st => exec i k { st with obs := st.obs.emit s b }
  | .read p k, st => exec i (k (readObs i st.obs p).2) { st with obs := (readObs i st.obs p).1 }
  | .write p b k, st =>
    exec i (k (writeObs i st.obs p b).2) { st with obs := (writeObs i st.obs p b).1 }
  | .exit c, st => ({ st with obs := { st.obs with exit := c } }, none)

/-- The observation of a final state of a main program, whose value is its exit code. -/
def finish : St × Option ExitCode → Obs
  | (st, some c) => { st.obs with exit := c }
  | (st, none) => st.obs

/-- **The observation of a main program** on the invocation `i`. -/
def obs (p : Prog ExitCode) (i : Input) : Obs := finish (p.exec i (St.init i))

/-- **`p` satisfies `S`**: every run of `p` is allowed by `S`. -/
def Sat (p : Prog ExitCode) (S : Spec) : Prop := ∀ i, S i (p.obs i)

end Prog

/-! ## Pure cores -/

/-- The result of a pure core: what to print, the files to write and the exit code. -/
structure Result where
  /-- Bytes for stdout. -/
  stdout : Bytes := []
  /-- Bytes for stderr. -/
  stderr : Bytes := []
  /-- Files to write, in order. -/
  files : List (String × Bytes) := []
  /-- The exit code. -/
  exit : ExitCode := 0
deriving Inhabited, Repr, DecidableEq

/-- Write a list of files, stopping at the first refused write (`false`). -/
def writeAll : List (String × Bytes) → Prog Bool
  | [] => .pure true
  | (p, b) :: fs => .write p b fun ok => if ok then writeAll fs else .pure false

/-- Read a list of files. -/
def readAll : List String → Prog (List (String × Option Bytes))
  | [] => .pure []
  | p :: ps => .read p fun b => (readAll ps).bind fun bs => .pure ((p, b) :: bs)

/-- **Emit a result**: stdout, stderr, the files, then exit with its code (`1` when a write is
refused). -/
def emit (r : Result) : Prog ExitCode := do
  print r.stdout
  eprint r.stderr
  let ok ← writeAll r.files
  pure (if ok then r.exit else 1)

/-- **The observation of emitting `r`** on `i`, having consumed `c` bytes of stdin, read the
files `rd` and logged the file events `lg`. -/
def Result.obs (r : Result) (i : Input) (c : Nat := 0) (rd : List FPath := [])
    (lg : List FileEv := []) : Obs :=
  let w := writeAllObs i
    { stdout := r.stdout, stderr := r.stderr, consumed := c, reads := rd, fs := i.fs, log := lg }
    r.files
  { w.1 with exit := if w.2 then r.exit else 1 }

namespace Prog

/-- **A program from a pure core** on the arguments and stdin. -/
def ofCore (core : List String → Bytes → Result) : Prog ExitCode := do
  let a ← getArgs
  let s ← readStdin
  emit (core a s)

/-- **A tool from a pure core**: `reads args` names the input files; the core gets the
arguments and their contents (`none`: absent or unreadable). It does not read stdin. -/
def ofTool (reads : List String → List String)
    (core : List String → List (String × Option Bytes) → Result) : Prog ExitCode := do
  let a ← getArgs
  let fs ← readAll (reads a)
  emit (core a fs)

end Prog

/-- The contents of the file the string `s` names, if any. -/
def _root_.Silmaril.Cli.Input.fileAt (i : Input) (s : String) : Option Bytes := (i.resolve s).bind i.fs

/-- The rooted path of the file `s` names, when there is a file. -/
def _root_.Silmaril.Cli.Input.readPath (i : Input) (s : String) : Option FPath :=
  (i.resolve s).filter fun q => (i.fs q).isSome

/-- The file-log event of reading the file `s` names, when there is a file. -/
def _root_.Silmaril.Cli.Input.readEv (i : Input) (s : String) : Option FileEv :=
  (i.readPath s).map fun q => .read q (i.fs q)

end Silmaril.Cli.Io

end
