module

public import Silmaril.Cli.Io.Check.Defs

/-!
# Running CLI programs and checking binaries

* `Prog.toIO args p`: runs a `Prog` with Lean's `IO` (the trusted reading of each operation:
  `IO.getEnv`, stdin read to its end, writes flushed, `IO.FS.readBinFile`/`writeBinFile` relative
  to the working directory, a failed write answered `false`, `IO.Process.exit`). `Prog.main`
  makes a `main` of it. The model's reading of the same operations is `Prog.exec`; that `IO`
  does what `exec` says is the trusted part of the bridge (as for every `IO` program).
* **The test harness**: a `Case` is an invocation with one writable root `"."` (the working
  directory) holding its files (`Case.input`). `runBinary cmd pre c` runs `cmd pre… args` in a
  fresh temporary directory holding the files, with exactly the environment `c.env` (nothing
  inherited), feeds `c.stdin`, and returns what it sees (`Snap`): stdout, stderr, the exit code
  (low 8 bits) and the files that are new or changed. `checkCases` runs cases against a `Check`
  and reports one line per case.

`argv[0]` cannot be chosen through `IO.Process.spawn`: the binary sees its own name (or what
`pre` makes of it, e.g. wasmtime passes the component's file name), so a `Check` used here must not
depend on `Input.prog`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Io

/-- A byte list as a `ByteArray`. -/
def toBA (b : Bytes) : ByteArray := ⟨b.toArray⟩

namespace Prog

variable {α : Type}

/-- **Run a program with `IO`**, with its arguments given. -/
def toIO (args : List String) : Prog α → IO α
  | .pure a => return a
  | .args k => toIO args (k args)
  | .env n k => do
    let v ← IO.getEnv n
    toIO args (k v)
  | .stdin k => do
    let b ← (← IO.getStdin).readBinToEnd
    toIO args (k b.data.toList)
  | .out s b k => do
    let h ← match s with
      | .stdout => IO.getStdout
      | .stderr => IO.getStderr
    h.write (toBA b)
    h.flush
    toIO args k
  | .read p k => do
    let r ← (do return some (← IO.FS.readBinFile p)) <|> (return none : IO (Option ByteArray))
    toIO args (k (r.map (·.data.toList)))
  | .write p b k => do
    let ok ← (do IO.FS.writeBinFile p (toBA b); return true) <|> (return false : IO Bool)
    toIO args (k ok)
  | .exit c => IO.Process.exit c

/-- A `main` for a program. -/
def main (p : Prog ExitCode) (args : List String) : IO UInt32 := do
  let c ← p.toIO args
  return c.toUInt32

end Prog

/-! ## The harness -/

/-- **One test case**: arguments, environment, stdin and the files of the working directory. -/
structure Case where
  /-- A name for the report. -/
  name : String
  /-- The arguments (without the program name). -/
  args : List String := []
  /-- The environment. -/
  env : List (String × String) := []
  /-- Stdin. -/
  stdin : Bytes := []
  /-- The files of the working directory, by relative path. -/
  files : List (String × Bytes) := []

/-- **The invocation of a case**: the working directory is the one writable root `"."`. -/
def Case.input (c : Case) : Input where
  prog := c.name
  args := c.args
  env := c.env
  stdin := c.stdin
  roots := [{ name := "." }]
  fs := Fs.ofList (c.files.map fun (p, b) => (⟨".", pathComps p⟩, b))

/-- The relative path of `f` under `dir`. -/
def relPath (dir f : System.FilePath) : String :=
  (f.toString.drop (dir.toString.length + 1)).toString

/-- The regular files under `dir`, with their contents. -/
def snapshot (dir : System.FilePath) : IO (List (String × Bytes)) := do
  let fs ← dir.walkDir
  let mut out := []
  for f in fs do
    if !(← f.isDir) then
      out := out ++ [(relPath dir f, (← IO.FS.readBinFile f).data.toList)]
  pure out

/-- **Run a binary** on a case: `cmd` with arguments `pre ++ c.args`. -/
def runBinary (cmd : String) (pre : List String) (c : Case) : IO Snap := do
  -- the case runs in a temporary directory: a relative command path is made absolute
  let cmd ← if cmd.contains '/' then
      (return (← IO.FS.realPath cmd).toString : IO String) <|> pure cmd
    else pure cmd
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  let dir ← IO.FS.createTempDir
  for (p, b) in c.files do
    let f := dir / p
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeBinFile f (toBA b)
  let child ← IO.Process.spawn
    { cmd, args := (pre ++ c.args).toArray, cwd := some dir,
      env := (c.env.map fun (k, v) => (k, some v)).toArray, inheritEnv := false,
      stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  let feed ← IO.asTask (prio := .dedicated) do
    stdin.write (toBA c.stdin)
    stdin.flush
  let outT ← IO.asTask (prio := .dedicated) child.stdout.readBinToEnd
  let err ← child.stderr.readBinToEnd
  let code ← child.wait
  let out ← IO.ofExcept outT.get
  let _ := feed.get
  let after ← snapshot dir
  IO.FS.removeDirAll dir
  let changed := after.filter fun (p, b) => c.files.lookup p != some b
  pure { stdout := out.data.toList, stderr := err.data.toList,
         files := changed.map fun (p, b) => (pathComps p, b), exit := code.toUInt8 }

/-- Show bytes, as text when they are valid UTF-8. -/
def showBytes (b : Bytes) : String :=
  match String.fromUTF8? (toBA b) with
  | some s => s.quote
  | none => s!"<{b.length} bytes>"

/-- Show a snapshot. -/
def showSnap (s : Snap) : String :=
  s!"exit {s.exit}, stdout {showBytes s.stdout}, stderr {showBytes s.stderr}, " ++
    s!"files {s.files.map fun f => "/".intercalate f.1}"

/-- **Check cases against a binary**; one `ok:`/`FAIL:` line each. Returns the number of
failures. -/
def checkCases (label : String) (chk : Check) (cmd : String) (pre : List String)
    (cases : List Case) : IO Nat := do
  let mut fails := 0
  for c in cases do
    let s ← runBinary cmd pre c
    if chk c.input s then
      IO.println s!"ok: {label} {c.name}"
    else
      IO.println s!"FAIL: {label} {c.name}: {showSnap s}"
      fails := fails + 1
  pure fails

end Silmaril.Cli.Io

end
