module

public import Silmaril.Cli.Behaviour.Defs

/-!
# CLI behaviour: files named on the command line, and file transformers

See `docs/projects/cli.md`. Most tools of the Binaryen and wasm-tools families
read one input (a file named by an argument, or stdin) and write one output (a file named by
`-o`, or stdout). This module gives that shape as one builder, so that a tool's spec is its
argument handling plus a function on bytes.

* `Input.resolve i s`: the rooted path an argument string names, WASI style. A relative path
  is under the root `"."` (the current directory preopen); an absolute path is under the first
  declared root whose name is an absolute prefix of it. `.` components are dropped; a path with
  a `..` component, or outside every root, names nothing (`none`).
* `FPath.cwd s`, `Input.inCwd i files`: relative paths under the current directory, and an
  invocation whose current directory holds the given files (a harness's test case).
* `Source` (stdin or a file) and `Sink` (stdout or a file); `Source.read` (a file outside the
  roots, or absent, cannot be read) and `Sink.Ok` (a file sink must be under a writable root).
* `failure`: a loose failure: nonzero exit, a non-empty message on stderr, nothing on stdout,
  no file read or changed. The message is left open.
* File logs (`Obs.log`): reading a file source is one `read` event, writing a file sink one
  `write` event after it, so transformers are `Logged` and compose exactly in pipes that share
  files (`logged_transform`).
* **`transform src dst f`**: read the source `src i`, apply `f i`; on `.ok y` write `y` to the
  sink `dst i` and exit `0` with no stderr, on `.error msg` print `msg` on stderr and exit `1`
  with no file changed. When a source or sink is missing (`none`: an unresolvable argument) or
  cannot be used, it is a `failure`.
* `filter f`: stdin to stdout through a total function.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli

/-- The path components of a string, without empty and `.` components. -/
def pathComps (s : String) : List String :=
  (s.splitOn "/").filter fun c => c ≠ "" ∧ c ≠ "."

/-- **The rooted path an argument names** (WASI style), if any. -/
def Input.resolve (i : Input) (s : String) : Option FPath :=
  let cs := pathComps s
  if ".." ∈ cs then none
  else if s.startsWith "/" then
    (i.roots.find? fun r => r.name.startsWith "/" && (pathComps r.name).isPrefixOf cs).map
      fun r => ⟨r.name, cs.drop (pathComps r.name).length⟩
  else if i.roots.any (·.name == ".") then some ⟨".", cs⟩
  else none

/-- The path a relative path string names under the current directory preopen `"."`. -/
def FPath.cwd (s : String) : FPath := ⟨".", pathComps s⟩

/-- **The invocation with the current directory as a writable root holding `files`** (relative
path strings), the shape of a test case of a harness that runs a binary in a fresh temporary
directory. -/
def Input.inCwd (i : Input) (files : List (String × Bytes)) : Input :=
  { i with roots := { name := "." } :: i.roots,
           fs := Fs.ofList (files.map fun f => (FPath.cwd f.1, f.2)) }

/-- Where a tool reads its input. -/
inductive Source where
  /-- Standard input. -/
  | stdin
  /-- A file. -/
  | file (p : FPath)
deriving DecidableEq, Repr

/-- Where a tool writes its output. -/
inductive Sink where
  /-- Standard output. -/
  | stdout
  /-- A file. -/
  | file (p : FPath)
deriving DecidableEq, Repr

/-- The contents of a source, if it can be read: a file must exist under a declared root. -/
def Source.read (i : Input) : Source → Option Bytes
  | .stdin => some i.stdin
  | .file p => if i.Under p then i.fs p else none

/-- The stdin consumed by reading a source. -/
def Source.consumed (i : Input) : Source → Nat
  | .stdin => i.stdin.length
  | .file _ => 0

/-- The files read by reading a source. -/
def Source.reads : Source → List FPath
  | .stdin => []
  | .file p => [p]

/-- The file log of reading a source: one read of the file, seeing what it holds. -/
def Source.log (i : Input) : Source → List FileEv
  | .stdin => []
  | .file p => [.read p (i.fs p)]

/-- A sink can be written: stdout always, a file under a writable root. -/
def Sink.Ok (i : Input) : Sink → Prop
  | .stdout => True
  | .file p => i.Writable p

/-- The observation of writing `y` to the sink `d` (stdin consumed `c`, files read `r`, file
log `l` so far). -/
def Sink.write (i : Input) (c : Nat) (r : List FPath) (l : List FileEv) (y : Bytes) : Sink → Obs
  | .stdout => { stdout := y, consumed := c, reads := r, fs := i.fs, log := l }
  | .file p => { consumed := c, reads := r, fs := i.fs.set p (some y), log := l ++ [.write p (some y)] }

namespace Spec

/-- **A loose failure**: nonzero exit, some message on stderr, nothing on stdout, no file read
or changed, no more stdin consumed than there is. -/
def failure : Spec := fun i o =>
  o.exit ≠ 0 ∧ o.stderr ≠ [] ∧ o.stdout = [] ∧ o.reads = [] ∧ o.fs = i.fs ∧
    o.consumed ≤ i.stdin.length ∧ o.log = []

/-- The spec of `transform` once source and sink are known. -/
def transformAt (s : Source) (d : Sink) (f : Bytes → Except Bytes Bytes) : Spec := fun i o =>
  match s.read i with
  | none => failure i o
  | some x =>
    match f x with
    | .error msg =>
      o = { stderr := msg, exit := 1, consumed := s.consumed i, reads := s.reads, fs := i.fs,
            log := s.log i }
    | .ok y => (d.Ok i ∧ o = d.write i (s.consumed i) s.reads (s.log i) y) ∨ (¬ d.Ok i ∧ failure i o)

/-- **A file transformer**: source `src i`, sink `dst i`, function `f i` (see the module
docstring). -/
def transform (src : Input → Option Source) (dst : Input → Option Sink)
    (f : Input → Bytes → Except Bytes Bytes) : Spec := fun i o =>
  match src i, dst i with
  | some s, some d => transformAt s d (f i) i o
  | _, _ => failure i o

/-- **A filter**: stdin to stdout through `f`. -/
def filter (f : Bytes → Bytes) : Spec :=
  transform (fun _ => some .stdin) (fun _ => some .stdout) fun _ x => .ok (f x)

end Spec

end Silmaril.Cli
