module

public import Mathlib.Order.CompleteLattice.Basic

/-!
# CLI behaviour: observations, specifications, refinement, composition

A loose model of what a command-line program does, as seen from outside (`docs/projects/wasm-binaryen-tooling.md`,
track *behaviour*). It is the target that argument grammars (track *args*), Lean `IO`
programs and WASI `wasi:cli/command` components (track *bridge*) and real tools (track
*apply*) are related to.

## The model

* An **invocation** `Input`: program name, arguments (without the program name), environment,
  stdin, the declared roots (WASI preopens, `wasmtime --dir`) and the files under them.
* An **observation** `Obs` of a terminating run: stdout, stderr, exit code, how many stdin
  bytes were consumed, the files read, and the final files.
* Files are `Fs := FPath → Option Bytes`: rooted paths (`root`, components below it) to
  contents. Directories, metadata and file descriptors are not modelled.
* A **specification** `Spec := Input → Obs → Prop` allows a set of observations per input, so
  nondeterminism (e.g. the interleaving of two stderr streams in a pipe) is allowed. It is a
  plain function type, so it inherits Mathlib's complete lattice:
  - **refinement** is `S ≤ T` (`S` refines `T`: every observation `S` allows, `T` allows);
  - `S ⊓ T` asks for both, `⊤` (chaos) allows everything, `⊥` (miracle) nothing.
  An implementation is read as the spec of its possible observations, so "implements" is
  refinement too (`det f ≤ S ↔ ∀ i, S i (f i)`).

The model is *partial correctness*: it says nothing about runs that do not terminate, and
`⊥` refines everything. `Total S` (every input has an allowed observation) rules out
miracles; it is inherited upwards along `≤`.

## Builders

* `det f`, `pure f` (a filter that touches no files), `prints f`, and requirements meant to be
  combined with `⊓`: `exits c`, `succeeds`, `fails`, `stdoutIs`, `stderrIs`, `silent`, `keepsFiles`,
  `confined` (the footprint lies under the declared roots), `consumesAll`.
* `guard P S` (`S` where `P` holds, chaos elsewhere: a precondition).
* Allowances: `orFail S` (also a nonzero exit after a prefix of an allowed stdout) and
  `orRefused S` (after an environment refusal, a prefix of an allowed stdout, then the allowed
  exit or a failure).

## Partial observations

`Seen` is what has been observed of a run so far; `S.Partial i p` says `p` is a partial view
(`Seen.Le`, `≼`) of an observation `S` allows. Views of WASI traces and LPS trace prefixes
produce `Seen`s.

## Composition

* `mapInput f S`, `withArgs as S`, `withStdin bs S`, `setEnv k v S`: change the invocation.
* `seq S T` (`S; T`): stdin and files threaded, outputs concatenated, `T`'s exit code.
  `andThen S T` (`S && T`) and `orElse S T` (`S || T`) short-circuit on the exit code.
* `pipe S T` (`S | T`): `T` reads `S`'s stdout; the two stderr streams are interleaved in any
  way (`Interleave`); the two programs' file logs interleave in any order that replays from the
  files before the pipe (exact for shared files, `coherent`); `T`'s exit code (no `pipefail`).
  `pipeO` is the open form (associative), `pipeSeq` the schedule "`S`'s files first".
* `case k S` (the coproduct, or copairing, of the specs `S a` along the classifier `k`) and
  `dispatch cmds dflt`: subcommand dispatch on the first argument, a `case`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli

/-- Byte strings. -/
abbrev Bytes := List UInt8

/-- The UTF-8 bytes of a string. -/
def utf8 (s : String) : Bytes := s.toUTF8.toList

/-- A declared root: a WASI preopen (`wasmtime --dir`), by name, read-only or writable. -/
structure Root where
  /-- The guest-visible name of the root, e.g. `"."` or `"/work"`. -/
  name : String
  /-- Whether files under the root may be written or created. -/
  writable : Bool := true
deriving DecidableEq, Repr, Inhabited

/-- A path under a root: the root's name and the components below it. -/
structure FPath where
  /-- The name of the root. -/
  root : String
  /-- The path components below the root. -/
  rel : List String
deriving DecidableEq, Repr, Inhabited

/-- Files: the contents of each rooted path, `none` when there is no file. -/
abbrev Fs := FPath → Option Bytes

namespace Fs

/-- No files. -/
def empty : Fs := fun _ => none

/-- Set (or, with `none`, remove) the file at `p`. -/
def set (fs : Fs) (p : FPath) (c : Option Bytes) : Fs := fun q => if q = p then c else fs q

/-- Files from a list; the first entry of a path wins. -/
def ofList (l : List (FPath × Bytes)) : Fs := fun p => l.lookup p

end Fs

/-- **A whole-file event** of a run, in the order the run made it. -/
inductive FileEv where
  /-- The run read the file `p` and saw `c` (`none`: no file). -/
  | read (p : FPath) (c : Option Bytes)
  /-- The run set the file `p` to `c` (`none`: removed it). -/
  | write (p : FPath) (c : Option Bytes)
deriving DecidableEq, Repr

/-- **Replay a file log** on the files `fs`: the files after its writes, or `none` when a read
saw something other than what the files held at that point. -/
def Fs.replay (fs : Fs) : List FileEv → Option Fs
  | [] => some fs
  | .read p c :: l => if fs p = c then Fs.replay fs l else none
  | .write p c :: l => Fs.replay (fs.set p c) l

/-- **An invocation of a command-line program.** -/
structure Input where
  /-- The program name (`argv[0]`). -/
  prog : String := "prog"
  /-- The arguments, without the program name. -/
  args : List String := []
  /-- The environment, in order; the first binding of a name wins. -/
  env : List (String × String) := []
  /-- Standard input. -/
  stdin : Bytes := []
  /-- The declared roots. -/
  roots : List Root := []
  /-- The files before the run. -/
  fs : Fs := Fs.empty

namespace Input

/-- `argv`: the program name, then the arguments (what WASI's `get-arguments` returns). -/
def argv (i : Input) : List String := i.prog :: i.args

/-- The value of the environment variable `k`. -/
def getEnv (i : Input) (k : String) : Option String := i.env.lookup k

/-- `p` lies under a declared root. -/
def Under (i : Input) (p : FPath) : Prop := p.root ∈ i.roots.map Root.name

/-- `p` lies under a declared writable root. -/
def Writable (i : Input) (p : FPath) : Prop :=
  p.root ∈ (i.roots.filter Root.writable).map Root.name

instance (i : Input) (p : FPath) : Decidable (i.Under p) := by unfold Under; infer_instance
instance (i : Input) (p : FPath) : Decidable (i.Writable p) := by unfold Writable; infer_instance

end Input

/-- Exit codes: a process exit status, `0` for success. -/
abbrev ExitCode := UInt8

/-- **An observation of a terminating run.** -/
structure Obs where
  /-- Everything written to stdout. -/
  stdout : Bytes := []
  /-- Everything written to stderr. -/
  stderr : Bytes := []
  /-- The exit code. -/
  exit : ExitCode := 0
  /-- How many bytes of stdin were consumed. -/
  consumed : Nat := 0
  /-- The files read (as a set: order and repetition carry no meaning). -/
  reads : List FPath := []
  /-- The files after the run. -/
  fs : Fs
  /-- The environment refused an operation during the run (an error answer, a write that
  accepted nothing: a closed stdout, a full disk). Specs usually ignore it; `orRefused` lets a
  run lose output, or fail, after a refusal. -/
  refused : Bool := false
  /-- The whole-file reads and writes, in order (`FileEv`). Optional detail: a spec that fixes
  it (`Spec.Logged`) can be composed exactly in a pipe whose programs share files. -/
  log : List FileEv := []

/-- The invocation left for a program run after one observed as `o`: the rest of stdin and
the files `o` left; arguments, environment and roots are shared. -/
def Input.after (i : Input) (o : Obs) : Input :=
  { i with stdin := i.stdin.drop o.consumed, fs := o.fs }

/-- Two observations one after the other: outputs and reads concatenated, consumption added,
the second's exit code and files. -/
def Obs.andThen (o₁ o₂ : Obs) : Obs where
  stdout := o₁.stdout ++ o₂.stdout
  stderr := o₁.stderr ++ o₂.stderr
  exit := o₂.exit
  consumed := o₁.consumed + o₂.consumed
  reads := o₁.reads ++ o₂.reads
  fs := o₂.fs
  refused := o₁.refused || o₂.refused
  log := o₁.log ++ o₂.log

/-- `l` is an interleaving of `a` and `b` (each kept in order). -/
inductive Interleave {α : Type} : List α → List α → List α → Prop where
  | nil : Interleave [] [] []
  | left {x a b l} : Interleave a b l → Interleave (x :: a) b (x :: l)
  | right {x a b l} : Interleave a b l → Interleave a (x :: b) (x :: l)

/-- **A partial observation**: what has been seen of a run so far, possibly before it ended
(a component observed mid-run, an LPS trace prefix, a harness that does not see everything).
Streams are what was written so far; `exit` is `some c` once the run has ended with `c`;
`consumed` and `reads` are lower bounds; `fs` is the final files when they were observed;
`refused` records a refusal seen so far. `Seen.Le p o` (`p ≼ o`) says `p` is a partial view of
the complete observation `o`. -/
structure Seen where
  /-- Stdout written so far. -/
  stdout : Bytes := []
  /-- Stderr written so far. -/
  stderr : Bytes := []
  /-- The exit code, once the run has ended. -/
  exit : Option ExitCode := none
  /-- Stdin consumed so far (a lower bound). -/
  consumed : Nat := 0
  /-- Files read so far (a lower bound). -/
  reads : List FPath := []
  /-- The files at the end of the run, when observed. -/
  fs : Option Fs := none
  /-- A refusal was seen. -/
  refused : Bool := false

/-- **`p` is a partial view of `o`**: its streams are prefixes, its counts lower bounds, a refusal
it saw is `o`'s; once it has seen the end, the streams and exit code are exactly `o`'s, and so
are the files if it saw them. -/
def Seen.Le (p : Seen) (o : Obs) : Prop :=
  p.stdout <+: o.stdout ∧ p.stderr <+: o.stderr ∧ p.consumed ≤ o.consumed ∧
    (∀ q ∈ p.reads, q ∈ o.reads) ∧ (p.refused = true → o.refused = true) ∧
    ∀ c, p.exit = some c →
      c = o.exit ∧ p.stdout = o.stdout ∧ p.stderr = o.stderr ∧ ∀ f, p.fs = some f → f = o.fs

@[inherit_doc] scoped infix:50 " ≼ " => Seen.Le

/-- The complete view of an observation. -/
def Obs.seen (o : Obs) : Seen :=
  { stdout := o.stdout, stderr := o.stderr, exit := some o.exit, consumed := o.consumed,
    reads := o.reads, fs := some o.fs, refused := o.refused }

/-- **A CLI behaviour specification**: the observations allowed for each invocation.
Refinement is `≤` (Mathlib's order on predicates). -/
abbrev Spec := Input → Obs → Prop

namespace Spec

/-- Every invocation has an allowed observation (no miracles). -/
def Total (S : Spec) : Prop := ∀ i, ∃ o, S i o

/-! ## Builders -/

/-- Exactly the observation `f i`: a deterministic program, or a fully determined spec. -/
def det (f : Input → Obs) : Spec := fun i o => o = f i

/-- What a program that touches no files shows. -/
structure Out where
  /-- Stdout. -/
  stdout : Bytes := []
  /-- Stderr. -/
  stderr : Bytes := []
  /-- The exit code. -/
  exit : ExitCode := 0

/-- The observation of a program that touches no files, consumed `c` bytes of stdin and left
the files `fs`. -/
def Out.toObs (r : Out) (c : Nat) (fs : Fs) : Obs :=
  { stdout := r.stdout, stderr := r.stderr, exit := r.exit, consumed := c, fs := fs }

/-- **A pure program**: outputs and exit code `f i`, no file read or changed (an empty file
log), any amount of stdin consumed. -/
def pure (f : Input → Out) : Spec := fun i o =>
  o.stdout = (f i).stdout ∧ o.stderr = (f i).stderr ∧ o.exit = (f i).exit ∧
    o.fs = i.fs ∧ o.reads = [] ∧ o.consumed ≤ i.stdin.length ∧ o.log = []

/-- **Print `f i` and succeed**: exit `0`, stdout `f i`, no file changed; stderr is free (the
bridge's `prints`). -/
def prints (f : Input → Bytes) : Spec := fun i o => o.exit = 0 ∧ o.stdout = f i ∧ o.fs = i.fs

/-- Exit code `c`. -/
def exits (c : ExitCode) : Spec := fun _ o => o.exit = c

/-- Exit code `0`. -/
def succeeds : Spec := exits 0

/-- A nonzero exit code. -/
def fails : Spec := fun _ o => o.exit ≠ 0

/-- Stdout is `f i`. -/
def stdoutIs (f : Input → Bytes) : Spec := fun i o => o.stdout = f i

/-- Stderr is `f i`. -/
def stderrIs (f : Input → Bytes) : Spec := fun i o => o.stderr = f i

/-- Nothing on stderr. -/
def silent : Spec := fun _ o => o.stderr = []

/-- No file changed. -/
def keepsFiles : Spec := fun i o => o.fs = i.fs

/-- All of stdin consumed. -/
def consumesAll : Spec := fun i o => o.consumed = i.stdin.length

/-- **The footprint lies under the declared roots**: files read are under a root, changed
files under a writable root, and no more stdin is consumed than there is. -/
def confined : Spec := fun i o =>
  (∀ p ∈ o.reads, i.Under p) ∧ (∀ p, o.fs p ≠ i.fs p → i.Writable p) ∧
    o.consumed ≤ i.stdin.length

/-- The environment refused nothing. -/
def reliable : Spec := fun _ o => o.refused = false

/-- **`S`, or a failure**: the run may also exit nonzero, for any reason, having written a
prefix of what an allowed observation writes on stdout. Stderr (a diagnostic), files and the
rest are free. The usual allowance for "for every host" statements in which the host may stop
a run (a trap, an `exit` call the spec does not foresee). -/
def orFail (S : Spec) : Spec := fun i o =>
  S i o ∨ (o.exit ≠ 0 ∧ ∃ o', S i o' ∧ o.stdout <+: o'.stdout)

/-- **`S`, or output lost to a refusal**: after the environment refused an operation (a closed
stdout, a full disk, a failed WASI write), the run may have written only a prefix of what an
allowed observation writes on stdout, and then ends as that observation does or fails
(nonzero). Stderr and files are free. A program that ignores failed writes (exit `0`) and one
that reports them (exit `1`) both satisfy `orRefused S` when their reliable runs satisfy `S`.
In a reliable environment this is `S` again (`orRefused_inf_reliable`); its failing runs are
`orFail`'s (`orRefused_inf_fails_le_orFail`). -/
def orRefused (S : Spec) : Spec := fun i o =>
  S i o ∨ (o.refused = true ∧
    ∃ o', S i o' ∧ o.stdout <+: o'.stdout ∧ (o.exit = o'.exit ∨ o.exit ≠ 0))

/-- **The file log replays**: from the files before the run, every read of `o.log` sees what
the files hold at that point and the writes lead to `o.fs`. -/
def coherent : Spec := fun i o => i.fs.replay o.log = some o.fs

/-- **`S` logs its file effects**: every observation it allows is `coherent`. Pipes compose
logged specs exactly (`pipe`). -/
def Logged (S : Spec) : Prop := S ≤ coherent

/-- `S` where `P` holds, anything elsewhere: `P` is a precondition. -/
def guard (P : Input → Prop) (S : Spec) : Spec := fun i o => P i → S i o

/-! ## Changing the invocation -/

/-- Run `S` on the invocation changed by `f`. -/
def mapInput (f : Input → Input) (S : Spec) : Spec := fun i o => S (f i) o

/-- Run `S` with the arguments `as` (the invocation's arguments are ignored). -/
def withArgs (as : List String) (S : Spec) : Spec := mapInput (fun i => { i with args := as }) S

/-- Run `S` with stdin `bs`. -/
def withStdin (bs : Bytes) (S : Spec) : Spec := mapInput (fun i => { i with stdin := bs }) S

/-- Run `S` with the environment variable `k` set to `v`. -/
def setEnv (k v : String) (S : Spec) : Spec := mapInput (fun i => { i with env := (k, v) :: i.env }) S

/-! ## Sequential composition -/

/-- **`S; T`**: `T` runs on what `S` left (rest of stdin, files). -/
def seq (S T : Spec) : Spec := fun i o =>
  ∃ o₁ o₂, S i o₁ ∧ T (i.after o₁) o₂ ∧ o = o₁.andThen o₂

/-- **`S && T`**: `T` runs only when `S` succeeds. -/
def andThen (S T : Spec) : Spec := fun i o =>
  (∃ o₁ o₂, S i o₁ ∧ o₁.exit = 0 ∧ T (i.after o₁) o₂ ∧ o = o₁.andThen o₂) ∨ (S i o ∧ o.exit ≠ 0)

/-- **`S || T`**: `T` runs only when `S` fails. -/
def orElse (S T : Spec) : Spec := fun i o =>
  (∃ o₁ o₂, S i o₁ ∧ o₁.exit ≠ 0 ∧ T (i.after o₁) o₂ ∧ o = o₁.andThen o₂) ∨ (S i o ∧ o.exit = 0)

/-- **The program that does nothing and succeeds** (`true`). -/
def skip : Spec := fun i o => o = { fs := i.fs }

/-! ## Pipes -/

/-- **The open pipe `S | T`**: `T`'s stdin is `S`'s stdout; stdout and exit code are `T`'s, the
stderr streams and the file logs interleave in any way, the pipe consumes what `S` consumed.
Each program runs on files `fs₁`, `fs₂` of its own: what it saw of the shared files is in its
log. The files are not closed yet (`o.fs` is free): `pipe` adds `coherent`. -/
def pipeO (S T : Spec) : Spec := fun i o =>
  ∃ o₁ o₂ fs₁ fs₂, S { i with fs := fs₁ } o₁ ∧ T { i with stdin := o₁.stdout, fs := fs₂ } o₂ ∧
    o.stdout = o₂.stdout ∧ Interleave o₁.stderr o₂.stderr o.stderr ∧ o.exit = o₂.exit ∧
    o.consumed = o₁.consumed ∧ o.reads = o₁.reads ++ o₂.reads ∧
    Interleave o₁.log o₂.log o.log ∧ o.refused = (o₁.refused || o₂.refused)

/-- **`S | T`**, exactly: the two programs run concurrently on shared files, so their file
events interleave in any order that replays from the files before the pipe (`coherent`), and
the files after are those of the interleaving. For logged specs (`Logged`) whose runs read each
path at most once and not after writing it, these are exactly the runs of the pipe: `T` may
read a file before or after `S` writes it. The sequential schedule is one of them
(`pipeSeq_le_pipe`). A pipeline `a | b | c` is `pipeO (pipeO a b) c ⊓ coherent`
(`pipeO_assoc`), with one closing for all its programs. -/
def pipe (S T : Spec) : Spec := pipeO S T ⊓ coherent

/-- **`S | T` scheduled `S` first**: `T` runs on the files `S` left (the pass-1 pipe). Exact up
to the order of the file log when the footprints are separate (disjoint, or shared read-only)
and the specs framed (`Silmaril.Cli.Footprint`: `pipe_le_pipeSeq`, `relog_pipe_eq`); with shared
files it is only the schedule in which `S` finishes its file effects first (`pipeSeq_le_pipe`).
Associative (`pipeSeq_assoc`). -/
def pipeSeq (S T : Spec) : Spec := fun i o =>
  ∃ o₁ o₂, S i o₁ ∧ T { i with stdin := o₁.stdout, fs := o₁.fs } o₂ ∧
    o.stdout = o₂.stdout ∧ Interleave o₁.stderr o₂.stderr o.stderr ∧ o.exit = o₂.exit ∧
    o.consumed = o₁.consumed ∧ o.reads = o₁.reads ++ o₂.reads ∧ o.fs = o₂.fs ∧
    o.refused = (o₁.refused || o₂.refused) ∧ o.log = o₁.log ++ o₂.log

/-! ## Partial observations -/

/-- **`p` is a partial view of a run `S` allows** on `i`: the output so far extends to an
allowed observation, and is one once the run has ended. -/
def Partial (S : Spec) (i : Input) (p : Seen) : Prop := ∃ o, S i o ∧ p ≼ o

/-! ## Case analysis and subcommand dispatch -/

/-- **The copairing of the specs `S a` along the classifier `k`**: on an invocation `i`, the
spec `S (k i)`. With `k` the subcommand an invocation names, this is subcommand dispatch. -/
def case {α : Type} (k : Input → α) (S : α → Spec) : Spec := fun i o => S (k i) i o

/-- The command an invocation selects from `cmds` (by its first argument), with the remaining
arguments. -/
def select (cmds : List (String × Spec)) (i : Input) : Option (Spec × List String) :=
  match i.args with
  | c :: rest => (cmds.lookup c).map (·, rest)
  | [] => none

/-- **Subcommand dispatch**: when the first argument names a command of `cmds`, that command
runs on the remaining arguments; otherwise `dflt` runs (usually a usage error). -/
def dispatch (cmds : List (String × Spec)) (dflt : Spec) : Spec :=
  case (select cmds) fun
    | some (S, rest) => withArgs rest S
    | none => dflt

end Spec

end Silmaril.Cli
