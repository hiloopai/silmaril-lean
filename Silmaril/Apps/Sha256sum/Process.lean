module

public import Silmaril.Apps.Sha256sum.Run

/-! # `sha256sum` over a system-call process model

`sha256sum : World → Outcome` says what the program shows. This file says what it means for
a *program* (a machine that issues system calls: a Lean reference program, or the x86-64
binary under an instruction-set model) to implement it.

## The model

* `Call`/`Ret`: the system calls that cross the world boundary (spec.md §10): `openat`
  read-only, `read`, `write`, `close`; `exit_group` ends a run. `brk` is the process's own
  memory management, invisible to the world, and is handled by the machine adapter
  (`Sha256sum.X86Sys`), not by the environment.
* `KState` and `worldEnv w`: a kernel consistent with the world `w`. Descriptors 0, 1 and 2
  are open; `openat` consults the oracle `w.fs`; reads deliver the file's bytes in **any
  chunking** (any nonempty prefix of what is left, the empty read only at the end), then
  EOF, or the oracle's read error; standard input is consumed once; writes to 1 and 2 may be
  **partial** (any nonempty prefix is accepted); on a full standard output every write to 1
  fails with `ENOSPC`.
* `Machine`: a program as a state machine whose steps are internal, a system call with a
  continuation on the reply, an exit, or stuck (a fault or an unmodeled instruction).
* `Exec M E s k evs n`: from program state `s` and kernel state `k`, the program issues the
  calls and receives the replies `evs` under environment `E`, and exits with status `n`.
* `observe evs n`: the bytes accepted on 1 and on 2, and the status.

The observation is what crosses the process boundary, not the calls: two programs that
chunk their reads and writes differently are indistinguishable (compare `CLI.Observation`
on branch `process/cli-model`).

## The statements

* `Satisfies M E init dom`: on every world in `dom`, every exiting run observes exactly
  `sha256sum w`. Safety only.
* `Live M E init dom budget`: every run on a world in `dom` takes at most `budget w` steps
  and never gets stuck, so every maximal run exits.
* `Satisfies.mono`, `Live.mono`: both transfer to any smaller environment (`E' ≤ E`). This
  is the lattice argument of `Process/CLI/Env.lean` (branch `process/cli-model`) for this
  richer call set: prove at the most permissive environment that works, reuse everywhere
  below.

`worldEnv` admits neither `EINTR` nor `EIO` mid-file nor partial-failure writes: it is the
`reliable` point of that ladder, extended with files. Those are listed as open in
`Sha256sum/Plan.lean`.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Sys

open Silmaril.Apps.Sha256sum

/-! ## Calls and replies -/

inductive Call where
  | openat (path : Bytes)
  | read (fd count : Nat)
  | write (fd : Nat) (bytes : Bytes)
  | close (fd : Nat)
  deriving DecidableEq, Repr

inductive Ret where
  /-- A count or a descriptor. -/
  | ok (n : Nat)
  /-- The bytes of a successful read. -/
  | data (b : Bytes)
  | err (e : Errno)
  deriving DecidableEq, Repr

/-- What an open descriptor refers to. -/
inductive Src where
  | stdin
  | stdout
  | stderr
  /-- A file opened read-only: its oracle result and the read position. -/
  | file (r : ReadResult) (pos : Nat)
  deriving DecidableEq, Repr

structure KState where
  fds : Nat → Option Src
  /-- What is left of standard input. -/
  stdin : Stdin

def KState.init (w : World) : KState where
  fds n := if n = 0 then some .stdin else if n = 1 then some .stdout
    else if n = 2 then some .stderr else none
  stdin := w.stdin

def KState.set (k : KState) (fd : Nat) (s : Option Src) : KState :=
  { k with fds := fun n => if n = fd then s else k.fds n }

/-- An environment: which replies (and next kernel states) a call admits. -/
abbrev Env := KState → Call → Ret → KState → Prop

/-- A read of up to `count` bytes from `rest` returns a chunk: nonempty unless `rest` is
empty or the request is for zero bytes. -/
def Chunk (rest : Bytes) (count : Nat) (b : Bytes) : Prop :=
  b <+: rest ∧ b.length ≤ count ∧ (b = [] → rest = [] ∨ count = 0)

/-- A write accepts a nonempty prefix of a nonempty buffer. -/
def Accepts (bytes : Bytes) (n : Nat) : Prop := n ≤ bytes.length ∧ (bytes ≠ [] → 0 < n)

/-- The kernel of a world `w`. -/
inductive WorldStep (w : World) : Env
  | openFail {k path e} : w.fs path = .openErr e → WorldStep w k (.openat path) (.err e) k
  | openOk {k path fd} : (∀ e, w.fs path ≠ .openErr e) → k.fds fd = none →
      WorldStep w k (.openat path) (.ok fd) (k.set fd (some (.file (w.fs path) 0)))
  | readStdin {k fd count b rest} : k.fds fd = some .stdin → k.stdin = .bytes rest →
      Chunk rest count b → WorldStep w k (.read fd count) (.data b)
        { k with stdin := .bytes (rest.drop b.length) }
  | readStdinDir {k fd count} : k.fds fd = some .stdin → k.stdin = .dir →
      WorldStep w k (.read fd count) (.err .EISDIR) k
  | readFile {k fd count d pos b} : k.fds fd = some (.file (.ok d) pos) →
      Chunk (d.drop pos) count b →
      WorldStep w k (.read fd count) (.data b) (k.set fd (some (.file (.ok d) (pos + b.length))))
  | readPartial {k fd count e pre pos b} : k.fds fd = some (.file (.readErr e pre) pos) →
      pos < pre.length → Chunk (pre.drop pos) count b → b ≠ [] →
      WorldStep w k (.read fd count) (.data b)
        (k.set fd (some (.file (.readErr e pre) (pos + b.length))))
  | readFail {k fd count e pre pos} : k.fds fd = some (.file (.readErr e pre) pos) →
      pre.length ≤ pos → WorldStep w k (.read fd count) (.err e) k
  | readBad {k fd count} : (k.fds fd = none ∨ k.fds fd = some .stdout ∨ k.fds fd = some .stderr) →
      WorldStep w k (.read fd count) (.err .EBADF) k
  | writeOut {k fd bytes n} : k.fds fd = some .stdout → w.stdoutFull = false → Accepts bytes n →
      WorldStep w k (.write fd bytes) (.ok n) k
  | writeFull {k fd bytes} : k.fds fd = some .stdout → w.stdoutFull = true →
      WorldStep w k (.write fd bytes) (.err .ENOSPC) k
  | writeErr {k fd bytes n} : k.fds fd = some .stderr → Accepts bytes n →
      WorldStep w k (.write fd bytes) (.ok n) k
  | writeBad {k fd bytes} : (k.fds fd = none ∨ k.fds fd = some .stdin ∨
      ∃ r p, k.fds fd = some (.file r p)) → WorldStep w k (.write fd bytes) (.err .EBADF) k
  | closeOk {k fd s} : k.fds fd = some s → WorldStep w k (.close fd) (.ok 0) (k.set fd none)
  | closeBad {k fd} : k.fds fd = none → WorldStep w k (.close fd) (.err .EBADF) k

/-! ## Programs -/

inductive Action (S : Type) where
  | tau (s : S)
  | call (c : Call) (k : Ret → S)
  | exit (status : Nat)
  /-- A fault, or a configuration the model gives no meaning to. -/
  | stuck

structure Machine where
  State : Type
  step : State → Action State

/-- One observable event: a call and its reply. -/
abbrev Event := Call × Ret

/-- A run that ends in `exit_group(n)`; `n` is reduced modulo 256 as Linux does. -/
inductive Exec (M : Machine) (E : Env) : M.State → KState → List Event → Nat → Prop
  | exit {s k n} : M.step s = .exit n → Exec M E s k [] (n % 256)
  | tau {s s' k evs n} : M.step s = .tau s' → Exec M E s' k evs n → Exec M E s k evs n
  | call {s c f k r k' evs n} : M.step s = .call c f → E k c r k' →
      Exec M E (f r) k' evs n → Exec M E s k ((c, r) :: evs) n

/-- A partial run of `steps` machine steps. -/
inductive Reach (M : Machine) (E : Env) : Nat → M.State → KState → M.State → KState → Prop
  | refl {s k} : Reach M E 0 s k s k
  | tau {n s s' k t kt} : M.step s = .tau s' → Reach M E n s' k t kt → Reach M E (n + 1) s k t kt
  | call {n s c f k r k' t kt} : M.step s = .call c f → E k c r k' →
      Reach M E n (f r) k' t kt → Reach M E (n + 1) s k t kt

/-- The bytes accepted on descriptor `fd`. -/
def written (fd : Nat) : List Event → Bytes
  | [] => []
  | (.write d bytes, .ok n) :: rest => (if d = fd then bytes.take n else []) ++ written fd rest
  | _ :: rest => written fd rest

def observe (evs : List Event) (status : Nat) : Outcome :=
  { stdout := written 1 evs, stderr := written 2 evs, status := status }

/-! ## The statements -/

/-- Safety: every exiting run on a world of `dom` shows `sha256sum w`. The program is
started from `init w` (its loader: arguments, environment, image). -/
def Satisfies (M : Machine) (env : World → Env) (init : World → M.State) (dom : World → Prop) :
    Prop :=
  ∀ w, dom w → ∀ evs n, Exec M (env w) (init w) (KState.init w) evs n →
    observe evs n = sha256sum w

/-- Liveness within a budget: no reachable state is stuck, and no run is longer than
`budget w` steps. With `Satisfies`, every maximal run exits with `sha256sum w`. -/
def Live (M : Machine) (env : World → Env) (init : World → M.State) (dom : World → Prop)
    (budget : World → Nat) : Prop :=
  ∀ w, dom w → ∀ n t kt, Reach M (env w) n (init w) (KState.init w) t kt →
    n ≤ budget w ∧ M.step t ≠ .stuck

/-- `E' ≤ E`: every reply `E'` admits, `E` admits. -/
def Env.Le (E' E : Env) : Prop := ∀ k c r k', E' k c r k' → E k c r k'

theorem Exec.mono {M : Machine} {E E' : Env} (le : Env.Le E' E) {s k evs n}
    (h : Exec M E' s k evs n) : Exec M E s k evs n := by
  induction h with
  | exit hs => exact .exit hs
  | tau hs _ ih => exact .tau hs ih
  | call hs he _ ih => exact .call hs (le _ _ _ _ he) ih

theorem Reach.mono {M : Machine} {E E' : Env} (le : Env.Le E' E) {n s k t kt}
    (h : Reach M E' n s k t kt) : Reach M E n s k t kt := by
  induction h with
  | refl => exact .refl
  | tau hs _ ih => exact .tau hs ih
  | call hs he _ ih => exact .call hs (le _ _ _ _ he) ih

/-- Safety proved at a permissive environment holds at every smaller one. -/
theorem Satisfies.mono {M : Machine} {env env' : World → Env} {init : World → M.State}
    {dom : World → Prop} (le : ∀ w, Env.Le (env' w) (env w)) (h : Satisfies M env init dom) :
    Satisfies M env' init dom :=
  fun w hw evs n run => h w hw evs n (run.mono (le w))

theorem Live.mono {M : Machine} {env env' : World → Env} {init : World → M.State}
    {dom : World → Prop} {budget : World → Nat} (le : ∀ w, Env.Le (env' w) (env w))
    (h : Live M env init dom budget) : Live M env' init dom budget :=
  fun w hw n t kt r => h w hw n t kt (r.mono (le w))

/-- Restricting the domain is free. -/
theorem Satisfies.restrict {M : Machine} {env : World → Env} {init : World → M.State}
    {dom dom' : World → Prop} (sub : ∀ w, dom' w → dom w) (h : Satisfies M env init dom) :
    Satisfies M env init dom' :=
  fun w hw => h w (sub w hw)

/-! ## Refinement between programs

A program `B` (the binary) *trace-refines* a program `A` (a reference program) when every
exiting run of `B` is, call for call, an exiting run of `A` with the same status. Then
`Satisfies` transfers from `A` to `B`: the specification proof is done once, on the
reference program, and the binary proof is a simulation that never mentions
`sha256sum`. -/

def TraceRefines (B A : Machine) (env : World → Env) (initB : World → B.State)
    (initA : World → A.State) (dom : World → Prop) : Prop :=
  ∀ w, dom w → ∀ evs n, Exec B (env w) (initB w) (KState.init w) evs n →
    Exec A (env w) (initA w) (KState.init w) evs n

theorem Satisfies.of_traceRefines {B A : Machine} {env : World → Env} {initB : World → B.State}
    {initA : World → A.State} {dom : World → Prop} (r : TraceRefines B A env initB initA dom)
    (h : Satisfies A env initA dom) : Satisfies B env initB dom :=
  fun w hw evs n run => h w hw evs n (r w hw evs n run)

/-! ## Relational loaders

A real loader does not determine the initial state (stack address, auxiliary vector,
environment strings), so the statements about a binary quantify over every initial state
the loader relation admits. -/

def SatisfiesRel (M : Machine) (env : World → Env) (init : World → M.State → Prop)
    (dom : World → Prop) : Prop :=
  ∀ w, dom w → ∀ s, init w s → ∀ evs n, Exec M (env w) s (KState.init w) evs n →
    observe evs n = sha256sum w

def LiveRel (M : Machine) (env : World → Env) (init : World → M.State → Prop)
    (dom : World → Prop) (budget : World → Nat) : Prop :=
  ∀ w, dom w → ∀ s, init w s → ∀ n t kt, Reach M (env w) n s (KState.init w) t kt →
    n ≤ budget w ∧ M.step t ≠ .stuck

def TraceRefinesRel (B A : Machine) (env : World → Env) (initB : World → B.State → Prop)
    (initA : World → A.State) (dom : World → Prop) : Prop :=
  ∀ w, dom w → ∀ s, initB w s → ∀ evs n, Exec B (env w) s (KState.init w) evs n →
    Exec A (env w) (initA w) (KState.init w) evs n

theorem SatisfiesRel.of_traceRefines {B A : Machine} {env : World → Env}
    {initB : World → B.State → Prop} {initA : World → A.State} {dom : World → Prop}
    (r : TraceRefinesRel B A env initB initA dom) (h : Satisfies A env initA dom) :
    SatisfiesRel B env initB dom :=
  fun w hw s hs evs n run => h w hw evs n (r w hw s hs evs n run)

theorem SatisfiesRel.mono {M : Machine} {env env' : World → Env} {init : World → M.State → Prop}
    {dom : World → Prop} (le : ∀ w, Env.Le (env' w) (env w)) (h : SatisfiesRel M env init dom) :
    SatisfiesRel M env' init dom :=
  fun w hw s hs evs n run => h w hw s hs evs n (run.mono (le w))

theorem LiveRel.mono {M : Machine} {env env' : World → Env} {init : World → M.State → Prop}
    {dom : World → Prop} {budget : World → Nat} (le : ∀ w, Env.Le (env' w) (env w))
    (h : LiveRel M env init dom budget) : LiveRel M env' init dom budget :=
  fun w hw s hs n t kt r => h w hw s hs n t kt (r.mono (le w))

end Silmaril.Apps.Sha256sum.Sys
