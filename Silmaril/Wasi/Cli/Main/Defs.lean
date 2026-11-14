module

public import Silmaril.Wasi.Cli.Defs
public import Silmaril.Wasi.Comp.Defs
public import Silmaril.Cli.Front.Defs

/-!
# `Command.mainWith` on a WASI host

`Silmaril.Cli.Args` derives the front end of a program from its grammar `c : Command` and runs it
over any `Host m` (`Command.mainWith`): read the declared environment variables, `interpret`
the arguments, print help, version or a usage error (exit 0, 0, 2), else call the program's
body with the matches. This module gives that program a **WASI host**, so that a
`wasi:cli/command` component is built behind an args grammar, and states what such a
component does in the CLI behaviour model (`Silmaril.Wasi.Cli.Main.Thms`).

## Programs over WASI imports

* `WProg I α`: a finite program over the imports `I` (`Silmaril.Games.Prog`, the free monad of the
  world's signature), `callI f args` one import call.
* `CliM I = ExceptT UInt32 (WProg I)`: such a program that may stop early with an exit code
  (`throw k`).
* `PRun p t r`: **the runs of a program**, as event lists `t` (a request, the host's answer,
  …) ending with the result `r` (`none`: the run stops before returning). The plays of a
  component built from programs are read through it (`Silmaril.Wasi.Cli.Main.Thms.plays_iff`).

## The host

`Api I` collects what a WASI version provides for a CLI front end, as programs: `args`
(`get-arguments`), `env` (`get-environment`), `put ch bytes` (write bytes on stdout or
stderr, `false` when the host fails the write) and `finish k` (end the run with exit code
`k`). `Api.host A : Host (CliM I)` is the host of `Command.mainWith`: `getEnvs` calls
`get-environment` once, `putLine` writes the line and stops with exit code `1` when the write
fails. `Api.main A c run` is the body of `run`: `get-arguments`, then `c.mainWith A.host run`
on the arguments after the program name, then `finish` with the code (or the code of the
`throw`). `Api.after A vs K` is the same program with the front end's decision fixed to `K`:
`get-arguments`, `get-environment`, then `K`; on an invocation whose outcome is `.run m` the
component of `Api.main` behaves as that of `Api.after A c.envVars (run m)`
(`Silmaril.Wasi.Cli.Main.Thms`).

The WASI 0.2 and 0.3 instances are `Silmaril.Wasi.Cli.Host2.api2` and `Silmaril.Wasi.Cli.Host3.api3`.

## Exit codes

`exit01 S`: `S` with every nonzero exit code read as `1`. A WASI 0.2 command reports only
success or failure (`wasi:cli/exit.exit(result)`, or `run`'s `result`; `exit-with-code` is
`@unstable` in 0.2), so a 0.2 component meets `exit01 (c.spec S)` at best; WASI 0.3 has
`exit-with-code` and meets `c.spec S` itself.

A Silmaril addition; the guide is `docs/projects/wasm-binaryen-tooling.md`.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli

open Silmaril.Cli
open Silmaril.Wasm.Component (Val)

/-! ## Programs over WASI imports -/

/-- **A finite program over the imports `I`** returning an `α`. -/
abbrev WProg (I : Set FnName) (α : Type) : Type := Silmaril.Games.Prog (nsig I) α

/-- **A CLI program over the imports `I`**: it may stop early with an exit code (`throw k`). -/
abbrev CliM (I : Set FnName) : Type → Type := ExceptT UInt32 (WProg I)

/-- Call the import `f` with `args`; the answer (`none`: a trap). -/
def callI {I : Set FnName} (f : FnName) (hf : f ∈ I) (args : List Val) :
    WProg I (Option (List Val)) :=
  .call (⟨f, hf⟩, args) .pure

/-- **The runs of a program**: `PRun p t r`, the program `p` makes the import calls of `t`
(each request followed by the host's answer) and returns `r` (`some a`), or stops (`none`)
before returning, possibly with a request pending. -/
inductive PRun {I : Set FnName} {α : Type} : WProg I α → List WEv → Option α → Prop where
  /-- Nothing happened yet. -/
  | stop (p : WProg I α) : PRun p [] none
  /-- The program returned. -/
  | done (a : α) : PRun (.pure a) [] (some a)
  /-- The program called an import and waits for the answer. -/
  | ask (m : (nsig I).Op) (k : Option (List Val) → WProg I α) :
      PRun (.call m k) [.req m.1.1 m.2] none
  /-- The program called an import, received `n`, and went on. -/
  | step (m : (nsig I).Op) (k : Option (List Val) → WProg I α) (n : Option (List Val))
      {t : List WEv} {r : Option α} :
      PRun (k n) t r → PRun (.call m k) (.req m.1.1 m.2 :: .imp m.1.1 m.2 n :: t) r

/-- **Run a program against a scripted host** for at most `n` calls: the events and the
result (`none`: the host did not answer, or the calls ran out). For tests and examples
(`traceOf_run`: every such trace is a run). -/
def traceOf {I : Set FnName} {α : Type} (host : FnName → List Val → Option (List Val)) :
    WProg I α → Nat → List WEv × Option α
  | .pure a, _ => ([], some a)
  | .call m _, 0 => ([.req m.1.1 m.2], none)
  | .call m k, n + 1 =>
    let a := host m.1.1 m.2
    let r := traceOf host (k a) n
    (.req m.1.1 m.2 :: .imp m.1.1 m.2 a :: r.1, r.2)

/-- The exit code of a finished `CliM` program: its result, or the code it threw. -/
def exitCode : Except UInt32 UInt32 → UInt32
  | .ok k => k
  | .error k => k

/-! ## The host -/

/-- **What a WASI version provides for a CLI front end**, as programs over its imports. -/
structure Api (I : Set FnName) where
  /-- `get-arguments`: the program name and the arguments (`none`: an ill-formed answer). -/
  args : WProg I (Option (List String))
  /-- `get-environment`. -/
  env : WProg I (List (String × String))
  /-- Write bytes on a channel; `false` when the write failed. -/
  put : Channel → Bytes → WProg I Bool
  /-- End the run with an exit code. -/
  finish : UInt32 → BProg I

namespace Api

variable {I : Set FnName} (A : Api I)

/-- The lookup of the declared variables `vs` in an environment. -/
def look (vs : List String) (e : List (String × String)) : String → Option String :=
  fun v => if v ∈ vs then e.lookup v else none

/-- Read the declared variables `vs` (one `get-environment` call). -/
def getEnvs (vs : List String) : CliM I (String → Option String) :=
  ExceptT.mk (A.env.bind fun e => .pure (.ok (look vs e)))

/-- Print a line; stop with exit code `1` when the write fails. -/
def putLine (ch : Channel) (s : String) : CliM I Unit :=
  ExceptT.mk ((A.put ch (utf8 (s ++ "\n"))).bind fun ok =>
    .pure (if ok then .ok () else .error 1))

/-- **The host of `Command.mainWith` on a WASI version.** -/
def host : Silmaril.Cli.Host (CliM I) := ⟨A.getEnvs, A.putLine⟩

/-- Run a `CliM` program to its end: `finish` with its code. -/
def close (K : CliM I UInt32) : BProg I := (ExceptT.run K).bind fun r => A.finish (exitCode r)

/-- **The `run` export of a component behind the grammar `c`**: `get-arguments`, then
`c.mainWith A.host run` on the arguments after the program name. -/
def main (c : Command) (run : Matches → CliM I UInt32) : BProg I :=
  A.args.bind fun
    | some argv => A.close (c.mainWith A.host run argv.tail)
    | none => A.finish 1

/-- **The same program with the front end's decision fixed**: `get-arguments`,
`get-environment` (the variables `vs`), then `K`. -/
def after (vs : List String) (K : CliM I UInt32) : BProg I :=
  A.args.bind fun _ => A.close (A.getEnvs vs >>= fun _ => K)

/-- The component of `A.main c run`, answering every export call. -/
def body {X : Set FnName} (c : Command) (run : Matches → CliM I UInt32) :
    Body I X := fun _ => A.main c run

/-- The component of `A.after vs K`. -/
def bodyAfter {X : Set FnName} (vs : List String) (K : CliM I UInt32) : Body I X :=
  fun _ => A.after vs K

end Api

/-! ## Specifications of what the front end prints -/

/-- **`S` with every nonzero exit code read as `1`** (what a WASI 0.2 command can report). -/
def exit01 (S : Spec) : Spec := fun i o =>
  ∃ o', S i o' ∧ o = { o' with exit := if o'.exit = 0 then 0 else 1 }

/-- Print the line `s` on `ch` and exit with `k`, nothing else (the help, version and usage
error outcomes of `Command.spec`). -/
def lineSpec (ch : Channel) (s : String) (k : ExitCode) : Spec := fun i o =>
  o = { Beh.lineObs i (some (ch, s)) with exit := k }

/-! ## What a WASI version must provide -/

namespace Api

variable {I : Set FnName} {St : Type} (A : Api I) (T : Input → Silmaril.Wasm.Resource.Protocol St WEv)

/-- **The theory pins `get-arguments`**: a finished `A.args` whose answers the theory accepts
returns the program name and the arguments. -/
def ArgsOk : Prop :=
  ∀ i t a, PRun A.args t (some a) → (T i).Accepts (hostView t) → a = some i.argv

/-- **The theory pins `get-environment`**, after any accepted prefix. -/
def EnvOk : Prop :=
  ∀ i pre t e, PRun A.env t (some e) → (T i).Accepts (hostView (pre ++ t)) → e = i.env

/-- **Printing a line is read as printing it** (allowing failure as `F` says): the component
that runs `get-arguments`, `get-environment`, prints the line `s` on `ch` and exits with `k`
is seen through `V` as a run of `F (lineSpec ch s k)`. -/
def EmitOk (V : View) (F : Spec → Spec) (X : Set FnName) : Prop :=
  ∀ i vs ch s (k : UInt32), (ag (I := I) (X := X) (fun t => (T i).Accepts (hostView t))
    (V.Guar (F (lineSpec ch s k.toUInt8)) i)).holds
      (ofBody (A.bodyAfter vs (A.putLine ch s >>= fun _ => pure k)))

end Api

end Silmaril.Wasi.Cli

end
