module

public import Silmaril.Wasi.Versions.FsMore.Defs

@[expose] public section

/-!
# WASI 0.3 `wasi:cli` and `wasi:clocks` outside the P3 slice: a loose theory and a host

The P3 slice (`Silmaril.Wasi.Versions.P3`) covers `stdout`/`stdin` streams and the monotonic
`now`/`wait-for`. This module covers the other 0.3 functions that have something to check,
from `specs/wasi/0.3.2/cli/{environment,exit}.wit` and
`specs/wasi/0.3.2/clocks/{monotonic-clock,system-clock}.wit`:

* **Environment** (`get-environment`, `get-arguments`, `get-initial-cwd`): "this import function
  should return the same values each time it is called". The theory is relative to an
  environment `E : Env3` (variables, arguments, initial working directory) and asks every answer
  to be `E`'s. That is the constant-environment reading; a theory that only asks the answers to
  agree with each other is weaker (every `E`-theory refines it).
* **Exit** (`exit: func(status: result)`, `exit-with-code: func(status-code: u8)`): never
  return; an answer is rejected, a trap (the run ends) is accepted.
* **The monotonic clock with `wait-until`**: `now` never decreases, and after `wait-until(w)`
  (answered) or `wait-for(d)` (answered, after a `now` of `l`) the next `now` is at least `w`,
  respectively `l + d` saturated at `2^64 - 1` (as `P3OverP2.clockTh3s`). The bound is kept as a
  `u64`, so no overflow invariant is needed.
* **The system clock** (`now: func() -> instant`, `instant { seconds: s64, nanoseconds: u32 }`):
  `nanoseconds < 10^9`, as for the 0.2 `datetime`.

Ill-shaped answers of the clock are rejected only for `now`; `get-resolution` and the terminal
functions are not constrained beyond the WIT typing.

The host `cli3Impl E` answers `E`, traps on `exit`, answers the monotonic `now` with the larger
of the last reading and the bound (the clock jumps forward when waited on), `{0, 0}` for the
system clock, and returns from the waits.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Cli3More

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net (gated)
open Silmaril.Wasi.Versions.FsMore (charsV strC)

/-! ## Names -/

def getEnv3 : FnName := ⟨"wasi:cli/environment@0.3.2", "get-environment"⟩
def getArgs3 : FnName := ⟨"wasi:cli/environment@0.3.2", "get-arguments"⟩
def getCwd3 : FnName := ⟨"wasi:cli/environment@0.3.2", "get-initial-cwd"⟩
def exit3 : FnName := ⟨"wasi:cli/exit@0.3.2", "exit"⟩
def exitCode3 : FnName := ⟨"wasi:cli/exit@0.3.2", "exit-with-code"⟩
def monoNow3 : FnName := ⟨"wasi:clocks/monotonic-clock@0.3.2", "now"⟩
def waitUntil3 : FnName := ⟨"wasi:clocks/monotonic-clock@0.3.2", "wait-until"⟩
def waitFor3' : FnName := ⟨"wasi:clocks/monotonic-clock@0.3.2", "wait-for"⟩
def sysNow3 : FnName := ⟨"wasi:clocks/system-clock@0.3.2", "now"⟩

/-! ## The environment -/

/-- An environment: variables, arguments, initial working directory. -/
structure Env3 where
  vars : List (List Char × List Char)
  args : List (List Char)
  cwd : Option (List Char)

/-- A `list<string>`, decoded. -/
def strsOf : Val → Option (List (List Char))
  | .record vs => vs.mapM charsV
  | _ => none

/-- A `tuple<string, string>`, decoded. -/
def pairOf : Val → Option (List Char × List Char)
  | .record [k, v] => do pure (← charsV k, ← charsV v)
  | _ => none

/-- A `list<tuple<string, string>>`, decoded. -/
def pairsOf : Val → Option (List (List Char × List Char))
  | .record vs => vs.mapM pairOf
  | _ => none

/-- An `option<string>`, decoded. -/
def optStrOf : Val → Option (Option (List Char))
  | .variant 0 none => some none
  | .variant 1 (some s) => (charsV s).map some
  | _ => none

/-- The single value of an answer. -/
def one : Option (List Val) → Option Val
  | some [v] => some v
  | _ => none

/-! ## The state and the checks -/

/-- The clock state: the last monotonic reading, and the bound owed to the next one. -/
structure Clk3 where
  last : BitVec 64 := 0
  lb : BitVec 64 := 0

/-- The larger of two `u64`s. -/
def bmax (a b : BitVec 64) : BitVec 64 := if a ≤ b then b else a

/-- `l + d`, saturated at `2^64 - 1`. -/
def satAdd (l d : BitVec 64) : BitVec 64 :=
  if l.toNat + d.toNat < 2 ^ 64 then l + d else BitVec.allOnes 64

/-- `nanoseconds < 10^9` of an `instant`. -/
def instantOk : Option (List Val) → Bool
  | some [.record [.s64 _, .u32 ns]] => ns.toNat < 1000000000
  | _ => false

/-- The check of every answer. -/
def cli3Ok (E : Env3) (q : Clk3) : WEv → Bool
  | .imp f _ r =>
    if f = getEnv3 then (one r).bind pairsOf == some E.vars
    else if f = getArgs3 then (one r).bind strsOf == some E.args
    else if f = getCwd3 then (one r).bind optStrOf == some E.cwd
    else if f = exit3 ∨ f = exitCode3 then r.isNone
    else if f = monoNow3 then
      (match r with
       | some [.u64 x] => decide (q.last ≤ x) && decide (q.lb ≤ x)
       | _ => false)
    else if f = sysNow3 then instantOk r
    else true
  | _ => true

/-- The next state. -/
def cli3Next (q : Clk3) : WEv → Clk3
  | .imp f a r =>
    if f = monoNow3 then
      (match r with
       | some [.u64 x] => { last := x, lb := 0 }
       | _ => q)
    else if f = waitUntil3 then
      (match a, r with
       | [.u64 w], some _ => { q with lb := bmax q.lb w }
       | _, _ => q)
    else if f = waitFor3' then
      (match a, r with
       | [.u64 d], some _ => { q with lb := bmax q.lb (satAdd q.last d) }
       | _, _ => q)
    else q
  | _ => q

/-- **The loose theory of the 0.3 environment, exit and clocks** over the environment `E`. -/
def cli3Th (E : Env3) : Protocol Clk3 WEv := gated {} cli3Next (cli3Ok E)

/-! ## The host -/

/-- The clock state after the answers `p`. -/
def clk3State (p : List WEv) : Clk3 := p.foldl cli3Next {}

/-- The encoding of a `list<tuple<string, string>>`. -/
def pairsV (l : List (List Char × List Char)) : Val :=
  .record (l.map fun x => .record [strC x.1, strC x.2])

/-- The encoding of an `option<string>`. -/
def optStrV : Option (List Char) → Val
  | none => .variant 0 none
  | some s => .variant 1 (some (strC s))

/-- **The concrete host of the environment `E`.** -/
def cli3Impl (E : Env3) : Impl := fun p f _ =>
  let q := clk3State p
  if f = getEnv3 then some [pairsV E.vars]
  else if f = getArgs3 then some [.record (E.args.map strC)]
  else if f = getCwd3 then some [optStrV E.cwd]
  else if f = exit3 ∨ f = exitCode3 then none
  else if f = monoNow3 then some [.u64 (bmax q.last q.lb)]
  else if f = sysNow3 then some [.record [.s64 0, .u32 0]]
  else if f = waitUntil3 ∨ f = waitFor3' then some []
  else none

end Silmaril.Wasi.Versions.Cli3More
