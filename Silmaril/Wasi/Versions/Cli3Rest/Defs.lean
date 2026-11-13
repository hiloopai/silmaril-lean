module

public import Silmaril.Wasi.Versions.Net.Defs
public import Silmaril.Wasi.Versions.P3.Defs

@[expose] public section

/-!
# The last 0.3 `wasi:cli` and `wasi:clocks` imports: stderr, terminals, resolutions

`Silmaril.Wasi.Versions.Cli3More` covers the 0.3 environment, exit and the clock readings; the P3
slice covers stdin and stdout. This module covers the remaining imports of
`vendor/wasi/0.3.2/cli/{stdio,terminal}.wit` and `vendor/wasi/0.3.2/clocks/
{monotonic-clock,system-clock}.wit`:

* **`stderr.write-via-stream(data: stream<u8>) -> future<result<_, error-code>>`**: "If the
  stream's writable end is dropped this function will either return success once the entire
  contents of the stream have been written or an error-code". The theory `outTh W E` is written
  for any such function `W` (`stderrWrite3` here; `P3.stdoutWrite3` has the same text): a
  `future.read` of the future `W` answered that completes with `ok` needs the writable end of
  the stream passed to `W` to have been dropped before. It is the future clause of
  `P3.stdoutTh3`, gated; unlike `stdoutTh3` it does not constrain `stream.write`, and it
  constrains only the futures of `W`.
* **`get-terminal-stdin`, `get-terminal-stdout`, `get-terminal-stderr`** (`-> option<…>`): "If
  stdin is connected to a terminal, return a `terminal-input` handle". Whether a stream is a
  terminal is a link-time fact (the interfaces are "link-time authorities"), so the theory is
  relative to a terminal environment `E : Term3`: the answer is `some` exactly when `E` says
  the stream is a terminal.
* **`monotonic-clock.get-resolution`, `system-clock.get-resolution`** (`-> duration`, a
  `u64`): the theory is relative to the resolutions `E.monoRes`, `E.sysRes` and asks the
  answer to be that value. The WIT text does not say that the resolution is constant; this is
  the reading in which the resolution is a property of the implementation (a partial claim).

Everything else (errors, traps, other functions, the futures of other functions) is not
constrained.

The host `outImpl W E` answers fresh stream and future handles, completes every
`stream.write` in full, answers a `future.read` of a future of `W` with `COMPLETED` and `ok`
only once the writable end is dropped (`BLOCKED` before), and answers the terminals and
resolutions from `E`. Unlike `P3.stdout3Impl`, whose futures report `ok` at once and which is
therefore rejected by `stdoutTh3` (`P3.stdout_early_ok_rejected`), it waits for the drop.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Cli3Rest

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (CopyResult packCopy)
open Silmaril.Wasi.Versions.Net (gated)
open Silmaril.Wasi.Versions.P3 (natV natOf cStreamNew cStreamWrite cStreamDropW cFutureRead)

/-! ## Names -/

def stderrWrite3 : FnName := ⟨"wasi:cli/stderr@0.3.2", "write-via-stream"⟩
def termIn3 : FnName := ⟨"wasi:cli/terminal-stdin@0.3.2", "get-terminal-stdin"⟩
def termOut3 : FnName := ⟨"wasi:cli/terminal-stdout@0.3.2", "get-terminal-stdout"⟩
def termErr3 : FnName := ⟨"wasi:cli/terminal-stderr@0.3.2", "get-terminal-stderr"⟩
def monoRes3 : FnName := ⟨"wasi:clocks/monotonic-clock@0.3.2", "get-resolution"⟩
def sysRes3 : FnName := ⟨"wasi:clocks/system-clock@0.3.2", "get-resolution"⟩

/-! ## The environment -/

/-- The link-time facts: which standard streams are terminals, and the clock resolutions. -/
structure Term3 where
  stdin : Bool
  stdout : Bool
  stderr : Bool
  monoRes : BitVec 64
  sysRes : BitVec 64

/-! ## The state -/

/-- The stream pairs created (readable, writable), the futures of `W` with the writable end of
their stream, and the dropped writable ends. -/
structure OutSt where
  pairs : List (Nat × Nat) := []
  futs : List (Nat × Nat) := []
  dropped : List Nat := []

/-- The value of `k` in an association list of numbers. -/
def nlook (k : Nat) (l : List (Nat × Nat)) : Option Nat := (l.find? (·.1 == k)).map (·.2)

/-- The future `fv` is done: it is not a future of `W`, or its writable end is dropped. -/
def futDone (q : OutSt) (fv : Val) : Bool :=
  match (natOf fv).bind (nlook · q.futs) with
  | some w => q.dropped.contains w
  | none => true

/-- An answer `ok(handle)` of an `option<resource>`, or `none`. -/
def optSome : Option (List Val) → Option Bool
  | some [.variant 0 none] => some false
  | some [.variant 1 (some _)] => some true
  | _ => none

/-- A `u64` answer equal to `x`, or an ill-shaped one. -/
def u64Is (x : BitVec 64) : Option (List Val) → Bool
  | some [.u64 y] => y == x
  | _ => true

/-! ## The theory -/

/-- The next state. -/
def outNext (W : FnName) (q : OutSt) : WEv → OutSt
  | .imp f a r =>
    if f = cStreamNew then
      (match r with
       | some [rv, wv] => (match natOf rv, natOf wv with
         | some r', some w' => { q with pairs := (r', w') :: q.pairs }
         | _, _ => q)
       | _ => q)
    else if f = W then
      (match a, r with
       | [rv], some [fv] => (match (natOf rv).bind (nlook · q.pairs), natOf fv with
         | some w', some f' => { q with futs := (f', w') :: q.futs }
         | _, _ => q)
       | _, _ => q)
    else if f = cStreamDropW then
      (match a with
       | [wv] => { q with dropped := (natOf wv).toList ++ q.dropped }
       | _ => q)
    else q
  | _ => q

/-- The check of every answer. -/
def outOk (E : Term3) (q : OutSt) : WEv → Bool
  | .imp f a r =>
    if f = cFutureRead then
      (match a, r with
       | [fv], some [_, .variant 0 none] => futDone q fv
       | _, _ => true)
    else if f = termIn3 then (optSome r).all (· == E.stdin)
    else if f = termOut3 then (optSome r).all (· == E.stdout)
    else if f = termErr3 then (optSome r).all (· == E.stderr)
    else if f = monoRes3 then u64Is E.monoRes r
    else if f = sysRes3 then u64Is E.sysRes r
    else true
  | _ => true

/-- **The loose theory** of the output function `W` (its futures report success only after
the writable end is dropped), the terminals and the resolutions of `E`. -/
def outTh (W : FnName) (E : Term3) : Protocol OutSt WEv := gated {} (outNext W) (outOk E)

/-- **The 0.3 stderr theory.** -/
abbrev stderrTh3 (E : Term3) : Protocol OutSt WEv := outTh stderrWrite3 E

/-! ## The host -/

/-- The state after the answers `p`. -/
def outState (W : FnName) (p : List WEv) : OutSt := p.foldl (outNext W) {}

/-- An `option<resource>` answer: a fresh handle `h` or `none`. -/
def termA (b : Bool) (h : Nat) : Option (List Val) :=
  if b then some [.variant 1 (some (natV h))] else some [.variant 0 none]

/-- The answer of a `future.read` of `fv`: `COMPLETED`, `ok` once done, `BLOCKED` before. -/
def futA (q : OutSt) (fv : Val) : Option (List Val) :=
  if futDone q fv then some [natV CopyResult.completed.toNat, .variant 0 none]
  else some [natV Silmaril.Wasm.Component.Async.blocked, .record []]

/-- **The concrete host** of the output function `W` and the environment `E`. -/
def outImpl (W : FnName) (E : Term3) : Impl := fun p f a =>
  let q := outState W p
  if f = cStreamNew then some [natV (2 * p.length + 1), natV (2 * p.length + 2)]
  else if f = W then some [natV (2 * p.length + 1)]
  else if f = cStreamWrite then
    some [natV (packCopy .completed (bytesOf (a.getD 1 (.record []))).length)]
  else if f = cStreamDropW then some []
  else if f = cFutureRead then
    (match a with
     | [fv] => futA q fv
     | _ => none)
  else if f = termIn3 then termA E.stdin p.length
  else if f = termOut3 then termA E.stdout p.length
  else if f = termErr3 then termA E.stderr p.length
  else if f = monoRes3 then some [.u64 E.monoRes]
  else if f = sysRes3 then some [.u64 E.sysRes]
  else none

/-- **The 0.3 stderr host.** -/
abbrev stderrImpl3 (E : Term3) : Impl := outImpl stderrWrite3 E

end Silmaril.Wasi.Versions.Cli3Rest
