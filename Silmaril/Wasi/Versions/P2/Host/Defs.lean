module

public import Silmaril.Wasi.Versions.P2.World.Defs

@[expose] public section

/-!
# WASI 0.2: loose and concrete hosts

* `p2Loose r = loose (p2Th r)`: the **loose host** of the WASI 0.2 theory in the reading `r`,
  the largest host satisfying it (`Silmaril.Wasi.Host`).
* `p2Impl`: a **concrete host** of the command slice. Its `wasi:io` part (`ioImpl`) answers from
  the theory state of the answers so far (`ioState p`):
  * output streams accept `4096` bytes per `check-write`, writes within the permit succeed and
    writes beyond it trap, flushes complete at once, `splice` moves nothing;
  * every input stream is at end of file (`error(closed)`), as for an empty stdin;
  * pollables are always ready; `poll` lists every index (and traps on an empty list);
  * a closed stream answers `error(closed)`.
  Its other answers: `now` is #856's tick clock `clockImpl`, #856's filesystem functions are
  #856's `fsImpl`, handles are fresh (the number of answers so far, as in #856's `stdoutImpl`),
  the environment and arguments are empty, there is no terminal, `exit` traps (the run ends).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2

open Silmaril.Games
open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- **The loose host of the WASI 0.2 theory.** -/
def p2Loose {Y : Sig.{0}} {I : Set FnName} (r : Reading) : Host Y I := loose (p2Th r)

/-- The `wasi:io` theory state after the answers `p`. -/
def ioState (p : List WEv) : IoSt := p.foldl ioNext ioInit

/-- A `u32` handle. -/
def hnd (n : Nat) : Val := .u32 (BitVec.ofNat 32 n)

/-- `error(closed)` on a closed stream, otherwise `v`. -/
def orClosed (s : IoSt) (h : BitVec 32) (v : Option (List Val)) : Option (List Val) :=
  if s.closed h then some [errClosed] else v

/-- The answer of `poll(in)`: every index; a trap on an empty list. -/
def pollImpl : List Val → Option (List Val)
  | [.record ps] => if ps.isEmpty then none else some [.record ((List.range ps.length).map hnd)]
  | _ => some [.record []]

/-- **The `wasi:io` part of the concrete host**, in the state `s` after `n` answers. -/
def ioImpl (s : IoSt) (n : Nat) (o : IoOp) (a : List Val) : Option (List Val) :=
  let h := selfOf a
  match o with
  | .checkWrite => orClosed s h (some [okV (some (.u64 4096))])
  | .write | .writeZeroes =>
    if writeLen o a ≤ s.permit h then orClosed s h (some [okV none]) else none
  | .bwf | .bwzf | .flush | .bflush => orClosed s h (some [okV none])
  | .splice | .bsplice => orClosed s h (some [okV (some (.u64 0))])
  | .read | .bread | .skip | .bskip => some [errClosed]
  | .oSubscribe | .iSubscribe => some [hnd n]
  | .ready => some [.bool true]
  | .block | .pDrop | .other => some []
  | .poll => pollImpl a

/-- The other functions of the concrete host (in the order of `cliOk`, then #856's clock and
filesystem hosts). -/
def restImpl (p : List WEv) (f : FnName) (a : List Val) : Option (List Val) :=
  if f = cliExit then none
  else if f = getEnv then some [.record []]
  else if f = getArgs then some [.record []]
  else if f = initialCwd then some [.variant 0 none]
  else if f = getStdin ∨ f = getStdout ∨ f = getStderr ∨ f = monoSubInstant ∨
      f = monoSubDuration then some [hnd p.length]
  else if f = getTermStdin ∨ f = getTermStdout ∨ f = getTermStderr then some [.variant 0 none]
  else if f = monoRes then some [.u64 1]
  else if f = wallNow ∨ f = wallRes then some [.record [.u64 0, .u32 0]]
  else if f = fdReadStream ∨ f = fdWriteStream ∨ f = fdAppendStream then
    some [okV (some (hnd p.length))]
  else if f = fdGetType then some [okV (some (.variant 6 none))]
  else if f = streamDrop then some []
  else if f = clockNow then clockImpl p f a
  else fsImpl p f a

/-- **The concrete WASI 0.2 host.** -/
def p2Impl : Impl := fun p f a =>
  if ioOp f = .other then restImpl p f a else ioImpl (ioState p) p.length (ioOp f) a

end Silmaril.Wasi.Versions.P2
