module

public import Silmaril.Project.WasmP3Rust.TasksP3.Defs
public import Silmaril.Project.WasmP3Rust.DenX.Defs

/-!
# The `cat` and `echo` statements in the world with data-carrying events

`Silmaril.Project.WasmP3Rust.TasksP3` states `Task.catCopiesP3` in `p3World`, where a blocked
`stream.read` completed through `waitable-set.wait` delivers no data, and where `stdinBytes`
counts only reads answered `COMPLETED` directly. A faithful model of `cat` (which waits for
stdin) cannot meet `catG1` there (`Silmaril.Project.WasmP3Rust.CatX.Thms`). This module restates
the targets over `DenX.p3xWorld` and its encoding (events carry the data their copy delivered).

* `stdinBytesX`: the bytes delivered on stdin's readable ends: every `stream.read` answer with a
  count `k` (`COMPLETED`, `DROPPED` or `CANCELLED`: a copy may deliver items and then report
  that the writer dropped the stream), and every `STREAM_READ` event with its data;
* `waitTh3x`: `waitTh3`'s discipline for writes (a `STREAM_WRITE` event, in the 3-element form,
  only for a blocked write, once), and the same for reads: a `STREAM_READ` event on `r` is
  delivered only while a read on `r` is blocked, once, and carries its data (the 4-element
  form);
* `stdoutTh3x = stdoutTh3 × waitTh3x`; `catGX` is `catG1` with `stdinBytesX`;
* `argsTh args`: `get-arguments` answers the UTF-8 bytes of `args`; `echoTh args =
  stdoutTh3x × argsTh args`.

| statement | status |
|---|---|
| `Task.catCopiesX den` | proved for `DenX.den` with the core model `stdioK catPlan` (`StdioK.Thms.cat_copies_model`); open for the real core code (`Task.catCore`) |
| `Task.catDebugCopiesX den` | the same with `stdioK catDebugPlan` (`catDebug_copies_model`) |
| `Task.echoPrintsX den args` (= `Task.echoPrintsP3 p3xWorld den (echoTh args) args`) | proved for `DenX.den` with `stdioK echoPlan`, every `args` (`echo_prints_model`) |
| `Task.cat_release_debugX den` | open |

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust

open Silmaril.Wasi Silmaril.Wasi.Versions.P3
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Project.Shapes.Component (WasiSat)
open Silmaril.Project.WasmP3Rust.DenX (p3xWorld getArgs3 argsOf evStreamRead)
open Silmaril.Wasm.Component.BinaryP3 (Ast)

/-! ## Stdin, with data-carrying events -/

/-- The count of a packed copy result (any result). -/
def copyCount (n : Nat) : Option Nat :=
  match copyOf n with
  | some (some (_, k)) => some k
  | _ => none

/-- One event of the stdin scan: the readable ends of `stdin.read-via-stream` so far, and the
bytes the event delivered on them: a `stream.read` answer with a count, or a `STREAM_READ`
event with its data. -/
def inStep (rs : List Nat) : WEv → List Nat × List (BitVec 8)
  | .imp f a r =>
    if f = stdinRead3 then
      match r with
      | some [.record [rv, _]] =>
        match natOf rv with
        | some r' => (r' :: rs, [])
        | none => (rs, [])
      | _ => (rs, [])
    else if f = cStreamRead then
      match a, r with
      | [rv, _], some [pv, items] =>
        match natOf rv, natOf pv >>= copyCount with
        | some r', some k => if r' ∈ rs then (rs, (bytesOf items).take k) else (rs, [])
        | _, _ => (rs, [])
      | _, _ => (rs, [])
    else if f = cWait then
      match r with
      | some [cv, iv, pv, items] =>
        match natOf cv, natOf iv, natOf pv >>= copyCount with
        | some c, some i, some k =>
          if c = evStreamRead ∧ i ∈ rs then (rs, (bytesOf items).take k) else (rs, [])
        | _, _, _ => (rs, [])
      | _ => (rs, [])
    else (rs, [])
  | _ => (rs, [])

/-- The bytes delivered on stdin along `t`, from the readable ends `rs`. -/
def stdinScanX : List Nat → List WEv → List (BitVec 8)
  | _, [] => []
  | rs, e :: t => (inStep rs e).2 ++ stdinScanX (inStep rs e).1 t

/-- **The bytes stdin delivered along `t`.** -/
def stdinBytesX (t : List WEv) : List (BitVec 8) := stdinScanX [] t

/-! ## The wait discipline for reads and writes -/

/-- One step of the wait discipline: the writable ends with a blocked `stream.write` and the
readable ends with a blocked `stream.read`. -/
def waitStepX (q : List Nat × List Nat) : WEv → Option (List Nat × List Nat)
  | .imp f a r =>
    if f = cStreamWrite then
      match a, r with
      | [wv, _], some [pv] =>
        if natOf pv = some Silmaril.Wasm.Component.Async.blocked then
          match natOf wv with
          | some w => some (w :: q.1, q.2)
          | none => some q
        else some q
      | _, _ => some q
    else if f = cStreamRead then
      match a, r with
      | [rv, _], some [pv, _] =>
        if natOf pv = some Silmaril.Wasm.Component.Async.blocked then
          match natOf rv with
          | some r' => some (q.1, r' :: q.2)
          | none => some q
        else some q
      | _, _ => some q
    else if f = cWait then
      match r with
      | some (cv :: iv :: _ :: rest) =>
        if natOf cv = some streamWriteCode then
          match natOf iv, rest with
          | some w, [] => if w ∈ q.1 then some (q.1.erase w, q.2) else none
          | _, _ => none
        else if natOf cv = some evStreamRead then
          match natOf iv, rest with
          | some r', [_] => if r' ∈ q.2 then some (q.1, q.2.erase r') else none
          | _, _ => none
        else some q
      | _ => some q
    else some q
  | _ => some q

/-- **The wait discipline of WASI 0.3 hosts, for writes and reads.** -/
def waitTh3x : Protocol (List Nat × List Nat) WEv := ⟨([], []), waitStepX⟩

/-- **The loose stdout theory with the wait discipline for reads and writes.** -/
def stdoutTh3x : Protocol (OutSt × (List Nat × List Nat)) WEv := stdoutTh3.prod waitTh3x

/-- **`cat`'s guarantee, for one run**, with stdin observed through `stdinBytesX`. -/
def catGX : Protocol (List WEv) WEv :=
  onceG fun t =>
    (stdoutBytes t).isPrefixOf (stdinBytesX t) && (!runOk t || stdoutBytes t == stdinBytesX t)

/-! ## Arguments -/

/-- Each `get-arguments` answer is a list of strings whose UTF-8 bytes are those of `args`. -/
def argsOk (args : List String) : WEv → Bool
  | .imp f _ r => !decide (f = getArgs3) || decide (argsOf r = some (args.map utf8))
  | _ => true

/-- **The arguments theory**: `get-arguments` answers `args`. -/
def argsTh (args : List String) : Protocol Unit WEv := pointwise (argsOk args)

/-- The theory of `echo`: stdout with the wait discipline, and the arguments. -/
def echoTh (args : List String) : Protocol ((OutSt × (List Nat × List Nat)) × Unit) WEv :=
  stdoutTh3x.prod (argsTh args)

/-! ## The targets -/

/-- **Over every host of `T`, the component meets `G`** under `den` in `p3xWorld`. -/
def Task.satX (b : List UInt8) (den : Ast → p3xWorld.Model) {S S' : Type} (T : Protocol S WEv)
    (G : Protocol S' WEv) : Prop :=
  ∃ c : Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf b) = .ok c ∧ WasiSat (den c) T G

/-- **`cat` copies stdin to stdout** modulo rechunking, with data-carrying events. -/
def Task.catCopiesX (den : Ast → p3xWorld.Model) : Prop :=
  Task.satX Cat.File.bytes den stdoutTh3x catGX

/-- **The debug build of `cat` copies stdin to stdout.** -/
def Task.catDebugCopiesX (den : Ast → p3xWorld.Model) : Prop :=
  Task.satX CatDebug.File.bytes den stdoutTh3x catGX

/-- **`echo` prints its arguments**: `Task.echoPrintsP3` in `p3xWorld` with `echoTh args`. -/
def Task.echoPrintsX (den : Ast → p3xWorld.Model) (args : List String) : Prop :=
  Task.echoPrintsP3 p3xWorld den (echoTh args) args

/-- **The release and debug builds of `cat` behave the same** under `den` in `p3xWorld`. -/
def Task.cat_release_debugX (den : Ast → p3xWorld.Model) : Prop :=
  ∃ a b : Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf Cat.File.bytes) = .ok a ∧
    Silmaril.Wasm.Component.BinaryP3.parse (arrOf CatDebug.File.bytes) = .ok b ∧ den a = den b

end Silmaril.Project.WasmP3Rust

end
