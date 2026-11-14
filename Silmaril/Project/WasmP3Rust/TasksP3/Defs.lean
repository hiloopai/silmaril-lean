module

public import Silmaril.Project.WasmP3Rust.Tasks.Defs
public import Silmaril.Wasm.Component.BinaryP3.Defs
public import Silmaril.Wasm.Component.BinaryP3.Project.Defs
public import Silmaril.Wasm.Component.BinaryP3.World.Defs
public import Silmaril.Project.WasmP3Rust.World.Defs

/-!
# The WASI 0.3 Rust examples: the statements, restated on the grammar with async built-ins

`Silmaril.Project.WasmP3Rust.Tasks` froze the targets . Two of their choices make the
behavioural ones (`Task.hello_prints`, `Task.cat_copies`, …) unprovable for any useful
semantics; this module states corrected versions, and
`Silmaril.Project.WasmP3Rust.TasksP3.Thms` proves what is wrong with the old ones.

1. **The old parser.** The old statements start with `Binary.parse b = .ok c`: the parser at
   `8505ba7`, which rejects every example (their `canon` sections hold async built-ins). The
   new statements use `BinaryP3.parse` (`d095e2f`), over `BinaryP3.Ast`.
2. **The observation.** `WasiEveryHost σ T G` checks `G` on `xtrace p`, the *export* events of
   the play of `σ` linked with a host (the host's moves are hidden). `helloG` reads stdout from
   the import answers (`osTrace3`), so on export events it sees no output, and it then holds
   exactly when `run` never returns `ok` (`TasksP3.Thms.helloG_xtrace`). The new statements use
   `WasiSat σ T G` (`silmaril.shapes.component.wasi_sat`): every play of `σ` with uninterpreted
   imports whose answers satisfy `T` satisfies `G` on **all** its events. This is the same
   quantification over hosts (a host is a strategy whose answers satisfy `T`), with the
   import events visible.
3. **The theory.** The loose stdout theory `stdoutTh3` does not constrain
   `waitable-set.wait`: a host may report the completion of a blocked `stream.write` twice, or
   with no write pending, and `osTrace3` then counts the bytes again. No component that waits
   after a blocked write meets `helloG` over every such host. `waitTh3` adds the discipline of
   `definitions.py` (`Waitable.get_pending_event` clears the event, L760–766 at `d095e2f`): a
   `STREAM_WRITE` event on `w` is delivered only while a write on `w` is blocked, and once.
   `stdoutTh3w` is both.
4. **One `run`.** A `wasi:cli/command` host calls `run` once. `den` starts every export call
   afresh, so a second call prints again; the guarantees are stated for traces with at most one
   call of `run` (`onceG`).


## Summary

| statement | shape | status |
|---|---|---|
| `Parses3 b` (= `Task.parsesP3 b`) | the file is a component of the grammar with async built-ins | proved for the four files (`TasksP3.Thms`) |
| `Valid3 b` | it is well scoped (`BinaryP3.wellScopedC3`: `wellScopedC` lifted, plus the type operands of `stream.*`, `future.*`, `task.return`) | proved for the four files |
| `HasWorld3 b W` | it targets `W` (`BinaryP3.World.targets`: closed types, width subtyping of instances) | proved for the four files with `W = Cli.command` |
| `Task.helloPrintsP3 den` | `WasiSat (den c) stdoutTh3w helloG1` | proved for `den` with the hand-written core model `helloK` (`HelloDen`); open for the real core code (`Task.helloCore`) |
| `Task.catCopiesP3`, `Task.catDebugCopiesP3` | the same with `catG1` | open |
| `Task.echoPrintsP3 W den T args` | the same with `echoG1 args`, in a world with `wasi:cli/environment` | open |
| `Task.cat_release_debug3 den` | the release and debug builds of `cat` have the same denotation | open |

**Why `targets`, not `silmaril.shapes.component.has_world`.** `HasWorld c W` asks that the
projection `projectX c` *be* `W` up to names. For these components `projectX` (lifted,
`BinaryP3.projectX3`) is `none`: the export `wasi:cli/run@0.3.0` is an instance of a nested
component, of no type `projectX` knows. Even with a type, the projection would keep the
`stream`/`future`/`result` types the component defines for its built-ins and the trimmed
import types (`echo` imports `environment` with `get-arguments` only), so no WIT world equals
it. `targets` states the Component Model's own relation instead (what `wasm-tools component
targets` checks): the world provides every import at a subtype and the component every export
of the world.

Integration note: an earlier version first restated the behavioural targets as
`Task.everyHost3`-based statements (`WasiEveryHost` over `stdoutTh3`); those keep flaws 2–4
above (`everyHost_hello_no_ok` applies to them unchanged), so they were dropped in favour of
the `WasiSat` statements here.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust

open Silmaril.Wasi Silmaril.Wasi.Versions.P3
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Project.Shapes.Component (WasiSat)

/-! ## Structure: parse, scoping, world -/

/-- **The file parses** under the grammar with async built-ins. -/
def Parses3 (b : List UInt8) : Prop :=
  ∃ c : Silmaril.Wasm.Component.BinaryP3.Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf b) = .ok c

/-- **The component is well scoped** (`BinaryP3.wellScopedC3`). -/
def Valid3 (b : List UInt8) : Prop :=
  ∃ c : Silmaril.Wasm.Component.BinaryP3.Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf b) = .ok c ∧
    Silmaril.Wasm.Component.BinaryP3.wellScopedC3 c = true

/-- **The component targets the world `W`** (`BinaryP3.World.targets`). -/
def HasWorld3 (b : List UInt8) (W : Silmaril.Wasm.Wit.Project.WorldType) : Prop :=
  ∃ c : Silmaril.Wasm.Component.BinaryP3.Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf b) = .ok c ∧
    Silmaril.Wasm.Component.BinaryP3.World.targets c W = true

/-! ## The wait discipline -/

/-- `STREAM_WRITE` (`EventCode.STREAM_WRITE = 3`). -/
def streamWriteCode : Nat := 3

/-- One step of the wait discipline: the state is the list of writable ends with a blocked
`stream.write`; a `STREAM_WRITE` event of `waitable-set.wait` must be for one of them, and
ends its blocked write. -/
def waitStep (q : List Nat) : WEv → Option (List Nat)
  | .imp f a r =>
    if f = cStreamWrite then
      match a, r with
      | [wv, _], some [pv] =>
        if natOf pv = some Silmaril.Wasm.Component.Async.blocked then
          match natOf wv with
          | some w => some (w :: q)
          | none => some q
        else some q
      | _, _ => some q
    else if f = cWait then
      match r with
      | some [cv, iv, _] =>
        if natOf cv = some streamWriteCode then
          match natOf iv with
          | some w => if w ∈ q then some (q.erase w) else none
          | none => none
        else some q
      | _ => some q
    else some q
  | _ => some q

/-- **The wait discipline of WASI 0.3 hosts.** -/
def waitTh3 : Protocol (List Nat) WEv := ⟨[], waitStep⟩

/-- **The loose stdout theory with the wait discipline.** -/
def stdoutTh3w : Protocol (OutSt × List Nat) WEv := stdoutTh3.prod waitTh3

/-! ## Guarantees for one run -/

/-- The calls of `run` along `t`. -/
def runCalls (t : List WEv) : Nat :=
  t.countP fun
    | .call f _ => decide (f = run3)
    | _ => false

/-- Stdout accepted a prefix of `msg`, and all of it once `run` returned `ok`. -/
def printsP (msg : List (BitVec 8)) (t : List WEv) : Bool :=
  (stdoutBytes t).isPrefixOf msg && (!runOk t || stdoutBytes t == msg)

/-- A trace predicate required of the traces with at most one call of `run`. -/
def onceG (P : List WEv → Bool) : Protocol (List WEv) WEv :=
  ofTraces fun t => !decide (runCalls t ≤ 1) || P t

/-- The message of `hello`, `Hello, WASI 0.3!\n` in ASCII (written out so that the kernel need not
evaluate `String.toUTF8`; `utf8 "Hello, WASI 0.3!\n"` evaluates to the same list). -/
def helloMsg : List (BitVec 8) :=
  [72, 101, 108, 108, 111, 44, 32, 87, 65, 83, 73, 32, 48, 46, 51, 33, 10]

/-- **`hello`'s guarantee, for one run.** -/
def helloG1 : Protocol (List WEv) WEv := onceG (printsP helloMsg)

/-- **`cat`'s guarantee, for one run**: stdout accepted a prefix of what stdin delivered. -/
def catG1 : Protocol (List WEv) WEv :=
  onceG fun t =>
    (stdoutBytes t).isPrefixOf (stdinBytes t) && (!runOk t || stdoutBytes t == stdinBytes t)

/-! ## The restated targets -/

open Silmaril.Wasm.Component.BinaryP3 (Ast)

/-- **The file parses** under the async-aware grammar (`d095e2f`). -/
def Task.parsesP3 (b : List UInt8) : Prop :=
  ∃ c : Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf b) = .ok c

/-- **Over every host of `T`, the component meets `G`** on all events, under `den`. -/
def Task.satP3 (b : List UInt8) (den : Ast → p3World.Model) {S S' : Type} (T : Protocol S WEv)
    (G : Protocol S' WEv) : Prop :=
  ∃ c : Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf b) = .ok c ∧ WasiSat (den c) T G

/-- **`hello` prints its line** over every host of the stdout theory with the wait discipline. -/
def Task.helloPrintsP3 (den : Ast → p3World.Model) : Prop :=
  Task.satP3 Hello.File.bytes den stdoutTh3w helloG1

/-- Open: **`cat` copies stdin to stdout** modulo rechunking. -/
def Task.catCopiesP3 (den : Ast → p3World.Model) : Prop :=
  Task.satP3 Cat.File.bytes den stdoutTh3w catG1

/-- Open: the debug build of `cat` copies stdin to stdout. -/
def Task.catDebugCopiesP3 (den : Ast → p3World.Model) : Prop :=
  Task.satP3 CatDebug.File.bytes den stdoutTh3w catG1

/-- `echo`'s guarantee, for one run: it prints its arguments after the program name, joined by
spaces. -/
def echoG1 (args : List String) : Protocol (List WEv) WEv :=
  onceG (printsP (utf8 (" ".intercalate (args.drop 1) ++ "\n")))

/-- Open: **`echo` prints its arguments**, in a world `W` with `wasi:cli/environment` whose
theory `T` (which should include the wait discipline) makes `get-arguments` answer `args`. -/
def Task.echoPrintsP3 {S : Type} (W : World) (den : Ast → W.Model) (T : Protocol S WEv)
    (args : List String) : Prop :=
  ∃ c : Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf Echo.File.bytes) = .ok c ∧
    WasiSat (den c) T (echoG1 args)

/-- Open: **the release and debug builds of `cat` behave the same** under `den`. -/
def Task.cat_release_debug3 (den : Ast → p3World.Model) : Prop :=
  ∃ a b : Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf Cat.File.bytes) = .ok a ∧
    Silmaril.Wasm.Component.BinaryP3.parse (arrOf CatDebug.File.bytes) = .ok b ∧ den a = den b

end Silmaril.Project.WasmP3Rust

end
