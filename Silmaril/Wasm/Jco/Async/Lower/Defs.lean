module

public import Silmaril.Wasm.Component.Async.Defs

/-!
# Async lowers, futures and streams through the adaptor (part (e))

The adaptor-side programs that let a **synchronous** core module use an async world, over the
handle table of `Silmaril.Wasm.Component.Async` (one table; items are component values, the guest
memory copy is not modelled):

* **Async lowering of an import** (`lowStep`). The module calls a world import synchronously;
  the world's import is lowered with `canon lower … async`. The adaptor's shim starts the call
  (`callAsync`, a subtask handle `t`), creates a waitable set (`waitable-set.new`), joins `t` to
  it (`waitable.join`), and then waits (`waitable-set.wait`) until the event of `t` is the
  `subtask` event; it reads the results the callee's `task.return` stored, drops the subtask
  (`subtask.drop`) and resumes the module with them. The shim's thread runs without
  interleaving until it suspends (cooperative scheduling), so the three start built-ins are one
  step. `LowRun` interleaves the shim's steps with arbitrary built-ins of other parties.
* **A future result** (`futureOut`). A world function returning `future<T>` from a module
  returning a `T`: the adaptor creates a future (`future.new`), writes the value
  (`future.write`, pending until a reader comes) and returns the readable end.
* **A stream result** (`streamOut`). A world function returning `stream<T>` from a module
  returning a `list<T>`: `stream.new`, a pending `stream.write` of the items, and the readable
  end.

Handles passed as parameters (`stream<T>`, `future<T>`, `borrow`/`own` of these ends) keep their
number in this one-table model, so the adaptor passes them through unchanged; the transfer of
ends between per-instance tables is not modelled (`docs/projects/wasm-components.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Store Op Res Event EventCode step)

/-- The program counter of the adaptor's async-lowering shim. -/
inductive LowPc where
  /-- Not yet called. -/
  | start
  /-- Waiting on the set `ws` for the subtask `t`. -/
  | waiting (t ws : Nat)
  /-- Resumed with these results. -/
  | done (vs : List Val)

/-- **One step of the async-lowering shim** (`none`: no step, i.e. suspended, finished, or a
trap). -/
def lowStep (st : Store) : LowPc → Option (Store × LowPc)
  | .start =>
    match step st .callAsync with
    | some (s₁, _) =>
      match step s₁ .wsNew with
      | some (s₂, _) =>
        match step s₂ (.join st.next s₁.next) with
        | some (s₃, _) => some (s₃, .waiting st.next s₁.next)
        | none => none
      | none => none
    | none => none
  | .waiting t ws =>
    match step st (.wait ws) with
    | some (s₁, .event e) =>
      if e.code = .subtask ∧ e.index = t then
        match (s₁.tasks t).result with
        | some vs =>
          match step s₁ (.subtaskDrop t) with
          | some (s₂, _) => some (s₂, .done vs)
          | none => none
        | none => none
      else none
    | _ => none
  | .done _ => none

/-- A run of the shim interleaved with built-ins of other parties. -/
inductive LowRun : Store → LowPc → Store → LowPc → Prop where
  | refl (st pc) : LowRun st pc st pc
  | shim {st pc st' pc' st'' pc''} : lowStep st pc = some (st', pc') →
      LowRun st' pc' st'' pc'' → LowRun st pc st'' pc''
  | env {st pc st' r st'' pc''} (op : Op) : step st op = some (st', r) →
      LowRun st' pc st'' pc'' → LowRun st pc st'' pc''

/-- **A future result**: create a future, write `v` to it, return the readable end. -/
def futureOut (st : Store) (v : Val) : Option (Store × Nat) :=
  match step st .futureNew with
  | some (s₁, .ends r w) =>
    match step s₁ (.futureWrite w v) with
    | some (s₂, _) => some (s₂, r)
    | none => none
  | _ => none

/-- **A stream result**: create a stream, write the items `xs`, return the readable end. -/
def streamOut (st : Store) (xs : List Val) : Option (Store × Nat) :=
  match step st .streamNew with
  | some (s₁, .ends r w) =>
    match step s₁ (.streamWrite w xs) with
    | some (s₂, _) => some (s₂, r)
    | none => none
  | _ => none

/-- A worked run: the shim starts the call on the empty store, the callee task `1` returns
`[u32 7]`, the shim resumes. -/
def lowDemo : Option (List Val) :=
  match lowStep Store.empty .start with
  | some (s₁, pc₁) =>
    match step s₁ (.taskReturn 1 [.u32 7]) with
    | some (s₂, _) =>
      match lowStep s₂ pc₁ with
      | some (_, .done vs) => some vs
      | _ => none
    | none => none
  | none => none

end Silmaril.Wasm.Jco.Async
