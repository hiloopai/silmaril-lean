module

public import Silmaril.Raw.Project.WasmP3Rust.HelloCore.Refute
public import Silmaril.Project.WasmP3Rust.CoreLayer.Defs

/-!
# `hello` with its real core code: `Task.helloCore` and what is known

`CoreLayer.coreKs` is the core layer of a component run by silmaril's Core 3.0 interpreter
(`Silmaril.Project.WasmP3Rust.CoreLayer`): the three core modules of `hello.wasm` (shim, main,
fixup) instantiated with the `canon` built-ins as host functions. `Task.helloCore coreKs` says the
real code refines the model `helloK` (`HelloDen`).

**PROVED**

* `not_model_freadFirst`: no play of `den (fun _ => helloK) HelloP3.ast` asks `run`, calls
  `stream.new` (answered `(1, 2)`), `write-via-stream(1)` (answered `3`), and then
  `future.read(3)`: the model calls `waitable-set.new` third (kernel, by inverting the runs of
  `red helloK`);
* `not_helloCore_of_freadFirst`: so `Task.helloCore Ks` fails for any core semantics `Ks` under
  which `hello.wasm` has that play.

**TESTED, NOT PROVED**: under `coreKs`, `hello.wasm` has that play. `wasip3-trace` (compiled,
`tools/wasip3-trace`) runs the lifted `run` of `hello.wasm` on silmaril's interpreter under
`den`'s driver: the calls are `stream.new`, `write-via-stream`, `future.read` (the
`write_via_stream(rx).await` branch of `futures::join!` is polled first), then
`future.drop-readable`, `stream.write`, `stream.drop-writable`, `task.return` with every host
it was run with (see `tools/wasm-tools/README.md`). The kernel cannot run the interpreter on
`hello`'s instance (its memory is a 1.1 MB `ByteArray`, linear-time per access in the kernel), so
`Task.coreFreadFirst` is stated, open.

**OPEN** (frozen)

* `Task.coreFreadFirst`: the play above is a play of `den coreKs HelloP3.ast` (tested);
  with it, `not_helloCore_core` refutes `Task.helloCore coreKs`;
* `Task.helloPrintsCore`: `Task.helloPrintsP3 (den coreKs)`, the statement `helloCore` was a
  route to; a proof needs a model of the real call sequence (`future.read` first,
  `future.drop-readable`, `waitable.join(_, 0)` before each event's delivery,
  `waitable-set.drop` at the end) and its refinement by the interpreter.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.HelloCore

open Silmaril.Project.WasmP3Rust.Den Silmaril.Project.WasmP3Rust.HelloDen

/-- **The model does not issue `future.read` third.** -/
theorem not_model_freadFirst' (q : F3.Op) : freadFirst q ∉ den (fun _ => helloK) HelloP3.ast :=
  not_model_freadFirst q

/-- **`Task.helloCore` fails for a core semantics under which `hello` reads its future
third.** -/
theorem not_helloCore_of_freadFirst {Ks : Silmaril.Wasm.Component.BinaryP3.Ast → CoreExec}
    {q : F3.Op} (h : freadFirst q ∈ den Ks HelloP3.ast) : ¬ HelloDen.Task.helloCore Ks :=
  fun hc => not_model_freadFirst q (hc h)

/-- Open (tested by `wasip3-trace`): under silmaril's interpreter, `hello.wasm` reads its future
third. -/
def Task.coreFreadFirst : Prop := ∃ q, freadFirst q ∈ den CoreLayer.coreKs HelloP3.ast

/-- `Task.helloCore` is refuted for the real core layer, given the tested play. -/
theorem not_helloCore_core (h : Task.coreFreadFirst) : ¬ HelloDen.Task.helloCore CoreLayer.coreKs :=
  let ⟨_, hq⟩ := h; not_helloCore_of_freadFirst hq

/-- Open: `hello.wasm` prints its line under `den` with its real core code. -/
def Task.helloPrintsCore : Prop := Task.helloPrintsP3 (den CoreLayer.coreKs)

end Silmaril.Project.WasmP3Rust.HelloCore

end
