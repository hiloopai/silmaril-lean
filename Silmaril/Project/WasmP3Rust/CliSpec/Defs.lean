module

public import Silmaril.Wasi.Cli.Defs
public import Silmaril.Cli.Io.Examples.Defs
public import Silmaril.Project.WasmP3Rust.TasksX.Defs

/-!
# `echo.wasm` and `cat.wasm` against CLI behaviour specifications

The worked examples of the WASI bridge of `docs/projects/wasm-binaryen-tooling.md`: the pinned Rust WASI 0.3
components `examples/wasip3-rust/dist/{echo,cat}.wasm`, stated to satisfy CLI behaviour
specifications for every host of a theory, through the WASI 0.3 view (`echo`: `p3View`, which
does not read stdin; `cat`: `p3xView`, with `DenX`'s data-carrying stdin reading).

* **echo**: the spec is `orFail echoSpec` (`Silmaril.Cli.Io.Examples.echoSpec`, the spec the Lean
  program `echoProg` is proved to satisfy and that `cli-harness` checks binaries against): the
  line of the arguments, or a failure after a prefix of it. The theory `echoCliTh i` is `echo`'s
  (stdout with the wait discipline, `get-arguments` answering `i.prog :: i.args`).
* **cat**: the spec is `orFail catNow`: stdout is the part of stdin consumed, nothing else
  observed (`catNow ⊓ consumesAll` refines `catSpec`, `catNow_inf_consumesAll`). The theory
  `catCliTh i` is stdout with the wait discipline, and stdin delivering a prefix of `i.stdin`
  (`stdinTh i`). A host may end stdin early, so a run need not consume all of it.

Nothing in the WASI theories rules out a failing host (or an allocation failure), hence
`orFail`.

`Task.echoCli den`, `Task.catCli den`: the file parses, and its denotation under `den` satisfies
the spec.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli
open Silmaril.Project.WasmP3Rust.DenX (p3xWorld)
open Silmaril.Wasm.Component.BinaryP3 (Ast)

/-- **The WASI 0.3 view with `DenX`'s stdin reading** (`stdinBytesX`). -/
def p3xView : View := p3View none fun t => toBytes (stdinBytesX t)

/-- The theory of `echo`'s host on the invocation `i`. -/
def echoCliTh (i : Input) := echoTh (i.prog :: i.args)

/-- **`echo.wasm` satisfies `echo`'s CLI specification** (allowing failure) under `den`, for
every host of `echoCliTh`. -/
def Task.echoCli (den : Ast → p3xWorld.Model) : Prop :=
  ∃ c : Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf Echo.File.bytes) = .ok c ∧
    CliSat (den c) echoCliTh (p3View) (Spec.orFail Silmaril.Cli.Io.Examples.echoSpec)

/-- **The behavioural target for `echo`'s real core code** (open, frozen): under the core
semantics `Ks`, `echo.wasm` prints the line of its arguments, for every argument list. It is all
`Task.echoCli` needs (`echoCli_of_lines`) and is implied by `StdioK.Task.echoCore Ks`
(`echoLines_of_core`), which asks the whole denotation to refine the model's and is expected
to fail for the real code (see `docs/projects/wasm-binaryen-tooling.md`). -/
def Task.echoLines (Ks : Ast → DenX.CoreExecX) : Prop :=
  ∀ args, Task.echoPrintsX (DenX.den Ks) args

/-- **`cat` so far**: stdout is the part of stdin consumed; nothing else observed (no file
read, written or logged). -/
def catNow : Spec := fun i o =>
  o.stdout = i.stdin.take o.consumed ∧ o.consumed ≤ i.stdin.length ∧ o.stderr = [] ∧
    o.exit = 0 ∧ o.fs = i.fs ∧ o.reads = [] ∧ o.log = []

/-- Stdin delivered a prefix of `i.stdin`. -/
def stdinTh (i : Input) : Silmaril.Wasm.Resource.Protocol (List WEv) WEv :=
  ofTraces fun t => (toBytes (stdinBytesX t)).isPrefixOf i.stdin

/-- The theory of `cat`'s host on `i`: stdout with the wait discipline, stdin from `i.stdin`. -/
def catCliTh (i : Input) := stdoutTh3x.prod (stdinTh i)

/-- **`cat.wasm` satisfies `cat`'s CLI specification** (allowing failure) under `den`, for
every host of `catCliTh`. -/
def Task.catCli (den : Ast → p3xWorld.Model) : Prop :=
  ∃ c : Ast, Silmaril.Wasm.Component.BinaryP3.parse (arrOf Cat.File.bytes) = .ok c ∧
    CliSat (den c) catCliTh p3xView (Spec.orFail catNow)

end Silmaril.Project.WasmP3Rust

end
