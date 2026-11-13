module

public import Silmaril.Wasm.Wat
public import Silmaril.Servers.WasiCore.Defs
public meta import Silmaril.Wasm.Wat.CoreModules
public meta import Silmaril.Wasm.Wat.CoreInstructions
public meta import Lean.Elab.Term

@[expose] public section

/-!
# The example `wasi:http` components as core modules

The core modules of the example components of `tests/servers/wasi-http`: each is
`common.wat` (imports, memory, allocator, `answer`) followed by one server's part, exactly as
`tests/servers/wasi-http/build.sh` assembles them before `wasm-tools component embed` and
`component new`. They are read from those files at elaboration time by `wat3_files!`, with
the Core 3 WAT frontend of `wat3!` (`Silmaril.Wasm.Wat`): the Lean terms below are the
frontend's output on the very sources the conformance test builds. (Lake does not track the
`.wat` files: a change to them needs a rebuild of this module.)

* `helloCore`, `routeCore`, `echoCore`: the core modules of `hello`, `route` and `echo`;
* `binFuel`: the step bound of their denotations `coreBody m binFuel`
  (`Silmaril.Servers.WasiCore`).

A Silmaril addition.
-/

namespace Silmaril.Servers.WasiBinaries

open Lean Elab Term in
/-- The module `(module <contents of the files>)`, by the `wat3!` frontend, the paths relative
to this source file. -/
meta def watFilesTerm (paths : List String) : TermElabM Syntax := do
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let mut text := "(module\n"
  for p in paths do
    text := text ++ (← IO.FS.readFile (dir / p)) ++ "\n"
  text := text ++ ")"
  liftMacroM (Silmaril.Wasm.Wat.Core.moduleTerm
    (fun scope nodes => Silmaril.Wasm.Wat.Core.instructions scope nodes) text)

open Lean Elab Term in
/-- `wat3_files! "a.wat" "b.wat"`: the Core 3 module whose fields are the contents of the
files, in order (paths relative to the current source file). -/
elab "wat3_files! " ps:str* : term => do
  let stx ← watFilesTerm (ps.toList.map (·.getString))
  elabTerm stx (some (mkConst ``Silmaril.Wasm.Module))

/-- The core module of `hello`. -/
def helloCore : Silmaril.Wasm.Module :=
  wat3_files! "../../../tests/servers/wasi-http/common.wat"
    "../../../tests/servers/wasi-http/hello.wat"

/-- The core module of `route`. -/
def routeCore : Silmaril.Wasm.Module :=
  wat3_files! "../../../tests/servers/wasi-http/common.wat"
    "../../../tests/servers/wasi-http/route.wat"

/-- The core module of `echo`. -/
def echoCore : Silmaril.Wasm.Module :=
  wat3_files! "../../../tests/servers/wasi-http/common.wat"
    "../../../tests/servers/wasi-http/echo.wat"

/-- The step bound of the denotations of the example modules. -/
def binFuel : Nat := 100000

end Silmaril.Servers.WasiBinaries
