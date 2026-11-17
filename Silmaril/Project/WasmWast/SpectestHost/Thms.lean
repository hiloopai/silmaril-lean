module

public import Silmaril.Project.WasmWast.SpectestHost.Defs
public import Silmaril.Project.Shapes.WasmWastHost.Thms

/-!
# WAST rows: the `spectest` host's identity semantics (kernel-checked)

Hand-written (see `Silmaril.Project.WasmWast.SpectestHost.Defs`). `script` proves every claim of
`cmds` against `Spectest.host` by one `decide +kernel` evaluation of `scriptHK`; `log` gives its
host-call log by one evaluation of `logHK`.

* `silmaril.wasm_wast.spectest_host.shared_memory`: after `$W` stores 42 through its import of
  `spectest`'s `memory`, `$R`'s load through its own import returns 42: the memory is shared, as
  in the reference interpreter. A registry that allocated a memory per import would give 0
  (`tools/wasm-wast/regress/wrong-spectest-shared.wast`, which wasmtime must reject).
* `….before_write`: the shared memory starts zeroed.
* `….globals`: the two imports of `global_i32` read 666 each (fresh globals,
  `Spectest.resolve?_global_twice`; their identity is not observable).
* `….log`: **the observation**: the host-call log of the script is `[(1, [i32 42])]`: one call of
  `print_i32` (host code 1) with 42; the reference interpreter prints `42 : i32`.
-/

@[expose] public section

namespace Silmaril.Project.WasmWast.SpectestHost

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Project.Shapes.WasmWastHost

/-- The kernel checker accepts the script. -/
theorem check : scriptHK Silmaril.Wasm.SingleThreaded.neverFail 100000 cmds = true := by
  decide +kernel

/-- Every claim of the script. -/
theorem script : ScriptHolds Silmaril.Wasm.SingleThreaded.neverFail cmds := .of_kernel check

/-- The kernel log checker: one `print_i32` call with 42. -/
theorem checkLog : logHK Silmaril.Wasm.SingleThreaded.neverFail 100000 cmds =
    some [(1, [Val.i32 42])] := by
  decide +kernel

silmaril instance silmaril.wasm_wast.spectest_host.before_write (expect := "THM") :=
  silmaril.shapes.wasm.wast.host.returns_only (o := Silmaril.Wasm.SingleThreaded.neverFail)
  (pre := pre cmds 2) (act := .invoke (.named "R") "load" []) (vs := [Val.i32 0])

@[answers "silmaril.wasm_wast.spectest_host.before_write" thm]
theorem before_write : silmaril.wasm_wast.spectest_host.before_write :=
  script.returnsOnly 2 (by kernel_rfl)

silmaril instance silmaril.wasm_wast.spectest_host.shared_memory (expect := "THM") :=
  silmaril.shapes.wasm.wast.host.returns_only (o := Silmaril.Wasm.SingleThreaded.neverFail)
  (pre := pre cmds 4) (act := .invoke (.named "R") "load" []) (vs := [Val.i32 42])

@[answers "silmaril.wasm_wast.spectest_host.shared_memory" thm]
theorem shared_memory : silmaril.wasm_wast.spectest_host.shared_memory :=
  script.returnsOnly 4 (by kernel_rfl)

silmaril instance silmaril.wasm_wast.spectest_host.globals (expect := "THM") :=
  silmaril.shapes.wasm.wast.host.returns_only (o := Silmaril.Wasm.SingleThreaded.neverFail)
  (pre := pre cmds 5) (act := .invoke (.named "W") "g" []) (vs := [Val.i32 1332])

@[answers "silmaril.wasm_wast.spectest_host.globals" thm]
theorem globals : silmaril.wasm_wast.spectest_host.globals :=
  script.returnsOnly 5 (by kernel_rfl)

silmaril instance silmaril.wasm_wast.spectest_host.log (expect := "THM") :=
  silmaril.shapes.wasm.wast.host.log_is (o := Silmaril.Wasm.SingleThreaded.neverFail)
  (cmds := cmds) (l := [(1, [Val.i32 42])])

@[answers "silmaril.wasm_wast.spectest_host.log" thm]
theorem log : silmaril.wasm_wast.spectest_host.log :=
  .of_kernel checkLog

/-- The printed values: `42 : i32`. -/
theorem printed : Spectest.printed [(1, [Val.i32 42])] = [Val.i32 42] := rfl

silmaril group silmaril.wasm_wast.spectest_host (title := "The spectest host: shared memory, fresh globals, the print log (hand-written linked script)")
  (children := [
    silmaril.wasm_wast.spectest_host.before_write,
    silmaril.wasm_wast.spectest_host.shared_memory,
    silmaril.wasm_wast.spectest_host.globals,
    silmaril.wasm_wast.spectest_host.log])

end Silmaril.Project.WasmWast.SpectestHost

end
