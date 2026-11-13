module

public import Silmaril.Project.Defs
public import Silmaril.Wasm.Verify.FnSpec.Defs
public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# Standard problem shapes: WebAssembly modules

| name | statement |
|---|---|
| `silmaril.shapes.wasm.fn_spec` | `FnMeets m i S`: function `i` of the module `m` meets the `FnSpec` `S` (`Verified m i S`, proved by `wasm_vc`) |
| `silmaril.shapes.wasm.returns` | `Returns m a args res`: `$invoke` of function address `a` of the instantiated `m` on `args` returns `res` |

The module `m` is a registered value of format `wasm` or `wat` (the row is then
`X.Satisfies (fun m => …)`, so the file must decode), or a Lean module (a `wat3!` quote).
`FnMeets` is partial correctness with safety, for every input, at every numeric profile and
for every host relation (`FnSpec.sound`); `Returns` is one run of silmaril-lean's verified
interpreter on a module with no imports. Rows:

```lean
silmaril instance demo.double.fn0 := silmaril.shapes.wasm.fn_spec
  (m := demo.double) (i := 0) (S := Demo.Wasm.doubleSpec)
silmaril instance demo.wasm.mul.run_3_4 := silmaril.shapes.wasm.returns
  (m := Demo.Wasm.pureProg) (a := 4) (args := [.i32 3, .i32 4]) (res := [.i32 12])
```

`Silmaril.Project.Shapes.Wasm.Thms` proves a `returns` row with one kernel evaluation of the library's
structural interpreter `runInvokeK` (`Returns.of_kernel`; `Returns.of_value_kernel` also
decodes the file).
-/

@[expose] public section

namespace Silmaril.Project.Shapes

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core

/-- **Function `i` of `m` meets `S`**: `wasm_vc` proves `S.vc` of its body. -/
@[problem "silmaril.shapes.wasm.fn_spec"
  (title := "A function of a Wasm module meets its specification")]
def FnMeets {α : Type} (m : Module) (i : Nat) (S : Silmaril.Wasm.Verify.FnSpec α) : Prop :=
  Silmaril.Wasm.Verify.Verified m i S

/-- The store of `m` instantiated against no imports (`none` if instantiation fails). -/
def wasmStore? (m : Module) : Option (Store Nat) :=
  match instantiateOnce? (Silmaril.Wasm.Game.importStore []) m [] with
  | some (s, _, _) => some s
  | none => none

/-- The result of `$invoke` of function address `a` on `args`, run with `fuel` steps of
silmaril-lean's verified interpreter (no host function, memory never grows). -/
def wasmRun (m : Module) (fuel a : Nat) (args : List Val) : Option Result :=
  match wasmStore? m with
  | some s =>
    match Silmaril.Wasm.SingleThreaded.Exec.runInvoke? (fun _ _ _ _ => false) fuel s a args with
    | some (_, _, r) => r
    | none => none
  | none => none

/-- `wasmRun` with the library's structural interpreter `runInvokeK`, which the kernel evaluates
(`wasmRun_eq_kernel`). -/
noncomputable def wasmRunK (m : Module) (fuel a : Nat) (args : List Val) : Option Result :=
  match wasmStore? m with
  | some s =>
    match Silmaril.Wasm.Verify.Kernel.runInvokeK (fun _ _ _ _ => false) fuel s a args with
    | some (_, _, r) => r
    | none => none
  | none => none

/-- **A run returns `res`**: with some fuel, `$invoke` of function address `a` of the
instantiated `m` on `args` returns the values `res`. -/
@[problem "silmaril.shapes.wasm.returns"
  (title := "A Wasm invocation returns given values")]
def Returns (m : Module) (a : Nat) (args res : List Val) : Prop :=
  ∃ fuel, wasmRun m fuel a args = some (.values res)

end Silmaril.Project.Shapes

end

