module

public import Silmaril.Project.Shapes.Wasm.Defs
public import Silmaril.Wasm.Verify.Kernel.Thms

/-! # Standard problem shapes: WebAssembly modules (transfer lemmas)

* `FnMeets.of_vc`: a row of `fn_spec` from the body and its verification condition (the goal
  `wasm_vc` proves); `FnMeets.vc`: the converse, to refute a row.
* `wasmRun_eq_kernel`: `wasmRun = wasmRunK` (`runInvokeK_eq`).
* `Returns.of_kernel fuel h`: a row of `returns` on a Lean module, with `h` proved by
  `kernel_rfl` or `decide +kernel`; `Returns.of_value_kernel fuel h`: a row on a registered
  value, `h` one kernel `Bool` that decodes the file and runs it.
-/

@[expose] public section

namespace Silmaril.Project.Shapes

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core

theorem FnMeets.of_vc {α : Type} {m : Module} {i : Nat} {S : Silmaril.Wasm.Verify.FnSpec α}
    {fn : Func} (h : m.funcs[i]? = some fn) (hv : S.vc fn) : FnMeets m i S :=
  ⟨fn, h, hv⟩

/-- The verification condition of a row, at the body `fn` (`rfl` proves `hfn` on a Lean module):
the converse of `of_vc`, to refute a row. -/
theorem FnMeets.vc {α : Type} {m : Module} {i : Nat} {S : Silmaril.Wasm.Verify.FnSpec α}
    {fn : Func} (h : FnMeets m i S) (hfn : m.funcs[i]? = some fn) : S.vc fn := by
  obtain ⟨fn', hfn', hv⟩ := h
  cases hfn.symm.trans hfn'
  exact hv

theorem wasmRun_eq_kernel : wasmRun = wasmRunK := by
  funext m fuel a args
  rw [wasmRun, wasmRunK, Silmaril.Wasm.Verify.Kernel.runInvokeK_eq]

/-- A row of `returns` from one kernel evaluation with `fuel` steps. -/
theorem Returns.of_kernel {m : Module} {a : Nat} {args res : List Val} (fuel : Nat)
    (h : wasmRunK m fuel a args = some (.values res)) : Returns m a args res :=
  ⟨fuel, by rw [wasmRun_eq_kernel]; exact h⟩

/-- A row of `returns` on a registered value: one kernel `Bool` decodes the file and runs it. -/
theorem Returns.of_value_kernel {X : Value Module} {a : Nat} {args res : List Val} (fuel : Nat)
    (h : (X.parse.any fun m => decide (wasmRunK m fuel a args = some (.values res))) = true) :
    X.Satisfies fun m => Returns m a args res := by
  cases hx : X.parse with
  | none => rw [hx] at h; cases h
  | some m =>
    rw [hx] at h
    exact ⟨m, hx, Returns.of_kernel fuel (by simpa using h)⟩

end Silmaril.Project.Shapes
