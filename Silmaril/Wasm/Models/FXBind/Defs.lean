module

public import Silmaril.Wasm.Models.FXLower.Defs

/-!
# Lowering WasmFX partial application (`cont.bind`) to Wasm

The first lowering (`Silmaril.Wasm.Models.FXLower`) compiles `resume (cont.new (ref.func a))` to a
call of `a`. This topic extends the fragment with **partial application**: the source binds the
first arguments `vs₁` of a fresh continuation of `a` with `cont.bind`, then resumes it with the
remaining arguments `vs₂`:

    vs₂ vs₁ ref.func a cont.new $ct cont.bind $ct $ct' resume $ct' (on …)*

In the typed proposal `cont.bind $ct $ct'` consumes exactly as many values as `$ct` has more
parameters than `$ct'`, and the function receives `vs₁ ++ vs₂` (bound arguments first). The
intended target is the plain call

    vs₁ vs₂ ref.func a call_ref

The FX reduction (`StepFX`) is untyped: `cont.bind` binds *any* suffix of the operand stack and
`resume` passes *any* suffix. So the correspondence is stated for the reduction as it is:
the source's behaviours are those of calls of `a` on the stack's **rotations** `U₂ ++ X₂` (for
`vs₂ ++ vs₁ = X₂ ++ U₂`, `U₂` the bound part), possibly after values left outside the handler.

* `srcBind a ct ct' hs vs₂ vs₁`: the FX source code;
* `bindK C U`: the continuation that `cont.bind` makes from `C` by binding `U`;
* `tgtCall a d (vs₁ ++ vs₂)` (from `FXLower`): the intended target.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXBind

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX

/-- **Source**: bind `vs₁` to a fresh continuation of `a`, then resume it with `vs₂`. -/
def srcBind (a : Nat) (ct ct' : TypeIdx) (hs : List OnClause) (vs₂ vs₁ : List Val) :
    List AdminFX :=
  cvals (vs₂ ++ vs₁) ++
    [.core (.ref (.func a)), .fx (.contNew ct), .fx (.contBind ct ct'), .fx (.resume ct' hs)]

/-- The continuation `cont.bind` makes from `C` by binding the values `U`. -/
def bindK (C : ContFX) (U : List Val) : ContFX := ⟨fun c => C.plug (cvals U ++ c)⟩

end Silmaril.Wasm.Models.FXBind
