module

public import Silmaril.Wasm.V1.Modules
public import Silmaril.Wasm.Lime1.Modules
public import Silmaril.Wasm.Modules
public import Silmaril.Wasm.Wat.Print
public meta import Silmaril.Wasm.Wat.Modules
public meta import Silmaril.Wasm.Wat.CoreModules
public meta import Silmaril.Wasm.Wat.CoreInstructions

/-! # WAT quotations

`wat1!`, `watLime!`, and `wat3!` construct the independent source modules for
Wasm 1, Lime 1, and Core 3. The corresponding `_expr!` quotations construct
instruction lists; without a module scope only numeric references can be resolved.
Core 3 expressions that allocate implicit function types require a module quotation.

These are elaboration-time syntax frontends, not validators. Profile-specific
unsupported constructs are errors. The generated term contains only
ordinary Lean constructors and is checked by the kernel. See `docs/projects/wasm-wat.md`.
-/

public meta section

namespace Silmaril.Wasm.Wat

macro "wat1! " text:str : term => moduleTerm .v1 text.getString
macro "watLime! " text:str : term => moduleTerm .lime text.getString
macro "wat1_expr! " text:str : term => expressionTerm .v1 text.getString
macro "watLime_expr! " text:str : term => expressionTerm .lime text.getString
macro "wat3! " text:str : term =>
  Core.moduleTerm (fun scope nodes => Core.instructions scope nodes) text.getString
macro "wat3_expr! " text:str : term => Core.expressionTerm text.getString

end Silmaril.Wasm.Wat
