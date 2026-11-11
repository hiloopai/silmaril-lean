module

public import Silmaril.Wasm.SSA.Bridge.Defs
public import Silmaril.Wasm.SSA.Fragment.Defs
public import Silmaril.Wasm.Binaryen.Interp
public import Silmaril.Wasm.Binaryen.Typing
import Silmaril.Proofs.Wasm.SSA.Bridge.RoundTrip

/-!
# The fragment inside Binaryen's folded IR: round trip and adequacy

* Proved: lowering then recognising is the identity on the fragment
  (`ofBExpr?_toBExpr?`, `ofBExprs?_toBExprs?`), and likewise for functions
  whose silmaril function type has the fragment's parameter and result types
  (`ofBFunc?_toBFunc?`).
* Adequacy with respect to silmaril's native Binaryen interpreter
  (`Silmaril.Wasm.Binaryen.Eval`) is proved in `Native` (`native_adequate`)
  for functions passing the arity check `FragFunc.native`; it excludes the
  conversion operators, which that interpreter does not implement. Silmaril's
  obligations relating the interpreter to Core 3.0 small-step execution
  (`Binaryen/AdequacyReduce.lean`) are open upstream.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm (IntType FuncType TypeIdx ValType)
open Silmaril.Wasm.Binaryen (BExpr BFunc)
open Silmaril.Wasm.Execution.Core (Val Store ModuleInst Frame)

theorem ofBExpr?_toBExpr? {e : Expr} {b : BExpr} (h : toBExpr? e = some b) :
    ofBExpr? b = some e :=
  Silmaril.Proofs.Wasm.SSA.Bridge.ofBExpr_toBExpr e h

theorem ofBExprs?_toBExprs? {es : List Expr} {bs : List BExpr} (h : toBExprs? es = some bs) :
    ofBExprs? bs = some es :=
  Silmaril.Proofs.Wasm.SSA.Bridge.ofBExprs_toBExprs es h

theorem ofBFunc?_toBFunc? {ty : TypeIdx} {f : FragFunc} {bf : BFunc} (h : toBFunc? ty f = some bf)
    {ft : FuncType} (hp : ft.params = f.params.map fun t => .num (.int t))
    (hr : ft.results = resultTypes f.result) : ofBFunc? ft bf = some f :=
  Silmaril.Proofs.Wasm.SSA.Bridge.ofBFunc_toBFunc h hp hr

/-! ## Adequacy

Adequacy against silmaril's native Binaryen interpreter is `native_adequate`
(`Silmaril.Wasm.SSA.Native.Thms`), proved in both directions for functions passing
the arity check `FragFunc.native`. It does not cover the conversion operators,
for which the native interpreter has no rule, so a statement under Core
validation alone (`SeqOk`) for the whole fragment would be false. -/

end Silmaril.Wasm.SSA
