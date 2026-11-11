module

public import Silmaril.Wasm.FX.Asyncify.Tool.Selective.Defs

/-!
# The selective mode is correct: definitions

`Silmaril.Wasm.FX.Asyncify.Tool.SelSim.Thms` proves `SelectiveBeh`
(`Silmaril.Wasm.FX.Asyncify.Tool.Selective`): the output of `--selective` has the source's
behaviours on the frame machine under the host protocol. The proof is a simulation for every
program that is well formed up to pure statements holding calls of *calm* functions; for
`selProg P` the calm functions are `SelCalm P`, the defined functions outside `mayS P`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

/-- The calm functions of the selective mode: defined functions outside `mayS P`. -/
def SelCalm (P : Prog) (g : Nat) : Prop :=
  P.imps.length ≤ g ∧ g < P.imps.length + P.fns.length ∧ mayS P g = false

/-- A function of the selective program: call statements to calm functions are pure. -/
def selFn (P : Prog) (fn : FnSrc) : FnSrc := { fn with stmts := fn.stmts.map (selStmt P) }

end Silmaril.Wasm.FX.Asyncify.Tool
