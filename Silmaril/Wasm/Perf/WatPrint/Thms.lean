module

public import Silmaril.Wasm.Perf.WatPrint.Defs
public import Silmaril.Wasm.Wit.Tool.Defs
import Silmaril.Proofs.Wasm.Perf.WatPrint.Eq

/-!
# The string-builder printer prints what `Sexp.printAll` prints

`ppS_eq` (with `ppLS_eq`, by mutual induction): `ppS flat ind s acc = acc ++ String.ofList
(pp flat ind s)`; `printAllF_eq : printAllF = Sexp.printAll`; `printF_eq : printF = Wat.print`
(also registered with `@[csimp]`); `printWatF_eq : printWatF = Wit.Tool.printWat`. The proofs
are in `Silmaril.Proofs.Wasm.Perf.WatPrint.Eq`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.WatPrint

open Silmaril.Wasm.Component.Wat (Sexp)
open Silmaril.Wasm.Component.Wat.Sexp (pp)

theorem ppS_eq (flat : Bool) (ind : Nat) (s : Sexp) (acc : String) :
    ppS flat ind s acc = acc ++ String.ofList (pp flat ind s) :=
  Silmaril.Proofs.Wasm.Perf.WatPrint.ppS_eq flat ind s acc

theorem printAllF_eq : printAllF = Sexp.printAll :=
  Silmaril.Proofs.Wasm.Perf.WatPrint.printAllF_eq

theorem printF_eq : printF = Silmaril.Wasm.Component.Wat.print :=
  Silmaril.Proofs.Wasm.Perf.WatPrint.printF_eq

/-- `Wat.print` for the compiler: code compiled in a module that imports this one prints with
`printF`. -/
@[csimp] theorem print_eq_printF : @Silmaril.Wasm.Component.Wat.print = @printF := printF_eq.symm

theorem printWatF_eq : printWatF = Silmaril.Wasm.Wit.Tool.printWat :=
  Silmaril.Proofs.Wasm.Perf.WatPrint.printWatF_eq

end Silmaril.Wasm.Perf.WatPrint
