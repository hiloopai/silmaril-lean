module

public import Silmaril.Proofs.Wasm.LimeCompile.SimLift.Basic

/-!
# Lifting run transport to export refinement: what is proved

* `session_transport`: a session from a store is one from every store related to it by a
  `SessTransport` relation, with the same observations.
* **`exportRefines_of_instTransport`**: `InstTransport P host m m'` gives
  `ExportRefines (· = ·) P host m m'`, and `exportEquiv_of_instTransport` gives `ExportEquiv`
  from transport both ways.

This is silmaril-lean's `exportRefines_of_bodiesRel` with the store relation as a parameter, so
that a compiler may change data instances, add functions and types, and change code
non-locally. It is used by `Silmaril.Wasm.LimeCompile.PassiveEquiv`.

New statements over the proofs in `Silmaril.Proofs.Wasm.LimeCompile.SimLift`.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.SimLift

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (ExportRefines ExportEquiv Session Call)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Session transport.** -/
theorem session_transport {S : Store H → Store H → Prop} {mi mi' : ModuleInst}
    (T : SessTransport P host S mi mi') {s : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (hs : Session P host mi s script bs) {t : Store H} (hst : S s t) :
    Session P host mi' t script bs :=
  Silmaril.Proofs.Wasm.LimeCompile.SimLift.session_transport T hs hst

/-- **Export refinement from instantiation transport.** -/
theorem exportRefines_of_instTransport {m m' : Module} (T : InstTransport P host m m') :
    ExportRefines (· = ·) P host m m' :=
  Silmaril.Proofs.Wasm.LimeCompile.SimLift.exportRefines_of_instTransport T

/-- **Export equivalence from transport both ways.** -/
theorem exportEquiv_of_instTransport {m m' : Module} (T : InstTransport P host m m')
    (T' : InstTransport P host m' m) : ExportEquiv (· = ·) P host m m' :=
  Silmaril.Proofs.Wasm.LimeCompile.SimLift.exportEquiv_of_instTransport T T'

end Silmaril.Wasm.LimeCompile.SimLift
