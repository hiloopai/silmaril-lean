module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# The vector errata: the `vec_` and `vN` lookups in `simEnv20V B` (kernel `rfl`)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d82 Original.d88)

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_vec20V : ∃ ps qs, (simEnv20V B).findTyp? "vec_" = some (ps, [.instD qs
    [.expA (.varE "Vnn")] (.aliasT (.varT "vN" [.expA (.callE "size"
      [.expA (.subE (.varE "Vnn") (.varT "Vnn" []) (.varT "valtype" []))])]))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_vN20V : ∃ ps qs, (simEnv20V B).findTyp? "vN" = some (ps, [.instD qs
    [.expA (.varE "N")] (.aliasT (.varT "iN" [.expA (.varE "N")]))]) :=
  ⟨_, _, rfl⟩

end Silmaril.Wasm.SpecTec.Sim20.VecFix
