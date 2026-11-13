module

public import Silmaril.Wasm.SpecTec.Sim20.VecFix.Defs
public import Silmaril.Wasm.SpecTec.Sim20.VecRefute.Thms

/-!
# The vector errata: the typing interface

`typedV_of_hasTyp_true`: a closed type that `hasTyp` accepts from the empty scope at some fuel is
accepted from every term-only scope (`TypedV`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)

/-- **A closed type accepted from the empty scope is `TypedV`.** -/
theorem typedV_of_hasTyp_true {env : Env} {x : IL.Id} {v : Value} {n : Nat}
    (h : hasTyp n env VarEnv.empty (.varT x []) v = .ok true) : TypedV env (.varT x []) v :=
  fun _ hρ => Sim.IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ hρ ⟨n, h⟩

end Silmaril.Wasm.SpecTec.Sim20.VecFix
