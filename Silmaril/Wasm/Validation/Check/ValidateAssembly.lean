module

public import Silmaril.Wasm.Validation.Check.ValidateComplete
public import Silmaril.Wasm.Validation.Check.TypesComplete
public import Silmaril.Wasm.Validation.Check.InstrsComplete
public import Silmaril.Wasm.Validation.Check.InstrsCompleteStep

@[expose] public section

/-! # Assembly of `validate?` completeness

Reduces completeness of `validate?` to exactly two hypotheses:

* `hT : ∀ Δ, Δ.Ok → Δ.recs = [] → TyOkComplete Δ` — completeness of `TyOk.check`
  in closed well-formed contexts (to be discharged by `TyOk.check_complete`,
  `Check/TyOkComplete.lean`);
* `hA : StepComplete.AtomComplete atomC` — completeness of the fallthrough atomic
  oracle (to be discharged by `atomC_complete_of …`, `Check/AtomComplete.lean`).

The `types` hypothesis of `ValidateComplete` comes from `typesC_complete`, and the
`expr` hypothesis from `checkExpr?_complete` with `directStep_complete`.
-/

namespace Silmaril.Wasm.Validation

section ValidateAssembly

variable (hT : ∀ Δ : TypeCtx, Δ.Ok → Δ.recs = [] → TyOkComplete Δ)
  (hA : StepComplete.AtomComplete atomC)

include hT in
theorem tyOkC_oracleComplete : TyOkOracleComplete tyOkC :=
  fun Δ _ _ hΔ hr h => hT Δ hΔ hr h

include hT in
theorem tyOkC_stepComplete : StepComplete.TyOkComplete tyOkC :=
  fun Δ _ _ hΔ hr h => hT Δ hΔ hr h

include hT in
theorem defaultTypes_complete {rts : List RecType} {dts : List DefType}
    (h : TypesOk {} rts dts) : defaultCheckers.types? {} rts = some dts :=
  typesC_complete hT h

include hT hA in
theorem atomC_directComplete : DirectComplete atomC tyOkC :=
  directStep_complete hA (tyOkC_stepComplete hT)

include hT hA in
theorem exprC_complete :
    ∀ C e ts, C.Wf → C.recs = [] → ExprOk C e ts → exprC C e ts = true :=
  fun _ _ _ hC hr h =>
    checkExpr?_complete (atomC_directComplete hT hA) (tyOkC_oracleComplete hT) hC hr h

include hT hA in
/-- Completeness of `validate?`, relative to `TyOk.check` completeness (`hT`) and
atomic-oracle completeness (`hA`). -/
theorem validate?_complete_of_atom {m : Module} {mt : CModuleType} (h : ModuleOk m mt) :
    validate? m = some mt :=
  validate?_complete_of hT (defaultTypes_complete hT) (exprC_complete hT hA) h

include hT hA in
theorem validate?_isSome_iff_of_atom {m : Module} : (validate? m).isSome ↔ ModuleValid m :=
  validate?_isSome_iff_of hT (defaultTypes_complete hT) (exprC_complete hT hA)

/-- Decidability of module validity via `validate?`, relative to `hT` and `hA`. -/
def decidableModuleValid_of_atom (m : Module) : Decidable (ModuleValid m) :=
  decidableModuleValid_of hT (defaultTypes_complete hT) (exprC_complete hT hA) m

end ValidateAssembly

end Silmaril.Wasm.Validation
