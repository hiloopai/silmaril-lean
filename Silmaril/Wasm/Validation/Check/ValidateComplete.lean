module

public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Validation.Check.ModuleCompleteWf
public import Silmaril.Wasm.Validation.Check.ModuleDefsComplete
public import Silmaril.Wasm.Validation.Check.FuncComplete
public import Silmaril.Wasm.Validation.Check.TyOkDerivedComplete

@[expose] public section

/-! # Completeness of the concrete validator `validate?`, relative to three pieces

The results here are parameterised by three completeness hypotheses:

* `hT`: completeness of `TyOk.check` in well-formed contexts without `RECS`;
* `htypes`: completeness of the type-section checker `defaultCheckers.types?`;
* `hexpr`: completeness of the expression checker `exprC` in well-formed contexts
  without `RECS`.

The unconditional versions are obtained by instantiating `hT` with
`TyOk.check_complete`, `htypes` with `typesC_complete hT`, and `hexpr` with the
instruction-checker completeness lemma (Check/InstrsComplete). Those files are
deliberately not imported here.
-/

namespace Silmaril.Wasm.Validation

section ValidateComplete

variable (hT : ∀ Δ : TypeCtx, Δ.Ok → Δ.recs = [] → TyOkComplete Δ)
  (htypes : ∀ {rts dts}, TypesOk {} rts dts → defaultCheckers.types? {} rts = some dts)
  (hexpr : ∀ C e ts, C.Wf → C.recs = [] → ExprOk C e ts → exprC C e ts = true)

include hT in
theorem tyOkC_complete_wf :
    ∀ Δ {k} (t : Ty k), Δ.Ok → Δ.recs = [] → TyOk Δ t → tyOkC Δ t = true :=
  fun Δ _ _ hΔ hr h => hT Δ hΔ hr h

include hexpr in
theorem constC_complete_wf :
    ∀ C e t, C.Wf → C.recs = [] → ExprOkConst C e t → constC C e t = true := by
  intro C e t hC hr h
  simp only [constC, constOk, Bool.and_eq_true]
  exact ⟨hexpr _ _ _ hC hr h.typed, ExprConst.check_complete h.const⟩

include hT htypes hexpr in
theorem defaultCheckers_completeWf : defaultCheckers.CompleteWf where
  types h := htypes h
  import_ hC hr h := importCheck?_complete (tyOkC_complete_wf hT) hC hr h
  tag hC hr h := tagCheck?_complete (tyOkC_complete_wf hT) hC hr h
  globals hC hr h :=
    globalsCheck?_complete (tyOkC_complete_wf hT) (constC_complete_wf hexpr) hC hr h
  mem h := memCheck_complete h
  table hC hr h :=
    tableDefCheck?_complete (tyOkC_complete_wf hT) (constC_complete_wf hexpr) hC hr h
  func hC hr h := funcCheck_complete (tyOkC_complete_wf hT) hexpr hC hr h
  data hC hr h := dataCheck_complete (constC_complete_wf hexpr) hC hr h
  elem hC hr h :=
    elemCheck?_complete (tyOkC_complete_wf hT) (constC_complete_wf hexpr) hC hr h
  start hC hr h := startCheck_complete hC hr h
  export_ hC hr h := exportCheck?_complete hC hr h

include hT htypes hexpr in
theorem validate?_complete_of {m : Module} {mt : CModuleType} (h : ModuleOk m mt) :
    validate? m = some mt :=
  checkModule?_complete_wf (defaultCheckers_completeWf hT htypes hexpr) h

include hT htypes hexpr in
theorem validate?_isSome_iff_of {m : Module} : (validate? m).isSome ↔ ModuleValid m :=
  checkModule?_isSome_iff_wf defaultCheckers_sound (defaultCheckers_completeWf hT htypes hexpr)

/-- Decidability of module validity via `validate?`, relative to the three hypotheses. -/
def decidableModuleValid_of (m : Module) : Decidable (ModuleValid m) :=
  decidableModuleValidWf defaultCheckers_sound (defaultCheckers_completeWf hT htypes hexpr) m

end ValidateComplete

end Silmaril.Wasm.Validation
