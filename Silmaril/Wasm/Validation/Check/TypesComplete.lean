module

public import Silmaril.Wasm.Validation.Check.Types
public import Silmaril.Wasm.Validation.Check.TyOkDerivedComplete
public import Silmaril.Wasm.Validation.RollClosed
public import Silmaril.Wasm.Validation.Subtyping.WeakenEmpty
public import Silmaril.Wasm.Validation.Subtyping.DefInv

@[expose] public section

/-! # Completeness of the module type-section checker

`typesCheck? RecTypeOkAt.check {} rts` finds `dts` whenever `TypesOk {} rts dts`,
given completeness of `TyOk.check` in every well-formed context without `RECS`.
Every context the checker visits has closed, empty-context-valid types (from the
group's own validity, `Context.rollGroup_tyOk`), hence is `Ok` and satisfies
`SuperBodiesOk`.
-/

namespace Silmaril.Wasm.Validation

namespace TypesComplete

theorem ok_of_empty {C : Context} (hT : ∀ d ∈ C.types, TyOk {} d) : C.toTypeCtx.Ok :=
  fun d hd =>
    have h0 := hT d hd
    ⟨SubClosed.closed_of_empty h0, wireCallRef_tyOk_of_empty _ h0⟩

theorem superBodiesOk_of_empty {C : Context} (hT : ∀ d ∈ C.types, TyOk {} d) :
    SuperBodiesOk C := by
  intro x d sups' ct' hd hun
  exact wireCallRef_tyOk_of_empty _ (DefInv.unroll_ok (hT d (List.mem_of_getElem? hd)) hun).1

theorem gen (hT : ∀ Δ : TypeCtx, Δ.Ok → Δ.recs = [] → TyOkComplete Δ)
    {C : Context} {rts : List RecType} {dts : List DefType} (h : TypesOk C rts dts) :
    (∀ d ∈ C.types, TyOk {} d) → C.recs = [] →
      typesCheck? RecTypeOkAt.check C rts = some dts := by
  induction h with
  | nil => intro _ _; rfl
  | @cons C rt rts dts hok _ ih =>
    intro hTy hr
    have hg := Context.rollGroup_tyOk hTy hr hok
    have hTy' : ∀ d ∈ ({ C with types := C.types ++ C.rollGroup rt } : Context).types,
        TyOk {} d := by
      intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact hTy d hd
      · exact hg d hd
    have hΔ := ok_of_empty hTy'
    have hchk := RecTypeOkAt.check_complete (hT _ hΔ hr) hΔ hr (superBodiesOk_of_empty hTy') hok
    simp only [typesCheck?, hchk, ite_true, ih hTy' hr, Option.map_some]

end TypesComplete

/-- Completeness of the default type-section checker (the `types` field of
`ModuleCheckers.CompleteWf` for `defaultCheckers`). -/
theorem typesC_complete (hT : ∀ Δ : TypeCtx, Δ.Ok → Δ.recs = [] → TyOkComplete Δ)
    {rts : List RecType} {dts : List DefType} (h : TypesOk {} rts dts) :
    typesCheck? RecTypeOkAt.check {} rts = some dts :=
  TypesComplete.gen hT h (by simp) rfl

end Silmaril.Wasm.Validation
