module

public import Silmaril.Wasm.Validation.Check.Func
public import Silmaril.Wasm.Validation.Instructions.Properties

@[expose] public section

/-! # Completeness of the function-definition checker

`funcCheck_complete`: relative to completeness of `tyOk` and `exprOk` on
well-formed contexts without `RECS`.
-/

namespace Silmaril.Wasm.Validation

section FuncComplete

variable {tyOk : TypeCtx → {k : TKind} → Ty k → Bool}
  {exprOk : Context → Expr → List CValType → Bool}

theorem LocalOk.tyOk_type {C : Context} {t : ValType} {lt : LocalType} (h : LocalOk C t lt) :
    TyOk C.toTypeCtx lt.type := by
  cases h with
  | set h _ => exact h
  | unset h _ => exact h

theorem locals_tyOk {C : Context} {ts : List ValType} {lts : List LocalType}
    (h : List.Forall₂ (LocalOk C) ts lts) : ∀ lt ∈ lts, TyOk C.toTypeCtx lt.type := by
  induction h with
  | nil => simp
  | cons h _ ih =>
    intro lt hlt
    rcases List.mem_cons.mp hlt with rfl | hlt
    · exact h.tyOk_type
    · exact ih lt hlt

theorem localCheck?_complete_wf
    (htyOk' : ∀ Δ {k} (t : Ty k), Δ.Ok → Δ.recs = [] → TyOk Δ t → tyOk Δ t = true)
    {C : Context} (hΔ : C.toTypeCtx.Ok) (hr : C.recs = []) {t : ValType} {lt : LocalType}
    (h : LocalOk C t lt) : localCheck? tyOk C t = some lt := by
  cases h with
  | set h hd => simp [localCheck?, htyOk' _ _ hΔ hr h, hd]
  | unset h hd => simp [localCheck?, htyOk' _ _ hΔ hr h, hd]

theorem localsCheck?_complete_wf
    (htyOk' : ∀ Δ {k} (t : Ty k), Δ.Ok → Δ.recs = [] → TyOk Δ t → tyOk Δ t = true)
    {C : Context} (hΔ : C.toTypeCtx.Ok) (hr : C.recs = []) {ts : List ValType}
    {lts : List LocalType} (h : List.Forall₂ (LocalOk C) ts lts) :
    localsCheck? tyOk C ts = some lts := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [localsCheck?, localCheck?_complete_wf htyOk' hΔ hr h, ih]

/-- The body context of a function is well-formed. -/
theorem Context.Wf.funcBody {C : Context} (hC : C.Wf) {ps rs : List CValType}
    {lts : List LocalType} (hps : ResultOk C.toTypeCtx ps) (hrs : ResultOk C.toTypeCtx rs)
    (hl : ∀ lt ∈ lts, TyOk C.toTypeCtx lt.type) : (C.funcBody ps rs lts).Wf := by
  refine ⟨hC.types, hC.tags, hC.globals, hC.tables, hC.funcs, ?_, ?_, ?_, hC.elems⟩
  · intro lt hlt
    simp only [Context.funcBody, List.mem_append, List.mem_map] at hlt
    rcases hlt with ⟨t, ht, rfl⟩ | hlt
    · exact hps t ht
    · exact hl lt hlt
  · intro ts hts
    simp only [Context.funcBody, List.mem_singleton] at hts
    subst hts; exact hrs
  · intro ts hts
    simp only [Context.funcBody, Option.some.injEq] at hts
    subst hts; exact hrs

theorem funcCheck_complete
    (htyOk' : ∀ Δ {k} (t : Ty k), Δ.Ok → Δ.recs = [] → TyOk Δ t → tyOk Δ t = true)
    (hexpr' : ∀ C e ts, C.Wf → C.recs = [] → ExprOk C e ts → exprOk C e ts = true)
    {C : Context} {f : Func} {d : DefType} :
    C.Wf → C.recs = [] → FuncOk C f d → funcCheck tyOk exprOk C f d = true := by
  intro hC hr h
  cases h with
  | @mk ps rs lts hd he hl hb =>
    obtain ⟨hps, hrs⟩ := Expand.func_ok (hC.type hd) he
    have hlts : localsCheck? tyOk C f.locals = some lts :=
      localsCheck?_complete_wf htyOk' hC.types hr hl
    have hlt : ∀ lt ∈ lts, TyOk C.toTypeCtx lt.type := locals_tyOk hl
    have hbody := hexpr' _ _ _ (hC.funcBody hps hrs hlt) hr hb
    simp [funcCheck, hd, Expand.iff.mp he, hlts, hbody]

end FuncComplete

end Silmaril.Wasm.Validation
