module

public import Silmaril.Wasm.Validation.Check.ModuleDefs
public import Silmaril.Wasm.Validation.Instructions.Properties

@[expose] public section

/-! # Completeness of the per-definition module checkers

Completeness, with exact outputs, of the checkers in `Check/ModuleDefs.lean`,
relative to completeness of the oracles `tyOk` and `constOk` on well-formed
contexts without `RECS`.
-/

namespace Silmaril.Wasm.Validation

section ModuleDefsComplete

variable {tyOk : TypeCtx → {k : TKind} → Ty k → Bool}
  {constOk : Context → Expr → CValType → Bool}

theorem isTagComp_complete {ps : Ty (.list .val)} : isTagComp (.func ps .nil) = true := by
  cases ps <;> rfl

theorem isFuncComp_complete {ps rs : Ty (.list .val)} : isFuncComp (.func ps rs) = true := by
  cases ps <;> cases rs <;> rfl

section Complete

variable (htyOk' : ∀ Δ {k} (t : Ty k), Δ.Ok → Δ.recs = [] → TyOk Δ t → tyOk Δ t = true)

include htyOk'

theorem tagTypeCheck_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {d : DefType}
    (h : TagTypeOk Δ d) : tagTypeCheck tyOk Δ d = true := by
  obtain ⟨h1, ps, he⟩ := h
  simp [tagTypeCheck, htyOk' _ _ hΔ hr h1, Expand.iff.mp he, isTagComp_complete]

theorem globalTypeCheck_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {g : CGlobalType} (h : GlobalTypeOk Δ g) : globalTypeCheck tyOk Δ g = true :=
  htyOk' _ _ hΔ hr h

omit htyOk' in
theorem memTypeCheck_complete {m : MemoryType} (h : MemTypeOk m) : memTypeCheck m = true := by
  simpa [memTypeCheck, MemTypeOk] using h

theorem tableTypeCheck_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {t : CTableType} (h : TableTypeOk Δ t) : tableTypeCheck tyOk Δ t = true := by
  simp [tableTypeCheck, h.1, htyOk' _ _ hΔ hr h.2]

theorem externTypeCheck_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {xt : CExternType} (h : ExternTypeOk Δ xt) : externTypeCheck tyOk Δ xt = true := by
  cases h with
  | tag h => exact tagTypeCheck_complete htyOk' hΔ hr h
  | global h => exact globalTypeCheck_complete htyOk' hΔ hr h
  | mem h => exact memTypeCheck_complete h
  | table h => exact tableTypeCheck_complete htyOk' hΔ hr h
  | func h he =>
    simp [externTypeCheck, htyOk' _ _ hΔ hr h, Expand.iff.mp he, isFuncComp_complete]

theorem tagCheck?_complete {C : Context} {x : TagType} {d : DefType} :
    C.Wf → C.recs = [] → TagOk C x d → tagCheck? tyOk C x = some d := by
  intro hC hr ⟨hd, ht⟩
  simp [tagCheck?, hd, tagTypeCheck_complete htyOk' hC.types hr ht]

section Const

variable (hconst' : ∀ C e t, C.Wf → C.recs = [] → ExprOkConst C e t → constOk C e t = true)

include hconst'

theorem globalCheck?_complete {C : Context} {g : Global} {gt : CGlobalType} :
    C.Wf → C.recs = [] → GlobalOk C g gt → globalCheck? tyOk constOk C g = some gt := by
  rintro hC hr ⟨rfl, ht, hi⟩
  simp [globalCheck?, globalTypeCheck_complete htyOk' hC.types hr ht, hconst' _ _ _ hC hr hi]

omit htyOk' hconst' in
theorem Context.Wf.addGlobal {C : Context} (hC : C.Wf) {gt : CGlobalType}
    (hg : TyOk C.toTypeCtx gt.type) : ({ C with globals := C.globals ++ [gt] } : Context).Wf :=
  ⟨hC.types, hC.tags, fun g hg' => by
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hC.globals g hg'
    · exact hg, hC.tables, hC.funcs, hC.locals, hC.labels, hC.return_, hC.elems⟩

theorem globalsCheck?_complete {C : Context} {gs : List Global} {gts : List CGlobalType} :
    C.Wf → C.recs = [] → GlobalsOk C gs gts → globalsCheck? tyOk constOk C gs = some gts := by
  intro hC hr h
  induction h with
  | nil => rfl
  | cons hg _ ih =>
    have hg' := hg
    obtain ⟨_, ht, _⟩ := hg'
    simp [globalsCheck?, globalCheck?_complete htyOk' hconst' hC hr hg,
      ih (hC.addGlobal ht) hr]

omit htyOk' hconst' in
theorem memCheck_complete {mt : MemoryType} : MemOk mt → memCheck mt = true :=
  memTypeCheck_complete

theorem tableDefCheck?_complete {C : Context} {t : Table} {tt : CTableType} :
    C.Wf → C.recs = [] → TableOk C t tt → tableDefCheck? tyOk constOk C t = some tt := by
  rintro hC hr ⟨rfl, ht, hi⟩
  simp [tableDefCheck?, tableTypeCheck_complete htyOk' hC.types hr ht, hconst' _ _ _ hC hr hi]

omit htyOk' in
theorem dataModeCheck_complete {C : Context} {m : DataMode} :
    C.Wf → C.recs = [] → DataModeOk C m → dataModeCheck constOk C m = true := by
  intro hC hr h
  cases h with
  | passive => rfl
  | active h ho => simp [dataModeCheck, h, hconst' _ _ _ hC hr ho]

omit htyOk' in
theorem dataCheck_complete {C : Context} {d : Data} :
    C.Wf → C.recs = [] → DataOk C d → dataCheck constOk C d = true :=
  dataModeCheck_complete hconst'

omit htyOk' in
theorem elemModeCheck_complete {C : Context} {m : ElemMode} {rt : CRefType} :
    C.Wf → C.recs = [] → TyOk C.toTypeCtx rt → ElemModeOk C m rt →
    elemModeCheck constOk C m rt = true := by
  intro hC hr hrt h
  cases h with
  | passive => rfl
  | declarative => rfl
  | active h hs ho =>
    have hrt' := hC.tables _ (List.mem_of_getElem? h)
    simp [elemModeCheck, h, Sub.check_complete hC.types hr hs hrt hrt',
      hconst' _ _ _ hC hr ho]

theorem elemCheck?_complete {C : Context} {e : Elem} {rt : CRefType} :
    C.Wf → C.recs = [] → ElemOk C e rt → elemCheck? tyOk constOk C e = some rt := by
  rintro hC hr ⟨rfl, ht, hi, hm⟩
  have hall : (e.init.all fun ex => constOk C ex (.refv (C.closeRef e.type))) = true := by
    simp only [List.all_eq_true]
    exact fun ex hex => hconst' _ _ _ hC hr (hi ex hex)
  simp [elemCheck?, htyOk' _ _ hC.types hr ht, hall,
    elemModeCheck_complete hconst' hC hr ht hm]

end Const

end Complete

theorem startCheck_complete {C : Context} {x : FuncIdx} :
    C.Wf → C.recs = [] → StartOk C x → startCheck C x = true := by
  intro _ _ ⟨d, hd, he⟩
  simp [startCheck, hd, Expand.iff.mp he]

theorem importCheck?_complete
    (htyOk' : ∀ Δ {k} (t : Ty k), Δ.Ok → Δ.recs = [] → TyOk Δ t → tyOk Δ t = true)
    {C : Context} {im : Import} {xt : CExternType} :
    C.Wf → C.recs = [] → ImportOk C im xt → importCheck? tyOk C im = some xt := by
  intro hC hr ⟨hx, ht⟩
  simp [importCheck?, hx, externTypeCheck_complete htyOk' hC.types hr ht]

theorem externIdxCheck?_complete {C : Context} {ix : ExternIdx} {xt : CExternType}
    (h : ExternIdxOk C ix xt) : externIdxCheck? C ix = some xt := by
  cases h <;> simp [externIdxCheck?, *]

theorem exportCheck?_complete {C : Context} {e : Export} {xt : CExternType} :
    C.Wf → C.recs = [] → ExportOk C e xt → exportCheck? C e = some xt :=
  fun _ _ h => externIdxCheck?_complete h

end ModuleDefsComplete

end Silmaril.Wasm.Validation
