module

public import Silmaril.Wasm.Validation.Modules
public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # Checkers for per-definition module judgments

Computable checkers, with soundness, for `TagOk`, `GlobalOk`, `GlobalsOk`, `MemOk`,
`TableOk`, `DataOk`, `ElemOk`, `StartOk`, `ImportOk` and `ExportOk`
(`Validation/Modules.lean`). `TypesOk`, `LocalOk` and `FuncOk` are handled elsewhere.

The checkers are parametrised over two oracles, curried first:
* `tyOk : TypeCtx → {k : TKind} → Ty k → Bool`, sound for `TyOk`;
* `constOk : Context → Expr → CValType → Bool`, sound for `ExprOkConst`.

Completeness is not claimed.
-/

namespace Silmaril.Wasm.Validation

section ModuleDefs

variable (tyOk : TypeCtx → {k : TKind} → Ty k → Bool)
  (constOk : Context → Expr → CValType → Bool)

/-! ## Local deciders for the non-recursive type judgments -/

/-- Is the composite type a function type with no results? -/
def isTagComp : CCompType → Bool
  | .func _ .nil => true
  | _ => false

theorem isTagComp_sound : {ct : CCompType} → isTagComp ct = true → ∃ ps, ct = .func ps .nil
  | .func ps .nil, _ => ⟨ps, rfl⟩
  | .func _ (.cons _ _), h => by simp [isTagComp] at h
  | .struct _, h => by simp [isTagComp] at h
  | .array _, h => by simp [isTagComp] at h

/-- Is the composite type a function type? -/
def isFuncComp : CCompType → Bool
  | .func _ _ => true
  | _ => false

theorem isFuncComp_sound : {ct : CCompType} → isFuncComp ct = true → ∃ ps rs, ct = .func ps rs
  | .func ps rs, _ => ⟨ps, rs, rfl⟩
  | .struct _, h => by simp [isFuncComp] at h
  | .array _, h => by simp [isFuncComp] at h

def tagTypeCheck (Δ : TypeCtx) (d : DefType) : Bool :=
  tyOk Δ d && (d.expand?.map isTagComp).getD false

def globalTypeCheck (Δ : TypeCtx) (g : CGlobalType) : Bool := tyOk Δ g.type

def memTypeCheck (m : MemoryType) : Bool := decide m.Valid

def tableTypeCheck (Δ : TypeCtx) (t : CTableType) : Bool :=
  decide (t.limits.Valid (2 ^ t.address.width - 1)) && tyOk Δ t.element

def externTypeCheck (Δ : TypeCtx) : CExternType → Bool
  | .tag d => tagTypeCheck tyOk Δ d
  | .global g => globalTypeCheck tyOk Δ g
  | .mem m => memTypeCheck m
  | .table t => tableTypeCheck tyOk Δ t
  | .func d => tyOk Δ d && (d.expand?.map isFuncComp).getD false

/-! ## Checkers -/

/-- `Tag_ok`. -/
def tagCheck? (C : Context) (x : TagType) : Option DefType :=
  match C.type? x with
  | some d => if tagTypeCheck tyOk C.toTypeCtx d then some d else none
  | none => none

/-- `Global_ok`. -/
def globalCheck? (C : Context) (g : Global) : Option CGlobalType :=
  if globalTypeCheck tyOk C.toTypeCtx (C.closeGlobalType g.type) &&
      constOk C g.init (C.closeGlobalType g.type).type then some (C.closeGlobalType g.type)
  else none

/-- `Globals_ok`. -/
def globalsCheck? : Context → List Global → Option (List CGlobalType)
  | _, [] => some []
  | C, g :: gs =>
    match globalCheck? tyOk constOk C g with
    | some gt =>
      match globalsCheck? { C with globals := C.globals ++ [gt] } gs with
      | some gts => some (gt :: gts)
      | none => none
    | none => none

/-- `Mem_ok`. -/
def memCheck (m : MemoryType) : Bool := memTypeCheck m

/-- `Table_ok`. -/
def tableDefCheck? (C : Context) (t : Table) : Option CTableType :=
  if tableTypeCheck tyOk C.toTypeCtx (C.closeTableType t.type) &&
      constOk C t.init (.refv (C.closeTableType t.type).element) then some (C.closeTableType t.type)
  else none

/-- `Datamode_ok`. -/
def dataModeCheck (C : Context) : DataMode → Bool
  | .passive => true
  | .active x off =>
    match C.mems[x.toNat]? with
    | some m => constOk C off m.address.valType
    | none => false

/-- `Data_ok`. -/
def dataCheck (C : Context) (d : Data) : Bool := dataModeCheck constOk C d.mode

/-- `Elemmode_ok`. -/
def elemModeCheck (C : Context) : ElemMode → CRefType → Bool
  | .passive, _ => true
  | .declarative, _ => true
  | .active x off, rt =>
    match C.tables[x.toNat]? with
    | some tt => Sub.check C.toTypeCtx rt tt.element && constOk C off tt.address.valType
    | none => false

/-- `Elem_ok`. -/
def elemCheck? (C : Context) (e : Elem) : Option CRefType :=
  if tyOk C.toTypeCtx (C.closeRef e.type) &&
      e.init.all (fun ex => constOk C ex (.refv (C.closeRef e.type))) &&
      elemModeCheck constOk C e.mode (C.closeRef e.type) then some (C.closeRef e.type)
  else none

/-- `Start_ok`. -/
def startCheck (C : Context) (x : FuncIdx) : Bool :=
  match C.funcs[x.toNat]? with
  | some d => decide (d.expand? = some (.func .nil .nil))
  | none => false

/-- `Import_ok`. -/
def importCheck? (C : Context) (im : Import) : Option CExternType :=
  match C.closeExtern? im.type with
  | some xt => if externTypeCheck tyOk C.toTypeCtx xt then some xt else none
  | none => none

/-- `Externidx_ok` by lookup. -/
def externIdxCheck? (C : Context) : ExternIdx → Option CExternType
  | .tag x => C.tags[x.toNat]?.map .tag
  | .global x => C.globals[x.toNat]?.map .global
  | .memory x => C.mems[x.toNat]?.map .mem
  | .table x => C.tables[x.toNat]?.map .table
  | .func x => C.funcs[x.toNat]?.map .func

/-- `Export_ok`. -/
def exportCheck? (C : Context) (e : Export) : Option CExternType := externIdxCheck? C e.index

/-! ## Soundness -/

variable {tyOk} {constOk}

section Sound

variable (htyOk : ∀ Δ {k} (t : Ty k), tyOk Δ t = true → TyOk Δ t)
  (hconst : ∀ C e t, constOk C e t = true → ExprOkConst C e t)

include htyOk

theorem tagTypeCheck_sound {Δ : TypeCtx} {d : DefType} (h : tagTypeCheck tyOk Δ d = true) :
    TagTypeOk Δ d := by
  unfold tagTypeCheck at h
  simp only [Bool.and_eq_true] at h
  refine ⟨htyOk _ _ h.1, ?_⟩
  obtain ⟨_, h2⟩ := h
  cases hx : d.expand? with
  | none => simp [hx] at h2
  | some ct =>
    rw [hx] at h2
    obtain ⟨ps, rfl⟩ := isTagComp_sound (by simpa using h2)
    exact ⟨ps, Expand.iff.mpr hx⟩

theorem globalTypeCheck_sound {Δ : TypeCtx} {g : CGlobalType}
    (h : globalTypeCheck tyOk Δ g = true) : GlobalTypeOk Δ g := htyOk _ _ h

omit htyOk in
theorem memTypeCheck_sound {m : MemoryType} (h : memTypeCheck m = true) : MemTypeOk m := by
  simpa [memTypeCheck, MemTypeOk] using h

theorem tableTypeCheck_sound {Δ : TypeCtx} {t : CTableType}
    (h : tableTypeCheck tyOk Δ t = true) : TableTypeOk Δ t := by
  unfold tableTypeCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, htyOk _ _ h.2⟩

theorem externTypeCheck_sound {Δ : TypeCtx} {xt : CExternType}
    (h : externTypeCheck tyOk Δ xt = true) : ExternTypeOk Δ xt := by
  cases xt with
  | tag d => exact .tag (tagTypeCheck_sound htyOk h)
  | global g => exact .global (globalTypeCheck_sound htyOk h)
  | mem m => exact .mem (memTypeCheck_sound h)
  | table t => exact .table (tableTypeCheck_sound htyOk h)
  | func d =>
    simp only [externTypeCheck, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases hx : d.expand? with
    | none => simp [hx] at h2
    | some ct =>
      rw [hx] at h2
      obtain ⟨ps, rs, rfl⟩ := isFuncComp_sound (by simpa using h2)
      exact .func (htyOk _ _ h1) (Expand.iff.mpr hx)

theorem tagCheck?_sound {C : Context} {x : TagType} {d : DefType}
    (h : tagCheck? tyOk C x = some d) : TagOk C x d := by
  unfold tagCheck? at h
  split at h
  · rename_i d' hd
    split at h
    · cases h; exact ⟨hd, tagTypeCheck_sound htyOk (by assumption)⟩
    · cases h
  · cases h

include hconst

theorem globalCheck?_sound {C : Context} {g : Global} {gt : CGlobalType}
    (h : globalCheck? tyOk constOk C g = some gt) : GlobalOk C g gt := by
  unfold globalCheck? at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    exact ⟨rfl, globalTypeCheck_sound htyOk hc.1, hconst _ _ _ hc.2⟩
  · cases h

theorem globalsCheck?_sound :
    {C : Context} → {gs : List Global} → {gts : List CGlobalType} →
    globalsCheck? tyOk constOk C gs = some gts → GlobalsOk C gs gts
  | C, [], gts, h => by
    simp only [globalsCheck?, Option.some.injEq] at h
    subst h; exact .nil
  | C, g :: gs, gts, h => by
    simp only [globalsCheck?] at h
    split at h
    · rename_i gt hg
      split at h
      · rename_i gts' hs
        cases h
        exact .cons (globalCheck?_sound htyOk hconst hg) (globalsCheck?_sound hs)
      · cases h
    · cases h

omit htyOk hconst in
theorem memCheck_sound {m : MemoryType} (h : memCheck m = true) : MemOk m :=
  memTypeCheck_sound h

theorem tableDefCheck?_sound {C : Context} {t : Table} {tt : CTableType}
    (h : tableDefCheck? tyOk constOk C t = some tt) : TableOk C t tt := by
  unfold tableDefCheck? at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    exact ⟨rfl, tableTypeCheck_sound htyOk hc.1, hconst _ _ _ hc.2⟩
  · cases h

omit htyOk in
theorem dataModeCheck_sound {C : Context} {m : DataMode} (h : dataModeCheck constOk C m = true) :
    DataModeOk C m := by
  cases m with
  | passive => exact .passive
  | active x off =>
    simp only [dataModeCheck] at h
    split at h
    · rename_i mt hm
      exact .active (a := mt.address) (l := mt.limits) (by simpa using hm) (hconst _ _ _ h)
    · cases h

omit htyOk in
theorem dataCheck_sound {C : Context} {d : Data} (h : dataCheck constOk C d = true) :
    DataOk C d := dataModeCheck_sound hconst h

omit htyOk in
theorem elemModeCheck_sound {C : Context} {m : ElemMode} {rt : CRefType}
    (h : elemModeCheck constOk C m rt = true) : ElemModeOk C m rt := by
  cases m with
  | passive => exact .passive
  | declarative => exact .declarative
  | active x off =>
    simp only [elemModeCheck] at h
    split at h
    · rename_i tt ht
      simp only [Bool.and_eq_true] at h
      exact .active (a := tt.address) (l := tt.limits) (rt' := tt.element) (by simpa using ht)
        (Sub.check_sound h.1) (hconst _ _ _ h.2)
    · cases h

theorem elemCheck?_sound {C : Context} {e : Elem} {rt : CRefType}
    (h : elemCheck? tyOk constOk C e = some rt) : ElemOk C e rt := by
  unfold elemCheck? at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    exact ⟨rfl, htyOk _ _ h1, fun ex hex => hconst _ _ _ (h2 ex hex),
      elemModeCheck_sound hconst h3⟩
  · cases h

end Sound

theorem startCheck_sound {C : Context} {x : FuncIdx} (h : startCheck C x = true) :
    StartOk C x := by
  unfold startCheck at h
  split at h
  · rename_i d hd
    exact ⟨d, hd, Expand.iff.mpr (by simpa using h)⟩
  · cases h

theorem importCheck?_sound (htyOk : ∀ Δ {k} (t : Ty k), tyOk Δ t = true → TyOk Δ t)
    {C : Context} {im : Import} {xt : CExternType}
    (h : importCheck? tyOk C im = some xt) : ImportOk C im xt := by
  unfold importCheck? at h
  split at h
  · rename_i xt' hx
    split at h
    · cases h; exact ⟨hx, externTypeCheck_sound htyOk (by assumption)⟩
    · cases h
  · cases h

theorem externIdxCheck?_sound {C : Context} {ix : ExternIdx} {xt : CExternType}
    (h : externIdxCheck? C ix = some xt) : ExternIdxOk C ix xt := by
  cases ix with
  | tag x =>
    simp only [externIdxCheck?, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h; exact .tag hd
  | global x =>
    simp only [externIdxCheck?, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h; exact .global hd
  | memory x =>
    simp only [externIdxCheck?, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h; exact .mem hd
  | table x =>
    simp only [externIdxCheck?, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h; exact .table hd
  | func x =>
    simp only [externIdxCheck?, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h; exact .func hd

theorem exportCheck?_sound {C : Context} {e : Export} {xt : CExternType}
    (h : exportCheck? C e = some xt) : ExportOk C e xt := externIdxCheck?_sound h

end ModuleDefs

end Silmaril.Wasm.Validation
