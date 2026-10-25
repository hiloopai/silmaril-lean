module

public import Silmaril.Wasm.Validation.Const
public import Silmaril.Wasm.Modules

@[expose] public section

/-! # Module validation (§2.4)

Rule-for-rule: `Type_ok`, `Types_ok` (sequential), `Tag_ok`, `Global_ok`,
`Globals_ok` (sequential), `Mem_ok`, `Table_ok`, `Local_ok`, `Func_ok`,
`Data_ok`/`Datamode_ok`, `Elem_ok`/`Elemmode_ok`, `Start_ok`, `Import_ok`,
`Export_ok`/`Externidx_ok`, `Module_ok`.

Closed types: `Type_ok` rolls the group at `x = |C.TYPES|` (`$rolldt`) and then
closes the result against the (closed) types so far, so the context only ever
holds closed defined types. By `closDefTypes_snoc` this is `$clos_deftypes` of
the spec's open `TYPES`.
-/

namespace Silmaril.Wasm.Validation

/-! ## Free function indices (`$funcidx_nonfuncs`) -/

/-- Function indices occurring in an instruction (`$free_instr(..).FUNCS`). -/
def Instr.freeFuncs : Instr → List Nat
  | .call x | .returnCall x | .refFunc x => [x.toNat]
  | .block _ body | .loop _ body | .tryTable _ _ body =>
      body.attach.flatMap (fun i => Instr.freeFuncs i.val)
  | .if_ _ b₁ b₂ =>
      b₁.attach.flatMap (fun i => Instr.freeFuncs i.val) ++
        b₂.attach.flatMap (fun i => Instr.freeFuncs i.val)
  | _ => []
termination_by i => sizeOf i
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem i.property
  all_goals omega

def Expr.freeFuncs (e : Expr) : List Nat := e.flatMap Instr.freeFuncs

/-- `$funcidx_nonfuncs(global* mem* table* elem* export*)`: the `REFS` of `Module_ok`. -/
def funcIdxNonFuncs (m : Module) : List Nat :=
  m.globals.flatMap (fun g => Expr.freeFuncs g.init) ++
  m.tables.flatMap (fun t => Expr.freeFuncs t.init) ++
  m.elems.flatMap (fun e => e.init.flatMap Expr.freeFuncs ++ match e.mode with
    | .active _ off => Expr.freeFuncs off
    | _ => []) ++
  m.exports.flatMap (fun e => match e.index with
    | .func x => [x.toNat]
    | _ => [])

/-! ## Closing module-level syntax -/

/-- `$rolldt(x, rectype)` at `x = |C.TYPES|`, closed against `C.TYPES`. -/
def Context.rollGroup (C : Context) (rt : RecType) : List DefType :=
  (rolldt C.types.length (liftRec rt)).map fun d => d.substAll (C.types.map .dt)

def Context.closeGlobalType (C : Context) (g : GlobalType) : CGlobalType :=
  ⟨g.mutability, C.closeVal g.value⟩

def Context.closeTableType (C : Context) (t : TableType) : CTableType :=
  ⟨t.address, t.limits, C.closeRef t.element⟩

/-- `$clos_externtype(C, xt)`; `none` when a type index is out of range. -/
def Context.closeExtern? (C : Context) : ExternType → Option CExternType
  | .tag x => (C.type? x).map .tag
  | .global g => some (.global (C.closeGlobalType g))
  | .memory m => some (.mem m)
  | .table t => some (.table (C.closeTableType t))
  | .func x => (C.type? x).map .func

/-! ## Definitions -/

/-- `Types_ok` with `Type_ok` inlined. -/
inductive TypesOk : Context → List RecType → List DefType → Prop where
  | nil {C : Context} : TypesOk C [] []
  | cons {C : Context} {rt : RecType} {rts : List RecType} {dts : List DefType}
      (hok : RecTypeOkAt { C with types := C.types ++ C.rollGroup rt } rt.types C.types.length)
      (hs : TypesOk { C with types := C.types ++ C.rollGroup rt } rts dts) :
      TypesOk C (rt :: rts) (C.rollGroup rt ++ dts)

/-- `Tag_ok`. -/
def TagOk (C : Context) (x : TagType) (d : DefType) : Prop :=
  C.type? x = some d ∧ TagTypeOk C.toTypeCtx d

/-- `Global_ok`. -/
def GlobalOk (C : Context) (g : Global) (gt : CGlobalType) : Prop :=
  gt = C.closeGlobalType g.type ∧ GlobalTypeOk C.toTypeCtx gt ∧ ExprOkConst C g.init gt.type

/-- `Globals_ok`: each global's initializer sees the globals before it. -/
inductive GlobalsOk : Context → List Global → List CGlobalType → Prop where
  | nil {C : Context} : GlobalsOk C [] []
  | cons {C : Context} {g : Global} {gs : List Global} {gt : CGlobalType}
      {gts : List CGlobalType}
      (h : GlobalOk C g gt) (hs : GlobalsOk { C with globals := C.globals ++ [gt] } gs gts) :
      GlobalsOk C (g :: gs) (gt :: gts)

/-- `Mem_ok`. -/
def MemOk (m : MemoryType) : Prop := MemTypeOk m

/-- `Table_ok`. -/
def TableOk (C : Context) (t : Table) (tt : CTableType) : Prop :=
  tt = C.closeTableType t.type ∧ TableTypeOk C.toTypeCtx tt ∧ ExprOkConst C t.init (.refv tt.element)

/-- `Local_ok`. -/
inductive LocalOk (C : Context) : ValType → LocalType → Prop where
  | set {t : ValType} (h : TyOk C.toTypeCtx (C.closeVal t)) (hd : Defaultable (C.closeVal t)) :
      LocalOk C t ⟨.set, C.closeVal t⟩
  | unset {t : ValType} (h : TyOk C.toTypeCtx (C.closeVal t)) (hd : ¬ Defaultable (C.closeVal t)) :
      LocalOk C t ⟨.unset, C.closeVal t⟩

/-- The body context of `Func_ok`. -/
def Context.funcBody (C : Context) (params results : List CValType) (lts : List LocalType) :
    Context :=
  { C with locals := params.map (⟨.set, ·⟩) ++ lts, labels := [results], return_ := some results }

/-- `Func_ok`. -/
inductive FuncOk (C : Context) : Func → DefType → Prop where
  | mk {f : Func} {d : DefType} {ps rs : Ty (.list .val)} {lts : List LocalType}
      (hd : C.type? f.type = some d) (he : Expand d (.func ps rs))
      (hl : List.Forall₂ (LocalOk C) f.locals lts)
      (hb : ExprOk (C.funcBody ps.toList rs.toList lts) f.body rs.toList) :
      FuncOk C f d

/-- `Datamode_ok`. -/
inductive DataModeOk (C : Context) : DataMode → Prop where
  | passive : DataModeOk C .passive
  | active {x : MemIdx} {off : Expr} {a : AddrType} {l : Limits}
      (h : C.mems[x.toNat]? = some ⟨a, l⟩) (ho : ExprOkConst C off a.valType) :
      DataModeOk C (.active x off)

/-- `Data_ok`. -/
def DataOk (C : Context) (d : Data) : Prop := DataModeOk C d.mode

/-- `Elemmode_ok`. -/
inductive ElemModeOk (C : Context) : ElemMode → CRefType → Prop where
  | passive {rt : CRefType} : ElemModeOk C .passive rt
  | declarative {rt : CRefType} : ElemModeOk C .declarative rt
  | active {x : TableIdx} {off : Expr} {rt : CRefType} {a : AddrType} {l : Limits}
      {rt' : CRefType}
      (h : C.tables[x.toNat]? = some ⟨a, l, rt'⟩) (hs : Sub C.toTypeCtx rt rt')
      (ho : ExprOkConst C off a.valType) :
      ElemModeOk C (.active x off) rt

/-- `Elem_ok`. -/
def ElemOk (C : Context) (e : Elem) (rt : CRefType) : Prop :=
  rt = C.closeRef e.type ∧ TyOk C.toTypeCtx rt ∧ (∀ ex ∈ e.init, ExprOkConst C ex (.refv rt)) ∧
    ElemModeOk C e.mode rt

/-- `Start_ok`. -/
def StartOk (C : Context) (x : FuncIdx) : Prop :=
  ∃ d, C.funcs[x.toNat]? = some d ∧ Expand d (.func .nil .nil)

/-- `Import_ok`. -/
def ImportOk (C : Context) (im : Import) (xt : CExternType) : Prop :=
  C.closeExtern? im.type = some xt ∧ ExternTypeOk C.toTypeCtx xt

/-- `Externidx_ok`. -/
inductive ExternIdxOk (C : Context) : ExternIdx → CExternType → Prop where
  | tag {x : TagIdx} {d : DefType} (h : C.tags[x.toNat]? = some d) : ExternIdxOk C (.tag x) (.tag d)
  | global {x : GlobalIdx} {g : CGlobalType} (h : C.globals[x.toNat]? = some g) :
      ExternIdxOk C (.global x) (.global g)
  | mem {x : MemIdx} {m : MemoryType} (h : C.mems[x.toNat]? = some m) :
      ExternIdxOk C (.memory x) (.mem m)
  | table {x : TableIdx} {t : CTableType} (h : C.tables[x.toNat]? = some t) :
      ExternIdxOk C (.table x) (.table t)
  | func {x : FuncIdx} {d : DefType} (h : C.funcs[x.toNat]? = some d) :
      ExternIdxOk C (.func x) (.func d)

/-- `Export_ok`. -/
def ExportOk (C : Context) (e : Export) (xt : CExternType) : Prop := ExternIdxOk C e.index xt

/-! ## Modules -/

/-- `Module_ok: ⊢ module : moduletype`. `C'` is the context of tags, globals,
memories and tables (imported globals and all functions); `C` adds the defined
entities, data and element segments. -/
inductive ModuleOk : Module → CModuleType → Prop where
  | mk {m : Module} {dts : List DefType} {xtI : List CExternType} {jts : List DefType}
      {gts : List CGlobalType} {tts : List CTableType} {fdts : List DefType}
      {rts : List CRefType} {xtE : List CExternType} {C' C : Context}
      (htypes : TypesOk {} m.types dts)
      (himports : List.Forall₂ (ImportOk { types := dts }) m.imports xtI)
      (hC' : C' = { types := dts, globals := CExternType.globals xtI,
                    funcs := CExternType.funcs xtI ++ fdts, refs := funcIdxNonFuncs m })
      (hC : C = { C' with
                  tags := CExternType.tags xtI ++ jts, globals := C'.globals ++ gts,
                  mems := CExternType.mems xtI ++ m.memories,
                  tables := CExternType.tables xtI ++ tts,
                  datas := m.data.map fun _ => (), elems := rts })
      (htags : List.Forall₂ (TagOk C') m.tags jts)
      (hglobals : GlobalsOk C' m.globals gts)
      (hmems : ∀ mt ∈ m.memories, MemOk mt)
      (htables : List.Forall₂ (TableOk C') m.tables tts)
      (hfuncs : List.Forall₂ (FuncOk C) m.funcs fdts)
      (hdata : ∀ d ∈ m.data, DataOk C d)
      (helems : List.Forall₂ (ElemOk C) m.elems rts)
      (hstart : ∀ x, m.start = some x → StartOk C x)
      (hexports : List.Forall₂ (ExportOk C) m.exports xtE)
      (hdisjoint : (m.exports.map Export.name).Nodup) :
      ModuleOk m ⟨xtI, xtE⟩

/-- A module is valid when it has a module type. -/
def ModuleValid (m : Module) : Prop := ∃ mt, ModuleOk m mt

/-! ## Proofs -/

theorem List.Forall₂.det' {α β : Type _} {R₁ R₂ : α → β → Prop}
    (hR : ∀ a b₁ b₂, R₁ a b₁ → R₂ a b₂ → b₁ = b₂) :
    ∀ {l : List α} {l₁ l₂ : List β}, List.Forall₂ R₁ l l₁ → List.Forall₂ R₂ l l₂ → l₁ = l₂
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h₁ hs₁, .cons h₂ hs₂ => by
    rw [hR _ _ _ h₁ h₂, List.Forall₂.det' hR hs₁ hs₂]

theorem TypesOk.det {C : Context} {rts : List RecType} {d₁ d₂ : List DefType}
    (h₁ : TypesOk C rts d₁) (h₂ : TypesOk C rts d₂) : d₁ = d₂ := by
  induction h₁ generalizing d₂ with
  | nil => cases h₂; rfl
  | cons _ _ ih => cases h₂ with
    | cons _ hs => rw [ih hs]

theorem GlobalsOk.det {C₁ C₂ : Context} {gs : List Global} {g₁ g₂ : List CGlobalType}
    (hT : C₁.types = C₂.types) (h₁ : GlobalsOk C₁ gs g₁) (h₂ : GlobalsOk C₂ gs g₂) :
    g₁ = g₂ := by
  induction h₁ generalizing C₂ g₂ with
  | nil => cases h₂; rfl
  | cons h _ ih => cases h₂ with
    | cons h' hs =>
      have e : _ = _ := h.1.trans (h'.1.trans (by simp [Context.closeGlobalType,
        Context.closeVal, hT])).symm
      subst e
      rw [ih (C₂ := { C₂ with globals := C₂.globals ++ [_] }) hT hs]

theorem ExternIdxOk.det {C : Context} {x : ExternIdx} {t₁ t₂ : CExternType}
    (h₁ : ExternIdxOk C x t₁) (h₂ : ExternIdxOk C x t₂) : t₁ = t₂ := by
  cases h₁ <;> cases h₂ <;> simp_all

/-- Module types are unique (validation is deterministic on types). -/
theorem ModuleOk.unique {m : Module} {mt₁ mt₂ : CModuleType}
    (h₁ : ModuleOk m mt₁) (h₂ : ModuleOk m mt₂) : mt₁ = mt₂ := by
  obtain ⟨ht₁, hi₁, rfl, rfl, hj₁, hg₁, -, htb₁, hf₁, -, he₁, -, hx₁, -⟩ := h₁
  obtain ⟨ht₂, hi₂, rfl, rfl, hj₂, hg₂, -, htb₂, hf₂, -, he₂, -, hx₂, -⟩ := h₂
  obtain rfl := TypesOk.det ht₁ ht₂
  obtain rfl := List.Forall₂.det' (fun _ _ _ a b => Option.some.inj (a.1.symm.trans b.1)) hi₁ hi₂
  obtain rfl := List.Forall₂.det' (fun _ _ _ a b => by
    cases a with | mk hd _ _ _ => cases b with | mk hd' _ _ _ =>
      exact Option.some.inj (hd.symm.trans hd')) hf₁ hf₂
  obtain rfl := List.Forall₂.det' (fun _ _ _ a b => Option.some.inj (a.1.symm.trans b.1)) hj₁ hj₂
  obtain rfl := GlobalsOk.det rfl hg₁ hg₂
  obtain rfl := List.Forall₂.det' (fun _ _ _ a b => a.1.trans b.1.symm) htb₁ htb₂
  obtain rfl := List.Forall₂.det' (fun _ _ _ a b => a.1.trans b.1.symm) he₁ he₂
  obtain rfl := List.Forall₂.det' (R₁ := ExportOk _) (R₂ := ExportOk _)
    (fun _ _ _ a b => ExternIdxOk.det a b) hx₁ hx₂
  rfl

mutual
theorem TyOk.freeIdx_lt : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k}, TyOk Δ t →
    ∀ y ∈ t.freeIdx, y < Δ.types.length
  | _, _, _, .idx h, y, hy => by
    simp only [Ty.freeIdx, List.mem_singleton] at hy
    subst hy
    exact (List.getElem?_eq_some_iff.1 h).1
  | _, _, _, .recv _, y, hy => by simp [Ty.freeIdx] at hy
  | _, _, _, .dt h, y, hy => TyOk.freeIdx_lt h y hy
  | _, _, _, .defn h _, y, hy => GroupOk2.freeIdx_lt h y hy
  | _, _, _, .abs _, y, hy => by simp [Ty.freeIdx] at hy
  | _, _, _, .bot, y, hy => by simp [Ty.freeIdx] at hy
  | _, _, _, .use h, y, hy => TyOk.freeIdx_lt h y hy
  | _, _, _, .ref h, y, hy => TyOk.freeIdx_lt h y hy
  | _, _, _, .num _, y, hy => by simp [Ty.freeIdx] at hy
  | _, _, _, .vec _, y, hy => by simp [Ty.freeIdx] at hy
  | _, _, _, .refv h, y, hy => TyOk.freeIdx_lt h y hy
  | _, _, _, .botv, y, hy => by simp [Ty.freeIdx] at hy
  | _, _, _, .val h, y, hy => TyOk.freeIdx_lt h y hy
  | _, _, _, .pack _, y, hy => by simp [Ty.freeIdx] at hy
  | _, _, _, .field h, y, hy => TyOk.freeIdx_lt h y hy
  | _, _, _, .struct h, y, hy => TyOk.freeIdx_lt h y hy
  | _, _, _, .array h, y, hy => TyOk.freeIdx_lt h y hy
  | _, _, _, .func hp hr, y, hy => by
    simp only [Ty.freeIdx, List.mem_append] at hy
    exact hy.elim (TyOk.freeIdx_lt hp y) (TyOk.freeIdx_lt hr y)
  | _, _, _, .nil, y, hy => by simp [Ty.freeIdx] at hy
  | _, _, _, .cons ha hl, y, hy => by
    simp only [Ty.freeIdx, List.mem_append] at hy
    exact hy.elim (TyOk.freeIdx_lt ha y) (TyOk.freeIdx_lt hl y)

theorem SubOk2.freeIdx_lt : ∀ {Δ : TypeCtx} {st : CSubType} {i : Nat}, SubOk2 Δ st i →
    ∀ y ∈ st.freeIdx, y < Δ.types.length
  | _, _, _, .noSuper hct, y, hy => by
    simp only [Ty.freeIdx, List.nil_append] at hy
    exact TyOk.freeIdx_lt hct y hy
  | _, _, _, .oneSuper hu _ _ hct _, y, hy => by
    simp only [Ty.freeIdx, List.append_nil, List.mem_append] at hy
    exact hy.elim (TyOk.freeIdx_lt hu y) (TyOk.freeIdx_lt hct y)

theorem GroupOk2.freeIdx_lt : ∀ {Δ : TypeCtx} {g : CRecType} {i : Nat}, GroupOk2 Δ g i →
    ∀ y ∈ g.freeIdx, y < Δ.types.length
  | _, _, _, .nil, y, hy => by simp [Ty.freeIdx] at hy
  | _, _, _, .cons h hs, y, hy => by
    simp only [Ty.freeIdx, List.mem_append] at hy
    exact hy.elim (SubOk2.freeIdx_lt h y) (GroupOk2.freeIdx_lt hs y)
end

theorem Context.length_rollGroup (C : Context) (rt : RecType) :
    (C.rollGroup rt).length = rt.types.length := by
  simp [Context.rollGroup, rolldt, rollrt, liftRec, Ty.subs, Ty.length_subst, Ty.length_ofList]

/-- A closed source composite type mentions only indices of the context. -/
theorem Context.freeIdx_liftComp_lt {C : Context} {ct : CompositeType}
    (h : TyOk C.toTypeCtx (C.closeComp ct)) : ∀ y ∈ (liftComp ct).freeIdx, y < C.types.length := by
  intro y hy
  by_contra hlt
  have hn : Subst.all (C.types.map .dt) (.idx y) = none := by
    simp [Subst.all]; omega
  exact hlt (TyOk.freeIdx_lt h y (Ty.freeIdx_subst_of_none _ _ y hy hn))

theorem SubTypeOkAt.freeIdx_lt {C : Context} {st : SubType} {x₀ : Nat}
    (h : SubTypeOkAt C st x₀) : ∀ y ∈ (liftSub st).freeIdx, y < C.types.length := by
  cases h with
  | noSuper hct =>
    intro y hy
    simp only [liftSub, Ty.freeIdx, List.map_nil, Ty.ofList_nil, List.nil_append] at hy
    exact Context.freeIdx_liftComp_lt hct y hy
  | oneSuper _ hd _ hct _ =>
    intro y hy
    simp only [liftSub, Ty.freeIdx, List.map_cons, List.map_nil, Ty.ofList_cons, Ty.ofList_nil,
      liftTypeIdx, List.append_nil, List.mem_append, List.mem_singleton] at hy
    rcases hy with rfl | hy
    · exact (List.getElem?_eq_some_iff.1 hd).1
    · exact Context.freeIdx_liftComp_lt hct y hy

theorem RecTypeOkAt.freeIdx_lt {C : Context} {sts : List SubType} {x : Nat}
    (h : RecTypeOkAt C sts x) : ∀ st ∈ sts, ∀ y ∈ (liftSub st).freeIdx, y < C.types.length := by
  induction h with
  | nil => simp
  | cons h _ ih =>
    intro st hst
    rcases List.mem_cons.1 hst with rfl | hst
    · exact h.freeIdx_lt
    · exact ih st hst

/-- Rolling a valid group against a closed context yields closed defined types. -/
theorem Context.rollGroup_closed {C : Context} {rt : RecType} (hC : ∀ d ∈ C.types, d.Closed)
    (hok : RecTypeOkAt { C with types := C.types ++ C.rollGroup rt } rt.types C.types.length) :
    ∀ d ∈ C.rollGroup rt, d.Closed := by
  have hb : ∀ y ∈ (liftRec rt).freeIdx, y < C.types.length + rt.types.length := by
    intro y hy
    simp only [liftRec, Ty.freeIdx, Ty.mem_freeIdx_ofList, List.mem_map] at hy
    obtain ⟨_, ⟨st, hst, rfl⟩, hy⟩ := hy
    have := hok.freeIdx_lt st hst y hy
    simpa [Context.length_rollGroup] using this
  intro d hd
  simp only [Context.rollGroup, rolldt, List.mem_map, List.mem_range] at hd
  obtain ⟨_, ⟨i, _, rfl⟩, rfl⟩ := hd
  unfold Ty.Closed
  apply List.eq_nil_iff_forall_not_mem.2
  intro y hy
  rcases Ty.freeIdx_subst _ _ (fun _ => rfl) y hy with ⟨hy, hn⟩ | ⟨x, _, u, hu, hy⟩
  · -- `y` is free in the rolled group and beyond the context
    have hge : C.types.length ≤ y := by
      simp only [Subst.all, List.getElem?_eq_none_iff, List.length_map] at hn
      exact hn
    simp only [Ty.freeIdx, liftRec, rollrt] at hy
    rcases Ty.freeIdx_subst _ _ (fun _ => rfl) y hy with ⟨hy', hn'⟩ | ⟨x, _, u, hu, hy'⟩
    · have := hb y (by simpa [liftRec, Ty.freeIdx] using hy')
      simp only [Ty.length_ofList, List.length_map] at hn'
      split at hn' <;> simp_all
    · simp only [Ty.length_ofList, List.length_map] at hu
      split at hu
      · simp only [Option.some.injEq] at hu; subst hu; simp [Ty.freeIdx] at hy'
      · simp at hu
  · simp only [Subst.all, List.getElem?_map, Option.map_eq_some_iff] at hu
    obtain ⟨d', hd', rfl⟩ := hu
    have := hC d' (List.mem_of_getElem? hd')
    simp only [Ty.freeIdx] at hy
    rw [show d'.freeIdx = [] from this] at hy
    simp at hy

/-- The closed `TYPES` of a valid module (what instantiation allocates). -/
theorem TypesOk.closed {C : Context} {rts : List RecType} {dts : List DefType}
    (hC : ∀ d ∈ C.types, d.Closed) (h : TypesOk C rts dts) : ∀ d ∈ dts, d.Closed := by
  induction h with
  | nil => simp
  | @cons C rt rts dts hok _ ih =>
    have hg := Context.rollGroup_closed hC hok
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact hg d hd
    · refine ih (fun d hd => ?_) d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact hC d hd
      · exact hg d hd

end Silmaril.Wasm.Validation
