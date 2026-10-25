module

public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Obs
public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Const
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc

@[expose] public section

/-! # Instantiation of profile modules

A module without tables, element segments and tags whose global initialisers are
profile constants and whose data segments have constant offsets instantiates in
closed form (`inst_closed`, `inst_of_closed`): the initialisers' values (`gv`)
become temporary globals and then the module's globals, the functions follow the
store's, and the code is the data segments' initialisation followed by the start
call (`startCode`). The simulation context of two such instances is `mkCtx`.
-/

namespace Silmaril.Wasm.Binaryen.RUMESim

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

/-! ## Foreign stores from store typing -/

theorem refOk_lt {H : Type} {s : Store H} {r : Ref} {t : CRefType} (h : RefOk s r t) :
    refF s.funcs.length r := by
  induction h with
  | func h => exact (List.getElem?_eq_some_iff.1 h).1
  | extern _ _ ih => exact ih
  | sub _ _ _ ih => exact ih
  | _ => trivial

theorem valOk_valF {H : Type} {s : Store H} {v : Val} {t : CValType} (h : ValOk s v t) :
    valF s.funcs.length v := by
  cases h with
  | ref h => exact refOk_lt h
  | _ => trivial

theorem fieldValOk_fvF {H : Type} {s : Store H} {v : FieldVal} {t : CStorageType}
    (h : FieldValOk s v t) : fvF s.funcs.length v := by
  cases h with
  | val h => exact valOk_valF h
  | pack => trivial

theorem forall₂_mem_left'' {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b, R a b
  | _, _, .nil, _, h => by simp at h
  | _ :: _, b :: _, .cons hr t, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨b, hr⟩
    · exact forall₂_mem_left'' t a h

theorem externAddr_func_lt {H : Type} {s : Store H} {a : Nat} {xt : CExternType}
    (h : ExternAddrOk s (.func a) xt) : a < s.funcs.length := by
  generalize hx : (ExternAddr.func a) = xa at h
  induction h with
  | func h => cases hx; exact (List.getElem?_eq_some_iff.1 h).1
  | sub _ _ _ ih => exact ih hx
  | _ => cases hx

theorem externAddr_global_lt {H : Type} {s : Store H} {a : Nat} {xt : CExternType}
    (h : ExternAddrOk s (.global a) xt) : a < s.globals.length := by
  generalize hx : (ExternAddr.global a) = xa at h
  induction h with
  | global h => cases hx; exact (List.getElem?_eq_some_iff.1 h).1
  | sub _ _ _ ih => exact ih hx
  | _ => cases hx

/-- **A valid store is foreign** to everything allocated after it. -/
theorem storeF_of_storeOk {H : Type} {s : Store H} (hs : StoreOk s) :
    StoreF s.funcs.length s.globals.length s where
  tables ti hti r hr := refOk_lt ((hs.tables ti hti).2.2 r hr)
  elems ei hei r hr := refOk_lt ((hs.elems ei hei).2 r hr)
  structs si hsi fv hfv := by
    obtain ⟨fs, -, hf⟩ := hs.structs si hsi
    obtain ⟨t, ht⟩ := forall₂_mem_left'' hf fv hfv
    exact fieldValOk_fvF ht
  arrays ai hai fv hfv := by
    obtain ⟨ft, -, hf⟩ := hs.arrays ai hai
    exact fieldValOk_fvF (hf fv hfv)
  exns e he v hv := by
    obtain ⟨ti, ts, -, -, hf⟩ := hs.exns e he
    obtain ⟨t, ht⟩ := forall₂_mem_left'' hf v hv
    exact valOk_valF ht
  globals g hg := valOk_valF (hs.globals g hg).2
  funcs a ha fi hfi c hc := by
    cases hs.funcs fi (List.mem_of_getElem? hfi) with
    | wasm hdt hm hcode hf hsub =>
      cases hm with
      | mk htypes htags hglobals hfuncs =>
        refine ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
        · obtain ⟨d, hd⟩ := forall₂_mem_left'' hfuncs a' ha'
          exact externAddr_func_lt hd
        · obtain ⟨g, hg⟩ := forall₂_mem_left'' hglobals a' ha'
          exact externAddr_global_lt hg
    | host hdt he hcode => rw [hc] at hcode; cases hcode

/-- Two valid modules with the same types and imports have the same import types. -/
theorem moduleOk_xtI {N N' : Module} (ht : N.types = N'.types) (hi : N.imports = N'.imports)
    {xtI xtE xtI' xtE' : List CExternType} (h : ModuleOk N ⟨xtI, xtE⟩)
    (h' : ModuleOk N' ⟨xtI', xtE'⟩) : xtI = xtI' := by
  cases h with
  | mk htypes himports =>
    cases h' with
    | mk htypes' himports' =>
      rw [← ht] at htypes'
      have hd := TypesOk.det htypes htypes'
      subst hd
      rw [← hi] at himports'
      exact List.Forall₂.det' (fun im a b h1 h2 => by
        have := h1.1.symm.trans h2.1
        exact Option.some.inj this) himports himports'

/-! ### Instantiation of profile modules -/

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The initialisation of the data segments (`$rundata` of each). -/
def dataCode (N : Module) : List Admin :=
  expression ((List.range N.data.length).zip N.data |>.flatMap fun (i, d) => runData i d)

/-- The code an instantiation of a module without tables and element segments runs:
the data segments' initialisation, then its start call. -/
def startCode (N : Module) : List Admin :=
  dataCode N ++ match N.start with
  | some x => [.plain (.call x)]
  | none => []

/-- The global types `$instantiate` evaluates the initialisers at. -/
def gtys (N : Module) : List CGlobalType :=
  N.globals.map fun g =>
    ⟨g.type.mutability, (liftVal g.type.value).substAll ((allocTypes N.types).map .dt)⟩

/-- Code made of instructions that the module's code may contain unchanged is related
to itself. -/
theorem codeR_expression_simple {X : SimCtx} : ∀ {is : List Instr},
    (∀ i ∈ is, simpleI i = true) → CodeR X .ours (expression is) (expression is)
  | [], _ => .nil
  | i :: is, h => .cons (.plainO (.simple (h i (by simp))))
      (codeR_expression_simple fun j hj => h j (by simp [hj]))

/-- The data initialisation of a module whose active segments have constant offsets is
related to itself: it holds only constants, `memory.init` and `data.drop`. -/
theorem dataCode_rel {X : SimCtx} {N : Module}
    (hN : ∀ d ∈ N.data, ∀ x off, d.mode = .active x off → ∃ c, off = [.intConst .i32 c]) :
    CodeR X .ours (dataCode N) (dataCode N) := by
  unfold dataCode
  refine codeR_expression_simple fun i hi => ?_
  simp only [List.mem_flatMap] at hi
  obtain ⟨⟨j, d⟩, hjd, hi⟩ := hi
  have hd := hN d (List.of_mem_zip hjd).2
  simp only [runData] at hi
  split at hi
  · simp at hi
  · next y off hm =>
    obtain ⟨c, rfl⟩ := hd y off hm
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem inst_data {N : Module} (ht : N.tables = []) (he : N.elems = [])
    {s : Store H} {xas : List ExternAddr} {c : Config H} (h : Instantiate P host s N xas c) :
    ∃ s₁ f₁ valsG s₄ mi, evalGlobals? evalConst? s ⟨[], ModuleInst.initial s N xas⟩ (gtys N)
        (N.globals.map Global.init) = some (s₁, f₁, valsG) ∧
      allocModule? s₁ N xas valsG [] [] = some (s₄, mi) ∧
      c = ⟨s₄, { module := mi }, startCode N⟩ := by
  obtain ⟨_, _, hmod, _⟩ := h.valid
  obtain ⟨hcG, -, -⟩ := hmod.initConst
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, hG, hT, hE, hM, rfl⟩ := h.run
  simp only [ht, List.map_nil] at hT
  cases hT
  simp only [he, List.map_nil] at hE
  cases hE
  refine ⟨s₁, f₁, valsG, s₄, mi, evalGlobals?_complete evalConst?_evalComplete hG hcG, hM, ?_⟩
  cases hs : N.start <;> simp [he, startCode, dataCode, expression, hs]

theorem inst_of_data {N : Module} (ht : N.tables = []) (he : N.elems = [])
    (hdb : ∀ d ∈ N.data, d.bytes.size < 2 ^ 32) (hdl : N.data.length ≤ 2 ^ 32)
    {s : Store H} {xas : List ExternAddr}
    (hvalid : ∃ xtE xtI, ModuleOk N ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    {s₁ : Store H} {f₁ : Frame} {valsG : List Val} {s₄ : Store H} {mi : ModuleInst}
    (hG : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s N xas⟩ (gtys N)
      (N.globals.map Global.init) = some (s₁, f₁, valsG))
    (hM : allocModule? s₁ N xas valsG [] [] = some (s₄, mi)) :
    Instantiate P host s N xas ⟨s₄, { module := mi }, startCode N⟩ := by
  refine ⟨hvalid, ⟨by simp [he], hdl, hdb, by simp [he]⟩, s₁, s₁, s₁, s₄, f₁, f₁, f₁, valsG, [], [], mi,
    evalGlobals?_sound evalConst?_evalSound hG, ?_, ?_, hM, ?_⟩
  · simp only [ht, List.map_nil]; exact .nil
  · simp only [he, List.map_nil]; exact .nil
  · cases hs : N.start <;> simp [he, startCode, dataCode, expression, hs]

theorem inst_det {N : Module} {s : Store H} {xas : List ExternAddr} {c₁ c₂ : Config H}
    (h₁ : Instantiate P host s N xas c₁) (h₂ : Instantiate P host s N xas c₂) : c₁ = c₂ := by
  have e₁ := instantiate?_evalConst_complete h₁
  have e₂ := instantiate?_evalConst_complete h₂
  rw [e₁] at e₂
  exact Option.some.inj e₂

theorem tmpStore_nil (s : Store H) : tmpStore s [] [] = s := by
  cases s; simp [tmpStore]

theorem tmpFrame_zero {mi : ModuleInst} (h : mi.globals = []) (g0 : Nat) :
    tmpFrame mi g0 0 = ⟨[], mi⟩ := by
  cases mi; simp_all [tmpFrame]

/-- Global initialisation of a profile module, in closed form. -/
theorem evalGlobals?_profile {s : Store H} {mi : ModuleInst} (hmi : mi.globals = [])
    {tys : List CGlobalType} {es : List Expr} (hl : tys.length = es.length)
    (hpc : ∀ e ∈ es, ∀ i ∈ e, pcI i) :
    evalGlobals? evalConst? s ⟨[], mi⟩ tys es = (gv [] es).map fun vals =>
      (tmpStore s tys vals, tmpFrame mi s.globals.length vals.length, vals) := by
  have h := evalGlobals?_env (s := s) (mi := mi) tys es [] [] hl rfl hpc
  simp only [tmpStore_nil, List.length_nil, tmpFrame_zero hmi, List.nil_append,
    List.drop_zero] at h
  exact h

/-- Exports related by name and kind, with related function addresses. -/
def XRel (F : Nat → Nat → Prop) (a b : ExportInst) : Prop :=
  a.name = b.name ∧ ((∃ x y, a.addr = .func x ∧ b.addr = .func y ∧ F x y) ∨
    ((∀ x, a.addr ≠ .func x) ∧ (∀ y, b.addr ≠ .func y)))

theorem exportFunc?_rel {F : Nat → Nat → Prop} :
    ∀ {la lb : List ExportInst}, List.Forall₂ (XRel F) la lb → ∀ (x : String),
      (∀ a, exportFunc? { exports := la } x = some a →
        ∃ b, exportFunc? { exports := lb } x = some b ∧ F a b) ∧
      (∀ b, exportFunc? { exports := lb } x = some b → ∃ a, exportFunc? { exports := la } x = some a)
  | [], [], .nil, x => ⟨fun a h => by simp [exportFunc?] at h, fun b h => by simp [exportFunc?] at h⟩
  | ea :: la, eb :: lb, .cons hr t, x => by
    obtain ⟨ih1, ih2⟩ := exportFunc?_rel t x
    obtain ⟨hn, hk⟩ := hr
    by_cases hx : ea.name = x
    · have hx' : eb.name = x := hn ▸ hx
      rcases hk with ⟨a, b, ha, hb, hab⟩ | ⟨ha, hb⟩
      · obtain ⟨na, addra⟩ := ea
        obtain ⟨nb, addrb⟩ := eb
        simp only at hx hx' ha hb
        subst hx hx' ha hb
        refine ⟨fun a' h => ⟨b, by simp [exportFunc?], ?_⟩, fun _ _ => ⟨a, by simp [exportFunc?]⟩⟩
        simp [exportFunc?] at h
        subst h
        exact hab
      · refine ⟨fun a' h => ?_, fun b' h => ?_⟩
        · exfalso
          obtain ⟨n, addr⟩ := ea
          simp only at hx ha
          cases addr <;> simp_all [exportFunc?]
        · exfalso
          obtain ⟨n, addr⟩ := eb
          simp only at hx' hb
          cases addr <;> simp_all [exportFunc?]
    · have hx' : ¬ eb.name = x := hn ▸ hx
      have e1 : exportFunc? { exports := ea :: la } x = exportFunc? { exports := la } x := by
        simp [exportFunc?, hx]
      have e2 : exportFunc? { exports := eb :: lb } x = exportFunc? { exports := lb } x := by
        simp [exportFunc?, hx']
      rw [e1, e2]
      exact ⟨ih1, ih2⟩

theorem exportFunc?_exports (mi : ModuleInst) (x : String) :
    exportFunc? mi x = exportFunc? { exports := mi.exports } x := rfl

/-- Renamed exports allocate related export instances. -/
theorem mapM_allocExport_rel {F : Nat → Nat → Prop} (ρ : Ren) (kf kg : Nat → Bool)
    {EA EB : ModuleInst} (hm : EA.mems = EB.mems)
    (hf : ∀ x : FuncIdx, kf x.toNat = true → ∀ a, EA.funcs[x.toNat]? = some a →
      ∃ b, EB.funcs[(ρ.funcIdx x).toNat]? = some b ∧ F a b)
    (hg : ∀ x : GlobalIdx, kg x.toNat = true → ∀ a, EA.globals[x.toNat]? = some a →
      ∃ b, EB.globals[(ρ.globalIdx x).toNat]? = some b) :
    ∀ (es : List Export) {xiA : List ExportInst},
    (∀ e ∈ es, (∃ x, e.index = .func x ∧ kf x.toNat = true) ∨
      (∃ x, e.index = .global x ∧ kg x.toNat = true) ∨ (∃ x, e.index = .memory x)) →
    es.mapM (allocExport? EA) = some xiA →
    ∃ xiB, (es.map fun e => match e.index with
        | .func f => { e with index := .func (ρ.funcIdx f) }
        | .global g => { e with index := .global (ρ.globalIdx g) }
        | _ => e).mapM (allocExport? EB) = some xiB ∧ List.Forall₂ (XRel F) xiA xiB
  | [], xiA, _, h => by simp at h; subst h; exact ⟨[], rfl, .nil⟩
  | e :: es, xiA, he, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨xa, hxa, xiA', hxiA', rfl⟩ := h
    obtain ⟨xiB, hB, hR⟩ := mapM_allocExport_rel ρ kf kg hm hf hg es (fun e' h' => he e' (by simp [h']))
      hxiA'
    obtain ⟨name, idx⟩ := e
    rcases he ⟨name, idx⟩ (by simp) with ⟨x, hx, hk⟩ | ⟨x, hx, hk⟩ | ⟨x, hx⟩
    · simp only at hx
      subst hx
      simp only [allocExport?, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at hxa
      obtain ⟨a, ha, rfl⟩ := hxa
      obtain ⟨b, hb, hab⟩ := hf x hk a ha
      refine ⟨⟨name, .func b⟩ :: xiB, ?_, .cons ⟨rfl, .inl ⟨a, b, rfl, rfl, hab⟩⟩ hR⟩
      simp [List.mapM_cons, allocExport?, hb, hB]
    · simp only at hx
      subst hx
      simp only [allocExport?, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at hxa
      obtain ⟨a, ha, rfl⟩ := hxa
      obtain ⟨b, hb⟩ := hg x hk a ha
      refine ⟨⟨name, .global b⟩ :: xiB, ?_, .cons ⟨rfl, .inr ⟨by simp, by simp⟩⟩ hR⟩
      simp [List.mapM_cons, allocExport?, hb, hB]
    · simp only at hx
      subst hx
      simp only [allocExport?, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at hxa
      obtain ⟨a, ha, rfl⟩ := hxa
      have hb : EB.mems[x.toNat]? = some a := by rw [← hm]; exact ha
      refine ⟨⟨name, .mem a⟩ :: xiB, ?_, .cons ⟨rfl, .inr ⟨by simp, by simp⟩⟩ hR⟩
      simp [List.mapM_cons, allocExport?, hb, hB]



/-- `allocModule?` succeeds when its function types and exports resolve. -/
theorem allocModule?_some {s : Store H} {m : Module} {xas : List ExternAddr} {valsG : List Val}
    {refsT : List Ref} {refsE : List (List Ref)} {tagTypes funcTypes : List DefType}
    {xi : List ExportInst}
    (ht : m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) = some tagTypes)
    (hf : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some funcTypes)
    (hx : m.exports.mapM (allocExport?
        { tags := ExternAddr.tags xas ++ List.range' s.tags.length tagTypes.length,
          globals := ExternAddr.globals xas ++ List.range' s.globals.length
            (min m.globals.length valsG.length),
          mems := ExternAddr.mems xas ++ List.range' s.mems.length m.memories.length,
          tables := ExternAddr.tables xas ++ List.range' s.tables.length
            (min m.tables.length refsT.length),
          funcs := ExternAddr.funcs xas ++
            (List.range m.funcs.length).map (s.funcs.length + ·) }) = some xi) :
    ∃ p, allocModule? s m xas valsG refsT refsE = some p := by
  unfold allocModule?
  simp only [Option.bind_eq_bind]
  cases ht' : m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) with
  | none => rw [ht] at ht'; cases ht'
  | some tagTypes' =>
  rw [ht] at ht'
  cases ht'
  cases hf' : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) with
  | none => rw [hf] at hf'; cases hf'
  | some funcTypes' =>
  rw [hf] at hf'
  cases hf'
  simp only [Option.bind_some, allocMany_tag_eq, allocMany_global_eq, allocMany_mem_eq,
    allocMany_table_eq, allocMany_data_eq, allocMany_elem_eq]
  simp [allocMany_func_eq, hx]

/-- The exports' view of an instance of a profile module (`$allocmodule` before exports). -/
def EIrec (s : Store H) (N : Module) (xas : List ExternAddr) (vals : List Val) : ModuleInst :=
  { tags := ExternAddr.tags xas ++
      List.range' (tmpStore s (gtys N) vals).tags.length ([] : List DefType).length,
    globals := ExternAddr.globals xas ++ List.range' (tmpStore s (gtys N) vals).globals.length
      (min N.globals.length vals.length),
    mems := ExternAddr.mems xas ++
      List.range' (tmpStore s (gtys N) vals).mems.length N.memories.length,
    tables := ExternAddr.tables xas ++ List.range' (tmpStore s (gtys N) vals).tables.length
      (min N.tables.length ([] : List Ref).length),
    funcs := ExternAddr.funcs xas ++
      (List.range N.funcs.length).map ((tmpStore s (gtys N) vals).funcs.length + ·) }

/-- The module instance of a profile module. -/
def MIrec (s : Store H) (N : Module) (xas : List ExternAddr) (vals : List Val)
    (xi : List ExportInst) : ModuleInst :=
  { types := allocTypes N.types,
    tags := ExternAddr.tags xas ++
      List.range' (tmpStore s (gtys N) vals).tags.length ([] : List DefType).length,
    globals := ExternAddr.globals xas ++ List.range' (tmpStore s (gtys N) vals).globals.length
      (min N.globals.length vals.length),
    mems := ExternAddr.mems xas ++
      List.range' (tmpStore s (gtys N) vals).mems.length N.memories.length,
    tables := ExternAddr.tables xas ++ List.range' (tmpStore s (gtys N) vals).tables.length
      (min N.tables.length ([] : List Ref).length),
    funcs := ExternAddr.funcs xas ++
      (List.range N.funcs.length).map ((tmpStore s (gtys N) vals).funcs.length + ·),
    datas := List.range' (tmpStore s (gtys N) vals).datas.length N.data.length,
    elems := List.range' (tmpStore s (gtys N) vals).elems.length
      (min N.elems.length ([] : List (List Ref)).length),
    exports := xi }

/-- The store after instantiating a profile module. -/
def STrec (s : Store H) (N : Module) (vals : List Val) (ft : List DefType) (mi : ModuleInst) :
    Store H :=
  let s₁ := tmpStore s (gtys N) vals
  { s₁ with
    tags := s₁.tags ++ ([] : List DefType).map TagInst.mk,
    globals := s₁.globals ++ ((gtys N).zip vals).map (fun p => ⟨p.1, p.2⟩),
    mems := s₁.mems ++ N.memories.map fun m =>
      ⟨m, ByteArray.mk (Array.replicate (m.limits.min.val * Silmaril.Wasm.Execution.Memory.pageSize) 0)⟩,
    tables := s₁.tables ++
      ((N.tables.map fun t => (⟨t.type.address, t.type.limits,
        (liftRef t.type.element).substAll ((allocTypes N.types).map .dt)⟩ : CTableType)).zip
        ([] : List Ref)).map (fun p => ⟨p.1, List.replicate p.1.limits.min.val p.2⟩),
    datas := s₁.datas ++ (N.data.map Data.bytes).map DataInst.mk,
    elems := s₁.elems ++
      ((N.elems.map fun e => (liftRef e.type).substAll ((allocTypes N.types).map .dt)).zip
        ([] : List (List Ref))).map (fun p => ⟨p.1, p.2⟩),
    funcs := s₁.funcs ++ (ft.zip N.funcs).map fun p => ⟨p.1, mi, .wasm p.2⟩ }

/-- The facts a profile module needs to instantiate in closed form. -/
structure Profiled (N : Module) : Prop where
  tags : N.tags = []
  tables : N.tables = []
  elems : N.elems = []
  data : ∀ d ∈ N.data, d.bytes.size < 2 ^ 32 ∧
    ∀ x off, d.mode = .active x off → ∃ c, off = [.intConst .i32 c]
  dataLen : N.data.length ≤ 2 ^ 32
  pc : ∀ g ∈ N.globals, ∀ i ∈ g.init, pcI i

/-- **Closed form** of the instantiation of a profile module. -/
theorem inst_closed {N : Module} (hN : Profiled N) {s : Store H} {xas : List ExternAddr}
    (hxg : ExternAddr.globals xas = []) {c : Config H} (h : Instantiate P host s N xas c) :
    ∃ vals ft xi, gv [] (N.globals.map Global.init) = some vals ∧
      N.funcs.mapM (fun fn => (allocTypes N.types)[fn.type.toNat]?) = some ft ∧
      N.exports.mapM (allocExport? (EIrec s N xas vals)) = some xi ∧
      c = ⟨STrec s N vals ft (MIrec s N xas vals xi), { module := MIrec s N xas vals xi },
        startCode N⟩ := by
  obtain ⟨s₁, f₁, valsG, s₄, mi, hG, hM, rfl⟩ := inst_data hN.tables hN.elems h
  have hmi0 : (ModuleInst.initial s N xas).globals = [] := by simp [ModuleInst.initial, hxg]
  rw [evalGlobals?_profile hmi0 (by simp [gtys])
    (fun e he => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 he
      exact hN.pc g hg)] at hG
  obtain ⟨vals, hvals, hG'⟩ := Option.map_eq_some_iff.1 hG
  simp only [Prod.mk.injEq] at hG'
  obtain ⟨rfl, -, rfl⟩ := hG'
  obtain ⟨tagTypes, funcTypes, xi, ht, hf, hx, hmi, hs4⟩ := allocModule?_inv hM
  rw [hN.tags] at ht
  simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at ht
  subst ht
  refine ⟨vals, funcTypes, xi, hvals, hf, hx, ?_⟩
  subst hmi hs4
  rfl

/-- **Instantiation** of a profile module from closed-form data. -/
theorem inst_of_closed {N : Module} (hN : Profiled N) {s : Store H} {xas : List ExternAddr}
    (hxg : ExternAddr.globals xas = [])
    (hvalid : ∃ xtE xtI, ModuleOk N ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    {vals : List Val} {ft : List DefType} {xi : List ExportInst}
    (hvals : gv [] (N.globals.map Global.init) = some vals)
    (hf : N.funcs.mapM (fun fn => (allocTypes N.types)[fn.type.toNat]?) = some ft)
    (hx : N.exports.mapM (allocExport? (EIrec s N xas vals)) = some xi) :
    Instantiate P host s N xas
      ⟨STrec s N vals ft (MIrec s N xas vals xi), { module := MIrec s N xas vals xi },
        startCode N⟩ := by
  have hmi0 : (ModuleInst.initial s N xas).globals = [] := by simp [ModuleInst.initial, hxg]
  have hG := evalGlobals?_profile (s := s) hmi0 (tys := gtys N) (es := N.globals.map Global.init)
    (by simp [gtys]) (fun e he => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 he
      exact hN.pc g hg)
  rw [hvals, Option.map_some] at hG
  have ht : N.tags.mapM (fun x => (allocTypes N.types)[x.toNat]?) = some [] := by
    rw [hN.tags]; rfl
  obtain ⟨⟨s₄, mi⟩, hM⟩ := allocModule?_some (s := tmpStore s (gtys N) vals) (valsG := vals)
    (refsT := []) (refsE := []) ht hf hx
  have hres := inst_of_data (P := P) (host := host) hN.tables hN.elems
    (fun d hd => (hN.data d hd).1) hN.dataLen hvalid hG hM
  obtain ⟨tagTypes, funcTypes, xi', ht', hf', hx', hmi, hs4⟩ := allocModule?_inv hM
  rw [ht] at ht'
  cases ht'
  rw [hf] at hf'
  cases hf'
  have hx2 : N.exports.mapM (allocExport? (EIrec s N xas vals)) = some xi' := hx'
  rw [hx] at hx2
  cases hx2
  subst hmi hs4
  exact hres

/-! ### The simulation context of two instances -/

/-- The context relating two instances through index relations. -/
abbrev mkCtx (n0 g0 : Nat) (KF KG : Nat → Nat → Prop) (MA MB : ModuleInst) : SimCtx where
  n0 := n0
  g0 := g0
  F a b := ∃ x y, KF x y ∧ MA.funcs[x]? = some a ∧ MB.funcs[y]? = some b
  G a b := ∃ x y, KG x y ∧ MA.globals[x]? = some a ∧ MB.globals[y]? = some b
  KF := KF
  KG := KG
  MA := MA
  MB := MB

theorem nodup_getElem?_inj {l : List Nat} (hl : l.Nodup) {x x' a : Nat} (h : l[x]? = some a)
    (h' : l[x']? = some a) : x = x' := by
  obtain ⟨hx, rfl⟩ := List.getElem?_eq_some_iff.1 h
  obtain ⟨hx', e⟩ := List.getElem?_eq_some_iff.1 h'
  exact (List.Nodup.getElem_inj_iff hl).1 e.symm

theorem mkCtx_wf {n0 g0 : Nat} {KF KG : Nat → Nat → Prop} {MA MB : ModuleInst}
    (htypes : MA.types = MB.types) (hmems : MA.mems = MB.mems)
    (hdatas : MA.datas = MB.datas)
    (hkf : ∀ x y a, KF x y → MA.funcs[x]? = some a → ∃ b, MB.funcs[y]? = some b)
    (hkg : ∀ x y a, KG x y → MA.globals[x]? = some a → ∃ b, MB.globals[y]? = some b)
    (hfun : ∀ x y y', KG x y → KG x y' → y = y') (hinj : ∀ x x' y, KG x y → KG x' y → x = x')
    (hA : MA.globals.Nodup) (hB : MB.globals.Nodup) :
    (mkCtx n0 g0 KF KG MA MB).WF where
  types := htypes
  mems := hmems
  datas := hdatas
  kf x y a h ha := by
    obtain ⟨b, hb⟩ := hkf x y a h ha
    exact ⟨b, hb, x, y, h, ha, hb⟩
  kg x y a h ha := by
    obtain ⟨b, hb⟩ := hkg x y a h ha
    exact ⟨b, hb, x, y, h, ha, hb⟩
  gfun a b b' h h' := by
    obtain ⟨x, y, hxy, ha, hb⟩ := h
    obtain ⟨x', y', hxy', ha', hb'⟩ := h'
    have := nodup_getElem?_inj hA ha ha'
    subst this
    have := hfun _ _ _ hxy hxy'
    subst this
    rw [hb] at hb'
    exact Option.some.inj hb'
  ginj a a' b h h' := by
    obtain ⟨x, y, hxy, ha, hb⟩ := h
    obtain ⟨x', y', hxy', ha', hb'⟩ := h'
    have := nodup_getElem?_inj hB hb hb'
    subst this
    have := hinj _ _ _ hxy hxy'
    subst this
    rw [ha] at ha'
    exact Option.some.inj ha'

/-- Related export lists, read backwards. -/
theorem xrel_flip {F : Nat → Nat → Prop} :
    ∀ {la lb : List ExportInst}, List.Forall₂ (XRel F) la lb →
      List.Forall₂ (XRel fun b a => F a b) lb la
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons ⟨hn, hk⟩ t => by
    refine .cons ⟨hn.symm, ?_⟩ (xrel_flip t)
    rcases hk with ⟨x, y, hx, hy, hxy⟩ | ⟨hx, hy⟩
    · exact .inl ⟨y, x, hy, hx, hxy⟩
    · exact .inr ⟨hy, hx⟩

/-- Related exports of two instances. -/
theorem exportsRel_of {X : SimCtx} (h : List.Forall₂ (XRel X.F) X.MA.exports X.MB.exports) :
    ExportsRel X :=
  ⟨fun x a ha => (exportFunc?_rel h x).1 a ha, fun x b hb => (exportFunc?_rel h x).2 b hb⟩

end Silmaril.Wasm.Binaryen.RUMESim
