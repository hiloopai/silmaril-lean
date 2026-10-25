module

public import Silmaril.Wasm.Execution.Core.Step.Aggregate
public import Silmaril.Wasm.Validation.Modules

@[expose] public section

/-! # Store typing and store extension (§7.0, §7.1 "Instances", "Store", "Store extension")

Rule-for-rule: `Taginst_ok`, `Globalinst_ok`, `Meminst_ok`, `Tableinst_ok`,
`Funcinst_ok`, `Datainst_ok`, `Eleminst_ok`, `Exportinst_ok`, `Structinst_ok`,
`Arrayinst_ok`, `Exninst_ok`, `Moduleinst_ok`, `Store_ok`, `ImmutReachable`,
`NotImmutReachable`, `Extend_*`, `Context_ok`.

Deviation (documented): `Funcinst_ok` in the spec only covers Wasm code; host
function instances have no rule, which would make every store containing a host
function ill-typed. `FuncInstOk.host` accepts a host function whose type is a
valid function type; the host's behaviour is constrained separately by
`HostOk` (`Soundness.lean`).

Deviation (documented): `Structinst_ok`/`Arrayinst_ok`
(spec/7.1-soundness.configurations.spectec:136-144) do not require the
instance's defined type to be closed. `StoreOk` adds the invariants
`structsClosed`/`arraysClosed` (`TyOk {} si.type`, `TyOk {} ai.type`). Every
instance allocated by `struct.new`/`array.new*` takes its type from the
module's (closed) type list, so the invariant is preserved; without it
`RefInstrOk.retype`, `callRef_inv` and `StateOk.redexSubOk` are false.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

def TagInstOk (ti : TagInst) : Prop := TagTypeOk {} ti.type

def GlobalInstOk (s : Store H) (gi : GlobalInst) : Prop :=
  GlobalTypeOk {} gi.type ∧ ValOk s gi.value gi.type.type

def MemInstOk (mi : MemInst) : Prop :=
  MemTypeOk mi.type ∧ mi.bytes.size = mi.type.limits.min.val * Memory.pageSize

def TableInstOk (s : Store H) (ti : TableInst) : Prop :=
  TableTypeOk {} ti.type ∧ ti.refs.length = ti.type.limits.min.val ∧
    ∀ r ∈ ti.refs, RefOk s r ti.type.element

def ElemInstOk (s : Store H) (ei : ElemInst) : Prop :=
  TyOk {} ei.type ∧ ∀ r ∈ ei.refs, RefOk s r ei.type

def ExportInstOk (s : Store H) (xi : ExportInst) : Prop := ∃ xt, ExternAddrOk s xi.addr xt

def StructInstOk (s : Store H) (si : StructInst) : Prop :=
  ∃ fs, Expand si.type (.struct fs) ∧
    List.Forall₂ (FieldValOk s) si.fields (fs.toList.map fieldStorage)

def ArrayInstOk (s : Store H) (ai : ArrayInst) : Prop :=
  ∃ ft, Expand ai.type (.array ft) ∧ ∀ fv ∈ ai.fields, FieldValOk s fv (fieldStorage ft)

def ExnInstOk (s : Store H) (e : ExnInst) : Prop :=
  ∃ ti ts, s.tags[e.tag]? = some ti ∧ Expand ti.type (.func ts .nil) ∧
    List.Forall₂ (ValOk s) e.fields ts.toList

/-- `Moduleinst_ok: s ⊢ moduleinst : context`.

Deviation (documented): SpecTec leaves `RECS` unconstrained; we require
`RECS = []` (module validation contexts always have empty `RECS`). With bogus
`RECS`, subtyping checked in a callee frame's context need not hold in `{}`, which
makes preservation of `return_call_ref` out of a frame false. -/
inductive ModuleInstOk (s : Store H) : ModuleInst → Context → Prop where
  | mk {mi : ModuleInst} {tags : List DefType} {globals : List CGlobalType}
      {mems : List MemoryType} {tables : List CTableType} {funcs : List DefType}
      {elems : List CRefType} {k : Nat}
      (htypes : ∀ d ∈ mi.types, TyOk {} d)
      (htags : List.Forall₂ (fun a t => ExternAddrOk s (.tag a) (.tag t)) mi.tags tags)
      (hglobals : List.Forall₂ (fun a g => ExternAddrOk s (.global a) (.global g)) mi.globals globals)
      (hfuncs : List.Forall₂ (fun a d => ExternAddrOk s (.func a) (.func d)) mi.funcs funcs)
      (hmems : List.Forall₂ (fun a m => ExternAddrOk s (.mem a) (.mem m)) mi.mems mems)
      (htables : List.Forall₂ (fun a t => ExternAddrOk s (.table a) (.table t)) mi.tables tables)
      (hdatas : ∀ a ∈ mi.datas, ∃ di, s.datas[a]? = some di)
      (helems : List.Forall₂ (fun a rt => ∃ ei, s.elems[a]? = some ei ∧ ElemInstOk s ei ∧
        ei.type = rt) mi.elems elems)
      (hexports : ∀ xi ∈ mi.exports, ExportInstOk s xi)
      (hdisjoint : (mi.exports.map ExportInst.name).Nodup)
      (hexportAddrs : ∀ xi ∈ mi.exports, xi.addr ∈ mi.tags.map .tag ++ mi.globals.map .global ++
        mi.mems.map .mem ++ mi.tables.map .table ++ mi.funcs.map .func)
      (hk : k ≤ mi.funcs.length) :
      ModuleInstOk s mi
        { types := mi.types, recs := [], tags := tags, globals := globals, mems := mems,
          tables := tables, funcs := funcs, datas := mi.datas.map fun _ => (), elems := elems,
          refs := List.range k }

theorem ModuleInstOk.recs_nil {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.recs = [] := by
  cases h; rfl

/-- `Funcinst_ok` (plus the host-function rule, see the module doc). -/
inductive FuncInstOk (s : Store H) : FuncInst H → Prop where
  | wasm {fi : FuncInst H} {C : Context} {code : Func} {d' : DefType}
      (hdt : TyOk {} fi.type) (hm : ModuleInstOk s fi.module C) (hcode : fi.code = .wasm code)
      (hf : FuncOk C code d') (hs : Sub C.toTypeCtx d' fi.type) : FuncInstOk s fi
  | host {fi : FuncInst H} {h : H} {ps rs : Ty (.list .val)}
      (hdt : TyOk {} fi.type) (he : Expand fi.type (.func ps rs)) (hcode : fi.code = .host h) :
      FuncInstOk s fi

/-- `ImmutReachable: fv_1 >>_s fv_2`. -/
inductive ImmutReachable (s : Store H) : FieldVal → FieldVal → Prop where
  | trans {a b c : FieldVal} (h₁ : ImmutReachable s a b) (h₂ : ImmutReachable s b c) :
      ImmutReachable s a c
  | refStruct {a i : Nat} {si : StructInst} {fs : Ty (.list .field)} {z : CStorageType}
      {fv : FieldVal} (hs : s.structs[a]? = some si) (he : Expand si.type (.struct fs))
      (hi : fs.toList[i]? = some (.field .const z)) (hfv : si.fields[i]? = some fv) :
      ImmutReachable s (.val (.ref (.struct a))) fv
  | refArray {a i : Nat} {ai : ArrayInst} {z : CStorageType} {fv : FieldVal}
      (hs : s.arrays[a]? = some ai) (he : Expand ai.type (.array (.field .const z)))
      (hfv : ai.fields[i]? = some fv) :
      ImmutReachable s (.val (.ref (.array a))) fv
  | refExn {a i : Nat} {e : ExnInst} {v : Val} (hs : s.exns[a]? = some e)
      (hv : e.fields[i]? = some v) :
      ImmutReachable s (.val (.ref (.exn a))) (.val v)
  | refExtern (r : Ref) : ImmutReachable s (.val (.ref (.extern r))) (.val (.ref r))

/-- `Store_ok`. -/
structure StoreOk (s : Store H) : Prop where
  tags : ∀ ti ∈ s.tags, TagInstOk ti
  globals : ∀ gi ∈ s.globals, GlobalInstOk s gi
  mems : ∀ mi ∈ s.mems, MemInstOk mi
  tables : ∀ ti ∈ s.tables, TableInstOk s ti
  funcs : ∀ fi ∈ s.funcs, FuncInstOk s fi
  elems : ∀ ei ∈ s.elems, ElemInstOk s ei
  structs : ∀ si ∈ s.structs, StructInstOk s si
  arrays : ∀ ai ∈ s.arrays, ArrayInstOk s ai
  exns : ∀ e ∈ s.exns, ExnInstOk s e
  acyclicStructs : ∀ a < s.structs.length,
    ¬ ImmutReachable s (.val (.ref (.struct a))) (.val (.ref (.struct a)))
  acyclicArrays : ∀ a < s.arrays.length,
    ¬ ImmutReachable s (.val (.ref (.array a))) (.val (.ref (.array a)))
  acyclicExns : ∀ a < s.exns.length,
    ¬ ImmutReachable s (.val (.ref (.exn a))) (.val (.ref (.exn a)))
  /-- Deviation: struct instance types are closed (not in `Structinst_ok`). -/
  structsClosed : ∀ si ∈ s.structs, TyOk {} si.type
  /-- Deviation: array instance types are closed (not in `Arrayinst_ok`). -/
  arraysClosed : ∀ ai ∈ s.arrays, TyOk {} ai.type

/-! ## Store extension -/

/-- Pointwise extension of a list of instances (new instances may be appended). -/
def ExtendsList {α : Type} (R : α → α → Prop) (l l' : List α) : Prop :=
  l.length ≤ l'.length ∧ ∀ (i : Nat) x, l[i]? = some x → ∃ y, l'[i]? = some y ∧ R x y

def ExtendTag (a b : TagInst) : Prop := a = b

def ExtendGlobal (a b : GlobalInst) : Prop :=
  a.type = b.type ∧ (a.type.mutability = .var ∨ a.value = b.value)

def ExtendMem (a b : MemInst) : Prop :=
  a.type.address = b.type.address ∧ a.type.limits.max = b.type.limits.max ∧
    a.type.limits.min.val ≤ b.type.limits.min.val ∧ a.bytes.size ≤ b.bytes.size

def ExtendTable (a b : TableInst) : Prop :=
  a.type.address = b.type.address ∧ a.type.limits.max = b.type.limits.max ∧
    a.type.element = b.type.element ∧
    a.type.limits.min.val ≤ b.type.limits.min.val ∧ a.refs.length ≤ b.refs.length

def ExtendFunc (a b : FuncInst H) : Prop :=
  a.type = b.type ∧ a.module = b.module ∧
    (∀ c, a.code = .wasm c → b.code = .wasm c) ∧ (∀ h, a.code = .host h → b.code = .host h)

def ExtendData (a b : DataInst) : Prop := a = b ∨ b.bytes = ByteArray.empty

def ExtendElem (a b : ElemInst) : Prop := a.type = b.type ∧ (a.refs = b.refs ∨ b.refs = [])

/-- `Extend_structinst`. The spec iterates `(mut? zt)*`, `fv*` and `fv'*` jointly, so both
field lists have the length of the expanded struct type. -/
def ExtendStruct (a b : StructInst) : Prop :=
  a.type = b.type ∧ ∃ fs, Expand a.type (.struct fs) ∧ a.fields.length = b.fields.length ∧
    a.fields.length = fs.toList.length ∧
    ∀ (i : Nat) fv, a.fields[i]? = some fv →
      (∃ z, fs.toList[i]? = some (Ty.field .var z)) ∨ b.fields[i]? = some fv

def ExtendArray (a b : ArrayInst) : Prop :=
  a.type = b.type ∧ ∃ m z, Expand a.type (.array (.field m z)) ∧ a.fields.length = b.fields.length ∧
    (m = .var ∨ a.fields = b.fields)

def ExtendExn (a b : ExnInst) : Prop := a = b

/-- `Extend_store: s ⪯ s'`. -/
structure Extend (s s' : Store H) : Prop where
  tags : ExtendsList ExtendTag s.tags s'.tags
  globals : ExtendsList ExtendGlobal s.globals s'.globals
  mems : ExtendsList ExtendMem s.mems s'.mems
  tables : ExtendsList ExtendTable s.tables s'.tables
  funcs : ExtendsList ExtendFunc s.funcs s'.funcs
  datas : ExtendsList ExtendData s.datas s'.datas
  elems : ExtendsList ExtendElem s.elems s'.elems
  structs : ExtendsList ExtendStruct s.structs s'.structs
  arrays : ExtendsList ExtendArray s.arrays s'.arrays
  exns : ExtendsList ExtendExn s.exns s'.exns

/-! ### Instance-level reflexivity and transitivity -/

theorem Expand.func_eq {d : DefType} {c₁ c₂ : CCompType} (h₁ : Expand d c₁) (h₂ : Expand d c₂) :
    c₁ = c₂ :=
  Option.some.inj ((Expand.iff.mp h₁).symm.trans (Expand.iff.mp h₂))

theorem ExtendsList.refl_of {α : Type} {R : α → α → Prop} {l : List α} (h : ∀ x ∈ l, R x x) :
    ExtendsList R l l :=
  ⟨Nat.le_refl _, fun _ x hx => ⟨x, hx, h x (List.mem_of_getElem? hx)⟩⟩

theorem ExtendsList.trans_of {α : Type} {R : α → α → Prop} {l₁ l₂ l₃ : List α}
    (hR : ∀ x y z, R x y → R y z → R x z)
    (h₁ : ExtendsList R l₁ l₂) (h₂ : ExtendsList R l₂ l₃) : ExtendsList R l₁ l₃ := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun i x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := h₁.2 i x hx
  obtain ⟨z, hz, hyz⟩ := h₂.2 i y hy
  exact ⟨z, hz, hR _ _ _ hxy hyz⟩

theorem ExtendsList.get {α : Type} {R : α → α → Prop} {l l' : List α} (h : ExtendsList R l l')
    {i : Nat} {x : α} (hx : l[i]? = some x) : ∃ y, l'[i]? = some y ∧ R x y := h.2 i x hx

theorem ExtendStruct.trans' {a b c : StructInst} (h₁ : ExtendStruct a b) (h₂ : ExtendStruct b c) :
    ExtendStruct a c := by
  obtain ⟨hab, fs, he, hl, hlf, hf⟩ := h₁
  obtain ⟨hbc, fs', he', hl', _, hf'⟩ := h₂
  rw [← hab] at he'
  have hfs : fs' = fs := by
    have := Expand.func_eq he he'
    cases this; rfl
  subst hfs
  refine ⟨hab.trans hbc, fs', he, hl.trans hl', hlf, fun i fv h => ?_⟩
  rcases hf i fv h with hz | hb
  · exact .inl hz
  · exact hf' i fv hb

theorem ExtendArray.trans' {a b c : ArrayInst} (h₁ : ExtendArray a b) (h₂ : ExtendArray b c) :
    ExtendArray a c := by
  obtain ⟨hab, m, z, he, hl, hm⟩ := h₁
  obtain ⟨hbc, m', z', he', hl', hm'⟩ := h₂
  rw [← hab] at he'
  have hmz : m' = m ∧ z' = z := by
    have := Expand.func_eq he he'
    cases this; exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hmz
  refine ⟨hab.trans hbc, m', z', he, hl.trans hl', ?_⟩
  rcases hm with hv | hf
  · exact .inl hv
  · rcases hm' with hv | hf'
    · exact .inl hv
    · exact .inr (hf.trans hf')

/-- Reflexivity of store extension. Needs `StoreOk s`: `Extend_structinst` and
`Extend_arrayinst` require the instance type to expand to a struct/array type,
which only a typed store guarantees. (Fixed statement: the skeleton had no
hypothesis, which is false for ill-typed stores.) -/
theorem Extend.refl {s : Store H} (hs : StoreOk s) : Extend s s where
  tags := ExtendsList.refl_of fun _ _ => rfl
  globals := ExtendsList.refl_of fun _ _ => ⟨rfl, .inr rfl⟩
  mems := ExtendsList.refl_of fun _ _ => ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  tables := ExtendsList.refl_of fun _ _ => ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  funcs := ExtendsList.refl_of fun _ _ => ⟨rfl, rfl, fun _ h => h, fun _ h => h⟩
  datas := ExtendsList.refl_of fun _ _ => .inl rfl
  elems := ExtendsList.refl_of fun _ _ => ⟨rfl, .inl rfl⟩
  structs := ExtendsList.refl_of fun si hsi => by
    obtain ⟨fs, he, hf⟩ := hs.structs si hsi
    exact ⟨rfl, fs, he, rfl, by simpa using hf.length_eq, fun _ _ h => .inr h⟩
  arrays := ExtendsList.refl_of fun ai hai => by
    obtain ⟨ft, he, _⟩ := hs.arrays ai hai
    match ft, he with
    | .field m z, he => exact ⟨rfl, m, z, he, rfl, .inr rfl⟩
  exns := ExtendsList.refl_of fun _ _ => rfl

theorem Extend.trans {s₁ s₂ s₃ : Store H} (h₁ : Extend s₁ s₂) (h₂ : Extend s₂ s₃) :
    Extend s₁ s₃ where
  tags := ExtendsList.trans_of (fun _ _ _ h h' => h.trans h') h₁.tags h₂.tags
  globals := ExtendsList.trans_of (fun _ _ _ h h' => ⟨h.1.trans h'.1, by
      rcases h.2 with hv | hv
      · exact .inl hv
      · rcases h'.2 with hv' | hv'
        · exact .inl (by rw [h.1]; exact hv')
        · exact .inr (hv.trans hv')⟩) h₁.globals h₂.globals
  mems := ExtendsList.trans_of (fun _ _ _ h h' => ⟨h.1.trans h'.1, h.2.1.trans h'.2.1,
      Nat.le_trans h.2.2.1 h'.2.2.1, Nat.le_trans h.2.2.2 h'.2.2.2⟩) h₁.mems h₂.mems
  tables := ExtendsList.trans_of (fun _ _ _ h h' => ⟨h.1.trans h'.1, h.2.1.trans h'.2.1,
      h.2.2.1.trans h'.2.2.1, Nat.le_trans h.2.2.2.1 h'.2.2.2.1,
      Nat.le_trans h.2.2.2.2 h'.2.2.2.2⟩) h₁.tables h₂.tables
  funcs := ExtendsList.trans_of (fun _ _ _ h h' => ⟨h.1.trans h'.1, h.2.1.trans h'.2.1,
      fun c hc => h'.2.2.1 c (h.2.2.1 c hc), fun c hc => h'.2.2.2 c (h.2.2.2 c hc)⟩)
      h₁.funcs h₂.funcs
  datas := ExtendsList.trans_of (fun a b c h h' => by
      rcases h' with rfl | hc
      · exact h
      · exact .inr hc) h₁.datas h₂.datas
  elems := ExtendsList.trans_of (fun a b c h h' => ⟨h.1.trans h'.1, by
      rcases h'.2 with hr | hr
      · rw [← hr]; exact h.2
      · exact .inr hr⟩) h₁.elems h₂.elems
  structs := ExtendsList.trans_of (fun _ _ _ h h' => h.trans' h') h₁.structs h₂.structs
  arrays := ExtendsList.trans_of (fun _ _ _ h h' => h.trans' h') h₁.arrays h₂.arrays
  exns := ExtendsList.trans_of (fun _ _ _ h h' => h.trans h') h₁.exns h₂.exns

/-- Typing of values is stable under store extension. -/
theorem RefOk.extend {s s' : Store H} {r : Ref} {rt : CRefType} (he : Extend s s')
    (h : RefOk s r rt) : RefOk s' r rt := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h =>
    obtain ⟨si', h', hx⟩ := he.structs.get h
    have := RefOk.struct (s := s') h'
    rwa [← hx.1] at this
  | array h =>
    obtain ⟨ai', h', hx⟩ := he.arrays.get h
    have := RefOk.array (s := s') h'
    rwa [← hx.1] at this
  | func h =>
    obtain ⟨fi', h', hx⟩ := he.funcs.get h
    have := RefOk.func (s := s') h'
    rwa [← hx.1] at this
  | exn h =>
    obtain ⟨e', h', _⟩ := he.exns.get h
    exact .exn h'
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem ValOk.extend {s s' : Store H} {v : Val} {t : CValType} (he : Extend s s')
    (h : ValOk s v t) : ValOk s' v t := by
  cases h with
  | num v => exact .num v
  | vec b => exact .vec b
  | ref h => exact .ref (h.extend he)

theorem ValOk.forall₂_extend {s s' : Store H} {vs : List Val} {ts : List CValType}
    (he : Extend s s') (h : List.Forall₂ (ValOk s) vs ts) : List.Forall₂ (ValOk s') vs ts :=
  h.imp fun _ _ h => h.extend he

theorem FieldValOk.extend {s s' : Store H} {v : FieldVal} {t : CStorageType} (he : Extend s s')
    (h : FieldValOk s v t) : FieldValOk s' v t := by
  cases h with
  | val h => exact .val (h.extend he)
  | pack p b => exact .pack p b

theorem LimitsSub.of_grow {l l' : Limits} (hmax : l.max = l'.max) (hmin : l.min.val ≤ l'.min.val) :
    LimitsSub l' l := by
  rcases l with ⟨n, m⟩
  rcases l' with ⟨n', m'⟩
  simp only at hmax hmin
  subst hmax
  cases m with
  | none => exact .eps hmin
  | some m => exact .max hmin (fun _ e => by cases e; exact Nat.le_refl _)

/-- An external address stays typed after store extension. Memories and tables may
grow, so the old type is recovered by subsumption, which needs its validity
(`StoreOk s`). -/
theorem ExternAddrOk.extend {s s' : Store H} {xa : ExternAddr} {xt : CExternType}
    (hs : StoreOk s) (he : Extend s s') (h : ExternAddrOk s xa xt) : ExternAddrOk s' xa xt := by
  induction h with
  | tag h =>
    obtain ⟨ti', h', hx⟩ := he.tags.get h
    cases hx; exact .tag h'
  | global h =>
    obtain ⟨gi', h', hx⟩ := he.globals.get h
    have := ExternAddrOk.global (s := s') h'
    rwa [← hx.1] at this
  | @mem a mi h =>
    obtain ⟨mi', h', ha, hmax, hmin, _⟩ := he.mems.get h
    refine .sub (.mem h') (.mem (hs.mems mi (List.mem_of_getElem? h)).1) (.mem ?_)
    rcases hmt : mi.type with ⟨at₁, l₁⟩
    rcases hmt' : mi'.type with ⟨at₂, l₂⟩
    rw [hmt, hmt'] at ha hmax hmin
    simp only at ha hmax hmin
    subst ha
    exact .mk (LimitsSub.of_grow hmax hmin)
  | @table a ti h =>
    obtain ⟨ti', h', ha, hmax, hel, hmin, _⟩ := he.tables.get h
    refine .sub (.table h') (.table (hs.tables ti (List.mem_of_getElem? h)).1) (.table ?_)
    rcases hmt : ti.type with ⟨at₁, l₁, r₁⟩
    rcases hmt' : ti'.type with ⟨at₂, l₂, r₂⟩
    rw [hmt, hmt'] at ha hmax hel hmin
    simp only at ha hmax hel hmin
    subst ha; subst hel
    exact .mk (LimitsSub.of_grow hmax hmin) (Sub.refl _ (k := .ref) trivial _)
      (Sub.refl _ (k := .ref) trivial _)
  | func h =>
    obtain ⟨fi', h', hx⟩ := he.funcs.get h
    have := ExternAddrOk.func (s := s') h'
    rwa [← hx.1] at this
  | sub _ hok hsub ih => exact .sub ih hok hsub

/-- The address of a typed external address exists after extension. -/
theorem ExternAddrOk.exists_type {s s' : Store H} {xa : ExternAddr} {xt : CExternType}
    (he : Extend s s') (h : ExternAddrOk s xa xt) : ∃ xt', ExternAddrOk s' xa xt' := by
  induction h with
  | tag h => obtain ⟨_, h', _⟩ := he.tags.get h; exact ⟨_, .tag h'⟩
  | global h => obtain ⟨_, h', _⟩ := he.globals.get h; exact ⟨_, .global h'⟩
  | mem h => obtain ⟨_, h', _⟩ := he.mems.get h; exact ⟨_, .mem h'⟩
  | table h => obtain ⟨_, h', _⟩ := he.tables.get h; exact ⟨_, .table h'⟩
  | func h => obtain ⟨_, h', _⟩ := he.funcs.get h; exact ⟨_, .func h'⟩
  | sub _ _ _ ih => exact ih

theorem ElemInstOk.extend {s s' : Store H} {ei ei' : ElemInst} (he : Extend s s')
    (hx : ExtendElem ei ei') (h : ElemInstOk s ei) : ElemInstOk s' ei' := by
  obtain ⟨ht, hr⟩ := hx
  refine ⟨ht ▸ h.1, fun r hr' => ?_⟩
  rw [← ht]
  rcases hr with hr | hr
  · rw [← hr] at hr'; exact (h.2 r hr').extend he
  · rw [hr] at hr'; cases hr'

/-- Module instances stay typed after store extension. -/
theorem ModuleInstOk.extend {s s' : Store H} {mi : ModuleInst} {C : Context} (hs : StoreOk s)
    (he : Extend s s') (h : ModuleInstOk s mi C) : ModuleInstOk s' mi C := by
  cases h with
  | mk htypes htags hglobals hfuncs hmems htables hdatas helems hexports hdisjoint hexportAddrs hk =>
    refine .mk htypes (htags.imp fun _ _ h => h.extend hs he)
      (hglobals.imp fun _ _ h => h.extend hs he) (hfuncs.imp fun _ _ h => h.extend hs he)
      (hmems.imp fun _ _ h => h.extend hs he) (htables.imp fun _ _ h => h.extend hs he)
      (fun a ha => ?_) (helems.imp fun _ _ h => ?_) (fun xi hxi => ?_) hdisjoint hexportAddrs hk
    · obtain ⟨di, hdi⟩ := hdatas a ha
      obtain ⟨di', h', _⟩ := he.datas.get hdi
      exact ⟨di', h'⟩
    · obtain ⟨ei, hei, hok, rfl⟩ := h
      obtain ⟨ei', h', hx⟩ := he.elems.get hei
      exact ⟨ei', h', hok.extend he hx, hx.1.symm⟩
    · obtain ⟨xt, hxt⟩ := hexports xi hxi
      exact hxt.exists_type he

/-! ## Contexts (§7.0) -/

/-- `Context_ok`. -/
def ContextOk (C : Context) : Prop :=
  (∀ i (d : DefType), C.types[i]? = some d → TyOk { types := C.types.take i } d) ∧
  (∀ i (st : CSubType), C.recs[i]? = some st → SubOk2 C.toTypeCtx st i) ∧
  (∀ d ∈ C.tags, TagTypeOk { types := C.types } d) ∧
  (∀ g ∈ C.globals, GlobalTypeOk { types := C.types } g) ∧
  (∀ m ∈ C.mems, MemTypeOk m) ∧
  (∀ t ∈ C.tables, TableTypeOk { types := C.types } t) ∧
  (∀ d ∈ C.funcs, TyOk { types := C.types } d ∧ ∃ ps rs, Expand d (.func ps rs)) ∧
  (∀ rt ∈ C.elems, TyOk { types := C.types } rt) ∧
  (∀ lt ∈ C.locals, TyOk { types := C.types } lt.type) ∧
  (∀ ts ∈ C.labels, ResultOk { types := C.types } ts) ∧
  (∀ ts, C.return_ = some ts → ResultOk { types := C.types } ts) ∧
  (∀ x ∈ C.refs, x < C.funcs.length)

end Silmaril.Wasm.Execution.Core
