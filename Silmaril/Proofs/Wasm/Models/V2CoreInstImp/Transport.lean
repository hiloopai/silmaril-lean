module

public import Silmaril.Proofs.Wasm.Models.V2CoreInstImp.Progress

/-!
# Core import typing back to 2.0, at memories

Core types an external address of a store image by `Silmaril.Wasm.Execution.Core.ExternAddrOk`,
with Core's `Externtype_sub`. 2.0 has its own `ExternAddrOk`, with 2.0's `Externtype_sub`. This
file transports the first back to the second for memory imports, at every 2.0 store:

* `coreMems`, `coreTags` etc.: the components of `Store.toCore s`;
* `LimLe l₀ l`: the numeric content of `Limits_sub`, reflexive and transitive, implied by Core's
  `LimitsSub` (`limLe_of_limitsSub`);
* `mem_of_coreAddrOk`: a Core typing of `MEM a` at the image store names a 2.0 memory instance
  of `s` whose limits are `LimLe`-below the type's;
* `memImport_transport`: a memory import that Core types at the image of a 2.0 address is typed
  by 2.0 at that address.

The same holds for global and table imports (`globalImport_transport`, `tableImport_transport`).
Core's chains of `Externtype_sub` steps collapse (`ExternSub.trans`), and Core's subtyping between
two images of 2.0 value or reference types is equality (`V2Core.Reflect.toC_sub_toC`,
`refToC_sub'`), so a Core `Globaltype_sub` (`Tabletype_sub`) between images is 2.0's.

For stores with no function, every Core-typed address is a memory, a global or a table
(`mgt_addr`), so every import transports (`import_transport_noF`). Function imports are not
covered: they need Core's subtyping on defined types between images.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstImp

open Silmaril.Wasm.V2 Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation

variable {H : Type}

/-! ## The image store -/

theorem toCore_eq {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (h : Store.toCore s = some cs) :
    cs.tags = [] ∧ cs.globals = s.globals.map GlobalInst.toCore ∧
      cs.mems = s.mems.map MemInst.toCore ∧ cs.tables = s.tables.map TableInst.toCore ∧
      (s.funcs.mapM FuncInst.toCore) = some cs.funcs := by
  simp only [Store.toCore, Option.map_eq_some_iff] at h
  obtain ⟨fs, hfs, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, hfs⟩

/-! ## Limits -/

/-- The numeric content of `Limits_sub` on Core limits. -/
def LimLe (l₀ l : Silmaril.Wasm.Limits) : Prop :=
  l.min.val ≤ l₀.min.val ∧ ∀ m₂, l.max = some m₂ → ∃ m₁, l₀.max = some m₁ ∧ m₁.val ≤ m₂.val

theorem limLe_refl (l : Silmaril.Wasm.Limits) : LimLe l l :=
  ⟨Nat.le_refl _, fun m₂ h => ⟨m₂, h, Nat.le_refl _⟩⟩

theorem limLe_trans {a b c : Silmaril.Wasm.Limits} (h₁ : LimLe a b) (h₂ : LimLe b c) :
    LimLe a c := by
  refine ⟨Nat.le_trans h₂.1 h₁.1, fun m₃ hm₃ => ?_⟩
  obtain ⟨m₂, hm₂, hle₂⟩ := h₂.2 m₃ hm₃
  obtain ⟨m₁, hm₁, hle₁⟩ := h₁.2 m₂ hm₂
  exact ⟨m₁, hm₁, Nat.le_trans hle₁ hle₂⟩

theorem limLe_of_limitsSub {a b : Silmaril.Wasm.Limits}
    (h : Silmaril.Wasm.Validation.LimitsSub a b) : LimLe a b := by
  cases h with
  | max hn hm => exact ⟨hn, fun m h => ⟨_, rfl, hm m h⟩⟩
  | eps hn => exact ⟨hn, fun m h => absurd h (by simp)⟩

theorem widen32_val (n : Fin (2 ^ 32)) : (Silmaril.Wasm.V2.widen32 n).val = n.val := rfl

/-- `LimLe` on images is 2.0's `Limits_sub`. -/
theorem limits_sub_of_limLe {a b : Limits} (h : LimLe a.toCore b.toCore) : a.Sub b := by
  rw [Limits.sub_iff]
  refine ⟨h.1, fun m₂ hm₂ => ?_⟩
  obtain ⟨m₁, hm₁, hle⟩ := h.2 (Silmaril.Wasm.V2.widen32 m₂)
    (Option.map_eq_some_iff.2 ⟨m₂, Option.mem_def.1 hm₂, rfl⟩)
  have hm : ∃ m₁', a.max = some m₁' ∧ Silmaril.Wasm.V2.widen32 m₁' = m₁ := by
    simpa [Limits.toCore] using hm₁
  obtain ⟨m₁', ha, rfl⟩ := hm
  exact ⟨m₁', ha, hle⟩

/-! ## Memory addresses -/

/-- **A Core typing of `MEM a` at the image store** names a 2.0 memory instance whose limits are
below the typing's. -/
theorem mem_of_coreAddrOk {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Store.toCore s = some cs) {xa : Silmaril.Wasm.Execution.Core.ExternAddr}
    {xt : Silmaril.Wasm.Validation.CExternType}
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs xa xt) :
    ∀ a, xa = .mem a → ∃ mi, s.mems[a]? = some mi ∧ ∃ l, xt = .mem ⟨.i32, l⟩ ∧
      LimLe mi.type.limits.toCore l := by
  have hm := (toCore_eq hcs).2.2.1
  induction h with
  | tag _ => intro a h; cases h
  | global _ => intro a h; cases h
  | table _ => intro a h; cases h
  | func _ => intro a h; cases h
  | @mem a' cmi hcmi =>
    intro a ha
    cases ha
    rw [hm, List.getElem?_map, Option.map_eq_some_iff] at hcmi
    obtain ⟨mi, hmi, rfl⟩ := hcmi
    exact ⟨mi, hmi, _, rfl, limLe_refl _⟩
  | sub _ _ hs ih =>
    intro a ha
    obtain ⟨mi, hmi, l, rfl, hle⟩ := ih a ha
    cases hs with
    | mem hms =>
      cases hms with
      | mk hl => exact ⟨mi, hmi, _, rfl, limLe_trans hle (limLe_of_limitsSub hl)⟩

/-- **A memory import Core types at an image address is typed by 2.0 there.** -/
theorem memImport_transport {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Store.toCore s = some cs) {a : Nat} {mt : MemoryType}
    (hok : ExternType.Ok (.memory mt))
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs (.mem a) (.mem mt.toCore)) :
    ExternAddrOk s (.mem a) (.memory mt) := by
  obtain ⟨mi, hmi, l, hl, hle⟩ := mem_of_coreAddrOk hcs h a rfl
  have hl' : l = mt.limits.toCore := by
    simp only [MemoryType.toCore, Silmaril.Wasm.Validation.CExternType.mem.injEq,
      Silmaril.Wasm.MemoryType.mk.injEq, true_and] at hl
    exact hl.symm
  subst hl'
  exact .sub (.mem hmi) hok (.memory (limits_sub_of_limLe hle))

/-! ## Global addresses -/

/-- **A Core typing of `GLOBAL a` is a subtype of the instance's type**: Core's chain of
`Externtype_sub` steps collapses (`ExternSub.trans`). -/
theorem global_of_coreAddrOk {cs : Silmaril.Wasm.Execution.Core.Store H}
    {xa : Silmaril.Wasm.Execution.Core.ExternAddr} {xt : Silmaril.Wasm.Validation.CExternType}
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs xa xt) :
    ∀ a, xa = .global a → ∃ cgi, cs.globals[a]? = some cgi ∧
      (xt = .global cgi.type ∨ Silmaril.Wasm.Validation.ExternTypeOk {} xt) ∧
      Silmaril.Wasm.Validation.ExternSub {} (.global cgi.type) xt := by
  induction h with
  | tag _ => intro a h; cases h
  | @global a' cgi hcgi =>
    intro a ha
    cases ha
    exact ⟨cgi, hcgi, .inl rfl, Silmaril.Wasm.Validation.ExternSub.refl _ _⟩
  | mem _ => intro a h; cases h
  | table _ => intro a h; cases h
  | func _ => intro a h; cases h
  | sub _ hok hs ih =>
    intro a ha
    obtain ⟨cgi, hcgi, hmid, hsub⟩ := ih a ha
    refine ⟨cgi, hcgi, .inr hok, ?_⟩
    rcases hmid with rfl | hmok
    · exact hs
    · exact Silmaril.Wasm.Validation.ExternSub.trans
        Silmaril.Wasm.Validation.TypeCtx.ok_empty hmok hsub hs

/-- Core's `Globaltype_sub` between two images of 2.0 global types is equality. -/
theorem globalSub_toC {g₀ g : GlobalType}
    (h : Silmaril.Wasm.Validation.ExternSub {} (.global (ToCore.globalToC g₀))
      (.global (ToCore.globalToC g))) : g₀ = g := by
  obtain ⟨m₀, t₀⟩ := g₀
  obtain ⟨m, t⟩ := g
  cases h with
  | global hg =>
    cases hg with
    | const hs =>
      have e : t₀ = t :=
        Silmaril.Proofs.Wasm.Models.V2Core.Reflect.toC_sub_toC
          Silmaril.Wasm.Validation.TypeCtx.ok_empty rfl hs
      simp_all
    | var hs _ =>
      have e : t₀ = t :=
        Silmaril.Proofs.Wasm.Models.V2Core.Reflect.toC_sub_toC
          Silmaril.Wasm.Validation.TypeCtx.ok_empty rfl hs
      simp_all

/-- **A global import Core types at an image address is typed by 2.0 there.** -/
theorem globalImport_transport {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Store.toCore s = some cs) {a : Nat} {g : GlobalType}
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs (.global a) (.global (ToCore.globalToC g))) :
    ExternAddrOk s (.global a) (.global g) := by
  obtain ⟨cgi, hcgi, -, hsub⟩ := global_of_coreAddrOk h a rfl
  have hgl := (toCore_eq hcs).2.1
  rw [hgl, List.getElem?_map, Option.map_eq_some_iff] at hcgi
  obtain ⟨gi, hgi, rfl⟩ := hcgi
  have e : gi.type = g := globalSub_toC hsub
  exact e ▸ .global hgi

/-! ## Table addresses -/

/-- **A Core typing of `TABLE a` is a subtype of the instance's type** (the chain collapses). -/
theorem table_of_coreAddrOk {cs : Silmaril.Wasm.Execution.Core.Store H}
    {xa : Silmaril.Wasm.Execution.Core.ExternAddr} {xt : Silmaril.Wasm.Validation.CExternType}
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs xa xt) :
    ∀ a, xa = .table a → ∃ cti, cs.tables[a]? = some cti ∧
      (xt = .table cti.type ∨ Silmaril.Wasm.Validation.ExternTypeOk {} xt) ∧
      Silmaril.Wasm.Validation.ExternSub {} (.table cti.type) xt := by
  induction h with
  | tag _ => intro a h; cases h
  | global _ => intro a h; cases h
  | mem _ => intro a h; cases h
  | @table a' cti hcti =>
    intro a ha
    cases ha
    exact ⟨cti, hcti, .inl rfl, Silmaril.Wasm.Validation.ExternSub.refl _ _⟩
  | func _ => intro a h; cases h
  | sub _ hok hs ih =>
    intro a ha
    obtain ⟨cti, hcti, hmid, hsub⟩ := ih a ha
    refine ⟨cti, hcti, .inr hok, ?_⟩
    rcases hmid with rfl | hmok
    · exact hs
    · exact Silmaril.Wasm.Validation.ExternSub.trans
        Silmaril.Wasm.Validation.TypeCtx.ok_empty hmok hsub hs

/-- Core's `Tabletype_sub` between two images of 2.0 table types is 2.0's `Tabletype_sub`. -/
theorem tableSub_toC {t₀ t : TableType}
    (h : Silmaril.Wasm.Validation.ExternSub {} (.table (ToCore.tableToC t₀))
      (.table (ToCore.tableToC t))) : t₀.Sub t := by
  cases h with
  | table ht =>
    cases ht with
    | mk hl h₁ _ =>
      exact ⟨limits_sub_of_limLe (limLe_of_limitsSub hl),
        Silmaril.Proofs.Wasm.Models.V2Core.Reflect.refToC_sub'
          Silmaril.Wasm.Validation.TypeCtx.ok_empty rfl h₁⟩

/-- **A table import Core types at an image address is typed by 2.0 there.** -/
theorem tableImport_transport {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Store.toCore s = some cs) {a : Nat} {t : TableType}
    (hok : ExternType.Ok (.table t))
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs (.table a) (.table (ToCore.tableToC t))) :
    ExternAddrOk s (.table a) (.table t) := by
  obtain ⟨cti, hcti, -, hsub⟩ := table_of_coreAddrOk h a rfl
  have htb := (toCore_eq hcs).2.2.2.1
  rw [htb, List.getElem?_map, Option.map_eq_some_iff] at hcti
  obtain ⟨ti, hti, rfl⟩ := hcti
  exact .sub (.table hti) hok (.table (tableSub_toC hsub))

/-! ## Stores without functions or tables -/

/-- In a Core store with no tag or function, every typed address is a memory, a global or a
table. -/
theorem mgt_addr {cs : Silmaril.Wasm.Execution.Core.Store H} (ht : cs.tags = [])
    (hf : cs.funcs = [])
    {xa : Silmaril.Wasm.Execution.Core.ExternAddr} {xt : Silmaril.Wasm.Validation.CExternType}
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs xa xt) :
    (∃ a, xa = .mem a) ∨ (∃ a, xa = .global a) ∨ ∃ a, xa = .table a := by
  induction h with
  | tag h => exact absurd h (by simp [ht])
  | global _ => exact .inr (.inl ⟨_, rfl⟩)
  | mem _ => exact .inl ⟨_, rfl⟩
  | table _ => exact .inr (.inr ⟨_, rfl⟩)
  | func h => exact absurd h (by simp [hf])
  | sub _ _ _ ih => exact ih

/-- A 2.0 address whose image is `MEM a` is `MEM a`. -/
theorem eq_mem_of_toCore {xa : ExternAddr} {a : Nat} (h : xa.toCore = .mem a) : xa = .mem a := by
  cases xa <;> simp_all [ExternAddr.toCore]

/-- A 2.0 address whose image is `TABLE a` is `TABLE a`. -/
theorem eq_table_of_toCore {xa : ExternAddr} {a : Nat} (h : xa.toCore = .table a) :
    xa = .table a := by
  cases xa <;> simp_all [ExternAddr.toCore]

/-- A 2.0 address whose image is `GLOBAL a` is `GLOBAL a`. -/
theorem eq_global_of_toCore {xa : ExternAddr} {a : Nat} (h : xa.toCore = .global a) :
    xa = .global a := by
  cases xa <;> simp_all [ExternAddr.toCore]

/-- The Core closure of the image of a 2.0 global type is its closed image. -/
theorem closeGlobalType_toCore (C : Silmaril.Wasm.Validation.Context) (g : GlobalType) :
    C.closeGlobalType g.toCore = ToCore.globalToC g := by
  simp only [Silmaril.Wasm.Validation.Context.closeGlobalType, GlobalType.toCore,
    ToCore.globalToC, Silmaril.Wasm.Validation.Context.closeVal, Silmaril.Wasm.Validation.Ty.substAll]
  exact congrArg _ (ValType.subst_toC _ g.value)

/-- The memory case of `import_transport_noFT`. -/
theorem import_transport_mem {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Store.toCore s = some cs) {ft' : List FuncType} {C : Silmaril.Wasm.Validation.Context}
    {imp : Import} {it : ExternType} {ct : Silmaril.Wasm.Validation.CExternType} {a : Nat}
    (h₂ : ImportOk { types := ft' } imp it)
    (hc : Silmaril.Wasm.Validation.ImportOk C imp.toCore ct)
    (ha : Silmaril.Wasm.Execution.Core.ExternAddrOk cs (.mem a) ct) :
    ExternAddrOk s (.mem a) it := by
  obtain ⟨mi, -, l, rfl, -⟩ := mem_of_coreAddrOk hcs ha a rfl
  obtain ⟨hclose, -⟩ := hc
  obtain ⟨hit, hok⟩ := h₂
  cases hd : imp.desc with
  | memory mt =>
    have hct' : Silmaril.Wasm.Validation.CExternType.mem ⟨.i32, l⟩ = .mem mt.toCore := by
      simpa [Import.toCore, hd, ImportDesc.toCore, Silmaril.Wasm.Validation.Context.closeExtern?]
        using hclose.symm
    have hit' : it = .memory mt := by
      simpa [hd, Module.importType?] using hit.symm
    subst hit'
    exact memImport_transport hcs hok (hct' ▸ ha)
  | func x => simp [Import.toCore, hd, ImportDesc.toCore,
      Silmaril.Wasm.Validation.Context.closeExtern?] at hclose
  | table t => simp [Import.toCore, hd, ImportDesc.toCore,
      Silmaril.Wasm.Validation.Context.closeExtern?] at hclose
  | global t => simp [Import.toCore, hd, ImportDesc.toCore,
      Silmaril.Wasm.Validation.Context.closeExtern?] at hclose

/-- The global case of `import_transport_noFT`. -/
theorem import_transport_global {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Store.toCore s = some cs) {ft' : List FuncType} {C : Silmaril.Wasm.Validation.Context}
    {imp : Import} {it : ExternType} {ct : Silmaril.Wasm.Validation.CExternType} {a : Nat}
    (h₂ : ImportOk { types := ft' } imp it)
    (hc : Silmaril.Wasm.Validation.ImportOk C imp.toCore ct)
    (ha : Silmaril.Wasm.Execution.Core.ExternAddrOk cs (.global a) ct) :
    ExternAddrOk s (.global a) it := by
  obtain ⟨cgi, -, -, hsub⟩ := global_of_coreAddrOk ha a rfl
  obtain ⟨hclose, -⟩ := hc
  obtain ⟨hit, -⟩ := h₂
  cases hd : imp.desc with
  | global g =>
    have hct : ct = .global (ToCore.globalToC g) := by
      have e : Silmaril.Wasm.Validation.CExternType.global (C.closeGlobalType g.toCore) = ct := by
        simpa [Import.toCore, hd, ImportDesc.toCore,
          Silmaril.Wasm.Validation.Context.closeExtern?] using hclose
      rw [← e, closeGlobalType_toCore]
    have hit' : it = .global g := by
      simpa [hd, Module.importType?] using hit.symm
    subst hit' hct
    exact globalImport_transport hcs ha
  | memory mt =>
    have hct : ct = .mem mt.toCore := by
      simpa [Import.toCore, hd, ImportDesc.toCore, Silmaril.Wasm.Validation.Context.closeExtern?]
        using hclose.symm
    subst hct
    cases hsub
  | func x =>
    obtain ⟨d, -, rfl⟩ : ∃ d, C.type? x = some d ∧ Silmaril.Wasm.Validation.CExternType.func d = ct := by
      simpa [Import.toCore, hd, ImportDesc.toCore, Silmaril.Wasm.Validation.Context.closeExtern?]
        using hclose
    cases hsub
  | table t =>
    have hct : ct = .table (C.closeTableType t.toCore) := by
      simpa [Import.toCore, hd, ImportDesc.toCore, Silmaril.Wasm.Validation.Context.closeExtern?]
        using hclose.symm
    subst hct
    cases hsub

/-- The table case of `import_transport_noF`. -/
theorem import_transport_table {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Store.toCore s = some cs) {ft' : List FuncType} {C : Silmaril.Wasm.Validation.Context}
    {imp : Import} {it : ExternType} {ct : Silmaril.Wasm.Validation.CExternType} {a : Nat}
    (h₂ : ImportOk { types := ft' } imp it)
    (hc : Silmaril.Wasm.Validation.ImportOk C imp.toCore ct)
    (ha : Silmaril.Wasm.Execution.Core.ExternAddrOk cs (.table a) ct) :
    ExternAddrOk s (.table a) it := by
  obtain ⟨cti, -, -, hsub⟩ := table_of_coreAddrOk ha a rfl
  obtain ⟨hclose, -⟩ := hc
  obtain ⟨hit, hok⟩ := h₂
  cases hd : imp.desc with
  | table t =>
    have hct : ct = .table (ToCore.tableToC t) := by
      have e : Silmaril.Wasm.Validation.CExternType.table (C.closeTableType t.toCore) = ct := by
        simpa [Import.toCore, hd, ImportDesc.toCore,
          Silmaril.Wasm.Validation.Context.closeExtern?] using hclose
      rw [← e, Silmaril.Wasm.V2.Validation.closeTableType_toCore]
      rfl
    have hit' : it = .table t := by
      simpa [hd, Module.importType?] using hit.symm
    subst hit' hct
    exact tableImport_transport hcs hok ha
  | memory mt =>
    have hct : ct = .mem mt.toCore := by
      simpa [Import.toCore, hd, ImportDesc.toCore, Silmaril.Wasm.Validation.Context.closeExtern?]
        using hclose.symm
    subst hct
    cases hsub
  | func x =>
    obtain ⟨d, -, rfl⟩ : ∃ d, C.type? x = some d ∧ Silmaril.Wasm.Validation.CExternType.func d = ct := by
      simpa [Import.toCore, hd, ImportDesc.toCore, Silmaril.Wasm.Validation.Context.closeExtern?]
        using hclose
    cases hsub
  | global g =>
    have hct : ct = .global (C.closeGlobalType g.toCore) := by
      simpa [Import.toCore, hd, ImportDesc.toCore, Silmaril.Wasm.Validation.Context.closeExtern?]
        using hclose.symm
    subst hct
    cases hsub

/-- **One import, at a store with no function**: a 2.0-valid import whose image Core types at
the image of `xa` is typed by 2.0 at `xa`. -/
theorem import_transport_noF {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Store.toCore s = some cs) (hf : s.funcs = [])
    {ft' : List FuncType} {C : Silmaril.Wasm.Validation.Context} {imp : Import}
    {it : ExternType} {ct : Silmaril.Wasm.Validation.CExternType} {xa : ExternAddr}
    (h₂ : ImportOk { types := ft' } imp it)
    (hc : Silmaril.Wasm.Validation.ImportOk C imp.toCore ct)
    (ha : Silmaril.Wasm.Execution.Core.ExternAddrOk cs xa.toCore ct) : ExternAddrOk s xa it := by
  obtain ⟨htg, -, -, -, hfs⟩ := toCore_eq hcs
  have hfs' : cs.funcs = [] := by rw [hf] at hfs; exact (Option.some.inj hfs).symm
  rcases mgt_addr htg hfs' ha with ⟨a, hxa⟩ | ⟨a, hxa⟩ | ⟨a, hxa⟩
  · rw [eq_mem_of_toCore hxa]
    exact import_transport_mem hcs h₂ hc (hxa ▸ ha)
  · rw [eq_global_of_toCore hxa]
    exact import_transport_global hcs h₂ hc (hxa ▸ ha)
  · rw [eq_table_of_toCore hxa]
    exact import_transport_table hcs h₂ hc (hxa ▸ ha)

/-- Three `Forall₂`s over the import list, its images, the 2.0 and Core import types and the
address images combine elementwise. -/
theorem forall₂_combine {α β γ δ ε ζ : Type} {f : α → γ} {g : ε → ζ} {R₂ : α → β → Prop}
    {RC : γ → δ → Prop} {RA : ζ → δ → Prop} {RS : ε → β → Prop}
    (hstep : ∀ a b c e, R₂ a b → RC (f a) c → RA (g e) c → RS e b) :
    ∀ {as : List α} {bs : List β} {cs : List δ} {es : List ε}, List.Forall₂ R₂ as bs →
      List.Forall₂ RC (as.map f) cs → List.Forall₂ RA (es.map g) cs → List.Forall₂ RS es bs
  | [], [], [], [], .nil, _, _ => .nil
  | [], [], _ :: _, _, .nil, hc, _ => by cases hc
  | [], [], [], _ :: _, .nil, _, ha => by cases ha
  | _ :: _, _ :: _, [], _, .cons _ _, hc, _ => by cases hc
  | _ :: _, _ :: _, _ :: _, [], .cons _ _, _, ha => by cases ha
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons h₂ hs, .cons hc hcs, .cons ha has =>
    .cons (hstep _ _ _ _ h₂ hc ha) (forall₂_combine hstep hs hcs has)

end Silmaril.Proofs.Wasm.Models.V2CoreInstImp
