module

public import Silmaril.Wasm.Component.Engine.Interface
public import Silmaril.Wasm.Component.Engine.Laws
public import Silmaril.Wasm.SingleThreaded.Interface
public import Silmaril.Wasm.SingleThreaded.Exec.Interp
public import Silmaril.Wasm.Validation.Check.ValidateFinal
public import Silmaril.Wasm.Validation.Subtyping.Decide
public import Silmaril.Wasm.Execution.Core.Exec.PrepareDirect
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Execution.Core.Exec.ExternAddrCheck
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationTypes

/-!
# The concrete Core 3.0 core engine

`core3 o` is the `CoreEngine` whose modules are Core 3.0 modules (`Silmaril.Wasm.Module`), whose
store is the Core store (`Execution.Core.Store`), whose threads are the store-free threads of the
single-threaded machine (`SingleThreaded.Thread`), and whose internal step is the computable
interpreter step `Exec.stepI o` (the deterministic single-threaded profile with grow oracle `o`).
Every field is computable.

* Static types: function types are closed defined types (`DefType`); extern types are closed extern
  types valid in the empty context, `{τ : CExternType // ExternTypeOk {} τ}`, with import matching
  `ExternSub {}` (Wasm 3.0 spec, "Import Subtyping" / "External Types"); subtyping is decided by
  `ExternSub.decideEmpty`. Validity is `ModuleValid`. Import and export types are those computed by
  the validator `validate?`, paired with the names of `m.imports` / `m.exports` (`[]` for invalid
  modules). They are valid in the empty context (`ModuleOk.imports_externTypeOk`,
  `ModuleOk.exports_externTypeOk`).
* `externTypeE?` is the principal type of an external address (`externAddrType?`, the spec's
  `Externaddr_ok` instance type), kept only when it is valid in the empty context (always the case on
  well-typed stores, `externAddrType?_typeOk`).
* `prepareE?` is `instantiateOnce?` (`$evalglobals`, then the spec's direct instantiation
  `instantiateDirect?` of the global-free residue `Module.globalResidue`: allocation, then direct
  element/data segment initialisation; the start function is returned, not run), guarded by
  `validate?` and the `Externaddr_ok` check `externAddrsOk?` of the arguments against the module's
  import types. The start function index is mapped to its address in the new module instance.
  `instantiateOnce?` allocates every global once, where the spec's `$instantiate` allocates it in
  `$evalglobals` and again in `$allocmodule`; on global-free modules the two are equal
  (`instantiateOnce?_of_nil`, `prepareE?_of_nil`). `prepareSpecE?` is the same guard over the
  transcription's double-allocating `instantiateDirect?` of the module itself (which follows the
  spec's `$instantiate` up to the deviations listed in Silmaril.Wasm.Execution.Core.Instantiation), and `core3Spec o` is
  the engine with it, every other field being that of `core3 o`.
* `statusE o` is the flat view of `statusC (stepI o)`: a result or a callout whose values are not all
  numeric is reported as `stuck` (this never happens for flat-typed functions on typed stores).
* `Internal` is the graph of the interpreter step, `internalC (stepI o) c = some c'`, so the
  executable stepper `core3Exec o` is deterministic by definition (`core3Exec_deterministic`).

No law is proved here (see `Engine/Laws.lean` for the statements).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

namespace Core3

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-! ## Import and export types are valid in the empty context -/

/-- Every right element of a `Forall₂` pair is related to some left element. -/
theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => by cases hb
  | _, _, .cons (a := a) h hs, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨a', ha', h'⟩ := forall₂_mem_right hs b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem mem_tags {d : DefType} : ∀ {xs : List CExternType}, d ∈ CExternType.tags xs → .tag d ∈ xs
  | [], h => by cases h
  | .tag d' :: xs, h => by
    simp only [CExternType.tags, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_tags h)
  | .global _ :: _, h | .mem _ :: _, h | .table _ :: _, h | .func _ :: _, h =>
    List.mem_cons_of_mem _ (mem_tags h)

theorem mem_globals {g : CGlobalType} :
    ∀ {xs : List CExternType}, g ∈ CExternType.globals xs → .global g ∈ xs
  | [], h => by cases h
  | .global g' :: xs, h => by
    simp only [CExternType.globals, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_globals h)
  | .tag _ :: _, h | .mem _ :: _, h | .table _ :: _, h | .func _ :: _, h =>
    List.mem_cons_of_mem _ (mem_globals h)

theorem mem_mems {mt : MemoryType} :
    ∀ {xs : List CExternType}, mt ∈ CExternType.mems xs → .mem mt ∈ xs
  | [], h => by cases h
  | .mem m' :: xs, h => by
    simp only [CExternType.mems, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_mems h)
  | .tag _ :: _, h | .global _ :: _, h | .table _ :: _, h | .func _ :: _, h =>
    List.mem_cons_of_mem _ (mem_mems h)

theorem mem_tables {t : CTableType} :
    ∀ {xs : List CExternType}, t ∈ CExternType.tables xs → .table t ∈ xs
  | [], h => by cases h
  | .table t' :: xs, h => by
    simp only [CExternType.tables, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_tables h)
  | .tag _ :: _, h | .global _ :: _, h | .mem _ :: _, h | .func _ :: _, h =>
    List.mem_cons_of_mem _ (mem_tables h)

theorem mem_funcs {d : DefType} :
    ∀ {xs : List CExternType}, d ∈ CExternType.funcs xs → .func d ∈ xs
  | [], h => by cases h
  | .func d' :: xs, h => by
    simp only [CExternType.funcs, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_funcs h)
  | .tag _ :: _, h | .global _ :: _, h | .mem _ :: _, h | .table _ :: _, h =>
    List.mem_cons_of_mem _ (mem_funcs h)

/-- `Import_ok` in the module's type context gives validity in the empty context: the closed
import type only mentions the module's defined types `dts`, which are valid in `{}`. -/
theorem ImportOk.externTypeOk_empty {dts : List DefType} (hd : ∀ d ∈ dts, TyOk {} d)
    {im : Import} {xt : CExternType} (h : ImportOk { types := dts } im xt) :
    ExternTypeOk {} xt := by
  obtain ⟨hc, hok⟩ := h
  cases hty : im.type with
  | tag x =>
    rw [hty] at hc
    simp only [Context.closeExtern?, Context.type?, Option.map_eq_some_iff] at hc
    obtain ⟨d, hx, rfl⟩ := hc
    cases hok with
    | tag h => exact .tag ⟨hd d (List.mem_of_getElem? hx), h.2⟩
  | global g =>
    rw [hty] at hc
    simp only [Context.closeExtern?, Option.some.injEq] at hc
    subst hc
    cases hok with
    | global h => exact .global (TyOk.closeVal_empty hd rfl h)
  | memory mt =>
    rw [hty] at hc
    simp only [Context.closeExtern?, Option.some.injEq] at hc
    subst hc
    cases hok with
    | mem h => exact .mem h
  | table t =>
    rw [hty] at hc
    simp only [Context.closeExtern?, Option.some.injEq] at hc
    subst hc
    cases hok with
    | table h => exact .table ⟨h.1, TyOk.closeRef_empty hd rfl h.2⟩
  | func x =>
    rw [hty] at hc
    simp only [Context.closeExtern?, Context.type?, Option.map_eq_some_iff] at hc
    obtain ⟨d, hx, rfl⟩ := hc
    cases hok with
    | func _ he => exact .func (hd d (List.mem_of_getElem? hx)) he

/-- The import types of a valid module are valid in the empty context. -/
theorem ModuleOk.imports_externTypeOk {m : Module} {xtI xtE : List CExternType}
    (h : ModuleOk m ⟨xtI, xtE⟩) : ∀ τ ∈ xtI, ExternTypeOk {} τ := by
  cases h with
  | @mk dts _ _ _ _ _ _ _ _ _ htypes himports =>
    intro τ hτ
    obtain ⟨im, -, hi⟩ := forall₂_mem_right himports τ hτ
    exact ImportOk.externTypeOk_empty htypes.tyOk_empty' hi

theorem GlobalsOk.globalTypeOk_empty {dts : List DefType} (hd : ∀ d ∈ dts, TyOk {} d) :
    ∀ {C : Context} {gs : List Global} {gts : List CGlobalType}, C.types = dts →
      GlobalsOk C gs gts → ∀ gt ∈ gts, GlobalTypeOk {} gt := by
  intro C gs gts hT h
  induction h with
  | nil => intro gt hgt; cases hgt
  | @cons C₁ g gs gt gts hg _ ih =>
    intro gt' hgt'
    rcases List.mem_cons.mp hgt' with rfl | hgt'
    · have h2 : TyOk C₁.toTypeCtx gt'.type := hg.2.1
      rw [hg.1] at h2 ⊢
      simp only [Context.closeGlobalType, Context.closeVal, GlobalTypeOk, hT] at h2 ⊢
      exact TyOk.closeVal_empty hd (Δ := C₁.toTypeCtx) hT h2
    · exact ih hT gt' hgt'

/-- The export types of a valid module are valid in the empty context. -/
theorem ModuleOk.exports_externTypeOk {m : Module} {xtI xtE : List CExternType}
    (h : ModuleOk m ⟨xtI, xtE⟩) : ∀ τ ∈ xtE, ExternTypeOk {} τ := by
  have hI := ModuleOk.imports_externTypeOk h
  cases h with
  | @mk dts _ jts gts tts fdts _ _ C' C htypes _ hC' hC htags hglobals hmems htables hfuncs
      _ _ _ hexports _ =>
    have hdts : ∀ d ∈ dts, TyOk {} d := htypes.tyOk_empty'
    have hC'T : C'.types = dts := by rw [hC']
    have hCT : C.types = dts := by rw [hC, hC']
    intro τ hτ
    obtain ⟨⟨_, idx⟩, -, he⟩ := forall₂_mem_right hexports τ hτ
    have he : ExternIdxOk C idx τ := he
    cases he with
    | @tag x d hx =>
      rw [hC] at hx
      rcases List.mem_append.mp (List.mem_of_getElem? hx) with hm | hm
      · exact hI _ (mem_tags hm)
      · obtain ⟨t, -, ht⟩ := forall₂_mem_right htags d hm
        have h1 : C'.types[t.toNat]? = some d := ht.1
        rw [hC'T] at h1
        exact .tag ⟨hdts d (List.mem_of_getElem? h1), ht.2.2⟩
    | @global x g hx =>
      rw [hC, hC'] at hx
      rcases List.mem_append.mp (List.mem_of_getElem? hx) with hm | hm
      · exact hI _ (mem_globals hm)
      · exact .global (GlobalsOk.globalTypeOk_empty hdts hC'T hglobals g hm)
    | @mem x mt hx =>
      rw [hC] at hx
      rcases List.mem_append.mp (List.mem_of_getElem? hx) with hm | hm
      · exact hI _ (mem_mems hm)
      · exact .mem (hmems mt hm)
    | @table x tt hx =>
      rw [hC] at hx
      rcases List.mem_append.mp (List.mem_of_getElem? hx) with hm | hm
      · exact hI _ (mem_tables hm)
      · obtain ⟨t, -, ht⟩ := forall₂_mem_right htables tt hm
        have h2 := ht.2.1
        refine .table ⟨h2.1, ?_⟩
        have h3 := h2.2
        rw [ht.1] at h3 ⊢
        simp only [Context.closeTableType, Context.closeRef, hC'T] at h3 ⊢
        exact TyOk.closeRef_empty hdts hC'T h3
    | @func x d hx =>
      rw [hC, hC'] at hx
      rcases List.mem_append.mp (List.mem_of_getElem? hx) with hm | hm
      · exact hI _ (mem_funcs hm)
      · obtain ⟨fn, -, hfn⟩ := forall₂_mem_right hfuncs d hm
        cases hfn with
        | mk hd' he _ _ =>
          have h1 : C.types[fn.type.toNat]? = some d := hd'
          rw [hCT] at h1
          exact .func (hdts d (List.mem_of_getElem? h1)) he

theorem validate?_imports_externTypeOk {m : Module} {mt : CModuleType}
    (h : validate? m = some mt) : ∀ τ ∈ mt.imports, ExternTypeOk {} τ := by
  obtain ⟨xi, xe⟩ := mt
  exact ModuleOk.imports_externTypeOk (validate?_sound h)

theorem validate?_exports_externTypeOk {m : Module} {mt : CModuleType}
    (h : validate? m = some mt) : ∀ τ ∈ mt.exports, ExternTypeOk {} τ := by
  obtain ⟨xi, xe⟩ := mt
  exact ModuleOk.exports_externTypeOk (validate?_sound h)

/-- Every import and export type computed by `validate?` is valid in the empty context. -/
theorem validate?_externTypeOk {m : Module} {mt : CModuleType} (h : validate? m = some mt) :
    ∀ τ ∈ mt.imports ++ mt.exports, ExternTypeOk {} τ := by
  intro τ hτ
  rcases List.mem_append.mp hτ with hτ | hτ
  · exact validate?_imports_externTypeOk h τ hτ
  · exact validate?_exports_externTypeOk h τ hτ

/-! ## Definitions -/

/-- Extern types of the concrete engine: closed extern types valid in the empty context. -/
abbrev ExtT : Type := {τ : CExternType // ExternTypeOk {} τ}

/-- Import types: `validate?`'s import types, named by `m.imports`; `[]` for invalid modules. -/
def importTypesE (m : Module) : List (String × String × ExtT) :=
  match h : validate? m with
  | some mt =>
    (m.imports.zip (mt.imports.attachWith _ (validate?_imports_externTypeOk h))).map
      fun p => (p.1.moduleName, p.1.name, p.2)
  | none => []

/-- Export types: `validate?`'s export types, named by `m.exports`; `[]` for invalid modules. -/
def exportTypesE (m : Module) : List (String × ExtT) :=
  match h : validate? m with
  | some mt =>
    (m.exports.zip (mt.exports.attachWith _ (validate?_exports_externTypeOk h))).map
      fun p => (p.1.name, p.2)
  | none => []

/-- The type of an external address: its principal type, when that is valid in `{}`. -/
def externTypeE? {H : Type} (s : Store H) (xa : ExternAddr) : Option ExtT :=
  match externAddrType? s xa with
  | some τ => if h : ExternTypeOk.check {} τ = true then some ⟨τ, ExternTypeOk.check_sound h⟩
    else none
  | none => none

/-- Instantiation with the transcription's double-allocating `instantiateDirect?`, which follows
the spec's `$instantiate` (every global allocated in `$evalglobals` and again in `$allocmodule`) up
to the deviations listed in Silmaril.Wasm.Execution.Core.Instantiation: `instantiateDirect?` on a module accepted by
`validate?` whose arguments pass `externAddrsOk?` against its import types; the start index
becomes the start address. -/
def prepareSpecE? {H : Type} (s : Store H) (m : Module) (xas : List ExternAddr) :
    Option (Store H × ModuleInst × Option Nat) :=
  match validate? m with
  | none => none
  | some mt =>
    if externAddrsOk? s xas mt.imports then
      match instantiateDirect? s m xas with
      | none => none
      | some (s', f', none) => some (s', f'.module, none)
      | some (s', f', some x) => f'.module.funcs[x.toNat]?.map fun a => (s', f'.module, some a)
    else none

-- FLAG(statement-change): the definition runs `instantiateOnce?` (every global allocated once)
-- instead of the spec's `instantiateDirect?`, which `prepareSpecE?` keeps.
/-- Instantiation: `instantiateOnce?` (every global allocated once) on a module accepted by
`validate?` whose arguments pass `externAddrsOk?` against its import types; the start index
becomes the start address. -/
def prepareE? {H : Type} (s : Store H) (m : Module) (xas : List ExternAddr) :
    Option (Store H × ModuleInst × Option Nat) :=
  match validate? m with
  | none => none
  | some mt =>
    if externAddrsOk? s xas mt.imports then
      match instantiateOnce? s m xas with
      | none => none
      | some (s', f', none) => some (s', f'.module, none)
      | some (s', f', some x) => f'.module.funcs[x.toNat]?.map fun a => (s', f'.module, some a)
    else none

/-- Component-level call results as single-threaded call results. -/
def toCR : CallResult → SingleThreaded.CallResult
  | .values vs => .values (vs.map SingleThreaded.ofFlat)
  | .trap => .trap

/-- The flat status: `statusC (stepI o)` with values converted to flat values; non-flat results
and non-flat callout arguments are `stuck`. -/
def statusE {H : Type} (o : SingleThreaded.GrowOracle) (s : Store H) (t : SingleThreaded.Thread) :
    Status H :=
  match SingleThreaded.statusC (SingleThreaded.Exec.stepI o) s t with
  | .running => .running
  | .returned (.values vs) =>
    match vs.mapM SingleThreaded.toFlat? with
    | some fvs => .returned (.values fvs)
    | none => .stuck
  | .returned .trap => .returned .trap
  | .callout h args =>
    match args.mapM SingleThreaded.toFlat? with
    | some fargs => .callout h fargs
    | none => .stuck
  | .stuck => .stuck

/-- The function address of an external address, if it is one. -/
def asFunc? : ExternAddr → Option Nat
  | .func a => some a
  | _ => none

/-- The memory address of an external address, if it is one. -/
def asMemory? : ExternAddr → Option Nat
  | .mem a => some a
  | _ => none

/-- The table address of an external address, if it is one. -/
def asTable? : ExternAddr → Option Nat
  | .table a => some a
  | _ => none

/-- The global address of an external address, if it is one. -/
def asGlobal? : ExternAddr → Option Nat
  | .global a => some a
  | _ => none

/-- Named exports of a module instance. -/
def instExports (i : ModuleInst) : List (String × ExternAddr) := i.exports.map fun x => (x.name, x.addr)

/-- The type of a function address. -/
def funcTypeE? {H : Type} (s : Store H) (a : Nat) : Option DefType := s.funcs[a]?.map (·.type)

end Core3

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Core3

/-- The concrete Core 3.0 engine over grow oracle `o`. -/
def core3 (o : SingleThreaded.GrowOracle) : CoreEngine where
  Module := Silmaril.Wasm.Module
  Valid := ModuleValid
  FuncType := DefType
  ExternType := ExtT
  ExternSub a b := Validation.ExternSub {} a.1 b.1
  ofFlatType := SingleThreaded.ofFlatType
  flatType? := SingleThreaded.flatType?
  importTypes := importTypesE
  exportTypes := exportTypesE
  Store := Execution.Core.Store
  empty _ := {}
  FuncAddr := Nat
  MemAddr := Nat
  TableAddr := Nat
  GlobalAddr := Nat
  ExternVal := ExternAddr
  asFunc? := Core3.asFunc?
  asMemory? := Core3.asMemory?
  asTable? := Core3.asTable?
  asGlobal? := Core3.asGlobal?
  ofFunc := .func
  Inst := Execution.Core.ModuleInst
  exports := instExports
  externType? := externTypeE?
  prepare? := prepareE?
  allocHost := SingleThreaded.allocHost
  funcType? := funcTypeE?
  memAddrType? := SingleThreaded.memAddrType?
  memSize? := SingleThreaded.memSize?
  memRead? := SingleThreaded.memRead?
  memWrite? := SingleThreaded.memWrite?
  tableAddrType? := SingleThreaded.tableAddrType?
  tableFunc? := SingleThreaded.tableFunc?
  Thread _ := SingleThreaded.Thread
  invoke := SingleThreaded.Thread.invokeFlat
  status := statusE o
  Internal c c' := SingleThreaded.internalC (SingleThreaded.Exec.stepI o) c = some c'
  resume s t r := SingleThreaded.resume s t (toCR r)

/-- Import matching of the concrete engine is decidable (`ExternSub.decideEmpty`). -/
instance core3_decExternSub (o : SingleThreaded.GrowOracle) (a b : (core3 o).ExternType) :
    Decidable ((core3 o).ExternSub a b) :=
  Validation.ExternSub.decideEmpty a.1 b.1 a.2 b.2

/-- The executable stepper of the concrete engine: the interpreter step itself. -/
def core3Exec (o : SingleThreaded.GrowOracle) : (core3 o).Exec where
  step? := SingleThreaded.internalC (SingleThreaded.Exec.stepI o)
  step?_sound h := h

theorem core3Exec_deterministic (o : SingleThreaded.GrowOracle) :
    CoreEngine.ExecDeterministic (core3Exec o) :=
  .of_deterministic fun h => h

/-- The concrete engine with the transcription's double-allocating instantiation
(`Core3.prepareSpecE?`, over `Execution.Core.instantiateDirect?`, which follows the spec's
`$instantiate` up to the deviations listed in Silmaril.Wasm.Execution.Core.Instantiation); every other field is that of
`core3 o`. On global-free modules the two engines instantiate alike (`Core3.prepareE?_of_nil`);
in general they correspond up to a renaming of global addresses (Engine/Core3/GlobalRen.lean). -/
def core3Spec (o : SingleThreaded.GrowOracle) : CoreEngine :=
  { core3 o with prepare? := Core3.prepareSpecE? }

/-- Import matching of the spec engine is that of `core3 o`, hence decidable. -/
instance core3Spec_decExternSub (o : SingleThreaded.GrowOracle) (a b : (core3Spec o).ExternType) :
    Decidable ((core3Spec o).ExternSub a b) :=
  core3_decExternSub o a b

namespace Core3

/-! ## Basic facts about the definitions -/

theorem core3_internal_iff {o : SingleThreaded.GrowOracle} {H : Type}
    {c c' : (core3 o).Config H} :
    (core3 o).Internal c c' ↔ SingleThreaded.internalC (SingleThreaded.Exec.stepI o) c = some c' :=
  Iff.rfl

theorem core3_externSub_iff {o : SingleThreaded.GrowOracle} {a b : (core3 o).ExternType} :
    (core3 o).ExternSub a b ↔ Validation.ExternSub {} a.1 b.1 :=
  Iff.rfl

theorem core3_valid_iff {o : SingleThreaded.GrowOracle} {m : (core3 o).Module} :
    (core3 o).Valid m ↔ ModuleValid m :=
  Iff.rfl

/-- On global-free modules single allocation is the spec's instantiation. -/
theorem prepareE?_of_nil {H : Type} {s : Store H} {m : Module} {xas : List ExternAddr}
    (h : m.globals = []) : prepareE? s m xas = prepareSpecE? s m xas := by
  unfold prepareE? prepareSpecE?
  rw [instantiateOnce?_of_nil h]

/-! ### The spec engine shares every field of `core3 o` but instantiation -/

section Spec
variable (o : SingleThreaded.GrowOracle) {H : Type}

theorem core3_prepare? : (core3 o).prepare? (H := H) = prepareE? := rfl
theorem core3Spec_prepare? : (core3Spec o).prepare? (H := H) = prepareSpecE? := rfl
theorem core3Spec_status : (core3Spec o).status (H := H) = (core3 o).status (H := H) := rfl
theorem core3Spec_internal : (core3Spec o).Internal (H := H) = (core3 o).Internal (H := H) := rfl
theorem core3Spec_resume : (core3Spec o).resume (H := H) = (core3 o).resume (H := H) := rfl
theorem core3Spec_invoke : (core3Spec o).invoke (H := H) = (core3 o).invoke (H := H) := rfl
theorem core3Spec_externType? :
    (core3Spec o).externType? (H := H) = (core3 o).externType? (H := H) := rfl
theorem core3Spec_allocHost : (core3Spec o).allocHost (H := H) = (core3 o).allocHost (H := H) := rfl
theorem core3Spec_memWrite? : (core3Spec o).memWrite? (H := H) = (core3 o).memWrite? (H := H) := rfl

end Spec

theorem map_zip_attachWith {α β : Type} {P : β → Prop} :
    ∀ (l : List α) (l' : List β) (H : ∀ b ∈ l', P b),
      (l.zip (l'.attachWith P H)).map (fun p => (p.1, p.2.1)) = l.zip l'
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: l, b :: l', H => by
    simp only [List.attachWith_cons, List.zip_cons_cons, List.map_cons]
    rw [map_zip_attachWith l l']

theorem importTypesE_eq {m : Module} {mt : CModuleType} (h : validate? m = some mt) :
    (importTypesE m).map (fun p => (p.1, p.2.1, p.2.2.1)) =
      (m.imports.zip mt.imports).map fun p => (p.1.moduleName, p.1.name, p.2) := by
  unfold importTypesE
  split
  · rename_i mt' h'
    rw [h] at h'
    cases h'
    rw [List.map_map, ← map_zip_attachWith m.imports mt.imports
      (validate?_imports_externTypeOk h), List.map_map]
    rfl
  · rename_i h'
    rw [h] at h'
    cases h'

theorem exportTypesE_eq {m : Module} {mt : CModuleType} (h : validate? m = some mt) :
    (exportTypesE m).map (fun p => (p.1, p.2.1)) =
      (m.exports.zip mt.exports).map fun p => (p.1.name, p.2) := by
  unfold exportTypesE
  split
  · rename_i mt' h'
    rw [h] at h'
    cases h'
    rw [List.map_map, ← map_zip_attachWith m.exports mt.exports
      (validate?_exports_externTypeOk h), List.map_map]
    rfl
  · rename_i h'
    rw [h] at h'
    cases h'

theorem importTypesE_of_none {m : Module} (h : validate? m = none) : importTypesE m = [] := by
  unfold importTypesE
  split
  · rename_i mt h'; rw [h] at h'; cases h'
  · rfl

theorem exportTypesE_of_none {m : Module} (h : validate? m = none) : exportTypesE m = [] := by
  unfold exportTypesE
  split
  · rename_i mt h'; rw [h] at h'; cases h'
  · rfl

theorem externTypeE?_val {H : Type} {s : Store H} {xa : ExternAddr} {τ : ExtT}
    (h : externTypeE? s xa = some τ) : externAddrType? s xa = some τ.1 := by
  unfold externTypeE? at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

theorem externTypeE?_of_typeOk {H : Type} {s : Store H} (hs : StoreOk s) {xa : ExternAddr}
    {τ : CExternType} (h : externAddrType? s xa = some τ) :
    externTypeE? s xa = some ⟨τ, externAddrType?_typeOk hs h⟩ := by
  unfold externTypeE?
  rw [h]
  have hc : ExternTypeOk.check {} τ = true :=
    ExternTypeOk.check_complete (TyOk.check_complete TypeCtx.ok_empty rfl) (externAddrType?_typeOk hs h)
  simp [hc]

/-! ## Smoke tests -/

/-- A freshly allocated host function, invoked with no arguments, is parked on its host code. -/
example :
    (core3 SingleThreaded.neverFail).status ((core3 SingleThreaded.neverFail).allocHost
        ((core3 SingleThreaded.neverFail).empty Nat) ⟨[], []⟩ 7).1
      ((core3 SingleThreaded.neverFail).invoke ((core3 SingleThreaded.neverFail).allocHost
        ((core3 SingleThreaded.neverFail).empty Nat) ⟨[], []⟩ 7).2 []) = .callout 7 [] := by
  decide +kernel

/-- The same with flat arguments: they are passed to the host unchanged. -/
example :
    (core3 SingleThreaded.neverFail).status ((core3 SingleThreaded.neverFail).allocHost
        ((core3 SingleThreaded.neverFail).empty Nat) ⟨[.int .i32, .int .i64], [.int .i32]⟩ 3).1
      ((core3 SingleThreaded.neverFail).invoke ((core3 SingleThreaded.neverFail).allocHost
        ((core3 SingleThreaded.neverFail).empty Nat) ⟨[.int .i32, .int .i64], [.int .i32]⟩ 3).2
        [⟨.int .i32, 5⟩, ⟨.int .i64, 9⟩]) = .callout 3 [⟨.int .i32, 5⟩, ⟨.int .i64, 9⟩] := by
  decide +kernel

/-- The empty module has no imports and no exports. -/
example : importTypesE {} = [] ∧ exportTypesE {} = [] := by decide +kernel

/-- A module exporting a global: its export type matches itself, and it instantiates with no
start function. -/
example :
    (match (core3 SingleThreaded.neverFail).exportTypes exGlobal with
      | [("g", τ)] => decide ((core3 SingleThreaded.neverFail).ExternSub τ τ)
      | _ => false) = true ∧
    (((core3 SingleThreaded.neverFail).prepare? ((core3 SingleThreaded.neverFail).empty Nat)
      exGlobal []).map fun r => r.2.2) = some none := by
  decide +kernel

/-- Instantiating with a wrong number of arguments fails. -/
example : prepareE? (H := Nat) {} exGlobal [.func 0] = none := by decide +kernel

/-- A module defining one global: single allocation leaves one global in the store, named by the
instance; the spec's `$instantiate` leaves two, the instance naming the second. -/
example :
    ((prepareE? (H := Nat) {} exGlobal []).map fun r => (r.2.1.globals, r.1.globals.length)) =
      some ([0], 1) ∧
    ((prepareSpecE? (H := Nat) {} exGlobal []).map fun r =>
      (r.2.1.globals, r.1.globals.length)) = some ([1], 2) := by
  decide +kernel

end Core3

end Silmaril.Wasm.Component.Engine
