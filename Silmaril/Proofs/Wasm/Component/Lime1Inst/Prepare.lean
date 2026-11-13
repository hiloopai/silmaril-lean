module

public import Silmaril.Proofs.Wasm.Component.Lime1Inst.Retract
public import Silmaril.Proofs.Wasm.Component.Lime1Inst.Alloc

/-!
# Lime1 preparation is Core instantiation at every profile

The copied `Lime1.Execution.prepare_core` relates Lime1 preparation to Core `Instantiate`
followed by the segment programs, at `coreProfile` (`Profile.spec`), for the image module
`m.toCore`. None of its ingredients depends on the profile (`elemLoop_core`, `dataLoop_core`,
`evalExprs_tables` and `evalExprss_elems` are stated at every `P`), and element types are only
read by allocation (`allocModule?_elems`). So the same holds:

* at **every profile** `P`, in particular at the deterministic `profile o`, where the executable
  instantiation is complete (`Silmaril.Wasm.Instantiation.instantiateDirect?_complete`);
* for **every Core module `M` decoding to `m`**: `M` is `m.toCore` with other element types
  (`module_retract`), because `Lime1.Elem.ofCore?` also accepts non-null `(ref func)` segments.

* `prepare_coreP`: the statement, under the copied `InstantiationBounds`.

No profile transfer of runs is needed: the run is built at the target profile directly.
Adapted from `prepare_core` (`Silmaril/Raw/Wasm/Versions/Lime1/ToCore/Instantiation.lean`,
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Inst

open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Lime1.Execution
open Silmaril.Wasm.Execution (Runtime.ExternVal Runtime.ModuleInst)
open Silmaril.Wasm.Execution.Runtime (GlobalInst)

variable {H : Type}

/-- The Core module `m.toCore` with the element segments `es`. -/
abbrev withElems (m : Silmaril.Wasm.Lime1.Module) (es : List Silmaril.Wasm.Elem) :
    Silmaril.Wasm.Module :=
  { m.toCore with elems := es }

theorem runElems_funcref (n : Nat) (es : List Silmaril.Wasm.Elem) :
    (((List.range n).zip (es.map funcrefElem)).flatMap fun (i, e) =>
        Silmaril.Wasm.Execution.Core.runElem i e) =
      ((List.range n).zip es).flatMap fun (i, e) => Silmaril.Wasm.Execution.Core.runElem i e := by
  rw [List.zip_map_right, List.flatMap_map]
  rfl

theorem erase_retype {S S' : ToCore.CStore H} (h : ElemRetype S S') :
    ToCore.Store.erase S' = ToCore.Store.erase S := by
  rw [h.1]; rfl

/-- The segment code of the module with the elements `es`, then the start call. -/
abbrev segStart (m : Silmaril.Wasm.Lime1.Module) (es : List Silmaril.Wasm.Elem) :
    List Silmaril.Wasm.Execution.Core.Admin :=
  Silmaril.Wasm.Execution.Core.expression
      (((List.range es.length).zip es).flatMap fun (i, e) =>
        Silmaril.Wasm.Execution.Core.runElem i e) ++
    Silmaril.Wasm.Execution.Core.expression
      (((List.range m.toCore.data.length).zip m.toCore.data).flatMap fun (i, d) =>
        Silmaril.Wasm.Execution.Core.runData i d) ++
    (match m.toCore.start with | some x => [.plain (.call x)] | none => [])

/-- The provisional frame of `$instantiate`. -/
abbrev frame0 {H : Type} (B : Silmaril.Wasm.Execution.Core.Store H) (M : Silmaril.Wasm.Module)
    (xas : List Silmaril.Wasm.Execution.Core.ExternAddr) : Silmaril.Wasm.Execution.Core.Frame :=
  { module := Silmaril.Wasm.Execution.Core.ModuleInst.initial B M xas }

/-- **The parts of `$instantiate` and of the segment run for a Lime1 preparation**, at every
profile, for every Core module `{m.toCore with elems := es}` with `es` retyping to the image's
element segments. No validity is needed. -/
theorem prepare_parts {P : Profile} {tgt : ToCore.CHostSemantics H} {before : Store H}
    {m : Silmaril.Wasm.Lime1.Module} {imports : List Runtime.ExternVal} {p : Prepared H}
    {es : List Silmaril.Wasm.Elem} (hes : es.map funcrefElem = m.toCore.elems)
    (bounds : InstantiationBounds before m) (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid m)
    (hp : prepare? before m imports = some p) :
    ∃ (Sa S : ToCore.CStore H) (mi : ToCore.CModuleInst)
      (refsE : List (List Silmaril.Wasm.Execution.Core.Ref)),
      Silmaril.Wasm.Execution.Core.EvalExprs P tgt before.toCore
        (frame0 before.toCore (withElems m es) (imports.map Runtime.ExternVal.toCore))
        ((withElems m es).tables.map Silmaril.Wasm.Table.init) before.toCore
        (frame0 before.toCore (withElems m es) (imports.map Runtime.ExternVal.toCore))
        (m.tables.map fun _ => .null) ∧
      Silmaril.Wasm.Execution.Core.EvalExprss P tgt before.toCore
        (frame0 before.toCore (withElems m es) (imports.map Runtime.ExternVal.toCore))
        ((withElems m es).elems.map Silmaril.Wasm.Elem.init) before.toCore
        (frame0 before.toCore (withElems m es) (imports.map Runtime.ExternVal.toCore)) refsE ∧
      Silmaril.Wasm.Execution.Core.allocModule? before.toCore (withElems m es)
        (imports.map Runtime.ExternVal.toCore) [] (m.tables.map fun _ => .null) refsE =
        some (Sa, mi) ∧
      Silmaril.Wasm.Execution.Core.Steps P tgt ⟨Sa, { module := mi }, segStart m es⟩
        ⟨S, { module := mi }, startCode m.toCore⟩ ∧
      ToCore.Store.erase S = p.store.toCore ∧ ToCore.ModuleInstSim p.module mi := by
  have hg := bounds.noGlobals
  have hlen : es.length = m.toCore.elems.length := by rw [← hes, List.length_map]
  obtain ⟨allocated, elems, data, ha, he, hd, hst⟩ := prepare?_inv hp
  obtain ⟨exports, funcs, hex, hfn, hmod, halloc⟩ := allocate?_inv hg ha
  have he2 := mapM_forall₂ he
  have hd2 := mapM_forall₂ hd
  obtain ⟨Sa0, mi, hAM0, hmi, hmiE, hmiD, hSaE0, hSaD0, hSaG0, hSaS0⟩ :=
    allocModule_core (refsE := elems.map elemRefs) hg hex hfn
      (by rw [List.length_map]; exact he2.length_eq.symm)
  obtain ⟨Sa, hAM, hre⟩ := allocModule?_elems hlen hAM0
  have hSaE : Sa.elems.map (·.refs) = elems.map elemRefs := hre.2.trans hSaE0
  have hSaD : Sa.datas.map (·.bytes) = m.data.map (·.bytes) := by rw [hre.1]; exact hSaD0
  have hSaG : Sa.globals = before.toCore.globals := by rw [hre.1]; exact hSaG0
  have hSaS := (erase_retype hre).trans hSaS0
  -- the frame module
  have hFg : mi.globals = p.module.globals.map (·.value) := by
    have := congrArg (·.globals) hmi
    rw [hmod]
    simpa [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore] using this
  have hFt : mi.tables = p.module.tables.map (·.value) := by
    have := congrArg (·.tables) hmi
    rw [hmod]
    simpa [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore] using this
  have hFm : mi.mems = p.module.memories.map (·.value) := by
    have := congrArg (·.mems) hmi
    rw [hmod]
    simpa [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore] using this
  -- the initial store
  have hG0 : Sa.globals = allocated.globals.map GlobalInst.toCore := by
    rw [hSaG, halloc]; rfl
  have hS0 : ToCore.Store.erase Sa = allocated.toCore := by rw [hSaS, halloc]
  have htab : ∀ t ∈ allocated.tables, t.refs.length < 2 ^ 32 := by
    rw [halloc]
    intro t ht
    simp only [List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨tt, -, rfl⟩
    · exact bounds.tables t ht
    · simp only [List.length_replicate]; exact tt.limits.min.isLt
  have hmem : ∀ t ∈ allocated.memories, t.data.size ≤ 2 ^ 32 := by
    rw [halloc]
    intro t ht
    simp only [List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨mt, hmt, rfl⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht
      exact (bounds.storeWF.2 i t hi).1
    · have hvt := (hv.memories mt hmt).1
      simp only [ByteArray.size, Array.size_replicate, Silmaril.Wasm.Execution.Memory.pageSize]
      omega
  -- element segments
  obtain ⟨S1, h1, hS1, hG1, hD1, -⟩ := elemLoop_core (P := P) (tgt := tgt)
    (F := { module := mi }) hFg hFt htab m.elems elems 0 Sa allocated he2
    (by simpa using bounds.elemCount)
    (fun i hi => by simp [hmiE, List.getElem?_range hi])
    (fun i hi => by
      have := congrArg (·[i]?) hSaE
      simpa [List.getElem?_map] using this)
    hG0 hS0 (fun _ => rfl)
    (Silmaril.Wasm.Execution.Core.expression
      (((List.range' 0 m.data.length).zip (m.data.map Silmaril.Wasm.Lime1.Data.toCore)).flatMap
        fun (i, d) => Silmaril.Wasm.Execution.Core.runData i d) ++ startCode m.toCore)
  -- data segments
  obtain ⟨S2, h2, hS2⟩ := dataLoop_core (P := P) (tgt := tgt)
    (F := { module := mi }) hFg hFm hmem m.data data 0 S1 (elems.foldl applyElem allocated) hd2
    bounds.data (by simpa using bounds.dataCount)
    (fun i hi => by simp [hmiD, List.getElem?_range hi])
    (fun i hi => by
      have := congrArg (·[i]?) hSaD
      rw [hD1]
      simpa [List.getElem?_map] using this)
    (hG1.trans hG0) hS1 (fun i => by rw [foldl_applyElem_memories]) (startCode m.toCore)
  have hcode : Silmaril.Wasm.Execution.Core.expression
        (((List.range es.length).zip es).flatMap fun (i, e) =>
          Silmaril.Wasm.Execution.Core.runElem i e) ++
      Silmaril.Wasm.Execution.Core.expression
        (((List.range m.toCore.data.length).zip m.toCore.data).flatMap fun (i, d) =>
          Silmaril.Wasm.Execution.Core.runData i d) ++
      (match m.toCore.start with | some x => [.plain (.call x)] | none => []) =
      Silmaril.Wasm.Execution.Core.expression
        (((List.range' 0 m.elems.length).zip (m.elems.map Silmaril.Wasm.Lime1.Elem.toCore)).flatMap
          fun (i, e) => Silmaril.Wasm.Execution.Core.runElem i e) ++
      (Silmaril.Wasm.Execution.Core.expression
        (((List.range' 0 m.data.length).zip (m.data.map Silmaril.Wasm.Lime1.Data.toCore)).flatMap
          fun (i, d) => Silmaril.Wasm.Execution.Core.runData i d) ++ startCode m.toCore) := by
    rw [← runElems_funcref, hes, hlen]
    simp only [Silmaril.Wasm.Lime1.Module.toCore, List.length_map, List.range_eq_range',
      List.append_assoc]
    rfl
  have hinit : (withElems m es).elems.map Silmaril.Wasm.Elem.init =
      (m.elems.map Silmaril.Wasm.Lime1.Elem.toCore).map Silmaril.Wasm.Elem.init := by
    have h2 : m.elems.map Silmaril.Wasm.Lime1.Elem.toCore = m.toCore.elems := rfl
    rw [h2, ← hes, List.map_map]
    rfl
  have hf0 : (frame0 before.toCore (withElems m es)
      (imports.map Runtime.ExternVal.toCore)).module.funcs = p.module.funcs.map (·.value) := by
    rw [hmod]
    simp [Silmaril.Wasm.Execution.Core.ModuleInst.initial, baseInst,
      externAddr_funcs_toCore, addresses, Silmaril.Wasm.Execution.Runtime.Store.toCore,
      Silmaril.Wasm.Lime1.Module.toCore, Function.comp_def]
  have hEE : Silmaril.Wasm.Execution.Core.EvalExprss P tgt before.toCore
      (frame0 before.toCore (withElems m es) (imports.map Runtime.ExternVal.toCore))
      ((withElems m es).elems.map Silmaril.Wasm.Elem.init) before.toCore
      (frame0 before.toCore (withElems m es) (imports.map Runtime.ExternVal.toCore))
      (elems.map elemRefs) := by
    rw [hinit]; exact evalExprss_elems _ _ hf0 he2
  have hsteps : Silmaril.Wasm.Execution.Core.Steps P tgt ⟨Sa, { module := mi }, segStart m es⟩
      ⟨S2, { module := mi }, startCode m.toCore⟩ := by
    rw [segStart, hcode]; exact h1.trans h2
  have hsim : ToCore.ModuleInstSim p.module mi := by
    show ToCore.ModuleInst.erase mi = p.module.toCore
    rw [hmod]; exact hmi
  exact ⟨Sa, S2, mi, elems.map elemRefs, evalExprs_tables _ _ m.tables, hEE, hAM, hsteps,
    by rw [hS2, hst], hsim⟩

/-- The size guard of `$instantiate` and `prepare?`, from the copied side conditions. -/
theorem bounded_of {before : Store H} {m : Silmaril.Wasm.Lime1.Module}
    {es : List Silmaril.Wasm.Elem} (hes : es.map funcrefElem = m.toCore.elems)
    (bounds : InstantiationBounds before m) :
    (withElems m es).elems.length ≤ 2 ^ 32 ∧ (withElems m es).data.length ≤ 2 ^ 32 ∧
      (∀ d ∈ (withElems m es).data, d.bytes.size < 2 ^ 32) ∧
      (∀ e ∈ (withElems m es).elems, e.init.length < 2 ^ 32) := by
  have hlen : es.length = m.toCore.elems.length := by rw [← hes, List.length_map]
  refine ⟨by simpa [hlen, Silmaril.Wasm.Lime1.Module.toCore] using bounds.elemCount,
    by simpa [Silmaril.Wasm.Lime1.Module.toCore] using bounds.dataCount,
    by simpa [Silmaril.Wasm.Lime1.Module.toCore, Silmaril.Wasm.Lime1.Data.toCore] using bounds.data,
    fun e he' => ?_⟩
  have hm : funcrefElem e ∈ m.toCore.elems := hes ▸ List.mem_map_of_mem he'
  obtain ⟨e', he'', heq⟩ : ∃ e' ∈ m.elems, Silmaril.Wasm.Lime1.Elem.toCore e' = funcrefElem e := by
    simpa only [Silmaril.Wasm.Lime1.Module.toCore, List.mem_map] using hm
  have hi : e.init = (Silmaril.Wasm.Lime1.Elem.toCore e').init := by rw [heq]; rfl
  rw [hi]
  simpa [Silmaril.Wasm.Lime1.Elem.toCore] using bounds.elemSize e' he''

theorem evalGlobals_nil {P : Profile} {tgt : ToCore.CHostSemantics H} {before : Store H}
    {m : Silmaril.Wasm.Lime1.Module} {es : List Silmaril.Wasm.Elem} (hg : m.globals = [])
    (f : Silmaril.Wasm.Execution.Core.Frame) :
    Silmaril.Wasm.Execution.Core.EvalGlobals P tgt before.toCore f
      ((withElems m es).globals.map fun g => ⟨g.type.mutability,
        (Silmaril.Wasm.Validation.liftVal g.type.value).substAll
          ((Silmaril.Wasm.Execution.Core.allocTypes (withElems m es).types).map .dt)⟩)
      ((withElems m es).globals.map Silmaril.Wasm.Global.init) before.toCore f [] := by
  simp only [Silmaril.Wasm.Lime1.Module.toCore, hg, List.map_nil]; exact .nil

/-- **Lime1 preparation is Core instantiation followed by the segment programs, at every
profile**, for every Core module whose `funcref`-typed form is the image of the Lime1 module. -/
theorem prepare_coreP {P : Profile} {tgt : ToCore.CHostSemantics H} {before : Store H}
    {m : Silmaril.Wasm.Lime1.Module} {imports : List Runtime.ExternVal} {p : Prepared H}
    {es : List Silmaril.Wasm.Elem} (hes : es.map funcrefElem = m.toCore.elems)
    (hvalid : ∃ xtE xtI, Silmaril.Wasm.Validation.ModuleOk (withElems m es) ⟨xtI, xtE⟩ ∧
      List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk before.toCore)
        (imports.map Runtime.ExternVal.toCore) xtI)
    (bounds : InstantiationBounds before m) (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid m)
    (hp : prepare? before m imports = some p) :
    ∃ c S, Silmaril.Wasm.Execution.Core.Instantiate P tgt before.toCore (withElems m es)
        (imports.map Runtime.ExternVal.toCore) c ∧
      Silmaril.Wasm.Execution.Core.Steps P tgt c ⟨S, c.frame, startCode m.toCore⟩ ∧
      ToCore.Store.erase S = p.store.toCore ∧ ToCore.ModuleInstSim p.module c.frame.module ∧
      c.frame.locals = [] := by
  obtain ⟨Sa, S, mi, refsE, hT, hE, hAM, hR, hS, hsim⟩ := prepare_parts (P := P) (tgt := tgt)
    hes bounds hv hp
  refine ⟨⟨Sa, { module := mi }, segStart m es⟩, S,
    ⟨hvalid, bounded_of hes bounds, ?_⟩, hR, hS, hsim, rfl⟩
  exact ⟨_, _, _, Sa, _, _, _, [], _, refsE, mi, evalGlobals_nil bounds.noGlobals _, hT, hE, hAM,
    rfl⟩

theorem constExpr_tables (m : Silmaril.Wasm.Lime1.Module) (es : List Silmaril.Wasm.Elem) :
    ∀ e ∈ (withElems m es).tables.map Silmaril.Wasm.Table.init,
      Silmaril.Wasm.Execution.Core.ConstExpr e := by
  intro e he
  simp only [Silmaril.Wasm.Lime1.Module.toCore, List.map_map, List.mem_map] at he
  obtain ⟨t, -, rfl⟩ := he
  intro i hi
  simp only [Function.comp_apply, Silmaril.Wasm.Lime1.tableToCore, List.mem_singleton] at hi
  subst hi; trivial

theorem constExpr_elems {m : Silmaril.Wasm.Lime1.Module} {es : List Silmaril.Wasm.Elem}
    (hes : es.map funcrefElem = m.toCore.elems) :
    ∀ l ∈ (withElems m es).elems.map Silmaril.Wasm.Elem.init, ∀ e ∈ l,
      Silmaril.Wasm.Execution.Core.ConstExpr e := by
  intro l hl e he i hi
  have hinit : es.map Silmaril.Wasm.Elem.init =
      m.elems.map fun e => e.init.map Silmaril.Wasm.Lime1.funcRef := by
    have h := congrArg (List.map Silmaril.Wasm.Elem.init) hes
    simpa [List.map_map, funcrefElem, Function.comp_def, Silmaril.Wasm.Lime1.Module.toCore,
      Silmaril.Wasm.Lime1.Elem.toCore] using h
  have hl' : l ∈ m.elems.map fun e => e.init.map Silmaril.Wasm.Lime1.funcRef := hinit ▸ hl
  obtain ⟨e', -, rfl⟩ := List.mem_map.mp hl'
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
  simp only [Silmaril.Wasm.Lime1.funcRef, List.mem_singleton] at hi
  subst hi; trivial

/-- The executable Core preparation, from the parts of `$instantiate`. -/
theorem prepare?_of_parts {before : Store H} {m : Silmaril.Wasm.Lime1.Module}
    {imports : List Runtime.ExternVal} {es : List Silmaril.Wasm.Elem}
    (hes : es.map funcrefElem = m.toCore.elems) (bounds : InstantiationBounds before m)
    {Sa : ToCore.CStore H} {mi : ToCore.CModuleInst}
    {refsE : List (List Silmaril.Wasm.Execution.Core.Ref)}
    (hT' : Silmaril.Wasm.Execution.Core.evalExprs? Silmaril.Wasm.Execution.Core.evalConst?
      before.toCore (frame0 before.toCore (withElems m es) (imports.map Runtime.ExternVal.toCore))
      ((withElems m es).tables.map Silmaril.Wasm.Table.init) =
      some (before.toCore, frame0 before.toCore (withElems m es)
        (imports.map Runtime.ExternVal.toCore), m.tables.map fun _ => .null))
    (hE' : Silmaril.Wasm.Execution.Core.evalExprss? Silmaril.Wasm.Execution.Core.evalConst?
      before.toCore (frame0 before.toCore (withElems m es) (imports.map Runtime.ExternVal.toCore))
      ((withElems m es).elems.map Silmaril.Wasm.Elem.init) =
      some (before.toCore, frame0 before.toCore (withElems m es)
        (imports.map Runtime.ExternVal.toCore), refsE))
    (hAM : Silmaril.Wasm.Execution.Core.allocModule? before.toCore (withElems m es)
        (imports.map Runtime.ExternVal.toCore) [] (m.tables.map fun _ => .null) refsE =
        some (Sa, mi)) :
    Silmaril.Wasm.Execution.Core.prepare? Silmaril.Wasm.Execution.Core.evalConst?
      before.toCore (withElems m es) (imports.map Runtime.ExternVal.toCore) =
      some (⟨Sa, { module := mi }, Silmaril.Wasm.Instantiation.initCode (withElems m es)⟩,
        m.toCore.start) := by
  unfold Silmaril.Wasm.Execution.Core.prepare?
  split
  · have hgl : (withElems m es).globals = [] := by
      simp only [Silmaril.Wasm.Lime1.Module.toCore, bounds.noGlobals, List.map_nil]
    rw [hgl]
    simp only [List.map_nil, Silmaril.Wasm.Execution.Core.evalGlobals?]
    erw [hT']
    simp only
    erw [hE']
    simp only
    rw [hAM]
    rfl
  · exact absurd (bounded_of hes bounds) ‹_›

/-- **Lime1 preparation is the executable Core preparation** `prepare? evalConst?` (allocation
and segment code), followed by a run of the segment code at every profile. No validity is
needed. -/
theorem prepare_runP {P : Profile} {tgt : ToCore.CHostSemantics H} {before : Store H}
    {m : Silmaril.Wasm.Lime1.Module} {imports : List Runtime.ExternVal} {p : Prepared H}
    {es : List Silmaril.Wasm.Elem} (hes : es.map funcrefElem = m.toCore.elems)
    (bounds : InstantiationBounds before m) (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid m)
    (hp : prepare? before m imports = some p) :
    ∃ (c : Silmaril.Wasm.Execution.Core.Config H) (S : ToCore.CStore H),
      Silmaril.Wasm.Execution.Core.prepare? Silmaril.Wasm.Execution.Core.evalConst? before.toCore
        (withElems m es) (imports.map Runtime.ExternVal.toCore) = some (c, m.toCore.start) ∧
      c.code = Silmaril.Wasm.Instantiation.initCode (withElems m es) ∧
      Silmaril.Wasm.Execution.Core.Steps P tgt ⟨c.store, c.frame, c.code ++ startCode m.toCore⟩
        ⟨S, c.frame, startCode m.toCore⟩ ∧
      ToCore.Store.erase S = p.store.toCore ∧ ToCore.ModuleInstSim p.module c.frame.module ∧
      c.frame.module.types =
        Silmaril.Wasm.Execution.Core.allocTypes (withElems m es).types := by
  obtain ⟨Sa, S, mi, refsE, hT, hE, hAM, hR, hS, hsim⟩ := prepare_parts (P := P) (tgt := tgt)
    hes bounds hv hp
  have hty : mi.types = Silmaril.Wasm.Execution.Core.allocTypes (withElems m es).types := by
    obtain ⟨_, _, _, -, -, -, hmi, -⟩ := Silmaril.Wasm.Execution.Core.allocModule?_inv hAM
    rw [hmi]
  have hprep := prepare?_of_parts hes bounds
    (Silmaril.Wasm.Execution.Core.evalExprs?_complete
      Silmaril.Proofs.Wasm.Instantiation.evalConst?_evalComplete hT (constExpr_tables m es))
    (Silmaril.Wasm.Execution.Core.evalExprss?_complete
      Silmaril.Proofs.Wasm.Instantiation.evalConst?_evalComplete hE (constExpr_elems hes)) hAM
  exact ⟨_, S, hprep, rfl, hR, hS, hsim, hty⟩

end Silmaril.Proofs.Wasm.Component.Lime1Inst
